/-
  LambdaSat — Completeness Specification
  Fase 13: Completeness Gaps (v1.5.1)

  Defines the bestNode DAG acyclicity predicate, proves that cost
  computation with a positive cost function produces acyclic bestNode
  selections, and proves fuel sufficiency for extraction completeness.

  Key results (G1 — DAG acyclicity):
  - `BestNodeChild`: child relationship via bestNode pointers
  - `AcyclicBestNodeDAG`: acyclicity via ranking function
  - `BestCostLowerBound`: bestCost ≥ costFn(bestNode) + Σ children costs
  - `bestCostLowerBound_acyclic`: lower bound + positive costs → acyclic (0 sorry, 0 axioms)
  - `computeCostsF_acyclic`: computeCostsF with positive costs → acyclic DAG (0 sorry)

  Key results (G2 — fuel sufficiency):
  - `extractF_of_rank`: fuel > rank(id) → extractF succeeds (0 sorry, 0 axioms)
  - `extractAuto_complete`: extractAuto succeeds when rank < numClasses (0 sorry, 0 axioms)

  Zero sorry. The HashMap API gap (m.keys vs m.toList.map Prod.fst) is closed via
  Std.HashMap.keys/toList simp lemmas and Std.HashMap.nodup_keys in Lean 4.26.
-/
import LambdaSat.Extractable

namespace LambdaSat

open UnionFind

variable {Op : Type} [NodeOps Op] [BEq Op] [Hashable Op]
  [LawfulBEq Op] [LawfulHashable Op]

-- ══════════════════════════════════════════════════════════════════
-- Section 1: Definitions
-- ══════════════════════════════════════════════════════════════════

/-- Look up the bestCost of the canonical representative of `cid`. -/
def bestCostOf (g : EGraph Op) (cid : EClassId) : Nat :=
  match g.classes.get? (root g.unionFind cid) with
  | some cls => cls.bestCost
  | none => infinityCost

/-- Child relationship via bestNode pointers: `parentId` has a bestNode
    whose children include `childId`. -/
def BestNodeChild (g : EGraph Op) (parentId childId : EClassId) : Prop :=
  ∃ cls nd,
    g.classes.get? (root g.unionFind parentId) = some cls ∧
    cls.bestNode = some nd ∧
    childId ∈ nd.children

/-- The bestNode DAG is acyclic: there exists a ranking function that
    strictly decreases along `BestNodeChild` edges. -/
def AcyclicBestNodeDAG (g : EGraph Op) : Prop :=
  ∃ (rank : EClassId → Nat),
    ∀ parentId childId, BestNodeChild g parentId childId →
      rank childId < rank parentId

/-- After cost computation, bestCost satisfies a lower bound:
    bestCost(cid) ≥ costFn(bestNode) + Σ bestCostOf(children of bestNode).
    This is the key invariant for acyclicity. -/
def BestCostLowerBound (g : EGraph Op) (costFn : ENode Op → Nat) : Prop :=
  ∀ cid cls nd, g.classes.get? cid = some cls →
    cls.bestNode = some nd →
    cls.bestCost ≥ costFn nd +
      nd.children.foldl (fun sum c => sum + bestCostOf g c) 0

-- ══════════════════════════════════════════════════════════════════
-- Section 2: BestCostLowerBound implies acyclicity
-- ══════════════════════════════════════════════════════════════════

/-- Foldl with non-negative additions is ≥ init. -/
private theorem foldl_ge_init (g : EGraph Op) (children : List EClassId) (init : Nat) :
    children.foldl (fun sum c => sum + bestCostOf g c) init ≥ init := by
  induction children generalizing init with
  | nil => exact Nat.le_refl _
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    exact Nat.le_trans (Nat.le_add_right _ _) (ih _)

/-- If `childId` is in a list, then the fold sum ≥ bestCostOf childId. -/
private theorem foldl_sum_ge_mem (g : EGraph Op) (children : List EClassId)
    (childId : EClassId) (hmem : childId ∈ children) :
    children.foldl (fun sum c => sum + bestCostOf g c) 0 ≥ bestCostOf g childId := by
  suffices h : ∀ init, childId ∈ children →
      children.foldl (fun sum c => sum + bestCostOf g c) init ≥ init + bestCostOf g childId by
    have := h 0 hmem; omega
  intro init hmem
  induction children generalizing init with
  | nil => contradiction
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hmem with heq | hmem_tl
    · subst heq
      exact foldl_ge_init g tl _
    · have := ih hmem_tl (init + bestCostOf g hd) hmem_tl
      omega

/-- **BestCostLowerBound with positive cost function implies acyclic DAG.**
    Uses bestCostOf as the ranking function: if bestCost(parent) ≥ costFn(nd) + Σ children
    and costFn ≥ 1, then bestCost(parent) > bestCost(child). -/
theorem bestCostLowerBound_acyclic (g : EGraph Op) (costFn : ENode Op → Nat)
    (hlb : BestCostLowerBound g costFn)
    (hcost_pos : ∀ (nd : ENode Op), 0 < costFn nd) :
    AcyclicBestNodeDAG g := by
  refine ⟨bestCostOf g, ?_⟩
  intro parentId childId ⟨cls, nd, hcls, hbn, hchild⟩
  have hlb' := hlb (root g.unionFind parentId) cls nd hcls hbn
  have hsum := foldl_sum_ge_mem g nd.children childId hchild
  have hpos := hcost_pos nd
  have hparent : bestCostOf g parentId = cls.bestCost := by
    unfold bestCostOf; rw [hcls]
  rw [hparent]
  omega

-- ══════════════════════════════════════════════════════════════════
-- Section 3: updateClassBest properties
-- ══════════════════════════════════════════════════════════════════

/-- When updateClassBest returns changed=true, the cost equals
    costFn(nd) + childCosts computed using the accumulator. -/
private theorem updateClassBest_cost_eq (uf : UnionFind) (costFn : ENode Op → Nat)
    (acc : Std.HashMap EClassId (EClass Op)) (eclass : EClass Op) :
    let r := updateClassBest uf costFn acc eclass
    r.2.2 = true →
    ∀ nd, r.2.1 = some nd →
    r.1 = costFn nd + nd.children.foldl
      (fun sum cid => sum + match acc.get? (root uf cid) with
        | some ec => ec.bestCost | none => infinityCost) 0 := by
  simp only [updateClassBest]
  exact @Array.foldl_induction (ENode Op) (Nat × Option (ENode Op) × Bool)
    eclass.nodes
    (fun _ st =>
      st.2.2 = true →
      ∀ nd, st.2.1 = some nd →
      st.1 = costFn nd + nd.children.foldl
        (fun sum cid => sum + match acc.get? (root uf cid) with
          | some ec => ec.bestCost | none => infinityCost) 0)
    _
    (fun h => by simp at h)
    _
    (fun ⟨i, hi⟩ ⟨curBest, curNode, curChanged⟩ prev => by
      dsimp only
      split
      · intro _ nd hnd
        cases Option.some.inj hnd
        simp [ENode.children]; rfl
      · exact prev)

/-- bestCost can only decrease through updateClassBest. -/
private theorem updateClassBest_bestCost_le (uf : UnionFind) (costFn : ENode Op → Nat)
    (acc : Std.HashMap EClassId (EClass Op)) (eclass : EClass Op) :
    (updateClassBest uf costFn acc eclass).1 ≤ eclass.bestCost := by
  simp only [updateClassBest]
  exact @Array.foldl_induction (ENode Op) (Nat × Option (ENode Op) × Bool)
    eclass.nodes
    (fun _ st => st.1 ≤ eclass.bestCost)
    _
    (Nat.le_refl _)
    _
    (fun ⟨i, hi⟩ ⟨curBest, curNode, curChanged⟩ prev => by
      dsimp only
      split
      · exact Nat.le_of_lt (by omega)
      · exact prev)

-- ══════════════════════════════════════════════════════════════════
-- Section 4: computeCostsF produces BestCostLowerBound
-- ══════════════════════════════════════════════════════════════════

/-- Self-referential lower bound invariant on a classes HashMap. -/
private def SelfLB (uf : UnionFind) (classes : Std.HashMap EClassId (EClass Op))
    (costFn : ENode Op → Nat) : Prop :=
  ∀ cid cls nd, classes.get? cid = some cls → cls.bestNode = some nd →
    cls.bestCost ≥ costFn nd + nd.children.foldl
      (fun sum c => sum + match classes.get? (root uf c) with
        | some ec => ec.bestCost | none => infinityCost) 0

-- ── Helpers for closing the processKeys-preserves-SelfLB gap ──

/-- HashMap insert: get? at same key returns inserted value. -/
private theorem get?_insert_self_cls (m : Std.HashMap EClassId (EClass Op))
    (k : EClassId) (v : EClass Op) :
    (m.insert k v).get? k = some v := by
  simp only [Std.HashMap.get?_eq_getElem?]
  rw [Std.HashMap.getElem?_insert]; simp

/-- HashMap insert: get? at different key is unchanged. -/
private theorem get?_insert_ne_cls (m : Std.HashMap EClassId (EClass Op))
    (k k' : EClassId) (v : EClass Op) (h : k ≠ k') :
    (m.insert k v).get? k' = m.get? k' := by
  simp only [Std.HashMap.get?_eq_getElem?]
  rw [Std.HashMap.getElem?_insert]; simp [beq_iff_eq, h]

/-- HashMap toList keys have no duplicates (bridge from keys API). -/
private theorem keys_nodup_cls
    (m : Std.HashMap EClassId (EClass Op)) : (m.toList.map Prod.fst).Nodup := by
  have : m.keys = m.toList.map Prod.fst := by
    simp [Std.HashMap.keys, Std.HashMap.toList]
  rw [← this]; exact Std.HashMap.nodup_keys

/-- Pointwise f ≤ g implies foldl sum with f ≤ foldl sum with g. -/
private theorem foldl_sum_le_pointwise (children : List EClassId) {f g : EClassId → Nat}
    (hle : ∀ c, f c ≤ g c) :
    children.foldl (fun sum c => sum + f c) 0 ≤
    children.foldl (fun sum c => sum + g c) 0 := by
  suffices h : ∀ i1 i2, i1 ≤ i2 →
      children.foldl (fun s c => s + f c) i1 ≤ children.foldl (fun s c => s + g c) i2 by
    exact h 0 0 (Nat.le_refl _)
  intro i1 i2 hi
  induction children generalizing i1 i2 with
  | nil => exact hi
  | cons hd tl ih =>
    simp only [List.foldl_cons]; apply ih; have := hle hd; omega

/-- **processKeys preserves SelfLB.** Key invariant: unprocessed keys have
    their original entries in acc. Nodup ensures each key is processed at most
    once, so bestCost at any position can only decrease, maintaining the
    self-referential lower bound. -/
private theorem processKeys_preserves_SelfLB (uf : UnionFind) (costFn : ENode Op → Nat)
    (classes : Std.HashMap EClassId (EClass Op))
    : ∀ (keys : List EClassId) (acc : Std.HashMap EClassId (EClass Op)) (changed : Bool),
      SelfLB uf acc costFn →
      (∀ k, k ∈ keys → acc.get? k = classes.get? k) →
      keys.Nodup →
      SelfLB uf (processKeys uf costFn classes keys acc changed).1 costFn := by
  intro keys
  induction keys with
  | nil => intro acc changed hslb _ _; exact hslb
  | cons classId rest ih =>
    intro acc changed hslb horig hnodup
    simp only [processKeys]
    split
    · -- classes.get? classId = none → skip, acc unchanged
      exact ih acc changed hslb
        (fun k hk => horig k (List.mem_cons.mpr (Or.inr hk)))
        (List.nodup_cons.mp hnodup).2
    · -- classes.get? classId = some eclass
      next eclass heclass =>
      by_cases hchg : (updateClassBest uf costFn acc eclass).snd.snd = true
      · -- changed = true → insert updated entry
        simp only [hchg, ite_true]
        have hnotmem : classId ∉ rest := (List.nodup_cons.mp hnodup).1
        have hrest_nodup := (List.nodup_cons.mp hnodup).2
        have hacc_cid : acc.get? classId = some eclass := by
          rw [horig classId (List.mem_cons.mpr (Or.inl rfl))]; exact heclass
        have hcost_le := updateClassBest_bestCost_le uf costFn acc eclass
        -- Abbreviate the new entry for readability
        let ne : EClass Op :=
          { eclass with
            bestCost := (updateClassBest uf costFn acc eclass).fst
            bestNode := (updateClassBest uf costFn acc eclass).snd.fst }
        -- getCost monotonicity: inserting lower cost doesn't increase lookups
        have hcost_mono : ∀ c,
            (match (acc.insert classId ne).get? (root uf c) with
              | some ec => ec.bestCost | none => infinityCost) ≤
            (match acc.get? (root uf c) with
              | some ec => ec.bestCost | none => infinityCost) := by
          intro c
          by_cases heq : classId = root uf c
          · rw [← heq, get?_insert_self_cls, hacc_cid]; simp [ne]; exact hcost_le
          · rw [get?_insert_ne_cls _ _ _ _ heq]; exact Nat.le.refl
        -- SelfLB for the updated acc
        have hslb' : SelfLB uf (acc.insert classId ne) costFn := by
          intro cid cls nd hget' hbn
          by_cases heq : classId = cid
          · -- cid = classId: newly inserted entry
            subst heq
            rw [get?_insert_self_cls] at hget'
            have hcls := Option.some.inj hget'; subst hcls
            have hcost_eq :=
              updateClassBest_cost_eq uf costFn acc eclass hchg nd hbn
            have hmono := foldl_sum_le_pointwise nd.children hcost_mono
            have h_ne_cost : ne.bestCost =
              (updateClassBest uf costFn acc eclass).fst := rfl
            omega
          · -- cid ≠ classId: unchanged entry
            rw [get?_insert_ne_cls _ _ _ _ heq] at hget'
            have hold := hslb cid cls nd hget' hbn
            have hmono := foldl_sum_le_pointwise nd.children hcost_mono
            omega
        -- Rest keys unchanged
        have horig' : ∀ k, k ∈ rest →
            (acc.insert classId ne).get? k = classes.get? k := by
          intro k hk
          have hne : classId ≠ k := fun h => hnotmem (h ▸ hk)
          rw [get?_insert_ne_cls _ _ _ _ hne]
          exact horig k (List.mem_cons.mpr (Or.inr hk))
        exact ih _ true hslb' horig' hrest_nodup
      · -- changed = false → no insert, acc unchanged
        simp only [hchg]
        exact ih acc changed hslb
          (fun k hk => horig k (List.mem_cons.mpr (Or.inr hk)))
          (List.nodup_cons.mp hnodup).2

/-- computeCostsLoop preserves the self-referential lower bound.
    Each processKeys pass only decreases costs, so the SelfLB invariant
    is maintained through all iterations. -/
private theorem computeCostsLoop_selfLB (uf : UnionFind) (costFn : ENode Op → Nat)
    : ∀ (fuel : Nat) (classes : Std.HashMap EClassId (EClass Op)),
    SelfLB uf classes costFn →
    SelfLB uf (computeCostsLoop uf costFn classes fuel) costFn
  | 0, classes, h => h
  | n + 1, classes, h => by
    simp only [computeCostsLoop]
    have h_pk : SelfLB uf (processKeys uf costFn classes
        (classes.toList.map Prod.fst) classes false).1 costFn :=
      processKeys_preserves_SelfLB uf costFn classes _ _ _ h
        (fun _ _ => rfl) (keys_nodup_cls classes)
    split
    · exact computeCostsLoop_selfLB uf costFn n _ h_pk
    · exact h_pk

/-- **computeCostsF on a fresh graph produces a BestCostLowerBound.**
    A "fresh" graph has bestNode = none for all classes (the default after
    saturateF, since saturation doesn't modify bestNode/bestCost). -/
theorem computeCostsF_bestCost_lower_bound (g : EGraph Op) (costFn : ENode Op → Nat)
    (fuel : Nat)
    (h_fresh : ∀ cid cls, g.classes.get? cid = some cls → cls.bestNode = none) :
    BestCostLowerBound (computeCostsF g costFn fuel) costFn := by
  -- BestCostLowerBound for computeCostsF = SelfLB for computeCostsLoop output
  -- (since computeCostsF_preserves_uf means the UF is unchanged)
  show SelfLB g.unionFind (computeCostsLoop g.unionFind costFn g.classes fuel) costFn
  apply computeCostsLoop_selfLB
  -- Initial classes have bestNode = none → SelfLB vacuously true
  intro cid cls nd hcls hbn
  exact absurd hbn (by simp [h_fresh cid cls hcls])

/-- **computeCostsF with positive cost function produces an acyclic bestNode DAG.**
    Combines BestCostLowerBound (from cost monotonicity) with the acyclicity theorem.
    Hypothesis `h_fresh`: all classes have bestNode = none (true after saturateF). -/
theorem computeCostsF_acyclic (g : EGraph Op) (costFn : ENode Op → Nat)
    (fuel : Nat)
    (h_fresh : ∀ cid cls, g.classes.get? cid = some cls → cls.bestNode = none)
    (hcost_pos : ∀ (nd : ENode Op), 0 < costFn nd) :
    AcyclicBestNodeDAG (computeCostsF g costFn fuel) :=
  bestCostLowerBound_acyclic _ costFn
    (computeCostsF_bestCost_lower_bound g costFn fuel h_fresh) hcost_pos

-- ══════════════════════════════════════════════════════════════════
-- Section 5: Fuel sufficiency for extractF
-- ══════════════════════════════════════════════════════════════════

variable {Expr : Type} [Extractable Op Expr]

/-- mapOption succeeds when f succeeds on all elements. -/
private theorem mapOption_some_of_forall {f : α → Option β} {l : List α}
    (h : ∀ a, a ∈ l → ∃ b, f a = some b) :
    ∃ bs, mapOption f l = some bs := by
  induction l with
  | nil => exact ⟨[], rfl⟩
  | cons hd tl ih =>
    obtain ⟨b, hb⟩ := h hd (List.mem_cons.mpr (Or.inl rfl))
    have ih' := ih (fun a ha => h a (List.mem_cons.mpr (Or.inr ha)))
    obtain ⟨bs, hbs⟩ := ih'
    exact ⟨b :: bs, by simp [mapOption, hb, hbs]⟩

/-- **Fuel sufficiency**: if the bestNode DAG is acyclic (via rank function),
    every class has bestNode set, and reconstruct always succeeds,
    then extractF returns `some` when fuel > rank(id).

    Proof by strong induction on `rank id`:
    - Unfold extractF: lookup class (succeeds by hset), get bestNode (succeeds by hset),
      recurse on children with fuel-1 (succeeds by ih since rank child < rank parent
      from hrank, and fuel-1 > rank child since fuel > rank parent). -/
theorem extractF_of_rank (g : EGraph Op)
    (rank : EClassId → Nat)
    (hrank : ∀ parentId childId, BestNodeChild g parentId childId →
      rank childId < rank parentId)
    (hset : ∀ cid cls, g.classes.get? (root g.unionFind cid) = some cls →
      ∃ nd, cls.bestNode = some nd)
    (hclass : ∀ cid, ∃ cls, g.classes.get? (root g.unionFind cid) = some cls)
    (hrecon : ∀ (nd : ENode Op) (childExprs : List Expr),
      (Extractable.reconstruct nd.op childExprs).isSome = true)
    : ∀ (id : EClassId) (fuel : Nat), fuel > rank id →
      (extractF (Expr := Expr) g id fuel).isSome = true := by
  -- Suffices to prove: ∀ n id, rank id = n → fuel > n → extractF succeeds
  -- by strong induction on n
  suffices h : ∀ n, ∀ id, rank id = n → ∀ fuel, fuel > n →
      (extractF (Expr := Expr) g id fuel).isSome = true by
    intro id fuel hfuel; exact h (rank id) id rfl fuel hfuel
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro id hrn fuel hfuel
    match fuel, hfuel with
    | fuel + 1, hfuel =>
      -- Unfold extractF and resolve class/bestNode lookups
      obtain ⟨cls, hcls⟩ := hclass id
      obtain ⟨nd, hnd⟩ := hset id cls hcls
      -- Show mapOption succeeds on children via ih
      have hmop : ∃ bs, mapOption (fun c => extractF (Expr := Expr) g c fuel)
          (NodeOps.children nd.op) = some bs := by
        apply mapOption_some_of_forall
        intro c hc
        have hbnc : BestNodeChild g id c := ⟨cls, nd, hcls, hnd, hc⟩
        have hrc : rank c < n := by rw [← hrn]; exact hrank id c hbnc
        have hfc : fuel > rank c := by omega
        have := ih (rank c) hrc c rfl fuel hfc
        obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp this
        exact ⟨v, hv⟩
      obtain ⟨bs, hbs⟩ := hmop
      simp only [extractF, hcls, hnd, hbs]
      exact hrecon nd bs

/-- **extractAuto completeness**: if the bestNode DAG is acyclic with rank bounded
    by `numClasses`, all classes have bestNode set, and reconstruct always succeeds,
    then `extractAuto` returns `some`.

    This closes gap G2 (fuel sufficiency). -/
theorem extractAuto_complete (g : EGraph Op)
    (rank : EClassId → Nat)
    (hrank : ∀ parentId childId, BestNodeChild g parentId childId →
      rank childId < rank parentId)
    (hbound : ∀ id, rank id < g.numClasses)
    (hset : ∀ cid cls, g.classes.get? (root g.unionFind cid) = some cls →
      ∃ nd, cls.bestNode = some nd)
    (hclass : ∀ cid, ∃ cls, g.classes.get? (root g.unionFind cid) = some cls)
    (hrecon : ∀ (nd : ENode Op) (childExprs : List Expr),
      (Extractable.reconstruct nd.op childExprs).isSome = true)
    (rootId : EClassId) :
    (extractAuto (Expr := Expr) g rootId).isSome = true := by
  unfold extractAuto
  exact extractF_of_rank g rank hrank hset hclass hrecon rootId
    (g.numClasses + 1) (by have := hbound rootId; omega)

end LambdaSat
