/-
  LambdaSat — Semantic Specification
  Domain-agnostic semantic soundness: ConsistentValuation, merge/add/processClass
  preserve consistency, computeCostsF total version, BestNodeInv lifecycle.
  Generalized from VR1CS-Lean v1.3.0 (replaces ZMod p / CircuitNodeOp with typeclasses).
-/
import LambdaSat.CoreSpec
import LambdaSat.EMatch
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace LambdaSat

open UnionFind

-- ══════════════════════════════════════════════════════════════════
-- Section 0: NodeSemantics Typeclass
-- ══════════════════════════════════════════════════════════════════

/-- Typeclass for semantic evaluation of e-graph node operations.
    `Val` is the semantic domain (e.g., `ZMod p` for circuits, `Nat` for arithmetic).
    `env` maps external inputs, `v` maps e-class IDs to values. -/
class NodeSemantics (Op : Type) (Val : Type) [NodeOps Op] where
  /-- Evaluate an operation given an environment and a class-value mapping. -/
  evalOp : Op → (Nat → Val) → (EClassId → Val) → Val
  /-- `evalOp` depends on `v` only through the children of `op`. -/
  evalOp_ext : ∀ (op : Op) (env : Nat → Val) (v v' : EClassId → Val),
    (∀ c ∈ NodeOps.children op, v c = v' c) → evalOp op env v = evalOp op env v'
  /-- `mapChildren f` commutes with `evalOp`: replacing children by `f` in the op
      is equivalent to precomposing `v` with `f`. -/
  evalOp_mapChildren : ∀ (f : EClassId → EClassId) (op : Op) (env : Nat → Val)
    (v : EClassId → Val),
    evalOp (NodeOps.mapChildren f op) env v = evalOp op env (fun c => v (f c))
  /-- Ops with identical skeletons evaluate the same when corresponding children
      have matching values. The skeleton is `mapChildren (fun _ => 0) op`.
      This bridges pattern evaluation to node evaluation in ematchF_sound. -/
  evalOp_skeleton : ∀ (op₁ op₂ : Op) (env : Nat → Val) (v₁ v₂ : EClassId → Val),
    NodeOps.mapChildren (fun _ => (0 : EClassId)) op₁ =
      NodeOps.mapChildren (fun _ => (0 : EClassId)) op₂ →
    (∀ (i : Nat) (h₁ : i < (NodeOps.children op₁).length)
        (h₂ : i < (NodeOps.children op₂).length),
      v₁ ((NodeOps.children op₁)[i]) = v₂ ((NodeOps.children op₂)[i])) →
    evalOp op₁ env v₁ = evalOp op₂ env v₂

/-- Semantic evaluation of an ENode: delegates to `NodeSemantics.evalOp`. -/
def NodeEval {Op Val : Type} [NodeOps Op] [NodeSemantics Op Val]
    (node : ENode Op) (env : Nat → Val) (v : EClassId → Val) : Val :=
  NodeSemantics.evalOp node.op env v

variable {Op : Type} {Val : Type}
  [NodeOps Op] [BEq Op] [Hashable Op] [LawfulBEq Op] [LawfulHashable Op]
  [NodeSemantics Op Val]

-- ══════════════════════════════════════════════════════════════════
-- Section 1: ConsistentValuation + Basic Theorems
-- ══════════════════════════════════════════════════════════════════

/-- A valuation `v : EClassId → Val` is consistent with an e-graph `g`
    under environment `env` if:
    (1) UF-equivalent class IDs have the same value, and
    (2) every node in a class evaluates to that class's value. -/
def ConsistentValuation (g : EGraph Op) (env : Nat → Val) (v : EClassId → Val) : Prop :=
  (∀ i j, root g.unionFind i = root g.unionFind j → v i = v j) ∧
  (∀ classId eclass, g.classes.get? classId = some eclass →
    ∀ node, node ∈ eclass.nodes.toList →
      NodeEval node env v = v classId)

/-- The empty e-graph trivially has a consistent valuation. -/
theorem empty_consistent [Inhabited Val] (env : Nat → Val) :
    ConsistentValuation (Op := Op) EGraph.empty env (fun _ => default) := by
  constructor
  · intro _ _ _; rfl
  · intro classId eclass h
    simp [EGraph.empty, Std.HashMap.get?_eq_getElem?, Std.HashMap.ofList_nil] at h

/-- Consistent valuations respect root: v(root i) = v i. -/
theorem consistent_root_eq (g : EGraph Op) (env : Nat → Val) (v : EClassId → Val)
    (hv : ConsistentValuation g env v) (hwf : WellFormed g.unionFind)
    (hid : i < g.unionFind.parent.size) :
    v (root g.unionFind i) = v i :=
  hv.1 (root g.unionFind i) i (root_idempotent g.unionFind i hwf hid)

/-- root of out-of-bounds id equals id. -/
private theorem root_oob (uf : UnionFind) (id : EClassId)
    (h : ¬(id < uf.parent.size)) :
    root uf id = id := by
  simp only [root]
  match hps : uf.parent.size with
  | 0 => rfl
  | _ + 1 => exact rootD_succ_oob (by omega)

/-- v(root id) = v id, handling both in-bounds and out-of-bounds. -/
theorem consistent_root_eq' (g : EGraph Op) (env : Nat → Val) (v : EClassId → Val)
    (hv : ConsistentValuation g env v) (hwf : WellFormed g.unionFind)
    (id : EClassId) :
    v (root g.unionFind id) = v id := by
  by_cases hid : id < g.unionFind.parent.size
  · exact consistent_root_eq g env v hv hwf hid
  · rw [root_oob g.unionFind id hid]

/-- find (path compression) preserves ConsistentValuation. -/
theorem find_consistent (g : EGraph Op) (id : EClassId)
    (env : Nat → Val) (v : EClassId → Val)
    (hv : ConsistentValuation g env v) (hwf : WellFormed g.unionFind) :
    ConsistentValuation (g.find id).2 env v := by
  have hfr : ∀ j, root (g.find id).2.unionFind j = root g.unionFind j := by
    intro j; simp [EGraph.find]; exact find_preserves_roots g.unionFind id j hwf
  constructor
  · intro i j hrij
    exact hv.1 i j (by rw [← hfr i, ← hfr j]; exact hrij)
  · intro classId eclass hcls node hmem
    simp [EGraph.find] at hcls
    exact hv.2 classId eclass hcls node hmem

/-- UF-equivalent IDs have the same valuation. -/
theorem equiv_same_value (g : EGraph Op)
    (env : Nat → Val) (v : EClassId → Val)
    (hv : ConsistentValuation g env v)
    (id1 id2 : EClassId)
    (heq : root g.unionFind id1 = root g.unionFind id2) :
    v id1 = v id2 :=
  hv.1 id1 id2 heq

/-- Nodes in the same e-class evaluate identically under any
    consistent valuation. -/
theorem class_nodes_same_value (g : EGraph Op) (classId : EClassId)
    (eclass : EClass Op) (hcls : g.classes.get? classId = some eclass)
    (env : Nat → Val) (v : EClassId → Val)
    (hv : ConsistentValuation g env v)
    (n1 n2 : ENode Op) (h1 : n1 ∈ eclass.nodes.toList) (h2 : n2 ∈ eclass.nodes.toList) :
    NodeEval n1 env v = NodeEval n2 env v := by
  rw [hv.2 classId eclass hcls n1 h1, hv.2 classId eclass hcls n2 h2]

-- ══════════════════════════════════════════════════════════════════
-- Section 2: NodeEval Helpers (generic via typeclass laws)
-- ══════════════════════════════════════════════════════════════════

/-- NodeEval depends only on children values. -/
theorem nodeEval_children_eq (node : ENode Op) (env : Nat → Val)
    (v v' : EClassId → Val)
    (h : ∀ c, c ∈ node.children → v c = v' c) :
    NodeEval node env v = NodeEval node env v' :=
  NodeSemantics.evalOp_ext node.op env v v' h

/-- go produces pairs whose .2 have same UF-root as .1 in the original graph. -/
private theorem go_pairs_roots_sem (cs : List EClassId) (g : EGraph Op)
    (ps : List (EClassId × EClassId))
    (hwf : WellFormed g.unionFind)
    (hps : ∀ p ∈ ps, root g.unionFind p.2 = root g.unionFind p.1)
    (hcs : ∀ c ∈ cs, c < g.unionFind.parent.size) :
    ∀ p ∈ (EGraph.canonicalize.go cs g ps).1,
      root g.unionFind p.2 = root g.unionFind p.1 := by
  induction cs generalizing g ps with
  | nil => unfold EGraph.canonicalize.go; exact hps
  | cons c rest ih =>
    unfold EGraph.canonicalize.go
    have hc_lt := hcs c (List.Mem.head rest)
    have hwf' := egraph_find_uf_wf g c hwf
    have hconv : ∀ j, root (g.find c).2.unionFind j = root g.unionFind j :=
      fun j => egraph_find_preserves_roots g c j hwf
    have hps' : ∀ p ∈ ((c, (g.find c).1) :: ps),
        root (g.find c).2.unionFind p.2 = root (g.find c).2.unionFind p.1 := by
      intro p hp; rcases List.mem_cons.mp hp with rfl | hp
      · simp; rw [egraph_find_fst, hconv, hconv]
        exact root_idempotent g.unionFind c hwf hc_lt
      · rw [hconv, hconv]; exact hps p hp
    have hcs' : ∀ c' ∈ rest, c' < (g.find c).2.unionFind.parent.size :=
      fun c' hc' => by rw [egraph_find_uf_size]
                       exact hcs c' (List.mem_cons_of_mem c hc')
    intro p hp
    have := ih (g.find c).2 ((c, (g.find c).1) :: ps) hwf' hps' hcs' p hp
    simp only [hconv] at this; exact this

/-- Lookup in canonicalize pairs preserves UF-roots. -/
private theorem lookup_root_eq_sem (pairs : List (EClassId × EClassId))
    (uf : UnionFind) (c : EClassId)
    (hpairs : ∀ p ∈ pairs, root uf p.2 = root uf p.1) :
    root uf (match pairs.find? (fun (old, _) => old == c) with
     | some (_, new_) => new_ | none => c) = root uf c := by
  match h : pairs.find? (fun (old, _) => old == c) with
  | some (old, new_) =>
    simp only [h]
    have hmem := List.mem_of_find?_eq_some h
    have hbeq := List.find?_some h
    rw [hpairs (old, new_) hmem]
    simp [BEq.beq] at hbeq; rw [hbeq]
  | none => simp [h]

/-- NodeEval invariant under canonicalize with UF-consistent valuation. -/
theorem nodeEval_canonical (g : EGraph Op) (node : ENode Op)
    (env : Nat → Val) (v : EClassId → Val)
    (huf : ∀ i j, root g.unionFind i = root g.unionFind j → v i = v j)
    (hwf : WellFormed g.unionFind)
    (hbnd : ∀ c ∈ node.children, c < g.unionFind.parent.size) :
    NodeEval (g.canonicalize node).1 env v = NodeEval node env v := by
  by_cases h : node.children = []
  · rw [canonicalize_leaf g node h]
  · -- Non-leaf: use evalOp_mapChildren + evalOp_ext
    have hpairs := go_pairs_roots_sem (ENode.children node) g []
      hwf (fun _ h' => nomatch h') hbnd
    -- Unfold canonicalize for non-leaf case; use if_neg to select else branch
    unfold EGraph.canonicalize at *
    dsimp only at *
    have hie : ¬ ((ENode.children node).isEmpty = true) := by rwa [List.isEmpty_iff]
    rw [if_neg hie]
    -- Now goal involves (let (pairs,g') := go ...; let f := ...; (node.mapChildren f, g')).1
    -- NodeEval delegates to evalOp; use mapChildren law
    simp only [NodeEval, ENode.mapChildren]
    rw [NodeSemantics.evalOp_mapChildren]
    apply NodeSemantics.evalOp_ext
    intro c hc
    exact huf _ _ (lookup_root_eq_sem _ g.unionFind c hpairs)

-- ══════════════════════════════════════════════════════════════════
-- Section 3: merge preserves ConsistentValuation
-- ══════════════════════════════════════════════════════════════════

/-- merge preserves ConsistentValuation when the merged classes have equal
    values. The same valuation v works for the merged graph. -/
theorem merge_consistent (g : EGraph Op) (id1 id2 : EClassId)
    (env : Nat → Val) (v : EClassId → Val)
    (hv : ConsistentValuation g env v) (hwf : WellFormed g.unionFind)
    (h1 : id1 < g.unionFind.parent.size) (h2 : id2 < g.unionFind.parent.size)
    (heq : v (root g.unionFind id1) = v (root g.unionFind id2)) :
    ConsistentValuation (g.merge id1 id2) env v := by
  -- Pure UF-level lemmas
  have hfpr1 : ∀ k, root (g.unionFind.find id1).2 k = root g.unionFind k :=
    fun k => find_preserves_roots g.unionFind id1 k hwf
  have hwf1 : WellFormed (g.unionFind.find id1).2 :=
    find_preserves_wf g.unionFind id1 hwf
  have hfpr2 : ∀ k, root ((g.unionFind.find id1).2.find id2).2 k = root g.unionFind k :=
    fun k => (find_preserves_roots _ id2 k hwf1).trans (hfpr1 k)
  have hwf2 : WellFormed ((g.unionFind.find id1).2.find id2).2 :=
    find_preserves_wf _ id2 hwf1
  have hsz2 : ((g.unionFind.find id1).2.find id2).2.parent.size = g.unionFind.parent.size := by
    rw [find_snd_size, find_snd_size]
  -- Unfold merge
  unfold EGraph.merge; simp only [EGraph.find, find_fst_eq_root]
  rw [show root (g.unionFind.find id1).2 id2 = root g.unionFind id2 from hfpr1 id2]
  -- Split on root equality
  split
  · -- Same root: merge returns g2
    constructor
    · intro i j hij; rw [hfpr2, hfpr2] at hij; exact hv.1 i j hij
    · intro cid cls hcls nd hmem; exact hv.2 cid cls hcls nd hmem
  · -- Different roots
    rename_i hne_beq
    have hne : root g.unionFind id1 ≠ root g.unionFind id2 := by
      intro h; exact hne_beq (beq_iff_eq.mpr h)
    -- Bounds for union_root_cases
    have hr1_bnd : root g.unionFind id1 < ((g.unionFind.find id1).2.find id2).2.parent.size :=
      hsz2 ▸ rootD_bounded hwf.1 h1
    have hr2_bnd : root g.unionFind id2 < ((g.unionFind.find id1).2.find id2).2.parent.size :=
      hsz2 ▸ rootD_bounded hwf.1 h2
    -- root_idempotent
    have hr1_idem : root g.unionFind (root g.unionFind id1) = root g.unionFind id1 :=
      root_idempotent g.unionFind id1 hwf h1
    have hr2_idem : root g.unionFind (root g.unionFind id2) = root g.unionFind id2 :=
      root_idempotent g.unionFind id2 hwf h2
    constructor
    · -- Part 1: UF-consistency
      intro i j hij
      have hvi := (consistent_root_eq' g env v hv hwf i).symm
      have hvj := (consistent_root_eq' g env v hv hwf j).symm
      rw [hvi, hvj]
      rcases union_root_cases _ _ _ i hwf2 hr1_bnd hr2_bnd with hi | ⟨hi_new, hi_old⟩ <;>
        rcases union_root_cases _ _ _ j hwf2 hr1_bnd hr2_bnd with hj | ⟨hj_new, hj_old⟩
      · rw [hi, hj] at hij; simp only [hfpr2] at hij; exact congrArg v hij
      · rw [hi, hj_new] at hij; simp only [hfpr2] at hij hj_old
        rw [hij, hr1_idem, hj_old, hr2_idem]; exact heq
      · rw [hi_new, hj] at hij; simp only [hfpr2] at hij hi_old
        rw [hi_old, hr2_idem, ← hij, hr1_idem]; exact heq.symm
      · simp only [hfpr2] at hi_old hj_old; rw [hi_old, hr2_idem, hj_old, hr2_idem]
    · -- Part 2: Node-consistency
      intro classId eclass hcls node hmem
      simp only [] at hcls
      by_cases hid : root g.unionFind id1 = classId
      · -- classId = root1: eclass = mergedClass
        subst hid
        simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
          beq_self_eq_true, ite_true] at hcls
        have hcls_eq := Option.some.inj hcls
        rw [← hcls_eq] at hmem
        rcases eclass_union_mem _ _ node hmem with h1 | h2
        · -- node from class1
          cases hcls1 : g.classes[root g.unionFind id1]? with
          | none =>
            simp only [hcls1, Option.getD,
              show (default : EClass Op).nodes = #[] from rfl] at h1
            exact nomatch h1
          | some c1 =>
            simp only [hcls1, Option.getD_some] at h1
            exact hv.2 (root g.unionFind id1) c1
              (by rw [Std.HashMap.get?_eq_getElem?]; exact hcls1) node h1
        · -- node from class2
          cases hcls2 : g.classes[root g.unionFind id2]? with
          | none =>
            simp only [hcls2, Option.getD,
              show (default : EClass Op).nodes = #[] from rfl] at h2
            exact nomatch h2
          | some c2 =>
            simp only [hcls2, Option.getD_some] at h2
            rw [hv.2 (root g.unionFind id2) c2
              (by rw [Std.HashMap.get?_eq_getElem?]; exact hcls2) node h2]
            exact heq.symm
      · -- classId ≠ root1: eclass from g.classes unchanged
        have hcls_orig : g.classes.get? classId = some eclass := by
          simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
            beq_eq_false_iff_ne.mpr hid] at hcls
          rw [Std.HashMap.get?_eq_getElem?]; exact hcls
        exact hv.2 classId eclass hcls_orig node hmem

-- ══════════════════════════════════════════════════════════════════
-- Section 4: canonicalize + processClass consistency
-- ══════════════════════════════════════════════════════════════════

/-- canonicalize preserves ConsistentValuation (only does path compression). -/
theorem canonicalize_consistent (g : EGraph Op) (node : ENode Op)
    (env : Nat → Val) (v : EClassId → Val)
    (hv : ConsistentValuation g env v) (hwf : WellFormed g.unionFind) :
    ConsistentValuation (g.canonicalize node).2 env v := by
  have hroots : ∀ j, root (g.canonicalize node).2.unionFind j = root g.unionFind j :=
    canonicalize_preserves_roots g node hwf
  constructor
  · intro i j hij
    exact hv.1 i j (by rw [← hroots i, ← hroots j]; exact hij)
  · intro classId eclass hcls nd hmem
    rw [canonicalize_classes] at hcls
    exact hv.2 classId eclass hcls nd hmem

/-- processClass preserves ConsistentValuation. -/
theorem processClass_consistent (g : EGraph Op) (classId : EClassId)
    (env : Nat → Val) (v : EClassId → Val)
    (hv : ConsistentValuation g env v) (hwf : WellFormed g.unionFind) :
    ConsistentValuation (g.processClass classId).1 env v := by
  constructor
  · intro i j hij
    have hroots := processClass_preserves_roots g classId hwf
    exact hv.1 i j (by rw [← hroots i, ← hroots j]; exact hij)
  · intro cid cls hcls nd hmem
    rw [processClass_classes] at hcls
    exact hv.2 cid cls hcls nd hmem

-- ══════════════════════════════════════════════════════════════════
-- Section 5: add_node extends ConsistentValuation
-- ══════════════════════════════════════════════════════════════════

/-- Adding a LEAF node that misses the hashcons extends the valuation. -/
theorem add_leaf_miss_consistent (g : EGraph Op) (node : ENode Op)
    (env : Nat → Val) (v : EClassId → Val)
    (hv : ConsistentValuation g env v) (hwf : EGraphWF g)
    (hleaf : node.children = [])
    (hmiss : g.hashcons.get? node = none) :
    ∃ v', ConsistentValuation (g.add node).2 env v' ∧
    v' (g.add node).1 = NodeEval node env v' ∧
    ∀ i, i < g.unionFind.parent.size → v' i = v i := by
  rw [add_leaf_new g node hleaf hmiss]; simp only []
  -- Witness: extend v with the new class mapped to its NodeEval value
  refine ⟨fun i => if i = g.unionFind.parent.size then NodeEval node env v else v i,
    ⟨?_, ?_⟩, ?_, ?_⟩
  · -- UF-consistency
    have hroots : ∀ k, root ⟨g.unionFind.parent.push g.unionFind.parent.size⟩ k =
        root g.unionFind k := root_push_all_eq hwf.uf_wf
    have hrootN : root g.unionFind g.unionFind.parent.size = g.unionFind.parent.size :=
      root_oob g.unionFind g.unionFind.parent.size (Nat.lt_irrefl _)
    have hroot_bnd : ∀ j, j < g.unionFind.parent.size → root g.unionFind j <
        g.unionFind.parent.size := fun j hj => rootD_bounded hwf.uf_wf.1 hj
    intro i j hij; simp only []
    rw [hroots, hroots] at hij
    by_cases hi : i = g.unionFind.parent.size
    · subst hi
      by_cases hj : j = g.unionFind.parent.size
      · subst hj; rfl
      · exfalso; rw [hrootN] at hij
        by_cases hjb : j < g.unionFind.parent.size
        · exact Nat.ne_of_lt (hroot_bnd j hjb) hij.symm
        · exact hj (by rw [root_oob g.unionFind j hjb] at hij; exact hij.symm)
    · by_cases hj : j = g.unionFind.parent.size
      · subst hj; exfalso; rw [hrootN] at hij
        by_cases hib : i < g.unionFind.parent.size
        · exact Nat.ne_of_lt (hroot_bnd i hib) hij
        · exact hi (by rw [root_oob g.unionFind i hib] at hij; exact hij)
      · simp only [hi, hj, ite_false]; exact hv.1 i j hij
  · -- Node-consistency
    intro classId eclass hcls nd hmem; simp only []
    by_cases hid : g.unionFind.parent.size = classId
    · subst hid
      simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
        beq_self_eq_true, ite_true] at hcls
      rw [← Option.some.inj hcls] at hmem
      simp [EClass.singleton] at hmem
      simp only [show g.unionFind.parent.size = g.unionFind.parent.size from rfl, ite_true]
      rw [hmem]
      exact nodeEval_children_eq node env
        (fun i => if i = g.unionFind.parent.size then NodeEval node env v else v i) v
        (fun c hc => by rw [hleaf] at hc; exact nomatch hc)
    · simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] at hcls
      split at hcls
      · rename_i heq; simp at heq; exact absurd heq hid
      · have hcls' : g.classes.get? classId = some eclass := by
          rw [Std.HashMap.get?_eq_getElem?]; exact hcls
        simp only [show classId ≠ g.unionFind.parent.size from Ne.symm hid, ite_false]
        rw [nodeEval_children_eq nd env
          (fun i => if i = g.unionFind.parent.size then NodeEval node env v else v i) v
          (fun c hc => by
            show (if c = g.unionFind.parent.size then _ else _) = _
            rw [if_neg (Nat.ne_of_lt
              (hwf.children_bounded classId eclass hcls' nd hmem c hc))])]
        exact hv.2 classId eclass hcls' nd hmem
  · -- v'(N) = NodeEval node env v'
    simp only [show g.unionFind.parent.size = g.unionFind.parent.size from rfl, ite_true]
    exact (nodeEval_children_eq node env
      (fun i => if i = g.unionFind.parent.size then NodeEval node env v else v i) v
      (fun c hc => by rw [hleaf] at hc; exact nomatch hc)).symm
  · -- Forward preservation
    intro i hi; simp only []
    show (if i = g.unionFind.parent.size then _ else _) = _
    rw [if_neg (Nat.ne_of_lt hi)]

/-- Adding a LEAF node that hits the hashcons preserves the valuation. -/
theorem add_leaf_hit_consistent (g : EGraph Op) (node : ENode Op) (existingId : EClassId)
    (env : Nat → Val) (v : EClassId → Val)
    (hv : ConsistentValuation g env v) (hwf : WellFormed g.unionFind)
    (hleaf : node.children = [])
    (hhit : g.hashcons.get? node = some existingId)
    (hhca : ∃ cls, g.classes.get? existingId = some cls ∧ node ∈ cls.nodes.toList) :
    ConsistentValuation (g.add node).2 env v ∧
    v (g.add node).1 = NodeEval node env v ∧
    ∀ i, i < g.unionFind.parent.size → v i = v i := by
  rw [add_leaf_existing g node existingId hleaf hhit]
  obtain ⟨cls, hcls, hmem⟩ := hhca
  refine ⟨find_consistent g existingId env v hv hwf, ?_, fun _ _ => rfl⟩
  simp [EGraph.find, find_fst_eq_root]
  have heval := hv.2 existingId cls hcls node hmem
  rw [heval]; exact consistent_root_eq' g env v hv hwf existingId

/-- Adding any node with bounded children extends the consistent valuation. -/
theorem add_node_consistent (g : EGraph Op) (node : ENode Op)
    (env : Nat → Val) (v : EClassId → Val)
    (hv : ConsistentValuation g env v) (inv : AddExprInv g)
    (hbnd : ∀ c ∈ node.children, c < g.unionFind.parent.size) :
    ∃ v', ConsistentValuation (g.add node).2 env v'
        ∧ v' (g.add node).1 = NodeEval node env v'
        ∧ ∀ i, i < g.unionFind.parent.size → v' i = v i := by
  simp only [EGraph.add]
  split
  · -- Hit case: canonNode already in hashcons
    rename_i existingId hm
    refine ⟨v, find_consistent _ _ env v
      (canonicalize_consistent g node env v hv inv.uf_wf)
      (canonicalize_uf_wf g node inv.uf_wf), ?_, fun _ _ => rfl⟩
    show v ((g.canonicalize node).2.find existingId).1 = NodeEval node env v
    rw [egraph_find_fst]
    have hcv1 := canonicalize_consistent g node env v hv inv.uf_wf
    have hwf1 := canonicalize_uf_wf g node inv.uf_wf
    rw [canonicalize_hashcons] at hm
    have hev := inv.hashcons_entries_valid _ _ hm
    have hbnd1 : existingId < (g.canonicalize node).2.unionFind.parent.size := by
      rw [canonicalize_uf_size]; exact hev
    have hv_root : v (root (g.canonicalize node).2.unionFind existingId) = v existingId :=
      hcv1.1 _ _ (root_idempotent (g.canonicalize node).2.unionFind existingId hwf1 hbnd1)
    rw [hv_root]
    obtain ⟨cls, hcls, hmem⟩ := inv.hashcons_classes_aligned _ existingId hm
    rw [← nodeEval_canonical g node env v hv.1 inv.uf_wf hbnd]
    exact (hv.2 existingId cls hcls (g.canonicalize node).1 hmem).symm
  · -- Miss case: create new class (all inline, no `set`)
    rename_i hmiss
    simp only [UnionFind.add]
    have hwf1 := canonicalize_uf_wf g node inv.uf_wf
    have hcusz : (g.canonicalize node).2.unionFind.parent.size = g.unionFind.parent.size :=
      canonicalize_uf_size g node
    -- Witness: extend v with the new class
    refine ⟨fun i => if i = g.unionFind.parent.size then NodeEval node env v else v i,
      ⟨?_, ?_⟩, ?_, ?_⟩
    · -- UF-consistency
      have hroots : ∀ k,
          root ⟨(g.canonicalize node).2.unionFind.parent.push
            (g.canonicalize node).2.unionFind.parent.size⟩ k = root g.unionFind k :=
        fun k => ((root_push_all_eq hwf1 k).trans (canonicalize_preserves_roots g node inv.uf_wf k))
      have hrootN : root g.unionFind g.unionFind.parent.size = g.unionFind.parent.size :=
        root_oob g.unionFind _ (Nat.lt_irrefl _)
      have hroot_bnd : ∀ j, j < g.unionFind.parent.size → root g.unionFind j <
          g.unionFind.parent.size := fun j hj => rootD_bounded inv.uf_wf.1 hj
      intro i j hij; simp only []
      rw [hroots, hroots] at hij
      by_cases hi : i = g.unionFind.parent.size
      · subst hi; by_cases hj : j = g.unionFind.parent.size
        · subst hj; rfl
        · exfalso; rw [hrootN] at hij
          by_cases hjb : j < g.unionFind.parent.size
          · exact Nat.ne_of_lt (hroot_bnd j hjb) hij.symm
          · exact hj (by rw [root_oob g.unionFind j hjb] at hij; exact hij.symm)
      · by_cases hj : j = g.unionFind.parent.size
        · subst hj; exfalso; rw [hrootN] at hij
          by_cases hib : i < g.unionFind.parent.size
          · exact Nat.ne_of_lt (hroot_bnd i hib) hij
          · exact hi (by rw [root_oob g.unionFind i hib] at hij; exact hij)
        · simp only [hi, hj, ite_false]; exact hv.1 i j hij
    · -- Node-consistency
      intro classId eclass hcls nd hmem; simp only []
      by_cases hid : g.unionFind.parent.size = classId
      · subst hid
        simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] at hcls
        split at hcls
        · simp at hcls; subst hcls
          simp [EClass.singleton] at hmem; rw [hmem]
          simp only [show g.unionFind.parent.size = g.unionFind.parent.size from rfl, ite_true]
          rw [nodeEval_children_eq (g.canonicalize node).1 env
            (fun i => if i = g.unionFind.parent.size then NodeEval node env v else v i) v
            (fun c hc => by
              show (if c = g.unionFind.parent.size then _ else _) = _
              rw [if_neg (Nat.ne_of_lt
                (canonicalize_output_bounded g node inv.uf_wf hbnd c hc))])]
          exact nodeEval_canonical g node env v hv.1 inv.uf_wf hbnd
        · rename_i hne; simp [hcusz] at hne
      · simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] at hcls
        split at hcls
        · rename_i heq; simp at heq; rw [hcusz] at heq; exact absurd heq hid
        · rw [canonicalize_classes] at hcls
          have hcls' : g.classes.get? classId = some eclass := by
            rw [Std.HashMap.get?_eq_getElem?]; exact hcls
          simp only [show classId ≠ g.unionFind.parent.size from Ne.symm hid, ite_false]
          rw [nodeEval_children_eq nd env
            (fun i => if i = g.unionFind.parent.size then NodeEval node env v else v i) v
            (fun c hc => by
              show (if c = g.unionFind.parent.size then _ else _) = _
              rw [if_neg (Nat.ne_of_lt
                (inv.children_bounded classId eclass hcls' nd hmem c hc))])]
          exact hv.2 classId eclass hcls' nd hmem
    · -- v'(returned ID) = NodeEval node env v'
      simp only [hcusz, show g.unionFind.parent.size = g.unionFind.parent.size from rfl, ite_true]
      exact (nodeEval_children_eq node env
        (fun i => if i = g.unionFind.parent.size then NodeEval node env v else v i) v
        (fun c hc => by
          show (if c = g.unionFind.parent.size then _ else _) = _
          rw [if_neg (Nat.ne_of_lt (hbnd c hc))])).symm
    · -- Forward preservation
      intro i hi; simp only [hcusz]
      show (if i = g.unionFind.parent.size then _ else _) = _
      rw [if_neg (Nat.ne_of_lt hi)]

-- ══════════════════════════════════════════════════════════════════
-- Section 6: processClass merges semantically valid
-- ══════════════════════════════════════════════════════════════════

/-- HCA + ConsistentValuation implies each hashcons entry evaluates correctly. -/
private theorem hashcons_entries_eval (g : EGraph Op) (env : Nat → Val)
    (v : EClassId → Val) (hv : ConsistentValuation g env v)
    (hca : HashconsClassesAligned g) :
    ∀ nd id, g.hashcons.get? nd = some id → NodeEval nd env v = v id := by
  intro nd id hget
  obtain ⟨cls, hcls, hmem⟩ := hca nd id hget
  exact hv.2 id cls hcls nd hmem

/-- processClass emits merge pairs with semantically equal valuations. -/
theorem processClass_merges_semantically_valid (g : EGraph Op) (classId : EClassId)
    (env : Nat → Val) (v : EClassId → Val)
    (hv : ConsistentValuation g env v) (hwf : WellFormed g.unionFind)
    (hca : HashconsClassesAligned g) (hcb : ChildrenBounded g) :
    ∀ (pr : EClassId × EClassId), pr ∈ (g.processClass classId).2 →
      v pr.1 = v pr.2 := by
  unfold EGraph.processClass
  simp only [EGraph.find, find_fst_eq_root]
  split
  · intro pr hp; exact nomatch hp
  · rename_i eclass heclass
    have hcls_canon : g.classes.get? (root g.unionFind classId) = some eclass := by
      rw [Std.HashMap.get?_eq_getElem?]; exact heclass
    have h_base : (∀ pr ∈ ([] : List (EClassId × EClassId)), v pr.1 = v pr.2) ∧
        (∀ k, root (g.unionFind.find classId).2 k = root g.unionFind k) ∧
        WellFormed (g.unionFind.find classId).2 ∧
        (∀ nd id, g.hashcons.get? nd = some id →
          g.hashcons.get? nd = some id ∨ id = root g.unionFind classId) ∧
        (g.unionFind.find classId).2.parent.size = g.unionFind.parent.size :=
      (by constructor
          · intro _ h; exact nomatch h
          · constructor
            · intro k; exact find_preserves_roots g.unionFind classId k hwf
            · constructor
              · exact find_preserves_wf g.unionFind classId hwf
              · constructor
                · intro nd id h; exact Or.inl h
                · exact find_snd_size g.unionFind classId)
    exact (@Array.foldl_induction (ENode Op) (EGraph Op × List (EClassId × EClassId))
      eclass.nodes
      (fun _ (r : EGraph Op × List (EClassId × EClassId)) =>
        (∀ pr ∈ r.2, v pr.1 = v pr.2) ∧
        (∀ k, root r.1.unionFind k = root g.unionFind k) ∧
        WellFormed r.1.unionFind ∧
        (∀ nd id, r.1.hashcons.get? nd = some id →
          g.hashcons.get? nd = some id ∨ id = root g.unionFind classId) ∧
        r.1.unionFind.parent.size = g.unionFind.parent.size)
      _
      h_base
      _
      (fun ⟨i, hi⟩ b ih => by
        obtain ⟨acc, merges⟩ := b
        obtain ⟨ih_sem, ih_roots, ih_wf, ih_hcs, ih_sz⟩ := ih
        dsimp only at ih_sem ih_roots ih_wf ih_hcs ih_sz ⊢
        have a1_hcs := canonicalize_hashcons acc eclass.nodes[i]
        have a1_roots : ∀ k, root (acc.canonicalize eclass.nodes[i]).2.unionFind k =
            root g.unionFind k :=
          fun k => by rw [canonicalize_preserves_roots acc _ ih_wf]; exact ih_roots k
        have a1_wf := canonicalize_uf_wf acc eclass.nodes[i] ih_wf
        have a1_sz : (acc.canonicalize eclass.nodes[i]).2.unionFind.parent.size =
            g.unionFind.parent.size := by
          rw [canonicalize_uf_size]; exact ih_sz
        have a1_hcs_inv : ∀ nd id,
            (acc.canonicalize eclass.nodes[i]).2.hashcons.get? nd = some id →
            g.hashcons.get? nd = some id ∨ id = root g.unionFind classId := by
          intro nd id h; rw [a1_hcs] at h; exact ih_hcs nd id h
        have ins_inv : ∀ nd id,
            (((acc.canonicalize eclass.nodes[i]).2.hashcons.erase eclass.nodes[i]).insert
              (acc.canonicalize eclass.nodes[i]).1 (root g.unionFind classId)).get? nd = some id →
            g.hashcons.get? nd = some id ∨ id = root g.unionFind classId := by
          intro nd id hget
          by_cases hcn : (acc.canonicalize eclass.nodes[i]).1 = nd
          · subst hcn; rw [hashcons_get?_insert_self] at hget
            exact .inr (Option.some.inj hget.symm)
          · rw [hashcons_get?_insert_ne _ _ _ _ hcn] at hget
            by_cases hnn : eclass.nodes[i] = nd
            · subst hnn; rw [hashcons_get?_erase_self] at hget; exact nomatch hget
            · rw [hashcons_get?_erase_ne _ _ _ hnn, a1_hcs] at hget
              exact ih_hcs nd id hget
        split
        · exact ⟨ih_sem, a1_roots, a1_wf, a1_hcs_inv, a1_sz⟩
        · rename_i hne_beq
          have hne : (acc.canonicalize eclass.nodes[i]).1 ≠ eclass.nodes[i] :=
            fun h => hne_beq (beq_iff_eq.mpr h)
          split
          · rename_i existingId hexists
            refine ⟨?_, a1_roots, a1_wf, ins_inv, a1_sz⟩
            intro pr hpr
            simp only [List.mem_cons] at hpr
            rcases hpr with rfl | hpr
            · simp only []
              have hex_acc : acc.hashcons.get? (acc.canonicalize eclass.nodes[i]).1 =
                  some existingId := by
                have h1 : ((acc.canonicalize eclass.nodes[i]).2.hashcons.erase eclass.nodes[i]).get?
                    (acc.canonicalize eclass.nodes[i]).1 = some existingId := hexists
                rw [hashcons_get?_erase_ne _ _ _ hne.symm, a1_hcs] at h1; exact h1
              rcases ih_hcs _ _ hex_acc with hg_orig | hid_eq
              · obtain ⟨cls_ex, hcls_ex, hmem_ex⟩ := hca _ _ hg_orig
                have heval_ex := hv.2 existingId cls_ex hcls_ex _ hmem_ex
                have hmem_i : eclass.nodes[i] ∈ eclass.nodes.toList :=
                  Array.mem_toList_iff.mpr (Array.getElem_mem hi)
                have heval_can := hv.2 _ eclass hcls_canon _ hmem_i
                have huf_acc : ∀ a b, root acc.unionFind a = root acc.unionFind b →
                    v a = v b :=
                  fun a b h => hv.1 a b (by rw [← ih_roots a, ← ih_roots b]; exact h)
                have hbnd_acc : ∀ c ∈ (eclass.nodes[i]).children,
                    c < acc.unionFind.parent.size := by
                  intro c hc; rw [ih_sz]; exact hcb _ eclass hcls_canon _ hmem_i c hc
                have heval_canonical :=
                  nodeEval_canonical acc eclass.nodes[i] env v huf_acc ih_wf hbnd_acc
                exact heval_can.symm.trans (heval_canonical.symm.trans heval_ex)
              · rw [hid_eq]
            · exact ih_sem pr hpr
          · exact ⟨ih_sem, a1_roots, a1_wf, ins_inv, a1_sz⟩)).1

-- ══════════════════════════════════════════════════════════════════
-- Section 7: mergeAll preserves ConsistentValuation
-- ══════════════════════════════════════════════════════════════════

/-- Folding merge over valid pairs preserves ConsistentValuation. -/
theorem mergeAll_consistent : ∀ (merges : List (EClassId × EClassId))
    (g : EGraph Op) (env : Nat → Val) (v : EClassId → Val),
    ConsistentValuation g env v →
    WellFormed g.unionFind →
    (∀ p ∈ merges, v p.1 = v p.2) →
    (∀ p ∈ merges, p.1 < g.unionFind.parent.size ∧ p.2 < g.unionFind.parent.size) →
    ConsistentValuation (merges.foldl (fun acc (id1, id2) => acc.merge id1 id2) g) env v := by
  intro merges
  induction merges with
  | nil => intro _ _ _ hv _ _ _; exact hv
  | cons hd tl ih =>
    intro g env v hv hwf hval hbnd
    simp only [List.foldl_cons]
    have hhd_val := hval hd (.head _)
    have hhd_bnd := hbnd hd (.head _)
    have hv' := merge_consistent g hd.1 hd.2 env v hv hwf hhd_bnd.1 hhd_bnd.2
      (by rw [consistent_root_eq' g env v hv hwf hd.1,
              consistent_root_eq' g env v hv hwf hd.2]; exact hhd_val)
    have hwf' := merge_preserves_uf_wf' g hd.1 hd.2 hwf hhd_bnd.1
    have hsz := merge_uf_size g hd.1 hd.2
    exact ih (g.merge hd.1 hd.2) env v hv' hwf'
      (fun p hp => hval p (.tail _ hp))
      (fun p hp => by rw [hsz]; exact hbnd p (.tail _ hp))

-- ══════════════════════════════════════════════════════════════════
-- Section 8: computeCostsF (total version) + ConsistentValuation
-- ══════════════════════════════════════════════════════════════════

/-- Compute updated bestCost/bestNode for one class. -/
private def updateClassBest (uf : UnionFind) (costFn : ENode Op → Nat)
    (acc : Std.HashMap EClassId (EClass Op)) (eclass : EClass Op)
    : Nat × Option (ENode Op) × Bool :=
  let getCost (id : EClassId) : Nat :=
    match acc.get? (root uf id) with
    | some ec => ec.bestCost
    | none => 1000000000
  eclass.nodes.foldl
    (init := (eclass.bestCost, eclass.bestNode, false))
    fun (curBest, curNode, curChanged) node =>
      let childCosts := node.children.foldl (fun sum cid => sum + getCost cid) 0
      let cost := costFn node + childCosts
      if cost < curBest then (cost, some node, true)
      else (curBest, curNode, curChanged)

/-- Process a list of class IDs, updating bestCost/bestNode. -/
private def processKeys (uf : UnionFind) (costFn : ENode Op → Nat)
    (origClasses : Std.HashMap EClassId (EClass Op))
    : List EClassId → Std.HashMap EClassId (EClass Op) → Bool →
      Std.HashMap EClassId (EClass Op) × Bool
  | [], acc, changed => (acc, changed)
  | classId :: rest, acc, changed =>
    match origClasses.get? classId with
    | none => processKeys uf costFn origClasses rest acc changed
    | some eclass =>
      let r := updateClassBest uf costFn acc eclass
      if r.2.2 then
        processKeys uf costFn origClasses rest
          (acc.insert classId { eclass with bestCost := r.1, bestNode := r.2.1 })
          true
      else
        processKeys uf costFn origClasses rest acc changed

/-- Loop: repeatedly process all keys until convergence or fuel exhaustion. -/
private def computeCostsLoop (uf : UnionFind) (costFn : ENode Op → Nat)
    : Std.HashMap EClassId (EClass Op) → Nat → Std.HashMap EClassId (EClass Op)
  | classes, 0 => classes
  | classes, n + 1 =>
    let (classes', changed) :=
      processKeys uf costFn classes (classes.toList.map Prod.fst) classes false
    if changed then computeCostsLoop uf costFn classes' n
    else classes'

/-- Total fuel-based version of computeCosts. -/
def computeCostsF (g : EGraph Op) (costFn : ENode Op → Nat)
    (fuel : Nat := 100) : EGraph Op :=
  { g with classes := computeCostsLoop g.unionFind costFn g.classes fuel }

/-- computeCostsF preserves the unionFind. -/
theorem computeCostsF_preserves_uf (g : EGraph Op) (costFn : ENode Op → Nat) (fuel : Nat) :
    (computeCostsF g costFn fuel).unionFind = g.unionFind := rfl

-- ── NodesFrom: result entries have same nodes as original ──

private def NodesFrom (origClasses acc : Std.HashMap EClassId (EClass Op)) : Prop :=
  ∀ cid cls, acc.get? cid = some cls →
    ∃ cls_orig, origClasses.get? cid = some cls_orig ∧ cls.nodes = cls_orig.nodes

private theorem nodesFrom_refl (classes : Std.HashMap EClassId (EClass Op)) :
    NodesFrom classes classes :=
  fun _ cls h => ⟨cls, h, rfl⟩

private theorem nodesFrom_trans (a b c : Std.HashMap EClassId (EClass Op))
    (h1 : NodesFrom a b) (h2 : NodesFrom b c) : NodesFrom a c := by
  intro cid cls hget
  obtain ⟨cls_mid, hmid, hn_mid⟩ := h2 cid cls hget
  obtain ⟨cls_orig, horig, hn_orig⟩ := h1 cid cls_mid hmid
  exact ⟨cls_orig, horig, hn_mid.trans hn_orig⟩

private theorem nodesFrom_insert (origClasses acc : Std.HashMap EClassId (EClass Op))
    (classId : EClassId) (eclass : EClass Op) (bestCost : Nat) (bestNode : Option (ENode Op))
    (horig : origClasses.get? classId = some eclass)
    (hacc : NodesFrom origClasses acc) :
    NodesFrom origClasses
      (acc.insert classId { eclass with bestCost := bestCost, bestNode := bestNode }) := by
  intro cid cls hget
  simp [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] at hget
  split at hget
  · rename_i heq
    have heq' : classId = cid := by simpa using heq
    cases Option.some.inj hget
    exact ⟨eclass, heq' ▸ horig, rfl⟩
  · exact hacc cid cls (by simp [Std.HashMap.get?_eq_getElem?]; exact hget)

private theorem processKeys_preserves_nodes (uf : UnionFind) (costFn : ENode Op → Nat)
    (origClasses : Std.HashMap EClassId (EClass Op))
    (keys : List EClassId) (acc : Std.HashMap EClassId (EClass Op)) (changed : Bool)
    (h : NodesFrom origClasses acc) :
    NodesFrom origClasses (processKeys uf costFn origClasses keys acc changed).1 := by
  induction keys generalizing acc changed with
  | nil => exact h
  | cons classId rest ih =>
    simp only [processKeys]
    split
    · exact ih _ _ h
    · rename_i eclass heclass
      split
      · exact ih _ _ (nodesFrom_insert origClasses acc classId eclass _ _
          (by rw [Std.HashMap.get?_eq_getElem?]; exact heclass) h)
      · exact ih _ _ h

private theorem computeCostsLoop_preserves_nodes (uf : UnionFind) (costFn : ENode Op → Nat)
    (origClasses : Std.HashMap EClassId (EClass Op))
    : ∀ (fuel : Nat) (classes : Std.HashMap EClassId (EClass Op)),
      NodesFrom origClasses classes →
      NodesFrom origClasses (computeCostsLoop uf costFn classes fuel)
  | 0, classes, h => h
  | n + 1, classes, h => by
    simp only [computeCostsLoop]
    have hpk := processKeys_preserves_nodes uf costFn classes
      (classes.toList.map Prod.fst) classes false (nodesFrom_refl classes)
    have htr := nodesFrom_trans origClasses classes _ h hpk
    split
    · exact computeCostsLoop_preserves_nodes uf costFn origClasses _ _ htr
    · exact htr

/-- computeCostsF preserves ConsistentValuation. -/
theorem computeCostsF_preserves_consistency (g : EGraph Op) (costFn : ENode Op → Nat)
    (fuel : Nat) (env : Nat → Val) (v : EClassId → Val)
    (hv : ConsistentValuation g env v) :
    ConsistentValuation (computeCostsF g costFn fuel) env v := by
  constructor
  · exact hv.1
  · intro classId eclass hget node hnode
    have hnf := computeCostsLoop_preserves_nodes g.unionFind costFn g.classes fuel
      g.classes (nodesFrom_refl _)
    obtain ⟨cls_orig, horig, hnodes_eq⟩ := hnf classId eclass hget
    rw [hnodes_eq] at hnode
    exact hv.2 classId cls_orig horig node hnode

-- ── BestNodeInv ──

/-- Every bestNode is in the class's nodes array. -/
def BestNodeInv (classes : Std.HashMap EClassId (EClass Op)) : Prop :=
  ∀ cid cls nd, classes.get? cid = some cls →
    cls.bestNode = some nd → nd ∈ cls.nodes.toList

/-- When updateClassBest returns nodeChanged = true, bestNode ∈ nodes. -/
private theorem updateClassBest_bestNode_mem (uf : UnionFind) (costFn : ENode Op → Nat)
    (acc : Std.HashMap EClassId (EClass Op)) (eclass : EClass Op) :
    let r := updateClassBest uf costFn acc eclass
    r.2.2 = true → ∀ nd, r.2.1 = some nd → nd ∈ eclass.nodes.toList := by
  simp only [updateClassBest]
  exact @Array.foldl_induction (ENode Op) (Nat × Option (ENode Op) × Bool)
    eclass.nodes
    (fun _ st => st.2.2 = true → ∀ nd, st.2.1 = some nd → nd ∈ eclass.nodes.toList)
    _
    (fun h => by simp at h)
    _
    (fun ⟨i, hi⟩ ⟨_curBest, _curNode, _curChanged⟩ prev => by
      dsimp only
      split
      · intro _ nd hnd
        cases Option.some.inj hnd
        exact Array.getElem_mem_toList hi
      · exact prev)

private theorem processKeys_preserves_bestNodeInv (uf : UnionFind) (costFn : ENode Op → Nat)
    (origClasses : Std.HashMap EClassId (EClass Op))
    (keys : List EClassId) (acc : Std.HashMap EClassId (EClass Op)) (changed : Bool)
    (h : BestNodeInv acc) :
    BestNodeInv (processKeys uf costFn origClasses keys acc changed).1 := by
  induction keys generalizing acc changed with
  | nil => exact h
  | cons classId rest ih =>
    simp only [processKeys]
    split
    · exact ih _ _ h
    · rename_i eclass heclass
      split
      · apply ih
        intro cid cls nd hget hbn
        simp [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] at hget
        split at hget
        · cases Option.some.inj hget
          exact updateClassBest_bestNode_mem uf costFn acc eclass
            (by assumption) nd hbn
        · exact h cid cls nd
            (by simp [Std.HashMap.get?_eq_getElem?]; exact hget) hbn
      · exact ih _ _ h

private theorem computeCostsLoop_preserves_bestNodeInv (uf : UnionFind) (costFn : ENode Op → Nat)
    : ∀ (fuel : Nat) (classes : Std.HashMap EClassId (EClass Op)),
      BestNodeInv classes →
      BestNodeInv (computeCostsLoop uf costFn classes fuel)
  | 0, classes, h => h
  | n + 1, classes, h => by
    simp only [computeCostsLoop]
    split
    · apply computeCostsLoop_preserves_bestNodeInv
      exact processKeys_preserves_bestNodeInv _ _ _ _ _ _ h
    · exact processKeys_preserves_bestNodeInv _ _ _ _ _ _ h

/-- After computeCostsF, every bestNode is in the class's nodes array. -/
theorem computeCostsF_bestNode_in_nodes (g : EGraph Op) (costFn : ENode Op → Nat) (fuel : Nat)
    (h_inv : BestNodeInv g.classes) :
    ∀ cid cls nd, (computeCostsF g costFn fuel).classes.get? cid = some cls →
      cls.bestNode = some nd → nd ∈ cls.nodes.toList :=
  computeCostsLoop_preserves_bestNodeInv g.unionFind costFn fuel g.classes h_inv

-- ══════════════════════════════════════════════════════════════════
-- Section 9: rebuildF (total version)
-- ══════════════════════════════════════════════════════════════════

/-- Body of one rebuild iteration. -/
def rebuildStepBody (g : EGraph Op) : EGraph Op :=
  let toProcess := g.worklist ++ g.dirtyArr.toList
  let g1 : EGraph Op := { g with worklist := [], dirtyArr := #[] }
  let (g2, pendingMerges) := toProcess.foldl (fun (acc, merges) classId =>
    let (acc', newMerges) := acc.processClass classId
    (acc', newMerges ++ merges)
  ) (g1, [])
  pendingMerges.foldl (fun acc (id1, id2) => acc.merge id1 id2) g2

/-- Fuel-based total version of rebuild. -/
def rebuildF (g : EGraph Op) : Nat → EGraph Op
  | 0 => g
  | fuel + 1 =>
    if g.worklist.isEmpty && g.dirtyArr.isEmpty then g
    else rebuildF (rebuildStepBody g) fuel

/-- rebuildF preserves PostMergeInvariant. -/
theorem rebuildF_preserves_pmi (g : EGraph Op) (fuel : Nat)
    (hpmi : PostMergeInvariant g) :
    PostMergeInvariant (rebuildF g fuel) := by
  induction fuel generalizing g with
  | zero => exact hpmi
  | succ n ih =>
    simp only [rebuildF]
    split
    · exact hpmi
    · apply ih
      exact rebuildStep_preserves_pmi g (g.worklist ++ g.dirtyArr.toList) hpmi

-- ══════════════════════════════════════════════════════════════════
-- Section 10: BestNodeInv Lifecycle
-- ══════════════════════════════════════════════════════════════════

/-- Forward inclusion: elements of ec1.nodes survive in (ec1.union ec2).nodes. -/
private theorem eclass_union_mem_left' (ec1 ec2 : EClass Op) (n : ENode Op)
    (h : n ∈ ec1.nodes.toList) : n ∈ (ec1.union ec2).nodes.toList := by
  simp only [EClass.union]
  exact @Array.foldl_induction (ENode Op) (Array (ENode Op)) ec2.nodes
    (fun _ acc => n ∈ acc.toList) ec1.nodes h
    (fun acc x => if acc.contains x then acc else acc.push x)
    (fun ⟨_, _⟩ b ih => by
      dsimp only; split
      · exact ih
      · rw [Array.toList_push]; exact List.mem_append.mpr (.inl ih))

/-- Forward inclusion for the right operand. -/
private theorem eclass_union_mem_right' (ec1 ec2 : EClass Op) (n : ENode Op)
    (h : n ∈ ec2.nodes.toList) : n ∈ (ec1.union ec2).nodes.toList := by
  simp only [EClass.union]
  have hmem : n ∈ ec2.nodes := Array.mem_toList_iff.mp h
  obtain ⟨k, hk_lt, hk_eq⟩ := Array.mem_iff_getElem.mp hmem
  rw [← hk_eq]
  exact @Array.foldl_induction (ENode Op) (Array (ENode Op)) ec2.nodes
    (fun i acc => ∀ j (hj : j < ec2.nodes.size), j < i → ec2.nodes[j] ∈ acc.toList)
    ec1.nodes
    (fun _ _ hji => absurd hji (Nat.not_lt_zero _))
    (fun acc x => if acc.contains x then acc else acc.push x)
    (fun ⟨i, hi⟩ b prev => by
      intro j hj hjlt
      rcases Nat.lt_succ_iff_lt_or_eq.mp hjlt with hjlt | hjlt
      · have := prev j hj hjlt
        dsimp only; split
        · exact this
        · rw [Array.toList_push]; exact List.mem_append.mpr (.inl this)
      · subst hjlt; dsimp only; split
        · rename_i hc
          exact Array.mem_toList_iff.mpr (Array.mem_of_contains_eq_true hc)
        · rw [Array.toList_push]
          exact List.mem_append.mpr (.inr (List.mem_singleton.mpr rfl)))
    k hk_lt hk_lt

/-- The empty e-graph trivially satisfies BestNodeInv. -/
private theorem bestNodeInv_empty : BestNodeInv (EGraph.empty (Op := Op).classes) := by
  intro cid cls _nd hget
  simp [EGraph.empty, Std.HashMap.get?_eq_getElem?, Std.HashMap.ofList_nil] at hget

/-- Adding a node preserves BestNodeInv. -/
private theorem add_preserves_bestNodeInv (g : EGraph Op) (node : ENode Op)
    (h : BestNodeInv g.classes) :
    BestNodeInv (g.add node).2.classes := by
  simp only [EGraph.add]
  split
  · intro cid cls nd hget hbn
    simp only [EGraph.find] at hget
    rw [canonicalize_classes] at hget
    exact h cid cls nd hget hbn
  · intro cid cls nd hget hbn
    simp only [UnionFind.add] at hget
    by_cases hid : (g.canonicalize node).2.unionFind.parent.size = cid
    · subst hid
      simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
        beq_self_eq_true, ite_true] at hget
      have hcls := Option.some.inj hget
      rw [← hcls] at hbn ⊢
      simp only [EClass.singleton] at hbn ⊢
      have h_eq := Option.some.inj hbn; subst h_eq
      simp [EClass.singleton]
    · simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
        beq_eq_false_iff_ne.mpr hid, ite_false] at hget
      rw [canonicalize_classes] at hget
      exact h cid cls nd (by rw [Std.HashMap.get?_eq_getElem?]; exact hget) hbn

/-- merge preserves BestNodeInv. -/
private theorem merge_preserves_bestNodeInv (g : EGraph Op) (id1 id2 : EClassId)
    (h : BestNodeInv g.classes) :
    BestNodeInv (g.merge id1 id2).classes := by
  unfold EGraph.merge EGraph.find
  simp only [find_fst_eq_root]
  split
  · exact h
  · intro cid cls nd hget hbn
    by_cases hid : g.unionFind.root id1 = cid
    · subst hid
      rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
        if_pos (beq_self_eq_true _)] at hget
      obtain rfl := Option.some.inj hget
      simp only [EClass.union] at hbn
      split at hbn
      · have hnd_mem : nd ∈ (g.classes[g.unionFind.root id1]?.getD default).nodes.toList := by
          cases hc : g.classes[g.unionFind.root id1]? with
          | none => simp [hc, show (default : EClass Op).nodes = #[] from rfl] at hbn
          | some c =>
            simp [hc] at hbn
            exact h _ c nd (by rw [Std.HashMap.get?_eq_getElem?]; exact hc) hbn
        exact eclass_union_mem_left' _ _ _ hnd_mem
      · have hnd_mem : nd ∈ (g.classes[(g.unionFind.find id1).snd.root id2]?.getD default).nodes.toList := by
          cases hc : g.classes[(g.unionFind.find id1).snd.root id2]? with
          | none => simp [hc, show (default : EClass Op).nodes = #[] from rfl] at hbn
          | some c =>
            simp [hc] at hbn
            exact h _ c nd (by rw [Std.HashMap.get?_eq_getElem?]; exact hc) hbn
        exact eclass_union_mem_right' _ _ _ hnd_mem
    · rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
        show (g.unionFind.root id1 == cid) = false from beq_eq_false_iff_ne.mpr hid,
        if_neg (by decide : ¬(false = true))] at hget
      exact h cid cls nd (by rw [Std.HashMap.get?_eq_getElem?]; exact hget) hbn

/-- Folding merge preserves BestNodeInv. -/
private theorem mergeAll_preserves_bestNodeInv :
    ∀ (merges : List (EClassId × EClassId)) (g : EGraph Op),
    BestNodeInv g.classes →
    BestNodeInv (merges.foldl (fun acc (id1, id2) => acc.merge id1 id2) g).classes
  | [], _, h => h
  | (id1, id2) :: tl, g, h => by
    simp only [List.foldl_cons]
    exact mergeAll_preserves_bestNodeInv tl _ (merge_preserves_bestNodeInv g id1 id2 h)

-- ══════════════════════════════════════════════════════════════════
-- Section 11: merge preserves HashconsClassesAligned
-- ══════════════════════════════════════════════════════════════════

/-- Merge preserves HashconsClassesAligned. -/
theorem merge_preserves_hashcons_classes_aligned (g : EGraph Op) (id1 id2 : EClassId)
    (hca : HashconsClassesAligned g) :
    HashconsClassesAligned (g.merge id1 id2) := by
  intro node id hget
  rw [merge_hashcons] at hget
  obtain ⟨cls, hcls, hmem⟩ := hca node id hget
  unfold EGraph.merge; simp only [EGraph.find, find_fst_eq_root]
  split
  · exact ⟨cls, hcls, hmem⟩
  · simp only []
    by_cases hid : root g.unionFind id1 = id
    · subst hid
      simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
        beq_self_eq_true, ↓reduceIte]
      refine ⟨_, rfl, ?_⟩
      have hcls' : g.classes[root g.unionFind id1]? = some cls := by
        rw [← Std.HashMap.get?_eq_getElem?]; exact hcls
      simp only [hcls', Option.getD_some]
      exact eclass_union_mem_left' cls _ node hmem
    · rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
          show (root g.unionFind id1 == id) = false from beq_eq_false_iff_ne.mpr hid,
          if_neg (by decide : ¬(false = true)),
          ← Std.HashMap.get?_eq_getElem?]
      exact ⟨cls, hcls, hmem⟩

-- ══════════════════════════════════════════════════════════════════
-- Section 12: SemanticHashconsInv — weak hashcons invariant for rebuild
-- ══════════════════════════════════════════════════════════════════

/-- Semantic hashcons invariant: every hashcons entry `(nd, id)` satisfies
    `NodeEval nd env v = v (root uf id)`.

    This is strictly weaker than `HashconsClassesAligned ∧ ConsistentValuation`:
    it only captures the semantic consequence, not the structural membership.
    The key property is that SHI is preserved through `processClass`'s hashcons
    updates (erase + insert), whereas `HashconsClassesAligned` breaks during
    the processAll foldl because processClass modifies hashcons without
    updating classes. -/
def SemanticHashconsInv (g : EGraph Op) (env : Nat → Val) (v : EClassId → Val) : Prop :=
  ∀ nd id, g.hashcons.get? nd = some id →
    NodeEval nd env v = v (root g.unionFind id)

/-- SHI is derivable from `HashconsClassesAligned + ConsistentValuation + WellFormed`. -/
theorem hca_cv_implies_shi (g : EGraph Op) (env : Nat → Val) (v : EClassId → Val)
    (hcv : ConsistentValuation g env v) (hwf : WellFormed g.unionFind)
    (hca : HashconsClassesAligned g) :
    SemanticHashconsInv g env v := by
  intro nd id hget
  obtain ⟨cls, hcls, hmem⟩ := hca nd id hget
  exact (hcv.2 id cls hcls nd hmem).trans (consistent_root_eq' g env v hcv hwf id).symm

/-- SHI is derivable from `EGraphWF + ConsistentValuation`. -/
theorem ewf_cv_implies_shi (g : EGraph Op) (env : Nat → Val) (v : EClassId → Val)
    (hwf : EGraphWF g) (hcv : ConsistentValuation g env v) :
    SemanticHashconsInv g env v :=
  hca_cv_implies_shi g env v hcv hwf.uf_wf hwf.hashcons_classes_aligned

/-- SHI holds vacuously for the empty e-graph. -/
theorem empty_shi [Inhabited Val] (env : Nat → Val) :
    SemanticHashconsInv (Op := Op) EGraph.empty env (fun _ => default) := by
  intro nd id h
  simp [EGraph.empty, Std.HashMap.get?_eq_getElem?, Std.HashMap.ofList_nil] at h

omit [LawfulBEq Op] [LawfulHashable Op] in
/-- Clearing worklist/dirtyArr preserves SHI (hashcons and UF unchanged). -/
theorem clear_worklist_shi (g : EGraph Op) (env : Nat → Val) (v : EClassId → Val)
    (hshi : SemanticHashconsInv g env v) :
    SemanticHashconsInv { g with worklist := ([] : List EClassId), dirtyArr := #[] } env v :=
  hshi

/-- merge preserves SHI when the merged classes have equal values.
    merge doesn't change hashcons, and root changes are compatible. -/
theorem merge_preserves_shi (g : EGraph Op) (id1 id2 : EClassId)
    (env : Nat → Val) (v : EClassId → Val)
    (hshi : SemanticHashconsInv g env v)
    (hcv : ConsistentValuation g env v)
    (hwf : WellFormed g.unionFind)
    (h1 : id1 < g.unionFind.parent.size) (h2 : id2 < g.unionFind.parent.size)
    (heq : v (root g.unionFind id1) = v (root g.unionFind id2)) :
    SemanticHashconsInv (g.merge id1 id2) env v := by
  intro nd mid hget
  rw [merge_hashcons] at hget
  have hshi_orig := hshi nd mid hget
  have hcv_merged := merge_consistent g id1 id2 env v hcv hwf h1 h2 heq
  rw [hshi_orig]
  exact (consistent_root_eq' g env v hcv hwf mid).trans
    (consistent_root_eq' (g.merge id1 id2) env v hcv_merged
      (merge_preserves_uf_wf' g id1 id2 hwf h1) mid).symm

/-- mergeAll preserves SHI when CV and WF are threaded alongside.
    Follows the same induction pattern as mergeAll_consistent. -/
theorem mergeAll_preserves_shi : ∀ (merges : List (EClassId × EClassId))
    (g : EGraph Op) (env : Nat → Val) (v : EClassId → Val),
    ConsistentValuation g env v →
    WellFormed g.unionFind →
    SemanticHashconsInv g env v →
    (∀ p ∈ merges, v p.1 = v p.2) →
    (∀ p ∈ merges, p.1 < g.unionFind.parent.size ∧ p.2 < g.unionFind.parent.size) →
    SemanticHashconsInv (merges.foldl (fun acc (id1, id2) => acc.merge id1 id2) g) env v := by
  intro merges
  induction merges with
  | nil => intro _ _ _ _ _ hshi _ _; exact hshi
  | cons hd tl ih =>
    intro g env v hcv hwf hshi hval hbnd
    simp only [List.foldl_cons]
    have hhd_val := hval hd (.head _)
    have hhd_bnd := hbnd hd (.head _)
    have heq : v (root g.unionFind hd.1) = v (root g.unionFind hd.2) := by
      rw [consistent_root_eq' g env v hcv hwf hd.1,
          consistent_root_eq' g env v hcv hwf hd.2]; exact hhd_val
    have hshi' := merge_preserves_shi g hd.1 hd.2 env v hshi hcv hwf hhd_bnd.1 hhd_bnd.2 heq
    have hcv' := merge_consistent g hd.1 hd.2 env v hcv hwf hhd_bnd.1 hhd_bnd.2 heq
    have hwf' := merge_preserves_uf_wf' g hd.1 hd.2 hwf hhd_bnd.1
    have hsz := merge_uf_size g hd.1 hd.2
    exact ih (g.merge hd.1 hd.2) env v hcv' hwf' hshi'
      (fun p hp => hval p (.tail _ hp))
      (fun p hp => by rw [hsz]; exact hbnd p (.tail _ hp))

-- ══════════════════════════════════════════════════════════════════
-- Section 13: processClass preserves SHI + merge validity
-- ══════════════════════════════════════════════════════════════════

/-- processClass preserves SHI and produces semantically valid merge pairs.
    This is the key enabler for closing the rebuildStepBody sorry:
    unlike `processClass_merges_semantically_valid` (which needs HCA),
    this only needs SHI (which IS preserved through processAll's foldl). -/
theorem processClass_shi_combined (g : EGraph Op) (classId : EClassId)
    (env : Nat → Val) (v : EClassId → Val)
    (hcv : ConsistentValuation g env v)
    (hshi : SemanticHashconsInv g env v)
    (hpmi : PostMergeInvariant g) :
    SemanticHashconsInv (g.processClass classId).1 env v ∧
    (∀ pr ∈ (g.processClass classId).2,
      v (root g.unionFind pr.1) = v (root g.unionFind pr.2)) := by
  unfold EGraph.processClass
  simp only [EGraph.find, find_fst_eq_root]
  -- g1 = {g with uf := find(uf, classId).2}, canonId = root g.uf classId
  have g1_roots : ∀ k, root (g.unionFind.find classId).2 k = root g.unionFind k :=
    fun k => find_preserves_roots g.unionFind classId k hpmi.uf_wf
  have g1_wf : WellFormed (g.unionFind.find classId).2 :=
    find_preserves_wf g.unionFind classId hpmi.uf_wf
  have g1_sz : (g.unionFind.find classId).2.parent.size = g.unionFind.parent.size :=
    find_snd_size g.unionFind classId
  split
  · -- none: no class found
    exact ⟨fun nd id hget => by rw [hshi nd id hget]; congr 1; exact (g1_roots id).symm,
      fun _ h => nomatch h⟩
  · -- some eclass
    rename_i eclass heclass
    have hcls_canon : g.classes.get? (root g.unionFind classId) = some eclass := by
      rwa [Std.HashMap.get?_eq_getElem?]
    have canonId_bnd : root g.unionFind classId < g.unionFind.parent.size := by
      apply hpmi.classes_entries_valid
      rw [Std.HashMap.contains_eq_isSome_getElem?,
          show g.classes[root g.unionFind classId]? =
            g.classes.get? (root g.unionFind classId) from
            (Std.HashMap.get?_eq_getElem? ..).symm,
          hcls_canon]; rfl
    -- Thread ((SHI ∧ merges_valid), roots, wf, size) through the inner foldl
    -- Group first two conjuncts so .1 matches the goal
    have h_base :
        (fun (r : EGraph Op × List (EClassId × EClassId)) =>
          (SemanticHashconsInv r.1 env v ∧ (∀ pr ∈ r.2, v (root g.unionFind pr.1) = v (root g.unionFind pr.2))) ∧
          (∀ k, root r.1.unionFind k = root g.unionFind k) ∧
          WellFormed r.1.unionFind ∧
          r.1.unionFind.parent.size = g.unionFind.parent.size)
        ({ unionFind := (g.unionFind.find classId).2, hashcons := g.hashcons,
           classes := g.classes, worklist := g.worklist, dirtyArr := g.dirtyArr }, []) :=
      ⟨⟨(fun nd id hget => by rw [hshi nd id hget]; congr 1; exact (g1_roots id).symm),
        (fun _ h => nomatch h)⟩, (fun k => g1_roots k), g1_wf, g1_sz⟩
    exact (@Array.foldl_induction (ENode Op) (EGraph Op × List (EClassId × EClassId))
      eclass.nodes
      (fun _ (r : EGraph Op × List (EClassId × EClassId)) =>
        (SemanticHashconsInv r.1 env v ∧ (∀ pr ∈ r.2, v (root g.unionFind pr.1) = v (root g.unionFind pr.2))) ∧
        (∀ k, root r.1.unionFind k = root g.unionFind k) ∧
        WellFormed r.1.unionFind ∧
        r.1.unionFind.parent.size = g.unionFind.parent.size)
      _
      h_base
      _
      (fun ⟨i, hi⟩ b ih => by
        obtain ⟨acc, merges⟩ := b
        obtain ⟨⟨ih_shi, ih_sem⟩, ih_roots, ih_wf, ih_sz⟩ := ih
        dsimp only at ih_shi ih_sem ih_roots ih_wf ih_sz ⊢
        -- Properties after canonicalize
        have a1_hcs := canonicalize_hashcons acc eclass.nodes[i]
        have a1_roots : ∀ k, root (acc.canonicalize eclass.nodes[i]).2.unionFind k =
            root g.unionFind k :=
          fun k => by rw [canonicalize_preserves_roots acc _ ih_wf]; exact ih_roots k
        have a1_wf := canonicalize_uf_wf acc eclass.nodes[i] ih_wf
        have a1_sz : (acc.canonicalize eclass.nodes[i]).2.unionFind.parent.size =
            g.unionFind.parent.size := by
          rw [canonicalize_uf_size]; exact ih_sz
        -- SHI for acc1 (canonicalize doesn't change hashcons)
        have a1_shi : SemanticHashconsInv (acc.canonicalize eclass.nodes[i]).2 env v := by
          intro nd id hget; rw [a1_hcs] at hget
          have := ih_shi nd id hget
          rw [this]; congr 1; exact (ih_roots id).trans (a1_roots id).symm
        -- Derive UF-consistency of v from root preservation
        have acc_cv : ∀ a b, root acc.unionFind a = root acc.unionFind b → v a = v b :=
          fun a b h => hcv.1 a b (by rw [← ih_roots a, ← ih_roots b]; exact h)
        -- Children bounded in acc
        have hmem_i : eclass.nodes[i] ∈ eclass.nodes.toList :=
          Array.mem_toList_iff.mpr (Array.getElem_mem hi)
        have hbnd_i : ∀ c ∈ (eclass.nodes[i]).children, c < acc.unionFind.parent.size := by
          intro c hc; rw [ih_sz]
          exact hpmi.children_bounded _ eclass hcls_canon _ hmem_i c hc
        -- nodeEval_canonical + CV combined
        have heval_canon : NodeEval (acc.canonicalize eclass.nodes[i]).1 env v =
            v (root g.unionFind classId) :=
          (nodeEval_canonical acc eclass.nodes[i] env v acc_cv ih_wf hbnd_i).trans
            (hcv.2 (root g.unionFind classId) eclass hcls_canon _ hmem_i)
        split
        · -- Case 1: canonNode == node, no hashcons change
          exact ⟨⟨a1_shi, ih_sem⟩, a1_roots, a1_wf, a1_sz⟩
        · -- Case 2: canonNode ≠ node
          rename_i hne_beq
          -- SHI for erased hashcons
          have erase_shi : ∀ nd id,
              ((acc.canonicalize eclass.nodes[i]).2.hashcons.erase eclass.nodes[i]).get? nd =
                some id →
              NodeEval nd env v = v (root g.unionFind id) := by
            intro nd id hget
            by_cases hnn : eclass.nodes[i] = nd
            · subst hnn; rw [hashcons_get?_erase_self] at hget; exact nomatch hget
            · rw [hashcons_get?_erase_ne _ _ _ hnn, a1_hcs] at hget
              rw [ih_shi nd id hget, ih_roots]
          -- SHI for inserted hashcons
          have insert_shi : ∀ nd id,
              (((acc.canonicalize eclass.nodes[i]).2.hashcons.erase eclass.nodes[i]).insert
                (acc.canonicalize eclass.nodes[i]).1 (root g.unionFind classId)).get? nd =
                some id →
              NodeEval nd env v = v (root g.unionFind id) := by
            intro nd id hget
            by_cases hcn : (acc.canonicalize eclass.nodes[i]).1 = nd
            · subst hcn; rw [hashcons_get?_insert_self] at hget
              rw [heval_canon, Option.some.inj hget.symm]
              exact (consistent_root_eq' g env v hcv hpmi.uf_wf (root g.unionFind classId)).symm
            · rw [hashcons_get?_insert_ne _ _ _ _ hcn] at hget
              exact erase_shi nd id hget
          -- SHI for the new graph with updated hashcons
          have new_shi : SemanticHashconsInv
              { (acc.canonicalize eclass.nodes[i]).2 with
                hashcons := ((acc.canonicalize eclass.nodes[i]).2.hashcons.erase eclass.nodes[i]).insert
                  (acc.canonicalize eclass.nodes[i]).1 (root g.unionFind classId) } env v := by
            intro nd id hget; simp only [] at hget
            rw [insert_shi nd id hget, a1_roots]
          split
          · -- Subcase: existing entry found → emit merge
            rename_i existingId hexists
            refine ⟨⟨new_shi, ?_⟩, a1_roots, a1_wf, a1_sz⟩
            intro pr hpr
            simp only [List.mem_cons] at hpr
            rcases hpr with rfl | hpr
            · simp only []
              have h_ex := erase_shi _ _ hexists
              exact (consistent_root_eq' g env v hcv hpmi.uf_wf (root g.unionFind classId)).trans
                (heval_canon.symm.trans h_ex)
            · exact ih_sem pr hpr
          · -- Subcase: no existing entry
            exact ⟨⟨new_shi, ih_sem⟩, a1_roots, a1_wf, a1_sz⟩)).1

-- ══════════════════════════════════════════════════════════════════
-- Section 14: rebuildStepBody preserves CV (closes sorry)
-- ══════════════════════════════════════════════════════════════════

/-- processAll preserves CV + SHI and produces valid merge pairs.
    Threads (CV, SHI, PMI, merge_validity, roots_eq, size_eq) through the foldl. -/
theorem processAll_preserves_cv_shi : ∀ (toProcess : List EClassId)
    (g : EGraph Op) (merges : List (EClassId × EClassId))
    (env : Nat → Val) (v : EClassId → Val),
    ConsistentValuation g env v →
    PostMergeInvariant g →
    SemanticHashconsInv g env v →
    (∀ pr ∈ merges, v (root g.unionFind pr.1) = v (root g.unionFind pr.2)) →
    let result := toProcess.foldl
      (fun (am : EGraph Op × List (EClassId × EClassId)) (cid : EClassId) =>
        ((am.1.processClass cid).1, (am.1.processClass cid).2 ++ am.2))
      (g, merges)
    ConsistentValuation result.1 env v ∧
    SemanticHashconsInv result.1 env v ∧
    (∀ pr ∈ result.2, v (root g.unionFind pr.1) = v (root g.unionFind pr.2)) ∧
    (∀ k, root result.1.unionFind k = root g.unionFind k) := by
  intro toProcess
  induction toProcess with
  | nil => intro g merges env v hcv _ hshi hm; exact ⟨hcv, hshi, hm, fun _ => rfl⟩
  | cons cid rest ih =>
    intro g merges env v hcv hpmi hshi hm
    simp only [List.foldl_cons]
    have hcv' := processClass_consistent g cid env v hcv hpmi.uf_wf
    have hpmi' := processClass_preserves_pmi g cid hpmi
    have ⟨hshi', hmerges'⟩ := processClass_shi_combined g cid env v hcv hshi hpmi
    have hroots := processClass_preserves_roots g cid hpmi.uf_wf
    have hm' : ∀ pr ∈ (g.processClass cid).2 ++ merges,
        v (root g.unionFind pr.1) = v (root g.unionFind pr.2) := by
      intro pr hpr
      simp only [List.mem_append] at hpr
      rcases hpr with hpr | hpr
      · exact hmerges' pr hpr
      · exact hm pr hpr
    have hm_adj : ∀ pr ∈ (g.processClass cid).2 ++ merges,
        v (root (g.processClass cid).1.unionFind pr.1) =
        v (root (g.processClass cid).1.unionFind pr.2) := by
      intro pr hpr; rw [hroots pr.1, hroots pr.2]; exact hm' pr hpr
    have ⟨hcv_final, hshi_final, hm_final, hroots_final⟩ :=
      ih (g.processClass cid).1 ((g.processClass cid).2 ++ merges) env v
        hcv' hpmi' hshi' hm_adj
    refine ⟨hcv_final, hshi_final, fun pr hpr => ?_, fun k => ?_⟩
    · have := hm_final pr hpr; simp only [hroots] at this; exact this
    · rw [hroots_final, hroots]

/-- Core rebuild fact: processAll then mergeAll preserves the triple. -/
private theorem rebuildStep_preserves_triple_aux (g1 : EGraph Op)
    (toProcess : List EClassId) (env : Nat → Val) (v : EClassId → Val)
    (hcv : ConsistentValuation g1 env v)
    (hpmi : PostMergeInvariant g1)
    (hshi : SemanticHashconsInv g1 env v) :
    let pa := toProcess.foldl
      (fun (am : EGraph Op × List (EClassId × EClassId)) (cid : EClassId) =>
        ((am.1.processClass cid).1, (am.1.processClass cid).2 ++ am.2))
      (g1, ([] : List (EClassId × EClassId)))
    ConsistentValuation (pa.2.foldl (fun acc (id1, id2) => acc.merge id1 id2) pa.1) env v ∧
    PostMergeInvariant (pa.2.foldl (fun acc (id1, id2) => acc.merge id1 id2) pa.1) ∧
    SemanticHashconsInv (pa.2.foldl (fun acc (id1, id2) => acc.merge id1 id2) pa.1) env v := by
  intro pa
  have ⟨hcv2, hshi2, hmerges_valid, hroots2⟩ := processAll_preserves_cv_shi
    toProcess g1 [] env v hcv hpmi hshi (fun _ h => nomatch h)
  have ⟨hpmi2, hsize2, hbnd2⟩ := processAll_preserves_pmi toProcess g1 []
    hpmi (fun _ h => nomatch h)
  have hval : ∀ p ∈ pa.2, v p.1 = v p.2 := by
    intro p hp
    have hroot := hmerges_valid p hp
    have hcre1 := consistent_root_eq' pa.1 env v hcv2 hpmi2.uf_wf p.1
    have hcre2 := consistent_root_eq' pa.1 env v hcv2 hpmi2.uf_wf p.2
    calc v p.1
        _ = v (root pa.1.unionFind p.1) := hcre1.symm
        _ = v (root g1.unionFind p.1) := by congr 1; exact hroots2 p.1
        _ = v (root g1.unionFind p.2) := hroot
        _ = v (root pa.1.unionFind p.2) := by congr 1; exact (hroots2 p.2).symm
        _ = v p.2 := hcre2
  have hbnd_sz : ∀ p ∈ pa.2,
      p.1 < pa.1.unionFind.parent.size ∧ p.2 < pa.1.unionFind.parent.size := by
    intro p hp; rw [hsize2]; exact hbnd2 p hp
  exact ⟨mergeAll_consistent pa.2 pa.1 env v hcv2 hpmi2.uf_wf hval hbnd_sz,
    mergeAll_preserves_pmi pa.2 pa.1 hpmi2 hbnd_sz,
    mergeAll_preserves_shi pa.2 pa.1 env v hcv2 hpmi2.uf_wf hshi2 hval hbnd_sz⟩

/-- rebuildStepBody preserves ConsistentValuation (same v), using SHI.
    Also preserves PostMergeInvariant and SemanticHashconsInv for threading. -/
theorem rebuildStepBody_preserves_triple (g : EGraph Op)
    (env : Nat → Val) (v : EClassId → Val)
    (hcv : ConsistentValuation g env v)
    (hpmi : PostMergeInvariant g)
    (hshi : SemanticHashconsInv g env v) :
    ConsistentValuation (rebuildStepBody g) env v ∧
    PostMergeInvariant (rebuildStepBody g) ∧
    SemanticHashconsInv (rebuildStepBody g) env v :=
  rebuildStep_preserves_triple_aux
    { g with worklist := [], dirtyArr := #[] }
    (g.worklist ++ g.dirtyArr.toList) env v
    hcv (clear_worklist_pmi g hpmi) (clear_worklist_shi g env v hshi)

end LambdaSat
