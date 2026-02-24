/-
  LambdaSat — Saturation Specification
  Fase 5 Subfase 3-5: Total instantiateF/ematchF + soundness proofs.

  Key components:
  - `instantiateF`: total (fuel-based) pattern instantiation
  - `ematchF`: total (fuel-based) e-matching
  - `applyRuleAtF`: fuel-based rule application
  - `saturateF`: fuel-based saturation loop
  - Soundness theorems for each operation (Opcion A: assumes valid rule application)

  Generalized from VR1CS-Lean v1.3.0 SemanticSpec.lean:1656-1962.
-/
import LambdaSat.SoundRule

namespace LambdaSat

open UnionFind

-- ══════════════════════════════════════════════════════════════════
-- Section 0: ReplaceChildrenSound — interface law for replaceChildren
-- ══════════════════════════════════════════════════════════════════

/-- Law: children of `replaceChildren op ids` come from `ids`.
    Any reasonable NodeOps instance satisfies this. Required for
    instantiateF soundness proofs. -/
def ReplaceChildrenSound (Op : Type) [NodeOps Op] : Prop :=
  ∀ (op : Op) (ids : List EClassId),
    ∀ c ∈ NodeOps.children (NodeOps.replaceChildren op ids), c ∈ ids

-- ══════════════════════════════════════════════════════════════════
-- Section 1: instantiateF — Total pattern instantiation (fuel-based)
-- ══════════════════════════════════════════════════════════════════

variable {Op : Type} [NodeOps Op] [BEq Op] [Hashable Op]

/-- Total pattern instantiation. Given a pattern and a substitution,
    add the corresponding nodes to the e-graph.
    Uses fuel for termination (nested inductive Pattern Op requires it).

    Port of vr1cs SemanticSpec:1656-1688, simplified from 8 cases to 2. -/
def instantiateF (fuel : Nat) (g : EGraph Op) (pattern : Pattern Op)
    (subst : Substitution) : Option (EClassId × EGraph Op) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match pattern with
    | .patVar pv =>
      match subst.lookup pv with
      | some id => some (id, g)
      | none => none
    | .node skelOp subpats =>
      let rec go (g : EGraph Op) (pats : List (Pattern Op))
          (ids : List EClassId) : Option (List EClassId × EGraph Op) :=
        match pats with
        | [] => some (ids.reverse, g)
        | p :: ps =>
          match instantiateF fuel g p subst with
          | none => none
          | some (id, g') => go g' ps (id :: ids)
      match go g subpats [] with
      | none => none
      | some (childIds, g') =>
        some (g'.add ⟨NodeOps.replaceChildren skelOp childIds⟩)

-- Equation lemmas for instantiateF (needed because let rec go blocks default unfolding)
@[simp] theorem instantiateF_zero (g : EGraph Op) (pat : Pattern Op)
    (subst : Substitution) : instantiateF 0 g pat subst = none := by
  cases pat <;> rfl

@[simp] theorem instantiateF_succ_patVar (n : Nat) (g : EGraph Op) (pv : PatVarId)
    (subst : Substitution) :
    instantiateF (n + 1) g (.patVar pv) subst =
    (match subst.lookup pv with | some id => some (id, g) | none => none) := rfl

@[simp] theorem instantiateF_succ_node (n : Nat) (g : EGraph Op) (skelOp : Op)
    (subpats : List (Pattern Op)) (subst : Substitution) :
    instantiateF (n + 1) g (.node skelOp subpats) subst =
    (match instantiateF.go subst n g subpats [] with
      | none => none
      | some (childIds, g') => some (g'.add ⟨NodeOps.replaceChildren skelOp childIds⟩)) := rfl

-- ══════════════════════════════════════════════════════════════════
-- Section 2: instantiateF preserves AddExprInv
-- ══════════════════════════════════════════════════════════════════

variable [LawfulBEq Op] [LawfulHashable Op]

-- instantiateF.go : Substitution → Nat → EGraph Op → List (Pattern Op) → List EClassId → ...

set_option linter.unusedSectionVars false in
/-- Helper: the inner `go` of instantiateF preserves AddExprInv. -/
private theorem instantiateF_go_preserves_addExprInv (subst : Substitution) (fuel : Nat)
    (ih : ∀ (g0 : EGraph Op) (pat0 : Pattern Op) (_inv0 : AddExprInv g0)
      (_h_s0 : ∀ pv id, subst.get? pv = some id → id < g0.unionFind.parent.size),
      ∀ id g', instantiateF fuel g0 pat0 subst = some (id, g') →
      AddExprInv g' ∧ id < g'.unionFind.parent.size ∧
      g0.unionFind.parent.size ≤ g'.unionFind.parent.size)
    (g : EGraph Op) (pats : List (Pattern Op)) (ids : List EClassId)
    (inv : AddExprInv g)
    (h_subst : ∀ pv id, subst.get? pv = some id → id < g.unionFind.parent.size)
    (h_ids : ∀ id ∈ ids, id < g.unionFind.parent.size) :
    ∀ resultIds g', instantiateF.go subst fuel g pats ids = some (resultIds, g') →
    AddExprInv g' ∧ g.unionFind.parent.size ≤ g'.unionFind.parent.size ∧
    (∀ id ∈ resultIds, id < g'.unionFind.parent.size) := by
  induction pats generalizing g ids with
  | nil =>
    intro resultIds g' h
    simp only [instantiateF.go] at h
    have ⟨h1, h2⟩ := Prod.mk.inj (Option.some.inj h)
    subst h2; subst h1
    exact ⟨inv, Nat.le_refl _, fun id hid => h_ids id (List.mem_reverse.mp hid)⟩
  | cons p ps ihgo =>
    intro resultIds g' h
    simp only [instantiateF.go] at h
    split at h
    · exact absurd h (by simp)
    · rename_i id1 g1 h1
      have ⟨inv1, hbnd1, hsize1⟩ := ih g p inv h_subst id1 g1 h1
      have h_subst1 : ∀ pv id, subst.get? pv = some id → id < g1.unionFind.parent.size :=
        fun pv id hs => Nat.lt_of_lt_of_le (h_subst pv id hs) hsize1
      have h_ids1 : ∀ id ∈ id1 :: ids, id < g1.unionFind.parent.size := by
        intro id hid; simp only [List.mem_cons] at hid
        rcases hid with rfl | hid
        · exact hbnd1
        · exact Nat.lt_of_lt_of_le (h_ids id hid) hsize1
      have ⟨inv', hsize', hbnds'⟩ := ihgo g1 (id1 :: ids) inv1 h_subst1 h_ids1
        resultIds g' h
      exact ⟨inv', Nat.le_trans hsize1 hsize', hbnds'⟩

attribute [local irreducible] EGraph.add in
/-- instantiateF preserves AddExprInv. Each recursive call uses g.add
    which preserves AddExprInv. Requires substitution IDs to be bounded.

    Port of vr1cs SemanticSpec:1763-1851, simplified to 2 pattern cases. -/
theorem instantiateF_preserves_addExprInv (fuel : Nat) (g : EGraph Op) (pat : Pattern Op)
    (subst : Substitution) (inv : AddExprInv g)
    (hrc : ReplaceChildrenSound Op)
    (h_subst : ∀ pv id, subst.get? pv = some id → id < g.unionFind.parent.size) :
    ∀ id g', instantiateF fuel g pat subst = some (id, g') →
    AddExprInv g' ∧ id < g'.unionFind.parent.size ∧
    g.unionFind.parent.size ≤ g'.unionFind.parent.size := by
  induction fuel generalizing g pat with
  | zero =>
    intro id g' h
    simp [instantiateF_zero] at h
  | succ n ih =>
    intro id g' h
    cases pat with
    | patVar pv =>
      simp only [instantiateF_succ_patVar, Substitution.lookup] at h
      split at h
      · rename_i existId hget
        have heq := Prod.mk.inj (Option.some.inj h)
        rw [← heq.1, ← heq.2]
        exact ⟨inv, h_subst pv existId hget, Nat.le_refl _⟩
      · exact absurd h nofun
    | node skelOp subpats =>
      simp only [instantiateF_succ_node] at h
      split at h
      · exact absurd h nofun
      · rename_i childIds g1 hgo
        have heq := Prod.mk.inj (Option.some.inj h)
        rw [← heq.1, ← heq.2]
        have ⟨inv1, hsize1, hbnds1⟩ := instantiateF_go_preserves_addExprInv
          subst n (fun g0 pat0 inv0 hs0 => ih g0 pat0 inv0 hs0)
          g subpats [] inv h_subst (fun _ => nofun)
          childIds g1 hgo
        have hchildren_bnd : ∀ c ∈ (⟨NodeOps.replaceChildren skelOp childIds⟩ : ENode Op).children,
            c < g1.unionFind.parent.size := by
          intro c hc
          simp only [ENode.children] at hc
          exact hbnds1 c (hrc skelOp childIds c hc)
        exact ⟨add_preserves_add_expr_inv g1 _ inv1 hchildren_bnd,
               add_id_bounded g1 _ inv1,
               Nat.le_trans hsize1 (add_uf_size_ge g1 _)⟩

-- ══════════════════════════════════════════════════════════════════
-- Section 3: instantiateF preserves ConsistentValuation
-- ══════════════════════════════════════════════════════════════════

variable {Val : Type} [NodeSemantics Op Val]

set_option linter.unusedSectionVars false in
/-- Helper: the inner `go` of instantiateF preserves ConsistentValuation. -/
private theorem instantiateF_go_preserves_consistency (subst : Substitution) (fuel : Nat)
    (env : Nat → Val)
    (_hrc : ReplaceChildrenSound Op)
    (ih_cv : ∀ (g0 : EGraph Op) (pat0 : Pattern Op) (v0 : EClassId → Val)
      (_hv0 : ConsistentValuation g0 env v0) (_inv0 : AddExprInv g0)
      (_h_s0 : ∀ pv id, subst.get? pv = some id → id < g0.unionFind.parent.size),
      ∀ id g', instantiateF fuel g0 pat0 subst = some (id, g') →
      ∃ v', ConsistentValuation g' env v' ∧
        ∀ i, i < g0.unionFind.parent.size → v' i = v0 i)
    (ih_inv : ∀ (g0 : EGraph Op) (pat0 : Pattern Op) (_inv0 : AddExprInv g0)
      (_h_s0 : ∀ pv id, subst.get? pv = some id → id < g0.unionFind.parent.size),
      ∀ id g', instantiateF fuel g0 pat0 subst = some (id, g') →
      AddExprInv g' ∧ id < g'.unionFind.parent.size ∧
      g0.unionFind.parent.size ≤ g'.unionFind.parent.size)
    (g : EGraph Op) (pats : List (Pattern Op)) (ids : List EClassId)
    (v : EClassId → Val) (hv : ConsistentValuation g env v) (inv : AddExprInv g)
    (h_subst : ∀ pv id, subst.get? pv = some id → id < g.unionFind.parent.size) :
    ∀ resultIds g', instantiateF.go subst fuel g pats ids = some (resultIds, g') →
    ∃ v', ConsistentValuation g' env v' ∧
      ∀ i, i < g.unionFind.parent.size → v' i = v i := by
  induction pats generalizing g v ids with
  | nil =>
    intro resultIds g' h
    simp only [instantiateF.go] at h
    have ⟨_, h2⟩ := Prod.mk.inj (Option.some.inj h)
    subst h2; exact ⟨v, hv, fun _ _ => rfl⟩
  | cons p ps ihgo =>
    intro resultIds g' h
    simp only [instantiateF.go] at h
    split at h
    · exact absurd h nofun
    · rename_i id1 g1 h1
      obtain ⟨v1, hcv1, hfp1⟩ := ih_cv g p v hv inv h_subst id1 g1 h1
      have ⟨inv1, _, hsize1⟩ := ih_inv g p inv h_subst id1 g1 h1
      have h_subst1 : ∀ pv id, subst.get? pv = some id → id < g1.unionFind.parent.size :=
        fun pv id hs => Nat.lt_of_lt_of_le (h_subst pv id hs) hsize1
      obtain ⟨v', hcv', hfp'⟩ := ihgo g1 (id1 :: ids) v1 hcv1 inv1 h_subst1
        resultIds g' h
      exact ⟨v', hcv', fun i hi =>
        (hfp' i (Nat.lt_of_lt_of_le hi hsize1)).trans (hfp1 i hi)⟩

attribute [local irreducible] EGraph.add in
/-- instantiateF preserves ConsistentValuation. Each add call extends
    the valuation consistently.

    Port of vr1cs SemanticSpec:1854-1962, simplified to 2 pattern cases.
    Uses L-369 pattern: threading ∃v' through recursive calls. -/
theorem instantiateF_preserves_consistency (fuel : Nat) (g : EGraph Op) (pat : Pattern Op)
    (subst : Substitution) (env : Nat → Val) (v : EClassId → Val)
    (hv : ConsistentValuation g env v) (inv : AddExprInv g)
    (hrc : ReplaceChildrenSound Op)
    (h_subst : ∀ pv id, subst.get? pv = some id → id < g.unionFind.parent.size) :
    ∀ id g', instantiateF fuel g pat subst = some (id, g') →
    ∃ v', ConsistentValuation g' env v' ∧
      ∀ i, i < g.unionFind.parent.size → v' i = v i := by
  induction fuel generalizing g v pat with
  | zero =>
    intro id g' h
    simp [instantiateF_zero] at h
  | succ n ih =>
    intro id g' h
    cases pat with
    | patVar pv =>
      simp only [instantiateF_succ_patVar, Substitution.lookup] at h
      split at h
      · rename_i existId hget
        have ⟨_, h_g⟩ := Prod.mk.inj (Option.some.inj h)
        subst h_g; exact ⟨v, hv, fun _ _ => rfl⟩
      · exact absurd h nofun
    | node skelOp subpats =>
      simp only [instantiateF_succ_node] at h
      split at h
      · exact absurd h nofun
      · rename_i childIds g1 hgo
        rw [← (Prod.mk.inj (Option.some.inj h)).2]
        -- Get consistency from go
        obtain ⟨v1, hcv1, hfp1⟩ := instantiateF_go_preserves_consistency subst n env
          hrc (fun g0 pat0 v0 hv0 inv0 hs0 => ih g0 pat0 v0 hv0 inv0 hs0)
          (fun g0 pat0 inv0 hs0 =>
            instantiateF_preserves_addExprInv n g0 pat0 subst inv0 hrc hs0)
          g subpats [] v hv inv h_subst childIds g1 hgo
        -- Get invariant for add
        have ⟨inv1, hsize1, hbnds1⟩ := instantiateF_go_preserves_addExprInv subst n
          (fun g0 pat0 inv0 hs0 =>
            instantiateF_preserves_addExprInv n g0 pat0 subst inv0 hrc hs0)
          g subpats [] inv h_subst (fun _ => nofun)
          childIds g1 hgo
        have hchildren_bnd : ∀ c ∈ (⟨NodeOps.replaceChildren skelOp childIds⟩ : ENode Op).children,
            c < g1.unionFind.parent.size := by
          intro c hc; simp only [ENode.children] at hc
          exact hbnds1 c (hrc skelOp childIds c hc)
        obtain ⟨v2, hcv2, _, hfp2⟩ := add_node_consistent g1
          ⟨NodeOps.replaceChildren skelOp childIds⟩ env v1 hcv1 inv1 hchildren_bnd
        exact ⟨v2, hcv2, fun i hi =>
          (hfp2 i (Nat.lt_of_lt_of_le hi hsize1)).trans (hfp1 i hi)⟩

-- ══════════════════════════════════════════════════════════════════
-- Section 4: ematchF — Total e-matching (fuel-based)
-- ══════════════════════════════════════════════════════════════════

/-- Total version of `ematch` — fuel-based. Uses `root` instead of `find`
    to avoid side effects (path compression).

    Port of vr1cs SemanticSpec:1692-1758, generalized via sameShape + children. -/
def ematchF (fuel : Nat) (g : EGraph Op) (pattern : Pattern Op)
    (classId : EClassId) (subst : Substitution := .empty) : MatchResult :=
  match fuel with
  | 0 => []
  | fuel + 1 =>
    let canonId := root g.unionFind classId
    match pattern with
    | .patVar pv =>
      match subst.extend pv canonId with
      | some s => [s]
      | none => []
    | .node skelOp subpats =>
      match g.classes.get? canonId with
      | none => []
      | some eclass =>
        let rec matchChildren (pats : List (Pattern Op))
            (nodeChildren : List EClassId) (subst : Substitution)
            (acc : MatchResult) : MatchResult :=
          match pats, nodeChildren with
          | [], [] => acc ++ [subst]
          | p :: ps, c :: cs =>
            let results := ematchF fuel g p c subst
            results.foldl (fun a s => matchChildren ps cs s a) acc
          | _, _ => acc
        eclass.nodes.foldl (init := []) fun acc node =>
          if sameShape skelOp node.op then
            matchChildren subpats (NodeOps.children node.op) subst acc
          else acc

-- ══════════════════════════════════════════════════════════════════
-- Section 5: applyRuleAtF — Fuel-based rule application
-- ══════════════════════════════════════════════════════════════════

/-- Apply a rewrite rule at a specific class, using fuel-based ematch
    and total instantiate. -/
def applyRuleAtF (fuel : Nat) (g : EGraph Op) (rule : RewriteRule Op)
    (classId : EClassId) : EGraph Op :=
  let results := ematchF fuel g rule.lhs classId
  results.foldl (fun acc subst =>
    let condMet := match rule.sideCondCheck with
      | some check => check acc subst
      | none => true
    if !condMet then acc
    else
      match instantiateF fuel acc rule.rhs subst with
      | none => acc
      | some (rhsId, acc') =>
        let canonLhs := root acc'.unionFind classId
        let canonRhs := root acc'.unionFind rhsId
        if canonLhs == canonRhs then acc'
        else acc'.merge classId rhsId) g

/-- Apply a rule to all classes using fuel-based operations. -/
def applyRuleF (fuel : Nat) (g : EGraph Op) (rule : RewriteRule Op) : EGraph Op :=
  let allClasses := g.classes.toList.map (·.1)
  allClasses.foldl (fun acc classId => applyRuleAtF fuel acc rule classId) g

/-- Apply a list of rules once across the entire e-graph (fuel-based). -/
def applyRulesF (fuel : Nat) (g : EGraph Op) (rules : List (RewriteRule Op)) : EGraph Op :=
  rules.foldl (applyRuleF fuel) g

-- ══════════════════════════════════════════════════════════════════
-- Section 6: saturateF — Total saturation loop
-- ══════════════════════════════════════════════════════════════════

/-- Total saturation loop. Applies rules for at most `maxIter` iterations.
    Each iteration: apply all rules, then rebuild via `rebuildStepBody` + `rebuildF`.
    Uses `fuel` for ematch/instantiate and `rebuildFuel` for rebuild. -/
def saturateF (fuel : Nat) (maxIter : Nat) (rebuildFuel : Nat)
    (g : EGraph Op) (rules : List (RewriteRule Op)) : EGraph Op :=
  match maxIter with
  | 0 => g
  | n + 1 =>
    let g' := applyRulesF fuel g rules
    let g'' := rebuildF g' rebuildFuel
    if g''.numClasses == g.numClasses then g''
    else saturateF fuel n rebuildFuel g'' rules

-- ══════════════════════════════════════════════════════════════════
-- Section 7: Soundness — Opcion A (assumes valid rule application)
-- ══════════════════════════════════════════════════════════════════

/-- Predicate: a step function preserves the triple (CV, PMI, SHI).
    This is the core composability property for the saturation pipeline.
    Superseded in v1.0.0 by `saturateF_preserves_consistent_internal` (EMatchSpec)
    which derives this from ematchF_sound + PatternSoundRule + InstantiateEvalSound. -/
def PreservesCV (env : Nat → Val) (step : EGraph Op → EGraph Op) : Prop :=
  ∀ (g : EGraph Op) (v : EClassId → Val),
    ConsistentValuation g env v →
    PostMergeInvariant g →
    SemanticHashconsInv g env v →
    ∃ v', ConsistentValuation (step g) env v' ∧
          PostMergeInvariant (step g) ∧
          SemanticHashconsInv (step g) env v'

set_option linter.unusedSectionVars false in
/-- foldl preserves the triple when each element's step does. -/
theorem foldl_preserves_cv {α : Type} (env : Nat → Val) (l : List α)
    (f : EGraph Op → α → EGraph Op)
    (hf : ∀ a ∈ l, PreservesCV env (fun g => f g a))
    (g : EGraph Op) (v : EClassId → Val)
    (hcv : ConsistentValuation g env v)
    (hpmi : PostMergeInvariant g)
    (hshi : SemanticHashconsInv g env v) :
    ∃ v', ConsistentValuation (l.foldl f g) env v' ∧
          PostMergeInvariant (l.foldl f g) ∧
          SemanticHashconsInv (l.foldl f g) env v' := by
  induction l generalizing g v with
  | nil => exact ⟨v, hcv, hpmi, hshi⟩
  | cons a as ih =>
    have hmem : a ∈ a :: as := by simp
    obtain ⟨v1, hcv1, hpmi1, hshi1⟩ := hf a hmem g v hcv hpmi hshi
    exact ih (fun a' ha' => hf a' (by simp [ha'])) (f g a) v1 hcv1 hpmi1 hshi1

/-- rebuildStepBody preserves the triple (CV, PMI, SHI) with the same v.
    Uses SemanticHashconsInv to close the soundness gap. -/
theorem rebuildStepBody_preserves_cv (env : Nat → Val) (g : EGraph Op)
    (v : EClassId → Val) (hcv : ConsistentValuation g env v)
    (hpmi : PostMergeInvariant g) (hshi : SemanticHashconsInv g env v) :
    ConsistentValuation (rebuildStepBody g) env v ∧
    PostMergeInvariant (rebuildStepBody g) ∧
    SemanticHashconsInv (rebuildStepBody g) env v :=
  rebuildStepBody_preserves_triple g env v hcv hpmi hshi

/-- rebuildF preserves the triple with the same v. -/
theorem rebuildF_preserves_cv (env : Nat → Val) (fuel : Nat)
    (g : EGraph Op) (v : EClassId → Val) (hcv : ConsistentValuation g env v)
    (hpmi : PostMergeInvariant g) (hshi : SemanticHashconsInv g env v) :
    ConsistentValuation (rebuildF g fuel) env v ∧
    PostMergeInvariant (rebuildF g fuel) ∧
    SemanticHashconsInv (rebuildF g fuel) env v := by
  induction fuel generalizing g v with
  | zero => exact ⟨hcv, hpmi, hshi⟩
  | succ n ih =>
    simp only [rebuildF]
    split
    · exact ⟨hcv, hpmi, hshi⟩
    · have ⟨hcv', hpmi', hshi'⟩ := rebuildStepBody_preserves_cv env g v hcv hpmi hshi
      exact ih (rebuildStepBody g) v hcv' hpmi' hshi'

set_option linter.unusedSectionVars false in
/-- applyRulesF preserves the triple when each rule application does. -/
theorem applyRulesF_preserves_cv (fuel : Nat) (env : Nat → Val)
    (rules : List (RewriteRule Op))
    (h_rules : ∀ rule ∈ rules, PreservesCV env (applyRuleF fuel · rule))
    (g : EGraph Op) (v : EClassId → Val)
    (hcv : ConsistentValuation g env v)
    (hpmi : PostMergeInvariant g) (hshi : SemanticHashconsInv g env v) :
    ∃ v', ConsistentValuation (applyRulesF fuel g rules) env v' ∧
          PostMergeInvariant (applyRulesF fuel g rules) ∧
          SemanticHashconsInv (applyRulesF fuel g rules) env v' := by
  simp only [applyRulesF]
  exact foldl_preserves_cv env rules (fun g r => applyRuleF fuel g r)
    h_rules g v hcv hpmi hshi

/-- Main soundness theorem: saturateF preserves ConsistentValuation
    when each rule application preserves the triple (Opcion A assumption).
    Zero sorry — rebuild soundness proven via SemanticHashconsInv. -/
theorem saturateF_preserves_consistent (fuel maxIter rebuildFuel : Nat)
    (g : EGraph Op) (rules : List (RewriteRule Op))
    (env : Nat → Val) (v : EClassId → Val)
    (hcv : ConsistentValuation g env v)
    (hpmi : PostMergeInvariant g) (hshi : SemanticHashconsInv g env v)
    (h_rules : ∀ rule ∈ rules, PreservesCV env (applyRuleF fuel · rule)) :
    ∃ v', ConsistentValuation (saturateF fuel maxIter rebuildFuel g rules) env v' := by
  induction maxIter generalizing g v with
  | zero => exact ⟨v, hcv⟩
  | succ n ih =>
    simp only [saturateF]
    obtain ⟨v1, hcv1, hpmi1, hshi1⟩ :=
      applyRulesF_preserves_cv fuel env rules h_rules g v hcv hpmi hshi
    have ⟨hcv2, hpmi2, hshi2⟩ :=
      rebuildF_preserves_cv env rebuildFuel (applyRulesF fuel g rules) v1 hcv1 hpmi1 hshi1
    split
    · exact ⟨v1, hcv2⟩
    · exact ih (rebuildF (applyRulesF fuel g rules) rebuildFuel) v1 hcv2 hpmi2 hshi2

end LambdaSat
