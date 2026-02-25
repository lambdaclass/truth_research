/-
  LambdaSat — ILP Extraction Specification
  Fase 3 Subfase 5: Formal verification of ILP-guided extraction

  Key theorems:
  - `extractILP_correct`: ILP-guided extraction produces semantically correct expressions
  - `ilp_extraction_soundness`: end-to-end pipeline soundness

  The proof strategy mirrors `extractF_correct` (greedy) but uses ILP solution
  as the guide instead of bestNode pointers. When extractILP succeeds (returns
  some expr), the intermediate matches guarantee: selected node ∈ class.nodes,
  valid index, children extracted. ConsistentValuation + ExtractableSound then
  bridge to semantic correctness.
-/
import LambdaSat.ILPCheck

namespace LambdaSat.ILP

open LambdaSat UnionFind

-- ══════════════════════════════════════════════════════════════════
-- ILP Solution Invariant
-- ══════════════════════════════════════════════════════════════════

variable {Op : Type} {Val : Type} {Expr : Type}
  [NodeOps Op] [BEq Op] [Hashable Op]
  [LawfulBEq Op] [LawfulHashable Op]
  [NodeSemantics Op Val]
  [Extractable Op Expr] [EvalExpr Expr Val]

/-- A valid ILP solution: checkSolution passes and all selected nodes
    have valid indices in their respective classes. -/
def ValidSolution (g : EGraph Op) (rootId : EClassId) (sol : ILPSolution) : Prop :=
  checkSolution g rootId sol = true

set_option linter.unusedSectionVars false in
/-- If checkSolution passes, the root class is active. -/
theorem validSol_root_active (g : EGraph Op) (rootId : EClassId)
    (sol : ILPSolution) (hv : ValidSolution g rootId sol) :
    sol.isActive (root g.unionFind rootId) = true := by
  simp only [ValidSolution, checkSolution, checkRootActive, Bool.and_eq_true] at hv
  exact hv.1.1.1

set_option linter.unusedSectionVars false in
/-- The root check is trivially sound: if it passes, the root is active. -/
theorem checkRootActive_sound (rootId : EClassId) (sol : ILPSolution)
    (h : checkRootActive rootId sol = true) :
    sol.isActive rootId = true := h

-- ══════════════════════════════════════════════════════════════════
-- checkSolution Decomposition (v1.2.0)
-- ══════════════════════════════════════════════════════════════════

/-- Helper: a `List.foldl` with a monotone-false body starting at `false` stays `false`. -/
private theorem foldl_false_stays {α : Type _} (f : Bool → α → Bool)
    (hf : ∀ x, f false x = false) (l : List α) :
    List.foldl f false l = false := by
  induction l with
  | nil => rfl
  | cons hd tl ih => simp only [List.foldl_cons, hf, ih]

/-- Helper: if a `List.foldl` with `init := true` and a monotone-false body returns `true`,
    then for every element, the body returns `true` with `acc = true`.

    This is the key reusable lemma for decomposing `HashMap.fold (init := true) (fun acc k v => ...)`
    checks into per-element properties. -/
private theorem foldl_bool_true {α : Type _} {l : List α} {f : Bool → α → Bool}
    (hf : ∀ x, f false x = false)
    (h : List.foldl f true l = true) :
    ∀ x ∈ l, f true x = true := by
  induction l with
  | nil => intro x hx; simp at hx
  | cons hd tl ih =>
    intro x hx
    simp only [List.foldl_cons] at h
    cases hfhd : f true hd with
    | true =>
      rw [hfhd] at h
      cases List.mem_cons.mp hx with
      | inl heq => rw [heq]; exact hfhd
      | inr hmem => exact ih h x hmem
    | false =>
      rw [hfhd] at h; rw [foldl_false_stays f hf tl] at h
      exact absurd h Bool.false_ne_true

set_option linter.unusedSectionVars false in
/-- If `checkExactlyOne` passes, then:
    - Every active class has a selected node with a valid index.
    - Every inactive class has no selected node. -/
theorem checkExactlyOne_sound (g : EGraph Op) (sol : ILPSolution)
    (h : checkExactlyOne g sol = true)
    (classId : EClassId) (eclass : EClass Op)
    (hget : g.classes.get? classId = some eclass) :
    (sol.isActive classId = true →
      ∃ idx, sol.selectedNodes.get? classId = some idx ∧
             idx < eclass.nodes.size) ∧
    (sol.isActive classId = false →
      (sol.selectedNodes.get? classId).isNone = true) := by
  unfold checkExactlyOne at h
  rw [Std.HashMap.fold_eq_foldl_toList] at h
  let body : Bool → EClassId × EClass Op → Bool := fun acc b =>
    if sol.isActive b.1 = true then
      match sol.selectedNodes.get? b.1 with
      | some idx => acc && decide (idx < b.2.nodes.size)
      | none => false
    else acc && (sol.selectedNodes.get? b.1).isNone
  have hf_mono : ∀ x, body false x = false := by
    intro ⟨cid, ecl⟩; simp only [body]
    split
    · split <;> simp [Bool.false_and]
    · simp [Bool.false_and]
  have hall := foldl_bool_true hf_mono (f := body) h
  have hmem : (classId, eclass) ∈ g.classes.toList :=
    Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr
      (Std.HashMap.get?_eq_getElem? ▸ hget)
  have hpair := hall (classId, eclass) hmem
  simp only [body] at hpair
  constructor
  · intro hactive
    rw [hactive] at hpair; simp only [↓reduceIte] at hpair
    split at hpair
    · rename_i idx hidx; exact ⟨idx, hidx, by simpa using hpair⟩
    · exact absurd hpair Bool.false_ne_true
  · intro hinactive
    rw [hinactive] at hpair
    simp only [Bool.false_eq_true, ↓reduceIte, Bool.true_and] at hpair
    exact hpair

set_option linter.unusedSectionVars false in
/-- If `checkChildDeps` passes, then for any class with a selected node,
    every child of that node is active (after canonicalization). -/
theorem checkChildDeps_sound (g : EGraph Op) (sol : ILPSolution)
    (h : checkChildDeps g sol = true)
    (classId : EClassId) (eclass : EClass Op)
    (hget : g.classes.get? classId = some eclass)
    (idx : Nat) (hsel : sol.selectedNodes.get? classId = some idx)
    (hidx : idx < eclass.nodes.size) :
    ∀ child ∈ (NodeOps.children (eclass.nodes[idx]).op),
      sol.isActive (root g.unionFind child) = true := by
  unfold checkChildDeps at h
  rw [Std.HashMap.fold_eq_foldl_toList] at h
  let body : Bool → EClassId × EClass Op → Bool := fun acc b =>
    match sol.selectedNodes.get? b.1 with
    | none => acc
    | some nIdx =>
      if _hh : nIdx < b.2.nodes.size then
        acc && (NodeOps.children (b.2.nodes[nIdx]).op).all fun child =>
          sol.isActive (root g.unionFind child)
      else acc
  have hf_mono : ∀ x, body false x = false := by
    intro ⟨cid, ecl⟩; simp only [body]
    split
    · rfl
    · split
      · simp [Bool.false_and]
      · rfl
  have hall := foldl_bool_true hf_mono (f := body) h
  have hmem : (classId, eclass) ∈ g.classes.toList :=
    Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr
      (Std.HashMap.get?_eq_getElem? ▸ hget)
  have hpair := hall (classId, eclass) hmem
  simp only [body, hsel, dif_pos hidx, Bool.true_and] at hpair
  exact List.all_eq_true.mp hpair

set_option linter.unusedSectionVars false in
/-- If `checkAcyclicity` passes, then for any class with a selected node,
    every non-self-referencing child has a strictly lower level. -/
theorem checkAcyclicity_sound (g : EGraph Op) (sol : ILPSolution)
    (h : checkAcyclicity g sol = true)
    (classId : EClassId) (eclass : EClass Op)
    (hget : g.classes.get? classId = some eclass)
    (idx : Nat) (hsel : sol.selectedNodes.get? classId = some idx)
    (hidx : idx < eclass.nodes.size) :
    ∀ child ∈ (NodeOps.children (eclass.nodes[idx]).op),
      root g.unionFind child ≠ classId →
      sol.getLevel classId > sol.getLevel (root g.unionFind child) := by
  unfold checkAcyclicity at h
  rw [Std.HashMap.fold_eq_foldl_toList] at h
  let body : Bool → EClassId × EClass Op → Bool := fun acc b =>
    match sol.selectedNodes.get? b.1 with
    | none => acc
    | some nIdx =>
      if _hh : nIdx < b.2.nodes.size then
        acc && (NodeOps.children (b.2.nodes[nIdx]).op).all fun child =>
          let canonChild := root g.unionFind child
          if canonChild == b.1 then true
          else sol.getLevel b.1 > sol.getLevel canonChild
      else acc
  have hf_mono : ∀ x, body false x = false := by
    intro ⟨cid, ecl⟩; simp only [body]
    split
    · rfl
    · split
      · simp [Bool.false_and]
      · rfl
  have hall := foldl_bool_true hf_mono (f := body) h
  have hmem : (classId, eclass) ∈ g.classes.toList :=
    Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr
      (Std.HashMap.get?_eq_getElem? ▸ hget)
  have hpair := hall (classId, eclass) hmem
  simp only [body, hsel, dif_pos hidx, Bool.true_and] at hpair
  intro child hchild hneq
  have hc := (List.all_eq_true.mp hpair) child hchild
  simp [beq_eq_false_iff_ne.mpr hneq] at hc
  exact hc

-- ══════════════════════════════════════════════════════════════════
-- checkSolution Composition (v1.2.0)
-- ══════════════════════════════════════════════════════════════════

set_option linter.unusedSectionVars false in
/-- Decompose `ValidSolution` into its four constituent checks:
    root activation, exactly-one selection, child dependencies, and acyclicity. -/
theorem validSolution_decompose (g : EGraph Op) (rootId : EClassId)
    (sol : ILPSolution) (hv : ValidSolution g rootId sol) :
    sol.isActive (root g.unionFind rootId) = true ∧
    checkExactlyOne g sol = true ∧
    checkChildDeps g sol = true ∧
    checkAcyclicity g sol = true := by
  simp only [ValidSolution, checkSolution, checkRootActive, Bool.and_eq_true] at hv
  exact ⟨hv.1.1.1, hv.1.1.2, hv.1.2, hv.2⟩

-- ══════════════════════════════════════════════════════════════════
-- Extraction Correctness (CRITICAL theorem)
-- ══════════════════════════════════════════════════════════════════

/-- ILP-guided extraction produces semantically correct expressions.

    If:
    - `ConsistentValuation g env v` (e-graph semantics are consistent)
    - `ValidSolution g rootId sol` (ILP solution passes all checks)
    - `ExtractableSound Op Expr Val` (reconstruction preserves semantics)
    - `extractILP g sol classId fuel = some expr`

    Then: `EvalExpr.evalExpr expr env = v (root g.unionFind classId)`

    Proof strategy (mirrors extractF_correct):
    - Induction on fuel
    - extractILP success → selected node index valid → node ∈ class.nodes
    - ConsistentValuation → NodeEval(selectedNode) env v = v classId
    - ExtractableSound → EvalExpr.evalExpr expr env = NodeSemantics.evalOp ...
    - IH on children (with double root-idempotent bridge) -/
theorem extractILP_correct (g : EGraph Op) (rootId : EClassId)
    (sol : ILPSolution) (env : Nat → Val) (v : EClassId → Val)
    (hcv : ConsistentValuation g env v)
    (hwf : WellFormed g.unionFind)
    (_hvalid : ValidSolution g rootId sol)
    (hsound : ExtractableSound Op Expr Val) :
    ∀ (fuel : Nat) (classId : EClassId) (expr : Expr),
      extractILP g sol classId fuel = some expr →
      EvalExpr.evalExpr expr env = v (root g.unionFind classId) := by
  intro fuel
  induction fuel with
  | zero => intro classId expr h; simp [extractILP] at h
  | succ n ih =>
    intro classId expr hext
    unfold extractILP at hext
    simp only [] at hext
    -- Split on sol.selectedNodes.get? (root uf classId)
    split at hext
    · exact absurd hext (by simp)
    · rename_i nodeIdx hselected
      -- Split on g.classes.get? (root uf classId)
      split at hext
      · exact absurd hext (by simp)
      · rename_i eclass heclass
        -- Split on if nodeIdx < eclass.nodes.size
        split at hext
        · rename_i hidx
          -- Split on mapOption
          split at hext
          · exact absurd hext (by simp)
          · rename_i childExprs hmapOpt
            -- hext : Extractable.reconstruct (eclass.nodes[nodeIdx]).op childExprs = some expr
            -- The selected node is in the class (by array indexing)
            have hnode_mem : (eclass.nodes[nodeIdx]) ∈ eclass.nodes.toList :=
              Array.getElem_mem_toList hidx
            -- NodeEval of selected node = v (root classId) (from ConsistentValuation)
            have heval := hcv.2 (root g.unionFind classId) eclass heclass
              (eclass.nodes[nodeIdx]) hnode_mem
            -- children lengths match
            have hlen := mapOption_length hmapOpt
            -- each child evaluates correctly (by IH + double root bridge)
            have hchildren : ∀ (i : Nat) (hi : i < childExprs.length)
                (hio : i < (NodeOps.children (eclass.nodes[nodeIdx]).op).length),
                EvalExpr.evalExpr childExprs[i] env =
                  v ((NodeOps.children (eclass.nodes[nodeIdx]).op)[i]'hio) := by
              intro i hi hio
              have hget := mapOption_get hmapOpt i hio hi
              simp only [] at hget
              -- hget : extractILP g sol (root uf child_i) n = some childExprs[i]
              rw [ih _ _ hget]
              -- goal: v (root uf (root uf child_i)) = v child_i
              rw [consistent_root_eq' g env v hcv hwf _]
              exact consistent_root_eq' g env v hcv hwf _
            -- bridge: evalExpr expr = evalOp (from ExtractableSound)
            rw [hsound (eclass.nodes[nodeIdx]).op childExprs expr env v hext hlen hchildren]
            -- goal: NodeSemantics.evalOp = v (root classId)
            exact heval
        · simp at hext

/-- End-to-end ILP extraction soundness.
    If the full pipeline succeeds (saturate + ILP solve + extract),
    the result is semantically equivalent to the original. -/
theorem ilp_extraction_soundness (g : EGraph Op) (rootId : EClassId)
    (sol : ILPSolution) (env : Nat → Val) (v : EClassId → Val)
    (hcv : ConsistentValuation g env v)
    (hwf : WellFormed g.unionFind)
    (hvalid : ValidSolution g rootId sol)
    (hsound : ExtractableSound Op Expr Val)
    (fuel : Nat) (expr : Expr)
    (hext : extractILP g sol rootId fuel = some expr) :
    EvalExpr.evalExpr expr env = v (root g.unionFind rootId) :=
  extractILP_correct g rootId sol env v hcv hwf hvalid hsound fuel rootId expr hext

-- ══════════════════════════════════════════════════════════════════
-- Fuel Sufficiency (F9S10)
-- ══════════════════════════════════════════════════════════════════

/-- `mapOption` is monotone: if `f` results are preserved by `g`, so is `mapOption`. -/
theorem mapOption_mono {α β : Type _} {f g : α → Option β} {l : List α} {bs : List β}
    (hm : mapOption f l = some bs)
    (hmono : ∀ a ∈ l, ∀ b, f a = some b → g a = some b) :
    mapOption g l = some bs := by
  induction l generalizing bs with
  | nil => simp [mapOption] at hm ⊢; exact hm
  | cons hd tl ih =>
    simp only [mapOption] at hm ⊢
    split at hm
    · exact absurd hm (by simp)
    · rename_i b hfhd
      split at hm
      · exact absurd hm (by simp)
      · rename_i bs' hmf
        have hbs : bs = b :: bs' := by cases hm; rfl
        rw [hmono hd (List.mem_cons.mpr (Or.inl rfl)) b hfhd]
        rw [ih hmf (fun a ha b hfa => hmono a (List.mem_cons.mpr (Or.inr ha)) b hfa)]
        rw [hbs]

set_option linter.unusedSectionVars false in
/-- `extractILPAuto` unfolds to `extractILP` with fuel `numClasses + 1`. -/
@[simp] theorem extractILPAuto_def (g : EGraph Op) (sol : ILPSolution)
    (rootId : EClassId) :
    extractILPAuto (Expr := Expr) g sol rootId =
      extractILP g sol rootId (g.numClasses + 1) := rfl

set_option linter.unusedSectionVars false in
/-- Fuel monotonicity: if extraction succeeds with fuel `n`, it succeeds with any `m ≥ n`. -/
theorem extractILP_fuel_mono (g : EGraph Op) (sol : ILPSolution) (id : EClassId) :
    ∀ (n m : Nat) (expr : Expr), n ≤ m →
    extractILP g sol id n = some expr →
    extractILP g sol id m = some expr := by
  intro n
  induction n generalizing id with
  | zero => intro m expr _ h; simp [extractILP] at h
  | succ k ih =>
    intro m expr hle h
    obtain ⟨m', rfl⟩ : ∃ m', m = k + 1 + m' := ⟨m - (k + 1), by omega⟩
    have hm : k + 1 + m' = (k + m') + 1 := by omega
    rw [hm]
    -- Unfold one step of extractILP in both h (fuel k+1) and goal (fuel (k+m')+1)
    simp only [extractILP] at h ⊢
    -- Both now have: let canonId := ...; match selectedNodes.get? canonId with ...
    -- The let binding reduces, leaving match chains that differ only in recursive fuel
    -- Split all matches in h to extract the successful path
    split at h
    · exact absurd h (by simp)
    · rename_i nodeIdx hsel
      split at h
      · exact absurd h (by simp)
      · rename_i eclass hcls
        split at h
        · rename_i hidx
          split at h
          · exact absurd h (by simp)
          · rename_i childExprs hmapOpt
            -- h : Extractable.reconstruct ... = some expr
            -- goal has the same match chain with fuel (k+m')
            -- Navigate the goal's matches using the same values
            simp only [dif_pos hidx] at ⊢
            have hmono : mapOption (fun c => extractILP g sol (root g.unionFind c) (k + m'))
                (NodeOps.children (eclass.nodes[nodeIdx]).op) = some childExprs :=
              mapOption_mono hmapOpt (fun a _ b hfa =>
                ih (root g.unionFind a) (k + m') b (by omega) hfa)
            rw [hmono]
            exact h
        · simp at h

end LambdaSat.ILP
