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

end LambdaSat.ILP
