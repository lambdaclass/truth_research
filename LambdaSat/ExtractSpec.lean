/-
  LambdaSat — Extraction Correctness Specification
  Fase 3 Subfase 2: Formal verification of greedy extraction

  Key theorem:
  - `extractF_correct`: if ConsistentValuation + BestNodeInv + ExtractableSound,
    then extractF returns an expression that evaluates to the correct value.

  Proof strategy:
  - Induction on fuel
  - BestNodeInv provides: bestNode ∈ class.nodes
  - ConsistentValuation node-consistency provides: NodeEval bestNode v = v classId
  - ExtractableSound bridges: evalExpr expr = evalOp op
  - Fuel descent ensures well-founded recursion
-/
import LambdaSat.Extractable

namespace LambdaSat

open UnionFind

variable {Op : Type} {Val : Type} {Expr : Type}
  [NodeOps Op] [BEq Op] [Hashable Op]
  [LawfulBEq Op] [LawfulHashable Op]
  [NodeSemantics Op Val]
  [Extractable Op Expr] [EvalExpr Expr Val]

-- ══════════════════════════════════════════════════════════════════
-- extractF_correct: Greedy extraction produces correct expressions
-- ══════════════════════════════════════════════════════════════════

/-- Greedy extraction produces semantically correct expressions.

    If:
    - `ConsistentValuation g env v` (e-graph semantics are consistent)
    - `BestNodeInv g.classes` (every bestNode is in its class's nodes)
    - `ExtractableSound Op Expr Val` (reconstruction preserves semantics)
    - `extractF g classId fuel = some expr`

    Then: `EvalExpr.evalExpr expr env = v (root g.unionFind classId)`

    Proof: induction on fuel.
    - Base (fuel = 0): extractF returns none — vacuously true.
    - Step (fuel + 1):
      1. bestNode ∈ class.nodes (from BestNodeInv)
      2. NodeEval bestNode env v = v classId (from ConsistentValuation)
      3. Each child extraction returns correct value (by IH on fuel)
      4. Extractable.reconstruct produces expr with correct eval (by ExtractableSound)
-/
theorem extractF_correct (g : EGraph Op) (env : Nat → Val) (v : EClassId → Val)
    (hcv : ConsistentValuation g env v)
    (hwf : WellFormed g.unionFind)
    (hbni : BestNodeInv g.classes)
    (hsound : ExtractableSound Op Expr Val) :
    ∀ (fuel : Nat) (classId : EClassId) (expr : Expr),
      extractF g classId fuel = some expr →
      EvalExpr.evalExpr expr env = v (root g.unionFind classId) := by
  intro fuel
  induction fuel with
  | zero => intro classId expr h; simp [extractF] at h
  | succ n ih =>
    intro classId expr hext
    unfold extractF at hext
    simp only [] at hext
    split at hext
    · exact absurd hext (by simp)
    · rename_i eclass heclass
      split at hext
      · exact absurd hext (by simp)
      · rename_i bestNode hbestNode
        split at hext
        · exact absurd hext (by simp)
        · rename_i childExprs hmapOpt
          -- bestNode ∈ eclass.nodes (from BestNodeInv)
          have hbn_mem := hbni _ _ _ heclass hbestNode
          -- NodeEval bestNode evaluates to v (root classId) (from ConsistentValuation)
          have heval := hcv.2 (root g.unionFind classId) eclass heclass bestNode hbn_mem
          -- children lengths match
          have hlen := mapOption_length hmapOpt
          -- each child expression evaluates correctly (by IH)
          have hchildren : ∀ (i : Nat) (hi : i < childExprs.length)
              (hio : i < (NodeOps.children bestNode.op).length),
              EvalExpr.evalExpr childExprs[i] env =
                v ((NodeOps.children bestNode.op)[i]'hio) := by
            intro i hi hio
            have hget := mapOption_get hmapOpt i hio hi
            simp only [] at hget
            rw [ih _ _ hget]
            exact consistent_root_eq' g env v hcv hwf _
          -- bridge: evalExpr expr = evalOp bestNode.op (from ExtractableSound)
          rw [hsound bestNode.op childExprs expr env v hext hlen hchildren]
          -- goal: NodeSemantics.evalOp bestNode.op env v = v (root classId)
          exact heval

/-- Corollary: extractAuto is also correct. -/
theorem extractAuto_correct (g : EGraph Op) (env : Nat → Val) (v : EClassId → Val)
    (hcv : ConsistentValuation g env v)
    (hwf : WellFormed g.unionFind)
    (hbni : BestNodeInv g.classes)
    (hsound : ExtractableSound Op Expr Val)
    (rootId : EClassId) (expr : Expr)
    (hext : extractAuto g rootId = some expr) :
    EvalExpr.evalExpr expr env = v (root g.unionFind rootId) :=
  extractF_correct g env v hcv hwf hbni hsound _ rootId expr hext

-- ══════════════════════════════════════════════════════════════════
-- computeCostsF preserves BestNodeInv + ConsistentValuation
-- (already proven in SemanticSpec.lean, re-exported here for convenience)
-- ══════════════════════════════════════════════════════════════════

/-- After computeCostsF, extraction is correct (combines cost computation
    preserving invariants with extraction correctness). -/
theorem computeCostsF_extractF_correct (g : EGraph Op) (costFn : ENode Op → Nat)
    (fuel : Nat) (env : Nat → Val) (v : EClassId → Val)
    (hcv : ConsistentValuation g env v)
    (hwf : WellFormed g.unionFind)
    (hbni : BestNodeInv g.classes)
    (hsound : ExtractableSound Op Expr Val)
    (extractFuel : Nat) (rootId : EClassId) (expr : Expr)
    (hext : extractF (computeCostsF g costFn fuel) rootId extractFuel = some expr) :
    EvalExpr.evalExpr expr env = v (root g.unionFind rootId) := by
  have hcv' := computeCostsF_preserves_consistency g costFn fuel env v hcv
  have hbni' := computeCostsF_bestNode_in_nodes g costFn fuel hbni
  have hwf' : WellFormed (computeCostsF g costFn fuel).unionFind := by
    rw [computeCostsF_preserves_uf]; exact hwf
  have hroot : root (computeCostsF g costFn fuel).unionFind rootId = root g.unionFind rootId := by
    simp [computeCostsF_preserves_uf]
  rw [hroot] at *
  exact extractF_correct (computeCostsF g costFn fuel) env v hcv' hwf' hbni' hsound
    extractFuel rootId expr hext

end LambdaSat
