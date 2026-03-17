/-
  LambdaSat — Unified Extraction Interface + Correctness
  Fase 10: Adapted from VerifiedExtraction/Integration.lean

  Provides a unified `extract` function dispatching to greedy or ILP-certificate
  methods, with a single correctness theorem parameterized by strategy.

  Key results:
  - `extract`: unified greedy/ILP dispatch
  - `extract_correct`: strategy-parameterized correctness theorem
-/
import LambdaSat.ExtractSpec
import LambdaSat.ILPSpec

namespace LambdaSat

open UnionFind ILP

/-! ## Extraction Strategy -/

/-- Selection of extraction method with associated parameters. -/
inductive ExtractionStrategy (Op : Type) [NodeOps Op] where
  /-- Greedy extraction: follow bestNode pointers with given fuel. -/
  | greedy (fuel : Nat)
  /-- ILP certificate extraction: follow externally-computed ILP solution. -/
  | ilp (solution : ILPSolution) (fuel : Nat)

variable {Op : Type} [NodeOps Op] [BEq Op] [Hashable Op]
  {Expr : Type} [Extractable Op Expr]

/-- Unified extraction: dispatches to the appropriate method. -/
def extract (g : EGraph Op) (rootId : EClassId) :
    ExtractionStrategy Op → Option Expr
  | .greedy fuel => extractF g rootId fuel
  | .ilp sol fuel => extractILP g sol rootId fuel

/-! ## Strategy-Specific Validity -/

/-- Each strategy requires a different validity witness.
    - Greedy needs `BestNodeInv`: every bestNode is in its class.
    - ILP needs `ValidSolution`: the 4-way certificate check passes. -/
def StrategyValid (g : EGraph Op) (rootId : EClassId) :
    ExtractionStrategy Op → Prop
  | .greedy _ => BestNodeInv g.classes
  | .ilp sol _ => ValidSolution g rootId sol

/-! ## Unified Correctness -/

variable [LawfulBEq Op] [LawfulHashable Op]
  {Val : Type} [NodeSemantics Op Val] [EvalExpr Expr Val]

/-- **Master extraction correctness theorem.**

    Regardless of whether greedy or ILP extraction is used, if:
    - The e-graph has a consistent valuation
    - The UnionFind is well-formed
    - The strategy-specific validity holds
    - The Extractable→NodeSemantics bridge is sound
    - Extraction succeeds

    Then the extracted expression evaluates to the semantic value of the root class. -/
theorem extract_correct
    (g : EGraph Op) (env : Nat → Val) (v : EClassId → Val)
    (hcv : ConsistentValuation g env v)
    (hwf : WellFormed g.unionFind)
    (hsound : ExtractableSound Op Expr Val)
    (rootId : EClassId) (strategy : ExtractionStrategy Op)
    (hvalid : StrategyValid g rootId strategy)
    (expr : Expr)
    (hext : extract g rootId strategy = some expr) :
    EvalExpr.evalExpr expr env = v (root g.unionFind rootId) := by
  cases strategy with
  | greedy fuel =>
    exact extractF_correct g env v hcv hwf hvalid hsound fuel rootId expr hext
  | ilp sol fuel =>
    exact ilp_extraction_soundness g rootId sol env v hcv hwf hvalid hsound fuel expr hext

end LambdaSat
