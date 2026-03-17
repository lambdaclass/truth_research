/-
  LambdaSat — Optimization Pipeline
  Fase 3 Subfase 3: Generic optimization pipeline
  saturate → computeCosts → extract (greedy or ILP)

  Domain-agnostic: uses Extractable typeclass for extraction.
  Supports both greedy (bestNode) and ILP-based optimal extraction.
-/
import LambdaSat.Extractable
import LambdaSat.Saturate
import LambdaSat.ILPSolver

namespace LambdaSat

open UnionFind

-- ══════════════════════════════════════════════════════════════════
-- Optimization Configuration
-- ══════════════════════════════════════════════════════════════════

/-! ## TCB Note

    The functions in this file (`optimizeExpr`, `optimizeExprILP`, `optimizeExprAuto`)
    use `partial def saturate` (Saturate.lean) and are **outside the verified TCB**.
    They provide production features (timeouts, node limits, statistics) that cannot
    be expressed in total functions.

    For formally verified optimization, use `optimizeF` or `optimizeWithStrategyF`
    from `PipelineSoundness.lean`, which compose the total, verified spec functions
    (`saturateF`, `computeCostsF`, `extractAuto`/`extract`) with proven correctness
    theorems (`optimizeF_soundness`, `optimizeWithStrategyF_soundness`). -/

/-- Optimization pipeline configuration. -/
structure OptConfig where
  /-- Saturation configuration -/
  saturation     : SaturationConfig := {}
  /-- Extraction mode: greedy or ILP -/
  extractionMode : ILP.ExtractionMode := .greedy
  /-- ILP solver configuration (used when extraction = ilp) -/
  solverConfig   : ILP.SolverConfig := {}
  /-- Compute costs fuel (iterations for cost convergence) -/
  costsFuel      : Nat := 100
  deriving Repr, Inhabited

/-- Optimization statistics. -/
structure OptStats where
  iterations : Nat
  saturated  : Bool
  reason     : String
  extraction : String := "greedy"
  deriving Repr, Inhabited

-- ══════════════════════════════════════════════════════════════════
-- Greedy Optimization Pipeline
-- ══════════════════════════════════════════════════════════════════

variable {Op : Type} {Expr : Type}
  [NodeOps Op] [BEq Op] [Hashable Op]
  [Extractable Op Expr]

/-- Run the greedy optimization pipeline:
    1. Saturate with rewrite rules
    2. Compute costs with given cost function
    3. Extract best expression via bestNode pointers -/
def optimizeExpr (g : EGraph Op) (rootId : EClassId)
    (rules : List (RewriteRule Op))
    (costFn : ENode Op → Nat)
    (config : OptConfig := {}) : Option Expr × OptStats :=
  let satResult := saturate g rules config.saturation
  let g1 := computeCostsF satResult.graph costFn config.costsFuel
  let extracted := extractAuto g1 rootId
  let stats : OptStats := {
    iterations := satResult.iterations
    saturated := satResult.saturated
    reason := satResult.reason
    extraction := "greedy"
  }
  (extracted, stats)

/-- Run optimization with explicit fuel for extraction. -/
def optimizeExprWithFuel (g : EGraph Op) (rootId : EClassId)
    (rules : List (RewriteRule Op))
    (costFn : ENode Op → Nat)
    (extractionFuel : Nat)
    (config : OptConfig := {}) : Option Expr × OptStats :=
  let satResult := saturate g rules config.saturation
  let g1 := computeCostsF satResult.graph costFn config.costsFuel
  let extracted := extractF g1 rootId extractionFuel
  let stats : OptStats := {
    iterations := satResult.iterations
    saturated := satResult.saturated
    reason := satResult.reason
    extraction := "greedy"
  }
  (extracted, stats)

-- ══════════════════════════════════════════════════════════════════
-- ILP Optimization Pipeline (IO, for external solver)
-- ══════════════════════════════════════════════════════════════════

/-- Run the ILP optimization pipeline:
    1. Saturate with rewrite rules
    2. Encode e-graph as ILP problem
    3. Solve ILP (external HiGHS or internal B&B)
    4. Extract via ILP solution, falling back to greedy if ILP fails -/
def optimizeExprILP (g : EGraph Op) (rootId : EClassId)
    (rules : List (RewriteRule Op))
    (costFn : ENode Op → Nat)
    (config : OptConfig := {}) : IO (Option Expr × OptStats) := do
  let satResult := saturate g rules config.saturation
  let g1 := computeCostsF satResult.graph costFn config.costsFuel
  -- Try ILP extraction
  let prob := ILP.encodeEGraph g1 rootId costFn
  let solResult ← ILP.solveILP prob config.solverConfig
  let (extracted, mode) := match solResult with
    | some _sol =>
      -- ILP solved; for now use greedy extraction
      -- (F3S5 will add extractILP using the solution)
      (extractAuto g1 rootId, "ilp_solved_greedy_fallback")
    | none =>
      (extractAuto g1 rootId, "greedy_ilp_failed")
  let stats : OptStats := {
    iterations := satResult.iterations
    saturated := satResult.saturated
    reason := satResult.reason
    extraction := mode
  }
  return (extracted, stats)

/-- Unified optimization: auto-selects greedy or ILP based on config. -/
def optimizeExprAuto (g : EGraph Op) (rootId : EClassId)
    (rules : List (RewriteRule Op))
    (costFn : ENode Op → Nat)
    (config : OptConfig := {}) : IO (Option Expr × OptStats) := do
  match config.extractionMode with
  | .greedy => return optimizeExpr g rootId rules costFn config
  | .ilp => optimizeExprILP g rootId rules costFn config
  | .ilpAuto =>
    let satResult := saturate g rules config.saturation
    if satResult.graph.numClasses > 10 then
      optimizeExprILP g rootId rules costFn config
    else
      return optimizeExpr g rootId rules costFn config

end LambdaSat
