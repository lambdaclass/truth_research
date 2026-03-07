/-
  LambdaSat — Equality Saturation Loop
  Generic saturation engine: apply rules, rebuild, iterate to fixpoint.
  Generalized from VR1CS-Lean v1.3.0.
-/
import LambdaSat.EMatch

namespace LambdaSat

structure SaturationConfig where
  maxIterations : Nat := 10
  maxNodes : Nat := 100
  maxClasses : Nat := 50
  deriving Repr, Inhabited

structure SaturationResult (Op : Type) [BEq Op] [Hashable Op] where
  graph : EGraph Op
  iterations : Nat
  saturated : Bool
  reason : String

instance {Op : Type} [BEq Op] [Hashable Op] : Inhabited (SaturationResult Op) where
  default := ⟨default, 0, false, ""⟩

section SaturateDefs

variable {Op : Type} [NodeOps Op] [BEq Op] [Hashable Op]

private def saturateStep (g : EGraph Op) (rules : List (RewriteRule Op)) : EGraph Op :=
  let g' := applyRules g rules
  g'.rebuild

private def checkLimits (g : EGraph Op) (config : SaturationConfig) : Option String :=
  if g.numNodes > config.maxNodes then some s!"node limit ({config.maxNodes})"
  else if g.numClasses > config.maxClasses then some s!"class limit ({config.maxClasses})"
  else none

private def reachedFixpoint (before after : EGraph Op) : Bool :=
  before.numNodes == after.numNodes && before.numClasses == after.numClasses

/-- Run equality saturation with bounded iterations. -/
partial def saturate (g : EGraph Op) (rules : List (RewriteRule Op))
    (config : SaturationConfig := {}) : SaturationResult Op :=
  let rec loop (current : EGraph Op) (iter : Nat) : SaturationResult Op :=
    if iter >= config.maxIterations then
      { graph := current, iterations := iter, saturated := false,
        reason := "max iterations" }
    else
      match checkLimits current config with
      | some reason =>
        { graph := current, iterations := iter, saturated := false,
          reason := reason }
      | none =>
        let next := saturateStep current rules
        if reachedFixpoint current next then
          { graph := next, iterations := iter + 1, saturated := true,
            reason := "fixpoint" }
        else
          loop next (iter + 1)
  loop g 0

/-- Large configuration for more thorough saturation. -/
def SaturationConfig.large : SaturationConfig where
  maxIterations := 30
  maxNodes := 10000
  maxClasses := 5000

end SaturateDefs

end LambdaSat
