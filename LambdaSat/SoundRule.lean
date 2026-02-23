/-
  LambdaSat — Sound Rewrite Rules
  Fase 5 Subfase 1-2: SoundRewriteRule structure + consistency preservation.

  Provides verified rewrite rules that carry a semantic soundness proof:
  the LHS and RHS expressions evaluate identically for all environments.
  Generalized from VR1CS-Lean v1.3.0 SoundRule.lean.

  Key components:
  - `SoundRewriteRule`: unconditional sound rewrite rule
  - `ConditionalSoundRewriteRule`: rule with a side condition
  - `sound_rule_preserves_consistency`: merging after a sound rule preserves CV
-/
import LambdaSat.SemanticSpec

namespace LambdaSat

open UnionFind

-- ══════════════════════════════════════════════════════════════════
-- Section 1: SoundRewriteRule
-- ══════════════════════════════════════════════════════════════════

/-- A sound rewrite rule carries a syntactic `RewriteRule` for e-matching
    plus a semantic proof that LHS and RHS expressions evaluate identically.

    `Op` is the node operation type, `Expr` is the expression type for
    semantic reasoning, `Val` is the semantic domain (e.g., `Nat`, `ZMod p`).

    The `eval` field provides expression evaluation — typically instantiated
    to `EvalExpr.evalExpr` when connecting to the extraction pipeline. -/
structure SoundRewriteRule (Op : Type) (Expr : Type) (Val : Type)
    [BEq Op] [Hashable Op] where
  /-- Rule name for debugging/display -/
  name : String
  /-- Syntactic rewrite rule for e-matching -/
  rule : RewriteRule Op
  /-- Semantic LHS expression parameterized by variable assignment -/
  lhsExpr : (Nat → Expr) → Expr
  /-- Semantic RHS expression parameterized by variable assignment -/
  rhsExpr : (Nat → Expr) → Expr
  /-- Expression evaluator -/
  eval : Expr → (Nat → Val) → Val
  /-- Soundness: LHS and RHS evaluate to the same value for all environments -/
  soundness : ∀ (env : Nat → Val) (vars : Nat → Expr),
    eval (lhsExpr vars) env = eval (rhsExpr vars) env

-- ══════════════════════════════════════════════════════════════════
-- Section 2: ConditionalSoundRewriteRule
-- ══════════════════════════════════════════════════════════════════

/-- A conditional sound rewrite rule extends `SoundRewriteRule` with a side
    condition that must hold for the rule to apply. The soundness proof
    guarantees that IF the condition holds, THEN LHS = RHS semantically.

    For unconditional rules, use `SoundRewriteRule.toConditional`. -/
structure ConditionalSoundRewriteRule (Op : Type) (Expr : Type) (Val : Type)
    [BEq Op] [Hashable Op] where
  name : String
  rule : RewriteRule Op
  lhsExpr : (Nat → Expr) → Expr
  rhsExpr : (Nat → Expr) → Expr
  eval : Expr → (Nat → Val) → Val
  sideCond : (Nat → Val) → (Nat → Expr) → Prop
  soundness : ∀ (env : Nat → Val) (vars : Nat → Expr),
    sideCond env vars →
    eval (lhsExpr vars) env = eval (rhsExpr vars) env

/-- Lift an unconditional rule to a conditional one with trivial side condition. -/
def SoundRewriteRule.toConditional {Op Expr Val : Type} [BEq Op] [Hashable Op]
    (r : SoundRewriteRule Op Expr Val) : ConditionalSoundRewriteRule Op Expr Val where
  name := r.name
  rule := r.rule
  lhsExpr := r.lhsExpr
  rhsExpr := r.rhsExpr
  eval := r.eval
  sideCond := fun _ _ => True
  soundness := fun env vars _ => r.soundness env vars

/-- A conditional rule is sound if its proof holds for all valid inputs. -/
def ConditionalSoundRewriteRule.IsSound {Op Expr Val : Type} [BEq Op] [Hashable Op]
    (r : ConditionalSoundRewriteRule Op Expr Val) : Prop :=
  ∀ (env : Nat → Val) (vars : Nat → Expr),
    r.sideCond env vars →
    r.eval (r.lhsExpr vars) env = r.eval (r.rhsExpr vars) env

theorem ConditionalSoundRewriteRule.isSound {Op Expr Val : Type} [BEq Op] [Hashable Op]
    (r : ConditionalSoundRewriteRule Op Expr Val) : r.IsSound :=
  r.soundness

-- ══════════════════════════════════════════════════════════════════
-- Section 3: sound_rule_preserves_consistency
-- ══════════════════════════════════════════════════════════════════

variable {Op : Type} {Val : Type} {Expr : Type}
  [NodeOps Op] [BEq Op] [Hashable Op] [LawfulBEq Op] [LawfulHashable Op]
  [NodeSemantics Op Val]

/-- Applying a SoundRewriteRule (which guarantees lhs.eval = rhs.eval)
    via merge preserves ConsistentValuation.

    Port of vr1cs SemanticSpec:444-456, generalized from CircuitExpr to generic Expr.
    This is a direct corollary of `merge_consistent` + `rule.soundness`. -/
theorem sound_rule_preserves_consistency
    (g : EGraph Op) (rule : SoundRewriteRule Op Expr Val)
    (lhsId rhsId : EClassId)
    (env : Nat → Val) (v : EClassId → Val)
    (hv : ConsistentValuation g env v) (hwf : WellFormed g.unionFind)
    (h1 : lhsId < g.unionFind.parent.size) (h2 : rhsId < g.unionFind.parent.size)
    (vars : Nat → Expr)
    (h_lhs : v (root g.unionFind lhsId) = rule.eval (rule.lhsExpr vars) env)
    (h_rhs : v (root g.unionFind rhsId) = rule.eval (rule.rhsExpr vars) env) :
    ConsistentValuation (g.merge lhsId rhsId) env v :=
  merge_consistent g lhsId rhsId env v hv hwf h1 h2
    (by rw [h_lhs, h_rhs, rule.soundness env vars])

/-- Conditional version: if the side condition holds, merging preserves CV. -/
theorem conditional_sound_rule_preserves_consistency
    (g : EGraph Op) (rule : ConditionalSoundRewriteRule Op Expr Val)
    (lhsId rhsId : EClassId)
    (env : Nat → Val) (v : EClassId → Val)
    (hv : ConsistentValuation g env v) (hwf : WellFormed g.unionFind)
    (h1 : lhsId < g.unionFind.parent.size) (h2 : rhsId < g.unionFind.parent.size)
    (vars : Nat → Expr)
    (h_cond : rule.sideCond env vars)
    (h_lhs : v (root g.unionFind lhsId) = rule.eval (rule.lhsExpr vars) env)
    (h_rhs : v (root g.unionFind rhsId) = rule.eval (rule.rhsExpr vars) env) :
    ConsistentValuation (g.merge lhsId rhsId) env v :=
  merge_consistent g lhsId rhsId env v hv hwf h1 h2
    (by rw [h_lhs, h_rhs, rule.soundness env vars h_cond])

end LambdaSat
