/-
  LambdaSat — Extractable Typeclass + Generic Extraction
  Fase 3 Subfase 1: Domain-agnostic expression extraction from e-graphs.

  Key components:
  - `Extractable` typeclass: reconstruct expressions from e-graph nodes
  - `EvalExpr` typeclass: evaluate extracted expressions
  - `ExtractableSound`: soundness law connecting reconstruction to node semantics
  - `extractF` : fuel-based extraction following bestNode pointers
  - `mapOption` : total helper for extracting all children (with spec lemmas for F3S2)
-/
import LambdaSat.SemanticSpec

namespace LambdaSat

open UnionFind

-- ══════════════════════════════════════════════════════════════════
-- Helper: mapOption (total, with spec lemmas for F3S2 proofs)
-- ══════════════════════════════════════════════════════════════════

/-- Apply `f` to each element, collecting results.
    Returns `none` if any application returns `none`. -/
def mapOption (f : α → Option β) : List α → Option (List β)
  | [] => some []
  | a :: as =>
    match f a with
    | none => none
    | some b =>
      match mapOption f as with
      | none => none
      | some bs => some (b :: bs)

@[simp] theorem mapOption_nil (f : α → Option β) : mapOption f [] = some [] := rfl

/-- Inversion lemma for cons case. -/
theorem mapOption_cons_inv {f : α → Option β} {a : α} {as : List α} {results : List β}
    (h : mapOption f (a :: as) = some results) :
    ∃ b bs, f a = some b ∧ mapOption f as = some bs ∧ results = b :: bs := by
  simp only [mapOption] at h
  split at h
  · exact absurd h (by simp)
  · rename_i b hb
    split at h
    · exact absurd h (by simp)
    · rename_i bs hbs
      exact ⟨b, bs, hb, hbs, (Option.some.inj h).symm⟩

theorem mapOption_cons_some {f : α → Option β} {a : α} {as : List α}
    {b : β} {bs : List β}
    (hf : f a = some b) (hrest : mapOption f as = some bs) :
    mapOption f (a :: as) = some (b :: bs) := by
  simp [mapOption, hf, hrest]

theorem mapOption_length {f : α → Option β} {l : List α} {results : List β}
    (h : mapOption f l = some results) : results.length = l.length := by
  induction l generalizing results with
  | nil => simp [mapOption] at h; subst h; rfl
  | cons a as ih =>
    obtain ⟨b, bs, _, hrest, hrsl⟩ := mapOption_cons_inv h
    subst hrsl
    simp [ih hrest]

theorem mapOption_get {f : α → Option β} {l : List α} {results : List β}
    (h : mapOption f l = some results)
    (i : Nat) (hil : i < l.length) (hir : i < results.length) :
    f l[i] = some results[i] := by
  induction l generalizing results i with
  | nil => exact absurd hil (Nat.not_lt_zero _)
  | cons a as ih =>
    obtain ⟨b, bs, hfa, hrest, hrsl⟩ := mapOption_cons_inv h
    subst hrsl
    match i with
    | 0 => exact hfa
    | i + 1 =>
      exact ih hrest i (Nat.lt_of_succ_lt_succ hil) (Nat.lt_of_succ_lt_succ hir)

-- ══════════════════════════════════════════════════════════════════
-- Extractable + EvalExpr Typeclasses
-- ══════════════════════════════════════════════════════════════════

/-- Typeclass for reconstructing expressions from e-graph nodes.
    Any domain (circuits, lambda calculus, arithmetic) can instantiate this. -/
class Extractable (Op : Type) (Expr : Type) where
  /-- Reconstruct an expression from an op and its children's extracted expressions. -/
  reconstruct : Op → List Expr → Option Expr

/-- Typeclass for evaluating extracted expressions.
    `Val` is the semantic domain (e.g., ZMod p for circuits, Nat for arithmetic). -/
class EvalExpr (Expr : Type) (Val : Type) where
  /-- Evaluate an expression given an environment for external inputs. -/
  evalExpr : Expr → (Nat → Val) → Val

/-- Soundness law connecting Extractable + EvalExpr to NodeSemantics.
    If reconstruction succeeds and each child expression evaluates to the
    value of its corresponding child class, then the reconstructed expression
    evaluates to `NodeSemantics.evalOp` applied to those child values.

    This is the key bridge: extracted `Expr` semantics ↔ e-graph `NodeSemantics`. -/
def ExtractableSound (Op Expr Val : Type) [NodeOps Op] [NodeSemantics Op Val]
    [Extractable Op Expr] [EvalExpr Expr Val] : Prop :=
  ∀ (op : Op) (childExprs : List Expr) (expr : Expr)
    (env : Nat → Val) (v : EClassId → Val),
  Extractable.reconstruct op childExprs = some expr →
  childExprs.length = (NodeOps.children op).length →
  (∀ (i : Nat) (hi : i < childExprs.length) (hio : i < (NodeOps.children op).length),
    EvalExpr.evalExpr childExprs[i] env =
      v ((NodeOps.children op)[i]'hio)) →
  EvalExpr.evalExpr expr env = NodeSemantics.evalOp op env v

-- ══════════════════════════════════════════════════════════════════
-- Generic extractF: fuel-based extraction via bestNode
-- ══════════════════════════════════════════════════════════════════

variable {Op : Type} {Expr : Type}
  [NodeOps Op] [BEq Op] [Hashable Op]
  [Extractable Op Expr]

/-- Extract an expression from the e-graph starting at class `id`.
    Follows `bestNode` pointers set by `computeCosts`.
    Uses fuel for termination (fuel ≥ numClasses suffices for acyclic graphs).

    Returns `some expr` if extraction succeeds, `none` if fuel runs out,
    class not found, or no bestNode is set. -/
def extractF (g : EGraph Op) (id : EClassId) : Nat → Option Expr
  | 0 => none
  | fuel + 1 =>
    let canonId := root g.unionFind id
    match g.classes.get? canonId with
    | none => none
    | some eclass =>
      match eclass.bestNode with
      | none => none
      | some bestNode =>
        let children := NodeOps.children bestNode.op
        match mapOption (fun c => extractF g c fuel) children with
        | none => none
        | some childExprs => Extractable.reconstruct bestNode.op childExprs

-- ══════════════════════════════════════════════════════════════════
-- Basic lemmas
-- ══════════════════════════════════════════════════════════════════

/-- extractF with zero fuel always returns none. -/
@[simp] theorem extractF_zero (g : EGraph Op) (id : EClassId) :
    extractF g id 0 = (none : Option Expr) := rfl

/-- Convenience: extract with fuel = numClasses + 1. -/
def extractAuto (g : EGraph Op) (rootId : EClassId) : Option Expr :=
  extractF g rootId (g.numClasses + 1)

end LambdaSat
