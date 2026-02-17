/-
  LambdaSat — Generic E-Matching
  Domain-agnostic pattern matching and rewriting for e-graphs.
  Generalized from VR1CS-Lean v1.3.0 (replaces CircuitPattern with generic Pattern Op).
-/
import LambdaSat.Core

namespace LambdaSat

abbrev PatVarId := Nat

/-- Generic pattern for e-matching, parameterized by operation type.
    - `patVar pv`: matches any e-class, binds to variable `pv`
    - `node skelOp subpats`: matches e-nodes whose op has the same shape as `skelOp`,
      recursively matching children against `subpats` -/
inductive Pattern (Op : Type) where
  | patVar : PatVarId → Pattern Op
  | node : Op → List (Pattern Op) → Pattern Op
  deriving Inhabited

abbrev Substitution := Std.HashMap PatVarId EClassId

namespace Substitution

def empty : Substitution := Std.HashMap.ofList []

def extend (subst : Substitution) (pv : PatVarId) (id : EClassId) : Option Substitution :=
  match subst.get? pv with
  | none => some (subst.insert pv id)
  | some existingId => if existingId == id then some subst else none

def lookup (subst : Substitution) (pv : PatVarId) : Option EClassId :=
  subst.get? pv

end Substitution

abbrev MatchResult := List Substitution

/-- Check if two ops have the same shape (ignoring children).
    Maps all children to 0 and compares via BEq. -/
def sameShape {Op : Type} [NodeOps Op] [BEq Op] (p o : Op) : Bool :=
  NodeOps.mapChildren (fun _ => 0) p == NodeOps.mapChildren (fun _ => 0) o

-- E-match: find all substitutions making the pattern match a given class.
-- Uses `root` (non-compressing) to avoid threading e-graph state.
mutual
partial def ematch {Op : Type} [NodeOps Op] [BEq Op] [Hashable Op]
    (g : EGraph Op) (pattern : Pattern Op) (classId : EClassId)
    (subst : Substitution := .empty) : MatchResult :=
  let canonId := g.unionFind.root classId
  match pattern with
  | .patVar pv =>
    match subst.extend pv canonId with
    | some s => [s]
    | none => []
  | .node skelOp subpats =>
    match g.classes.get? canonId with
    | none => []
    | some eclass =>
      eclass.nodes.foldl (init := []) fun acc node =>
        if sameShape skelOp node.op then
          let children := NodeOps.children node.op
          matchPairs g subpats children subst acc
        else acc

partial def matchPairs {Op : Type} [NodeOps Op] [BEq Op] [Hashable Op]
    (g : EGraph Op) (pats : List (Pattern Op))
    (children : List EClassId) (subst : Substitution) (acc : MatchResult) : MatchResult :=
  match pats, children with
  | [], [] => acc ++ [subst]
  | p :: ps, c :: cs =>
    let results := ematch g p c subst
    results.foldl (fun a s => matchPairs g ps cs s a) acc
  | _, _ => acc  -- arity mismatch
end

section EMatchDefs

variable {Op : Type} [NodeOps Op] [BEq Op] [Hashable Op]

/-- Search for all instances of a pattern in the entire e-graph. -/
def searchPattern (g : EGraph Op) (pattern : Pattern Op) : List (EClassId × Substitution) :=
  g.classes.fold (fun acc classId _ =>
    let results := ematch g pattern classId
    acc ++ results.map (classId, ·)) []

/-- Instantiate a pattern with a substitution, adding nodes to the e-graph.
    Uses `replaceChildren` to construct ops from pattern skeletons. -/
partial def instantiate (g : EGraph Op) (pattern : Pattern Op) (subst : Substitution)
    : Option (EClassId × EGraph Op) :=
  match pattern with
  | .patVar pv =>
    match subst.lookup pv with
    | some id => some (id, g)
    | none => none
  | .node skelOp subpats =>
    let rec go (g : EGraph Op) (pats : List (Pattern Op)) (ids : List EClassId)
        : Option (List EClassId × EGraph Op) :=
      match pats with
      | [] => some (ids.reverse, g)
      | p :: ps =>
        match instantiate g p subst with
        | none => none
        | some (id, g') => go g' ps (id :: ids)
    match go g subpats [] with
    | none => none
    | some (childIds, g') =>
      let newOp := NodeOps.replaceChildren skelOp childIds
      some (g'.add ⟨newOp⟩)

/-- A rewrite rule for equality saturation.
    Optionally includes a side condition that must pass before the rule fires. -/
structure RewriteRule (Op : Type) [BEq Op] [Hashable Op] where
  name : String
  lhs : Pattern Op
  rhs : Pattern Op
  sideCondCheck : Option (EGraph Op → Substitution → Bool) := none

/-- Apply a rewrite rule at a specific class. -/
def applyRuleAt (g : EGraph Op) (rule : RewriteRule Op) (classId : EClassId) : EGraph Op :=
  let results := ematch g rule.lhs classId
  results.foldl (fun acc subst =>
    let condMet := match rule.sideCondCheck with
      | some check => check acc subst
      | none => true
    if !condMet then acc
    else
      match instantiate acc rule.rhs subst with
      | none => acc
      | some (rhsId, acc') =>
        let canonLhs := acc'.unionFind.root classId
        let canonRhs := acc'.unionFind.root rhsId
        if canonLhs == canonRhs then acc'
        else acc'.merge classId rhsId
  ) g

/-- Apply a rule to all classes in the e-graph. -/
def applyRule (g : EGraph Op) (rule : RewriteRule Op) : EGraph Op :=
  let allClasses := g.classes.toList.map (·.1)
  allClasses.foldl (fun acc classId => applyRuleAt acc rule classId) g

/-- Apply a list of rules once across the entire e-graph. -/
def applyRules (g : EGraph Op) (rules : List (RewriteRule Op)) : EGraph Op :=
  rules.foldl applyRule g

end EMatchDefs

end LambdaSat
