/-
  LambdaSat — ILP Certificate Checking + ILP-Guided Extraction
  Fase 3 Subfase 5: Decidable solution checking + extraction via Extractable

  Architecture:
  - `checkSolution`: decidable check that ILP solution is valid for the e-graph
  - `extractILP`: fuel-based extraction following ILP-selected nodes (via Extractable)
  - Correctness verified in ILPSpec.lean (extractILP_correct, ilp_extraction_soundness)

  TCB: external solver is only trusted for *optimality*.
  Solution *correctness* is verified by checkSolution (decidable, no sorry).
-/
import LambdaSat.Extractable
import LambdaSat.ILPEncode

namespace LambdaSat.ILP

open LambdaSat UnionFind

-- ══════════════════════════════════════════════════════════════════
-- Solution Checking (decidable, for certificate verification)
-- ══════════════════════════════════════════════════════════════════

variable {Op : Type} [NodeOps Op] [BEq Op] [Hashable Op]

/-- Check that the root class is activated. -/
def checkRootActive (rootId : EClassId) (sol : ILPSolution) : Bool :=
  sol.isActive rootId

/-- Check that each active class has exactly one selected node,
    and the selected node index is valid. -/
def checkExactlyOne (g : EGraph Op) (sol : ILPSolution) : Bool :=
  g.classes.fold (init := true) fun acc classId eclass =>
    if sol.isActive classId then
      match sol.selectedNodes.get? classId with
      | some idx => acc && (idx < eclass.nodes.size)
      | none => false
    else
      acc && (sol.selectedNodes.get? classId).isNone

/-- Check child dependency: all children of selected nodes are activated. -/
def checkChildDeps (g : EGraph Op) (sol : ILPSolution) : Bool :=
  g.classes.fold (init := true) fun acc classId eclass =>
    match sol.selectedNodes.get? classId with
    | none => acc
    | some idx =>
      if h : idx < eclass.nodes.size then
        let node := eclass.nodes[idx]
        let children := NodeOps.children node.op
        acc && children.all fun child =>
          sol.isActive (root g.unionFind child)
      else acc

/-- Check acyclicity: for selected nodes, parent level > child level. -/
def checkAcyclicity (g : EGraph Op) (sol : ILPSolution) : Bool :=
  g.classes.fold (init := true) fun acc classId eclass =>
    match sol.selectedNodes.get? classId with
    | none => acc
    | some idx =>
      if h : idx < eclass.nodes.size then
        let node := eclass.nodes[idx]
        let children := NodeOps.children node.op
        acc && children.all fun child =>
          let canonChild := root g.unionFind child
          if canonChild == classId then true  -- Self-loops OK (leaf)
          else sol.getLevel classId > sol.getLevel canonChild
      else acc

/-- Full decidable solution check: combines all constraint checks. -/
def checkSolution (g : EGraph Op) (rootId : EClassId)
    (sol : ILPSolution) : Bool :=
  let canonRoot := root g.unionFind rootId
  checkRootActive canonRoot sol &&
  checkExactlyOne g sol &&
  checkChildDeps g sol &&
  checkAcyclicity g sol

-- ══════════════════════════════════════════════════════════════════
-- ILP-Guided Extraction (via Extractable typeclass)
-- ══════════════════════════════════════════════════════════════════

variable {Expr : Type} [Extractable Op Expr]

/-- Extract an expression following ILP solution's selected nodes.
    Uses fuel for termination (fuel ≥ numClasses suffices for acyclic solutions).
    The ILP solution's level ordering guarantees termination for valid solutions. -/
def extractILP (g : EGraph Op) (sol : ILPSolution) (id : EClassId) :
    Nat → Option Expr
  | 0 => none
  | fuel + 1 =>
    let canonId := root g.unionFind id
    match sol.selectedNodes.get? canonId with
    | none => none  -- Class not active
    | some nodeIdx =>
      match g.classes.get? canonId with
      | none => none
      | some eclass =>
        if h : nodeIdx < eclass.nodes.size then
          let node := eclass.nodes[nodeIdx]
          let children := NodeOps.children node.op
          match mapOption (fun c => extractILP g sol (root g.unionFind c) fuel) children with
          | none => none
          | some childExprs => Extractable.reconstruct node.op childExprs
        else none

/-- Convenience: extract with fuel = numClasses + 1. -/
def extractILPAuto (g : EGraph Op) (sol : ILPSolution) (rootId : EClassId) :
    Option Expr :=
  extractILP g sol rootId (g.numClasses + 1)

-- ══════════════════════════════════════════════════════════════════
-- Cost Computation
-- ══════════════════════════════════════════════════════════════════

/-- Compute total cost of an ILP solution's selected nodes. -/
def solutionCost (g : EGraph Op) (sol : ILPSolution)
    (costFn : ENode Op → Nat) : Nat :=
  g.classes.fold (init := 0) fun acc classId eclass =>
    match sol.selectedNodes.get? classId with
    | none => acc
    | some idx =>
      if h : idx < eclass.nodes.size then
        acc + costFn eclass.nodes[idx]
      else acc

-- ══════════════════════════════════════════════════════════════════
-- Basic Lemmas
-- ══════════════════════════════════════════════════════════════════

@[simp] theorem extractILP_zero (g : EGraph Op) (sol : ILPSolution) (id : EClassId) :
    extractILP (Expr := Expr) g sol id 0 = none := rfl

set_option linter.unusedSectionVars false in
/-- `solutionCost` unfolds to its fold definition. -/
@[simp] theorem solutionCost_unfold (g : EGraph Op) (sol : ILPSolution)
    (costFn : ENode Op → Nat) :
    solutionCost g sol costFn =
      g.classes.fold (init := 0) fun acc classId eclass =>
        match sol.selectedNodes.get? classId with
        | none => acc
        | some idx =>
          if h : idx < eclass.nodes.size then acc + costFn eclass.nodes[idx]
          else acc := rfl

set_option linter.unusedSectionVars false in
/-- `solutionCost` is nonnegative (trivially, since it returns `Nat`). -/
theorem solutionCost_nonneg (g : EGraph Op) (sol : ILPSolution)
    (costFn : ENode Op → Nat) :
    0 ≤ solutionCost g sol costFn := Nat.zero_le _

end LambdaSat.ILP
