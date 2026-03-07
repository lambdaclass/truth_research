/-
  LambdaSat — ILP Encoding for E-Graph Extraction
  Fase 3 Subfase 4: Encode e-graph → ILP problem

  Encodes the ILP formulation from TENSAT (Yang et al., 2021):
  - One nodeSelect variable per node in each class
  - One classActive variable per class
  - One level variable per class (for acyclicity)
  - Constraints: root activation, exactly-one, child dependency, acyclicity
-/
import LambdaSat.ILP

namespace LambdaSat.ILP

open LambdaSat UnionFind

-- ══════════════════════════════════════════════════════════════════
-- Encoding: E-graph → ILP Problem
-- ══════════════════════════════════════════════════════════════════

variable {Op : Type} [NodeOps Op] [BEq Op] [Hashable Op]

/-- Get the canonical (root) class IDs for all children of a node. -/
private def canonicalChildren (g : EGraph Op) (node : ENode Op) : List EClassId :=
  (NodeOps.children node.op).map (root g.unionFind ·)

/-- Collect all canonical class IDs in the e-graph. -/
private def collectClasses (g : EGraph Op) : Array EClassId :=
  g.classes.fold (fun acc classId _ => acc.push classId) #[]

/-- Encode an e-graph extraction problem as an ILP problem.
    `rootId` is the class from which we extract.
    `costFn` maps nodes to their local cost (e.g., mul=1, add=0). -/
def encodeEGraph (g : EGraph Op) (rootId : EClassId)
    (costFn : ENode Op → Nat) : ILPProblem := Id.run do
  let canonRoot := root g.unionFind rootId
  let allClasses := collectClasses g
  let numC := allClasses.size
  let bigM : Int := (numC : Int) + 1

  -- Phase 1: Bounds
  let mut bounds : Array VarBound := #[]

  for classId in allClasses do
    bounds := bounds.push { var := .classActive classId, lo := 0, hi := 1 }
    bounds := bounds.push { var := .level classId, lo := 0, hi := numC }
    match g.classes.get? classId with
    | none => pure ()
    | some eclass =>
      for h : idx in [:eclass.nodes.size] do
        bounds := bounds.push { var := .nodeSelect classId idx, lo := 0, hi := 1 }

  -- Phase 2: Objective — minimize Σ cost(n) · s_n
  let mut objective : Array ObjTerm := #[]
  for classId in allClasses do
    match g.classes.get? classId with
    | none => pure ()
    | some eclass =>
      for h : idx in [:eclass.nodes.size] do
        let node := eclass.nodes[idx]
        let cost := costFn node
        if cost > 0 then
          objective := objective.push { cost := cost, var := .nodeSelect classId idx }

  -- Phase 3: Constraints
  let mut constraints : Array ILPConstraint := #[]

  -- C1: Root activation: a_root = 1
  constraints := constraints.push {
    name := "root_active"
    terms := #[{ coeff := 1, var := .classActive canonRoot }]
    op := .eq
    rhs := 1
  }

  -- C2: Exactly-one per class: Σ s_n - a_c = 0
  for classId in allClasses do
    match g.classes.get? classId with
    | none => pure ()
    | some eclass =>
      let mut terms : Array LinTerm := #[]
      for h : idx in [:eclass.nodes.size] do
        terms := terms.push { coeff := 1, var := .nodeSelect classId idx }
      terms := terms.push { coeff := -1, var := .classActive classId }
      constraints := constraints.push {
        name := s!"exactly_one_{classId}"
        terms := terms
        op := .eq
        rhs := 0
      }

  -- C3: Child dependency: s_n - a_{child} ≤ 0
  for classId in allClasses do
    match g.classes.get? classId with
    | none => pure ()
    | some eclass =>
      for h : idx in [:eclass.nodes.size] do
        let node := eclass.nodes[idx]
        let children := canonicalChildren g node
        for child in children do
          constraints := constraints.push {
            name := s!"child_dep_{classId}_{idx}_{child}"
            terms := #[
              { coeff := 1, var := .nodeSelect classId idx },
              { coeff := -1, var := .classActive child }
            ]
            op := .le
            rhs := 0
          }

  -- C4: Acyclicity: -L_c + L_child - M·s_n ≤ M - 1
  for classId in allClasses do
    match g.classes.get? classId with
    | none => pure ()
    | some eclass =>
      for h : idx in [:eclass.nodes.size] do
        let node := eclass.nodes[idx]
        let children := canonicalChildren g node
        for child in children do
          if child != classId then
            constraints := constraints.push {
              name := s!"acyclic_{classId}_{idx}_{child}"
              terms := #[
                { coeff := -1, var := .level classId },
                { coeff := 1, var := .level child },
                { coeff := -bigM, var := .nodeSelect classId idx }
              ]
              op := .le
              rhs := bigM - 1
            }

  return { bounds := bounds
         , objective := objective
         , constraints := constraints
         , numClasses := numC
         , rootClassId := canonRoot }

-- ══════════════════════════════════════════════════════════════════
-- Problem Statistics
-- ══════════════════════════════════════════════════════════════════

/-- Statistics about an encoded ILP problem. -/
structure ILPStats where
  numVars        : Nat
  numConstraints : Nat
  numClasses     : Nat
  rootClassId    : EClassId
  deriving Repr, Inhabited

def ILPProblem.stats (p : ILPProblem) : ILPStats where
  numVars := p.numVars
  numConstraints := p.numConstraints
  numClasses := p.numClasses
  rootClassId := p.rootClassId

-- ══════════════════════════════════════════════════════════════════
-- Feasibility Checking (decidable, for certificate verification)
-- ══════════════════════════════════════════════════════════════════

/-- Evaluate a variable in a solution. -/
def evalVar (sol : ILPSolution) (var : ILPVar) : Int :=
  match var with
  | .nodeSelect classId nodeIdx =>
    match sol.selectedNodes.get? classId with
    | some idx => if idx == nodeIdx then 1 else 0
    | none => 0
  | .classActive classId =>
    if sol.isActive classId then 1 else 0
  | .level classId =>
    (sol.getLevel classId : Int)

/-- Evaluate the LHS of a constraint: Σ coeff_i · var_i. -/
def evalConstraintLHS (sol : ILPSolution) (terms : Array LinTerm) : Int :=
  terms.foldl (fun acc t => acc + t.coeff * evalVar sol t.var) 0

/-- Check if a single constraint is satisfied by the solution. -/
def checkConstraint (sol : ILPSolution) (c : ILPConstraint) : Bool :=
  let lhs := evalConstraintLHS sol c.terms
  match c.op with
  | .le => lhs ≤ c.rhs
  | .ge => lhs ≥ c.rhs
  | .eq => lhs == c.rhs

/-- Check if all bounds are satisfied. -/
def checkBounds (sol : ILPSolution) (bounds : Array VarBound) : Bool :=
  bounds.all fun b =>
    let val := evalVar sol b.var
    b.lo ≤ val && val ≤ b.hi

/-- Decidable feasibility check: does the solution satisfy all constraints and bounds? -/
def ILPSolution.isFeasible (sol : ILPSolution) (prob : ILPProblem) : Bool :=
  checkBounds sol prob.bounds && prob.constraints.all (checkConstraint sol ·)

-- ══════════════════════════════════════════════════════════════════
-- Solution from raw variable assignment
-- ══════════════════════════════════════════════════════════════════

/-- Build an ILPSolution from a raw variable→value map (for solver output parsing). -/
def ILPSolution.fromVarMap (varMap : Std.HashMap String Int)
    (prob : ILPProblem) : ILPSolution := Id.run do
  let mut selectedNodes : Std.HashMap EClassId Nat := Std.HashMap.ofList []
  let mut activatedClasses : Std.HashMap EClassId Bool := Std.HashMap.ofList []
  let mut levels : Std.HashMap EClassId Nat := Std.HashMap.ofList []
  let mut objValue : Nat := 0

  for bound in prob.bounds do
    let varName := toString bound.var
    let val := varMap.get? varName |>.getD 0
    match bound.var with
    | .nodeSelect classId nodeIdx =>
      if val > 0 then
        selectedNodes := selectedNodes.insert classId nodeIdx
    | .classActive classId =>
      activatedClasses := activatedClasses.insert classId (val > 0)
    | .level classId =>
      levels := levels.insert classId val.toNat

  for obj in prob.objective do
    let varName := toString obj.var
    let val := varMap.get? varName |>.getD 0
    if val > 0 then
      objValue := objValue + obj.cost

  return { selectedNodes := selectedNodes
         , activatedClasses := activatedClasses
         , levels := levels
         , objectiveValue := objValue }

-- ══════════════════════════════════════════════════════════════════
-- Simp lemmas and soundness theorems
-- ══════════════════════════════════════════════════════════════════

/-- `evalVar` unfolds for `nodeSelect`. -/
@[simp] theorem evalVar_nodeSelect (sol : ILPSolution) (cid : EClassId) (nid : Nat) :
    evalVar sol (.nodeSelect cid nid) =
      match sol.selectedNodes.get? cid with
      | some idx => if idx == nid then 1 else 0
      | none => 0 := rfl

/-- `evalVar` unfolds for `classActive`. -/
@[simp] theorem evalVar_classActive (sol : ILPSolution) (cid : EClassId) :
    evalVar sol (.classActive cid) =
      if sol.isActive cid then 1 else 0 := rfl

/-- `evalVar` unfolds for `level`. -/
@[simp] theorem evalVar_level (sol : ILPSolution) (cid : EClassId) :
    evalVar sol (.level cid) = (sol.getLevel cid : Int) := rfl

/-- If all bounds are satisfied, each variable is within its bounds. -/
theorem checkBounds_sound (sol : ILPSolution) (bounds : Array VarBound)
    (h : checkBounds sol bounds = true) :
    ∀ b ∈ bounds, b.lo ≤ evalVar sol b.var ∧ evalVar sol b.var ≤ b.hi := by
  unfold checkBounds at h
  intro b hb
  have hb_elem := Array.all_eq_true_iff_forall_mem.mp h b hb
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hb_elem
  exact hb_elem

/-- If an ILP solution is feasible, all bounds and constraints are satisfied. -/
theorem isFeasible_sound (sol : ILPSolution) (prob : ILPProblem)
    (h : sol.isFeasible prob = true) :
    checkBounds sol prob.bounds = true ∧
    ∀ c ∈ prob.constraints, checkConstraint sol c = true := by
  unfold ILPSolution.isFeasible at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1, Array.all_eq_true_iff_forall_mem.mp h.2⟩

-- ══════════════════════════════════════════════════════════════════
-- Encoding Structural Properties (F9S9)
-- ══════════════════════════════════════════════════════════════════

section EncodingProperties

variable {Op : Type} [NodeOps Op] [BEq Op] [Hashable Op]
  [LawfulBEq Op] [LawfulHashable Op]

private theorem fold_push_keys_size {α β : Type _} [BEq α] [Hashable α]
    [EquivBEq α] [LawfulHashable α] (m : Std.HashMap α β) :
    (m.fold (fun acc k _ => acc.push k) #[]).size = m.size := by
  rw [Std.HashMap.fold_eq_foldl_toList, ← Std.HashMap.length_toList (m := m)]
  suffices ∀ (init : Array α) (l : List (α × β)),
    (List.foldl (fun acc b => acc.push b.1) init l).size = init.size + l.length by
    simp
  intro init l
  induction l generalizing init with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih]; simp [Array.size_push]; omega

set_option linter.unusedSectionVars false in
/-- `encodeEGraph` stores the canonical root class ID. -/
theorem encodeEGraph_rootClassId (g : EGraph Op) (rootId : EClassId)
    (costFn : ENode Op → Nat) :
    (encodeEGraph g rootId costFn).rootClassId = root g.unionFind rootId := by
  unfold encodeEGraph; rfl

set_option linter.unusedSectionVars false in
/-- `encodeEGraph` records the number of e-classes. -/
theorem encodeEGraph_numClasses (g : EGraph Op) (rootId : EClassId)
    (costFn : ENode Op → Nat) :
    (encodeEGraph g rootId costFn).numClasses = g.classes.size := by
  unfold encodeEGraph
  exact fold_push_keys_size g.classes

end EncodingProperties

end LambdaSat.ILP
