/-
  LambdaSat — Integration Tests
  Fase 4 Subfase 4: Concrete arithmetic domain + end-to-end pipeline tests.

  Defines a simple arithmetic domain (Add, Mul, Const, Var) and instantiates
  all LambdaSat typeclasses to test extraction, ILP extraction, saturation,
  and the optimization pipeline.
-/
import LambdaSat

open LambdaSat LambdaSat.ILP UnionFind

-- ══════════════════════════════════════════════════════════════════
-- Section 1: Arithmetic Operation Type
-- ══════════════════════════════════════════════════════════════════

/-- Simple arithmetic operations for testing. -/
inductive ArithOp where
  | const : Nat → ArithOp      -- constant literal
  | var   : Nat → ArithOp      -- external variable (index into env)
  | add   : EClassId → EClassId → ArithOp  -- addition
  | mul   : EClassId → EClassId → ArithOp  -- multiplication
  deriving Repr, Inhabited, DecidableEq

instance : BEq ArithOp where
  beq a b := decide (a = b)

instance : Hashable ArithOp where
  hash
    | .const n => mixHash 1 (hash n)
    | .var n => mixHash 2 (hash n)
    | .add l r => mixHash 3 (mixHash (hash l) (hash r))
    | .mul l r => mixHash 4 (mixHash (hash l) (hash r))

instance : LawfulBEq ArithOp where
  eq_of_beq {a b} h := by simp [BEq.beq] at h; exact h
  rfl {a} := by simp [BEq.beq]

instance : LawfulHashable ArithOp where
  hash_eq {a b} h := by
    have := eq_of_beq h
    subst this; rfl

-- ══════════════════════════════════════════════════════════════════
-- Section 2: NodeOps Instance
-- ══════════════════════════════════════════════════════════════════

instance : NodeOps ArithOp where
  children
    | .const _ => []
    | .var _ => []
    | .add l r => [l, r]
    | .mul l r => [l, r]
  mapChildren f
    | .const n => .const n
    | .var n => .var n
    | .add l r => .add (f l) (f r)
    | .mul l r => .mul (f l) (f r)
  replaceChildren op cs :=
    match op, cs with
    | .add _ _, [l, r] => .add l r
    | .mul _ _, [l, r] => .mul l r
    | op, _ => op
  mapChildren_children f op := by
    cases op <;> simp

-- ══════════════════════════════════════════════════════════════════
-- Section 3: Arithmetic Expression Type + Extractable/EvalExpr
-- ══════════════════════════════════════════════════════════════════

/-- Extracted arithmetic expression (AST). -/
inductive ArithExpr where
  | const : Nat → ArithExpr
  | var   : Nat → ArithExpr
  | add   : ArithExpr → ArithExpr → ArithExpr
  | mul   : ArithExpr → ArithExpr → ArithExpr
  deriving Repr, Inhabited, DecidableEq

instance : Extractable ArithOp ArithExpr where
  reconstruct op childExprs :=
    match op, childExprs with
    | .const n, [] => some (.const n)
    | .var n, [] => some (.var n)
    | .add _ _, [l, r] => some (.add l r)
    | .mul _ _, [l, r] => some (.mul l r)
    | _, _ => none

/-- Evaluate an arithmetic expression. Defined separately to avoid
    recursive typeclass instance resolution issues. -/
def evalArithExpr : ArithExpr → (Nat → Nat) → Nat
  | .const n, _ => n
  | .var i, env => env i
  | .add l r, env => evalArithExpr l env + evalArithExpr r env
  | .mul l r, env => evalArithExpr l env * evalArithExpr r env

instance : EvalExpr ArithExpr Nat where
  evalExpr := evalArithExpr

instance : NodeSemantics ArithOp Nat where
  evalOp op env v :=
    match op with
    | .const n => n
    | .var i => env i
    | .add l r => v l + v r
    | .mul l r => v l * v r
  evalOp_ext op env v v' h := by
    cases op with
    | const _ => rfl
    | var _ => rfl
    | add l r =>
      show v l + v r = v' l + v' r
      rw [h l (by simp [NodeOps.children]), h r (by simp [NodeOps.children])]
    | mul l r =>
      show v l * v r = v' l * v' r
      rw [h l (by simp [NodeOps.children]), h r (by simp [NodeOps.children])]
  evalOp_mapChildren f op env v := by
    cases op <;> rfl

-- ══════════════════════════════════════════════════════════════════
-- Section 4: Helper — Build e-graphs for testing
-- ══════════════════════════════════════════════════════════════════

/-- Add a constant node and return its class ID + updated graph. -/
def addConst (g : EGraph ArithOp) (n : Nat) : EClassId × EGraph ArithOp :=
  g.add ⟨.const n⟩

/-- Add a variable node and return its class ID + updated graph. -/
def addVar (g : EGraph ArithOp) (i : Nat) : EClassId × EGraph ArithOp :=
  g.add ⟨.var i⟩

/-- Add an add node and return its class ID + updated graph. -/
def addAddNode (g : EGraph ArithOp) (l r : EClassId) : EClassId × EGraph ArithOp :=
  g.add ⟨.add l r⟩

/-- Add a mul node and return its class ID + updated graph. -/
def addMulNode (g : EGraph ArithOp) (l r : EClassId) : EClassId × EGraph ArithOp :=
  g.add ⟨.mul l r⟩

-- ══════════════════════════════════════════════════════════════════
-- Test 1: Basic greedy extraction from a leaf (const)
-- ══════════════════════════════════════════════════════════════════

/-- Build a graph with just `const 42`, compute costs, extract. -/
def test1_constExtraction : IO Bool := do
  let g0 : EGraph ArithOp := .empty
  let (rootId, g1) := addConst g0 42
  let costFn : ENode ArithOp → Nat := fun _ => 1
  let g2 := g1.computeCosts costFn
  let result : Option ArithExpr := extractAuto g2 rootId
  return result == some (.const 42)

-- ══════════════════════════════════════════════════════════════════
-- Test 2: Extraction of (x + 3) where x is var 0
-- ══════════════════════════════════════════════════════════════════

def test2_addExtraction : IO Bool := do
  let g0 : EGraph ArithOp := .empty
  let (xId, g1) := addVar g0 0
  let (c3Id, g2) := addConst g1 3
  let (rootId, g3) := addAddNode g2 xId c3Id
  let costFn : ENode ArithOp → Nat := fun _ => 1
  let g4 := g3.computeCosts costFn
  let result : Option ArithExpr := extractAuto g4 rootId
  return result == some (.add (.var 0) (.const 3))

-- ══════════════════════════════════════════════════════════════════
-- Test 3: Extraction of (x * (y + 2))
-- ══════════════════════════════════════════════════════════════════

def test3_nestedExtraction : IO Bool := do
  let g0 : EGraph ArithOp := .empty
  let (xId, g1) := addVar g0 0
  let (yId, g2) := addVar g1 1
  let (c2Id, g3) := addConst g2 2
  let (sumId, g4) := addAddNode g3 yId c2Id
  let (rootId, g5) := addMulNode g4 xId sumId
  let costFn : ENode ArithOp → Nat := fun _ => 1
  let g6 := g5.computeCosts costFn
  let result : Option ArithExpr := extractAuto g6 rootId
  return result == some (.mul (.var 0) (.add (.var 1) (.const 2)))

-- ══════════════════════════════════════════════════════════════════
-- Test 4: Saturation with commutativity of add
-- ══════════════════════════════════════════════════════════════════

/-- Rewrite rule: a + b ↦ b + a -/
def addCommRule : RewriteRule ArithOp where
  name := "add_comm"
  lhs := .node (.add 0 0) [.patVar 0, .patVar 1]
  rhs := .node (.add 0 0) [.patVar 1, .patVar 0]

def test4_saturation : IO Bool := do
  let g0 : EGraph ArithOp := .empty
  let (xId, g1) := addVar g0 0
  let (yId, g2) := addVar g1 1
  let (_rootId, g3) := addAddNode g2 xId yId
  let config : SaturationConfig := { maxIterations := 5, maxNodes := 50, maxClasses := 20 }
  let result := saturate g3 [addCommRule] config
  return result.graph.numNodes >= g3.numNodes

-- ══════════════════════════════════════════════════════════════════
-- Test 5: Greedy optimization pipeline
-- ══════════════════════════════════════════════════════════════════

def test5_optimizePipeline : IO Bool := do
  let g0 : EGraph ArithOp := .empty
  let (xId, g1) := addVar g0 0
  let (c0Id, g2) := addConst g1 0
  let (rootId, g3) := addAddNode g2 xId c0Id
  let costFn : ENode ArithOp → Nat
    | ⟨.const _⟩ => 0
    | ⟨.var _⟩ => 1
    | ⟨.add _ _⟩ => 2
    | ⟨.mul _ _⟩ => 3
  let pair : Option ArithExpr × OptStats := optimizeExpr g3 rootId [] costFn
  return pair.1.isSome && pair.2.extraction == "greedy"

-- ══════════════════════════════════════════════════════════════════
-- Test 6: ILP extraction with hand-crafted solution
-- ══════════════════════════════════════════════════════════════════

def test6_ilpExtraction : IO Bool := do
  let g0 : EGraph ArithOp := .empty
  let (c5Id, g1) := addConst g0 5
  let (c3Id, g2) := addConst g1 3
  let (rootId, g3) := addAddNode g2 c5Id c3Id
  let canonRoot := root g3.unionFind rootId
  let canonC5 := root g3.unionFind c5Id
  let canonC3 := root g3.unionFind c3Id
  let sol : ILPSolution := {
    selectedNodes := Std.HashMap.ofList [(canonRoot, 0), (canonC5, 0), (canonC3, 0)]
    activatedClasses := Std.HashMap.ofList [(canonRoot, true), (canonC5, true), (canonC3, true)]
    levels := Std.HashMap.ofList [(canonRoot, 2), (canonC5, 0), (canonC3, 0)]
    objectiveValue := 3
  }
  let result : Option ArithExpr := extractILP g3 sol rootId (g3.numClasses + 1)
  return result.isSome

-- ══════════════════════════════════════════════════════════════════
-- Test 7: ILP checkSolution
-- ══════════════════════════════════════════════════════════════════

def test7_checkSolution : IO Bool := do
  let g0 : EGraph ArithOp := .empty
  let (c5Id, g1) := addConst g0 5
  let (c3Id, g2) := addConst g1 3
  let (rootId, g3) := addAddNode g2 c5Id c3Id
  let canonRoot := root g3.unionFind rootId
  let canonC5 := root g3.unionFind c5Id
  let canonC3 := root g3.unionFind c3Id
  let sol : ILPSolution := {
    selectedNodes := Std.HashMap.ofList [(canonRoot, 0), (canonC5, 0), (canonC3, 0)]
    activatedClasses := Std.HashMap.ofList [(canonRoot, true), (canonC5, true), (canonC3, true)]
    levels := Std.HashMap.ofList [(canonRoot, 2), (canonC5, 0), (canonC3, 0)]
    objectiveValue := 3
  }
  return checkSolution g3 rootId sol

-- ══════════════════════════════════════════════════════════════════
-- Test 8: Parallel saturation (falls back to sequential for small graph)
-- ══════════════════════════════════════════════════════════════════

def test8_parallelSaturation : IO Bool := do
  let g0 : EGraph ArithOp := .empty
  let (xId, g1) := addVar g0 0
  let (yId, g2) := addVar g1 1
  let (_rootId, g3) := addAddNode g2 xId yId
  let config : ParallelSatConfig := {
    maxIterations := 5, maxNodes := 50, maxClasses := 20,
    numTasks := 2, parallelThreshold := 1
  }
  let result ← parallelSaturate g3 [addCommRule] config
  return result.graph.numNodes >= g3.numNodes

-- ══════════════════════════════════════════════════════════════════
-- Test Runner
-- ══════════════════════════════════════════════════════════════════

def runTest (name : String) (test : IO Bool) : IO Bool := do
  let result ← test
  if result then
    IO.println s!"  PASS {name}"
  else
    IO.println s!"  FAIL {name}"
  return result

def main : IO UInt32 := do
  IO.println "LambdaSat Integration Tests"
  IO.println "==========================="
  let mut passed := 0
  let mut total := 0

  let tests : List (String × IO Bool) := [
    ("T1: const extraction", test1_constExtraction),
    ("T2: add extraction (x + 3)", test2_addExtraction),
    ("T3: nested extraction (x * (y + 2))", test3_nestedExtraction),
    ("T4: saturation with add_comm", test4_saturation),
    ("T5: greedy optimization pipeline", test5_optimizePipeline),
    ("T6: ILP extraction (hand-crafted)", test6_ilpExtraction),
    ("T7: ILP checkSolution", test7_checkSolution),
    ("T8: parallel saturation", test8_parallelSaturation)
  ]

  for (name, test) in tests do
    total := total + 1
    let ok ← runTest name test
    if ok then passed := passed + 1

  IO.println s!"\n{passed}/{total} tests passed"
  if passed == total then
    IO.println "All tests passed!"
    return 0
  else
    IO.println "Some tests FAILED"
    return 1
