# Test Specifications: LambdaSat v1.2.0

Generated: 2026-02-25 (manual — Gemini unavailable)
Project: /Users/manuelpuebla/Documents/claudio/lambdasat-lean
Toolchain: leanprover/lean4:v4.26.0
Mathlib: no

> **Este archivo es leído por otra sesión de Claude Code que escribe
> los archivos .lean de test. NO contiene código compilable.**
>
> LambdaSat es self-contained (sin Mathlib). Las propiedades SlimCheck
> requieren agregar `import Mathlib.Testing.SlimCheck` + implementar
> `SampleableExt`/`Shrinkable` para tipos custom (`EGraph`, `Pattern`, etc.).
> Todas las propiedades están marcadas `NOT_YET_RUNNABLE` salvo las que
> operen sobre tipos estándar (`Nat`, `Int`, `List`, `Bool`).

## Instrucciones para la sesión de testing

1. Leer este archivo completo
2. Para cada nodo, leer el código fuente real (`scout.py` + `Read`)
3. Escribir `Tests/Properties/{NodeName}.lean` con las propiedades especificadas
4. Escribir `Tests/Integration/{NodeName}.lean` con los integration tests
5. Compilar cada archivo con `lake env lean Tests/.../*.lean` hasta que pase
6. Usar `/ask-lean` o `/ask-dojo` si faltan tácticas o instancias

### Convenciones obligatorias

**Properties** (`Tests/Properties/{Name}.lean`):
- `import Mathlib.Testing.SlimCheck` (si Mathlib disponible)
- Cada propiedad como `example` o `theorem` con `slim_check` tactic
- Comentario con prioridad: `-- P0, INVARIANT: descripción`
- Si un tipo necesita `SampleableExt` y no existe: `-- NOT_YET_RUNNABLE`

**Integration** (`Tests/Integration/{Name}.lean`):
- Cada test imprime `[PASS] nombre` o `[FAIL] nombre`
- Función `main : IO UInt32` que retorna 0 si todo pasa, 1 si hay fallos
- Pattern: `def T1_name : IO Bool := do ...`

### Ejecución (la hace la sesión implementadora)

```bash
lake env lean Tests/Properties/*.lean
lake env lean Tests/Integration/*.lean
```

---

## Especificaciones por nodo

### F1S2 — UnionFind

- **Tipo**: FUNDACIONAL
- **Archivos fuente**: `LambdaSat/UnionFind.lean`
- **Target properties**: `Tests/Properties/UnionFind.lean`
- **Target integration**: `Tests/Integration/UnionFind.lean`

PROPERTIES:
- [P1] P0 IDEMPOTENCY: find is idempotent — root(root(x)) = root(x)
  Sketch: example (uf : UF) (x : Nat) : root (root uf x).1 x = root uf x := ...
  SampleableExt: yes (UF needs custom instance)
  Risk: path compression corrupts root identity

- [P2] P0 INVARIANT: merge preserves parent array size
  Sketch: example (uf : UF) (a b : Nat) : (merge uf a b).parent.size = uf.parent.size := ...
  SampleableExt: yes
  Risk: merge silently grows or shrinks array

- [P3] P1 COMMUTATIVITY: merge(a,b) and merge(b,a) produce equivalent roots
  Sketch: example (uf : UF) (a b x : Nat) : root (merge uf a b) x = root (merge uf b a) x
  SampleableExt: yes
  Risk: merge order affects equivalence classes

- [P4] P1 INVARIANT: root returns value < parent.size (bounded)
  Sketch: example (uf : UF) (huf : WellFormed uf) (x : Nat) (hx : x < uf.parent.size) : (root uf x).2 < uf.parent.size
  SampleableExt: yes
  Risk: out-of-bounds root after path compression

- [P5] P2 PRESERVATION: find preserves WellFormed
  Sketch: example (uf : UF) (huf : WellFormed uf) (x : Nat) : WellFormed (root uf x).1
  SampleableExt: yes
  Risk: path compression breaks UF invariant

INTEGRATION:
- [T1] BASIC: create UF, add elements, merge, find root
  Setup: UF with 5 elements, merge(0,1), merge(2,3), merge(1,3)
  Check: root(0) = root(3), root(0) ≠ root(4)

- [T2] EDGE_CASE: empty UF — find on empty array
  Setup: UF with parent = #[]
  Check: root 0 returns (uf, 0) without crash

- [T3] EDGE_CASE: self-merge — merge(x, x)
  Setup: UF with 3 elements, merge(1, 1)
  Check: root(1) unchanged, parent.size unchanged

- [T4] STRESS: chain merge — merge(0,1), merge(1,2), ..., merge(n-1,n)
  Setup: UF with 20 elements, chain merges
  Check: all elements have same root, parent.size = 20

- [T5] EDGE_CASE: single-element UF
  Setup: UF with parent = #[0]
  Check: root(0) = 0, merge(0,0) no-op

---

### F1S3 — Core (EGraph)

- **Tipo**: FUNDACIONAL
- **Archivos fuente**: `LambdaSat/Core.lean`
- **Target properties**: `Tests/Properties/Core.lean`
- **Target integration**: `Tests/Integration/Core.lean`

PROPERTIES:
- [P1] P0 INVARIANT: add returns valid class ID (< next class counter)
  Sketch: example (g : EGraph ArithOp) (node : ENode ArithOp) : (g.add node).1 is valid class
  SampleableExt: yes (EGraph ArithOp)
  Risk: add creates dangling class reference

- [P2] P0 IDEMPOTENCY: adding same node twice returns same class (hashcons)
  Sketch: example (g : EGraph ArithOp) (n : ENode ArithOp) : let (id1, g1) := g.add n; let (id2, _) := g1.add n; root g1.unionFind id1 = root g1.unionFind id2
  SampleableExt: yes
  Risk: hashcons deduplication broken — creates duplicate classes

- [P3] P1 PRESERVATION: merge preserves number of classes in HashMap
  Sketch: -- merge may not change classes.size immediately (deferred to rebuild)
  SampleableExt: yes
  Risk: merge corrupts class map

- [P4] P1 INVARIANT: rebuild is idempotent — rebuild(rebuild(g)) = rebuild(g)
  Sketch: example (g : EGraph ArithOp) : g.rebuild.rebuild.classes.size = g.rebuild.classes.size
  SampleableExt: yes
  Risk: rebuild oscillates or diverges

INTEGRATION:
- [T1] BASIC: add 3 nodes, verify class count
  Setup: empty graph, add const(1), const(2), add(c1, c2)
  Check: numClasses = 3

- [T2] EDGE_CASE: empty graph — numClasses = 0, numNodes = 0
  Setup: EGraph.empty
  Check: numClasses = 0, numNodes = 0

- [T3] EDGE_CASE: add node with children pointing to nonexistent classes
  Setup: empty graph, add(⟨.add 999 888⟩)
  Check: should succeed (Core doesn't enforce ChildrenBounded at add time)

- [T4] BASIC: merge + rebuild cycle
  Setup: add const(1), add const(2), merge both, rebuild
  Check: both original IDs have same root after rebuild

- [T5] STRESS: add 50 leaf nodes, verify hashcons dedup
  Setup: add const(i) for i in 0..49, then add const(0) again
  Check: second const(0) returns same class as first, numClasses = 50

---

### F2S1 — CoreSpec (EGraphWF)

- **Tipo**: CRITICO
- **Archivos fuente**: `LambdaSat/CoreSpec.lean`
- **Target properties**: `Tests/Properties/CoreSpec.lean`
- **Target integration**: `Tests/Integration/CoreSpec.lean`

PROPERTIES:
- [P1] P0 INVARIANT: egraph_empty_wf — empty graph is well-formed
  Sketch: theorem : EGraphWF (EGraph.empty : EGraph ArithOp) := egraph_empty_wf
  SampleableExt: no (direct theorem application)
  Risk: foundation of all WF reasoning is incorrect

- [P2] P0 PRESERVATION: add preserves WF
  Sketch: example (g : EGraph ArithOp) (hwf : EGraphWF g) (n : ENode ArithOp) : EGraphWF (g.add n).2
  SampleableExt: yes
  Risk: adding nodes breaks invariants

- [P3] P1 PRESERVATION: merge preserves ChildrenBounded
  Sketch: -- merge_preserves_children_bounded already proven
  SampleableExt: yes
  Risk: merge breaks child reference validity

INTEGRATION:
- [T1] BASIC: construct well-formed graph, verify WF properties hold
  Setup: empty → add const(1) → add const(2) → add add(c1,c2)
  Check: HashconsConsistent, ClassesConsistent, ChildrenBounded all true (via decidable checks or theorem application)

- [T2] EDGE_CASE: verify egraph_empty_wf compiles and applies
  Setup: `#check @egraph_empty_wf`
  Check: type-checks without error

---

### F2S2 — EMatch

- **Tipo**: PARALELO
- **Archivos fuente**: `LambdaSat/EMatch.lean`, `LambdaSat/EMatchSpec.lean`
- **Target properties**: `Tests/Properties/EMatch.lean`
- **Target integration**: `Tests/Integration/EMatch.lean`

PROPERTIES:
- [P1] P0 SOUNDNESS: ematchF returns substitutions that satisfy pattern
  Sketch: -- ematchF_sound already proven as theorem
  SampleableExt: yes (Pattern ArithOp, EGraph ArithOp)
  Risk: e-matching returns incorrect substitutions → unsound rewrites

- [P2] P1 INVARIANT: ematchF with fuel=0 returns empty list
  Sketch: example (g : EGraph ArithOp) (pat : Pattern ArithOp) (cid : EClassId) : ematchF 0 g pat cid = []
  SampleableExt: no
  Risk: fuel=0 doesn't terminate matching

- [P3] P1 PRESERVATION: ematchF doesn't modify the e-graph (read-only)
  Sketch: -- ematchF returns List Substitution, no modified graph
  SampleableExt: no (structural — ematchF signature doesn't return EGraph)
  Risk: n/a (by type)

INTEGRATION:
- [T1] BASIC: match pattern ?x + ?y against class containing add(c1, c2)
  Setup: graph with const(1), const(2), add(c1,c2); pattern = .node (.add (.pvar 0) (.pvar 1))
  Check: ematchF returns non-empty list with correct substitution

- [T2] EDGE_CASE: match against empty graph
  Setup: empty graph, any pattern
  Check: ematchF returns []

- [T3] EDGE_CASE: match leaf pattern ?x against leaf node
  Setup: graph with const(42); pattern = .pvar 0
  Check: ematchF returns substitution mapping ?0 → const(42)'s class

- [T4] EDGE_CASE: no match — pattern doesn't match any node
  Setup: graph with only const nodes; pattern = .node (.add ...)
  Check: ematchF returns []

- [T5] STRESS: diamond pattern — shared variable ?x appears twice
  Setup: graph with add(c1, c1) (same child); pattern = .node (.add (.pvar 0) (.pvar 0))
  Check: ematchF returns substitution where both occurrences map to same class

---

### F2S3 — Saturate

- **Tipo**: HOJA
- **Archivos fuente**: `LambdaSat/Saturate.lean`, `LambdaSat/SaturationSpec.lean`
- **Target properties**: `Tests/Properties/Saturate.lean`
- **Target integration**: `Tests/Integration/Saturate.lean`

PROPERTIES:
- [P1] P0 PRESERVATION: saturateF preserves consistency (theorem exists)
  Sketch: -- saturateF_preserves_consistent already proven
  SampleableExt: yes
  Risk: saturation introduces inconsistent merges

- [P2] P1 INVARIANT: saturateF with fuel=0 returns unchanged graph
  Sketch: example (g : EGraph ArithOp) (rules : List ...) : (saturateF 0 0 maxN g rules).numClasses = g.numClasses
  SampleableExt: yes
  Risk: zero-fuel saturation mutates state

- [P3] P1 INVARIANT: saturateF monotonically increases graph size
  Sketch: example (g : EGraph ArithOp) (rules) (fuel) : g.numNodes ≤ (saturateF fuel maxI maxN g rules).numNodes
  SampleableExt: yes
  Risk: saturation loses nodes

INTEGRATION:
- [T1] BASIC: saturate with add_comm rule, verify graph grows
  Setup: graph with add(x, y); rule = add_comm; fuel = 5
  Check: numNodes after > numNodes before

- [T2] EDGE_CASE: saturate empty graph — no crash
  Setup: empty graph, any rules, fuel = 5
  Check: returns graph (possibly empty), no crash

- [T3] EDGE_CASE: saturate with empty rule list
  Setup: graph with nodes; rules = []; fuel = 10
  Check: graph unchanged (numNodes same)

- [T4] EDGE_CASE: saturate with maxNodes = 0 — hits limit immediately
  Setup: graph with 1 node; rules = [add_comm]; fuel=10, maxIter=10, maxNodes=0
  Check: returns immediately (graph unchanged or minimal growth)

- [T5] STRESS: fixpoint detection — saturate until no new nodes added
  Setup: graph with add(x,y); rule = add_comm; high fuel
  Check: reaches fixpoint (2 iterations: original + commuted)

---

### F2S4 — SemanticSpec

- **Tipo**: CRITICO
- **Archivos fuente**: `LambdaSat/SemanticSpec.lean`
- **Target properties**: `Tests/Properties/SemanticSpec.lean`
- **Target integration**: `Tests/Integration/SemanticSpec.lean`

PROPERTIES:
- [P1] P0 SOUNDNESS: merge_consistent — merge preserves ConsistentValuation
  Sketch: -- theorem merge_consistent already proven
  SampleableExt: yes (EGraph, valuation)
  Risk: fundamental soundness broken — merge introduces semantic inequivalence

- [P2] P0 PRESERVATION: rebuildStepBody_preserves_triple — rebuild preserves (CV, PMI, SHI)
  Sketch: -- theorem already proven (closed the sorry gap in v0.3.0)
  SampleableExt: yes
  Risk: rebuild step destroys semantic consistency

- [P3] P1 SOUNDNESS: computeCostsF_preserves_consistency
  Sketch: -- theorem already proven
  SampleableExt: yes
  Risk: cost computation corrupts valuation consistency

INTEGRATION:
- [T1] BASIC: verify ConsistentValuation holds for a concrete graph+valuation
  Setup: graph with const(5), const(3), add(c5,c3); valuation v where v(cAdd) = v(c5) + v(c3)
  Check: ConsistentValuation g env v holds (via decidable check or #check)

- [T2] EDGE_CASE: empty graph — ConsistentValuation vacuously true
  Setup: empty graph, any valuation
  Check: ConsistentValuation holds (no classes to check)

---

### F3S1 — Extractable + extractF

- **Tipo**: PARALELO
- **Archivos fuente**: `LambdaSat/Extractable.lean`, `LambdaSat/ExtractSpec.lean`
- **Target properties**: `Tests/Properties/Extractable.lean`
- **Target integration**: `Tests/Integration/Extractable.lean`

PROPERTIES:
- [P1] P0 SOUNDNESS: extractF_correct — extracted expression evaluates to same value
  Sketch: -- theorem extractF_correct already proven
  SampleableExt: yes
  Risk: extraction produces semantically wrong expression

- [P2] P1 INVARIANT: extractF with fuel=0 returns none
  Sketch: example (g : EGraph ArithOp) (id : EClassId) : extractF g id 0 = none
  SampleableExt: no
  Risk: fuel=0 doesn't terminate

- [P3] P1 INVARIANT: extractAuto uses numClasses+1 as fuel
  Sketch: -- extractAuto_def already proven
  SampleableExt: no
  Risk: auto fuel insufficient

INTEGRATION:
- [T1] BASIC: extract leaf (const 42)
  Setup: graph with const(42), computeCosts, extractAuto
  Check: result = some (.const 42)

- [T2] BASIC: extract tree (add(var(0), const(3)))
  Setup: build graph, computeCosts, extractAuto
  Check: result = some (.add (.var 0) (.const 3))

- [T3] EDGE_CASE: extract from empty graph
  Setup: empty graph, extractAuto at class 0
  Check: result = none

- [T4] EDGE_CASE: extract with fuel=1 on 3-level tree
  Setup: graph with add(mul(x,y), const(1)), extractF with fuel=1
  Check: result = none (insufficient fuel for depth-3 tree)

- [T5] EDGE_CASE: extract after merge — picks bestNode
  Setup: add const(1), add const(2), merge both, computeCosts, extractAuto
  Check: result.isSome (extracts one of the two)

---

### F3S4+F3S6+F9S* — ILP Pipeline

- **Tipo**: CRITICO (aggregate)
- **Archivos fuente**: `LambdaSat/ILP.lean`, `LambdaSat/ILPEncode.lean`, `LambdaSat/ILPCheck.lean`, `LambdaSat/ILPSpec.lean`
- **Target properties**: `Tests/Properties/ILPPipeline.lean`
- **Target integration**: `Tests/Integration/ILPPipeline.lean`

PROPERTIES:
- [P1] P0 SOUNDNESS: extractILP_correct — ILP-guided extraction is sound
  Sketch: -- theorem extractILP_correct already proven
  SampleableExt: yes (ILPSolution)
  Risk: ILP extraction produces semantically wrong expression

- [P2] P0 SOUNDNESS: ilp_extraction_soundness — end-to-end ILP pipeline
  Sketch: -- theorem ilp_extraction_soundness already proven
  SampleableExt: yes
  Risk: full pipeline broken

- [P3] P0 INVARIANT: checkSolution rejects solutions that violate constraints
  Sketch: -- checkRootActive_sound, checkExactlyOne_sound, checkChildDeps_sound, checkAcyclicity_sound all proven
  SampleableExt: yes
  Risk: invalid ILP solution accepted → unsound extraction

- [P4] P0 PRESERVATION: encodeEGraph_rootClassId — encoding preserves root
  Sketch: theorem : (encodeEGraph g rootId costFn).rootClassId = root g.unionFind rootId := encodeEGraph_rootClassId g rootId costFn
  SampleableExt: no (direct theorem application)
  Risk: encoding targets wrong root class

- [P5] P0 PRESERVATION: encodeEGraph_numClasses — encoding preserves class count
  Sketch: theorem : (encodeEGraph g rootId costFn).numClasses = g.classes.size := encodeEGraph_numClasses g rootId costFn
  SampleableExt: no
  Risk: encoding has wrong class count → bad M constant in acyclicity

- [P6] P1 INVARIANT: extractILP_fuel_mono — more fuel doesn't change result
  Sketch: -- theorem extractILP_fuel_mono already proven
  SampleableExt: yes
  Risk: increasing fuel changes extraction result

- [P7] P1 INVARIANT: evalVar for nodeSelect ∈ {0, 1}
  Sketch: example (sol : ILPSolution) (cid : EClassId) (nid : Nat) : evalVar sol (.nodeSelect cid nid) = 0 ∨ evalVar sol (.nodeSelect cid nid) = 1
  SampleableExt: no (standard types only)
  Risk: evalVar produces out-of-bound values

- [P8] P1 INVARIANT: evalVar for classActive ∈ {0, 1}
  Sketch: example (sol : ILPSolution) (cid : EClassId) : evalVar sol (.classActive cid) = 0 ∨ evalVar sol (.classActive cid) = 1
  SampleableExt: no
  Risk: evalVar produces out-of-bound values

- [P9] P2 INVARIANT: solutionCost is nonneg (trivially Nat)
  Sketch: -- theorem solutionCost_nonneg already proven
  SampleableExt: no
  Risk: n/a (type guarantees)

- [P10] P2 INVARIANT: checkBounds on empty bounds is true
  Sketch: example (sol : ILPSolution) : checkBounds sol #[] = true
  SampleableExt: no
  Risk: vacuous case handled incorrectly

INTEGRATION:
- [T1] BASIC: encode graph, verify problem has constraints
  Setup: graph with const(5), const(3), add(c5,c3); encode with costFn = 1
  Check: prob.constraints.size > 0, prob.bounds.size > 0

- [T2] BASIC: valid solution passes checkSolution
  Setup: graph with add(c5,c3); hand-craft valid ILPSolution
  Check: checkSolution g rootId sol = true

- [T3] BASIC: valid solution extracts successfully
  Setup: same as T2; extractILP with fuel = numClasses + 1
  Check: result.isSome

- [T4] EDGE_CASE: extractILP with fuel=0 returns none
  Setup: valid graph + valid solution, fuel = 0
  Check: result = none

- [T5] EDGE_CASE: checkSolution rejects inactive root
  Setup: graph, solution with activatedClasses[root] = false
  Check: checkSolution = false

- [T6] EDGE_CASE: checkSolution rejects out-of-range node index
  Setup: graph, solution with selectedNodes[root] = 999
  Check: checkSolution = false

- [T7] EDGE_CASE: checkSolution rejects bad level ordering (parent < child)
  Setup: graph with parent-child, levels[parent] = 0, levels[child] = 2
  Check: checkSolution = false

- [T8] EDGE_CASE: self-loop child accepted by acyclicity
  Setup: graph where child class = parent class (after merge)
  Check: checkAcyclicity passes (if child == classId then true)

- [T9] EDGE_CASE: solutionCost with zero-cost function
  Setup: any graph, costFn = fun _ => 0
  Check: solutionCost = 0

- [T10] EDGE_CASE: empty graph rejected by checkSolution
  Setup: empty graph, empty solution, root = 0
  Check: checkSolution = false

- [T11] STRESS: fuel monotonicity — fuel=3 and fuel=100 give same result
  Setup: valid graph + valid solution
  Check: extractILP g sol root 3 = extractILP g sol root 100

- [T12] BASIC: encodeEGraph structural properties
  Setup: graph with 3 classes
  Check: prob.rootClassId = root g.unionFind rootId, prob.numClasses = g.classes.size

- [T13] EDGE_CASE: checkSolution with missing child activation
  Setup: graph with add(c5,c3); solution activates root but not c5/c3
  Check: checkSolution = false

- [T14] EDGE_CASE: isFeasible on problem with no constraints
  Setup: ILPProblem with empty constraints, solution satisfies bounds
  Check: isFeasible = true (vacuously)

---

### F3S3 — Optimize

- **Tipo**: PARALELO
- **Archivos fuente**: `LambdaSat/Optimize.lean`
- **Target properties**: `Tests/Properties/Optimize.lean`
- **Target integration**: `Tests/Integration/Optimize.lean`

PROPERTIES:
- [P1] P1 SOUNDNESS: optimizeExpr composes saturation + extraction correctly
  Sketch: -- optimizeExpr is a pipeline wrapper; its soundness follows from composing saturateF_preserves_consistent + extractF_correct
  SampleableExt: yes
  Risk: pipeline wiring error — saturation output not fed to extraction correctly

INTEGRATION:
- [T1] BASIC: optimizeExpr on simple expression
  Setup: graph with add(x, const(0)); rule = add_identity; costFn = fun _ => 1
  Check: result.isSome, extracted expression is simpler or equivalent

- [T2] EDGE_CASE: optimizeExpr with no rules
  Setup: graph with add(x, y); rules = []; fuel = 5
  Check: returns original expression (no rewrites applied)

- [T3] EDGE_CASE: optimizeExpr with fuel=0
  Setup: any graph, any rules
  Check: returns expression from un-saturated graph

---

### F4S1+F4S2 — ParallelMatch + ParallelSaturate

- **Tipo**: HOJA (IO wrappers, outside formal TCB)
- **Archivos fuente**: `LambdaSat/ParallelMatch.lean`, `LambdaSat/ParallelSaturate.lean`
- **Target properties**: (none — IO-based, no formal properties)
- **Target integration**: `Tests/Integration/Parallel.lean`

PROPERTIES:
(none — IO.asTask wrappers don't carry formal proofs; their correctness
depends on Lean's task runtime. Use sequential saturateF + ematchF for
formal guarantees.)

INTEGRATION:
- [T1] BASIC: parallel saturation produces same or larger graph than input
  Setup: graph with add(x,y); rule = add_comm; ParallelSatConfig with numTasks=2
  Check: result.graph.numNodes >= input.numNodes

- [T2] EDGE_CASE: parallel saturation with numTasks=1 (degenerates to sequential)
  Setup: same graph; numTasks = 1
  Check: result equivalent to sequential saturateF

- [T3] EDGE_CASE: parallel saturation on empty graph
  Setup: empty graph; any rules
  Check: no crash, returns graph

- [T4] STRESS: parallel saturation with parallelThreshold = 0 (always parallel)
  Setup: graph with 5 nodes; parallelThreshold = 0, numTasks = 4
  Check: completes without hanging, numNodes >= original

---

### F4S3 — TranslationValidation

- **Tipo**: HOJA
- **Archivos fuente**: `LambdaSat/TranslationValidation.lean`
- **Target properties**: `Tests/Properties/TranslationValidation.lean`
- **Target integration**: (none — pure theorem file)

PROPERTIES:
- [P1] P0 SOUNDNESS: full_pipeline_soundness type-checks
  Sketch: #check @full_pipeline_soundness
  SampleableExt: no
  Risk: top-level theorem has sorry or incorrect type

- [P2] P0 SOUNDNESS: optimization_soundness_ilp type-checks
  Sketch: #check @optimization_soundness_ilp
  SampleableExt: no
  Risk: ILP optimization theorem has sorry

- [P3] P1 SOUNDNESS: greedy_ilp_equivalent type-checks
  Sketch: #check @greedy_ilp_equivalent
  SampleableExt: no
  Risk: greedy/ILP equivalence theorem broken

INTEGRATION:
(none — TranslationValidation contains only theorems. Correctness is
verified by the Lean type-checker at compile time.)

---

### F8S1+F8S2+F8S3 — Discharge Hypotheses

- **Tipo**: FUNDACIONAL/CRITICO
- **Archivos fuente**: `LambdaSat/EMatchSpec.lean`, `LambdaSat/AddNodeTriple.lean`
- **Target properties**: `Tests/Properties/DischargeHypotheses.lean`
- **Target integration**: (none — pure theorem file)

PROPERTIES:
- [P1] P0 SOUNDNESS: InstantiateEvalSound_holds type-checks with no sorry
  Sketch: #check @InstantiateEvalSound_holds
  SampleableExt: no
  Risk: main hypothesis discharge has sorry

- [P2] P0 SOUNDNESS: sameShapeSemantics_holds type-checks
  Sketch: #check @sameShapeSemantics_holds
  SampleableExt: no
  Risk: shape semantics hypothesis not actually discharged

- [P3] P0 SOUNDNESS: ematchF_substitution_bounded type-checks
  Sketch: #check @ematchF_substitution_bounded
  SampleableExt: no
  Risk: substitution boundedness not actually proven

- [P4] P0 PRESERVATION: add_node_triple type-checks
  Sketch: #check @add_node_triple
  SampleableExt: no
  Risk: add_node doesn't preserve (CV,PMI,SHI,HCB) quadruple

INTEGRATION:
(none — pure theorems verified by Lean type-checker.)

---

### F3S5 — ILPSolver

- **Tipo**: HOJA (outside TCB)
- **Archivos fuente**: `LambdaSat/ILPSolver.lean`
- **Target properties**: (none — solver is outside TCB, certificate-checked)
- **Target integration**: `Tests/Integration/ILPSolver.lean`

PROPERTIES:
(none — ILP solver output is validated by checkSolution before use.
The solver itself is intentionally outside the TCB.)

INTEGRATION:
- [T1] BASIC: branch-and-bound on trivial 1-variable problem
  Setup: ILPProblem with 1 variable, bounds [0,1], minimize x
  Check: returns solution with x=0

- [T2] EDGE_CASE: problem with no feasible solution
  Setup: ILPProblem with contradictory constraints (x ≤ 0 AND x ≥ 1)
  Check: solver returns none or infeasible indicator

- [T3] BASIC: evalObjective computes correct value
  Setup: objective = [2*x + 3*y], solution x=1, y=2
  Check: evalObjective = 8

---

## Resumen

| Métrica | Total |
|---------|-------|
| Nodos cubiertos | 13 (agrupados de 33 DAG nodes) |
| Properties | 32 (16 P0, 12 P1, 4 P2) |
| Integration tests | 49 |
| Archivos .lean a crear | ~15 (7 property + 8 integration) |

### Estado de implementación (v1.2.0)

Los 23 tests de `Tests/IntegrationTests.lean` ya cubren:
- T1-T5: greedy extraction (basic + nested + saturation)
- T6-T7: ILP extraction + checkSolution
- T8: parallel saturation
- T9-T14: edge cases (empty graph, self-merge, zero-fuel, invalid solution, hashcons, near-zero fuel)
- T15-T23: ILP edge cases (fuel=0, inactive root, bad index, bad levels, self-loop, zero-cost, encode structural, fuel monotonicity, empty graph)

**Cobertura ya existente**: ~30 de los 49 integration tests especificados arriba están cubiertos (parcial o totalmente) por los 23 tests existentes. Los tests faltantes son principalmente:
- Properties (SlimCheck): 0/32 — requiere Mathlib dependency
- UF-specific integration: chain merge, single-element
- EMatch-specific: diamond pattern, empty graph match
- Solver-specific: B&B trivial problem, infeasible detection
- Optimize-specific: pipeline with no rules, fuel=0

### Nota sobre SlimCheck

LambdaSat es self-contained (sin Mathlib). Para implementar las 32 propiedades SlimCheck:
1. Agregar `require mathlib from ...` a lakefile.toml
2. Implementar `SampleableExt` para: `EGraph ArithOp`, `ILPSolution`, `Pattern ArithOp`, `Substitution`
3. Implementar `Shrinkable` para los mismos tipos
4. Esto es un esfuerzo significativo (~200-400 LOC de infraestructura de testing)

Alternativa: convertir las propiedades P0 en `#eval` tests concretos (como los T15-T23 existentes) que verifican instancias específicas en lugar de propiedades universales. Menor cobertura pero cero dependencias nuevas.
