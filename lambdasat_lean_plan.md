# Plan: LambdaSat-Lean v0.1.0 — Motor Genérico de Equality Saturation Verificado

## Contexto

**Posición**: LambdaSat-Lean v0.0.0 (genesis), Lean 4 v4.26.0, 0 archivos .lean
**Dominio**: Motor genérico de equality saturation formalmente verificado, parametrizado por typeclasses
**Origen**: Generalización de VR1CS-Lean v1.3.0 (~6,758 LOC en 14 archivos EGraph, ~148 teoremas, zero sorry)
**Riesgo a VR1CS-Lean**: CERO — no se toca ni un byte del proyecto existente
**Complejidad**: MAX

## Bibliografía (key references)

- **egg** (Willsey et al., POPL 2021) — Rebuilding, e-class analyses, foundational e-graph library
- **Willsey PhD Thesis** (2021) — Comprehensive treatment of e-graphs, extraction, congruence closure
- **Charguéraud & Pottier** (JAR 2019) — Verified Union-Find in Coq with amortized complexity
- **Stevens** (2025) — Verified proof-producing Union-Find in Isabelle
- **Suciu et al.** (ICDT 2025) — Semantic foundations of equality saturation via tree automata
- **Selsam et al.** (IJCAR 2016) — Congruence closure in intensional type theory (applicable to Lean)
- **lean-egg** (Rossel et al., POPL 2026) — Equality saturation tactic for Lean 4
- **TENSAT** (Yang et al., 2021) — ILP extraction from tensor e-graphs
- **Merckx et al.** (2025) — ILP extraction with value reuse for Julia IR
- **Flatt et al.** (FMCAD 2022) — Small proofs from congruence closure
- **Nieuwenhuis & Oliveras** (IC 2007) — Fast congruence closure O(n log n)

## Lecciones Aplicables (de VR1CS-Lean)

| ID | Lección | Aplicación |
|----|---------|------------|
| L-203 | Fuel parameter + depth bound separado | rootD, extractF, computeCosts |
| L-205 | IsRootAt → fixpoint predicate (hr1_fix) | Generalizar para union_preserves_equiv |
| L-207 | by_contra no existe sin Mathlib | rcases Nat.lt_or_ge para bounds |
| L-209 | beq_iff_eq bridge Bool↔Prop | Crucial para BEq de ENode Op |
| L-218 | Array.foldl_induction exact @ | Tipos explícitos obligatorios |
| L-222 | PostMergeInvariant patrón | Sub-invariante durante merge |
| L-229 | Factoring pattern (field directo) | hwf.uf_wf → hufwf |
| L-231 | List.foldl induction más limpio | Preferir sobre Array.foldl_induction |
| L-134 | DAG = orden de trabajo | Este plan |
| L-135 | Clasificación FUND > CRÍT > PAR > HOJA | Ver DAG abajo |
| L-136 | De-risk crítico con sketch | CoreSpec, SemanticSpec |
| L-138 | NUNCA diferir fundacional | UnionFind, Core primero |
| L-082 | Axiomas falsos: theorem+sorry | Auditar precondiciones |
| L-057 | termination_by + decreasing_by | Eliminar partial |
| L-048 | NO inst.op, SÍ operadores estándar | NodeOps via BEq, ring tactic |

## Expert Synthesis

**Mathlib**: No tiene UnionFind ni congruence closure. Usar `Array.data_set`, `Array.get_set_eq/ne` de Std; `CommRing` de Mathlib si se necesita.

**Typeclass design**:
- `NodeOps` → `NodeSemantics` → `Extractable` via `extends`
- BEq/Hashable para `ENode Op`: instancias MANUALES, NO `deriving` (Lean 4.26 no auto-derive para tipos parametrizados con constraints)
- EGraph genérico SOLO en `Op`; UnionFind/HashMap se quedan con `Nat`-indexed
- `ConsistentValuation` como proposición separada, parametrizada por `Val`
- Mantener `Type 0` (no universe polymorphism); HashMap requiere keys en `Type 0`
- Fuel-based extraction con `Option` return; no `termination_by` sobre e-graph DAG genérico

## DAG de Dependencias

```
F1S1 (Setup)
  │
  ▼
F1S2 (UnionFind) ─────────────── [FOUNDATIONAL, direct copy]
  │
  ▼
F1S3 (Typeclasses + Core) ────── [FOUNDATIONAL, ~350 LOC]
  │
  ├─────────────────────────┐
  ▼                         ▼
F2S1 (CoreSpec)           F2S2 (EMatch)
  [CRITICAL, ~1,400]       [INTERMEDIATE, ~220]
  │                         │
  │                         ▼
  │                       F2S3 (Saturate)
  │                         [LEAF, ~80]
  │                         │
  ▼                         │
F2S4 (SemanticSpec)  ◄──────┘ (uses Core, not Saturate directly)
  [CRITICAL, ~2,100]
  │
  ├───────────────────┬─────────────────────┐
  ▼                   ▼                     ▼
F3S1 (Optimize)     F3S2 (ILP+Encode)    F4S3 (TransVal)
  [INTERMEDIATE]      [INTERMEDIATE]        [LEAF, ~150]
  │                   │
  │                   ▼
  │                 F3S3 (ILPSolver)
  │                   [LEAF, ~320]
  │                   │
  ├───────────────────┘
  ▼
F3S4 (ILPCheck+Spec) ────────── [CRITICAL, ~350]
  │
  ├───────────────────┐
  ▼                   ▼
F4S1 (ParMatch)     F4S2 (ParSaturate)
  [LEAF, ~210]        [LEAF, ~130]
  │                   │
  └───────────────────┘
               │
               ▼
         F4S4 (Integration + Tests)
               [LEAF, ~300]
```

**Parallel blocks identificados**:
- F1S1 → F1S2 → F1S3 (secuencial, fundacional)
- F2S1 ‖ F2S2 (paralelo, independientes tras F1S3)
- F2S3 (tras F2S2)
- F2S4 (tras F2S1, GATE de-risk obligatorio)
- F3S1 ‖ F3S2 (paralelo, independientes tras F2S4)
- F3S3 (tras F3S2)
- F3S4 (tras F3S3 + F2S4, GATE de-risk)
- F4S1 ‖ F4S2 ‖ F4S3 (paralelo, tras F3S4)
- F4S4 (tras todo)

---

## Plan de Trabajo (Orden Topológico)

---

### Fase 1: Foundation [FUNDACIONAL, secuencial obligatorio]

#### Fase 1 Subfase 1: Project Setup

**Archivos**: `lakefile.toml`, `lean-toolchain`, `LambdaSat.lean` (root)
**Entregables**:
- `lakefile.toml` con `name = "lambdasat-lean"`, Lean 4.26.0
- `lean-toolchain`: `leanprover/lean4:v4.26.0`
- `LambdaSat.lean`: módulo raíz (imports)
- `lake build` compila limpio

**LOC**: ~30
**Teoremas**: 0
**Dependencias**: ninguna

---

#### Fase 1 Subfase 2: UnionFind [FUNDACIONAL]

**Archivo**: `LambdaSat/UnionFind.lean`
**Fuente**: Copia directa de `VR1CS/EGraph/UnionFind.lean`
**Cambios**: Solo namespace (`VR1CS.EGraph` → `LambdaSat`)

**Entregables**:
- Todas las definiciones: `UnionFind`, `rootD`, `root`, `find`, `compressPath`, `merge`/`union`
- Todos los predicados: `IsRootAt`, `ParentsBounded`, `IsAcyclic`, `WellFormed`
- **44 teoremas** verificados (zero sorry)
- `lake build` pasa

**LOC**: 1,235
**Teoremas**: 44
**Dependencias**: F1S1
**Benchmark**: `lake build` < 30s, zero sorry

---

#### Fase 1 Subfase 3: Typeclasses + E-Graph Core [FUNDACIONAL]

**Archivo**: `LambdaSat/Core.lean`
**Fuente**: Generalización de `VR1CS/EGraph/Core.lean` (252 LOC)

**Entregables**:

1. **Typeclasses** (definiciones centrales):
```lean
class NodeOps (Op : Type) where
  children : Op → List EClassId
  mapChildren : Op → (EClassId → EClassId) → Op

class CostModel (Op : Type) where
  localCost : Op → Nat
```

2. **Tipos genéricos**:
```lean
structure ENode (Op : Type) where
  op : Op

-- BEq/Hashable manuales (L-048, expert advice)
instance [BEq Op] : BEq (ENode Op) where ...
instance [Hashable Op] : Hashable (ENode Op) where ...
```

3. **EGraph genérico** (parametrizado por `Op`):
```lean
structure EGraph (Op : Type) [BEq Op] [Hashable Op] where
  unionFind : UnionFind
  hashcons  : Std.HashMap (ENode Op) EClassId
  classes   : Std.HashMap EClassId (EClass Op)
  worklist  : List EClassId
  dirtyArr  : Array EClassId
```

4. **Operaciones**: `empty`, `find`, `canonicalize`, `add`, `merge`, `processClass`, `rebuild`, `computeCosts`, `getClass`, `stats`

**Cambios respecto a VR1CS**:
- `CircuitNodeOp` → `Op` con `[NodeOps Op] [BEq Op] [Hashable Op]`
- `ENode.children` → delegado a `NodeOps.children node.op`
- `ENode.mapChildren f` → `⟨NodeOps.mapChildren node.op f⟩`
- `ENode.localCost` → `CostModel.localCost node.op`
- Funciones idénticas en estructura lógica

**LOC**: ~350
**Teoremas**: 0
**Dependencias**: F1S2
**Benchmark**: `lake build` < 30s

**GATE de-risk**: Verificar que `Std.HashMap` acepta `ENode Op` con instancias BEq/Hashable manuales antes de proceder.

---

### Fase 2: Specification [CRITICAL path]

#### Fase 2 Subfase 1: CoreSpec [CRITICAL]

**Archivo**: `LambdaSat/CoreSpec.lean`
**Fuente**: Generalización de `VR1CS/EGraph/CoreSpec.lean` (1,368 LOC, 64 thms)

**Entregables**:
- `ENode.isCanonical` genérico
- `HashconsConsistent`, `HashconsComplete`, `ClassesConsistent`, `HashconsClassesAligned`, `ChildrenBounded`
- `EGraphWF (Op : Type)` structure
- `PostMergeInvariant (Op : Type)` structure (L-222)
- `AddExprInv (Op : Type)` structure (L-234)
- Bridge lemmas: `egraph_find_*`, `hashcons_get?_insert_*`
- Teoremas: `add_preserves_wf`, `merge_preserves_pmi`, `rebuild_restores_wf`, etc.
- **~64 teoremas** (zero sorry)

**Cambios respecto a VR1CS**:
- `ENode` → `ENode Op`
- `EGraph` → `EGraph Op`
- `node.children` → `NodeOps.children node.op`
- Todas las pruebas usan tácticas domain-agnostic (`simp`, `omega`, `exact`, `rfl`)
- NO hay dependencia de `ZMod p` ni `CircuitNodeOp`

**LOC**: ~1,400
**Teoremas**: ~64
**Dependencias**: F1S3
**Benchmark**: `lake build` < 60s, zero sorry

**GATE de-risk**: Sketch `add_preserves_wf` con tipos genéricos ANTES de escribir todos los lemmas.

**Estrategia de prueba** (L-229, L-222):
- Factoring: `hwf : EGraphWF eg` → extraer `hwf.uf_wf` donde solo se necesita UF
- PostMergeInvariant: misma estructura, solo cambiar tipos
- Usar firewall `_aux` para teoremas difíciles (L-136)

---

#### Fase 2 Subfase 2: EMatch [INTERMEDIATE, paralelo con F2S1]

**Archivo**: `LambdaSat/EMatch.lean`
**Fuente**: Generalización de `VR1CS/EGraph/EMatch.lean` (201 LOC)

**Entregables**:
- `Pattern Op` genérico (reemplaza `CircuitPattern`)
- `Match` structure
- `ematchNode`, `ematchPattern`
- `searchPattern` (fold sobre classes)

**Cambios**: `CircuitPattern` → `Pattern Op`, `CircuitNodeOp` → `Op`

**LOC**: ~220
**Teoremas**: 0
**Dependencias**: F1S3
**Benchmark**: `lake env lean LambdaSat/EMatch.lean` limpio

---

#### Fase 2 Subfase 3: Saturate [LEAF]

**Archivo**: `LambdaSat/Saturate.lean`
**Fuente**: Generalización de `VR1CS/EGraph/Saturate.lean` (70 LOC)

**Entregables**:
- `RewriteRule Op` genérico
- `SoundRewriteRule Op Val` (con proof de soundness)
- `applyRule`, `applyRules`
- `saturate` (loop con fuel)
- `SaturationConfig`, `SaturationResult`

**LOC**: ~80
**Teoremas**: 0
**Dependencias**: F2S2
**Benchmark**: `lake env lean LambdaSat/Saturate.lean` limpio

---

#### Fase 2 Subfase 4: SemanticSpec [CRITICAL]

**Archivo**: `LambdaSat/SemanticSpec.lean`
**Fuente**: Generalización de `VR1CS/EGraph/SemanticSpec.lean` (2,061 LOC, 36 thms)

**Entregables**:
- `NodeSemantics Op Val` typeclass:
```lean
class NodeSemantics (Op : Type) (Val : Type) extends NodeOps Op where
  evalOp : Op → (Nat → Val) → (EClassId → Val) → Val
```
- `NodeEval` genérico (delegado a `NodeSemantics.evalOp`)
- `ConsistentValuation` genérico:
```lean
def ConsistentValuation [NodeSemantics Op Val] (g : EGraph Op) (env : Nat → Val) (v : EClassId → Val) : Prop :=
  (∀ i j, root g.unionFind i = root g.unionFind j → v i = v j) ∧
  (∀ classId eclass, g.classes.get? classId = some eclass →
    ∀ node, node ∈ eclass.nodes.toList →
      NodeSemantics.evalOp node.op env v = v classId)
```
- Teoremas: `empty_consistent`, `add_preserves_consistent`, `merge_preserves_consistent`
- `sound_rule_preserves_consistency`
- `computeCostsF_preserves_consistency`
- `extractF_correct`
- **~36 teoremas** (zero sorry)

**Cambios respecto a VR1CS**:
- `ZMod p` → `Val` con `[NodeSemantics Op Val]`
- `NodeEval` por pattern match → `NodeSemantics.evalOp` (typeclass method)
- Proofs que usan `ring` tactic → necesitan `[CommRing Val]` o similar
- Los simp lemmas (`nodeEval_addGate`, etc.) se eliminan (el typeclass method se unfolds directamente)

**LOC**: ~2,100
**Teoremas**: ~36
**Dependencias**: F2S1 (CoreSpec)
**Benchmark**: `lake build` < 90s, zero sorry

**GATE de-risk OBLIGATORIO**: Sketch `merge_preserves_consistent` con tipos genéricos. Este es el teorema más difícil del proyecto. Verificar que las pruebas que usan `ring` transfieren con `[CommRing Val]`.

**Obstáculo anticipado**: Los simp lemmas de NodeEval en VR1CS usan `rfl` porque `NodeEval` se define por pattern match. En la versión genérica, `NodeSemantics.evalOp` es un method opaco — las pruebas no pueden unfold. **Mitigación**: Definir `@[simp]` lemmas en la instancia concreta, no en el genérico. Las pruebas genéricas deben usar la hipótesis `ConsistentValuation` directamente sin necesitar simp sobre `evalOp`.

---

### Fase 3: Extraction + Optimization

#### Fase 3 Subfase 1: Optimize [INTERMEDIATE]

**Archivo**: `LambdaSat/Optimize.lean`
**Fuente**: Generalización de `VR1CS/EGraph/Optimize.lean` (181 LOC)

**Entregables**:
- `Extractable Op Expr Val` typeclass:
```lean
class Extractable (Op : Type) (Expr : Type) (Val : Type)
    [NodeSemantics Op Val] where
  reconstruct : Op → List Expr → Option Expr
  evalExpr : Expr → (Nat → Val) → Val
  reconstruct_sound : ...
```
- `extractF` (fuel-based extraction, genérico)
- `optimizeExpr` (saturate → computeCosts → extract)

**LOC**: ~200
**Teoremas**: 0 (soundness está en SemanticSpec/ILPSpec)
**Dependencias**: F2S3 (Saturate), F2S4 (SemanticSpec)
**Benchmark**: `lake env lean LambdaSat/Optimize.lean` limpio

---

#### Fase 3 Subfase 2: ILP + ILPEncode [INTERMEDIATE, paralelo con F3S1]

**Archivos**: `LambdaSat/ILP.lean`, `LambdaSat/ILPEncode.lean`
**Fuente**: Generalización de VR1CS ILP.lean (186) + ILPEncode.lean (233)

**Entregables**:
- `ILPVar`, `ILPConstraint`, `ILPProblem`, `ILPSolution` (tipos genéricos)
- `encodeEGraph : EGraph Op → EClassId → CostModel Op → ILPProblem`
- `ILPSolution.isFeasible` (decidable checker)

**Cambios**: `ENode` → `ENode Op`, `CostModel` genérico

**LOC**: ~420
**Teoremas**: 0
**Dependencias**: F1S3
**Benchmark**: `lake env lean LambdaSat/ILPEncode.lean` limpio

---

#### Fase 3 Subfase 3: ILPSolver [LEAF]

**Archivo**: `LambdaSat/ILPSolver.lean`
**Fuente**: Generalización de VR1CS ILPSolver.lean (314 LOC)

**Entregables**:
- `ILPProblem.toMPS` (serialización MPS)
- `parseSolution` (parse HiGHS output)
- `solveExternal` (IO.Process)
- `solveBranchAndBound` (pure Lean B&B fallback)
- `solveILP` (unified interface)

**LOC**: ~320
**Teoremas**: 0 (TCB — solver output verificado en ILPCheck)
**Dependencias**: F3S2
**Benchmark**: B&B < 1s para <50 classes

---

#### Fase 3 Subfase 4: ILPCheck + ILPSpec [CRITICAL]

**Archivos**: `LambdaSat/ILPCheck.lean`, `LambdaSat/ILPSpec.lean`
**Fuente**: Generalización de VR1CS ILPCheck (149) + ILPSpec (174)

**Entregables**:
- `checkSolution : EGraph Op → EClassId → ILPSolution → Bool`
- `extractILP : EGraph Op → EClassId → ILPSolution → Option Expr`
- **Theorem `extractILP_correct`**: certificate-checked extraction is sound
- **Theorem `ilp_extraction_soundness`**: end-to-end pipeline soundness
- ~4 major + ~15 supporting lemmas

**LOC**: ~350
**Teoremas**: ~19
**Dependencias**: F2S4 (SemanticSpec), F3S3 (ILPSolver)
**Benchmark**: `lake build` < 60s, zero sorry

**GATE de-risk**: Sketch `extractILP_correct` proof structure before writing supporting lemmas.

---

### Fase 4: Parallelism + Integration

#### Fase 4 Subfase 1: ParallelMatch [LEAF, paralelo con F4S2/F4S3]

**Archivo**: `LambdaSat/ParallelMatch.lean`
**Fuente**: Generalización de VR1CS ParallelMatch.lean (209 LOC)

**Entregables**:
- `matchRuleChunk`, `searchPatternParallel`, `matchAllRulesParallel`
- Read-only e-graph during matching (use `root` not `find`)

**LOC**: ~210
**Teoremas**: 0
**Dependencias**: F2S2 (EMatch)

---

#### Fase 4 Subfase 2: ParallelSaturate [LEAF]

**Archivo**: `LambdaSat/ParallelSaturate.lean`
**Fuente**: Generalización de VR1CS ParallelSaturate.lean (125 LOC)

**Entregables**:
- `ParallelSatConfig`, `parallelSaturateStep`, `parallelSaturate`
- Threshold-based fallback to sequential

**LOC**: ~130
**Teoremas**: 0
**Dependencias**: F2S3 (Saturate), F4S1 (ParallelMatch)

---

#### Fase 4 Subfase 3: TranslationValidation [LEAF, paralelo con F4S1/F4S2]

**Archivo**: `LambdaSat/TranslationValidation.lean`
**Fuente**: Nuevo (basado en Path B de VR1CS)

**Entregables**:
- `ProofWitness Op Val` structure
- `validateOptimization` (proof witness checker)
- Bridge theorems for external tool integration

**LOC**: ~150
**Teoremas**: ~4
**Dependencias**: F2S4 (SemanticSpec)

---

#### Fase 4 Subfase 4: Integration + Tests [LEAF]

**Archivos**: `LambdaSat.lean` (update), `Tests/Basic.lean`

**Entregables**:
- Root module exports all public API
- Smoke tests: empty e-graph, add/merge, saturate, extract
- `#eval` tests con instancia ejemplo (simple arithmetic ops)
- Documentation: update `CLAUDE.md`, `README.md`

**LOC**: ~300
**Teoremas**: 0
**Dependencias**: todas las subfases anteriores
**Benchmark**: `lake build` < 120s, zero sorry, zero axioms

---

## Tabla Resumen

| Subfase | Tipo | Archivo(s) | LOC | Thms | Depende de |
|---------|------|-----------|:---:|:----:|:----------:|
| F1S1 Setup | FUND | lakefile, toolchain | 30 | 0 | — |
| F1S2 UnionFind | FUND | UnionFind.lean | 1,235 | 44 | F1S1 |
| F1S3 Core | FUND | Core.lean | 350 | 0 | F1S2 |
| F2S1 CoreSpec | CRÍT | CoreSpec.lean | 1,400 | 64 | F1S3 |
| F2S2 EMatch | INTER | EMatch.lean | 220 | 0 | F1S3 |
| F2S3 Saturate | HOJA | Saturate.lean | 80 | 0 | F2S2 |
| F2S4 SemanticSpec | CRÍT | SemanticSpec.lean | 2,100 | 36 | F2S1 |
| F3S1 Optimize | INTER | Optimize.lean | 200 | 0 | F2S3, F2S4 |
| F3S2 ILP+Encode | INTER | ILP.lean, ILPEncode.lean | 420 | 0 | F1S3 |
| F3S3 ILPSolver | HOJA | ILPSolver.lean | 320 | 0 | F3S2 |
| F3S4 ILPCheck+Spec | CRÍT | ILPCheck.lean, ILPSpec.lean | 350 | 19 | F2S4, F3S3 |
| F4S1 ParMatch | HOJA | ParallelMatch.lean | 210 | 0 | F2S2 |
| F4S2 ParSaturate | HOJA | ParallelSaturate.lean | 130 | 0 | F2S3, F4S1 |
| F4S3 TransVal | HOJA | TranslationValidation.lean | 150 | 4 | F2S4 |
| F4S4 Integration | HOJA | Tests + docs | 300 | 0 | ALL |
| **TOTAL** | | **15 archivos** | **~7,495** | **~167** | |

## Orden Topológico de Ejecución

```
Bloque 1 (secuencial, FUNDACIONAL):
  F1S1 → F1S2 → F1S3

Bloque 2 (paralelo):
  F2S1 (CoreSpec) ‖ F2S2 (EMatch)
  → F2S3 (Saturate, tras F2S2)

GATE: De-risk F2S4 (sketch merge_preserves_consistent)

Bloque 3 (secuencial, CRÍTICO):
  F2S4 (SemanticSpec)

Bloque 4 (paralelo):
  F3S1 (Optimize) ‖ F3S2 (ILP+Encode)
  → F3S3 (ILPSolver, tras F3S2)

GATE: De-risk F3S4 (sketch extractILP_correct)

Bloque 5 (secuencial, CRÍTICO):
  F3S4 (ILPCheck+Spec)

Bloque 6 (paralelo):
  F4S1 (ParMatch) ‖ F4S2 (ParSaturate) ‖ F4S3 (TransVal)

Bloque 7:
  F4S4 (Integration + Tests)
```

## Benchmarks de Aceptación

| Métrica | Target | Stretch |
|---------|--------|---------|
| LOC total | ≥ 6,000 | ≥ 7,000 |
| Teoremas | ≥ 148 | ≥ 167 |
| Sorry count | **0** | 0 |
| Axiomas personalizados | **0** | 0 |
| `lake build` time | < 120s | < 90s |
| Compilación sin warnings | 100% | 100% |

## Riesgos y Mitigaciones

| Riesgo | Nivel | Mitigación |
|--------|-------|------------|
| F2S4: pruebas que usan `ring` no transfieren sin `CommRing Val` | ALTO | GATE de-risk; verificar transferencia antes de invertir en lemmas |
| F2S1: CoreSpec proofs con tipos genéricos más verbose | MEDIO | Factoring pattern (L-229), firewall _aux |
| BEq/Hashable para ENode Op en HashMap | MEDIO | GATE de-risk F1S3; instancias manuales |
| `ConsistentValuation` genérico puede necesitar axiomas extra | MEDIO | Sketch temprano; usar `nodeEval_generic` simp lemmas |
| Lean 4.26 instance resolution con cadena extends | BAJO | Mantener Type 0, cadena lineal simple |
| `partial` en rebuild/computeCosts | BAJO | Fuel-based como en VR1CS probado |

## Próximos Pasos

1. Ejecutar F1S1 (Setup: lakefile.toml, lean-toolchain)
2. Ejecutar F1S2 (UnionFind: copia directa, renombrar namespace)
3. Ejecutar F1S3 (Core: definir typeclasses + EGraph genérico)
4. GATE de-risk: sketch de `add_preserves_wf` genérico
