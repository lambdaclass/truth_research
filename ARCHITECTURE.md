# OptiSat: Architecture

## Current Version: v1.5.2

### Fase 1: Foundation

**Contents**: Project setup, UnionFind (direct copy from VR1CS-Lean, zero coupling), and typeclass-parameterized E-Graph Core with generic `NodeOps`, `CostModel`, `ENode Op`, `EGraph Op`.

**Files**:
- `lakefile.toml`
- `LambdaSat.lean`
- `LambdaSat/UnionFind.lean`
- `LambdaSat/Core.lean`

#### DAG (v0.1.0)

| Nodo | Tipo | Deps | Status |
|------|------|------|--------|
| F1S1 Setup | FUND | — | completed ✓ |
| F1S2 UnionFind | FUND | F1S1 | completed ✓ |
| F1S3 Core | FUND | F1S2 | completed ✓ |

#### Bloques

- [x] **Bloque 1**: 

---

### Fase 2: Specification

**Contents**: CoreSpec (EGraphWF, PostMergeInvariant, AddExprInv, ~64 theorems), EMatch (generic Pattern Op), Saturate (RewriteRule Op, SoundRewriteRule Op Val, fuel-based loop), and SemanticSpec (NodeSemantics Op Val, ConsistentValuation, extractF_correct, ~36 theorems). GATE de-risk on merge_preserves_consistent.

**Files**:
- `LambdaSat/CoreSpec.lean`
- `LambdaSat/EMatch.lean`
- `LambdaSat/Saturate.lean`
- `LambdaSat/SemanticSpec.lean`

#### DAG (v0.1.0)

| Nodo | Tipo | Deps | Status |
|------|------|------|--------|
| F2S1 CoreSpec | CRIT | F1S3 | completed ✓ |
| F2S2 EMatch | PAR | F1S3 | completed ✓ |
| F2S3 Saturate | HOJA | F2S2 | completed ✓ |
| F2S4 SemanticSpec | CRIT | F2S1 | completed ✓ |

#### Bloques

- [x] **Bloque 2**: 

---

### Fase 3: Extraction + Optimization

**Contents**: Extractable typeclass + extractF (fuel-based generic extraction), ExtractSpec (extractF_correct, extractAuto_correct, computeCostsF_extractF_correct), Optimize pipeline (saturate → computeCosts → extract), ILP types/encoding/solver, and ILP certificate checking with verified extraction (extractILP_correct, ilp_extraction_soundness).

**Files**:
- `LambdaSat/Extractable.lean`
- `LambdaSat/ExtractSpec.lean`
- `LambdaSat/Optimize.lean`
- `LambdaSat/ILP.lean`
- `LambdaSat/ILPEncode.lean`
- `LambdaSat/ILPSolver.lean`
- `LambdaSat/ILPCheck.lean`
- `LambdaSat/ILPSpec.lean`

#### DAG (v0.1.0)

| Nodo | Tipo | Deps | Status |
|------|------|------|--------|
| F3S1 Extractable+extractF | PAR | F2S3, F2S4 | completed ✓ |
| F3S2 ExtractSpec | PAR | F3S1 | completed ✓ |
| F3S3 Optimize | PAR | F3S1 | completed ✓ |
| F3S4 ILP+Encode | PAR | F1S3 | completed ✓ |
| F3S5 ILPSolver | HOJA | F3S4 | completed ✓ |
| F3S6 ILPCheck+Spec | CRIT | F2S4, F3S5 | completed ✓ |

#### Bloques

- [x] **Bloque 4**: 

---

### Fase 4: Parallelism + Integration

**Contents**: Parallel matching (IO.asTask, read-only e-graph), parallel saturation (threshold-based fallback), translation validation (ProofWitness Op Val, 5 soundness theorems), and integration tests (8/8 PASS with ArithOp concrete instance).

**Files**:
- `LambdaSat/ParallelMatch.lean`
- `LambdaSat/ParallelSaturate.lean`
- `LambdaSat/TranslationValidation.lean`
- `Tests/IntegrationTests.lean`

#### DAG (v0.1.0)

| Nodo | Tipo | Deps | Status |
|------|------|------|--------|
| F4S1 ParMatch | HOJA | F2S2 | completed ✓ |
| F4S2 ParSaturate | HOJA | F2S3, F4S1 | completed ✓ |
| F4S3 TransVal | HOJA | F2S4 | completed ✓ |
| F4S4 Integration | HOJA | ALL | completed ✓ |

#### Bloques

- [x] **Bloque 6**: 

---

### Fase 5: Saturation Soundness (v0.2.0)

**Contents**: SoundRewriteRule structure (unconditional + conditional), sound_rule_preserves_consistency, fuel-based saturation spec (instantiateF, ematchF, applyRuleAtF, saturateF), PreservesCV composability predicate, full pipeline soundness with saturation. 1 isolated sorry in `rebuildStepBody_preserves_cv`.

**Files**:
- `LambdaSat/SoundRule.lean`
- `LambdaSat/SaturationSpec.lean`

#### DAG (v0.2.0)

| Nodo | Tipo | Deps | Status |
|------|------|------|--------|
| F5S1 SoundRewriteRule | FUND | F2S4 | completed ✓ |
| F5S2 SoundRulePreservesCV | FUND | F5S1 | completed ✓ |
| F5S3 InstantiateF | CRIT | F5S1 | completed ✓ |
| F5S4 EmatchF+ApplyRule | CRIT | F5S2, F5S3 | completed ✓ |
| F5S5 SaturateF | CRIT | F5S4 | completed ✓ |
| F5S6 ChainClose | HOJA | F5S5 | completed ✓ |

#### Bloques

- [x] **Bloque 8**: F5S1 + F5S2
- [x] **Bloque 9**: F5S3
- [x] **Bloque 10**: F5S4 + F5S5
- [x] **Bloque 11**: F5S6

**Sorry**: 1 isolated (`rebuildStepBody_preserves_cv`) — processClass/mergeAll require WellFormed, not available during rebuild intermediate states. Confined to rebuild path; all other chain links fully proven.

---

### Fase 6: Close Rebuild Sorry (v0.3.0)

**Contents**: SemanticHashconsInv (semantic hashcons invariant replacing HashconsClassesAligned), processClass preserves SHI, processAll threaded invariant, close `rebuildStepBody_preserves_cv` sorry.

**Key innovation**: `SemanticHashconsInv g env v` = `∀ nd id, hashcons[nd] = some id → NodeEval nd env v = v(root id)`. Preservable through processClass foldl (unlike HCA). The triple (CV, PMI, SHI) is self-preserving through rebuildStepBody.

**Files**:
- `LambdaSat/SemanticSpec.lean` (modified: +SHI + ~5 theorems)
- `LambdaSat/SaturationSpec.lean` (modified: close sorry, update signatures)

#### DAG (v0.3.0)

| Nodo | Tipo | Deps | Status |
|------|------|------|--------|
| F6S1 SemanticHashconsInv | FUND | — | ✓ |
| F6S2 processClass_preserves_shi | CRIT/GATE | F6S1 | ✓ |
| F6S3 processAll_threaded | CRIT | F6S2 | ✓ |
| F6S4 rebuildStepBody closure | CRIT | F6S3 | ✓ |
| F6S5 chain_update | HOJA | F6S4 | ✓ |

#### Bloques

- [x] **Bloque 12**: F6S1
- [x] **Bloque 13**: F6S2 (GATE de-risk)
- [x] **Bloque 14**: F6S3 + F6S4
- [x] **Bloque 15**: F6S5

---

### Fase 7: ematchF Soundness (v1.0.0)

**Contents**: Pattern.eval denotational semantics, ematchF_sound theorem (if ematchF returns σ, Pattern.eval under σ = v(classId)), applyRuleF_preserves_cv_internal without PreservesCV assumption, strongest pipeline soundness. OptiSat becomes first formally verified complete equality saturation motor.

**Key innovation**: `Pattern.eval pat env v subst` gives semantic value of pattern under substitution. `ematchF_sound` proves the motor finds only valid matches. Eliminates user burden of providing `PreservesCV` proofs.

**Files**:
- `LambdaSat/EMatchSpec.lean` (NEW)
- `LambdaSat/SaturationSpec.lean` (modified)
- `LambdaSat/TranslationValidation.lean` (modified)

#### DAG (v1.0.0)

| Nodo | Tipo | Deps | Status |
|------|------|------|--------|
| F7S1 Pattern.eval | FUND | — | ✓ |
| F7S2 Pattern.eval props | FUND | F7S1 | ✓ |
| F7S3 ematchF_sound | CRIT/GATE | F7S2 | ✓ |
| F7S4 applyRuleF_internal | CRIT | F7S3 | ✓ |
| F7S5 saturateF_internal | CRIT | F7S4 | ✓ |
| F7S6 pipeline_update | HOJA | F7S5 | ✓ |

#### Bloques

- [x] **Bloque 16**: F7S1 + F7S2 ✓
- [x] **Bloque 17**: F7S3 (GATE de-risk) ✓
- [x] **Bloque 18**: F7S4 ✓ (L-388..L-392)
- [x] **Bloque 19**: F7S5 + F7S6 ✓

---

### Fase 8: Discharge Hypotheses + Polish (v1.1.0)

**Contents**: Probar las 3 hipótesis no descargadas del Path B como teoremas internos: SameShapeSemantics (evaluación de ops con misma forma), ematchF_substitution_bounded (sustituciones acotadas), InstantiateEvalSound (instantiateF preserva triple CV+PMI+SHI + valor correcto). Eliminar hipótesis de `full_pipeline_soundness_internal`. Cubrir recomendaciones P1-P5 de autopsia.

**Key insight**: `instantiateF` solo hace `add` (no merge directo), lo que simplifica InstantiateEvalSound. `ematchF` es read-only (no muta g), lo que hace hematch_bnd estructural. SameShapeSemantics se deriva de `evalOp_mapChildren` + `LawfulBEq` o se agrega como lemma condicional.

**Lecciones aplicables**: L-391 (decomposition), L-378/L-383 (SubstExtends IH), L-375/L-382 (dual motives Pattern.rec), L-234 (sub-invariante), L-392 (value agreement monotonicity), L-390 (foldl suffices).

**Files**:
- `LambdaSat/EMatchSpec.lean` (modified: +3 teoremas principales + auxiliares)
- `LambdaSat/SaturationSpec.lean` (modified: strengthen instantiateF proofs if needed)
- `LambdaSat/TranslationValidation.lean` (modified: remove 3 hypotheses from pipeline)
- `LambdaSat/SemanticSpec.lean` (modified: add evalOp_sameShape lemma if needed)
- `README.md` (modified: fix metrics, document TCB boundary)
- `Tests/IntegrationTests.lean` (modified: add edge-case tests)

#### DAG (v1.1.0)

| Nodo | Tipo | Deps | Status |
|------|------|------|--------|
| F8S1 SameShapeSemantics_holds | FUND | — | completed ✓ |
| F8S2 ematchF_substitution_bounded | FUND | — | completed ✓ |
| F8S3 InstantiateEvalSound_holds | CRIT/GATE | F8S1 | completed ✓ |
| F8S4 Update pipeline signatures | HOJA | F8S1, F8S2, F8S3 | completed ✓ |
| F8S5 P1-P5 docs and tests | HOJA | F8S4 | completed ✓ |

#### Bloques

- [x] **Bloque 20**: F8S1 + F8S2 (paralelo, ~120-180 LOC)
- [x] **Bloque 21**: F8S3 (GATE de-risk con sketch _aux, ~150-250 LOC)
- [x] **Bloque 22**: F8S4 + F8S5 (paralelo, ~130-200 LOC)

#### Decisiones de diseño

**SameShapeSemantics**: La definición de `sameShape` nullifica children via `mapChildren (fun _ => 0)` y compara con `BEq`. Con `LawfulBEq Op` (o `LawfulBEq (ENode Op)`), esto da igualdad proposicional del skeleton. Luego `evalOp_mapChildren` permite demostrar que la evaluación coincide. Si LawfulBEq no está disponible, agregar como lemma condicional con precondición `sameShape_implies_skeleton_eq`. De-risk en B20 determinará el approach.

**InstantiateEvalSound**: Generalizar `instantiateF_preserves_consistency` (SaturationSpec:233, ya prueba CV+PMI) agregando SHI preservation + valor correcto. El caso `patVar` es trivial (g no cambia). El caso `node` usa foldl + `add_node_consistent` + SameShapeSemantics bridge. Patrón reutilizable de `processClass_shi_combined` (SemanticSpec:1168).

**hematch_bnd**: Inducción sobre Pattern + fuel. `ematchF` es read-only. Cada σ.get? retorna IDs del grafo existente (< g.uf.size). Reutiliza `matchChildren_sound` (ya probado).

**P2 (SlimCheck)**: Deferred a v1.2.0 — requiere Mathlib dependency, OptiSat es self-contained. Documentado en README.

---

### Fase 9: ILP Certificate Verification (v1.2.0)

**Contents**: Formal verification of the ILP extraction pipeline. Proves what `ValidSolution` means by decomposing `checkSolution` into individual Prop properties (root activation, exactly-one selection, child dependencies, acyclicity). Certificate evaluation soundness (evalVar, checkConstraint, isFeasible). Encoding correctness for `encodeEGraph`. Fuel sufficiency for `extractILPAuto`.

**Key insight** (L-250): `ValidSolution` is a user-facing bridge, not an internal correctness requirement. `extractILP_correct` already works with `ValidSolution` as hypothesis; the bridge allows users to discharge it computationally via `checkSolution`.

**Strategy**: Decompose `checkSolution = check1 && check2 && check3 && check4` via `Bool.and_eq_true_iff`. Each `checkN = true → PropN` proven separately. F9S3 (checkExactlyOne) pioneers the HashMap.fold approach; F9S4/F9S5 replicate the pattern.

**QA feedback incorporated**:
- F9S3 is GATE: establishes reusable HashMap.fold decomposition approach
- F9S5: constructive proof via level decrease contradiction (no Classical.em)
- F9S9: spec-first approach — define `EncodingSpec` Prop before proving

**Files**:
- `LambdaSat/ILP.lean` (modified: +simp lemmas)
- `LambdaSat/ILPSpec.lean` (modified: +checkSolution decomposition, fuel, cost)
- `LambdaSat/ILPEncode.lean` (modified: +cert eval, +encoding correctness)

#### DAG (v1.2.0)

| Nodo | Tipo | Deps | Status |
|------|------|------|--------|
| F9S1 ILP simp lemmas | HOJA | — | ✓ |
| F9S2 checkRootActive_sound | HOJA | F9S1 | ✓ |
| F9S3 checkExactlyOne_sound | CRIT/GATE | F9S1 | ✓ |
| F9S4 checkChildDeps_sound | PAR | F9S1, F9S3 | ✓ |
| F9S5 checkAcyclicity_sound | PAR | F9S1, F9S3 | ✓ |
| F9S6 checkSolution_sound | HOJA | F9S2-F9S5 | ✓ |
| F9S7 evalVar+checkConstraint | PAR | — | ✓ |
| F9S8 isFeasible_sound | PAR | F9S7 | ✓ |
| F9S9 encodeEGraph_correctness | FUND | F9S1 | ✓ |
| F9S10 extractILPAuto_fuel | HOJA | F9S5, F9S9 | ✓ |
| F9S11 solutionCost_correct | HOJA | F9S1 | ✓ |

#### Bloques

- [x] **Bloque 23**: F9S1 + F9S2 (parallel HOJAS: simp foundation + rootActive) ✓
- [x] **Bloque 24**: F9S3 (GATE: checkExactlyOne — pioneers HashMap.fold approach) ✓
- [x] **Bloque 25**: F9S4 + F9S5 + F9S7 + F9S8 (parallel PARs: checkChildDeps + acyclicity + cert eval) ✓
- [x] **Bloque 26**: F9S6 + F9S11 (parallel HOJAS: composition + cost) ✓
- [x] **Bloque 27**: F9S9 (FUND: encodeEGraph correctness) ✓
- [x] **Bloque 28**: F9S10 (HOJA: fuel sufficiency) ✓

#### Decisiones de diseño

**HashMap.fold approach**: `checkExactlyOne`, `checkChildDeps`, `checkAcyclicity` all use `g.classes.fold`. Instead of fighting `HashMap.fold` directly (L-200, L-302: intractable), prove properties from the RESULT structure: if `fold (init := true) (fun acc k v => acc && f k v) = true`, then `∀ (k, v) ∈ map, f k v = true`. Pioneer this approach in F9S3 (GATE), then replicate in F9S4/F9S5.

**Spec-first for F9S9**: Define `EncodingSpec g constraints : Prop` specifying what a correct encoding means (root constraint exists, exactly-one constraints per reachable class, child dependency constraints, acyclicity constraints). Then prove `encodeEGraph g` satisfies this spec. De-risk with `_aux` sketch — may defer to v1.2.1 if compound invariant proves intractable.

**Certificate evaluation (F9S7-F9S8)**: Independent of checkSolution decomposition. `evalVar`, `checkConstraint`, `checkBounds` are simpler (no HashMap.fold). Use `Array.all` → `∀` bridge for `isFeasible_sound`.

**Scope**: Soundness only (checkSolution = true → properties hold). No completeness (¬ValidSolution → checkSolution = false). ILP solver remains outside TCB.

---

### Fase 10: Unified Extraction Verification (v1.3.0)

**Contents**: Integration of VerifiedExtraction's unified extraction interface into OptiSat. Enriches `NodeOps` typeclass with `localCost` and `mapChildren_id`, creates unified `ExtractionStrategy` dispatch (greedy/ILP), and proves the master `extract_correct` theorem composing `extractF_correct` + `ilp_extraction_soundness`.

**Key insight**: OptiSat already had 100% of the underlying theorems (`extractF_correct`, `ilp_extraction_soundness`). The integration required only typeclass enrichment + a thin composition layer (78 LOC). Adapted from VerifiedExtraction/Integration.lean without adding it as a dependency.

**Files**:
- `LambdaSat/Core.lean` (modified: +localCost, +mapChildren_id to NodeOps + ENode)
- `LambdaSat/Extraction.lean` (new: ExtractionStrategy, extract, StrategyValid, extract_correct)
- `LambdaSat.lean` (modified: +import Extraction)
- `Tests/IntegrationTests.lean` (modified: +localCost/mapChildren_id instance, +2 smoke tests)

#### DAG (v1.3.0)

| Nodo | Tipo | Deps | Status |
|------|------|------|--------|
| F10S1 NodeOps enrichment | FUND | — | ✓ |
| F10S2 Extraction.lean | CRIT | F10S1 | ✓ |
| F10S3 Wire + verify | HOJA | F10S2 | ✓ |

#### Bloques

- [x] **Bloque 29**: F10S1 (FUND: add localCost + mapChildren_id to NodeOps, update ArithOp instance) ✓
- [x] **Bloque 30**: F10S2 (CRIT: create Extraction.lean with extract_correct — zero axioms, zero warnings) ✓
- [x] **Bloque 31**: F10S3 (HOJA: wire imports + 2 smoke tests, 25/25 integration tests pass) ✓

---

### Fase 11: DP Extraction Optimality (v1.4.0)

**Contents**: Verified DP-based optimal extraction via nice tree decompositions. Copies/adapts infrastructure from DynamicTreeProg (NiceTree, NatOpt, FoldMin, InsertMin utilities) and VerifiedExtraction (TreewidthDP types + DPTableLemmas proofs). Bottom-up DP via `treeFold_inv` on NiceTree, producing `dp_optimal_of_validNTD: dpOptimalCost ≤ selectionCost`.

**Key insight**: VerifiedExtraction already adapted DynamicTreeProg into its `Util/` directory. Copy from VE/Util directly (identical content, correct namespacing). The e-graph-specific code (~1100 LOC) from VE/TreewidthDP + VE/DPTableLemmas is the core work. The capstone theorem `dp_optimal_of_validNTD` composes `runDP_DPCompleteInv` → `dpOptimalityWitness_from_completeInv` → `dp_extraction_optimal` with zero axioms.

**Reference**: Goharshady et al. 2024 "Fast and Optimal Extraction for Sparse Equality Graphs" §4. Lessons L-371 (copy, don't import), L-467 (DP tight bound), L-405 (HashMap.fold).

**Files** (new):
- `LambdaSat/Util/NatOpt.lean` (46 LOC, 11T) — Nat.min properties
- `LambdaSat/Util/FoldMin.lean` (81 LOC, 6T) — List.foldl Nat.min
- `LambdaSat/Util/InsertMin.lean` (88 LOC, 4T+1D) — HashMap insertWith min
- `LambdaSat/Util/NiceTree.lean` (107 LOC, 6T+5D) — NiceTree catamorphism + invariant preservation
- `LambdaSat/TreewidthDP.lean` (372 LOC, 9T+20D) — DP types, operations, DPCompleteInv, optimality structures
- `LambdaSat/DPTableLemmas.lean` (728 LOC, 45T+1D) — Canonicalization + all 4 operation proofs + ValidNTD + runDP_DPCompleteInv + dp_optimal_of_validNTD

**Files** (modified):
- `LambdaSat.lean` — add 6 new module imports
- `Tests/IntegrationTests.lean` — 4 DP smoke tests (T26-T29)

#### DAG (v1.4.0)

| Nodo | Tipo | Deps | Status |
|------|------|------|--------|
| F11S1 NatOpt utilities | PAR | — | ✓ |
| F11S2 FoldMin utilities | PAR | F11S1 | ✓ |
| F11S3 InsertMin utilities | PAR | F11S1 | ✓ |
| F11S4 NiceTree catamorphism | PAR | — | ✓ |
| F11S5 TreewidthDP types + DP ops | FUND | F11S1-S4 | ✓ |
| F11S6 DPTableLemmas (canon + insertMin + fold + 4 ops + ValidNTD + master) | CRIT | F11S5 | ✓ |
| F11S7-S9 Operation DPCompleteInv proofs | PAR | F11S6 | ✓ (in F11S6) |
| F11S10 runDP_DPCompleteInv | GATE | F11S7-S9 | ✓ (in F11S6) |
| F11S11 dp_optimal_of_validNTD | HOJA | F11S10 | ✓ (in F11S6) |
| F11S12 Integration + smoke tests | HOJA | F11S11 | ✓ |

#### Bloques

- [x] **Bloque 32**: F11S1 + F11S4 (NatOpt 46 LOC + NiceTree 107 LOC — both compile) ✓
- [x] **Bloque 33**: F11S2 + F11S3 (FoldMin 81 LOC + InsertMin 88 LOC — both compile) ✓
- [x] **Bloque 34**: F11S5 (TreewidthDP 372 LOC — all types, operations, optimality structures compile) ✓
- [x] **Bloque 35-37**: F11S6-S10 (DPTableLemmas 728 LOC — canonicalization + 4 operation proofs + ValidNTD + runDP_DPCompleteInv compile as single file) ✓
- [x] **Bloque 38**: F11S11-S12 (dp_optimal_of_validNTD added to DPTableLemmas + 6 imports + 4 smoke tests, 29/29 PASS) ✓

#### Decisiones de diseño

**Consolidation**: Planned nodes F11S7-S11 (4 operation proofs + ValidNTD + runDP_DPCompleteInv + dp_optimal_of_validNTD) were implemented in a single `DPTableLemmas.lean` file, matching VE's structure. This collapsed Bloques 35-37 into one file write.

**Namespace**: All new code under `LambdaSat` namespace. Utilities under `LambdaSat.Util.{NatOpt,FoldMin,InsertMin,NiceTree}`. DP-specific under `LambdaSat.TreewidthDP` and `LambdaSat.DPTableLemmas`.

**Copy source**: Copied from VerifiedExtraction/Util/ (already adapted from DynamicTreeProg). For e-graph-specific code, copied from VerifiedExtraction/TreewidthDP.lean and DPTableLemmas.lean. Only namespace changes (`VerifiedExtraction` → `LambdaSat`) needed.

---

### Fase 12: API-Specification Bridge (v1.5.0)

**Contents**: Verified pipeline functions that compose existing spec theorems (`saturateF_preserves_consistent`, `computeCostsF_extractF_correct`, `extract_correct`) into user-facing correctness guarantees. Creates the "last mile" connection between the verified internals and the public API.

**Key insight**: The public API functions (`optimizeExpr`, `saturate`) are `partial def` and cannot be reasoned about in Lean 4. Instead of refactoring them (which would break production features like timeouts), we create new verified pipeline functions (`optimizeF`, `optimizeWithStrategyF`) that compose the already-verified `*F` functions. This follows the established codebase pattern: `ematch`→`ematchF`, `rebuild`→`rebuildF`, `saturate`→`saturateF`, now `optimizeExpr`→`optimizeF`.

**Reference**: Three-Tier Bridge pattern (Extraction.lean v1.3.0), L-337 (compositional correctness), L-393 (wiring theorems ≤5 lines), L-352 (spec-impl connection).

**Files** (new):
- `LambdaSat/PipelineSoundness.lean` — optimizeF, optimizeWithStrategyF, soundness theorems

**Files** (modified):
- `LambdaSat/Optimize.lean` — TCB boundary documentation
- `LambdaSat.lean` — +import PipelineSoundness
- `Tests/IntegrationTests.lean` — pipeline soundness smoke tests
- `README.md` — v1.5.0 update

#### DAG (v1.5.0)

| Nodo | Tipo | Deps | Status |
|------|------|------|--------|
| F12S1 optimizeF + optimizeWithStrategyF defs | FUND | — | ✓ |
| F12S2 optimizeF_soundness + optimizeWithStrategyF_soundness | CRIT | F12S1 | ✓ |
| F12S3 Integration + TCB docs + README | HOJA | F12S2 | ✓ |

#### Bloques

- [x] **Bloque 39**: F12S1 (FUND: define optimizeF + optimizeWithStrategyF in PipelineSoundness.lean) ✓
- [x] **Bloque 40**: F12S2 (CRIT: prove optimizeF_soundness + optimizeWithStrategyF_soundness — wiring theorems, 0 axioms, 0 warnings) ✓
- [x] **Bloque 41**: F12S3 (HOJA: wire imports + 2 smoke tests T30-T31, TCB docs in Optimize.lean, README v1.5.0, 31/31 PASS) ✓

---

### Fase 13: Completeness (v1.5.1)

**Contents**: Formal completeness for the extraction pipeline. Proves bestNode DAG acyclicity after cost computation, fuel sufficiency for `extractAuto`, and discharges remaining hypotheses (`WellFormed`, `BestNodeInv`) from pipeline soundness theorems. Closes the gap between soundness ("IF some THEN correct") and completeness ("IF answer exists THEN extractAuto finds it").

**Gaps addressed**:
- G1: bestNode DAG acyclicity not proven (CRITICAL)
- G2: Fuel sufficiency for extractAuto not proven (HIGH)
- G3: WellFormed/BestNodeInv hypotheses in pipeline theorems not auto-discharged (HIGH)

**Reference**: L-203 (fuel depth bound via pigeonhole), L-222 (sub-invariant factoring), L-292 (fuel monotonicity), L-338 (fuel composition via max).

**Files** (new):
- `LambdaSat/CompletenessSpec.lean` — AcyclicBestNodeDAG, fuel sufficiency, extractAuto_complete

**Files** (modified):
- `LambdaSat/PipelineSoundness.lean` — saturateF_preserves_quadruple_internal, optimizeF_soundness_complete
- `LambdaSat.lean` — +import CompletenessSpec
- `Tests/IntegrationTests.lean` — completeness smoke tests T32-T33
- `README.md` — v1.5.1 update

#### DAG (v1.5.1)

| Nodo | Tipo | Deps | Status |
|------|------|------|--------|
| N13.1 AcyclicBestNodeDAG definition + proof | FUND | — | ✓ |
| N13.2 Fuel sufficiency + extractAuto completeness | CRIT | N13.1 | ✓ |
| N13.3 Hypothesis discharge (WF + BNI chain) | PAR | — | ✓ |
| N13.4 Integration tests + documentation | HOJA | N13.1, N13.2, N13.3 | ✓ |

#### Bloques

- [x] **Bloque 42**: N13.1 (FUND: AcyclicBestNodeDAG in CompletenessSpec.lean — bestCostLowerBound_acyclic, 0 sorry, 0 axioms. HashMap API gap closed via Std.HashMap.nodup_keys in Lean 4.26)
- [x] **Bloque 43**: N13.3 (PAR: saturateF_preserves_quadruple_internal, optimizeF_soundness_complete in PipelineSoundness.lean, 0 sorry, 0 axioms)
- [x] **Bloque 44**: N13.2 (CRIT: extractF_of_rank, extractAuto_complete — strong induction on rank, 0 sorry, 0 axioms)
- [x] **Bloque 45**: N13.4 (HOJA: tests T32-T33, README/ARCHITECTURE/BENCHMARKS v1.5.1, Path G)

---

## Version History

| Version | Date | Highlights |
|---------|------|------------|
| **v0.1.0** | Feb 2026 | Full typeclass-parameterized e-graph engine: 4 phases, 15 nodes, 17 src files, 6,241 LOC, 181 theorems, zero sorry, zero axioms. Generalized from VR1CS-Lean v1.3.0. |
| **v0.2.0** | Feb 2026 | Saturation soundness: SoundRewriteRule, SaturationSpec (instantiateF, ematchF, saturateF), PreservesCV, full_pipeline_soundness_greedy. 19 src files, 6,538 LOC, 188 theorems, 1 sorry (isolated in rebuild), zero axioms. |
| **v0.3.0** | Feb 2026 | Zero sorry: SemanticHashconsInv closes rebuildStepBody gap. 19 src files, 6,895 LOC, 198 theorems, 0 sorry, zero axioms. |
| **v1.0.0** | Feb 2026 | PreservesCV eliminated: Pattern.eval + ematchF_sound + full_pipeline_soundness_internal. 20 src files, 7,748 LOC, 218 theorems, 0 sorry, zero axioms, zero user assumptions. |
| **v1.1.0** | Feb 2026 | Zero external hypotheses: InstantiateEvalSound_holds + ematchF_substitution_bounded + processClass_preserves_hcb + full_pipeline_soundness. 21 src files, 8,622 LOC, 233 theorems, 0 sorry, zero axioms, zero external hypotheses. 13 integration tests (5 new edge-case tests). |
| **v1.2.0** | Feb 2026 | ILP certificate verification: checkSolution soundness (4 check*_sound), encoding properties (encodeEGraph_rootClassId/numClasses), extractILP fuel monotonicity. 21 src files, 8,956 LOC, 248 theorems, 0 sorry, zero axioms. 23 integration tests (9 new ILP edge-case tests). |
| **v1.3.0** | Mar 2026 | Unified extraction verification: ExtractionStrategy dispatch, extract_correct master theorem (greedy + ILP). NodeOps enriched with localCost + mapChildren_id. Adapted from VerifiedExtraction. 22 src files, 9,034 LOC, 249 theorems, 0 sorry, zero axioms. 25 integration tests. |
| **v1.4.0** | Mar 2026 | DP extraction optimality: Treewidth DP on nice tree decompositions. dp_optimal_of_validNTD (dpOptimalCost ≤ selectionCost). 6 new files, 1422 new LOC, 81 new theorems. Adapted from VerifiedExtraction + DynamicTreeProg. 28 src files, ~10,456 LOC, ~330 theorems, 0 sorry, zero axioms. 29 integration tests. |
| **v1.5.0** | Mar 2026 | API-specification bridge: User-facing verified pipeline functions (optimizeF, optimizeWithStrategyF) with formal soundness proofs. Closes "last mile" gap between verified internals and public API. 1 new file, 163 new LOC, 2 new theorems (0 axioms), 2 new defs. 29 src files, 10,643 LOC, 351 theorems, 0 sorry, zero axioms. 31 integration tests. |
| **v1.5.1** | Mar 2026 | Extraction completeness: bestNode DAG acyclicity (bestCostLowerBound_acyclic), fuel sufficiency (extractF_of_rank), extractAuto_complete, hypothesis discharge (saturateF_preserves_quadruple_internal). HashMap API gap closed via `Std.HashMap.keys`/`toList` simp lemmas + `Std.HashMap.nodup_keys` (Lean 4.26). 1 new file, ~670 new LOC, 7 new theorems, **0 sorry**, 0 axioms. 30 src files, 11,310 LOC, 358 theorems. 33 integration tests. |
| **v1.5.2** | Mar 2026 | Project rename LambdaSat → OptiSat in all documentation. Source module paths unchanged. 363 theorems, 0 sorry, zero axioms. 33 integration tests. |

---

## Soundness Chain (v1.1.0)

```
Path A (v0.3.0 — with PreservesCV assumption):
  find_preserves_roots (UnionFind)
    → merge_consistent (CoreSpec + SemanticSpec)
      → rebuildStepBody_preserves_triple (SemanticSpec)
        → saturateF_preserves_consistent (SaturationSpec)
          → full_pipeline_soundness_greedy (TranslationValidation)

Path B (v1.0.0 — no user assumptions):
  ematchF_sound (EMatchSpec)
    → applyRuleAtF_sound (EMatchSpec)
      → saturateF_preserves_consistent_internal (EMatchSpec)
        → computeCostsF_preserves_consistency (SemanticSpec)
          → extractF_correct / extractILP_correct (ExtractSpec / ILPSpec)
            → full_pipeline_soundness_internal (TranslationValidation)

Path C (v1.1.0 — zero external hypotheses):
  sameShapeSemantics_holds (EMatchSpec)
  + InstantiateEvalSound_holds (EMatchSpec)
  + ematchF_substitution_bounded (EMatchSpec)
  + processClass_preserves_hcb (CoreSpec)
    → full_pipeline_soundness (TranslationValidation)

Path D (v1.3.0 — unified extraction):
  extractF_correct (ExtractSpec)
  + ilp_extraction_soundness (ILPSpec)
    → extract_correct (Extraction) — strategy-parameterized dispatch

Path E (v1.4.0 — DP optimality):
  dpLeaf/Forget/Introduce/Join_DPCompleteInv (DPTableLemmas)
    → runDP_DPCompleteInv (DPTableLemmas) — ValidNTD induction
      → dpOptimalityWitness_from_completeInv (TreewidthDP)
        → dp_optimal_of_validNTD (DPTableLemmas) — dpOptimalCost ≤ selectionCost

Path F (v1.5.0 — user-facing pipeline soundness):
  full_pipeline_soundness (TranslationValidation)
    → optimizeF_soundness (PipelineSoundness) — greedy pipeline
  saturateF_preserves_consistent_internal + extract_correct
    → optimizeWithStrategyF_soundness (PipelineSoundness) — strategy-parameterized

Path G (v1.5.1 — extraction completeness):
  BestCostLowerBound + positive costFn
    → bestCostLowerBound_acyclic (CompletenessSpec) — AcyclicBestNodeDAG
      → extractF_of_rank (CompletenessSpec) — fuel sufficiency via rank
        → extractAuto_complete (CompletenessSpec) — extraction always succeeds
```

**Sorry**: 0 across all versions (v0.3.0–v1.5.2). The HashMap API gap in `computeCostsLoop_selfLB` (v1.5.1) was closed via `Std.HashMap.keys`/`toList` simp lemmas + `Std.HashMap.nodup_keys` available in Lean 4.26. **PreservesCV**: eliminated in v1.0.0. **External hypotheses**: eliminated in v1.1.0.

---

## Trusted Computing Base (TCB)

**Verified** (inside TCB — correctness follows from Lean kernel type-checking):
- UnionFind: find, merge, path compression (44 theorems)
- Core: add, merge, rebuild, canonicalize (79 theorems)
- SemanticSpec: ConsistentValuation, SemanticHashconsInv, rebuild preservation (49 theorems)
- EMatchSpec: ematchF_sound, InstantiateEvalSound_holds, ematchF_substitution_bounded (25 theorems)
- SaturationSpec: saturateF_preserves_consistent_internal (13 theorems)
- ExtractSpec: extractF_correct (3 theorems)
- ILPSpec: ilp_extraction_soundness (3 theorems)
- Extraction: extract_correct — unified greedy/ILP dispatch (1 theorem)
- TreewidthDP: DPCompleteInv, DPOptimalityWitness, optimality bridge (3 theorems)
- DPTableLemmas: ValidNTD, runDP_DPCompleteInv, dp_optimal_of_validNTD (45 theorems)
- Util: NatOpt (11T), NiceTree (6T+5D), FoldMin (6T), InsertMin (4T+1D) — DP infrastructure
- TranslationValidation: full_pipeline_soundness (8 theorems)
- PipelineSoundness: optimizeF_soundness, optimizeWithStrategyF_soundness (2 theorems) ← v1.5.0
- CompletenessSpec: bestCostLowerBound_acyclic, extractF_of_rank, extractAuto_complete (7 theorems, 0 sorry, 0 axioms) ← v1.5.1

**Assumed correct** (outside TCB):
- Lean 4 kernel (v4.26.0) — type-checks all proofs
- Lean 4 compiler — generates runtime code from verified definitions
- OS / hardware — executes compiled code
- Typeclass instances — users must correctly implement NodeOps, NodeSemantics, Extractable for their domain
- ILP solver (HiGHS / branch-and-bound) — untrusted oracle, output validated by `checkSolution`

**Unverified wrappers** (correct by construction but no formal proof):
- ParallelMatch.lean — IO.asTask wrapper around verified sequential ematchF
- ParallelSaturate.lean — IO.asTask wrapper around verified sequential saturateF
- Optimize.lean — `optimizeExpr`/`optimizeExprILP`/`optimizeExprAuto` use `partial def saturate` (timeouts, node limits, stats). For verified optimization, use `optimizeF`/`optimizeWithStrategyF` from PipelineSoundness.lean

---

## Previous Versions

(none)

---
