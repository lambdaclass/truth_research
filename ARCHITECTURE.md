# LambdaSat-Lean: Architecture

## Current Version: v0.2.0

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

### Fase 6: Close Rebuild Sorry (v0.3.0) — PLANNED

**Contents**: SemanticHashconsInv (semantic hashcons invariant replacing HashconsClassesAligned), processClass preserves SHI, processAll threaded invariant, close `rebuildStepBody_preserves_cv` sorry.

**Key innovation**: `SemanticHashconsInv g env v` = `∀ nd id, hashcons[nd] = some id → NodeEval nd env v = v(root id)`. Preservable through processClass foldl (unlike HCA). The triple (CV, PMI, SHI) is self-preserving through rebuildStepBody.

**Files**:
- `LambdaSat/SemanticSpec.lean` (modified: +SHI + ~5 theorems)
- `LambdaSat/SaturationSpec.lean` (modified: close sorry, update signatures)

#### DAG (v0.3.0)

| Nodo | Tipo | Deps | Status |
|------|------|------|--------|
| F6S1 SemanticHashconsInv | FUND | — | pending |
| F6S2 processClass_preserves_shi | CRIT/GATE | F6S1 | pending |
| F6S3 processAll_threaded | CRIT | F6S2 | pending |
| F6S4 rebuildStepBody closure | CRIT | F6S3 | pending |
| F6S5 chain_update | HOJA | F6S4 | pending |

#### Bloques

- [ ] **Bloque 12**: F6S1
- [ ] **Bloque 13**: F6S2 (GATE de-risk)
- [ ] **Bloque 14**: F6S3 + F6S4
- [ ] **Bloque 15**: F6S5

---

### Fase 7: ematchF Soundness (v1.0.0) — PLANNED

**Contents**: Pattern.eval denotational semantics, ematchF_sound theorem (if ematchF returns σ, Pattern.eval under σ = v(classId)), applyRuleF_preserves_cv_internal without PreservesCV assumption, strongest pipeline soundness. LambdaSat becomes first formally verified complete equality saturation motor.

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

### Fase 8: Discharge Hypotheses + Polish (v1.1.0) — PLANNED

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

**P2 (SlimCheck)**: Deferred a v1.2.0 — requiere Mathlib dependency, LambdaSat es self-contained. Documentado en README.

---

## Version History

| Version | Date | Highlights |
|---------|------|------------|
| **v0.1.0** | Feb 2026 | Full typeclass-parameterized e-graph engine: 4 phases, 15 nodes, 17 src files, 6,241 LOC, 181 theorems, zero sorry, zero axioms. Generalized from VR1CS-Lean v1.3.0. |
| **v0.2.0** | Feb 2026 | Saturation soundness: SoundRewriteRule, SaturationSpec (instantiateF, ematchF, saturateF), PreservesCV, full_pipeline_soundness_greedy. 19 src files, 6,538 LOC, 188 theorems, 1 sorry (isolated in rebuild), zero axioms. |
| **v0.3.0** | Feb 2026 | Zero sorry: SemanticHashconsInv closes rebuildStepBody gap. 19 src files, 6,895 LOC, 198 theorems, 0 sorry, zero axioms. |
| **v1.0.0** | Feb 2026 | PreservesCV eliminated: Pattern.eval + ematchF_sound + full_pipeline_soundness_internal. 20 src files, 7,748 LOC, 218 theorems, 0 sorry, zero axioms, zero user assumptions. |
| **v1.1.0** | Feb 2026 | Zero external hypotheses: InstantiateEvalSound_holds + ematchF_substitution_bounded + processClass_preserves_hcb + full_pipeline_soundness. 21 src files, 8,622 LOC, 233 theorems, 0 sorry, zero axioms, zero external hypotheses. 13 integration tests (5 new edge-case tests). |

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
```

**Sorry**: 0 since v0.3.0. **PreservesCV**: eliminated in v1.0.0. **External hypotheses**: eliminated in v1.1.0.

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
- TranslationValidation: full_pipeline_soundness (8 theorems)

**Assumed correct** (outside TCB):
- Lean 4 kernel (v4.26.0) — type-checks all proofs
- Lean 4 compiler — generates runtime code from verified definitions
- OS / hardware — executes compiled code
- Typeclass instances — users must correctly implement NodeOps, NodeSemantics, Extractable for their domain
- ILP solver (HiGHS / branch-and-bound) — untrusted oracle, output validated by `checkSolution`

**Unverified wrappers** (correct by construction but no formal proof):
- ParallelMatch.lean — IO.asTask wrapper around verified sequential ematchF
- ParallelSaturate.lean — IO.asTask wrapper around verified sequential saturateF

---

## Previous Versions

(none)

---
