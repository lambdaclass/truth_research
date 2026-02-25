# LambdaSat-Lean Benchmarks (v0.2.0)

## Criteria (v0.1.0)

| Métrica | Target | Stretch |
|---------|--------|---------|
| LOC total | ≥ 6,000 | ≥ 7,000 |
| Teoremas | ≥ 148 | ≥ 167 |
| Sorry count | **0** | 0 |
| Axiomas personalizados | **0** | 0 |
| `lake build` time | < 120s | < 90s |
| Compilación sin warnings | 100% | 100% |
| Tests de integración | 8 | 8 PASS |

---

## Current Results

### Fase 1: Foundation

**Status**: PASS

| Métrica | Target | Actual | Status |
|---------|--------|--------|--------|
| LOC | ~1,615 | 1,497+ | PASS |
| Teoremas | 44 | 44 | PASS |
| Sorry | 0 | 0 | PASS |
| `lake build` | < 30s | PASS | PASS |

### Fase 2: Specification

**Status**: PASS

| Métrica | Target | Actual | Status |
|---------|--------|--------|--------|
| LOC | ~3,800 | 2,820 | PASS |
| Teoremas | ~100 | 119 | PASS |
| Sorry | 0 | 0 | PASS |
| `lake build` | < 90s | PASS | PASS |

### Fase 3: Extraction + Optimization

**Status**: PASS

| Métrica | Target | Actual | Status |
|---------|--------|--------|--------|
| LOC nuevos | ~1,290 | 1,273 | PASS |
| Teoremas nuevos | ~19 | 13 | PASS (see note) |
| Sorry | 0 | 0 | PASS |
| `lake build` | < 60s | PASS | PASS |

**Teoremas críticos**: `extractF_correct`, `extractAuto_correct`, `computeCostsF_extractF_correct`, `extractILP_correct`, `ilp_extraction_soundness`.

### Fase 4: Parallelism + Integration

**Status**: PASS

| Métrica | Target | Actual | Status |
|---------|--------|--------|--------|
| LOC nuevos | ~790 | 711 | PASS |
| Teoremas nuevos | ~4 | 5 | PASS |
| Sorry | 0 | 0 | PASS |
| Tests | 8 | 8/8 PASS | PASS |

**Teoremas**: `congruence_merge`, `congruence_extract`, `optimization_soundness_greedy`, `optimization_soundness_ilp`, `greedy_ilp_equivalent`.


### Fase 5: Saturation Soundness (v0.2.0)

**Status**: PASS

| Métrica | Target | Actual | Status |
|---------|--------|--------|--------|
| LOC nuevos | ~300 | 297 | PASS |
| Teoremas nuevos | ~7 | 7 | PASS |
| Sorry | 0 new | 0 new (1 inherited) | PASS |
| `lake build` | < 30s | PASS | PASS |

**Teoremas**: `sound_rule_preserves_consistency`, `instantiateF_preserves_consistency`, `applyRulesF_preserves_cv`, `rebuildF_preserves_cv`, `saturateF_preserves_consistent`, `full_pipeline_soundness_greedy`.

### Aggregate (v0.2.0)

| Métrica | Target | Actual | Status |
|---------|--------|--------|--------|
| LOC total | ≥ 6,000 | 6,538 | **PASS** |
| Teoremas total | ≥ 148 | 188 | **PASS** (+27%) |
| Sorry | 0 | 1 (isolated in rebuild) | **PARTIAL** |
| Axiomas | 0 | 0 | **PASS** |
| Módulos | 17+ | 19 src + 1 test | **PASS** |
| Tests | 8 | 8/8 PASS | **PASS** |

---

## Criteria: Fase 6 — Close Rebuild Sorry (v0.3.0)

### Mechanical Checks (all nodes)

<!-- CHECK:MECH -->
| ID | Check | Method | Pass Criteria |
|----|-------|--------|---------------|
| `MECH-1` | Zero sorry | `grep -rn sorry LambdaSat/` | 0 matches (excluding comments) |
| `MECH-2` | Zero custom axioms | `#print axioms` per new theorem | Only `propext`, `Quot.sound`, `Classical.choice` |
| `MECH-3` | Clean build | `lake build` | Exit 0 |
| `MECH-4` | Zero warnings | `lake build 2>&1 \| grep -i warning` | Empty |
| `MECH-5` | No `native_decide` on proof-relevant | Manual inspection | Only in `Decidable`/`Bool` contexts |
| `MECH-6` | No `simp [*]` in final proofs | Manual inspection | All `simp` uses explicit lists or `simp only` |
| `MECH-7` | Doc comments on public defs/theorems | Manual inspection | All new `def`, `theorem`, `structure` with `/-- -/` |
| `MECH-8` | `lean_verify` clean | MCP tool per new theorem | Only standard axioms |

### F6S1 — SemanticHashconsInv [FUND]

<!-- CHECK:F6S1 -->
| ID | Criteria | Weight |
|----|----------|--------|
| `F6S1-DEF-1` | SHI: `∀ nd id, hashcons[nd] = some id → NodeEval nd env v = v(root id)` | REQUIRED |
| `F6S1-DEF-2` | SHI is a `Prop` predicate | REQUIRED |
| `F6S1-DEF-3` | `ewf_cv_implies_shi`: `EGraphWF g → CV g env v → SHI g env v` | REQUIRED |
| `F6S1-EDGE-1` | SHI with empty hashcons (vacuous truth) | REQUIRED |
| `F6S1-QUAL-1` | Strictly weaker than `HashconsConsistent ∧ HCA` | CHECK |
| `F6S1-ARCH-1` | No changes to existing public API signatures | REQUIRED |

### F6S2 — processClass_preserves_shi [CRIT/GATE]

<!-- CHECK:F6S2 -->
| ID | Criteria | Weight |
|----|----------|--------|
| `F6S2-THM-1` | `processClass_preserves_shi`: SHI preserved through processClass | REQUIRED |
| `F6S2-THM-2` | `processClass_merges_valid_via_shi`: merge pairs satisfy `v(root a) = v(root b)` using SHI | REQUIRED |
| `F6S2-THM-3` | Zero sorry in proof body | REQUIRED |
| `F6S2-EDGE-1` | processClass on non-existent classId = no-op | CHECK |
| `F6S2-EDGE-2` | processClass on class with 1 node (canonical, no merges) | CHECK |
| `F6S2-STRESS-1` | Handles erase old + insert canonical hashcons update correctly | CHECK |
| `F6S2-ROBUST-1` | Composes with existing `processClass_consistent`, not duplicate | REQUIRED |
| `F6S2-QUAL-1` | Gate de-risk: sketch proof before F6S3 dependents | REQUIRED |

### F6S3 — processAll_threaded [CRIT]

<!-- CHECK:F6S3 -->
| ID | Criteria | Weight |
|----|----------|--------|
| `F6S3-THM-1` | Triple (CV, PMI, SHI) preserved through foldl processClass | REQUIRED |
| `F6S3-THM-2` | Accumulated merges bounded (IDs < uf.size) | REQUIRED |
| `F6S3-THM-3` | Accumulated merges semantically valid (`v(root a) = v(root b)`) | REQUIRED |
| `F6S3-THM-4` | Zero sorry | REQUIRED |
| `F6S3-EDGE-1` | Empty worklist = identity | CHECK |
| `F6S3-ROBUST-1` | Uses `foldl_induction` or `induction classes` pattern | CHECK |
| `F6S3-ROBUST-2` | Valuation threading: each step produces v_i passed to next | REQUIRED |

### F6S4 — rebuildStepBody closure [CRIT]

<!-- CHECK:F6S4 -->
| ID | Criteria | Weight |
|----|----------|--------|
| `F6S4-THM-1` | Sorry at SaturationSpec.lean:399 CLOSED | REQUIRED |
| `F6S4-THM-2` | Proof uses SHI (references SemanticHashconsInv) | REQUIRED |
| `F6S4-THM-3` | No NEW sorry anywhere in project | REQUIRED |
| `F6S4-THM-4` | No axiom leakage | REQUIRED |
| `F6S4-THM-5` | Two-phase proof: processAll → mergeAll | REQUIRED |
| `F6S4-THM-6` | Statement signature UNCHANGED | REQUIRED |
| `F6S4-ROBUST-1` | `rebuildF_preserves_cv` still compiles unchanged | REQUIRED |
| `F6S4-ROBUST-2` | `saturateF_preserves_consistent` still compiles | REQUIRED |
| `F6S4-ROBUST-3` | `full_pipeline_soundness_greedy` still compiles | REQUIRED |
| `F6S4-QUAL-1` | Proof < 80 lines | CHECK |

### F6S5 — chain_update [HOJA]

<!-- CHECK:F6S5 -->
| ID | Criteria | Weight |
|----|----------|--------|
| `F6S5-BUILD-1` | Full `lake build` clean | REQUIRED |
| `F6S5-BUILD-2` | Integration tests 8/8 PASS | REQUIRED |
| `F6S5-SORRY-1` | Global sorry = 0 | REQUIRED |
| `F6S5-SORRY-2` | Global axiom audit clean | REQUIRED |
| `F6S5-DOC-1` | ARCHITECTURE.md Fase 6 marked completed | REQUIRED |
| `F6S5-DOC-2` | README.md: v0.3.0, 0 sorry | REQUIRED |
| `F6S5-DOC-3` | BENCHMARKS.md: Fase 6 results recorded | REQUIRED |
| `F6S5-TAG-1` | Git tag `v0.3.0` | REQUIRED |

### Aggregate Targets (v0.3.0)

| Métrica | Target | Stretch |
|---------|--------|---------|
| LOC total | ≥ 6,800 | ≥ 7,000 |
| Teoremas total | ≥ 195 | ≥ 200 |
| Sorry count | **0** | 0 |
| Custom axioms | **0** | 0 |
| Integration tests | 8/8 PASS | 8/8 PASS |
| New theorems (Fase 6) | ≥ 5 | ≥ 8 |

---

## Criteria: Fase 7 — ematchF Soundness (v1.0.0)

### F7S1 — Pattern.eval [FUND]

<!-- CHECK:F7S1 -->
| ID | Criteria | Weight |
|----|----------|--------|
| `F7S1-DEF-1` | `Pattern.eval` denotational semantics: PVar → v(σ(pv)), PNode → evalOp(childVals) | REQUIRED |
| `F7S1-DEF-2` | Total function (returns `Option Val`, no sorry, no partial) | REQUIRED |
| `F7S1-EDGE-1` | Leaf pattern `PNode op []` evaluates correctly | CHECK |
| `F7S1-EDGE-2` | Unbound variable returns `none` | CHECK |
| `F7S1-QUAL-1` | Imports only EMatch + SemanticSpec (separation of concerns) | REQUIRED |
| `F7S1-ARCH-1` | Substitution model explicitly documented | REQUIRED |

### F7S2 — Pattern.eval props [FUND]

<!-- CHECK:F7S2 -->
| ID | Criteria | Weight |
|----|----------|--------|
| `F7S2-THM-1` | `Pattern.eval_well_typed` | REQUIRED |
| `F7S2-THM-2` | `Pattern.eval_ext`: extensionality under root-equivalent valuations | REQUIRED |
| `F7S2-THM-3` | Zero sorry | REQUIRED |
| `F7S2-STRESS-1` | Compatible with existing `NodeSemantics` | REQUIRED |
| `F7S2-QUAL-1` | Proofs by structural induction on Pattern | CHECK |

### F7S3 — ematchF_sound [CRIT/GATE]

<!-- CHECK:F7S3 -->
| ID | Criteria | Weight |
|----|----------|--------|
| `F7S3-THM-1` | `ematchF_sound`: σ ∈ ematchF → Pattern.eval(pat, env, v, σ) = some(v(root classId)) | REQUIRED |
| `F7S3-THM-2` | Zero sorry | REQUIRED |
| `F7S3-THM-3` | References actual `ematchF` from SaturationSpec, not re-implementation | REQUIRED |
| `F7S3-EDGE-1` | PVar pattern with existing binding requires root equality | CHECK |
| `F7S3-EDGE-2` | Fuel exhaustion = empty result | CHECK |
| `F7S3-STRESS-1` | Multiple matches in same class all sound | CHECK |
| `F7S3-STRESS-2` | Shared variable pattern (diamond) | CHECK |
| `F7S3-QUAL-1` | Gate de-risk: sketch before F7S4 | REQUIRED |

### F7S4 — applyRuleF_internal [CRIT]

<!-- CHECK:F7S4 -->
| ID | Criteria | Weight |
|----|----------|--------|
| `F7S4-THM-1` | `applyRuleF_preserves_cv_internal`: NO `PreservesCV` hypothesis | REQUIRED |
| `F7S4-THM-2` | Uses ematchF_sound (F7S3) | REQUIRED |
| `F7S4-THM-3` | Composes with existing SoundRule infrastructure | REQUIRED |
| `F7S4-THM-4` | Zero sorry | REQUIRED |
| `F7S4-ROBUST-1` | Old `applyRulesF_preserves_cv` still compiles | REQUIRED |
| `F7S4-ROBUST-2` | Backward compatible for users with existing PreservesCV proofs | REQUIRED |

### F7S5 — saturateF_internal [CRIT]

<!-- CHECK:F7S5 -->
| ID | Criteria | Weight |
|----|----------|--------|
| `F7S5-THM-1` | `saturateF_preserves_consistent_internal`: hypothesis is `SoundRewriteRule`, NOT `PreservesCV` | REQUIRED |
| `F7S5-THM-2` | Derives per-rule PreservesCV from SoundRewriteRule via F7S4 | REQUIRED |
| `F7S5-THM-3` | Zero sorry | REQUIRED |
| `F7S5-THM-4` | Old `saturateF_preserves_consistent` preserved | REQUIRED |
| `F7S5-QUAL-1` | Short proof (<30 lines) by composition | CHECK |

### F7S6 — pipeline_update [HOJA]

<!-- CHECK:F7S6 -->
| ID | Criteria | Weight |
|----|----------|--------|
| `F7S6-BUILD-1` | Full `lake build` clean | REQUIRED |
| `F7S6-BUILD-2` | Integration tests 8/8 PASS | REQUIRED |
| `F7S6-SORRY-1` | Global sorry = 0 | REQUIRED |
| `F7S6-THM-1` | `full_pipeline_soundness_internal` using SoundRewriteRule | REQUIRED |
| `F7S6-THM-2` | Old `full_pipeline_soundness_greedy` preserved | REQUIRED |
| `F7S6-DOC-1` | ARCHITECTURE.md Fase 7 completed | REQUIRED |
| `F7S6-DOC-2` | README.md: v1.0.0, "first verified eqsat" | REQUIRED |
| `F7S6-DOC-3` | EMatchSpec.lean in LambdaSat.lean imports | REQUIRED |
| `F7S6-TAG-1` | Git tag `v1.0.0` | REQUIRED |

### Aggregate Targets (v1.0.0)

| Métrica | Target | Stretch |
|---------|--------|---------|
| LOC total | ≥ 7,000 | ≥ 7,500 |
| Teoremas total | ≥ 210 | ≥ 225 |
| Sorry count | **0** | 0 |
| Custom axioms | **0** | 0 |
| Integration tests | 8/8 PASS | 8/8 PASS |
| New theorems (Fase 7) | ≥ 8 | ≥ 12 |
| New file (EMatchSpec.lean) | ≥ 200 LOC | ≥ 300 LOC |
| `PreservesCV` eliminated from user API | YES | YES |

### Cross-Cutting Criteria

<!-- CHECK:CROSS -->
| ID | Criteria |
|----|----------|
| `CROSS-1` | No regression: every v0.2.0 theorem compiles with identical or stronger statement |
| `CROSS-2` | Sorry monotonic: v0.2.0(1) → v0.3.0(0) → v1.0.0(0) |
| `CROSS-3` | Theorem count monotonic: v0.2.0(188) → v0.3.0(≥195) → v1.0.0(≥210) |
| `CROSS-4` | No `native_decide` on proof-relevant types |
| `CROSS-5` | No `simp [*]` in final proofs |
| `CROSS-6` | Build reproducibility: `lake clean && lake build` succeeds |

### Risk Assessment

| Node | Risk | Mitigation |
|------|------|------------|
| F6S2 | HIGH | Gate de-risk: sketch proof before dependents |
| F6S4 | MEDIUM | Linear dependency; F6S3 MUST work first |
| F7S3 | HIGH | Gate de-risk: sketch proof before F7S4 |
| F7S4 | MEDIUM | Composition of ematchF_sound + existing infra |
| F7S1 | LOW | Definition, not proof — but bad def makes F7S3 impossible |

---

## Criteria: Fase 8 — Discharge Hypotheses + Polish (v1.1.0)

### Mechanical Checks (all nodes)

<!-- CHECK:MECH-v1.1.0 -->
| ID | Check | Method | Pass Criteria |
|----|-------|--------|---------------|
| `MECH-1` | Zero sorry | `grep -rn sorry LambdaSat/` | 0 matches (excluding comments) |
| `MECH-2` | Zero custom axioms | `lean_verify` per new theorem | Only `propext`, `Quot.sound`, `Classical.choice` |
| `MECH-3` | Clean build | `lake build` | Exit 0 |
| `MECH-4` | Zero warnings | `lake build 2>&1` | No warnings |
| `MECH-5` | No `native_decide` | Manual inspection | Only in `Decidable`/`Bool` contexts |
| `MECH-6` | No `simp [*]` | Manual inspection | All `simp` with explicit lists or `simp only` |
| `MECH-7` | Doc comments | Manual inspection | All new `def`, `theorem` with `/-- -/` |
| `MECH-8` | `lean_verify` clean | MCP tool per theorem | Only standard axioms |

### F8S1 — SameShapeSemantics_holds [FUND]

<!-- CHECK:F8S1 -->
| ID | Criteria | Weight |
|----|----------|--------|
| `F8S1-THM-1` | Theorem proving SameShapeSemantics (or equivalent lemma) compiles without sorry | REQUIRED |
| `F8S1-THM-2` | Uses only existing NodeSemantics axioms (evalOp_ext, evalOp_mapChildren, mapChildren_children) or minimal new preconditions | REQUIRED |
| `F8S1-THM-3` | `lean_verify` shows zero custom axioms | REQUIRED |
| `F8S1-EDGE-1` | Handles ops with empty children (leaf nodes like Const, Var) | CHECK |
| `F8S1-EDGE-2` | Handles sameShape=false case (theorem simply doesn't apply) | CHECK |
| `F8S1-ARCH-1` | Does NOT modify NodeSemantics typeclass definition | REQUIRED |
| `F8S1-ARCH-2` | If precondition needed, it's trivially dischargeable for ArithOp | REQUIRED |
| `F8S1-QUAL-1` | Proof ≤ 60 lines | CHECK |

### F8S2 — ematchF_substitution_bounded [FUND]

<!-- CHECK:F8S2 -->
| ID | Criteria | Weight |
|----|----------|--------|
| `F8S2-THM-1` | `ematchF_substitution_bounded`: ∀ σ ∈ ematchF fuel g pat classId, ∀ pv id, σ.get? pv = some id → id < g.uf.parent.size | REQUIRED |
| `F8S2-THM-2` | Zero sorry | REQUIRED |
| `F8S2-THM-3` | `lean_verify` shows zero custom axioms | REQUIRED |
| `F8S2-EDGE-1` | fuel=0 → empty list (vacuous truth) | CHECK |
| `F8S2-EDGE-2` | patVar case: σ has exactly 1 binding = classId | CHECK |
| `F8S2-EDGE-3` | node case with no matching classes → empty result | CHECK |
| `F8S2-STRESS-1` | Deep pattern (depth >> fuel) → empty result | CHECK |
| `F8S2-ROBUST-1` | Composes with existing matchChildren_sound | REQUIRED |
| `F8S2-QUAL-1` | Proof by structural induction on Pattern + fuel | CHECK |

### F8S3 — InstantiateEvalSound_holds [CRIT/GATE]

<!-- CHECK:F8S3 -->
| ID | Criteria | Weight |
|----|----------|--------|
| `F8S3-THM-1` | Theorem proving InstantiateEvalSound: instantiateF preserves CV + PMI + SHI + value correct | REQUIRED |
| `F8S3-THM-2` | Value correctness: `v'(root g'.uf id) = Pattern.eval pat env (substVal v g.uf σ)` | REQUIRED |
| `F8S3-THM-3` | Value agreement: `∀ i, i < g.uf.parent.size → v' i = v i` | REQUIRED |
| `F8S3-THM-4` | Size monotonicity: `g.uf.parent.size ≤ g'.uf.parent.size` | REQUIRED |
| `F8S3-THM-5` | Zero sorry | REQUIRED |
| `F8S3-THM-6` | `lean_verify` shows zero custom axioms | REQUIRED |
| `F8S3-EDGE-1` | patVar case: g unchanged, v' = v | CHECK |
| `F8S3-EDGE-2` | node with empty subpats (leaf-like Pattern.node) | CHECK |
| `F8S3-STRESS-1` | Deeply nested pattern (foldl over many subpats) | CHECK |
| `F8S3-ROBUST-1` | Reutiliza instantiateF_preserves_consistency (no duplica) | REQUIRED |
| `F8S3-ROBUST-2` | SHI preservation via add (not merge) path | CHECK |
| `F8S3-QUAL-1` | Gate de-risk: sketch with sorry BEFORE dependents | REQUIRED |
| `F8S3-QUAL-2` | Proof ≤ 250 lines | CHECK |

### F8S4 — Update pipeline signatures [HOJA]

<!-- CHECK:F8S4 -->
| ID | Criteria | Weight |
|----|----------|--------|
| `F8S4-SIG-1` | `full_pipeline_soundness_internal` has NO `SameShapeSemantics` hypothesis | REQUIRED |
| `F8S4-SIG-2` | `full_pipeline_soundness_internal` has NO `InstantiateEvalSound` hypothesis | REQUIRED |
| `F8S4-SIG-3` | `full_pipeline_soundness_internal` has NO `hematch_bnd` inline hypothesis | REQUIRED |
| `F8S4-SIG-4` | Intermediate theorems (applyRuleAtF_sound, saturateF_preserves_consistent_internal) updated | REQUIRED |
| `F8S4-BUILD-1` | Full `lake build` clean | REQUIRED |
| `F8S4-ROBUST-1` | Path A theorems (full_pipeline_soundness_greedy) unchanged | REQUIRED |
| `F8S4-ROBUST-2` | Old SoundRewriteRule path still works | REQUIRED |
| `F8S4-DOC-1` | Docstrings updated to reflect "zero hypotheses" | REQUIRED |

### F8S5 — P1-P5 docs and tests [HOJA]

<!-- CHECK:F8S5 -->
| ID | Criteria | Weight |
|----|----------|--------|
| `F8S5-P1-1` | README.md theorem count matches actual (grep count) | REQUIRED |
| `F8S5-P1-2` | README.md LOC count matches actual (wc -l) | REQUIRED |
| `F8S5-P1-3` | README.md states "zero hypotheses" for Path B | REQUIRED |
| `F8S5-P3-1` | ≥3 #eval edge-case tests added (empty graph, fuel=0, self-merge) | REQUIRED |
| `F8S5-P4-1` | Integration tests still 8/8 PASS + new edge cases PASS | REQUIRED |
| `F8S5-P5-1` | README documents TCB boundary for ParallelMatch/ParallelSaturate | REQUIRED |
| `F8S5-P5-2` | P2 (SlimCheck) explicitly deferred to v1.2.0 with justification | REQUIRED |
| `F8S5-DOC-1` | ARCHITECTURE.md Fase 8 marked completed | REQUIRED |
| `F8S5-DOC-2` | BENCHMARKS.md: Fase 8 results recorded | REQUIRED |
| `F8S5-TAG-1` | Git tag `v1.1.0` | REQUIRED |

### Aggregate Targets (v1.1.0)

| Métrica | Target | Stretch |
|---------|--------|---------|
| LOC total | ≥ 7,100 | ≥ 7,400 |
| Teoremas total | ≥ 230 | ≥ 240 |
| Sorry count | **0** | 0 |
| Custom axioms | **0** | 0 |
| Hipótesis en full_pipeline_soundness_internal | **0** (was 3) | 0 |
| Integration tests | 8/8 PASS | 10+ PASS |
| New theorems (Fase 8) | ≥ 5 | ≥ 10 |
| `lake build` time | ≤ v1.0.0 + 10% | ≤ v1.0.0 |
| Path B fully self-contained | YES | YES |

### Cross-Cutting Criteria (v1.1.0)

<!-- CHECK:CROSS-v1.1.0 -->
| ID | Criteria |
|----|----------|
| `CROSS-1` | No regression: every v1.0.0 theorem compiles with identical or stronger statement |
| `CROSS-2` | Sorry monotonic: 0 → 0 |
| `CROSS-3` | Theorem count monotonic: v1.0.0(226) → v1.1.0(≥230) |
| `CROSS-4` | Hypothesis count: v1.0.0(3) → v1.1.0(0) in full_pipeline_soundness_internal |
| `CROSS-5` | Build reproducibility: `lake clean && lake build` succeeds |

### Risk Assessment (v1.1.0)

| Node | Risk | Mitigation |
|------|------|------------|
| F8S3 | HIGH | Gate de-risk: sketch with sorry before B22. Reutilizar patrón de processClass_shi_combined |
| F8S1 | MEDIUM | De-risk: verify evalOp_mapChildren + LawfulBEq approach compiles before full proof |
| F8S2 | LOW | Structural induction, ematchF read-only, reutiliza matchChildren_sound |
| F8S4 | LOW | Mechanical replacement of hypotheses with theorem calls |
| F8S5 | LOW | Documentation + tests, no proofs |

---

## Legacy Results (pre-structured)

> Benchmark results not linked to any identified phase. Preserved for reference.

### Legacy Results (pre-structured)

> Benchmark results not linked to any identified phase. Preserved for reference.

### Aggregate (v0.1.0)

| Métrica | Target | Actual | Status |
|---------|--------|--------|--------|
| LOC total | ≥ 6,000 | 6,241 | **PASS** |
| Teoremas total | ≥ 148 | 181 | **PASS** (+22%) |
| Sorry | 0 | 0 | **PASS** |
| Axiomas | 0 | 0 | **PASS** |
| Módulos | 17+ | 17 src + 1 test | **PASS** |
| Tests | 8 | 8/8 PASS | **PASS** |
| `lake build` | < 120s | 20 jobs OK | **PASS** |

### VR1CS-Lean vs LambdaSat-Lean Comparison

| Métrica | VR1CS-Lean | LambdaSat-Lean | Delta |
|---------|-----------|----------------|-------|
| LOC (e-graph) | 7,435 | 5,926 | -20.3% |
| Teoremas | 158 | 181 | +14.6% |
| Densidad (thm/KLOC) | 21.2 | 30.5 | +43.9% |
| Typeclasses | 1 | 4 | +3 |
| Instances | 5 | 9 | +4 |

### Verificación Formal

| Invariante | Significado | Usado por |
|------------|-------------|-----------|
| `ConsistentValuation` | UF-equiv + node-consistency | extractF_correct, extractILP_correct |
| `BestNodeInv` | bestNode in class.nodes | extractF_correct |
| `ExtractableSound` | reconstruct preserves semantics | extractF_correct, extractILP_correct |
| `ValidSolution` | checkSolution = true | ilp_extraction_soundness |
| `WellFormed` | ParentsBounded + IsAcyclic | Todos los teoremas |

### TCB (Trusted Computing Base)

| Componente | En TCB? | Razón |
|------------|---------|-------|
| Lean 4 kernel | Sí | Compilador + verificador de tipos |
| Extractable instances | Sí | El usuario provee reconstruct/evalExpr |
| checkSolution | No | Decidable, verificado |
| ILP solver externo (HiGHS) | Solo optimality | Correctness verificada por checkSolution |
| Pure Lean B&B | Solo optimality | Fallback sin IO |

---

### GATE: InstantiateEvalSound (v0.1.0)

**Closed**: 2026-02-25 | **Status**: PASS

#### 1. What is tested and why

Nodes covered: F8S3 InstantiateEvalSound_holds.

#### 2. Performance

| Metric | Target | Actual | Status |
|--------|--------|--------|--------|
| LOC | — | 1936 | — |
| Theorems | — | 92 | — |
| Lemmas | — | 0 | — |
| Defs | — | 15 | — |
| Sorry count | 0 | 0 | PASS |

#### 3. Acceptability Analysis

- **Acceptable**: Meets minimum criteria (zero sorry, compiles)

#### 4. Bugs, Warnings, Sorries

| Item | Location | Cause | Affected Nodes | Mitigation |
|------|----------|-------|----------------|------------|
| (none) | — | — | — | — |

### Pipeline + Polish (v0.1.0)

**Closed**: 2026-02-25 | **Status**: PASS

#### 1. What is tested and why

Nodes covered: F8S4 Update pipeline signatures, F8S5 P1-P5 docs and tests.

#### 2. Performance

| Metric | Target | Actual | Status |
|--------|--------|--------|--------|
| LOC | — | 0 | — |
| Theorems | — | 0 | — |
| Lemmas | — | 0 | — |
| Defs | — | 0 | — |
| Sorry count | 0 | 0 | PASS |

#### 3. Acceptability Analysis

- **Acceptable**: Meets minimum criteria (zero sorry, compiles)

#### 4. Bugs, Warnings, Sorries

| Item | Location | Cause | Affected Nodes | Mitigation |
|------|----------|-------|----------------|------------|
| (none) | — | — | — | — |

## Previous Results

(none)
