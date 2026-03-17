# OptiSat

Formally verified equality saturation engine in Lean 4, parameterized by typeclasses. OptiSat provides a domain-agnostic e-graph with 363 theorems, **zero sorry**, zero custom axioms, and a machine-checked soundness chain from union-find operations through pattern matching, saturation, and extraction — with **zero external hypotheses** in the final pipeline theorem, **verified DP-optimal extraction** via treewidth decomposition, **user-facing pipeline soundness** via `optimizeF_soundness`, and **extraction completeness** via `extractAuto_complete`.

Generalized from [VR1CS-Lean](https://github.com/manuel0921/vr1cs-lean) v1.3.0.

---

## What it solves

Equality saturation is a program optimization technique that explores an exponential space of equivalent programs simultaneously. Most implementations are unverified — if the e-graph engine has a bug, the optimizer silently produces wrong results.

OptiSat proves, in Lean 4, that every step of the equality saturation pipeline preserves semantic equivalence:

```lean
-- Merging equivalent classes preserves all valuations
theorem merge_consistent (g : EGraph Op) (id1 id2 : EClassId)
    (env : Nat → Val) (v : EClassId → Val)
    (hc : ConsistentValuation g env v) (heq : v id1 = v id2) : ...

-- Sound rewrite rules preserve consistency
theorem sound_rule_preserves_consistency (g : EGraph Op)
    (rule : SoundRewriteRule Op Expr Val) (lhsId rhsId : EClassId)
    (env : Nat → Val) (v : EClassId → Val)
    (hv : ConsistentValuation g env v) : ...

-- E-matching is sound: returned substitutions match pattern semantics (v1.0.0)
theorem ematchF_sound (g : EGraph Op) (pat : Pattern Op)
    (classId : EClassId) (σ : Substitution)
    (hmem : σ ∈ ematchF fuel g pat classId) :
    Pattern.eval pat env v σ = v (root g.unionFind classId)

-- Full pipeline with zero external hypotheses (v1.1.0)
theorem full_pipeline_soundness (g : EGraph Op)
    (rules : List (PatternSoundRule Op Val))
    (hcv : ConsistentValuation g env v) (hpmi : PostMergeInvariant g)
    (hshi : SemanticHashconsInv g env v) (hhcb : HashconsChildrenBounded g)
    ... :
    ∃ v_sat, EvalExpr.evalExpr expr env =
      v_sat (root (saturateF ...).unionFind rootId)
```

---

## Typeclass architecture

OptiSat is parameterized over three typeclasses. To use it for a new domain, implement these:

```lean
-- 1. Define node structure
class NodeOps (Op : Type) where
  children : Op → List EClassId
  mapChildren : (EClassId → EClassId) → Op → Op
  replaceChildren : Op → List EClassId → Op
  mapChildren_children : ∀ f op, children (mapChildren f op) = (children op).map f

-- 2. Define semantics
class NodeSemantics (Op : Type) (Val : Type) extends NodeOps Op where
  evalOp : Op → (Nat → Val) → (EClassId → Val) → Val
  evalOp_ext : ...     -- evalOp depends on v only through children
  evalOp_mapChildren : ... -- mapChildren commutes with evalOp

-- 3. Define extraction
class Extractable (Op : Type) (Expr : Type) extends NodeOps Op where
  reconstruct : Op → List Expr → Option Expr
```

See `Tests/IntegrationTests.lean` for a complete example with an arithmetic domain (`ArithOp`).

---

## Soundness chain

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
    → full_pipeline_soundness (TranslationValidation)

Path D (v1.3.0 — unified extraction):
  extractF_correct (ExtractSpec)
  + ilp_extraction_soundness (ILPSpec)
    → extract_correct (Extraction) — strategy-parameterized dispatch

Path E (v1.4.0 — DP optimality):
  dpLeaf/Forget/Introduce/Join_DPCompleteInv (DPTableLemmas)
    → runDP_DPCompleteInv (DPTableLemmas) — ValidNTD induction
      → dp_optimal_of_validNTD: dpOptimalCost ≤ selectionCost

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

**Sorry status**: **Zero sorry** since v0.3.0 through v1.5.2. The HashMap API gap (`m.keys` vs `m.toList.map Prod.fst`) that existed in v1.5.1 was closed using `Std.HashMap.keys`/`Std.HashMap.toList` + `Std.HashMap.nodup_keys` bridge lemmas. **Zero external hypotheses** since v1.1.0.

In v0.3.0, `PreservesCV` required users to prove that each rule application preserves consistency. In v1.0.0, `ematchF_sound` + `InstantiateEvalSound` derive this automatically from pattern soundness. In v1.1.0, the three remaining hypotheses (`SameShapeSemantics`, `InstantiateEvalSound`, `ematchF_substitution_bounded`) are all discharged as internal theorems, yielding `full_pipeline_soundness` with only structural assumptions about the initial e-graph state.

Four-tier invariant system:
- **EGraphWF**: Full well-formedness (hashcons + classes + UF consistency)
- **PostMergeInvariant**: Partial during merge (before rebuild)
- **AddExprInv**: Partial during addExpr (recursive insertion)
- **SemanticHashconsInv**: Semantic hashcons consistency through rebuild (v0.3.0)

---

## Build

**Requirements**: `elan`, Lean 4 toolchain `leanprover/lean4:v4.26.0`.

```bash
git clone <repo>
cd optisat
lake build
```

Run integration tests:

```bash
lake env lean Tests/IntegrationTests.lean
```

No Mathlib dependency — OptiSat is self-contained.

---

## Example: arithmetic domain

```lean
-- Define operations
inductive ArithOp where
  | const : Nat → ArithOp
  | var   : Nat → ArithOp
  | add   : EClassId → EClassId → ArithOp
  | mul   : EClassId → EClassId → ArithOp

-- Implement typeclasses (NodeOps, NodeSemantics, Extractable)
-- ... (see Tests/IntegrationTests.lean for full implementation)

-- Build e-graph and optimize
let g0 : EGraph ArithOp := .empty
let (xId, g1) := g0.add ⟨.var 0⟩
let (c3Id, g2) := g1.add ⟨.const 3⟩
let (addId, g3) := g2.add ⟨.add xId c3Id⟩
let g4 := g3.computeCosts (fun _ => 1)
let result : Option ArithExpr := extractAuto g4 addId
-- result = some (.add (.var 0) (.const 3))
```

---

## File structure

```
OptiSat/
├── LambdaSat/
│   ├── UnionFind.lean              -- Union-Find with path compression (44 theorems)
│   ├── Core.lean                   -- EGraph Op [NodeOps Op]: add, merge, rebuild
│   ├── CoreSpec.lean               -- EGraphWF, PostMergeInvariant, AddExprInv (79 theorems)
│   ├── EMatch.lean                 -- Pattern Op, generic e-matching
│   ├── Saturate.lean               -- Fuel-based saturation loop
│   ├── SemanticSpec.lean           -- ConsistentValuation, SemanticHashconsInv (49 theorems)
│   ├── SoundRule.lean              -- SoundRewriteRule, conditional rules (3 theorems)
│   ├── SaturationSpec.lean         -- Saturation soundness chain (13 theorems, 0 sorry)
│   ├── AddNodeTriple.lean          -- add_node_triple: add preserves (CV,PMI,SHI,HCB) (3 theorems) ← v1.1.0
│   ├── EMatchSpec.lean             -- ematchF_sound, InstantiateEvalSound_holds (25 theorems) ← v1.0.0+
│   ├── Extractable.lean            -- Extractable typeclass + extractF
│   ├── ExtractSpec.lean            -- extractF_correct, extractAuto_correct
│   ├── Optimize.lean               -- Saturation + extraction pipelines
│   ├── ILP.lean                    -- ILP types and data structures
│   ├── ILPEncode.lean              -- E-graph → ILP encoding + encoding properties (5 theorems) ← v1.2.0
│   ├── ILPSolver.lean              -- HiGHS external + branch-and-bound solver
│   ├── ILPCheck.lean               -- Certificate checking + verified extraction
│   ├── ILPSpec.lean                -- ILP soundness: check*_sound, extractILP_correct, fuel_mono (12 theorems) ← v1.2.0
│   ├── Extraction.lean             -- Unified ExtractionStrategy dispatch, extract_correct (2 theorems) ← v1.3.0
│   ├── ParallelMatch.lean          -- IO.asTask parallel e-matching
│   ├── ParallelSaturate.lean       -- Parallel saturation with threshold fallback
│   ├── TranslationValidation.lean  -- ProofWitness, full_pipeline_soundness (8 theorems)
│   ├── PipelineSoundness.lean      -- optimizeF, optimizeWithStrategyF + soundness (2 theorems) ← v1.5.0
│   ├── CompletenessSpec.lean       -- AcyclicBestNodeDAG, extractF_of_rank, extractAuto_complete (7 theorems) ← v1.5.1
│   ├── TreewidthDP.lean            -- DP types, operations, dpOptimalityWitness (9 theorems) ← v1.4.0
│   ├── DPTableLemmas.lean          -- DP correctness: 4 operation proofs + dp_optimal_of_validNTD (45 theorems) ← v1.4.0
│   └── Util/
│       ├── NatOpt.lean             -- NatOpt (Option Nat with min/le) (11 theorems) ← v1.4.0
│       ├── NiceTree.lean           -- Nice tree decomposition + treeFold catamorphism (6 theorems) ← v1.4.0
│       ├── FoldMin.lean            -- Fold-with-minimum lemmas (6 theorems) ← v1.4.0
│       └── InsertMin.lean          -- Insert-min HashMap operations (4 theorems) ← v1.4.0
├── Tests/
│   └── IntegrationTests.lean       -- ArithOp concrete instance, 33 pipeline tests
├── lakefile.toml
├── lean-toolchain                  -- leanprover/lean4:v4.26.0
└── LambdaSat.lean                  -- module root
```

---

## Extraction modes

OptiSat supports two extraction strategies, both with verified soundness:

| Mode | Strategy | Theorem | TCB |
|------|----------|---------|-----|
| Greedy | Follow `bestNode` pointers (fuel-based) | `extractF_correct` | Lean kernel |
| ILP | Encode as integer linear program, solve externally, check certificate | `ilp_extraction_soundness` | Lean kernel + ILP solver (certificate-checked) |
| DP | Treewidth DP on nice tree decomposition, optimal cost | `dp_optimal_of_validNTD` | Lean kernel |

All three are unified under `extract_correct` (v1.3.0+), which dispatches by `ExtractionStrategy`.

The ILP solver (HiGHS or built-in branch-and-bound) is outside the TCB — its output is validated by `checkSolution` before extraction.

### Trusted Computing Base (TCB)

The soundness guarantee depends only on:

1. **Lean 4 kernel** — type-checks all proofs
2. **Typeclass instances** — users must correctly implement `NodeOps`, `NodeSemantics`, `Extractable` for their domain. OptiSat proves that *given correct instances*, the pipeline is sound.

Outside the TCB:
- **ILP solver** (HiGHS/B&B): certificate-checked by `checkSolution`
- **ParallelMatch.lean** / **ParallelSaturate.lean**: use `IO.asTask` for parallel execution. These are `IO`-based wrappers around the verified sequential algorithms. They do not carry formal proofs — their correctness depends on Lean's task runtime producing the same results as sequential execution.
- **Optimize.lean**: `optimizeExpr`, `optimizeExprILP`, `optimizeExprAuto` use `partial def saturate` (with timeouts, node limits, statistics). For formally verified optimization, use `optimizeF` or `optimizeWithStrategyF` from **PipelineSoundness.lean**, which compose total, verified spec functions with proven correctness theorems.

---

## Phases

| Fase | Status | Scope |
|------|--------|-------|
| Fase 1: Foundation | Complete | UnionFind, EGraph Core (typeclass-parameterized) |
| Fase 2: Specification | Complete | CoreSpec (79 thms), EMatch, Saturate, SemanticSpec (49 thms) |
| Fase 3: Extraction + Optimization | Complete | Extractable, ExtractSpec, Optimize, ILP pipeline + ILPSpec |
| Fase 4: Parallelism + Integration | Complete | ParallelMatch, ParallelSaturate, TranslationValidation, 29 integration tests |
| Fase 5: Saturation Soundness | Complete | SoundRule, SaturationSpec — closes the soundness gap for saturation |
| Fase 6: Close Rebuild Sorry | Complete | SemanticHashconsInv + rebuildStepBody_preserves_triple — zero sorry |
| Fase 7: ematchF Soundness | Complete | Pattern.eval, ematchF_sound, full_pipeline_soundness_internal — eliminates PreservesCV |
| Fase 8: Discharge Hypotheses | Complete | InstantiateEvalSound_holds, ematchF_substitution_bounded, full_pipeline_soundness — zero external hypotheses |
| Fase 9: ILP Certificate Verification | Complete | checkSolution soundness, encoding properties, extractILP fuel monotonicity (15 new theorems) |
| Fase 10: Unified Extraction | Complete | ExtractionStrategy dispatch, extract_correct master theorem (greedy + ILP) |
| Fase 11: DP Extraction Optimality | Complete | Treewidth DP via nice tree decompositions, dp_optimal_of_validNTD (81 new theorems) |
| Fase 12: API-Specification Bridge | Complete | Verified pipeline functions + user-facing soundness (optimizeF_soundness, optimizeWithStrategyF_soundness) |
| Fase 13: Completeness | Complete | bestNode DAG acyclicity, fuel sufficiency, extraction completeness (extractAuto_complete) |

**Current version: v1.5.2** — 363 theorems, **zero sorry**, zero custom axioms, **zero external hypotheses** in `full_pipeline_soundness`, **verified DP-optimal extraction** via `dp_optimal_of_validNTD`, **user-facing pipeline soundness** via `optimizeF_soundness`, **extraction completeness** via `extractAuto_complete`.

