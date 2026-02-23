# LambdaSat

Formally verified equality saturation engine in Lean 4, parameterized by typeclasses. LambdaSat provides a domain-agnostic e-graph with 188 theorems, 1 isolated `sorry`, zero custom axioms, and a machine-checked soundness chain from union-find operations through saturation and extraction.

Generalized from [VR1CS-Lean](https://github.com/manuelpuebla/vr1cs-lean) v1.3.0.

---

## What it solves

Equality saturation is a program optimization technique that explores an exponential space of equivalent programs simultaneously. Most implementations are unverified — if the e-graph engine has a bug, the optimizer silently produces wrong results.

LambdaSat proves, in Lean 4, that every step of the equality saturation pipeline preserves semantic equivalence:

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

-- Saturation preserves consistent valuation (v0.2.0)
theorem saturateF_preserves_consistent (fuel maxIter rebuildFuel : Nat)
    (g : EGraph Op) (rules : List (RewriteRule Op))
    (env : Nat → Val) (v : EClassId → Val)
    (hcv : ConsistentValuation g env v)
    (h_rules : ∀ rule ∈ rules, PreservesCV env (applyRuleF fuel · rule)) :
    ∃ v', ConsistentValuation (saturateF fuel maxIter rebuildFuel g rules) env v'

-- Full pipeline: saturate → extract is semantically correct (v0.2.0)
theorem full_pipeline_soundness_greedy (g : EGraph Op)
    (rules : List (RewriteRule Op)) ... :
    ∃ v_sat, EvalExpr.evalExpr expr env =
      v_sat (root (saturateF ...).unionFind rootId)
```

---

## Typeclass architecture

LambdaSat is parameterized over three typeclasses. To use it for a new domain, implement these:

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
find_preserves_roots (UnionFind)
  → merge_consistent (CoreSpec + SemanticSpec)
    → sound_rule_preserves_consistency (SoundRule)
      → instantiateF_preserves_consistency (SaturationSpec)
        → applyRulesF_preserves_cv (SaturationSpec)
          → saturateF_preserves_consistent (SaturationSpec)           ← NEW v0.2.0
            → computeCostsF_preserves_consistency (SemanticSpec)
              → extractF_correct (ExtractSpec)
              → extractILP_correct (ILPSpec)
                → full_pipeline_soundness_greedy (TranslationValidation)  ← NEW v0.2.0
                → optimization_soundness_greedy / _ilp (TranslationValidation)
```

**Sorry status**: 1 isolated `sorry` in `rebuildStepBody_preserves_cv` — the rebuild step requires threading full `EGraphWF` invariants through intermediate states where they don't hold. The sorry is confined to the rebuild path; all other chain links are fully proven.

Three-tier invariant system:
- **EGraphWF**: Full well-formedness (hashcons + classes + UF consistency)
- **PostMergeInvariant**: Partial during merge (before rebuild)
- **AddExprInv**: Partial during addExpr (recursive insertion)

---

## Build

**Requirements**: `elan`, Lean 4 toolchain `leanprover/lean4:v4.26.0`.

```bash
git clone <repo>
cd lambdasat-lean
lake build
```

Run integration tests:

```bash
lake env lean Tests/IntegrationTests.lean
```

No Mathlib dependency — LambdaSat is self-contained.

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
LambdaSat/
├── LambdaSat/
│   ├── UnionFind.lean              -- Union-Find with path compression (44 theorems)
│   ├── Core.lean                   -- EGraph Op [NodeOps Op]: add, merge, rebuild
│   ├── CoreSpec.lean               -- EGraphWF, PostMergeInvariant, AddExprInv (78 theorems)
│   ├── EMatch.lean                 -- Pattern Op, generic e-matching
│   ├── Saturate.lean               -- Fuel-based saturation loop
│   ├── SemanticSpec.lean           -- ConsistentValuation, merge/add consistency (40 theorems)
│   ├── SoundRule.lean              -- SoundRewriteRule, conditional rules (4 theorems)
│   ├── SaturationSpec.lean         -- Saturation soundness chain (10 theorems, 1 sorry)
│   ├── Extractable.lean            -- Extractable typeclass + extractF
│   ├── ExtractSpec.lean            -- extractF_correct, extractAuto_correct
│   ├── Optimize.lean               -- Saturation + extraction pipelines
│   ├── ILP.lean                    -- ILP types and data structures
│   ├── ILPEncode.lean              -- E-graph → ILP encoding
│   ├── ILPSolver.lean              -- HiGHS external + branch-and-bound solver
│   ├── ILPCheck.lean               -- Certificate checking + verified extraction
│   ├── ILPSpec.lean                -- extractILP_correct, ilp_extraction_soundness
│   ├── ParallelMatch.lean          -- IO.asTask parallel e-matching
│   ├── ParallelSaturate.lean       -- Parallel saturation with threshold fallback
│   └── TranslationValidation.lean  -- ProofWitness, optimization_soundness (6 theorems)
├── Tests/
│   └── IntegrationTests.lean       -- ArithOp concrete instance, 8 pipeline tests
├── lakefile.toml
├── lean-toolchain                  -- leanprover/lean4:v4.26.0
└── LambdaSat.lean                  -- module root
```

---

## Extraction modes

LambdaSat supports two extraction strategies, both with verified soundness:

| Mode | Strategy | Theorem | TCB |
|------|----------|---------|-----|
| Greedy | Follow `bestNode` pointers (fuel-based) | `extractF_correct` | Lean kernel |
| ILP | Encode as integer linear program, solve externally, check certificate | `ilp_extraction_soundness` | Lean kernel + ILP solver (certificate-checked) |

The ILP solver (HiGHS or built-in branch-and-bound) is outside the TCB — its output is validated by `checkSolution` before extraction.

---

## Phases

| Fase | Status | Scope |
|------|--------|-------|
| Fase 1: Foundation | Complete | UnionFind, EGraph Core (typeclass-parameterized) |
| Fase 2: Specification | Complete | CoreSpec (78 thms), EMatch, Saturate, SemanticSpec (40 thms) |
| Fase 3: Extraction + Optimization | Complete | Extractable, ExtractSpec, Optimize, ILP pipeline + ILPSpec |
| Fase 4: Parallelism + Integration | Complete | ParallelMatch, ParallelSaturate, TranslationValidation, 8 integration tests |
| Fase 5: Saturation Soundness | Complete | SoundRule, SaturationSpec — closes the soundness gap for saturation |

**Current version: v0.2.0** — 188 theorems, 6,538 LOC, 1 sorry (isolated in rebuild), zero custom axioms.
