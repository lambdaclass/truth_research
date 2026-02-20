# LambdaSat

Formally verified equality saturation engine in Lean 4, parameterized by typeclasses. LambdaSat provides a domain-agnostic e-graph with 181 theorems, zero `sorry`, zero custom axioms, and a machine-checked soundness chain from union-find operations through extraction.

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

-- Greedy extraction produces semantically equivalent expressions
theorem optimization_soundness_greedy (pw : ProofWitness Op Expr)
    (env : Nat → Val) (v : EClassId → Val)
    (hc : ConsistentValuation pw.graph env v) : ...

-- ILP-based extraction with certificate checking
theorem ilp_extraction_soundness (g : EGraph Op) (sol : ILPSolution)
    (rootClass : EClassId) (env : Nat → Val) (v : EClassId → Val) : ...
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
    → sound_rule_preserves_consistency (via SoundRewriteRule typeclass)
      → computeCostsF_preserves_consistency (SemanticSpec)
        → extractF_correct (ExtractSpec)
        → extractILP_correct (ILPSpec)
          → optimization_soundness_greedy / optimization_soundness_ilp (TranslationValidation)
```

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
│   └── TranslationValidation.lean  -- ProofWitness, optimization_soundness (5 theorems)
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

**Current version: v0.1.0** — 181 theorems, 5,327 LOC, zero sorry, zero custom axioms.
