# LambdaSat-Lean: Standalone Verified Equality Saturation Engine

## Motivation

LambdaSat-Lean extracts the verified e-graph engine from VR1CS-Lean into a standalone, domain-agnostic library parameterized by typeclasses. The goal: a reusable verified equality saturation engine for any first-order term rewriting domain.

## Risk Analysis

### Option A: Prose-only (argue generality in the paper)
**Risk: ZERO in code.** Nothing is touched. The risk is *paper credibility* — a reviewer may request the generic artifact and reject if only the hardcoded `CircuitNodeOp` version exists.

### Option B: Refactor VR1CS-Lean in-place
**Risk: HIGH.** `CircuitNodeOp` is hardcoded in `Core.lean` and propagates transitively to 12 of 14 engine files. Changing `EGraph` to `EGraph Op` with typeclasses requires:

- Modifying **Core.lean** (foundational structure, 1,368 LOC of spec depend on it)
- Re-proving **CoreSpec.lean** (64 theorems now about generic `EGraph Op`)
- Re-proving **SemanticSpec.lean** (36 theorems, most complex: 2,061 LOC)
- Adapting **EMatch.lean** (pattern matching with `CircuitPattern` to generic patterns)
- Adapting **ILPCheck.lean** + **ILPSpec.lean** (3 key theorems)
- **All** files importing Core.lean change their signatures

This means touching ~5,100 LOC of spec with ~156 verified theorems. A single type change propagation error breaks the entire proof chain. And this is on a **v1.3.0 released project with tag**. Unacceptable.

### Option C: Standalone from scratch (LambdaSat-Lean)
**Risk to VR1CS-Lean: ZERO.** Not a single byte touched.
**Risk to AMO-Lean: ZERO.** Not a single byte touched.

## Domain Coupling Analysis

| Layer | Source Files | R1CS Coupling | In LambdaSat-Lean |
|-------|-------------|---------------|-------------------|
| Union-Find | `UnionFind.lean` | **ZERO** | Direct copy (1,235 LOC, 44 theorems) |
| E-Graph Core | `Core.lean` | `CircuitNodeOp` hardcoded | Rewrite with `variable {Op : Type} [NodeOps Op]` |
| CoreSpec | `CoreSpec.lean` | Indirect via `ENode` | Re-prove over `ENode Op` (most proofs transfer) |
| Saturate | `Saturate.lean` | Only via `RewriteRule` | Minor interface change |
| EMatch | `EMatch.lean` | `CircuitPattern` | Generic `Pattern Op` |
| ILP* | `ILP.lean`, `ILPEncode.lean`, `ILPSolver.lean` | Only via `ENode` | Type change, logic identical |
| ILPCheck | `ILPCheck.lean` | Via `extractILP` | Generic with `Extractable` typeclass |
| Parallel* | `ParallelMatch.lean`, `ParallelSaturate.lean` | Only via `RewriteRule` | Minor change |
| **SemanticSpec** | `SemanticSpec.lean` | **Deep ZMod p** | `NodeSemantics Op Val` typeclass |
| **ILPSpec** | `ILPSpec.lean` | **Deep ZMod p** | Re-prove over generic `Val` |

## Typeclass Architecture

```lean
/-- Operator interface: structural operations on nodes -/
class NodeOps (Op : Type) where
  children : Op → List EClassId
  mapChildren : Op → (EClassId → EClassId) → Op
  beq : Op → Op → Bool
  hash : Op → UInt64

/-- Semantic interface: denotational semantics for operators -/
class NodeSemantics (Op : Type) (Val : Type) extends NodeOps Op where
  evalOp : Op → (Nat → Val) → (EClassId → Val) → Val

/-- Extraction interface: reconstructing surface expressions -/
class Extractable (Op : Type) (Expr : Type) (Val : Type)
    extends NodeSemantics Op Val where
  reconstruct : Op → List Expr → Option Expr
  evalExpr : Expr → (Nat → Val) → Val
  reconstruct_sound : ∀ op children exprs env v,
    (∀ i, evalExpr (exprs[i]) env = v (children[i])) →
    evalOp op env v = evalExpr (reconstruct op exprs) env
```

## Target Project Structure

```
lambdasat-lean/                      (standalone, ~6,000 LOC, ~156 theorems)
├── LambdaSat/
│   ├── UnionFind.lean               -- direct copy (zero coupling)
│   ├── Core.lean                    -- EGraph Op, NodeOps typeclass
│   ├── CoreSpec.lean                -- EGraphWF Op, PostMergeInvariant Op
│   ├── SemanticSpec.lean            -- ConsistentValuation Op Val
│   ├── EMatch.lean                  -- Pattern Op, generic ematch
│   ├── Saturate.lean                -- generic saturation
│   ├── ILP.lean + ILPEncode.lean    -- generic ILP
│   ├── ILPSolver.lean               -- unchanged
│   ├── ILPCheck.lean + ILPSpec.lean -- extractILP Op Expr Val
│   ├── ParallelMatch.lean           -- generic
│   └── ParallelSaturate.lean        -- generic
├── lean-toolchain
└── lakefile.toml

vr1cs-lean/                          (unchanged, imports lambdasat-lean)
├── VR1CS/
│   ├── Basic.lean                   -- CircuitExpr + CircuitNodeOp instance
│   ├── EGraph/Basic.lean            -- bridge CircuitExpr <-> LambdaSat
│   └── ... (everything else intact)
└── lakefile.toml                    -- adds require lambdasat-lean
```

## Key Design Decisions

1. **UnionFind.lean is a direct copy** — zero R1CS coupling, 1,235 LOC, 44 theorems transfer verbatim.

2. **"Generic" files** (Core, CoreSpec, Saturate, ILP, Parallel) only need `CircuitNodeOp` replaced by a type parameter `Op`. The proof structure is identical because the tactics (`ring`, `simp`, `omega`, `decide`) are domain-agnostic.

3. **"Semantic" files** (SemanticSpec, ILPSpec) need `ZMod p` abstracted to a generic `Val` with `CommRing` structure. Most proofs transfer because they use `ring` tactic.

4. **VR1CS-Lean can eventually import LambdaSat-Lean** as a Lake dependency, but this is not required for the academic paper. The two projects coexist as independent artifacts.

## Potential Instantiations

| Domain | Operator Type | Val Type | Application |
|--------|--------------|----------|-------------|
| **R1CS circuits** | `CircuitNodeOp` | `ZMod p` | ZK proof optimization (VR1CS-Lean) |
| **Tensor graphs** | `TensorOp` | `Tensor Shape` | ML compiler optimization (TENSAT-style) |
| **Lambda calculus** | `LambdaOp` | `Value` | Verified compiler optimization |
| **SQL queries** | `RelAlgOp` | `Relation` | Query optimization |
| **Hardware circuits** | `GateOp` | `BitVec n` | RTL optimization |
| **Polynomial arithmetic** | `PolyOp` | `Polynomial R` | CAS simplification |

## Recommendation

**Option C (LambdaSat-Lean standalone).** Zero risk to existing projects, produces an independently citable artifact, and the majority of proof code transfers because tactics are domain-agnostic.
