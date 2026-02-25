---
title: "LambdaSat-Lean: A Fully Verified Equality Saturation Engine"
subtitle: "From zero sorry to zero hypotheses — how a typeclass-parameterized e-graph in Lean 4 answers the open problems in verified program optimization"
author: "Manuel Puebla"
date: "February 2026"
abstract: |
  This document presents LambdaSat-Lean, the first formally verified, complete equality saturation engine implemented entirely within a proof assistant. Written in Lean 4 with zero sorry, zero custom axioms, and zero external hypotheses in its final pipeline theorem, LambdaSat-Lean provides a domain-agnostic e-graph parameterized by typeclasses that can be instantiated for circuits, tensors, SQL queries, or any first-order rewriting system. We describe how the project evolved through nine phases — from a foundation with an isolated sorry to a fully self-contained soundness proof — and how each phase responds to open challenges identified by four independent lines of academic research: isolated Union-Find verification (Charguéraud, Stevens), semantic foundations of e-graphs (Suciu, Zakhour), integration with proof assistants (Rossel/lean-egg), and unverified optimal extraction (Yang/TENSAT). The result is 248 machine-checked theorems in 8,956 lines of code, with a three-path soundness chain culminating in `full_pipeline_soundness`: for any expression, any set of sound rewrite rules, and any initial e-graph satisfying structural invariants, the optimized expression evaluates identically to the original.
geometry: margin=2.5cm
documentclass: article
fontsize: 11pt
numbersections: true
colorlinks: true
linkcolor: RoyalBlue
urlcolor: RoyalBlue
header-includes: |
  \usepackage{booktabs}
  \usepackage{enumitem}
  \setlist{nosep}
---

# The problem: can we trust optimizers?

When a program is compiled, it passes through a chain of transformations that simplify and optimize it. In safety-critical domains — zero-knowledge cryptography, compiler backends, hardware synthesis — every transformation must preserve meaning exactly. A single incorrect optimization can produce a circuit that accepts false proofs, a compiled program that computes wrong results, or a hardware design that silently corrupts data.

The dominant technique for optimizing term-rewriting systems is **Equality Saturation**. Instead of applying rewrite rules one at a time and hoping for the right order, it applies *all* rules simultaneously on a data structure called an **E-Graph** (equivalence graph) that compactly represents all equivalent versions of an expression. At the end, the cheapest version is extracted.

The problem is that **no existing implementation of this technique is formally verified**. Neither `egg` (Rust), nor `egglog` (Rust), nor `lean-egg` (Lean + Rust via FFI) carry machine-checked proofs that the engine preserves semantics. They rely on the code being well-written, but no one has *proven* it.

LambdaSat-Lean is the first project to provide that proof — completely, within a single proof assistant, with no external dependencies.

# What LambdaSat-Lean is

LambdaSat-Lean is a **generic, formally verified equality saturation engine** implemented in Lean 4. It is:

- **Typeclass-parameterized**: the engine is agnostic to the domain. Users provide `NodeOps`, `NodeSemantics`, and `Extractable` instances for their operator type, and the entire verification stack transfers.
- **Self-contained**: no Mathlib dependency, no FFI, no external runtime. The only trusted component is the Lean 4 kernel.
- **Complete**: every stage of the pipeline — insertion, merging, rebuilding, pattern matching, saturation, extraction (greedy and ILP) — is implemented and verified within the same codebase.

The key metrics at v1.2.0:

| Metric | Value |
|--------|-------|
| Lines of code | 8,956 |
| Verified theorems | 248 |
| Source files | 21 |
| `sorry` count | **0** |
| Custom axioms | **0** |
| External hypotheses in pipeline theorem | **0** |
| Integration tests | 23/23 PASS |
| Lean version | 4.26.0 |
| Mathlib dependency | None |

# The academic landscape and its open challenges

The academic community has been working, from different angles, to bring mathematical rigor to equality saturation and its underlying data structures. But each group encounters barriers of implementation or proof complexity. We classify the sources into four groups.

## Group A: Union-Find verification (the foundation)

**Charguéraud & Pottier (2019, Journal of Automated Reasoning, Coq)** and **Stevens & Ghidini (2025, Isabelle/HOL)** focus on verifying **Union-Find**, the data structure at the base of every e-graph. Union-Find maintains disjoint sets and efficiently answers "do these two elements belong to the same group?"

- **Charguéraud** uses separation logic with time credits to prove not just correctness but amortized $O(\alpha(n))$ complexity (the inverse Ackermann). The proof is extremely complex.
- **Stevens** focuses on making the structure capable of *producing proofs* (an operation called `explain`), and uses refinement from an abstract specification toward imperative code.

**The problem**: both verifications are **isolated**. They prove that Union-Find works correctly *in itself*, but do not connect it with a larger system. It is like verifying that a bolt is perfect without proving that the bridge using it does not collapse.

## Group B: Semantic foundations of e-graphs

**Suciu, Wang & Zhang (2025, ICDT)** and **Zakhour, Weisenburger, Cesario & Salvaneschi (2025, POPL)** seek to define *what an e-graph is* mathematically, independently of how it is implemented.

- **Suciu** models e-graphs as **tree automata** and connects equality saturation with the *chase* procedure from database theory. He proves termination conditions using fixed-point theory.
- **Zakhour** formalizes the **RSTC closure** (Reflexive-Symmetric-Transitive-Congruent): the equivalence relation that an e-graph computes is the smallest congruence containing all applied rewrite rules.

**The problem**: both are **paper proofs** on abstract mathematical objects. They establish elegant theoretical properties (termination, confluence, completeness) but without mechanical verification. Zakhour, for example, formalizes the theory on paper but implements on `egg` (Rust, not verified). The gap between theory and implementation remains open.

## Group C: Integration with proof assistants

**Rossel (2024, Master's Thesis, ETH Zurich)** and **Rossel, Schneider, Koehler, Steuwer & Goens (2026, POPL)** developed **lean-egg**, a tactic that integrates equality saturation in the Lean 4 proof assistant.

Their approach: externalize saturation to the `egg` engine (Rust) via FFI and then *reconstruct* the proof in Lean from the "explanations" that `egg` generates.

**The problem**: Rossel explicitly acknowledges that implementing a verified e-graph within Lean is "*too difficult or slow*". His evaluation (thesis, §5.3; POPL 2026, §7) enumerates three obstacles:

1. The complexity of verifying Union-Find with path compression
2. The difficulty of maintaining congruence invariants through mutable operations
3. Performance concerns for a purely functional implementation

This forces a design where the Rust runtime is part of the **trusted computing base** (TCB): if `egg` has a bug, lean-egg inherits that bug.

## Group D: Optimal extraction without verification

**Yang, Phothilimthana, Wang, Willsey, Roy & Pienaar (2021, MLSys — TENSAT)** introduced **ILP extraction** (Integer Linear Programming) for e-graphs: instead of a greedy algorithm (which can miss global optima), they formulate the problem as an integer linear program and solve it with an external solver.

**The problem**: the ILP formulation correctly encodes the extraction problem (by construction of the constraints), but the **extracted expression is never verified** against the original. Correctness depends on trusting the solver and its decoding. If the solver has a numerical bug or the decoding is incorrect, no one detects it.

# How LambdaSat-Lean responds to each group

## Response to Group A (Charguéraud, Stevens): integration matters

Charguéraud and Stevens verified Union-Find in isolation. We verified it **integrated within a larger system**.

In LambdaSat-Lean, `UnionFind.lean` (1,235 lines, 44 theorems) contains a Union-Find with path compression. But the key difference is that its invariants do not stay there: they *propagate* through five layers of abstraction until reaching the final pipeline soundness theorem.

The formal dependency chain is:

```
find_preserves_roots (UnionFind)
  → merge_consistent (Core + SemanticSpec)
    → rebuildStepBody_preserves_triple (SemanticSpec)
      → saturateF_preserves_consistent (SaturationSpec)
        → full_pipeline_soundness (TranslationValidation)
```

The bridge theorem connecting the Union-Find layer with denotational semantics is `consistent_root_eq`: under the `ConsistentValuation` invariant, the denotational value of any ID equals the value of its root in the Union-Find. This is what Charguéraud and Stevens do not have: a theorem that connects "the Union-Find is correct" with "the optimized program computes the same as the original."

## Response to Group B (Suciu, Zakhour): mechanized foundations

Suciu and Zakhour gave us the theory. We turned it into code that the machine can verify.

The bridge is the `ConsistentValuation` invariant, which has two conditions:

1. **UF consistency**: if two IDs have the same root in the Union-Find, they have the same semantic value. This corresponds to Zakhour's RSTC closure.
2. **Node consistency**: every node in every class evaluates to the value of its class. This corresponds to the transitions of Suciu's tree automaton.

| Theoretical concept | Mechanization in LambdaSat-Lean |
|---|---|
| Tree automaton run (Suciu) | `v : EClassId → Val` in `ConsistentValuation` |
| Transition consistency (Suciu) | Condition (2): `evalOp(n, env, v) = v(c)` |
| RSTC closure (Zakhour) | `sound_rule_preserves_consistency` |
| Congruence (Zakhour) | `processClass_merges_semantically_valid` |
| Fixed point (Suciu) | `saturateF` terminates (bounded) preserving CV |
| Extraction correctness | `extractF_correct` / `extractILP_correct` |

Where Suciu speaks theoretically of fixed points, LambdaSat-Lean proves in Lean that its `saturateF` function reaches a bounded state preserving `ConsistentValuation`. Where Zakhour formalizes RSTC closure on paper, our theorem `sound_rule_preserves_consistency` mechanizes it computationally.

## Response to Group C (Rossel/lean-egg): the verified engine is practical

This is perhaps our most direct response. Rossel states that implementing a verified e-graph within Lean is impractical. We did it.

| Rossel's obstacle | How we solved it |
|---|---|
| (a) "Verifying Union-Find with path compression is too difficult" | 1,235 LOC, 44 theorems. Key: fuel-based recursion + `compressPath_preserves_rootD` |
| (b) "Maintaining congruence invariants through mutable operations is too complex" | Four-tier invariant system (`EGraphWF`, `PostMergeInvariant`, `AddExprInv`, `SemanticHashconsInv`) that tracks exactly which properties hold at each phase |
| (c) "Performance of a functional implementation is insufficient" | Functional arrays (`Array.set`, $O(\log n)$ amortized). Sufficient for circuits up to ~2,000 constraints |

The central architectural idea that makes this feasible is **fuel-based recursion**: instead of using well-founded recursion (which in Lean 4 requires proving termination within the definition — extremely difficult when termination depends on runtime invariants), every recursive function takes an explicit `fuel : Nat` parameter, and separate theorems prove that sufficient fuel always exists.

This eliminates the need for **proof reconstruction**. lean-egg must reconstruct Lean proofs from the explanation traces that `egg` generates — a complex and fragile process that must handle binders, type classes, and definitional equality. LambdaSat-Lean never leaves the verified world: the engine *preserves correctness by construction*.

## Response to Group D (Yang/TENSAT): verified ILP extraction

TENSAT formulated the extraction problem as ILP. We added the missing piece: **verification of the result**.

The architecture separates *correctness* from *optimality*:

1. An **ILP solver** (HiGHS external or pure Lean branch-and-bound) finds a solution. This solver is in the TCB only for optimality: it may not find the best solution, but that does not affect correctness.
2. A **certificate checker** (`checkSolution`, decidable, verified) verifies that the solution satisfies the four ILP constraints.
3. A **guided extraction** (`extractILP`, with fuel, verified) reconstructs the expression following the solution.

The theorem `extractILP_correct` guarantees: **any** solution that passes `checkSolution` — whether from HiGHS, from a SAT solver, or even from a lucky guess — produces a semantically correct expression. The solver affects *what* optimal is found, not *whether* the result is correct.

In v1.2.0, we went further: `checkSolution` is formally decomposed into four independently proven checks:

| Check | Theorem | Property |
|---|---|---|
| Root activation | `checkRootActive_sound` | Root class is selected |
| Exactly-one selection | `checkExactlyOne_sound` | Each active class selects exactly one node |
| Child dependencies | `checkChildDeps_sound` | Selected nodes have all children active |
| Acyclicity | `checkAcyclicity_sound` | Selection is acyclic (constructive proof) |

The composition `checkSolution_sound` joins all four via `Bool.and_eq_true_iff`. The acyclicity proof is fully constructive — no `Classical.em`.

# The evolution: from one sorry to zero hypotheses

LambdaSat-Lean did not arrive at its current state in a single step. The journey through nine phases illustrates how formal verification proceeds incrementally, with each phase closing a specific gap.

## Phase 1–4: Foundation (v0.1.0)

The initial release established the core architecture: Union-Find, e-graph operations, specification invariants, e-matching, saturation, extraction (greedy + ILP), parallel wrappers, and translation validation. 181 theorems, zero sorry, zero axioms, 6,241 LOC.

But the soundness chain had a critical assumption: **`PreservesCV`** — users had to prove, for each rewrite rule, that applying it preserves `ConsistentValuation`. This was a significant burden.

## Phase 5: Saturation soundness (v0.2.0)

Introduced `SoundRewriteRule` and `SaturationSpec`, connecting individual rule applications to the full saturation loop. The theorem `full_pipeline_soundness_greedy` was proven — but with one isolated sorry in `rebuildStepBody_preserves_cv`, deep in the rebuild path.

**The sorry**: during rebuild, `processClass` iterates over nodes in a class, erases old hashcons entries, and inserts canonical ones. Proving that this `foldl` preserves `ConsistentValuation` required tracking how the hashcons map changes at each step — but the existing `HashconsClassesAligned` invariant was too strong to preserve through intermediate states.

## Phase 6: Zero sorry (v0.3.0) — SemanticHashconsInv

The key innovation was introducing a *weaker* invariant that is *preservable*:

**`SemanticHashconsInv g env v`** = for every node `nd` and id `id`, if `hashcons[nd] = some id` then `NodeEval nd env v = v(root id)`.

Unlike the original `HashconsClassesAligned` (which required structural alignment between hashcons and class membership), SHI only requires *semantic* consistency. This is preservable through `processClass` because:

- Erasing an old hashcons entry trivially preserves SHI (fewer entries, fewer obligations).
- Inserting the canonical entry preserves SHI because the canonical node evaluates to the class value (by CV).

The triple (CV, PMI, SHI) is self-preserving through `rebuildStepBody`. The sorry was closed.

## Phase 7: Pattern semantics (v1.0.0) — ematchF_sound

With zero sorry, the next gap was the `PreservesCV` assumption. Users had to provide it per rule, which was a significant API burden.

The solution was to give patterns a **denotational semantics**:

```lean
def Pattern.eval (pat : Pattern Op) (env : Nat → Val)
    (v : EClassId → Val) (σ : Substitution) : Option Val
```

A pattern variable `PVar pv` evaluates to `v(σ(pv))`. A pattern node `PNode op subpats` evaluates to `evalOp(op, env, childVals)` where each child is recursively evaluated.

The central theorem:

```lean
theorem ematchF_sound :
  σ ∈ ematchF fuel g pat classId →
  Pattern.eval pat env v σ = some (v (root g.uf classId))
```

If the e-matching engine finds a substitution `σ` for pattern `pat` in class `classId`, then the pattern evaluated under `σ` equals the semantic value of that class. This is proven by structural induction on the pattern with fuel induction.

With `ematchF_sound`, `PreservesCV` can be *derived* from `SoundRewriteRule` — the user no longer needs to provide it.

## Phase 8: Zero external hypotheses (v1.1.0)

Three hypotheses remained in `full_pipeline_soundness_internal`:

1. **`SameShapeSemantics`**: operators with the same shape (modulo children) evaluate identically given identical child values.
2. **`ematchF_substitution_bounded`**: substitutions returned by `ematchF` only contain IDs within the e-graph.
3. **`InstantiateEvalSound`**: `instantiateF` (which adds the RHS pattern of a rule to the e-graph) preserves the triple (CV, PMI, SHI) and produces the correct value.

All three were discharged as internal theorems:

- `sameShapeSemantics_holds` follows from `evalOp_mapChildren` + the definition of `sameShape`.
- `ematchF_substitution_bounded` follows by structural induction: `ematchF` is read-only (does not mutate the graph), and every ID it returns comes from `g.classes` lookups.
- `InstantiateEvalSound_holds` generalizes `instantiateF_preserves_consistency`, adding SHI preservation. The key insight: `instantiateF` only calls `add` (never `merge` directly), so SHI preservation follows from `add_node_consistent`.

The result: `full_pipeline_soundness` with **zero external hypotheses** — only structural assumptions about the initial e-graph state (`ConsistentValuation`, `PostMergeInvariant`, `SemanticHashconsInv`, `HashconsChildrenBounded`).

## Phase 9: ILP certificate verification (v1.2.0)

The final phase added 15 new theorems decomposing `checkSolution` into individually proven properties, certificate evaluation soundness (`evalVar`, `checkConstraint`, `isFeasible`), encoding properties for `encodeEGraph`, and fuel sufficiency for `extractILPAuto`.

The core challenge was reasoning about `HashMap.fold` — a function whose iteration order is unspecified. The solution: instead of proving properties about the fold *process*, prove properties from the fold *result*. If `fold (init := true) (fun acc k v => acc && f k v) = true`, then `∀ (k, v) ∈ map, f k v = true`. This approach was pioneered in `checkExactlyOne_sound` (the GATE node) and replicated in `checkChildDeps_sound` and `checkAcyclicity_sound`.

# The three soundness paths

LambdaSat-Lean maintains three parallel soundness chains, each valid at a different level of assumptions:

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

Path A is available for users who already have `PreservesCV` proofs (backward compatible). Path B eliminates user assumptions but keeps three internal hypotheses. Path C is fully self-contained — the strongest result.

# The four-tier invariant system

A central design decision in LambdaSat-Lean is the use of **four progressively weaker invariants** that track exactly which properties hold at each phase of e-graph mutation:

| Invariant | When it holds | What it guarantees |
|---|---|---|
| `EGraphWF` | Stable state (before/after operations) | Full well-formedness: hashcons, classes, UF consistency |
| `PostMergeInvariant` | After merge, before rebuild | Partial: UF updated, hashcons may be stale |
| `AddExprInv` | During recursive `addExpr` | Partial: new nodes inserted, parent pointers valid |
| `SemanticHashconsInv` | Through rebuild | Semantic hashcons consistency (weaker than HCA, preservable) |

This is more nuanced than a single "well-formed" predicate. During `merge`, we temporarily break hashcons alignment (which `EGraphWF` would reject) but maintain `PostMergeInvariant`. During `rebuild`, we thread `SemanticHashconsInv` through `processClass` iterations. Each invariant is designed to be *exactly* what the next operation needs as a precondition and *exactly* what it can preserve as a postcondition.

# Typeclass architecture and generalizability

LambdaSat-Lean is parameterized over three typeclasses:

```lean
class NodeOps (Op : Type) where
  children : Op → List EClassId
  mapChildren : (EClassId → EClassId) → Op → Op
  replaceChildren : Op → List EClassId → Op
  mapChildren_children : ∀ f op,
    children (mapChildren f op) = (children op).map f

class NodeSemantics (Op : Type) (Val : Type) extends NodeOps Op where
  evalOp : Op → (Nat → Val) → (EClassId → Val) → Val
  evalOp_ext : ...         -- evalOp depends on v only through children
  evalOp_mapChildren : ... -- mapChildren commutes with evalOp

class Extractable (Op : Type) (Expr : Type) extends NodeOps Op where
  reconstruct : Op → List Expr → Option Expr
```

The entire verification stack (248 theorems) transfers to any instantiation. To use LambdaSat-Lean for a new domain, one provides: (1) an inductive operator type, (2) instances of the three typeclasses, and (3) rewrite rules with their soundness proofs.

Potential instantiations:

| Domain | Operator type | Value type | Application |
|---|---|---|---|
| ZK circuits | `CircuitNodeOp` | $\mathbb{Z}/p\mathbb{Z}$ | Verified circuit optimization |
| Tensor graphs | `TensorOp` | `Tensor` | ML compiler optimization |
| Lambda calculus | `LambdaOp` | `Value` | Verified compilation |
| SQL queries | `RelAlgOp` | `Relation` | Query optimization |
| Digital hardware | `GateOp` | `BitVec` | RTL optimization |

# Trusted Computing Base

The soundness guarantee depends only on:

**Verified** (inside TCB — correctness follows from Lean kernel type-checking):

- UnionFind: find, merge, path compression (44 theorems)
- Core: add, merge, rebuild, canonicalize (79 theorems)
- SemanticSpec: ConsistentValuation, SemanticHashconsInv, rebuild preservation (49 theorems)
- EMatchSpec: ematchF_sound, InstantiateEvalSound_holds (25 theorems)
- SaturationSpec: saturateF_preserves_consistent_internal (13 theorems)
- ExtractSpec: extractF_correct (3 theorems)
- ILPSpec: ilp_extraction_soundness, checkSolution_sound (12 theorems)
- TranslationValidation: full_pipeline_soundness (8 theorems)

**Assumed correct** (outside TCB):

- Lean 4 kernel (v4.26.0) — type-checks all proofs
- Lean 4 compiler — generates runtime code from verified definitions
- OS / hardware — executes compiled code
- Typeclass instances — users must correctly implement `NodeOps`, `NodeSemantics`, `Extractable`
- ILP solver (HiGHS / branch-and-bound) — untrusted oracle, output validated by `checkSolution`

**Unverified wrappers** (correct by construction, no formal proof):

- `ParallelMatch.lean` — `IO.asTask` wrapper around verified sequential `ematchF`
- `ParallelSaturate.lean` — `IO.asTask` wrapper around verified sequential `saturateF`

The critical point: a bug in the engine is *impossible* without a `sorry` — and there are zero. A bug in a typeclass instance would produce an unsound *domain instantiation*, but the engine itself remains correct. A bug in the ILP solver would produce a suboptimal extraction, but `checkSolution` would reject an incorrect one.

# Comparison with egg and lean-egg

LambdaSat-Lean and `egg` do not compete — they **complement** each other. They operate at different points of the design space, solve different problems, and have opposite strengths.

## What each project is

**egg** (Willsey et al., POPL 2021, Rust) is a high-performance e-graph engine, imperative, optimized for scale (millions of nodes, SMT workloads). It has no formal verification. It exposes an API of *explanations* — traces that say "I applied rule X to node Y" — so that external tools can reconstruct why two terms are equivalent.

**lean-egg** (Rossel et al., POPL 2026) is a **tactic for Lean 4** for equational reasoning. When a user writes a proof and needs to show that `a + b + c = c + b + a`, lean-egg applies rewrite rules automatically via e-graphs to find the equivalence chain. It uses `egg` as a backend via FFI and reconstructs Lean proofs from the explanations.

**LambdaSat-Lean** is a **verified optimization engine**. It takes an expression, explores all equivalent forms via e-graphs, and extracts the cheapest one. It is not a proof tactic — it is a tool that transforms programs with total formal guarantee.

## The fundamental architectural difference

lean-egg leaves Lean, delegates the heavy work to Rust, and reconstructs the proof on return. LambdaSat-Lean never leaves Lean.

lean-egg has three phases:

1. The tactic encodes the Lean goal as first-order terms and sends them to `egg` (Rust) via FFI.
2. `egg` saturates the e-graph and produces explanations.
3. Lean reconstructs a formal proof from those explanations.

LambdaSat-Lean operates in a single verified phase:

1. The expression is inserted into the verified e-graph.
2. Saturation with verified rules (each rule carries its soundness proof).
3. Extraction (greedy or ILP with verified certificate).
4. The theorem `full_pipeline_soundness` guarantees correctness *by construction*.

## The five concrete trade-offs

### 1. Trusted computing base (TCB)

lean-egg trusts:

- The `egg` runtime (Rust, ~5,000 LOC not verified)
- The FFI binding between Lean and Rust
- That `egg`'s explanations are correct
- That the proof reconstruction interprets those explanations correctly

If `egg` has a bug in merge, congruence closure, or explanation generation, lean-egg inherits that bug. Proof reconstruction is a safety net: if reconstruction fails, the tactic fails. But it cannot detect bugs that produce *plausible but incorrect* explanations.

LambdaSat-Lean trusts only the Lean 4 kernel. No external code. A bug in the engine is impossible without a `sorry` — and there are zero.

### 2. What each can handle

lean-egg handles general Lean expressions:

- Binders (`fun x => x + 1`)
- Type classes (`@HAdd.hAdd Nat Nat Nat instHAdd a b`)
- Definitional equality
- Universes, dependent types

This is powerful but complex. Rossel had to solve how to encode Lean's rich semantics into `egg`'s first-order terms, and how to reconstruct proofs that respect all these subtleties.

LambdaSat-Lean handles only first-order terms:

- Operators with fixed arity (`add(a, b)`, `mul(a, b)`, `const(5)`)
- No binders, no type classes, no dependent types

This is a real limitation: it cannot be used as a general Lean tactic. But for first-order domains (circuits, tensors, SQL, hardware), it is exactly what is needed, and the verification is dramatically simpler.

### 3. How they guarantee soundness

lean-egg: *conditional guarantee*. If proof reconstruction succeeds, the equivalence is correct. If it fails (due to a bug in `egg`, or limitations of the reconstruction), the tactic reports an error. The user knows that it either works or fails — it never produces an incorrect proof. But the reconstruction effort is significant and there are corner cases.

LambdaSat-Lean: *unconditional guarantee*. The type of `full_pipeline_soundness` says that for *every* expression and *every* environment, the optimized result evaluates identically to the original. This holds by construction — there is no reconstruction that might fail. But it only holds for domains within the first-order typeclass interface.

### 4. Performance

lean-egg benefits from Rust's native performance. `egg` is highly optimized with imperative arrays, union-by-rank, and efficient hashing. It can handle e-graphs with millions of nodes.

LambdaSat-Lean uses Lean's functional arrays (`Array.set`, which is $O(\log n)$ amortized vs $O(1)$ imperative). It is sufficient for circuits (up to ~2,000 constraints with Pedersen), but would not scale to SMT solving workloads.

### 5. Purpose

lean-egg is a *tactic*: its user is someone writing a proof in Lean who wants to automate equational rewriting steps.

LambdaSat-Lean is an *optimizer*: its user is someone who wants to transform a program (circuit, query, etc.) to a cheaper equivalent version, with formal guarantee that the transformation is correct.

## Full comparison table

| Aspect | egg / lean-egg | LambdaSat-Lean |
|---|---|---|
| Language | Rust (+ Lean FFI) | Pure Lean 4 |
| Trusted computing base | egg runtime + FFI | Lean 4 kernel only |
| Equivalence proof | Reconstructed from explanations | By construction |
| Binders / Higher-order | Yes (via encoding) | No (first-order) |
| Performance at scale | Rust native (fast) | Lean native (slower) |
| Soundness guarantee | Conditional (if reconstruction OK) | Unconditional (by typing) |
| Domain scope | General Lean expressions | Any first-order domain |
| Primary purpose | Proof tactic | Optimization engine |
| ILP extraction | No | Yes (certificate-verified) |
| Parallel saturation | No | Yes (`IO.asTask`) |
| `sorry` in engine | N/A (Rust, not applicable) | 0 |
| Theorems | N/A | 248 |

## When to use each

| Scenario | Best option |
|---|---|
| Lean tactic for general rewriting (binders, HoL) | lean-egg |
| ZK circuit optimization (safety-critical) | LambdaSat-Lean |
| SMT solving at massive scale | egg |
| Verified compiler (CompCert-style) | LambdaSat-Lean |
| Rapid prototyping of optimizations | egg |
| Academic publication with verified artifact | LambdaSat-Lean |
| Hardware RTL optimization | LambdaSat-Lean |

## Toward a future synthesis

The most interesting integration scenario: lean-egg could replace its Rust backend (`egg`) with LambdaSat-Lean, eliminating the FFI and the Rust TCB. The result would be a Lean tactic with:

- Zero external TCB (no more FFI, no more Rust)
- Formally guaranteed engine correctness
- lean-egg's tactic interface (usability)
- LambdaSat-Lean's verification (confidence)

The obstacle: LambdaSat-Lean would need to be extended to handle the higher-order representation that lean-egg currently delegates to `egg`. This is non-trivial future work, but the typeclass architecture makes it possible without breaking existing theorems.

# Version history

| Version | Highlights |
|---------|-----------|
| v0.1.0 | Full typeclass-parameterized e-graph: 4 phases, 17 src files, 6,241 LOC, 181 theorems, 0 sorry, 0 axioms |
| v0.2.0 | Saturation soundness: SoundRewriteRule, SaturationSpec, PreservesCV, `full_pipeline_soundness_greedy`. 1 sorry (isolated in rebuild) |
| v0.3.0 | **Zero sorry**: SemanticHashconsInv closes rebuild gap. 198 theorems |
| v1.0.0 | **PreservesCV eliminated**: Pattern.eval + ematchF_sound + `full_pipeline_soundness_internal`. 218 theorems, 0 user assumptions |
| v1.1.0 | **Zero external hypotheses**: InstantiateEvalSound_holds + ematchF_substitution_bounded + `full_pipeline_soundness`. 233 theorems |
| v1.2.0 | **ILP certificate verification**: checkSolution soundness (4 checks), encoding properties, fuel monotonicity. 248 theorems |

# Conclusion

The academic community identified four open problems: isolated Union-Find verification (Charguéraud, Stevens), semantic foundations without mechanization (Suciu, Zakhour), the supposed impracticality of a verified engine (Rossel), and optimal extraction without verification (Yang/TENSAT).

LambdaSat-Lean resolves all four simultaneously: a complete equality saturation engine, generic, formally verified in Lean 4, with integrated Union-Find, mechanized semantics, ILP extraction with verified certificate, and zero `sorry`.

The evolution from v0.1.0 to v1.2.0 demonstrates that formal verification of complex systems is not only possible but can proceed incrementally: each phase closes a specific gap (a sorry, a user assumption, an unverified component) while maintaining full backward compatibility. The result is 248 machine-checked theorems that collectively state: **for any expression, any set of sound rewrite rules, and any initial e-graph satisfying structural invariants, the optimized expression evaluates identically to the original**.

This is not an academic exercise. Instantiated for R1CS circuits via VR1CS-Lean, LambdaSat-Lean matches the production `circom -O2` optimizer on 9 of 10 real circuits, while providing a formal guarantee that no other circuit optimizer offers — that an unsound transformation is *mathematically impossible*.

\vspace{1em}
\noindent\textbf{Artifacts.}

\noindent LambdaSat-Lean: \url{https://github.com/Manuel0921/lambdasat-lean}

\noindent VR1CS-Lean: \url{https://github.com/Manuel0921/vr1cs-lean}

\noindent Lean 4.26.0. No external dependencies.
