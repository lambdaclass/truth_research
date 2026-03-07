/-
  LambdaSat-Lean — Verified Equality Saturation Engine
  A domain-agnostic, typeclass-parameterized e-graph engine in Lean 4.
  Generalized from VR1CS-Lean v1.3.0.

  Modules:
  - UnionFind: Verified union-find with path compression
  - Core: E-graph core types and operations
  - CoreSpec: E-graph specification and invariants
  - EMatch: Pattern matching (e-matching)
  - Saturate: Equality saturation loop
  - SemanticSpec: Semantic specification (ConsistentValuation, BestNodeInv)
  - Extractable: Extractable typeclass + generic extractF
  - ExtractSpec: Extraction correctness verification
  - ILP: ILP data model for optimal extraction
  - ILPEncode: E-graph → ILP encoding (TENSAT formulation)
  - ILPSolver: HiGHS external + pure Lean B&B solvers
  - ILPCheck: ILP certificate checking + ILP-guided extraction
  - ILPSpec: ILP extraction formal verification
  - ParallelMatch: Parallel pattern matching infrastructure
  - ParallelSaturate: Parallel saturation loop
  - Optimize: Optimization pipeline (greedy + ILP)
  - TranslationValidation: End-to-end soundness theorems
-/
import LambdaSat.UnionFind
import LambdaSat.Core
import LambdaSat.EMatch
import LambdaSat.Saturate
import LambdaSat.CoreSpec
import LambdaSat.SemanticSpec
import LambdaSat.Extractable
import LambdaSat.ExtractSpec
import LambdaSat.ILP
import LambdaSat.ILPEncode
import LambdaSat.ILPSolver
import LambdaSat.ILPCheck
import LambdaSat.ILPSpec
import LambdaSat.ParallelMatch
import LambdaSat.ParallelSaturate
import LambdaSat.Optimize
import LambdaSat.SoundRule
import LambdaSat.SaturationSpec
import LambdaSat.AddNodeTriple
import LambdaSat.EMatchSpec
import LambdaSat.TranslationValidation
