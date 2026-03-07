/-
  LambdaSat — Parallel Pattern Matching Infrastructure
  Fase 4 Subfase 1: Parallel matching via Lean 4 Task API

  Key design: read-only e-graph during matching.
  - LambdaSat's `ematch` already uses `root` (pure, no path compression)
  - Collect all matches in parallel, then apply sequentially
  - Embarrassingly parallel: each class's ematch is independent
-/
import LambdaSat.EMatch

namespace LambdaSat

open UnionFind

-- ══════════════════════════════════════════════════════════════════
-- Match Result Types
-- ══════════════════════════════════════════════════════════════════

/-- A match result for a specific rule at a specific class. -/
structure RuleMatch where
  classId : EClassId
  subst   : Substitution
  deriving Inhabited

variable {Op : Type} [NodeOps Op] [BEq Op] [Hashable Op]

/-- Collect matches from ematch into an array of RuleMatch. -/
private def collectMatches (g : EGraph Op) (pattern : Pattern Op)
    (classId : EClassId) : Array RuleMatch :=
  let results := ematch g pattern classId
  results.foldl (fun acc subst =>
    acc.push { classId := classId, subst := subst }) #[]

/-- Match a single rule against a chunk of class IDs (pure, read-only). -/
def matchRuleChunk (g : EGraph Op) (rule : RewriteRule Op) (classIds : Array EClassId) :
    Array RuleMatch :=
  classIds.foldl (init := #[]) fun acc classId =>
    acc ++ collectMatches g rule.lhs classId

-- ══════════════════════════════════════════════════════════════════
-- Chunking Utilities
-- ══════════════════════════════════════════════════════════════════

/-- Split an array into `n` roughly equal chunks. -/
def splitIntoChunks {α : Type} (arr : Array α) (n : Nat) : Array (Array α) :=
  if n == 0 || arr.isEmpty then #[arr]
  else
    let chunkSize := max ((arr.size + n - 1) / n) 1
    Id.run do
      let mut result : Array (Array α) := #[]
      let mut start : Nat := 0
      for _ in [:n] do
        if start >= arr.size then break
        let endIdx := min (start + chunkSize) arr.size
        result := result.push (arr.extract start endIdx)
        start := endIdx
      return result

-- ══════════════════════════════════════════════════════════════════
-- Parallel Matching
-- ══════════════════════════════════════════════════════════════════

/-- Search for all instances of a pattern across all classes in parallel.
    Uses IO.asTask to run matching on chunks concurrently.
    The e-graph is read-only during matching (uses `root`, not `find`). -/
def searchPatternParallel (g : EGraph Op) (pattern : Pattern Op) (numTasks : Nat := 4) :
    IO (Array RuleMatch) := do
  let allClassIds := g.classes.fold (fun acc classId _ => acc.push classId)
    (#[] : Array EClassId)
  if allClassIds.size ≤ 1 || numTasks ≤ 1 then
    -- Sequential fallback for tiny graphs
    return allClassIds.foldl (init := #[]) fun acc classId =>
      acc ++ collectMatches g pattern classId
  else
    let chunks := splitIntoChunks allClassIds numTasks
    let tasks ← chunks.mapM fun chunk => do
      IO.asTask (prio := .dedicated) do
        return chunk.foldl (init := #[]) fun acc classId =>
          acc ++ collectMatches g pattern classId
    let mut allResults : Array RuleMatch := #[]
    for task in tasks do
      let result ← IO.ofExcept (← IO.wait task)
      allResults := allResults ++ result
    return allResults

/-- Match all rules against the e-graph in parallel.
    Each rule is matched independently via IO.asTask. -/
def matchAllRulesParallel (g : EGraph Op) (rules : List (RewriteRule Op))
    (numTasks : Nat := 4) :
    IO (Array (RewriteRule Op × Array RuleMatch)) := do
  let ruleArray := rules.toArray
  if ruleArray.size ≤ 1 || numTasks ≤ 1 then
    -- Sequential fallback
    let mut results : Array (RewriteRule Op × Array RuleMatch) := #[]
    for rule in ruleArray do
      let allClassIds := g.classes.fold (fun acc classId _ => acc.push classId)
        (#[] : Array EClassId)
      let ruleMatches := matchRuleChunk g rule allClassIds
      results := results.push (rule, ruleMatches)
    return results
  else
    let tasks ← ruleArray.mapM fun rule => do
      IO.asTask (prio := .dedicated) do
        let allClassIds := g.classes.fold (fun acc classId _ => acc.push classId)
          (#[] : Array EClassId)
        let ruleMatches := matchRuleChunk g rule allClassIds
        return (rule, ruleMatches)
    let mut results : Array (RewriteRule Op × Array RuleMatch) := #[]
    for task in tasks do
      let result ← IO.ofExcept (← IO.wait task)
      results := results.push result
    return results

-- ══════════════════════════════════════════════════════════════════
-- Sequential Apply (after parallel match)
-- ══════════════════════════════════════════════════════════════════

/-- Apply collected match results sequentially (merge is not thread-safe).
    Side conditions are re-checked at apply time since the e-graph may
    have changed between matching and applying. -/
def applyMatchResults (g : EGraph Op) (rule : RewriteRule Op)
    (ruleMatches : Array RuleMatch) : EGraph Op :=
  ruleMatches.foldl (init := g) fun acc m =>
    let condMet := match rule.sideCondCheck with
      | some check => check acc m.subst
      | none => true
    if !condMet then acc
    else
      match instantiate acc rule.rhs m.subst with
      | none => acc
      | some (rhsId, acc') =>
        let canonLhs := acc'.unionFind.root m.classId
        let canonRhs := acc'.unionFind.root rhsId
        if canonLhs == canonRhs then acc'
        else acc'.merge m.classId rhsId

/-- Apply all rule match results sequentially, then rebuild once. -/
def applyAllMatchResultsAndRebuild (g : EGraph Op)
    (allRuleMatches : Array (RewriteRule Op × Array RuleMatch)) : EGraph Op :=
  let g' := allRuleMatches.foldl (init := g) fun acc (rule, ruleMatches) =>
    applyMatchResults acc rule ruleMatches
  g'.rebuild

end LambdaSat
