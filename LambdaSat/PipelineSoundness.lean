/-
  LambdaSat — Verified Pipeline Soundness
  Fase 12: API-Specification Bridge (v1.5.0)

  Creates the "last mile" connection between verified internals and the public API.
  The public API functions (optimizeExpr, saturate) are `partial def` and cannot
  be reasoned about in Lean 4. This module provides verified pipeline functions
  (optimizeF, optimizeWithStrategyF) that compose already-verified spec functions,
  with formal correctness proofs.

  Key results:
  - `optimizeF`: verified greedy pipeline (saturateF + computeCostsF + extractAuto)
  - `optimizeWithStrategyF`: verified strategy-parameterized pipeline
  - `optimizeF_soundness`: end-to-end correctness for greedy extraction
  - `optimizeWithStrategyF_soundness`: end-to-end correctness for any strategy

  Pattern: Three-Tier Bridge (cf. Extraction.lean v1.3.0, L-337, L-393)
-/
import LambdaSat.Extraction
import LambdaSat.SaturationSpec
import LambdaSat.EMatchSpec
import LambdaSat.TranslationValidation

namespace LambdaSat

open UnionFind ILP

variable {Op : Type} {Val : Type} {Expr : Type}
  [NodeOps Op] [BEq Op] [Hashable Op]
  [LawfulBEq Op] [LawfulHashable Op]
  [DecidableEq Op] [Repr Op] [Inhabited Op]
  [NodeSemantics Op Val]
  [Extractable Op Expr] [EvalExpr Expr Val]

set_option linter.unusedSectionVars false

-- ══════════════════════════════════════════════════════════════════
-- Section 1: Verified Pipeline Functions
-- ══════════════════════════════════════════════════════════════════

/-- Verified greedy optimization pipeline.
    Composes `saturateF` + `computeCostsF` + `extractAuto` — all total, verified functions.

    This is the verified counterpart of `optimizeExpr` (Optimize.lean).
    `optimizeExpr` uses `partial def saturate` (with timeouts and stats);
    `optimizeF` uses `def saturateF` (total, fuel-based, formally verified).

    Parameters:
    - `fuel`: fuel for ematch/instantiate within each saturation step
    - `maxIter`: maximum saturation iterations
    - `rebuildFuel`: fuel for rebuild within each saturation step
    - `costFuel`: iterations for cost convergence -/
def optimizeF (fuel maxIter rebuildFuel : Nat)
    (g : EGraph Op) (rules : List (RewriteRule Op))
    (costFn : ENode Op → Nat) (costFuel : Nat)
    (rootId : EClassId) : Option Expr :=
  let g_sat := saturateF fuel maxIter rebuildFuel g rules
  let g_cost := computeCostsF g_sat costFn costFuel
  extractAuto g_cost rootId

/-- Verified strategy-parameterized optimization pipeline.
    Like `optimizeF` but dispatches extraction via `ExtractionStrategy`
    (greedy or ILP-certificate), following the `extract_correct` pattern. -/
def optimizeWithStrategyF (fuel maxIter rebuildFuel : Nat)
    (g : EGraph Op) (rules : List (RewriteRule Op))
    (costFn : ENode Op → Nat) (costFuel : Nat)
    (rootId : EClassId) (strategy : ExtractionStrategy Op) : Option Expr :=
  let g_sat := saturateF fuel maxIter rebuildFuel g rules
  let g_cost := computeCostsF g_sat costFn costFuel
  extract g_cost rootId strategy

-- ══════════════════════════════════════════════════════════════════
-- Section 2: Soundness Theorems
-- ══════════════════════════════════════════════════════════════════

/-- **Greedy pipeline soundness.** If `optimizeF` returns `some expr`, then
    `expr` evaluates to the semantic value of the root class in the saturated graph.

    Composes: `full_pipeline_soundness` + definitional unfolding of `optimizeF`/`extractAuto`.
    Proof body: 2 lines (unfold + exact). -/
theorem optimizeF_soundness [Inhabited Val] (g : EGraph Op)
    (rules : List (PatternSoundRule Op Val))
    (costFn : ENode Op → Nat) (costFuel fuel maxIter rebuildFuel : Nat)
    (env : Nat → Val) (v : EClassId → Val)
    (hcv : ConsistentValuation g env v)
    (hpmi : PostMergeInvariant g) (hshi : SemanticHashconsInv g env v)
    (hhcb : HashconsChildrenBounded g)
    (rootId : EClassId) (expr : Expr)
    (hwf_sat : WellFormed (saturateF fuel maxIter rebuildFuel g
      (rules.map (·.rule))).unionFind)
    (hbni_sat : BestNodeInv (saturateF fuel maxIter rebuildFuel g
      (rules.map (·.rule))).classes)
    (hsound : ExtractableSound Op Expr Val)
    (hopt : optimizeF fuel maxIter rebuildFuel g (rules.map (·.rule))
      costFn costFuel rootId = some expr) :
    ∃ (v_sat : EClassId → Val), EvalExpr.evalExpr expr env =
      v_sat (root (saturateF fuel maxIter rebuildFuel g
        (rules.map (·.rule))).unionFind rootId) := by
  unfold optimizeF extractAuto at hopt
  exact full_pipeline_soundness g rules costFn costFuel fuel maxIter rebuildFuel
    env v hcv hpmi hshi hhcb rootId _ expr hwf_sat hbni_sat hsound hopt

/-- **Strategy-parameterized pipeline soundness.** If `optimizeWithStrategyF`
    returns `some expr`, then `expr` evaluates to the semantic value of the root class.

    Works for both greedy and ILP-certificate extraction strategies.
    Composes: `saturateF_preserves_consistent_internal` + `computeCostsF` preservation
    + `extract_correct`. -/
theorem optimizeWithStrategyF_soundness [Inhabited Val] (g : EGraph Op)
    (rules : List (PatternSoundRule Op Val))
    (costFn : ENode Op → Nat) (costFuel fuel maxIter rebuildFuel : Nat)
    (env : Nat → Val) (v : EClassId → Val)
    (hcv : ConsistentValuation g env v)
    (hpmi : PostMergeInvariant g) (hshi : SemanticHashconsInv g env v)
    (hhcb : HashconsChildrenBounded g)
    (rootId : EClassId) (strategy : ExtractionStrategy Op)
    (hwf_sat : WellFormed (saturateF fuel maxIter rebuildFuel g
      (rules.map (·.rule))).unionFind)
    (hvalid_sat : StrategyValid (computeCostsF (saturateF fuel maxIter rebuildFuel g
      (rules.map (·.rule))) costFn costFuel) rootId strategy)
    (hsound : ExtractableSound Op Expr Val)
    (expr : Expr)
    (hopt : optimizeWithStrategyF fuel maxIter rebuildFuel g (rules.map (·.rule))
      costFn costFuel rootId strategy = some expr) :
    ∃ (v_sat : EClassId → Val), EvalExpr.evalExpr expr env =
      v_sat (root (saturateF fuel maxIter rebuildFuel g
        (rules.map (·.rule))).unionFind rootId) := by
  unfold optimizeWithStrategyF at hopt
  -- Step 1: Get consistent valuation for the saturated graph
  have hematch_bnd : ∀ (g' : EGraph Op) (rule : PatternSoundRule Op Val),
      rule ∈ rules → PostMergeInvariant g' →
      ∀ (classId : EClassId), classId < g'.unionFind.parent.size →
      ∀ σ ∈ ematchF fuel g' rule.rule.lhs classId,
      ∀ pv id, σ.get? pv = some id → id < g'.unionFind.parent.size :=
    fun g' _rule _hrule hpmi' classId hclass σ hmem pv id hσ =>
      ematchF_substitution_bounded g' hpmi' fuel _rule.rule.lhs classId ∅ hclass
        (fun pv' id' h => absurd h (by rw [Std.HashMap.get?_eq_getElem?]; simp))
        σ hmem pv id hσ
  obtain ⟨v_sat, hcv_sat⟩ := saturateF_preserves_consistent_internal fuel maxIter
    rebuildFuel g rules env v hcv hpmi hshi hhcb sameShapeSemantics_holds
    (InstantiateEvalSound_holds env) hematch_bnd
  -- Step 2: Cost computation preserves consistency and well-formedness
  have hcv_cost := computeCostsF_preserves_consistency
    (saturateF fuel maxIter rebuildFuel g (rules.map (·.rule))) costFn costFuel
    env v_sat hcv_sat
  have hwf_cost : WellFormed (computeCostsF (saturateF fuel maxIter rebuildFuel g
      (rules.map (·.rule))) costFn costFuel).unionFind := by
    rw [computeCostsF_preserves_uf]; exact hwf_sat
  -- Step 3: Extract from cost graph is correct
  have hresult := extract_correct
    (computeCostsF (saturateF fuel maxIter rebuildFuel g (rules.map (·.rule)))
      costFn costFuel)
    env v_sat hcv_cost hwf_cost hsound rootId strategy hvalid_sat expr hopt
  -- Step 4: Root is preserved through cost computation
  have hroot : root (computeCostsF (saturateF fuel maxIter rebuildFuel g
      (rules.map (·.rule))) costFn costFuel).unionFind rootId =
    root (saturateF fuel maxIter rebuildFuel g
      (rules.map (·.rule))).unionFind rootId := by
    simp [computeCostsF_preserves_uf]
  rw [hroot] at hresult
  exact ⟨v_sat, hresult⟩

-- ══════════════════════════════════════════════════════════════════
-- Section 3: Hypothesis Discharge (Fase 13, N13.3)
-- ══════════════════════════════════════════════════════════════════

/-- Helper: PatternSoundRules imply PreservesCV for each rewrite rule.
    Factors the h_rules construction from saturateF_preserves_consistent_internal. -/
private theorem patternSoundRules_preserveCV [Inhabited Val] (fuel : Nat) (env : Nat → Val)
    (rules : List (PatternSoundRule Op Val)) :
    ∀ rule ∈ rules.map (·.rule), PreservesCV env (applyRuleF fuel · rule) := by
  have hematch_bnd : ∀ (g' : EGraph Op) (rule : PatternSoundRule Op Val),
      rule ∈ rules → PostMergeInvariant g' →
      ∀ (classId : EClassId), classId < g'.unionFind.parent.size →
      ∀ σ ∈ ematchF fuel g' rule.rule.lhs classId,
      ∀ pv id, σ.get? pv = some id → id < g'.unionFind.parent.size :=
    fun g' _rule _hrule hpmi' classId hclass σ hmem pv id hσ =>
      ematchF_substitution_bounded g' hpmi' fuel _rule.rule.lhs classId ∅ hclass
        (fun pv' id' h => absurd h (by rw [Std.HashMap.get?_eq_getElem?]; simp))
        σ hmem pv id hσ
  intro rule hrule
  obtain ⟨psrule, hps, hrw⟩ := List.mem_map.mp hrule
  rw [← hrw]
  intro g' v' hcv' hpmi' hshi' hhcb'
  simp only [applyRuleF]
  suffices h : ∀ (l : List EClassId) (acc : EGraph Op) (v_acc : EClassId → Val),
    (∀ cid ∈ l, cid < g'.unionFind.parent.size) →
    ConsistentValuation acc env v_acc → PostMergeInvariant acc →
    SemanticHashconsInv acc env v_acc → HashconsChildrenBounded acc →
    g'.unionFind.parent.size ≤ acc.unionFind.parent.size →
    ∃ v'', ConsistentValuation (l.foldl (fun acc classId =>
      applyRuleAtF fuel acc psrule.rule classId) acc) env v'' ∧
      PostMergeInvariant (l.foldl (fun acc classId =>
        applyRuleAtF fuel acc psrule.rule classId) acc) ∧
      SemanticHashconsInv (l.foldl (fun acc classId =>
        applyRuleAtF fuel acc psrule.rule classId) acc) env v'' ∧
      HashconsChildrenBounded (l.foldl (fun acc classId =>
        applyRuleAtF fuel acc psrule.rule classId) acc) by
    obtain ⟨v'', hcv'', hpmi'', hshi'', hhcb''⟩ := h _ g' v'
      (fun cid hcid => by
        have ⟨a, hmem, ha_eq⟩ : ∃ a ∈ g'.classes.toList, a.1 = cid :=
          List.mem_map.mp hcid
        have hcont : g'.classes.contains a.fst = true := by
          rw [Std.HashMap.contains_eq_isSome_getElem?,
              Std.HashMap.mem_toList_iff_getElem?_eq_some.mp hmem]; rfl
        exact ha_eq ▸ hpmi'.classes_entries_valid a.fst hcont)
      hcv' hpmi' hshi' hhcb' Nat.le.refl
    exact ⟨v'', hcv'', hpmi'', hshi'', hhcb''⟩
  intro l
  induction l with
  | nil =>
    intro acc v_acc _ hcv hpmi hshi hhcb _
    exact ⟨v_acc, hcv, hpmi, hshi, hhcb⟩
  | cons cid rest ih =>
    intro acc v_acc hbnd hcv_acc hpmi_acc hshi_acc hhcb_acc hsize_acc
    simp only [List.foldl_cons]
    have hcid : cid < acc.unionFind.parent.size :=
      Nat.lt_of_lt_of_le (hbnd cid (.head _)) hsize_acc
    obtain ⟨v'', hcv'', hpmi'', hshi'', hhcb'', hsize''⟩ :=
      applyRuleAtF_sound fuel psrule cid env sameShapeSemantics_holds
        (InstantiateEvalSound_holds env) acc v_acc hcv_acc hpmi_acc
        hshi_acc hhcb_acc hcid (hematch_bnd acc psrule hps hpmi_acc cid hcid)
    exact ih _ v'' (fun c hc => hbnd c (.tail _ hc)) hcv'' hpmi'' hshi'' hhcb''
      (Nat.le_trans hsize_acc hsize'')

/-- **saturateF preserves WellFormed.** Derives WellFormed from PMI preservation
    through the saturation pipeline. Corollary of `saturateF_preserves_quadruple`. -/
theorem saturateF_preserves_wf [Inhabited Val] (fuel maxIter rebuildFuel : Nat)
    (g : EGraph Op) (rules : List (PatternSoundRule Op Val))
    (env : Nat → Val) (v : EClassId → Val)
    (hcv : ConsistentValuation g env v)
    (hpmi : PostMergeInvariant g) (hshi : SemanticHashconsInv g env v)
    (hhcb : HashconsChildrenBounded g) :
    WellFormed (saturateF fuel maxIter rebuildFuel g (rules.map (·.rule))).unionFind :=
  let ⟨_, _, hpmi_sat, _, _⟩ := saturateF_preserves_quadruple fuel maxIter rebuildFuel g
    (rules.map (·.rule)) env v hcv hpmi hshi hhcb
    (patternSoundRules_preserveCV fuel env rules)
  hpmi_sat.uf_wf

/-- **Hypothesis-free greedy pipeline soundness.** Like `optimizeF_soundness` but
    auto-discharges `hwf_sat` and `hbni_sat` from initial e-graph invariants.

    Replaces the two external hypotheses:
    - `hwf_sat` — derived via `saturateF_preserves_quadruple` → PMI → `.uf_wf`
    - `hbni_sat` — derived via `saturateF_preserves_bni` from `hbni_init`

    The only new hypothesis compared to `optimizeF_soundness` is `hbni_init`,
    which states that the initial e-graph satisfies BestNodeInv. This is trivially
    true for freshly constructed graphs (all classes have `bestNode := none`). -/
theorem optimizeF_soundness_complete [Inhabited Val] (g : EGraph Op)
    (rules : List (PatternSoundRule Op Val))
    (costFn : ENode Op → Nat) (costFuel fuel maxIter rebuildFuel : Nat)
    (env : Nat → Val) (v : EClassId → Val)
    (hcv : ConsistentValuation g env v)
    (hpmi : PostMergeInvariant g) (hshi : SemanticHashconsInv g env v)
    (hhcb : HashconsChildrenBounded g)
    (hbni_init : BestNodeInv g.classes)
    (rootId : EClassId) (expr : Expr)
    (hsound : ExtractableSound Op Expr Val)
    (hopt : optimizeF fuel maxIter rebuildFuel g (rules.map (·.rule))
      costFn costFuel rootId = some expr) :
    ∃ (v_sat : EClassId → Val), EvalExpr.evalExpr expr env =
      v_sat (root (saturateF fuel maxIter rebuildFuel g
        (rules.map (·.rule))).unionFind rootId) :=
  optimizeF_soundness g rules costFn costFuel fuel maxIter rebuildFuel env v
    hcv hpmi hshi hhcb rootId expr
    (saturateF_preserves_wf fuel maxIter rebuildFuel g rules env v hcv hpmi hshi hhcb)
    (saturateF_preserves_bni fuel maxIter rebuildFuel g (rules.map (·.rule)) hbni_init)
    hsound hopt

end LambdaSat
