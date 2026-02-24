/-
  LambdaSat — E-Match Specification
  Fase 7 Subfase 1-2: Pattern.eval denotational semantics + SameShapeSemantics.

  Key definitions:
  - `Pattern.eval`: denotational semantics for patterns
  - `SameShapeSemantics`: property connecting sameShape to evalOp

  Key theorems:
  - `sameShape_children_length`: sameShape implies children have equal length
  - `Pattern.eval_patVar`: equation lemma for patVar
  - `Pattern.eval_ext`: extensionality of Pattern.eval in σ

  Pattern.eval gives denotational semantics: given an environment `env` and
  a variable assignment `σ : PatVarId → Val`, each pattern evaluates to a value.
  For `patVar pv`, it returns `σ pv`. For `node skelOp subpats`, it evaluates
  subpatterns recursively, builds a child valuation, and applies `evalOp`.

  SameShapeSemantics bridges pattern evaluation to node evaluation: when
  `sameShape skelOp nd.op = true` and children agree, `evalOp skelOp = evalOp nd.op`.
  This is the key property for ematchF_sound (Bloque 17).
-/
import LambdaSat.SaturationSpec

namespace LambdaSat

open UnionFind

set_option linter.unusedSectionVars false

-- ══════════════════════════════════════════════════════════════════
-- Section 0: SameShapeSemantics
-- ══════════════════════════════════════════════════════════════════

variable {Op : Type} [NodeOps Op] [BEq Op] [Hashable Op] [LawfulBEq Op] [LawfulHashable Op]

/-- Two ops with the same shape have children of equal length.
    Follows from `mapChildren_children` + `LawfulBEq`. -/
theorem sameShape_children_length {op₁ op₂ : Op} (h : sameShape op₁ op₂ = true) :
    (NodeOps.children op₁).length = (NodeOps.children op₂).length := by
  simp [sameShape] at h
  have h1 := NodeOps.mapChildren_children (fun _ => (0 : EClassId)) op₁
  have h2 := NodeOps.mapChildren_children (fun _ => (0 : EClassId)) op₂
  rw [h] at h1; rw [h1] at h2
  have := congrArg List.length h2
  simp [List.length_map] at this
  exact this

variable {Val : Type} [NodeSemantics Op Val]

/-- SameShapeSemantics: operators with the same shape produce the same
    semantic value when corresponding children have matching values.

    This property connects pattern evaluation to e-graph node evaluation.
    Required for `ematchF_sound` (Bloque 17). Any reasonable domain
    (arithmetic, circuits, etc.) satisfies this: same-shape ops differ
    only in children, and `evalOp` depends on children by `evalOp_ext`. -/
def SameShapeSemantics : Prop :=
  ∀ (op₁ op₂ : Op) (env : Nat → Val) (v₁ v₂ : EClassId → Val),
    sameShape op₁ op₂ = true →
    (∀ (i : Nat) (h₁ : i < (NodeOps.children op₁).length)
        (h₂ : i < (NodeOps.children op₂).length),
      v₁ ((NodeOps.children op₁)[i]) = v₂ ((NodeOps.children op₂)[i])) →
    NodeSemantics.evalOp op₁ env v₁ = NodeSemantics.evalOp op₂ env v₂

-- ══════════════════════════════════════════════════════════════════
-- Section 1: Pattern.eval — Denotational Semantics
-- ══════════════════════════════════════════════════════════════════

variable [Inhabited Val]

/-- Denotational semantics for patterns.

    - `patVar pv` evaluates to `σ pv` (variable lookup)
    - `node skelOp subpats` evaluates subpatterns recursively, builds a
      child valuation `w` mapping each child of `skelOp` to the corresponding
      subpattern value, and applies `evalOp skelOp env w`.

    The child valuation is built via association list (zip + lookup).
    For children not in the zip, `default` is used — this is sound because
    `evalOp_ext` guarantees `evalOp` depends on `v` only through children. -/
def Pattern.eval : Pattern Op → (Nat → Val) → (PatVarId → Val) → Val
  | .patVar pv, _, σ => σ pv
  | .node skelOp subpats, env, σ =>
    let childVals := subpats.map (fun p => Pattern.eval p env σ)
    let children := NodeOps.children skelOp
    let w : EClassId → Val := fun id =>
      match (children.zip childVals).lookup id with
      | some val => val
      | none => default
    NodeSemantics.evalOp skelOp env w

/-- Equation lemma: `Pattern.eval` on `patVar` is variable lookup. -/
theorem Pattern.eval_patVar (pv : PatVarId) (env : Nat → Val) (σ : PatVarId → Val) :
    Pattern.eval (.patVar (Op := Op) pv) env σ = σ pv := by
  unfold Pattern.eval; rfl

-- ══════════════════════════════════════════════════════════════════
-- Section 2: Pattern.eval Properties
-- ══════════════════════════════════════════════════════════════════

/-- Extensionality: `Pattern.eval` depends on `σ` pointwise.
    If `σ₁` and `σ₂` agree on all pattern variable IDs,
    then `eval pat env σ₁ = eval pat env σ₂`.

    Proved using `Pattern.rec` (structural induction for nested inductives). -/
theorem Pattern.eval_ext : ∀ (pat : Pattern Op) (env : Nat → Val) (σ₁ σ₂ : PatVarId → Val),
    (∀ pv, σ₁ pv = σ₂ pv) → Pattern.eval pat env σ₁ = Pattern.eval pat env σ₂ :=
  @Pattern.rec Op
    (fun pat => ∀ (env : Nat → Val) (σ₁ σ₂ : PatVarId → Val),
      (∀ pv, σ₁ pv = σ₂ pv) → Pattern.eval pat env σ₁ = Pattern.eval pat env σ₂)
    (fun pats => ∀ (env : Nat → Val) (σ₁ σ₂ : PatVarId → Val),
      (∀ pv, σ₁ pv = σ₂ pv) →
      pats.map (fun p => Pattern.eval p env σ₁) = pats.map (fun p => Pattern.eval p env σ₂))
    -- patVar case
    (fun pv env σ₁ σ₂ h => by rw [eval_patVar, eval_patVar, h])
    -- node case: ih_list gives map equality → child valuation agrees → evalOp agrees
    (fun skelOp subpats ih_list env σ₁ σ₂ h => by
      simp only [Pattern.eval]
      have hm := ih_list env σ₁ σ₂ h
      congr 1; funext id; rw [hm])
    -- nil case
    (fun _ _ _ _ => rfl)
    -- cons case
    (fun p ps ih_p ih_ps env σ₁ σ₂ h => by
      simp only [List.map]
      exact congr (congrArg _ (ih_p env σ₁ σ₂ h)) (ih_ps env σ₁ σ₂ h))

/-- Map lemma: subpats.map eval agrees when σ agrees. Helper for inductive proofs. -/
theorem Pattern.map_eval_ext : ∀ (pats : List (Pattern Op)) (env : Nat → Val)
    (σ₁ σ₂ : PatVarId → Val),
    (∀ pv, σ₁ pv = σ₂ pv) →
    pats.map (fun p => Pattern.eval p env σ₁) = pats.map (fun p => Pattern.eval p env σ₂) :=
  @List.rec (Pattern Op)
    (fun pats => ∀ (env : Nat → Val) (σ₁ σ₂ : PatVarId → Val),
      (∀ pv, σ₁ pv = σ₂ pv) →
      pats.map (fun p => Pattern.eval p env σ₁) = pats.map (fun p => Pattern.eval p env σ₂))
    (fun _ _ _ _ => rfl)
    (fun p ps ih env σ₁ σ₂ h => by
      simp only [List.map]
      exact congr (congrArg _ (Pattern.eval_ext p env σ₁ σ₂ h)) (ih env σ₁ σ₂ h))

-- ══════════════════════════════════════════════════════════════════
-- Section 3: ematchF Soundness — Auxiliary Definitions
-- ══════════════════════════════════════════════════════════════════

/-- Convert a Substitution to a valuation: look up each pattern variable's bound
    class ID and evaluate via `v ∘ root`. Unbound variables map to `default`. -/
def substVal (v : EClassId → Val) (uf : UnionFind) (σ : Substitution) : PatVarId → Val :=
  fun pv => match σ.get? pv with
  | some id => v (root uf id)
  | none => default

/-- A pattern is well-formed: node skeletons have distinct children,
    the number of subpatterns matches the number of children, and
    all subpatterns are recursively well-formed.
    Required for `ematchF_sound` to bridge zip+lookup to positional access. -/
def AllDistinctChildren : Pattern Op → Prop
  | .patVar _ => True
  | .node skelOp subpats =>
    (NodeOps.children skelOp).Nodup ∧
    subpats.length = (NodeOps.children skelOp).length ∧
    ∀ p ∈ subpats, AllDistinctChildren p

/-- For a list with no duplicate keys, zip+lookup at the i-th key gives the i-th value. -/
theorem zip_lookup_nodup {α β : Type} [BEq α] [LawfulBEq α]
    (keys : List α) (vals : List β) (i : Nat)
    (hnd : keys.Nodup) (hi : i < keys.length) (hlen : keys.length ≤ vals.length) :
    (keys.zip vals).lookup (keys[i]) = some (vals[i]'(by omega)) := by
  induction keys generalizing vals i with
  | nil => simp at hi
  | cons k ks ih =>
    cases vals with
    | nil => simp at hlen
    | cons v vs =>
      simp [List.zip, List.lookup]
      obtain ⟨hk_notin, hks_nd⟩ := List.nodup_cons.mp hnd
      cases i with
      | zero =>
        simp [BEq.beq, LawfulBEq.eq_of_beq]
      | succ j =>
        simp at hlen hi
        have hk_ne : (ks[j]'(by omega) == k) = false := by
          rw [beq_eq_false_iff_ne]
          intro heq
          exact hk_notin (heq ▸ List.getElem_mem (by omega))
        simp [hk_ne]
        exact ih vs j hks_nd (by omega) (by omega)

/-- If `Substitution.extend` succeeds, the resulting substitution maps `pv` to `id`. -/
theorem Substitution.extend_some_get (subst : Substitution) (pv : PatVarId) (id : EClassId)
    (s : Substitution) (h : subst.extend pv id = some s) : s.get? pv = some id := by
  simp [Substitution.extend] at h
  split at h
  · -- get? pv = none → s = insert pv id
    rw [Option.some.inj h.symm]; simp
  · -- get? pv = some eid, eid == id → s = subst
    rename_i eid hget
    split at h
    · rename_i hbeq; rw [Option.some.inj h.symm]; simp [hget, hbeq]
    · simp at h

/-- σ₂ extends σ₁: every binding in σ₁ is preserved in σ₂. -/
def SubstExtends (σ₁ σ₂ : Substitution) : Prop :=
  ∀ pv id, σ₁.get? pv = some id → σ₂.get? pv = some id

theorem SubstExtends.refl (σ : Substitution) : SubstExtends σ σ :=
  fun _ _ h => h

theorem SubstExtends.trans {σ₁ σ₂ σ₃ : Substitution}
    (h₁₂ : SubstExtends σ₁ σ₂) (h₂₃ : SubstExtends σ₂ σ₃) : SubstExtends σ₁ σ₃ :=
  fun pv id h => h₂₃ pv id (h₁₂ pv id h)

/-- extend preserves all existing bindings in the substitution. -/
theorem Substitution.extend_extends (subst : Substitution) (pv : PatVarId) (id : EClassId)
    (s : Substitution) (h : subst.extend pv id = some s) : SubstExtends subst s := by
  simp [Substitution.extend] at h
  split at h
  · -- get? pv = none → s = insert pv id
    rename_i hget_none
    rw [Option.some.inj h.symm]
    intro pv' id' hget'
    by_cases heq : pv' = pv
    · subst heq; simp at hget_none; exact absurd hget' (by simp [hget_none])
    · simp [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, Ne.symm heq]
      rwa [Std.HashMap.get?_eq_getElem?] at hget'
  · rename_i eid hget
    split at h
    · rw [Option.some.inj h.symm]; exact SubstExtends.refl subst
    · simp at h

set_option linter.unusedSimpArgs false

/-- Foldl invariant: if all initial elements satisfy P, and each step preserves P,
    then all final elements satisfy P. -/
theorem list_foldl_forall {α β : Type} {P : β → Prop} {f : List β → α → List β}
    (l : List α) (init : List β)
    (hinit : ∀ x ∈ init, P x)
    (hstep : ∀ a ∈ l, ∀ acc : List β, (∀ x ∈ acc, P x) → ∀ x ∈ f acc a, P x) :
    ∀ x ∈ l.foldl f init, P x := by
  induction l generalizing init with
  | nil => exact hinit
  | cons hd tl ih =>
    simp only [List.foldl]
    apply ih
    · exact hstep hd (.head _) init hinit
    · intro a ha; exact hstep a (.tail _ ha)

/-- matchChildren soundness: if σ is in the matchChildren output (and not in acc),
    then σ extends subst₀ and each subpattern evaluates correctly under any
    extension of σ.

    Proved by induction on the subpatterns list, using the ematchF IH for fuel n. -/
theorem matchChildren_sound
    (g : EGraph Op) (env : Nat → Val) (v : EClassId → Val)
    (_hcv : ConsistentValuation g env v) (_hwf : WellFormed g.unionFind)
    (n : Nat)
    (ih_fuel : ∀ (pat : Pattern Op) (classId : EClassId) (subst₀ σ : Substitution),
      σ ∈ ematchF n g pat classId subst₀ →
      AllDistinctChildren pat →
      SubstExtends subst₀ σ ∧
      (∀ σ' : Substitution, SubstExtends σ σ' →
        Pattern.eval pat env (substVal v g.unionFind σ') = v (root g.unionFind classId)))
    : ∀ (pats : List (Pattern Op)) (nodeChildren : List EClassId)
        (subst₀ : Substitution) (acc : MatchResult) (σ : Substitution),
      σ ∈ ematchF.matchChildren g n pats nodeChildren subst₀ acc →
      σ ∉ acc →
      (∀ p ∈ pats, AllDistinctChildren p) →
      pats.length = nodeChildren.length →
      SubstExtends subst₀ σ ∧
      (∀ (i : Nat) (hi : i < pats.length) (hi2 : i < nodeChildren.length),
        ∀ σ' : Substitution, SubstExtends σ σ' →
          Pattern.eval pats[i] env (substVal v g.unionFind σ') =
            v (root g.unionFind nodeChildren[i])) := by
  intro pats
  induction pats with
  | nil =>
    intro nodeChildren subst₀ acc σ hmem hnacc hdc hlen
    cases nodeChildren with
    | nil =>
      -- matchChildren [] [] subst₀ acc = acc ++ [subst₀]
      unfold ematchF.matchChildren at hmem
      simp at hmem
      rcases hmem with hmem_acc | hmem_eq
      · exact absurd hmem_acc hnacc
      · exact ⟨hmem_eq ▸ SubstExtends.refl subst₀, fun i hi hi2 => by simp at hi⟩
    | cons c cs =>
      -- matchChildren [] (c :: cs) subst₀ acc = acc (length mismatch)
      simp at hlen
  | cons p ps ih_pats =>
    intro nodeChildren subst₀ acc σ hmem hnacc hdc hlen
    cases nodeChildren with
    | nil => simp at hlen
    | cons c cs =>
      simp at hlen
      unfold ematchF.matchChildren at hmem
      -- hmem : σ ∈ (ematchF n g p c subst₀).foldl
      --   (fun a s => matchChildren g n ps cs s a) acc
      -- Define Q(σ) = σ ∈ acc ∨ P(σ) where P is our target property
      let P : Substitution → Prop := fun σ =>
        SubstExtends subst₀ σ ∧
        (∀ (i : Nat) (hi : i < (p :: ps).length) (hi2 : i < (c :: cs).length),
          ∀ σ', SubstExtends σ σ' →
            Pattern.eval (p :: ps)[i] env (substVal v g.unionFind σ') =
              v (root g.unionFind (c :: cs)[i]))
      -- Use foldl_forall with Q(σ) = σ ∈ acc ∨ P(σ)
      have hfoldl : σ ∈ acc ∨ P σ :=
        list_foldl_forall
          (P := fun σ => σ ∈ acc ∨ P σ)
          (f := fun a s => ematchF.matchChildren g n ps cs s a)
          (ematchF n g p c subst₀) acc
          (fun x hx => Or.inl hx)
          (fun σ_mid hmid acc' hacc' x hx => by
            by_cases hx_acc : x ∈ acc'
            · exact hacc' x hx_acc
            · right
              have hp_dc := hdc p (.head _)
              have hps_dc : ∀ q ∈ ps, AllDistinctChildren q :=
                fun q hq => hdc q (.tail _ hq)
              have ⟨hext_mid, heval_mid⟩ := ih_fuel p c subst₀ σ_mid hmid hp_dc
              have ⟨hext_x, heval_x⟩ :=
                ih_pats cs σ_mid acc' x hx hx_acc hps_dc hlen
              exact ⟨hext_mid.trans hext_x, fun i hi hi2 σ' hσ' => by
                cases i with
                | zero => exact heval_mid σ' (hext_x.trans hσ')
                | succ j => simp at hi hi2; exact heval_x j hi hi2 σ' hσ'⟩)
          σ hmem
      exact hfoldl.resolve_left hnacc

-- ══════════════════════════════════════════════════════════════════
-- Section 4: ematchF Soundness — Main Theorem
-- ══════════════════════════════════════════════════════════════════

/-- **Strengthened ematchF soundness**: ematchF extends the substitution and
    the pattern evaluates correctly under any extension of the output.

    This strengthened form is needed for the node case: when matchChildren
    processes child i, later children may extend the substitution further,
    but the eval result for child i remains valid under these extensions. -/
theorem ematchF_sound_strong (g : EGraph Op) (env : Nat → Val) (v : EClassId → Val)
    (hcv : ConsistentValuation g env v) (hwf : WellFormed g.unionFind)
    (hsss : SameShapeSemantics (Op := Op) (Val := Val)) :
    ∀ (fuel : Nat) (pat : Pattern Op) (classId : EClassId) (subst₀ σ : Substitution),
      σ ∈ ematchF fuel g pat classId subst₀ →
      AllDistinctChildren pat →
      SubstExtends subst₀ σ ∧
      (∀ σ' : Substitution, SubstExtends σ σ' →
        Pattern.eval pat env (substVal v g.unionFind σ') = v (root g.unionFind classId)) := by
  intro fuel
  induction fuel with
  | zero => intro pat classId subst₀ σ hmem; simp [ematchF] at hmem
  | succ n ih =>
    intro pat classId subst₀ σ hmem hdc
    cases pat with
    | patVar pv =>
      unfold ematchF at hmem; simp only [] at hmem
      split at hmem
      · rename_i s hext; simp at hmem
        have hext_get := Substitution.extend_some_get subst₀ pv _ s hext
        have hext_ext := Substitution.extend_extends subst₀ pv _ s hext
        exact ⟨hmem ▸ hext_ext, fun σ' hσ' => by
          rw [Pattern.eval_patVar]; simp only [substVal]
          rw [hσ' pv _ (hmem ▸ hext_get)]
          exact consistent_root_eq' g env v hcv hwf (root g.unionFind classId)⟩
      · simp at hmem
    | node skelOp subpats =>
      unfold ematchF at hmem; simp only [] at hmem
      -- Split on class lookup
      split at hmem
      · simp at hmem
      · rename_i eclass hclass
        -- Get AllDistinctChildren components
        simp only [AllDistinctChildren] at hdc
        obtain ⟨hnodup, hlen_pat, hdc_sub⟩ := hdc
        -- Define property Q
        let Q : Substitution → Prop := fun σ =>
          SubstExtends subst₀ σ ∧
          (∀ σ' : Substitution, SubstExtends σ σ' →
            (Pattern.node skelOp subpats).eval env (substVal v g.unionFind σ') =
              v (root g.unionFind classId))
        suffices hQ : Q σ from hQ
        -- Use Array foldl → List foldl conversion
        rw [← Array.foldl_toList] at hmem
        -- Provide f explicitly to resolve metavariable
        exact list_foldl_forall (P := Q)
          (f := fun acc (nd : ENode Op) =>
            if sameShape skelOp nd.op = true
            then ematchF.matchChildren g n subpats (NodeOps.children nd.op) subst₀ acc
            else acc)
          eclass.nodes.toList [] (fun _ h => absurd h (by simp))
          (fun nd hnd acc' hacc' x hx => by
            dsimp only [] at hx
            split at hx
            · -- sameShape skelOp nd.op = true
              rename_i hshape
              by_cases hx_acc : x ∈ acc'
              · exact hacc' x hx_acc
              · -- x is new from matchChildren
                have hlen_eq : subpats.length = (NodeOps.children nd.op).length :=
                  hlen_pat.trans (sameShape_children_length hshape)
                have ⟨hext_x, heval_x⟩ :=
                  matchChildren_sound g env v hcv hwf n ih
                    subpats (NodeOps.children nd.op) subst₀ acc' x hx hx_acc hdc_sub hlen_eq
                exact ⟨hext_x, fun σ' hσ' => by
                  -- Bridge: Pattern.eval → SameShapeSemantics → CV
                  -- Step 1: CV gives evalOp nd.op env v = v (root classId)
                  have hcv_nd := hcv.2 (root g.unionFind classId) eclass hclass nd hnd
                  simp only [NodeEval] at hcv_nd
                  -- Step 2: Define w explicitly for SameShapeSemantics
                  let w : EClassId → Val := fun id =>
                    match ((NodeOps.children skelOp).zip
                      (subpats.map (fun p => p.eval env (substVal v g.unionFind σ')))).lookup id with
                    | some val => val
                    | none => default
                  -- Step 3: Positional child agreement
                  have hchildren_agree :
                      ∀ (i : Nat) (h₁ : i < (NodeOps.children skelOp).length)
                        (h₂ : i < (NodeOps.children nd.op).length),
                      w ((NodeOps.children skelOp)[i]) =
                        v ((NodeOps.children nd.op)[i]) := by
                    intro i h₁ h₂
                    have hlen_cv : (NodeOps.children skelOp).length ≤
                        (subpats.map (fun p => p.eval env (substVal v g.unionFind σ'))).length := by
                      simp [List.length_map]; omega
                    dsimp only [w]
                    rw [zip_lookup_nodup _ _ i hnodup h₁ hlen_cv]
                    simp [List.getElem_map]
                    rw [heval_x i (by omega) h₂ σ' hσ']
                    exact consistent_root_eq' g env v hcv hwf _
                  -- Step 4: SameShapeSemantics bridge
                  have hss := hsss skelOp nd.op env w v hshape hchildren_agree
                  -- Step 5: Connect Pattern.eval to evalOp skelOp env w
                  show (Pattern.node skelOp subpats).eval env (substVal v g.unionFind σ') =
                    v (root g.unionFind classId)
                  simp only [Pattern.eval]
                  exact hss.trans hcv_nd⟩
            · -- sameShape = false: x ∈ acc'
              exact hacc' x hx)
          σ hmem

/-- **ematchF soundness**: if e-matching succeeds, the pattern evaluates to the
    matched class's value under the resulting substitution. Corollary of the
    strengthened version. -/
theorem ematchF_sound (g : EGraph Op) (env : Nat → Val) (v : EClassId → Val)
    (hcv : ConsistentValuation g env v) (hwf : WellFormed g.unionFind)
    (hsss : SameShapeSemantics (Op := Op) (Val := Val)) :
    ∀ (fuel : Nat) (pat : Pattern Op) (classId : EClassId) (subst₀ σ : Substitution),
      σ ∈ ematchF fuel g pat classId subst₀ →
      AllDistinctChildren pat →
      Pattern.eval pat env (substVal v g.unionFind σ) = v (root g.unionFind classId) :=
  fun fuel pat classId subst₀ σ hmem hdc =>
    (ematchF_sound_strong g env v hcv hwf hsss fuel pat classId subst₀ σ hmem hdc).2 σ
      (SubstExtends.refl σ)

-- ══════════════════════════════════════════════════════════════════
-- Section 5: Pipeline — From ematchF_sound to PreservesCV
-- ══════════════════════════════════════════════════════════════════
-- This section shows that for PatternSoundRules with a verified instantiation
-- property (InstantiateEvalSound), PreservesCV is derivable, eliminating the
-- monolithic assumption from v0.3.0.
--
-- Decomposition:
--   1. ematchF_sound (proven, Section 4) — e-matching returns correct substitutions
--   2. PatternSoundRule — rewrite rules with Pattern.eval-level soundness
--   3. InstantiateEvalSound — instantiateF preserves triple + gives correct value
-- These compose to give PreservesCV for each rule application step.

/-- A rewrite rule with Pattern.eval-level soundness: the LHS and RHS patterns
    evaluate identically under any substitution. Unlike `SoundRewriteRule`
    (which uses `eval : Expr → env → Val`), this uses `Pattern.eval` directly,
    enabling a clean bridge from `ematchF_sound` to merge correctness. -/
structure PatternSoundRule (Op : Type) [NodeOps Op] [BEq Op] [Hashable Op]
    (Val : Type) [NodeSemantics Op Val] [Inhabited Val] where
  rule : RewriteRule Op
  soundness : ∀ (env : Nat → Val) (σ : PatVarId → Val),
    Pattern.eval rule.lhs env σ = Pattern.eval rule.rhs env σ
  lhs_wf : AllDistinctChildren rule.lhs
  rhs_wf : AllDistinctChildren rule.rhs

/-- Semantic match-merge equality: ematch + PatternSoundRule → lhs=rhs=v(classId). -/
theorem pattern_rule_match_eq (g : EGraph Op) (env : Nat → Val) (v : EClassId → Val)
    (hcv : ConsistentValuation g env v) (hwf : WellFormed g.unionFind)
    (hsss : SameShapeSemantics (Op := Op) (Val := Val))
    (psrule : PatternSoundRule Op Val)
    (fuel : Nat) (classId : EClassId) (σ : Substitution)
    (hmem : σ ∈ ematchF fuel g psrule.rule.lhs classId) :
    Pattern.eval psrule.rule.lhs env (substVal v g.unionFind σ) =
      Pattern.eval psrule.rule.rhs env (substVal v g.unionFind σ) ∧
    Pattern.eval psrule.rule.lhs env (substVal v g.unionFind σ) =
      v (root g.unionFind classId) :=
  ⟨psrule.soundness env (substVal v g.unionFind σ),
   ematchF_sound g env v hcv hwf hsss fuel psrule.rule.lhs classId .empty σ hmem psrule.lhs_wf⟩

/-- Focused property: instantiateF preserves the (CV, PMI, SHI) triple and
    gives the instantiated node the correct semantic value.
    Replaces the monolithic PreservesCV assumption from v0.3.0.

    This takes PMI (not EGraphWF/AddExprInv) to compose correctly through the
    foldl in applyRuleAtF where merge breaks HashconsClassesAligned. -/
def InstantiateEvalSound (Op : Type) (Val : Type) [NodeOps Op] [BEq Op] [Hashable Op]
    [NodeSemantics Op Val] [Inhabited Val] (env : Nat → Val) : Prop :=
  ∀ (fuel : Nat) (g : EGraph Op) (pat : Pattern Op)
    (subst : Substitution) (v : EClassId → Val),
    ConsistentValuation g env v →
    PostMergeInvariant g →
    SemanticHashconsInv g env v →
    AllDistinctChildren pat →
    (∀ pv id, subst.get? pv = some id → id < g.unionFind.parent.size) →
    ∀ id g', instantiateF fuel g pat subst = some (id, g') →
    ∃ v', ConsistentValuation g' env v' ∧
      PostMergeInvariant g' ∧
      SemanticHashconsInv g' env v' ∧
      id < g'.unionFind.parent.size ∧
      g.unionFind.parent.size ≤ g'.unionFind.parent.size ∧
      (∀ i, i < g.unionFind.parent.size → v' i = v i) ∧
      v' (root g'.unionFind id) = Pattern.eval pat env (substVal v g.unionFind subst)

/-- substVal agrees across graph extensions when valuations agree on the original.
    Key bridge: ematchF produces substitutions for g₀, but we instantiate in g_acc.
    If v_acc agrees with v₀ on g₀'s IDs and both are consistent, substVal matches. -/
theorem substVal_agrees (g g₀ : EGraph Op) (env : Nat → Val) (v v₀ : EClassId → Val)
    (hcv : ConsistentValuation g env v) (hcv₀ : ConsistentValuation g₀ env v₀)
    (hwf : WellFormed g.unionFind) (hwf₀ : WellFormed g₀.unionFind)
    (hagrees : ∀ i, i < g₀.unionFind.parent.size → v i = v₀ i)
    (σ : Substitution) (pv : PatVarId)
    (hbnd : ∀ pv' id, σ.get? pv' = some id → id < g₀.unionFind.parent.size) :
    substVal v g.unionFind σ pv = substVal v₀ g₀.unionFind σ pv := by
  simp only [substVal]
  cases h : σ.get? pv with
  | some id =>
    simp only []
    rw [consistent_root_eq' g env v hcv hwf id, hagrees id (hbnd pv id h)]
    exact (consistent_root_eq' g₀ env v₀ hcv₀ hwf₀ id).symm
  | none => rfl

/-- Value chain: for an ematch result σ from g₀, eval(rhs, substVal v g.uf σ) = v(root g.uf classId)
    when v agrees with v₀ on g₀. Chains through: substVal_agrees → eval_ext → soundness →
    ematchF_sound → consistent_root_eq' in both directions. -/
private theorem ematch_value_chain (g₀ g : EGraph Op) (env : Nat → Val) (v₀ v : EClassId → Val)
    (hcv₀ : ConsistentValuation g₀ env v₀) (hcv : ConsistentValuation g env v)
    (hwf₀ : WellFormed g₀.unionFind) (hwf : WellFormed g.unionFind)
    (hagrees : ∀ i, i < g₀.unionFind.parent.size → v i = v₀ i)
    (hsss : SameShapeSemantics (Op := Op) (Val := Val))
    (psrule : PatternSoundRule Op Val) (fuel : Nat) (classId : EClassId)
    (hclass : classId < g₀.unionFind.parent.size)
    (σ : Substitution) (hmem : σ ∈ ematchF fuel g₀ psrule.rule.lhs classId)
    (hbnd : ∀ pv id, σ.get? pv = some id → id < g₀.unionFind.parent.size) :
    Pattern.eval psrule.rule.rhs env (substVal v g.unionFind σ) =
      v (root g.unionFind classId) :=
  calc Pattern.eval psrule.rule.rhs env (substVal v g.unionFind σ)
      _ = Pattern.eval psrule.rule.rhs env (substVal v₀ g₀.unionFind σ) :=
          Pattern.eval_ext _ env _ _ (fun pv =>
            substVal_agrees g g₀ env v v₀ hcv hcv₀ hwf hwf₀ hagrees σ pv hbnd)
      _ = Pattern.eval psrule.rule.lhs env (substVal v₀ g₀.unionFind σ) :=
          (psrule.soundness env _).symm
      _ = v₀ (root g₀.unionFind classId) :=
          ematchF_sound g₀ env v₀ hcv₀ hwf₀ hsss fuel _ classId .empty σ hmem psrule.lhs_wf
      _ = v₀ classId := consistent_root_eq' g₀ env v₀ hcv₀ hwf₀ classId
      _ = v classId := (hagrees classId hclass).symm
      _ = v (root g.unionFind classId) := (consistent_root_eq' g env v hcv hwf classId).symm

set_option linter.unusedSectionVars false in
/-- A single instantiate+merge step in applyRuleAtF preserves (CV, PMI, SHI) and
    value agreement with the original graph.
    Used as the inductive step for the inner foldl in applyRuleAtF. -/
private theorem applyRuleAtF_step_sound
    (fuel : Nat) (psrule : PatternSoundRule Op Val) (classId : EClassId) (env : Nat → Val)
    (hsss : SameShapeSemantics (Op := Op) (Val := Val))
    (hies : InstantiateEvalSound Op Val env)
    (g₀ : EGraph Op) (v₀ : EClassId → Val)
    (hcv₀ : ConsistentValuation g₀ env v₀) (hpmi₀ : PostMergeInvariant g₀)
    (hclass : classId < g₀.unionFind.parent.size)
    (acc : EGraph Op) (v_acc : EClassId → Val) (σ : Substitution)
    (hcv : ConsistentValuation acc env v_acc) (hpmi : PostMergeInvariant acc)
    (hshi : SemanticHashconsInv acc env v_acc)
    (hagrees : ∀ i, i < g₀.unionFind.parent.size → v_acc i = v₀ i)
    (hsize : g₀.unionFind.parent.size ≤ acc.unionFind.parent.size)
    (hmem : σ ∈ ematchF fuel g₀ psrule.rule.lhs classId)
    (hbnd : ∀ pv id, σ.get? pv = some id → id < g₀.unionFind.parent.size) :
    let step_result :=
      let condMet := match psrule.rule.sideCondCheck with
        | some check => check acc σ | none => true
      if !condMet then acc
      else match instantiateF fuel acc psrule.rule.rhs σ with
        | none => acc
        | some (rhsId, acc') =>
          if root acc'.unionFind classId == root acc'.unionFind rhsId then acc'
          else acc'.merge classId rhsId
    ∃ v', ConsistentValuation step_result env v' ∧
      PostMergeInvariant step_result ∧
      SemanticHashconsInv step_result env v' ∧
      (∀ i, i < g₀.unionFind.parent.size → v' i = v₀ i) ∧
      g₀.unionFind.parent.size ≤ step_result.unionFind.parent.size := by
  -- dsimp reduces let bindings (condMet, canonLhs, canonRhs)
  dsimp only []
  -- Case split on sideCondCheck to eliminate the match inside the if-condition,
  -- so that subsequent `split` targets the outer ite/match correctly.
  have h_subst_bnd : ∀ pv id, σ.get? pv = some id → id < acc.unionFind.parent.size :=
    fun pv id h => Nat.lt_of_lt_of_le (hbnd pv id h) hsize
  -- Common proof for the instantiateF branch (used by both sideCondCheck cases)
  suffices h_inst : ∃ v',
      ConsistentValuation (match instantiateF fuel acc psrule.rule.rhs σ with
        | none => acc | some (rhsId, acc') =>
          if (acc'.unionFind.root classId == acc'.unionFind.root rhsId) = true
          then acc' else acc'.merge classId rhsId) env v' ∧
      PostMergeInvariant (match instantiateF fuel acc psrule.rule.rhs σ with
        | none => acc | some (rhsId, acc') =>
          if (acc'.unionFind.root classId == acc'.unionFind.root rhsId) = true
          then acc' else acc'.merge classId rhsId) ∧
      SemanticHashconsInv (match instantiateF fuel acc psrule.rule.rhs σ with
        | none => acc | some (rhsId, acc') =>
          if (acc'.unionFind.root classId == acc'.unionFind.root rhsId) = true
          then acc' else acc'.merge classId rhsId) env v' ∧
      (∀ i, i < g₀.unionFind.parent.size → v' i = v₀ i) ∧
      g₀.unionFind.parent.size ≤ (match instantiateF fuel acc psrule.rule.rhs σ with
        | none => acc | some (rhsId, acc') =>
          if (acc'.unionFind.root classId == acc'.unionFind.root rhsId) = true
          then acc' else acc'.merge classId rhsId).unionFind.parent.size by
    match psrule.rule.sideCondCheck with
    | none =>
      have h : ¬((!true : Bool) = true) := by decide
      simp only [if_neg h]; exact h_inst
    | some check =>
      by_cases hcond : ((!check acc σ : Bool) = true)
      · simp only [if_pos hcond]; exact ⟨v_acc, hcv, hpmi, hshi, hagrees, hsize⟩
      · simp only [if_neg hcond]; exact h_inst
  -- Prove h_inst: the instantiateF match preserves everything
  split
  · exact ⟨v_acc, hcv, hpmi, hshi, hagrees, hsize⟩
  · rename_i rhsId' acc'' hinst
    obtain ⟨v', hcv', hpmi', hshi', hrhsBnd, hsize', hagrees', hval⟩ :=
      hies fuel acc psrule.rule.rhs σ v_acc hcv hpmi hshi psrule.rhs_wf h_subst_bnd
        rhsId' acc'' hinst
    have hagrees_g₀ : ∀ i, i < g₀.unionFind.parent.size → v' i = v₀ i :=
      fun i hi => (hagrees' i (Nat.lt_of_lt_of_le hi hsize)).trans (hagrees i hi)
    have hsize_g₀ : g₀.unionFind.parent.size ≤ acc''.unionFind.parent.size :=
      Nat.le_trans hsize hsize'
    have hclass' : classId < acc''.unionFind.parent.size :=
      Nat.lt_of_lt_of_le hclass hsize_g₀
    have hval_eq : v' (root acc''.unionFind rhsId') = v' (root acc''.unionFind classId) := by
      rw [hval, ematch_value_chain g₀ acc env v₀ v_acc hcv₀ hcv hpmi₀.uf_wf hpmi.uf_wf
        hagrees hsss psrule fuel classId hclass σ hmem hbnd,
        consistent_root_eq' acc env v_acc hcv hpmi.uf_wf classId,
        ← hagrees' classId (Nat.lt_of_lt_of_le hclass hsize)]
      exact (consistent_root_eq' acc'' env v' hcv' hpmi'.uf_wf classId).symm
    split
    · exact ⟨v', hcv', hpmi', hshi', hagrees_g₀, hsize_g₀⟩
    · exact ⟨v', merge_consistent acc'' classId rhsId' env v' hcv' hpmi'.uf_wf
        hclass' hrhsBnd hval_eq.symm,
        merge_preserves_pmi acc'' classId rhsId' hpmi' hclass',
        merge_preserves_shi acc'' classId rhsId' env v' hshi' hcv'
          hpmi'.uf_wf hclass' hrhsBnd hval_eq.symm,
        hagrees_g₀, merge_uf_size acc'' classId rhsId' ▸ hsize_g₀⟩

set_option linter.unusedSectionVars false in
set_option maxHeartbeats 400000 in
/-- applyRuleAtF preserves (CV, PMI, SHI) for a PatternSoundRule.
    Proven by induction on the inner foldl (match results). -/
theorem applyRuleAtF_sound (fuel : Nat) (psrule : PatternSoundRule Op Val)
    (classId : EClassId) (env : Nat → Val)
    (hsss : SameShapeSemantics (Op := Op) (Val := Val))
    (hies : InstantiateEvalSound Op Val env)
    (g : EGraph Op) (v : EClassId → Val)
    (hcv : ConsistentValuation g env v) (hpmi : PostMergeInvariant g)
    (hshi : SemanticHashconsInv g env v)
    (hclass : classId < g.unionFind.parent.size)
    (hematch_bnd : ∀ σ ∈ ematchF fuel g psrule.rule.lhs classId,
      ∀ pv id, σ.get? pv = some id → id < g.unionFind.parent.size) :
    ∃ v', ConsistentValuation (applyRuleAtF fuel g psrule.rule classId) env v' ∧
      PostMergeInvariant (applyRuleAtF fuel g psrule.rule classId) ∧
      SemanticHashconsInv (applyRuleAtF fuel g psrule.rule classId) env v' ∧
      g.unionFind.parent.size ≤ (applyRuleAtF fuel g psrule.rule classId).unionFind.parent.size := by
  unfold applyRuleAtF
  -- Generalize to foldl with invariant: (CV, PMI, SHI, agrees, size)
  suffices h : ∀ (l : List Substitution) (acc : EGraph Op) (v_acc : EClassId → Val),
    (∀ σ ∈ l, σ ∈ ematchF fuel g psrule.rule.lhs classId) →
    ConsistentValuation acc env v_acc → PostMergeInvariant acc →
    SemanticHashconsInv acc env v_acc →
    (∀ i, i < g.unionFind.parent.size → v_acc i = v i) →
    g.unionFind.parent.size ≤ acc.unionFind.parent.size →
    ∃ v', ConsistentValuation (l.foldl (fun acc subst =>
      let condMet := match psrule.rule.sideCondCheck with
        | some check => check acc subst | none => true
      if !condMet then acc
      else match instantiateF fuel acc psrule.rule.rhs subst with
        | none => acc
        | some (rhsId, acc') =>
          if root acc'.unionFind classId == root acc'.unionFind rhsId then acc'
          else acc'.merge classId rhsId) acc) env v' ∧
      PostMergeInvariant (l.foldl (fun acc subst =>
      let condMet := match psrule.rule.sideCondCheck with
        | some check => check acc subst | none => true
      if !condMet then acc
      else match instantiateF fuel acc psrule.rule.rhs subst with
        | none => acc
        | some (rhsId, acc') =>
          if root acc'.unionFind classId == root acc'.unionFind rhsId then acc'
          else acc'.merge classId rhsId) acc) ∧
      SemanticHashconsInv (l.foldl (fun acc subst =>
      let condMet := match psrule.rule.sideCondCheck with
        | some check => check acc subst | none => true
      if !condMet then acc
      else match instantiateF fuel acc psrule.rule.rhs subst with
        | none => acc
        | some (rhsId, acc') =>
          if root acc'.unionFind classId == root acc'.unionFind rhsId then acc'
          else acc'.merge classId rhsId) acc) env v' ∧
      g.unionFind.parent.size ≤ (l.foldl (fun acc subst =>
      let condMet := match psrule.rule.sideCondCheck with
        | some check => check acc subst | none => true
      if !condMet then acc
      else match instantiateF fuel acc psrule.rule.rhs subst with
        | none => acc
        | some (rhsId, acc') =>
          if root acc'.unionFind classId == root acc'.unionFind rhsId then acc'
          else acc'.merge classId rhsId) acc).unionFind.parent.size by
    obtain ⟨v', hcv', hpmi', hshi', hsize'⟩ := h _ g v (fun σ hσ => hσ) hcv hpmi hshi
      (fun _ _ => rfl) Nat.le.refl
    exact ⟨v', hcv', hpmi', hshi', hsize'⟩
  intro l
  induction l with
  | nil => intro acc v_acc _ hcv hpmi hshi _ hsize; exact ⟨v_acc, hcv, hpmi, hshi, hsize⟩
  | cons σ rest ih =>
    intro acc v_acc hmem hcv_acc hpmi_acc hshi_acc hagrees hsize
    simp only [List.foldl_cons]
    have hmem_σ := hmem σ (.head _)
    have hbnd_σ := hematch_bnd σ hmem_σ
    obtain ⟨v', hcv', hpmi', hshi', hagrees', hsize'⟩ :=
      applyRuleAtF_step_sound fuel psrule classId env hsss hies g v hcv hpmi hclass
        acc v_acc σ hcv_acc hpmi_acc hshi_acc hagrees hsize hmem_σ hbnd_σ
    exact ih _ v' (fun σ' hσ' => hmem σ' (.tail _ hσ')) hcv' hpmi' hshi' hagrees' hsize'

set_option linter.unusedSectionVars false in
set_option maxHeartbeats 400000 in
/-- Full pipeline: saturateF preserves ConsistentValuation when all rules are
    PatternSoundRules and InstantiateEvalSound holds.

    This eliminates the monolithic `PreservesCV` assumption from v0.3.0 and
    replaces it with two modular, verifiable properties:
    1. `ematchF_sound` — fully proven (zero sorry, this file)
    2. `InstantiateEvalSound` — focused property about instantiateF's value

    The derivation: for each rule, applyRuleAtF_sound gives (CV, PMI, SHI)
    preservation, which composes through the outer foldl to give PreservesCV
    for the full applyRuleF → saturateF pipeline. -/
theorem saturateF_preserves_consistent_internal (fuel maxIter rebuildFuel : Nat)
    (g : EGraph Op) (rules : List (PatternSoundRule Op Val))
    (env : Nat → Val) (v : EClassId → Val)
    (hcv : ConsistentValuation g env v)
    (hpmi : PostMergeInvariant g) (hshi : SemanticHashconsInv g env v)
    (hsss : SameShapeSemantics (Op := Op) (Val := Val))
    (hies : InstantiateEvalSound Op Val env)
    (hematch_bnd : ∀ (g' : EGraph Op) (rule : PatternSoundRule Op Val),
      rule ∈ rules → PostMergeInvariant g' →
      ∀ (classId : EClassId), classId < g'.unionFind.parent.size →
      ∀ σ ∈ ematchF fuel g' rule.rule.lhs classId,
      ∀ pv id, σ.get? pv = some id → id < g'.unionFind.parent.size) :
    ∃ v', ConsistentValuation
      (saturateF fuel maxIter rebuildFuel g (rules.map (·.rule))) env v' :=
  saturateF_preserves_consistent fuel maxIter rebuildFuel g (rules.map (·.rule))
    env v hcv hpmi hshi (fun rule hrule => by
      obtain ⟨psrule, hps, hrw⟩ := List.mem_map.mp hrule
      rw [← hrw]
      -- Derive PreservesCV from applyRuleAtF_sound
      intro g' v' hcv' hpmi' hshi'
      -- applyRuleF = foldl applyRuleAtF over allClasses
      simp only [applyRuleF]
      -- Prove foldl over classes preserves triple
      suffices h : ∀ (l : List EClassId) (acc : EGraph Op) (v_acc : EClassId → Val),
        (∀ cid ∈ l, cid < g'.unionFind.parent.size) →
        ConsistentValuation acc env v_acc → PostMergeInvariant acc →
        SemanticHashconsInv acc env v_acc →
        g'.unionFind.parent.size ≤ acc.unionFind.parent.size →
        ∃ v'', ConsistentValuation (l.foldl (fun acc classId =>
          applyRuleAtF fuel acc psrule.rule classId) acc) env v'' ∧
          PostMergeInvariant (l.foldl (fun acc classId =>
            applyRuleAtF fuel acc psrule.rule classId) acc) ∧
          SemanticHashconsInv (l.foldl (fun acc classId =>
            applyRuleAtF fuel acc psrule.rule classId) acc) env v'' by
        obtain ⟨v'', hcv'', hpmi'', hshi''⟩ := h _ g' v'
          (fun cid hcid => by
            have ⟨a, hmem, ha_eq⟩ : ∃ a ∈ g'.classes.toList, a.1 = cid :=
              List.mem_map.mp hcid
            have hcont : g'.classes.contains a.fst = true := by
              rw [Std.HashMap.contains_eq_isSome_getElem?,
                  Std.HashMap.mem_toList_iff_getElem?_eq_some.mp hmem]; rfl
            exact ha_eq ▸ hpmi'.classes_entries_valid a.fst hcont)
          hcv' hpmi' hshi' Nat.le.refl
        exact ⟨v'', hcv'', hpmi'', hshi''⟩
      intro l
      induction l with
      | nil => intro acc v_acc _ hcv hpmi hshi _; exact ⟨v_acc, hcv, hpmi, hshi⟩
      | cons cid rest ih =>
        intro acc v_acc hbnd hcv_acc hpmi_acc hshi_acc hsize_acc
        simp only [List.foldl_cons]
        have hcid : cid < acc.unionFind.parent.size :=
          Nat.lt_of_lt_of_le (hbnd cid (.head _)) hsize_acc
        obtain ⟨v'', hcv'', hpmi'', hshi'', hsize''⟩ :=
          applyRuleAtF_sound fuel psrule cid env hsss hies acc v_acc hcv_acc hpmi_acc
            hshi_acc hcid (hematch_bnd acc psrule hps hpmi_acc cid hcid)
        exact ih _ v'' (fun c hc => hbnd c (.tail _ hc)) hcv'' hpmi'' hshi''
          (Nat.le_trans hsize_acc hsize''))

end LambdaSat
