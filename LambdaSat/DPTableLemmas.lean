/-
  LambdaSat.DPTableLemmas — DP Correctness Proofs

  Complete proof chain for DPCompleteInv preservation through all four
  DP operations (leaf, introduce, forget, join), plus the master theorem
  `runDP_DPCompleteInv` via ValidNTD induction.

  Adapted from VerifiedExtraction/DPTableLemmas.lean (0 sorry, 0 axioms).
-/
import LambdaSat.TreewidthDP

namespace LambdaSat.DPTableLemmas

open LambdaSat
open LambdaSat.TreewidthDP
open LambdaSat.Util.NiceTree (NiceTree treeFold treeFold_inv)

variable {Op : Type} [NodeOps Op] [BEq Op] [Hashable Op]

set_option linter.unusedSectionVars false

/-! ## bagLe infrastructure -/

private theorem bagLe_trans : ∀ a b c : EClassId × Nat,
    bagLe a b = true → bagLe b c = true → bagLe a c = true := by
  intro ⟨a1, a2⟩ ⟨b1, b2⟩ ⟨c1, c2⟩
  simp only [bagLe, decide_eq_true_eq]
  intro hab hbc
  rcases hab with h1 | ⟨rfl, h2⟩
  · rcases hbc with h3 | ⟨rfl, _⟩
    · left; exact Nat.lt_trans h1 h3
    · left; exact h1
  · rcases hbc with h3 | ⟨rfl, h4⟩
    · left; exact h3
    · right; exact ⟨rfl, Nat.le_trans h2 h4⟩

private theorem bagLe_total : ∀ a b : EClassId × Nat,
    (bagLe a b || bagLe b a) = true := by
  intro ⟨a1, a2⟩ ⟨b1, b2⟩
  simp only [bagLe, Bool.or_eq_true, decide_eq_true_eq]
  by_cases h : a1 < b1
  · left; left; exact h
  · by_cases h2 : b1 < a1
    · right; left; exact h2
    · have heq : a1 = b1 := Nat.le_antisymm (Nat.le_of_not_lt h2) (Nat.le_of_not_lt h)
      by_cases h3 : a2 ≤ b2
      · left; right; exact ⟨heq, h3⟩
      · right; right; exact ⟨heq.symm, Nat.le_of_lt (Nat.not_le.mp h3)⟩

/-! ## Canonical form -/

/-- Canonicalization is idempotent. -/
theorem canonicalize_idempotent (ba : BagAssignment) :
    canonicalizeAssignment (canonicalizeAssignment ba) = canonicalizeAssignment ba := by
  unfold canonicalizeAssignment
  exact List.mergeSort_of_pairwise (List.pairwise_mergeSort bagLe_trans bagLe_total ba)

/-- Permutations have the same canonical form. -/
theorem canon_eq_of_perm (l1 l2 : BagAssignment) (h : l1.Perm l2) :
    canonicalizeAssignment l1 = canonicalizeAssignment l2 := by
  unfold canonicalizeAssignment
  exact List.Perm.eq_of_pairwise
    (fun a b _ _ hab hba => by
      obtain ⟨a1, a2⟩ := a; obtain ⟨b1, b2⟩ := b
      simp only [bagLe, decide_eq_true_eq] at hab hba
      rcases hab with hl | ⟨rfl, hr⟩
      · rcases hba with hl2 | ⟨rfl, _⟩
        · exact absurd (Nat.lt_trans hl hl2) (Nat.lt_irrefl _)
        · exact absurd hl (Nat.lt_irrefl _)
      · rcases hba with hl2 | ⟨_, hr2⟩
        · exact absurd hl2 (Nat.lt_irrefl _)
        · exact Prod.ext rfl (Nat.le_antisymm hr hr2))
    (List.pairwise_mergeSort bagLe_trans bagLe_total l1)
    (List.pairwise_mergeSort bagLe_trans bagLe_total l2)
    ((List.mergeSort_perm l1 bagLe).trans (h.trans (List.mergeSort_perm l2 bagLe).symm))

/-- Same canonical form implies permutation. -/
theorem perm_of_canon_eq (l1 l2 : BagAssignment)
    (h : canonicalizeAssignment l1 = canonicalizeAssignment l2) : l1.Perm l2 := by
  unfold canonicalizeAssignment at h
  exact (List.mergeSort_perm l1 bagLe).symm.trans (h ▸ List.mergeSort_perm l2 bagLe)

/-- Appending same suffix to canonical-equal lists gives canonical-equal results. -/
theorem canon_append_congr (l1 l2 : BagAssignment) (suffix : BagAssignment)
    (h : canonicalizeAssignment l1 = canonicalizeAssignment l2) :
    canonicalizeAssignment (l1 ++ suffix) = canonicalizeAssignment (l2 ++ suffix) :=
  canon_eq_of_perm _ _ ((perm_of_canon_eq l1 l2 h).append (List.Perm.refl suffix))

/-- Filtering canonical-equal lists gives canonical-equal results. -/
theorem canon_filter_of_canon_eq {l1 l2 : BagAssignment}
    (heq : canonicalizeAssignment l1 = canonicalizeAssignment l2) (p : EClassId × Nat → Bool) :
    canonicalizeAssignment (l1.filter p) = canonicalizeAssignment (l2.filter p) :=
  canon_eq_of_perm _ _ ((perm_of_canon_eq l1 l2 heq).filter p)

/-- Canonicalize preserves membership. -/
theorem mem_canon_iff (x : EClassId × Nat) (ba : BagAssignment) :
    x ∈ canonicalizeAssignment ba ↔ x ∈ ba :=
  List.mem_mergeSort

/-! ## List BEq helpers -/

private theorem list_beq_refl' [BEq α] [ReflBEq α] (l : List α) :
    List.beq l l = true := by
  induction l with | nil => rfl | cons x xs ih => simp [List.beq, ih]

private theorem list_beq_eq' [BEq α] [LawfulBEq α] {l1 l2 : List α}
    (h : List.beq l1 l2 = true) : l1 = l2 := by
  induction l1 generalizing l2 with
  | nil => cases l2 <;> simp_all [List.beq]
  | cons x xs ih =>
    cases l2 with
    | nil => simp [List.beq] at h
    | cons y ys =>
      simp only [List.beq, Bool.and_eq_true] at h
      rw [eq_of_beq h.1, ih h.2]

/-! ## DPTable.insertMin Lemmas -/

/-- After insertMin, the target key has some value ≤ the inserted cost. -/
theorem insertMin_get_self (t : DPTable) (ba : BagAssignment) (cost : Nat) :
    ∃ c, (t.insertMin ba cost).get? ba = some c ∧ c ≤ cost := by
  simp only [DPTable.get?, DPTable.insertMin,
    Std.HashMap.getD_eq_getD_getElem?, ← Std.HashMap.get?_eq_getElem?]
  cases hget : t.entries.get? (canonicalizeAssignment ba) with
  | none => simp [Option.getD]
  | some old =>
    simp only [Option.getD]
    by_cases hlt : cost < old
    · simp [hlt]
    · simp [hlt]; exact ⟨old, hget, Nat.le_of_not_lt hlt⟩

/-- insertMin preserves entries for other keys. -/
theorem insertMin_get_ne (t : DPTable) (ba ba' : BagAssignment) (cost : Nat)
    (hne : ¬(canonicalizeAssignment ba == canonicalizeAssignment ba' : Bool)) :
    (t.insertMin ba cost).get? ba' = t.get? ba' := by
  simp only [DPTable.get?, DPTable.insertMin,
    Std.HashMap.getD_eq_getD_getElem?, ← Std.HashMap.get?_eq_getElem?]
  have hne' : (canonicalizeAssignment ba == canonicalizeAssignment ba') = false :=
    Bool.eq_false_iff.mpr hne
  split
  case isTrue h =>
    rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, hne']; simp
  case isFalse h => rfl

/-- After insertMin, if there was an old entry, the result value ≤ old. -/
theorem insertMin_le_old (t : DPTable) (ba : BagAssignment) (cost old : Nat)
    (h_old : t.get? ba = some old) :
    ∃ c, (t.insertMin ba cost).get? ba = some c ∧ c ≤ old := by
  simp only [DPTable.get?, DPTable.insertMin,
    Std.HashMap.getD_eq_getD_getElem?, ← Std.HashMap.get?_eq_getElem?] at h_old ⊢
  cases hget : t.entries.get? (canonicalizeAssignment ba) with
  | none => rw [hget] at h_old; simp at h_old
  | some oldVal =>
    simp only [Option.getD, hget] at h_old ⊢
    injection h_old with h_eq; subst h_eq
    by_cases hlt : cost < oldVal
    · simp [hlt]; exact Nat.le_of_lt hlt
    · simp [hlt]; exact ⟨oldVal, hget, Nat.le_refl _⟩

/-- insertMin on empty produces exactly the inserted value. -/
theorem insertMin_empty_get (ba : BagAssignment) (cost : Nat) :
    (DPTable.empty.insertMin ba cost).get? ba = some cost := by
  simp only [DPTable.get?, DPTable.insertMin, DPTable.empty,
    Std.HashMap.getD_eq_getD_getElem?, ← Std.HashMap.get?_eq_getElem?]
  simp [Option.getD]

/-- BEq-equal canonical forms give the same get? result. -/
theorem get?_canon_congr (t : DPTable) (ba ba' : BagAssignment)
    (h : (canonicalizeAssignment ba == canonicalizeAssignment ba') = true) :
    t.get? ba = t.get? ba' := by
  simp only [DPTable.get?]
  congr 1
  simp only [BEq.beq] at h
  rw [canonicalize_idempotent, canonicalize_idempotent] at h
  exact list_beq_eq' h

/-- Empty DPTable has no entries. -/
theorem empty_get?_none (ba : BagAssignment) : DPTable.empty.get? ba = none := by
  simp [DPTable.get?, DPTable.empty]

/-- Entry provenance: after insertMin, either existed before or came from insertion. -/
theorem insertMin_provenance (t : DPTable) (ba_new ba : BagAssignment) (cost_new cost : Nat)
    (h : (t.insertMin ba_new cost_new).get? ba = some cost) :
    (t.get? ba = some cost) ∨
    (canonicalizeAssignment ba = canonicalizeAssignment ba_new ∧ cost ≤ cost_new) := by
  by_cases hne : (canonicalizeAssignment ba_new == canonicalizeAssignment ba : Bool)
  case neg =>
    left; rw [insertMin_get_ne t ba_new ba cost_new hne] at h; exact h
  case pos =>
    right
    have heq : canonicalizeAssignment ba_new = canonicalizeAssignment ba := by
      simp only [BEq.beq] at hne
      rw [canonicalize_idempotent, canonicalize_idempotent] at hne
      exact list_beq_eq' hne
    refine ⟨heq.symm, ?_⟩
    obtain ⟨c, hc, hle⟩ := insertMin_get_self t ba_new cost_new
    simp only [DPTable.get?, ← heq] at h hc
    have : c = cost := by rw [hc] at h; injection h
    subst this; exact hle

/-- insertMin preserves or lowers existing entries (monotonicity). -/
theorem insertMin_monotone (t : DPTable) (ba : BagAssignment) (cost : Nat)
    (ba' : BagAssignment) (cost' : Nat) (h : t.get? ba' = some cost') :
    ∃ cost'', (t.insertMin ba cost).get? ba' = some cost'' ∧ cost'' ≤ cost' := by
  by_cases hbeq : (canonicalizeAssignment ba == canonicalizeAssignment ba' : Bool)
  case pos =>
    have h_same := get?_canon_congr t ba ba' hbeq
    have h_ba : t.get? ba = some cost' := by rw [h_same]; exact h
    obtain ⟨c, hc, hle⟩ := insertMin_le_old t ba cost cost' h_ba
    have h_res := get?_canon_congr (t.insertMin ba cost) ba ba' hbeq
    exact ⟨c, by rw [← h_res]; exact hc, hle⟩
  case neg =>
    rw [insertMin_get_ne t ba ba' cost hbeq]
    exact ⟨cost', h, Nat.le_refl _⟩

/-! ## HashMap fold bridge -/

/-- HashMap.fold on DPTable = List.foldl on toList. -/
theorem dpTable_fold_eq_list {β : Type} (t : DPTable) (f : β → BagAssignment → Nat → β) (init : β) :
    t.entries.fold f init = t.entries.toList.foldl (fun acc (kv : BagAssignment × Nat) => f acc kv.1 kv.2) init := by
  simp only [Std.HashMap.fold_eq_foldl_toList]

/-- get? → toList membership (richer version with canonical form). -/
theorem get?_some_toList' (t : DPTable) (ba : BagAssignment) (cost : Nat)
    (h : t.get? ba = some cost) :
    ∃ ba', canonicalizeAssignment ba' = canonicalizeAssignment ba ∧
           (ba', cost) ∈ t.entries.toList := by
  simp only [DPTable.get?] at h
  rw [Std.HashMap.get?_eq_getElem?] at h
  obtain ⟨ba', hbeq, hmem⟩ := Std.HashMap.getElem?_eq_some_iff_exists_beq_and_mem_toList.mp h
  refine ⟨ba', ?_, hmem⟩
  simp only [BEq.beq] at hbeq
  rw [canonicalize_idempotent] at hbeq
  exact (list_beq_eq' hbeq).symm

/-- BagAssignment BEq-equals its canonical form. -/
theorem ba_beq_canonicalize (ba : BagAssignment) :
    (ba == canonicalizeAssignment ba) = true := by
  show (instBEqBagAssignment.beq ba (canonicalizeAssignment ba)) = true
  simp only [BEq.beq]
  rw [canonicalize_idempotent]
  exact list_beq_refl' _

/-! ## Fold Mechanics -/

/-- Monotonicity through foldl of insertMin. -/
theorem foldl_insertMin_monotone
    (entries : List (BagAssignment × Nat))
    (proj : BagAssignment × Nat → BagAssignment)
    (pcost : BagAssignment × Nat → Nat)
    (init : DPTable) (ba' : BagAssignment) (cost' : Nat)
    (h : init.get? ba' = some cost') :
    ∃ cost'', (entries.foldl (fun acc kv => acc.insertMin (proj kv) (pcost kv)) init).get?
      ba' = some cost'' ∧ cost'' ≤ cost' := by
  induction entries generalizing init cost' with
  | nil => exact ⟨cost', h, Nat.le_refl _⟩
  | cons x xs ih =>
    simp only [List.foldl]
    obtain ⟨c, hc, hle⟩ := insertMin_monotone _ (proj x) (pcost x) _ cost' h
    obtain ⟨c', hc', hle'⟩ := ih _ c hc
    exact ⟨c', hc', Nat.le_trans hle' hle⟩

/-- After foldl of insertMin, every processed entry has a result ≤ its cost. -/
theorem foldl_insertMin_entry_bound
    (entries : List (BagAssignment × Nat))
    (proj : BagAssignment × Nat → BagAssignment)
    (pcost : BagAssignment × Nat → Nat)
    (init : DPTable) (x : BagAssignment × Nat) (hmem : x ∈ entries) :
    ∃ cost', (entries.foldl (fun acc kv => acc.insertMin (proj kv) (pcost kv)) init).get?
      (proj x) = some cost' ∧ cost' ≤ pcost x := by
  induction entries generalizing init with
  | nil => simp at hmem
  | cons y ys ih =>
    simp only [List.foldl]
    cases List.mem_cons.mp hmem with
    | inl heq =>
      subst heq
      obtain ⟨c, hc, hle⟩ := insertMin_get_self init (proj x) (pcost x)
      obtain ⟨c', hc', hle'⟩ := foldl_insertMin_monotone ys proj pcost _ (proj x) c hc
      exact ⟨c', hc', Nat.le_trans hle' hle⟩
    | inr hmem_ys =>
      exact ih (init.insertMin (proj y) (pcost y)) hmem_ys

/-- Foldl of a monotone function preserves existing table entries. -/
theorem foldl_mono_preserves {α : Type} (l : List α) (f : DPTable → α → DPTable)
    (h_mono : ∀ t x ba c, t.get? ba = some c → ∃ c', (f t x).get? ba = some c' ∧ c' ≤ c)
    (init : DPTable) (ba : BagAssignment) (cost : Nat) (h : init.get? ba = some cost) :
    ∃ cost', (l.foldl f init).get? ba = some cost' ∧ cost' ≤ cost := by
  induction l generalizing init cost with
  | nil => exact ⟨cost, h, Nat.le_refl _⟩
  | cons x xs ih =>
    obtain ⟨c, hc, hle⟩ := h_mono init x ba cost h
    obtain ⟨c', hc', hle'⟩ := ih (f init x) c hc
    exact ⟨c', hc', Nat.le_trans hle' hle⟩

/-- If processing a list member creates a bounded entry, the full foldl preserves it. -/
theorem foldl_creates_bounded_entry {α : Type} (l : List α) (f : DPTable → α → DPTable)
    (h_mono : ∀ t x ba c, t.get? ba = some c → ∃ c', (f t x).get? ba = some c' ∧ c' ≤ c)
    (x : α) (hmem : x ∈ l) (k : BagAssignment) (bound : Nat)
    (hx : ∀ t, ∃ cost, (f t x).get? k = some cost ∧ cost ≤ bound)
    (init : DPTable) :
    ∃ cost, (l.foldl f init).get? k = some cost ∧ cost ≤ bound := by
  obtain ⟨l₁, l₂, heq⟩ := List.append_of_mem hmem; subst heq
  rw [List.foldl_append]; simp only [List.foldl]
  obtain ⟨c, hc, hle⟩ := hx (l₁.foldl f init)
  obtain ⟨c', hc', hle'⟩ := foldl_mono_preserves l₂ f h_mono _ k c hc
  exact ⟨c', hc', Nat.le_trans hle' hle⟩

/-! ## selectionToBag infrastructure -/

theorem selectionToBag_filter (sel : ENodeSelection) (bag : List EClassId) (v : EClassId) :
    (selectionToBag sel bag).filter (fun (cid, _) => cid != v) =
    selectionToBag sel (bag.filter (· != v)) := by
  simp only [selectionToBag]; induction bag with
  | nil => simp
  | cons c cs ih =>
    by_cases hv : c = v
    · subst hv
      cases hsel : sel.get? c with
      | none => simp_all
      | some nidx => simp_all
    · cases hsel : sel.get? c with
      | none => simp_all [bne]
      | some nidx => simp_all [bne]

theorem selectionToBag_append (sel : ENodeSelection) (bag : List EClassId) (v : EClassId)
    (nidx : Nat) (h : sel.get? v = some nidx) :
    selectionToBag sel (bag ++ [v]) = selectionToBag sel bag ++ [(v, nidx)] := by
  simp only [selectionToBag, List.filterMap_append, List.filterMap_cons, List.filterMap_nil,
    h, Option.map_some]

/-! ## selectionCost Arithmetic -/


private theorem selCost_foldl_shift (g : EGraph Op) (sel : ENodeSelection) (costFn : ENode Op → Nat)
    (l : List EClassId) (a b : Nat) :
    l.foldl (fun acc cid => match sel.get? cid with
      | some nidx => acc + nodeCost g cid nidx costFn | none => acc) (a + b) =
    a + l.foldl (fun acc cid => match sel.get? cid with
      | some nidx => acc + nodeCost g cid nidx costFn | none => acc) b := by
  induction l generalizing b with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl]; split
    · next nidx _ =>
      have : a + b + nodeCost g x nidx costFn = a + (b + nodeCost g x nidx costFn) := by omega
      rw [this]; exact ih _
    · exact ih _

/-- selectionCost is additive over append. -/
theorem selectionCost_append (g : EGraph Op) (sel : ENodeSelection)
    (A B : List EClassId) (costFn : ENode Op → Nat) :
    selectionCost g sel (A ++ B) costFn =
      selectionCost g sel A costFn + selectionCost g sel B costFn := by
  simp only [selectionCost, List.foldl_append]
  exact selCost_foldl_shift g sel costFn B _ 0

/-! ## BagCost correspondence (for dpJoin) -/

/-- BagCost as computed in dpJoin. -/
def bagCostFoldl (g : EGraph Op) (ba : BagAssignment) (costFn : ENode Op → Nat) : Nat :=
  ba.foldl (fun acc (cid, nidx) => acc + nodeCost g cid nidx costFn) 0

/-- Permutation preserves bagCost. -/

theorem bagCostFoldl_perm (g : EGraph Op) (ba1 ba2 : BagAssignment) (costFn : ENode Op → Nat)
    (h : ba1.Perm ba2) : bagCostFoldl g ba1 costFn = bagCostFoldl g ba2 costFn := by
  unfold bagCostFoldl
  exact h.foldl_eq'
    (fun x _ y _ z => by obtain ⟨c1, n1⟩ := x; obtain ⟨c2, n2⟩ := y; simp only []; omega) 0

/-- selectionCost equals bagCostFoldl of selectionToBag when sel covers all bag classes. -/

theorem selectionCost_eq_bagCost (g : EGraph Op) (sel : ENodeSelection)
    (bag : List EClassId) (costFn : ENode Op → Nat)
    (h_valid : ∀ cid ∈ bag, ∃ nidx, sel.get? cid = some nidx) :
    selectionCost g sel bag costFn = bagCostFoldl g (selectionToBag sel bag) costFn := by
  unfold selectionCost bagCostFoldl selectionToBag
  generalize (0 : Nat) = init
  induction bag generalizing init with
  | nil => simp
  | cons c cs ih =>
    obtain ⟨nidx, hsel⟩ := h_valid c (List.mem_cons_self)
    have ih' := ih (fun cid hc => h_valid cid (List.mem_cons_of_mem c hc))
    simp only [List.filterMap_cons, hsel, Option.map_some, List.foldl_cons]
    exact ih' _

/-! ## isConsistentWithBag simplification -/

/-- isConsistentWithBag always true for valid node indices. -/
theorem isConsistentWithBag_of_valid (g : EGraph Op) (classId : EClassId)
    (nodeIdx : Nat) (ba : BagAssignment)
    (h : nodeIdx ∈ validNodeIndices g classId) :
    isConsistentWithBag g classId nodeIdx ba = true := by
  unfold isConsistentWithBag; unfold validNodeIndices at h
  generalize g.classes.get? classId = v at h ⊢
  cases v with
  | none => simp at h
  | some ec =>
    dsimp at h ⊢
    have hidx : nodeIdx < ec.nodes.size := List.mem_range.mp h
    simp [dif_pos hidx]
    intro x _; split <;> rfl

/-! ## dpIntroduce inner fold helpers -/

/-- Inner foldl of dpIntroduce preserves existing entries. -/
theorem intro_inner_mono (g : EGraph Op) (v : EClassId) (ba : BagAssignment)
    (cost : Nat) (costFn : ENode Op → Nat)
    (validNodes : List Nat) (t : DPTable) (ba' : BagAssignment) (c : Nat)
    (h : t.get? ba' = some c) :
    ∃ c', (validNodes.foldl (fun acc nodeIdx =>
      if isConsistentWithBag g v nodeIdx ba then
        acc.insertMin (ba ++ [(v, nodeIdx)]) (cost + nodeCost g v nodeIdx costFn)
      else acc) t).get? ba' = some c' ∧ c' ≤ c := by
  induction validNodes generalizing t c with
  | nil => exact ⟨c, h, Nat.le_refl _⟩
  | cons n ns ih =>
    simp only [List.foldl]; by_cases hc' : isConsistentWithBag g v n ba
    · simp only [hc', ite_true]
      obtain ⟨c', hc', hle⟩ := insertMin_monotone t _ _ ba' c h
      obtain ⟨c'', hc'', hle'⟩ := ih _ c' hc'; exact ⟨c'', hc'', Nat.le_trans hle' hle⟩
    · simp only [hc']; exact ih t c h

/-- Inner foldl creates bounded entry for a valid nodeIdx. -/
theorem intro_inner_bounded (g : EGraph Op) (v : EClassId) (ba : BagAssignment)
    (cost : Nat) (costFn : ENode Op → Nat)
    (validNodes : List Nat) (nidx : Nat) (hmem : nidx ∈ validNodes)
    (hvalid : nidx ∈ validNodeIndices g v) (bound : Nat)
    (hbound : cost + nodeCost g v nidx costFn ≤ bound) (t : DPTable) :
    ∃ c, (validNodes.foldl (fun acc nodeIdx =>
      if isConsistentWithBag g v nodeIdx ba then
        acc.insertMin (ba ++ [(v, nodeIdx)]) (cost + nodeCost g v nodeIdx costFn)
      else acc) t).get? (ba ++ [(v, nidx)]) = some c ∧ c ≤ bound := by
  obtain ⟨l₁, l₂, heq⟩ := List.append_of_mem hmem; subst heq
  rw [List.foldl_append]; simp only [List.foldl]
  have hcons := isConsistentWithBag_of_valid g v nidx ba hvalid
  simp only [hcons, ite_true]
  obtain ⟨c, hc, hle⟩ := insertMin_get_self (l₁.foldl _ t) (ba ++ [(v, nidx)]) _
  obtain ⟨c', hc', hle'⟩ := intro_inner_mono g v ba cost costFn l₂ _ _ c hc
  exact ⟨c', hc', Nat.le_trans hle' (Nat.le_trans hle hbound)⟩

/-! ## dpJoin step monotonicity -/

/-- dpJoin's fold step is monotone. -/

theorem dpJoin_step_mono (g : EGraph Op) (rightTable : DPTable) (costFn : ENode Op → Nat)
    (t : DPTable) (kv : BagAssignment × Nat) (ba' : BagAssignment) (c : Nat)
    (h : t.get? ba' = some c) :
    ∃ c', (match rightTable.get? kv.1 with
      | some rightCost =>
        let bagCost := kv.1.foldl (fun acc (cid, nidx) => acc + nodeCost g cid nidx costFn) 0
        t.insertMin kv.1 (kv.2 + rightCost - bagCost)
      | none => t).get? ba' = some c' ∧ c' ≤ c := by
  cases rightTable.get? kv.1 with
  | none => exact ⟨c, h, Nat.le_refl _⟩
  | some rc => exact insertMin_monotone t _ _ ba' c h

/-! ## DPCompleteInv Preservation — All Four DP Operations -/

/-- **dpLeaf**: trivially satisfies DPCompleteInv. -/

theorem dpLeaf_DPCompleteInv (g : EGraph Op) (costFn : ENode Op → Nat) :
    DPCompleteInv g costFn [] [] dpLeaf where
  has_bounded_entry := by
    intro sel _
    simp only [selectionToBag, List.filterMap_nil]
    unfold dpLeaf
    obtain ⟨c, hc, hle⟩ := insertMin_get_self DPTable.empty [] 0
    exact ⟨c, hc, by simp [selectionCost]; omega⟩

/-- **dpForget**: projects out v from bag, classes unchanged. -/

theorem dpForget_DPCompleteInv (g : EGraph Op) (costFn : ENode Op → Nat)
    (v : EClassId) (childBag childClasses : List EClassId)
    (childTable : DPTable)
    (h_child : DPCompleteInv g costFn childBag childClasses childTable) :
    DPCompleteInv g costFn (childBag.filter (· != v)) childClasses (dpForget childTable v) where
  has_bounded_entry := by
    intro sel h_valid
    obtain ⟨childCost, hget, hbound⟩ := h_child.has_bounded_entry sel h_valid
    obtain ⟨ba_s, hcan_s, hmem_s⟩ := get?_some_toList' childTable _ childCost hget
    have h_entry : ∃ cost', (dpForget childTable v).get?
        (ba_s.filter (fun (cid, _) => cid != v)) = some cost' ∧ cost' ≤ childCost := by
      unfold dpForget; rw [dpTable_fold_eq_list]
      exact foldl_insertMin_entry_bound _ (fun kv => kv.1.filter (fun (cid, _) => cid != v))
        (fun kv => kv.2) DPTable.empty (ba_s, childCost) hmem_s
    obtain ⟨cost', hget', hle'⟩ := h_entry
    have hcan_filter : canonicalizeAssignment (ba_s.filter (fun (cid, _) => cid != v)) =
        canonicalizeAssignment (selectionToBag sel (childBag.filter (· != v))) := by
      rw [← selectionToBag_filter]; exact canon_filter_of_canon_eq hcan_s _
    have hbeq : (canonicalizeAssignment (ba_s.filter (fun (cid, _) => cid != v)) ==
        canonicalizeAssignment (selectionToBag sel (childBag.filter (· != v)))) = true := by
      simp only [BEq.beq]; rw [hcan_filter]; exact list_beq_refl' _
    rw [get?_canon_congr _ _ _ hbeq] at hget'
    exact ⟨cost', hget', Nat.le_trans hle' hbound⟩

/-- **dpIntroduce**: adds v to bag and classes, extending entries. -/
theorem dpIntroduce_DPCompleteInv (g : EGraph Op) (costFn : ENode Op → Nat)
    (v : EClassId) (childBag childClasses : List EClassId)
    (childTable : DPTable)
    (h_child : DPCompleteInv g costFn childBag childClasses childTable)
    (h_cost_concat : ∀ (sel : ENodeSelection),
      selectionCost g sel (childClasses ++ [v]) costFn =
        selectionCost g sel childClasses costFn + selectionCost g sel [v] costFn) :
    DPCompleteInv g costFn (childBag ++ [v]) (childClasses ++ [v])
      (dpIntroduce g childTable v costFn) where
  has_bounded_entry := by
    intro sel h_valid
    have hv := h_valid v (List.mem_append.mpr (Or.inr (List.mem_cons_self)))
    obtain ⟨nidx, hsel_v, hvalid_v⟩ := hv
    have h_vc : ∀ cid ∈ childClasses, ∃ nidx, sel.get? cid = some nidx ∧ nidx ∈ validNodeIndices g cid :=
      fun c hc => h_valid c (List.mem_append.mpr (Or.inl hc))
    obtain ⟨childCost, hget_c, hbound_c⟩ := h_child.has_bounded_entry sel h_vc
    obtain ⟨ba_s, hcan_s, hmem_s⟩ := get?_some_toList' childTable _ childCost hget_c
    have hcan_ext : canonicalizeAssignment (ba_s ++ [(v, nidx)]) =
        canonicalizeAssignment (selectionToBag sel (childBag ++ [v])) := by
      rw [selectionToBag_append sel childBag v nidx hsel_v]
      exact canon_append_congr ba_s (selectionToBag sel childBag) [(v, nidx)] hcan_s
    have h_parent_bound : childCost + nodeCost g v nidx costFn ≤
        selectionCost g sel (childClasses ++ [v]) costFn := by
      rw [h_cost_concat]
      have hsel_v_cost : selectionCost g sel [v] costFn = nodeCost g v nidx costFn := by
        unfold selectionCost; simp only [List.foldl_cons, List.foldl_nil, hsel_v]; omega
      rw [hsel_v_cost]; exact Nat.add_le_add_right hbound_c _
    have h_outer_mono : ∀ (t : DPTable) (kv : BagAssignment × Nat) (ba' : BagAssignment) (c : Nat),
        t.get? ba' = some c →
        ∃ c', ((fun newTable ba cost => (validNodeIndices g v).foldl (fun (acc : DPTable) nodeIdx =>
          if isConsistentWithBag g v nodeIdx ba then
            acc.insertMin (ba ++ [(v, nodeIdx)]) (cost + nodeCost g v nodeIdx costFn)
          else acc) newTable) t kv.1 kv.2).get? ba' = some c' ∧ c' ≤ c :=
      fun t kv ba' c h => intro_inner_mono g v kv.1 kv.2 costFn (validNodeIndices g v) t ba' c h
    have h_creates : ∀ t, ∃ cost,
        ((fun newTable ba cost => (validNodeIndices g v).foldl (fun (acc : DPTable) nodeIdx =>
          if isConsistentWithBag g v nodeIdx ba then
            acc.insertMin (ba ++ [(v, nodeIdx)]) (cost + nodeCost g v nodeIdx costFn)
          else acc) newTable) t ba_s childCost).get? (ba_s ++ [(v, nidx)]) = some cost ∧
        cost ≤ selectionCost g sel (childClasses ++ [v]) costFn :=
      fun t => intro_inner_bounded g v ba_s childCost costFn (validNodeIndices g v) nidx
        hvalid_v hvalid_v (selectionCost g sel (childClasses ++ [v]) costFn) h_parent_bound t
    unfold dpIntroduce; rw [dpTable_fold_eq_list]
    obtain ⟨cost, hcost, hle⟩ := foldl_creates_bounded_entry _ _ h_outer_mono (ba_s, childCost) hmem_s
      (ba_s ++ [(v, nidx)]) (selectionCost g sel (childClasses ++ [v]) costFn) h_creates DPTable.empty
    have hbeq : (canonicalizeAssignment (ba_s ++ [(v, nidx)]) ==
        canonicalizeAssignment (selectionToBag sel (childBag ++ [v]))) = true := by
      simp only [BEq.beq]; rw [hcan_ext]; exact list_beq_refl' _
    rw [get?_canon_congr _ _ _ hbeq] at hcost
    exact ⟨cost, hcost, hle⟩

/-- **dpJoin**: both children share same bag, matching entries combine. -/
theorem dpJoin_DPCompleteInv (g : EGraph Op) (costFn : ENode Op → Nat)
    (bag leftClasses rightClasses parentClasses : List EClassId)
    (leftTable rightTable : DPTable)
    (h_left : DPCompleteInv g costFn bag leftClasses leftTable)
    (h_right : DPCompleteInv g costFn bag rightClasses rightTable)
    (h_parent_left : ∀ c, c ∈ leftClasses → c ∈ parentClasses)
    (h_parent_right : ∀ c, c ∈ rightClasses → c ∈ parentClasses)
    (h_bag_left : ∀ c, c ∈ bag → c ∈ leftClasses)
    (_h_bag_right : ∀ c, c ∈ bag → c ∈ rightClasses)
    (h_cost_decompose : ∀ (sel : ENodeSelection),
      selectionCost g sel parentClasses costFn =
        selectionCost g sel leftClasses costFn + selectionCost g sel rightClasses costFn -
        selectionCost g sel bag costFn) :
    DPCompleteInv g costFn bag parentClasses (dpJoin g leftTable rightTable costFn) where
  has_bounded_entry := by
    intro sel h_valid
    have h_vl : ∀ cid ∈ leftClasses, ∃ nidx, sel.get? cid = some nidx ∧ nidx ∈ validNodeIndices g cid :=
      fun c hc => h_valid c (h_parent_left c hc)
    have h_vr : ∀ cid ∈ rightClasses, ∃ nidx, sel.get? cid = some nidx ∧ nidx ∈ validNodeIndices g cid :=
      fun c hc => h_valid c (h_parent_right c hc)
    obtain ⟨leftCost, hleft, hbl⟩ := h_left.has_bounded_entry sel h_vl
    obtain ⟨rightCost, hright, hbr⟩ := h_right.has_bounded_entry sel h_vr
    obtain ⟨ba_s, hcan_s, hmem_s⟩ := get?_some_toList' leftTable _ leftCost hleft
    have hbeq : (canonicalizeAssignment ba_s == canonicalizeAssignment (selectionToBag sel bag)) = true := by
      simp only [BEq.beq]; rw [hcan_s]; exact list_beq_refl' _
    have hr_ba_s : rightTable.get? ba_s = some rightCost := by
      rw [get?_canon_congr rightTable ba_s (selectionToBag sel bag) hbeq]; exact hright
    have h_bag_valid : ∀ cid ∈ bag, ∃ nidx, sel.get? cid = some nidx := by
      intro cid hc; obtain ⟨nidx, hsel, _⟩ := h_vl cid (h_bag_left cid hc); exact ⟨nidx, hsel⟩
    have hbc : ba_s.foldl (fun acc (cid, nidx) => acc + nodeCost g cid nidx costFn) 0 =
        selectionCost g sel bag costFn := by
      have hperm := perm_of_canon_eq ba_s (selectionToBag sel bag) hcan_s
      have h_eq := bagCostFoldl_perm g ba_s (selectionToBag sel bag) costFn hperm
      have h_sel := selectionCost_eq_bagCost g sel bag costFn h_bag_valid
      show bagCostFoldl g ba_s costFn = selectionCost g sel bag costFn
      rw [h_eq, ← h_sel]
    have h_bound : leftCost + rightCost - selectionCost g sel bag costFn ≤
        selectionCost g sel parentClasses costFn := by
      rw [h_cost_decompose]; exact Nat.sub_le_sub_right (Nat.add_le_add hbl hbr) _
    unfold dpJoin; rw [dpTable_fold_eq_list]
    have h_mono : ∀ (t : DPTable) (kv : BagAssignment × Nat) (ba' : BagAssignment) (c : Nat),
        t.get? ba' = some c →
        ∃ c', (match rightTable.get? kv.1 with
          | some rightCost => let bagCost := kv.1.foldl (fun acc (cid, nidx) => acc + nodeCost g cid nidx costFn) 0
            DPTable.insertMin t kv.1 (kv.2 + rightCost - bagCost) | none => t).get? ba' = some c' ∧ c' ≤ c :=
      fun t kv ba' c h => dpJoin_step_mono g rightTable costFn t kv ba' c h
    have h_creates : ∀ t, ∃ cost,
        (match rightTable.get? ba_s with
          | some rightCost => let bagCost := ba_s.foldl (fun acc (cid, nidx) => acc + nodeCost g cid nidx costFn) 0
            DPTable.insertMin t ba_s (leftCost + rightCost - bagCost) | none => t).get? ba_s = some cost ∧
        cost ≤ selectionCost g sel parentClasses costFn := by
      intro t; rw [hr_ba_s, hbc]
      obtain ⟨c, hc, hle⟩ := insertMin_get_self t ba_s (leftCost + rightCost - selectionCost g sel bag costFn)
      exact ⟨c, hc, Nat.le_trans hle h_bound⟩
    obtain ⟨cost, hcost, hle⟩ := foldl_creates_bounded_entry _ _ h_mono (ba_s, leftCost) hmem_s ba_s
      (selectionCost g sel parentClasses costFn) h_creates DPTable.empty
    refine ⟨cost, ?_, hle⟩
    have hcongr : ∀ (t : DPTable), t.get? ba_s = t.get? (selectionToBag sel bag) :=
      fun t => get?_canon_congr t ba_s (selectionToBag sel bag) hbeq
    rw [← hcongr]; exact hcost

/-! ## ValidNTD: Structural validity for nice tree decompositions -/

/-- A NiceTree of NTDNodeData is structurally valid for DP when each node's
    bag/subtreeClasses relate correctly to its children's data. -/
inductive ValidNTD (g : EGraph Op) (costFn : ENode Op → Nat) :
    NiceTree NTDNodeData → Prop where
  | leaf (nd : NTDNodeData) (hnt : nd.nodeType = .leaf)
      (hbag : nd.bag = []) (hsub : nd.subtreeClasses = []) :
      ValidNTD g costFn (.leaf nd)
  | introduce (nd : NTDNodeData) (child : NiceTree NTDNodeData) (v : EClassId)
      (hnt : nd.nodeType = .introduce v)
      (hbag : nd.bag = child.data.bag ++ [v])
      (hsub : nd.subtreeClasses = child.data.subtreeClasses ++ [v])
      (hchild : ValidNTD g costFn child) :
      ValidNTD g costFn (.unary nd child)
  | forget (nd : NTDNodeData) (child : NiceTree NTDNodeData) (v : EClassId)
      (hnt : nd.nodeType = .forget v)
      (hbag : nd.bag = child.data.bag.filter (· != v))
      (hsub : nd.subtreeClasses = child.data.subtreeClasses)
      (hchild : ValidNTD g costFn child) :
      ValidNTD g costFn (.unary nd child)
  | join (nd : NTDNodeData) (left right : NiceTree NTDNodeData)
      (hnt : nd.nodeType = .join)
      (hbag_l : left.data.bag = nd.bag)
      (hbag_r : right.data.bag = nd.bag)
      (hpl : ∀ c, c ∈ left.data.subtreeClasses → c ∈ nd.subtreeClasses)
      (hpr : ∀ c, c ∈ right.data.subtreeClasses → c ∈ nd.subtreeClasses)
      (hbl : ∀ c, c ∈ nd.bag → c ∈ left.data.subtreeClasses)
      (hbr : ∀ c, c ∈ nd.bag → c ∈ right.data.subtreeClasses)
      (hcost : ∀ (sel : ENodeSelection),
        selectionCost g sel nd.subtreeClasses costFn =
          selectionCost g sel left.data.subtreeClasses costFn +
          selectionCost g sel right.data.subtreeClasses costFn -
          selectionCost g sel nd.bag costFn)
      (hleft : ValidNTD g costFn left) (hright : ValidNTD g costFn right) :
      ValidNTD g costFn (.binary nd left right)

/-! ## runDP reduction lemmas -/

private theorem runDP_leaf (g : EGraph Op) (costFn : ENode Op → Nat)
    (nd : NTDNodeData) (hnt : nd.nodeType = .leaf) :
    runDP g costFn (.leaf nd) = dpLeaf := by
  simp only [runDP, treeFold, hnt]

private theorem runDP_introduce (g : EGraph Op) (costFn : ENode Op → Nat)
    (nd : NTDNodeData) (child : NiceTree NTDNodeData) (v : EClassId)
    (hnt : nd.nodeType = .introduce v) :
    runDP g costFn (.unary nd child) = dpIntroduce g (runDP g costFn child) v costFn := by
  simp only [runDP, treeFold, hnt]

private theorem runDP_forget (g : EGraph Op) (costFn : ENode Op → Nat)
    (nd : NTDNodeData) (child : NiceTree NTDNodeData) (v : EClassId)
    (hnt : nd.nodeType = .forget v) :
    runDP g costFn (.unary nd child) = dpForget (runDP g costFn child) v := by
  simp only [runDP, treeFold, hnt]

private theorem runDP_join (g : EGraph Op) (costFn : ENode Op → Nat)
    (nd : NTDNodeData) (left right : NiceTree NTDNodeData)
    (hnt : nd.nodeType = .join) :
    runDP g costFn (.binary nd left right) =
      dpJoin g (runDP g costFn left) (runDP g costFn right) costFn := by
  simp only [runDP, treeFold, hnt]

/-! ## runDP_DPCompleteInv: Master theorem via ValidNTD induction -/

/-- **runDP produces DPCompleteInv at every level** by induction on ValidNTD.
    Uses the four operation proofs (leaf/forget/introduce/join_DPCompleteInv)
    composed with runDP reduction lemmas. -/
theorem runDP_DPCompleteInv (g : EGraph Op) (costFn : ENode Op → Nat)
    (tree : NiceTree NTDNodeData)
    (hvalid : ValidNTD g costFn tree) :
    DPCompleteInv g costFn tree.data.bag tree.data.subtreeClasses
      (runDP g costFn tree) := by
  induction hvalid with
  | leaf nd hnt hbag hsub =>
    simp only [NiceTree.data, hbag, hsub, runDP_leaf g costFn nd hnt]
    exact dpLeaf_DPCompleteInv g costFn
  | introduce nd child v hnt hbag hsub _hchild ih =>
    simp only [NiceTree.data, hbag, hsub, runDP_introduce g costFn nd child v hnt]
    exact dpIntroduce_DPCompleteInv g costFn v child.data.bag child.data.subtreeClasses
      (runDP g costFn child) ih
      (fun sel => selectionCost_append g sel child.data.subtreeClasses [v] costFn)
  | forget nd child v hnt hbag hsub _hchild ih =>
    simp only [NiceTree.data, hbag, hsub, runDP_forget g costFn nd child v hnt]
    exact dpForget_DPCompleteInv g costFn v child.data.bag child.data.subtreeClasses
      (runDP g costFn child) ih
  | join nd left right hnt hbag_l hbag_r hpl hpr hbl hbr hcost _hleft _hright ihl ihr =>
    simp only [NiceTree.data, runDP_join g costFn nd left right hnt]
    rw [hbag_l] at ihl; rw [hbag_r] at ihr
    exact dpJoin_DPCompleteInv g costFn nd.bag left.data.subtreeClasses right.data.subtreeClasses
      nd.subtreeClasses (runDP g costFn left) (runDP g costFn right)
      ihl ihr hpl hpr hbl hbr hcost

/-! ## dp_optimal_of_validNTD: Composed Public API Theorem -/

/-- **Composed DP optimality theorem.**

    Given a `ValidNTD` proof for a nice tree decomposition, the DP computation
    produces a cost that is ≤ any valid node selection's cost.

    Composes: `runDP_DPCompleteInv` → `dpOptimalityWitness_from_completeInv`
    → `dp_extraction_optimal`. -/
theorem dp_optimal_of_validNTD
    (g : EGraph Op) (costFn : ENode Op → Nat)
    (tree : NiceTree NTDNodeData)
    (hvalid : ValidNTD g costFn tree)
    (hbag_empty : tree.data.bag = [])
    (sel : ENodeSelection)
    (hsel : ∀ cid ∈ tree.data.subtreeClasses,
      ∃ nidx, sel.get? cid = some nidx ∧ nidx ∈ validNodeIndices g cid) :
    dpOptimalCost (runDP g costFn tree) ≤
      selectionCost g sel tree.data.subtreeClasses costFn := by
  have hinv := runDP_DPCompleteInv g costFn tree hvalid
  rw [hbag_empty] at hinv
  exact (dpOptimalityWitness_from_completeInv g costFn tree hinv).dp_is_lower_bound sel hsel

end LambdaSat.DPTableLemmas
