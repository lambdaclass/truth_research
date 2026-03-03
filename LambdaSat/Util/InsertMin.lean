import Std.Data.HashMap
import LambdaSat.Util.NatOpt
/-!
# LambdaSat.Util.InsertMin — HashMap min-insert correctness

Theorems about `insertMin`: inserting a value into a HashMap while
keeping the minimum. Used by DPTable construction.
Adapted from VerifiedExtraction/Util/InsertMin.lean (0 sorry, 0 axioms).
-/

namespace LambdaSat.Util.InsertMin

def insertMin {α : Type} [BEq α] [Hashable α]
    (m : Std.HashMap α Nat) (k : α) (v : Nat) : Std.HashMap α Nat :=
  match m.get? k with
  | some old => if v < old then m.insert k v else m
  | none => m.insert k v

theorem insertMin_get_ne {α : Type} [BEq α] [Hashable α]
    [EquivBEq α] [LawfulHashable α]
    (m : Std.HashMap α Nat) (k : α) (v : Nat) (k' : α) (hne : ¬(k == k')) :
    (insertMin m k v).get? k' = m.get? k' := by
  simp only [insertMin]
  split
  · split
    · simp only [Std.HashMap.get?_eq_getElem?]
      rw [Std.HashMap.getElem?_insert]
      simp [hne]
    · rfl
  · simp only [Std.HashMap.get?_eq_getElem?]
    rw [Std.HashMap.getElem?_insert]
    simp [hne]

theorem insertMin_le_new {α : Type} [BEq α] [Hashable α]
    [EquivBEq α] [LawfulHashable α]
    (m : Std.HashMap α Nat) (k : α) (v : Nat) :
    ∃ w, (insertMin m k v).get? k = some w ∧ w ≤ v := by
  simp only [insertMin]
  split
  case h_1 old heq =>
    split
    case isTrue hlt =>
      refine ⟨v, ?_, Nat.le_refl _⟩
      simp only [Std.HashMap.get?_eq_getElem?]
      rw [Std.HashMap.getElem?_insert]
      simp
    case isFalse hge =>
      refine ⟨old, heq, ?_⟩
      omega
  case h_2 =>
    refine ⟨v, ?_, Nat.le_refl _⟩
    simp only [Std.HashMap.get?_eq_getElem?]
    rw [Std.HashMap.getElem?_insert]
    simp

theorem insertMin_le_old {α : Type} [BEq α] [Hashable α]
    [EquivBEq α] [LawfulHashable α]
    (m : Std.HashMap α Nat) (k : α) (v : Nat) (old : Nat)
    (h_old : m.get? k = some old) :
    ∃ w, (insertMin m k v).get? k = some w ∧ w ≤ old := by
  simp only [insertMin, h_old]
  split
  case isTrue hlt =>
    refine ⟨v, ?_, Nat.le_of_lt hlt⟩
    simp only [Std.HashMap.get?_eq_getElem?]
    rw [Std.HashMap.getElem?_insert]
    simp
  case isFalse hge =>
    exact ⟨old, h_old, Nat.le_refl _⟩

theorem insertMin_bound {α : Type} [BEq α] [Hashable α]
    [EquivBEq α] [LawfulHashable α]
    (m : Std.HashMap α Nat) (k : α) (v : Nat)
    (bound : Nat) (hv : bound ≤ v)
    (h_old : ∀ old, m.get? k = some old → bound ≤ old) :
    ∃ w, (insertMin m k v).get? k = some w ∧ bound ≤ w := by
  simp only [insertMin]
  split
  case h_1 old heq =>
    split
    case isTrue hlt =>
      exact ⟨v, by simp only [Std.HashMap.get?_eq_getElem?]; rw [Std.HashMap.getElem?_insert]; simp, hv⟩
    case isFalse hge =>
      exact ⟨old, heq, h_old old heq⟩
  case h_2 =>
    exact ⟨v, by simp only [Std.HashMap.get?_eq_getElem?]; rw [Std.HashMap.getElem?_insert]; simp, hv⟩

end LambdaSat.Util.InsertMin
