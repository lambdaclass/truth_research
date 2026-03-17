/-!
# LambdaSat.Util.NatOpt — Nat.min optimization properties

Properties of `Nat.min` critical for DP optimization arguments.
Adapted from VerifiedExtraction/Util/NatOpt.lean (0 sorry, 0 axioms).
-/

namespace LambdaSat.Util.NatOpt

theorem min_le_left (a b : Nat) : Nat.min a b ≤ a := by
  simp only [Nat.min_def]; split <;> omega

theorem min_le_right (a b : Nat) : Nat.min a b ≤ b := by
  simp only [Nat.min_def]; split <;> omega

theorem le_min_iff (a b c : Nat) : c ≤ Nat.min a b ↔ c ≤ a ∧ c ≤ b := by
  constructor
  · intro h; exact ⟨Nat.le_trans h (min_le_left a b), Nat.le_trans h (min_le_right a b)⟩
  · intro ⟨ha, hb⟩; simp only [Nat.min_def]; split <;> omega

theorem min_le_of_le_left {a b c : Nat} (h : a ≤ c) : Nat.min a b ≤ c :=
  Nat.le_trans (min_le_left a b) h

theorem min_le_of_le_right {a b c : Nat} (h : b ≤ c) : Nat.min a b ≤ c :=
  Nat.le_trans (min_le_right a b) h

theorem min_add_right (a b c : Nat) : Nat.min a b + c = Nat.min (a + c) (b + c) := by
  simp only [Nat.min_def]; split <;> split <;> omega

theorem add_min_left (a b c : Nat) : c + Nat.min a b = Nat.min (c + a) (c + b) := by
  simp only [Nat.min_def]; split <;> split <;> omega

theorem add_le_add {a b c d : Nat} (h1 : a ≤ b) (h2 : c ≤ d) : a + c ≤ b + d :=
  Nat.add_le_add h1 h2

theorem min_comm (a b : Nat) : Nat.min a b = Nat.min b a := by
  simp only [Nat.min_def]; split <;> split <;> omega

theorem min_assoc (a b c : Nat) : Nat.min (Nat.min a b) c = Nat.min a (Nat.min b c) := by
  simp only [Nat.min_def]
  repeat (first | split | omega)

theorem min_self (a : Nat) : Nat.min a a = a := by
  simp only [Nat.min_def]; split <;> rfl

end LambdaSat.Util.NatOpt
