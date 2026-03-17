import LambdaSat.Util.NatOpt
/-!
# LambdaSat.Util.FoldMin — List.foldl with Nat.min

Theorems about `List.foldl Nat.min`. The workhorse for dpForget:
minimizing over all choices for a forgotten vertex in the DP table.
Adapted from VerifiedExtraction/Util/FoldMin.lean (0 sorry, 0 axioms).
-/

namespace LambdaSat.Util.FoldMin

open LambdaSat.Util.NatOpt

theorem foldl_min_le_init (l : List Nat) (init : Nat) :
    l.foldl Nat.min init ≤ init := by
  induction l generalizing init with
  | nil => exact Nat.le_refl _
  | cons x xs ih =>
    simp only [List.foldl_cons]
    exact Nat.le_trans (ih _) (min_le_left init x)

theorem foldl_min_le_mem (l : List Nat) (init : Nat) (x : Nat) (hx : x ∈ l) :
    l.foldl Nat.min init ≤ x := by
  induction l generalizing init with
  | nil => contradiction
  | cons y ys ih =>
    simp only [List.foldl_cons, List.mem_cons] at *
    rcases hx with rfl | h
    · exact Nat.le_trans (foldl_min_le_init ys _) (min_le_right init x)
    · exact ih _ h

theorem foldl_min_lower_bound (l : List Nat) (init bound : Nat)
    (h_init : bound ≤ init) (h_all : ∀ x ∈ l, bound ≤ x) :
    bound ≤ l.foldl Nat.min init := by
  induction l generalizing init with
  | nil => exact h_init
  | cons y ys ih =>
    simp only [List.foldl_cons]
    apply ih
    · exact (le_min_iff init y bound).mpr ⟨h_init, h_all y (by simp)⟩
    · exact fun x hx => h_all x (by simp [hx])

theorem foldl_min_map_le {α : Type} (l : List α) (f : α → Nat) (init : Nat)
    (x : α) (hx : x ∈ l) :
    (l.map f).foldl Nat.min init ≤ f x := by
  apply foldl_min_le_mem
  exact List.mem_map.mpr ⟨x, hx, rfl⟩

theorem foldl_min_attained (l : List Nat) (init : Nat) :
    l.foldl Nat.min init = init ∨ ∃ x ∈ l, l.foldl Nat.min init = x := by
  induction l generalizing init with
  | nil => exact Or.inl rfl
  | cons y ys ih =>
    simp only [List.foldl_cons]
    rcases ih (Nat.min init y) with h | ⟨z, hz, heq⟩
    · by_cases hiy : init ≤ y
      · have hmin : Nat.min init y = init := by
          simp only [Nat.min_def]; split <;> omega
        rw [hmin] at h ⊢
        exact Or.inl h
      · have hmin : Nat.min init y = y := by
          simp only [Nat.min_def]; split <;> omega
        rw [hmin] at h ⊢
        exact Or.inr ⟨y, by simp, h⟩
    · exact Or.inr ⟨z, by simp [hz], heq⟩

theorem foldl_min_mono {α : Type} (l : List α) (f g : α → Nat)
    (init_f init_g : Nat)
    (h_init : init_f ≤ init_g)
    (h_fg : ∀ x ∈ l, f x ≤ g x) :
    (l.map f).foldl Nat.min init_f ≤ (l.map g).foldl Nat.min init_g := by
  induction l generalizing init_f init_g with
  | nil => exact h_init
  | cons x xs ih =>
    simp only [List.map_cons, List.foldl_cons]
    apply ih
    · have hfg : f x ≤ g x := h_fg x (by simp)
      simp only [Nat.min_def]; split <;> split <;> omega
    · exact fun y hy => h_fg y (by simp [hy])

end LambdaSat.Util.FoldMin
