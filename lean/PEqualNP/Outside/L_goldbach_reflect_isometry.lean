import Mathlib

/-!
# L-goldbach-reflect-isometry

The reflection `k ↦ n - k` is an involution of the window `range (n + 1)`, so
it preserves the window energy: summing `‖b (n - k)‖^2` enumerates the same
terms as `‖b k‖^2`.
-/

theorem PEqualNP.Outside.L_goldbach_reflect_isometry :
    ∀ (n : ℕ) (b : ℕ → ℂ), (∑ k ∈ Finset.range (n+1), ‖b (n-k)‖^2) = ∑ k ∈ Finset.range (n+1), ‖b k‖^2 := by
  intro n b
  exact Finset.sum_range_reflect (fun j => ‖b j‖^2) (n+1)
