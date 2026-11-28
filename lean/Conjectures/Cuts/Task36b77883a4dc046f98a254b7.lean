import Mathlib

theorem Conjectures.Cuts.Task36b77883a4dc046f98a254b7 :
    ∀ (x1 : ℝ) (x2 : ℕ) (x3 : ℂ), ‖x3‖ ≤ x1 * ↑x2 → -(x1 * ↑x2) ≤ x3.re := by
  intro x1 x2 x3 h
  have h1 : |x3.re| ≤ ‖x3‖ := Complex.abs_re_le_norm x3
  have h2 : -‖x3‖ ≤ x3.re := neg_le_of_abs_le h1
  linarith
