import Mathlib

theorem Conjectures.Cuts.Task36b77883a4dc046f98a254b7 :
    ∀ (x1 : ℝ) (x2 : ℕ) (x3 : ℂ), ‖x3‖ ≤ x1 * ↑x2 → -(x1 * ↑x2) ≤ x3.re := by
  intro x1 x2 x3 h
  exact (abs_le.mp ((Complex.abs_re_le_norm x3).trans h)).1
