import Mathlib

theorem PEqualNP.Outside.L_goldbach_square_norm :
    ∀ (S M : ℂ) (E : ℝ), ‖S - M‖ ≤ E → ‖S ^ 2 - M ^ 2‖ ≤ E * (2 * ‖M‖ + E) := by
  intro S M E hE
  have hadd : S + M = (S - M) + (M + M) := by ring
  have hplus : ‖S + M‖ ≤ 2 * ‖M‖ + E := by
    rw [hadd]
    calc
      ‖(S - M) + (M + M)‖ ≤ ‖S - M‖ + ‖M + M‖ := norm_add_le _ _
      _ ≤ E + (‖M‖ + ‖M‖) := add_le_add hE (norm_add_le M M)
      _ = 2 * ‖M‖ + E := by ring
  have hfactor : S ^ 2 - M ^ 2 = (S - M) * (S + M) := by ring
  rw [hfactor, norm_mul]
  exact mul_le_mul hE hplus (norm_nonneg _) ((norm_nonneg _).trans hE)
