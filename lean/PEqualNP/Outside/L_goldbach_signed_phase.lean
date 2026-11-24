import Mathlib

open scoped BigOperators

theorem PEqualNP.Outside.L_goldbach_signed_phase :
    ∀ (u S M : ℂ) (E : ℝ), ‖u‖=1 → ‖S-M‖≤E → (u*M^2).re-E*(2*‖M‖+E)≤(u*S^2).re := by
  intro u S M E hu hE
  have hsquare : ‖S ^ 2 - M ^ 2‖ ≤ E * (2 * ‖M‖ + E) := by
    have hsum : ‖S + M‖ ≤ 2 * ‖M‖ + E := calc
      ‖S + M‖ = ‖(S - M) + (M + M)‖ := by rw [show S + M = (S - M) + (M + M) by ring]
      _ ≤ ‖S - M‖ + ‖M + M‖ := norm_add_le _ _
      _ ≤ E + (‖M‖ + ‖M‖) := add_le_add hE (norm_add_le M M)
      _ = _ := by ring
    rw [show S ^ 2 - M ^ 2 = (S - M) * (S + M) by ring, Complex.norm_mul]
    exact mul_le_mul hE hsum (norm_nonneg _) ((norm_nonneg _).trans hE)
  have herr : ‖u * S ^ 2 - u * M ^ 2‖ ≤ E * (2 * ‖M‖ + E) := by
    rw [← mul_sub, Complex.norm_mul, hu, one_mul]
    exact hsquare
  have hre : |(u * S ^ 2).re - (u * M ^ 2).re| ≤ E * (2 * ‖M‖ + E) := by
    rw [← Complex.sub_re]
    exact (Complex.abs_re_le_norm _).trans herr
  linarith only [hre, neg_abs_le ((u * S ^ 2).re - (u * M ^ 2).re)]
