import Mathlib

namespace PEqualNP.Outside

open scoped BigOperators

theorem L_goldbach_square_norm :
    ∀ (S M : ℂ) (E : ℝ), ‖S-M‖≤E → ‖S^2-M^2‖≤E*(2*‖M‖+E) := by
  intro S M E hE
  have hE0 : 0 ≤ E := le_trans (norm_nonneg (S - M)) hE
  have hshift : ‖S + M‖ ≤ 2 * ‖M‖ + E := by
    have hEq : S + M = (S - M) + 2 * M := by ring
    rw [hEq]
    calc ‖(S - M) + 2 * M‖ ≤ ‖S - M‖ + ‖(2 : ℂ) * M‖ := norm_add_le _ _
      _ = ‖S - M‖ + 2 * ‖M‖ := by rw [norm_mul, Complex.norm_two]
      _ ≤ E + 2 * ‖M‖ := by linarith
      _ = 2 * ‖M‖ + E := by ring
  calc ‖S ^ 2 - M ^ 2‖ = ‖(S - M) * (S + M)‖ := by
        congr 1
        ring
    _ = ‖S - M‖ * ‖S + M‖ := norm_mul _ _
    _ ≤ E * (2 * ‖M‖ + E) := mul_le_mul hE hshift (norm_nonneg _) hE0

end PEqualNP.Outside