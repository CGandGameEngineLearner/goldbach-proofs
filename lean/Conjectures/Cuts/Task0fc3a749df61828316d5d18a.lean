import Mathlib

namespace Conjectures.Cuts

/-- For `X ≥ 3` the quantity `X / (log X)^2` is nonnegative (numerator nonnegative, squared
denominator nonnegative), and a real factor `c ≥ 1` dominates it, so `X/(log X)^2 ≤ c·X/(log X)^2`. -/
theorem Task0fc3a749df61828316d5d18a :
    ∀ (x1 : ℝ), (1 : ℝ) ≤ x1 → ∀ (x3 : ℕ), (3 : ℕ) ≤ x3 → ↑x3 / Real.log ↑x3 ^ (2 : ℕ) ≤ x1 * (↑x3 / Real.log ↑x3 ^ (2 : ℕ)) := by
  intro x1 hx1 x3 _
  have hnum : (0 : ℝ) ≤ (x3 : ℝ) := Nat.cast_nonneg x3
  have hden : (0 : ℝ) ≤ Real.log (x3 : ℝ) ^ (2 : ℕ) := sq_nonneg _
  exact le_mul_of_one_le_left (div_nonneg hnum hden) hx1

end Conjectures.Cuts
