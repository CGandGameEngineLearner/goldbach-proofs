import Mathlib

/-- PREPUB twin-primes cut: `L-twin-primes-cut-0fc3a749df61828316d5d18a`.
For `x3 ≥ 3` the quantity `x3 / (log x3)^2` is nonnegative, so for `x1 ≥ 1` it is at most
`x1` times itself. -/
theorem Conjectures.Cuts.Task0fc3a749df61828316d5d18a :
    ∀ (x1 : ℝ), (1 : ℝ) ≤ x1 → ∀ (x3 : ℕ), (3 : ℕ) ≤ x3 →
      (↑x3 : ℝ) / Real.log ↑x3 ^ (2 : ℕ) ≤ x1 * ((↑x3 : ℝ) / Real.log ↑x3 ^ (2 : ℕ)) := by
  intro x1 hx1 x3 hx3
  have hx3r : (3 : ℝ) ≤ (x3 : ℝ) := by exact_mod_cast hx3
  have hlog : 0 < Real.log (x3 : ℝ) := Real.log_pos (by linarith)
  have hsq : (0 : ℝ) < Real.log (x3 : ℝ) ^ (2 : ℕ) := by positivity
  have hq : (0 : ℝ) < (↑x3 : ℝ) / Real.log ↑x3 ^ (2 : ℕ) := by
    exact div_pos (by linarith) hsq
  nlinarith [hq, hx1]
