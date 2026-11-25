import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

theorem PEqualNP.Outside.L_goldbach_finite_band_fixed_loss_bridge :
    ∀ A B P n a b : ℝ, 0 < n → a-b > 1/10^5 → a*n ≤ A → B ≤ b*n → P ≤ n/10^5 → 0 < A-B-P := by
  intro A B P n a b hn hab hA hB hP
  have hmargin := mul_lt_mul_of_pos_right hab hn
  linarith [show (a - b) * n = a * n - b * n by ring,
    show (1 / 10^5 : ℝ) * n = n / 10^5 by ring]

