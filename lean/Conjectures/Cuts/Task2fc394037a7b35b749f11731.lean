import Mathlib
import PEqualNP.Outside.L_twin_primes_window_bridge
import PEqualNP.Outside.L_twin_primes_divisor_bridge
import Conjectures.TwinPrimes.EnergyBridgeV2

theorem Conjectures.Cuts.Task2fc394037a7b35b749f11731 : (∀ (x1 x2 x3 : ℝ), (0 : ℝ) < x1 → (0 : ℝ) ≤ x2 → (0 : ℝ) ≤ x3 → x1 / (2 : ℝ) * x2 * x3 ≤ x1 * x2 * x3) := by
  intro x1 x2 x3 h1 h2 h3
  have h : (0:ℝ) ≤ x1 * x2 * x3 := mul_nonneg (mul_nonneg h1.le h2) h3
  have hr : x1 / 2 * x2 * x3 = 1 / 2 * (x1 * x2 * x3) := by ring
  rw [hr]
  linarith
