import Mathlib
import PEqualNP.Outside.L_twin_primes_window_bridge
import PEqualNP.Outside.L_twin_primes_divisor_bridge
import Conjectures.TwinPrimes.EnergyBridgeV2

theorem Conjectures.Cuts.Task02eebd9a0cb4aa408e7d075e : (∀ (x1 : ℕ), (0 : ℝ) ≤ ↑(ArithmeticFunction.moebius x1) ^ (2 : ℕ) * (ArithmeticFunction.vonMangoldt x1 * Real.log ↑x1 + ∑ x2 ∈ x1.divisors, ArithmeticFunction.vonMangoldt x2 * ArithmeticFunction.vonMangoldt (x1 / x2)) * if Nat.Prime (x1 + (2 : ℕ)) then Real.log (↑x1 + (2 : ℝ)) else (0 : ℝ)) := by
  intro x1
  refine mul_nonneg (mul_nonneg (sq_nonneg _) ?_) ?_
  · refine add_nonneg (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
      (Real.log_natCast_nonneg x1)) ?_
    exact Finset.sum_nonneg fun d _ =>
      mul_nonneg ArithmeticFunction.vonMangoldt_nonneg ArithmeticFunction.vonMangoldt_nonneg
  · split_ifs
    · exact Real.log_nonneg (by have h : (0:ℝ) ≤ x1 := Nat.cast_nonneg x1; linarith)
    · exact le_rfl
