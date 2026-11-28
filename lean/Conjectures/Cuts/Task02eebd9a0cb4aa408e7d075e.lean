import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

open ArithmeticFunction

theorem Conjectures.Cuts.Task02eebd9a0cb4aa408e7d075e :
  (∀ (x1 : ℕ), (0 : ℝ) ≤ ↑(ArithmeticFunction.moebius x1) ^ (2 : ℕ) * (ArithmeticFunction.vonMangoldt x1 * Real.log ↑x1 + ∑ x2 ∈ x1.divisors, ArithmeticFunction.vonMangoldt x2 * ArithmeticFunction.vonMangoldt (x1 / x2)) * if Nat.Prime (x1 + (2 : ℕ)) then Real.log (↑x1 + (2 : ℝ)) else (0 : ℝ)) := by
  intro n
  have hConvolution :
      0 ≤ ∑ d ∈ n.divisors, vonMangoldt d * vonMangoldt (n / d) :=
    Finset.sum_nonneg fun _ _ => mul_nonneg vonMangoldt_nonneg vonMangoldt_nonneg
  apply mul_nonneg
  · exact mul_nonneg (sq_nonneg _) (add_nonneg
      (mul_nonneg vonMangoldt_nonneg (Real.log_natCast_nonneg n)) hConvolution)
  · split
    · simpa only [Nat.cast_add, Nat.cast_ofNat] using Real.log_natCast_nonneg (n + 2)
    · exact le_rfl
