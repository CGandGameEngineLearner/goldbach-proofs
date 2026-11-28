import Mathlib
import PEqualNP.Outside.L_twin_primes_window_bridge
import PEqualNP.Outside.L_twin_primes_divisor_bridge
import Conjectures.TwinPrimes.EnergyBridgeV2

-- child 1 en: von Mangoldt's function is nonnegative on every natural number.
-- child 1 zh: von Mangoldt 函数在全体自然数上非负。
-- child 2 en: the real logarithm is nonnegative on every natural number.
-- child 2 zh: 实对数在全体自然数上非负。

theorem Conjectures.Cuts.Cut2f9d9293ee21cde896628e36
    (h₁ : ∀ n : ℕ, 0 ≤ ArithmeticFunction.vonMangoldt n)
    (h₂ : ∀ n : ℕ, 0 ≤ Real.log (n : ℝ)) :
    (∀ (x1 : ℕ), (0 : ℝ) ≤ ↑(ArithmeticFunction.moebius x1) ^ (2 : ℕ) * (ArithmeticFunction.vonMangoldt x1 * Real.log ↑x1 + ∑ x2 ∈ x1.divisors, ArithmeticFunction.vonMangoldt x2 * ArithmeticFunction.vonMangoldt (x1 / x2)) * if Nat.Prime (x1 + (2 : ℕ)) then Real.log (↑x1 + (2 : ℝ)) else (0 : ℝ)) := by
  intro x1
  have hmu : 0 ≤ (ArithmeticFunction.moebius x1 : ℝ) ^ (2 : ℕ) := sq_nonneg _
  have hfirst : 0 ≤ ArithmeticFunction.vonMangoldt x1 * Real.log (x1 : ℝ) :=
    mul_nonneg (h₁ x1) (h₂ x1)
  have hsum : 0 ≤ ∑ x2 ∈ x1.divisors,
      ArithmeticFunction.vonMangoldt x2 * ArithmeticFunction.vonMangoldt (x1 / x2) := by
    exact Finset.sum_nonneg fun x2 hx2 =>
      mul_nonneg (h₁ x2) (h₁ (x1 / x2))
  have hmiddle : 0 ≤ ArithmeticFunction.vonMangoldt x1 * Real.log (x1 : ℝ) +
      ∑ x2 ∈ x1.divisors, ArithmeticFunction.vonMangoldt x2 * ArithmeticFunction.vonMangoldt (x1 / x2) :=
    add_nonneg hfirst hsum
  have hlast : 0 ≤ if Nat.Prime (x1 + 2) then Real.log ((x1 : ℝ) + 2) else 0 := by
    by_cases hp : Nat.Prime (x1 + 2)
    · rw [if_pos hp]
      have hx1 : 1 ≤ x1 + 2 := by omega
      have hxR : (1 : ℝ) ≤ (x1 : ℝ) + 2 := by exact_mod_cast hx1
      exact Real.log_nonneg hxR
    · simp [hp]
  exact mul_nonneg (mul_nonneg hmu hmiddle) hlast
