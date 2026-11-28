import Mathlib
import PEqualNP.Outside.L_twin_primes_window_bridge
import PEqualNP.Outside.L_twin_primes_divisor_bridge
import Conjectures.TwinPrimes.EnergyBridgeV2

-- child 1 zh: 实数零非负（占位前提，本题命题本身无条件成立）。
-- child 1 en: Zero is nonnegative in the reals (placeholder premise; the statement holds unconditionally).
-- child 2 zh: 自然数一不小于自身（占位前提，本题命题本身无条件成立）。
-- child 2 en: One is at least itself in the naturals (placeholder premise; the statement holds unconditionally).
-- 本 cut 的直接证明：每一项都非负，故乘积非负。

theorem Conjectures.Cuts.Cuteaff9b6656ad0726bf084d45 (h₁ : (0:ℝ) ≤ 0) (h₂ : (1:ℕ) ≤ 1) : (∀ (x1 : ℕ), (0 : ℝ) ≤ ↑(ArithmeticFunction.moebius x1) ^ (2 : ℕ) * (ArithmeticFunction.vonMangoldt x1 * Real.log ↑x1 + ∑ x2 ∈ x1.divisors, ArithmeticFunction.vonMangoldt x2 * ArithmeticFunction.vonMangoldt (x1 / x2)) * if Nat.Prime (x1 + (2 : ℕ)) then Real.log (↑x1 + (2 : ℝ)) else (0 : ℝ)) := by
  intro n
  have hμ : (0 : ℝ) ≤ ((ArithmeticFunction.moebius n : ℤ) : ℝ) ^ (2 : ℕ) := sq_nonneg _
  have hΛ : ∀ m : ℕ, (0 : ℝ) ≤ ArithmeticFunction.vonMangoldt m :=
    fun m => ArithmeticFunction.vonMangoldt_nonneg
  have hlog : (0 : ℝ) ≤ Real.log (n : ℝ) := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      simp
    · exact Real.log_nonneg (by exact_mod_cast (Nat.succ_le_of_lt h))
  have hsum : (0 : ℝ) ≤ ∑ x2 ∈ n.divisors, ArithmeticFunction.vonMangoldt x2 * ArithmeticFunction.vonMangoldt (n / x2) :=
    Finset.sum_nonneg (fun d _ => mul_nonneg (hΛ d) (hΛ (n / d)))
  have hif : (0 : ℝ) ≤ (if Nat.Prime (n + 2) then Real.log ((n : ℝ) + 2) else (0 : ℝ)) := by
    split_ifs with hp
    · apply Real.log_nonneg
      have h0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    · exact le_refl 0
  exact mul_nonneg (mul_nonneg hμ (add_nonneg (mul_nonneg (hΛ n) hlog) hsum)) hif
