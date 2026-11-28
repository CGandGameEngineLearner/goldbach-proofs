import Mathlib
import PEqualNP.Outside.L_twin_primes_window_bridge
import PEqualNP.Outside.L_twin_primes_divisor_bridge
import Conjectures.TwinPrimes.EnergyBridgeV2

-- child 1 zh: 加权 Mertens 和在每个截点都被常数倍的 X 控制。
-- child 1 en: The weighted Mertens sum is bounded by a constant multiple of X at every cutoff.
-- child 2 zh: O(X) 的常数可以随时放大，故前一条的常数即为主命题所需的常数。
-- child 2 en: The constant in an O(X) bound can always be enlarged, so the constant from the first child serves the main claim.

theorem Conjectures.Cuts.Cutbf901f24a78d99f33739f1c2
    (h₁ : ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ, (∑ x3 ∈ Finset.range (X + (1 : ℕ)), ↑(ArithmeticFunction.moebius x3) * (ArithmeticFunction.vonMangoldt x3 * Real.log ↑x3 + ∑ x4 ∈ x3.divisors, ArithmeticFunction.vonMangoldt x4 * ArithmeticFunction.vonMangoldt (x3 / x4)) * if Nat.Prime (x3 + (2 : ℕ)) then Real.log (↑x3 + (2 : ℝ)) else (0 : ℝ)) ≤ C * ↑X)
    (h₂ : ∀ C : ℝ, 0 < C → ∃ C' : ℝ, 0 < C' ∧ ∀ X : ℕ, C * ↑X ≤ C' * ↑X) :
    (∃ (x1 : ℝ), (0 : ℝ) < x1 ∧ ∀ (x2 : ℕ), (∑ x3 ∈ Finset.range (x2 + (1 : ℕ)), ↑(ArithmeticFunction.moebius x3) * (ArithmeticFunction.vonMangoldt x3 * Real.log ↑x3 + ∑ x4 ∈ x3.divisors, ArithmeticFunction.vonMangoldt x4 * ArithmeticFunction.vonMangoldt (x3 / x4)) * if Nat.Prime (x3 + (2 : ℕ)) then Real.log (↑x3 + (2 : ℝ)) else (0 : ℝ)) ≤ x1 * ↑x2) := by
  obtain ⟨C, hC, hS⟩ := h₁
  obtain ⟨C', hC', hle⟩ := h₂ C hC
  refine ⟨C', hC', ?_⟩
  intro X
  exact le_trans (hS X) (hle X)
