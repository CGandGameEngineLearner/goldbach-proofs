import Mathlib
import PEqualNP.Outside.L_twin_primes_window_bridge
import PEqualNP.Outside.L_twin_primes_divisor_bridge
import Conjectures.TwinPrimes.EnergyBridgeV2

-- child 1 zh: 加权 Mertens 和有线性上界 sum ≤ C·X。
-- child 1 en: The weighted Mertens sum has a linear upper bound sum ≤ C·X.
-- child 2 zh: 加权 Mertens 和有线性下界 -C·X ≤ sum。
-- child 2 en: The weighted Mertens sum has a linear lower bound -C·X ≤ sum.

theorem Conjectures.Cuts.Cut02e00e143fec3fad726e2d79
    (h₁ : ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ, (∑ x3 ∈ Finset.range (X + (1 : ℕ)), ↑(ArithmeticFunction.moebius x3) * (ArithmeticFunction.vonMangoldt x3 * Real.log ↑x3 + ∑ x4 ∈ x3.divisors, ArithmeticFunction.vonMangoldt x4 * ArithmeticFunction.vonMangoldt (x3 / x4)) * if Nat.Prime (x3 + (2 : ℕ)) then Real.log (↑x3 + (2 : ℝ)) else (0 : ℝ)) ≤ C * ↑X)
    (h₂ : ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ, -C * ↑X ≤ (∑ x3 ∈ Finset.range (X + (1 : ℕ)), ↑(ArithmeticFunction.moebius x3) * (ArithmeticFunction.vonMangoldt x3 * Real.log ↑x3 + ∑ x4 ∈ x3.divisors, ArithmeticFunction.vonMangoldt x4 * ArithmeticFunction.vonMangoldt (x3 / x4)) * if Nat.Prime (x3 + (2 : ℕ)) then Real.log (↑x3 + (2 : ℝ)) else (0 : ℝ))) :
    (∃ (x1 : ℝ), (0 : ℝ) < x1 ∧ ∀ (x2 : ℕ), |∑ x3 ∈ Finset.range (x2 + (1 : ℕ)), ↑(ArithmeticFunction.moebius x3) * (ArithmeticFunction.vonMangoldt x3 * Real.log ↑x3 + ∑ x4 ∈ x3.divisors, ArithmeticFunction.vonMangoldt x4 * ArithmeticFunction.vonMangoldt (x3 / x4)) * if Nat.Prime (x3 + (2 : ℕ)) then Real.log (↑x3 + (2 : ℝ)) else (0 : ℝ)| ≤ x1 * ↑x2) := by
  obtain ⟨C1, hC1, hUp⟩ := h₁
  obtain ⟨C2, hC2, hLo⟩ := h₂
  refine ⟨max C1 C2, lt_of_lt_of_le hC1 (le_max_left _ _), ?_⟩
  intro X
  apply abs_le.mpr
  constructor
  · have h := hLo X
    have hmax : C2 ≤ max C1 C2 := le_max_right _ _
    have hx : (0 : ℝ) ≤ ↑X := by exact_mod_cast Nat.zero_le X
    nlinarith
  · have h := hUp X
    have hmax : C1 ≤ max C1 C2 := le_max_left _ _
    have hx : (0 : ℝ) ≤ ↑X := by exact_mod_cast Nat.zero_le X
    nlinarith
