import Mathlib
import PEqualNP.Outside.L_twin_primes_window_bridge
import PEqualNP.Outside.L_twin_primes_divisor_bridge
import Conjectures.TwinPrimes.EnergyBridgeV2

-- child 1 zh: 沿无界尺度，异素因子对的质量至多等于对应素数质量。
-- child 1 en: Along unbounded scales the distinct-prime-factor mass is at most the matching prime mass.
-- child 2 zh: 素数质量加上 ε 倍的 X log X 不会变小，故右侧放宽后不等式仍成立。
-- child 2 en: Enlarging the right side by eps times X log X keeps the inequality valid.

theorem Conjectures.Cuts.Cut63b881520dc39cdcdc47ffc5
    (h₁ : have x1 : ℕ → ℝ := fun (x1 : ℕ) => if Nat.Prime (x1 + (2 : ℕ)) then Real.log (↑x1 + (2 : ℝ)) else (0 : ℝ); have x2 : ℕ → ℝ := fun (x2 : ℕ) => ∑ x3 ∈ Finset.range (x2 + (1 : ℕ)), (∑ x4 ∈ x3.divisors with Nat.Prime x4 ∧ Nat.Prime (x3 / x4) ∧ x4 ≠ x3 / x4, Real.log ↑x4 * Real.log ↑(x3 / x4)) * x1 x3; have x3 : ℕ → ℝ := fun (x3 : ℕ) => ∑ x4 ∈ Finset.range (x3 + (1 : ℕ)), (if Nat.Prime x4 then Real.log ↑x4 ^ (2 : ℕ) else (0 : ℝ)) * x1 x4; ∀ (x6 : ℕ), ∃ (x7 : ℕ), x6 < x7 ∧ x2 x7 ≤ x3 x7)
    (h₂ : have x1 : ℕ → ℝ := fun (x1 : ℕ) => if Nat.Prime (x1 + (2 : ℕ)) then Real.log (↑x1 + (2 : ℝ)) else (0 : ℝ); have x2 : ℕ → ℝ := fun (x2 : ℕ) => ∑ x3 ∈ Finset.range (x2 + (1 : ℕ)), (∑ x4 ∈ x3.divisors with Nat.Prime x4 ∧ Nat.Prime (x3 / x4) ∧ x4 ≠ x3 / x4, Real.log ↑x4 * Real.log ↑(x3 / x4)) * x1 x3; have x3 : ℕ → ℝ := fun (x3 : ℕ) => ∑ x4 ∈ Finset.range (x3 + (1 : ℕ)), (if Nat.Prime x4 then Real.log ↑x4 ^ (2 : ℕ) else (0 : ℝ)) * x1 x4; ∀ (x4 : ℝ), (0 : ℝ) < x4 → ∀ (x6 : ℕ), x3 x6 ≤ x3 x6 + x4 * ↑x6 * Real.log ↑x6) :
    (have x1 : ℕ → ℝ := fun (x1 : ℕ) => if Nat.Prime (x1 + (2 : ℕ)) then Real.log (↑x1 + (2 : ℝ)) else (0 : ℝ); have x2 : ℕ → ℝ := fun (x2 : ℕ) => ∑ x3 ∈ Finset.range (x2 + (1 : ℕ)), (∑ x4 ∈ x3.divisors with Nat.Prime x4 ∧ Nat.Prime (x3 / x4) ∧ x4 ≠ x3 / x4, Real.log ↑x4 * Real.log ↑(x3 / x4)) * x1 x3; have x3 : ℕ → ℝ := fun (x3 : ℕ) => ∑ x4 ∈ Finset.range (x3 + (1 : ℕ)), (if Nat.Prime x4 then Real.log ↑x4 ^ (2 : ℕ) else (0 : ℝ)) * x1 x4; ∀ (x4 : ℝ), (0 : ℝ) < x4 → ∀ (x6 : ℕ), ∃ (x7 : ℕ), x6 < x7 ∧ x2 x7 ≤ x3 x7 + x4 * ↑x7 * Real.log ↑x7) := by
  intro eps heps B
  obtain ⟨X, hB, hle⟩ := h₁ B
  exact ⟨X, hB, le_trans hle (h₂ eps heps X)⟩
