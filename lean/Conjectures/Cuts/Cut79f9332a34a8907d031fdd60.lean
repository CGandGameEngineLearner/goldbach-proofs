import Mathlib
import PEqualNP.Outside.L_twin_primes_window_bridge
import PEqualNP.Outside.L_twin_primes_divisor_bridge
import Conjectures.TwinPrimes.EnergyBridgeV2

-- child 1 zh: 对每个正 ε 与任意截点，存在更晚的 X≥1 使异素因子对质量至多为素数质量加 (ε/2)·X·log X。
-- child 1 en: For every positive eps and cutoff, some later X≥1 has distinct-prime-factor mass at most prime mass plus (eps/2)*X*log X.
-- child 2 zh: 对 X≥1，X·log X 非负，故 (ε/2)·X·log X 不超过 ε·X·log X。
-- child 2 en: For X≥1 the quantity X*log X is nonnegative, so (eps/2)*X*log X is at most eps*X*log X.

theorem Conjectures.Cuts.Cut79f9332a34a8907d031fdd60
    (h₁ : (have x1 : ℕ → ℝ := fun (x1 : ℕ) => if Nat.Prime (x1 + (2 : ℕ)) then Real.log (↑x1 + (2 : ℝ)) else (0 : ℝ); have x2 : ℕ → ℝ := fun (x2 : ℕ) => ∑ x3 ∈ Finset.range (x2 + (1 : ℕ)), (∑ x4 ∈ x3.divisors with Nat.Prime x4 ∧ Nat.Prime (x3 / x4) ∧ x4 ≠ x3 / x4, Real.log ↑x4 * Real.log ↑(x3 / x4)) * x1 x3; have x3 : ℕ → ℝ := fun (x3 : ℕ) => ∑ x4 ∈ Finset.range (x3 + (1 : ℕ)), (if Nat.Prime x4 then Real.log ↑x4 ^ (2 : ℕ) else (0 : ℝ)) * x1 x4; ∀ (x4 : ℝ), (0 : ℝ) < x4 → ∀ (x6 : ℕ), ∃ (x7 : ℕ), x6 < x7 ∧ 1 ≤ x7 ∧ x2 x7 ≤ x3 x7 + (x4 / 2) * ↑x7 * Real.log ↑x7))
    (h₂ : ∀ (x4 : ℝ), (0 : ℝ) < x4 → ∀ (x7 : ℕ), 1 ≤ x7 → (x4 / 2) * ↑x7 * Real.log ↑x7 ≤ x4 * ↑x7 * Real.log ↑x7) :
    (have x1 : ℕ → ℝ := fun (x1 : ℕ) => if Nat.Prime (x1 + (2 : ℕ)) then Real.log (↑x1 + (2 : ℝ)) else (0 : ℝ); have x2 : ℕ → ℝ := fun (x2 : ℕ) => ∑ x3 ∈ Finset.range (x2 + (1 : ℕ)), (∑ x4 ∈ x3.divisors with Nat.Prime x4 ∧ Nat.Prime (x3 / x4) ∧ x4 ≠ x3 / x4, Real.log ↑x4 * Real.log ↑(x3 / x4)) * x1 x3; have x3 : ℕ → ℝ := fun (x3 : ℕ) => ∑ x4 ∈ Finset.range (x3 + (1 : ℕ)), (if Nat.Prime x4 then Real.log ↑x4 ^ (2 : ℕ) else (0 : ℝ)) * x1 x4; ∀ (x4 : ℝ), (0 : ℝ) < x4 → ∀ (x6 : ℕ), ∃ (x7 : ℕ), x6 < x7 ∧ x2 x7 ≤ x3 x7 + x4 * ↑x7 * Real.log ↑x7) := by
  intro ε hε B
  obtain ⟨X, hBX, h1X, hle⟩ := h₁ ε hε B
  refine ⟨X, hBX, ?_⟩
  exact le_trans hle (h₂ ε hε X h1X)
