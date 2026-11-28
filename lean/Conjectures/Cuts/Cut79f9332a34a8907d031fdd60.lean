import Mathlib
import PEqualNP.Outside.L_twin_primes_window_bridge
import PEqualNP.Outside.L_twin_primes_divisor_bridge
import Conjectures.TwinPrimes.EnergyBridgeV2

-- child 1 zh: 对每个正 ε 与任意截点，存在更晚的 X≥1 使异素因子对质量至多为素数质量加 (ε/2)·X·log X。
-- child 1 en: For every positive eps and cutoff, some later X≥1 has distinct-prime-factor mass at most prime mass plus (eps/2)*X*log X.
-- child 2 zh: 对 X≥1，X·log X 非负，故两边同加素数质量后 (ε/2) 项不超过 ε 项。
-- child 2 en: For X≥1, X*log X is nonnegative, so after adding prime mass the (eps/2) term does not exceed the eps term.

theorem Conjectures.Cuts.Cut79f9332a34a8907d031fdd60
    (h₁ : (let Y1 : ℕ → ℝ := fun (n : ℕ) => if Nat.Prime (n + (2 : ℕ)) then Real.log (↑n + (2 : ℝ)) else (0 : ℝ); let Y2 : ℕ → ℝ := fun (n : ℕ) => ∑ m3 ∈ Finset.range (n + (1 : ℕ)), (∑ m4 ∈ m3.divisors with Nat.Prime m4 ∧ Nat.Prime (m3 / m4) ∧ m4 ≠ m3 / m4, Real.log ↑m4 * Real.log ↑(m3 / m4)) * x1 m3; let Y3 : ℕ → ℝ := fun (n : ℕ) => ∑ m4 ∈ Finset.range (n + (1 : ℕ)), (if Nat.Prime m4 then Real.log ↑m4 ^ (2 : ℕ) else (0 : ℝ)) * x1 m4; ∀ (ε : ℝ), (0 : ℝ) < ε → ∀ (B : ℕ), ∃ (X : ℕ), B < X ∧ 1 ≤ X ∧ Y2 X ≤ Y3 X + (ε / 2) * ↑X * Real.log ↑X))
    (h₂ : (let Y1 : ℕ → ℝ := fun (n : ℕ) => if Nat.Prime (n + (2 : ℕ)) then Real.log (↑n + (2 : ℝ)) else (0 : ℝ); let Y2 : ℕ → ℝ := fun (n : ℕ) => ∑ m3 ∈ Finset.range (n + (1 : ℕ)), (∑ m4 ∈ m3.divisors with Nat.Prime m4 ∧ Nat.Prime (m3 / m4) ∧ m4 ≠ m3 / m4, Real.log ↑m4 * Real.log ↑(m3 / m4)) * x1 m3; let Y3 : ℕ → ℝ := fun (n : ℕ) => ∑ m4 ∈ Finset.range (n + (1 : ℕ)), (if Nat.Prime m4 then Real.log ↑m4 ^ (2 : ℕ) else (0 : ℝ)) * x1 m4; ∀ (ε : ℝ), (0 : ℝ) < ε → ∀ (X : ℕ), 1 ≤ X → Y3 X + (ε / 2) * ↑X * Real.log ↑X ≤ Y3 X + ε * ↑X * Real.log ↑X)) :
    (have x1 : ℕ → ℝ := fun (x1 : ℕ) => if Nat.Prime (x1 + (2 : ℕ)) then Real.log (↑x1 + (2 : ℝ)) else (0 : ℝ); have x2 : ℕ → ℝ := fun (x2 : ℕ) => ∑ x3 ∈ Finset.range (x2 + (1 : ℕ)), (∑ x4 ∈ x3.divisors with Nat.Prime x4 ∧ Nat.Prime (x3 / x4) ∧ x4 ≠ x3 / x4, Real.log ↑x4 * Real.log ↑(x3 / x4)) * x1 x3; have x3 : ℕ → ℝ := fun (x3 : ℕ) => ∑ x4 ∈ Finset.range (x3 + (1 : ℕ)), (if Nat.Prime x4 then Real.log ↑x4 ^ (2 : ℕ) else (0 : ℝ)) * x1 x4; ∀ (x4 : ℝ), (0 : ℝ) < x4 → ∀ (x6 : ℕ), ∃ (x7 : ℕ), x6 < x7 ∧ x2 x7 ≤ x3 x7 + x4 * ↑x7 * Real.log ↑x7) := by
  intro ε hε B
  obtain ⟨X, hBX, h1X, hle⟩ := h₁ ε hε B
  refine ⟨X, hBX, ?_⟩
  exact le_trans hle (h₂ ε hε X h1X)
