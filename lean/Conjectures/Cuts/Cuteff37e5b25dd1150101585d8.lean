import Mathlib
import PEqualNP.Outside.L_twin_primes_window_bridge
import PEqualNP.Outside.L_twin_primes_divisor_bridge
import Conjectures.TwinPrimes.EnergyBridgeV2

-- child 1 zh: 半素数加权质量满足一致的塞尔伯格型上界（解析硬核）。
-- child 1 en: The semiprime-weighted mass satisfies a uniform Selberg-type upper bound (the analytic core).
-- child 2 zh: 纯实数缩放事实：正数一半乘两个非负数不超过自身乘积。
-- child 2 en: A pure real scaling fact: half of a positive times two nonnegatives does not exceed the full product.

theorem Conjectures.Cuts.Cuteff37e5b25dd1150101585d8
    (h₁ : ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ X : ℕ, N ≤ X →
      (∑ x3 ∈ Finset.range (X + (1 : ℕ)), (∑ x4 ∈ x3.divisors with Nat.Prime x4 ∧ Nat.Prime (x3 / x4) ∧ x4 ≠ x3 / x4, Real.log ↑x4 * Real.log ↑(x3 / x4)) * (if Nat.Prime (x3 + (2 : ℕ)) then Real.log (↑x3 + (2 : ℝ)) else (0 : ℝ))) ≤
        (∑ x4 ∈ Finset.range (X + (1 : ℕ)), (if Nat.Prime x4 then Real.log ↑x4 ^ (2 : ℕ) else (0 : ℝ)) * (if Nat.Prime (x4 + (2 : ℕ)) then Real.log (↑x4 + (2 : ℝ)) else (0 : ℝ))) + e * ↑X * Real.log ↑X)
    (h₂ : ∀ (e a b : ℝ), 0 < e → 0 ≤ a → 0 ≤ b → e / 2 * a * b ≤ e * a * b) :
    (have x1 : ℕ → ℝ := fun (x1 : ℕ) => if Nat.Prime (x1 + (2 : ℕ)) then Real.log (↑x1 + (2 : ℝ)) else (0 : ℝ); have x2 : ℕ → ℝ := fun (x2 : ℕ) => ∑ x3 ∈ Finset.range (x2 + (1 : ℕ)), (∑ x4 ∈ x3.divisors with Nat.Prime x4 ∧ Nat.Prime (x3 / x4) ∧ x4 ≠ x3 / x4, Real.log ↑x4 * Real.log ↑(x3 / x4)) * x1 x3; have x3 : ℕ → ℝ := fun (x3 : ℕ) => ∑ x4 ∈ Finset.range (x3 + (1 : ℕ)), (if Nat.Prime x4 then Real.log ↑x4 ^ (2 : ℕ) else (0 : ℝ)) * x1 x4; ∀ (x4 : ℝ), (0 : ℝ) < x4 → ∀ (x6 : ℕ), ∃ (x7 : ℕ), x6 < x7 ∧ x2 x7 ≤ x3 x7 + x4 * ↑x7 * Real.log ↑x7) := by
  intro x1 x2 x3 e he B
  have he2 : (0 : ℝ) < e / 2 := by linarith
  obtain ⟨N, hN⟩ := h₁ (e / 2) he2
  refine ⟨max B N + 1, by omega, ?_⟩
  have hX : N ≤ max B N + 1 := by omega
  have hX1 : 1 ≤ max B N + 1 := by omega
  have h1X := hN _ hX
  have hcast : (1 : ℝ) ≤ ↑(max B N + 1) := by exact_mod_cast hX1
  have hscale := h₂ e _ _ he (Nat.cast_nonneg (max B N + 1)) (Real.log_nonneg hcast)
  have hle : (∑ x4 ∈ Finset.range (max B N + 1 + (1 : ℕ)), (if Nat.Prime x4 then Real.log ↑x4 ^ (2 : ℕ) else (0 : ℝ)) * (if Nat.Prime (x4 + (2 : ℕ)) then Real.log (↑x4 + (2 : ℝ)) else (0 : ℝ))) + e / 2 * ↑(max B N + 1) * Real.log ↑(max B N + 1) ≤
      (∑ x4 ∈ Finset.range (max B N + 1 + (1 : ℕ)), (if Nat.Prime x4 then Real.log ↑x4 ^ (2 : ℕ) else (0 : ℝ)) * (if Nat.Prime (x4 + (2 : ℕ)) then Real.log (↑x4 + (2 : ℝ)) else (0 : ℝ))) + e * ↑(max B N + 1) * Real.log ↑(max B N + 1) :=
    add_le_add_right hscale _
  exact le_trans h1X hle
