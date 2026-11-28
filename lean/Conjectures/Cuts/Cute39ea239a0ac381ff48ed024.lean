import Mathlib
import PEqualNP.Outside.L_twin_primes_window_bridge
import PEqualNP.Outside.L_twin_primes_divisor_bridge
import Conjectures.TwinPrimes.EnergyBridgeV2

-- child 1 en: a positive constant bounds the absolute value of the weighted rough count at every n.
-- child 1 zh: 存在正数 C，使加权粗糙计数的绝对值在每个 n 上都被 C·n 控制。
-- child 2 en: every natural number is nonnegative as an integer.
-- child 2 zh: 每个自然数作为整数非负。

theorem Conjectures.Cuts.Cute39ea239a0ac381ff48ed024
    (h₁ : ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      |(({x2 ∈ Finset.range (n + (1 : ℕ)) | (1 : ℕ) < x2 ∧ Nat.Prime (x2 + (2 : ℕ)) ∧
          ∀ x3 ∈ x2.divisors, Nat.Prime x3 → n ≤ x3 ^ (10 : ℕ)} : Finset ℕ).card : ℝ) *
          Real.log (n : ℝ) ^ (2 : ℕ)| ≤ C * (n : ℝ))
    (h₂ : ∀ n : ℕ, (0 : ℤ) ≤ (n : ℤ)) :
    (have x1 : ℕ → Finset ℕ := fun (x1 : ℕ) => {x2 ∈ Finset.range (x1 + (1 : ℕ)) | (1 : ℕ) < x2 ∧ Nat.Prime (x2 + (2 : ℕ)) ∧ ∀ x3 ∈ x2.divisors, Nat.Prime x3 → x1 ≤ x3 ^ (10 : ℕ)}; ∃ (x2 : ℝ), (0 : ℝ) < x2 ∧ ∃ (x3 : ℕ), ∀ (x4 : ℕ), x3 ≤ x4 → ↑(x1 x4).card * Real.log ↑x4 ^ (2 : ℕ) ≤ x2 * ↑x4) := by
  obtain ⟨C, hC, hbound⟩ := h₁
  refine ⟨C, hC, 0, ?_⟩
  intro n hn
  have h := hbound n
  have hnonneg : (0 : ℝ) ≤ (({x2 ∈ Finset.range (n + (1 : ℕ)) | (1 : ℕ) < x2 ∧ Nat.Prime (x2 + (2 : ℕ)) ∧
          ∀ x3 ∈ x2.divisors, Nat.Prime x3 → n ≤ x3 ^ (10 : ℕ)} : Finset ℕ).card : ℝ) *
          Real.log (n : ℝ) ^ (2 : ℕ) := by
    exact mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  simpa [abs_of_nonneg hnonneg] using h
