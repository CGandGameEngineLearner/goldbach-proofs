import Mathlib

theorem Conjectures.Cuts.Taskade271f1930ebbe386768f9b :
    ∀ (x1 : ℕ), (∑ x2 ∈ Finset.range ((2 : ℕ) * x1 + (1 : ℕ)), if x1 < x2 ∧ (50 : ℕ) * x2 < (51 : ℕ) * x1 ∧ Nat.Prime x2 ∧ Nat.Prime (x2 + (2 : ℕ)) then Real.log ↑x2 * Real.log ↑(x2 + (2 : ℕ)) else (0 : ℝ)) ≤ ∑ x2 ∈ Finset.range ((2 : ℕ) * x1 + (1 : ℕ)) with x1 < x2 ∧ (50 : ℕ) * x2 < (51 : ℕ) * x1, ArithmeticFunction.vonMangoldt x2 * ArithmeticFunction.vonMangoldt (x2 + (2 : ℕ)) := by
  intro X
  rw [Finset.sum_filter]
  apply Finset.sum_le_sum
  intro n _
  by_cases h₁ : X < n
  · by_cases h₂ : 50*n < 51*X
    · simp only [h₁, h₂, true_and, if_true]
      by_cases hp : Nat.Prime n ∧ Nat.Prime (n+2)
      · rw [if_pos hp, ArithmeticFunction.vonMangoldt_apply_prime hp.1,
          ArithmeticFunction.vonMangoldt_apply_prime hp.2]
      · rw [if_neg hp]
        exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg ArithmeticFunction.vonMangoldt_nonneg
    · simp [h₂]
  · simp [h₁]
