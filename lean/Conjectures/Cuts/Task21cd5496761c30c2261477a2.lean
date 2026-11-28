import Mathlib

/-- Double counting: the sum over targets of the product of the two band counts equals the
sum over exponent pairs of the simultaneous prime counts. -/
theorem Conjectures.Cuts.Task21cd5496761c30c2261477a2 : (∀ (x1 x2 : ℕ), ∑ x3 ∈ Finset.Ico x1 ((2 : ℕ) * x1), {x4 ∈ Finset.Icc (1 : ℕ) (x2 / (2 : ℕ)) | Nat.Prime (x3 - (2 : ℕ) ^ x4)}.card * {x4 ∈ Finset.Icc (x2 / (2 : ℕ) + (1 : ℕ)) x2 | Nat.Prime (x3 - (2 : ℕ) ^ x4)}.card = ∑ x3 ∈ Finset.Icc (1 : ℕ) (x2 / (2 : ℕ)), ∑ x4 ∈ Finset.Icc (x2 / (2 : ℕ) + (1 : ℕ)) x2, {x5 ∈ Finset.Ico x1 ((2 : ℕ) * x1) | Nat.Prime (x5 - (2 : ℕ) ^ x3) ∧ Nat.Prime (x5 - (2 : ℕ) ^ x4)}.card) := by
  classical
  intro x1 x2
  conv_lhs => simp only [Finset.card_eq_sum_ones, Finset.sum_mul_sum, Finset.sum_filter, mul_one,
    mul_zero, Finset.sum_const_zero, mul_ite, Finset.sum_ite_irrel]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro m _
  by_cases h1 : Nat.Prime (m - 2^a) <;> by_cases h2 : Nat.Prime (m - 2^b) <;> simp [h1, h2]
