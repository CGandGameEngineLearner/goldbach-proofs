import Mathlib

theorem Conjectures.Cuts.Taske0618a497d83df2f826e1fd0 : (∀ (x1 : ℕ), ∑ x2 ∈ Finset.range x1 with Nat.Prime x2 ∧ x1 < (3 : ℕ) * x2 ∧ (3 : ℕ) * x2 < (2 : ℕ) * x1 ∧ (1 : ℕ) < x1 - x2 ∧ x1 < (x1 - x2).minFac ^ (5 : ℕ), ↑(ArithmeticFunction.liouville (x1 - x2)) = ↑{x2 ∈ Finset.range x1 | Nat.Prime x2 ∧ x1 < (3 : ℕ) * x2 ∧ (3 : ℕ) * x2 < (2 : ℕ) * x1 ∧ (1 : ℕ) < x1 - x2 ∧ x1 < (x1 - x2).minFac ^ (5 : ℕ)}.card - (2 : ℝ) * ↑{x2 ∈ {x2 ∈ Finset.range x1 | Nat.Prime x2 ∧ x1 < (3 : ℕ) * x2 ∧ (3 : ℕ) * x2 < (2 : ℕ) * x1 ∧ (1 : ℕ) < x1 - x2 ∧ x1 < (x1 - x2).minFac ^ (5 : ℕ)} | Odd (ArithmeticFunction.cardFactors (x1 - x2))}.card) := by
  intro N
  let S := (Finset.range N).filter (fun p => Nat.Prime p ∧ N < 3*p ∧ 3*p < 2*N ∧ 1 < N-p ∧ N < (N-p).minFac^5)
  change ∑ p ∈ S, (ArithmeticFunction.liouville (N-p) : ℝ) = _
  have row (p : ℕ) (hp : p ∈ S) : (ArithmeticFunction.liouville (N-p) : ℝ) =
      1 - 2 * (if Odd (ArithmeticFunction.cardFactors (N-p)) then 1 else 0 : ℝ) := by
    have h : 1 < N-p := (Finset.mem_filter.mp hp).2.2.2.2.1
    rw [ArithmeticFunction.liouville_apply (by omega : N-p ≠ 0)]
    rcases Nat.even_or_odd (ArithmeticFunction.cardFactors (N-p)) with he | ho
    · simp [he.neg_one_pow, (Nat.not_odd_iff_even.mpr he)]
    · simp [ho.neg_one_pow, ho]
      <;> norm_num
  rw [Finset.sum_congr rfl row, Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp [S]
