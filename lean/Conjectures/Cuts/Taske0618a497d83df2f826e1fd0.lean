import Mathlib

theorem Conjectures.Cuts.Taske0618a497d83df2f826e1fd0 : (∀ (x1 : ℕ), ∑ x2 ∈ Finset.range x1 with Nat.Prime x2 ∧ x1 < (3 : ℕ) * x2 ∧ (3 : ℕ) * x2 < (2 : ℕ) * x1 ∧ (1 : ℕ) < x1 - x2 ∧ x1 < (x1 - x2).minFac ^ (5 : ℕ), ↑(ArithmeticFunction.liouville (x1 - x2)) = ↑{x2 ∈ Finset.range x1 | Nat.Prime x2 ∧ x1 < (3 : ℕ) * x2 ∧ (3 : ℕ) * x2 < (2 : ℕ) * x1 ∧ (1 : ℕ) < x1 - x2 ∧ x1 < (x1 - x2).minFac ^ (5 : ℕ)}.card - (2 : ℝ) * ↑{x2 ∈ {x2 ∈ Finset.range x1 | Nat.Prime x2 ∧ x1 < (3 : ℕ) * x2 ∧ (3 : ℕ) * x2 < (2 : ℕ) * x1 ∧ (1 : ℕ) < x1 - x2 ∧ x1 < (x1 - x2).minFac ^ (5 : ℕ)} | Odd (ArithmeticFunction.cardFactors (x1 - x2))}.card) := by
  classical
  intro n
  let C := (Finset.range n).filter (fun p =>
    Nat.Prime p ∧ n < 3 * p ∧ 3 * p < 2 * n ∧ 1 < n - p ∧ n < (n - p).minFac ^ 5)
  let oddCount (p : ℕ) := Odd (ArithmeticFunction.cardFactors (n - p))
  change (∑ p ∈ C, (ArithmeticFunction.liouville (n - p) : ℝ)) =
    (C.card : ℝ) - 2 * ((C.filter oddCount).card : ℝ)
  calc
    (∑ p ∈ C, (ArithmeticFunction.liouville (n - p) : ℝ)) =
        ∑ p ∈ C, ((1 : ℝ) - 2 * (if oddCount p then 1 else 0)) := by
      refine Finset.sum_congr rfl (fun p hp => ?_)
      have hn : n - p ≠ 0 := by
        have hh := (Finset.mem_filter.mp hp).2.2.2.2.1
        omega
      rw [ArithmeticFunction.liouville_apply hn]
      rcases Nat.even_or_odd (ArithmeticFunction.cardFactors (n - p)) with he | ho
      · rw [he.neg_one_pow]
        simp [oddCount, Nat.not_odd_iff_even.mpr he]
      · rw [ho.neg_one_pow]
        norm_num [oddCount, ho]
    _ = _ := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_filter]
      simp
