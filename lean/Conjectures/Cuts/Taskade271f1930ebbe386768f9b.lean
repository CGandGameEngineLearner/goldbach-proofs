import Mathlib

/- Termwise bound. Inside the strict window, the vonMangoldt product at a twin prime pair n, n+2
equals the log-weight log n times log (n+2), and it is nonnegative at every other integer of the
window; outside the window the log-weighted summand is zero. Summing over the range and folding
the filter therefore gives the inequality. -/

theorem Conjectures.Cuts.Taskade271f1930ebbe386768f9b :
    ∀ (x1 : ℕ), (∑ x2 ∈ Finset.range ((2 : ℕ) * x1 + (1 : ℕ)), if x1 < x2 ∧ (50 : ℕ) * x2 < (51 : ℕ) * x1 ∧ Nat.Prime x2 ∧ Nat.Prime (x2 + (2 : ℕ)) then Real.log ↑x2 * Real.log ↑(x2 + (2 : ℕ)) else (0 : ℝ)) ≤ ∑ x2 ∈ Finset.range ((2 : ℕ) * x1 + (1 : ℕ)) with x1 < x2 ∧ (50 : ℕ) * x2 < (51 : ℕ) * x1, ArithmeticFunction.vonMangoldt x2 * ArithmeticFunction.vonMangoldt (x2 + (2 : ℕ)) := by
  intro X
  rw [Finset.sum_filter]
  refine Finset.sum_le_sum ?_
  intro n _
  by_cases hw : X < n ∧ (50 : ℕ) * n < (51 : ℕ) * X
  · by_cases hp : Nat.Prime n ∧ Nat.Prime (n + 2)
    · have hwp : X < n ∧ (50 : ℕ) * n < (51 : ℕ) * X ∧ Nat.Prime n ∧ Nat.Prime (n + 2) :=
        ⟨hw.1, hw.2, hp.1, hp.2⟩
      rw [ite_eq_left hwp, ite_eq_left hw, ArithmeticFunction.vonMangoldt_apply_prime hp.1,
        ArithmeticFunction.vonMangoldt_apply_prime hp.2]
    · rw [ite_eq_right (fun h => hp h.2.2), ite_eq_left hw]
      exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg ArithmeticFunction.vonMangoldt_nonneg
  · have hnot : ¬ (X < n ∧ (50 : ℕ) * n < (51 : ℕ) * X ∧ Nat.Prime n ∧ Nat.Prime (n + 2)) :=
      fun h => hw ⟨h.1, h.2.1⟩
    rw [ite_eq_right hnot, ite_eq_right hw]
