import Mathlib

open scoped BigOperators

/-
The truncated Möbius coefficient of Vaughan's identity: on every `a > 1` the
full divisor sum of `μ` vanishes, so the tail above the cutoff `U` equals minus
the short part below `U`.
-/
theorem Conjectures.Goldbach.Type2CornerMoebiusTruncation :
    let μ := fun d : ℕ => ((ArithmeticFunction.moebius d : ℤ) : ℝ)
    ∀ (a U : ℕ), 1 < a →
      (∑ d ∈ (Nat.divisors a).filter (fun d => U < d), μ d)
        = - ∑ d ∈ (Nat.divisors a).filter (fun d => d ≤ U), μ d := by
  intro μ a U ha
  have hne : a ≠ 1 := ne_of_gt ha
  have integerSum : (∑ d ∈ Nat.divisors a, ArithmeticFunction.moebius d) = 0 := by
    rw [← ArithmeticFunction.coe_mul_zeta_apply (f := ArithmeticFunction.moebius) (x := a),
      ArithmeticFunction.moebius_mul_coe_zeta, ArithmeticFunction.one_apply_ne hne]
  have realSum : (∑ d ∈ Nat.divisors a, μ d) = 0 := by
    simp only [μ]
    exact_mod_cast integerSum
  have partition :
      (∑ d ∈ (Nat.divisors a).filter (fun d => U < d), μ d) +
      (∑ d ∈ (Nat.divisors a).filter (fun d => d ≤ U), μ d) = 0 := by
    rw [show (∑ d ∈ (Nat.divisors a).filter (fun d => U < d), μ d) +
        (∑ d ∈ (Nat.divisors a).filter (fun d => d ≤ U), μ d)
        = ∑ d ∈ Nat.divisors a, μ d from by
      simpa only [not_lt] using
        (Finset.sum_filter_add_sum_filter_not (Nat.divisors a) (fun d => U < d) (fun d => μ d))]
    exact realSum
  exact (eq_neg_iff_add_eq_zero).mpr partition
