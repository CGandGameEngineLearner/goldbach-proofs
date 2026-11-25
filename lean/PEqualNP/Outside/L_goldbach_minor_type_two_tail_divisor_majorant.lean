import Mathlib

theorem PEqualNP.Outside.L_goldbach_minor_type_two_tail_divisor_majorant :
    ∀ U R : ℕ, |∑ d ∈ R.divisors.filter (fun d => U < d), (ArithmeticFunction.moebius d:ℝ)| ≤ (R.divisors.card:ℝ) := by
  intro U R
  calc |∑ d ∈ R.divisors.filter (fun d => U < d), (ArithmeticFunction.moebius d : ℝ)|
      ≤ ∑ d ∈ R.divisors.filter (fun d => U < d), |(ArithmeticFunction.moebius d : ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ R.divisors.filter (fun d => U < d), (1:ℝ) := by
        apply Finset.sum_le_sum
        intro d _
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
    _ = ((R.divisors.filter (fun d => U < d)).card : ℝ) := by simp
    _ ≤ (R.divisors.card : ℝ) := by
        have h := Finset.card_filter_le (s := R.divisors) (p := fun d => U < d)
        exact_mod_cast h
