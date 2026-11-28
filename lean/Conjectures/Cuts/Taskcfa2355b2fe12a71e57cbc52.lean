import Mathlib

/-!
# Conjectures.Cuts.Taskcfa2355b2fe12a71e57cbc52

Adding the nonnegative distinct-factor mass only increases the total.

The inner sum over divisors with both factors prime and distinct is a sum of
products of two logarithms of primes, hence of nonnegative reals; the weight
`x1` is nonnegative as well.  Therefore `x2 n ≥ 0` for every `n`, and the
goal `x3 n ≤ x2 n + x3 n` is immediate.
-/

theorem Conjectures.Cuts.Taskcfa2355b2fe12a71e57cbc52 :
    have x1 : ℕ → ℝ := fun (x1 : ℕ) => if Nat.Prime (x1 + (2 : ℕ)) then Real.log (↑x1 + (2 : ℝ)) else (0 : ℝ); have x2 : ℕ → ℝ := fun (x2 : ℕ) => ∑ x3 ∈ Finset.range (x2 + (1 : ℕ)), (∑ x4 ∈ x3.divisors with Nat.Prime x4 ∧ Nat.Prime (x3 / x4) ∧ x4 ≠ x3 / x4, Real.log ↑x4 * Real.log ↑(x3 / x4)) * x1 x3; have x3 : ℕ → ℝ := fun (x3 : ℕ) => ∑ x4 ∈ Finset.range (x3 + (1 : ℕ)), (if Nat.Prime x4 then Real.log ↑x4 ^ (2 : ℕ) else (0 : ℝ)) * x1 x4; ∀ (x4 : ℕ), x3 x4 ≤ x2 x4 + x3 x4 := by
  intro x1 x2 x3 x4
  have hx1 : ∀ n : ℕ, 0 ≤ x1 n := by
    intro n
    dsimp only [x1]
    split_ifs
    · refine Real.log_nonneg ?_
      have : (1 : ℕ) ≤ n + 2 := by omega
      exact_mod_cast this
    · norm_num
  have hinner : ∀ n : ℕ, 0 ≤ ∑ d ∈ n.divisors with Nat.Prime d ∧ Nat.Prime (n / d) ∧ d ≠ n / d,
      Real.log (↑d : ℝ) * Real.log (↑(n / d) : ℝ) := by
    intro n
    apply Finset.sum_nonneg
    intro d hd
    rw [Finset.mem_filter] at hd
    have hd1 : Nat.Prime d := hd.2.1
    have hd2 : Nat.Prime (n / d) := hd.2.2.1
    refine mul_nonneg (Real.log_nonneg ?_) (Real.log_nonneg ?_)
    · have : (2 : ℕ) ≤ d := Nat.Prime.two_le hd1
      exact_mod_cast (by omega : (1 : ℕ) ≤ d)
    · have : (2 : ℕ) ≤ n / d := Nat.Prime.two_le hd2
      exact_mod_cast (by omega : (1 : ℕ) ≤ n / d)
  have hx2 : 0 ≤ x2 x4 := by
    dsimp only [x2]
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (hinner i) (hx1 i)
  linarith
