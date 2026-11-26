import Mathlib.Basic.Real.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc

namespace PEqualNP.Outside

/-- On candidates with one or two prime factors counted with multiplicity,
subtracting the parity-weighted sum doubles exactly the prime contributions. -/
theorem L_goldbach_finite_weighted_liouville_selector :
    ∀ (S : Finset ℕ) (n : ℕ) (w : ℕ → ℝ),
      (∀ p ∈ S, 2 ≤ n-p ∧ (n-p).primeFactorsList.length ≤ 2) →
      (∑ p ∈ S, w p) - (∑ p ∈ S, w p*(-1:ℝ)^(n-p).primeFactorsList.length) =
        2*(∑ p ∈ S.filter (fun p => Nat.Prime (n-p)), w p) := by
  intro S n w hS
  rw [← Finset.sum_sub_distrib, Finset.sum_filter, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  obtain ⟨hmin, hmax⟩ := hS p hp
  have hpos : 0 < (n-p).primeFactorsList.length :=
    ArithmeticFunction.cardFactors_pos_iff_one_lt.mpr hmin
  have hone : (n-p).primeFactorsList.length = 1 ↔ Nat.Prime (n-p) :=
    ArithmeticFunction.cardFactors_eq_one_iff_prime
  by_cases hprime : Nat.Prime (n-p)
  · simp [hprime, hone.mpr hprime, two_mul]
  · have htwo : (n-p).primeFactorsList.length = 2 := by
      have := mt hone.mp hprime
      omega
    simp [hprime, htwo]

end PEqualNP.Outside
