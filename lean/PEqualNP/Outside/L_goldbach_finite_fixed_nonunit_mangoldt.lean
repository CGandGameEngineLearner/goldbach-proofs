import Mathlib.Data.Nat.Log
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

namespace PEqualNP.Outside

/-- The total Mangoldt weight of the nonunit classes modulo `q` up to `n` is at most
`log n` for each distinct prime divisor of `q`. -/
theorem L_goldbach_finite_fixed_nonunit_mangoldt :
    ∀ q n : ℕ, 1 ≤ q → 1 ≤ n →
      (∑ k ∈ (Finset.range (n+1)).filter (fun k => ¬ Nat.Coprime k q),
        ArithmeticFunction.vonMangoldt k) ≤ (q.primeFactors.card:ℝ)*Real.log n := by
  intro q n hq hn
  classical
  let M := ∏ p ∈ q.primeFactors, p ^ Nat.log p n
  have hM : 0 < M := Finset.prod_pos fun p hp => pow_pos (Nat.prime_of_mem_primeFactors hp).pos _
  let S := (Finset.range (n+1)).filter (fun k => ¬ Nat.Coprime k q)
  have hsupport : S.filter (fun k => ArithmeticFunction.vonMangoldt k ≠ 0) ⊆ M.divisors := by
    intro k hk
    obtain ⟨hkS, hweight⟩ := Finset.mem_filter.mp hk
    obtain ⟨hkrange, hnonunit⟩ := Finset.mem_filter.mp hkS
    obtain ⟨p, j, hp, _, rfl⟩ := ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hweight
    have hprime := Nat.prime_iff.mpr hp
    have hdvd : p ∣ q := by
      by_contra h
      exact hnonunit ((hprime.coprime_iff_not_dvd.mpr h).pow_left j)
    have hpq := Nat.mem_primeFactors.mpr ⟨hprime, hdvd, Nat.ne_of_gt hq⟩
    have hj : j ≤ Nat.log p n :=
      Nat.le_log_of_pow_le hprime.one_lt (Finset.mem_range_succ_iff.mp hkrange)
    exact Nat.mem_divisors.mpr ⟨(pow_dvd_pow p hj).trans
      (Finset.dvd_prod_of_mem (fun r => r ^ Nat.log r n) hpq), hM.ne'⟩
  have hbound : M ≤ n ^ q.primeFactors.card := by
    calc
      M ≤ ∏ _p ∈ q.primeFactors, n :=
        Finset.prod_le_prod fun p _ => Nat.pow_log_le_self p (Nat.ne_of_gt hn)
      _ = _ := Finset.prod_const n
  change (∑ k ∈ S, ArithmeticFunction.vonMangoldt k) ≤ _
  rw [← Finset.sum_filter_ne_zero (f := fun k => ArithmeticFunction.vonMangoldt k) S]
  calc
    _ ≤ ∑ k ∈ M.divisors, ArithmeticFunction.vonMangoldt k :=
      Finset.sum_le_sum_of_subset_of_nonneg hsupport fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg
    _ = Real.log M := ArithmeticFunction.vonMangoldt_sum
    _ ≤ Real.log ((n ^ q.primeFactors.card : ℕ) : ℝ) :=
      Real.log_le_log (by exact_mod_cast hM) (by exact_mod_cast hbound)
    _ = _ := by rw [Nat.cast_pow, Real.log_pow]

end PEqualNP.Outside
