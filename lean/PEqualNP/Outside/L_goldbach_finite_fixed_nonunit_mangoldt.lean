import Mathlib

theorem PEqualNP.Outside.L_goldbach_finite_fixed_nonunit_mangoldt :
    ∀ q n : ℕ, 1 ≤ q → 1 ≤ n →
      (∑ k ∈ (Finset.range (n + 1)).filter (fun k => ¬ Nat.Coprime k q),
        ArithmeticFunction.vonMangoldt k) ≤ (q.primeFactors.card : ℝ) * Real.log n := by
  intro q n qPositive nPositive
  have qNonzero : q ≠ 0 := (show 0 < q from qPositive).ne'
  have nNonzero : n ≠ 0 := (show 0 < n from nPositive).ne'
  let nonunits := (Finset.range (n + 1)).filter (fun k => ¬ Nat.Coprime k q)
  let powerProduct := ∏ p ∈ q.primeFactors, p ^ Nat.log p n
  have productPositive : 0 < powerProduct :=
    Finset.prod_pos fun p membership => pow_pos (Nat.prime_of_mem_primeFactors membership).pos _
  have sumOnPrimePowers :
      (∑ k ∈ nonunits.filter IsPrimePow, ArithmeticFunction.vonMangoldt k) =
        ∑ k ∈ nonunits, ArithmeticFunction.vonMangoldt k := by
    refine Finset.sum_subset (Finset.filter_subset _ _) ?_
    intro k membership outsideSupport
    exact ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr fun primePower =>
      outsideSupport (Finset.mem_filter.mpr ⟨membership, primePower⟩)
  have supportSubset : nonunits.filter IsPrimePow ⊆ powerProduct.divisors := by
    intro k membership
    obtain ⟨nonunit, primePower⟩ := Finset.mem_filter.mp membership
    obtain ⟨inRange, notCoprime⟩ := Finset.mem_filter.mp nonunit
    have kLe : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp inRange)
    obtain ⟨p, exponent, prime, _, rfl⟩ := (isPrimePow_nat_iff k).mp primePower
    have dividesModulus : p ∣ q := by
      by_contra doesNotDivide
      exact notCoprime ((prime.coprime_iff_not_dvd.mpr doesNotDivide).pow_left exponent)
    have primeFactor : p ∈ q.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨prime, dividesModulus, qNonzero⟩
    have dividesPower : p ^ exponent ∣ p ^ Nat.log p n :=
      Nat.pow_dvd_pow p (Nat.le_log_of_pow_le prime.one_lt kLe)
    have dividesProduct : p ^ Nat.log p n ∣ powerProduct :=
      Finset.dvd_prod_of_mem (fun p => p ^ Nat.log p n) primeFactor
    exact Nat.mem_divisors.mpr ⟨dividesPower.trans dividesProduct, productPositive.ne'⟩
  change (∑ k ∈ nonunits, ArithmeticFunction.vonMangoldt k) ≤ _
  calc
    _ = ∑ k ∈ nonunits.filter IsPrimePow, ArithmeticFunction.vonMangoldt k := sumOnPrimePowers.symm
    _ ≤ ∑ k ∈ powerProduct.divisors, ArithmeticFunction.vonMangoldt k :=
      Finset.sum_le_sum_of_subset_of_nonneg supportSubset
        (fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg)
    _ = Real.log (powerProduct : ℝ) := ArithmeticFunction.vonMangoldt_sum
    _ = ∑ p ∈ q.primeFactors, Real.log ((p ^ Nat.log p n : ℕ) : ℝ) := by
      change Real.log (↑(∏ p ∈ q.primeFactors, p ^ Nat.log p n) : ℝ) = _
      rw [Nat.cast_prod]
      exact Real.log_prod fun p membership => Nat.cast_ne_zero.mpr
        (pow_ne_zero _ (Nat.prime_of_mem_primeFactors membership).ne_zero)
    _ ≤ ∑ _p ∈ q.primeFactors, Real.log n := by
      apply Finset.sum_le_sum
      intro p membership
      apply Real.log_le_log (Nat.cast_pos.mpr (pow_pos (Nat.prime_of_mem_primeFactors membership).pos _))
      exact_mod_cast Nat.pow_log_le_self p nNonzero
    _ = (q.primeFactors.card : ℝ) * Real.log n := by simp [nsmul_eq_mul]
