import Mathlib

theorem PEqualNP.Outside.L_goldbach_coset_nonunit_bias :
    let w := fun k : ℕ => if k.Prime then Real.log (k:ℝ) else 0
    let F := fun n q r : ℕ => (Finset.range (n+1)).filter (fun k => k%q=r)
    let A := fun n q r : ℕ => ∑ k ∈ F n q r, w k
    ∀ n q r : ℕ, 0<q → r<q → ¬r.Coprime q → A n q r ≤ ∑ p ∈ q.primeFactors, Real.log (p:ℝ) := by
  dsimp only
  intro n q r modulus_pos _ nonunit
  rw [← Finset.sum_filter]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro prime member
    obtain ⟨in_class, is_prime⟩ := Finset.mem_filter.mp member
    have residue : prime % q = r := (Finset.mem_filter.mp in_class).2
    apply Nat.mem_primeFactors.mpr
    refine ⟨is_prime, is_prime.dvd_iff_not_coprime.mpr ?_, modulus_pos.ne'⟩
    intro coprime
    apply nonunit
    rw [← residue]
    change Nat.gcd (prime % q) q = 1
    rw [← Nat.gcd_rec q prime]
    exact coprime.symm
  · intro prime member _
    apply Real.log_nonneg
    exact_mod_cast (Nat.prime_of_mem_primeFactors member).one_le
