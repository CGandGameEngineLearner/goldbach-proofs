import Mathlib

/-- A prime in a nonunit residue class must divide the modulus. -/
theorem PEqualNP.Outside.L_goldbach_coset_nonunit_bias :
    let w := fun k : ℕ => if k.Prime then Real.log (k:ℝ) else 0; let F := fun n q r : ℕ => (Finset.range (n+1)).filter (fun k => k % q = r); let A := fun n q r : ℕ => ∑ k ∈ F n q r, w k; ∀ n q r : ℕ, 0<q → r<q → ¬r.Coprime q → A n q r ≤ ∑ p ∈ q.primeFactors, Real.log (p:ℝ) := by
  classical
  dsimp only
  intro n q r hq _hr hnonunit
  have hsubset :
      ((Finset.range (n + 1)).filter (fun k => k % q = r)).filter Nat.Prime ⊆
        q.primeFactors := by
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hpclass, hprime⟩
    have hresidue := (Finset.mem_filter.mp hpclass).2
    apply hprime.mem_primeFactors ?_ (Nat.ne_of_gt hq)
    apply hprime.dvd_iff_not_coprime.mpr
    intro hcoprime
    apply hnonunit
    rw [← hresidue]
    change Nat.gcd (p % q) q = 1
    rw [← Nat.gcd_rec q p]
    exact hcoprime.symm
  rw [← Finset.sum_filter]
  apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
  intro p hp _
  apply Real.log_nonneg
  exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt.le
