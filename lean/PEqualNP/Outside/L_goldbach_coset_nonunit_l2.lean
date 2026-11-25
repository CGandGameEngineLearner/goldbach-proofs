import Mathlib

theorem PEqualNP.Outside.L_goldbach_coset_nonunit_l2 :
    let F := fun n q r : ℕ => (Finset.range (n+1)).filter (fun k => k % q=r); let w := fun k : ℕ => if k.Prime then Real.log (k:ℝ) else 0; let A := fun n q r : ℕ => ∑ k ∈ F n q r, w k; ∀ n q : ℕ, 0<q → (∑ r ∈ (Finset.range q).filter (fun r => ¬r.Coprime q), (A n q r)^2) ≤ (∑ p ∈ q.primeFactors, Real.log (p:ℝ))^2 := by
  intro F w A n q hq
  let bad := (Finset.range q).filter (fun r => ¬r.Coprime q)
  let indices := (Finset.range (n+1)).filter (fun k => k % q ∈ bad)
  have hlog (p : ℕ) (hp : p.Prime) : 0 ≤ Real.log (p : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hp.one_le)
  have hw (k : ℕ) : 0 ≤ w k := by
    change 0 ≤ if k.Prime then Real.log (k : ℝ) else 0
    split_ifs with hk
    · exact hlog k hk
    · exact le_rfl
  have hA (r : ℕ) : 0 ≤ A n q r := Finset.sum_nonneg (fun k _ => hw k)
  have hsubset : indices.filter Nat.Prime ⊆ q.primeFactors := by
    intro k hk
    obtain ⟨hi, hp⟩ := Finset.mem_filter.mp hk
    have hbad := (Finset.mem_filter.mp (Finset.mem_filter.mp hi).2).2
    apply hp.mem_primeFactors _ hq.ne'
    by_contra hnd
    apply hbad
    change Nat.gcd (k % q) q = 1
    rw [← Nat.gcd_rec, Nat.gcd_comm]
    exact hp.coprime_iff_not_dvd.mpr hnd
  have hmass : (∑ r ∈ bad, A n q r) ≤ ∑ p ∈ q.primeFactors, Real.log (p : ℝ) := by
    calc
      _ = ∑ k ∈ indices, w k :=
        Finset.sum_fiberwise_eq_sum_filter (Finset.range (n+1)) bad (fun k => k % q) w
      _ = ∑ p ∈ indices.filter Nat.Prime, Real.log (p : ℝ) := by
        conv_rhs => rw [Finset.sum_filter]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun p hp _ => hlog p (Nat.mem_primeFactors.mp hp).1)
  calc
    _ ≤ (∑ r ∈ bad, A n q r)^2 :=
      Finset.sum_sq_le_sq_sum_of_nonneg (fun r _ => hA r)
    _ ≤ _ := pow_le_pow_left₀ (Finset.sum_nonneg (fun r _ => hA r)) hmass 2
