import Mathlib

namespace PEqualNP.Outside

theorem L_goldbach_unit_nonempty_even :
    let U := fun q n : ℕ =>
      (Finset.range q).filter (fun a => Nat.Coprime a q ∧ Nat.Coprime (n + q - a) q)
    ∀ q n, 0 < q → Even n → (U q n).Nonempty := by
  dsimp only
  intro q n hq hn
  by_cases hn0 : n = 0
  · subst n
    refine ⟨q - 1, ?_⟩
    simp only [Finset.mem_filter, Finset.mem_range]
    have hqsub : q - (q - 1) = 1 := by omega
    have hc1 : Nat.Coprime (q - 1) q := by
      rw [← Nat.coprime_sub_self_right (by omega : q - 1 ≤ q)]
      simp [hqsub]
    have hc2 : Nat.Coprime (0 + q - (q - 1)) q := by
      rw [show 0 + q - (q - 1) = q - (q - 1) by omega, hqsub]
      simp
    exact ⟨Nat.sub_lt hq (by norm_num), hc1, hc2⟩
  · have hn2dvd : 2 ∣ n := by
      rcases hn with ⟨k, hk⟩
      use k
      omega
    have hn2 : 2 ≤ n := Nat.le_of_dvd (by omega : 0 < n) hn2dvd
    let rs : ℕ → ℕ := fun p => if n ≡ 1 [MOD p] then 2 else 1
    let pf : Finset ℕ := q.primeFactors
    have hp_pos : ∀ p ∈ pf, p ≠ 0 := by
      intro p hp
      exact (Nat.mem_primeFactors.mp hp).1.ne_zero
    have hp_pair : Set.Pairwise (↑pf : Set ℕ) (fun p p' => Nat.Coprime (id p) (id p')) := by
      intro p hp p' hp' hne
      exact (Nat.coprime_primes (Nat.mem_primeFactors.mp hp).1 (Nat.mem_primeFactors.mp hp').1).2 hne
    let zC := Nat.chineseRemainderOfFinset (a := rs) (s := id) pf hp_pos hp_pair
    let z : ℕ := zC
    have hzltprod : (z : ℕ) < ∏ p ∈ pf, p := by
      simpa [z, zC] using Nat.chineseRemainderOfFinset_lt_prod (a := rs) (s := id) hp_pos hp_pair
    have hprod_le : (∏ p ∈ pf, p) ≤ q := by
      exact Nat.le_of_dvd hq (by simpa [pf] using Nat.prod_primeFactors_dvd q)
    have hzltq : z < q := lt_of_lt_of_le hzltprod hprod_le
    have hz_le_nq : z ≤ n + q := by omega
    have hzmod : ∀ p ∈ pf, z ≡ rs p [MOD p] := by
      intro p hp
      simpa [z, zC] using zC.property p hp
    have hnot_rs : ∀ p ∈ pf, ¬ p ∣ rs p := by
      intro p hp hdiv
      have hpp : Nat.Prime p := (Nat.mem_primeFactors.mp hp).1
      by_cases h1 : n ≡ 1 [MOD p]
      · have hdiv2 : p ∣ 2 := by simpa [rs, h1] using hdiv
        have hple2 : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdiv2
        have hp2 : p = 2 := le_antisymm hple2 hpp.two_le
        subst p
        have hnmod0 : n ≡ 0 [MOD 2] := Nat.modEq_zero_iff_dvd.mpr hn2dvd
        have h01 : 0 ≡ 1 [MOD 2] := hnmod0.symm.trans h1
        have hbad : 2 ∣ 1 := (Nat.modEq_iff_dvd' (by norm_num : 0 ≤ 1)).mp h01
        norm_num at hbad
      · have hdiv1 : p ∣ 1 := by simpa [rs, h1] using hdiv
        exact hpp.not_dvd_one hdiv1
    have hnot_z : ∀ p ∈ pf, ¬ p ∣ z := by
      intro p hp hpz
      have hz0 : z ≡ 0 [MOD p] := Nat.modEq_zero_iff_dvd.mpr hpz
      have hrs0 : rs p ≡ 0 [MOD p] := (hzmod p hp).symm.trans hz0
      exact hnot_rs p hp (Nat.modEq_zero_iff_dvd.mp hrs0)
    have hnot_n_rs : ∀ p ∈ pf, ¬ p ∣ n - rs p := by
      intro p hp hdiv
      have hpp : Nat.Prime p := (Nat.mem_primeFactors.mp hp).1
      by_cases h1 : n ≡ 1 [MOD p]
      · have hdiv2 : p ∣ n - 2 := by simpa [rs, h1] using hdiv
        have h2n : 2 ≡ n [MOD p] := (Nat.modEq_iff_dvd' (by omega : 2 ≤ n)).mpr hdiv2
        have h12 : 1 ≡ 2 [MOD p] := h1.symm.trans h2n.symm
        have hbad : p ∣ 1 := (Nat.modEq_iff_dvd' (by norm_num : 1 ≤ 2)).mp h12
        exact hpp.not_dvd_one hbad
      · have hdiv1 : p ∣ n - 1 := by simpa [rs, h1] using hdiv
        have h1n : 1 ≡ n [MOD p] := (Nat.modEq_iff_dvd' (le_trans (by norm_num : 1 ≤ 2) hn2)).mpr hdiv1
        exact h1 h1n.symm
    have hnot_nqz : ∀ p ∈ pf, ¬ p ∣ n + q - z := by
      intro p hp hpdiv
      have hppq : p ∣ q := (Nat.mem_primeFactors.mp hp).2.1
      have hn1 : 1 ≤ n := le_trans (by norm_num : 1 ≤ 2) hn2
      have hrs_le_n : rs p ≤ n := by
        by_cases h1 : n ≡ 1 [MOD p]
        · simpa [rs, h1] using hn2
        · simpa [rs, h1] using hn1
      have hqmod : q ≡ 0 [MOD p] := Nat.modEq_zero_iff_dvd.mpr hppq
      have hnqmod : n + q ≡ n [MOD p] := by
        simpa using (Nat.ModEq.add (Nat.ModEq.refl n) hqmod)
      have hsub : n + q - z ≡ n - rs p [MOD p] :=
        Nat.ModEq.sub hz_le_nq hrs_le_n hnqmod (hzmod p hp)
      have h0 : n + q - z ≡ 0 [MOD p] := Nat.modEq_zero_iff_dvd.mpr hpdiv
      have hr0 : n - rs p ≡ 0 [MOD p] := hsub.symm.trans h0
      exact hnot_n_rs p hp (Nat.modEq_zero_iff_dvd.mp hr0)
    have hcop_z : Nat.Coprime z q := by
      by_contra hc
      rcases Nat.Prime.not_coprime_iff_dvd.mp hc with ⟨p, hpp, hpz, hpq⟩
      have hpmem : p ∈ pf := by
        rw [Nat.mem_primeFactors]
        exact ⟨hpp, hpq, hq.ne'⟩
      exact hnot_z p hpmem hpz
    have hcop_nqz : Nat.Coprime (n + q - z) q := by
      by_contra hc
      rcases Nat.Prime.not_coprime_iff_dvd.mp hc with ⟨p, hpp, hpd, hpq⟩
      have hpmem : p ∈ pf := by
        rw [Nat.mem_primeFactors]
        exact ⟨hpp, hpq, hq.ne'⟩
      exact hnot_nqz p hpmem hpd
    refine ⟨z, ?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hzltq, hcop_z, hcop_nqz⟩

end PEqualNP.Outside
