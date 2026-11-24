import Mathlib

private lemma pair_lemma_of_le {p k r s : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hk : 0 < k)
    (hsr : s ≤ r) (hrq : r < p ^ k) (hsq : s < p ^ k)
    (hr : p ^ k ∣ r ^ 2 + 1) (hs : p ^ k ∣ s ^ 2 + 1) :
    r = s ∨ r + s = p ^ k := by
  have hk0 : k ≠ 0 := Nat.pos_iff_ne_zero.mp hk
  have hp2le : 2 ≤ p := hp.two_le
  have hpq : p ∣ p ^ k := dvd_pow_self p hk0
  have hqr : p ∣ r ^ 2 + 1 := hpq.trans hr
  have hqs : p ∣ s ^ 2 + 1 := hpq.trans hs
  have hpr : ¬ p ∣ r := by
    intro h
    have h2 : p ∣ r ^ 2 := by simpa [pow_two] using dvd_mul_of_dvd_left h r
    have hone : p ∣ (r ^ 2 + 1) - r ^ 2 := Nat.dvd_sub hqr h2
    have h1 : (r ^ 2 + 1) - r ^ 2 = 1 := by omega
    rw [h1] at hone
    exact hp.not_dvd_one hone
  have hps : ¬ p ∣ s := by
    intro h
    have h2 : p ∣ s ^ 2 := by simpa [pow_two] using dvd_mul_of_dvd_left h s
    have hone : p ∣ (s ^ 2 + 1) - s ^ 2 := Nat.dvd_sub hqs h2
    have h1 : (s ^ 2 + 1) - s ^ 2 = 1 := by omega
    rw [h1] at hone
    exact hp.not_dvd_one hone
  have hrne : r ≠ 0 := by
    intro h0
    have h1 : p ^ k ∣ 1 := by simpa [h0] using hr
    have h2 : 2 ≤ p ^ k := le_trans hp.two_le (Nat.le_self_pow hk0 p)
    have h3 : p ^ k ≤ 1 := Nat.le_of_dvd (by norm_num) h1
    omega
  have hsq : s ^ 2 ≤ r ^ 2 := Nat.pow_le_pow_left hsr 2
  have hdiff0 : p ^ k ∣ (r ^ 2 + 1) - (s ^ 2 + 1) := Nat.dvd_sub hr hs
  have hdiff : p ^ k ∣ r ^ 2 - s ^ 2 := by
    have heq : (r ^ 2 + 1) - (s ^ 2 + 1) = r ^ 2 - s ^ 2 := by omega
    rwa [heq] at hdiff0
  have hfac : r ^ 2 - s ^ 2 = (r + s) * (r - s) := sq_tsub_sq r s
  have hmul : p ^ k ∣ (r + s) * (r - s) := by rw [hfac] at hdiff; exact hdiff
  by_cases hdvd : p ∣ r - s
  · have hpns : ¬ p ∣ r + s := by
      intro hps2
      have h2r : p ∣ 2 * r := by
        have h := Nat.dvd_add hdvd hps2
        have heq : (r - s) + (r + s) = 2 * r := by omega
        rwa [heq] at h
      rcases hp.dvd_mul.mp h2r with h | h
      · have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) h
        omega
      · exact hpr h
    have hcop : Nat.Coprime (p ^ k) (r + s) :=
      Nat.Coprime.pow_left k (hp.coprime_iff_not_dvd.mpr hpns)
    have hdiv : p ^ k ∣ r - s := hcop.dvd_of_dvd_mul_left hmul
    left
    have hlt : r - s < p ^ k := by omega
    have h0 : r - s = 0 := Nat.eq_zero_of_dvd_of_lt hdiv hlt
    omega
  · have hcop : Nat.Coprime (p ^ k) (r - s) :=
      Nat.Coprime.pow_left k (hp.coprime_iff_not_dvd.mpr hdvd)
    have hdiv : p ^ k ∣ r + s := hcop.dvd_of_dvd_mul_right hmul
    right
    have hpos : r + s ≠ 0 := by omega
    have hlt : r + s < 2 * p ^ k := by omega
    exact Nat.eq_of_dvd_of_lt_two_mul hpos hdiv hlt

private lemma pair_lemma {p k r s : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hk : 0 < k)
    (hrq : r < p ^ k) (hsq : s < p ^ k)
    (hr : p ^ k ∣ r ^ 2 + 1) (hs : p ^ k ∣ s ^ 2 + 1) :
    r = s ∨ r + s = p ^ k := by
  rcases le_total s r with hsr | hrs
  · exact pair_lemma_of_le hp hp2 hk hsr hrq hsq hr hs
  · rcases pair_lemma_of_le hp hp2 hk hrs hsq hrq hs hr with h | h
    · exact Or.inl h.symm
    · exact Or.inr (by omega)

theorem PEqualNP.Outside.L_quadratic_primes_prime_power_roots :
    let roots := fun (q : ℕ) => ((Finset.range q).filter (fun r => q ∣ r^2+1)).card; ∀ p k : ℕ, Nat.Prime p → p ≠ 2 → 0 < k → roots (p^k) ≤ 2 := by
  intro roots p k hp hp2 hk
  show ((Finset.range (p ^ k)).filter (fun r => p ^ k ∣ r ^ 2 + 1)).card ≤ 2
  classical
  by_cases hne : ((Finset.range (p ^ k)).filter (fun r => p ^ k ∣ r ^ 2 + 1)).Nonempty
  · obtain ⟨r0, hr0⟩ := hne
    have hr0' := Finset.mem_filter.mp hr0
    have hsub : ((Finset.range (p ^ k)).filter (fun r => p ^ k ∣ r ^ 2 + 1)) ⊆ ({r0, p ^ k - r0} : Finset ℕ) := by
      intro s hs
      have hs' := Finset.mem_filter.mp hs
      have hslt : s < p ^ k := Finset.mem_range.mp hs'.1
      have hrlt : r0 < p ^ k := Finset.mem_range.mp hr0'.1
      have hkey := pair_lemma hp hp2 hk hrlt hslt hr0'.2 hs'.2
      rcases hkey with h | h
      · simp [h]
      · have h2 : s = p ^ k - r0 := by omega
        simp [h2]
    calc ((Finset.range (p ^ k)).filter (fun r => p ^ k ∣ r ^ 2 + 1)).card
        ≤ ({r0, p ^ k - r0} : Finset ℕ).card := Finset.card_le_card hsub
      _ ≤ 2 := by
          have h := Finset.card_insert_le r0 ({p ^ k - r0} : Finset ℕ)
          simp only [Finset.card_singleton] at h
          omega
  · have hempty : ((Finset.range (p ^ k)).filter (fun r => p ^ k ∣ r ^ 2 + 1)) = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hne
    rw [hempty]
    simp
