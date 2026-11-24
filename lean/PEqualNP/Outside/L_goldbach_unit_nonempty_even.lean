import Mathlib

private lemma coprime_congr {a b q : ℕ} (h : a ≡ b [MOD q]) :
    a.Coprime q ↔ b.Coprime q := by
  rw [Nat.coprime_iff_gcd_eq_one, Nat.coprime_iff_gcd_eq_one, h.gcd_eq]

private lemma coprime_shift {m M n a : ℕ} (hm : 0 < m) (ha : a < m * M) :
    (n + m * M - a).Coprime m ↔ (n + m - a % m).Coprime m := by
  have hle1 : a ≤ m * M := le_of_lt ha
  have hle2 : a % m ≤ m := le_of_lt (Nat.mod_lt a hm)
  have hmod : (n + m * M - a) ≡ (n + m - a % m) [MOD m] := by
    have e1 : n + m * M - a = n + (m * M - a) := by omega
    have e2 : n + m - a % m = n + (m - a % m) := by omega
    rw [e1, e2]
    have h1 : m * M ≡ m [MOD m] := by
      show m * M % m = m % m
      rw [Nat.mul_mod_right, Nat.mod_self]
    have h2 : m * M - a ≡ m - a % m [MOD m] :=
      Nat.ModEq.sub hle1 hle2 h1 (Nat.mod_modEq a m).symm
    exact Nat.ModEq.add (Nat.ModEq.refl n) h2
  exact coprime_congr hmod

private lemma prime_residue {p n : ℕ} (hp : Nat.Prime p) (hne : p = 2 → Even n) :
    ∃ r : ℕ, r < p ∧ ¬ p ∣ r ∧ ¬ p ∣ (n + p - r) := by
  have hp2 : 2 ≤ p := hp.two_le
  rcases eq_or_ne p 2 with hp2eq | hp2ne
  · subst hp2eq
    obtain ⟨k, hk⟩ := hne rfl
    refine ⟨1, by norm_num, by norm_num, ?_⟩
    intro h
    have hnk : n + 2 - 1 = k + k + 1 := by omega
    rw [hnk] at h
    have hkk : 2 ∣ k + k := ⟨k, by omega⟩
    have h1 : 2 ∣ (k + k + 1) - (k + k) := Nat.dvd_sub h hkk
    rw [show k + k + 1 - (k + k) = 1 by omega] at h1
    norm_num at h1
  · have hp3 : 3 ≤ p := by omega
    have hpnotdvd2 : ¬ p ∣ 2 := by
      intro h
      have h2 := Nat.le_of_dvd (by norm_num) h
      omega
    by_cases hmod : n % p = 1
    · refine ⟨2, by omega, hpnotdvd2, ?_⟩
      have hnm : n = 1 + p * (n / p) := by
        have := Nat.div_add_mod n p
        rw [hmod] at this
        omega
      have hexp : n + p - 2 = p * (n / p) + (p - 1) := by
        nth_rw 1 [hnm]
        omega
      rw [Nat.dvd_iff_mod_eq_zero, hexp, Nat.mul_add_mod,
        Nat.mod_eq_of_lt (by omega : p - 1 < p)]
      omega
    · refine ⟨1, by omega, ?_, ?_⟩
      · intro h
        have h2 := Nat.dvd_one.mp h
        omega
      · rw [Nat.dvd_iff_mod_eq_zero]
        rcases Nat.eq_zero_or_pos (n % p) with h0 | hpos
        · have hnm : n = p * (n / p) := by
            have h := Nat.div_add_mod n p
            rw [h0] at h
            omega
          have hexp : n + p - 1 = p * (n / p) + (p - 1) := by
            nth_rw 1 [hnm]
            omega
          rw [hexp, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega : p - 1 < p)]
          omega
        · have hnm : n = n % p + p * (n / p) := by
            have h := Nat.div_add_mod n p
            omega
          have hlt : n % p < p := Nat.mod_lt n hp.pos
          have hprod : p * (n / p + 1) = p * (n / p) + p := by ring
          have hp1 : 1 ≤ p := by omega
          have hsub : n % p - 1 + 1 = n % p := Nat.sub_add_cancel hpos
          have hexp : n + p - 1 = p * (n / p + 1) + (n % p - 1) := by
            nth_rw 1 [hnm]
            rw [hprod]
            have e1 : (n % p + p * (n / p)) + p - 1
                = (n % p + p * (n / p)) + (p - 1) := Nat.add_sub_assoc hp1 _
            rw [e1]
            omega
          rw [hexp, Nat.mul_add_mod,
            Nat.mod_eq_of_lt (by omega : n % p - 1 < p)]
          omega

private lemma prime_power_elem {p : ℕ} (hp : Nat.Prime p) {e : ℕ} (he : 1 ≤ e) {n : ℕ}
    (hne : p = 2 → Even n) :
    ∃ a : ℕ, a < p^e ∧ Nat.Coprime a (p^e) ∧ Nat.Coprime (n + p^e - a) (p^e) := by
  obtain ⟨r, hr_lt, hr_notdvd, hnpr⟩ := prime_residue hp hne
  have hpe_ge : p ≤ p^e := Nat.le_self_pow (by omega : e ≠ 0) p
  have hdp : p ∣ p^e - p := by
    apply Nat.dvd_sub
    · rw [show e = e - 1 + 1 by omega, Nat.pow_succ']
      exact dvd_mul_right p _
    · exact dvd_refl p
  have hid : n + p^e - r = (n + p - r) + (p^e - p) := by omega
  refine ⟨r, by omega, ?_, ?_⟩
  · rw [Nat.coprime_pow_right_iff (by omega : 0 < e), Nat.coprime_comm,
      hp.coprime_iff_not_dvd]
    exact hr_notdvd
  · rw [Nat.coprime_pow_right_iff (by omega : 0 < e), Nat.coprime_comm,
      hp.coprime_iff_not_dvd]
    rw [hid, Nat.add_comm (n + p - r) (p^e - p)]
    exact fun h => hnpr ((Nat.dvd_add_iff_right hdp).mpr h)

theorem PEqualNP.Outside.L_goldbach_unit_nonempty_even :
    let U := fun q n : ℕ => (Finset.range q).filter (fun a => Nat.Coprime a q ∧ Nat.Coprime (n+q-a) q); ∀ q n, 0<q → Even n → (U q n).Nonempty := by
  dsimp only
  intro q n hq hne
  revert hq hne
  induction q using Nat.strong_induction_on with
  | _ q ih =>
    intro hq hne
    rcases Nat.eq_or_lt_of_le (show 1 ≤ q from hq) with hq1 | hqgt
    · have hqeq : q = 1 := hq1.symm
      rw [hqeq]
      refine ⟨0, ?_⟩
      simp
    · have hqne : q ≠ 0 := by omega
      have hqne1 : q ≠ 1 := by omega
      obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hqne1
      obtain ⟨e, m, hpm, hqeq⟩ := Nat.exists_eq_pow_mul_and_not_dvd hqne p hp.ne_one
      have he : 1 ≤ e := by
        rcases Nat.eq_zero_or_pos e with h0 | hpos
        · exfalso
          rw [h0, pow_zero, one_mul] at hqeq
          rw [hqeq] at hpdvd
          exact hpm hpdvd
        · exact hpos
      have hpe_ge2 : 2 ≤ p^e := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
      have hm_pos : 0 < m := by
        rcases Nat.eq_zero_or_pos m with h0 | hpos
        · rw [h0, Nat.mul_zero] at hqeq
          omega
        · exact hpos
      have hm_lt : m < p^e * m := by
        have h1 : 2 * m ≤ p^e * m := Nat.mul_le_mul_right m hpe_ge2
        omega
      have hm_lt_q : m < q := by
        rw [hqeq]
        exact hm_lt
      have hcop_pm : (p^e).Coprime m := by
        rw [Nat.coprime_pow_left_iff he]
        exact (hp.coprime_iff_not_dvd).mpr hpm
      obtain ⟨a1, ha1_lt, ha1_cop, ha1_cop2⟩ := prime_power_elem hp he (fun _ => hne)
      obtain ⟨a2, ha2mem⟩ := ih m hm_lt_q hm_pos hne
      have ha2 : a2 < m ∧ Nat.Coprime a2 m ∧ Nat.Coprime (n + m - a2) m := by
        simpa [Finset.mem_filter, Finset.mem_range] using ha2mem
      let hk := Nat.chineseRemainder hcop_pm a1 a2
      let a : ℕ := ↑hk
      have ha1' : a ≡ a1 [MOD p^e] := hk.prop.1
      have ha2' : a ≡ a2 [MOD m] := hk.prop.2
      have ha_lt : a < p^e * m :=
        Nat.chineseRemainder_lt_mul hcop_pm a1 a2 (by omega) (by omega)
      rw [hqeq]
      refine ⟨a, ?_⟩
      simp only [Finset.mem_filter, Finset.mem_range]
      refine ⟨ha_lt, ?_, ?_⟩
      · rw [Nat.coprime_mul_iff_right]
        exact ⟨(coprime_congr ha1').mpr ha1_cop, (coprime_congr ha2').mpr ha2.2.1⟩
      · rw [Nat.coprime_mul_iff_right]
        constructor
        · have hstep : (n + p^e * m - a).Coprime (p^e) ↔
              (n + p^e - a % p^e).Coprime (p^e) :=
            coprime_shift (M := m) (pow_pos hp.pos e) ha_lt
          have hamod : a % p^e = a1 := by
            have h : a % p^e = a1 % p^e := ha1'
            rw [Nat.mod_eq_of_lt ha1_lt] at h
            exact h
          rw [hstep, hamod]
          exact ha1_cop2
        · have hm_lt' : a < m * p^e := by rwa [Nat.mul_comm m (p^e)]
          have hstep : (n + m * p^e - a).Coprime m ↔ (n + m - a % m).Coprime m :=
            coprime_shift (M := p^e) hm_pos hm_lt'
          have hcomm : n + p^e * m - a = n + m * p^e - a := by rw [Nat.mul_comm (p^e) m]
          have hamod : a % m = a2 := by
            have h : a % m = a2 % m := ha2'
            rw [Nat.mod_eq_of_lt ha2.1] at h
            exact h
          rw [hcomm, hstep, hamod]
          exact ha2.2.2
