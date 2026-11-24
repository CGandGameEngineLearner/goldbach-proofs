import Mathlib

theorem PEqualNP.Outside.L_goldbach_unit_nonempty_even :
    let U := fun q n : ℕ => (Finset.range q).filter (fun a => Nat.Coprime a q ∧ Nat.Coprime (n+q-a) q);
    ∀ q n, 0<q → Even n → (U q n).Nonempty := by
  dsimp only
  -- A residue class that avoids 0 and n modulo every prime dividing the modulus works.
  have key : ∀ (q n : ℕ), (∃ a : ℕ, a < q ∧ ∀ p : ℕ, Nat.Prime p → p ∣ q →
      ¬ p ∣ a ∧ ((a : ZMod p) ≠ (n : ZMod p))) →
      ((Finset.range q).filter (fun a => Nat.Coprime a q ∧ Nat.Coprime (n+q-a) q)).Nonempty := by
    intro q n h
    obtain ⟨a, ha, hap⟩ := h
    have hcop1 : Nat.Coprime a q :=
      (Nat.coprime_of_dvd (fun r hr hrq => (hap r hr hrq).1)).symm
    have hcop2 : Nat.Coprime (n + q - a) q := by
      refine (Nat.coprime_of_dvd ?_).symm
      intro r hr hrq hdvd
      have hzero : ((n + q - a : ℕ) : ZMod r) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hdvd
      have hcast : ((n + q - a : ℕ) : ZMod r) = (n : ZMod r) - (a : ZMod r) := by
        rw [Nat.cast_sub (show a ≤ n + q by omega), Nat.cast_add]
        have hq0 : ((q : ℕ) : ZMod r) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hrq
        rw [hq0]
        ring
      have hna : (n : ZMod r) = (a : ZMod r) := sub_eq_zero.1 (hcast.symm.trans hzero)
      exact (hap r hr hrq).2 hna.symm
    exact ⟨a, Finset.mem_filter.2 ⟨Finset.mem_range.2 ha, hcop1, hcop2⟩⟩
  -- The residue exists: prime powers first, then assembled by the Chinese remainder theorem.
  have main : ∀ q : ℕ, 0 < q → ∀ n : ℕ, Even n → ∃ a : ℕ, a < q ∧ ∀ p : ℕ, Nat.Prime p → p ∣ q →
      ¬ p ∣ a ∧ ((a : ZMod p) ≠ (n : ZMod p)) := by
    intro q
    induction q using Nat.strong_induction_on with
    | ind q ih =>
      intro hq n hn
      rcases Nat.lt_or_ge q 2 with hq2 | hq2
      · have hq1 : q = 1 := by omega
        subst hq1
        refine ⟨0, by omega, ?_⟩
        intro p hp hp1
        exact ⟨fun _ => absurd hp1 hp.not_dvd_one, fun _ => absurd hp1 hp.not_dvd_one⟩
      · have hq0 : q ≠ 0 := by omega
        have hqne1 : q ≠ 1 := by omega
        obtain ⟨p, pp, hpq⟩ := Nat.exists_prime_and_dvd hqne1
        have he1 : 1 ≤ q.factorization p :=
          (Nat.Prime.pow_dvd_iff_le_factorization pp hq0).1 (by simpa using hpq)
        have hpow_dvd : p ^ q.factorization p ∣ q :=
          (Nat.Prime.pow_dvd_iff_le_factorization pp hq0).2 le_rfl
        have hpow_pos : 0 < p ^ q.factorization p := Nat.pow_pos pp.pos
        have hsplit : p ^ q.factorization p * (q / p ^ q.factorization p) = q :=
          Nat.mul_div_cancel' hpow_dvd
        have hpow_ge : 2 ≤ p ^ q.factorization p := by
          have : 1 < p ^ q.factorization p := Nat.one_lt_pow (by omega) pp.one_lt
          omega
        by_cases hk1 : q / p ^ q.factorization p = 1
        · -- q is a prime power: 1 or 2 is a unit that stays away from n
          have hQm : q = p ^ q.factorization p := by
            conv_lhs => rw [← hsplit]
            rw [hk1, Nat.mul_one]
          have hmod2 : n % 2 = 0 := Nat.dvd_iff_mod_eq_zero.1 (even_iff_two_dvd.1 hn)
          by_cases hrem : n % p = 1
          · have hpne : p ≠ 2 := by
              intro h; rw [h] at hrem; omega
            have hp3 : 3 ≤ p := by have := pp.two_le; omega
            have hp_le_pow : p ≤ p ^ q.factorization p := by
              simpa using Nat.pow_le_pow_right pp.pos he1
            have hq3 : 3 ≤ q := by omega
            refine ⟨2, by omega, ?_⟩
            intro r hr hrq
            have hrq' : r ∣ p ^ q.factorization p := by rwa [hQm] at hrq
            have hreq : r = p := ((Nat.dvd_prime pp).1 (Nat.Prime.dvd_of_dvd_pow hr hrq')).resolve_left hr.ne_one
            rw [hreq]
            refine ⟨Nat.not_dvd_of_pos_of_lt (by omega) (by omega), ?_⟩
            intro hcon
            have hmodeq : 2 ≡ n [MOD p] := (ZMod.natCast_eq_natCast_iff 2 n p).1 hcon
            rw [Nat.ModEq, Nat.mod_eq_of_lt (by omega), hrem] at hmodeq
            omega
          · refine ⟨1, by omega, ?_⟩
            intro r hr hrq
            have hrq' : r ∣ p ^ q.factorization p := by rwa [hQm] at hrq
            have hreq : r = p := ((Nat.dvd_prime pp).1 (Nat.Prime.dvd_of_dvd_pow hr hrq')).resolve_left hr.ne_one
            rw [hreq]
            refine ⟨pp.not_dvd_one, ?_⟩
            intro hcon
            have hmodeq : 1 ≡ n [MOD p] := (ZMod.natCast_eq_natCast_iff 1 n p).1 hcon
            rw [Nat.ModEq, Nat.mod_eq_of_lt pp.one_lt] at hmodeq
            omega
        · -- both parts are smaller moduli: combine their residues
          have hk_ge1 : 1 ≤ q / p ^ q.factorization p := by
            have := Nat.div_pos (Nat.le_of_dvd (by omega) hpow_dvd) hpow_pos
            omega
          have hk_ge2 : 2 ≤ q / p ^ q.factorization p := by omega
          have hpow_lt : p ^ q.factorization p < q := by
            have h1 : p ^ q.factorization p * 2 ≤ p ^ q.factorization p * (q / p ^ q.factorization p) :=
              Nat.mul_le_mul_left _ hk_ge2
            rw [hsplit] at h1
            omega
          have hk_lt : q / p ^ q.factorization p < q := by
            have h1 : 2 * (q / p ^ q.factorization p) ≤ p ^ q.factorization p * (q / p ^ q.factorization p) :=
              Nat.mul_le_mul_right _ hpow_ge
            rw [hsplit] at h1
            omega
          obtain ⟨a1, ha1_lt, ha1⟩ := ih (p ^ q.factorization p) hpow_lt hpow_pos n hn
          obtain ⟨a2, ha2_lt, ha2⟩ := ih (q / p ^ q.factorization p) hk_lt (by omega) n hn
          have hcop : (p ^ q.factorization p).Coprime (q / p ^ q.factorization p) := by
            refine Nat.coprime_of_dvd ?_
            intro r hr hrpow hrk
            have h1 : r ∣ p := Nat.Prime.dvd_of_dvd_pow hr hrpow
            have hrp : r = p := ((Nat.dvd_prime pp).1 h1).resolve_left hr.ne_one
            have hrk' : p ∣ q / p ^ q.factorization p := by rwa [hrp] at hrk
            have hbig : p ^ (q.factorization p + 1) ∣ q := by
              rw [Nat.pow_succ]
              have h2 := Nat.mul_dvd_mul_left (p ^ q.factorization p) hrk'
              rwa [hsplit] at h2
            have := (Nat.Prime.pow_dvd_iff_le_factorization pp hq0).1 hbig
            omega
          set z := (Nat.chineseRemainder hcop a1 a2).val with hz
          have hz_lt : z < q := by
            have h := Nat.chineseRemainder_lt_mul hcop a1 a2 (by omega) (by omega)
            rw [hsplit] at h
            exact h
          have hz1 : z ≡ a1 [MOD p ^ q.factorization p] := (Nat.chineseRemainder hcop a1 a2).2.1
          have hz2 : z ≡ a2 [MOD q / p ^ q.factorization p] := (Nat.chineseRemainder hcop a1 a2).2.2
          refine ⟨z, hz_lt, ?_⟩
          intro r hr hrq
          have hprod : r ∣ p ^ q.factorization p ∨ r ∣ q / p ^ q.factorization p := by
            refine (Nat.Prime.dvd_mul hr).1 ?_
            rwa [hsplit]
          rcases hprod with hdiv | hdiv
          · refine ⟨?_, ?_⟩
            · intro hcon
              exact (ha1 r hr hdiv).1 ((Nat.ModEq.dvd_iff hz1 hdiv).1 hcon)
            · intro hcon
              have hmod := Nat.ModEq.of_dvd hdiv hz1
              exact (ha1 r hr hdiv).2 (((ZMod.natCast_eq_natCast_iff _ _ r).2 hmod).symm.trans hcon)
          · refine ⟨?_, ?_⟩
            · intro hcon
              exact (ha2 r hr hdiv).1 ((Nat.ModEq.dvd_iff hz2 hdiv).1 hcon)
            · intro hcon
              have hmod := Nat.ModEq.of_dvd hdiv hz2
              exact (ha2 r hr hdiv).2 (((ZMod.natCast_eq_natCast_iff _ _ r).2 hmod).symm.trans hcon)
  intro q n hq hn
  exact key q n (main q hq n hn)
