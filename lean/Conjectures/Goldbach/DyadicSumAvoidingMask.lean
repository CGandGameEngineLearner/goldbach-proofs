import Mathlib

namespace Conjectures.Goldbach

theorem dyadic_sum_avoiding_mask (W : ℕ) (hW : 0 < W) :
    ∃ M : ℕ, 1 < M ∧ Nat.Coprime W M ∧ ∃ S : Finset ℕ, S ⊆ Finset.range M ∧
      M ≤ 8 * S.card ∧ ∀ (a b k : ℕ), a ∈ S → b ∈ S → (a + b) % M ≠ (2 ^ k) % M := by
  rcases eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr hW.ne') with h1 | h2
  · -- W = 1 : M = 3, S = {0}
    subst h1
    refine ⟨3, by decide, by decide, {0}, ?_, ?_, ?_⟩
    · intro x hx
      rw [Finset.mem_singleton] at hx
      subst hx
      simp
    · simp
    · intro a b k ha hb
      rw [Finset.mem_singleton] at ha hb
      subst ha
      subst hb
      have h3 : ¬ (3 ∣ 2 ^ k) := by
        intro hd
        have hp : Nat.Prime 3 := by norm_num
        have h2' : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow hp hd
        have := Nat.le_of_dvd (by norm_num) h2'
        omega
      have hpos : 0 < 2 ^ k % 3 := by
        rcases Nat.eq_zero_or_pos (2 ^ k % 3) with h | h
        · exact absurd (Nat.dvd_of_mod_eq_zero h) h3
        · exact h
      show (0 + 0) % 3 ≠ 2 ^ k % 3
      norm_num
      exact Nat.ne_of_lt hpos
  · -- main case: 2 ≤ W
    have hW2 : 2 ≤ W := h2
    set L : ℕ := Nat.factorial W + 1 with hL
    have hfac2 : 2 ≤ Nat.factorial W :=
      Nat.le_of_dvd (Nat.factorial_pos W) (Nat.dvd_factorial (by norm_num) hW2)
    have hL3 : 3 ≤ L := by
      simp only [hL]
      omega
    set t : ℕ := 2 ^ (L - 3) with ht
    have htpos : 0 < t := by rw [ht]; exact Nat.two_pow_pos _
    have ht1 : 1 ≤ t := htpos
    set M : ℕ := 8 * t - 1 with hM
    have hpowL : 2 ^ L = 8 * t := by
      have hLs : L = (L - 3) + 3 := by omega
      rw [hLs, pow_add, ht]
      norm_num
      ring
    have hML : M = 2 ^ L - 1 := by
      rw [hM, ← hpowL]
    -- key: no prime dividing W divides M
    have key : ∀ p : ℕ, p.Prime → p ∣ W → ¬ p ∣ M := by
      intro p hp hpW hpM
      have hpWle : p ≤ W := Nat.le_of_dvd hW hpW
      have h2L : 2 ^ L ≡ 2 [MOD p] := by
        rcases hp.eq_two_or_odd with h2p | hodd
        · subst h2p
          have hd : 2 ∣ 2 ^ L := by
            exact Nat.pow_dvd_pow 2 (by omega : 1 ≤ L)
          have h0 : 2 ^ L % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp hd
          show 2 ^ L % 2 = 2 % 2
          rw [h0]
        · -- p odd
          have hcop2p : Nat.Coprime 2 p := by
            rw [Nat.coprime_two_left]
            exact Nat.odd_iff.mpr hodd
          have hflt : 2 ^ (p - 1) ≡ 1 [MOD p] := by
            have h := Nat.ModEq.pow_totient hcop2p
            rwa [Nat.totient_prime hp] at h
          have hpdvd : p - 1 ∣ Nat.factorial W := by
            apply Nat.dvd_factorial
            · have := hp.two_le
              omega
            · omega
          obtain ⟨m, hm⟩ := hpdvd
          have hstep : 2 ^ Nat.factorial W ≡ 1 [MOD p] := by
            have h := hflt.pow m
            rw [← pow_mul, one_pow] at h
            rwa [← hm] at h
          have hsplit : 2 ^ L = 2 ^ Nat.factorial W * 2 := by
            rw [hL, pow_succ]
          rw [hsplit]
          simpa using hstep.mul (Nat.ModEq.refl 2)
      have hp1 : 1 ≡ 2 ^ L [MOD p] := by
        rw [Nat.modEq_iff_dvd' (by have := Nat.two_pow_pos L; omega : 1 ≤ 2 ^ L)]
        rw [hML] at hpM
        exact hpM
      have h12 : 1 ≡ 2 [MOD p] := hp1.trans h2L
      have hd1 : p ∣ 1 := by
        rw [Nat.modEq_iff_dvd' (by norm_num : 1 ≤ 2)] at h12
        simpa using h12
      exact hp.not_dvd_one hd1
    have hcop : Nat.Coprime W M := by
      rw [Nat.coprime_iff_gcd_eq_one]
      rcases eq_or_ne (Nat.gcd W M) 1 with hg | hg
      · exact hg
      · exfalso
        obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hg
        exact key p hp (hpd.trans (Nat.gcd_dvd_left W M)) (hpd.trans (Nat.gcd_dvd_right W M))
    have hMgt1 : 1 < M := by
      rw [hM]
      omega
    refine ⟨M, hMgt1, hcop, Finset.Ico (2 * t + 1) (3 * t + 1), ?_, ?_, ?_⟩
    · -- subset of range M
      intro x hx
      rw [Finset.mem_Ico] at hx
      rw [Finset.mem_range, hM]
      omega
    · -- M ≤ 8 * card
      rw [Nat.card_Ico]
      have hcard : 3 * t + 1 - (2 * t + 1) = t := by omega
      rw [hcard, hM]
      omega
    · -- avoid 2^k
      intro a b k ha hb
      rw [Finset.mem_Ico] at ha hb
      have hLpos : 0 < L := by omega
      have hmod' : 1 ≡ 2 ^ L [MOD M] := by
        rw [Nat.modEq_iff_dvd' (by have := Nat.two_pow_pos L; omega : 1 ≤ 2 ^ L)]
        rw [hML]
      have hmod : 2 ^ L ≡ 1 [MOD M] := hmod'.symm
      have hkm : 2 ^ k ≡ 2 ^ (k % L) [MOD M] := by
        have hk : k = k / L * L + k % L := (Nat.div_add_mod k L).symm.trans (by rw [mul_comm])
        conv_lhs => rw [hk]
        rw [pow_add]
        have hp2 : 2 ^ (k / L * L) = (2 ^ L) ^ (k / L) := by
          rw [mul_comm, pow_mul]
        rw [hp2]
        simpa using (hmod.pow (k / L)).mul (Nat.ModEq.refl (2 ^ (k % L)))
      have h4 : 2 ^ (L - 1) = 4 * t := by
        have hs : 2 ^ (L - 1) * 2 = 2 ^ L := by
          rw [← pow_succ, show L - 1 + 1 = L by omega]
        rw [hpowL] at hs
        omega
      have hle4 : 2 ^ (k % L) ≤ 4 * t := by
        have h1 : k % L ≤ L - 1 := by
          have := Nat.mod_lt k hLpos
          omega
        have hd : 2 ^ (k % L) ∣ 2 ^ (L - 1) := Nat.pow_dvd_pow 2 h1
        have hle : 2 ^ (k % L) ≤ 2 ^ (L - 1) := Nat.le_of_dvd (Nat.two_pow_pos _) hd
        rw [h4] at hle
        exact hle
      have hlt : 2 ^ (k % L) < M := by
        rw [hM]
        omega
      have hmodpow : 2 ^ k % M = 2 ^ (k % L) := by
        have h' : 2 ^ k % M = 2 ^ (k % L) % M := hkm
        rw [Nat.mod_eq_of_lt hlt] at h'
        exact h'
      have hltab : a + b < M := by
        rw [hM]
        omega
      have hmodab : (a + b) % M = a + b := Nat.mod_eq_of_lt hltab
      rw [hmodab, hmodpow]
      have hlow : 4 * t + 2 ≤ a + b := by omega
      exact (show 2 ^ (k % L) < a + b by omega).ne'

end Conjectures.Goldbach
