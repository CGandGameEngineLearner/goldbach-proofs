import Mathlib

open scoped BigOperators

theorem Conjectures.Goldbach.DyadicSumAvoidingMask :
    ∀ W : ℕ, 0 < W → ∃ M : ℕ, 1 < M ∧ Nat.Coprime W M ∧ ∃ S : Finset ℕ, S ⊆ Finset.range M ∧ M ≤ 8 * S.card ∧ ∀ (a b k : ℕ), a ∈ S → b ∈ S → (a+b)%M ≠ (2^k)%M := by
  intro W hW
  -- Step 1: a prime s strictly larger than W and 5.
  obtain ⟨s, hs_ge, hs_prime⟩ := Nat.exists_infinite_primes (max W 5 + 1)
  have hWs : W < s := by
    have h1 : W ≤ max W 5 := le_max_left W 5
    omega
  have hs5 : 5 < s := by
    have h1 : 5 ≤ max W 5 := le_max_right W 5
    omega
  have hs3 : 3 ≤ s := by omega
  have hs6 : 6 ≤ s := by omega
  have hspos : 0 < s := by omega
  -- Step 2: L = 2^(s-3), M = 8L-1 = 2^s - 1, S = [3L, 4L-1].
  set L : ℕ := 2 ^ (s - 3) with hL
  set M : ℕ := 8 * L - 1 with hM
  set S : Finset ℕ := Finset.Icc (3 * L) (4 * L - 1) with hS
  have hLpos : 0 < L := by rw [hL]; positivity
  have h2s : 2 ^ s = 8 * L := by
    rw [show (8 : ℕ) = 2 ^ 3 by norm_num, hL, ← pow_add]
    congr 1
    omega
  have hMeq : M = 2 ^ s - 1 := by rw [hM, h2s]
  have h2s_ge : 64 ≤ 2 ^ s := by
    have h := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hs6
    simpa using h
  have hMgt1 : 1 < M := by rw [hMeq]; omega
  -- Step 3: coprimality.
  have hcop : Nat.Coprime W M := by
    by_contra hcon
    have hgcd_ne : Nat.gcd W M ≠ 1 := fun h => hcon ((Nat.coprime_iff_gcd_eq_one).mpr h)
    have hgcd_pos : 0 < Nat.gcd W M := Nat.gcd_pos_of_pos_left M hW
    have hgcd_gt : 1 < Nat.gcd W M := by omega
    obtain ⟨p, hp_prime, hp_dvd_g⟩ := Nat.exists_prime_and_dvd (n := Nat.gcd W M) hgcd_ne
    have hp_dvd_W : p ∣ W := dvd_trans hp_dvd_g (Nat.gcd_dvd_left W M)
    have hp_dvd_M : p ∣ M := dvd_trans hp_dvd_g (Nat.gcd_dvd_right W M)
    have hpW : p ≤ W := Nat.le_of_dvd hW hp_dvd_W
    have hd : p ∣ 2 ^ s - 1 := by rw [← hMeq]; exact hp_dvd_M
    -- p is odd, since 2^s - 1 is odd.
    have hp2 : p ≠ 2 := by
      rintro rfl
      obtain ⟨t, ht⟩ := hd
      have h2sp : 2 ^ s = 2 * 2 ^ (s - 1) := by
        rw [← pow_succ']
        congr 1
        omega
      have hy : 1 ≤ 2 ^ (s - 1) := Nat.one_le_two_pow
      omega
    -- In ZMod p: 2^s = 1.
    have hzero : ((2 ^ s - 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff (2 ^ s - 1) p).mpr hd
    have hsub : ((2 ^ s : ℕ) : ZMod p) - 1 = 0 := by
      have h1 : 1 ≤ 2 ^ s := Nat.one_le_two_pow
      rw [← hzero, Nat.cast_sub h1]
      simp
    have hpow1 : (2 : ZMod p) ^ s = 1 := by
      have h := sub_eq_zero.mp hsub
      rw [Nat.cast_pow] at h
      simpa using h
    have hord_dvd_s : orderOf (2 : ZMod p) ∣ s := orderOf_dvd_of_pow_eq_one hpow1
    -- Fermat: 2^(p-1) = 1, so the order divides p - 1.
    have h2ne0 : (2 : ZMod p) ≠ 0 := by
      intro h0
      have hd2 : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using h0)
      have hp2le : 2 ≤ p := hp_prime.two_le
      have hple : p ≤ 2 := Nat.le_of_dvd (by norm_num) hd2
      omega
    have hfermat : (2 : ZMod p) ^ (p - 1) = 1 :=
      @ZMod.pow_card_sub_one_eq_one p ⟨hp_prime⟩ (2 : ZMod p) h2ne0
    have hord_dvd_pm1 : orderOf (2 : ZMod p) ∣ p - 1 := orderOf_dvd_of_pow_eq_one hfermat
    -- The order is not 1.
    have hord_ne1 : orderOf (2 : ZMod p) ≠ 1 := by
      intro h1
      have h2 : (2 : ZMod p) = 1 := by
        have hpow := pow_orderOf_eq_one (2 : ZMod p)
        rw [h1, pow_one] at hpow
        exact hpow
      have hone : (1 : ZMod p) = 0 := by
        have h : (2 : ZMod p) - 1 = 0 := by rw [h2]; ring
        have h21 : (2 : ZMod p) - 1 = 1 := by ring
        rwa [h21] at h
      have hd1 : p ∣ 1 := (ZMod.natCast_eq_zero_iff 1 p).mp (by simpa using hone)
      exact hp_prime.not_dvd_one hd1
    have hord_eq : orderOf (2 : ZMod p) = s := by
      rcases hs_prime.eq_one_or_self_of_dvd (orderOf (2 : ZMod p)) hord_dvd_s with h | h
      · exact absurd h hord_ne1
      · exact h
    have hs_dvd_pm1 : s ∣ p - 1 := by rw [← hord_eq]; exact hord_dvd_pm1
    have hp2le : 2 ≤ p := hp_prime.two_le
    have hp1pos : 0 < p - 1 := by omega
    have hle : s ≤ p - 1 := Nat.le_of_dvd hp1pos hs_dvd_pm1
    omega
  refine ⟨M, hMgt1, hcop, S, ?_, ?_, ?_⟩
  · -- S is contained in range M
    intro x hx
    rw [hS, Finset.mem_Icc] at hx
    rw [Finset.mem_range]
    omega
  · -- M ≤ 8 * card S
    have hcard : S.card = L := by
      rw [hS, Nat.card_Icc]
      omega
    omega
  · -- avoidance
    intro a b k ha hb
    rw [hS, Finset.mem_Icc] at ha hb
    obtain ⟨ha1, ha2⟩ := ha
    obtain ⟨hb1, hb2⟩ := hb
    have hab_lo : 6 * L ≤ a + b := by omega
    have hab_hi : a + b < M := by omega
    have hab_mod : (a + b) % M = a + b := Nat.mod_eq_of_lt hab_hi
    have hr_lt : k % s < s := Nat.mod_lt k hspos
    have h2r_le : 2 ^ (k % s) ≤ 4 * L := by
      have h1 : 2 ^ (k % s) ≤ 2 ^ (s - 1) :=
        Nat.pow_le_pow_right (show 0 < 2 by norm_num) (by omega)
      have h4 : 2 ^ (s - 1) = 4 * L := by
        have hs1 : s - 1 = (s - 3) + 2 := by omega
        rw [hs1, pow_add, hL]
        ring
      omega
    have h2r_lt : 2 ^ (k % s) < a + b := by omega
    -- 2^s ≡ 1 mod M.
    have hmod : (2 ^ s) % M = 1 % M := by
      have hkey : 2 ^ s = 1 + M * 1 := by omega
      rw [hkey, Nat.add_mul_mod_self_left]
    have hpow : Nat.ModEq M ((2 ^ s) ^ (k / s)) 1 := by
      have h := Nat.ModEq.pow (n := M) (a := 2 ^ s) (b := 1) (k / s) hmod
      simpa using h
    have hmul : Nat.ModEq M ((2 ^ s) ^ (k / s) * 2 ^ (k % s)) (2 ^ (k % s)) := by
      have h := Nat.ModEq.mul hpow (Nat.ModEq.refl (n := M) (2 ^ (k % s)))
      simpa using h
    have hk_eq : 2 ^ k = (2 ^ s) ^ (k / s) * 2 ^ (k % s) := by
      have hdiv : s * (k / s) + k % s = k := Nat.div_add_mod k s
      calc 2 ^ k = 2 ^ (s * (k / s) + k % s) := by rw [hdiv]
        _ = (2 ^ s) ^ (k / s) * 2 ^ (k % s) := by rw [pow_add, pow_mul]
    have hk_mod : (2 ^ k) % M = 2 ^ (k % s) := by
      have h : ((2 ^ s) ^ (k / s) * 2 ^ (k % s)) % M = (2 ^ (k % s)) % M := hmul
      rw [← hk_eq] at h
      rw [h, Nat.mod_eq_of_lt (by omega : 2 ^ (k % s) < M)]
    intro hcontra
    rw [hab_mod, hk_mod] at hcontra
    omega
