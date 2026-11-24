import Mathlib

/-!
# L-goldbach-unit-nonempty-even

Every even target passes the unit-pair test at every positive modulus: for `q > 0` and even
`n` there is `a < q` with `a` and `n + q - a` both coprime to `q`, i.e. `(U q n).Nonempty`.

At the prime power `s` inside `q`, the residue `a = 1` works unless `n ≡ 1 [MOD p]`, where
`a = 2` does; for `p = 2` evenness gives `n ≡ 0 [MOD 2]`, so the first case always applies.
The `s`-part and the coprime cofactor `m` (handled by induction on `q`) are then assembled
by the Chinese remainder theorem.  Divisibility of `n + s - a` is transferred through
integer congruences to avoid truncated natural subtraction.
-/

namespace PEqualNP.Outside.GoldbachUnitNonemptyEvenAux

/-- A non-coprime pair with positive second entry has a prime common divisor. -/
theorem exists_prime_dvd_of_not_coprime {x s : ℕ} (hnc : ¬ x.Coprime s) (hs : 0 < s) :
    ∃ r : ℕ, r.Prime ∧ r ∣ x ∧ r ∣ s := by
  have hg : x.gcd s ≠ 1 := by rwa [Nat.coprime_iff_gcd_eq_one] at hnc
  have hg0 : x.gcd s ≠ 0 := by
    intro h0
    rw [Nat.gcd_eq_zero_iff] at h0
    omega
  obtain ⟨r, hr, hrd⟩ := Nat.exists_prime_and_dvd (by omega)
  exact ⟨r, hr, hrd.trans (Nat.gcd_dvd_left x s), hrd.trans (Nat.gcd_dvd_right x s)⟩

/-- Divisibility `p ∣ n + s - c` becomes the integer congruence `n ≡ c [ZMOD p]`. -/
theorem int_modEq_of_dvd {p s n c : ℕ} (hps : p ∣ s) (hdvd : p ∣ n + s - c)
    (hc : c ≤ n + s) : (n : ℤ) ≡ (c : ℤ) [ZMOD p] := by
  have h1 : (p : ℤ) ∣ ((n + s - c : ℕ) : ℤ) := Int.natCast_dvd_natCast.mpr hdvd
  have h2 : ((n + s - c : ℕ) : ℤ) = (n : ℤ) + (s : ℤ) - c := by
    rw [Nat.cast_sub hc, Nat.cast_add]
  have h3 : (p : ℤ) ∣ (s : ℤ) := Int.natCast_dvd_natCast.mpr hps
  rw [Int.modEq_iff_dvd]
  have hkey : ((s : ℤ) - ((n + s - c : ℕ) : ℤ)) = ((c : ℤ) - n) := by
    rw [h2]; ring
  rw [← hkey]
  exact dvd_sub h3 (h2 ▸ h1)

theorem int_modEq_one_of_mod {p n : ℕ} (hp : 1 < p) (h1 : n % p = 1) :
    (n : ℤ) ≡ (1 : ℤ) [ZMOD p] := by
  have h0 : ((n % p : ℕ) : ℤ) = ((1 % p : ℕ) : ℤ) := by
    rw [h1, Nat.mod_eq_of_lt hp]
  show (n : ℤ) % (p : ℤ) = (1 : ℤ) % (p : ℤ)
  rw [← Int.natCast_mod]
  exact h0

/-- The unit-pair test at a prime power `s`: `a = 1` unless `n ≡ 1 [MOD p]`, then `a = 2`. -/
theorem prime_pow_pair {p s n : ℕ} (hp : p.Prime) (hs2 : 2 ≤ s) (hps : p ∣ s)
    (honly : ∀ r : ℕ, r.Prime → r ∣ s → r = p) (hn : Even n) :
    ∃ a, a < s ∧ a.Coprime s ∧ (n + s - a).Coprime s := by
  have hp1 : 1 < p := hp.one_lt
  by_cases hmod : n % p = 1
  · have hp2 : p ≠ 2 := by
      intro h
      subst h
      rcases hn with ⟨t, rfl⟩
      omega
    have hp3 : 3 ≤ p := by omega
    have hpsle : p ≤ s := Nat.le_of_dvd (show 0 < s by omega) hps
    refine ⟨2, by omega, ?_, ?_⟩
    · by_contra hnc
      obtain ⟨r, hr, hrx, hrs⟩ := exists_prime_dvd_of_not_coprime hnc (show 0 < s by omega)
      have hle : r ≤ 2 := Nat.le_of_dvd two_pos hrx
      have hr1 : 1 < r := hr.one_lt
      have hr2 : r = 2 := by omega
      have hrp := honly r hr hrs
      omega
    · by_contra hnc
      obtain ⟨r, hr, hrx, hrs⟩ := exists_prime_dvd_of_not_coprime hnc (show 0 < s by omega)
      have hrp : r = p := honly r hr hrs
      have hrx' : p ∣ n + s - 2 := hrp ▸ hrx
      have hint : (n : ℤ) ≡ (2 : ℤ) [ZMOD p] :=
      int_modEq_of_dvd hps hrx' (show 2 ≤ n + s by omega)
      have hint2 : (n : ℤ) ≡ (1 : ℤ) [ZMOD p] := int_modEq_one_of_mod hp1 hmod
      have h12 : (1 : ℤ) % (p : ℤ) = (2 : ℤ) % (p : ℤ) := hint2.symm.trans hint
      have e1 : (1 : ℤ) % (p : ℤ) = 1 :=
        Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hp1)
      have e2 : (2 : ℤ) % (p : ℤ) = 2 :=
        Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hp3)
      rw [e1, e2] at h12
      omega
  · refine ⟨1, by omega, by simp [Nat.coprime_one_left_iff], ?_⟩
    by_contra hnc
    obtain ⟨r, hr, hrx, hrs⟩ := exists_prime_dvd_of_not_coprime hnc (show 0 < s by omega)
    have hrp : r = p := honly r hr hrs
    have hrx' : p ∣ n + s - 1 := hrp ▸ hrx
    have hint : (n : ℤ) ≡ (1 : ℤ) [ZMOD p] :=
      int_modEq_of_dvd hps hrx' (show 1 ≤ n + s by omega)
    have hA : ((n % p : ℕ) : ℤ) = ((1 % p : ℕ) : ℤ) :=
      show (n : ℤ) % (p : ℤ) = (1 : ℤ) % (p : ℤ) from hint
    rw [Nat.mod_eq_of_lt hp1] at hA
    exact hmod (Int.natCast_inj.mp hA)

/-- Split `q` at a prime `p` into the full `p`-power part and a coprime cofactor. -/
theorem exists_prime_pow_split {q p : ℕ} (hp : p.Prime) (hpq : p ∣ q) (hq : 2 ≤ q) :
    ∃ s m : ℕ, s.Coprime m ∧ 2 ≤ s ∧ 1 ≤ m ∧ m < q ∧ s * m = q ∧ p ∣ s ∧
      ∀ r : ℕ, r.Prime → r ∣ s → r = p := by
  have hq0 : q ≠ 0 := by omega
  have hfe : 0 < q.factorization p := by
    have hp1 : p ^ 1 ∣ q := by simpa using hpq
    have h := (Nat.Prime.pow_dvd_iff_le_factorization hp hq0).mp hp1
    omega
  have hsqd : p ^ q.factorization p ∣ q :=
    (Nat.Prime.pow_dvd_iff_le_factorization hp hq0).mpr (le_refl _)
  have hpe1 : 1 < p ^ q.factorization p := Nat.one_lt_pow (Nat.ne_of_gt hfe) hp.one_lt
  have hps : p ∣ p ^ q.factorization p := by
    obtain ⟨t, ht⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hfe)
    rw [ht, Nat.pow_succ]
    exact dvd_mul_left _ _
  have hmpos : 0 < q / p ^ q.factorization p :=
    Nat.div_pos (Nat.le_of_dvd (show 0 < q by omega) hsqd)
      (show 0 < p ^ q.factorization p by omega)
  refine ⟨p ^ q.factorization p, q / p ^ q.factorization p, ?_, ?_, ?_, ?_, ?_, hps, ?_⟩
  · by_contra hnc
    obtain ⟨r, hr, hrs, hrm⟩ := exists_prime_dvd_of_not_coprime hnc hmpos
    have hrp : r = p := Nat.prime_eq_prime_of_dvd_pow hr hp hrs
    have hrm' : p ∣ q / p ^ q.factorization p := hrp ▸ hrm
    have hpem : p ^ (q.factorization p + 1) ∣ q := by
      calc p ^ (q.factorization p + 1) = p ^ q.factorization p * p := Nat.pow_succ _ _
        _ ∣ p ^ q.factorization p * (q / p ^ q.factorization p) :=
          Nat.mul_dvd_mul (dvd_refl _) hrm'
        _ = q := Nat.mul_div_cancel' hsqd
    have h := (Nat.Prime.pow_dvd_iff_le_factorization hp hq0).mp hpem
    omega
  · omega
  · omega
  · have h2m : 2 * (q / p ^ q.factorization p) ≤ q := by
      refine le_trans ?_ (Nat.mul_div_cancel' hsqd).le
      exact Nat.mul_le_mul_right _ (show 2 ≤ p ^ q.factorization p by omega)
    rw [Nat.two_mul] at h2m
    omega
  · exact Nat.mul_div_cancel' hsqd
  · intro r hr hrs
    exact Nat.prime_eq_prime_of_dvd_pow hr hp hrs

/-- Transfer along the divisor: `k ≡ a [MOD s]` and `s ∣ q` give `(n + q - k) ≡ (n + s - a) [MOD s]`. -/
theorem modEq_sub {s q n k a : ℕ} (hsq : s ∣ q) (hkq : k ≤ n + q) (has : a ≤ n + s)
    (hk : k ≡ a [MOD s]) : (n + q - k) ≡ (n + s - a) [MOD s] := by
  have hkz : (k : ℤ) ≡ (a : ℤ) [ZMOD s] := (Int.natCast_modEq_iff).mpr hk
  have hqz : (q : ℤ) ≡ ((s : ℕ) : ℤ) [ZMOD s] := by
    have h1 : (q : ℤ) ≡ 0 [ZMOD s] :=
      (Int.modEq_zero_iff_dvd).mpr (Int.natCast_dvd_natCast.mpr hsq)
    have h2 : ((s : ℕ) : ℤ) ≡ 0 [ZMOD s] := (Int.modEq_zero_iff_dvd).mpr (dvd_refl _)
    exact h1.trans h2.symm
  have e1 : ((n + q - k : ℕ) : ℤ) = (n : ℤ) + (q : ℤ) - k := by
    rw [Nat.cast_sub hkq, Nat.cast_add]
  have e2 : ((n + s - a : ℕ) : ℤ) = (n : ℤ) + ((s : ℕ) : ℤ) - a := by
    rw [Nat.cast_sub has, Nat.cast_add]
  have key : ((n + q - k : ℕ) : ℤ) ≡ ((n + s - a : ℕ) : ℤ) [ZMOD s] := by
    rw [e1, e2]
    exact ((hqz.add_left (n : ℤ)).sub_right (k : ℤ)).trans
      (hkz.sub_left ((n : ℤ) + ((s : ℕ) : ℤ)))
  exact (Int.natCast_modEq_iff).mp key

/-- The unit-pair statement, by strong induction on the modulus. -/
theorem unit_pair (q : ℕ) : ∀ n : ℕ, 0 < q → Even n →
    ∃ a, a < q ∧ a.Coprime q ∧ (n + q - a).Coprime q := by
  induction q using Nat.strong_induction_on with
  | ind q ih =>
    intro n hq hn
    by_cases hq1 : q = 1
    · subst hq1
      exact ⟨0, by omega, by simp [Nat.coprime_one_right_iff],
        by simp [Nat.coprime_one_right_iff]⟩
    obtain ⟨p, hp, hpq⟩ := Nat.exists_prime_and_dvd (by omega)
    obtain ⟨s, m, hcop, hs2, hm1, hmlt, hqsm, hps, hsf⟩ := exists_prime_pow_split hp hpq (by omega)
    obtain ⟨a₂, ha₂, hc₂, hnc₂⟩ := prime_pow_pair hp hs2 hps hsf hn
    obtain ⟨a₁, ha₁, hc₁, hnc₁⟩ := ih m hmlt n (by omega) hn
    obtain ⟨k, hk1, hk2, hklt⟩ :
        ∃ k, k ≡ a₂ [MOD s] ∧ k ≡ a₁ [MOD m] ∧ k < s * m := by
      refine ⟨(Nat.chineseRemainder hcop a₂ a₁).val,
        (Nat.chineseRemainder hcop a₂ a₁).2.1, (Nat.chineseRemainder hcop a₂ a₁).2.2, ?_⟩
      exact Nat.chineseRemainder_lt_mul hcop a₂ a₁ (by omega) (by omega)
    have hkq : k < q := by
      rw [← hqsm]
      exact hklt
    have hsq : s ∣ q := ⟨m, hqsm.symm⟩
    have hmsq : m ∣ q := ⟨s, hqsm.symm.trans (Nat.mul_comm s m)⟩
    have hks : k.Coprime s := by
      rw [Nat.coprime_iff_gcd_eq_one, Nat.ModEq.gcd_eq hk1]
      rwa [Nat.coprime_iff_gcd_eq_one] at hc₂
    have hkm : k.Coprime m := by
      rw [Nat.coprime_iff_gcd_eq_one, Nat.ModEq.gcd_eq hk2]
      rwa [Nat.coprime_iff_gcd_eq_one] at hc₁
    have hns : (n + q - k).Coprime s := by
      rw [Nat.coprime_iff_gcd_eq_one,
        Nat.ModEq.gcd_eq (modEq_sub hsq (show k ≤ n + q by omega) (show a₂ ≤ n + s by omega) hk1)]
      rwa [Nat.coprime_iff_gcd_eq_one] at hnc₂
    have hnm : (n + q - k).Coprime m := by
      rw [Nat.coprime_iff_gcd_eq_one,
        Nat.ModEq.gcd_eq (modEq_sub hmsq (show k ≤ n + q by omega) (show a₁ ≤ n + m by omega) hk2)]
      rwa [Nat.coprime_iff_gcd_eq_one] at hnc₁
    have hfin : (n + q - k).Coprime q := by
      have hcmb := Nat.Coprime.mul_right hns hnm
      rwa [hqsm] at hcmb
    exact ⟨k, by omega, by rw [← hqsm]; exact Nat.Coprime.mul_right hks hkm, hfin⟩

end PEqualNP.Outside.GoldbachUnitNonemptyEvenAux

theorem PEqualNP.Outside.L_goldbach_unit_nonempty_even :
    let U := fun q n : ℕ => (Finset.range q).filter (fun a => Nat.Coprime a q ∧ Nat.Coprime (n+q-a) q); ∀ q n, 0<q → Even n → (U q n).Nonempty :=
  fun q n hq hn => by
    obtain ⟨a, ha, hc1, hc2⟩ :=
      PEqualNP.Outside.GoldbachUnitNonemptyEvenAux.unit_pair q n hq hn
    exact ⟨a, Finset.mem_filter.2 ⟨Finset.mem_range.2 ha, hc1, hc2⟩⟩
