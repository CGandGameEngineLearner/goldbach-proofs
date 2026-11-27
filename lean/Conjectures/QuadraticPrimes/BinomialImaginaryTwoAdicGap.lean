import Mathlib

namespace TwoAdicAux

lemma lt_pow (n : ℕ) : n + 3 < 2 ^ (n + 2) := by
  induction n with
  | zero => norm_num
  | succ n ih => rw [pow_succ]; omega

lemma val_choose_two (n : ℕ) : multiplicity 2 ((n + 3).choose 2) + 1 ≤ n + 1 := by
  have h1 : 2 ^ multiplicity 2 ((n + 3).choose 2) ∣ (n + 3).choose 2 := pow_multiplicity_dvd 2 _
  generalize multiplicity 2 ((n + 3).choose 2) = e at h1 ⊢
  have h2 : (n + 3) * (n + 2) = (n + 3).choose 2 * 2 := by
    have := Nat.add_one_mul_choose_eq (n + 2) 1
    simpa using this
  have h3 : 2 ^ (e + 1) ∣ (n + 3) * (n + 2) := by
    rw [h2, pow_succ]; exact Nat.mul_dvd_mul_right h1 2
  have h4 : 2 ^ (e + 1) ≤ n + 3 := by
    rcases Nat.even_or_odd n with hn | hn
    · have hodd : Odd (n + 3) := by
        obtain ⟨r, hr⟩ := hn
        exact ⟨r + 1, by omega⟩
      have hc : Nat.Coprime (2 ^ (e + 1)) (n + 3) :=
        Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hodd)
      have hd : 2 ^ (e + 1) ∣ n + 2 := hc.dvd_of_dvd_mul_left h3
      exact le_trans (Nat.le_of_dvd (by omega) hd) (by omega)
    · have hodd : Odd (n + 2) := by
        obtain ⟨r, hr⟩ := hn
        exact ⟨r + 1, by omega⟩
      have hc : Nat.Coprime (2 ^ (e + 1)) (n + 2) :=
        Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hodd)
      have hd : 2 ^ (e + 1) ∣ n + 3 := hc.dvd_of_dvd_mul_right h3
      exact Nat.le_of_dvd (by omega) hd
  have h5 := lt_pow n
  have h6 : 2 ^ (e + 1) < 2 ^ (n + 2) := lt_of_le_of_lt h4 h5
  have h7 := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp h6
  omega

lemma term_dvd (a : ℤ) (ha : Even a) (j k : ℕ) (hk : k + 3 ≤ j) :
    ((2 : ℤ) ^ (multiplicity 2 (j.choose 2) + 1) * a ^ 2) ∣
      (a ^ (k + 3) * ((j.choose (k + 3) : ℕ) : ℤ)) := by
  have hmul := Nat.choose_mul (n := j) (k := k + 3) (s := 2) (by omega)
  have hpos1 : j.choose (k + 3) ≠ 0 := (Nat.choose_pos hk).ne'
  have hpos2 : (k + 3).choose 2 ≠ 0 := (Nat.choose_pos (by omega)).ne'
  have hpos3 : j.choose 2 ≠ 0 := (Nat.choose_pos (by omega)).ne'
  have hpos4 : (j - 2).choose (k + 3 - 2) ≠ 0 := (Nat.choose_pos (by omega)).ne'
  have hv := congrArg (multiplicity 2) hmul
  rw [Nat.multiplicity_mul hpos1 hpos2, Nat.multiplicity_mul hpos3 hpos4] at hv
  have hk2 := val_choose_two k
  have hle : multiplicity 2 (j.choose 2) + 1 ≤ multiplicity 2 (j.choose (k + 3)) + (k + 1) := by
    omega
  have h1 : (2 : ℤ) ^ (multiplicity 2 (j.choose (k + 3))) ∣ ((j.choose (k + 3) : ℕ) : ℤ) := by
    exact_mod_cast (pow_multiplicity_dvd 2 (j.choose (k + 3)))
  obtain ⟨b, hb⟩ := ha
  obtain ⟨c, hc⟩ := h1
  obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le hle
  have hpow : (2 : ℤ) ^ (multiplicity 2 (j.choose (k + 3))) * 2 ^ (k + 1) =
      2 ^ (multiplicity 2 (j.choose 2) + 1) * 2 ^ t := by
    rw [← pow_add, ← pow_add, ht]
  refine ⟨2 ^ t * b ^ (k + 1) * c, ?_⟩
  rw [hc, hb]
  linear_combination (4 * b ^ (k + 3) * c) * hpow

lemma sqrtd_pow_even (s : ℕ) :
    (Zsqrtd.sqrtd : GaussianInt) ^ (2 * s) = (((-1 : ℤ) ^ s : ℤ) : GaussianInt) := by
  rw [pow_mul, pow_two, Zsqrtd.dmuld, Int.cast_pow]

lemma main_expand (a : ℤ) (ha : Even a) (s : ℕ) :
    ∃ g : ℤ, ((⟨a, 1⟩ : GaussianInt) ^ (2 * s + 3)).im =
      2 ^ (multiplicity 2 ((2 * s + 3).choose 2) + 1) * a ^ 2 * g
        + a ^ 2 * (((2 * s + 3).choose 2 : ℕ) : ℤ) * (-1) ^ s + (-1) ^ (s + 1) := by
  have hdec : (⟨a, 1⟩ : GaussianInt) = (a : GaussianInt) + Zsqrtd.sqrtd := by
    ext <;> simp
  rw [hdec, add_pow, Finset.sum_range_succ', Finset.sum_range_succ', Finset.sum_range_succ']
  have hdvd : (((2 : ℤ) ^ (multiplicity 2 ((2 * s + 3).choose 2) + 1) * a ^ 2 : ℤ) : GaussianInt) ∣
      ∑ k ∈ Finset.range (2 * s + 1), (a : GaussianInt) ^ (k + 1 + 1 + 1) *
        Zsqrtd.sqrtd ^ (2 * s + 3 - (k + 1 + 1 + 1)) *
        (((2 * s + 3).choose (k + 1 + 1 + 1) : ℕ) : GaussianInt) := by
    apply Finset.dvd_sum
    intro k hk
    have hk' : k + 3 ≤ 2 * s + 3 := by
      have := Finset.mem_range.mp hk
      omega
    have h1 := term_dvd a ha (2 * s + 3) k hk'
    have h2 := (Zsqrtd.intCast_dvd_intCast (d := -1) _ _).mpr h1
    rw [mul_right_comm]
    refine Dvd.dvd.mul_right ?_ _
    have e3 : k + 1 + 1 + 1 = k + 3 := by omega
    rw [e3]
    push_cast at h2 ⊢
    exact h2
  obtain ⟨G, hG⟩ := hdvd
  refine ⟨G.im, ?_⟩
  have e2 : 2 * s + 3 - (0 + 1 + 1) = 2 * s + 1 := by omega
  have e1 : 2 * s + 3 - (0 + 1) = 2 * (s + 1) := by omega
  have e0 : 2 * s + 3 - 0 = 2 * (s + 1) + 1 := by omega
  have hterm2 : (a : GaussianInt) ^ (0 + 1 + 1) * Zsqrtd.sqrtd ^ (2 * s + 3 - (0 + 1 + 1)) *
      (((2 * s + 3).choose (0 + 1 + 1) : ℕ) : GaussianInt) =
      ((a ^ 2 * (-1) ^ s * (((2 * s + 3).choose 2 : ℕ) : ℤ) : ℤ) : GaussianInt) * Zsqrtd.sqrtd := by
    rw [e2, pow_succ Zsqrtd.sqrtd (2 * s), sqrtd_pow_even]
    push_cast
    ring
  have hterm1 : (a : GaussianInt) ^ (0 + 1) * Zsqrtd.sqrtd ^ (2 * s + 3 - (0 + 1)) *
      (((2 * s + 3).choose (0 + 1) : ℕ) : GaussianInt) =
      ((a * (-1) ^ (s + 1) * (((2 * s + 3).choose 1 : ℕ) : ℤ) : ℤ) : GaussianInt) := by
    rw [e1, sqrtd_pow_even]
    push_cast
    ring
  have hterm0 : (a : GaussianInt) ^ 0 * Zsqrtd.sqrtd ^ (2 * s + 3 - 0) *
      (((2 * s + 3).choose 0 : ℕ) : GaussianInt) =
      (((-1) ^ (s + 1) : ℤ) : GaussianInt) * Zsqrtd.sqrtd := by
    rw [e0, pow_succ Zsqrtd.sqrtd (2 * (s + 1)), sqrtd_pow_even]
    push_cast
    simp
  rw [hterm2, hterm1, hterm0, hG]
  simp only [Zsqrtd.im_add, Zsqrtd.im_smul, Zsqrtd.im_intCast, Zsqrtd.im_sqrtd]
  ring

end TwoAdicAux

theorem Conjectures.QuadraticPrimes.BinomialImaginaryTwoAdicGap : (∀ (a : ℤ) (j : ℕ), a ≠ 0 → Even a → Odd j → 3 ≤ j → let d := ((⟨a,1⟩ : GaussianInt)^j).im - (-1 : ℤ)^((j-1)/2); d ≠ 0 ∧ padicValNat 2 d.natAbs = padicValNat 2 (j.choose 2) + 2 * padicValNat 2 a.natAbs) := by
  intro a j ha0 hae hjo hj3
  obtain ⟨s, hs⟩ : ∃ s, j = 2 * s + 3 := by
    obtain ⟨m, hm⟩ := hjo
    exact ⟨m - 1, by omega⟩
  subst hs
  obtain ⟨g, hg⟩ := TwoAdicAux.main_expand a hae s
  have e : (2 * s + 3 - 1) / 2 = s + 1 := by omega
  have hC0 : (2 * s + 3).choose 2 ≠ 0 := (Nat.choose_pos (by omega)).ne'
  obtain ⟨o, ho⟩ : 2 ^ multiplicity 2 ((2 * s + 3).choose 2) ∣ (2 * s + 3).choose 2 :=
    pow_multiplicity_dvd 2 _
  have hoodd : Odd o := by
    rcases Nat.even_or_odd o with h | h
    · exfalso
      have hnd := pow_succ_multiplicity_not_dvd (p := 2) hC0
      have h2 : 2 ^ (multiplicity 2 ((2 * s + 3).choose 2) + 1) ∣
          2 ^ multiplicity 2 ((2 * s + 3).choose 2) * o := by
        rw [pow_succ]
        exact mul_dvd_mul_left _ (even_iff_two_dvd.mp h)
      rw [← ho] at h2
      exact hnd h2
    · exact h
  intro d
  set v := multiplicity 2 ((2 * s + 3).choose 2) with hv
  set w : ℤ := 2 * g + (o : ℤ) * (-1) ^ s with hw
  have hd : d = a ^ 2 * (2 ^ v * w) := by
    have hCz : (((2 * s + 3).choose 2 : ℕ) : ℤ) = 2 ^ v * (o : ℤ) := by
      rw [ho]; push_cast; ring
    simp only [d]
    rw [hg, e, hCz, hw]
    ring
  have hwodd : Odd w := by
    rw [hw]
    exact Even.add_odd (even_two_mul g)
      (Odd.mul ((Int.odd_natCast o).mpr hoodd) (Odd.pow odd_neg_one))
  have hw0 : w ≠ 0 := by
    intro h
    rw [h] at hwodd
    exact absurd hwodd (by decide)
  have hwn : ¬ 2 ∣ w.natAbs := by
    have : Odd w.natAbs := Int.natAbs_odd.mpr hwodd
    exact Nat.two_dvd_ne_zero.mpr (Nat.odd_iff.mp this)
  have ha0' : a.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr ha0
  have hw0' : w.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hw0
  refine ⟨?_, ?_⟩
  · rw [hd]
    exact mul_ne_zero (pow_ne_zero _ ha0) (mul_ne_zero (pow_ne_zero _ (by norm_num)) hw0)
  · have hnat : d.natAbs = a.natAbs ^ 2 * (2 ^ v * w.natAbs) := by
      rw [hd, Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_pow]
      rfl
    rw [Nat.padicValNat_def, Nat.padicValNat_def, Nat.padicValNat_def, hnat,
      Nat.multiplicity_mul (pow_ne_zero _ ha0') (mul_ne_zero (pow_ne_zero _ (by norm_num)) hw0'),
      Nat.multiplicity_pow, Nat.multiplicity_mul (pow_ne_zero _ (by norm_num)) hw0',
      Nat.multiplicity_prime_pow, multiplicity_eq_zero_of_not_dvd hwn]
    omega
