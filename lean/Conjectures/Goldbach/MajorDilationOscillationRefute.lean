import Mathlib
import Conjectures.Goldbach.MajorFixed144

/-!
# Goldbach gap `L-goldbach-major-dilation-oscillation-refute`

Refutation of uniform sublinear oscillation under independent arc dilation:
there is a fixed `ε > 0` (`1 / 100000`) such that for arbitrarily large even `n`
(chosen as `n = 2 ^ k`), choosing `r q a = 2` on the upper half of the moduli
`Q/2 < q ≤ Q` whenever the real arithmetic phase `(unitMean q a ^ 2 * phase (-n*a/q)).re`
is nonnegative (and `1` otherwise) increases the major-arc real part by at least `n / 40960 - o(n)`.
-/

open scoped BigOperators ComplexConjugate
open Finset Filter MeasureTheory intervalIntegral
open Conjectures.Goldbach.MajorFixed144_aux.GoldbachMajorArc

namespace Conjectures.Goldbach.MajorDilationOscillationRefute_aux

/-! ### 1. Finite Ramanujan sums and unit-mean identities -/

private def unitsBelow (m : ℕ) : Finset ℕ :=
  (Finset.range m).filter (fun a => Nat.Coprime a m)

private theorem unitsBelow_card (m : ℕ) : (unitsBelow m).card = m.totient := by
  unfold unitsBelow
  rw [Nat.totient_eq_card_coprime]
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_range]
  exact and_congr_right (fun _ => Nat.coprime_comm)

private noncomputable def rphase (m h a : ℕ) : ℂ :=
  Complex.exp (((2 * Real.pi * ((h : ℝ) * a / m) : ℝ) : ℂ) * Complex.I)

private theorem rphase_character (m h a : ℕ) [NeZero m] :
    rphase m h a = ZMod.stdAddChar ((h : ZMod m) * (a : ZMod m)) := by
  have ch := ZMod.stdAddChar_coe (N := m) ((h * a : ℕ) : ℤ)
  push_cast at ch
  rw [ch]
  unfold rphase
  push_cast
  congr 1
  ring

private theorem rphase_modulus (m h a : ℕ) [NeZero m] :
    rphase m h (a % m) = rphase m h a := by
  simp only [rphase_character, ZMod.natCast_mod]

private theorem rphase_pair (q r h a b : ℕ) (hq : 0 < q) (hr : 0 < r) :
    rphase (q * r) h ((r * a + q * b) % (q * r)) = rphase q h a * rphase r h b := by
  have : NeZero (q * r) := ⟨Nat.ne_of_gt (Nat.mul_pos hq hr)⟩
  rw [rphase_modulus]
  unfold rphase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  have qnz : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have rnz : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  field_simp

private noncomputable def ram (q h : ℕ) : ℂ :=
  ∑ a ∈ unitsBelow q, rphase q h a

private theorem ram_one (h : ℕ) : ram 1 h = 1 := by
  simp [ram, unitsBelow, rphase]

private theorem ram_mul {q r : ℕ} (hq : 0 < q) (hr : 0 < r) (hc : q.Coprime r) (h : ℕ) :
    ram (q * r) h = ram q h * ram r h := by
  let combine (x : ℕ × ℕ) := (r * x.1 + q * x.2) % (q * r)
  let pairs := unitsBelow q ×ˢ unitsBelow r
  have member {m a : ℕ} : a ∈ unitsBelow m ↔ a < m ∧ Nat.Coprime a m := by
    simp only [unitsBelow, Finset.mem_filter, Finset.mem_range]
  have maps : pairs.image combine ⊆ unitsBelow (q * r) := by
    intro z hz
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
    apply member.mpr
    refine ⟨Nat.mod_lt _ (Nat.mul_pos hq hr), ?_⟩
    change Nat.gcd ((r * a + q * b) % (q * r)) (q * r) = 1
    rw [← Nat.gcd_rec]
    change Nat.Coprime (q * r) (r * a + q * b)
    apply Nat.coprime_mul_iff_left.mpr
    constructor
    · rw [Nat.coprime_add_mul_left_right]
      exact hc.mul_right (member.mp ha).2.symm
    · rw [add_comm, Nat.coprime_add_mul_left_right]
      exact hc.symm.mul_right (member.mp hb).2.symm
  have injective : Set.InjOn combine (↑pairs) := by
    rintro ⟨a, b⟩ hab ⟨c, d⟩ hcd he
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
    obtain ⟨hc1, hd⟩ := Finset.mem_product.mp hcd
    have congruence : r * a + q * b ≡ r * c + q * d [MOD q * r] := he
    apply Prod.ext
    · have hmod := congruence.of_dvd (dvd_mul_right q r)
      have reduced : r * a ≡ r * c [MOD q] := by
        simpa only [Nat.ModEq, Nat.add_mod, Nat.mul_mod_right, add_zero, Nat.mod_mod] using hmod
      exact (Nat.ModEq.cancel_left_of_coprime hc reduced).eq_of_lt_of_lt
        (member.mp ha).1 (member.mp hc1).1
    · have hmod := congruence.of_dvd (dvd_mul_left r q)
      have reduced : q * b ≡ q * d [MOD r] := by
        simpa only [Nat.ModEq, Nat.add_mod, Nat.mul_mod_right, zero_add, Nat.mod_mod] using hmod
      exact (Nat.ModEq.cancel_left_of_coprime hc.symm reduced).eq_of_lt_of_lt
        (member.mp hb).1 (member.mp hd).1
  have covers : pairs.image combine = unitsBelow (q * r) := by
    apply Finset.eq_of_subset_of_card_le maps
    rw [Finset.card_image_of_injOn injective, unitsBelow_card, Nat.totient_mul hc]
    simp only [pairs, Finset.card_product, unitsBelow_card]
    exact le_rfl
  unfold ram
  rw [← covers, Finset.sum_image injective, Finset.sum_mul_sum, ← Finset.sum_product']
  exact Finset.sum_congr rfl fun x _ => rphase_pair q r h x.1 x.2 hq hr

private theorem ram_prime {p : ℕ} (hp : p.Prime) (h : ℕ) :
    ram p h = (if p ∣ h then (p : ℂ) else 0) - 1 := by
  have full : ∑ a ∈ Finset.range p, rphase p h a = if p ∣ h then (p : ℂ) else 0 := by
    let : NeZero p := ⟨hp.ne_zero⟩
    calc
      _ = ∑ x : ZMod p, ZMod.stdAddChar ((h : ZMod p) * x) := by
        apply Finset.sum_bij (fun (a : ℕ) _ => (a : ZMod p))
        · intro a _
          exact Finset.mem_univ _
        · intro a ha b hb hab
          simpa only [ZMod.val_natCast_of_lt (Finset.mem_range.mp ha),
            ZMod.val_natCast_of_lt (Finset.mem_range.mp hb)] using congrArg ZMod.val hab
        · intro x _
          exact ⟨x.val, Finset.mem_range.mpr x.val_lt, ZMod.natCast_zmod_val x⟩
        · intro a _
          have cast_eq : (h : ZMod p) * a = ((h * a : ℕ) : ℤ) := by push_cast; rfl
          rw [cast_eq, ZMod.stdAddChar_coe]
          unfold rphase
          congr 1
          push_cast
          ring
      _ = _ := by
        by_cases hd : p ∣ h
        · have hz : (h : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff h p).mpr hd
          simp [hd, hz, ZMod.card]
        · have hz : (h : ZMod p) ≠ 0 := fun hz => hd ((ZMod.natCast_eq_zero_iff h p).mp hz)
          rw [ite_eq_right hd]
          exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar p hz)
  have hfilter : unitsBelow p = Finset.range p \ {0} := by
    ext a
    simp only [unitsBelow, Finset.mem_filter, Finset.mem_range, Finset.mem_sdiff,
      Finset.mem_singleton]
    constructor
    · rintro ⟨ha, hcop⟩
      refine ⟨ha, ?_⟩
      rintro rfl
      simp [Nat.Coprime] at hcop
      exact hp.ne_one hcop
    · rintro ⟨ha, ha0⟩
      refine ⟨ha, ?_⟩
      rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
      exact fun hd => ha0 (Nat.eq_zero_of_dvd_of_lt hd ha)
  have hsub : {0} ⊆ Finset.range p := Finset.singleton_subset_iff.mpr (Finset.mem_range.mpr hp.pos)
  have h0 : rphase p h 0 = 1 := by simp [rphase]
  unfold ram
  rw [hfilter, ← full]
  have hs := Finset.sum_sdiff hsub (f := fun a => rphase p h a)
  rw [Finset.sum_singleton, h0] at hs
  exact eq_sub_of_add_eq hs

private theorem ram_unit (q a : ℕ) (hq : 0 < q) (ha : a.Coprime q) :
    ram q a = ram q 1 := by
  let : NeZero q := ⟨hq.ne'⟩
  have hperm : (unitsBelow q).image (fun r => (r * a) % q) = unitsBelow q := by
    apply Finset.eq_of_subset_of_card_le
    · intro z hz
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hz
      simp only [unitsBelow, Finset.mem_filter, Finset.mem_range] at hr ⊢
      refine ⟨Nat.mod_lt _ hq, ?_⟩
      change Nat.gcd ((r * a) % q) q = 1
      rw [← Nat.gcd_rec]
      exact (hr.2.mul_left ha).symm
    · rw [Finset.card_image_of_injOn]
      intro x hx y hy hxy
      simp only [unitsBelow, Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hx hy
      have hmod : x * a ≡ y * a [MOD q] := hxy
      exact (Nat.ModEq.cancel_right_of_coprime ha.symm hmod).eq_of_lt_of_lt hx.1 hy.1
  unfold ram
  calc
    _ = ∑ r ∈ unitsBelow q, rphase q 1 ((r * a) % q) := by
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [rphase_modulus]
      unfold rphase
      congr 2
      push_cast
      ring
    _ = ∑ z ∈ (unitsBelow q).image (fun r => (r * a) % q), rphase q 1 z := by
      rw [Finset.sum_image]
      intro x hx y hy hxy
      simp only [unitsBelow, Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hx hy
      have hmod : x * a ≡ y * a [MOD q] := hxy
      exact (Nat.ModEq.cancel_right_of_coprime ha.symm hmod).eq_of_lt_of_lt hx.1 hy.1
    _ = _ := by rw [hperm]

private theorem ram_one_sq {q : ℕ} (hq : 0 < q) (hsq : Squarefree q) :
    ram q 1 ^ 2 = 1 := by
  induction q using Nat.recOnPosPrimePosCoprime with
  | zero => omega
  | one => simp [ram_one]
  | prime_pow p k hp hk =>
    cases k with
    | zero => omega
    | succ k =>
      cases k with
      | zero =>
        have hone : ¬ p ∣ 1 := fun h => hp.ne_one (Nat.dvd_one.mp h)
        rw [pow_one, ram_prime hp, ite_eq_right hone]
        norm_num
      | succ j =>
        exfalso
        have hp2 : p * p ∣ p ^ (j + 2) := ⟨p ^ j, by ring⟩
        exact Nat.Prime.ne_one hp (Nat.isUnit_iff.mp (hsq p hp2))
  | coprime a b ha hb hab ia ib =>
    have hsq' := (Nat.squarefree_mul hab).mp hsq
    rw [ram_mul (by omega) (by omega) hab, mul_pow, ia (by omega) hsq'.1, ib (by omega) hsq'.2,
      one_mul]

private theorem ram_pow2_sq {q : ℕ} (hq : 0 < q) (hsq : Squarefree q) (k : ℕ) :
    ram q (2 ^ k) = 1 ∨ ram q (2 ^ k) = -1 := by
  induction q using Nat.recOnPosPrimePosCoprime with
  | zero => omega
  | one => left; exact ram_one _
  | prime_pow p m hp hm =>
    cases m with
    | zero => omega
    | succ m =>
      cases m with
      | zero =>
        rw [pow_one, ram_prime hp]
        by_cases hp2 : p = 2
        · subst hp2
          by_cases hk0 : k = 0
          · subst hk0; norm_num
          · have h2d : 2 ∣ 2 ^ k := dvd_pow_self 2 hk0
            rw [ite_eq_left h2d]; left; norm_num
        · have hnd : ¬ p ∣ 2 ^ k := fun hd => hp2 (Nat.Prime.dvd_of_dvd_pow hp hd |> fun h =>
            (Nat.dvd_prime Nat.prime_two).mp h |>.resolve_left hp.ne_one)
          rw [ite_eq_right hnd]; right; norm_num
      | succ j =>
        exfalso
        have hp2 : p * p ∣ p ^ (j + 2) := ⟨p ^ j, by ring⟩
        exact Nat.Prime.ne_one hp (Nat.isUnit_iff.mp (hsq p hp2))
  | coprime a b ha hb hab ia ib =>
    have hsq' := (Nat.squarefree_mul hab).mp hsq
    rw [ram_mul (by omega) (by omega) hab]
    rcases ia (by omega) hsq'.1 with ha1 | ha1 <;>
      rcases ib (by omega) hsq'.2 with hb1 | hb1 <;>
      simp [ha1, hb1]

private theorem unitsBelow_eq_numerators (q : ℕ) (hq : 1 < q) :
    unitsBelow q = numerators q := by
  ext a
  simp only [unitsBelow, numerators, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨ha1, ha2⟩; exact ⟨by omega, ha2⟩
  · rintro ⟨ha1, ha2⟩
    have ha_ne : a ≠ q := by
      rintro rfl
      simp [Nat.Coprime] at ha2
      omega
    exact ⟨by omega, ha2⟩

private theorem unitMean_sq {q a : ℕ} (hq : 0 < q) (hsq : Squarefree q) (ha : a.Coprime q) :
    unitMean q a ^ 2 = (1 / (q.totient : ℝ) ^ 2 : ℝ) := by
  have hterm : ∀ r : ℕ, phase ((r : ℝ) * ((a : ℝ) / q)) = rphase q a r := by
    intro r
    unfold phase rphase
    congr 2
    push_cast
    ring
  have hum : unitMean q a = ram q a / (q.totient : ℂ) := by
    rw [unitMean]
    exact congrArg (· / (q.totient : ℂ)) (Finset.sum_congr rfl fun r _ => hterm r)
  rw [hum, ram_unit q a hq ha, div_pow, ram_one_sq hq hsq]
  simp only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_pow, Complex.ofReal_natCast]

private theorem totient_ge_six_of_squarefree {q : ℕ} (hq : 31 ≤ q) (hsq : Squarefree q) :
    6 ≤ q.totient := by
  have hne0 : q ≠ 0 := by omega
  have hex : ∃ p ∈ q.primeFactors, 7 ≤ p := by
    by_contra hall
    push Not at hall
    have hsub : q.primeFactors ⊆ ({2, 3, 5} : Finset ℕ) := by
      intro p hp
      have hpr := Nat.prime_of_mem_primeFactors hp
      have hle6 : p ≤ 6 := by have := hall p hp; omega
      have h6 : p ≠ 4 ∧ p ≠ 6 := ⟨fun h => by subst h; norm_num at hpr,
        fun h => by subst h; norm_num at hpr⟩
      have h2 := hpr.two_le
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    have hdvd : ∏ p ∈ q.primeFactors, p ∣ ∏ p ∈ ({2, 3, 5} : Finset ℕ), p :=
      Finset.prod_dvd_prod_of_subset _ _ id hsub
    rw [Nat.prod_primeFactors_of_squarefree hsq] at hdvd
    have h30 : ∏ p ∈ ({2, 3, 5} : Finset ℕ), p = 30 := by decide
    rw [h30] at hdvd
    have := Nat.le_of_dvd (by decide) hdvd
    omega
  obtain ⟨p, hp_mem, hp7⟩ := hex
  have hp_prime := Nat.prime_of_mem_primeFactors hp_mem
  have hp_dvd : p ∣ q := Nat.dvd_of_mem_primeFactors hp_mem
  have hcop : p.Coprime (q / p) := by
    by_contra hnc
    have hd1 : p ∣ q / p := by
      by_contra hd
      exact hnc (hp_prime.coprime_iff_not_dvd.mpr hd)
    have hd2 : p * p ∣ q := by
      obtain ⟨t, ht⟩ := hd1
      refine ⟨t, ?_⟩
      calc q = p * (q / p) := (Nat.mul_div_cancel' hp_dvd).symm
        _ = p * (p * t) := by rw [ht]
        _ = p * p * t := by ring
    exact Nat.Prime.ne_one hp_prime (Nat.isUnit_iff.mp (hsq p hd2))
  have hq_eq : q = p * (q / p) := (Nat.mul_div_cancel' hp_dvd).symm
  have hqdiv_pos : 0 < q / p := Nat.div_pos (Nat.le_of_dvd (by omega) hp_dvd) hp_prime.pos
  have htot_div : 1 ≤ (q / p).totient := Nat.totient_pos.mpr hqdiv_pos
  have htot_p : p.totient = p - 1 := Nat.totient_prime hp_prime
  calc
    6 ≤ p - 1 := by omega
    _ = p.totient := htot_p.symm
    _ ≤ p.totient * (q / p).totient := Nat.le_mul_of_pos_right _ htot_div
    _ = (p * (q / p)).totient := (Nat.totient_mul hcop).symm
    _ = q.totient := by rw [← hq_eq]

private noncomputable def cTerm (n q a : ℕ) : ℝ :=
  (unitMean q a ^ 2 * phase (-(n : ℝ) * center q a)).re

private theorem pos_cosine_sum_lower {q k : ℕ} (hq : 31 ≤ q) (hsq : Squarefree q) :
    1 / (8 * (q : ℝ)) ≤
      ∑ a ∈ unitsBelow q, if 0 ≤ cTerm (2 ^ k) q a then cTerm (2 ^ k) q a else 0 := by
  let c := fun a : ℕ => cTerm (2 ^ k) q a
  change 1 / (8 * (q : ℝ)) ≤ ∑ a ∈ unitsBelow q, if 0 ≤ c a then c a else 0
  have hq_pos : 0 < q := by omega
  have hφ6 : 6 ≤ q.totient := totient_ge_six_of_squarefree hq hsq
  have hφ_pos : 0 < (q.totient : ℝ) := by exact_mod_cast (by omega : 0 < q.totient)
  let s : ℕ → ℝ := fun a => Real.cos (2 * Real.pi * ((2 ^ k : ℕ) : ℝ) * a / q)
  have hc_eq : ∀ a ∈ unitsBelow q, c a = s a / (q.totient : ℝ) ^ 2 := by
    intro a ha
    have ha_cop : a.Coprime q := (Finset.mem_filter.mp ha).2
    dsimp only [c, cTerm, center]
    rw [unitMean_sq hq_pos hsq ha_cop]
    rw [phase, Complex.exp_ofReal_mul_I]
    simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.add_re,
      Complex.I_re, Complex.I_im, mul_zero, sub_zero, add_zero]
    rw [show 2 * Real.pi * (-((2 ^ k : ℕ) : ℝ) * ((a : ℝ) / q)) =
      -(2 * Real.pi * ((2 ^ k : ℕ) : ℝ) * a / q) by ring, Real.cos_neg]
    dsimp only [s]
    ring
  have hsum_s : ∑ a ∈ unitsBelow q, s a = (ram q (2 ^ k)).re := by
    unfold ram
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    unfold rphase
    rw [Complex.exp_ofReal_mul_I]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, sub_zero, add_zero]
    dsimp only [s]
    congr 1
    ring
  have hsum_cos2 : ∑ a ∈ unitsBelow q, Real.cos (2 * Real.pi * ((2 ^ (k + 1) : ℕ) : ℝ) * a / q) =
      (ram q (2 ^ (k + 1))).re := by
    unfold ram
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    unfold rphase
    rw [Complex.exp_ofReal_mul_I]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, sub_zero, add_zero]
    congr 1
    ring
  have hram1 : -1 ≤ (ram q (2 ^ k)).re := by
    rcases ram_pow2_sq hq_pos hsq k with h1 | h1 <;> simp [h1]
  have hram2 : -1 ≤ (ram q (2 ^ (k + 1))).re := by
    rcases ram_pow2_sq hq_pos hsq (k + 1) with h1 | h1 <;> simp [h1]
  have hsum_sq : ((q.totient : ℝ) - 1) / 2 ≤ ∑ a ∈ unitsBelow q, s a ^ 2 := by
    have hident : ∀ a : ℕ, s a ^ 2 =
        (1 + Real.cos (2 * Real.pi * ((2 ^ (k + 1) : ℕ) : ℝ) * a / q)) / 2 := by
      intro a
      dsimp only [s]
      have h2 := Real.cos_two_mul (2 * Real.pi * ((2 ^ k : ℕ) : ℝ) * a / q)
      have harg : 2 * (2 * Real.pi * ((2 ^ k : ℕ) : ℝ) * a / q) =
          2 * Real.pi * ((2 ^ (k + 1) : ℕ) : ℝ) * a / q := by
        rw [pow_succ']
        push_cast
        ring
      rw [harg] at h2
      linarith
    simp_rw [hident, ← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_const,
      unitsBelow_card, nsmul_eq_mul, mul_one, hsum_cos2]
    linarith
  have habs_ge_sq : ∑ a ∈ unitsBelow q, s a ^ 2 ≤ ∑ a ∈ unitsBelow q, |s a| := by
    refine Finset.sum_le_sum fun a _ => ?_
    have hle1 : |s a| ≤ 1 := Real.abs_cos_le_one _
    rw [← sq_abs (s a)]
    nlinarith [abs_nonneg (s a)]
  have hpos_s : ((q.totient : ℝ) - 3) / 4 ≤ ∑ a ∈ unitsBelow q, if 0 ≤ s a then s a else 0 := by
    have hsplit : ∀ a : ℕ, (if 0 ≤ s a then s a else 0) = (|s a| + s a) / 2 := by
      intro a
      split_ifs with h
      · rw [abs_of_nonneg h]; ring
      · rw [abs_of_neg (lt_of_not_ge h)]; ring
    simp_rw [hsplit, ← Finset.sum_div, Finset.sum_add_distrib, hsum_s]
    linarith
  have hpos_c : ((q.totient : ℝ) - 3) / (4 * (q.totient : ℝ) ^ 2) ≤
      ∑ a ∈ unitsBelow q, if 0 ≤ c a then c a else 0 := by
    have hpos : 0 < (q.totient : ℝ) ^ 2 := sq_pos_of_pos hφ_pos
    have hterm : ∀ a ∈ unitsBelow q,
        (if 0 ≤ c a then c a else 0) = (if 0 ≤ s a then s a else 0) / (q.totient : ℝ) ^ 2 := by
      intro a ha
      rw [hc_eq a ha]
      by_cases hs : 0 ≤ s a
      · rw [if_pos (div_nonneg hs hpos.le), if_pos hs]
      · have hs' : s a < 0 := lt_of_not_ge hs
        rw [if_neg (not_le.mpr (div_neg_of_neg_of_pos hs' hpos)), if_neg hs]
        ring
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_div]
    have hdiv := div_le_div_of_nonneg_right hpos_s (by positivity : 0 ≤ (q.totient : ℝ) ^ 2)
    simpa [div_div] using hdiv
  have htot_le : (q.totient : ℝ) ≤ q := by exact_mod_cast Nat.totient_le q
  have hφ6R : (6 : ℝ) ≤ q.totient := by exact_mod_cast hφ6
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq_pos
  have h1 : 1 / (8 * (q : ℝ)) ≤ 1 / (8 * (q.totient : ℝ)) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
  have h2 : 1 / (8 * (q.totient : ℝ)) ≤ ((q.totient : ℝ) - 3) / (4 * (q.totient : ℝ) ^ 2) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  linarith

/-! ### 2. Squarefree density in `(Q/2, Q]` -/

private theorem card_multiples_Ioc (a b m : ℕ) (hm : 0 < m) :
    (((Finset.Ioc a b).filter (fun q => m ∣ q)).card : ℝ) ≤ ((b - a : ℕ) : ℝ) / m + 1 := by
  have hsub : ((Finset.Ioc a b).filter (fun q => m ∣ q)).image (fun q => q / m) ⊆
      Finset.Ioc (a / m) (b / m) := by
    intro t ht
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp ht
    have hq' := Finset.mem_filter.mp hq
    have hIoc := Finset.mem_Ioc.mp hq'.1
    refine Finset.mem_Ioc.mpr ⟨?_, Nat.div_le_div_right hIoc.2⟩
    have hqm : m * (q / m) = q := Nat.mul_div_cancel' hq'.2
    have hdiv_lt : a / m < q / m := by
      by_contra hle
      have hle' : q / m ≤ a / m := not_lt.mp hle
      have : q ≤ m * (a / m) := by
        calc q = m * (q / m) := hqm.symm
          _ ≤ m * (a / m) := Nat.mul_le_mul_left m hle'
      have := this.trans (Nat.mul_div_le a m)
      omega
    exact hdiv_lt
  have hinj : Set.InjOn (fun q => q / m) ↑((Finset.Ioc a b).filter (fun q => m ∣ q)) := by
    intro x hx y hy hxy
    dsimp only at hxy
    have hx' := (Finset.mem_filter.mp (Finset.mem_coe.mp hx)).2
    have hy' := (Finset.mem_filter.mp (Finset.mem_coe.mp hy)).2
    calc x = m * (x / m) := (Nat.mul_div_cancel' hx').symm
      _ = m * (y / m) := by rw [hxy]
      _ = y := Nat.mul_div_cancel' hy'
  have hcard : ((Finset.Ioc a b).filter (fun q => m ∣ q)).card ≤ b / m - a / m := by
    rw [← Finset.card_image_of_injOn hinj]
    exact (Finset.card_le_card hsub).trans (by rw [Nat.card_Ioc])
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hmul : (b / m - a / m : ℕ) * m ≤ (b - a) + m := by
    by_cases hab : a ≤ b
    · by_cases hle : a / m ≤ b / m
      · have h1 : (b / m) * m ≤ b := Nat.div_mul_le_self b m
        have h2 : a < (a / m) * m + m := Nat.lt_div_mul_add hm
        have h3 : (b / m - a / m) * m + (a / m) * m = (b / m) * m := by
          rw [← Nat.add_mul, Nat.sub_add_cancel hle]
        omega
      · have h0 : b / m - a / m = 0 := Nat.sub_eq_zero_of_le (not_le.mp hle).le
        rw [h0, zero_mul]
        exact Nat.zero_le _
    · have hle : b / m ≤ a / m := Nat.div_le_div_right (by omega)
      have h0 : b / m - a / m = 0 := Nat.sub_eq_zero_of_le hle
      rw [h0, zero_mul]
      exact Nat.zero_le _
  have hcardR : (((Finset.Ioc a b).filter (fun q => m ∣ q)).card : ℝ) ≤
      (b / m - a / m : ℕ) := by exact_mod_cast hcard
  have hmulR : ((b / m - a / m : ℕ) : ℝ) * m ≤ ((b - a : ℕ) : ℝ) + m := by
    exact_mod_cast hmul
  rw [← le_div_iff₀ hmR] at hmulR
  have hdiv_eq : (((b - a : ℕ) : ℝ) + m) / m = ((b - a : ℕ) : ℝ) / m + 1 := by
    field_simp [hmR.ne']
  linarith

private theorem inv_sq_tail_sum (M : ℕ) :
    ∑ m ∈ Finset.Icc 7 M, (1 : ℝ) / (m : ℝ) ^ 2 ≤ 1 / 6 := by
  have htele : ∀ m ∈ Finset.Icc 7 M,
      (1 : ℝ) / (m : ℝ) ^ 2 ≤ 1 / ((m : ℝ) - 1) - 1 / (m : ℝ) := by
    intro m hm
    have hm7 : 7 ≤ m := (Finset.mem_Icc.mp hm).1
    have hmR : (7 : ℝ) ≤ m := by exact_mod_cast hm7
    have hm0 : (0 : ℝ) < (m : ℝ) := by linarith
    have hm1 : (0 : ℝ) < (m : ℝ) - 1 := by linarith
    rw [div_sub_div _ _ hm1.ne' hm0.ne', div_le_div_iff₀ (by positivity) (mul_pos hm1 hm0)]
    nlinarith
  have hle : ∑ m ∈ Finset.Icc 7 M, (1 : ℝ) / (m : ℝ) ^ 2 ≤
      ∑ m ∈ Finset.Icc 7 M, (1 / ((m : ℝ) - 1) - 1 / (m : ℝ)) :=
    Finset.sum_le_sum htele
  have hsum : ∀ N : ℕ, 6 ≤ N →
      ∑ m ∈ Finset.Icc 7 N, (1 / ((m : ℝ) - 1) - 1 / (m : ℝ)) = 1 / 6 - 1 / (N : ℝ) := by
    intro N hN
    induction N, hN using Nat.le_induction with
    | base => simp
    | @succ N hN ih =>
        have hIcc : Finset.Icc 7 (N + 1) = insert (N + 1) (Finset.Icc 7 N) := by
          ext m; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
        have hnot : N + 1 ∉ Finset.Icc 7 N := by simp
        rw [hIcc, Finset.sum_insert hnot, ih]
        push_cast
        ring
  by_cases hM : 6 ≤ M
  · rw [hsum M hM] at hle
    have : 0 ≤ (1 : ℝ) / (M : ℝ) := by positivity
    linarith
  · have hemp : Finset.Icc 7 M = ∅ := Finset.Icc_eq_empty (by omega)
    rw [hemp, Finset.sum_empty]
    norm_num

private theorem exists_prime_sq_dvd_of_not_squarefree {q : ℕ} (hq : 0 < q) (hns : ¬ Squarefree q) :
    ∃ p : ℕ, p.Prime ∧ p ^ 2 ∣ q := by
  by_contra hno
  push_neg at hno
  apply hns
  intro d hd
  by_contra hnu
  have hd2 : 2 ≤ d := by
    rcases eq_or_ne d 0 with rfl | hd0
    · simp at hd; omega
    · have : d ≠ 1 := fun h => hnu (h ▸ isUnit_one)
      omega
  let p := d.minFac
  have hp : p.Prime := Nat.minFac_prime (by omega)
  have hpd : p ∣ d := Nat.minFac_dvd d
  exact hno p hp (by rw [sq]; exact (mul_dvd_mul hpd hpd).trans hd)

private theorem squarefree_reciprocal_lower (Q : ℕ) (hQ : 1600 ≤ Q) :
    1 / 80 ≤ ∑ q ∈ (Finset.Ioc (Q / 2) Q).filter Squarefree, (1 : ℝ) / (8 * (q : ℝ)) := by
  let S := Finset.Ioc (Q / 2) Q
  let M := Nat.sqrt Q
  let Pset := insert 2 (insert 3 (insert 5 (Finset.Icc 7 M)))
  have hnon_sub : S.filter (fun q => ¬ Squarefree q) ⊆
      Pset.biUnion (fun p => S.filter (fun q => p ^ 2 ∣ q)) := by
    intro q hq
    rw [Finset.mem_filter] at hq
    have hq_pos : 0 < q := by have := (Finset.mem_Ioc.mp hq.1).1; omega
    obtain ⟨p, hp_pr, hp2⟩ := exists_prime_sq_dvd_of_not_squarefree hq_pos hq.2
    refine Finset.mem_biUnion.mpr ⟨p, ?_, Finset.mem_filter.mpr ⟨hq.1, hp2⟩⟩
    have hp_le : p ≤ M :=
      Nat.le_sqrt.mpr (by rw [← sq]; exact (Nat.le_of_dvd hq_pos hp2).trans (Finset.mem_Ioc.mp hq.1).2)
    have hp2_ge : 2 ≤ p := hp_pr.two_le
    have hp4 : p ≠ 4 := fun h => by subst h; norm_num at hp_pr
    have hp6 : p ≠ 6 := fun h => by subst h; norm_num at hp_pr
    simp only [Pset, Finset.mem_insert, Finset.mem_Icc]
    omega
  have hlen : Q - Q / 2 = S.card := by simp [S, Nat.card_Ioc]
  let L : ℝ := ((Q - Q / 2 : ℕ) : ℝ)
  have hnon_card : ((S.filter (fun q => ¬ Squarefree q)).card : ℝ) ≤
      (511 / 900 : ℝ) * L + (Pset.card : ℝ) := by
    calc
      ((S.filter (fun q => ¬ Squarefree q)).card : ℝ)
          ≤ ((Pset.biUnion (fun p => S.filter (fun q => p ^ 2 ∣ q))).card : ℝ) := by
              exact_mod_cast Finset.card_le_card hnon_sub
      _ ≤ ∑ p ∈ Pset, ((S.filter (fun q => p ^ 2 ∣ q)).card : ℝ) := by
              exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ p ∈ Pset, (L / (p : ℝ) ^ 2 + 1) := by
              refine Finset.sum_le_sum fun p hp => ?_
              have hp_pos : 0 < p := by
                simp only [Pset, Finset.mem_insert, Finset.mem_Icc] at hp
                omega
              have hcm := card_multiples_Ioc (Q / 2) Q (p ^ 2) (pow_pos hp_pos 2)
              simpa [S, L] using hcm
      _ = L * (∑ p ∈ Pset, (1 : ℝ) / (p : ℝ) ^ 2) + (Pset.card : ℝ) := by
              rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one, Finset.mul_sum]
              congr 1
              refine Finset.sum_congr rfl fun p _ => by ring
      _ ≤ L * (511 / 900 : ℝ) + (Pset.card : ℝ) := by
              have hPsum : ∑ p ∈ Pset, (1 : ℝ) / (p : ℝ) ^ 2 ≤ 511 / 900 := by
                have h2not : (2 : ℕ) ∉ insert 3 (insert 5 (Finset.Icc 7 M)) := by simp
                have h3not : (3 : ℕ) ∉ insert 5 (Finset.Icc 7 M) := by simp
                have h5not : (5 : ℕ) ∉ Finset.Icc 7 M := by simp
                dsimp only [Pset]
                rw [Finset.sum_insert h2not, Finset.sum_insert h3not, Finset.sum_insert h5not]
                have htail := inv_sq_tail_sum M
                norm_num at htail ⊢
                linarith
              have hL0 : 0 ≤ L := Nat.cast_nonneg _
              nlinarith
      _ = (511 / 900 : ℝ) * L + (Pset.card : ℝ) := by ring
  have hPcard : Pset.card ≤ 3 + M := by
    have h1 : Pset.card ≤ (insert 3 (insert 5 (Finset.Icc 7 M))).card + 1 :=
      Finset.card_insert_le _ _
    have h2 : (insert 3 (insert 5 (Finset.Icc 7 M))).card ≤
        (insert 5 (Finset.Icc 7 M)).card + 1 := Finset.card_insert_le _ _
    have h3 : (insert 5 (Finset.Icc 7 M)).card ≤ (Finset.Icc 7 M).card + 1 :=
      Finset.card_insert_le _ _
    rw [Nat.card_Icc] at h3
    omega
  have hM_le : 40 * M ≤ Q := by
    have hM2 : M * M ≤ Q := Nat.sqrt_le Q
    have hM40 : 40 ≤ M := Nat.le_sqrt.mpr (by omega)
    nlinarith
  have hL_ge : Q ≤ 2 * (Q - Q / 2) := by omega
  have hP_le : (Pset.card : ℝ) ≤ (1 / 10 : ℝ) * L := by
    have h1 : (Pset.card : ℝ) ≤ 3 + (M : ℝ) := by exact_mod_cast hPcard
    have h2 : (40 : ℝ) * M ≤ Q := by exact_mod_cast hM_le
    have h3 : (Q : ℝ) ≤ 2 * L := by dsimp [L]; exact_mod_cast hL_ge
    have hQ1600 : (1600 : ℝ) ≤ Q := by exact_mod_cast hQ
    linarith
  have hsq_card : (L / 4 : ℝ) ≤ ((S.filter Squarefree).card : ℝ) := by
    have hdisj : Disjoint (S.filter Squarefree) (S.filter (fun q => ¬ Squarefree q)) :=
      Finset.disjoint_filter.mpr fun _ _ h1 h2 => h2 h1
    have hunion : S.filter Squarefree ∪ S.filter (fun q => ¬ Squarefree q) = S := by
      ext x
      simp only [Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
      · intro hx; by_cases h : Squarefree x <;> [left; right] <;> exact ⟨hx, h⟩
    have htot : (S.filter Squarefree).card + (S.filter (fun q => ¬ Squarefree q)).card = Q - Q / 2 := by
      rw [← Finset.card_union_of_disjoint hdisj, hunion, hlen]
    have htotR : ((S.filter Squarefree).card : ℝ) +
        ((S.filter (fun q => ¬ Squarefree q)).card : ℝ) = L := by
      dsimp only [L]
      exact_mod_cast htot
    linarith
  have hQ_pos : (0 : ℝ) < Q := by exact_mod_cast (by omega : 0 < Q)
  have hL_ge2 : (Q : ℝ) / 2 ≤ L := by
    have h3 : (Q : ℝ) ≤ 2 * L := by dsimp [L]; exact_mod_cast hL_ge
    linarith
  calc
    (1 / 80 : ℝ) ≤ (L / 4) / (8 * (Q : ℝ)) := by
      rw [le_div_iff₀ (by positivity)]
      linarith
    _ ≤ ((S.filter Squarefree).card : ℝ) * (1 / (8 * (Q : ℝ))) := by
      rw [div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_right hsq_card (by positivity)
    _ = ∑ _q ∈ S.filter Squarefree, (1 : ℝ) / (8 * (Q : ℝ)) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ q ∈ S.filter Squarefree, (1 : ℝ) / (8 * (q : ℝ)) := by
      refine Finset.sum_le_sum fun q hq => ?_
      have hq_mem := Finset.mem_Ioc.mp (Finset.mem_filter.mp hq).1
      have hq_pos : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
      have hq_le : (q : ℝ) ≤ Q := by exact_mod_cast hq_mem.2
      exact div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)

/-! ### 3. Kernel annulus lower bound -/

private theorem kernel_annulus_floor {n q : ℕ} (hn : 8 ≤ n) (hq_lo : cutoff n / 2 < q)
    (hq_hi : q ≤ cutoff n) :
    (n : ℝ) / 1024 ≤ intervalIntegral (fun β => ‖kernel n β‖ ^ 2) (width n q) (2 * width n q) volume := by
  have hw_pos : 0 < width n q := by
    unfold width
    have hq_pos : 0 < q := by omega
    have hQ_pos : 0 < cutoff n := cutoff_positive n
    positivity
  have hpoint : ∀ β ∈ Set.Icc (width n q) (2 * width n q),
      (Real.sin (Real.pi * ((n + 1 : ℕ) : ℝ) * β)) ^ 2 ≤
        (16 * Real.pi ^ 2 / (n : ℝ) ^ 2) * ‖kernel n β‖ ^ 2 := by
    intro β hβ
    have hβ_pos : 0 < β := lt_of_lt_of_le hw_pos hβ.1
    have hβ_hi : β ≤ 4 / (n : ℝ) := by
      have hq_ge : (cutoff n : ℝ) / 2 ≤ q := by
        have : cutoff n ≤ 2 * q := by omega
        have : (cutoff n : ℝ) ≤ 2 * (q : ℝ) := by exact_mod_cast this
        linarith
      have hqR : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
      have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      calc β ≤ 2 * width n q := hβ.2
        _ = 2 * (cutoff n : ℝ) / ((q : ℝ) * n) := by unfold width; ring
        _ ≤ 4 * (q : ℝ) / ((q : ℝ) * n) :=
            div_le_div_of_nonneg_right (by linarith) (by positivity)
        _ = 4 / (n : ℝ) := by field_simp [hqR.ne', hnR.ne']
    have hEpow : ∀ (j : ℕ) (x : ℝ), phase ((j : ℝ) * x) = phase x ^ j := by
      intro j x
      unfold phase
      rw [← Complex.exp_nat_mul]
      congr 1
      push_cast
      ring
    have hgeom : (1 - phase β) * kernel n β = 1 - phase (((n + 1 : ℕ) : ℝ) * β) := by
      unfold kernel
      simp_rw [hEpow]
      rw [mul_comm, geom_sum_mul_neg]
    have hsin_normSq : ∀ x : ℝ, ‖1 - phase x‖ ^ 2 = 4 * (Real.sin (Real.pi * x)) ^ 2 := by
      intro x
      have hnormSq : ‖1 - phase x‖ ^ 2 =
          (1 - Real.cos (2 * Real.pi * x)) ^ 2 + (-Real.sin (2 * Real.pi * x)) ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
        simp only [phase, Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im,
          Complex.exp_ofReal_mul_I, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
          Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, sub_zero, add_zero,
          Complex.add_im, Complex.mul_im, mul_one, zero_add, zero_sub]
        ring
      have hcos2 : Real.cos (2 * Real.pi * x) = 1 - 2 * (Real.sin (Real.pi * x)) ^ 2 := by
        have h := Real.cos_two_mul (Real.pi * x)
        rw [show 2 * (Real.pi * x) = 2 * Real.pi * x by ring] at h
        have hcs := Real.cos_sq_add_sin_sq (Real.pi * x)
        linarith
      have hcs2 := Real.cos_sq_add_sin_sq (2 * Real.pi * x)
      rw [hnormSq]
      nlinarith
    have hmul_eq : (Real.sin (Real.pi * β)) ^ 2 * ‖kernel n β‖ ^ 2 =
        (Real.sin (Real.pi * ((n + 1 : ℕ) : ℝ) * β)) ^ 2 := by
      have h1 : ‖(1 - phase β) * kernel n β‖ ^ 2 = ‖1 - phase (((n + 1 : ℕ) : ℝ) * β)‖ ^ 2 :=
        congrArg (· ^ 2) (congrArg norm hgeom)
      rw [norm_mul, mul_pow, hsin_normSq β, hsin_normSq (((n + 1 : ℕ) : ℝ) * β)] at h1
      rw [mul_assoc, ← mul_assoc Real.pi] at h1
      linarith
    have hsin_le : (Real.sin (Real.pi * β)) ^ 2 ≤ 16 * Real.pi ^ 2 / (n : ℝ) ^ 2 := by
      have hpiβ_nonneg : 0 ≤ Real.pi * β := by positivity
      have hsin_bd : |Real.sin (Real.pi * β)| ≤ Real.pi * β := by
        simpa [abs_of_nonneg hpiβ_nonneg] using Real.abs_sin_le_abs (x := Real.pi * β)
      have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      have hpiβ_hi : Real.pi * β ≤ 4 * Real.pi / (n : ℝ) := by
        calc Real.pi * β ≤ Real.pi * (4 / (n : ℝ)) :=
            mul_le_mul_of_nonneg_left hβ_hi Real.pi_pos.le
          _ = 4 * Real.pi / (n : ℝ) := by ring
      have hsq1 : (Real.sin (Real.pi * β)) ^ 2 ≤ (Real.pi * β) ^ 2 := by
        rw [← sq_abs (Real.sin (Real.pi * β))]
        exact sq_le_sq' (by linarith [abs_nonneg (Real.sin (Real.pi * β))]) hsin_bd
      have hsq2 : (Real.pi * β) ^ 2 ≤ (4 * Real.pi / (n : ℝ)) ^ 2 :=
        sq_le_sq' (by linarith) hpiβ_hi
      calc (Real.sin (Real.pi * β)) ^ 2 ≤ (4 * Real.pi / (n : ℝ)) ^ 2 := hsq1.trans hsq2
        _ = 16 * Real.pi ^ 2 / (n : ℝ) ^ 2 := by ring
    calc
      (Real.sin (Real.pi * ((n + 1 : ℕ) : ℝ) * β)) ^ 2
          = (Real.sin (Real.pi * β)) ^ 2 * ‖kernel n β‖ ^ 2 := hmul_eq.symm
      _ ≤ (16 * Real.pi ^ 2 / (n : ℝ) ^ 2) * ‖kernel n β‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hsin_le (sq_nonneg _)
  have hcont_sin : Continuous (fun β : ℝ => (Real.sin (Real.pi * ((n + 1 : ℕ) : ℝ) * β)) ^ 2) := by
    fun_prop
  have hcont_ker : Continuous (fun β : ℝ => ‖kernel n β‖ ^ 2) := by
    have hK : Continuous (kernel n) := by unfold kernel phase; fun_prop
    exact (hK.norm).pow 2
  have hint_sin :
      1 / (4 * (n : ℝ)) ≤
        intervalIntegral (fun β : ℝ => (Real.sin (Real.pi * ((n + 1 : ℕ) : ℝ) * β)) ^ 2)
          (width n q) (2 * width n q) volume := by
    let c : ℝ := 2 * Real.pi * ((n + 1 : ℕ) : ℝ)
    have hc_pos : 0 < c := by positivity
    let G : ℝ → ℝ := fun β => β / 2 - Real.sin (c * β) / (2 * c)
    have hGderiv : ∀ β ∈ Set.uIcc (width n q) (2 * width n q),
        HasDerivAt G ((Real.sin (Real.pi * ((n + 1 : ℕ) : ℝ) * β)) ^ 2) β := by
      intro β _
      have h1 : HasDerivAt (fun x : ℝ => x / 2) (1 / 2) β :=
        (hasDerivAt_id β).div_const 2
      have h2 : HasDerivAt (fun x : ℝ => Real.sin (c * x) / (2 * c))
          (Real.cos (c * β) * c / (2 * c)) β := by
        have hm : HasDerivAt (fun x : ℝ => c * x) c β := by
          simpa using (hasDerivAt_id β).const_mul c
        exact (hm.sin).div_const (2 * c)
      have hsub := h1.sub h2
      have hval : 1 / 2 - Real.cos (c * β) * c / (2 * c) =
          (Real.sin (Real.pi * ((n + 1 : ℕ) : ℝ) * β)) ^ 2 := by
        have hcos2 := Real.cos_two_mul (Real.pi * ((n + 1 : ℕ) : ℝ) * β)
        have hcs := Real.cos_sq_add_sin_sq (Real.pi * ((n + 1 : ℕ) : ℝ) * β)
        have harg : 2 * (Real.pi * ((n + 1 : ℕ) : ℝ) * β) = c * β := by dsimp [c]; ring
        rw [harg] at hcos2
        have hfrac : 1 / 2 - Real.cos (c * β) * c / (2 * c) = (1 - Real.cos (c * β)) / 2 := by
          field_simp [hc_pos.ne']
        rw [hfrac]
        linarith
      rwa [hval] at hsub
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hGderiv (hcont_sin.intervalIntegrable _ _)]
    have hdiff : G (2 * width n q) - G (width n q) =
        width n q / 2 - (Real.sin (c * (2 * width n q)) - Real.sin (c * width n q)) / (2 * c) := by
      dsimp only [G]
      ring
    rw [hdiff]
    have hw_lb : 1 / (n : ℝ) ≤ width n q := by
      unfold width
      have hqR : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
      have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      have hqQ : (q : ℝ) ≤ cutoff n := by exact_mod_cast hq_hi
      rw [div_le_div_iff₀ hnR (mul_pos hqR hnR)]
      nlinarith
    have hsin_bd : (Real.sin (c * (2 * width n q)) - Real.sin (c * width n q)) / (2 * c) ≤ 1 / c := by
      have hs1 := Real.sin_le_one (c * (2 * width n q))
      have hs2 := Real.neg_one_le_sin (c * width n q)
      have hdiv : (Real.sin (c * (2 * width n q)) - Real.sin (c * width n q)) / (2 * c) ≤
          2 / (2 * c) := div_le_div_of_nonneg_right (by linarith) (by positivity)
      have h2c : (2 : ℝ) / (2 * c) = 1 / c := by field_simp [hc_pos.ne']
      linarith
    have hc_lb : 6 * (n : ℝ) ≤ c := by
      dsimp only [c]
      have hpi3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
      have hn1 : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ n
      have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      nlinarith
    have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have h1c : 1 / c ≤ 1 / (6 * (n : ℝ)) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) hc_lb
    have hfrac_lb : 1 / (4 * (n : ℝ)) ≤ (1 / (n : ℝ)) / 2 - 1 / (6 * (n : ℝ)) := by
      field_simp [hnR.ne']
      norm_num
    linarith
  have hmono := intervalIntegral.integral_mono_on (μ := volume) (by linarith)
    (hcont_sin.intervalIntegrable _ _) ((hcont_ker.const_mul _).intervalIntegrable _ _) hpoint
  rw [intervalIntegral.integral_const_mul] at hmono
  have h1 : 1 / (4 * (n : ℝ)) ≤ (16 * Real.pi ^ 2 / (n : ℝ) ^ 2) *
      intervalIntegral (fun β => ‖kernel n β‖ ^ 2) (width n q) (2 * width n q) volume :=
    hint_sin.trans hmono
  have hpi4 : Real.pi < 4 := Real.pi_lt_four
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hpi2 : Real.pi ^ 2 ≤ 16 := by nlinarith [Real.pi_pos]
  have hcoeff : 0 < 16 * Real.pi ^ 2 / (n : ℝ) ^ 2 := by positivity
  have hupper : (16 * Real.pi ^ 2 / (n : ℝ) ^ 2) *
      intervalIntegral (fun β => ‖kernel n β‖ ^ 2) (width n q) (2 * width n q) volume ≤
      (256 / (n : ℝ) ^ 2) *
        intervalIntegral (fun β => ‖kernel n β‖ ^ 2) (width n q) (2 * width n q) volume := by
    refine mul_le_mul_of_nonneg_right ?_ ?_
    · exact div_le_div_of_nonneg_right (by linarith) (by positivity)
    · exact intervalIntegral.integral_nonneg (by linarith) fun _ _ => sq_nonneg _
  have h2 : 1 / (4 * (n : ℝ)) ≤ (256 / (n : ℝ) ^ 2) *
      intervalIntegral (fun β => ‖kernel n β‖ ^ 2) (width n q) (2 * width n q) volume :=
    h1.trans hupper
  have h3 : (n : ℝ) / 1024 = (1 / (4 * (n : ℝ))) / (256 / (n : ℝ) ^ 2) := by
    field_simp [hnR.ne']
    ring
  rw [h3, div_le_iff₀ (by positivity), mul_comm _ (256 / (n : ℝ) ^ 2)]
  exact h2

/-! ### 4. Disjointness of dilated windows and `o(n)` model error -/

private theorem dilated_cross_eq {n q s a b : ℕ} {t : ℝ} (hn : 8 * (cutoff n) ^ 2 < n)
    (hq : q ∈ Finset.Icc 1 (cutoff n)) (hs : s ∈ Finset.Icc 1 (cutoff n))
    (ha : |t - center q a| ≤ 2 * width n q) (hb : |t - center s b| ≤ 2 * width n s) :
    a * s = b * q := by
  obtain ⟨hq₁, hqQ⟩ := Finset.mem_Icc.mp hq
  obtain ⟨hs₁, hsQ⟩ := Finset.mem_Icc.mp hs
  have hqr : 0 < (q : ℝ) := by exact_mod_cast hq₁
  have hsr : 0 < (s : ℝ) := by exact_mod_cast hs₁
  have hnr : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  let Q := cutoff n
  have hsmall : 2 * Q * s + 2 * Q * q < n := by
    nlinarith only [hn, Nat.mul_le_mul_left Q hsQ, Nat.mul_le_mul_left Q hqQ]
  have hradii : 2 * (Q : ℝ) / (q * n) + 2 * Q / (s * n) < 1 / (q * s) := calc
    _ = ((2 * (Q : ℝ) * s + 2 * Q * q) / (q * s * n)) := by field_simp
    _ < (n : ℝ) / (q * s * n) := (div_lt_div_iff_of_pos_right (by positivity)).mpr (by exact_mod_cast hsmall)
    _ = _ := by field_simp
  by_contra hne
  have hsep : 1 / ((q : ℝ) * s) ≤ |(a : ℝ) / q - b / s| := by
    rw [show (a : ℝ) / q - b / s = (a * s - b * q) / (q * s) by field_simp, abs_div,
      abs_of_pos (mul_pos hqr hsr)]
    apply (div_le_div_iff_of_pos_right (mul_pos hqr hsr)).mpr
    rcases lt_or_gt_of_ne hne with hab | hba
    · have hgap : (a : ℝ) * s + 1 ≤ b * q := by exact_mod_cast Nat.succ_le_of_lt hab
      linarith [neg_le_abs ((a : ℝ) * s - b * q)]
    · have hgap : (b : ℝ) * q + 1 ≤ a * s := by exact_mod_cast Nat.succ_le_of_lt hba
      linarith [le_abs_self ((a : ℝ) * s - b * q)]
  have ht := abs_sub_le ((a : ℝ) / q) t ((b : ℝ) / s)
  rw [abs_sub_comm ((a : ℝ) / q) t] at ht
  change |t - (a : ℝ) / q| ≤ 2 * ((Q : ℝ) / (q * n)) at ha
  change |t - (b : ℝ) / s| ≤ 2 * ((Q : ℝ) / (s * n)) at hb
  rw [← mul_div_assoc] at ha hb
  linarith

private theorem dilated_center_unique {n q s a b : ℕ} {t : ℝ} (hn : 8 * (cutoff n) ^ 2 < n)
    (hq : q ∈ Finset.Icc 1 (cutoff n)) (hs : s ∈ Finset.Icc 1 (cutoff n))
    (ha : a ∈ numerators q) (hb : b ∈ numerators s)
    (hta : |t - center q a| ≤ 2 * width n q) (htb : |t - center s b| ≤ 2 * width n s) :
    q = s ∧ a = b := by
  have he := dilated_cross_eq hn hq hs hta htb
  have hc := (Finset.mem_filter.mp ha).2
  have hc' := (Finset.mem_filter.mp hb).2
  have hqs : q ∣ s := hc.symm.dvd_of_dvd_mul_left (he ▸ dvd_mul_left q b)
  have hsq : s ∣ q := hc'.symm.dvd_of_dvd_mul_left (he.symm ▸ dvd_mul_left s a)
  obtain rfl := Nat.dvd_antisymm hqs hsq
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_right (Finset.mem_Icc.mp hq).1 he⟩

private theorem norm_phase_local (x : ℝ) : ‖phase x‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

private theorem primeWeight_nonneg_local (k : ℕ) : 0 ≤ primeWeight k := by
  unfold primeWeight
  split_ifs with h
  · exact Real.log_nonneg (by exact_mod_cast h.one_le)
  · exact le_rfl

private theorem sum_primeWeight_local (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), primeWeight k = Chebyshev.theta n := by
  rw [Chebyshev.theta_eq_sum_primesLE_log, Nat.primesLE_eq_filter_range, Finset.sum_filter]
  rfl

private theorem unitMean_norm_local (q a : ℕ) (hq : 0 < q) : ‖unitMean q a‖ ≤ 1 := by
  let U := (Finset.range q).filter (fun r => r.Coprime q)
  have hcard : U.card = q.totient := by
    rw [Nat.totient_eq_card_coprime]
    congr 1
    ext k
    simp [U, Nat.coprime_comm]
  have hφ : 0 < (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
  unfold unitMean
  rw [norm_div, Complex.norm_natCast, div_le_one hφ]
  refine (norm_sum_le _ _).trans ?_
  change ∑ r ∈ U, ‖phase ((r : ℝ) * ((a : ℝ) / q))‖ ≤ _
  simp only [norm_phase_local, Finset.sum_const, nsmul_eq_mul, mul_one, hcard, le_refl]

private theorem dilated_arc_error {n q a : ℕ} (hn : 1 ≤ n) (hq : 0 < q) (_hQ : q ≤ cutoff n)
    {β : ℝ} (hβ : |β| ≤ 2 * width n q) :
    modelError n q a β ≤
      prefixError n ((a : ℝ) / q) (unitMean q a) * (1 + 4 * Real.pi * ((cutoff n : ℝ) / q)) *
        ((Real.log 4 + 2) * (n : ℝ)) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hscale : (n : ℝ) * |β| ≤ 2 * ((cutoff n : ℝ) / q) := by
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hq').mpr
    have hβ' : |β| ≤ 2 * (cutoff n : ℝ) / ((q : ℝ) * n) := by
      calc |β| ≤ 2 * width n q := hβ
        _ = 2 * (cutoff n : ℝ) / ((q : ℝ) * n) := by unfold width; ring
    calc (n : ℝ) * |β| * q = |β| * ((q : ℝ) * n) := by ring
      _ ≤ 2 * (cutoff n : ℝ) := (le_div_iff₀ (mul_pos hq' hn')).mp hβ'
  have hD : 0 ≤ prefixError n ((a : ℝ) / q) (unitMean q a) := by
    unfold prefixError
    refine (norm_nonneg (∑ k ∈ Finset.range 0,
      centerErrorTerm ((a : ℝ) / q) (unitMean q a) k)).trans ?_
    exact Finset.le_sup' (fun m => ‖∑ k ∈ Finset.range m,
      centerErrorTerm ((a : ℝ) / q) (unitMean q a) k‖)
      (Finset.mem_range.mpr (Nat.zero_lt_succ (n + 1)))
  have h1 : ‖primeSum n ((a : ℝ) / q + β) - unitMean q a * kernel n β‖ ≤
      prefixError n ((a : ℝ) / q) (unitMean q a) * (1 + 4 * Real.pi * ((cutoff n : ℝ) / q)) := by
    refine (shifted_sum_error n ((a : ℝ) / q) β (unitMean q a)).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ hD
    have : 2 * Real.pi * (n : ℝ) * |β| ≤ 4 * Real.pi * ((cutoff n : ℝ) / q) := by
      calc 2 * Real.pi * (n : ℝ) * |β| = 2 * Real.pi * ((n : ℝ) * |β|) := by ring
        _ ≤ 2 * Real.pi * (2 * ((cutoff n : ℝ) / q)) :=
            mul_le_mul_of_nonneg_left hscale (by positivity)
        _ = 4 * Real.pi * ((cutoff n : ℝ) / q) := by ring
    linarith
  have hsum : ‖primeSum n ((a : ℝ) / q + β)‖ ≤ Chebyshev.theta n := by
    rw [primeSum, ← sum_primeWeight_local]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [norm_mul, norm_phase_local, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (primeWeight_nonneg_local k)]
  have hkernel : ‖kernel n β‖ ≤ (n + 1 : ℕ) := by
    unfold kernel
    refine (norm_sum_le _ _).trans ?_
    simp [norm_phase_local]
  have hU := unitMean_norm_local q a hq
  have hplus : ‖primeSum n ((a : ℝ) / q + β) + unitMean q a * kernel n β‖ ≤
      (Real.log 4 + 2) * (n : ℝ) := by
    have h1n : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hcard := mul_le_mul_of_nonneg_right hU (show 0 ≤ (n : ℝ) + 1 by positivity)
    have hth := Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg n)
    have hadd : ‖primeSum n ((a : ℝ) / q + β) + unitMean q a * kernel n β‖ ≤
        Chebyshev.theta n + ‖unitMean q a‖ * ((n + 1 : ℕ) : ℝ) := by
      refine (norm_add_le _ _).trans (add_le_add hsum ?_)
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left hkernel (norm_nonneg _)
    push_cast at hcard hadd ⊢
    nlinarith only [hadd, hth, hcard, h1n]
  unfold modelError integrand
  dsimp only
  rw [← sub_mul, norm_mul, norm_phase_local, mul_one,
    show (primeSum n ((a : ℝ) / q + β)) ^ 2 - (unitMean q a * kernel n β) ^ 2 =
      (primeSum n ((a : ℝ) / q + β) - unitMean q a * kernel n β) *
        (primeSum n ((a : ℝ) / q + β) + unitMean q a * kernel n β) by ring,
    norm_mul]
  exact mul_le_mul h1 hplus (norm_nonneg _) (by positivity)

private theorem total_dilated_error_sublinear :
    ∀ᶠ n : ℕ in atTop,
      ∑ q ∈ Finset.Icc 1 (cutoff n), ∑ a ∈ numerators q,
        ((∫ β in (-2 * width n q)..(-width n q), modelError n q a β) +
          (∫ β in (width n q)..(2 * width n q), modelError n q a β)) ≤ (n : ℝ) / 200000 := by
  obtain ⟨M, hM, hpre⟩ := uniform_prefix_error
  let C : ℝ := 4 * ((1 + 4 * Real.pi) * (Real.log 4 + 2))
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hlimit := (envelope_saving M).const_mul (C * 16 ^ 4)
  simp only [mul_zero] at hlimit
  have hl := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hpre, eventually_ge_atTop (2 : ℕ), hl.eventually_ge_atTop 1,
    hlimit.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 200000)] with n hp hn hL hlim
  change (1 : ℝ) ≤ Real.log n at hL
  have hn1 : 1 ≤ n := by omega
  have hQ1 : 1 ≤ cutoff n := cutoff_positive n
  have hE : 0 ≤ errorEnvelope M n := by unfold errorEnvelope; positivity
  let B : ℝ := 2 * (cutoff n : ℝ) ^ 2 * errorEnvelope M n * ((1 + 4 * Real.pi) * (Real.log 4 + 2))
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hsingle : ∀ q ∈ Finset.Icc 1 (cutoff n), ∀ a ∈ numerators q,
      ((∫ β in (-2 * width n q)..(-width n q), modelError n q a β) +
        (∫ β in (width n q)..(2 * width n q), modelError n q a β)) ≤ B := by
    intro q hq a _
    have hq1 := (Finset.mem_Icc.mp hq).1
    have hqQ := (Finset.mem_Icc.mp hq).2
    have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq1
    have hQ' : (q : ℝ) ≤ cutoff n := by exact_mod_cast hqQ
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
    have hw_pos : 0 ≤ width n q := width_nonneg n q
    have hpt : ∀ β ∈ Set.Icc (-2 * width n q) (2 * width n q), modelError n q a β ≤
        errorEnvelope M n * ((1 + 4 * Real.pi) * (cutoff n : ℝ)) * ((Real.log 4 + 2) * (n : ℝ)) := by
      intro β hβ
      have hβ' : |β| ≤ 2 * width n q := abs_le.mpr ⟨by linarith [hβ.1], hβ.2⟩
      have hd := dilated_arc_error (a := a) hn1 hq1 hqQ hβ'
      have hscale : prefixError n ((a : ℝ) / q) (unitMean q a) *
          (1 + 4 * Real.pi * ((cutoff n : ℝ) / q)) ≤
          errorEnvelope M n * ((1 + 4 * Real.pi) * (cutoff n : ℝ)) := by
        calc _ ≤ ((q : ℝ) * errorEnvelope M n) * (1 + 4 * Real.pi * ((cutoff n : ℝ) / q)) :=
              mul_le_mul_of_nonneg_right (hp q a hq1 hqQ) (by positivity)
          _ = errorEnvelope M n * ((q : ℝ) + 4 * Real.pi * cutoff n) := by
              have hq_ne : (q : ℝ) ≠ 0 := by linarith
              field_simp [hq_ne]
          _ ≤ _ := mul_le_mul_of_nonneg_left (by nlinarith only [hQ']) hE
      exact hd.trans (mul_le_mul_of_nonneg_right hscale (by positivity))
    have hc : Continuous (modelError n q a) := by
      unfold modelError integrand primeSum kernel phase
      fun_prop
    have hintL : ∫ β in (-2 * width n q)..(-width n q), modelError n q a β ≤
        width n q * (errorEnvelope M n * ((1 + 4 * Real.pi) * (cutoff n : ℝ)) *
          ((Real.log 4 + 2) * (n : ℝ))) := by
      calc _ ≤ ∫ _β in (-2 * width n q)..(-width n q),
            errorEnvelope M n * ((1 + 4 * Real.pi) * (cutoff n : ℝ)) * ((Real.log 4 + 2) * (n : ℝ)) :=
          intervalIntegral.integral_mono_on (by linarith) (hc.intervalIntegrable _ _) (by simp)
            fun β hβ => hpt β ⟨hβ.1, hβ.2.trans (by linarith [hw_pos])⟩
        _ = _ := by rw [intervalIntegral.integral_const, smul_eq_mul]; ring
    have hintR : ∫ β in (width n q)..(2 * width n q), modelError n q a β ≤
        width n q * (errorEnvelope M n * ((1 + 4 * Real.pi) * (cutoff n : ℝ)) *
          ((Real.log 4 + 2) * (n : ℝ))) := by
      calc _ ≤ ∫ _β in (width n q)..(2 * width n q),
            errorEnvelope M n * ((1 + 4 * Real.pi) * (cutoff n : ℝ)) * ((Real.log 4 + 2) * (n : ℝ)) :=
          intervalIntegral.integral_mono_on (by linarith) (hc.intervalIntegrable _ _) (by simp)
            fun β hβ => hpt β ⟨by linarith [hβ.1, hw_pos], hβ.2⟩
        _ = _ := by rw [intervalIntegral.integral_const, smul_eq_mul]; ring
    have hlength : width n q ≤ (cutoff n : ℝ) / n := by
      unfold width
      exact div_le_div_of_nonneg_left (by positivity) hnR (by nlinarith)
    calc
      (∫ β in (-2 * width n q)..(-width n q), modelError n q a β) +
          (∫ β in (width n q)..(2 * width n q), modelError n q a β)
          ≤ width n q * (errorEnvelope M n * ((1 + 4 * Real.pi) * (cutoff n : ℝ)) *
              ((Real.log 4 + 2) * (n : ℝ))) +
            width n q * (errorEnvelope M n * ((1 + 4 * Real.pi) * (cutoff n : ℝ)) *
              ((Real.log 4 + 2) * (n : ℝ))) := add_le_add hintL hintR
      _ = 2 * width n q * (errorEnvelope M n * ((1 + 4 * Real.pi) * (cutoff n : ℝ)) *
            ((Real.log 4 + 2) * (n : ℝ))) := by ring
      _ ≤ 2 * ((cutoff n : ℝ) / n) * (errorEnvelope M n * ((1 + 4 * Real.pi) * (cutoff n : ℝ)) *
            ((Real.log 4 + 2) * (n : ℝ))) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlength (by norm_num)) (by positivity)
      _ = B := by dsimp [B]; field_simp [hnR.ne']
  have htot :
      ∑ q ∈ Finset.Icc 1 (cutoff n), ∑ a ∈ numerators q,
        ((∫ β in (-2 * width n q)..(-width n q), modelError n q a β) +
          (∫ β in (width n q)..(2 * width n q), modelError n q a β)) ≤
      C * (cutoff n : ℝ) ^ 4 * errorEnvelope M n := by
    calc
      _ ≤ ∑ q ∈ Finset.Icc 1 (cutoff n), ∑ _a ∈ numerators q, B :=
          Finset.sum_le_sum fun q hq => Finset.sum_le_sum fun a ha => hsingle q hq a ha
      _ ≤ ∑ q ∈ Finset.Icc 1 (cutoff n), ((q : ℝ) + 1) * B := by
          refine Finset.sum_le_sum fun q _ => ?_
          rw [Finset.sum_const, nsmul_eq_mul]
          refine mul_le_mul_of_nonneg_right ?_ hB
          have hsub : numerators q ⊆ Finset.range (q + 1) := Finset.filter_subset _ _
          exact_mod_cast (Finset.card_le_card hsub).trans_eq (Finset.card_range (q + 1))
      _ ≤ ∑ _q ∈ Finset.Icc 1 (cutoff n), ((cutoff n : ℝ) + 1) * B := by
          refine Finset.sum_le_sum fun q hq => mul_le_mul_of_nonneg_right ?_ hB
          exact_mod_cast Nat.add_le_add_right (Finset.mem_Icc.mp hq).2 1
      _ = (cutoff n : ℝ) * (((cutoff n : ℝ) + 1) * B) := by simp [Nat.card_Icc]
      _ ≤ (cutoff n : ℝ) * ((2 * (cutoff n : ℝ)) * B) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by linarith [show (1 : ℝ) ≤ cutoff n by exact_mod_cast hQ1]) hB) (Nat.cast_nonneg _)
      _ = C * (cutoff n : ℝ) ^ 4 * errorEnvelope M n := by dsimp [B, C]; ring
  have hpow := pow_le_pow_left₀ (Nat.cast_nonneg (α := ℝ) (cutoff n)) (cutoff_le_log_sq hn) 4
  have hlpow : (Real.log n) ^ 8 ≤ (Real.log n) ^ 10 := pow_le_pow_right₀ hL (by decide)
  have hcomp : (cutoff n : ℝ) ^ 4 ≤ 16 ^ 4 * (Real.log n) ^ 10 := by
    calc _ ≤ _ := hpow
      _ = 16 ^ 4 * (Real.log n) ^ 8 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hlpow (by norm_num)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  have hdiv : C * (cutoff n : ℝ) ^ 4 * errorEnvelope M n / n < (1 : ℝ) / 200000 := calc
    C * (cutoff n : ℝ) ^ 4 * errorEnvelope M n / n
        ≤ C * (16 ^ 4 * (Real.log n) ^ 10) * errorEnvelope M n / n :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcomp hC) hE) hnR.le
    _ = C * 16 ^ 4 * ((Real.log n) ^ 10 * errorEnvelope M n / n) := by ring
    _ < 1 / 200000 := hlim
  exact htot.trans ((div_le_iff₀ hnR).mp hdiv.le |>.trans_eq (by ring))

private theorem exists_pow2_witness (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ Even n ∧ 8 ≤ n ∧ 1600 ≤ cutoff n ∧ 8 * (cutoff n) ^ 2 < n ∧
      (∑ q ∈ Finset.Icc 1 (cutoff n), ∑ a ∈ numerators q,
        ((∫ β in (-2 * width n q)..(-width n q), modelError n q a β) +
          (∫ β in (width n q)..(2 * width n q), modelError n q a β)) ≤ (n : ℝ) / 200000) ∧
      ∃ k : ℕ, 1 ≤ k ∧ n = 2 ^ k := by
  have hpow_gt : ∀ m : ℕ, 24 ≤ m → 8 * (m + 1) ^ 4 < 2 ^ m := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => decide
    | @succ m hm ih =>
        have hm25 : 25 ≤ m + 1 := by omega
        have hstep1 : 25 * (m + 1) ^ 3 ≤ (m + 1) ^ 4 := by
          calc 25 * (m + 1) ^ 3 = (m + 1) ^ 3 * 25 := mul_comm _ _
            _ ≤ (m + 1) ^ 3 * (m + 1) := Nat.mul_le_mul_left _ hm25
            _ = (m + 1) ^ 4 := (pow_succ _ _).symm
        have hstep2 : 25 * (m + 1) ^ 2 ≤ (m + 1) ^ 3 := by
          calc 25 * (m + 1) ^ 2 = (m + 1) ^ 2 * 25 := mul_comm _ _
            _ ≤ (m + 1) ^ 2 * (m + 1) := Nat.mul_le_mul_left _ hm25
            _ = (m + 1) ^ 3 := (pow_succ _ _).symm
        have hstep3 : 25 * (m + 1) ≤ (m + 1) ^ 2 := by
          calc 25 * (m + 1) = (m + 1) * 25 := mul_comm _ _
            _ ≤ (m + 1) * (m + 1) := Nat.mul_le_mul_left _ hm25
            _ = (m + 1) ^ 2 := (pow_two _).symm
        have hexp : (m + 1 + 1) ^ 4 =
            (m + 1) ^ 4 + 4 * (m + 1) ^ 3 + 6 * (m + 1) ^ 2 + 4 * (m + 1) + 1 := by ring
        have hstep : 8 * (m + 1 + 1) ^ 4 ≤ 2 * (8 * (m + 1) ^ 4) := by omega
        have hpow2 : 2 ^ (m + 1) = 2 * 2 ^ m := pow_succ' 2 m
        omega
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp total_dilated_error_sublinear
  let k := max 40 (max N N₁)
  refine ⟨2 ^ k, ?_, ?_, ?_, ?_, ?_, ?_, k, by omega, rfl⟩
  · have hkN : N ≤ k := le_trans (le_max_left _ _) (le_max_right _ _)
    exact hkN.trans (Nat.lt_pow_self (by decide : 1 < 2)).le
  · refine ⟨2 ^ (k - 1), ?_⟩
    rw [← two_mul, ← pow_succ']
    congr 1
    omega
  · calc 8 ≤ 2 ^ 40 := by decide
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) (le_max_left _ _)
  · have hlog : 40 ≤ Nat.log 2 (2 ^ k + 2) := by
      refine Nat.le_log_of_pow_le (by decide) ?_
      calc 2 ^ 40 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) (le_max_left _ _)
        _ ≤ 2 ^ k + 2 := Nat.le_add_right _ _
    change 1600 ≤ (Nat.log 2 (2 ^ k + 2)) ^ 2
    nlinarith
  · have hlog_le : Nat.log 2 (2 ^ k + 2) ≤ k + 1 := by
      refine (Nat.log_lt_of_lt_pow (by positivity) ?_).le
      calc 2 ^ k + 2 < 2 ^ k + 2 ^ k := by
            have : 2 < 2 ^ k := lt_of_lt_of_le (by decide : 2 < 2 ^ 40)
              (Nat.pow_le_pow_right (by decide) (le_max_left _ _))
            omega
        _ = 2 ^ (k + 1) := by rw [pow_succ']; ring
    have hcut_le : cutoff (2 ^ k) ≤ (k + 1) ^ 2 := by
      change (Nat.log 2 (2 ^ k + 2)) ^ 2 ≤ (k + 1) ^ 2
      exact Nat.pow_le_pow_left hlog_le 2
    have hk24 : 24 ≤ k := by omega
    calc 8 * (cutoff (2 ^ k)) ^ 2 ≤ 8 * ((k + 1) ^ 2) ^ 2 :=
          Nat.mul_le_mul_left 8 (Nat.pow_le_pow_left hcut_le 2)
      _ = 8 * (k + 1) ^ 4 := by ring
      _ < 2 ^ k := hpow_gt k hk24
  · apply hN₁
    have hkN1 : N₁ ≤ k := le_trans (le_max_right _ _) (le_max_right _ _)
    exact hkN1.trans (Nat.lt_pow_self (by decide : 1 < 2)).le

private noncomputable def rChoice (n q a : ℕ) : ℝ :=
  if cutoff n / 2 < q ∧ q ≤ cutoff n ∧ 0 ≤ cTerm n q a then 2 else 1

private theorem rChoice_bounds (n q a : ℕ) :
    (1 / 2 : ℝ) ≤ rChoice n q a ∧ rChoice n q a ≤ 2 := by
  dsimp only [rChoice]
  split_ifs <;> norm_num

private noncomputable def winR (n : ℕ) (r' : ℕ → ℕ → ℝ) (q a : ℕ) : Set ℝ :=
  Set.Icc (center q a - r' q a * width n q) (center q a + r' q a * width n q)

private theorem winR_mem (n : ℕ) (r' : ℕ → ℕ → ℝ) (q a : ℕ) (t : ℝ) :
    t ∈ winR n r' q a ↔ |t - center q a| ≤ r' q a * width n q := by
  change _ ∧ _ ↔ _
  rw [abs_le]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

private theorem cont_integrand (n : ℕ) : Continuous (integrand n) := by
  unfold integrand primeSum phase
  fun_prop

private theorem int_winR (n : ℕ) (r' : ℕ → ℕ → ℝ) (q a : ℕ) :
    IntervalIntegrable ((winR n r' q a).indicator (integrand n)) volume 0 1 :=
  ⟨((cont_integrand n).intervalIntegrable 0 1).1.indicator measurableSet_Icc,
    ((cont_integrand n).intervalIntegrable 0 1).2.indicator measurableSet_Icc⟩

private theorem A_split_aux {n : ℕ} (hsep : 8 * (cutoff n) ^ 2 < n)
    (r' : ℕ → ℕ → ℝ) (hr' : ∀ q a, (1 / 2 : ℝ) ≤ r' q a ∧ r' q a ≤ 2) (t : ℝ) :
    ({t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ cutoff n ∧ a ≤ q ∧ Nat.Coprime a q ∧
      |t - (a : ℝ) / (q : ℝ)| ≤ r' q a * (cutoff n : ℝ) / ((q : ℝ) * (n : ℝ))}).indicator
      (integrand n) t =
    ∑ q ∈ Finset.Icc 1 (cutoff n), ∑ a ∈ numerators q,
      (winR n r' q a).indicator (integrand n) t := by
  classical
  let Sset := {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ cutoff n ∧ a ≤ q ∧ Nat.Coprime a q ∧
    |t - (a : ℝ) / (q : ℝ)| ≤ r' q a * (cutoff n : ℝ) / ((q : ℝ) * (n : ℝ))}
  have hwin_eq : ∀ q a, |t - center q a| ≤ r' q a * width n q ↔
      |t - (a : ℝ) / (q : ℝ)| ≤ r' q a * (cutoff n : ℝ) / ((q : ℝ) * (n : ℝ)) := by
    intro q a
    change |t - (a : ℝ) / (q : ℝ)| ≤ r' q a * ((cutoff n : ℝ) / ((q : ℝ) * (n : ℝ))) ↔ _
    rw [mul_div_assoc']
  by_cases ht : t ∈ Sset
  · rw [Set.indicator_of_mem ht]
    obtain ⟨q, a, hq1, hqQ, ha, hcop, habs⟩ := ht
    have hq : q ∈ Finset.Icc 1 (cutoff n) := Finset.mem_Icc.mpr ⟨hq1, hqQ⟩
    have ha' : a ∈ numerators q := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hcop⟩
    have hw : t ∈ winR n r' q a := (winR_mem n r' q a t).mpr ((hwin_eq q a).mpr habs)
    have hw2 : |t - center q a| ≤ 2 * width n q := by
      calc |t - center q a| ≤ r' q a * width n q := (winR_mem n r' q a t).mp hw
        _ ≤ 2 * width n q := mul_le_mul_of_nonneg_right (hr' q a).2 (width_nonneg n q)
    symm
    calc
      _ = ∑ b ∈ numerators q, (winR n r' q b).indicator (integrand n) t := by
        refine Finset.sum_eq_single_of_mem q hq fun s hs hsq => ?_
        refine Finset.sum_eq_zero fun b hb => Set.indicator_of_notMem (fun ht' => ?_) _
        have ht'2 : |t - center s b| ≤ 2 * width n s :=
          ((winR_mem n r' s b t).mp ht').trans
            (mul_le_mul_of_nonneg_right (hr' s b).2 (width_nonneg n s))
        exact hsq (dilated_center_unique hsep hs hq hb ha' ht'2 hw2).1
      _ = (winR n r' q a).indicator (integrand n) t := by
        refine Finset.sum_eq_single_of_mem a ha' fun b hb hba => ?_
        refine Set.indicator_of_notMem (fun ht' => ?_) _
        have ht'2 : |t - center q b| ≤ 2 * width n q :=
          ((winR_mem n r' q b t).mp ht').trans
            (mul_le_mul_of_nonneg_right (hr' q b).2 (width_nonneg n q))
        exact hba (dilated_center_unique hsep hq hq hb ha' ht'2 hw2).2
      _ = _ := Set.indicator_of_mem hw _
  · rw [Set.indicator_of_notMem ht]
    symm
    refine Finset.sum_eq_zero fun q hq => Finset.sum_eq_zero fun a ha => ?_
    refine Set.indicator_of_notMem (fun hw => ht ?_) _
    exact ⟨q, a, (Finset.mem_Icc.mp hq).1, (Finset.mem_Icc.mp hq).2,
      Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_filter.mp ha).1),
      (Finset.mem_filter.mp ha).2, (hwin_eq q a).mp ((winR_mem n r' q a t).mp hw)⟩

private theorem M_sum_aux {n : ℕ} (hsep : 8 * (cutoff n) ^ 2 < n)
    (r' : ℕ → ℕ → ℝ) (hr' : ∀ q a, (1 / 2 : ℝ) ≤ r' q a ∧ r' q a ≤ 2) :
    (intervalIntegral (fun t =>
      ({t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ cutoff n ∧ a ≤ q ∧ Nat.Coprime a q ∧
        |t - (a : ℝ) / (q : ℝ)| ≤ r' q a * (cutoff n : ℝ) / ((q : ℝ) * (n : ℝ))}).indicator
        (integrand n) t) 0 1 volume).re =
    ∑ q ∈ Finset.Icc 1 (cutoff n), ∑ a ∈ numerators q,
      (∫ t in (0 : ℝ)..1, (winR n r' q a).indicator (integrand n) t).re := by
  simp_rw [A_split_aux hsep r' hr']
  rw [intervalIntegral.integral_finsetSum]
  swap
  · intro q _
    exact ⟨integrable_finsetSum _ fun a _ => (int_winR n r' q a).1,
      integrable_finsetSum _ fun a _ => (int_winR n r' q a).2⟩
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [intervalIntegral.integral_finsetSum fun a _ => int_winR n r' q a, Complex.re_sum]

private theorem piece_eq_aux {n : ℕ} (hQ2 : 2 ≤ cutoff n) (hsep : 8 * (cutoff n) ^ 2 < n)
    {q : ℕ} (hq : q ∈ Finset.Icc 1 (cutoff n)) {a : ℕ} (ha : a ∈ numerators q) :
    (∫ t in (0 : ℝ)..1, (winR n (rChoice n) q a).indicator (integrand n) t).re -
      (∫ t in (0 : ℝ)..1, (winR n (fun _ _ => 1) q a).indicator (integrand n) t).re =
    if rChoice n q a = 2 then
      (∫ β in (-2 * width n q)..(-width n q), integrand n (center q a + β)).re +
        (∫ β in (width n q)..(2 * width n q), integrand n (center q a + β)).re
    else 0 := by
  have hq1 := (Finset.mem_Icc.mp hq).1
  have hqQ := (Finset.mem_Icc.mp hq).2
  by_cases hr2 : rChoice n q a = 2
  · simp only [hr2, ↓reduceIte]
    have hq_lo : cutoff n / 2 < q := by
      dsimp only [rChoice] at hr2
      split_ifs at hr2 with hc
      · exact hc.1
      · norm_num at hr2
    have hq_gt1 : 1 < q := by omega
    have ha_bounds : 0 < a ∧ a < q := by
      have hm := Finset.mem_filter.mp ha
      have hle : a ≤ q := Nat.le_of_lt_succ (Finset.mem_range.mp hm.1)
      have ha0 : a ≠ 0 := by rintro rfl; simp [Nat.Coprime] at hm; omega
      have haq : a ≠ q := by rintro rfl; simp [Nat.Coprime] at hm; omega
      omega
    have h2w_le : 2 * width n q ≤ 1 / (q : ℝ) := by
      unfold width
      have hqR : (0 : ℝ) < q := by exact_mod_cast hq1
      have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      have hcut_le : 2 * cutoff n ≤ n := by
        nlinarith [cutoff_positive n, hsep]
      rw [← mul_div_assoc, div_le_div_iff₀ (mul_pos hqR hnR) hqR]
      calc 2 * (cutoff n : ℝ) * q ≤ (n : ℝ) * q :=
            mul_le_mul_of_nonneg_right (by exact_mod_cast hcut_le) hqR.le
        _ = 1 * (q * n) := by ring
    have hc_lo : 0 ≤ center q a - 2 * width n q := by
      have hqR : (0 : ℝ) < q := by exact_mod_cast hq1
      have h1q : 1 / (q : ℝ) ≤ center q a := by
        unfold center
        exact div_le_div_of_nonneg_right (by exact_mod_cast ha_bounds.1) hqR.le
      linarith
    have hc_hi : center q a + 2 * width n q ≤ 1 := by
      have hqR : (0 : ℝ) < q := by exact_mod_cast hq1
      have haq : (a : ℝ) + 1 ≤ q := by exact_mod_cast ha_bounds.2
      have h1q : center q a + 1 / (q : ℝ) ≤ 1 := by
        unfold center
        rw [← add_div, div_le_one hqR]
        exact haq
      linarith
    have hw0 : 0 ≤ width n q := width_nonneg n q
    have hint_clip : ∀ c : ℝ, 0 ≤ c → c ≤ 2 → 0 ≤ center q a - c * width n q →
        center q a + c * width n q ≤ 1 →
        ∫ t in (0 : ℝ)..1, (Set.Icc (center q a - c * width n q) (center q a + c * width n q)).indicator
          (integrand n) t =
        ∫ β in (-c * width n q)..(c * width n q), integrand n (center q a + β) := by
      intro c hc0 hc2 hlo hhi
      have hord' : center q a - c * width n q ≤ center q a + c * width n q := by nlinarith
      rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc,
        MeasureTheory.integral_indicator measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc,
        Set.Icc_inter_Icc, max_eq_left hlo, min_eq_left hhi,
        integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hord']
      symm
      rw [intervalIntegral.integral_comp_add_left (f := fun t => integrand n t),
        show center q a + -c * width n q = center q a - c * width n q by ring]
    have hI2 :
        ∫ t in (0 : ℝ)..1, (winR n (rChoice n) q a).indicator (integrand n) t =
        ∫ β in (-2 * width n q)..(2 * width n q), integrand n (center q a + β) := by
      have hwin2 : winR n (rChoice n) q a =
          Set.Icc (center q a - 2 * width n q) (center q a + 2 * width n q) := by
        dsimp only [winR]; rw [hr2]
      rw [hwin2]
      simpa using hint_clip 2 (by norm_num) (by norm_num) hc_lo hc_hi
    have hI1 :
        ∫ t in (0 : ℝ)..1, (winR n (fun _ _ => 1) q a).indicator (integrand n) t =
        ∫ β in (-width n q)..(width n q), integrand n (center q a + β) := by
      have hwin1 : winR n (fun _ _ => 1) q a =
          Set.Icc (center q a - 1 * width n q) (center q a + 1 * width n q) := rfl
      rw [hwin1]
      simpa using hint_clip 1 (by norm_num) (by norm_num) (by linarith) (by linarith)
    have hcont_sh : Continuous (fun β : ℝ => integrand n (center q a + β)) :=
      (cont_integrand n).comp (continuous_const.add continuous_id)
    have hadd1 := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (hcont_sh.intervalIntegrable (-2 * width n q) (-width n q))
      (hcont_sh.intervalIntegrable (-width n q) (2 * width n q))
    have hadd2 := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (hcont_sh.intervalIntegrable (-width n q) (width n q))
      (hcont_sh.intervalIntegrable (width n q) (2 * width n q))
    rw [hI2, hI1, ← hadd1, ← hadd2]
    simp only [Complex.add_re]
    ring
  · have hr1 : rChoice n q a = 1 := by
      by_cases hc : cutoff n / 2 < q ∧ q ≤ cutoff n ∧ 0 ≤ cTerm n q a
      · exfalso; apply hr2; dsimp only [rChoice]; simp only [hc, and_self, ↓reduceIte]
      · dsimp only [rChoice]; simp only [hc, ↓reduceIte]
    simp only [hr2, ↓reduceIte]
    have hwin_eq : winR n (rChoice n) q a = winR n (fun _ _ => 1) q a := by
      dsimp only [winR]; rw [hr1]
    rw [hwin_eq, sub_self]

private theorem M_diff_aux {n : ℕ} (hQ2 : 2 ≤ cutoff n) (hsep : 8 * (cutoff n) ^ 2 < n) :
    ∑ q ∈ Finset.Icc 1 (cutoff n), ∑ a ∈ numerators q,
      (if rChoice n q a = 2 then
        (∫ β in (-2 * width n q)..(-width n q), integrand n (center q a + β)).re +
        (∫ β in (width n q)..(2 * width n q), integrand n (center q a + β)).re
      else 0) =
    (intervalIntegral (fun t =>
      ({t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ cutoff n ∧ a ≤ q ∧ Nat.Coprime a q ∧
        |t - (a : ℝ) / (q : ℝ)| ≤ rChoice n q a * (cutoff n : ℝ) / ((q : ℝ) * (n : ℝ))}).indicator
        (integrand n) t) 0 1 volume).re -
    (intervalIntegral (fun t =>
      ({t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ cutoff n ∧ a ≤ q ∧ Nat.Coprime a q ∧
        |t - (a : ℝ) / (q : ℝ)| ≤ (1 : ℝ) * (cutoff n : ℝ) / ((q : ℝ) * (n : ℝ))}).indicator
        (integrand n) t) 0 1 volume).re := by
  rw [M_sum_aux hsep (rChoice n) (rChoice_bounds n),
    M_sum_aux hsep (fun _ _ => 1) (fun _ _ => ⟨by norm_num, by norm_num⟩),
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun a ha => (piece_eq_aux hQ2 hsep hq ha).symm

private theorem model_eq_aux (n q a : ℕ) (u v : ℝ) :
    (∫ β in u..v, (unitMean q a * kernel n β) ^ 2 * phase (-(n : ℝ) * (center q a + β))).re =
      cTerm n q a * ∫ β in u..v, ‖kernel n β‖ ^ 2 := by
  have hpt : ∀ β : ℝ,
      (unitMean q a * kernel n β) ^ 2 * phase (-(n : ℝ) * (center q a + β)) =
      (unitMean q a ^ 2 * phase (-(n : ℝ) * center q a)) * ((‖kernel n β‖ ^ 2 : ℝ) : ℂ) := by
    intro β
    have hadd : -(n : ℝ) * (center q a + β) = -(n : ℝ) * center q a + -(n : ℝ) * β := by ring
    have hpa : phase (-(n : ℝ) * (center q a + β)) =
        phase (-(n : ℝ) * center q a) * phase (-(n : ℝ) * β) := by
      rw [hadd]
      unfold phase
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [hpa]
    have hkt := kernel_square_twist n β
    calc _ = (unitMean q a ^ 2 * phase (-(n : ℝ) * center q a)) *
          (kernel n β ^ 2 * phase (-(n : ℝ) * β)) := by ring
      _ = _ := by rw [hkt]
  simp_rw [hpt]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  rfl

private theorem ker_symm_aux (n q : ℕ) :
    ∫ β in (-2 * width n q)..(-width n q), ‖kernel n β‖ ^ 2 =
    ∫ β in (width n q)..(2 * width n q), ‖kernel n β‖ ^ 2 := by
  have hneg : ∀ β : ℝ, ‖kernel n (-β)‖ ^ 2 = ‖kernel n β‖ ^ 2 := by
    intro β
    have hk : kernel n (-β) = star (kernel n β) := by
      unfold kernel
      rw [star_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      unfold phase
      simp only [Complex.star_def, Complex.exp_ofReal_mul_I, map_add, map_mul,
        Complex.conj_ofReal, Complex.conj_I]
      rw [show 2 * Real.pi * ((j : ℝ) * -β) = -(2 * Real.pi * ((j : ℝ) * β)) by ring,
        Real.cos_neg, Real.sin_neg]
      push_cast
      ring
    rw [hk, norm_star]
  calc _ = ∫ β in (-2 * width n q)..(-width n q), ‖kernel n (-β)‖ ^ 2 := by simp_rw [hneg]
    _ = ∫ β in (-(-width n q))..(-(-2 * width n q)), ‖kernel n β‖ ^ 2 :=
        intervalIntegral.integral_comp_neg (fun β => ‖kernel n β‖ ^ 2)
    _ = _ := by ring_nf

private theorem diff_err_aux (n q a : ℕ) :
    (if rChoice n q a = 2 then
      2 * cTerm n q a * ∫ β in (width n q)..(2 * width n q), ‖kernel n β‖ ^ 2
    else 0) -
    (if rChoice n q a = 2 then
      (∫ β in (-2 * width n q)..(-width n q), integrand n (center q a + β)).re +
        (∫ β in (width n q)..(2 * width n q), integrand n (center q a + β)).re
    else 0) ≤
    ((∫ β in (-2 * width n q)..(-width n q), modelError n q a β) +
      (∫ β in (width n q)..(2 * width n q), modelError n q a β)) := by
  have hw0 : 0 ≤ width n q := width_nonneg n q
  by_cases hr2 : rChoice n q a = 2
  · simp only [hr2, ↓reduceIte]
    have hm1 := model_eq_aux n q a (-2 * width n q) (-width n q)
    have hm2 := model_eq_aux n q a (width n q) (2 * width n q)
    rw [ker_symm_aux n q] at hm1
    have hi_cont : Continuous (fun β => integrand n (center q a + β)) :=
      (cont_integrand n).comp (continuous_const.add continuous_id)
    have hm_cont : Continuous (fun β => (unitMean q a * kernel n β) ^ 2 *
        phase (-(n : ℝ) * (center q a + β))) := by
      unfold unitMean kernel phase
      fun_prop
    have hbnd : ∀ u v : ℝ, u ≤ v →
        (∫ β in u..v, (unitMean q a * kernel n β) ^ 2 *
          phase (-(n : ℝ) * (center q a + β))).re -
        (∫ β in u..v, integrand n (center q a + β)).re ≤
        ∫ β in u..v, modelError n q a β := by
      intro u v huv
      have hsub :
          (∫ β in u..v, (unitMean q a * kernel n β) ^ 2 *
            phase (-(n : ℝ) * (center q a + β))).re -
          (∫ β in u..v, integrand n (center q a + β)).re =
          (∫ β in u..v, ((unitMean q a * kernel n β) ^ 2 *
            phase (-(n : ℝ) * (center q a + β)) - integrand n (center q a + β))).re := by
        rw [← Complex.sub_re, ← intervalIntegral.integral_sub (hm_cont.intervalIntegrable _ _)
          (hi_cont.intervalIntegrable _ _)]
      rw [hsub]
      refine (Complex.re_le_norm _).trans ?_
      refine (intervalIntegral.norm_integral_le_integral_norm huv).trans ?_
      refine le_of_eq (intervalIntegral.integral_congr fun β _ => ?_)
      change ‖_ - _‖ = modelError n q a β
      rw [norm_sub_rev]
      rfl
    have hb1 := hbnd (-2 * width n q) (-width n q) (by linarith)
    have hb2 := hbnd (width n q) (2 * width n q) (by linarith)
    have htwo : 2 * cTerm n q a * ∫ β in (width n q)..(2 * width n q), ‖kernel n β‖ ^ 2 =
        (cTerm n q a * ∫ β in (width n q)..(2 * width n q), ‖kernel n β‖ ^ 2) +
          (cTerm n q a * ∫ β in (width n q)..(2 * width n q), ‖kernel n β‖ ^ 2) := by ring
    linarith only [hb1, hb2, hm1, hm2, htwo]
  · simp only [hr2, ↓reduceIte, sub_zero]
    have h01 : 0 ≤ ∫ β in (-2 * width n q)..(-width n q), modelError n q a β :=
      intervalIntegral.integral_nonneg (μ := volume) (by linarith : -2 * width n q ≤ -width n q)
        (fun _ _ => norm_nonneg _ : ∀ β ∈ Set.Icc (-2 * width n q) (-width n q),
          0 ≤ modelError n q a β)
    have h02 : 0 ≤ ∫ β in (width n q)..(2 * width n q), modelError n q a β :=
      intervalIntegral.integral_nonneg (μ := volume) (by linarith : width n q ≤ 2 * width n q)
        (fun _ _ => norm_nonneg _ : ∀ β ∈ Set.Icc (width n q) (2 * width n q),
          0 ≤ modelError n q a β)
    exact add_nonneg h01 h02

private theorem model_gain_aux {n k : ℕ} (hn8 : 8 ≤ n) (hQ1600 : 1600 ≤ cutoff n)
    (hn_pow : n = 2 ^ k) :
    (n : ℝ) / 40960 ≤
    ∑ q ∈ Finset.Icc 1 (cutoff n), ∑ a ∈ numerators q,
      if rChoice n q a = 2 then
        2 * cTerm n q a * ∫ β in (width n q)..(2 * width n q), ‖kernel n β‖ ^ 2
      else 0 := by
  let Ssq := (Finset.Ioc (cutoff n / 2) (cutoff n)).filter Squarefree
  have hSsq_sub : Ssq ⊆ Finset.Icc 1 (cutoff n) := by
    intro q hq
    have hm := Finset.mem_Ioc.mp (Finset.mem_filter.mp hq).1
    exact Finset.mem_Icc.mpr ⟨by omega, hm.2⟩
  have hq_nonneg : ∀ q ∈ Finset.Icc 1 (cutoff n),
      0 ≤ ∑ a ∈ numerators q, if rChoice n q a = 2 then
        2 * cTerm n q a * ∫ β in (width n q)..(2 * width n q), ‖kernel n β‖ ^ 2
      else 0 := by
    intro q _
    refine Finset.sum_nonneg fun a _ => ?_
    split_ifs with hr2
    · have hc0 : 0 ≤ cTerm n q a := by
        dsimp only [rChoice] at hr2
        split_ifs at hr2 with hc
        · exact hc.2.2
        · norm_num at hr2
      have hint0 : 0 ≤ ∫ β in (width n q)..(2 * width n q), ‖kernel n β‖ ^ 2 :=
        intervalIntegral.integral_nonneg (by linarith only [width_nonneg n q]) fun _ _ => sq_nonneg _
      exact mul_nonneg (mul_nonneg (by norm_num) hc0) hint0
    · exact le_rfl
  have hsum_sub :
      ∑ q ∈ Ssq, ∑ a ∈ numerators q,
        (if rChoice n q a = 2 then
          2 * cTerm n q a * ∫ β in (width n q)..(2 * width n q), ‖kernel n β‖ ^ 2
        else 0) ≤
      ∑ q ∈ Finset.Icc 1 (cutoff n), ∑ a ∈ numerators q,
        (if rChoice n q a = 2 then
          2 * cTerm n q a * ∫ β in (width n q)..(2 * width n q), ‖kernel n β‖ ^ 2
        else 0) :=
    Finset.sum_le_sum_of_subset_of_nonneg hSsq_sub fun q hq _ => hq_nonneg q hq
  have hterm_sq : ∀ q ∈ Ssq,
      (n : ℝ) / 512 * (1 / (8 * (q : ℝ))) ≤
      ∑ a ∈ numerators q,
        if rChoice n q a = 2 then
          2 * cTerm n q a * ∫ β in (width n q)..(2 * width n q), ‖kernel n β‖ ^ 2
        else 0 := by
    intro q hq
    have hq_mem := Finset.mem_filter.mp hq
    have hq_Ioc := Finset.mem_Ioc.mp hq_mem.1
    have hq_sq : Squarefree q := hq_mem.2
    have hq31 : 31 ≤ q := by omega
    have hker_lb := kernel_annulus_floor hn8 hq_Ioc.1 hq_Ioc.2
    have hunits_eq : unitsBelow q = numerators q := unitsBelow_eq_numerators q (by omega)
    have hcos_lb := pos_cosine_sum_lower (k := k) hq31 hq_sq
    rw [hunits_eq] at hcos_lb
    have hr2_iff : ∀ a : ℕ, (rChoice n q a = 2) ↔ 0 ≤ cTerm n q a := by
      intro a
      dsimp only [rChoice]
      have hcond : cutoff n / 2 < q ∧ q ≤ cutoff n := ⟨hq_Ioc.1, hq_Ioc.2⟩
      split_ifs with h1
      · exact ⟨fun _ => h1.2.2, fun _ => rfl⟩
      · constructor
        · intro h2; norm_num at h2
        · intro h0; exfalso; exact h1 ⟨hcond.1, hcond.2, h0⟩
    have hsum_eq :
        (∑ a ∈ numerators q, if rChoice n q a = 2 then
          2 * cTerm n q a * ∫ β in (width n q)..(2 * width n q), ‖kernel n β‖ ^ 2
        else 0) =
        (2 * ∫ β in (width n q)..(2 * width n q), ‖kernel n β‖ ^ 2) *
          ∑ a ∈ numerators q, (if 0 ≤ cTerm n q a then cTerm n q a else 0) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      by_cases hc0 : 0 ≤ cTerm n q a
      · have hr2' : rChoice n q a = 2 := (hr2_iff a).mpr hc0
        simp only [hr2', hc0, ↓reduceIte]
        ring
      · have hr2' : rChoice n q a ≠ 2 := fun h2 => hc0 ((hr2_iff a).mp h2)
        simp only [hr2', hc0, ↓reduceIte]
        ring
    rw [hsum_eq]
    have hcos_lb' : 1 / (8 * (q : ℝ)) ≤
        ∑ a ∈ numerators q, if 0 ≤ cTerm n q a then cTerm n q a else 0 := by
      rw [hn_pow]
      exact hcos_lb
    have hcos_nonneg : 0 ≤ 1 / (8 * (q : ℝ)) :=
      div_nonneg zero_le_one (mul_nonneg (by norm_num) (Nat.cast_nonneg q))
    have hint_nonneg : 0 ≤ 2 * ∫ β in (width n q)..(2 * width n q), ‖kernel n β‖ ^ 2 :=
      mul_nonneg (by norm_num)
        (intervalIntegral.integral_nonneg (μ := volume) (by linarith only [width_nonneg n q])
          fun _ _ => sq_nonneg _)
    exact mul_le_mul (by linarith only [hker_lb]) hcos_lb' hcos_nonneg hint_nonneg
  have hrec_lb := squarefree_reciprocal_lower (cutoff n) hQ1600
  have h1 : (n : ℝ) / 40960 = (n : ℝ) / 512 * (1 / 80) := by ring
  have h2 : (n : ℝ) / 512 * (1 / 80) ≤
      (n : ℝ) / 512 * ∑ q ∈ Ssq, (1 : ℝ) / (8 * (q : ℝ)) :=
    mul_le_mul_of_nonneg_left hrec_lb (div_nonneg (Nat.cast_nonneg n) (by norm_num))
  have h3 : (n : ℝ) / 512 * ∑ q ∈ Ssq, (1 : ℝ) / (8 * (q : ℝ)) =
      ∑ q ∈ Ssq, (n : ℝ) / 512 * (1 / (8 * (q : ℝ))) := Finset.mul_sum _ _ _
  have h4 : ∑ q ∈ Ssq, (n : ℝ) / 512 * (1 / (8 * (q : ℝ))) ≤
      ∑ q ∈ Ssq, ∑ a ∈ numerators q, (if rChoice n q a = 2 then
        2 * cTerm n q a * ∫ β in (width n q)..(2 * width n q), ‖kernel n β‖ ^ 2
      else 0) := Finset.sum_le_sum hterm_sq
  exact h1.trans_le (h2.trans (h3.trans_le (h4.trans hsum_sub)))

private theorem sum_err_aux {n : ℕ}
    (herr_tot : ∑ q ∈ Finset.Icc 1 (cutoff n), ∑ a ∈ numerators q,
      ((∫ β in (-2 * width n q)..(-width n q), modelError n q a β) +
        (∫ β in (width n q)..(2 * width n q), modelError n q a β)) ≤ (n : ℝ) / 200000) :
    (∑ q ∈ Finset.Icc 1 (cutoff n), ∑ a ∈ numerators q,
      if rChoice n q a = 2 then
        2 * cTerm n q a * ∫ β in (width n q)..(2 * width n q), ‖kernel n β‖ ^ 2
      else 0) -
    (∑ q ∈ Finset.Icc 1 (cutoff n), ∑ a ∈ numerators q,
      if rChoice n q a = 2 then
        (∫ β in (-2 * width n q)..(-width n q), integrand n (center q a + β)).re +
          (∫ β in (width n q)..(2 * width n q), integrand n (center q a + β)).re
      else 0) ≤ (n : ℝ) / 200000 := by
  rw [← Finset.sum_sub_distrib]
  refine (Finset.sum_le_sum fun q _ => ?_).trans herr_tot
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_le_sum fun a _ => diff_err_aux n q a

end Conjectures.Goldbach.MajorDilationOscillationRefute_aux

theorem Conjectures.Goldbach.MajorDilationOscillationRefute :
    ¬ (let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let f := fun (n : ℕ) (t : ℝ) => (S n w t)^2*E (-(n:ℝ)*t); let A := fun (n : ℕ) (r : ℕ → ℕ → ℝ) => {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Q n ∧ a ≤ q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ r q a * (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let M := fun (n : ℕ) (r : ℕ → ℕ → ℝ) => (intervalIntegral (fun t => (A n r).indicator (f n) t) (0:ℝ) 1 MeasureTheory.volume).re; ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, Even n → ∀ r : ℕ → ℕ → ℝ, (∀ q a, (1/2:ℝ) ≤ r q a ∧ r q a ≤ 2) → |M n r - M n (fun _ _ => 1)| ≤ ε*(n:ℝ)) := by
  intro hosc
  dsimp only at hosc
  obtain ⟨N, hN⟩ := hosc (1 / 100000) (by norm_num)
  obtain ⟨n, hnN, hn_even, hn8, hQ1600, hsep, herr_tot, k, _, hn_pow⟩ :=
    Conjectures.Goldbach.MajorDilationOscillationRefute_aux.exists_pow2_witness N
  let r := Conjectures.Goldbach.MajorDilationOscillationRefute_aux.rChoice n
  have hr_bounds : ∀ q a, (1 / 2 : ℝ) ≤ r q a ∧ r q a ≤ 2 :=
    Conjectures.Goldbach.MajorDilationOscillationRefute_aux.rChoice_bounds n
  have hle_osc := hN n hnN hn_even r hr_bounds
  have hM_diff := Conjectures.Goldbach.MajorDilationOscillationRefute_aux.M_diff_aux (by omega) hsep
  have hmodel_gain := Conjectures.Goldbach.MajorDilationOscillationRefute_aux.model_gain_aux
    hn8 hQ1600 hn_pow
  have hsum_err := Conjectures.Goldbach.MajorDilationOscillationRefute_aux.sum_err_aux herr_tot
  have hM_lb : (n : ℝ) / 40960 - (n : ℝ) / 200000 ≤
      (intervalIntegral (fun t =>
        ({t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ cutoff n ∧ a ≤ q ∧ Nat.Coprime a q ∧
          |t - (a : ℝ) / (q : ℝ)| ≤ r q a * (cutoff n : ℝ) / ((q : ℝ) * (n : ℝ))}).indicator
          (integrand n) t) 0 1 volume).re -
      (intervalIntegral (fun t =>
        ({t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ cutoff n ∧ a ≤ q ∧ Nat.Coprime a q ∧
          |t - (a : ℝ) / (q : ℝ)| ≤ (1 : ℝ) * (cutoff n : ℝ) / ((q : ℝ) * (n : ℝ))}).indicator
          (integrand n) t) 0 1 volume).re := by
    rw [← hM_diff]
    linarith [hmodel_gain, hsum_err]
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hlt : 1 / 100000 * (n : ℝ) < (n : ℝ) / 40960 - (n : ℝ) / 200000 := by linarith
  have hle_abs :
      (intervalIntegral (fun t =>
        ({t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ cutoff n ∧ a ≤ q ∧ Nat.Coprime a q ∧
          |t - (a : ℝ) / (q : ℝ)| ≤ r q a * (cutoff n : ℝ) / ((q : ℝ) * (n : ℝ))}).indicator
          (integrand n) t) 0 1 volume).re -
      (intervalIntegral (fun t =>
        ({t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ cutoff n ∧ a ≤ q ∧ Nat.Coprime a q ∧
          |t - (a : ℝ) / (q : ℝ)| ≤ (1 : ℝ) * (cutoff n : ℝ) / ((q : ℝ) * (n : ℝ))}).indicator
          (integrand n) t) 0 1 volume).re ≤
      |(intervalIntegral (fun t =>
        ({t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ cutoff n ∧ a ≤ q ∧ Nat.Coprime a q ∧
          |t - (a : ℝ) / (q : ℝ)| ≤ r q a * (cutoff n : ℝ) / ((q : ℝ) * (n : ℝ))}).indicator
          (integrand n) t) 0 1 volume).re -
      (intervalIntegral (fun t =>
        ({t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ cutoff n ∧ a ≤ q ∧ Nat.Coprime a q ∧
          |t - (a : ℝ) / (q : ℝ)| ≤ (1 : ℝ) * (cutoff n : ℝ) / ((q : ℝ) * (n : ℝ))}).indicator
          (integrand n) t) 0 1 volume).re| := le_abs_self _
  change |(intervalIntegral (fun t =>
        ({t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ cutoff n ∧ a ≤ q ∧ Nat.Coprime a q ∧
          |t - (a : ℝ) / (q : ℝ)| ≤ r q a * (cutoff n : ℝ) / ((q : ℝ) * (n : ℝ))}).indicator
          (integrand n) t) 0 1 volume).re -
      (intervalIntegral (fun t =>
        ({t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ cutoff n ∧ a ≤ q ∧ Nat.Coprime a q ∧
          |t - (a : ℝ) / (q : ℝ)| ≤ (1 : ℝ) * (cutoff n : ℝ) / ((q : ℝ) * (n : ℝ))}).indicator
          (integrand n) t) 0 1 volume).re| ≤ 1 / 100000 * (n : ℝ) at hle_osc
  linarith
