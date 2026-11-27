import Mathlib

open Finset BigOperators

namespace Conjectures.Goldbach.ReciprocalChordSum_aux

noncomputable def rnd (y : ℝ) : ℤ := ⌊y + 1/2⌋

noncomputable def frac (y : ℝ) : ℝ := y - (rnd y : ℝ)

theorem abs_frac (y : ℝ) : |frac y| ≤ 1/2 := by
  have h1 : (rnd y : ℝ) ≤ y + 1/2 := Int.floor_le _
  have h2 : y + 1/2 < (rnd y : ℝ) + 1 := Int.lt_floor_add_one _
  rw [frac, abs_le]
  constructor <;> linarith

noncomputable def Eaux (y : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * y : ℝ) : ℂ) * Complex.I)

noncomputable def capaux (H y : ℝ) : ℝ :=
  if Eaux y = 1 then H else min H (2 / ‖1 - Eaux y‖)

theorem capaux_le_H (H y : ℝ) : capaux H y ≤ H := by
  unfold capaux
  split
  · exact le_refl H
  · exact min_le_left H _

theorem capaux_le_chord (H y : ℝ) (h : Eaux y ≠ 1) :
    capaux H y ≤ 2 / ‖1 - Eaux y‖ := by
  unfold capaux
  rw [if_neg h]
  exact min_le_right H _

theorem exp_two_pi_mul_I : Complex.exp (((2 * Real.pi : ℝ) : ℂ) * Complex.I) = 1 := by
  rw [Complex.exp_mul_I]
  apply Complex.ext <;>
    simp [Complex.cos_ofReal_re, Complex.cos_ofReal_im, Complex.sin_ofReal_re,
      Complex.sin_ofReal_im, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, Real.cos_two_pi, Real.sin_two_pi]

theorem exp_two_pi_mul_I_int (n : ℤ) :
    Complex.exp (((2 * Real.pi * (n:ℝ) : ℝ) : ℂ) * Complex.I) = 1 := by
  have h : ((2 * Real.pi * (n:ℝ) : ℝ) : ℂ) * Complex.I
      = ((n:ℤ) : ℂ) * (((2 * Real.pi : ℝ) : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [h, Complex.exp_int_mul, exp_two_pi_mul_I, one_zpow]

theorem Eaux_sub_int (y : ℝ) (s : ℤ) : Eaux (y - (s:ℝ)) = Eaux y := by
  have h : ((2 * Real.pi * (y - (s:ℝ)) : ℝ) : ℂ) * Complex.I
      = ((2 * Real.pi * y : ℝ) : ℂ) * Complex.I
        + ((-(2 * Real.pi * (s:ℝ)) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [Eaux, Eaux, h, Complex.exp_add]
  have h2 : Complex.exp (((-(2 * Real.pi * (s:ℝ)) : ℝ) : ℂ) * Complex.I) = 1 := by
    have h3 : (-(2 * Real.pi * (s:ℝ)) : ℝ) = 2 * Real.pi * ((-s : ℤ) : ℝ) := by
      push_cast
      ring
    rw [h3]
    exact exp_two_pi_mul_I_int (-s)
  rw [h2, mul_one]

theorem norm_one_sub_Eaux (v : ℝ) :
    ‖(1 : ℂ) - Eaux v‖ = 2 * |Real.sin (Real.pi * v)| := by
  have hre : ((1 : ℂ) - Eaux v).re = 1 - Real.cos (2 * Real.pi * v) := by
    simp only [Eaux, Complex.exp_mul_I, Complex.sub_re, Complex.one_re, Complex.add_re,
      Complex.mul_re, Complex.I_re, Complex.I_im, Complex.cos_ofReal_re, Complex.cos_ofReal_im,
      Complex.sin_ofReal_re, Complex.sin_ofReal_im]
    ring
  have him : ((1 : ℂ) - Eaux v).im = -Real.sin (2 * Real.pi * v) := by
    simp only [Eaux, Complex.exp_mul_I, Complex.sub_im, Complex.one_im, Complex.add_im,
      Complex.mul_im, Complex.I_re, Complex.I_im, Complex.cos_ofReal_re, Complex.cos_ofReal_im,
      Complex.sin_ofReal_re, Complex.sin_ofReal_im]
    ring
  have hns : Complex.normSq (1 - Eaux v) = 4 * (Real.sin (Real.pi * v))^2 := by
    rw [Complex.normSq_apply, hre, him]
    have hA := Real.sin_sq_add_cos_sq (2 * Real.pi * v)
    have hB := Real.sin_sq_add_cos_sq (Real.pi * v)
    have hC : Real.cos (2 * Real.pi * v) = 2 * (Real.cos (Real.pi * v))^2 - 1 := by
      have h := Real.cos_two_mul (Real.pi * v)
      rwa [show 2 * (Real.pi * v) = 2 * Real.pi * v by ring] at h
    nlinarith
  have h3 : ‖(1 : ℂ) - Eaux v‖ ^ 2 = (2 * |Real.sin (Real.pi * v)|) ^ 2 := by
    rw [Complex.sq_norm, hns]
    nlinarith [sq_abs (Real.sin (Real.pi * v))]
  nlinarith [norm_nonneg ((1 : ℂ) - Eaux v), abs_nonneg (Real.sin (Real.pi * v))]

theorem norm_one_sub_Eaux_ge (v : ℝ) (hv : |v| ≤ 1/2) :
    4 * |v| ≤ ‖(1 : ℂ) - Eaux v‖ := by
  rw [norm_one_sub_Eaux]
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  have hsin : |Real.sin (Real.pi * v)| = |Real.sin (Real.pi * |v|)| := by
    by_cases hvv : 0 ≤ v
    · rw [abs_of_nonneg hvv]
    · rw [abs_of_nonpos (le_of_not_ge hvv),
        show Real.pi * (-v) = -(Real.pi * v) by ring, Real.sin_neg, abs_neg]
  have hx : (0:ℝ) ≤ Real.pi * |v| := by positivity
  have hx2 : Real.pi * |v| ≤ Real.pi / 2 := by nlinarith [abs_nonneg v]
  have hx3 : Real.pi * |v| ≤ Real.pi := by nlinarith [abs_nonneg v]
  have hnn : (0:ℝ) ≤ Real.sin (Real.pi * |v|) :=
    Real.sin_nonneg_of_nonneg_of_le_pi hx hx3
  have hmls := Real.mul_le_sin hx hx2
  have hkey : (2:ℝ) / Real.pi * (Real.pi * |v|) = 2 * |v| := by
    field_simp
  rw [hkey] at hmls
  rw [hsin, abs_of_nonneg hnn]
  linarith

noncomputable def idx (a q : ℕ) (t x : ℝ) (r : ℕ) : ℤ :=
  rnd ((q:ℝ) * x) + (a:ℤ) * (r:ℤ) - (q:ℤ) * rnd (x + (r:ℝ) * t)

theorem idx_cast (a q : ℕ) (hq : 1 ≤ q) (t x : ℝ) (r : ℕ) :
    ((idx a q t x r : ℤ) : ℝ)
      = (q:ℝ) * frac (x + (r:ℝ)*t) - frac ((q:ℝ)*x)
        - (q:ℝ)*(r:ℝ)*(t - (a:ℝ)/(q:ℝ)) := by
  have hq0 : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  simp only [idx, frac]
  push_cast
  field_simp
  ring

theorem idx_injOn (a q : ℕ) (hq : 1 ≤ q) (hcop : Nat.Coprime a q) (t x : ℝ) :
    Set.InjOn (idx a q t x) (↑(Finset.range q)) := by
  intro r hr r' hr' h
  have hrq : r < q := Finset.mem_range.mp (Finset.mem_coe.mp hr)
  have hr'q : r' < q := Finset.mem_range.mp (Finset.mem_coe.mp hr')
  have hcopZ : IsCoprime (q:ℤ) (a:ℤ) := Nat.isCoprime_iff_coprime.mpr hcop.symm
  have hdiv : (q:ℤ) ∣ (a:ℤ) * ((r:ℤ) - (r':ℤ)) := by
    refine ⟨rnd (x + (r:ℝ)*t) - rnd (x + (r':ℝ)*t), ?_⟩
    have h2 : (a:ℤ)*(r:ℤ) - (q:ℤ)*rnd (x + (r:ℝ)*t)
        = (a:ℤ)*(r':ℤ) - (q:ℤ)*rnd (x + (r':ℝ)*t) := by
      simp only [idx] at h
      linarith
    linarith
  have hdiv2 : (q:ℤ) ∣ ((r:ℤ) - (r':ℤ)) := hcopZ.dvd_of_dvd_mul_left hdiv
  obtain ⟨k, hk⟩ := hdiv2
  have hrZ : (r:ℤ) < (q:ℤ) := by exact_mod_cast hrq
  have hr'Z : (r':ℤ) < (q:ℤ) := by exact_mod_cast hr'q
  have hr0 : (0:ℤ) ≤ (r:ℤ) := Int.natCast_nonneg r
  have hr'0 : (0:ℤ) ≤ (r':ℤ) := Int.natCast_nonneg r'
  have hqZ : (0:ℤ) < (q:ℤ) := by exact_mod_cast hq
  have hlt : (r:ℤ) - (r':ℤ) < (q:ℤ) := by omega
  have hgt : -(q:ℤ) < (r:ℤ) - (r':ℤ) := by omega
  have hk1 : k ≤ 0 := by
    by_contra hc
    simp only [not_le] at hc
    have h1 : (1:ℤ) ≤ k := by omega
    have h2 : (q:ℤ)*1 ≤ (q:ℤ)*k := mul_le_mul_of_nonneg_left h1 (le_of_lt hqZ)
    linarith
  have hk2 : (0:ℤ) ≤ k := by
    by_contra hc
    simp only [not_le] at hc
    have h1 : k ≤ -1 := by omega
    have h2 : (q:ℤ)*k ≤ (q:ℤ)*(-1) := mul_le_mul_of_nonneg_left h1 (le_of_lt hqZ)
    linarith
  have hk0 : k = 0 := by omega
  subst hk0
  simp only [mul_zero] at hk
  have hEq : (r:ℤ) = (r':ℤ) := by linarith
  exact_mod_cast hEq

theorem err_le_one (a q : ℕ) (hq : 1 ≤ q) (t : ℝ)
    (ht : |t - (a:ℝ)/(q:ℝ)| ≤ 1/(q:ℝ)^2) (r : ℕ) (hr : r < q) :
    |(q:ℝ)*(r:ℝ)*(t - (a:ℝ)/(q:ℝ))| ≤ 1 := by
  have hq0 : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  have hr0 : (0:ℝ) ≤ (r:ℝ) := by positivity
  have hrq : (r:ℝ) ≤ (q:ℝ) := by exact_mod_cast le_of_lt hr
  calc |(q:ℝ)*(r:ℝ)*(t - (a:ℝ)/(q:ℝ))|
      = (q:ℝ)*(r:ℝ)*|t - (a:ℝ)/(q:ℝ)| := by
        rw [abs_mul, abs_mul, abs_of_pos hq0, abs_of_nonneg hr0]
    _ ≤ (q:ℝ)*(r:ℝ)*(1/(q:ℝ)^2) :=
        mul_le_mul_of_nonneg_left ht (mul_nonneg (le_of_lt hq0) hr0)
    _ = (r:ℝ)/(q:ℝ) := by field_simp
    _ ≤ 1 := by rw [div_le_one hq0]; exact hrq

theorem idx_abs_le (a q : ℕ) (hq : 1 ≤ q) (t x : ℝ)
    (ht : |t - (a:ℝ)/(q:ℝ)| ≤ 1/(q:ℝ)^2) (r : ℕ) (hr : r < q) :
    |((idx a q t x r : ℤ) : ℝ)| ≤ (q:ℝ)/2 + 3/2 := by
  have hq0 : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  have h3 := err_le_one a q hq t ht r hr
  rw [idx_cast a q hq t x r]
  have hA : |(q:ℝ) * frac (x + (r:ℝ)*t)| ≤ (q:ℝ)/2 := by
    rw [abs_mul, abs_of_pos hq0]
    have h := abs_frac (x + (r:ℝ)*t)
    have h' := mul_le_mul_of_nonneg_left h (le_of_lt hq0)
    linarith
  have hB : |frac ((q:ℝ)*x)| ≤ 1/2 := abs_frac _
  have hsum : |(q:ℝ) * frac (x + (r:ℝ)*t) - frac ((q:ℝ)*x) - (q:ℝ)*(r:ℝ)*(t - (a:ℝ)/(q:ℝ))|
      ≤ (|(q:ℝ) * frac (x + (r:ℝ)*t)| + |frac ((q:ℝ)*x)|)
        + |(q:ℝ)*(r:ℝ)*(t - (a:ℝ)/(q:ℝ))| := by
    have e1 : (q:ℝ) * frac (x + (r:ℝ)*t) - frac ((q:ℝ)*x) - (q:ℝ)*(r:ℝ)*(t - (a:ℝ)/(q:ℝ))
        = (q:ℝ) * frac (x + (r:ℝ)*t)
          - (frac ((q:ℝ)*x) + (q:ℝ)*(r:ℝ)*(t - (a:ℝ)/(q:ℝ))) := by ring
    rw [e1]
    have h1 : |(q:ℝ) * frac (x + (r:ℝ)*t)
          - (frac ((q:ℝ)*x) + (q:ℝ)*(r:ℝ)*(t - (a:ℝ)/(q:ℝ)))|
        ≤ |(q:ℝ) * frac (x + (r:ℝ)*t)|
          + |frac ((q:ℝ)*x) + (q:ℝ)*(r:ℝ)*(t - (a:ℝ)/(q:ℝ))| := by
      have h := abs_sub_le ((q:ℝ) * frac (x + (r:ℝ)*t)) 0
        (frac ((q:ℝ)*x) + (q:ℝ)*(r:ℝ)*(t - (a:ℝ)/(q:ℝ)))
      rw [sub_zero, zero_sub, abs_neg] at h
      exact h
    have h2 : |frac ((q:ℝ)*x) + (q:ℝ)*(r:ℝ)*(t - (a:ℝ)/(q:ℝ))|
        ≤ |frac ((q:ℝ)*x)| + |(q:ℝ)*(r:ℝ)*(t - (a:ℝ)/(q:ℝ))| := abs_add_le _ _
    linarith
  linarith

theorem idx_le_two_mul (a q : ℕ) (hq : 1 ≤ q) (t x : ℝ)
    (ht : |t - (a:ℝ)/(q:ℝ)| ≤ 1/(q:ℝ)^2) (r : ℕ) (hr : r < q)
    (hj : 3 ≤ |((idx a q t x r : ℤ) : ℝ)|) :
    |((idx a q t x r : ℤ) : ℝ)| ≤ 2 * (q:ℝ) * |frac (x + (r:ℝ)*t)| := by
  have hq0 : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  have h3 := err_le_one a q hq t ht r hr
  have hrel : (q:ℝ) * frac (x + (r:ℝ)*t)
      = ((idx a q t x r : ℤ) : ℝ)
        + (frac ((q:ℝ)*x) + (q:ℝ)*(r:ℝ)*(t - (a:ℝ)/(q:ℝ))) := by
    rw [idx_cast a q hq t x r]
    ring
  have hC : |frac ((q:ℝ)*x) + (q:ℝ)*(r:ℝ)*(t - (a:ℝ)/(q:ℝ))| ≤ 3/2 := by
    have h := abs_add_le (frac ((q:ℝ)*x)) ((q:ℝ)*(r:ℝ)*(t - (a:ℝ)/(q:ℝ)))
    have h2 := abs_frac ((q:ℝ)*x)
    linarith
  have hB : |((idx a q t x r : ℤ) : ℝ)| ≤ |(q:ℝ) * frac (x + (r:ℝ)*t)| + 3/2 := by
    rw [hrel]
    have h := abs_sub_le (((idx a q t x r : ℤ) : ℝ)
        + (frac ((q:ℝ)*x) + (q:ℝ)*(r:ℝ)*(t - (a:ℝ)/(q:ℝ)))) 0
        (frac ((q:ℝ)*x) + (q:ℝ)*(r:ℝ)*(t - (a:ℝ)/(q:ℝ)))
    rw [add_sub_cancel_right, sub_zero, zero_sub, abs_neg] at h
    linarith
  have hA : |(q:ℝ) * frac (x + (r:ℝ)*t)| = (q:ℝ) * |frac (x + (r:ℝ)*t)| := by
    rw [abs_mul, abs_of_pos hq0]
  rw [hA] at hB
  linarith

theorem capaux_le_idx (a q : ℕ) (hq : 1 ≤ q) (t x H : ℝ) (hH : 0 ≤ H)
    (ht : |t - (a:ℝ)/(q:ℝ)| ≤ 1/(q:ℝ)^2) (r : ℕ) (hr : r < q)
    (hj : 3 ≤ |((idx a q t x r : ℤ) : ℝ)|) :
    capaux H (x + (r:ℝ)*t) ≤ (q:ℝ) / |((idx a q t x r : ℤ) : ℝ)| := by
  have hq0 : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  have hv : |frac (x + (r:ℝ)*t)| ≤ 1/2 := abs_frac _
  have hkey : |((idx a q t x r : ℤ) : ℝ)| ≤ 2 * (q:ℝ) * |frac (x + (r:ℝ)*t)| :=
    idx_le_two_mul a q hq t x ht r hr hj
  have hidx0 : (0:ℝ) < |((idx a q t x r : ℤ) : ℝ)| := by linarith
  have hvpos : (0:ℝ) < |frac (x + (r:ℝ)*t)| := by
    by_contra hc
    simp only [not_lt] at hc
    have hz : |frac (x + (r:ℝ)*t)| = 0 := le_antisymm hc (abs_nonneg _)
    rw [hz] at hkey
    simp only [mul_zero] at hkey
    linarith
  have hE : Eaux (frac (x + (r:ℝ)*t)) = Eaux (x + (r:ℝ)*t) :=
    Eaux_sub_int (x + (r:ℝ)*t) (rnd (x + (r:ℝ)*t))
  have hnorm : 4 * |frac (x + (r:ℝ)*t)| ≤ ‖(1:ℂ) - Eaux (frac (x + (r:ℝ)*t))‖ :=
    norm_one_sub_Eaux_ge _ hv
  have hden : (0:ℝ) < ‖(1:ℂ) - Eaux (frac (x + (r:ℝ)*t))‖ := by
    have h : (0:ℝ) < 4 * |frac (x + (r:ℝ)*t)| := by linarith
    linarith
  have hne : Eaux (x + (r:ℝ)*t) ≠ 1 := by
    rw [← hE]
    intro hcon
    rw [hcon] at hnorm
    simp only [sub_self, norm_zero] at hnorm
    linarith
  have hcap : capaux H (x + (r:ℝ)*t)
      ≤ 2 / ‖(1:ℂ) - Eaux (frac (x + (r:ℝ)*t))‖ := by
    have h := capaux_le_chord H (x + (r:ℝ)*t) hne
    rwa [← hE] at h
  refine le_trans hcap ?_
  rw [div_le_div_iff₀ hden hidx0]
  have h1 : 2 * |((idx a q t x r : ℤ) : ℝ)| ≤ 4 * (q:ℝ) * |frac (x + (r:ℝ)*t)| := by linarith
  have h2 : 4 * (q:ℝ) * |frac (x + (r:ℝ)*t)|
      ≤ (q:ℝ) * ‖(1:ℂ) - Eaux (frac (x + (r:ℝ)*t))‖ := by
    have h := mul_le_mul_of_nonneg_left hnorm (le_of_lt hq0)
    linarith
  linarith

theorem one_sub_inv_le_log' {x : ℝ} (hx : 0 < x) : 1 - 1/x ≤ Real.log x := by
  have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hx)
  rw [Real.log_inv] at h
  rw [one_div]
  linarith

theorem inv_le_log_sub (k : ℕ) (hk : 2 ≤ k) :
    (1:ℝ)/((k:ℕ):ℝ) ≤ Real.log ((k:ℕ):ℝ) - (Real.log (((k:ℕ):ℝ) - 1)) := by
  have hkpos : (0:ℝ) < ((k:ℕ):ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hk1pos : (0:ℝ) < ((k:ℕ):ℝ) - 1 := by
    have h : (1:ℝ) < ((k:ℕ):ℝ) := by exact_mod_cast (by omega : 1 < k)
    linarith
  have hx : (0:ℝ) < ((k:ℕ):ℝ) / (((k:ℕ):ℝ) - 1) := div_pos hkpos hk1pos
  have h1 := one_sub_inv_le_log' hx
  rw [Real.log_div hkpos.ne' hk1pos.ne'] at h1
  have hinv : (1:ℝ)/(((k:ℕ):ℝ) / (((k:ℕ):ℝ) - 1)) = 1 - 1/((k:ℕ):ℝ) := by
    field_simp
  rw [hinv] at h1
  linarith

theorem sum_range_inv_le_log (n : ℕ) :
    (∑ i ∈ Finset.range n, (1:ℝ)/((i:ℝ)+3)) ≤ Real.log ((n:ℝ)+2) - Real.log 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have h := inv_le_log_sub (n+3) (by omega)
    push_cast at h
    have e1 : ((n:ℝ) + 3 - 1) = ((n:ℝ) + 2) := by ring
    rw [e1] at h
    have e2 : (((Nat.succ n : ℕ):ℝ) + 2) = ((n:ℝ) + 3) := by
      push_cast
      ring
    rw [e2]
    linarith

theorem sum_Icc_shift (f : ℕ → ℝ) (N : ℕ) (hN : 3 ≤ N) :
    (∑ k ∈ Finset.Icc 3 N, f k) = ∑ i ∈ Finset.range (N - 2), f (i + 3) := by
  have himg : Finset.Icc 3 N = (Finset.range (N-2)).image (fun i => i + 3) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
    constructor
    · intro hk
      exact ⟨k - 3, by omega, by omega⟩
    · rintro ⟨i, hi, rfl⟩
      omega
  have hinj : Set.InjOn (fun i : ℕ => i + 3) (↑(Finset.range (N-2))) := by
    intro a ha b hb hab
    have h : a + 3 = b + 3 := hab
    omega
  rw [himg, Finset.sum_image hinj]

theorem sum_Icc_inv_le_log (N : ℕ) (hN : 3 ≤ N) :
    (∑ k ∈ Finset.Icc 3 N, (1:ℝ)/((k:ℕ):ℝ)) ≤ Real.log ((N:ℕ):ℝ) - Real.log 2 := by
  have hshift : (∑ k ∈ Finset.Icc 3 N, (1:ℝ)/((k:ℕ):ℝ))
      = ∑ i ∈ Finset.range (N-2), (1:ℝ)/((i:ℝ)+3) := by
    rw [sum_Icc_shift (fun k => (1:ℝ)/((k:ℕ):ℝ)) N hN]
    apply Finset.sum_congr rfl
    intro i hi
    push_cast
    ring
  rw [hshift]
  have h := sum_range_inv_le_log (N - 2)
  have hcast : (((N-2:ℕ):ℕ):ℝ) + 2 = ((N:ℕ):ℝ) := by
    have h2 : (2:ℕ) ≤ N := by omega
    rw [Nat.cast_sub h2]
    push_cast
    ring
  rw [hcast] at h
  exact h

theorem sum_Icc_inv_le (q : ℕ) (hq : 1 ≤ q) :
    (∑ k ∈ Finset.Icc 3 (q+3), (1:ℝ)/((k:ℕ):ℝ)) ≤ 3 * Real.log (2 * (q:ℝ)) := by
  have h1 : (∑ k ∈ Finset.Icc 3 (q+3), (1:ℝ)/((k:ℕ):ℝ))
      ≤ Real.log (((q+3:ℕ):ℕ):ℝ) - Real.log 2 := sum_Icc_inv_le_log (q+3) (by omega)
  have hq0 : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  have hq1 : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
  have hlog2 : (0:ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hq2 : (1:ℝ) ≤ (q:ℝ)^2 := by nlinarith
  have hq3 : (1:ℝ) ≤ (q:ℝ)^3 := by
    have h := mul_le_mul hq1 hq2 (by norm_num) (by norm_num)
    nlinarith
  have hq4 : (q:ℝ) ≤ (q:ℝ)^3 := by
    have h := mul_le_mul_of_nonneg_left hq2 (le_of_lt hq0)
    nlinarith
  have hN : (((q+3:ℕ):ℕ):ℝ) ≤ 8 * (q:ℝ)^3 := by
    push_cast
    nlinarith
  have hlogN : Real.log (((q+3:ℕ):ℕ):ℝ) ≤ Real.log (8 * (q:ℝ)^3) :=
    Real.log_le_log (by positivity) hN
  have hpow : (8:ℝ) * (q:ℝ)^3 = (2 * (q:ℝ))^3 := by ring
  rw [hpow, Real.log_pow] at hlogN
  have h3 : ((3:ℕ):ℝ) = (3:ℝ) := by norm_num
  rw [h3] at hlogN
  linarith

theorem sum_inv_pos_le (j : ℕ → ℤ) (S : Finset ℕ) (M : ℕ)
    (hinj : ∀ r ∈ S, ∀ r' ∈ S, j r = j r' → r = r')
    (hpos : ∀ r ∈ S, 0 < j r)
    (hlo : ∀ r ∈ S, (3:ℤ) ≤ j r)
    (hhi : ∀ r ∈ S, j r ≤ (M:ℤ)) :
    (∑ r ∈ S, (1:ℝ)/|((j r : ℤ):ℝ)|) ≤ ∑ k ∈ Finset.Icc 3 M, (1:ℝ)/((k:ℕ):ℝ) := by
  classical
  have hinjSp : Set.InjOn (fun r => (j r).toNat) (↑S) := by
    intro r hr r' hr' h
    have hrS : r ∈ S := Finset.mem_coe.mp hr
    have hr'S : r' ∈ S := Finset.mem_coe.mp hr'
    have h1 : (((j r).toNat : ℕ) : ℤ) = j r := Int.toNat_of_nonneg (le_of_lt (hpos r hrS))
    have h2 : (((j r').toNat : ℕ) : ℤ) = j r' := Int.toNat_of_nonneg (le_of_lt (hpos r' hr'S))
    have h3 : (((j r).toNat : ℕ) : ℤ) = (((j r').toNat : ℕ) : ℤ) := by exact_mod_cast h
    rw [h1, h2] at h3
    exact hinj r hrS r' hr'S h3
  have hsub : S.image (fun r => (j r).toNat) ⊆ Finset.Icc 3 M := by
    intro k hk
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hk
    have h1 : (3:ℕ) ≤ (j r).toNat := by
      have h : ((3:ℕ):ℤ) ≤ (((j r).toNat : ℕ) : ℤ) := by
        rw [Int.toNat_of_nonneg (le_of_lt (hpos r hr))]
        exact hlo r hr
      exact_mod_cast h
    have h2 : (j r).toNat ≤ M := by
      have h : (((j r).toNat : ℕ) : ℤ) ≤ ((M:ℕ):ℤ) := by
        rw [Int.toNat_of_nonneg (le_of_lt (hpos r hr))]
        exact hhi r hr
      exact_mod_cast h
    exact Finset.mem_Icc.mpr ⟨h1, h2⟩
  have hrw : ∀ r ∈ S, (1:ℝ)/|((j r : ℤ):ℝ)| = (1:ℝ)/(((j r).toNat : ℕ):ℝ) := by
    intro r hr
    have hjr : (0:ℤ) < j r := hpos r hr
    have h1 : (((j r).toNat : ℕ):ℤ) = j r := Int.toNat_of_nonneg (le_of_lt hjr)
    have h2 : (((j r).toNat : ℕ):ℝ) = ((j r : ℤ):ℝ) := by exact_mod_cast h1
    have h3 : (0:ℝ) < ((j r : ℤ):ℝ) := by exact_mod_cast hjr
    rw [abs_of_pos h3, h2]
  calc (∑ r ∈ S, (1:ℝ)/|((j r : ℤ):ℝ)|)
      = ∑ r ∈ S, (1:ℝ)/(((j r).toNat : ℕ):ℝ) := by
        apply Finset.sum_congr rfl
        intro r hr
        exact hrw r hr
    _ = ∑ k ∈ S.image (fun r => (j r).toNat), (1:ℝ)/((k:ℕ):ℝ) := by
        rw [Finset.sum_image hinjSp]
    _ ≤ ∑ k ∈ Finset.Icc 3 M, (1:ℝ)/((k:ℕ):ℝ) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
        intro k hk hk'
        positivity

theorem sum_inv_le (j : ℕ → ℤ) (S : Finset ℕ) (M : ℕ)
    (hinj : ∀ r ∈ S, ∀ r' ∈ S, j r = j r' → r = r')
    (hbig : ∀ r ∈ S, 3 ≤ |((j r : ℤ):ℝ)|)
    (hbdd : ∀ r ∈ S, |((j r : ℤ):ℝ)| ≤ ((M:ℕ):ℝ)) :
    (∑ r ∈ S, (1:ℝ)/|((j r : ℤ):ℝ)|) ≤ 2 * (∑ k ∈ Finset.Icc 3 M, (1:ℝ)/((k:ℕ):ℝ)) := by
  classical
  have hpos' : ∀ r ∈ S, 0 < j r → (3:ℤ) ≤ j r ∧ j r ≤ ((M:ℕ):ℤ) := by
    intro r hr hjr
    have hb := hbig r hr
    have hd := hbdd r hr
    have habs : |((j r : ℤ):ℝ)| = ((j r : ℤ):ℝ) := abs_of_pos (by exact_mod_cast hjr)
    rw [habs] at hb hd
    exact ⟨by exact_mod_cast hb, by exact_mod_cast hd⟩
  have hneg' : ∀ r ∈ S, j r < 0 → (3:ℤ) ≤ -j r ∧ -j r ≤ ((M:ℕ):ℤ) := by
    intro r hr hjr
    have hb := hbig r hr
    have hd := hbdd r hr
    have habs : |((j r : ℤ):ℝ)| = ((-j r : ℤ):ℝ) := by
      have h4 : ((j r : ℤ):ℝ) ≤ 0 := by exact_mod_cast (le_of_lt hjr)
      rw [abs_of_nonpos h4]
      push_cast
      ring
    rw [habs] at hb hd
    exact ⟨by exact_mod_cast hb, by exact_mod_cast hd⟩
  have hne : ∀ r ∈ S, j r ≠ 0 := by
    intro r hr hz
    have hb := hbig r hr
    rw [hz] at hb
    simp only [Int.cast_zero, abs_zero] at hb
    linarith
  have hSmem : ∀ r ∈ S.filter (fun r => ¬ (0 < j r)), j r < 0 := by
    intro r hr
    have h2 : ¬ (0 < j r) := (Finset.mem_filter.mp hr).2
    have h3 : j r ≤ 0 := by omega
    have h4 : j r ≠ 0 := hne r (Finset.filter_subset _ _ hr)
    exact lt_of_le_of_ne h3 h4
  have hSp : (∑ r ∈ S.filter (fun r => 0 < j r), (1:ℝ)/|((j r : ℤ):ℝ)|)
      ≤ ∑ k ∈ Finset.Icc 3 M, (1:ℝ)/((k:ℕ):ℝ) := by
    refine sum_inv_pos_le j (S.filter (fun r => 0 < j r)) M ?_ ?_ ?_ ?_
    · intro r hr r' hr' h
      exact hinj r (Finset.filter_subset _ _ hr) r' (Finset.filter_subset _ _ hr') h
    · intro r hr
      exact (Finset.mem_filter.mp hr).2
    · intro r hr
      exact (hpos' r (Finset.filter_subset _ _ hr) (Finset.mem_filter.mp hr).2).1
    · intro r hr
      exact (hpos' r (Finset.filter_subset _ _ hr) (Finset.mem_filter.mp hr).2).2
  have hSm : (∑ r ∈ S.filter (fun r => ¬ (0 < j r)), (1:ℝ)/|((j r : ℤ):ℝ)|)
      ≤ ∑ k ∈ Finset.Icc 3 M, (1:ℝ)/((k:ℕ):ℝ) := by
    have h1 : (∑ r ∈ S.filter (fun r => ¬ (0 < j r)), (1:ℝ)/|((j r : ℤ):ℝ)|)
        = ∑ r ∈ S.filter (fun r => ¬ (0 < j r)), (1:ℝ)/|(((-j r : ℤ)):ℝ)| := by
      apply Finset.sum_congr rfl
      intro r hr
      have h5 : ((-j r : ℤ):ℝ) = -((j r : ℤ):ℝ) := by
        push_cast
        ring
      rw [h5, abs_neg]
    rw [h1]
    refine sum_inv_pos_le (fun r => -j r) (S.filter (fun r => ¬ (0 < j r))) M ?_ ?_ ?_ ?_
    · intro r hr r' hr' h
      have h2 : j r = j r' := by linarith
      exact hinj r (Finset.filter_subset _ _ hr) r' (Finset.filter_subset _ _ hr') h2
    · intro r hr
      have h5 := hSmem r hr
      omega
    · intro r hr
      exact (hneg' r (Finset.filter_subset _ _ hr) (hSmem r hr)).1
    · intro r hr
      exact (hneg' r (Finset.filter_subset _ _ hr) (hSmem r hr)).2
  have hkey : (∑ r ∈ S, (1:ℝ)/|((j r : ℤ):ℝ)|)
      = (∑ r ∈ S.filter (fun r => 0 < j r), (1:ℝ)/|((j r : ℤ):ℝ)|)
        + (∑ r ∈ S.filter (fun r => ¬ (0 < j r)), (1:ℝ)/|((j r : ℤ):ℝ)|) := by
    have h := Finset.sum_ite (p := fun r => 0 < j r) (s := S) (fun r => (1:ℝ)/|((j r : ℤ):ℝ)|) (fun r => (1:ℝ)/|((j r : ℤ):ℝ)|)
    simpa using h
  calc (∑ r ∈ S, (1:ℝ)/|((j r : ℤ):ℝ)|)
      = (∑ r ∈ S.filter (fun r => 0 < j r), (1:ℝ)/|((j r : ℤ):ℝ)|)
        + (∑ r ∈ S.filter (fun r => ¬ (0 < j r)), (1:ℝ)/|((j r : ℤ):ℝ)|) := hkey
    _ ≤ (∑ k ∈ Finset.Icc 3 M, (1:ℝ)/((k:ℕ):ℝ))
        + (∑ k ∈ Finset.Icc 3 M, (1:ℝ)/((k:ℕ):ℝ)) := add_le_add hSp hSm
    _ = 2 * (∑ k ∈ Finset.Icc 3 M, (1:ℝ)/((k:ℕ):ℝ)) := by ring

theorem sum_bound (a q : ℕ) (hq : 1 ≤ q) (hcop : Nat.Coprime a q) (t x H : ℝ) (hH : 0 ≤ H)
    (ht : |t - (a:ℝ)/(q:ℝ)| ≤ 1/(q:ℝ)^2) :
    (∑ r ∈ Finset.range q, capaux H (x + (r:ℝ)*t))
      ≤ 6 * (H + (q:ℝ) * Real.log (2 * (q:ℝ))) := by
  classical
  have hq0 : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  have hinj0 : Set.InjOn (idx a q t x) (↑(Finset.range q)) := idx_injOn a q hq hcop t x
  have hpt : ∀ r ∈ Finset.range q, capaux H (x + (r:ℝ)*t)
      ≤ (if |((idx a q t x r : ℤ):ℝ)| < 3 then H
          else (q:ℝ)/|((idx a q t x r : ℤ):ℝ)|) := by
    intro r hr
    have hrq : r < q := Finset.mem_range.mp hr
    by_cases hc : |((idx a q t x r : ℤ):ℝ)| < 3
    · rw [if_pos hc]
      exact capaux_le_H H _
    · rw [if_neg hc]
      have hc' : 3 ≤ |((idx a q t x r : ℤ):ℝ)| := by
        simp only [not_lt] at hc
        exact hc
      exact capaux_le_idx a q hq t x H hH ht r hrq hc'
  have hsum1 : (∑ r ∈ Finset.range q, capaux H (x + (r:ℝ)*t))
      ≤ ∑ r ∈ Finset.range q, (if |((idx a q t x r : ℤ):ℝ)| < 3 then H
          else (q:ℝ)/|((idx a q t x r : ℤ):ℝ)|) := Finset.sum_le_sum hpt
  have hsplit : (∑ r ∈ Finset.range q, (if |((idx a q t x r : ℤ):ℝ)| < 3 then H
        else (q:ℝ)/|((idx a q t x r : ℤ):ℝ)|))
      = (∑ r ∈ (Finset.range q).filter (fun r => |((idx a q t x r : ℤ):ℝ)| < 3), H)
        + (∑ r ∈ (Finset.range q).filter (fun r => ¬(|((idx a q t x r : ℤ):ℝ)| < 3)),
            (q:ℝ)/|((idx a q t x r : ℤ):ℝ)|) := by
    rw [Finset.sum_ite]
  have hcardA : (∑ r ∈ (Finset.range q).filter (fun r => |((idx a q t x r : ℤ):ℝ)| < 3), H)
      = (((Finset.range q).filter (fun r => |((idx a q t x r : ℤ):ℝ)| < 3)).card : ℝ) * H := by
    rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : ((Finset.range q).filter (fun r => |((idx a q t x r : ℤ):ℝ)| < 3)).card ≤ 5 := by
    have hmaps : Set.MapsTo (idx a q t x)
        (↑((Finset.range q).filter (fun r => |((idx a q t x r : ℤ):ℝ)| < 3)))
        (↑(Finset.Icc (-2:ℤ) 2)) := by
      intro r hr
      have hr' := Finset.mem_filter.mp (Finset.mem_coe.mp hr)
      have hP : |((idx a q t x r : ℤ):ℝ)| < 3 := hr'.2
      rw [abs_lt] at hP
      have h1 : (-2:ℤ) ≤ idx a q t x r := by
        by_contra hc
        have hc' : idx a q t x r ≤ -3 := by omega
        have h5 : ((idx a q t x r : ℤ):ℝ) ≤ (-3:ℝ) := by exact_mod_cast hc'
        linarith [hP.1]
      have h2 : idx a q t x r ≤ 2 := by
        by_contra hc
        have hc' : (3:ℤ) ≤ idx a q t x r := by omega
        have h5 : (3:ℝ) ≤ ((idx a q t x r : ℤ):ℝ) := by exact_mod_cast hc'
        linarith [hP.2]
      exact Finset.mem_coe.mpr (Finset.mem_Icc.mpr ⟨h1, h2⟩)
    have hin : Set.InjOn (idx a q t x)
        (↑((Finset.range q).filter (fun r => |((idx a q t x r : ℤ):ℝ)| < 3))) := by
      intro r hr r' hr' h
      exact hinj0 (Finset.mem_coe.mpr (Finset.filter_subset _ _ (Finset.mem_coe.mp hr)))
        (Finset.mem_coe.mpr (Finset.filter_subset _ _ (Finset.mem_coe.mp hr'))) h
    have h := Finset.card_le_card_of_injOn (idx a q t x) hmaps hin
    have h5 : (Finset.Icc (-2:ℤ) 2).card = 5 := by
      rw [Int.card_Icc]
      norm_num
    rw [h5] at h
    exact h
  have hpart1 : (((Finset.range q).filter (fun r => |((idx a q t x r : ℤ):ℝ)| < 3)).card : ℝ) * H
      ≤ 5 * H := by
    have h := mul_le_mul_of_nonneg_right
      (show (((Finset.range q).filter
        (fun r => |((idx a q t x r : ℤ):ℝ)| < 3)).card : ℝ) ≤ 5 from by exact_mod_cast hcard) hH
    exact h
  have hC : (∑ r ∈ (Finset.range q).filter (fun r => ¬(|((idx a q t x r : ℤ):ℝ)| < 3)),
        (q:ℝ)/|((idx a q t x r : ℤ):ℝ)|)
      ≤ 2 * (q:ℝ) * (∑ k ∈ Finset.Icc 3 (q+3), (1:ℝ)/((k:ℕ):ℝ)) := by
    have h1 : (∑ r ∈ (Finset.range q).filter (fun r => ¬(|((idx a q t x r : ℤ):ℝ)| < 3)),
          (q:ℝ)/|((idx a q t x r : ℤ):ℝ)|)
        = (q:ℝ) * (∑ r ∈ (Finset.range q).filter (fun r => ¬(|((idx a q t x r : ℤ):ℝ)| < 3)),
            (1:ℝ)/|((idx a q t x r : ℤ):ℝ)|) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [h1]
    have h2 := sum_inv_le (idx a q t x)
      ((Finset.range q).filter (fun r => ¬(|((idx a q t x r : ℤ):ℝ)| < 3))) (q+3)
      (fun r hr r' hr' h => hinj0
        (Finset.mem_coe.mpr (Finset.filter_subset _ _ hr))
        (Finset.mem_coe.mpr (Finset.filter_subset _ _ hr')) h)
      (fun r hr => by
        have h5 := (Finset.mem_filter.mp hr).2
        simp only [not_lt] at h5
        exact h5)
      (fun r hr => by
        have h5 := idx_abs_le a q hq t x ht r (Finset.mem_range.mp (Finset.mem_filter.mp hr).1)
        have h6 : (q:ℝ)/2 + 3/2 ≤ (((q+3:ℕ):ℕ):ℝ) := by
          push_cast
          linarith
        linarith)
    calc (q:ℝ) * (∑ r ∈ (Finset.range q).filter (fun r => ¬(|((idx a q t x r : ℤ):ℝ)| < 3)),
            (1:ℝ)/|((idx a q t x r : ℤ):ℝ)|)
        ≤ (q:ℝ) * (2 * (∑ k ∈ Finset.Icc 3 (q+3), (1:ℝ)/((k:ℕ):ℝ))) :=
          mul_le_mul_of_nonneg_left h2 (le_of_lt hq0)
      _ = 2 * (q:ℝ) * (∑ k ∈ Finset.Icc 3 (q+3), (1:ℝ)/((k:ℕ):ℝ)) := by ring
  have hS : (∑ k ∈ Finset.Icc 3 (q+3), (1:ℝ)/((k:ℕ):ℝ)) ≤ 3 * Real.log (2 * (q:ℝ)) :=
    sum_Icc_inv_le q hq
  calc (∑ r ∈ Finset.range q, capaux H (x + (r:ℝ)*t))
      ≤ ∑ r ∈ Finset.range q, (if |((idx a q t x r : ℤ):ℝ)| < 3 then H
          else (q:ℝ)/|((idx a q t x r : ℤ):ℝ)|) := hsum1
    _ = (∑ r ∈ (Finset.range q).filter (fun r => |((idx a q t x r : ℤ):ℝ)| < 3), H)
        + (∑ r ∈ (Finset.range q).filter (fun r => ¬(|((idx a q t x r : ℤ):ℝ)| < 3)),
            (q:ℝ)/|((idx a q t x r : ℤ):ℝ)|) := hsplit
    _ ≤ 5 * H + 2 * (q:ℝ) * (∑ k ∈ Finset.Icc 3 (q+3), (1:ℝ)/((k:ℕ):ℝ)) := by
        rw [hcardA]
        linarith
    _ ≤ 5 * H + 6 * (q:ℝ) * Real.log (2 * (q:ℝ)) := by
        have h := mul_le_mul_of_nonneg_left hS (by positivity : (0:ℝ) ≤ 2 * (q:ℝ))
        linarith
    _ ≤ 6 * (H + (q:ℝ) * Real.log (2 * (q:ℝ))) := by nlinarith

end Conjectures.Goldbach.ReciprocalChordSum_aux

namespace Conjectures.Goldbach

open Conjectures.Goldbach.ReciprocalChordSum_aux

theorem ReciprocalChordSum :
    let E (y : ℝ) := Complex.exp (((2 * Real.pi * y : ℝ) : ℂ) * Complex.I); let cap (H y : ℝ) := if E y = 1 then H else min H (2 / ‖1 - E y‖); ∀ (a q : ℕ) (t x H : ℝ), 1 ≤ q → Nat.Coprime a q → 0 ≤ H → |t - (a : ℝ) / q| ≤ 1 / (q : ℝ)^2 → (∑ r ∈ Finset.range q, cap H (x + (r : ℝ)*t)) ≤ 6 * (H + (q : ℝ) * Real.log (2 * q)) := by
  simp only []
  intro a q t x H hq hcop hH ht
  exact sum_bound a q hq hcop t x H hH ht

end Conjectures.Goldbach
