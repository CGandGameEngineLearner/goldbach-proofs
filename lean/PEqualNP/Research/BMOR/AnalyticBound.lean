import Mathlib

/-!
# The maximum used in BMOR Lemma 4.20

Bennett, Martin, O'Bryant and Rechnitzer, *Explicit bounds for primes in
arithmetic progressions*, Lemma 4.20, Definitions 4.15–4.16.
https://personal.math.ubc.ca/~bennett/BeMaObRe-IJM-2018.pdf#page=42
-/

namespace PEqualNP.Outside.BMOR

open Real

/-- The factor occurring in both summands of P₁ₐ, with u = log x and c = Rλ.
Its maximum on positive u is attained at u = a c. -/
theorem weight_peak {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    (∀ u : ℝ, 0 < u → u ^ a * exp (-u / c) ≤ (a*c / exp 1)^a) ∧
    (a*c)^a * exp (-(a*c) / c) = (a*c / exp 1)^a := by
  have hac := mul_pos ha hc
  have hlog : log (a*c / exp 1) = log (a*c) - 1 := by
    rw [log_div hac.ne' (exp_pos _).ne', log_exp]
  constructor
  · intro u hu
    have ht := Real.log_le_sub_one_of_pos (div_pos hu hac)
    rw [log_div hu.ne' hac.ne'] at ht
    have ht' := mul_le_mul_of_nonneg_left ht ha.le
    have hcancel : a * (u / (a*c)) = u / c := by field_simp
    rw [mul_sub, mul_sub, hcancel] at ht'
    rw [rpow_def_of_pos hu, ← exp_add, rpow_def_of_pos (div_pos hac (exp_pos _)), hlog,
      exp_le_exp]
    rw [neg_div]
    linarith only [ht']
  · rw [rpow_def_of_pos hac, ← exp_add, rpow_def_of_pos (div_pos hac (exp_pos _)), hlog]
    congr 1
    field_simp
    ring

/-- BMOR Definition 4.15. -/
noncomputable def P1a (x m r l H R : ℝ) : ℝ :=
  1 / H^m * (3 * R^(1/4 : ℝ) * l^(1/2 : ℝ) * (log x)^(r-1/4) /
    (16 * m^(3/4 : ℝ)) + (log x)^r/(2*m)) * exp (-(log x)/(R*l))

/-- The two maxima in BMOR Lemma 4.20 before extracting the common factor.
They come from log x = (r - 1/4) Rλ and log x = r Rλ, respectively. -/
theorem P1a_le_peaks {x m r l H R : ℝ} (hx : 1 < x) (hm : 0 < m)
    (hr : 1/4 < r) (hl : 0 < l) (hH : 0 < H) (hR : 0 < R) :
    P1a x m r l H R ≤ 1 / H^m *
      (3 * R^(1/4 : ℝ) * l^(1/2 : ℝ) / (16 * m^(3/4 : ℝ)) *
        ((r-1/4)*(R*l)/exp 1)^(r-1/4) + 1/(2*m) * (r*(R*l)/exp 1)^r) := by
  have h₁ := (weight_peak (sub_pos.mpr hr) (mul_pos hR hl)).1 (log x) (log_pos hx)
  have h₂ := (weight_peak (lt_trans (by norm_num : 0 < (1/4 : ℝ)) hr)
    (mul_pos hR hl)).1 (log x) (log_pos hx)
  let A := 3 * R^(1/4 : ℝ) * l^(1/2 : ℝ) / (16 * m^(3/4 : ℝ))
  let B := 1/(2*m)
  trans 1 / H^m * (A * ((log x)^(r-1/4)*exp (-(log x)/(R*l))) +
    B * ((log x)^r*exp (-(log x)/(R*l))))
  · unfold P1a A B
    apply le_of_eq
    ring
  · apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact add_le_add (mul_le_mul_of_nonneg_left h₁ (by positivity))
      (mul_le_mul_of_nonneg_left h₂ (by positivity))


/-- BMOR Definition 4.16, with e = exp 1. -/
noncomputable def Q1a (m r l H R : ℝ) : ℝ :=
  R^r / ((exp 1)^r * H^m) *
    (3 * (exp 1)^(1/4 : ℝ) * (r-1/4)^(r-1/4) * l^(r+1/4) /
      (16*m^(3/4 : ℝ)) + r^r * l^r / (2*m))

/-- BMOR Lemma 4.20. The two summands may attain their maxima at different x. -/
theorem lemma4_20 {x m r l H R : ℝ} (hx : 1 < x) (hm : 0 < m)
    (hr : 1/4 < r) (hl : 0 < l) (hH : 0 < H) (hR : 0 < R) :
    P1a x m r l H R ≤ Q1a m r l H R := by
  apply (P1a_le_peaks hx hm hr hl hH hR).trans (le_of_eq ?_)
  have hr' : 0 < r := lt_trans (by norm_num) hr
  have he := exp_pos 1
  have hhalf : l^(1/2 : ℝ) = l^(1/4 : ℝ)*l^(1/4 : ℝ) := by
    rw [← rpow_add hl]
    norm_num
  unfold Q1a
  rw [div_rpow (mul_pos (sub_pos.mpr hr) (mul_pos hR hl)).le he.le,
    div_rpow (mul_pos hr' (mul_pos hR hl)).le he.le,
    mul_rpow (sub_pos.mpr hr).le (mul_pos hR hl).le, mul_rpow hr'.le (mul_pos hR hl).le,
    mul_rpow hR.le hl.le, mul_rpow hR.le hl.le, rpow_sub hR, rpow_sub hl, rpow_sub he,
    rpow_add hl, hhalf]
  field_simp

end PEqualNP.Outside.BMOR
