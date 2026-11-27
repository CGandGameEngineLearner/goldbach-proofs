import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The half-plane comparison for Pintz's zero-density kernel

Pintz, *A new explicit formula in the additive theory of primes with applications II*,
§5, (5.23)–(5.24), https://arxiv.org/html/1804.09084v2.
The proof integrates a real differential identity for the truncated Laplace transform.
-/
open MeasureTheory

namespace PintzLaplaceKernel

noncomputable def transform (a : ℂ) (t : ℝ) : ℂ :=
  (1 - Complex.exp (-a*t)) / a

private theorem deriv_transform {a : ℂ} (ha : a ≠ 0) (x : ℂ) :
    HasDerivAt (fun v : ℂ => (1 - Complex.exp (-a*v))/a) (Complex.exp (-a*x)) x := by
  have h := (((hasDerivAt_id x).const_mul (-a)).cexp.const_sub (1:ℂ)).div_const a
  convert h using 1
  simp
  field_simp
  rfl

private theorem derivative_re_im {a : ℂ} (ha : a ≠ 0) (t : ℝ) :
    HasDerivAt (fun s => (transform a s).re) (Complex.exp (-a*t)).re t ∧
    HasDerivAt (fun s => (transform a s).im) (Complex.exp (-a*t)).im t := by
  have h := deriv_transform ha (t:ℂ)
  refine ⟨h.real_of_complex, ?_⟩
  have hi := (h.const_mul (-Complex.I)).real_of_complex
  simpa [transform, Complex.mul_re] using hi

private theorem kernel_coefficient (l w t : ℝ) :
    (Real.exp (2*l*w) - Real.exp (2*l*t)) * Real.exp (-l*t) =
    2 * Real.exp (l*w) * Real.sinh (l*(w-t)) := by
  rw [Real.sinh_eq, sub_mul, ← Real.exp_add, ← Real.exp_add]
  rw [show 2*l*w + -l*t = l*w + l*(w-t) by ring,
    show 2*l*t + -l*t = l*w + -(l*(w-t)) by ring,
    Real.exp_add, Real.exp_add]
  ring

/-- Exact energy identity behind (5.24). Its integral remainder is proportional
to the real part of the spectral parameter; it vanishes on the imaginary axis. -/
theorem energy_identity {l : ℝ} (hl : 0 < l) (w : ℝ) (z : ℂ) (hz : 0 ≤ z.re) :
    2 * Real.exp (l*w) *
      (∫ t in (0:ℝ)..w, Complex.exp (-z*t) * (Real.sinh (l*(w-t)) : ℂ)).re =
    l * Real.exp (2*l*w) * ‖transform ((l:ℂ)+z) w‖^2 +
    (2*l*z.re) * ∫ t in (0:ℝ)..w, Real.exp (2*l*t) * ‖transform ((l:ℂ)+z) t‖^2 := by
  let a : ℂ := l + z
  have ha : a ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp [a] at this
    linarith
  let U := fun t => transform a t
  let q := fun t : ℝ => (U t).re^2 + (U t).im^2
  let V := fun t : ℝ => Real.exp (2*l*t)
  let f := fun t : ℝ => Complex.exp (-a*t)
  let g := fun t : ℝ => (Complex.exp (-z*t)).re * Real.sinh (l*(w-t))
  -- At zero this primitive vanishes; at w only the squared transform survives.
  -- Its derivative has a remainder with sign determined by z.re.
  let P := fun t : ℝ => (V w - V t)*(U t).re + l*V t*q t
  have hODE (t : ℝ) : f t = 1-a*U t := by
    dsimp [f, U, transform]
    field_simp
    ring
  have hV (t : ℝ) : HasDerivAt V (2*l*V t) t := by
    simpa [V, mul_comm] using (((hasDerivAt_id t).const_mul (2*l)).exp)
  have hq (t : ℝ) : HasDerivAt q (2*(U t).re - 2*(l+z.re)*q t) t := by
    obtain ⟨hr, hi⟩ := derivative_re_im ha t
    convert (hr.pow 2).add (hi.pow 2) using 1
    change _ = 2 * (U t).re^(2-1) * (f t).re + 2 * (U t).im^(2-1) * (f t).im
    rw [hODE]
    simp [a, Complex.mul_re, Complex.mul_im, q]
    ring
  have hcoef (t : ℝ) : (V w - V t)*(f t).re = 2*Real.exp (l*w)*g t := by
    have hsplit : f t = (Real.exp (-l*t) : ℂ) * Complex.exp (-z*t) := by
      dsimp [f, a]
      rw [Complex.ofReal_exp, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [hsplit, Complex.re_ofReal_mul]
    dsimp [V, g]
    linear_combination (Complex.exp (-z*t)).re * kernel_coefficient l w t
  let D := fun t : ℝ => 2*Real.exp (l*w)*g t - 2*l*z.re*V t*q t
  have hP (t : ℝ) : HasDerivAt P (D t) t := by
    have hr := (derivative_re_im ha t).1
    have hp := (((hV t).const_sub (V w)).mul hr).add (((hV t).const_mul l).mul (hq t))
    convert hp using 1
    dsimp only [D]
    rw [← hcoef]
    change _ = -(2*l*V t)*(U t).re + (V w-V t)*(f t).re +
      (l*(2*l*V t)*q t + l*V t*(2*(U t).re-2*(l+z.re)*q t))
    ring
  have cg : Continuous g := by dsimp [g]; fun_prop
  have cD : Continuous D := by dsimp [D,g,V,q,U,transform]; fun_prop
  have hft := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := w)
    (fun t _ => hP t) (cD.intervalIntegrable _ _)
  have hz0 : U 0 = 0 := by simp [U, transform]
  have hend : P w - P 0 = l * Real.exp (2*l*w) * q w := by simp [P, V, q, hz0]
  rw [hend] at hft
  have hreal : (∫ t in (0:ℝ)..w, Complex.exp (-z*t) * (Real.sinh (l*(w-t)) : ℂ)).re =
      ∫ t in (0:ℝ)..w, g t := by
    have hc : Continuous (fun t : ℝ => Complex.exp (-z*t) * (Real.sinh (l*(w-t)):ℂ)) := by fun_prop
    simpa only [g, Complex.reCLM_apply, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero] using
      (Complex.reCLM.intervalIntegral_comp_comm (hc.intervalIntegrable (μ := MeasureTheory.volume) 0 w)).symm
  have normq (t : ℝ) : ‖transform ((l:ℂ)+z) t‖^2 = q t := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    dsimp only [q, U, a]
    ring
  have cQ : Continuous (fun t => V t * q t) := by dsimp [V, q, U, transform]; fun_prop
  change (∫ t in (0:ℝ)..w, 2 * Real.exp (l*w) * g t - (2*l*z.re*V t)*q t) = _ at hft
  simp_rw [mul_assoc (2*l*z.re)] at hft
  have i₁ : IntervalIntegrable (fun t => (2*Real.exp (l*w))*g t) MeasureTheory.volume 0 w :=
    (continuous_const.mul cg).intervalIntegrable _ _
  have i₂ : IntervalIntegrable (fun t => (2*l*z.re)*(V t*q t)) MeasureTheory.volume 0 w :=
    (continuous_const.mul cQ).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub i₁ i₂, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul] at hft
  simp_rw [normq]
  rw [hreal]
  change _ = _ + (2*l*z.re) * ∫ t in (0:ℝ)..w, V t*q t
  linarith only [hft]

/-- The half-plane inequality with the integral and the squared quotient of
(5.23). The width may be zero. -/
theorem half_plane {l w : ℝ} (hl : 0 < l) (hw : 0 ≤ w) (z : ℂ) (hz : 0 ≤ z.re) :
    l * Real.exp (w*l) / 2 * ‖(transform ((l:ℂ)+z) w)^2‖ ≤
      (∫ t in (0:ℝ)..w, Complex.exp (-z*t) * (Real.sinh (l*(w-t)) : ℂ)).re := by
  have h := energy_identity hl w z hz
  have hI : 0 ≤ ∫ t in (0:ℝ)..w, Real.exp (2*l*t) * ‖transform ((l:ℂ)+z) t‖^2 :=
    intervalIntegral.integral_nonneg hw (fun _ _ => by positivity)
  have hr := mul_nonneg (show 0 ≤ 2*l*z.re by positivity) hI
  apply (mul_le_mul_iff_right₀ (show 0 < 2*Real.exp (l*w) by positivity)).mp
  rw [h, Complex.norm_pow, show w*l=l*w by ring,
    show 2*l*w = l*w + l*w by ring, Real.exp_add]
  linarith only [hr]

/-- The zero-frequency term in (5.28). -/
theorem kernel_at_zero {l : ℝ} (hl : 0 < l) (w : ℝ) :
    (∫ t in (0:ℝ)..w, Real.sinh (l*(w-t))) = (Real.cosh (w*l)-1)/l := by
  have h (t : ℝ) : HasDerivAt (fun x : ℝ => -Real.cosh (l*(w-x))/l)
      (Real.sinh (l*(w-t))) t := by
    have d := ((((hasDerivAt_id t).const_sub w).const_mul l).cosh.neg).div_const l
    convert d using 1
    simp
    field_simp
    rfl
  have hc : Continuous (fun t : ℝ => Real.sinh (l*(w-t))) := by fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => h t) (hc.intervalIntegrable _ _)]
  simp only [sub_self, mul_zero, Real.cosh_zero, sub_zero]
  rw [mul_comm w l]
  ring

/-- Passage from an explicit-formula estimate (5.28) on a finite family of
spectral parameters to its squared-transform row bound (5.29), with explicit
error amplification. Indices may have repeated spectral parameters. -/
theorem row_of_explicit_estimate {ι : Type*} (S : Finset ι) (z : ι → ℂ)
    {l w φ err : ℝ} (hl : 0 < l) (hw : 0 ≤ w) (hz : ∀ i ∈ S, 0 ≤ (z i).re)
    (hrow : (∑ i ∈ S, (∫ t in (0:ℝ)..w, Complex.exp (-z i*t) *
        (Real.sinh (l*(w-t)) : ℂ)).re) ≤
      φ/2 * Real.sinh (w*l) + (Real.cosh (w*l)-1)/l + err) :
    (∑ i ∈ S, ‖(transform ((l:ℂ)+z i) w)^2‖) ≤
      φ/2*((1-Real.exp (-2*w*l))/l) + ((1-Real.exp (-w*l))/l)^2 +
      2*Real.exp (-w*l)/l*err := by
  have hsum := Finset.sum_le_sum (fun i hi => half_plane hl hw (z i) (hz i hi))
  rw [← Finset.mul_sum] at hsum
  have h := hsum.trans hrow
  apply (mul_le_mul_iff_right₀ (show 0 < l*Real.exp (w*l)/2 by positivity)).mp
  apply h.trans_eq
  rw [Real.sinh_eq, Real.cosh_eq, show -2*w*l = -(w*l) + -(w*l) by ring,
    Real.exp_add, show -w*l = -(w*l) by ring, Real.exp_neg]
  field_simp [hl.ne', Real.exp_ne_zero]
  ring

end PintzLaplaceKernel

namespace PintzLaplaceKernel

/-- A frequency separation gives uniform decay of the truncated transform
for every nonnegative width on the closed right half-plane. -/
theorem transform_le_of_separation {z : ℂ} {w T : ℝ} (hw : 0 ≤ w) (hz : 0 ≤ z.re)
    (hT : 0 < T) (hsep : T ≤ |z.im|) : ‖transform z w‖ ≤ 2/T := by
  have hden := hsep.trans (Complex.abs_im_le_norm z)
  have harg : (-z*(w:ℂ)).re ≤ 0 := by
    simpa [Complex.mul_re] using (neg_nonpos.mpr (mul_nonneg hz hw) : -(z.re*w) ≤ 0)
  have hnum : ‖1 - Complex.exp (-z*(w:ℂ))‖ ≤ 2 := by
    have he : ‖Complex.exp (-z*(w:ℂ))‖ ≤ 1 := by
      rw [Complex.norm_exp]
      exact Real.exp_le_one_iff.mpr harg
    calc
      _ ≤ ‖(1:ℂ)‖ + ‖Complex.exp (-z*(w:ℂ))‖ := norm_sub_le _ _
      _ ≤ 2 := by simp only [norm_one]; linarith
  rw [transform, norm_div]
  exact div_le_div₀ (by norm_num) hnum hT hden

open Finset in
/-- The contribution of the far pairs to the majorant in (5.22), normalized
as in (5.27). The test for separation is on the scaled imaginary ordinates.
At separation sqrt(L) the coefficient is 4 exp(x A)/L. -/
theorem far_pair_sum_le {ι : Type*} (S : Finset ι) (R : ι → Finset ι)
    (a : ι → ℝ) (z : ι → ι → ℂ) {x A k r T : ℝ}
    (hx : 0 ≤ x) (hk : 0 ≤ k) (hr : 0 ≤ r) (hT : 0 < T)
    (ha : ∀ i ∈ S, 0 ≤ a i) (hsub : ∀ i ∈ S, R i ⊆ S)
    (hf : ∀ i ∈ S, ∀ j ∈ R i,
      0 ≤ (z i j).re ∧ (z i j).re ≤ A ∧ T ≤ |(z i j).im|) :
    (∑ i ∈ S, ∑ j ∈ R i, a i*a j * (Real.exp (x*(z i j).re) *
        ‖transform (z i j) k‖ * ‖transform (z i j) r‖)) ≤
      (∑ i ∈ S, a i)^2 * (4*Real.exp (x*A)/T^2) := by
  let C := 4*Real.exp (x*A)/T^2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hp (i : ι) (hi : i ∈ S) (j : ι) (hj : j ∈ R i) :
      Real.exp (x*(z i j).re) * ‖transform (z i j) k‖ * ‖transform (z i j) r‖ ≤ C := by
    obtain ⟨hz,hA,hsep⟩ := hf i hi j hj
    have he := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hA hx)
    have hb := mul_le_mul he (transform_le_of_separation hk hz hT hsep)
      (norm_nonneg _) (Real.exp_pos _).le
    exact (mul_le_mul hb (transform_le_of_separation hr hz hT hsep)
      (norm_nonneg _) (by positivity)).trans_eq (by dsimp [C]; ring)
  calc
    _ ≤ ∑ i ∈ S, ∑ j ∈ R i, a i*a j*C := by
      exact sum_le_sum fun i hi => sum_le_sum fun j hj =>
        mul_le_mul_of_nonneg_left (hp i hi j hj) (mul_nonneg (ha i hi) (ha j (hsub i hi hj)))
    _ ≤ ∑ i ∈ S, ∑ j ∈ S, a i*a j*C := by
      apply sum_le_sum
      intro i hi
      exact sum_le_sum_of_subset_of_nonneg (hsub i hi)
        (fun j hj _ => mul_nonneg (mul_nonneg (ha i hi) (ha j hj)) hC)
    _ = _ := by simp only [← sum_mul, ← mul_sum, sq, C]

end PintzLaplaceKernel
