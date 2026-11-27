import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Conjectures.Goldbach.FareyCubeSqrtDensityRatio

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

/-!
# The prime sum in Pintz's explicit formula

A bounded remainder in the first Mertens estimate transfers through the
compactly supported hyperbolic-sine weight with a loss of at most its value
at zero times the remainder. We keep the dependence on the scale explicit.
-/
open Real Finset MeasureTheory

namespace PintzPrimeSum

noncomputable def weight (l w L x : ℝ) : ℝ := Real.sinh (l*(w - Real.log x/L))

/-- Abel summation on [1, exp(Lw)]. A one-sided bound on the cumulative
coefficients suffices, including when the upper endpoint is an integer. -/
theorem weighted_sum_le (c : ℕ → ℝ) (hc : c 0 = 0) {C l w L : ℝ}
    (hl : 0 < l) (hw : 0 ≤ w) (hL : 0 < L)
    (hA : ∀ x : ℝ, 1 ≤ x → ∑ k ∈ Icc 0 ⌊x⌋₊, c k ≤ Real.log x+C) :
    ∑ n ∈ Icc 0 ⌊Real.exp (L*w)⌋₊, weight l w L n * c n ≤
      L/l * (Real.cosh (l*w)-1) + C*Real.sinh (l*w) := by
  let b := Real.exp (L*w)
  let f := weight l w L
  let v := fun x : ℝ => l*(w - Real.log x/L)
  let g := fun x : ℝ => l*Real.cosh (v x)/(L*x)
  let S := fun x : ℝ => ∑ k ∈ Icc 0 ⌊x⌋₊, c k
  have hb : 1 ≤ b := Real.one_le_exp (mul_nonneg hL.le hw)
  have hpos (x : ℝ) (hx : x ∈ Set.Icc 1 b) : 0 < x := zero_lt_one.trans_le hx.1
  have hv (x : ℝ) (hx : x ∈ Set.Icc 1 b) : HasDerivAt v (-l/(L*x)) x := by
    have d := (((Real.hasDerivAt_log (hpos x hx).ne').div_const L).const_sub w).const_mul l
    convert d using 1
    field_simp
  have hf (x : ℝ) (hx : x ∈ Set.Icc 1 b) : HasDerivAt f (-g x) x := by
    change HasDerivAt (fun t => Real.sinh (v t)) (-g x) x
    convert (hv x hx).sinh using 1
    unfold g
    ring
  have cg : ContinuousOn g (Set.Icc 1 b) := by
    dsimp [g,v]
    fun_prop (disch := intros; first | positivity | apply (hpos _ ‹_›).ne' | exact hL.ne' |
      apply mul_ne_zero hL.ne' (hpos _ ‹_›).ne')
  have gi : IntegrableOn g (Set.Icc 1 b) volume := cg.integrableOn_Icc
  have df : Set.EqOn (deriv f) (fun t => -g t) (Set.Icc 1 b) := fun t ht => (hf t ht).deriv
  have di : IntegrableOn (deriv f) (Set.Icc 1 b) :=
    gi.neg.congr_fun df.symm measurableSet_Icc
  have abel := sum_mul_eq_sub_integral_mul₀ c hc b (fun x hx => (hf x hx).differentiableAt) di
  have fb : f b = 0 := by simp [f, weight, b, Real.log_exp, hL.ne']
  have f1 : f 1 = Real.sinh (l*w) := by simp [f, weight]
  rw [fb, zero_mul, zero_sub] at abel
  have hreplace : (∫ t in Set.Ioc 1 b, deriv f t * S t) = -(∫ t in Set.Ioc 1 b, g t*S t) := by
    rw [← integral_neg]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    change deriv f t * S t = -(g t * S t)
    rw [df (Set.Ioc_subset_Icc_self ht)]
    ring
  change (∑ n ∈ Icc 0 ⌊b⌋₊, f n * c n) = -(∫ t in Set.Ioc 1 b, deriv f t * S t) at abel
  rw [hreplace, neg_neg] at abel
  let P := fun t : ℝ => -(Real.log t + C)*f t - L/l*Real.cosh (v t)
  have hP (x : ℝ) (hx : x ∈ Set.Icc 1 b) :
      HasDerivAt P (g x*(Real.log x + C)) x := by
    have hlog := (Real.hasDerivAt_log (hpos x hx).ne').add_const C
    have d := (hlog.neg.mul (hf x hx)).sub (((hv x hx).cosh).const_mul (L/l))
    convert d using 1
    dsimp [f, weight, g, v]
    field_simp
    ring
  have cu : ContinuousOn (fun x => g x*(Real.log x+C)) (Set.Icc 1 b) :=
    cg.mul ((Real.continuousOn_log.mono (fun x hx => (hpos x hx).ne')).add continuousOn_const)
  have iu : IntegrableOn (fun x => g x*(Real.log x+C)) (Set.Icc 1 b) volume := cu.integrableOn_Icc
  have iS : IntegrableOn (fun x => g x*S x) (Set.Icc 1 b) :=
    integrableOn_mul_sum_Icc c (by norm_num) gi
  have intP := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 1) (b := b)
    (fun x hx => hP x (by simpa [Set.uIcc_of_le hb] using hx))
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hb).2 iu)
  rw [intervalIntegral.integral_of_le hb] at intP
  change ∑ n ∈ Icc 0 ⌊b⌋₊, f n * c n ≤ _
  rw [abel]
  calc
    _ ≤ ∫ x in Set.Ioc 1 b, g x * (Real.log x+C) := by
      apply setIntegral_mono_on (iS.mono_set Set.Ioc_subset_Icc_self)
        (iu.mono_set Set.Ioc_subset_Icc_self) measurableSet_Ioc
      intro x hx
      have hx' := hpos x (Set.Ioc_subset_Icc_self hx)
      exact mul_le_mul_of_nonneg_left (hA x hx.1.le) (by dsimp [g]; positivity)
    _ = _ := by
      rw [intP]
      dsimp only [P]
      rw [fb, f1]
      simp [v, b, hL.ne']
      ring

/-- The effective unconditional Mertens constant already available in the
Goldbach repository. -/
private theorem cumulative (x : ℝ) (hx : 1 ≤ x) :
    ∑ n ∈ Icc 0 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n / n ≤ Real.log x + (Real.log 4+4) := by
  have h := WeightedTorusJets.Mertens.E₁Λ.le hx
  unfold WeightedTorusJets.Mertens.E₁Λ at h
  rw [Icc_eq_cons_Ioc (Nat.zero_le _), sum_cons]
  simpa only [Nat.cast_zero, div_zero, zero_add] using (sub_le_iff_le_add'.mp h)

noncomputable def twistedSum {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ) (l w L : ℝ) : ℂ :=
  ∑ n ∈ Icc 0 ⌊Real.exp (L*w)⌋₊,
    (weight l w L n * ArithmeticFunction.vonMangoldt n : ℝ) * (χ (n : ZMod q) / (n : ℂ)^s)

/-- The modulus of the entire twisted prime-power sum on Re(s)=1, after
division by L, is bounded by the zero-frequency integral plus the explicit
Mertens error. Uniform in the conductor, the character and Im(s). -/
theorem character_prime_sum {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ) (hs : s.re = 1)
    {l w L : ℝ} (hl : 0 < l) (hw : 0 ≤ w) (hL : 0 < L) :
    ‖twistedSum χ s l w L‖ / L ≤
      (Real.cosh (l*w)-1)/l + (Real.log 4 + 4)/L * Real.sinh (l*w) := by
  let I := Icc 0 ⌊Real.exp (L*w)⌋₊
  let c := fun n : ℕ => ArithmeticFunction.vonMangoldt n / (n:ℝ)
  let term := fun n : ℕ => ((weight l w L n * ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
    (χ (n : ZMod q) / (n : ℂ)^s)
  have hterm (n : ℕ) (hn : n ∈ I) : ‖term n‖ ≤ weight l w L n * c n := by
    rcases Nat.eq_zero_or_pos n with rfl | hnpos
    · simp [term, c]
    have hnx : (n:ℝ) ≤ Real.exp (L*w) :=
      (Nat.le_floor_iff (Real.exp_pos _).le).mp (mem_Icc.mp hn).2
    have hlog := Real.log_le_log (Nat.cast_pos.mpr hnpos) hnx
    rw [Real.log_exp] at hlog
    have hwgt : 0 ≤ weight l w L n := Real.sinh_nonneg_iff.mpr
      (mul_nonneg hl.le (sub_nonneg.mpr ((div_le_iff₀ hL).2 (by linarith))))
    have hΛ := ArithmeticFunction.vonMangoldt_nonneg (n := n)
    dsimp [term, c]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hwgt hΛ),
      norm_div, Complex.norm_natCast_cpow_of_pos hnpos, hs, Real.rpow_one]
    calc
      _ ≤ weight l w L n * ArithmeticFunction.vonMangoldt n * (1/(n:ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hwgt hΛ)
        exact div_le_div_of_nonneg_right (χ.norm_le_one _) (Nat.cast_nonneg _)
      _ = _ := by ring
  have hmain := weighted_sum_le c (by simp [c]) hl hw hL cumulative
  change ‖∑ n ∈ I, term n‖ / L ≤ _
  apply (div_le_iff₀ hL).2
  calc
    _ ≤ ∑ n ∈ I, ‖term n‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ I, weight l w L n * c n := sum_le_sum hterm
    _ ≤ _ := hmain.trans_eq (by field_simp)

/-- After the normalization in (5.26) the prime-sum contribution to the row
error is at most 2 C w / L, uniformly even as the positive zero distance l tends
to zero. -/
theorem normalized_error {C l w L : ℝ} (hC : 0 ≤ C) (hl : 0 < l) (hL : 0 < L) :
    (2*Real.exp (-(w*l))/l) * (C/L*Real.sinh (w*l)) ≤ 2*C*w/L := by
  have hid : 2*Real.exp (-(w*l))*Real.sinh (w*l) = 1-Real.exp (-(2*w*l)) := by
    rw [Real.sinh_eq, show -(2*w*l) = -(w*l) + -(w*l) by ring, Real.exp_add, Real.exp_neg]
    field_simp [Real.exp_ne_zero]
  have h := Real.one_sub_le_exp_neg (2*w*l)
  have hb : 2*Real.exp (-(w*l))*Real.sinh (w*l) ≤ 2*w*l := by linarith only [hid,h]
  have := mul_le_mul_of_nonneg_left hb hC
  calc
    _ = C*(2*Real.exp (-(w*l))*Real.sinh (w*l))/(L*l) := by ring
    _ ≤ C*(2*w*l)/(L*l) := div_le_div_of_nonneg_right this (mul_nonneg hL.le hl.le)
    _ = _ := by field_simp

/-- What remains of (5.28): the explicit-formula estimate against the signed
prime sum. From it, the squared-transform row bound follows with explicit
loss and no auxiliary prime-distribution hypothesis. -/
theorem row_of_signed_formula {ι : Type*} (S : Finset ι) (z : ι → ℂ)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ) (hs : s.re = 1)
    {l w L φ δ : ℝ} (hl : 0 < l) (hw : 0 ≤ w) (hL : 0 < L) (hδ : 0 ≤ δ)
    (hz : ∀ i ∈ S, 0 ≤ (z i).re)
    (hformula : (∑ i ∈ S, (∫ t in (0:ℝ)..w, Complex.exp (-z i*t) *
      (Real.sinh (l*(w-t)) : ℂ)).re) ≤ (φ/2+δ)*Real.sinh (w*l) -
      (twistedSum χ s l w L).re / L) :
    (∑ i ∈ S, ‖(PintzLaplaceKernel.transform ((l:ℂ)+z i) w)^2‖) ≤
      φ/2*((1-Real.exp (-2*w*l))/l) + ((1-Real.exp (-w*l))/l)^2 +
      2*w*(δ + (Real.log 4+4)/L) := by
  have hnorm := character_prime_sum χ s hs hl hw hL
  have hneg : -(twistedSum χ s l w L).re / L ≤ ‖twistedSum χ s l w L‖ / L :=
    div_le_div_of_nonneg_right ((neg_le_abs _).trans (Complex.abs_re_le_norm _)) hL.le
  let e := δ + (Real.log 4+4)/L
  have he : 0 ≤ e := by dsimp [e]; positivity
  have hr := PintzLaplaceKernel.row_of_explicit_estimate S z hl hw hz
    (φ := φ) (err := e*Real.sinh (w*l)) (by
      apply hformula.trans
      have hb := hneg.trans hnorm
      rw [mul_comm l w] at hb
      dsimp [e]
      calc
        _ = (φ/2+δ)*Real.sinh (w*l) + (-(twistedSum χ s l w L).re / L) := by ring
        _ ≤ _ := (add_le_add (le_refl ((φ/2+δ)*Real.sinh (w*l))) hb).trans_eq (by ring))
  have herr := normalized_error (C := e) (L := 1) (w := w) he hl (by norm_num)
  apply hr.trans
  apply add_le_add le_rfl
  change 2*Real.exp (-w*l)/l * (e*Real.sinh (w*l)) ≤ 2*w*e
  rw [mul_right_comm 2 w e, neg_mul]
  simpa only [div_one] using herr

end PintzPrimeSum
