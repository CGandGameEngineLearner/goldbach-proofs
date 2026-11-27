import PintzLaplaceKernel
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Conjectures.Goldbach.FareyCubeSqrtDensityRatio

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
