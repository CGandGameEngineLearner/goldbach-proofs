import Mathlib

/-! Re-submission: PR body records method, quantifiers and sources; fork renamed back to `goldbach-proofs` so the verification job can resolve the head repository. -/
/-!
# f176 -- the finite major-arc `sinc²` mass  (fork side)

Main result (frozen statement of `L-goldbach-finite-major-sinc-mass`, verbatim):

  `theorem ourproof64_finite_major_sinc_mass (h : ℝ) (hh : 0 < h) :
      let k := intervalIntegral (fun t : ℝ => Real.sinc (Real.pi * t) ^ 2) (-h) h volume
      0 ≤ k ∧ k ≤ 1 ∧ 1 - 2 / (9 * h) ≤ k`

The whole content is the exact total mass `∫_ℝ sinc (π t)^2 dt = 1` (nothing weaker suffices: the
upper bound `k ≤ 1` needs `total ≤ 1` and the lower bound `1 - 2/(9h) ≤ k` needs `total ≥ 1`,
since `1 - k = ∫_{|t| > h} sinc (π t)^2`).

Mathlib has no lemma for this mass, so we prove it here through the Fourier inversion formula
(`MeasureTheory.Integrable.fourierInv_fourier_eq`) applied to the hat function
`tri x = max 0 (1 - |x|)`, whose Fourier transform is computed by hand to be `sinc (π ·)^2`.
-/

noncomputable section

open MeasureTheory Real Filter
open scoped FourierTransform Topology

set_option maxHeartbeats 1000000

namespace GoldbachF176

/-! ## The hat function and its basic properties -/

/-- The hat (triangle) function `x ↦ max 0 (1 - |x|)`, viewed as a `ℂ`-valued function. -/
def tri (x : ℝ) : ℂ := ((max 0 (1 - |x|) : ℝ) : ℂ)

lemma tri_eq_of_abs_le {x : ℝ} (hx : |x| ≤ 1) : tri x = ((1 - |x| : ℝ) : ℂ) := by
  unfold tri
  rw [max_eq_right (by linarith)]

lemma tri_eq_zero_of_one_le_abs {x : ℝ} (hx : 1 ≤ |x|) : tri x = 0 := by
  unfold tri
  rw [max_eq_left (by linarith), Complex.ofReal_zero]

lemma continuous_tri : Continuous tri := by
  unfold tri
  fun_prop

lemma tri_neg (x : ℝ) : tri (-x) = tri x := by
  unfold tri
  simp only [abs_neg]

lemma tri_zero : tri 0 = 1 := by
  simp [tri]

lemma tri_eq_zero_of_notMem {x : ℝ} (hx : x ∉ Set.Ioc (-1 : ℝ) 1) : tri x = 0 := by
  apply tri_eq_zero_of_one_le_abs
  rw [Set.mem_Ioc, not_and_or, not_lt, not_le] at hx
  rcases hx with h | h
  · rw [abs_of_nonpos (by linarith)]; linarith
  · rw [abs_of_pos (by linarith)]; linarith

lemma integral_neg_one_one (g : ℝ → ℂ) (hg : Continuous g) :
    ∫ x in (-1 : ℝ)..1, g x = (∫ x in (0 : ℝ)..1, g (-x)) + ∫ x in (0 : ℝ)..1, g x := by
  have h1 : IntervalIntegrable g volume (-1 : ℝ) 0 := hg.intervalIntegrable _ _
  have h2 : IntervalIntegrable g volume (0 : ℝ) 1 := hg.intervalIntegrable _ _
  rw [← intervalIntegral.integral_add_adjacent_intervals h1 h2]
  congr 1
  have h := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := (1 : ℝ)) g
  simpa only [neg_zero] using h.symm

lemma integral_tri_eq_one : ∫ x, tri x = 1 := by
  have hzero : ∀ x ∉ Set.Ioc (-1 : ℝ) 1, tri x = 0 := fun x hx => tri_eq_zero_of_notMem hx
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero,
    ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  rw [integral_neg_one_one tri continuous_tri]
  have hsym : ∫ x in (0 : ℝ)..1, tri (-x) = ∫ x in (0 : ℝ)..1, tri x :=
    intervalIntegral.integral_congr (fun x _ => tri_neg x)
  rw [hsym, ← two_mul]
  have hone : ∫ x in (0 : ℝ)..1, tri x = ((1 / 2 : ℝ) : ℂ) := by
    have hpt : ∀ x ∈ Set.uIcc (0 : ℝ) 1, tri x = ((1 - x : ℝ) : ℂ) := by
      intro x hx
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
      rw [tri_eq_of_abs_le (by rw [abs_of_nonneg hx.1]; linarith [hx.2]),
        abs_of_nonneg hx.1]
    rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_ofReal]
    have hpoly : ∫ x in (0 : ℝ)..1, (1 - x) = 1 / 2 := by
      rw [intervalIntegral.integral_sub (μ := volume) (a := (0 : ℝ)) (b := 1)
        (f := fun _ : ℝ => (1 : ℝ)) (g := fun x : ℝ => x)
        (intervalIntegrable_const (c := (1 : ℝ)))
        (Continuous.intervalIntegrable continuous_id (0 : ℝ) 1)]
      simp only [intervalIntegral.integral_const, integral_id, smul_eq_mul]
      norm_num
    rw [hpoly]
  rw [hone, two_mul]
  norm_num

/-! ## `∫₀¹ (1 - x) cos (b x) dx = (1 - cos b) / b²` -/

lemma hasDerivAt_cos_prim_aux (b : ℝ) (hb : b ≠ 0) (x : ℝ) :
    HasDerivAt ((fun y : ℝ => (1 - y) * (Real.sin (b * y) / b))
        + fun y : ℝ => (1 - Real.cos (b * y)) / b ^ 2)
      ((-1) * (Real.sin (b * x) / b) + (1 - x) * Real.cos (b * x)
        + Real.sin (b * x) * b / b ^ 2) x := by
  have hinner : HasDerivAt (fun y : ℝ => b * y) b x := by
    simpa using (hasDerivAt_id x).const_mul b
  have hsin : HasDerivAt (fun y : ℝ => Real.sin (b * y) / b) (Real.cos (b * x)) x := by
    have h1 : HasDerivAt (fun y : ℝ => Real.sin (b * y)) (Real.cos (b * x) * b) x :=
      (Real.hasDerivAt_sin (b * x)).comp x hinner
    exact (h1.div_const b).congr_deriv (by field_simp)
  have hcos : HasDerivAt (fun y : ℝ => Real.cos (b * y)) (-Real.sin (b * x) * b) x :=
    (Real.hasDerivAt_cos (b * x)).comp x hinner
  have hsub : HasDerivAt (fun y : ℝ => 1 - y) (-1) x :=
    (hasDerivAt_id x).const_sub 1
  have hmul : HasDerivAt (fun y : ℝ => (1 - y) * (Real.sin (b * y) / b))
      ((-1) * (Real.sin (b * x) / b) + (1 - x) * Real.cos (b * x)) x := hsub.mul hsin
  have h2 : HasDerivAt (fun y : ℝ => (1 - Real.cos (b * y)) / b ^ 2)
      (Real.sin (b * x) * b / b ^ 2) x := by
    have h3 : HasDerivAt (fun y : ℝ => 1 - Real.cos (b * y)) (Real.sin (b * x) * b) x :=
      ((hasDerivAt_const (x := x) (1 : ℝ)).sub hcos).congr_deriv (by ring)
    exact h3.div_const (b ^ 2)
  exact hmul.add h2

lemma hasDerivAt_cos_prim (b : ℝ) (hb : b ≠ 0) (x : ℝ) :
    HasDerivAt ((fun y : ℝ => (1 - y) * (Real.sin (b * y) / b))
        + fun y : ℝ => (1 - Real.cos (b * y)) / b ^ 2)
      ((1 - x) * Real.cos (b * x)) x := by
  refine (hasDerivAt_cos_prim_aux b hb x).congr_deriv ?_
  field_simp
  ring

lemma integral_cos_mul (b : ℝ) (hb : b ≠ 0) :
    ∫ x in (0 : ℝ)..1, (1 - x) * Real.cos (b * x) = (1 - Real.cos b) / b ^ 2 := by
  have hcont : Continuous fun x : ℝ => (1 - x) * Real.cos (b * x) := by fun_prop
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := (fun y : ℝ => (1 - y) * (Real.sin (b * y) / b))
      + fun y : ℝ => (1 - Real.cos (b * y)) / b ^ 2)
    (f' := fun x : ℝ => (1 - x) * Real.cos (b * x))
    (fun x _ => hasDerivAt_cos_prim b hb x) (hcont.intervalIntegrable (0 : ℝ) 1)
  rw [h]
  simp only [Pi.add_apply, Real.sin_zero, Real.cos_zero, mul_zero, zero_div, sub_self,
    mul_one, zero_add, sub_zero]
  field_simp
  ring

/-! ## `∫₀¹ (1 - x) exp (d x) dx = (exp d - 1 - d) / d²` -/

lemma hasDerivAt_exp_prim_aux (d : ℂ) (x : ℝ) :
    HasDerivAt (fun u : ℝ => ((1 - u : ℝ) : ℂ) * Complex.exp (d * (u : ℂ)) / d
        + Complex.exp (d * (u : ℂ)) / d ^ 2)
      (((-1) * Complex.exp (d * (x : ℂ))
        + ((1 - x : ℝ) : ℂ) * (Complex.exp (d * (x : ℂ)) * d)) / d
        + Complex.exp (d * (x : ℂ)) * d / d ^ 2) x := by
  have hinner : HasDerivAt (fun u : ℝ => d * (u : ℂ)) d x := by
    simpa using (hasDerivAt_id (x := x) (𝕜 := ℝ)).ofReal_comp.const_mul d
  have hexp : HasDerivAt (fun u : ℝ => Complex.exp (d * (u : ℂ)))
      (Complex.exp (d * (x : ℂ)) * d) x := by
    have := (Complex.hasDerivAt_exp (d * (x : ℂ))).comp x hinner
    simpa [Function.comp_def] using this
  have hlin : HasDerivAt (fun u : ℝ => ((1 - u : ℝ) : ℂ)) (-1) x := by
    have := ((hasDerivAt_id (x := x) (𝕜 := ℝ)).const_sub 1).ofReal_comp
    simpa using this
  have hA : HasDerivAt (fun u : ℝ => ((1 - u : ℝ) : ℂ) * Complex.exp (d * (u : ℂ)))
      ((-1) * Complex.exp (d * (x : ℂ))
        + ((1 - x : ℝ) : ℂ) * (Complex.exp (d * (x : ℂ)) * d)) x := hlin.mul hexp
  exact (hA.div_const d).add (hexp.div_const (d ^ 2))

lemma hasDerivAt_exp_prim (d : ℂ) (hd : d ≠ 0) (x : ℝ) :
    HasDerivAt (fun u : ℝ => ((1 - u : ℝ) : ℂ) * Complex.exp (d * (u : ℂ)) / d
        + Complex.exp (d * (u : ℂ)) / d ^ 2)
      (((1 - x : ℝ) : ℂ) * Complex.exp (d * (x : ℂ))) x := by
  refine (hasDerivAt_exp_prim_aux d x).congr_deriv ?_
  field_simp
  ring

lemma integral_exp_mul_one_sub (d : ℂ) (hd : d ≠ 0) :
    ∫ u in (0 : ℝ)..1, ((1 - u : ℝ) : ℂ) * Complex.exp (d * (u : ℂ))
      = (Complex.exp d - 1 - d) / d ^ 2 := by
  have hcont : Continuous fun u : ℝ => ((1 - u : ℝ) : ℂ) * Complex.exp (d * (u : ℂ)) := by
    fun_prop
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun u : ℝ => ((1 - u : ℝ) : ℂ) * Complex.exp (d * (u : ℂ)) / d
      + Complex.exp (d * (u : ℂ)) / d ^ 2)
    (f' := fun u : ℝ => ((1 - u : ℝ) : ℂ) * Complex.exp (d * (u : ℂ)))
    (fun x _ => hasDerivAt_exp_prim d hd x) (hcont.intervalIntegrable (0 : ℝ) 1)
  rw [h]
  norm_num
  field_simp
  ring

/-! ## `exp (-2πiy·I) + exp (2πiy·I) = 2 cos (2πy)` -/

lemma exp_add_exp_neg_two_pi_I (y : ℝ) :
    Complex.exp (↑(-(2 * π * y)) * Complex.I) + Complex.exp (↑(2 * π * y) * Complex.I)
      = 2 * ↑(Real.cos (2 * π * y)) := by
  have hcos : (↑(Real.cos (2 * π * y)) : ℂ) = Complex.cos (↑(2 * π * y)) := Complex.ofReal_cos _
  have hneg : (↑(-(2 * π * y)) : ℂ) * Complex.I = -(↑(2 * π * y) * Complex.I) := by
    push_cast; ring
  have hdef : Complex.cos (↑(2 * π * y)) =
      (Complex.exp (↑(2 * π * y) * Complex.I)
        + Complex.exp (-(↑(2 * π * y)) * Complex.I)) / 2 := rfl
  rw [hcos, hdef, hneg]
  ring

/-! ## The Fourier transform of the hat function -/

/-- The integrand `exp (2πi x w) · tri x`. -/
def ep (w : ℝ) (x : ℝ) : ℂ := Complex.exp (↑(2 * π * x * w) * Complex.I) * tri x

/-- The integrand `exp (-2πi x w) · tri x`. -/
def em (w : ℝ) (x : ℝ) : ℂ := Complex.exp (↑(-2 * π * x * w) * Complex.I) * tri x

lemma em_cont (w : ℝ) : Continuous (em w) := by
  have h1 : Continuous fun x : ℝ => Complex.exp (↑(-2 * π * x * w) * Complex.I) := by fun_prop
  exact h1.mul continuous_tri

lemma ep_cont (w : ℝ) : Continuous (ep w) := by
  have h1 : Continuous fun x : ℝ => Complex.exp (↑(2 * π * x * w) * Complex.I) := by fun_prop
  exact h1.mul continuous_tri

lemma fourier_eq_em (w : ℝ) : 𝓕 tri w = ∫ x : ℝ, em w x := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp [em, smul_eq_mul]

lemma fourier_step2 (w : ℝ) : (∫ x : ℝ, em w x) = ∫ x in Set.Ioc (-1 : ℝ) 1, em w x := by
  have hzero : ∀ x ∉ Set.Ioc (-1 : ℝ) 1, em w x = 0 := by
    intro x hx
    simp [em, tri_eq_zero_of_notMem hx]
  exact (setIntegral_eq_integral_of_forall_compl_eq_zero hzero).symm

lemma fourier_step3 (w : ℝ) :
    (∫ x in Set.Ioc (-1 : ℝ) 1, em w x) = ∫ x in (-1 : ℝ)..1, em w x :=
  (intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)).symm

lemma fourier_step4 (w : ℝ) :
    (∫ x in (-1 : ℝ)..1, em w x)
      = (∫ x in (0 : ℝ)..1, em w (-x)) + ∫ x in (0 : ℝ)..1, em w x :=
  integral_neg_one_one _ (em_cont w)

lemma fourier_step5 (w : ℝ) : (∫ x in (0 : ℝ)..1, em w (-x)) = ∫ x in (0 : ℝ)..1, ep w x := by
  apply intervalIntegral.integral_congr
  intro x _
  simp only [em, ep, tri_neg]
  congr 2
  push_cast
  ring

lemma fourier_step6 (w : ℝ) :
    (∫ x in (0 : ℝ)..1, ep w x) + ∫ x in (0 : ℝ)..1, em w x
      = ∫ x in (0 : ℝ)..1, (ep w x + em w x) := by
  exact (intervalIntegral.integral_add ((ep_cont w).intervalIntegrable _ _)
    ((em_cont w).intervalIntegrable _ _)).symm

lemma fourier_step7 (w : ℝ) :
    (∫ x in (0 : ℝ)..1, (ep w x + em w x))
      = ∫ x in (0 : ℝ)..1, ((2 * ((1 - x) * Real.cos (2 * π * (x * w))) : ℝ) : ℂ) := by
  apply intervalIntegral.integral_congr
  intro x hx
  simp only [ep, em]
  have htri : tri x = ((1 - x : ℝ) : ℂ) := by
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
    rw [tri_eq_of_abs_le (by rw [abs_of_nonneg hx.1]; linarith [hx.2]), abs_of_nonneg hx.1]
  rw [htri,
    mul_comm (Complex.exp (↑(2 * π * x * w) * Complex.I)) (((1 - x : ℝ) : ℂ)),
    mul_comm (Complex.exp (↑(-2 * π * x * w) * Complex.I)) (((1 - x : ℝ) : ℂ))]
  have harg1 : (↑(2 * π * x * w) : ℂ) * Complex.I = ↑(2 * π * (x * w)) * Complex.I := by
    push_cast; ring
  have harg2 : (↑(-2 * π * x * w) : ℂ) * Complex.I = ↑(-(2 * π * (x * w))) * Complex.I := by
    push_cast; ring
  rw [harg1, harg2]
  have hkey : ((1 - x : ℝ) : ℂ) * Complex.exp (↑(2 * π * (x * w)) * Complex.I)
        + ((1 - x : ℝ) : ℂ) * Complex.exp (↑(-(2 * π * (x * w))) * Complex.I)
      = ((1 - x : ℝ) : ℂ) * (Complex.exp (↑(2 * π * (x * w)) * Complex.I)
          + Complex.exp (↑(-(2 * π * (x * w))) * Complex.I)) := by
    ring
  rw [hkey]
  rw [show Complex.exp (↑(2 * π * (x * w)) * Complex.I)
        + Complex.exp (↑(-(2 * π * (x * w))) * Complex.I)
      = 2 * ↑(Real.cos (2 * π * (x * w))) from by
    rw [add_comm]; exact exp_add_exp_neg_two_pi_I (x * w)]
  push_cast
  ring

lemma integral_two_one_sub_cos (w : ℝ) (hw : w ≠ 0) :
    ∫ x in (0 : ℝ)..1, 2 * ((1 - x) * Real.cos (2 * π * (x * w)))
      = 2 * ((1 - Real.cos (2 * π * w)) / (2 * π * w) ^ 2) := by
  have hb : (2 : ℝ) * π * w ≠ 0 := by
    have h2π : (2 : ℝ) * π ≠ 0 := by positivity
    exact mul_ne_zero h2π hw
  have hbase : ∫ x in (0 : ℝ)..1, (1 - x) * Real.cos ((2 * π * w) * x)
      = (1 - Real.cos (2 * π * w)) / (2 * π * w) ^ 2 := by
    have h := integral_cos_mul ((2 : ℝ) * π * w) hb
    rwa [show (2 : ℝ) * π * w = 2 * π * w by ring] at h
  rw [← hbase, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x _
  have harg : 2 * π * (x * w) = (2 * π * w) * x := by ring
  simp only [harg]

lemma fourier_tri_of_ne {w : ℝ} (hw : w ≠ 0) :
    𝓕 tri w = (((Real.sinc (π * w)) ^ 2 : ℝ) : ℂ) := by
  have hb : (2 : ℝ) * π * w ≠ 0 := by
    have h2π : (2 : ℝ) * π ≠ 0 := by positivity
    exact mul_ne_zero h2π hw
  have hpw : π * w ≠ 0 := mul_ne_zero Real.pi_ne_zero hw
  calc 𝓕 tri w = ∫ x : ℝ, em w x := fourier_eq_em w
    _ = ∫ x in Set.Ioc (-1 : ℝ) 1, em w x := fourier_step2 w
    _ = ∫ x in (-1 : ℝ)..1, em w x := fourier_step3 w
    _ = (∫ x in (0 : ℝ)..1, em w (-x)) + ∫ x in (0 : ℝ)..1, em w x := fourier_step4 w
    _ = (∫ x in (0 : ℝ)..1, ep w x) + ∫ x in (0 : ℝ)..1, em w x := by
        rw [fourier_step5 w]
    _ = ∫ x in (0 : ℝ)..1, (ep w x + em w x) := fourier_step6 w
    _ = ∫ x in (0 : ℝ)..1, ((2 * ((1 - x) * Real.cos (2 * π * (x * w))) : ℝ) : ℂ) :=
        fourier_step7 w
    _ = ((∫ x in (0 : ℝ)..1, 2 * ((1 - x) * Real.cos (2 * π * (x * w))) : ℝ) : ℂ) :=
        intervalIntegral.integral_ofReal
    _ = ((2 * ((1 - Real.cos (2 * π * w)) / (2 * π * w) ^ 2) : ℝ) : ℂ) := by
        rw [integral_two_one_sub_cos w hw]
    _ = (((Real.sinc (π * w)) ^ 2 : ℝ) : ℂ) := by
        congr 1
        have hcos : Real.cos (2 * π * w) = 1 - 2 * Real.sin (π * w) ^ 2 := by
          have h1 := Real.cos_two_mul (π * w)
          have h2 := Real.sin_sq (π * w)
          have e : 2 * π * w = 2 * (π * w) := by ring
          rw [e, h1]; linarith
        rw [Real.sinc_of_ne_zero hpw, hcos]
        field_simp
        ring

lemma fourier_tri_zero : 𝓕 tri 0 = (1 : ℂ) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  have hpt : ∀ x : ℝ, Complex.exp (↑(-2 * π * x * 0) * Complex.I) • tri x = tri x := by
    intro x; simp
  simp_rw [hpt]
  exact integral_tri_eq_one

lemma fourier_tri (w : ℝ) : 𝓕 tri w = (((Real.sinc (π * w)) ^ 2 : ℝ) : ℂ) := by
  rcases eq_or_ne w 0 with h | h
  · rw [h, fourier_tri_zero]
    norm_num [Real.sinc_zero]
  · exact fourier_tri_of_ne h

/-! ## The total mass `∫_ℝ sinc (π t)^2 dt = 1` -/

lemma integrable_tri : Integrable tri := by
  have hIcc : IntegrableOn tri (Set.Icc (-1 : ℝ) 1) :=
    ContinuousOn.integrableOn_compact isCompact_Icc continuous_tri.continuousOn
  refine hIcc.integrable_of_forall_notMem_eq_zero ?_
  intro x hx
  apply tri_eq_zero_of_one_le_abs
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
  rcases hx with h | h
  · rw [abs_of_nonpos (by linarith)]; linarith
  · rw [abs_of_pos (by linarith)]; linarith

/-! ## Integrability of `sinc (π ·)^2` and the model tails -/

lemma continuous_sinc_sq_pi : Continuous fun x : ℝ => (Real.sinc (π * x)) ^ 2 :=
  (Real.continuous_sinc.comp (by fun_prop)).pow 2

lemma abs_sinc_le_inv_abs {x : ℝ} (hx : x ≠ 0) : |Real.sinc x| ≤ 1 / |x| := by
  have hxpos : (0 : ℝ) < |x| := abs_pos.mpr hx
  have hsin : |Real.sin x| ≤ 1 := Real.abs_sin_le_one x
  rw [Real.sinc_of_ne_zero hx, abs_div]
  gcongr

lemma sinc_sq_pi_le {x : ℝ} (hx : x ≠ 0) :
    (Real.sinc (π * x)) ^ 2 ≤ 1 / (π ^ 2 * x ^ 2) := by
  have hπx : π * x ≠ 0 := mul_ne_zero Real.pi_ne_zero hx
  have h1 : |Real.sinc (π * x)| ≤ 1 / (π * |x|) := by
    have h := abs_sinc_le_inv_abs hπx
    rwa [abs_mul, abs_of_pos Real.pi_pos] at h
  have hsq : (1 / (π * |x|)) ^ 2 = 1 / (π ^ 2 * x ^ 2) := by
    rw [div_pow, mul_pow, sq_abs]
    ring
  have h2 : (Real.sinc (π * x)) ^ 2 = |Real.sinc (π * x)| ^ 2 := (sq_abs _).symm
  rw [h2, ← hsq]
  have hnn : (0 : ℝ) ≤ 1 / (π * |x|) := by positivity
  nlinarith [h1, abs_nonneg (Real.sinc (π * x))]

lemma hasDerivAt_inv_prim {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun y : ℝ => -((π ^ 2 * y)⁻¹)) (1 / (π ^ 2 * x ^ 2)) x := by
  have h1 : HasDerivAt (fun y : ℝ => π ^ 2 * y) (π ^ 2) x := by
    simpa using (hasDerivAt_id x).const_mul (π ^ 2)
  have h2 := (h1.inv (by positivity : π ^ 2 * x ≠ 0)).neg
  refine h2.congr_deriv ?_
  field_simp

lemma tendsto_inv_prim : Tendsto (fun y : ℝ => -((π ^ 2 * y)⁻¹)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun y : ℝ => π ^ 2 * y) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos (by positivity : (0 : ℝ) < π ^ 2)).mpr tendsto_id
  have h2 : Tendsto (fun y : ℝ => (π ^ 2 * y)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp h1
  simpa using h2.neg

lemma tendsto_inv_prim_atBot : Tendsto (fun y : ℝ => -((π ^ 2 * y)⁻¹)) atBot (𝓝 0) := by
  have h1 : Tendsto (fun y : ℝ => π ^ 2 * y) atBot atBot :=
    (tendsto_const_mul_atBot_of_pos (by positivity : (0 : ℝ) < π ^ 2)).mpr tendsto_id
  have h2 : Tendsto (fun y : ℝ => (π ^ 2 * y)⁻¹) atBot (𝓝 0) :=
    tendsto_inv_atBot_zero.comp h1
  simpa using h2.neg

lemma integrableOn_inv_sq_Ioi (a : ℝ) (ha : 0 < a) :
    IntegrableOn (fun x : ℝ => 1 / (π ^ 2 * x ^ 2)) (Set.Ioi a) :=
  integrableOn_Ioi_deriv_of_nonneg' (a := a) (g := fun y : ℝ => -((π ^ 2 * y)⁻¹))
    (g' := fun x : ℝ => 1 / (π ^ 2 * x ^ 2)) (l := 0)
    (fun x hx => hasDerivAt_inv_prim (by linarith [hx.out] : x ≠ 0))
    (fun x _ => by positivity) tendsto_inv_prim

lemma integrableOn_inv_sq_Iic (h : ℝ) (hh : 0 < h) :
    IntegrableOn (fun x : ℝ => 1 / (π ^ 2 * x ^ 2)) (Set.Iic (-h)) := by
  have h' : IntegrableOn (fun x : ℝ => 1 / (π ^ 2 * x ^ 2)) (Set.Iio (-h)) := by
    have hbase := (integrableOn_inv_sq_Ioi h hh).comp_neg
    rw [Set.neg_Ioi] at hbase
    exact hbase.congr (Filter.Eventually.of_forall fun x => by
      change 1 / (π ^ 2 * (-x) ^ 2) = 1 / (π ^ 2 * x ^ 2)
      rw [neg_sq])
  have hsingle : IntegrableOn (fun x : ℝ => 1 / (π ^ 2 * x ^ 2)) ({-h} : Set ℝ) :=
    integrableOn_singleton (f := fun x : ℝ => 1 / (π ^ 2 * x ^ 2)) (x := -h) (by finiteness) (by simp)
  have hsets : Set.Iic (-h) = Set.Iio (-h) ∪ ({-h} : Set ℝ) := by
    ext x
    simp only [Set.mem_Iic, Set.mem_union, Set.mem_Iio, Set.mem_singleton_iff]
    constructor
    · intro hx
      rcases lt_or_eq_of_le hx with hlt | heq
      · exact Or.inl hlt
      · exact Or.inr heq
    · rintro (hlt | heq)
      · linarith
      · linarith
  rw [hsets]
  exact h'.union hsingle

lemma integrable_sinc_sq_pi : Integrable fun x : ℝ => (Real.sinc (π * x)) ^ 2 := by
  have hIcc : IntegrableOn (fun x : ℝ => (Real.sinc (π * x)) ^ 2) (Set.Icc (-1 : ℝ) 1) :=
    ContinuousOn.integrableOn_compact isCompact_Icc continuous_sinc_sq_pi.continuousOn
  have hIoi : IntegrableOn (fun x : ℝ => (Real.sinc (π * x)) ^ 2) (Set.Ioi 1) := by
    refine (integrableOn_inv_sq_Ioi 1 (by norm_num)).mono' ?_ ?_
    · exact continuous_sinc_sq_pi.aestronglyMeasurable.restrict
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      refine sinc_sq_pi_le ?_
      simp only [Set.mem_Ioi] at hx
      intro hx0
      rw [hx0] at hx
      linarith
  have hev : ∀ x : ℝ, (Real.sinc (π * (-x))) ^ 2 = (Real.sinc (π * x)) ^ 2 := by
    intro x
    rw [show π * -x = -(π * x) by ring, Real.sinc_neg]
  have hIic : IntegrableOn (fun x : ℝ => (Real.sinc (π * x)) ^ 2) (Set.Iio (-1)) := by
    have h := hIoi.comp_neg
    rw [Set.neg_Ioi] at h
    exact h.congr (Filter.Eventually.of_forall fun x => hev x)
  have hbig : IntegrableOn (fun x : ℝ => (Real.sinc (π * x)) ^ 2)
      (((Set.Iio (-1 : ℝ)) ∪ Set.Icc (-1 : ℝ) 1) ∪ Set.Ioi 1) := (hIic.union hIcc).union hIoi
  have hset : (((Set.Iio (-1 : ℝ)) ∪ Set.Icc (-1 : ℝ) 1) ∪ Set.Ioi 1) = Set.univ := by
    ext x
    simp only [Set.mem_union, Set.mem_Icc, Set.mem_Ioi, Set.mem_Iio, Set.mem_univ, iff_true]
    by_cases hx : x < -1
    · exact Or.inl (Or.inl hx)
    · simp only [not_lt] at hx
      by_cases hx' : x ≤ 1
      · exact Or.inl (Or.inr ⟨hx, hx'⟩)
      · simp only [not_le] at hx'
        exact Or.inr hx'
  exact integrableOn_univ.mp (hset ▸ hbig)

lemma integral_complex_sinc_sq : ∫ x : ℝ, (((Real.sinc (π * x)) ^ 2 : ℝ) : ℂ) = 1 := by
  have h'f : Integrable (𝓕 tri) := by
    have hreal : Integrable fun x : ℝ => (Real.sinc (π * x)) ^ 2 := integrable_sinc_sq_pi
    have hcompl : Integrable fun x : ℝ => (((Real.sinc (π * x)) ^ 2 : ℝ) : ℂ) := by
      refine hreal.mono' ?_ ?_
      · exact (Complex.continuous_ofReal.comp continuous_sinc_sq_pi).aestronglyMeasurable
      · filter_upwards with x
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hcompl.congr (Filter.Eventually.of_forall fun x => (fourier_tri x).symm)
  have hinv := (integrable_tri.fourierInv_fourier_eq h'f
    (continuous_tri.continuousAt (x := 0)))
  have h1 : ∫ v, 𝓕 tri v = tri 0 := by
    rw [← hinv, Real.fourierInv_eq]
    simp
  simp_rw [fourier_tri] at h1
  rw [tri_zero] at h1
  exact h1

lemma integral_sinc_sq_pi : ∫ x : ℝ, (Real.sinc (π * x)) ^ 2 = 1 := by
  have h1 : Complex.ofReal (∫ x : ℝ, (Real.sinc (π * x)) ^ 2) = 1 :=
    (integral_ofReal (f := fun x : ℝ => (Real.sinc (π * x)) ^ 2)).symm.trans
      integral_complex_sinc_sq
  exact Complex.ofReal_inj.mp h1

end GoldbachF176

section Main

open GoldbachF176

/-- The frozen statement of `L-goldbach-finite-major-sinc-mass`, verbatim. -/
theorem ourproof64_finite_major_sinc_mass (h : ℝ) (hh : 0 < h) :
    let k := intervalIntegral (fun t : ℝ => Real.sinc (Real.pi * t) ^ 2) (-h) h MeasureTheory.volume
    0 ≤ k ∧ k ≤ 1 ∧ 1 - 2 / (9 * h) ≤ k := by
  have hhle : (0 : ℝ) < h := hh
  have hmass : ∫ x : ℝ, (Real.sinc (π * x)) ^ 2 = 1 := integral_sinc_sq_pi
  have hfi : Integrable fun x : ℝ => (Real.sinc (π * x)) ^ 2 := integrable_sinc_sq_pi
  have hIoc : ∫ x in (-h)..h, (Real.sinc (π * x)) ^ 2
      = ∫ x in Set.Ioc (-h) h, (Real.sinc (π * x)) ^ 2 :=
    intervalIntegral.integral_of_le (by linarith)
  -- the total mass splits into the window plus its complement
  have hcompl : (∫ x in Set.Ioc (-h) h, (Real.sinc (π * x)) ^ 2)
      + ∫ x in (Set.Ioc (-h) h)ᶜ, (Real.sinc (π * x)) ^ 2 = 1 := by
    rw [integral_add_compl measurableSet_Ioc hfi, hmass]
  -- the model tail `∫ 1/(π²x²)`
  have hIoiVal : ∫ x in Set.Ioi h, (1 : ℝ) / (π ^ 2 * x ^ 2) = 1 / (π ^ 2 * h) := by
    have := integral_Ioi_of_hasDerivAt_of_nonneg' (a := h) (g := fun y : ℝ => -((π ^ 2 * y)⁻¹))
      (g' := fun x : ℝ => 1 / (π ^ 2 * x ^ 2)) (l := 0)
      (fun x hx => hasDerivAt_inv_prim (by linarith [hx.out] : x ≠ 0))
      (fun x _ => by positivity) tendsto_inv_prim
    rw [this]
    field_simp
    ring
  have hIicVal : ∫ x in Set.Iic (-h), (1 : ℝ) / (π ^ 2 * x ^ 2) = 1 / (π ^ 2 * h) := by
    have := integral_Iic_of_hasDerivAt_of_tendsto' (a := -h)
      (f := fun y : ℝ => -((π ^ 2 * y)⁻¹))
      (f' := fun x : ℝ => 1 / (π ^ 2 * x ^ 2)) (m := 0)
      (fun x hx => hasDerivAt_inv_prim (by linarith [hx.out] : x ≠ 0))
      (integrableOn_inv_sq_Iic h hh) tendsto_inv_prim_atBot
    rw [this]
    field_simp
    ring
  have hIntIoi : IntegrableOn (fun x : ℝ => (1 : ℝ) / (π ^ 2 * x ^ 2)) (Set.Ioi h) :=
    integrableOn_inv_sq_Ioi h hh
  have hIntIic : IntegrableOn (fun x : ℝ => (1 : ℝ) / (π ^ 2 * x ^ 2)) (Set.Iic (-h)) :=
    integrableOn_inv_sq_Iic h hh
  have hcomplSet : (Set.Ioc (-h) h)ᶜ = Set.Iic (-h) ∪ Set.Ioi h := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_Ioc, Set.mem_union, Set.mem_Iic, Set.mem_Ioi,
      not_and_or, not_lt, not_le]
  have hdisj : Disjoint (Set.Iic (-h)) (Set.Ioi h) := by
    rw [Set.disjoint_left]
    intro x hx1 hx2
    simp only [Set.mem_Iic] at hx1
    simp only [Set.mem_Ioi] at hx2
    linarith
  have hIntTail : IntegrableOn (fun x : ℝ => (Real.sinc (π * x)) ^ 2) (Set.Iic (-h) ∪ Set.Ioi h) :=
    hfi.integrableOn.union hfi.integrableOn
  have hbound : ∫ x in (Set.Ioc (-h) h)ᶜ, (Real.sinc (π * x)) ^ 2 ≤ 2 / (π ^ 2 * h) := by
    rw [hcomplSet]
    calc ∫ x in Set.Iic (-h) ∪ Set.Ioi h, (Real.sinc (π * x)) ^ 2
        ≤ ∫ x in Set.Iic (-h) ∪ Set.Ioi h, (1 : ℝ) / (π ^ 2 * x ^ 2) := by
          refine setIntegral_mono_on hIntTail (hIntIic.union hIntIoi) ?_ ?_
          · exact measurableSet_Iic.union measurableSet_Ioi
          · intro x hx
            have hx0 : x ≠ 0 := by
              rcases hx with hx | hx
              · simp only [Set.mem_Iic] at hx; linarith
              · simp only [Set.mem_Ioi] at hx; linarith
            exact sinc_sq_pi_le hx0
      _ = 2 / (π ^ 2 * h) := by
          rw [setIntegral_union hdisj measurableSet_Ioi hIntIic hIntIoi, hIoiVal, hIicVal]
          ring
  have hconst : 2 / (π ^ 2 * h) ≤ 2 / (9 * h) := by
    have hπ2 : (9 : ℝ) < π ^ 2 := by nlinarith [Real.pi_gt_three]
    gcongr
  refine ⟨?_, ?_, ?_⟩
  · exact intervalIntegral.integral_nonneg (by linarith) (fun u _ => by positivity)
  · rw [hIoc]
    calc ∫ x in Set.Ioc (-h) h, (Real.sinc (π * x)) ^ 2
        ≤ ∫ x : ℝ, (Real.sinc (π * x)) ^ 2 :=
          setIntegral_le_integral hfi (Filter.Eventually.of_forall fun x => by positivity)
      _ = 1 := hmass
  · have hk : 1 - ∫ x in Set.Ioc (-h) h, (Real.sinc (π * x)) ^ 2 ≤ 2 / (9 * h) := by
      have := hbound
      linarith
    rw [hIoc]
    linarith

end Main
/-! ## 冻结声明（研究台 `L-goldbach-finite-major-sinc-mass`）

以模块全名声明，形状与同批已接受文件（如 `FareyInverseFullWeight.lean`）一致。 -/

theorem Conjectures.Goldbach.FiniteMajorSincMass (h : ℝ) (hh : 0 < h) :
    let k := intervalIntegral (fun t : ℝ => Real.sinc (Real.pi * t) ^ 2) (-h) h MeasureTheory.volume
    0 ≤ k ∧ k ≤ 1 ∧ 1 - 2 / (9 * h) ≤ k :=
  ourproof64_finite_major_sinc_mass h hh


