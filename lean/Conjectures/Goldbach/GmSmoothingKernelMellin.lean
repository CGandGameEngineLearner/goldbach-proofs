import Mathlib

open MeasureTheory Set Filter
open scoped Topology

namespace Conjectures.Goldbach.GmSmoothingKernelMellin_aux

lemma hasDerivAt_ofReal_coe (v : ℝ) : HasDerivAt (fun v : ℝ => (v : ℂ)) 1 v :=
  Complex.ofRealCLM.hasDerivAt

lemma hasDerivAt_exp_mul (s : ℂ) (v : ℝ) :
    HasDerivAt (fun v : ℝ => Complex.exp (s * (v : ℂ))) (s * Complex.exp (s * (v : ℂ))) v := by
  have h0 := (hasDerivAt_id' v).smul_const s
  have h1 := h0.cexp
  simpa [smul_eq_mul, mul_comm] using h1

/-- Explicit integral of `(a + b v) e^{s v}` over a real interval. -/
lemma integral_lin_exp (a b : ℂ) (s : ℂ) (hs : s ≠ 0) (lo hi : ℝ) :
    ∫ v in lo..hi, (a + b * (v : ℂ)) * Complex.exp (s * (v : ℂ)) =
      Complex.exp (s * (hi : ℂ)) * ((a + b * (hi : ℂ)) / s - b / s ^ 2) -
      Complex.exp (s * (lo : ℂ)) * ((a + b * (lo : ℂ)) / s - b / s ^ 2) := by
  have hE := fun v => hasDerivAt_exp_mul s v
  have hA : ∀ v : ℝ, HasDerivAt (fun v : ℝ => (a + b * (v : ℂ))) (b * 1) v := by
    intro v
    simpa using ((hasDerivAt_ofReal_coe v).const_mul b).const_add a
  have hF : ∀ v ∈ uIcc lo hi, HasDerivAt
      (fun v : ℝ => Complex.exp (s * (v : ℂ)) * ((a + b * (v : ℂ)) / s - b / s ^ 2))
      ((a + b * (v : ℂ)) * Complex.exp (s * (v : ℂ))) v := by
    intro v _
    have h := (hE v).mul ((hA v).div_const s |>.sub_const (b / s ^ 2))
    convert h using 1
    field_simp
    ring
  have hint : IntervalIntegrable (fun v : ℝ => (a + b * (v : ℂ)) * Complex.exp (s * (v : ℂ)))
      volume lo hi := by
    refine Continuous.intervalIntegrable ?_ _ _
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF hint]

lemma integral_lin (a b lo hi : ℝ) :
    ∫ v in lo..hi, (a + b * v) = (a * hi + b * hi ^ 2 / 2) - (a * lo + b * lo ^ 2 / 2) := by
  have hF : ∀ v ∈ uIcc lo hi, HasDerivAt (fun v : ℝ => a * v + (b / 2) * (v * v)) (a + b * v) v := by
    intro v _
    have h := ((hasDerivAt_id' v).const_mul a).add
      (((hasDerivAt_id' v).mul (hasDerivAt_id' v)).const_mul (b / 2))
    exact h.congr_deriv (by ring)
  have hint : IntervalIntegrable (fun v : ℝ => a + b * v) volume lo hi := by
    exact Continuous.intervalIntegrable (by fun_prop) _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF hint]
  ring

/-- The triangular kernel has total mass one. -/
lemma integral_ker (δ : ℝ) (hδ : 0 < δ) : ∫ v in (-δ)..δ, (1 / δ) * (1 - |v| / δ) = 1 := by
  have hc : Continuous (fun v : ℝ => (1 / δ) * (1 - |v| / δ)) :=
    continuous_const.mul (continuous_const.sub (continuous_abs.div_const δ))
  have hsplit : ∫ v in (-δ)..δ, (1 / δ) * (1 - |v| / δ) =
      (∫ v in (-δ)..0, (1 / δ) * (1 - |v| / δ)) + ∫ v in (0:ℝ)..δ, (1 / δ) * (1 - |v| / δ) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)).symm
  have hr : ∫ v in (0:ℝ)..δ, (1 / δ) * (1 - |v| / δ) =
      ∫ v in (0:ℝ)..δ, (1 / δ + (-(1 / δ ^ 2)) * v) := by
    refine intervalIntegral.integral_congr ?_
    intro v hv
    rw [Set.uIcc_of_le hδ.le] at hv
    dsimp only
    rw [abs_of_nonneg hv.1]
    field_simp
    ring
  have hl : ∫ v in (-δ)..(0:ℝ), (1 / δ) * (1 - |v| / δ) =
      ∫ v in (-δ)..(0:ℝ), (1 / δ + (1 / δ ^ 2) * v) := by
    refine intervalIntegral.integral_congr ?_
    intro v hv
    rw [Set.uIcc_of_le (by linarith : -δ ≤ 0)] at hv
    dsimp only
    rw [abs_of_nonpos hv.2]
    field_simp
    ring
  rw [hsplit, hr, hl, integral_lin, integral_lin]
  field_simp
  ring

lemma ker_nonneg {δ v : ℝ} (hδ : 0 < δ) (hv : |v| ≤ δ) : 0 ≤ (1 / δ) * (1 - |v| / δ) := by
  refine mul_nonneg (by positivity) ?_
  have hdiv : |v| / δ ≤ 1 := (div_le_one hδ).mpr hv
  linarith

/-- The closed form of the Mellin transform of the triangular kernel. -/
lemma main_id (δ : ℝ) (s : ℂ) (hδ : 0 < δ) (hs : s ≠ 0) :
    ∫ v in (-δ)..δ, (((1 / δ) * (1 - |v| / δ) : ℝ) : ℂ) * Complex.exp (s * (v : ℂ)) =
      ((Complex.exp (((δ / 2 : ℝ) : ℂ) * s) - Complex.exp (((-(δ / 2) : ℝ) : ℂ) * s)) /
        ((δ : ℂ) * s)) ^ 2 := by
  have hδ0 : (δ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hδ.ne'
  let g : ℝ → ℂ := fun v => (((1 / δ) * (1 - |v| / δ) : ℝ) : ℂ) * Complex.exp (s * (v : ℂ))
  have hg : Continuous g := by
    refine Continuous.mul ?_ ?_
    · exact Complex.continuous_ofReal.comp (continuous_const.mul (continuous_const.sub
        ((continuous_abs.div_const δ))))
    · exact Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
  have hsplit : ∫ v in (-δ)..δ, g v = (∫ v in (-δ)..0, g v) + (∫ v in (0:ℝ)..δ, g v) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hg.intervalIntegrable _ _) (hg.intervalIntegrable _ _)).symm
  have hright : ∫ v in (0:ℝ)..δ, g v =
      ∫ v in (0:ℝ)..δ, ((1 / (δ : ℂ)) + (-(1 / (δ : ℂ) ^ 2)) * (v : ℂ)) *
        Complex.exp (s * (v : ℂ)) := by
    refine intervalIntegral.integral_congr ?_
    intro v hv
    rw [Set.uIcc_of_le hδ.le] at hv
    have hv0 : 0 ≤ v := hv.1
    dsimp [g]
    congr 1
    rw [abs_of_nonneg hv0]
    push_cast
    field_simp
    ring
  have hleft : ∫ v in (-δ)..0, g v =
      ∫ v in (-δ)..(0:ℝ), ((1 / (δ : ℂ)) + ((1 / (δ : ℂ) ^ 2)) * (v : ℂ)) *
        Complex.exp (s * (v : ℂ)) := by
    refine intervalIntegral.integral_congr ?_
    intro v hv
    rw [Set.uIcc_of_le (by linarith : -δ ≤ 0)] at hv
    have hv0 : v ≤ 0 := hv.2
    dsimp [g]
    congr 1
    rw [abs_of_nonpos hv0]
    push_cast
    field_simp
    ring
  rw [hsplit, hright, hleft]
  rw [integral_lin_exp (1 / (δ : ℂ)) (-(1 / (δ : ℂ) ^ 2)) s hs 0 δ]
  rw [integral_lin_exp (1 / (δ : ℂ)) ((1 / (δ : ℂ) ^ 2)) s hs (-δ) 0]
  have hA2 : Complex.exp (((δ / 2 : ℝ) : ℂ) * s) ^ 2 = Complex.exp (s * (δ : ℂ)) := by
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hB2 : Complex.exp (((-(δ / 2) : ℝ) : ℂ) * s) ^ 2 = Complex.exp (s * ((-δ : ℝ) : ℂ)) := by
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hAB : Complex.exp (((δ / 2 : ℝ) : ℂ) * s) * Complex.exp (((-(δ / 2) : ℝ) : ℂ) * s) = 1 := by
    rw [← Complex.exp_add]
    have h0 : (((δ / 2 : ℝ) : ℂ) * s) + (((-(δ / 2) : ℝ) : ℂ) * s) = 0 := by
      push_cast
      ring
    rw [h0, Complex.exp_zero]
  have hsq : (Complex.exp (((δ / 2 : ℝ) : ℂ) * s) - Complex.exp (((-(δ / 2) : ℝ) : ℂ) * s)) ^ 2 =
      Complex.exp (s * (δ : ℂ)) + Complex.exp (s * ((-δ : ℝ) : ℂ)) - 2 := by
    calc _ = Complex.exp (((δ / 2 : ℝ) : ℂ) * s) ^ 2 -
        2 * (Complex.exp (((δ / 2 : ℝ) : ℂ) * s) * Complex.exp (((-(δ / 2) : ℝ) : ℂ) * s)) +
        Complex.exp (((-(δ / 2) : ℝ) : ℂ) * s) ^ 2 := by ring
      _ = _ := by rw [hA2, hAB, hB2]; ring
  rw [div_pow, hsq]
  simp only [Complex.ofReal_zero, mul_zero, add_zero, Complex.exp_zero, one_mul, Complex.ofReal_neg]
  field_simp
  ring

/-- The first bound: `‖M‖ ≤ exp (δ |Re s|)`, from the triangle inequality on the integral. -/
lemma bound_int (δ : ℝ) (s : ℂ) (hδ : 0 < δ) :
    ‖∫ v in (-δ)..δ, (((1 / δ) * (1 - |v| / δ) : ℝ) : ℂ) * Complex.exp (s * (v : ℂ))‖ ≤
      Real.exp (δ * |s.re|) := by
  let g : ℝ → ℂ := fun v => (((1 / δ) * (1 - |v| / δ) : ℝ) : ℂ) * Complex.exp (s * (v : ℂ))
  have hg : Continuous g := by
    refine Continuous.mul ?_ ?_
    · exact Complex.continuous_ofReal.comp (continuous_const.mul (continuous_const.sub
        ((continuous_abs.div_const δ))))
    · exact Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
  have hk : Continuous (fun v : ℝ => (1 / δ) * (1 - |v| / δ)) :=
    continuous_const.mul (continuous_const.sub (continuous_abs.div_const δ))
  calc ‖∫ v in (-δ)..δ, g v‖ ≤ ∫ v in (-δ)..δ, ‖g v‖ :=
        intervalIntegral.norm_integral_le_integral_norm (by linarith)
    _ ≤ ∫ v in (-δ)..δ, (1 / δ) * (1 - |v| / δ) * Real.exp (δ * |s.re|) := by
        refine intervalIntegral.integral_mono_on (by linarith)
          ((continuous_norm.comp hg).intervalIntegrable _ _)
          ((hk.mul continuous_const).intervalIntegrable _ _) ?_
        intro v hv
        have habs : |v| ≤ δ := abs_le.mpr ⟨hv.1, hv.2⟩
        have hker : 0 ≤ (1 / δ) * (1 - |v| / δ) := ker_nonneg hδ habs
        have hgn : ‖g v‖ = (1 / δ) * (1 - |v| / δ) * Real.exp (s.re * v) := by
          dsimp [g]
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hker, Complex.norm_exp]
          have hre : (s * (v : ℂ)).re = s.re * v := by simp [Complex.mul_re]
          rw [hre]
        have hexp : Real.exp (s.re * v) ≤ Real.exp (δ * |s.re|) := by
          refine Real.exp_le_exp.mpr ?_
          calc s.re * v ≤ |s.re * v| := le_abs_self _
            _ = |s.re| * |v| := abs_mul _ _
            _ ≤ |s.re| * δ := mul_le_mul_of_nonneg_left habs (abs_nonneg _)
            _ = δ * |s.re| := mul_comm _ _
        rw [hgn]
        exact mul_le_mul_of_nonneg_left hexp hker
    _ = Real.exp (δ * |s.re|) * ∫ v in (-δ)..δ, (1 / δ) * (1 - |v| / δ) := by
        rw [← intervalIntegral.integral_const_mul]
        refine intervalIntegral.integral_congr ?_
        intro v _
        ring
    _ = Real.exp (δ * |s.re|) := by rw [integral_ker δ hδ, mul_one]

/-- The second bound, from the closed form and the triangle inequality for `exp (±δ s / 2)`. -/
lemma bound_closed (δ : ℝ) (s : ℂ) (hδ : 0 < δ) (hs : s ≠ 0) :
    ‖((Complex.exp (((δ / 2 : ℝ) : ℂ) * s) - Complex.exp (((-(δ / 2) : ℝ) : ℂ) * s)) /
      ((δ : ℂ) * s)) ^ 2‖ ≤ 4 * Real.exp (δ * |s.re|) / (δ ^ 2 * ‖s‖ ^ 2) := by
  have hnorm : ‖((Complex.exp (((δ / 2 : ℝ) : ℂ) * s) - Complex.exp (((-(δ / 2) : ℝ) : ℂ) * s)) /
      ((δ : ℂ) * s)) ^ 2‖ =
      ‖Complex.exp (((δ / 2 : ℝ) : ℂ) * s) - Complex.exp (((-(δ / 2) : ℝ) : ℂ) * s)‖ ^ 2 /
        (δ ^ 2 * ‖s‖ ^ 2) := by
    rw [norm_pow, norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg hδ.le, div_pow, mul_pow]
  rw [hnorm]
  have hA : ‖Complex.exp (((δ / 2 : ℝ) : ℂ) * s)‖ = Real.exp (δ / 2 * s.re) := by
    rw [Complex.norm_exp]
    have hre : ((((δ / 2 : ℝ) : ℂ) * s)).re = δ / 2 * s.re := by simp [Complex.mul_re]
    rw [hre]
  have hB : ‖Complex.exp (((-(δ / 2) : ℝ) : ℂ) * s)‖ = Real.exp (-(δ / 2) * s.re) := by
    rw [Complex.norm_exp]
    have hre : (((( -(δ / 2) : ℝ) : ℂ) * s)).re = -(δ / 2) * s.re := by simp [Complex.mul_re]
    rw [hre]
  have hsub : ‖Complex.exp (((δ / 2 : ℝ) : ℂ) * s) - Complex.exp (((-(δ / 2) : ℝ) : ℂ) * s)‖ ≤
      2 * Real.exp (δ * |s.re| / 2) := by
    calc _ ≤ ‖Complex.exp (((δ / 2 : ℝ) : ℂ) * s)‖ + ‖Complex.exp (((-(δ / 2) : ℝ) : ℂ) * s)‖ :=
          norm_sub_le _ _
      _ = Real.exp (δ / 2 * s.re) + Real.exp (-(δ / 2) * s.re) := by rw [hA, hB]
      _ ≤ 2 * Real.exp (δ * |s.re| / 2) := by
          have h1 : δ / 2 * s.re ≤ δ * |s.re| / 2 := by
            calc δ / 2 * s.re ≤ δ / 2 * |s.re| :=
                  mul_le_mul_of_nonneg_left (le_abs_self s.re) (by positivity)
              _ = δ * |s.re| / 2 := by ring
          have h2 : -(δ / 2) * s.re ≤ δ * |s.re| / 2 := by
            calc -(δ / 2) * s.re = δ / 2 * (-s.re) := by ring
              _ ≤ δ / 2 * |s.re| :=
                  mul_le_mul_of_nonneg_left (neg_le_abs s.re) (by positivity)
              _ = δ * |s.re| / 2 := by ring
          have e1 := Real.exp_le_exp.mpr h1
          have e2 := Real.exp_le_exp.mpr h2
          linarith
  have hsq : ‖Complex.exp (((δ / 2 : ℝ) : ℂ) * s) - Complex.exp (((-(δ / 2) : ℝ) : ℂ) * s)‖ ^ 2 ≤
      (2 * Real.exp (δ * |s.re| / 2)) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hsub 2
  have hexp2 : (2 * Real.exp (δ * |s.re| / 2)) ^ 2 = 4 * Real.exp (δ * |s.re|) := by
    have h : Real.exp (δ * |s.re| / 2) ^ 2 = Real.exp (δ * |s.re|) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [mul_pow, h]
    ring
  rw [hexp2] at hsq
  refine div_le_div_of_nonneg_right hsq ?_
  positivity

end Conjectures.Goldbach.GmSmoothingKernelMellin_aux

open Conjectures.Goldbach.GmSmoothingKernelMellin_aux

theorem Conjectures.Goldbach.GmSmoothingKernelMellin :
    ∀ (δ : ℝ) (s : ℂ), 0 < δ → s ≠ 0 → let M : ℂ := ∫ v in (-δ)..δ, (((1 / δ) * (1 - |v| / δ) : ℝ) : ℂ) * Complex.exp (s * (v : ℂ)); M = ((Complex.exp (((δ / 2 : ℝ) : ℂ) * s) - Complex.exp (((-(δ / 2) : ℝ) : ℂ) * s)) / ((δ : ℂ) * s)) ^ 2 ∧ ‖M‖ ≤ min (Real.exp (δ * |s.re|)) (4 * Real.exp (δ * |s.re|) / (δ ^ 2 * ‖s‖ ^ 2)) := by
  intro δ s hδ hs
  dsimp only
  refine ⟨main_id δ s hδ hs, ?_⟩
  refine le_min (bound_int δ s hδ) ?_
  rw [main_id δ s hδ hs]
  exact bound_closed δ s hδ hs
