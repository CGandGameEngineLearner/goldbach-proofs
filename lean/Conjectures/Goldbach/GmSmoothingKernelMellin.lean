import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Add

open MeasureTheory intervalIntegral

namespace Conjectures.Goldbach

lemma hasDerivAt_ofRealCo (u : ℝ) :
    HasDerivAt (fun y : ℝ => (y : ℂ)) 1 u := by
  exact Complex.ofRealCLM.hasDerivAt

lemma hasDerivAt_gmExp (c : ℂ) (u : ℝ) :
    HasDerivAt (fun y : ℝ => Complex.exp (c * (y : ℂ))) (Complex.exp (c * (u : ℂ)) * c) u := by
  have hlin : HasDerivAt (fun y : ℝ => c * (y : ℂ)) c u := by
    simpa using (hasDerivAt_ofRealCo u).const_mul c
  exact hlin.cexp

lemma hasDerivAt_gmAffine (d : ℝ) (u : ℝ) :
    HasDerivAt (fun y : ℝ => (((1 - y / d : ℝ)) : ℂ)) (-(((1 / d : ℝ)) : ℂ)) u := by
  have hy : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 u := hasDerivAt_ofRealCo u
  have hc : HasDerivAt (fun y : ℝ => (((1 / d : ℝ)) : ℂ) * (y : ℂ)) (((1 / d : ℝ)) : ℂ) u := by
    simpa using hy.const_mul (((1 / d : ℝ)) : ℂ)
  have hsub : HasDerivAt (fun y : ℝ => (1 : ℂ) - (((1 / d : ℝ)) : ℂ) * (y : ℂ)) ((0 : ℂ) - (((1 / d : ℝ)) : ℂ)) u :=
    (hasDerivAt_const u (1 : ℂ)).sub hc
  have hfun : (fun y : ℝ => (1 : ℂ) - (((1 / d : ℝ)) : ℂ) * (y : ℂ)) = (fun y : ℝ => (((1 - y / d : ℝ)) : ℂ)) := by
    funext y
    push_cast
    ring
  rw [hfun] at hsub
  simpa using hsub

lemma hasDerivAt_gmAnti (d : ℝ) (hd : (d : ℂ) ≠ 0) (c : ℂ) (hc : c ≠ 0) (u : ℝ) :
    HasDerivAt (fun y : ℝ => Complex.exp (c * (y : ℂ)) *
      ((((1 - y / d : ℝ)) : ℂ) / c + 1 / ((d : ℂ) * c ^ 2)))
      ((((1 - u / d : ℝ)) : ℂ) * Complex.exp (c * (u : ℂ))) u := by
  have hexp : HasDerivAt (fun y : ℝ => Complex.exp (c * (y : ℂ))) (Complex.exp (c * (u : ℂ)) * c) u :=
    hasDerivAt_gmExp c u
  have hX : HasDerivAt (fun y : ℝ => (((1 - y / d : ℝ)) : ℂ)) (-(((1 / d : ℝ)) : ℂ)) u :=
    hasDerivAt_gmAffine d u
  have hG : HasDerivAt (fun y : ℝ => ((((1 - y / d : ℝ)) : ℂ) / c + 1 / ((d : ℂ) * c ^ 2)))
      ((-(((1 / d : ℝ)) : ℂ)) / c) u :=
    (hX.div_const c).add_const (1 / ((d : ℂ) * c ^ 2))
  have hval : c * ((((1 - u / d : ℝ)) : ℂ) / c + 1 / ((d : ℂ) * c ^ 2)) + (-(((1 / d : ℝ)) : ℂ)) / c
      = (((1 - u / d : ℝ)) : ℂ) := by
    push_cast
    field_simp
    ring
  have hmul := hexp.mul hG
  have htarget : Complex.exp (c * (u : ℂ)) * c *
      ((((1 - u / d : ℝ)) : ℂ) / c + 1 / ((d : ℂ) * c ^ 2)) +
      Complex.exp (c * (u : ℂ)) * ((-(((1 / d : ℝ)) : ℂ)) / c)
      = (((1 - u / d : ℝ)) : ℂ) * Complex.exp (c * (u : ℂ)) := by
    calc Complex.exp (c * (u : ℂ)) * c * ((((1 - u / d : ℝ)) : ℂ) / c + 1 / ((d : ℂ) * c ^ 2)) +
          Complex.exp (c * (u : ℂ)) * ((-(((1 / d : ℝ)) : ℂ)) / c)
        = Complex.exp (c * (u : ℂ)) *
          (c * ((((1 - u / d : ℝ)) : ℂ) / c + 1 / ((d : ℂ) * c ^ 2)) + (-(((1 / d : ℝ)) : ℂ)) / c) := by
          ring
      _ = Complex.exp (c * (u : ℂ)) * (((1 - u / d : ℝ)) : ℂ) := by rw [hval]
      _ = (((1 - u / d : ℝ)) : ℂ) * Complex.exp (c * (u : ℂ)) := by ring
  rw [htarget] at hmul
  exact hmul

lemma gmIntegral_T (d : ℝ) (hd : 0 < d) (c : ℂ) (hc : c ≠ 0) :
    ∫ x in (0 : ℝ)..d, ((((1 - x / d : ℝ)) : ℂ) * Complex.exp (c * (x : ℂ)))
      = Complex.exp (c * (d : ℂ)) / ((d : ℂ) * c ^ 2) - 1 / c - 1 / ((d : ℂ) * c ^ 2) := by
  have hd0 : d ≠ 0 := ne_of_gt hd
  have hdc : (d : ℂ) ≠ 0 := by exact_mod_cast hd0
  have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) d,
      HasDerivAt (fun y : ℝ => Complex.exp (c * (y : ℂ)) *
        ((((1 - y / d : ℝ)) : ℂ) / c + 1 / ((d : ℂ) * c ^ 2)))
        ((((1 - x / d : ℝ)) : ℂ) * Complex.exp (c * (x : ℂ))) x := by
    intro x hx
    exact hasDerivAt_gmAnti d hdc c hc x
  have hcont : Continuous (fun x : ℝ => ((((1 - x / d : ℝ)) : ℂ) * Complex.exp (c * (x : ℂ)))) := by
    apply Continuous.mul
    · exact Complex.continuous_ofReal.comp (continuous_const.sub (continuous_id.div_const d))
    · exact Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
  have hint : IntervalIntegrable (fun x : ℝ => ((((1 - x / d : ℝ)) : ℂ) * Complex.exp (c * (x : ℂ)))) volume (0 : ℝ) d :=
    hcont.intervalIntegrable 0 d
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0 : ℝ)) (b := d)
    (f := fun y : ℝ => Complex.exp (c * (y : ℂ)) * ((((1 - y / d : ℝ)) : ℂ) / c + 1 / ((d : ℂ) * c ^ 2)))
    (f' := fun x : ℝ => ((((1 - x / d : ℝ)) : ℂ) * Complex.exp (c * (x : ℂ)))) hderiv hint
  rw [hFTC]
  rw [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  simp only [zero_div, sub_zero, div_self hd0, sub_self, Complex.ofReal_zero, Complex.ofReal_one,
    one_mul, zero_add, mul_one]
  field_simp
  ring

lemma gmIntPos (d : ℝ) (hd : 0 < d) (c : ℂ) (hc : c ≠ 0) :
    ∫ x in (0 : ℝ)..d, (((1 / d) * (1 - x / d : ℝ)) : ℂ) * Complex.exp (c * (x : ℂ))
      = (((1 / d : ℝ)) : ℂ) * (Complex.exp (c * (d : ℂ)) / ((d : ℂ) * c ^ 2) - 1 / c - 1 / ((d : ℂ) * c ^ 2)) := by
  calc ∫ x in (0 : ℝ)..d, (((1 / d) * (1 - x / d : ℝ)) : ℂ) * Complex.exp (c * (x : ℂ))
      = ∫ x in (0 : ℝ)..d, (((1 / d : ℝ)) : ℂ) * ((((1 - x / d : ℝ)) : ℂ) * Complex.exp (c * (x : ℂ))) := by
        apply intervalIntegral.integral_congr
        intro x hx
        push_cast
        ring
    _ = (((1 / d : ℝ)) : ℂ) * ∫ x in (0 : ℝ)..d, ((((1 - x / d : ℝ)) : ℂ) * Complex.exp (c * (x : ℂ))) := by
        rw [intervalIntegral.integral_const_mul]
    _ = (((1 / d : ℝ)) : ℂ) * (Complex.exp (c * (d : ℂ)) / ((d : ℂ) * c ^ 2) - 1 / c - 1 / ((d : ℂ) * c ^ 2)) := by
        rw [gmIntegral_T d hd c hc]

lemma gmIntNeg (d : ℝ) (hd : 0 < d) (c : ℂ) (hc : c ≠ 0) :
    ∫ x in (0 : ℝ)..d, (((1 / d) * (1 - x / d : ℝ)) : ℂ) * Complex.exp ((-c) * (x : ℂ))
      = (((1 / d : ℝ)) : ℂ) * (Complex.exp ((-c) * (d : ℂ)) / ((d : ℂ) * (-c) ^ 2) - 1 / (-c) - 1 / ((d : ℂ) * (-c) ^ 2)) := by
  calc ∫ x in (0 : ℝ)..d, (((1 / d) * (1 - x / d : ℝ)) : ℂ) * Complex.exp ((-c) * (x : ℂ))
      = ∫ x in (0 : ℝ)..d, (((1 / d : ℝ)) : ℂ) * ((((1 - x / d : ℝ)) : ℂ) * Complex.exp ((-c) * (x : ℂ))) := by
        apply intervalIntegral.integral_congr
        intro x hx
        push_cast
        ring
    _ = (((1 / d : ℝ)) : ℂ) * ∫ x in (0 : ℝ)..d, ((((1 - x / d : ℝ)) : ℂ) * Complex.exp ((-c) * (x : ℂ))) := by
        rw [intervalIntegral.integral_const_mul]
    _ = (((1 / d : ℝ)) : ℂ) * (Complex.exp ((-c) * (d : ℂ)) / ((d : ℂ) * (-c) ^ 2) - 1 / (-c) - 1 / ((d : ℂ) * (-c) ^ 2)) := by
        rw [gmIntegral_T d hd (-c) (neg_ne_zero.mpr hc)]

lemma galg2 (D C E1 E2 : ℂ) (hD : D ≠ 0) (hC : C ≠ 0) :
    (1 / D) * ((E1 / (D * C ^ 2) - 1 / C - 1 / (D * C ^ 2)) + (E2 / (D * C ^ 2) - 1 / (-C) - 1 / (D * C ^ 2)))
      = (E1 + E2 - 2) / (D ^ 2 * C ^ 2) := by
  have h : (1 : ℂ) / (-C) = -(1 / C) := by ring
  rw [h]
  field_simp
  ring

set_option maxHeartbeats 400000 in
lemma gmIdentity (d : ℝ) (hd : 0 < d) (c : ℂ) (hc : c ≠ 0) :
    ∫ v in (-d)..d, (((1 / d) * (1 - |v| / d) : ℝ) : ℂ) * Complex.exp (c * (v : ℂ))
      = (Complex.exp (c * (d : ℂ)) + Complex.exp (-(c * (d : ℂ))) - 2) / ((d : ℂ) ^ 2 * c ^ 2) := by
  have hd0 : d ≠ 0 := ne_of_gt hd
  have hdc : (d : ℂ) ≠ 0 := by exact_mod_cast hd0
  have hcont : Continuous (fun v : ℝ => (((1 / d) * (1 - |v| / d) : ℝ) : ℂ) * Complex.exp (c * (v : ℂ))) := by
    apply Continuous.mul
    · exact Complex.continuous_ofReal.comp (continuous_const.mul (continuous_const.sub (continuous_abs.div_const d)))
    · exact Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
  have hnegint : ∫ x in (-d)..(0 : ℝ), (((1 / d) * (1 - |x| / d) : ℝ) : ℂ) * Complex.exp (c * (x : ℂ))
      = ∫ x in (0 : ℝ)..d, (((1 / d) * (1 - |(-x)| / d) : ℝ) : ℂ) * Complex.exp (c * ((-x : ℝ) : ℂ)) :=
    (intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := d)
      (f := fun v : ℝ => (((1 / d) * (1 - |v| / d) : ℝ) : ℂ) * Complex.exp (c * (v : ℂ)))).symm
  have hsplit : (∫ x in (-d)..(0 : ℝ), (((1 / d) * (1 - |x| / d) : ℝ) : ℂ) * Complex.exp (c * (x : ℂ)))
      + (∫ x in (0 : ℝ)..d, (((1 / d) * (1 - |x| / d) : ℝ) : ℂ) * Complex.exp (c * (x : ℂ)))
      = ∫ x in (-d)..d, (((1 / d) * (1 - |x| / d) : ℝ) : ℂ) * Complex.exp (c * (x : ℂ)) :=
    intervalIntegral.integral_add_adjacent_intervals (a := -d) (b := (0 : ℝ)) (c := d)
      (hcont.intervalIntegrable (-d) 0) (hcont.intervalIntegrable 0 d)
  have hpos : ∫ x in (0 : ℝ)..d, (((1 / d) * (1 - |x| / d) : ℝ) : ℂ) * Complex.exp (c * (x : ℂ))
      = (((1 / d : ℝ)) : ℂ) * (Complex.exp (c * (d : ℂ)) / ((d : ℂ) * c ^ 2) - 1 / c - 1 / ((d : ℂ) * c ^ 2)) := by
    calc ∫ x in (0 : ℝ)..d, (((1 / d) * (1 - |x| / d) : ℝ) : ℂ) * Complex.exp (c * (x : ℂ))
        = ∫ x in (0 : ℝ)..d, (((1 / d) * (1 - x / d : ℝ)) : ℂ) * Complex.exp (c * (x : ℂ)) := by
          apply intervalIntegral.integral_congr
          intro x hx
          dsimp only
          have hx0 : 0 ≤ x := by
            rcases Set.mem_uIcc.mp hx with h | h
            · exact h.1
            · linarith [h.1, h.2, hd]
          rw [abs_of_nonneg hx0]
          push_cast
          ring
      _ = (((1 / d : ℝ)) : ℂ) * (Complex.exp (c * (d : ℂ)) / ((d : ℂ) * c ^ 2) - 1 / c - 1 / ((d : ℂ) * c ^ 2)) :=
          gmIntPos d hd c hc
  have hneg : ∫ x in (0 : ℝ)..d, (((1 / d) * (1 - |(-x)| / d) : ℝ) : ℂ) * Complex.exp (c * ((-x : ℝ) : ℂ))
      = (((1 / d : ℝ)) : ℂ) * (Complex.exp ((-c) * (d : ℂ)) / ((d : ℂ) * (-c) ^ 2) - 1 / (-c) - 1 / ((d : ℂ) * (-c) ^ 2)) := by
    calc ∫ x in (0 : ℝ)..d, (((1 / d) * (1 - |(-x)| / d) : ℝ) : ℂ) * Complex.exp (c * ((-x : ℝ) : ℂ))
        = ∫ x in (0 : ℝ)..d, (((1 / d) * (1 - x / d : ℝ)) : ℂ) * Complex.exp ((-c) * (x : ℂ)) := by
          apply intervalIntegral.integral_congr
          intro x hx
          dsimp only
          have hx0 : 0 ≤ x := by
            rcases Set.mem_uIcc.mp hx with h | h
            · exact h.1
            · linarith [h.1, h.2, hd]
          rw [abs_neg, abs_of_nonneg hx0]
          have harg : c * (((-x : ℝ)) : ℂ) = (-c) * (x : ℂ) := by push_cast; ring
          rw [harg]
          push_cast
          ring
      _ = (((1 / d : ℝ)) : ℂ) * (Complex.exp ((-c) * (d : ℂ)) / ((d : ℂ) * (-c) ^ 2) - 1 / (-c) - 1 / ((d : ℂ) * (-c) ^ 2)) :=
          gmIntNeg d hd c hc
  rw [← hsplit]
  rw [hnegint, hpos, hneg]
  rw [show (-c) * (d : ℂ) = -(c * (d : ℂ)) from by ring,
      show (-c) ^ 2 = c ^ 2 from by ring]
  have hcast : (((1 / d : ℝ)) : ℂ) = 1 / (d : ℂ) := by push_cast; ring
  rw [hcast, ← mul_add, add_comm]
  exact galg2 (d : ℂ) c (Complex.exp (c * (d : ℂ))) (Complex.exp (-(c * (d : ℂ)))) hdc hc

set_option maxHeartbeats 600000 in
lemma gmSquare (d : ℝ) (hd : 0 < d) (c : ℂ) (hc : c ≠ 0) :
    (Complex.exp (c * (d : ℂ)) + Complex.exp (-(c * (d : ℂ))) - 2) / ((d : ℂ) ^ 2 * c ^ 2)
      = ((Complex.exp ((((d / 2 : ℝ)) : ℂ) * c) - Complex.exp ((((-(d / 2) : ℝ)) : ℂ) * c)) / ((d : ℂ) * c)) ^ 2 := by
  have hA : Complex.exp (c * (d : ℂ)) = Complex.exp ((((d / 2 : ℝ)) : ℂ) * c) ^ 2 := by
    have harg : c * (d : ℂ) = ((((d / 2 : ℝ)) : ℂ) * c) + ((((d / 2 : ℝ)) : ℂ) * c) := by push_cast; ring
    rw [harg, Complex.exp_add, sq]
  have hB : Complex.exp (-(c * (d : ℂ))) = Complex.exp ((((-(d / 2) : ℝ)) : ℂ) * c) ^ 2 := by
    have harg : -(c * (d : ℂ)) = ((((-(d / 2) : ℝ)) : ℂ) * c) + ((((-(d / 2) : ℝ)) : ℂ) * c) := by push_cast; ring
    rw [harg, Complex.exp_add, sq]
  have hAB : Complex.exp ((((d / 2 : ℝ)) : ℂ) * c) * Complex.exp ((((-(d / 2) : ℝ)) : ℂ) * c) = 1 := by
    rw [← Complex.exp_add]
    have harg : ((((d / 2 : ℝ)) : ℂ) * c) + ((((-(d / 2) : ℝ)) : ℂ) * c) = 0 := by push_cast; ring
    rw [harg, Complex.exp_zero]
  have hkey : Complex.exp ((((d / 2 : ℝ)) : ℂ) * c) ^ 2 + Complex.exp ((((-(d / 2) : ℝ)) : ℂ) * c) ^ 2 - 2
      = (Complex.exp ((((d / 2 : ℝ)) : ℂ) * c) - Complex.exp ((((-(d / 2) : ℝ)) : ℂ) * c)) ^ 2 := by
    rw [sub_sq]
    rw [show (2 : ℂ) * Complex.exp ((((d / 2 : ℝ)) : ℂ) * c) * Complex.exp ((((-(d / 2) : ℝ)) : ℂ) * c)
        = 2 * (Complex.exp ((((d / 2 : ℝ)) : ℂ) * c) * Complex.exp ((((-(d / 2) : ℝ)) : ℂ) * c)) from by ring]
    rw [hAB]
    ring
  rw [hA, hB, hkey, div_pow, mul_pow]

set_option maxHeartbeats 600000 in
lemma gmNormExpDiff (w : ℂ) :
    ‖Complex.exp w - Complex.exp (-w)‖ ≤ 2 * ‖w‖ * Real.exp |w.re| := by
  have hrepr : Complex.exp w - Complex.exp (-w) = ∫ t in (-1 : ℝ)..1, w * Complex.exp ((t : ℂ) * w) := by
    have hderiv : ∀ x ∈ Set.uIcc (-1 : ℝ) 1,
        HasDerivAt (fun y : ℝ => Complex.exp ((y : ℂ) * w)) (w * Complex.exp ((x : ℂ) * w)) x := by
      intro x hx
      have hlin : HasDerivAt (fun y : ℝ => (y : ℂ) * w) w x := by
        have h0 : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x := hasDerivAt_ofRealCo x
        simpa using h0.mul_const w
      simpa [mul_comm] using hlin.cexp
    have hcont : Continuous (fun x : ℝ => w * Complex.exp ((x : ℂ) * w)) :=
      continuous_const.mul (Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const))
    have hint : IntervalIntegrable (fun x : ℝ => w * Complex.exp ((x : ℂ) * w)) volume (-1 : ℝ) 1 :=
      hcont.intervalIntegrable _ _
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (-1 : ℝ)) (b := 1)
      (f := fun y : ℝ => Complex.exp ((y : ℂ) * w))
      (f' := fun x : ℝ => w * Complex.exp ((x : ℂ) * w)) hderiv hint
    rw [h]
    simp
  rw [hrepr]
  have hC : ‖∫ t in (-1 : ℝ)..1, w * Complex.exp ((t : ℂ) * w)‖ ≤ 2 * ‖w‖ * Real.exp |w.re| := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (-1 : ℝ)) (b := 1)
      (C := ‖w‖ * Real.exp |w.re|) (f := fun t : ℝ => w * Complex.exp ((t : ℂ) * w))
      (by
        intro t ht
        have ht1 : -1 < t := by simpa using ht.1
        have ht2 : t ≤ 1 := by simpa using ht.2
        have htabs : |t| ≤ 1 := abs_le.2 ⟨le_of_lt ht1, ht2⟩
        calc ‖w * Complex.exp ((t : ℂ) * w)‖ = ‖w‖ * Real.exp (t * w.re) := by
              rw [norm_mul, Complex.norm_exp]
              congr 1
              simp [Complex.mul_re]
          _ ≤ ‖w‖ * Real.exp |w.re| := by
              apply mul_le_mul_of_nonneg_left _ (norm_nonneg w)
              apply Real.exp_le_exp.2
              calc t * w.re ≤ |t * w.re| := le_abs_self _
                _ = |t| * |w.re| := abs_mul t w.re
                _ ≤ 1 * |w.re| := mul_le_mul_of_nonneg_right htabs (abs_nonneg w.re)
                _ = |w.re| := one_mul _)
    calc ‖∫ t in (-1 : ℝ)..1, w * Complex.exp ((t : ℂ) * w)‖ ≤ (‖w‖ * Real.exp |w.re|) * |1 - (-1)| := h
      _ = 2 * ‖w‖ * Real.exp |w.re| := by norm_num; ring
  exact hC

set_option maxHeartbeats 400000 in
lemma gmNormExpDiff' (w : ℂ) :
    ‖Complex.exp w - Complex.exp (-w)‖ ≤ 2 * Real.exp |w.re| := by
  have h1 : ‖Complex.exp w‖ = Real.exp w.re := Complex.norm_exp w
  have h2 : ‖Complex.exp (-w)‖ = Real.exp (-w.re) := by
    rw [Complex.norm_exp]
    congr 1
  calc ‖Complex.exp w - Complex.exp (-w)‖ ≤ ‖Complex.exp w‖ + ‖Complex.exp (-w)‖ := norm_sub_le _ _
    _ = Real.exp w.re + Real.exp (-w.re) := by rw [h1, h2]
    _ ≤ Real.exp |w.re| + Real.exp |w.re| := by
        apply add_le_add
        · exact Real.exp_le_exp.2 (le_abs_self w.re)
        · exact Real.exp_le_exp.2 (neg_le_abs w.re)
    _ = 2 * Real.exp |w.re| := by ring

set_option maxHeartbeats 400000 in
lemma gmNormBound (d : ℝ) (hd : 0 < d) (c : ℂ) (hc : c ≠ 0) :
    ‖((Complex.exp ((((d / 2 : ℝ)) : ℂ) * c) - Complex.exp ((((-(d / 2) : ℝ)) : ℂ) * c)) / ((d : ℂ) * c)) ^ 2‖
      ≤ min (Real.exp (d * |c.re|)) (4 * Real.exp (d * |c.re|) / (d ^ 2 * ‖c‖ ^ 2)) := by
  have hΔ1 : ‖Complex.exp ((((d / 2 : ℝ)) : ℂ) * c) - Complex.exp ((((-(d / 2) : ℝ)) : ℂ) * c)‖
      ≤ 2 * ‖(((d / 2 : ℝ)) : ℂ) * c‖ * Real.exp |((((d / 2 : ℝ)) : ℂ) * c).re| := by
    simpa only [Complex.ofReal_neg, neg_mul] using gmNormExpDiff ((((d / 2 : ℝ)) : ℂ) * c)
  have hΔ2 : ‖Complex.exp ((((d / 2 : ℝ)) : ℂ) * c) - Complex.exp ((((-(d / 2) : ℝ)) : ℂ) * c)‖
      ≤ 2 * Real.exp |((((d / 2 : ℝ)) : ℂ) * c).re| := by
    simpa only [Complex.ofReal_neg, neg_mul] using gmNormExpDiff' ((((d / 2 : ℝ)) : ℂ) * c)
  have hre : ((((d / 2 : ℝ)) : ℂ) * c).re = d / 2 * c.re := by
    simp [Complex.mul_re]
  have hx : |((((d / 2 : ℝ)) : ℂ) * c).re| = d / 2 * |c.re| := by
    rw [hre, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < d / 2)]
  have hwnorm : ‖(((d / 2 : ℝ)) : ℂ) * c‖ = d / 2 * ‖c‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith : (0 : ℝ) < d / 2)]
  have hden : ‖(d : ℂ) * c‖ = d * ‖c‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd]
  have hcw : 0 < ‖c‖ := norm_pos_iff.2 hc
  have hdwc : 0 < d * ‖c‖ := mul_pos hd hcw
  have hpos : 0 ≤ d * ‖c‖ := le_of_lt hdwc
  have hsq : ‖((Complex.exp ((((d / 2 : ℝ)) : ℂ) * c) - Complex.exp ((((-(d / 2) : ℝ)) : ℂ) * c)) / ((d : ℂ) * c)) ^ 2‖
      = (‖Complex.exp ((((d / 2 : ℝ)) : ℂ) * c) - Complex.exp ((((-(d / 2) : ℝ)) : ℂ) * c)‖ / (d * ‖c‖)) ^ 2 := by
    rw [norm_pow, norm_div, hden]
  have hE : Real.exp (d / 2 * |c.re|) ^ 2 = Real.exp (d * |c.re|) := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  have hwval : (2 * ‖(((d / 2 : ℝ)) : ℂ) * c‖ * Real.exp |((((d / 2 : ℝ)) : ℂ) * c).re|) / (d * ‖c‖)
      = Real.exp (d / 2 * |c.re|) := by
    rw [hwnorm, hx]
    have hdc : d * ‖c‖ ≠ 0 := ne_of_gt hdwc
    field_simp
    try ring
  rw [hsq]
  refine le_min ?_ ?_
  · calc (‖Complex.exp ((((d / 2 : ℝ)) : ℂ) * c) - Complex.exp ((((-(d / 2) : ℝ)) : ℂ) * c)‖ / (d * ‖c‖)) ^ 2
        ≤ ((2 * ‖(((d / 2 : ℝ)) : ℂ) * c‖ * Real.exp |((((d / 2 : ℝ)) : ℂ) * c).re|) / (d * ‖c‖)) ^ 2 :=
          pow_le_pow_left₀ (div_nonneg (norm_nonneg _) hpos) (div_le_div_of_nonneg_right hΔ1 hpos) 2
      _ = Real.exp (d / 2 * |c.re|) ^ 2 := by rw [hwval]
      _ = Real.exp (d * |c.re|) := hE
  · have h2 : (‖Complex.exp ((((d / 2 : ℝ)) : ℂ) * c) - Complex.exp ((((-(d / 2) : ℝ)) : ℂ) * c)‖ / (d * ‖c‖)) ^ 2
        ≤ (2 * Real.exp (d / 2 * |c.re|) / (d * ‖c‖)) ^ 2 := by
      have hle : ‖Complex.exp ((((d / 2 : ℝ)) : ℂ) * c) - Complex.exp ((((-(d / 2) : ℝ)) : ℂ) * c)‖ / (d * ‖c‖)
          ≤ 2 * Real.exp (d / 2 * |c.re|) / (d * ‖c‖) := by
        have h' := div_le_div_of_nonneg_right hΔ2 hpos
        rwa [hx] at h'
      exact pow_le_pow_left₀ (div_nonneg (norm_nonneg _) hpos) hle 2
    calc (‖Complex.exp ((((d / 2 : ℝ)) : ℂ) * c) - Complex.exp ((((-(d / 2) : ℝ)) : ℂ) * c)‖ / (d * ‖c‖)) ^ 2
        ≤ (2 * Real.exp (d / 2 * |c.re|) / (d * ‖c‖)) ^ 2 := h2
      _ = 4 * Real.exp (d * |c.re|) / (d ^ 2 * ‖c‖ ^ 2) := by
          rw [div_pow, mul_pow, hE]
          rw [mul_pow]
          norm_num

set_option maxHeartbeats 400000 in
theorem GmSmoothingKernelMellin :
    ∀ (d : ℝ) (c : ℂ), 0 < d → c ≠ 0 →
      (let M : ℂ := ∫ v in (-d)..d, (((1 / d) * (1 - |v| / d) : ℝ) : ℂ) * Complex.exp (c * (v : ℂ))
       M = ((Complex.exp (((d / 2 : ℝ) : ℂ) * c) - Complex.exp (((-(d / 2) : ℝ) : ℂ) * c)) / ((d : ℂ) * c)) ^ 2 ∧
       ‖M‖ ≤ min (Real.exp (d * |c.re|)) (4 * Real.exp (d * |c.re|) / (d ^ 2 * ‖c‖ ^ 2))) := by
  intro d c hd hc
  dsimp only
  have hval : (∫ v in (-d)..d, (((1 / d) * (1 - |v| / d) : ℝ) : ℂ) * Complex.exp (c * (v : ℂ)))
      = ((Complex.exp ((((d / 2 : ℝ)) : ℂ) * c) - Complex.exp ((((-(d / 2) : ℝ)) : ℂ) * c)) / ((d : ℂ) * c)) ^ 2 := by
    rw [gmIdentity d hd c hc]
    exact gmSquare d hd c hc
  exact ⟨hval, by rw [hval]; exact gmNormBound d hd c hc⟩
