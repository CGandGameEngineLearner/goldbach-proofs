import Mathlib

/-!
# MA-7002: real Fourier coefficient of a symmetric arc

The integral of `Real.cos (u * x)` over the symmetric window `[a - H, a + H]` equals
`2 * Real.cos (u * a) * Real.sin (u * H) / u` when `u` is nonzero.
-/

open MeasureTheory

theorem PEqualNP.Outside.L_goldbach_minor_cosine_window_coefficient :
    ∀ a H u : ℝ, 0 ≤ H → u ≠ 0 →
      intervalIntegral (fun x => Real.cos (u * x)) (a - H) (a + H) MeasureTheory.volume
        = 2 * Real.cos (u * a) * Real.sin (u * H) / u := by
  intro a H u hH hu
  have hderiv : ∀ x ∈ Set.uIcc (a - H) (a + H),
      HasDerivAt (fun y : ℝ => Real.sin (u * y) / u) (Real.cos (u * x)) x := by
    intro x hx
    have h2 : HasDerivAt (fun y : ℝ => Real.sin (u * y)) (Real.cos (u * x) * u) x := by
      simpa using (((hasDerivAt_id x).const_mul u).sin)
    have h3 : HasDerivAt (fun y : ℝ => Real.sin (u * y) / u) (Real.cos (u * x)) x := by
      have h4 := h2.div_const u
      have h5 : (Real.cos (u * x) * u) / u = Real.cos (u * x) := mul_div_cancel_right₀ _ hu
      rwa [h5] at h4
    exact h3
  have hint : IntervalIntegrable (fun x : ℝ => Real.cos (u * x)) MeasureTheory.volume (a - H) (a + H) := by
    have hc : Continuous fun x : ℝ => Real.cos (u * x) := by fun_prop
    exact hc.intervalIntegrable (a - H) (a + H)
  have hmain : intervalIntegral (fun x => Real.cos (u * x)) (a - H) (a + H) MeasureTheory.volume
      = Real.sin (u * (a + H)) / u - Real.sin (u * (a - H)) / u := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := a - H) (b := a + H)
      (f := fun y : ℝ => Real.sin (u * y) / u) (f' := fun x : ℝ => Real.cos (u * x)) hderiv hint
    simpa using h
  have hsin : Real.sin (u * (a + H)) - Real.sin (u * (a - H))
      = 2 * Real.cos (u * a) * Real.sin (u * H) := by
    rw [mul_add, mul_sub, Real.sin_add, Real.sin_sub]
    ring
  rw [hmain, ← sub_div, hsin]
