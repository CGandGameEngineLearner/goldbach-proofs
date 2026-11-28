import Mathlib

/-!
`L-goldbach-gm-smoothing-kernel-mellin` (batch of 2026-11-28 15:02).

Mellin transform `M(s) = ∫_{-δ}^{δ} (1/δ)(1 - |v|/δ) e^{s v} dv` of the triangular
smoothing kernel equals `((e^{δs/2} - e^{-δs/2}) / (δ s))²`.  The kernel has total
mass one, giving `‖M‖ ≤ e^{δ |Re s|}`, and the closed form gives
`‖M‖ ≤ 4 e^{δ |Re s|} / (δ² ‖s‖²)`.
-/

namespace GmSmoothingKernelMellinAux

/-- Derivative of `v ↦ exp(s·v)` for a real variable. -/
private theorem exp_deriv (s : ℂ) (v : ℝ) :
    HasDerivAt (fun w : ℝ => Complex.exp (s * (w : ℂ))) (Complex.exp (s * (v : ℂ)) * s) v := by
  have linear : HasDerivAt (fun z : ℂ => s * z) s (v : ℂ) := by
    simpa only [mul_one, id_eq] using (hasDerivAt_id (v : ℂ)).const_mul s
  change HasDerivAt (fun x : ℝ => Complex.exp (s * (x : ℂ)))
    (Complex.exp (s * (v : ℂ)) * s) v
  exact linear.cexp.comp_ofReal (z := v)

/-- Antiderivative pieces for `x·e^{s x}` and `(-x)·e^{s x}`: the affine factors. -/
private theorem affine_deriv (s : ℂ) (v : ℝ) :
    HasDerivAt (fun w : ℝ => s⁻¹ * (w : ℂ) - s⁻¹ * s⁻¹) (s⁻¹) v := by
  have h1 : HasDerivAt (fun w : ℝ => s⁻¹ * (w : ℂ)) (s⁻¹) v := by
    simpa only [id_eq, mul_one] using
      ((hasDerivAt_id (v : ℂ)).const_mul s⁻¹).comp_ofReal
  exact h1.sub_const (s⁻¹ * s⁻¹)

private theorem affine_deriv_neg (s : ℂ) (v : ℝ) :
    HasDerivAt (fun w : ℝ => (-s⁻¹) * (w : ℂ) + s⁻¹ * s⁻¹) (-s⁻¹) v := by
  have h1 : HasDerivAt (fun w : ℝ => (-s⁻¹) * (w : ℂ)) (-s⁻¹) v := by
    simpa only [id_eq, mul_one] using
      ((hasDerivAt_id (v : ℂ)).const_mul (-s⁻¹)).comp_ofReal
  exact h1.add_const (s⁻¹ * s⁻¹)

private theorem vexp_deriv (s : ℂ) (hs : s ≠ 0) (v : ℝ) :
    HasDerivAt (fun w : ℝ => Complex.exp (s * (w : ℂ)) * (s⁻¹ * (w : ℂ) - s⁻¹ * s⁻¹))
      ((v : ℂ) * Complex.exp (s * (v : ℂ))) v := by
  refine HasDerivAt.congr_deriv ((exp_deriv s v).mul (affine_deriv s v)) ?_
  field_simp
  abel

private theorem nvexp_deriv (s : ℂ) (hs : s ≠ 0) (v : ℝ) :
    HasDerivAt (fun w : ℝ => Complex.exp (s * (w : ℂ)) * ((-s⁻¹) * (w : ℂ) + s⁻¹ * s⁻¹))
      (-(v : ℂ) * Complex.exp (s * (v : ℂ))) v := by
  refine HasDerivAt.congr_deriv ((exp_deriv s v).mul (affine_deriv_neg s v)) ?_
  field_simp
  abel

private theorem exp_cont (s : ℂ) :
    Continuous (fun x : ℝ => Complex.exp (s * (x : ℂ))) :=
  Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)

private theorem vexp_cont (s : ℂ) :
    Continuous (fun x : ℝ => (x : ℂ) * Complex.exp (s * (x : ℂ))) :=
  Complex.continuous_ofReal.mul (exp_cont s)

private theorem nvexp_cont (s : ℂ) :
    Continuous (fun x : ℝ => -(x : ℂ) * Complex.exp (s * (x : ℂ))) :=
  (Complex.continuous_ofReal.neg).mul (exp_cont s)

/-- `∫_u^v e^{s x} = (e^{s v} - e^{s u}) / s` for `s ≠ 0`. -/
private theorem exp_integral (s : ℂ) (hs : s ≠ 0) (u v : ℝ) :
    (∫ x in u..v, Complex.exp (s * (x : ℂ))) =
      (Complex.exp (s * (v : ℂ)) - Complex.exp (s * (u : ℂ))) / s := by
  have hderiv : deriv (fun x : ℝ => Complex.exp (s * (x : ℂ)) * s⁻¹)
      = fun x : ℝ => Complex.exp (s * (x : ℂ)) := by
    funext x
    have h := ((exp_deriv s x).mul_const s⁻¹).deriv
    rw [mul_inv_cancel_right₀ hs] at h
    exact h
  rw [intervalIntegral.integral_deriv_eq_sub'
    (fun x : ℝ => Complex.exp (s * (x : ℂ)) * s⁻¹) hderiv
    (fun x _ => ((exp_deriv s x).mul_const s⁻¹).differentiableAt)
    (exp_cont s).continuousOn]
  rw [div_eq_mul_inv, sub_mul]

/-- `∫_u^v x·e^{s x}`. -/
private theorem vexp_integral (s : ℂ) (hs : s ≠ 0) (u v : ℝ) :
    (∫ x in u..v, ((x : ℂ) * Complex.exp (s * (x : ℂ)))) =
      Complex.exp (s * (v : ℂ)) * (s⁻¹ * (v : ℂ) - s⁻¹ * s⁻¹)
        - Complex.exp (s * (u : ℂ)) * (s⁻¹ * (u : ℂ) - s⁻¹ * s⁻¹) := by
  have hderiv : deriv (fun x : ℝ => Complex.exp (s * (x : ℂ)) * (s⁻¹ * (x : ℂ) - s⁻¹ * s⁻¹))
      = fun x : ℝ => (x : ℂ) * Complex.exp (s * (x : ℂ)) := by
    funext x
    exact (vexp_deriv s hs x).deriv
  rw [intervalIntegral.integral_deriv_eq_sub'
    (fun x : ℝ => Complex.exp (s * (x : ℂ)) * (s⁻¹ * (x : ℂ) - s⁻¹ * s⁻¹)) hderiv
    (fun x _ => (vexp_deriv s hs x).differentiableAt)
    (vexp_cont s).continuousOn]

/-- `∫_u^v (-x)·e^{s x}`. -/
private theorem nvexp_integral (s : ℂ) (hs : s ≠ 0) (u v : ℝ) :
    (∫ x in u..v, (-(x : ℂ) * Complex.exp (s * (x : ℂ)))) =
      Complex.exp (s * (v : ℂ)) * ((-s⁻¹) * (v : ℂ) + s⁻¹ * s⁻¹)
        - Complex.exp (s * (u : ℂ)) * ((-s⁻¹) * (u : ℂ) + s⁻¹ * s⁻¹) := by
  have hderiv : deriv (fun x : ℝ => Complex.exp (s * (x : ℂ)) * ((-s⁻¹) * (x : ℂ) + s⁻¹ * s⁻¹))
      = fun x : ℝ => -(x : ℂ) * Complex.exp (s * (x : ℂ)) := by
    funext x
    exact (nvexp_deriv s hs x).deriv
  rw [intervalIntegral.integral_deriv_eq_sub'
    (fun x : ℝ => Complex.exp (s * (x : ℂ)) * ((-s⁻¹) * (x : ℂ) + s⁻¹ * s⁻¹)) hderiv
    (fun x _ => (nvexp_deriv s hs x).differentiableAt)
    (nvexp_cont s).continuousOn]

/-- The half-angle square identity. -/
private theorem sq_half_angle (s : ℂ) (δ : ℝ) :
    (Complex.exp (s * ((δ / 2 : ℝ) : ℂ)) - Complex.exp (-(s * ((δ / 2 : ℝ) : ℂ)))) ^ 2
      = Complex.exp (s * (δ : ℂ)) + Complex.exp (-(s * (δ : ℂ))) - 2 := by
  set x : ℂ := s * ((δ / 2 : ℝ) : ℂ) with hx
  have hxx : x + x = s * (δ : ℂ) := by
    rw [hx, ← mul_add, ← Complex.ofReal_add]
    congr 1
    norm_num
  have hp : Complex.exp x * Complex.exp x = Complex.exp (s * (δ : ℂ)) := by
    rw [← Complex.exp_add, hxx]
  have hq : Complex.exp (-x) * Complex.exp (-x) = Complex.exp (-(s * (δ : ℂ))) := by
    rw [← Complex.exp_add, ← neg_add, ← hxx]
  have h0 : Complex.exp x * Complex.exp (-x) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  have h0r : Complex.exp (-x) * Complex.exp x = 1 := by
    rw [mul_comm]
    exact h0
  rw [sq, sub_mul, mul_sub, mul_sub, h0, hp, hq, h0r]
  push_cast
  ring


