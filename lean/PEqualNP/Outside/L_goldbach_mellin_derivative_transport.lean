import Mathlib

open MeasureTheory

theorem PEqualNP.Outside.L_goldbach_mellin_derivative_transport :
    let W := fun (F : ℝ → ℝ) (t : ℝ) => ∫ x : ℝ, (F x:ℂ)*Complex.exp (((t*x:ℝ):ℂ)*Complex.I); ∀ F : ℝ → ℝ, (∀ j : ℕ, ContDiff ℝ j F) → HasCompactSupport F → ∀ t : ℝ, W (deriv F) t = -((t:ℂ)*Complex.I)*W F t := by
  intro W F hsmooth hsupp t
  let c : ℂ := (t : ℂ) * Complex.I
  let phase (x : ℝ) := Complex.exp (((t*x : ℝ) : ℂ) * Complex.I)
  let f (x : ℝ) := (F x : ℂ)
  let fp (x : ℝ) := ((deriv F x : ℝ) : ℂ)
  have hphase : Continuous phase := by dsimp [phase]; fun_prop
  have hf : Continuous f := Complex.continuous_ofReal.comp (hsmooth 1).continuous
  have hfp : Continuous fp :=
    Complex.continuous_ofReal.comp ((hsmooth 1).continuous_deriv (by norm_num))
  have suppf : HasCompactSupport f := hsupp.comp_left Complex.ofReal_zero
  have suppfp : HasCompactSupport fp := hsupp.deriv.comp_left Complex.ofReal_zero
  have derivf (x : ℝ) : HasDerivAt f (fp x) x :=
    (((hsmooth 1).differentiable (by norm_num) x).hasDerivAt).ofReal_comp
  have derivphase (x : ℝ) : HasDerivAt phase (phase x * c) x := by
    have dt : HasDerivAt (fun y : ℝ => t*y) t x := by
      simpa using (hasDerivAt_id x).const_mul t
    exact (dt.ofReal_comp.mul_const Complex.I).cexp
  have hparts := integral_mul_deriv_eq_deriv_mul_of_integrable
    (fun x _ => derivf x) (fun x _ => derivphase x)
    ((hf.mul (hphase.mul continuous_const)).integrable_of_hasCompactSupport suppf.mul_right)
    ((hfp.mul hphase).integrable_of_hasCompactSupport suppfp.mul_right)
    ((hf.mul hphase).integrable_of_hasCompactSupport suppf.mul_right)
  change (∫ x, fp x * phase x) = -c * ∫ x, f x * phase x
  calc
    _ = -(∫ x, f x * (phase x * c)) := by
      simpa only [neg_neg] using (congrArg (fun z : ℂ => -z) hparts).symm
    _ = -(∫ x, c * (f x * phase x)) := by simp only [mul_comm c, mul_assoc]
    _ = _ := by rw [integral_const_mul, neg_mul]
