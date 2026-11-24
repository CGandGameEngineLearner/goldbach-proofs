import Mathlib

theorem PEqualNP.Outside.L_goldbach_harmonic_integral :
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); ∀ m : ℤ, intervalIntegral (fun t => E ((m:ℝ)*t)) (0:ℝ) 1 MeasureTheory.volume = if m=0 then 1 else 0 := by
  intro E m
  by_cases hm : m = 0
  · subst hm
    have hconst : (fun t : ℝ => E ((↑(0:ℤ) : ℝ) * t)) = (fun _ => (1:ℂ)) := by
      funext t
      simp [E]
    rw [hconst, intervalIntegral.integral_const]
    simp
  · have hc : ((m : ℂ) * (2 * Real.pi * Complex.I)) ≠ 0 := by
      apply mul_ne_zero
      · exact_mod_cast hm
      · exact Complex.two_pi_I_ne_zero
    have hrew : ∀ t : ℝ,
        E ((m : ℝ) * t) = Complex.exp (((m : ℂ) * (2 * Real.pi * Complex.I)) * (t : ℂ)) := by
      intro t
      simp only [E]
      push_cast
      ring
    rw [show (fun t : ℝ => E ((m : ℝ) * t))
          = (fun t : ℝ => Complex.exp (((m : ℂ) * (2 * Real.pi * Complex.I)) * (t : ℂ)))
        from funext hrew]
    rw [integral_exp_mul_complex hc]
    have hexp : Complex.exp (((m : ℂ) * (2 * Real.pi * Complex.I)) * ((1:ℝ):ℂ)) = 1 := by
      rw [show ((m : ℂ) * (2 * Real.pi * Complex.I)) * ((1:ℝ):ℂ)
            = (m : ℂ) * (2 * Real.pi * Complex.I) from by push_cast; ring]
      simpa using Complex.exp_int_mul_two_pi_mul_I m
    have hexp0 : Complex.exp (((m : ℂ) * (2 * Real.pi * Complex.I)) * ((0:ℝ):ℂ)) = 1 := by
      rw [show ((0:ℝ):ℂ) = 0 from by norm_num, mul_zero, Complex.exp_zero]
    rw [hexp, hexp0, if_neg hm]
    simp
