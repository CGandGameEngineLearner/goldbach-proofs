import Mathlib

theorem PEqualNP.Outside.L_goldbach_primitive_zero_window_increment :
    ∀ (u v : ℝ) (ρ : ℂ), 1 ≤ u → u ≤ v → 0 ≤ ρ.re → ρ ≠ 0 →
      ‖((v : ℂ)^ρ - (u : ℂ)^ρ)/ρ‖ ≤ v^ρ.re * min (Real.log (v/u)) (2/‖ρ‖) := by
  intro u v ρ hu huv hσ hρ
  have hu' : 0 < u := by linarith
  have hv : 0 < v := hu'.trans_le huv
  have hlog := Real.log_le_log hu' huv
  rw [mul_min_of_nonneg _ _ (Real.rpow_nonneg hv.le _)]
  apply le_min
  · -- Logarithmic coordinates make the derivative exactly exp(tρ).
    let F := fun t : ℝ => Complex.exp ((t : ℂ)*ρ)/ρ
    have derivF (t : ℝ) : HasDerivAt F (Complex.exp ((t : ℂ)*ρ)) t := by
      simpa [F, hρ] using
        (((hasDerivAt_id (t : ℂ)).mul_const ρ).cexp.div_const ρ).comp_ofReal
    have bound (t : ℝ) (ht : t ∈ Set.Ico (Real.log u) (Real.log v)) :
        ‖Complex.exp ((t : ℂ)*ρ)‖ ≤ v^ρ.re := by
      rw [Complex.norm_exp, Real.rpow_def_of_pos hv]
      apply Real.exp_le_exp.mpr
      simpa using mul_le_mul_of_nonneg_right ht.2.le hσ
    have h := norm_image_sub_le_of_norm_deriv_le_segment'
      (fun t _ => (derivF t).hasDerivWithinAt) bound _ (Set.right_mem_Icc.mpr hlog)
    have endpoint (x : ℝ) (hx : 0 < x) : F (Real.log x) = (x : ℂ)^ρ/ρ := by
      rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'), ← Complex.ofReal_log hx.le]
    rwa [endpoint v hv, endpoint u hu', ← sub_div, ← Real.log_div hv.ne' hu'.ne'] at h
  · rw [norm_div]
    calc
      _ ≤ (‖(v:ℂ)^ρ‖ + ‖(u:ℂ)^ρ‖)/‖ρ‖ :=
        div_le_div_of_nonneg_right (norm_sub_le ..) (norm_nonneg ρ)
      _ ≤ (v^ρ.re + v^ρ.re)/‖ρ‖ := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hv, Complex.norm_cpow_eq_rpow_re_of_pos hu']
        gcongr
      _ = _ := by ring
