import Mathlib

theorem PEqualNP.Outside.L_goldbach_even_shift_phase_filter :
    let w := fun k : ℕ => if Nat.Prime k then Real.log (k : ℝ) else 0
    let E := fun x : ℝ => Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)
    ∀ (H : ℕ) (t : ℝ), 0 < H → Real.sin (2 * Real.pi * t) ≠ 0 →
      ‖(∑ j ∈ Finset.range H, E (-2 * (j : ℝ) * t)) / (H : ℂ)‖
        ≤ min 1 (1 / ((H : ℝ) * |Real.sin (2 * Real.pi * t)|)) := by
  intro w E H t hH hsin
  have hsin_abs : |Real.sin (2 * Real.pi * t)| ≠ 0 := abs_ne_zero.mpr hsin
  set z : ℂ := E (-2 * t) with hz
  have hz_norm : ‖z‖ = 1 := by
    rw [hz]
    simp only [E]
    exact Complex.norm_exp_ofReal_mul_I _
  have hz_sub : ‖z - 1‖ = 2 * |Real.sin (2 * Real.pi * t)| := by
    have harg : E (-2 * t) = Complex.exp (Complex.I * ((-(4 * Real.pi * t) : ℝ) : ℂ)) := by
      simp only [E]
      congr 1
      push_cast
      ring
    rw [hz, harg, Complex.norm_exp_I_mul_ofReal_sub_one]
    have hx : (-(4 * Real.pi * t) : ℝ) / 2 = -(2 * Real.pi * t) := by ring
    rw [hx, Real.sin_neg, Real.norm_eq_abs, abs_mul, abs_two, abs_neg]
  have hz_ne : z ≠ 1 := by
    intro h
    have h0 : ‖z - 1‖ = 0 := by simp [h]
    rw [hz_sub] at h0
    have hzero : 2 * |Real.sin (2 * Real.pi * t)| = 0 := by linarith
    exact (mul_ne_zero (by norm_num) hsin_abs) hzero
  have hsum : (∑ j ∈ Finset.range H, E (-2 * (j : ℝ) * t)) = ∑ j ∈ Finset.range H, z ^ j := by
    refine Finset.sum_congr rfl ?_
    intro j _
    have hstep : (((2 * Real.pi * (-2 * (j : ℝ) * t) : ℝ) : ℂ) * Complex.I)
        = (j : ℂ) * ((((2 * Real.pi * (-2 * t) : ℝ) : ℂ)) * Complex.I) := by
      push_cast
      ring
    calc E (-2 * (j : ℝ) * t)
        = Complex.exp (((2 * Real.pi * (-2 * (j : ℝ) * t) : ℝ) : ℂ) * Complex.I) := by
            simp only [E]
      _ = Complex.exp ((j : ℂ) * ((((2 * Real.pi * (-2 * t) : ℝ) : ℂ)) * Complex.I)) := by
            rw [hstep]
      _ = (Complex.exp ((((2 * Real.pi * (-2 * t) : ℝ) : ℂ)) * Complex.I)) ^ j :=
            Complex.exp_nat_mul _ j
      _ = z ^ j := by rw [hz]
  have hgeom : (∑ j ∈ Finset.range H, z ^ j) = (z ^ H - 1) / (z - 1) :=
    geom_sum_eq (x := z) hz_ne H
  have htri : ‖∑ j ∈ Finset.range H, z ^ j‖ ≤ (H : ℝ) := by
    calc ‖∑ j ∈ Finset.range H, z ^ j‖ ≤ ∑ j ∈ Finset.range H, ‖z ^ j‖ :=
          norm_sum_le _ _
      _ = ∑ j ∈ Finset.range H, (1 : ℝ) := by
            refine Finset.sum_congr rfl ?_
            intro j _
            rw [norm_pow, hz_norm, one_pow]
      _ = (H : ℝ) := by simp
  have hchord : ‖∑ j ∈ Finset.range H, z ^ j‖ ≤ 1 / |Real.sin (2 * Real.pi * t)| := by
    have hnum : ‖z ^ H - 1‖ ≤ 2 := by
      calc ‖z ^ H - 1‖ ≤ ‖z ^ H‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 2 := by rw [norm_pow, hz_norm, one_pow]; norm_num
    rw [hgeom, norm_div, hz_sub]
    calc ‖z ^ H - 1‖ / (2 * |Real.sin (2 * Real.pi * t)|)
        ≤ 2 / (2 * |Real.sin (2 * Real.pi * t)|) := by
          apply div_le_div_of_nonneg_right hnum
          positivity
      _ = 1 / |Real.sin (2 * Real.pi * t)| := by
          field_simp
  have hdiv : ‖(∑ j ∈ Finset.range H, E (-2 * (j : ℝ) * t)) / (H : ℂ)‖
      = ‖∑ j ∈ Finset.range H, z ^ j‖ / (H : ℝ) := by
    rw [hsum, norm_div, Complex.norm_natCast]
  rw [hdiv]
  apply le_min
  · calc ‖∑ j ∈ Finset.range H, z ^ j‖ / (H : ℝ) ≤ (H : ℝ) / (H : ℝ) := by
          gcongr
      _ = 1 := by field_simp
  · calc ‖∑ j ∈ Finset.range H, z ^ j‖ / (H : ℝ)
        ≤ (1 / |Real.sin (2 * Real.pi * t)|) / (H : ℝ) := by gcongr
      _ = 1 / ((H : ℝ) * |Real.sin (2 * Real.pi * t)|) := by
          field_simp
