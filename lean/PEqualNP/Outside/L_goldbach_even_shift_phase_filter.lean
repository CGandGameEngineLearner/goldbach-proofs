import Mathlib

private lemma exp_neg_sub_exp (a : ℝ) :
    Complex.exp (((-a : ℝ) : ℂ) * Complex.I) - Complex.exp (((a : ℝ) : ℂ) * Complex.I)
      = -(2:ℂ) * Complex.I * (Real.sin a : ℂ) := by
  rw [Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg]
  push_cast
  ring

private lemma geom_denom (a : ℝ) :
    Complex.exp (((-(2*a) : ℝ) : ℂ) * Complex.I) - 1
      = Complex.exp (((-a : ℝ) : ℂ) * Complex.I)
        * (Complex.exp (((-a : ℝ) : ℂ) * Complex.I) - Complex.exp (((a : ℝ) : ℂ) * Complex.I)) := by
  have hmul : Complex.exp (((-a : ℝ) : ℂ) * Complex.I) * Complex.exp (((-a : ℝ) : ℂ) * Complex.I)
      = Complex.exp (((-(2*a) : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hone : Complex.exp (((-a : ℝ) : ℂ) * Complex.I) * Complex.exp (((a : ℝ) : ℂ) * Complex.I) = 1 := by
    rw [← Complex.exp_add]
    have h : (((-a : ℝ) : ℂ) * Complex.I + ((a : ℝ) : ℂ) * Complex.I) = 0 := by push_cast; ring
    rw [h, Complex.exp_zero]
  rw [mul_sub, hmul, hone]

private lemma geom_denom_norm (a : ℝ) :
    ‖Complex.exp (((-(2*a) : ℝ) : ℂ) * Complex.I) - 1‖ = 2 * |Real.sin a| := by
  rw [geom_denom, exp_neg_sub_exp a]
  simp only [norm_mul]
  rw [Complex.norm_I, Complex.norm_exp_ofReal_mul_I, Complex.norm_real, Real.norm_eq_abs]
  norm_num

theorem PEqualNP.Outside.L_goldbach_even_shift_phase_filter :
    let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); ∀ (H : ℕ) (t : ℝ), 0<H → Real.sin (2*Real.pi*t) ≠ 0 → ‖(∑ j ∈ Finset.range H, E (-2*(j:ℝ)*t))/(H:ℂ)‖ ≤ min 1 (1/((H:ℝ)*|Real.sin (2*Real.pi*t)|)) := by
  dsimp only
  intro H t hH hsin
  have hHpos : (0:ℝ) < (H:ℝ) := by exact_mod_cast hH
  have hHne : (H:ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    exact Nat.pos_iff_ne_zero.mp hH
  have hsinabs : 0 < |Real.sin (2*Real.pi*t)| := abs_pos.mpr hsin
  -- each term is a power of the base `Z = exp (-2π·2t·i)`
  have hterm : ∀ j ∈ Finset.range H,
      Complex.exp ((((2*Real.pi*(-2*(j:ℝ)*t) : ℝ) : ℂ)) * Complex.I)
        = Complex.exp ((((2*Real.pi*(-2*t) : ℝ) : ℂ)) * Complex.I) ^ j := by
    intro j _
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [Finset.sum_congr rfl hterm]
  set Z : ℂ := Complex.exp ((((2*Real.pi*(-2*t) : ℝ) : ℂ)) * Complex.I) with hZ
  have hz : ‖Z‖ = 1 := by rw [hZ]; exact Complex.norm_exp_ofReal_mul_I _
  -- telescoping geometric identity
  have hgeom := geom_sum_mul Z H
  have hstep : ‖∑ j ∈ Finset.range H, Z ^ j‖ * ‖Z - 1‖ ≤ 2 := by
    have h1 : ‖(∑ j ∈ Finset.range H, Z ^ j) * (Z - 1)‖
        = ‖∑ j ∈ Finset.range H, Z ^ j‖ * ‖Z - 1‖ := norm_mul _ _
    rw [← h1, hgeom]
    calc ‖Z ^ H - 1‖ ≤ ‖Z ^ H‖ + ‖1‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, hz]; norm_num
  -- the key modulus identity ‖Z - 1‖ = 2|sin(2πt)|
  have hden : ‖Z - 1‖ = 2 * |Real.sin (2*Real.pi*t)| := by
    rw [hZ]
    have harg : (2*Real.pi*(-2*t) : ℝ) = -(2*(2*Real.pi*t)) := by ring
    rw [harg]
    exact geom_denom_norm (2*Real.pi*t)
  have hkey : ‖∑ j ∈ Finset.range H, Z ^ j‖ ≤ 1 / |Real.sin (2*Real.pi*t)| := by
    have h2 : ‖∑ j ∈ Finset.range H, Z ^ j‖ * (2 * |Real.sin (2*Real.pi*t)|) ≤ 2 := by
      rw [← hden]; exact hstep
    rw [le_div_iff₀ hsinabs]
    nlinarith [norm_nonneg (∑ j ∈ Finset.range H, Z ^ j)]
  -- bound 1/(H|sin|) and bound 1, take the min
  have hb1 : ‖(∑ j ∈ Finset.range H, Z ^ j) / (H:ℂ)‖
      ≤ 1 / ((H:ℝ) * |Real.sin (2*Real.pi*t)|) := by
    rw [norm_div, Complex.norm_natCast]
    calc ‖∑ j ∈ Finset.range H, Z ^ j‖ / (H:ℝ)
        ≤ (1 / |Real.sin (2*Real.pi*t)|) / (H:ℝ) :=
          div_le_div_of_nonneg_right hkey (le_of_lt hHpos)
      _ = 1 / ((H:ℝ) * |Real.sin (2*Real.pi*t)|) := by rw [div_div, mul_comm]
  have hb2 : ‖(∑ j ∈ Finset.range H, Z ^ j) / (H:ℂ)‖ ≤ 1 := by
    rw [norm_div, Complex.norm_natCast, div_le_one hHpos]
    have h1 : ‖∑ j ∈ Finset.range H, Z ^ j‖ ≤ ∑ j ∈ Finset.range H, ‖Z ^ j‖ := norm_sum_le _ _
    have h2 : ∑ j ∈ Finset.range H, ‖Z ^ j‖ = (H:ℝ) := by simp [norm_pow, hz]
    rwa [h2] at h1
  exact le_min hb2 hb1