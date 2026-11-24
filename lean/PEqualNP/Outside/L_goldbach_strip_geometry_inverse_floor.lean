import Mathlib

/-!
# L-goldbach-strip-geometry-inverse-floor

On the critical line `re s = 1/2` the point `s` has modulus at least `1/2`, hence its
inverse has modulus at most `2`: `‖s⁻¹‖ ≤ 2`.  This bounds the denominator in the
functional-equation reflection, transplanted from the Riemann hypothesis
formalization (`ClaimStrip`).
-/

theorem PEqualNP.Outside.L_goldbach_strip_geometry_inverse_floor :
    ∀ s : ℂ, s.re=1/2 → ‖s⁻¹‖≤2 := by
  intro s hs
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hs
    simp at hs
  have hsq : (1/2:ℝ)^2 ≤ ‖s‖^2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hs]
    nlinarith [sq_nonneg s.im]
  have hnn : 0 ≤ ‖s‖ := norm_nonneg s
  have hnorm : (1/2:ℝ) ≤ ‖s‖ := by nlinarith
  rw [norm_inv, inv_eq_one_div, div_le_iff₀ (norm_pos_iff.mpr hs0)]
  linarith
