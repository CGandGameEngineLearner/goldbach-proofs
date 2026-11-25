import Mathlib

/-- The unit-circle chord bound applied to the frequency difference `(a - b) * x`. -/
theorem PEqualNP.Outside.L_goldbach_height_near_phase :
    ∀ a b x : ℝ, ‖Complex.exp ((((a-b)*x : ℝ) : ℂ)*Complex.I)-1‖ ≤ |a-b| * |x| := by
  intro a b x
  calc
    ‖Complex.exp ((((a-b)*x : ℝ) : ℂ)*Complex.I)-1‖ ≤ ‖(a-b)*x‖ := by
      simpa only [mul_comm] using
        (Real.norm_exp_I_mul_ofReal_sub_one_le (x := (a-b)*x))
    _ = |a-b| * |x| := by rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
