import Mathlib

theorem PEqualNP.Outside.L_goldbach_height_near_phase :
    ∀ a b x : ℝ, ‖Complex.exp ((((a-b)*x : ℝ) : ℂ)*Complex.I)-1‖ ≤ |a-b| * |x| := by
  intro a b x
  have h := Complex.norm_exp_I_mul_ofReal_sub_one ((a-b)*x)
  rw [show ((((a-b)*x : ℝ) : ℂ)*Complex.I) = Complex.I * (((a-b)*x : ℝ) : ℂ) from mul_comm _ _]
  rw [h]
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
  have h1 : |Real.sin (((a-b)*x)/2)| ≤ |((a-b)*x)/2| := Real.abs_sin_le_abs
  have h2 : |((a-b)*x)/2| = |a-b|*|x|/2 := by
    rw [abs_div, abs_mul]
    norm_num
  rw [h2] at h1
  linarith
