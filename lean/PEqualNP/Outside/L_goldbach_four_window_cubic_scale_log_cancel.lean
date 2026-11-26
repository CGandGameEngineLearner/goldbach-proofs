import Mathlib

theorem PEqualNP.Outside.L_goldbach_four_window_cubic_scale_log_cancel :
    ∀ X a b : ℝ, 0 < X → (a*Real.log X+b)-3*(a*Real.log (X/2)+b)+3*(a*Real.log (X/4)+b)-(a*Real.log (X/8)+b)=0 := by
  intro X a b hX
  have h2 : Real.log (X / 2) = Real.log X - Real.log 2 := by
    rw [Real.log_div (ne_of_gt hX) (by norm_num : (2:ℝ) ≠ 0)]
  have h4 : Real.log (X / 4) = Real.log X - 2 * Real.log 2 := by
    rw [Real.log_div (ne_of_gt hX) (by norm_num : (4:ℝ) ≠ 0)]
    rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast
    ring
  have h8 : Real.log (X / 8) = Real.log X - 3 * Real.log 2 := by
    rw [Real.log_div (ne_of_gt hX) (by norm_num : (8:ℝ) ≠ 0)]
    rw [show (8:ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    push_cast
    ring
  rw [h2, h4, h8]
  ring
