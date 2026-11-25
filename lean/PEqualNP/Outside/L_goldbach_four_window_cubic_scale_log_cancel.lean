import Mathlib

/-!
# Exact cancellation of the logarithmic diagonal baseline

Write `X / 4 = (X / 2) / 2` and `X / 8 = (X / 4) / 2`, so that each logarithm is the previous one minus `log 2`: `log (X / 2^j) = log X - j * log 2` for `j = 1, 2, 3`.  The affine expressions `a * log (X / 2^j) + b` are then combined with the binomial coefficients `1, -3, 3, -1`, which annihilate both the constant `b` and the linear-in-`j` part.
-/

theorem PEqualNP.Outside.L_goldbach_four_window_cubic_scale_log_cancel :
    ∀ X a b : ℝ, 0 < X → (a*Real.log X+b)-3*(a*Real.log (X/2)+b)+3*(a*Real.log (X/4)+b)-(a*Real.log (X/8)+b)=0 := by
  intro X a b hX
  have hX0 : X ≠ 0 := ne_of_gt hX
  have h2 : (2:ℝ) ≠ 0 := by norm_num
  have hX2 : X/2 ≠ 0 := by positivity
  have hX4 : X/4 ≠ 0 := by positivity
  have e2 : Real.log (X/2) = Real.log X - Real.log 2 := Real.log_div hX0 h2
  have e4 : Real.log (X/4) = Real.log (X/2) - Real.log 2 := by
    rw [show X/4 = X/2/2 from by ring]
    exact Real.log_div hX2 h2
  have e8 : Real.log (X/8) = Real.log (X/4) - Real.log 2 := by
    rw [show X/8 = X/4/2 from by ring]
    exact Real.log_div hX4 h2
  rw [e8, e4, e2]
  ring
