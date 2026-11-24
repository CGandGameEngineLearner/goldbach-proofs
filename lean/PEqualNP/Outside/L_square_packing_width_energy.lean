import Mathlib

theorem PEqualNP.Outside.L_square_packing_width_energy :
    ∀ c s:ℝ,c^2+s^2=1 → (|c|+|s|)^2≤2 := by
  intro c s h
  have hsq : (|c| + |s|)^2 = c^2 + s^2 + 2*|c|*|s| := by
    rw [add_sq, sq_abs, sq_abs]
    ring
  rw [hsq]
  nlinarith [h, sq_nonneg (|c| - |s|), sq_abs c, sq_abs s, mul_nonneg (abs_nonneg c) (abs_nonneg s)]
