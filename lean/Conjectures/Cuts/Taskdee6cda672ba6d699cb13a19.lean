import Mathlib

/-- The weight factor stays positive on non-degenerate intervals: for `x1 ≥ 1` the radical
`√(2 x1)` is positive because `2 x1 ≥ 2 > 0`, and `log (2 + 2 x1)` is positive because
`2 + 2 x1 ≥ 4 > 1`; a product of two positive reals is positive. -/
theorem Conjectures.Cuts.Taskdee6cda672ba6d699cb13a19 :
    ∀ (x1 : ℕ), (1 : ℕ) ≤ x1 → (0 : ℝ) < √((2 : ℝ) * ↑x1) * Real.log ((2 : ℝ) + (2 : ℝ) * ↑x1) := by
  intro x1 hx1
  have hx1r : (1 : ℝ) ≤ (x1 : ℝ) := by exact_mod_cast hx1
  have hrad : (0 : ℝ) < (2 : ℝ) * (x1 : ℝ) := by nlinarith
  have hsqrt : (0 : ℝ) < √((2 : ℝ) * (x1 : ℝ)) := Real.sqrt_pos.mpr hrad
  have harg : (1 : ℝ) < (2 : ℝ) + (2 : ℝ) * (x1 : ℝ) := by nlinarith
  have hlog : (0 : ℝ) < Real.log ((2 : ℝ) + (2 : ℝ) * (x1 : ℝ)) := Real.log_pos harg
  exact mul_pos hsqrt hlog
