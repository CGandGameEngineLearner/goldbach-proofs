import Mathlib

theorem Conjectures.Cuts.Taskb2a81abb2dd851a51d85cb0a :
    ∀ (x1 : ℝ), (0 : ℝ) < x1 → ∃ (x3 : ℝ), (0 : ℝ) < x3 ∧ ∃ (x4 : ℕ), ∀ (x5 : ℕ), x4 ≤ x5 → x3 * ↑x5 ≤ x1 * ↑x5 * Real.log ↑x5 := by
  intro x1 hx1
  refine ⟨x1 * Real.log 2, mul_pos hx1 (Real.log_pos (by norm_num)), 2, ?_⟩
  intro x5 hx5
  have hx5r : (2 : ℝ) ≤ (x5 : ℝ) := by exact_mod_cast hx5
  have hlog : Real.log 2 ≤ Real.log (x5 : ℝ) := Real.log_le_log (by norm_num) hx5r
  have hx5nn : (0 : ℝ) ≤ (x5 : ℝ) := Nat.cast_nonneg x5
  have hmul : x1 * Real.log 2 ≤ x1 * Real.log (x5 : ℝ) :=
    mul_le_mul_of_nonneg_left hlog (le_of_lt hx1)
  calc x1 * Real.log 2 * (x5 : ℝ) ≤ x1 * Real.log (x5 : ℝ) * (x5 : ℝ) :=
        mul_le_mul_of_nonneg_right hmul hx5nn
    _ = x1 * (x5 : ℝ) * Real.log (x5 : ℝ) := by ring
