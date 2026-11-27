import Mathlib

theorem Conjectures.JoshiAbc.FreyHeight :
    let h := fun (a b : ℕ) => Real.log ((a:ℝ)+b); ∀ a b : ℕ, 0 < a → 0 < b → 2*h a b + Real.log 12 ≤ Real.log (16*((a:ℝ)^2+a*b+(b:ℝ)^2)) := by
  show ∀ a b : ℕ, 0 < a → 0 < b →
    2 * Real.log ((a:ℝ) + b) + Real.log 12 ≤ Real.log (16 * ((a:ℝ)^2 + (a:ℝ)*b + (b:ℝ)^2))
  intro a b ha hb
  calc 2 * Real.log ((a:ℝ) + b) + Real.log 12
      = Real.log (((a:ℝ) + b)^2) + Real.log 12 := by rw [Real.log_pow]; push_cast; ring
    _ = Real.log (12 * ((a:ℝ) + b)^2) := by
        rw [Real.log_mul (by norm_num) (by positivity)]
        ring
    _ ≤ Real.log (16 * ((a:ℝ)^2 + (a:ℝ)*b + (b:ℝ)^2)) :=
        Real.log_le_log (by positivity) (by nlinarith [sq_nonneg ((a:ℝ) - b)])
