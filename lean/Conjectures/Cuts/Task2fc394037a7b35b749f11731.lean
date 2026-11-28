import Mathlib

namespace Conjectures.Cuts

theorem Task2fc394037a7b35b749f11731 :
    ∀ (x1 x2 x3 : ℝ), (0 : ℝ) < x1 → (0 : ℝ) ≤ x2 → (0 : ℝ) ≤ x3 →
      x1 / (2 : ℝ) * x2 * x3 ≤ x1 * x2 * x3 := by
  intro x1 x2 x3 hx1 hx2 hx3
  have hprod : (0 : ℝ) ≤ x1 * x2 * x3 := mul_nonneg (mul_nonneg hx1.le hx2) hx3
  have hrewrite : x1 / (2 : ℝ) * x2 * x3 = (1 / 2 : ℝ) * (x1 * x2 * x3) := by ring
  rw [hrewrite]
  linarith

end Conjectures.Cuts
