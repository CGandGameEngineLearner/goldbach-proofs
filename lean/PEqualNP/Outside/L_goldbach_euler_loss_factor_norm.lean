import Mathlib

namespace PEqualNP.Outside

/-- A single Euler factor `1 - z` is bounded below by `1 - ‖z‖`. -/
theorem L_goldbach_euler_loss_factor_norm : ∀ z : ℂ, 1 - ‖z‖ ≤ ‖1 - z‖ := by
  intro z
  simpa using norm_sub_norm_le (1 : ℂ) z

end PEqualNP.Outside
