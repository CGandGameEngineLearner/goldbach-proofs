import Mathlib

/-!
# L-goldbach-euler-loss-inv-loss

The tail of the geometric expansion of `(1-z)⁻¹`: when the disc of radius `r < 1`
holds `z`, the first omitted term bounds the whole remainder, `r / (1 - r)`.
-/

theorem PEqualNP.Outside.L_goldbach_euler_loss_inv_loss :
    ∀ (z : ℂ) (r : ℝ), ‖z‖≤r → r<1 → ‖(1-z)⁻¹-1‖≤r/(1-r) := by
  intro z r hz hr
  have h1 : (1:ℝ) - r ≤ ‖(1:ℂ) - z‖ := by
    have h2 := norm_sub_norm_le (1:ℂ) z
    rw [norm_one] at h2
    exact le_trans (sub_le_sub (le_refl (1:ℝ)) hz) h2
  have hrpos : 0 < 1 - r := by linarith
  have hrnn : 0 ≤ r := le_trans (norm_nonneg z) hz
  have hpos : 0 < ‖(1:ℂ) - z‖ := lt_of_lt_of_le hrpos h1
  have hne : (1:ℂ) - z ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hpos
    exact LT.lt.false hpos
  have hEq : ((1:ℂ) - z)⁻¹ - 1 = z * ((1:ℂ) - z)⁻¹ := by
    field_simp [hne]
    ring
  have key : ‖z‖ * ((1:ℝ) - r) ≤ r * ‖(1:ℂ) - z‖ :=
    calc ‖z‖ * ((1:ℝ) - r) ≤ r * ((1:ℝ) - r) :=
          mul_le_mul_of_nonneg_right hz hrpos.le
    _ ≤ r * ‖(1:ℂ) - z‖ := mul_le_mul_of_nonneg_left h1 hrnn
  rw [hEq, norm_mul, norm_inv, ← div_eq_mul_inv, div_le_div_iff₀ hpos hrpos]
  exact key
