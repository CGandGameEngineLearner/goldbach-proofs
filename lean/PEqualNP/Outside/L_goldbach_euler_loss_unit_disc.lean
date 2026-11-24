import Mathlib

theorem PEqualNP.Outside.L_goldbach_euler_loss_unit_disc :
    ∀ z : ℂ, ‖z‖<1 → 1-z≠0 := by
  intro z hz h
  rw [sub_eq_zero.mp h] at hz
  rw [Complex.norm_eq_abs, Complex.abs_one] at hz
  exact lt_irrefl 1 hz
