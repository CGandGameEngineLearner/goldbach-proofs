import Mathlib

theorem PEqualNP.Outside.L_goldbach_euler_loss_unit_disc :
    ∀ z : ℂ, ‖z‖<1 → 1-z≠0 := by
  intro z hz h
  have h1 : z = 1 := (sub_eq_zero.mp h).symm
  rw [h1, Complex.norm_one] at hz
  exact lt_irrefl 1 hz
