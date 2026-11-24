import Mathlib

/-!
# L-goldbach-euler-loss-unit-disc

A point strictly inside the unit disc stays away from `1`: `‖z‖ < 1` forces
`1 - z ≠ 0`.  This is the nonvanishing input to the Euler product loss accounting,
transplanted from the Riemann hypothesis formalization.
-/

theorem PEqualNP.Outside.L_goldbach_euler_loss_unit_disc :
    ∀ z : ℂ, ‖z‖<1 → 1-z≠0 := by
  intro z hz h
  rw [(sub_eq_zero.mp h).symm] at hz
  simp at hz
