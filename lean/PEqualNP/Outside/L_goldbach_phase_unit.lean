import Mathlib

open Complex

theorem PEqualNP.Outside.L_goldbach_phase_unit :
    let E := fun x : ℝ => Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I);
    ∀ t, ‖E t‖ = 1 := by
  intro E t
  exact Complex.norm_exp_ofReal_mul_I (2 * Real.pi * t)
