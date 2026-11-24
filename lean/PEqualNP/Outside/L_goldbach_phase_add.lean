import Mathlib

theorem PEqualNP.Outside.L_goldbach_phase_add :
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); ∀ s t, E (s+t)=E s*E t := by
  change ∀ s t : ℝ, Complex.exp (((2 * Real.pi * (s + t) : ℝ) : ℂ) * Complex.I) =
    Complex.exp (((2 * Real.pi * s : ℝ) : ℂ) * Complex.I) *
      Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I)
  intro s t
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring
