import Mathlib

theorem PEqualNP.Outside.L_goldbach_four_window_folding_collision :
    ∀ (h g t : ℝ) (m : ℤ) (k : ℕ), h-g=2*Real.pi*(m:ℝ) → Complex.exp (Complex.I * ((((k:ℝ)+t)*h:ℝ):ℂ)) = Complex.exp (Complex.I * ((((k:ℝ)+t)*g:ℝ):ℂ)) * Complex.exp (Complex.I * ((2*Real.pi*(m:ℝ)*t:ℝ):ℂ)) := by
  intro h g t m k hhg
  have hh : h = g + 2*Real.pi*(m:ℝ) := by linarith
  have hreal : ((k:ℝ)+t)*h = ((k:ℝ)+t)*g + 2*Real.pi*(m:ℝ)*t + 2*Real.pi*((m:ℝ)*(k:ℝ)) := by
    rw [hh]
    ring
  rw [← Complex.exp_add, Complex.exp_eq_exp_iff_exists_int]
  refine ⟨m * (k : ℤ), ?_⟩
  have hR : Complex.I * ↑(((k:ℝ)+t)*g) + Complex.I * ↑(2*Real.pi*(m:ℝ)*t)
        + (↑(m * (k:ℤ)) : ℂ) * (2 * Real.pi * Complex.I)
      = Complex.I * ↑(((k:ℝ)+t)*g + 2*Real.pi*(m:ℝ)*t + 2*Real.pi*((m:ℝ)*(k:ℝ))) := by
    push_cast
    ring
  rw [hR, hreal]
