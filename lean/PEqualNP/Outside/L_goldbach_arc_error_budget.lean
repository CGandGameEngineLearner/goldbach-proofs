import Mathlib

theorem PEqualNP.Outside.L_goldbach_arc_error_budget :
    ∀ M A B e h : ℝ, |A-M|≤e → -h≤B → e+h<M → 0<A+B := by
  intro M A B e h hAM hB hsum
  have h1 := (abs_le.mp hAM).1
  linarith
