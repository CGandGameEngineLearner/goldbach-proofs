import Mathlib

theorem PEqualNP.Outside.L_goldbach_arc_error_budget :
    ∀ M A B e h : ℝ, |A-M|≤e → -h≤B → e+h<M → 0<A+B := by
  intro M A B e h hA hB hbudget
  have hA_lower := (abs_le.mp hA).1
  linarith
