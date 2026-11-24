import Mathlib

theorem PEqualNP.Outside.L_goldbach_offset_cost :
    ∀ X h : ℝ, 0≤h → intervalIntegral (fun t : ℝ => (1+X*t)^2) (0:ℝ) h MeasureTheory.volume=h+X*h^2+X^2*h^3/3 := by
  intro X h _
  have deriv (t : ℝ) : HasDerivAt (fun x : ℝ => x + X*x^2 + X^2*x^3/3) ((1 + X*t)^2) t := by
    have ht := hasDerivAt_id t
    convert (ht.add ((ht.pow 2).const_mul X)).add (((ht.pow 3).const_mul (X^2)).div_const 3) using 1
    · ext x
      simp [id]
    · simp [id]
      ring
  have value := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := h) (fun t _ => deriv t)
    ((by fun_prop : Continuous (fun t : ℝ => (1 + X * t)^2)).intervalIntegrable _ _)
  simpa using value
