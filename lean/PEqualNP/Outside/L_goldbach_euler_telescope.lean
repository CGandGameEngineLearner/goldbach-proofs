import Mathlib

theorem PEqualNP.Outside.L_goldbach_euler_telescope :
    ∀ m : ℕ, Finset.prod (Finset.range m) (fun j => 1-1/((j:ℝ)+2)^2) = ((m:ℝ)+2)/(2*((m:ℝ)+1)) := by
  intro m
  induction m with
  | zero => norm_num
  | succ m ih =>
    rw [Finset.prod_range_succ, ih]
    have h1 : ((m:ℝ)+1) ≠ 0 := by positivity
    have h2 : ((m:ℝ)+2) ≠ 0 := by positivity
    have h3 : ((m:ℝ)+2)^2 ≠ 0 := by positivity
    push_cast
    field_simp
    ring
