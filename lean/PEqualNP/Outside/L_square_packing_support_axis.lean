import Mathlib

namespace PEqualNP.Outside

open scoped BigOperators

theorem L_square_packing_support_axis :
    ∀ A B u v:ℝ, abs u < 1/2 → abs v < 1/2 → 0 < abs A + abs B → abs (A*u+B*v) < (abs A + abs B)/2 := by
  intro A B u v hu hv hpos
  have h1 : abs (A*u+B*v) ≤ abs (A*u) + abs (B*v) := abs_add_le (A*u) (B*v)
  rw [abs_mul, abs_mul] at h1
  have hA : 0 ≤ abs A := abs_nonneg A
  have hB : 0 ≤ abs B := abs_nonneg B
  by_cases hA0 : abs A = 0
  · have hBpos : 0 < abs B := by linarith
    have hBv : abs B * abs v < abs B * (1/2) :=
      mul_lt_mul_of_pos_left hv hBpos
    have hAu : abs A * abs u = 0 := by rw [hA0, zero_mul]
    linarith
  · have hApos : 0 < abs A := by
      apply lt_of_le_of_ne hA
      intro h
      exact hA0 h.symm
    have hAu : abs A * abs u < abs A * (1/2) :=
      mul_lt_mul_of_pos_left hu hApos
    have hBv : abs B * abs v ≤ abs B * (1/2) :=
      mul_le_mul_of_nonneg_left (le_of_lt hv) hB
    linarith

end PEqualNP.Outside