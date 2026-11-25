import Mathlib

theorem PEqualNP.Outside.L_no_three_in_line_determinant_translation :
    ∀ (ax ay bx by cx cy tx ty : ℤ), ((bx + tx) - (ax + tx)) * ((cy + ty) - (ay + ty)) - ((by + ty) - (ay + ty)) * ((cx + tx) - (ax + tx)) = (bx - ax) * (cy - ay) - (by - ay) * (cx - ax) := by
  intro ax ay bx by cx cy tx ty
  ring
