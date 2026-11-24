import Mathlib

theorem PEqualNP.Outside.L_hash_collision_lab_triple_shell :
    ∀ (m x y z : ℤ), x + y + z = 0 → (m + x) * (m + x - 1) * (m + x - 2) + (m + y) * (m + y - 1) * (m + y - 2) + (m + z) * (m + z - 1) * (m + z - 2) = 3 * (m) * (m - 1) * (m - 2) + 6 * (m - 1) * (x ^ 2 + x * y + y ^ 2) + 3 * x * y * z := by
  intro m x y z h
  have hz : z = -(x + y) := by linarith
  rw [hz]
  ring
