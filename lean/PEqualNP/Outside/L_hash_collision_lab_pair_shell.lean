import Mathlib

theorem PEqualNP.Outside.L_hash_collision_lab_pair_shell :
    ∀ (m x y z : ℤ), x + y + z = 0 → (m + x) * (m + x - 1) + (m + y) * (m + y - 1) + (m + z) * (m + z - 1) = 3 * (m) * (m - 1) + 2 * (x ^ 2 + x * y + y ^ 2) := by
  intro m x y z h
  have hz : z = -(x + y) := by linarith
  rw [hz]
  ring
