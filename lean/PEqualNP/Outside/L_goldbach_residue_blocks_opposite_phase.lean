import Mathlib

theorem PEqualNP.Outside.L_goldbach_residue_blocks_opposite_phase :
    ∀ (q a n : ℕ), 0 < q → a < q → ((n + q - a) % q + a) % q = n % q := by
  intro q a n _ ha
  rw [Nat.mod_add_mod,
    Nat.sub_add_cancel (show a ≤ n + q by omega),
    Nat.add_mod_right]