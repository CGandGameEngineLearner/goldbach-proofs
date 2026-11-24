import Mathlib

/-- The reflected residue adds back to the target residue.
The offset by q ensures that the natural-number subtraction does not truncate. -/
theorem PEqualNP.Outside.L_goldbach_residue_blocks_opposite_phase :
    ∀ (q a n : ℕ), 0<q → a<q → ((n+q-a)%q+a)%q=n % q := by
  intro q a n _hq ha
  have hle : a ≤ n + q := by omega
  calc
    ((n + q - a) % q + a) % q
        = (((n + q - a) % q) % q + a % q) % q := Nat.add_mod _ _ _
    _ = ((n + q - a) % q + a % q) % q := by rw [Nat.mod_mod]
    _ = ((n + q - a) + a) % q := (Nat.add_mod _ _ _).symm
    _ = (n + q) % q := by rw [Nat.sub_add_cancel hle]
    _ = n % q := Nat.add_mod_right n q
