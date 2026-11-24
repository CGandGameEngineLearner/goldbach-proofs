import Mathlib

theorem PEqualNP.Outside.L_goldbach_residue_blocks_opposite_phase :
    ∀ (q a n : ℕ), 0<q → a<q → ((n+q-a)%q+a)%q=n%q := by
  intro q a n hq ha
  have h1 : n + q - a + a = n + q := by omega
  calc ((n + q - a) % q + a) % q = ((n + q - a) + a) % q := Nat.mod_add_mod (n + q - a) q a
    _ = (n + q) % q := by rw [h1]
    _ = n % q := Nat.add_mod_right n q
