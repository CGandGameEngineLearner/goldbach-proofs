import Mathlib

theorem PEqualNP.Outside.L_goldbach_cyclic_alias_free :
    ∀ n a b : ℕ, a≤n → b≤n → ((a + b) % (2*n+1) = n ↔ a+b=n) := by
  intro n a b ha hb
  have hle : a + b ≤ 2 * n := by omega
  constructor
  · intro h
    have h1 : a + b < 2 * n + 1 := by omega
    rwa [Nat.mod_eq_of_lt h1] at h
  · intro h
    rw [h]
    exact Nat.mod_eq_of_lt (by omega)
