import Mathlib

theorem PEqualNP.Outside.L_goldbach_004 : ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = 4 := by
  exact ⟨2, 2, Nat.prime_two, Nat.prime_two, rfl⟩
