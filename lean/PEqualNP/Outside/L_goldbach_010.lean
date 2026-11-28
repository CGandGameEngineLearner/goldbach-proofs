import Mathlib

theorem PEqualNP.Outside.L_goldbach_010 : ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = 10 := by
  exact ⟨3, 7, by decide, by decide, rfl⟩
