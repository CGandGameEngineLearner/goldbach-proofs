import Mathlib

theorem PEqualNP.Outside.L_goldbach_coverage_0004_0010 :
    ∀ n : ℕ, 4 ≤ n → n ≤ 10 → Even n → (∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n) := by
  intro n hlo hhi heven
  obtain ⟨k, hk⟩ := heven
  have cases_n : n = 4 ∨ n = 6 ∨ n = 8 ∨ n = 10 := by omega
  rcases cases_n with h | h | h | h <;> rw [h]
  · exact ⟨2, 2, by decide, by decide, rfl⟩
  · exact ⟨3, 3, by decide, by decide, rfl⟩
  · exact ⟨3, 5, by decide, by decide, rfl⟩
  · exact ⟨3, 7, by decide, by decide, rfl⟩
