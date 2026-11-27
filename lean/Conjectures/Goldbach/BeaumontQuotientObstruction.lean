import Mathlib

theorem Conjectures.Goldbach.BeaumontQuotientObstruction :
    ∀ m : ℕ, 1 < m → ∃ a b : ℕ, a ≠ b ∧ a % m = b % m ∧ Nat.Prime a ∧ ¬ Nat.Prime b := by
  intro m hm
  refine ⟨2, 2 + 2 * m, ?_, ?_, Nat.prime_two, ?_⟩
  · omega
  · rw [Nat.add_mul_mod_self_right]
  · intro hb
    have heven : Even (2 + 2 * m) := ⟨1 + m, by ring⟩
    rcases hb.eq_two_or_odd with h | h
    · omega
    · have hodd : Odd (2 + 2 * m) := by
        rw [Nat.odd_iff]
        exact h
      exact (Nat.not_even_iff_odd.mpr hodd) heven
