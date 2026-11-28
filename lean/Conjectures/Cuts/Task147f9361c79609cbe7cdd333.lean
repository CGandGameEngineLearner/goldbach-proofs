import Mathlib.NumberTheory.Bertrand

theorem Conjectures.Cuts.Task147f9361c79609cbe7cdd333 :
∃ (x1 : ℕ), ∀ (x2 : ℕ), x1 ≤ x2 → Even x2 → ∃ (x5 : ℕ), Nat.Prime x5 ∧ (3 : ℕ) * x5 ≤ (2 : ℕ) * x2 ∧ (2 : ℕ) * x2 ≤ (6 : ℕ) * x5 := by
  refine ⟨3, ?_⟩
  intro n hn _
  obtain ⟨p, hp, hlo, hhi⟩ :=
    Nat.exists_prime_lt_and_le_two_mul (n / 3) (by omega)
  exact ⟨p, hp, by omega, by omega⟩
