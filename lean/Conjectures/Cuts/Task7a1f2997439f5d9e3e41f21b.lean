import Mathlib

theorem Conjectures.Cuts.Task7a1f2997439f5d9e3e41f21b :
    ∀ (x1 : ℕ), (0 : ℕ) < {x2 ∈ (Finset.range (x1 + (1 : ℕ))).product (Fintype.piFinset fun (x2 : Fin (5 : ℕ)) => Finset.range (x1 + (1 : ℕ))) | Nat.Prime x2.1 ∧ Nat.Prime (x1 - (x2.1 + ∑ x3 : Fin (5 : ℕ), (2 : ℕ) ^ (x2.2 x3 + (1 : ℕ))))}.card → ∃ (x3 : ℕ) (x4 : ℕ), Nat.Prime x3 ∧ Nat.Prime x4 ∧ ∃ (x5 : Fin (5 : ℕ) → ℕ), x1 = x3 + x4 + ∑ x6 : Fin (5 : ℕ), (2 : ℕ) ^ (x5 x6 + (1 : ℕ)) := by
  intro x1 h
  obtain ⟨x2, hx2⟩ := Finset.card_pos.mp h
  obtain ⟨-, hp, hq⟩ := Finset.mem_filter.mp hx2
  refine ⟨x2.1, x1 - (x2.1 + ∑ i : Fin 5, 2 ^ (x2.2 i + 1)), hp, hq, x2.2, ?_⟩
  have h2 : 2 ≤ x1 - (x2.1 + ∑ i : Fin 5, 2 ^ (x2.2 i + 1)) := hq.two_le
  omega
