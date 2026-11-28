import Mathlib

theorem Conjectures.Cuts.Task091af1a2d9c2f24e05722ab7 :
    ∀ (x1 : ℝ), (0 : ℝ) < x1 → ∀ (x3 : ℕ), (0 : ℕ) < {x4 ∈ (Finset.range (x3 + (1 : ℕ))).product (Fintype.piFinset fun (x4 : Fin (6 : ℕ)) => Finset.range (x3 + (1 : ℕ))) | Nat.Prime x4.1 ∧ Nat.Prime (x3 - (x4.1 + ∑ x5 : Fin (6 : ℕ), (2 : ℕ) ^ (x4.2 x5 + (1 : ℕ)))) ∧ (↑(∑ x5 : Fin (6 : ℕ), (2 : ℕ) ^ (x4.2 x5 + (1 : ℕ))) : ℝ) ≤ (↑x3 : ℝ) ^ x1}.card → ∃ (x5 : ℕ) (x6 : ℕ), Nat.Prime x5 ∧ Nat.Prime x6 ∧ ∃ (x7 : Fin (6 : ℕ) → ℕ), x3 = x5 + x6 + ∑ x8 : Fin (6 : ℕ), (2 : ℕ) ^ (x7 x8 + (1 : ℕ)) ∧ (↑(∑ x8 : Fin (6 : ℕ), (2 : ℕ) ^ (x7 x8 + (1 : ℕ))) : ℝ) ≤ (↑x3 : ℝ) ^ x1 := by
  intro eps heps N h
  obtain ⟨x, hx⟩ := Finset.card_pos.mp h
  obtain ⟨-, hp, hq, hle⟩ := Finset.mem_filter.mp hx
  refine ⟨x.1, N - (x.1 + ∑ i : Fin 6, 2 ^ (x.2 i + 1)), hp, hq, x.2, ?_, ?_⟩
  · have h2 : 2 ≤ N - (x.1 + ∑ i : Fin 6, 2 ^ (x.2 i + 1)) := hq.two_le
    omega
  · exact hle
