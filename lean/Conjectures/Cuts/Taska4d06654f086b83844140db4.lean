import Mathlib

theorem Conjectures.Cuts.Taska4d06654f086b83844140db4 : (∀ (x1 : ℕ), (0 : ℝ) < ↑{x2 ∈ (Finset.range (x1 + (1 : ℕ))).product (Fintype.piFinset fun (x2 : Fin (13 : ℕ)) => Finset.range (x1 + (1 : ℕ))) | Nat.Prime x2.1 ∧ Nat.Prime (x1 - (x2.1 + ∑ x3 : Fin (13 : ℕ), (2 : ℕ) ^ (x2.2 x3 + (1 : ℕ))))}.card → ∃ (x3 : ℕ) (x4 : ℕ) (x5 : Fin (13 : ℕ) → ℕ), Nat.Prime x3 ∧ Nat.Prime x4 ∧ x1 = x3 + x4 + ∑ x6 : Fin (13 : ℕ), (2 : ℕ) ^ (x5 x6 + (1 : ℕ))) := by
  intro x1 h
  classical
  obtain ⟨pa, hpa⟩ := Finset.card_pos.mp (Nat.cast_pos.mp h)
  simp only [Finset.mem_filter] at hpa
  obtain ⟨-, hp, hq⟩ := hpa
  refine ⟨pa.1, x1 - (pa.1 + ∑ j : Fin 13, 2 ^ (pa.2 j + 1)), pa.2, hp, hq, ?_⟩
  have hq2 : 2 ≤ x1 - (pa.1 + ∑ j : Fin 13, 2 ^ (pa.2 j + 1)) := hq.two_le
  omega
