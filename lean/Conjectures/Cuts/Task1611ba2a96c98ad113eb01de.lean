import Mathlib

theorem Conjectures.Cuts.Task1611ba2a96c98ad113eb01de : (∀ (x1 : ℕ), (0 : ℝ) < ↑{x2 ∈ (Finset.range (x1 + (1 : ℕ))).product (Fintype.piFinset fun (x2 : Fin (6 : ℕ)) => Finset.range (x1 + (1 : ℕ))) | Nat.Prime x2.1 ∧ Nat.Prime (x1 - (x2.1 + ∑ x3 : Fin (6 : ℕ), (2 : ℕ) ^ (x2.2 x3 + (1 : ℕ))))}.card → ∃ (x3 : ℕ) (x4 : ℕ), Nat.Prime x3 ∧ Nat.Prime x4 ∧ ∃ (x5 : Fin (6 : ℕ) → ℕ), x1 = x3 + x4 + ∑ x6 : Fin (6 : ℕ), (2 : ℕ) ^ (x5 x6 + (1 : ℕ))) := by
  classical
  intro N h
  obtain ⟨⟨p, a⟩, hmem⟩ := Finset.card_pos.mp (Nat.cast_pos.mp h)
  obtain ⟨hp, hq⟩ := (Finset.mem_filter.mp hmem).2
  let s : ℕ := ∑ i : Fin 6, 2 ^ (a i + 1)
  change Nat.Prime (N - (p + s)) at hq
  refine ⟨p, N - (p + s), hp, hq, a, ?_⟩
  change N = p + (N - (p + s)) + s
  have hpos := hq.pos
  omega
