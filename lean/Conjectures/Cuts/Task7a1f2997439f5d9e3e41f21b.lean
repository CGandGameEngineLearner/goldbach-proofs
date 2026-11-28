import Mathlib

theorem Conjectures.Cuts.Task7a1f2997439f5d9e3e41f21b : (∀ (x1 : ℕ), (0 : ℕ) < {x2 ∈ (Finset.range (x1 + (1 : ℕ))).product (Fintype.piFinset fun (x2 : Fin (5 : ℕ)) => Finset.range (x1 + (1 : ℕ))) | Nat.Prime x2.1 ∧ Nat.Prime (x1 - (x2.1 + ∑ x3 : Fin (5 : ℕ), (2 : ℕ) ^ (x2.2 x3 + (1 : ℕ))))}.card → ∃ (x3 : ℕ) (x4 : ℕ), Nat.Prime x3 ∧ Nat.Prime x4 ∧ ∃ (x5 : Fin (5 : ℕ) → ℕ), x1 = x3 + x4 + ∑ x6 : Fin (5 : ℕ), (2 : ℕ) ^ (x5 x6 + (1 : ℕ))) := by
  intro n hcount
  obtain ⟨⟨p, a⟩, hmem⟩ := Finset.card_pos.mp hcount
  obtain ⟨hp, hq⟩ := (Finset.mem_filter.mp hmem).2
  let s := ∑ i : Fin 5, 2 ^ (a i + 1)
  change Nat.Prime p at hp
  change Nat.Prime (n - (p + s)) at hq
  refine ⟨p, n - (p + s), hp, hq, a, ?_⟩
  change n = p + (n - (p + s)) + s
  have hpos := hq.pos
  omega
