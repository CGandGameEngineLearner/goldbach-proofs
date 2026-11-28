import Mathlib

theorem Conjectures.Cuts.Task091af1a2d9c2f24e05722ab7 : (∀ (x1 : ℝ), (0 : ℝ) < x1 → ∀ (x3 : ℕ), (0 : ℕ) < {x4 ∈ (Finset.range (x3 + (1 : ℕ))).product (Fintype.piFinset fun (x4 : Fin (6 : ℕ)) => Finset.range (x3 + (1 : ℕ))) | Nat.Prime x4.1 ∧ Nat.Prime (x3 - (x4.1 + ∑ x5 : Fin (6 : ℕ), (2 : ℕ) ^ (x4.2 x5 + (1 : ℕ)))) ∧ (↑(∑ x5 : Fin (6 : ℕ), (2 : ℕ) ^ (x4.2 x5 + (1 : ℕ))) : ℝ) ≤ (↑x3 : ℝ) ^ x1}.card → ∃ (x5 : ℕ) (x6 : ℕ), Nat.Prime x5 ∧ Nat.Prime x6 ∧ ∃ (x7 : Fin (6 : ℕ) → ℕ), x3 = x5 + x6 + ∑ x8 : Fin (6 : ℕ), (2 : ℕ) ^ (x7 x8 + (1 : ℕ)) ∧ (↑(∑ x8 : Fin (6 : ℕ), (2 : ℕ) ^ (x7 x8 + (1 : ℕ))) : ℝ) ≤ (↑x3 : ℝ) ^ x1) := by
  intro ε _ n hcount
  obtain ⟨⟨p, a⟩, hmem⟩ := Finset.card_pos.mp hcount
  obtain ⟨hp, hq, hshift⟩ := (Finset.mem_filter.mp hmem).2
  let s := ∑ i : Fin 6, 2 ^ (a i + 1)
  change Nat.Prime (n - (p + s)) at hq
  refine ⟨p, n - (p + s), hp, hq, a, ?_, hshift⟩
  change n = p + (n - (p + s)) + s
  have hpos := hq.pos
  omega
