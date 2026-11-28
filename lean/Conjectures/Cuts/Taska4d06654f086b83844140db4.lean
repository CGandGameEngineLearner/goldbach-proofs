import Mathlib

theorem Conjectures.Cuts.Taska4d06654f086b83844140db4 : (∀ (x1 : ℕ), (0 : ℝ) < ↑{x2 ∈ (Finset.range (x1 + (1 : ℕ))).product (Fintype.piFinset fun (x2 : Fin (13 : ℕ)) => Finset.range (x1 + (1 : ℕ))) | Nat.Prime x2.1 ∧ Nat.Prime (x1 - (x2.1 + ∑ x3 : Fin (13 : ℕ), (2 : ℕ) ^ (x2.2 x3 + (1 : ℕ))))}.card → ∃ (x3 : ℕ) (x4 : ℕ) (x5 : Fin (13 : ℕ) → ℕ), Nat.Prime x3 ∧ Nat.Prime x4 ∧ x1 = x3 + x4 + ∑ x6 : Fin (13 : ℕ), (2 : ℕ) ^ (x5 x6 + (1 : ℕ))) := by
  classical
  intro n h
  norm_cast at h
  obtain ⟨⟨p, e⟩, hmem⟩ := Finset.card_pos.mp h
  obtain ⟨hp, hq⟩ := (Finset.mem_filter.mp hmem).2
  let s := ∑ i : Fin 13, 2 ^ (e i + 1)
  change Nat.Prime (n - (p+s)) at hq
  refine ⟨p, n-(p+s), e, hp, hq, ?_⟩
  change n = p + (n-(p+s)) + s
  have hqpos := hq.pos
  omega
