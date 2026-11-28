import Mathlib

/-- Adapted from the fleet proof of L-goldbach-cut-1611ba2a96c98ad113eb01de
(`Conjectures.Cuts.Task1611ba2a96c98ad113eb01de`), with the extra `N^ε` budget
condition carried in the filter and required in the conclusion. -/
theorem Conjectures.Cuts.Task091af1a2d9c2f24e05722ab7 :
    ∀ (x1 : ℝ), (0 : ℝ) < x1 → ∀ (x3 : ℕ), (0 : ℕ) < {x4 ∈ (Finset.range (x3 + (1 : ℕ))).product (Fintype.piFinset fun (x4 : Fin (6 : ℕ)) => Finset.range (x3 + (1 : ℕ))) | Nat.Prime x4.1 ∧ Nat.Prime (x3 - (x4.1 + ∑ x5 : Fin (6 : ℕ), (2 : ℕ) ^ (x4.2 x5 + (1 : ℕ)))) ∧ (↑(∑ x5 : Fin (6 : ℕ), (2 : ℕ) ^ (x4.2 x5 + (1 : ℕ))) : ℝ) ≤ (↑x3 : ℝ) ^ x1}.card → ∃ (x5 : ℕ) (x6 : ℕ), Nat.Prime x5 ∧ Nat.Prime x6 ∧ ∃ (x7 : Fin (6 : ℕ) → ℕ), x3 = x5 + x6 + ∑ x8 : Fin (6 : ℕ), (2 : ℕ) ^ (x7 x8 + (1 : ℕ)) ∧ (↑(∑ x8 : Fin (6 : ℕ), (2 : ℕ) ^ (x7 x8 + (1 : ℕ))) : ℝ) ≤ (↑x3 : ℝ) ^ x1 := by
  intro x1 _hx1 x3 hcard
  have hne : {x4 ∈ (Finset.range (x3 + (1 : ℕ))).product (Fintype.piFinset fun (x4 : Fin (6 : ℕ)) => Finset.range (x3 + (1 : ℕ))) | Nat.Prime x4.1 ∧ Nat.Prime (x3 - (x4.1 + ∑ x5 : Fin (6 : ℕ), (2 : ℕ) ^ (x4.2 x5 + (1 : ℕ)))) ∧ (↑(∑ x5 : Fin (6 : ℕ), (2 : ℕ) ^ (x4.2 x5 + (1 : ℕ))) : ℝ) ≤ (↑x3 : ℝ) ^ x1} ≠ ∅ := by
    intro hempty
    rw [hempty, Finset.card_empty] at hcard
    omega
  obtain ⟨x4, hx4⟩ := Finset.nonempty_iff_ne_empty.mpr hne
  rw [Finset.mem_filter] at hx4
  obtain ⟨_, hcond⟩ := hx4
  refine ⟨x4.1, x3 - (x4.1 + ∑ x5 : Fin (6 : ℕ), (2 : ℕ) ^ (x4.2 x5 + (1 : ℕ))),
    hcond.1, hcond.2.1, x4.2, ?_, hcond.2.2⟩
  have hlt := hcond.2.1.one_lt
  have hle : x4.1 + ∑ x5 : Fin (6 : ℕ), (2 : ℕ) ^ (x4.2 x5 + (1 : ℕ)) ≤ x3 := by omega
  omega
