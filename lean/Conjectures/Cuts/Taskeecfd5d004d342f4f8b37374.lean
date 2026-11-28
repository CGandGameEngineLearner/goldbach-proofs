import Mathlib

/-- Adapted from the fleet proof of L-goldbach-cut-091af1a2d9c2f24e05722ab7
(`Conjectures.Cuts.Task091af1a2d9c2f24e05722ab7`), with the parity hypothesis on the
even number carried in place of the positivity hypothesis on the exponent. -/
theorem Conjectures.Cuts.Taskeecfd5d004d342f4f8b37374 :
    ∀ (x1 : ℝ) (x2 : ℕ), Even x2 → (0 : ℕ) < {x4 ∈ (Finset.range (x2 + (1 : ℕ))).product (Fintype.piFinset fun (x4 : Fin (6 : ℕ)) => Finset.range (x2 + (1 : ℕ))) | Nat.Prime x4.1 ∧ Nat.Prime (x2 - (x4.1 + ∑ x5 : Fin (6 : ℕ), (2 : ℕ) ^ (x4.2 x5 + (1 : ℕ)))) ∧ (↑(∑ x5 : Fin (6 : ℕ), (2 : ℕ) ^ (x4.2 x5 + (1 : ℕ))) : ℝ) ≤ (↑x2 : ℝ) ^ x1}.card → ∃ (x5 : ℕ) (x6 : ℕ), Nat.Prime x5 ∧ Nat.Prime x6 ∧ ∃ (x7 : Fin (6 : ℕ) → ℕ), x2 = x5 + x6 + ∑ x8 : Fin (6 : ℕ), (2 : ℕ) ^ (x7 x8 + (1 : ℕ)) ∧ (↑(∑ x8 : Fin (6 : ℕ), (2 : ℕ) ^ (x7 x8 + (1 : ℕ))) : ℝ) ≤ (↑x2 : ℝ) ^ x1 := by
  intro x1 x2 _heven hcard
  have hne : {x4 ∈ (Finset.range (x2 + (1 : ℕ))).product (Fintype.piFinset fun (x4 : Fin (6 : ℕ)) => Finset.range (x2 + (1 : ℕ))) | Nat.Prime x4.1 ∧ Nat.Prime (x2 - (x4.1 + ∑ x5 : Fin (6 : ℕ), (2 : ℕ) ^ (x4.2 x5 + (1 : ℕ)))) ∧ (↑(∑ x5 : Fin (6 : ℕ), (2 : ℕ) ^ (x4.2 x5 + (1 : ℕ))) : ℝ) ≤ (↑x2 : ℝ) ^ x1} ≠ ∅ := by
    intro hempty
    rw [hempty, Finset.card_empty] at hcard
    omega
  obtain ⟨x4, hx4⟩ := Finset.nonempty_iff_ne_empty.mpr hne
  rw [Finset.mem_filter] at hx4
  obtain ⟨_, hcond⟩ := hx4
  refine ⟨x4.1, x2 - (x4.1 + ∑ x5 : Fin (6 : ℕ), (2 : ℕ) ^ (x4.2 x5 + (1 : ℕ))),
    hcond.1, hcond.2.1, x4.2, ?_, hcond.2.2⟩
  have hlt := hcond.2.1.one_lt
  have hle : x4.1 + ∑ x5 : Fin (6 : ℕ), (2 : ℕ) ^ (x4.2 x5 + (1 : ℕ)) ≤ x2 := by omega
  omega
