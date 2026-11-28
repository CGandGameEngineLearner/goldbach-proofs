import Mathlib

/-- Combinatorial extraction: if some admissible shift `e` gives a positive count of central
prime pairs for `x1 - 2 ^ e`, then a witness `(e, p, q)` exists with `x1 = p + q + 2 ^ e`
and the central-window inequalities. Adapted from the accepted proof of
`Conjectures.Cuts.Task7055f37c97d4bd40089d0608`. -/
theorem Conjectures.Cuts.Taskd8b75da4f10ca799a1346b90 :
    ∀ (x1 : ℕ), (0 : ℕ) < {x2 ∈ Finset.Icc (1 : ℕ) x1 | (1 : ℕ) ≤ x2 ∧ ((2 : ℕ) ^ x2) ^ (2 : ℕ) ≤ x1 ∧ (0 : ℕ) < {x3 ∈ Finset.range (x1 + (1 : ℕ)) | Nat.Prime x3 ∧ Nat.Prime (x1 - (2 : ℕ) ^ x2 - x3) ∧ x3 + (x1 - (2 : ℕ) ^ x2 - x3) ≤ (3 : ℕ) * x3 ∧ (3 : ℕ) * x3 ≤ (2 : ℕ) * (x3 + (x1 - (2 : ℕ) ^ x2 - x3))}.card}.card → ∃ (x3 : ℕ) (x4 : ℕ) (x5 : ℕ), (1 : ℕ) ≤ x3 ∧ ((2 : ℕ) ^ x3) ^ (2 : ℕ) ≤ x1 ∧ Nat.Prime x4 ∧ Nat.Prime x5 ∧ x1 = x4 + x5 + (2 : ℕ) ^ x3 ∧ x4 + x5 ≤ (3 : ℕ) * x4 ∧ (3 : ℕ) * x4 ≤ (2 : ℕ) * (x4 + x5) := by
  intro x1 h
  obtain ⟨e, he⟩ := Finset.card_pos.mp h
  obtain ⟨_, he1, he2, he3⟩ := Finset.mem_filter.mp he
  obtain ⟨p, hp⟩ := Finset.card_pos.mp he3
  obtain ⟨_, hpp, hqp, hw1, hw2⟩ := Finset.mem_filter.mp hp
  refine ⟨e, p, x1 - 2 ^ e - p, he1, he2, hpp, hqp, ?_, hw1, hw2⟩
  have hq : 2 ≤ x1 - 2 ^ e - p := Nat.Prime.two_le hqp
  omega
