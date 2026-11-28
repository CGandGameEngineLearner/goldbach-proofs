import Mathlib

theorem Conjectures.Cuts.Taskd8b75da4f10ca799a1346b90 : (∀ (x1 : ℕ), (0 : ℕ) < {x2 ∈ Finset.Icc (1 : ℕ) x1 | (1 : ℕ) ≤ x2 ∧ ((2 : ℕ) ^ x2) ^ (2 : ℕ) ≤ x1 ∧ (0 : ℕ) < {x3 ∈ Finset.range (x1 + (1 : ℕ)) | Nat.Prime x3 ∧ Nat.Prime (x1 - (2 : ℕ) ^ x2 - x3) ∧ x3 + (x1 - (2 : ℕ) ^ x2 - x3) ≤ (3 : ℕ) * x3 ∧ (3 : ℕ) * x3 ≤ (2 : ℕ) * (x3 + (x1 - (2 : ℕ) ^ x2 - x3))}.card}.card → ∃ (x3 : ℕ) (x4 : ℕ) (x5 : ℕ), (1 : ℕ) ≤ x3 ∧ ((2 : ℕ) ^ x3) ^ (2 : ℕ) ≤ x1 ∧ Nat.Prime x4 ∧ Nat.Prime x5 ∧ x1 = x4 + x5 + (2 : ℕ) ^ x3 ∧ x4 + x5 ≤ (3 : ℕ) * x4 ∧ (3 : ℕ) * x4 ≤ (2 : ℕ) * (x4 + x5)) := by
  intro x1 hpos
  obtain ⟨e, he⟩ := Finset.card_pos.mp hpos
  rw [Finset.mem_filter] at he
  obtain ⟨-, he1, he2, hcard⟩ := he
  obtain ⟨p, hp⟩ := Finset.card_pos.mp hcard
  rw [Finset.mem_filter] at hp
  obtain ⟨-, hpp, hpq, hw1, hw2⟩ := hp
  have hne : x1 - (2 : ℕ) ^ e - p ≠ 0 := Nat.Prime.ne_zero hpq
  refine ⟨e, p, x1 - (2 : ℕ) ^ e - p, he1, he2, hpp, hpq, ?_, hw1, hw2⟩
  have hlt : (2 : ℕ) ^ e + p < x1 := by
    by_contra hc
    have hle : x1 ≤ (2 : ℕ) ^ e + p := Nat.not_lt.mp hc
    rw [Nat.sub_sub, Nat.sub_eq_zero_of_le hle] at hne
    exact hne rfl
  have h := Nat.sub_add_cancel hlt
  omega
