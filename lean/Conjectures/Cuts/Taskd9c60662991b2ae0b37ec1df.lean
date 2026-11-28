import Mathlib

theorem Conjectures.Cuts.Taskd9c60662991b2ae0b37ec1df :
    ∀ (x1 : ℕ), {x2 ∈ Finset.Icc (1 : ℕ) x1 | (2 : ℕ) ≤ x2 ∧ ((2 : ℕ) ^ x2) ^ (2 : ℕ) ≤ x1 ∧ (0 : ℕ) < {x3 ∈ Finset.range (x1 - (2 : ℕ) ^ x2 + (1 : ℕ)) | Nat.Prime x3 ∧ Nat.Prime (x1 - (2 : ℕ) ^ x2 - x3)}.card}.card + {x2 ∈ Finset.Icc (1 : ℕ) x1 | (2 : ℕ) ≤ x2 ∧ ((2 : ℕ) ^ x2) ^ (2 : ℕ) ≤ x1 ∧ (0 : ℕ) < {x3 ∈ Finset.range (x1 + (2 : ℕ) - (2 : ℕ) ^ x2 + (1 : ℕ)) | Nat.Prime x3 ∧ Nat.Prime (x1 + (2 : ℕ) - (2 : ℕ) ^ x2 - x3)}.card}.card > {x2 ∈ Finset.Icc (1 : ℕ) x1 | (2 : ℕ) ≤ x2 ∧ ((2 : ℕ) ^ x2) ^ (2 : ℕ) ≤ x1}.card → ∃ (x3 : ℕ), (2 : ℕ) ≤ x3 ∧ ((2 : ℕ) ^ x3) ^ (2 : ℕ) ≤ x1 ∧ (0 : ℕ) < {x4 ∈ Finset.range (x1 - (2 : ℕ) ^ x3 + (1 : ℕ)) | Nat.Prime x4 ∧ Nat.Prime (x1 - (2 : ℕ) ^ x3 - x4)}.card ∧ (0 : ℕ) < {x4 ∈ Finset.range (x1 + (2 : ℕ) - (2 : ℕ) ^ x3 + (1 : ℕ)) | Nat.Prime x4 ∧ Nat.Prime (x1 + (2 : ℕ) - (2 : ℕ) ^ x3 - x4)}.card := by
  intro x1 h
  classical
  have hsubA :
      {x2 ∈ Finset.Icc (1 : ℕ) x1 | (2 : ℕ) ≤ x2 ∧ ((2 : ℕ) ^ x2) ^ (2 : ℕ) ≤ x1 ∧
          (0 : ℕ) < {x3 ∈ Finset.range (x1 - (2 : ℕ) ^ x2 + (1 : ℕ)) | Nat.Prime x3 ∧
            Nat.Prime (x1 - (2 : ℕ) ^ x2 - x3)}.card} ⊆
        {x2 ∈ Finset.Icc (1 : ℕ) x1 | (2 : ℕ) ≤ x2 ∧ ((2 : ℕ) ^ x2) ^ (2 : ℕ) ≤ x1} := by
    intro x2 hx2
    rw [Finset.mem_filter] at hx2
    rw [Finset.mem_filter]
    exact ⟨hx2.1, hx2.2.1, hx2.2.2.1⟩
  have hsubB :
      {x2 ∈ Finset.Icc (1 : ℕ) x1 | (2 : ℕ) ≤ x2 ∧ ((2 : ℕ) ^ x2) ^ (2 : ℕ) ≤ x1 ∧
          (0 : ℕ) < {x3 ∈ Finset.range (x1 + (2 : ℕ) - (2 : ℕ) ^ x2 + (1 : ℕ)) | Nat.Prime x3 ∧
            Nat.Prime (x1 + (2 : ℕ) - (2 : ℕ) ^ x2 - x3)}.card} ⊆
        {x2 ∈ Finset.Icc (1 : ℕ) x1 | (2 : ℕ) ≤ x2 ∧ ((2 : ℕ) ^ x2) ^ (2 : ℕ) ≤ x1} := by
    intro x2 hx2
    rw [Finset.mem_filter] at hx2
    rw [Finset.mem_filter]
    exact ⟨hx2.1, hx2.2.1, hx2.2.2.1⟩
  have hunion :
      {x2 ∈ Finset.Icc (1 : ℕ) x1 | (2 : ℕ) ≤ x2 ∧ ((2 : ℕ) ^ x2) ^ (2 : ℕ) ≤ x1 ∧
          (0 : ℕ) < {x3 ∈ Finset.range (x1 - (2 : ℕ) ^ x2 + (1 : ℕ)) | Nat.Prime x3 ∧
            Nat.Prime (x1 - (2 : ℕ) ^ x2 - x3)}.card} ∪
        {x2 ∈ Finset.Icc (1 : ℕ) x1 | (2 : ℕ) ≤ x2 ∧ ((2 : ℕ) ^ x2) ^ (2 : ℕ) ≤ x1 ∧
          (0 : ℕ) < {x3 ∈ Finset.range (x1 + (2 : ℕ) - (2 : ℕ) ^ x2 + (1 : ℕ)) | Nat.Prime x3 ∧
            Nat.Prime (x1 + (2 : ℕ) - (2 : ℕ) ^ x2 - x3)}.card} ⊆
        {x2 ∈ Finset.Icc (1 : ℕ) x1 | (2 : ℕ) ≤ x2 ∧ ((2 : ℕ) ^ x2) ^ (2 : ℕ) ≤ x1} :=
    Finset.union_subset hsubA hsubB
  have hle := Finset.card_le_card hunion
  have hsum := Finset.card_union_add_card_inter
    ({x2 ∈ Finset.Icc (1 : ℕ) x1 | (2 : ℕ) ≤ x2 ∧ ((2 : ℕ) ^ x2) ^ (2 : ℕ) ≤ x1 ∧
        (0 : ℕ) < {x3 ∈ Finset.range (x1 - (2 : ℕ) ^ x2 + (1 : ℕ)) | Nat.Prime x3 ∧
          Nat.Prime (x1 - (2 : ℕ) ^ x2 - x3)}.card} : Finset ℕ)
    ({x2 ∈ Finset.Icc (1 : ℕ) x1 | (2 : ℕ) ≤ x2 ∧ ((2 : ℕ) ^ x2) ^ (2 : ℕ) ≤ x1 ∧
        (0 : ℕ) < {x3 ∈ Finset.range (x1 + (2 : ℕ) - (2 : ℕ) ^ x2 + (1 : ℕ)) | Nat.Prime x3 ∧
          Nat.Prime (x1 + (2 : ℕ) - (2 : ℕ) ^ x2 - x3)}.card} : Finset ℕ)
  have hpos :
      (0 : ℕ) < ({x2 ∈ Finset.Icc (1 : ℕ) x1 | (2 : ℕ) ≤ x2 ∧ ((2 : ℕ) ^ x2) ^ (2 : ℕ) ≤ x1 ∧
          (0 : ℕ) < {x3 ∈ Finset.range (x1 - (2 : ℕ) ^ x2 + (1 : ℕ)) | Nat.Prime x3 ∧
            Nat.Prime (x1 - (2 : ℕ) ^ x2 - x3)}.card} ∩
        {x2 ∈ Finset.Icc (1 : ℕ) x1 | (2 : ℕ) ≤ x2 ∧ ((2 : ℕ) ^ x2) ^ (2 : ℕ) ≤ x1 ∧
          (0 : ℕ) < {x3 ∈ Finset.range (x1 + (2 : ℕ) - (2 : ℕ) ^ x2 + (1 : ℕ)) | Nat.Prime x3 ∧
            Nat.Prime (x1 + (2 : ℕ) - (2 : ℕ) ^ x2 - x3)}.card} : Finset ℕ).card := by
    omega
  obtain ⟨e, he⟩ := Finset.card_pos.mp hpos
  have heA := (Finset.mem_inter.mp he).1
  have heB := (Finset.mem_inter.mp he).2
  rw [Finset.mem_filter] at heA heB
  exact ⟨e, heA.2.1, heA.2.2.1, heA.2.2.2, heB.2.2.2⟩
