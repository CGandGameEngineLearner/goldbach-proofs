import Mathlib

theorem Conjectures.Cuts.Taskd9c60662991b2ae0b37ec1df : (∀ (x1 : ℕ), {x2 ∈ Finset.Icc (1 : ℕ) x1 | (2 : ℕ) ≤ x2 ∧ ((2 : ℕ) ^ x2) ^ (2 : ℕ) ≤ x1 ∧ (0 : ℕ) < {x3 ∈ Finset.range (x1 - (2 : ℕ) ^ x2 + (1 : ℕ)) | Nat.Prime x3 ∧ Nat.Prime (x1 - (2 : ℕ) ^ x2 - x3)}.card}.card + {x2 ∈ Finset.Icc (1 : ℕ) x1 | (2 : ℕ) ≤ x2 ∧ ((2 : ℕ) ^ x2) ^ (2 : ℕ) ≤ x1 ∧ (0 : ℕ) < {x3 ∈ Finset.range (x1 + (2 : ℕ) - (2 : ℕ) ^ x2 + (1 : ℕ)) | Nat.Prime x3 ∧ Nat.Prime (x1 + (2 : ℕ) - (2 : ℕ) ^ x2 - x3)}.card}.card > {x2 ∈ Finset.Icc (1 : ℕ) x1 | (2 : ℕ) ≤ x2 ∧ ((2 : ℕ) ^ x2) ^ (2 : ℕ) ≤ x1}.card → ∃ (x3 : ℕ), (2 : ℕ) ≤ x3 ∧ ((2 : ℕ) ^ x3) ^ (2 : ℕ) ≤ x1 ∧ (0 : ℕ) < {x4 ∈ Finset.range (x1 - (2 : ℕ) ^ x3 + (1 : ℕ)) | Nat.Prime x4 ∧ Nat.Prime (x1 - (2 : ℕ) ^ x3 - x4)}.card ∧ (0 : ℕ) < {x4 ∈ Finset.range (x1 + (2 : ℕ) - (2 : ℕ) ^ x3 + (1 : ℕ)) | Nat.Prime x4 ∧ Nat.Prime (x1 + (2 : ℕ) - (2 : ℕ) ^ x3 - x4)}.card) := by
  intro x1 h
  set U : Finset ℕ := {x2 ∈ Finset.Icc (1 : ℕ) x1 | (2 : ℕ) ≤ x2 ∧ ((2 : ℕ) ^ x2) ^ (2 : ℕ) ≤ x1} with hU
  set A : Finset ℕ := U.filter (fun e =>
    (0 : ℕ) < {x3 ∈ Finset.range (x1 - (2 : ℕ) ^ e + (1 : ℕ)) |
      Nat.Prime x3 ∧ Nat.Prime (x1 - (2 : ℕ) ^ e - x3)}.card) with hA
  set B : Finset ℕ := U.filter (fun e =>
    (0 : ℕ) < {x3 ∈ Finset.range (x1 + (2 : ℕ) - (2 : ℕ) ^ e + (1 : ℕ)) |
      Nat.Prime x3 ∧ Nat.Prime (x1 + (2 : ℕ) - (2 : ℕ) ^ e - x3)}.card) with hB
  have hA' : {x2 ∈ Finset.Icc (1 : ℕ) x1 | (2 : ℕ) ≤ x2 ∧ ((2 : ℕ) ^ x2) ^ (2 : ℕ) ≤ x1 ∧
      (0 : ℕ) < {x3 ∈ Finset.range (x1 - (2 : ℕ) ^ x2 + (1 : ℕ)) |
        Nat.Prime x3 ∧ Nat.Prime (x1 - (2 : ℕ) ^ x2 - x3)}.card} = A := by
    ext e
    simp [hU, hA, and_assoc]
  have hB' : {x2 ∈ Finset.Icc (1 : ℕ) x1 | (2 : ℕ) ≤ x2 ∧ ((2 : ℕ) ^ x2) ^ (2 : ℕ) ≤ x1 ∧
      (0 : ℕ) < {x3 ∈ Finset.range (x1 + (2 : ℕ) - (2 : ℕ) ^ x2 + (1 : ℕ)) |
        Nat.Prime x3 ∧ Nat.Prime (x1 + (2 : ℕ) - (2 : ℕ) ^ x2 - x3)}.card} = B := by
    ext e
    simp [hU, hB, and_assoc]
  rw [hA', hB'] at h
  by_contra hcon
  push Not at hcon
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro e heA heB
    rw [hA, Finset.mem_filter] at heA
    rw [hB, Finset.mem_filter] at heB
    obtain ⟨hU1, hpos1⟩ := heA
    obtain ⟨-, hpos2⟩ := heB
    rw [hU, Finset.mem_filter] at hU1
    obtain ⟨-, he2, he4⟩ := hU1
    have hle0 := hcon e he2 he4 hpos1
    omega
  have hcard := Finset.card_union_of_disjoint hdisj
  have hsubA : A ⊆ U := by
    rw [hA]
    exact Finset.filter_subset _ _
  have hsubB : B ⊆ U := by
    rw [hB]
    exact Finset.filter_subset _ _
  have hle := Finset.card_le_card (Finset.union_subset hsubA hsubB)
  omega
