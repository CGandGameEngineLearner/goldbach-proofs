import Mathlib

theorem Conjectures.Cuts.Taskd9c60662991b2ae0b37ec1df :
∀ (x1 : ℕ), {x2 ∈ Finset.Icc (1 : ℕ) x1 | (2 : ℕ) ≤ x2 ∧ ((2 : ℕ) ^ x2) ^ (2 : ℕ) ≤ x1 ∧ (0 : ℕ) < {x3 ∈ Finset.range (x1 - (2 : ℕ) ^ x2 + (1 : ℕ)) | Nat.Prime x3 ∧ Nat.Prime (x1 - (2 : ℕ) ^ x2 - x3)}.card}.card + {x2 ∈ Finset.Icc (1 : ℕ) x1 | (2 : ℕ) ≤ x2 ∧ ((2 : ℕ) ^ x2) ^ (2 : ℕ) ≤ x1 ∧ (0 : ℕ) < {x3 ∈ Finset.range (x1 + (2 : ℕ) - (2 : ℕ) ^ x2 + (1 : ℕ)) | Nat.Prime x3 ∧ Nat.Prime (x1 + (2 : ℕ) - (2 : ℕ) ^ x2 - x3)}.card}.card > {x2 ∈ Finset.Icc (1 : ℕ) x1 | (2 : ℕ) ≤ x2 ∧ ((2 : ℕ) ^ x2) ^ (2 : ℕ) ≤ x1}.card → ∃ (x3 : ℕ), (2 : ℕ) ≤ x3 ∧ ((2 : ℕ) ^ x3) ^ (2 : ℕ) ≤ x1 ∧ (0 : ℕ) < {x4 ∈ Finset.range (x1 - (2 : ℕ) ^ x3 + (1 : ℕ)) | Nat.Prime x4 ∧ Nat.Prime (x1 - (2 : ℕ) ^ x3 - x4)}.card ∧ (0 : ℕ) < {x4 ∈ Finset.range (x1 + (2 : ℕ) - (2 : ℕ) ^ x3 + (1 : ℕ)) | Nat.Prime x4 ∧ Nat.Prime (x1 + (2 : ℕ) - (2 : ℕ) ^ x3 - x4)}.card := by
  classical
  intro n h
  let good (m : ℕ) := 0 < ((Finset.range (m+1)).filter
    (fun p => Nat.Prime p ∧ Nat.Prime (m-p))).card
  let shifts := Finset.Icc 1 n
  let allowed (e : ℕ) := 2 ≤ e ∧ (2^e)^2 ≤ n
  let pool := shifts.filter allowed
  let left := shifts.filter (fun e => 2 ≤ e ∧ (2^e)^2 ≤ n ∧ good (n-2^e))
  let right := shifts.filter (fun e => 2 ≤ e ∧ (2^e)^2 ≤ n ∧ good (n+2-2^e))
  change pool.card < left.card + right.card at h
  have hsub : left ∪ right ⊆ pool := by
    intro e he
    rcases Finset.mem_union.mp he with hl|hr
    · have t := Finset.mem_filter.mp hl
      exact Finset.mem_filter.mpr ⟨t.1,t.2.1,t.2.2.1⟩
    · have t := Finset.mem_filter.mp hr
      exact Finset.mem_filter.mpr ⟨t.1,t.2.1,t.2.2.1⟩
  have bound := Finset.card_le_card hsub
  have identity := Finset.card_union_add_card_inter left right
  obtain ⟨e,he⟩ := Finset.card_pos.mp (show 0 < (left ∩ right).card by omega)
  obtain ⟨hl,hr⟩ := Finset.mem_inter.mp he
  have l := (Finset.mem_filter.mp hl).2
  have r := (Finset.mem_filter.mp hr).2
  exact ⟨e,l.1,l.2.1,l.2.2,r.2.2⟩
