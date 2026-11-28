import Mathlib

theorem Conjectures.Cuts.Task7055f37c97d4bd40089d0608 :
  (∀ (x1 : ℕ), (0 : ℕ) < {x2 ∈ Finset.range ((2 : ℕ) * x1 ^ (6 : ℕ) + (1 : ℕ)) | Nat.Prime x2 ∧ Nat.Prime ((2 : ℕ) * x1 ^ (6 : ℕ) - x2)}.card → ∃ (x3 : ℕ) (x4 : ℕ), Nat.Prime x3 ∧ Nat.Prime x4 ∧ x3 + x4 = (2 : ℕ) * x1 ^ (6 : ℕ)) := by
  intro n h
  obtain ⟨p, hp⟩ := Finset.card_pos.mp h
  obtain ⟨hrange, hprime, hpartner⟩ := Finset.mem_filter.mp hp
  have hle : p ≤ 2*n^6 := Nat.le_of_lt_succ (Finset.mem_range.mp hrange)
  exact ⟨p, 2*n^6-p, hprime, hpartner, by omega⟩
