import Mathlib

theorem Conjectures.Cuts.Task6f9a24094cccfabc5d125ad1 : (∀ (x1 : Fin (6 : ℕ) → ℕ), ∃ (x2 : Fin (13 : ℕ) → ℕ), ∑ x3 : Fin (13 : ℕ), (2 : ℕ) ^ (x2 x3 + (1 : ℕ)) = ∑ x3 : Fin (6 : ℕ), (2 : ℕ) ^ (x1 x3 + (1 : ℕ)) + (14 : ℕ)) := by
  intro e
  refine ⟨fun i => if h : (i : ℕ) < 6 then e ⟨(i : ℕ), h⟩ else 0, ?_⟩
  rw [show (13 : ℕ) = 6 + 7 from rfl, Fin.sum_univ_add]
  simp
