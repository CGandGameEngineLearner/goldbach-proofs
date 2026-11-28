import Mathlib

/- Pad a six-term tuple of positive powers of two with seven copies of `2 ^ 1`
to obtain a thirteen-term tuple whose total weight is exactly `14` larger. -/
theorem Conjectures.Cuts.Task6f9a24094cccfabc5d125ad1 : (∀ (x1 : Fin (6 : ℕ) → ℕ), ∃ (x2 : Fin (13 : ℕ) → ℕ), ∑ x3 : Fin (13 : ℕ), (2 : ℕ) ^ (x2 x3 + (1 : ℕ)) = ∑ x3 : Fin (6 : ℕ), (2 : ℕ) ^ (x1 x3 + (1 : ℕ)) + (14 : ℕ)) := by
  intro x1
  refine ⟨Fin.append (fun _ : Fin 7 => 0) x1, ?_⟩
  show (∑ x3 : Fin (7 + 6), (2 : ℕ) ^ (Fin.append (fun _ : Fin 7 => (0 : ℕ)) x1 x3 + (1 : ℕ)))
      = ∑ x3 : Fin (6 : ℕ), (2 : ℕ) ^ (x1 x3 + (1 : ℕ)) + (14 : ℕ)
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]
  simp [add_comm]
