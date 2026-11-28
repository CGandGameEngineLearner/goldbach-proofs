import Mathlib

theorem Conjectures.Cuts.Task6f9a24094cccfabc5d125ad1 : (∀ (x1 : Fin (6 : ℕ) → ℕ), ∃ (x2 : Fin (13 : ℕ) → ℕ), ∑ x3 : Fin (13 : ℕ), (2 : ℕ) ^ (x2 x3 + (1 : ℕ)) = ∑ x3 : Fin (6 : ℕ), (2 : ℕ) ^ (x1 x3 + (1 : ℕ)) + (14 : ℕ)) := by
  intro a
  refine ⟨Fin.append a (fun _ : Fin 7 => 0), ?_⟩
  rw [Fin.sum_univ_add (a := 6) (b := 7)]
  simp
