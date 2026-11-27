import Mathlib

theorem Conjectures.Goldbach.BeaumontDenseExactObstruction :
    ∃ A : Set ℝ, Dense A ∧ (0:ℝ) ∈ closure A ∧ (0:ℝ) ∉ A := by
  refine ⟨({0} : Set ℝ)ᶜ, dense_compl_singleton 0, ?_, ?_⟩
  · have h := (dense_compl_singleton (0 : ℝ)).closure_eq
    simp [h]
  · simp
