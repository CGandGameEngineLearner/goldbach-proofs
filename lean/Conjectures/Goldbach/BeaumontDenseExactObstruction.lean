-- re-submitted to clear an infrastructure failure
import Mathlib

open scoped BigOperators

theorem Conjectures.Goldbach.BeaumontDenseExactObstruction :
    ∃ A : Set ℝ, Dense A ∧ (0:ℝ) ∈ closure A ∧ (0:ℝ) ∉ A := by
  have hd : Dense ({0}ᶜ : Set ℝ) := dense_compl_singleton 0
  refine ⟨{0}ᶜ, hd, ?_, ?_⟩
  · rw [hd.closure_eq]
    exact Set.mem_univ 0
  · simp
