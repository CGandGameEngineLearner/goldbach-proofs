import Mathlib

/-- For any cutoff `x1` and lower bound `x2` one can pick a point `x3` exceeding both:
`x3 = max x1 x2 + 1` works, since `x1 ≤ max x1 x2` and `x2 ≤ max x1 x2`. -/
theorem Conjectures.Cuts.Taskd7aec65222ec3f7a311851a4 :
    ∀ (x1 x2 : ℕ), ∃ (x3 : ℕ), x1 < x3 ∧ x2 ≤ x3 := by
  intro x1 x2
  refine ⟨max x1 x2 + 1, ?_, ?_⟩
  · omega
  · omega
