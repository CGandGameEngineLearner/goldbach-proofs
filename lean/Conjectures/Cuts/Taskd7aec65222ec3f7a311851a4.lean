import Mathlib
import Conjectures.TwinPrimes.SharpWindowContamination

theorem Conjectures.Cuts.Taskd7aec65222ec3f7a311851a4 : (∀ (x1 x2 : ℕ), ∃ (x3 : ℕ), x1 < x3 ∧ x2 ≤ x3) := by
  intro B N
  exact ⟨max B N + 1, by omega, by omega⟩
