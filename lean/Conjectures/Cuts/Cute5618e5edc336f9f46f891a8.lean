import Conjectures.TwinPrimes.SharpWindowContamination

/-- PREPUB twin-primes cut: `L-twin-primes-cut-d7aec65222ec3f7a311851a4`.
For any cutoff B and lower bound N one can pick X exceeding both. -/
theorem Conjectures.Cuts.Cute5618e5edc336f9f46f891a8 : ∀ (x1 x2 : ℕ), ∃ (x3 : ℕ), x1 < x3 ∧ x2 ≤ x3 := by
  intro x1 x2
  exact ⟨x1 + x2 + 1, by omega, by omega⟩
