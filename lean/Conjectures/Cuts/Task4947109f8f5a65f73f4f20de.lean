import Mathlib

/-- A nonnegative polynomial coefficient counts the pairs whose shifted indices sum to `n`;
the proof adapts the coefficient-support argument posted for this task in
GitHub Discussions #4711. -/
theorem Conjectures.Cuts.Task4947109f8f5a65f73f4f20de :
    ∀ (x1 : Finset ℕ) (x2 : ℕ),
      (0 : ℕ) < ((∑ x3 ∈ x1, (Polynomial.monomial (x3 + (2 : ℕ))) (1 : ℕ)) ^ (2 : ℕ)).coeff (x2 + (4 : ℕ))
        ↔ ∃ x3 ∈ x1, ∃ x4 ∈ x1, x3 + x4 = x2 := by
  classical
  intro S n
  simp only [sq, Finset.sum_mul, Finset.mul_sum, Polynomial.finsetSum_coeff,
    Polynomial.monomial_mul_monomial, one_mul, Polynomial.coeff_monomial]
  simp only [Finset.sum_pos_iff]
  have term (p q : ℕ) : 0 < (if p + 2 + (q + 2) = n + 4 then 1 else 0 : ℕ) ↔ p + q = n := by
    by_cases h : p + q = n <;> simp [show (p + 2 + (q + 2) = n + 4) ↔ p + q = n by omega, h]
  simp only [Finsupp.single_apply]
  simp_rw [term]
  simp only [Nat.add_comm]
