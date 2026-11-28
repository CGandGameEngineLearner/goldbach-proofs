import Mathlib

theorem Conjectures.Cuts.Task4947109f8f5a65f73f4f20de : (by
  classical
  exact ∀ (S : Finset ℕ) (n : ℕ),
    0 < ((∑ p ∈ S, Polynomial.monomial (p+2) (1:ℕ))^2).coeff (n+4) ↔ ∃ p ∈ S, ∃ q ∈ S, p+q=n) := by
  classical
  intro S n
  simp only [sq,Finset.sum_mul,Finset.mul_sum,Polynomial.finsetSum_coeff,
    Polynomial.monomial_mul_monomial,one_mul,Polynomial.coeff_monomial]
  simp only [Finset.sum_pos_iff]
  have term (p q : ℕ) : 0 < (if p+2+(q+2)=n+4 then 1 else 0 : ℕ) ↔ p+q=n := by
    by_cases h : p+q=n <;> simp [show (p+2+(q+2)=n+4) ↔ p+q=n by omega,h]
  simp only [Finsupp.single_apply]
  simp_rw [term]
  simp only [Nat.add_comm]
