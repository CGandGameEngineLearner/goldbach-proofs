import Mathlib

namespace PEqualNP.Outside

open scoped BigOperators

/-- Residual from approximate antisymmetry: the doubled sum of a finite block of
coefficients is controlled by the total size of its pair defects against a
permutation of the index set. -/
theorem L_goldbach_zero_blocks_pair_defect :
    ∀ (n : ℕ) (a : Fin n → ℂ) (e : Fin n ≃ Fin n), 2*‖∑ i,a i‖≤∑ i,‖a i+a (e i)‖ := by
  intro n a e
  have hperm : ∑ i, a (e i) = ∑ i, a i := Equiv.sum_comp e a
  have hsum : ∑ i, (a i + a (e i)) = (2 : ℂ) * ∑ i, a i := by
    rw [Finset.sum_add_distrib, hperm]
    ring
  have hnorm : ‖(2 : ℂ) * ∑ i, a i‖ = 2 * ‖∑ i, a i‖ := by
    rw [norm_mul, Complex.norm_two]
  calc
    2 * ‖∑ i, a i‖ = ‖(2 : ℂ) * ∑ i, a i‖ := hnorm.symm
    _ = ‖∑ i, (a i + a (e i))‖ := by rw [hsum]
    _ ≤ ∑ i, ‖a i + a (e i)‖ := norm_sum_le _ _

end PEqualNP.Outside