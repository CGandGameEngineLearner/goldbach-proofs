import Mathlib

namespace PEqualNP.Outside

/-- Approximate antisymmetry of a paired block leaves a residual bounded by the
sum of the paired norms. -/
theorem L_goldbach_zero_blocks_pair_defect :
    ∀ (n : ℕ) (a : Fin n → ℂ) (e : Fin n ≃ Fin n),
      2 * ‖∑ i, a i‖ ≤ ∑ i, ‖a i + a (e i)‖ := by
  intro n a e
  have hsum : (∑ i, (a i + a (e i))) = 2 * ∑ i, a i := by
    rw [Finset.sum_add_distrib, Equiv.sum_comp e a]
    ring
  calc
    2 * ‖∑ i, a i‖ = ‖(2 : ℂ) * ∑ i, a i‖ := by
      rw [norm_mul]
      norm_num
    _ = ‖∑ i, (a i + a (e i))‖ := by rw [← hsum]
    _ ≤ ∑ i, ‖a i + a (e i)‖ := by
      simpa using norm_sum_le (Finset.univ) (fun i => a i + a (e i))

end PEqualNP.Outside
