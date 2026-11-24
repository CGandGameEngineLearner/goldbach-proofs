import Mathlib

theorem PEqualNP.Outside.L_goldbach_zero_blocks_pair_defect :
    ∀ (n : ℕ) (a : Fin n → ℂ) (e : Fin n ≃ Fin n), 2*‖∑ i,a i‖≤∑ i,‖a i+a (e i)‖ := by
  intro n a e
  have hre : (∑ i, a (e i)) = ∑ i, a i := Equiv.sum_comp e a
  have h2 : (2:ℂ) * (∑ i, a i) = ∑ i, (a i + a (e i)) := by
    rw [Finset.sum_add_distrib, hre]; ring
  calc 2 * ‖∑ i, a i‖ = ‖(2:ℂ) * ∑ i, a i‖ := by rw [norm_mul]; norm_num
    _ = ‖∑ i, (a i + a (e i))‖ := by rw [h2]
    _ ≤ ∑ i, ‖a i + a (e i)‖ := norm_sum_le _ _
