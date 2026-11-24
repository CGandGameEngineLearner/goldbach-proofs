import Mathlib

theorem PEqualNP.Outside.L_goldbach_zero_blocks_pair_cancel :
    ∀ (n : ℕ) (a : Fin n → ℂ) (e : Fin n ≃ Fin n), (∀ i,a (e i) = -a i) → ∑ i,a i=0 := by
  intro n a e h
  have h1 : ∑ i, a (e i) = ∑ i, a i := e.sum_comp a
  have h2 : (∑ i, a (e i)) + (∑ i, a i) = 0 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [h i]
    ring
  rw [h1] at h2
  have h3 : (2 : ℂ) * (∑ i, a i) = 0 := by
    rw [two_mul]
    exact h2
  rcases mul_eq_zero.mp h3 with h4 | h4
  · exact absurd h4 (by norm_num)
  · exact h4
