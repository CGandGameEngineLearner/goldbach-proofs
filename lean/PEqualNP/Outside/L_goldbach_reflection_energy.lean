import Mathlib

open scoped BigOperators

theorem PEqualNP.Outside.L_goldbach_reflection_energy :
    ∀ (n : ℕ) (b : ℕ → ℝ), (∑ k ∈ Finset.range (n+1), (b k + b (n-k))^2) - (∑ k ∈ Finset.range (n+1), (b k - b (n-k))^2) = 4 * ∑ k ∈ Finset.range (n+1), b k * b (n-k) := by
  intro n b
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring
