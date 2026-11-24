import Mathlib

open scoped BigOperators

theorem PEqualNP.Outside.L_goldbach_moving_weights_smooth_step :
    ∀ (n : ℕ) (w v a : Fin n → ℝ) (e : ℝ), (∀ i,|w i-v i|≤e) → |∑ i,a i*(w i-v i)|≤e*∑ i,|a i| := by
  intro n w v a e h
  calc
    |∑ i, a i * (w i - v i)| ≤ ∑ i, |a i * (w i - v i)| := by
      first
      | exact Finset.abs_sum_le_sum_abs _ _
      | exact?
    _ ≤ e * ∑ i, |a i| := by
      rw [Finset.mul_sum]
      simp only [abs_mul]
      apply Finset.sum_le_sum
      intro i hi
      calc
        |a i| * |w i - v i| ≤ |a i| * e :=
          mul_le_mul_of_nonneg_left (h i) (abs_nonneg _)
        _ = e * |a i| := mul_comm _ _
