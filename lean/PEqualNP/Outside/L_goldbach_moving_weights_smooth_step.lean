import Mathlib

theorem PEqualNP.Outside.L_goldbach_moving_weights_smooth_step :
    ∀ (n : ℕ) (w v a : Fin n → ℝ) (e : ℝ), (∀ i,|w i-v i|≤e) → |∑ i,a i*(w i-v i)|≤e*∑ i,|a i| := by
  intro n w v a e h
  calc |∑ i, a i*(w i-v i)| ≤ ∑ i, |a i*(w i-v i)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |a i| * |w i-v i| := by simp [abs_mul]
    _ ≤ ∑ i, |a i| * e := Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (h i) (abs_nonneg _))
    _ = (∑ i, |a i|) * e := by rw [Finset.sum_mul]
    _ = e * ∑ i, |a i| := by ring
