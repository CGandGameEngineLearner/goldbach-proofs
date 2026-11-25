import Mathlib

theorem PEqualNP.Outside.L_goldbach_reflected_long_complement_window :
    ∀ (n p d m D : ℕ), p < n → D < d → d*m = n-p → (n:ℝ)/3 ≤ p → (p:ℝ) ≤ 2*n/3 → D*m < n ∧ (n:ℝ)/3 ≤ d*m ∧ (d*m:ℝ) ≤ 2*n/3 := by
  intro n p d m D hpn hDd hdm hp3 hp23
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with hm | hm
    · exfalso
      rw [hm, Nat.mul_zero] at hdm
      have hpos : 0 < n - p := Nat.sub_pos_of_lt hpn
      omega
    · exact hm
  have hdm_le : d * m ≤ n := by
    rw [hdm]; exact Nat.sub_le n p
  have hDm_lt : D * m < d * m := Nat.mul_lt_mul_of_pos_right hDd hm0
  have hlt : D * m < n := Nat.lt_of_lt_of_le hDm_lt hdm_le
  have hprod : (d : ℝ) * (m : ℝ) = (n : ℝ) - (p : ℝ) := by
    rw [← Nat.cast_mul, hdm, Nat.cast_sub (le_of_lt hpn)]
  refine ⟨hlt, ?_, ?_⟩
  · rw [hprod]; linarith
  · rw [hprod]; linarith
