import Mathlib

theorem PEqualNP.Outside.L_goldbach_factor_line_near_diagonal_budget :
    ∀ (J : Finset ℤ) (D : ℕ) (u v : ℤ → ℝ) (B : ℝ), 0 ≤ B → (∀ i ∈ J, |u i * v i| ≤ B) → |∑ i ∈ J, ∑ j ∈ J.filter (fun j => j ≠ i ∧ (j-i).natAbs ≤ D), u i * v i * (u j * v j)| ≤ (J.card:ℝ) * (2*(D:ℝ)) * B^2 := by
  intro J D u v B hB h
  have hcard : ∀ i : ℤ, ((J.filter (fun j => j ≠ i ∧ (j-i).natAbs ≤ D)).card : ℝ) ≤ 2 * D := by
    intro i
    have hsub : J.filter (fun j => j ≠ i ∧ (j-i).natAbs ≤ D) ⊆ (Finset.Icc (i - D) (i + D)).erase i := by
      intro j hj
      simp only [Finset.mem_filter] at hj
      simp only [Finset.mem_erase, Finset.mem_Icc]
      refine ⟨hj.2.1, ?_, ?_⟩ <;> omega
    have h1 := Finset.card_le_card hsub
    have h2 : ((Finset.Icc (i - D) (i + D)).erase i).card = 2 * D := by
      rw [Finset.card_erase_of_mem (by simp), Int.card_Icc]; omega
    rw [h2] at h1; exact_mod_cast h1
  calc |∑ i ∈ J, ∑ j ∈ J.filter (fun j => j ≠ i ∧ (j-i).natAbs ≤ D), u i * v i * (u j * v j)|
      ≤ ∑ i ∈ J, |∑ j ∈ J.filter (fun j => j ≠ i ∧ (j-i).natAbs ≤ D), u i * v i * (u j * v j)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ J, (2 * (D:ℝ)) * B^2 := by
        apply Finset.sum_le_sum
        intro i hi
        calc |∑ j ∈ J.filter (fun j => j ≠ i ∧ (j-i).natAbs ≤ D), u i * v i * (u j * v j)|
            ≤ ∑ j ∈ J.filter (fun j => j ≠ i ∧ (j-i).natAbs ≤ D), |u i * v i * (u j * v j)| :=
              Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ j ∈ J.filter (fun j => j ≠ i ∧ (j-i).natAbs ≤ D), B^2 := by
              apply Finset.sum_le_sum
              intro j hj
              rw [abs_mul, sq]
              exact mul_le_mul (h i hi) (h j (Finset.mem_filter.mp hj).1) (abs_nonneg _) hB
          _ = ((J.filter (fun j => j ≠ i ∧ (j-i).natAbs ≤ D)).card : ℝ) * B^2 := by
              rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ (2 * (D:ℝ)) * B^2 := mul_le_mul_of_nonneg_right (hcard i) (sq_nonneg B)
    _ = (J.card:ℝ) * (2*(D:ℝ)) * B^2 := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring
