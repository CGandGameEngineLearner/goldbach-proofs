import Mathlib

theorem PEqualNP.Outside.L_goldbach_factor_line_near_diagonal_budget :
    ∀ (J : Finset ℤ) (D : ℕ) (u v : ℤ → ℝ) (B : ℝ), 0 ≤ B → (∀ i ∈ J, |u i * v i| ≤ B) → |∑ i ∈ J, ∑ j ∈ J.filter (fun j => j ≠ i ∧ (j-i).natAbs ≤ D), u i * v i * (u j * v j)| ≤ (J.card:ℝ) * (2*(D:ℝ)) * B^2 := by
  intro J D u v B hB hbound
  have inner : ∀ i ∈ J,
      |∑ j ∈ J.filter (fun j => j ≠ i ∧ (j-i).natAbs ≤ D), u i * v i * (u j * v j)|
        ≤ (2*(D:ℝ)) * B^2 := by
    intro i hi
    have hcard : (J.filter (fun j => j ≠ i ∧ (j-i).natAbs ≤ D)).card ≤ 2 * D := by
      have hsub : J.filter (fun j => j ≠ i ∧ (j-i).natAbs ≤ D) ⊆
          (Finset.Icc (i - (D:ℤ)) (i + (D:ℤ))).erase i := by
        intro j hj
        simp only [Finset.mem_filter] at hj
        simp only [Finset.mem_erase, Finset.mem_Icc]
        refine ⟨hj.2.1, ?_, ?_⟩
        · have h := hj.2.2; omega
        · have h := hj.2.2; omega
      calc (J.filter (fun j => j ≠ i ∧ (j-i).natAbs ≤ D)).card
          ≤ ((Finset.Icc (i - (D:ℤ)) (i + (D:ℤ))).erase i).card := Finset.card_le_card hsub
        _ = (Finset.Icc (i - (D:ℤ)) (i + (D:ℤ))).card - 1 :=
            Finset.card_erase_of_mem (by simp)
        _ ≤ 2 * D := by
            have h := Int.card_Icc_of_le (a := i - (D:ℤ)) (b := i + (D:ℤ)) (by omega)
            have hc : (Finset.Icc (i - (D:ℤ)) (i + (D:ℤ))).card = 2 * D + 1 := by omega
            omega
    have hcardR : ((J.filter (fun j => j ≠ i ∧ (j-i).natAbs ≤ D)).card : ℝ) ≤ 2*(D:ℝ) := by
      exact_mod_cast hcard
    calc |∑ j ∈ J.filter (fun j => j ≠ i ∧ (j-i).natAbs ≤ D), u i * v i * (u j * v j)|
        ≤ ∑ j ∈ J.filter (fun j => j ≠ i ∧ (j-i).natAbs ≤ D),
            |u i * v i * (u j * v j)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ J.filter (fun j => j ≠ i ∧ (j-i).natAbs ≤ D), B^2 := by
          apply Finset.sum_le_sum
          intro j hj
          have hjJ : j ∈ J := (Finset.mem_filter.mp hj).1
          have habs : |(u i * v i) * (u j * v j)| = |u i * v i| * |u j * v j| := abs_mul _ _
          have h1 : |u i * v i| ≤ B := hbound i hi
          have h2 : |u j * v j| ≤ B := hbound j hjJ
          have h3 : |u i * v i| * |u j * v j| ≤ B * B :=
            mul_le_mul h1 h2 (abs_nonneg (u j * v j)) hB
          calc |u i * v i * (u j * v j)| = |u i * v i| * |u j * v j| := habs
            _ ≤ B * B := h3
            _ = B^2 := by ring
      _ = ((J.filter (fun j => j ≠ i ∧ (j-i).natAbs ≤ D)).card : ℝ) * B^2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (2*(D:ℝ)) * B^2 := mul_le_mul_of_nonneg_right hcardR (sq_nonneg B)
  calc |∑ i ∈ J, ∑ j ∈ J.filter (fun j => j ≠ i ∧ (j-i).natAbs ≤ D), u i * v i * (u j * v j)|
      ≤ ∑ i ∈ J, |∑ j ∈ J.filter (fun j => j ≠ i ∧ (j-i).natAbs ≤ D),
          u i * v i * (u j * v j)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ J, (2*(D:ℝ)) * B^2 := Finset.sum_le_sum (fun i hi => inner i hi)
    _ = (J.card:ℝ) * ((2*(D:ℝ)) * B^2) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ = (J.card:ℝ) * (2*(D:ℝ)) * B^2 := by ring
