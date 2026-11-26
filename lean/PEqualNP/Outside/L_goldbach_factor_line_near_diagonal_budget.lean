import Mathlib

theorem PEqualNP.Outside.L_goldbach_factor_line_near_diagonal_budget :
    ∀ (J : Finset ℤ) (D : ℕ) (u v : ℤ → ℝ) (B : ℝ), 0 ≤ B → (∀ i ∈ J, |u i * v i| ≤ B) → |∑ i ∈ J, ∑ j ∈ J.filter (fun j => j ≠ i ∧ (j-i).natAbs ≤ D), u i * v i * (u j * v j)| ≤ (J.card:ℝ) * (2*(D:ℝ)) * B^2 := by
  intro J D u v B hB huv
  have hinner : ∀ i ∈ J,
      |∑ j ∈ J.filter (fun j => j ≠ i ∧ (j - i).natAbs ≤ D), u i * v i * (u j * v j)| ≤
        (2 * (D : ℝ)) * B ^ 2 := by
    intro i hi
    let S := J.filter (fun j => j ≠ i ∧ (j - i).natAbs ≤ D)
    let T := (Finset.Icc (i - (D : ℤ)) (i + (D : ℤ))).erase i
    have hsub : S ⊆ T := by
      intro j hj
      simp only [S, Finset.mem_filter] at hj
      simp only [T, Finset.mem_erase, Finset.mem_Icc]
      refine ⟨hj.2.1, ?_, ?_⟩ <;> omega
    have himem : i ∈ Finset.Icc (i - (D : ℤ)) (i + (D : ℤ)) := by
      simp only [Finset.mem_Icc]
      omega
    have hTcard : T.card = 2 * D := by
      dsimp only [T]
      rw [Finset.card_erase_of_mem himem, Int.card_Icc]
      omega
    have hScard : (S.card : ℝ) ≤ 2 * (D : ℝ) := by
      have hle : S.card ≤ 2 * D := hTcard ▸ Finset.card_le_card hsub
      exact_mod_cast hle
    have hterm : ∀ j ∈ S, |u i * v i * (u j * v j)| ≤ B ^ 2 := by
      intro j hj
      have hjJ : j ∈ J := (Finset.mem_filter.mp hj).1
      rw [abs_mul, sq]
      exact mul_le_mul (huv i hi) (huv j hjJ) (abs_nonneg _) hB
    calc
      |∑ j ∈ S, u i * v i * (u j * v j)|
          ≤ ∑ j ∈ S, |u i * v i * (u j * v j)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j ∈ S, B ^ 2 := Finset.sum_le_sum hterm
      _ = (S.card : ℝ) * B ^ 2 := by simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (2 * (D : ℝ)) * B ^ 2 := mul_le_mul_of_nonneg_right hScard (sq_nonneg B)
  calc
    |∑ i ∈ J, ∑ j ∈ J.filter (fun j => j ≠ i ∧ (j - i).natAbs ≤ D), u i * v i * (u j * v j)|
        ≤ ∑ i ∈ J, |∑ j ∈ J.filter (fun j => j ≠ i ∧ (j - i).natAbs ≤ D), u i * v i * (u j * v j)| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ J, (2 * (D : ℝ)) * B ^ 2 := Finset.sum_le_sum hinner
    _ = (J.card : ℝ) * (2 * (D : ℝ)) * B ^ 2 := by
          simp [Finset.sum_const, nsmul_eq_mul, mul_assoc]
