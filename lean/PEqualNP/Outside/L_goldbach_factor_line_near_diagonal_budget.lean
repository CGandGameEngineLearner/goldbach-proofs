import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Int.Interval
import Mathlib.Basic.Real.Basic

theorem PEqualNP.Outside.L_goldbach_factor_line_near_diagonal_budget :
    ∀ (J : Finset ℤ) (D : ℕ) (u v : ℤ → ℝ) (B : ℝ), 0 ≤ B → (∀ i ∈ J, |u i * v i| ≤ B) → |∑ i ∈ J, ∑ j ∈ J.filter (fun j => j ≠ i ∧ (j-i).natAbs ≤ D), u i * v i * (u j * v j)| ≤ (J.card:ℝ) * (2*(D:ℝ)) * B^2 := by
  classical
  intro J D u v B hB hweight
  let neighbors (i : ℤ) := J.filter (fun j => j ≠ i ∧ (j-i).natAbs ≤ D)
  have hcard (i : ℤ) : (neighbors i).card ≤ 2 * D := by
    let span := Finset.Icc (i - (D : ℤ)) (i + (D : ℤ))
    have hmem : i ∈ span := Finset.mem_Icc.mpr (by constructor <;> omega)
    have hsubset : neighbors i ⊆ span.erase i := by
      intro j hj
      obtain ⟨_, hne, hd⟩ := Finset.mem_filter.mp hj
      apply Finset.mem_erase.mpr
      refine ⟨hne, Finset.mem_Icc.mpr ⟨?_, ?_⟩⟩
      · have hneg : -(j-i) ≤ ((j-i).natAbs : ℤ) := by
          simpa only [Int.natAbs_neg] using (Int.le_natAbs (a := -(j-i)))
        omega
      · have hpos := Int.le_natAbs (a := j-i)
        omega
    have hnum := Finset.card_le_card hsubset
    rw [Finset.card_erase_of_mem hmem, Int.card_Icc] at hnum
    omega
  have hrow (i : ℤ) (hi : i ∈ J) :
      |∑ j ∈ neighbors i, u i * v i * (u j * v j)| ≤ 2 * (D : ℝ) * B^2 := by
    calc
      _ ≤ ∑ j ∈ neighbors i, |u i * v i * (u j * v j)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j ∈ neighbors i, B^2 := by
        apply Finset.sum_le_sum
        intro j hj
        rw [abs_mul, sq]
        exact mul_le_mul (hweight i hi) (hweight j (Finset.mem_filter.mp hj).1)
          (abs_nonneg _) hB
      _ = ((neighbors i).card : ℝ) * B^2 := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard i) (sq_nonneg _)
  calc
    _ ≤ ∑ i ∈ J, |∑ j ∈ neighbors i, u i * v i * (u j * v j)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ J, 2 * (D : ℝ) * B^2 := Finset.sum_le_sum hrow
    _ = _ := by simp [mul_assoc]
