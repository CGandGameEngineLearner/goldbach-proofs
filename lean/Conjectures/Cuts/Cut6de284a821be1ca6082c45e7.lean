import Mathlib

/-!
# 拆题：`L-goldbach-cut-3e346f15a42966fc1001fcc5` 按起点的奇偶两分

父题：在共同区间 $[X/2,2X)$ 中，表示数低于 $cX/(\log X)^2$ 的偶目标至多 $CX^{37/50}$ 个。

拆法按窗口起点 $X$ 的奇偶分成两支。两支的区间端点取整不同（$X/2$ 的取整与 $2X$ 的
奇偶性），这是筛法误差里唯一依赖起点奇偶的地方；其余部分两支完全平行。
两支覆盖全部 $X$（`Nat.even_or_odd`），故前提足够。

常数取两段的交集：$c=\min(c_1,c_2)$（更小的阈值只缩小集合），$C=\max(C_1,C_2)$。
-/

-- child 1 zh: 起点为偶数时，共同区间内低表示数偶目标至多 C X^(37/50)。
-- child 2 zh: 起点为奇数时，同一界成立。

theorem Conjectures.Cuts.Cut6de284a821be1ca6082c45e7
    (h₁ : (have x1 : ℕ → ℕ := fun (x1 : ℕ) => {x2 ∈ Finset.Icc (2 : ℕ) x1 | Nat.Prime x2 ∧ Nat.Prime (x1 - x2)}.card; ∃ (x2 : ℝ) (x3 : ℝ), (0 : ℝ) < x2 ∧ (0 : ℝ) < x3 ∧ ∃ (x4 : ℕ), ∀ x5 ≥ x4, Even x5 → ↑{x7 ∈ Finset.Ico (x5 / (2 : ℕ)) ((2 : ℕ) * x5) | Even x7 ∧ ↑(x1 x7) < x2 * ↑x5 / Real.log ↑x5 ^ (2 : ℕ)}.card ≤ x3 * ↑x5 ^ (37 / 50 : ℝ)))
    (h₂ : (have x1 : ℕ → ℕ := fun (x1 : ℕ) => {x2 ∈ Finset.Icc (2 : ℕ) x1 | Nat.Prime x2 ∧ Nat.Prime (x1 - x2)}.card; ∃ (x2 : ℝ) (x3 : ℝ), (0 : ℝ) < x2 ∧ (0 : ℝ) < x3 ∧ ∃ (x4 : ℕ), ∀ x5 ≥ x4, Odd x5 → ↑{x7 ∈ Finset.Ico (x5 / (2 : ℕ)) ((2 : ℕ) * x5) | Even x7 ∧ ↑(x1 x7) < x2 * ↑x5 / Real.log ↑x5 ^ (2 : ℕ)}.card ≤ x3 * ↑x5 ^ (37 / 50 : ℝ)))
    : (have x1 : ℕ → ℕ := fun (x1 : ℕ) => {x2 ∈ Finset.Icc (2 : ℕ) x1 | Nat.Prime x2 ∧ Nat.Prime (x1 - x2)}.card; ∃ (x2 : ℝ) (x3 : ℝ), (0 : ℝ) < x2 ∧ (0 : ℝ) < x3 ∧ ∃ (x4 : ℕ), ∀ x5 ≥ x4, ↑{x7 ∈ Finset.Ico (x5 / (2 : ℕ)) ((2 : ℕ) * x5) | Even x7 ∧ ↑(x1 x7) < x2 * ↑x5 / Real.log ↑x5 ^ (2 : ℕ)}.card ≤ x3 * ↑x5 ^ (37 / 50 : ℝ)) := by
  obtain ⟨c₁, C₁, hc₁, hC₁, N₁, hN₁⟩ := h₁
  obtain ⟨c₂, C₂, hc₂, hC₂, N₂, hN₂⟩ := h₂
  refine ⟨min c₁ c₂, max C₁ C₂, lt_min hc₁ hc₂, lt_max_of_lt_left hC₁, max (max N₁ N₂) 2, ?_⟩
  intro X hX
  have hX₁ : N₁ ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX
  have hX₂ : N₂ ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
  have hXge2 : 2 ≤ X := le_trans (le_max_right _ _) hX
  have hlogpos : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hLpos : 0 < Real.log (X : ℝ) ^ (2 : ℕ) := by positivity
  have hLnonneg : (0 : ℝ) ≤ Real.log (X : ℝ) ^ (2 : ℕ) := le_of_lt hLpos
  have hXnn : (0 : ℝ) ≤ (X : ℝ) := by positivity
  have hpow : (0 : ℝ) ≤ (X : ℝ) ^ (37 / 50 : ℝ) := Real.rpow_nonneg hXnn _
  have hmono : ∀ (c c' : ℝ), c ≤ c' →
      ((↑((Finset.Ico (X / 2) (2 * X)).filter
          (fun n => Even n ∧ (↑((Finset.Icc 2 n).filter (fun p => Nat.Prime p ∧ Nat.Prime (n - p))).card : ℝ)
            < c * ↑X / Real.log ↑X ^ (2 : ℕ))).card : ℝ))
        ≤ ((↑((Finset.Ico (X / 2) (2 * X)).filter
          (fun n => Even n ∧ (↑((Finset.Icc 2 n).filter (fun p => Nat.Prime p ∧ Nat.Prime (n - p))).card : ℝ)
            < c' * ↑X / Real.log ↑X ^ (2 : ℕ))).card : ℝ)) := by
    intro c c' hcc
    have hsub : ((Finset.Ico (X / 2) (2 * X)).filter
        (fun n => Even n ∧ (↑((Finset.Icc 2 n).filter (fun p => Nat.Prime p ∧ Nat.Prime (n - p))).card : ℝ)
          < c * ↑X / Real.log ↑X ^ (2 : ℕ)))
        ⊆ ((Finset.Ico (X / 2) (2 * X)).filter
        (fun n => Even n ∧ (↑((Finset.Icc 2 n).filter (fun p => Nat.Prime p ∧ Nat.Prime (n - p))).card : ℝ)
          < c' * ↑X / Real.log ↑X ^ (2 : ℕ))) := by
      intro n hn
      simp only [Finset.mem_filter] at hn ⊢
      refine ⟨hn.1, hn.2.1, ?_⟩
      have hle : c * (X : ℝ) / Real.log (X : ℝ) ^ (2 : ℕ)
          ≤ c' * (X : ℝ) / Real.log (X : ℝ) ^ (2 : ℕ) := by
        apply div_le_div_of_nonneg_right _ (le_of_lt hLpos)
        exact mul_le_mul_of_nonneg_right hcc hXnn
      exact lt_of_lt_of_le hn.2.2 hle
    exact_mod_cast Finset.card_le_card hsub
  rcases Nat.even_or_odd X with he | ho
  · exact le_trans (hmono _ _ (min_le_left _ _))
      (le_trans (hN₁ X hX₁ he) (by gcongr; exact le_max_left _ _))
  · exact le_trans (hmono _ _ (min_le_right _ _))
      (le_trans (hN₂ X hX₂ ho) (by gcongr; exact le_max_right _ _))