import Mathlib

-- child 1 zh: 长窗口（H ≥ √X）：例外数满足幂节省 H^(1-δ)。这一步是较长窗口上的标准能量/密度估计。
-- child 1 en: Long windows (H ≥ sqrt X): the exceptional count obeys the power saving H^(1-delta). This is the standard energy/density estimate on longer windows.
-- child 2 zh: 短窗口（X^(7/120+ε) < H < √X）：同一幂节省。真正的前沿在这一段。
-- child 2 en: Short windows (X^(7/120+eps) < H < sqrt X): the same power saving. This is where the frontier actually is.

theorem Conjectures.Cuts.Cut1041f77f613ed2e210734478
    (h₁ : ∀ ε : ℝ, 0 < ε → ∃ δ C : ℝ, 0 < δ ∧ δ < 1 ∧ 0 < C ∧ ∃ N : ℕ,
      ∀ X H : ℕ, N ≤ X → H ≤ X → (X : ℝ) ^ ((7 : ℝ) / 120 + ε) < (H : ℝ) →
        (X : ℝ) ^ (1 / 2 : ℝ) ≤ (H : ℝ) →
        ((((Finset.Icc (X - H) X).filter (fun n => 4 ≤ n ∧ Even n ∧
          ∀ p ∈ Finset.range (n + 1), ¬ (Nat.Prime p ∧ Nat.Prime (n - p)))).card) : ℝ) ≤
          C * (H : ℝ) ^ (1 - δ))
    (h₂ : ∀ ε : ℝ, 0 < ε → ∃ δ C : ℝ, 0 < δ ∧ δ < 1 ∧ 0 < C ∧ ∃ N : ℕ,
      ∀ X H : ℕ, N ≤ X → H ≤ X → (X : ℝ) ^ ((7 : ℝ) / 120 + ε) < (H : ℝ) →
        (H : ℝ) < (X : ℝ) ^ (1 / 2 : ℝ) →
        ((((Finset.Icc (X - H) X).filter (fun n => 4 ≤ n ∧ Even n ∧
          ∀ p ∈ Finset.range (n + 1), ¬ (Nat.Prime p ∧ Nat.Prime (n - p)))).card) : ℝ) ≤
          C * (H : ℝ) ^ (1 - δ)) :
    (∀ ε : ℝ, 0 < ε → ∃ δ C : ℝ, 0 < δ ∧ δ < 1 ∧ 0 < C ∧ ∃ N : ℕ,
      ∀ X H : ℕ, N ≤ X → H ≤ X → (X : ℝ) ^ ((7 : ℝ) / 120 + ε) < (H : ℝ) →
        ((((Finset.Icc (X - H) X).filter (fun n => 4 ≤ n ∧ Even n ∧
          ∀ p ∈ Finset.range (n + 1), ¬ (Nat.Prime p ∧ Nat.Prime (n - p)))).card) : ℝ) ≤
          C * (H : ℝ) ^ (1 - δ)) := by
  classical
  intro ε hε
  obtain ⟨δ₁, C₁, hδ₁, hδ₁lt, hC₁, N₁, hP₁⟩ := h₁ ε hε
  obtain ⟨δ₂, C₂, hδ₂, hδ₂lt, hC₂, N₂, hP₂⟩ := h₂ ε hε
  refine ⟨min δ₁ δ₂, max C₁ C₂, lt_min hδ₁ hδ₂, min_lt_iff.mpr (Or.inl hδ₁lt),
    lt_max_of_lt_left hC₁, max (max N₁ N₂) 4, ?_⟩
  intro X H hX hH hbig
  have hX4 : 4 ≤ X := le_trans (le_max_right (max N₁ N₂) 4) hX
  have hX₁ : N₁ ≤ X := le_trans (le_trans (le_max_left N₁ N₂) (le_max_left (max N₁ N₂) 4)) hX
  have hX₂ : N₂ ≤ X := le_trans (le_trans (le_max_right N₁ N₂) (le_max_left (max N₁ N₂) 4)) hX
  have hXpos : (1 : ℝ) < (X : ℝ) := by exact_mod_cast (by omega : 1 < X)
  have hone : (1 : ℝ) < (X : ℝ) ^ ((7 : ℝ) / 120 + ε) := Real.one_lt_rpow hXpos (by positivity)
  have hH1 : (1 : ℝ) ≤ (H : ℝ) := le_of_lt (lt_trans hone hbig)
  have hCmax : (0 : ℝ) < max C₁ C₂ := lt_max_of_lt_left hC₁
  by_cases hcase : (X : ℝ) ^ (1 / 2 : ℝ) ≤ (H : ℝ)
  · have hb := hP₁ X H hX₁ hH hbig hcase
    refine hb.trans ?_
    have hexp : (1 : ℝ) - δ₁ ≤ 1 - min δ₁ δ₂ := by linarith [min_le_left δ₁ δ₂]
    have hmono : (H : ℝ) ^ (1 - δ₁) ≤ (H : ℝ) ^ (1 - min δ₁ δ₂) :=
      Real.rpow_le_rpow_of_exponent_le hH1 hexp
    have hnonneg : (0 : ℝ) ≤ (H : ℝ) ^ (1 - δ₁) := Real.rpow_nonneg (by positivity) _
    calc C₁ * (H : ℝ) ^ (1 - δ₁) ≤ (max C₁ C₂) * (H : ℝ) ^ (1 - δ₁) :=
          mul_le_mul_of_nonneg_right (le_max_left C₁ C₂) hnonneg
      _ ≤ (max C₁ C₂) * (H : ℝ) ^ (1 - min δ₁ δ₂) :=
          mul_le_mul_of_nonneg_left hmono (le_of_lt hCmax)
  · have hlt : (H : ℝ) < (X : ℝ) ^ (1 / 2 : ℝ) := not_le.mp hcase
    have hb := hP₂ X H hX₂ hH hbig hlt
    refine hb.trans ?_
    have hexp : (1 : ℝ) - δ₂ ≤ 1 - min δ₁ δ₂ := by linarith [min_le_right δ₁ δ₂]
    have hmono : (H : ℝ) ^ (1 - δ₂) ≤ (H : ℝ) ^ (1 - min δ₁ δ₂) :=
      Real.rpow_le_rpow_of_exponent_le hH1 hexp
    have hnonneg : (0 : ℝ) ≤ (H : ℝ) ^ (1 - δ₂) := Real.rpow_nonneg (by positivity) _
    calc C₂ * (H : ℝ) ^ (1 - δ₂) ≤ (max C₁ C₂) * (H : ℝ) ^ (1 - δ₂) :=
          mul_le_mul_of_nonneg_right (le_max_right C₁ C₂) hnonneg
      _ ≤ (max C₁ C₂) * (H : ℝ) ^ (1 - min δ₁ δ₂) :=
          mul_le_mul_of_nonneg_left hmono (le_of_lt hCmax)
