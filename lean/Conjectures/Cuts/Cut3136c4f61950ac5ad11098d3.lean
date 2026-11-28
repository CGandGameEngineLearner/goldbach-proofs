import Mathlib
import Conjectures.TwinPrimes.SharpWindowContamination

-- child 1 zh: 在更窄的子窗 (X, 101X/100) 内孪生素数对已至少为 c·X/(log X)²。
-- child 1 en: Inside the narrower sub-window (X, 101X/100) the twin pairs already reach c*X/(log X)^2.
-- child 2 zh: 窄窗是原窗的子集，故窄窗计数不超过原窗计数。
-- child 2 en: The narrow window is contained in the original one, so its count is at most the original count.

theorem Conjectures.Cuts.Cut3136c4f61950ac5ad11098d3
    (h₁ : ∃ c : ℝ, 0 < c ∧ ∀ B : ℕ, ∃ X : ℕ, B < X ∧ c * ↑X / Real.log ↑X ^ (2 : ℕ) ≤ ↑{x4 ∈ Finset.range ((2 : ℕ) * X + (1 : ℕ)) | X < x4 ∧ (100 : ℕ) * x4 < (101 : ℕ) * X ∧ Nat.Prime x4 ∧ Nat.Prime (x4 + (2 : ℕ))}.card)
    (h₂ : ∀ X : ℕ, (↑{x4 ∈ Finset.range ((2 : ℕ) * X + (1 : ℕ)) | X < x4 ∧ (100 : ℕ) * x4 < (101 : ℕ) * X ∧ Nat.Prime x4 ∧ Nat.Prime (x4 + (2 : ℕ))}.card : ℝ) ≤ (↑{x4 ∈ Finset.range ((2 : ℕ) * X + (1 : ℕ)) | X < x4 ∧ (50 : ℕ) * x4 < (51 : ℕ) * X ∧ Nat.Prime x4 ∧ Nat.Prime (x4 + (2 : ℕ))}.card : ℝ)) :
    (∃ (x1 : ℝ), (0 : ℝ) < x1 ∧ ∀ (x2 : ℕ), ∃ (x3 : ℕ), x2 < x3 ∧ x1 * ↑x3 / Real.log ↑x3 ^ (2 : ℕ) ≤ ↑{x4 ∈ Finset.range ((2 : ℕ) * x3 + (1 : ℕ)) | x3 < x4 ∧ (50 : ℕ) * x4 < (51 : ℕ) * x3 ∧ Nat.Prime x4 ∧ Nat.Prime (x4 + (2 : ℕ))}.card) := by
  obtain ⟨c, hc, hX⟩ := h₁
  refine ⟨c, hc, ?_⟩
  intro B
  obtain ⟨X, hB, hle⟩ := hX B
  exact ⟨X, hB, le_trans hle (h₂ X)⟩
