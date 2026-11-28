import Mathlib

attribute [local instance] Classical.propDecidable

-- child 1 zh: 对每个充分大 X 与每个满足 X ≤ y、y + W y ≤ 2X 的 y，短窗 [y, y + W y] 内满足条件的偶数 n 计数为正（含 sqrt X 量级的素因子）。
-- child 1 en: For every sufficiently large X and every y with X ≤ y and y + W y ≤ 2 * X, the short window [y, y + W y] contains a positive number of even n admitting a prime pair with sqrt X ≤ p ≤ 2 * sqrt X.
-- child 2 zh: 短窗内计数为正时可取出见证 n 及其素数对。
-- child 2 en: A positive count in the short window yields a witness n together with its prime pair.

theorem Conjectures.Cuts.Cutc96ba331157f669dbac7a002
    (h₁ : ∃ X₀ : ℕ, ∀ X ≥ X₀, ∀ y : ℕ, X ≤ y →
      y + Nat.floor ((y : ℝ) ^ ((26 : ℝ) / 1075)) ≤ 2 * X →
      0 < {n ∈ Finset.Icc y (y + Nat.floor ((y : ℝ) ^ ((26 : ℝ) / 1075))) |
        Even n ∧ ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ Nat.sqrt X ≤ p ∧ p ≤ 2 * Nat.sqrt X ∧ p + q = n}.card)
    (h₂ : ∀ X y : ℕ,
      0 < {n ∈ Finset.Icc y (y + Nat.floor ((y : ℝ) ^ ((26 : ℝ) / 1075))) |
        Even n ∧ ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ Nat.sqrt X ≤ p ∧ p ≤ 2 * Nat.sqrt X ∧ p + q = n}.card →
      ∃ n : ℕ, y ≤ n ∧ n ≤ y + Nat.floor ((y : ℝ) ^ ((26 : ℝ) / 1075)) ∧ Even n ∧
        (∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ Nat.sqrt X ≤ p ∧ p ≤ 2 * Nat.sqrt X ∧ p + q = n)) :
    (let W := fun y : ℕ => Nat.floor ((y : ℝ) ^ ((26 : ℝ) / 1075)); ∃ X₀ : ℕ, ∀ X ≥ X₀, ∀ y : ℕ, X ≤ y → y + W y ≤ 2 * X → ∃ n : ℕ, y ≤ n ∧ n ≤ y + W y ∧ Even n ∧ (∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ Nat.sqrt X ≤ p ∧ p ≤ 2 * Nat.sqrt X ∧ p + q = n)) := by
  simp only []
  obtain ⟨X₀, hX⟩ := h₁
  exact ⟨X₀, fun X hX0 y hy hy2 => h₂ X y (hX X hX0 y hy hy2)⟩
