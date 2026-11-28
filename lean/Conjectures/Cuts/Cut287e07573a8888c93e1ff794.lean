import Mathlib

-- child 1 zh: ε ≤ 1 的情形：固定一个小的 ε 就足以给出表示。
-- child 1 en: The case 0 < ε ≤ 1: a fixed small epsilon already yields the representation.
-- child 2 zh: ε > 1 的情形。
-- child 2 en: The case 1 < ε of the same representation claim.

theorem Conjectures.Cuts.Cut287e07573a8888c93e1ff794
    (h₁ : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N → ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ ∃ a : Fin 6 → ℕ, N = p + q + ∑ i : Fin 6, 2 ^ (a i + 1) ∧ ((∑ i : Fin 6, (2 : ℕ) ^ (a i + 1) : ℕ) : ℝ) ≤ (N : ℝ) ^ ε)
    (h₂ : ∀ ε : ℝ, 1 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N → ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ ∃ a : Fin 6 → ℕ, N = p + q + ∑ i : Fin 6, 2 ^ (a i + 1) ∧ ((∑ i : Fin 6, (2 : ℕ) ^ (a i + 1) : ℕ) : ℝ) ≤ (N : ℝ) ^ ε) :
    (∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N → ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ ∃ a : Fin 6 → ℕ, N = p + q + ∑ i : Fin 6, 2 ^ (a i + 1) ∧ ((∑ i : Fin 6, (2 : ℕ) ^ (a i + 1) : ℕ) : ℝ) ≤ (N : ℝ) ^ ε) := by
  intro ε hε
  by_cases h : ε ≤ 1
  · exact h₁ ε hε h
  · exact h₂ ε (lt_of_not_ge h)
