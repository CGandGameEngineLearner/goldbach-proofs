import Mathlib
import Conjectures.TwinPrimes.SharpWindowContamination

-- child 1 zh: 二倍区间内孪生素数对计数最终至少为 c·X/(log X)^2，其中 c≥1。
-- child 1 en: The dyadic twin-pair count is eventually at least c*X/(log X)^2 for some c≥1.
-- child 2 zh: 当 X≥3 时 X/(log X)^2 非负，且 c≥1 故 X/(log X)^2 ≤ c·X/(log X)^2。
-- child 2 en: For X≥3 the quantity X/(log X)^2 is nonnegative and c≥1, so it is at most c times itself.

theorem Conjectures.Cuts.Cutf31d3abc8526587b60057ac0
    (h₁ : ∃ (N : ℕ) (c : ℝ), 1 ≤ c ∧ ∀ X : ℕ, N ≤ X → c * (↑X / (Real.log ↑X) ^ (2 : ℕ)) ≤ ↑{x4 ∈ Finset.Ioc X ((2 : ℕ) * X) | Nat.Prime x4 ∧ Nat.Prime (x4 + (2 : ℕ))}.card)
    (h₂ : ∀ (c : ℝ), 1 ≤ c → ∀ X : ℕ, 3 ≤ X → (↑X / (Real.log ↑X) ^ (2 : ℕ)) ≤ c * (↑X / (Real.log ↑X) ^ (2 : ℕ))) :
    (∃ (x1 : ℕ), ∀ (x2 : ℕ), x1 ≤ x2 → ↑x2 / Real.log ↑x2 ^ (2 : ℕ) ≤ ↑{x4 ∈ Finset.Ioc x2 ((2 : ℕ) * x2) | Nat.Prime x4 ∧ Nat.Prime (x4 + (2 : ℕ))}.card) := by
  obtain ⟨N, c, hc, hS⟩ := h₁
  refine ⟨max N 3, ?_⟩
  intro X hX
  have hNX : N ≤ X := by omega
  have h3X : 3 ≤ X := by omega
  exact le_trans (h₂ c hc X h3X) (hS X hNX)
