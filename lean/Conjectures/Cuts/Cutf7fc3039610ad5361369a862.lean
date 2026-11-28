import Mathlib
import Conjectures.TwinPrimes.SharpWindowContamination

-- child 1 zh: 二倍区间 (X,2X] 内孪生素数对计数最终至少为 c·X/(log X)^2。
-- child 1 en: The twin-pair count in (X,2X] is eventually at least c*X/(log X)^2.
-- child 2 zh: 对任意截点 B 和下界 N，可取到同时超过两者的 X。
-- child 2 en: For any cutoff B and lower bound N, one can pick X exceeding both.

theorem Conjectures.Cuts.Cutf7fc3039610ad5361369a862
    (h₁ : ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ X : ℕ, N ≤ X → c * ↑X / (Real.log ↑X) ^ (2 : ℕ) ≤ ↑{x4 ∈ Finset.Ioc X ((2 : ℕ) * X) | Nat.Prime x4 ∧ Nat.Prime (x4 + (2 : ℕ))}.card)
    (h₂ : ∀ (B : ℕ) (N : ℕ), ∃ X : ℕ, B < X ∧ N ≤ X) :
    (∃ (x1 : ℝ), (0 : ℝ) < x1 ∧ ∀ (x2 : ℕ), ∃ (x3 : ℕ), x2 < x3 ∧ x1 * ↑x3 / Real.log ↑x3 ^ (2 : ℕ) ≤ ↑{x4 ∈ Finset.Ioc x3 ((2 : ℕ) * x3) | Nat.Prime x4 ∧ Nat.Prime (x4 + (2 : ℕ))}.card) := by
  obtain ⟨c, hc, N, hS⟩ := h₁
  refine ⟨c, hc, ?_⟩
  intro B
  obtain ⟨X, hB, hNX⟩ := h₂ B N
  refine ⟨X, hB, ?_⟩
  exact hS X hNX
