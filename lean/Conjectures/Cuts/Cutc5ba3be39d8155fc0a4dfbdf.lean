import Mathlib

-- child 1 zh: 对每个自然数 n，2*n^6 都是两个素数之和（去掉冻结命题的「充分大」限制，是更强的闭前提）。
-- child 1 en: For every natural n, 2*n^6 is a sum of two primes (a stronger closed premise, removing the eventual restriction).
-- child 2 zh: 存在起点 N，使每个 n ≥ N 的 2*n^6 都有带序关系 p ≤ q 的两素数表示。
-- child 2 en: There is a threshold N such that every 2*n^6 with n ≥ N has a two-prime representation with the ordering p ≤ q.

theorem Conjectures.Cuts.Cutc5ba3be39d8155fc0a4dfbdf
    (h₁ : ∀ n : ℕ, ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = 2 * n ^ 6)
    (h₂ : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = 2 * n ^ 6 ∧ p ≤ q) :
    (∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = 2*n^6) := by
  obtain ⟨N, hN⟩ := h₂
  refine ⟨N, ?_⟩
  intro n hn
  obtain ⟨p, q, hp, hq, hpq, hle⟩ := hN n hn
  exact ⟨p, q, hp, hq, hpq⟩
