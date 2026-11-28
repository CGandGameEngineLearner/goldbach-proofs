import Mathlib

-- child 1 zh: 支撑前提：每个充分大的偶数 n 都有一个中心素数 p，即素数 p 满足 n/3 ≤ p ≤ 2n/3（等价于 3p ≤ 2n ≤ 6p）。
-- child 1 en: Support premise: every sufficiently large even n has a central prime p, i.e. a prime p with 3p ≤ 2n ≤ 6p.
-- child 2 zh: 三点平滑前提：对每个充分大的偶数 n 与每个中心素数 p，三个相邻偶数目标 n-2、n、n+2 中至少有一个可写成 p+q（q 为素数）。这一步是对中心移位三点卷积做统一下界估计的解析内容。
-- child 2 en: Three-point smoothing premise: for every sufficiently large even n and every central prime p, one of the three consecutive even targets n-2, n, n+2 is p+q with q prime. This is the analytic content, a uniform lower bound for the three-point convolution at the central shift.

theorem Conjectures.Cuts.Cut7ea882223d66bcade8c0350c
    (h₁ : ∃ N₁ : ℕ, ∀ n : ℕ, N₁ ≤ n → Even n →
      ∃ p : ℕ, Nat.Prime p ∧ 3 * p ≤ 2 * n ∧ 2 * n ≤ 6 * p)
    (h₂ : ∃ N₂ : ℕ, ∀ n : ℕ, N₂ ≤ n → Even n → ∀ p : ℕ, Nat.Prime p →
      3 * p ≤ 2 * n → 2 * n ≤ 6 * p →
      (∃ q : ℕ, Nat.Prime q ∧ p + q = n) ∨
        (∃ q : ℕ, Nat.Prime q ∧ p + q + 2 = n) ∨
          (∃ q : ℕ, Nat.Prime q ∧ p + q = n + 2)) :
    (∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → Even n → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧
      3 * p ≤ 2 * n ∧ 2 * n ≤ 6 * p ∧ |(p : ℤ) + (q : ℤ) - (n : ℤ)| ≤ 2) := by
  classical
  obtain ⟨N₁, hN₁⟩ := h₁
  obtain ⟨N₂, hN₂⟩ := h₂
  refine ⟨max N₁ N₂, ?_⟩
  intro n hn hnEven
  have hN₁' : N₁ ≤ n := le_trans (le_max_left N₁ N₂) hn
  have hN₂' : N₂ ≤ n := le_trans (le_max_right N₁ N₂) hn
  obtain ⟨p, hpPrime, hpLo, hpHi⟩ := hN₁ n hN₁' hnEven
  rcases hN₂ n hN₂' hnEven p hpPrime hpLo hpHi with ⟨q, hqPrime, hq⟩ |
    ⟨q, hqPrime, hq⟩ | ⟨q, hqPrime, hq⟩
  · refine ⟨p, q, hpPrime, hqPrime, hpLo, hpHi, ?_⟩
    have hcast : (p : ℤ) + (q : ℤ) - (n : ℤ) = 0 := by
      have h : (p : ℤ) + (q : ℤ) = (n : ℤ) := by exact_mod_cast hq
      linarith
    rw [hcast]
    norm_num
  · refine ⟨p, q, hpPrime, hqPrime, hpLo, hpHi, ?_⟩
    have hcast : (p : ℤ) + (q : ℤ) - (n : ℤ) = -2 := by
      have h : (p : ℤ) + (q : ℤ) + 2 = (n : ℤ) := by exact_mod_cast hq
      linarith
    rw [hcast]
    norm_num
  · refine ⟨p, q, hpPrime, hqPrime, hpLo, hpHi, ?_⟩
    have hcast : (p : ℤ) + (q : ℤ) - (n : ℤ) = 2 := by
      have h : (p : ℤ) + (q : ℤ) = (n : ℤ) + 2 := by exact_mod_cast hq
      linarith
    rw [hcast]
    norm_num
