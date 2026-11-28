import Mathlib

-- child 1 zh: 对每个 ε>0，每个充分大偶数 N 都有正数量的容许对 (p, a)：p 为素数，N - (p + Σ_{i<6} 2^(a_i+1)) 为素数，且六幂总偏移不超过 N^ε。
-- child 1 en: For every ε>0, every sufficiently large even N has a positive number of admissible pairs (p, a) with p prime, N - (p + sum_i 2^(a_i+1)) prime, and the six-power total shift at most N^ε.
-- child 2 zh: 容许对个数为正时取出见证，得到两个素数加六个二幂、且总偏移落在 N^ε 内的表示。
-- child 2 en: A positive admissible count yields a witness representation by two primes and six powers of two whose total shift lies inside the N^ε budget.

theorem Conjectures.Cuts.Cut18f56b9dbac4d9f7db4628d1
    (h₁ : ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N →
      0 < {x ∈ (Finset.range (N + 1)).product (Fintype.piFinset fun (_ : Fin 6) => Finset.range (N + 1)) |
        Nat.Prime x.1 ∧ Nat.Prime (N - (x.1 + ∑ i : Fin 6, 2 ^ (x.2 i + 1))) ∧
        ((∑ i : Fin 6, (2 : ℕ) ^ (x.2 i + 1) : ℕ) : ℝ) ≤ (N : ℝ) ^ ε}.card)
    (h₂ : ∀ ε : ℝ, 0 < ε → ∀ N : ℕ,
      0 < {x ∈ (Finset.range (N + 1)).product (Fintype.piFinset fun (_ : Fin 6) => Finset.range (N + 1)) |
        Nat.Prime x.1 ∧ Nat.Prime (N - (x.1 + ∑ i : Fin 6, 2 ^ (x.2 i + 1))) ∧
        ((∑ i : Fin 6, (2 : ℕ) ^ (x.2 i + 1) : ℕ) : ℝ) ≤ (N : ℝ) ^ ε}.card →
      ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ ∃ a : Fin 6 → ℕ,
        N = p + q + ∑ i : Fin 6, 2 ^ (a i + 1) ∧ ((∑ i : Fin 6, (2 : ℕ) ^ (a i + 1) : ℕ) : ℝ) ≤ (N : ℝ) ^ ε) :
    (∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N → ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ ∃ a : Fin 6 → ℕ, N = p + q + ∑ i : Fin 6, 2 ^ (a i + 1) ∧ ((∑ i : Fin 6, (2 : ℕ) ^ (a i + 1) : ℕ) : ℝ) ≤ (N : ℝ) ^ ε) := by
  intro ε hε
  obtain ⟨N₀, hN⟩ := h₁ ε hε
  exact ⟨N₀, fun N hN₀ hEven => h₂ ε hε N (hN N hN₀ hEven)⟩
