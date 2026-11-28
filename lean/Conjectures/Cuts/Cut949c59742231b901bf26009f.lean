import Mathlib

-- child 1 zh: 每个充分大偶数 N 都有正数量的容许对 (p, a)：p 为素数，且 N - (p + Σ_{i<5} 2^(a_i+1)) 也是素数。
-- child 1 en: Every sufficiently large even N has a positive number of admissible pairs (p, a) with p prime and N - (p + sum_i 2^(a_i+1)) prime.
-- child 2 zh: 容许对个数为正时可取出见证，得到两个素数加五个二幂的表示。
-- child 2 en: A positive admissible count yields a witness representation by two primes plus five powers of two.

theorem Conjectures.Cuts.Cut949c59742231b901bf26009f
    (h₁ : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N →
      0 < {x ∈ (Finset.range (N + 1)).product (Fintype.piFinset fun (_ : Fin 5) => Finset.range (N + 1)) |
        Nat.Prime x.1 ∧ Nat.Prime (N - (x.1 + ∑ i : Fin 5, 2 ^ (x.2 i + 1)))}.card)
    (h₂ : ∀ N : ℕ,
      0 < {x ∈ (Finset.range (N + 1)).product (Fintype.piFinset fun (_ : Fin 5) => Finset.range (N + 1)) |
        Nat.Prime x.1 ∧ Nat.Prime (N - (x.1 + ∑ i : Fin 5, 2 ^ (x.2 i + 1)))}.card →
      ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ ∃ a : Fin 5 → ℕ, N = p + q + ∑ i : Fin 5, 2 ^ (a i + 1)) :
    (∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N → ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ ∃ a : Fin 5 → ℕ, N = p + q + ∑ i : Fin 5, 2 ^ (a i + 1)) := by
  obtain ⟨N₀, hN⟩ := h₁
  exact ⟨N₀, fun N hN₀ hEven => h₂ N (hN N hN₀ hEven)⟩
