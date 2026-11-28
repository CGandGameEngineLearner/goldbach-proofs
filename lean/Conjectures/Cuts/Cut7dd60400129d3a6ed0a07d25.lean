import Mathlib

-- child 1 zh: 充分大的偶数可写成两个素数与恰好六个正指数二次幂之和。
-- child 1 en: Every sufficiently large even integer is a sum of two primes and exactly six positive powers of two.
-- child 2 zh: 给六项二次幂的指数元组添入七个指数 1，得到总和恰好多 14 的十三项元组。
-- child 2 en: Pad a six-term tuple with seven copies of 2 to obtain a thirteen-term tuple of total weight 14 more.
theorem Conjectures.Cuts.Cut7dd60400129d3a6ed0a07d25
    (hSix : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N →
      ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧
        ∃ a : Fin 6 → ℕ, N = p + q + ∑ i : Fin 6, 2 ^ (a i + 1))
    (hPad : ∀ a : Fin 6 → ℕ, ∃ e : Fin 13 → ℕ,
      (∑ j : Fin 13, (2 : ℕ) ^ (e j + 1)) =
        (∑ i : Fin 6, (2 : ℕ) ^ (a i + 1)) + 14) :
    (∃ N : ℕ, ∀ n ≥ N, Even n → ∃ (p q : ℕ) (e : Fin 13 → ℕ), Nat.Prime p ∧ Nat.Prime q ∧ n = p+q+∑ j, 2^(e j+1)) := by
  obtain ⟨N₀, hSix⟩ := hSix
  refine ⟨N₀ + 14, ?_⟩
  intro n hn hEven
  have hThreshold : N₀ ≤ n - 14 := by omega
  have hShiftEven : Even (n - 14) := by
    obtain ⟨k, hk⟩ := hEven
    exact ⟨k - 7, by omega⟩
  obtain ⟨p, q, hp, hq, a, ha⟩ := hSix (n - 14) hThreshold hShiftEven
  obtain ⟨e, he⟩ := hPad a
  exact ⟨p, q, e, hp, hq, by omega⟩
