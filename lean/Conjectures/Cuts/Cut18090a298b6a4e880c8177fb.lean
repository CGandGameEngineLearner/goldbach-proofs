import Mathlib
import PEqualNP.Outside.L_twin_primes_window_bridge
import PEqualNP.Outside.L_twin_primes_divisor_bridge
import Conjectures.TwinPrimes.EnergyBridgeV2

-- child 1 zh: 粗糙集中素数或半素数的个数至少占固定正比例。
-- child 1 en: Primes or semiprimes make up a fixed positive proportion of the rough set.
-- child 2 zh: 两种元素互补，故不在其中的元素计数不超过粗糙集基数减去素数或半素数计数。
-- child 2 en: The two classes are complementary, so the remaining count is at most the rough count minus the prime-or-semiprime count.

theorem Conjectures.Cuts.Cut18090a298b6a4e880c8177fb
    (h₁ : ∃ c : ℝ, 0 < c ∧ ∃ B0 : ℕ, ∀ B : ℕ, B0 ≤ B →
      c * ↑(({n ∈ Finset.range (B + 1) | 1 < n ∧ Nat.Prime (n + 2) ∧ ∀ p ∈ n.divisors, Nat.Prime p → B ≤ p ^ 10} : Finset ℕ).card) ≤
        ↑((({n ∈ Finset.range (B + 1) | 1 < n ∧ Nat.Prime (n + 2) ∧ ∀ p ∈ n.divisors, Nat.Prime p → B ≤ p ^ 10} : Finset ℕ).filter (fun n => Nat.Prime n ∨ ∃ d ∈ n.divisors, Nat.Prime d ∧ Nat.Prime (n / d) ∧ d ≠ n / d)).card))
    (h₂ : ∀ B : ℕ,
      ↑((({n ∈ Finset.range (B + 1) | 1 < n ∧ Nat.Prime (n + 2) ∧ ∀ p ∈ n.divisors, Nat.Prime p → B ≤ p ^ 10} : Finset ℕ).filter (fun n => ¬ ((fun n => Nat.Prime n ∨ ∃ d ∈ n.divisors, Nat.Prime d ∧ Nat.Prime (n / d) ∧ d ≠ n / d)) n)).card) ≤
        ↑(({n ∈ Finset.range (B + 1) | 1 < n ∧ Nat.Prime (n + 2) ∧ ∀ p ∈ n.divisors, Nat.Prime p → B ≤ p ^ 10} : Finset ℕ).card) - ↑((({n ∈ Finset.range (B + 1) | 1 < n ∧ Nat.Prime (n + 2) ∧ ∀ p ∈ n.divisors, Nat.Prime p → B ≤ p ^ 10} : Finset ℕ).filter (fun n => Nat.Prime n ∨ ∃ d ∈ n.divisors, Nat.Prime d ∧ Nat.Prime (n / d) ∧ d ≠ n / d)).card)) :
    (have x1 : ℕ → Finset ℕ := fun (x1 : ℕ) => {x2 ∈ Finset.range (x1 + (1 : ℕ)) | (1 : ℕ) < x2 ∧ Nat.Prime (x2 + (2 : ℕ)) ∧ ∀ x3 ∈ x2.divisors, Nat.Prime x3 → x1 ≤ x3 ^ (10 : ℕ)};
     let x2 : ℕ → Prop := fun (x2 : ℕ) => Nat.Prime x2 ∨ ∃ x3 ∈ x2.divisors, Nat.Prime x3 ∧ Nat.Prime (x2 / x3) ∧ x3 ≠ x2 / x3;
     ∃ (x3 : ℝ), (0 : ℝ) < x3 ∧ ∃ (x4 : ℕ), ∀ (x5 : ℕ), x4 ≤ x5 →
       ↑{x7 ∈ x1 x5 | ¬x2 x7}.card ≤ ((1 : ℝ) - x3) * ↑(x1 x5).card) := by
  obtain ⟨c, hc, B0, hB0⟩ := h₁
  refine ⟨c, hc, B0, ?_⟩
  intro B hB
  have h1 := hB0 B hB
  have h2 := h₂ B
  nlinarith [h1, h2]
