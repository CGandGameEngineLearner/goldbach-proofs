import Mathlib
import PEqualNP.Outside.L_twin_primes_window_bridge
import PEqualNP.Outside.L_twin_primes_divisor_bridge
import Conjectures.TwinPrimes.EnergyBridgeV2

-- child 1 zh: 取定常数 1/2：粗糙集中非素数且非半素数的元素最终至多占一半。
-- child 1 en: At the fixed constant 1/2, the rough-set elements that are neither prime nor semiprime make up at most half.
-- child 2 zh: 每个孪生素数对的前项都是"好"元素（素数即为好）。
-- child 2 en: The first member of every twin pair is good, since it is prime.

theorem Conjectures.Cuts.Cut52a9a3e7a7534ac26d0659ca
    (h₁ : ∀ B : ℕ, ∃ X : ℕ, B < X ∧ ↑(Finset.filter (fun x7 => ¬(Nat.Prime x7 ∨ ∃ x3 ∈ x7.divisors, Nat.Prime x3 ∧ Nat.Prime (x7 / x3) ∧ x3 ≠ x7 / x3)) (Finset.filter (fun x2 => (1 : ℕ) < x2 ∧ Nat.Prime (x2 + (2 : ℕ)) ∧ ∀ x3 ∈ x2.divisors, Nat.Prime x3 → B ≤ x3 ^ (10 : ℕ)) (Finset.range (B + (1 : ℕ))))).card ≤ (1 - 1/2) * ↑(Finset.filter (fun x2 => (1 : ℕ) < x2 ∧ Nat.Prime (x2 + (2 : ℕ)) ∧ ∀ x3 ∈ x2.divisors, Nat.Prime x3 → B ≤ x3 ^ (10 : ℕ)) (Finset.range (B + (1 : ℕ)))).card)
    (h₂ : ∀ n : ℕ, Nat.Prime n → Nat.Prime (n + (2 : ℕ)) → (Nat.Prime n ∨ ∃ d ∈ n.divisors, Nat.Prime d ∧ Nat.Prime (n / d) ∧ d ≠ n / d)) :
    (have x1 : ℕ → Finset ℕ := fun (x1 : ℕ) => {x2 ∈ Finset.range (x1 + (1 : ℕ)) | (1 : ℕ) < x2 ∧ Nat.Prime (x2 + (2 : ℕ)) ∧ ∀ x3 ∈ x2.divisors, Nat.Prime x3 → x1 ≤ x3 ^ (10 : ℕ)}; let x2 : ℕ → Prop := fun (x2 : ℕ) => Nat.Prime x2 ∨ ∃ x3 ∈ x2.divisors, Nat.Prime x3 ∧ Nat.Prime (x2 / x3) ∧ x3 ≠ x2 / x3; ∃ (x3 : ℝ), (0 : ℝ) < x3 ∧ ∃ (x4 : ℕ), ∀ (x5 : ℕ), x4 ≤ x5 → ↑{x7 ∈ x1 x5 | ¬x2 x7}.card ≤ ((1 : ℝ) - x3) * ↑(x1 x5).card) := by
  have hgood := h₂
  refine ⟨1/2, by norm_num, ?_⟩
  intro B
  obtain ⟨X, hB, hlt⟩ := h₁ B
  exact ⟨X, hB, hlt⟩
