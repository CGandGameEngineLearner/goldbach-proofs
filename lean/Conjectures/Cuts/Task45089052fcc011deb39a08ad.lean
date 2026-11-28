import Mathlib
import Conjectures.Goldbach.RoughFifthBridge

theorem Conjectures.Cuts.Task45089052fcc011deb39a08ad : (∀ (x1 : ℕ), (2 : ℝ) * ↑{x2 ∈ {x2 ∈ Finset.range x1 | Nat.Prime x2 ∧ x1 < (3 : ℕ) * x2 ∧ (3 : ℕ) * x2 < (2 : ℕ) * x1 ∧ (1 : ℕ) < x1 - x2 ∧ x1 < (x1 - x2).minFac ^ (5 : ℕ)} | Nat.Prime (x1 - x2)}.card = ↑{x2 ∈ Finset.range x1 | Nat.Prime x2 ∧ x1 < (3 : ℕ) * x2 ∧ (3 : ℕ) * x2 < (2 : ℕ) * x1 ∧ (1 : ℕ) < x1 - x2 ∧ x1 < (x1 - x2).minFac ^ (5 : ℕ)}.card - ∑ x2 ∈ Finset.range x1 with Nat.Prime x2 ∧ x1 < (3 : ℕ) * x2 ∧ (3 : ℕ) * x2 < (2 : ℕ) * x1 ∧ (1 : ℕ) < x1 - x2 ∧ x1 < (x1 - x2).minFac ^ (5 : ℕ), ↑(ArithmeticFunction.liouville (x1 - x2)) - (2 : ℝ) * ↑{x2 ∈ {x2 ∈ Finset.range x1 | Nat.Prime x2 ∧ x1 < (3 : ℕ) * x2 ∧ (3 : ℕ) * x2 < (2 : ℕ) * x1 ∧ (1 : ℕ) < x1 - x2 ∧ x1 < (x1 - x2).minFac ^ (5 : ℕ)} | ArithmeticFunction.cardFactors (x1 - x2) = (3 : ℕ)}.card) := by
  exact Conjectures.Goldbach.RoughFifthBridge
