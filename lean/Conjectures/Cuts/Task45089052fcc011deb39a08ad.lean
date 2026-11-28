import Mathlib
import Conjectures.Goldbach.RoughFifthBridge

/-!
Sign-counting identity for the rough-fifth candidate set, in the explicit (non-`let`) form
required by the cut statement: for every `N`,

  `2 * #{p ∈ C N : N - p prime} = |C N| - Σ_{p ∈ C N} λ(N - p) - 2 * #{p ∈ C N : Ω(N - p) = 3}`,

where `C N` is the set of primes `p < N` with `N < 3p < 2N`, `1 < N - p` and
`N < minFac (N - p) ^ 5`.  Every complement `N - p` then has `1 ≤ Ω(N - p) ≤ 4`
(the fifth-power roughness bound `minFac m ^ Ω m ≤ m`), which makes the identity a
pointwise check on `Ω ∈ {1,2,3,4}`.

Adapted from `Conjectures/Goldbach/RoughFifthBridge.lean` (accepted lemma
L-goldbach-rough-fifth-bridge), used directly rather than copied.
-/

theorem Conjectures.Cuts.Task45089052fcc011deb39a08ad :
    ∀ (x1 : ℕ), (2 : ℝ) * ↑{x2 ∈ {x2 ∈ Finset.range x1 | Nat.Prime x2 ∧ x1 < (3 : ℕ) * x2 ∧ (3 : ℕ) * x2 < (2 : ℕ) * x1 ∧ (1 : ℕ) < x1 - x2 ∧ x1 < (x1 - x2).minFac ^ (5 : ℕ)} | Nat.Prime (x1 - x2)}.card = ↑{x2 ∈ Finset.range x1 | Nat.Prime x2 ∧ x1 < (3 : ℕ) * x2 ∧ (3 : ℕ) * x2 < (2 : ℕ) * x1 ∧ (1 : ℕ) < x1 - x2 ∧ x1 < (x1 - x2).minFac ^ (5 : ℕ)}.card - ∑ x2 ∈ Finset.range x1 with Nat.Prime x2 ∧ x1 < (3 : ℕ) * x2 ∧ (3 : ℕ) * x2 < (2 : ℕ) * x1 ∧ (1 : ℕ) < x1 - x2 ∧ x1 < (x1 - x2).minFac ^ (5 : ℕ), ↑(ArithmeticFunction.liouville (x1 - x2)) - (2 : ℝ) * ↑{x2 ∈ {x2 ∈ Finset.range x1 | Nat.Prime x2 ∧ x1 < (3 : ℕ) * x2 ∧ (3 : ℕ) * x2 < (2 : ℕ) * x1 ∧ (1 : ℕ) < x1 - x2 ∧ x1 < (x1 - x2).minFac ^ (5 : ℕ)} | ArithmeticFunction.cardFactors (x1 - x2) = (3 : ℕ)}.card := by
  intro x1
  exact Conjectures.Goldbach.RoughFifthBridge x1
