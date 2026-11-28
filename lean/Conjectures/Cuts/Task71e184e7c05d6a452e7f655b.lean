import Mathlib
import PEqualNP.Outside.L_twin_primes_positive_product

/-!
# Conjectures.Cuts.Task71e184e7c05d6a452e7f655b

The negative main term (the twin-prime constant term) shifts the constant 1
strictly below 1.

The content of the statement is the strict inequality -2 * x5 / 50 + 1 < 1,
that is 0 < x5, where x5 is the twin-prime constant
prod over primes p > 2 of (1 - 1/(p-1)^2).  Its positivity is exactly the
accepted module PEqualNP.Outside.L_twin_primes_positive_product, imported
here; the remaining step is linear arithmetic.

Adapted from PEqualNP.Outside.L_twin_primes_positive_product (accepted
result L-twin-primes-positive-product).
-/

theorem Conjectures.Cuts.Task71e184e7c05d6a452e7f655b :
    have x1 : ℕ → Finset ℕ := fun (x1 : ℕ) => {x2 ∈ Finset.range ((2 : ℕ) * x1 + (1 : ℕ)) | x1 < x2 ∧ (50 : ℕ) * x2 < (51 : ℕ) * x1}; have x2 : ℕ → ℝ := fun (x2 : ℕ) => -(↑((ArithmeticFunction.moebius : ℕ → ℤ) x2) : ℝ) * Real.log (↑x2 : ℝ); have x3 : ℕ → ℕ := fun (x3 : ℕ) => ⌊(↑x3 : ℝ) ^ (1 / 3 : ℝ)⌋₊; have x4 : ℕ → ℕ := fun (x4 : ℕ) => ⌊√(↑x4 : ℝ) / Real.log ((2 : ℝ) + (↑x4 : ℝ)) ^ (5 : ℕ)⌋₊; have x5 : ℝ := ∏' (x5 : ℕ), if Nat.Prime x5 ∧ (2 : ℕ) < x5 then (1 : ℝ) - (1 : ℝ) / ((↑x5 : ℝ) - (1 : ℝ)) ^ (2 : ℕ) else (1 : ℝ); have x6 : ℕ → ℝ := fun (x6 : ℕ) => (∑ x7 ∈ x1 x6 with Nat.Prime x7, Real.log (↑x7 : ℝ) * {x8 ∈ (x7 + (2 : ℕ)).divisors | x3 x6 < x8 ∧ x4 x6 < x8}.sum x2) / (↑x6 : ℝ); (-2 : ℝ) * x5 / (50 : ℝ) + (1 : ℝ) < (1 : ℝ) := by
  intro x1 x2 x3 x4 x5 x6
  have hpos : (0 : ℝ) < x5 := PEqualNP.Outside.L_twin_primes_positive_product
  linarith
