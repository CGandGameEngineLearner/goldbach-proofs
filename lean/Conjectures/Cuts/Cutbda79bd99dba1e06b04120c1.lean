import Mathlib
import PEqualNP.Outside.L_twin_primes_window_bridge
import PEqualNP.Outside.L_twin_primes_divisor_bridge
import Conjectures.TwinPrimes.EnergyBridgeV2

-- child 1 zh: 长除数余量沿无界尺度至少达到常数 1。
-- child 1 en: The long-divisor remainder reaches at least the constant 1 along unbounded scales.
-- child 2 zh: 负主项（孪生素数常数项）把常数 1 的余量削减不到 1，即主项严格小于零。
-- child 2 en: The negative main term shifts the constant 1 down below 1, i.e. the main term is strictly negative.

theorem Conjectures.Cuts.Cutbda79bd99dba1e06b04120c1
    (h₁ : have x1 : ℕ → Finset ℕ := fun (x1 : ℕ) => {x2 ∈ Finset.range ((2 : ℕ) * x1 + (1 : ℕ)) | x1 < x2 ∧ (50 : ℕ) * x2 < (51 : ℕ) * x1}; have x2 : ℕ → ℝ := fun (x2 : ℕ) => -(↑((ArithmeticFunction.moebius : ℕ → ℤ) x2) : ℝ) * Real.log (↑x2 : ℝ); have x3 : ℕ → ℕ := fun (x3 : ℕ) => ⌊(↑x3 : ℝ) ^ (1 / 3 : ℝ)⌋₊; have x4 : ℕ → ℕ := fun (x4 : ℕ) => ⌊√(↑x4 : ℝ) / Real.log ((2 : ℝ) + (↑x4 : ℝ)) ^ (5 : ℕ)⌋₊; have x5 : ℝ := ∏' (x5 : ℕ), if Nat.Prime x5 ∧ (2 : ℕ) < x5 then (1 : ℝ) - (1 : ℝ) / ((↑x5 : ℝ) - (1 : ℝ)) ^ (2 : ℕ) else (1 : ℝ); have x6 : ℕ → ℝ := fun (x6 : ℕ) => (∑ x7 ∈ x1 x6 with Nat.Prime x7, Real.log (↑x7 : ℝ) * {x8 ∈ (x7 + (2 : ℕ)).divisors | x3 x6 < x8 ∧ x4 x6 < x8}.sum x2) / (↑x6 : ℝ); ∀ (x8 : ℕ), ∃ (x9 : ℕ), x8 < x9 ∧ (1 : ℝ) ≤ x6 x9)
    (h₂ : have x1 : ℕ → Finset ℕ := fun (x1 : ℕ) => {x2 ∈ Finset.range ((2 : ℕ) * x1 + (1 : ℕ)) | x1 < x2 ∧ (50 : ℕ) * x2 < (51 : ℕ) * x1}; have x2 : ℕ → ℝ := fun (x2 : ℕ) => -(↑((ArithmeticFunction.moebius : ℕ → ℤ) x2) : ℝ) * Real.log (↑x2 : ℝ); have x3 : ℕ → ℕ := fun (x3 : ℕ) => ⌊(↑x3 : ℝ) ^ (1 / 3 : ℝ)⌋₊; have x4 : ℕ → ℕ := fun (x4 : ℕ) => ⌊√(↑x4 : ℝ) / Real.log ((2 : ℝ) + (↑x4 : ℝ)) ^ (5 : ℕ)⌋₊; have x5 : ℝ := ∏' (x5 : ℕ), if Nat.Prime x5 ∧ (2 : ℕ) < x5 then (1 : ℝ) - (1 : ℝ) / ((↑x5 : ℝ) - (1 : ℝ)) ^ (2 : ℕ) else (1 : ℝ); have x6 : ℕ → ℝ := fun (x6 : ℕ) => (∑ x7 ∈ x1 x6 with Nat.Prime x7, Real.log (↑x7 : ℝ) * {x8 ∈ (x7 + (2 : ℕ)).divisors | x3 x6 < x8 ∧ x4 x6 < x8}.sum x2) / (↑x6 : ℝ); (-2 : ℝ) * x5 / (50 : ℝ) + 1 < 1) :
    (have x1 : ℕ → Finset ℕ := fun (x1 : ℕ) => {x2 ∈ Finset.range ((2 : ℕ) * x1 + (1 : ℕ)) | x1 < x2 ∧ (50 : ℕ) * x2 < (51 : ℕ) * x1}; have x2 : ℕ → ℝ := fun (x2 : ℕ) => -(↑((ArithmeticFunction.moebius : ℕ → ℤ) x2) : ℝ) * Real.log (↑x2 : ℝ); have x3 : ℕ → ℕ := fun (x3 : ℕ) => ⌊(↑x3 : ℝ) ^ (1 / 3 : ℝ)⌋₊; have x4 : ℕ → ℕ := fun (x4 : ℕ) => ⌊√(↑x4 : ℝ) / Real.log ((2 : ℝ) + (↑x4 : ℝ)) ^ (5 : ℕ)⌋₊; have x5 : ℝ := ∏' (x5 : ℕ), if Nat.Prime x5 ∧ (2 : ℕ) < x5 then (1 : ℝ) - (1 : ℝ) / ((↑x5 : ℝ) - (1 : ℝ)) ^ (2 : ℕ) else (1 : ℝ); have x6 : ℕ → ℝ := fun (x6 : ℕ) => (∑ x7 ∈ x1 x6 with Nat.Prime x7, Real.log (↑x7 : ℝ) * {x8 ∈ (x7 + (2 : ℕ)).divisors | x3 x6 < x8 ∧ x4 x6 < x8}.sum x2) / (↑x6 : ℝ); ∃ (x7 : ℝ), (0 : ℝ) < x7 ∧ ∀ (x8 : ℕ), ∃ (x9 : ℕ), x8 < x9 ∧ (-2 : ℝ) * x5 / (50 : ℝ) + x7 < x6 x9) := by
  refine ⟨1, by norm_num, ?_⟩
  intro B
  obtain ⟨X, hB, hle⟩ := h₁ B
  exact ⟨X, hB, lt_of_lt_of_le h₂ hle⟩
