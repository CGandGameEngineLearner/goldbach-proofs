import Mathlib
import PEqualNP.Outside.L_twin_primes_window_bridge
import PEqualNP.Outside.L_twin_primes_divisor_bridge
import Conjectures.TwinPrimes.EnergyBridgeV2

-- child 1 zh: 同一长除数余量沿无界尺度一致为正：存在固定正下界 c，使充分晚的 X 上 x6 X ≥ c。
-- child 1 en: The long-divisor remainder is uniformly positive along unbounded scales: some fixed c > 0 satisfies c < x6 X for arbitrarily large X.
-- child 2 zh: 孪生素数常数（欧拉乘积）为正，故负主项 -2 x5 / 50 严格小于零。
-- child 2 en: The twin-prime constant (an Euler product) is positive, so the negative main term -2 x5 / 50 is strictly below zero.

theorem Conjectures.Cuts.Cut78065e9d2af42bcc5772ecec
    (h₁ : (have x1 : ℕ → Finset ℕ := fun (x1 : ℕ) => {x2 ∈ Finset.range ((2 : ℕ) * x1 + (1 : ℕ)) | x1 < x2 ∧ (50 : ℕ) * x2 < (51 : ℕ) * x1}; have x2 : ℕ → ℝ := fun (x2 : ℕ) => -(↑((ArithmeticFunction.moebius : ℕ → ℤ) x2) : ℝ) * Real.log (↑x2 : ℝ); have x3 : ℕ → ℕ := fun (x3 : ℕ) => ⌊(↑x3 : ℝ) ^ (1 / 3 : ℝ)⌋₊; have x4 : ℕ → ℕ := fun (x4 : ℕ) => ⌊√(↑x4 : ℝ) / Real.log ((2 : ℝ) + (↑x4 : ℝ)) ^ (5 : ℕ)⌋₊; have x5 : ℝ := ∏' (x5 : ℕ), if Nat.Prime x5 ∧ (2 : ℕ) < x5 then (1 : ℝ) - (1 : ℝ) / ((↑x5 : ℝ) - (1 : ℝ)) ^ (2 : ℕ) else (1 : ℝ); have x6 : ℕ → ℝ := fun (x6 : ℕ) => (∑ x7 ∈ x1 x6 with Nat.Prime x7, Real.log (↑x7 : ℝ) * {x8 ∈ (x7 + (2 : ℕ)).divisors | x3 x6 < x8 ∧ x4 x6 < x8}.sum x2) / (↑x6 : ℝ); ∃ (x7 : ℝ), (0 : ℝ) < x7 ∧ ∀ (x8 : ℕ), ∃ (x9 : ℕ), x8 < x9 ∧ x7 < x6 x9))
    (h₂ : (have x5 : ℝ := ∏' (x5 : ℕ), if Nat.Prime x5 ∧ (2 : ℕ) < x5 then (1 : ℝ) - (1 : ℝ) / ((↑x5 : ℝ) - (1 : ℝ)) ^ (2 : ℕ) else (1 : ℝ); (0 : ℝ) < x5)) :
    (have x1 : ℕ → Finset ℕ := fun (x1 : ℕ) => {x2 ∈ Finset.range ((2 : ℕ) * x1 + (1 : ℕ)) | x1 < x2 ∧ (50 : ℕ) * x2 < (51 : ℕ) * x1}; have x2 : ℕ → ℝ := fun (x2 : ℕ) => -(↑((ArithmeticFunction.moebius : ℕ → ℤ) x2) : ℝ) * Real.log (↑x2 : ℝ); have x3 : ℕ → ℕ := fun (x3 : ℕ) => ⌊(↑x3 : ℝ) ^ (1 / 3 : ℝ)⌋₊; have x4 : ℕ → ℕ := fun (x4 : ℕ) => ⌊√(↑x4 : ℝ) / Real.log ((2 : ℝ) + (↑x4 : ℝ)) ^ (5 : ℕ)⌋₊; have x5 : ℝ := ∏' (x5 : ℕ), if Nat.Prime x5 ∧ (2 : ℕ) < x5 then (1 : ℝ) - (1 : ℝ) / ((↑x5 : ℝ) - (1 : ℝ)) ^ (2 : ℕ) else (1 : ℝ); have x6 : ℕ → ℝ := fun (x6 : ℕ) => (∑ x7 ∈ x1 x6 with Nat.Prime x7, Real.log (↑x7 : ℝ) * {x8 ∈ (x7 + (2 : ℕ)).divisors | x3 x6 < x8 ∧ x4 x6 < x8}.sum x2) / (↑x6 : ℝ); ∃ (x7 : ℝ), (0 : ℝ) < x7 ∧ ∀ (x8 : ℕ), ∃ (x9 : ℕ), x8 < x9 ∧ (-2 : ℝ) * x5 / (50 : ℝ) + x7 < x6 x9) := by
  dsimp only at h₁ h₂ ⊢
  obtain ⟨c, hc, hX⟩ := h₁
  refine ⟨c, hc, ?_⟩
  intro B
  obtain ⟨X, hB, hlt⟩ := hX B
  refine ⟨X, hB, ?_⟩
  linarith
