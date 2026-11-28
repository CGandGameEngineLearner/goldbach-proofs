import Mathlib
import PEqualNP.Outside.L_twin_primes_window_bridge
import PEqualNP.Outside.L_twin_primes_divisor_bridge
import Conjectures.TwinPrimes.EnergyBridgeV2

theorem Conjectures.Cuts.Taskcfa2355b2fe12a71e57cbc52 : (have x1 : ℕ → ℝ := fun (x1 : ℕ) => if Nat.Prime (x1 + (2 : ℕ)) then Real.log (↑x1 + (2 : ℝ)) else (0 : ℝ); have x2 : ℕ → ℝ := fun (x2 : ℕ) => ∑ x3 ∈ Finset.range (x2 + (1 : ℕ)), (∑ x4 ∈ x3.divisors with Nat.Prime x4 ∧ Nat.Prime (x3 / x4) ∧ x4 ≠ x3 / x4, Real.log ↑x4 * Real.log ↑(x3 / x4)) * x1 x3; have x3 : ℕ → ℝ := fun (x3 : ℕ) => ∑ x4 ∈ Finset.range (x3 + (1 : ℕ)), (if Nat.Prime x4 then Real.log ↑x4 ^ (2 : ℕ) else (0 : ℝ)) * x1 x4; ∀ (x4 : ℕ), x3 x4 ≤ x2 x4 + x3 x4) := by
  show ∀ (x4 : ℕ), (∑ x4 ∈ Finset.range (x4 + (1 : ℕ)), (if Nat.Prime x4 then Real.log ↑x4 ^ (2 : ℕ) else (0 : ℝ)) * (if Nat.Prime (x4 + (2 : ℕ)) then Real.log (↑x4 + (2 : ℝ)) else (0 : ℝ))) ≤ (∑ x3 ∈ Finset.range (x4 + (1 : ℕ)), (∑ x4 ∈ x3.divisors with Nat.Prime x4 ∧ Nat.Prime (x3 / x4) ∧ x4 ≠ x3 / x4, Real.log ↑x4 * Real.log ↑(x3 / x4)) * (if Nat.Prime (x3 + (2 : ℕ)) then Real.log (↑x3 + (2 : ℝ)) else (0 : ℝ))) + (∑ x4 ∈ Finset.range (x4 + (1 : ℕ)), (if Nat.Prime x4 then Real.log ↑x4 ^ (2 : ℕ) else (0 : ℝ)) * (if Nat.Prime (x4 + (2 : ℕ)) then Real.log (↑x4 + (2 : ℝ)) else (0 : ℝ)))
  intro n
  have hx1 : ∀ k : ℕ, (0:ℝ) ≤ (if Nat.Prime (k + (2 : ℕ)) then Real.log (↑k + (2 : ℝ)) else (0 : ℝ)) := by
    intro k
    split_ifs
    · exact Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) k; linarith)
    · exact le_rfl
  have hB : (0:ℝ) ≤ (∑ x3 ∈ Finset.range (n + (1 : ℕ)), (∑ x4 ∈ x3.divisors with Nat.Prime x4 ∧ Nat.Prime (x3 / x4) ∧ x4 ≠ x3 / x4, Real.log ↑x4 * Real.log ↑(x3 / x4)) * (if Nat.Prime (x3 + (2 : ℕ)) then Real.log (↑x3 + (2 : ℝ)) else (0 : ℝ))) := by
    apply Finset.sum_nonneg
    intro k _
    apply mul_nonneg _ (hx1 k)
    apply Finset.sum_nonneg
    intro d hd
    have hmem := (Finset.mem_filter.mp hd).2
    exact mul_nonneg (Real.log_nonneg (by exact_mod_cast hmem.1.one_lt.le))
      (Real.log_nonneg (by exact_mod_cast hmem.2.1.one_lt.le))
  linarith
