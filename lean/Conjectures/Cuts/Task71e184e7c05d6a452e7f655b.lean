import Mathlib
import PEqualNP.Outside.L_twin_primes_window_bridge
import PEqualNP.Outside.L_twin_primes_divisor_bridge
import Conjectures.TwinPrimes.EnergyBridgeV2

theorem Conjectures.Cuts.Task71e184e7c05d6a452e7f655b : (have x1 : ℕ → Finset ℕ := fun (x1 : ℕ) => {x2 ∈ Finset.range ((2 : ℕ) * x1 + (1 : ℕ)) | x1 < x2 ∧ (50 : ℕ) * x2 < (51 : ℕ) * x1}; have x2 : ℕ → ℝ := fun (x2 : ℕ) => -(↑((ArithmeticFunction.moebius : ℕ → ℤ) x2) : ℝ) * Real.log (↑x2 : ℝ); have x3 : ℕ → ℕ := fun (x3 : ℕ) => ⌊(↑x3 : ℝ) ^ (1 / 3 : ℝ)⌋₊; have x4 : ℕ → ℕ := fun (x4 : ℕ) => ⌊√(↑x4 : ℝ) / Real.log ((2 : ℝ) + (↑x4 : ℝ)) ^ (5 : ℕ)⌋₊; have x5 : ℝ := ∏' (x5 : ℕ), if Nat.Prime x5 ∧ (2 : ℕ) < x5 then (1 : ℝ) - (1 : ℝ) / ((↑x5 : ℝ) - (1 : ℝ)) ^ (2 : ℕ) else (1 : ℝ); have x6 : ℕ → ℝ := fun (x6 : ℕ) => (∑ x7 ∈ x1 x6 with Nat.Prime x7, Real.log (↑x7 : ℝ) * {x8 ∈ (x7 + (2 : ℕ)).divisors | x3 x6 < x8 ∧ x4 x6 < x8}.sum x2) / (↑x6 : ℝ); (-2 : ℝ) * x5 / (50 : ℝ) + (1 : ℝ) < (1 : ℝ)) := by
  show (-2 : ℝ) * (∏' (n : ℕ), if Nat.Prime n ∧ (2 : ℕ) < n then (1 : ℝ) - (1 : ℝ) / ((↑n : ℝ) - (1 : ℝ)) ^ (2 : ℕ) else (1 : ℝ)) / (50 : ℝ) + (1 : ℝ) < (1 : ℝ)
  set f : ℕ → ℝ := fun n => if Nat.Prime n ∧ (2 : ℕ) < n then (1 : ℝ) - (1 : ℝ) / ((↑n : ℝ) - (1 : ℝ)) ^ (2 : ℕ) else (1 : ℝ) with hf
  have hfpos : ∀ n, (0:ℝ) < f n := by
    intro n
    simp only [hf]
    split_ifs with h
    · have hnr : (3:ℝ) ≤ (n:ℝ) := by exact_mod_cast h.2
      have h1 : (1:ℝ) < ((n:ℝ) - 1) ^ 2 := by nlinarith
      have h2 : (1:ℝ) / ((n:ℝ) - 1) ^ 2 < 1 := by
        rw [div_lt_one (by nlinarith)]
        exact h1
      linarith
    · norm_num
  have hbound : ∀ n : ℕ, ‖Real.log (f n)‖ ≤ 8 * (1 / (n:ℝ) ^ 2) := by
    intro n
    by_cases h : Nat.Prime n ∧ (2:ℕ) < n
    · have hp := h.1
      have hn := h.2
      have hnr : (3:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
      have hA : (2:ℝ) ≤ ((n:ℝ) - 1) ^ 2 := by nlinarith
      have hx : (1:ℝ) / ((n:ℝ) - 1) ^ 2 ≤ 1/2 := one_div_le_one_div_of_le (by norm_num) hA
      have hx0 : (0:ℝ) < (1:ℝ) / ((n:ℝ) - 1) ^ 2 := by positivity
      have hpos1 : (0:ℝ) < 1 - (1:ℝ) / ((n:ℝ) - 1) ^ 2 := by linarith
      have hne : (1:ℝ) - (1:ℝ) / ((n:ℝ) - 1) ^ 2 ≠ 0 := hpos1.ne'
      have hfn : f n = 1 - (1:ℝ) / ((n:ℝ) - 1) ^ 2 := by
        simp only [hf]
        exact if_pos h
      have hlogneg : Real.log (1 - (1:ℝ) / ((n:ℝ) - 1) ^ 2) ≤ 0 :=
        Real.log_nonpos (by linarith) (by linarith)
      have h5 := Real.log_le_sub_one_of_pos (show (0:ℝ) < (1 - (1:ℝ) / ((n:ℝ) - 1) ^ 2)⁻¹ by positivity)
      rw [Real.log_inv] at h5
      have h6 : ((1:ℝ) - (1:ℝ) / ((n:ℝ) - 1) ^ 2)⁻¹ - 1 =
          ((1:ℝ) / ((n:ℝ) - 1) ^ 2) / (1 - (1:ℝ) / ((n:ℝ) - 1) ^ 2) := by
        rw [eq_div_iff hne, sub_mul, inv_mul_cancel₀ hne, one_mul, sub_sub_cancel]
      have h7 : ((1:ℝ) / ((n:ℝ) - 1) ^ 2) / (1 - (1:ℝ) / ((n:ℝ) - 1) ^ 2) ≤
          2 * ((1:ℝ) / ((n:ℝ) - 1) ^ 2) := by
        rw [div_le_iff₀ hpos1]
        nlinarith
      have h8 : 2 * ((1:ℝ) / ((n:ℝ) - 1) ^ 2) ≤ 8 * (1 / (n:ℝ) ^ 2) := by
        rw [mul_one_div, mul_one_div, div_le_div_iff₀ (by nlinarith) (by positivity)]
        nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 3 * (n:ℝ) - 2) (by linarith : (0:ℝ) ≤ (n:ℝ) - 2)]
      rw [hfn, Real.norm_eq_abs, abs_of_nonpos hlogneg]
      linarith
    · have hfn : f n = 1 := by
        simp only [hf]
        exact if_neg h
      rw [hfn, Real.log_one, norm_zero]
      positivity
  have hsum8 : Summable fun n : ℕ => 8 * (1 / (n:ℝ) ^ 2) :=
    (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)).mul_left 8
  have hsum : Summable fun n => Real.log (f n) := Summable.of_norm_bounded hsum8 hbound
  have hprod : HasProd f (Real.exp (∑' n, Real.log (f n))) :=
    Real.hasProd_of_hasSum_log hfpos hsum.hasSum
  have hpos : (0:ℝ) < ∏' n, f n := by
    rw [hprod.tprod_eq]
    exact Real.exp_pos _
  linarith
