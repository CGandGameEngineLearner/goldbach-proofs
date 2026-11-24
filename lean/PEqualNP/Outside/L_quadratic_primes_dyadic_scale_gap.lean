import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.NormNum

set_option maxRecDepth 1000000 in
theorem PEqualNP.Outside.L_quadratic_primes_dyadic_scale_gap :
    ∀ (x n : ℝ), (2 : ℝ) ^ (13230 : ℕ) < x → 0 ≤ n → n ≤ 2 * x →
      n ^ ((1323 : ℝ) / 1000) < x ^ ((13231 : ℝ) / 10000) := by
  intro x n hx hn0 hnx
  have hxr : (2 : ℝ) ^ ((13230 : ℕ) : ℝ) < x := by
    rw [Real.rpow_natCast]
    exact hx
  have hx0 : 0 < x := lt_trans (Real.rpow_pos_of_pos (by norm_num) _) hxr
  have hmain : n ^ (13230 : ℝ) < x ^ (13231 : ℝ) := by
    have h1 : n ^ (13230 : ℝ) ≤ (2 * x) ^ (13230 : ℝ) :=
      Real.rpow_le_rpow hn0 hnx (by norm_num)
    have h2 : (2 * x) ^ (13230 : ℝ) = (2 : ℝ) ^ (13230 : ℝ) * x ^ (13230 : ℝ) :=
      Real.mul_rpow (by norm_num) hx0.le
    have hxpow : 0 < x ^ (13230 : ℝ) := Real.rpow_pos_of_pos hx0 _
    have h3 : (2 : ℝ) ^ (13230 : ℝ) * x ^ (13230 : ℝ) < x * x ^ (13230 : ℝ) :=
      mul_lt_mul_of_pos_right hxr hxpow
    have h4 : x * x ^ (13230 : ℝ) = x ^ (13231 : ℝ) := by
      have h := Real.rpow_add hx0 (1 : ℝ) (13230 : ℝ)
      rw [show (13231 : ℝ) = 1 + 13230 by norm_num, h, Real.rpow_one]
    calc n ^ (13230 : ℝ) ≤ (2 * x) ^ (13230 : ℝ) := h1
      _ = (2 : ℝ) ^ (13230 : ℝ) * x ^ (13230 : ℝ) := h2
      _ < x * x ^ (13230 : ℝ) := h3
      _ = x ^ (13231 : ℝ) := h4
  have e1 : (n ^ (13230 : ℝ)) ^ ((1 : ℝ) / 10000) = n ^ ((1323 : ℝ) / 1000) := by
    rw [← Real.rpow_mul hn0]
    norm_num
  have e2 : (x ^ (13231 : ℝ)) ^ ((1 : ℝ) / 10000) = x ^ ((13231 : ℝ) / 10000) := by
    rw [← Real.rpow_mul hx0.le]
    norm_num
  have hlt : (n ^ (13230 : ℝ)) ^ ((1 : ℝ) / 10000) < (x ^ (13231 : ℝ)) ^ ((1 : ℝ) / 10000) := by
    rw [Real.rpow_lt_rpow_iff (Real.rpow_nonneg hn0 _) (Real.rpow_nonneg hx0.le _) (by norm_num)]
    exact hmain
  rwa [e1, e2] at hlt
