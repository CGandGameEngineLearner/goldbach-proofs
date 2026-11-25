import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

theorem PEqualNP.Outside.L_goldbach_finite_power_contamination_budget :
    ∀ (n : ℕ), 4*10^18 < n → Real.log (Real.log n) < (76:ℝ)/20 →
      2*((Nat.sqrt n:ℝ)+(Nat.log 2 n:ℝ)*(n:ℝ)^(1/3:ℝ))*(Real.log n)^2 < (n:ℝ)/10^5 := by
  intro n hn hband
  have hnR : (4 : ℝ) * 10^18 < (n : ℝ) := by exact_mod_cast hn
  have hnPos : (0 : ℝ) < n := by linarith only [hnR]
  have hlogPos : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith only [hnR])
  have hlogUpper : Real.log (n : ℝ) < 81 := by
    calc
      Real.log (n : ℝ) = Real.exp (Real.log (Real.log (n : ℝ))) := (Real.exp_log hlogPos).symm
      _ ≤ Real.exp 4 := Real.exp_monotone (by linarith only [hband])
      _ = (Real.exp 1) ^ 4 := by simp [← Real.exp_nat_mul]
      _ < (3 : ℝ) ^ 4 := pow_lt_pow_left₀ Real.exp_one_lt_three (Real.exp_pos _).le (by decide)
      _ = 81 := by norm_num
  have hlogTwo : (1 / 2 : ℝ) < Real.log 2 :=
    (by norm_num : (1 / 2 : ℝ) < 0.6931471803).trans Real.log_two_gt_d9
  have hlogBase : (Nat.log 2 n : ℝ) * Real.log 2 ≤ Real.log (n : ℝ) := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity)
      (by exact_mod_cast Nat.pow_log_le_self 2 (by omega : n ≠ 0))
  have hlogNat : (Nat.log 2 n : ℝ) ≤ 162 := by
    have h := mul_le_mul_of_nonneg_left hlogTwo.le (Nat.cast_nonneg (Nat.log 2 n))
    linarith only [h, hlogBase, hlogUpper]
  have hsqrtLower : (2000000000 : ℝ) ≤ Real.sqrt (n : ℝ) :=
    Real.le_sqrt_of_sq_le (by linarith only [hnR])
  have hsqrtBound : (Nat.sqrt n : ℝ) ≤ (n : ℝ) / 2000000000 := by
    refine Real.nat_sqrt_le_real_sqrt.trans ((le_div_iff₀ (by norm_num)).2 ?_)
    have hm := mul_le_mul_of_nonneg_right hsqrtLower (Real.sqrt_nonneg (n : ℝ))
    linarith only [hm, Real.sq_sqrt hnPos.le]
  let c : ℝ := (n : ℝ) ^ (1 / 3 : ℝ)
  have hc : 0 ≤ c := Real.rpow_nonneg hnPos.le _
  have hCube (x : ℝ) (hx : 0 ≤ x) : (x ^ (1 / 3 : ℝ)) ^ (3 : ℕ) = x := by
    rw [← Real.rpow_mul_natCast hx, show (1 / 3 : ℝ) * (3 : ℕ) = 1 by norm_num, Real.rpow_one]
  have hcLower : (1000000 : ℝ) ≤ c := by
    have hPower : ((1000000 : ℝ) ^ (3 : ℕ)) ^ (1 / 3 : ℝ) = 1000000 := by
      rw [← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 1000000),
        show (3 : ℕ) * (1 / 3 : ℝ) = 1 by norm_num, Real.rpow_one]
    rw [← hPower]
    exact Real.rpow_le_rpow (by positivity) (by linarith only [hnR]) (by norm_num)
  have hcBound : c ≤ (n : ℝ) / 1000000000000 := by
    apply (le_div_iff₀ (by norm_num)).2
    have hsq : (1000000000000 : ℝ) ≤ c ^ 2 := by
      simpa only [show (1000000 : ℝ)^2 = 1000000000000 by norm_num] using
        pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1000000) hcLower 2
    have hm := mul_le_mul_of_nonneg_left hsq hc
    have hp : c ^ (3 : ℕ) = (n : ℝ) := hCube (n : ℝ) hnPos.le
    nlinarith only [hm, hp]
  have hsum : (Nat.sqrt n : ℝ) + (Nat.log 2 n : ℝ) * c ≤
      (n : ℝ) / 2000000000 + 162 * ((n : ℝ) / 1000000000000) := by
    exact add_le_add hsqrtBound (mul_le_mul hlogNat hcBound hc (by norm_num))
  change 2 * ((Nat.sqrt n : ℝ) + (Nat.log 2 n : ℝ) * c) * (Real.log n)^2 < _
  calc
    _ ≤ (2 * ((n : ℝ) / 2000000000 + 162 * ((n : ℝ) / 1000000000000))) * (81 : ℝ)^2 := by
      apply mul_le_mul (mul_le_mul_of_nonneg_left hsum (by norm_num))
        (pow_le_pow_left₀ hlogPos.le hlogUpper.le 2) (sq_nonneg _) (by positivity)
    _ < _ := by linarith only [hnPos]
