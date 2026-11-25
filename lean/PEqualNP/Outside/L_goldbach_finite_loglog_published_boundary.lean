import Mathlib

private lemma logC_eq {C : ℝ} (hC : C = 2^20 * 5^18) :
    Real.log C = 20 * Real.log 2 + 18 * Real.log 5 := by
  rw [hC, Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
  push_cast
  ring

private lemma logC_lower : (42.83:ℝ) < Real.log ((4:ℝ)*10^18) := by
  have hC : (4:ℝ)*10^18 = 2^20 * 5^18 := by norm_num
  rw [logC_eq hC]
  have h2 := Real.log_two_gt_d9
  have h5 := Real.log_five_gt_d9
  linarith

private lemma logC_upper : Real.log ((4:ℝ)*10^18) < (42.84:ℝ) := by
  have hC : (4:ℝ)*10^18 = 2^20 * 5^18 := by norm_num
  rw [logC_eq hC]
  have h2 := Real.log_two_lt_d9
  have h5 := Real.log_five_lt_d9
  linarith

private lemma exp_fifteen_fourths_lt : Real.exp (15/4) < 42.6 := by
  have hpow : Real.exp (15/4) ^ 4 = Real.exp 15 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have he15 : Real.exp 15 = Real.exp 1 ^ 15 := by
    simpa using Real.exp_nat_mul 1 15
  have hb : Real.exp 1 ^ 15 < (2.7182818286:ℝ)^15 :=
    pow_lt_pow_left₀ Real.exp_one_lt_d9 (le_of_lt (Real.exp_pos 1)) (by norm_num)
  have hnum : (2.7182818286:ℝ)^15 < (42.6:ℝ)^4 := by norm_num
  have hkey : Real.exp (15/4)^4 < (42.6:ℝ)^4 := by
    rw [hpow, he15]
    linarith
  have hpos : (0:ℝ) ≤ Real.exp (15/4) := le_of_lt (Real.exp_pos _)
  exact (pow_lt_pow_iff_left₀ hpos (by norm_num) (by norm_num : (4:ℕ) ≠ 0)).mp hkey

private lemma exp_nineteen_fifths_gt : (42.84:ℝ) < Real.exp (19/5) := by
  have hpow : Real.exp (19/5) ^ 5 = Real.exp 19 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have he19 : Real.exp 19 = Real.exp 1 ^ 19 := by
    simpa using Real.exp_nat_mul 1 19
  have hb : (2.7182818283:ℝ)^19 < Real.exp 1 ^ 19 :=
    pow_lt_pow_left₀ Real.exp_one_gt_d9 (by norm_num) (by norm_num)
  have hnum : (42.84:ℝ)^5 < (2.7182818283:ℝ)^19 := by norm_num
  have hkey : (42.84:ℝ)^5 < Real.exp (19/5)^5 := by
    rw [hpow, he19]
    linarith
  have hpos : (0:ℝ) ≤ Real.exp (19/5) := le_of_lt (Real.exp_pos _)
  exact (pow_lt_pow_iff_left₀ (by norm_num) hpos (by norm_num : (5:ℕ) ≠ 0)).mp hkey

theorem PEqualNP.Outside.L_goldbach_finite_loglog_published_boundary : let C : ℝ := 4*10^18; (75:ℝ)/20 < Real.log (Real.log C) ∧ Real.log (Real.log C) < (76:ℝ)/20 := by
  dsimp only
  have hpos : (0:ℝ) < Real.log ((4:ℝ)*10^18) := Real.log_pos (by norm_num)
  constructor
  · rw [show (75:ℝ)/20 = 15/4 by norm_num]
    rw [Real.lt_log_iff_exp_lt hpos]
    have h1 := exp_fifteen_fourths_lt
    have h2 := logC_lower
    linarith
  · rw [show (76:ℝ)/20 = 19/5 by norm_num]
    rw [Real.log_lt_iff_lt_exp hpos]
    have h1 := logC_upper
    have h2 := exp_nineteen_fifths_gt
    linarith