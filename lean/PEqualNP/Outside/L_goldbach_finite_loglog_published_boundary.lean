import Mathlib

/-!
# FR-7002: the published verification endpoint lies in band 75

For `C = 4 * 10^18`, the iterated logarithm `log (log C)` lies strictly between
`75/20 = 3.75` and `76/20 = 3.8`.

Both comparisons are reduced to integer-power comparisons of `exp 1`:
`exp (171/4) < C` and `C < exp 43` (so `171/4 = 42.75 < log C < 43`), together with
`exp (15/4) < 171/4` and `43 < exp (19/5)`.
-/

theorem PEqualNP.Outside.L_goldbach_finite_loglog_published_boundary :
    let C : ℝ := 4*10^18;
    (75:ℝ)/20 < Real.log (Real.log C) ∧ Real.log (Real.log C) < (76:ℝ)/20 := by
  dsimp only
  have hCpos : (0:ℝ) < (4:ℝ)*10^18 := by norm_num
  have hlogCpos : (0:ℝ) < Real.log ((4:ℝ)*10^18) := Real.log_pos (by norm_num)
  have he_gt : (2.71:ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have he_lt : Real.exp 1 < (2.72:ℝ) := by linarith [Real.exp_one_lt_d9]
  -- `C < exp 43`
  have hexp43 : (4:ℝ)*10^18 < Real.exp 43 := by
    have h43 : Real.exp 43 = Real.exp 1 ^ 43 := by
      have h := Real.exp_nat_mul (1:ℝ) 43
      simpa using h
    rw [h43]
    have hnum : (4:ℝ)*10^18 < (2.71:ℝ)^43 := by norm_num
    have hp : (2.71:ℝ)^43 < Real.exp 1 ^ 43 :=
      pow_lt_pow_left₀ (n := 43) he_gt (by norm_num) (by norm_num)
    exact lt_trans hnum hp
  have hlogC_lt : Real.log ((4:ℝ)*10^18) < 43 :=
    (Real.log_lt_iff_lt_exp hCpos).mpr hexp43
  -- `43 < exp (19/5)`
  have h43exp : (43:ℝ) < Real.exp ((19:ℝ)/5) := by
    have h5 : Real.exp ((19:ℝ)/5) ^ 5 = Real.exp 19 := by
      have h := Real.exp_nat_mul ((19:ℝ)/5) 5
      rw [show (5:ℕ) * ((19:ℝ)/5) = 19 by norm_num] at h
      exact h.symm
    have hexp19 : Real.exp 19 = Real.exp 1 ^ 19 := by
      have h := Real.exp_nat_mul (1:ℝ) 19
      simpa using h
    have hpow : (43:ℝ)^5 < Real.exp ((19:ℝ)/5) ^ 5 := by
      rw [h5, hexp19]
      have hc : (43:ℝ)^5 < (2.71:ℝ)^19 := by norm_num
      have hp : (2.71:ℝ)^19 < Real.exp 1 ^ 19 :=
        pow_lt_pow_left₀ (n := 19) he_gt (by norm_num) (by norm_num)
      exact lt_trans hc hp
    exact (pow_lt_pow_iff_left₀ (by norm_num) (le_of_lt (Real.exp_pos _))
      (by norm_num : (5:ℕ) ≠ 0)).mp hpow
  have hlog43 : Real.log 43 < (19:ℝ)/5 :=
    (Real.log_lt_iff_lt_exp (by norm_num : (0:ℝ) < 43)).mpr h43exp
  -- `exp (171/4) < C`
  have hexp171 : Real.exp ((171:ℝ)/4) < (4:ℝ)*10^18 := by
    have h4 : Real.exp ((171:ℝ)/4) ^ 4 = Real.exp 171 := by
      have h := Real.exp_nat_mul ((171:ℝ)/4) 4
      rw [show (4:ℕ) * ((171:ℝ)/4) = 171 by norm_num] at h
      exact h.symm
    have hexp171' : Real.exp 171 = Real.exp 1 ^ 171 := by
      have h := Real.exp_nat_mul (1:ℝ) 171
      simpa using h
    have hpow : Real.exp ((171:ℝ)/4) ^ 4 < ((4:ℝ)*10^18)^4 := by
      rw [h4, hexp171']
      have hp : Real.exp 1 ^ 171 < (2.72:ℝ)^171 :=
        pow_lt_pow_left₀ (n := 171) he_lt (le_of_lt (Real.exp_pos 1)) (by norm_num)
      have hnum : (2.72:ℝ)^171 < ((4:ℝ)*10^18)^4 := by norm_num
      exact lt_trans hp hnum
    exact (pow_lt_pow_iff_left₀ (le_of_lt (Real.exp_pos _)) (by positivity)
      (by norm_num : (4:ℕ) ≠ 0)).mp hpow
  have hlogC_gt : (171:ℝ)/4 < Real.log ((4:ℝ)*10^18) :=
    (Real.lt_log_iff_exp_lt hCpos).mpr hexp171
  -- `exp (15/4) < 171/4`
  have hlog171 : (15:ℝ)/4 < Real.log ((171:ℝ)/4) := by
    have h4 : Real.exp ((15:ℝ)/4) ^ 4 = Real.exp 15 := by
      have h := Real.exp_nat_mul ((15:ℝ)/4) 4
      rw [show (4:ℕ) * ((15:ℝ)/4) = 15 by norm_num] at h
      exact h.symm
    have hexp15 : Real.exp 15 = Real.exp 1 ^ 15 := by
      have h := Real.exp_nat_mul (1:ℝ) 15
      simpa using h
    have hlt : Real.exp ((15:ℝ)/4) < (171:ℝ)/4 := by
      have hpow : Real.exp ((15:ℝ)/4) ^ 4 < ((171:ℝ)/4)^4 := by
        rw [h4, hexp15]
        have hp : Real.exp 1 ^ 15 < (2.72:ℝ)^15 :=
          pow_lt_pow_left₀ (n := 15) he_lt (le_of_lt (Real.exp_pos 1)) (by norm_num)
        have hnum : (2.72:ℝ)^15 < ((171:ℝ)/4)^4 := by norm_num
        exact lt_trans hp hnum
      exact (pow_lt_pow_iff_left₀ (le_of_lt (Real.exp_pos _)) (by norm_num)
        (by norm_num : (4:ℕ) ≠ 0)).mp hpow
    exact (Real.lt_log_iff_exp_lt (by norm_num : (0:ℝ) < (171:ℝ)/4)).mpr hlt
  constructor
  · have h1 : (15:ℝ)/4 < Real.log (Real.log ((4:ℝ)*10^18)) :=
      lt_trans hlog171 (Real.log_lt_log (by norm_num : (0:ℝ) < (171:ℝ)/4) hlogC_gt)
    have h75 : (75:ℝ)/20 = (15:ℝ)/4 := by norm_num
    rw [h75]
    exact h1
  · have h2 : Real.log (Real.log ((4:ℝ)*10^18)) < (19:ℝ)/5 :=
      lt_trans (Real.log_lt_log hlogCpos hlogC_lt) hlog43
    have h76 : (76:ℝ)/20 = (19:ℝ)/5 := by norm_num
    rw [h76]
    exact h2
