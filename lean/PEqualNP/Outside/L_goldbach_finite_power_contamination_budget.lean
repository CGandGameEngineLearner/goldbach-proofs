import Mathlib

theorem PEqualNP.Outside.L_goldbach_finite_power_contamination_budget :
    ∀ (n : ℕ), 4*10^18 < n → Real.log (Real.log n) < (76:ℝ)/20 → 2*((Nat.sqrt n:ℝ)+(Nat.log 2 n:ℝ)*(n:ℝ)^(1/3:ℝ))*(Real.log n)^2 < (n:ℝ)/10^5 := by
  intro n hn hband
  have hn_lower : (4 * 10^18 : ℝ) < n := by exact_mod_cast hn
  have hn_one : (1 : ℝ) < n := by linarith
  have hn_nonneg : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hlog_pos : 0 < Real.log n := Real.log_pos hn_one

  -- The band condition gives log n < 45 by bounding exp(4) and exp(1/5).
  have hexp_four : Real.exp 4 < (549 : ℝ) / 10 := by
    calc
      Real.exp 4 = Real.exp 1 ^ (4 : ℕ) := by
        norm_num [← Real.exp_nat_mul]
      _ < (2.72 : ℝ) ^ (4 : ℕ) :=
        pow_lt_pow_left₀ (Real.exp_one_lt_d9.trans (by norm_num))
          (Real.exp_pos _).le (by decide)
      _ < _ := by norm_num
  have hexp_fifth : (61 : ℝ) / 50 ≤ Real.exp (1 / 5) := by
    convert Real.quadratic_le_exp_of_nonneg (x := (1 : ℝ) / 5) (by norm_num) using 1
    norm_num
  have hexp_split : Real.exp ((76 : ℝ) / 20) * Real.exp (1 / 5) = Real.exp 4 := by
    rw [← Real.exp_add, show (76 : ℝ) / 20 + 1 / 5 = 4 by norm_num]
  have hexp_band : Real.exp ((76 : ℝ) / 20) < 45 := by
    have hscaled := mul_le_mul_of_nonneg_left hexp_fifth (Real.exp_pos ((76 : ℝ) / 20)).le
    rw [hexp_split] at hscaled
    linarith
  have hlog : Real.log n < 45 :=
    ((Real.log_lt_iff_lt_exp hlog_pos).mp hband).trans hexp_band

  have hpow_log_le : (2 : ℝ) ^ Nat.log 2 n ≤ (n : ℝ) := by
    exact_mod_cast Nat.pow_log_le_self 2 (by omega : n ≠ 0)
  have hlog_pow_le := Real.log_le_log (by positivity : 0 < (2 : ℝ) ^ Nat.log 2 n) hpow_log_le
  rw [Real.log_pow] at hlog_pow_le
  have hlog_two : (1 : ℝ) / 2 ≤ Real.log 2 := Real.log_two_gt_d9.le.trans' (by norm_num)
  have hlog_nat : (Nat.log 2 n : ℝ) ≤ 90 := by
    have hhalf := mul_le_mul_of_nonneg_left hlog_two (Nat.cast_nonneg (Nat.log 2 n))
    linarith

  let s := Real.sqrt n
  let c := (n : ℝ) ^ (1 / 3 : ℝ)
  have hs_nonneg : 0 ≤ s := Real.sqrt_nonneg _
  have hs_lower : 2000000000 < s := by
    apply (Real.lt_sqrt (by norm_num : 0 ≤ (2000000000 : ℝ))).mpr
    linarith
  have hs_sq : s ^ 2 = (n : ℝ) := Real.sq_sqrt hn_nonneg
  have hnat_sqrt : (Nat.sqrt n : ℝ) ≤ s := by
    apply (Real.le_sqrt (Nat.cast_nonneg _) hn_nonneg).mpr
    exact_mod_cast Nat.sqrt_le' n
  have hc_nonneg : 0 ≤ c := Real.rpow_nonneg hn_nonneg _
  have hc_cube : c ^ 3 = (n : ℝ) := by
    simpa [c, one_div] using Real.rpow_inv_natCast_pow hn_nonneg (by decide : (3 : ℕ) ≠ 0)
  have hc_le : c ≤ s / 100 := by
    apply le_of_pow_le_pow_left₀ (by decide : (3 : ℕ) ≠ 0) (by positivity)
    calc
      c ^ 3 = s ^ 2 := hc_cube.trans hs_sq.symm
      _ = s ^ 2 * 1 := by ring
      _ ≤ s ^ 2 * (s / 1000000) := mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)
      _ = (s / 100) ^ 3 := by ring
  have hcount : (Nat.sqrt n : ℝ) + (Nat.log 2 n : ℝ) * c ≤ 2 * s := by
    have hlog_term : (Nat.log 2 n : ℝ) * c ≤ 90 * (s / 100) :=
      mul_le_mul hlog_nat hc_le hc_nonneg (by norm_num)
    calc
      _ ≤ s + 90 * (s / 100) := by linarith only [hnat_sqrt, hlog_term]
      _ ≤ 2 * s := by linarith

  change 2 * ((Nat.sqrt n : ℝ) + (Nat.log 2 n : ℝ) * c) * (Real.log n) ^ 2 < _
  calc
    _ ≤ (2 * (2 * s)) * 45 ^ 2 :=
      mul_le_mul (mul_le_mul_of_nonneg_left hcount (by norm_num))
        (pow_le_pow_left₀ hlog_pos.le hlog.le 2) (sq_nonneg _) (by positivity)
    _ = s * 8100 := by ring
    _ < s * (s / 10 ^ 5) := mul_lt_mul_of_pos_left (by linarith) (by linarith)
    _ = (n : ℝ) / 10 ^ 5 := by rw [← hs_sq]; ring
