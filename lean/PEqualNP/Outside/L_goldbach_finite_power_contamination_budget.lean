import Mathlib

theorem PEqualNP.Outside.L_goldbach_finite_power_contamination_budget :
    ∀ (n : ℕ), 4*10^18 < n → Real.log (Real.log n) < (76:ℝ)/20 → 2*((Nat.sqrt n:ℝ)+(Nat.log 2 n:ℝ)*(n:ℝ)^(1/3:ℝ))*(Real.log n)^2 < (n:ℝ)/10^5 := by
  intro n hn hband
  have hn_large : (4 * 10 ^ 18 : ℝ) < n := by exact_mod_cast hn
  have hn_pos : (0 : ℝ) < n := by linarith
  have hlog_pos : 0 < Real.log n := Real.log_pos (by linarith)
  have hlog : Real.log n < 64 := calc
    Real.log n = Real.exp (Real.log (Real.log n)) := (Real.exp_log hlog_pos).symm
    _ < Real.exp 4 := Real.exp_lt_exp.mpr (hband.trans (by norm_num))
    _ = Real.exp 1 ^ (4 : ℕ) := (Real.exp_one_pow 4).symm
    _ ≤ (11 / 4 : ℝ) ^ (4 : ℕ) := by gcongr; linarith [Real.exp_one_lt_d9]
    _ < 64 := by norm_num
  have hbits : (Nat.log 2 n : ℝ) ≤ 128 := by
    have hpow : (2 : ℝ) ^ (Nat.log 2 n) ≤ n := by
      exact_mod_cast Nat.pow_log_le_self 2 (show n ≠ 0 by omega)
    have hlogpow := (Real.log_le_log_iff (by positivity) hn_pos).2 hpow
    rw [Real.log_pow] at hlogpow
    have hhalf : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith only [Real.log_two_gt_d9]
    have hmul := mul_le_mul_of_nonneg_left hhalf (Nat.cast_nonneg (α := ℝ) (Nat.log 2 n))
    linarith only [hmul, hlogpow, hlog]

  have hs_sq : (Nat.sqrt n : ℝ) ^ 2 ≤ n := by exact_mod_cast Nat.sqrt_le' n
  have hs : (Nat.sqrt n : ℝ) ≤ (n : ℝ) / 10^9 := by
    nlinarith only [hs_sq, hn_large, sq_nonneg ((Nat.sqrt n : ℝ) - 10^9)]
  let c : ℝ := (n : ℝ) ^ (1 / 3 : ℝ)
  have hc_nonneg : 0 ≤ c := Real.rpow_nonneg hn_pos.le _
  have hc_cube : c ^ (3 : ℕ) = n := by
    dsimp [c]
    rw [← Real.rpow_natCast _ 3, ← Real.rpow_mul hn_pos.le]
    norm_num
  have hc : c ≤ (n : ℝ) / 10^12 := by
    by_cases h : c ≤ 10^6
    · linarith only [h, hn_large]
    · have hge : (10 : ℝ)^6 ≤ c := le_of_not_ge h
      have hprod : c * (10 : ℝ)^6 * (10 : ℝ)^6 ≤ c*c*c := by gcongr
      linarith only [hprod, hc_cube, show c*c*c = c^3 by ring]
  have hmass : (Nat.sqrt n : ℝ) + (Nat.log 2 n : ℝ) * c ≤
      (n : ℝ) / 10^9 + 128 * ((n : ℝ) / 10^12) :=
    add_le_add hs (mul_le_mul hbits hc hc_nonneg (by norm_num))
  have hlog_sq : (Real.log n)^2 ≤ 64^2 := by gcongr
  change 2 * ((Nat.sqrt n : ℝ) + (Nat.log 2 n : ℝ) * c) * (Real.log n)^2 < _
  calc
    _ ≤ 2 * ((n : ℝ) / 10^9 + 128 * ((n : ℝ) / 10^12)) * (64 : ℝ)^2 :=
      mul_le_mul (mul_le_mul_of_nonneg_left hmass (by norm_num)) hlog_sq
        (sq_nonneg _) (by positivity)
    _ < (n : ℝ) / 10^5 := by linarith only [hn_pos]
