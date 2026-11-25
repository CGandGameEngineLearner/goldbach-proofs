import Mathlib

set_option maxRecDepth 4096 in
theorem PEqualNP.Outside.L_goldbach_finite_power_contamination_budget :
    ∀ (n : ℕ), 4*10^18 < n → Real.log (Real.log n) < (76:ℝ)/20 → 2*((Nat.sqrt n:ℝ)+(Nat.log 2 n:ℝ)*(n:ℝ)^(1/3:ℝ))*(Real.log n)^2 < (n:ℝ)/10^5 := by
  intro n lower band
  have realLower : (4 * 10 ^ 18 : ℝ) < n := by exact_mod_cast lower
  have logPos : 0 < Real.log n := Real.log_pos (by linarith)
  have expBound : Real.exp 1 ≤ 2.7183 := Real.exp_one_lt_d9.le.trans (by norm_num)
  have powerBound (degree : ℕ) : Real.exp degree ≤ (2.7183 : ℝ) ^ degree := by
    simpa only [← Real.exp_nat_mul, mul_one] using
      pow_le_pow_left₀ (Real.exp_nonneg 1) expBound degree
  have logUpper : Real.log n < 45 := by
    refine ((Real.log_lt_iff_lt_exp logPos).mp band).trans ?_
    apply lt_of_pow_lt_pow_left₀ 5 (by norm_num)
    rw [← Real.exp_nat_mul]
    norm_num only [Nat.cast_ofNat, show (5 : ℝ) * (76 / 20) = 19 by norm_num]
    exact (powerBound 19).trans_lt (by norm_num)
  have binaryUpper : (Nat.log 2 n : ℝ) ≤ 100 := by
    have size : (n : ℝ) < (2 : ℝ) ^ 100 := calc
      (n : ℝ) < Real.exp 45 := (Real.log_lt_iff_lt_exp (by linarith)).mp logUpper
      _ ≤ (2.7183 : ℝ) ^ 45 := powerBound 45
      _ ≤ (3 : ℝ) ^ 45 := pow_le_pow_left₀ (by norm_num) (by norm_num) 45
      _ < (2 : ℝ) ^ 100 := by norm_num
    have sizeNat : n < 2 ^ 100 := by exact_mod_cast size
    exact_mod_cast (Nat.log_lt_of_lt_pow (by omega : n ≠ 0) sizeNat).le
  have sqrtBudget : (Nat.sqrt n : ℝ) ≤ n / 10 ^ 9 := by
    have floorLower : 10 ^ 9 ≤ Nat.sqrt n := Nat.le_sqrt'.mpr (by omega)
    have scaled := (Nat.mul_le_mul_left (Nat.sqrt n) floorLower).trans (Nat.sqrt_le n)
    apply (le_div_iff₀ (by norm_num)).mpr
    exact_mod_cast scaled
  let root : ℝ := (n : ℝ) ^ (1 / 3 : ℝ)
  have rootNonneg : 0 ≤ root := Real.rpow_nonneg (by positivity) _
  have cube : root ^ 3 = n := by
    simpa only [root, one_div, Nat.cast_ofNat] using
      Real.rpow_inv_natCast_pow (x := (n : ℝ)) (by positivity) (by decide : (3 : ℕ) ≠ 0)
  have rootLower : (10 : ℝ) ^ 6 ≤ root := by
    apply le_of_pow_le_pow_left₀ (by decide : 3 ≠ 0) rootNonneg
    rw [cube]
    linarith
  have rootBudget : root ≤ n / 10 ^ 12 := by
    have squareLower := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 10 ^ 6) rootLower 2
    have scaled := mul_le_mul_of_nonneg_left squareLower rootNonneg
    nlinarith only [scaled, cube]
  change 2 * ((Nat.sqrt n : ℝ) + (Nat.log 2 n : ℝ) * root) * (Real.log n) ^ 2 < _
  calc
    _ ≤ 2 * ((n : ℝ) / 10 ^ 9 + 100 * ((n : ℝ) / 10 ^ 12)) * 45 ^ 2 := by
      gcongr
    _ < _ := by linarith
