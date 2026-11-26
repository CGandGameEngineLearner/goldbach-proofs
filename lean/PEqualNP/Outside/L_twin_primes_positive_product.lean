import Mathlib

theorem PEqualNP.Outside.L_twin_primes_positive_product :
    (let f := fun (p : ℕ) => if p.Prime ∧ 2 < p then 1-1/((p:ℝ)-1)^2 else 1; let twinC := ∏' p : ℕ, f p; 0 < twinC) := by
  let f : ℕ → ℝ := fun p => if p.Prime ∧ 2 < p then 1 - 1 / ((p : ℝ) - 1) ^ 2 else 1
  change 0 < ∏' p : ℕ, f p
  -- Every factor is positive: only odd primes change the factor `1`.
  have hpos : ∀ p : ℕ, 0 < f p := by
    intro p
    change 0 < (if p.Prime ∧ 2 < p then (1 : ℝ) - 1 / ((p : ℝ) - 1) ^ 2 else 1)
    split_ifs with h
    · have hp3 : (3 : ℝ) ≤ (p : ℝ) := by
        have : 3 ≤ p := by omega
        exact_mod_cast this
      have hsq : (4 : ℝ) ≤ ((p : ℝ) - 1) ^ 2 := by nlinarith
      have hle : 1 / ((p : ℝ) - 1) ^ 2 ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) hsq
      linarith
    · norm_num
  -- The logarithm of every factor is bounded by a shifted reciprocal square.
  have hlog_bound : ∀ p : ℕ, ‖Real.log (f p)‖ ≤ 8 / ((p : ℝ) + 1) ^ 2 := by
    intro p
    change ‖Real.log (if p.Prime ∧ 2 < p then (1 : ℝ) - 1 / ((p : ℝ) - 1) ^ 2 else 1)‖ ≤
      8 / ((p : ℝ) + 1) ^ 2
    by_cases h : p.Prime ∧ 2 < p
    · rw [if_pos h]
      have hp3 : (3 : ℝ) ≤ (p : ℝ) := by
        have : 3 ≤ p := by omega
        exact_mod_cast this
      have hden : (0 : ℝ) < ((p : ℝ) - 1) ^ 2 := by nlinarith
      have hbpos : (0 : ℝ) < (p : ℝ) + 1 := by linarith
      have hsq : (4 : ℝ) ≤ ((p : ℝ) - 1) ^ 2 := by nlinarith
      have ha_pos : (0 : ℝ) < 1 / ((p : ℝ) - 1) ^ 2 := by positivity
      have ha_le : 1 / ((p : ℝ) - 1) ^ 2 ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) hsq
      have hone_sub_pos : (0 : ℝ) < 1 - 1 / ((p : ℝ) - 1) ^ 2 := by linarith
      have hone_sub_le_one : 1 - 1 / ((p : ℝ) - 1) ^ 2 ≤ 1 := by linarith
      have hlog_nonpos : Real.log (1 - 1 / ((p : ℝ) - 1) ^ 2) ≤ 0 :=
        Real.log_nonpos (le_of_lt hone_sub_pos) hone_sub_le_one
      have habs : ‖Real.log (1 - 1 / ((p : ℝ) - 1) ^ 2)‖ =
          -Real.log (1 - 1 / ((p : ℝ) - 1) ^ 2) := by
        rw [Real.norm_eq_abs, abs_of_nonpos hlog_nonpos]
      rw [habs]
      have hlog_eq : -Real.log (1 - 1 / ((p : ℝ) - 1) ^ 2) =
          Real.log (1 / (1 - 1 / ((p : ℝ) - 1) ^ 2)) := by
        rw [Real.log_div (by norm_num) (ne_of_gt hone_sub_pos), Real.log_one, zero_sub]
      rw [hlog_eq]
      have hratio : 1 / (1 - 1 / ((p : ℝ) - 1) ^ 2) ≤ 1 + 2 * (1 / ((p : ℝ) - 1) ^ 2) := by
        rw [div_le_iff₀ (by linarith)]
        nlinarith
      have hlog_le : Real.log (1 / (1 - 1 / ((p : ℝ) - 1) ^ 2)) ≤
          Real.log (1 + 2 * (1 / ((p : ℝ) - 1) ^ 2)) :=
        Real.log_le_log (by positivity) hratio
      have hlog_le2 : Real.log (1 + 2 * (1 / ((p : ℝ) - 1) ^ 2)) ≤
          2 * (1 / ((p : ℝ) - 1) ^ 2) := by
        have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + 2 * (1 / ((p : ℝ) - 1) ^ 2) by positivity)
        linarith
      have hbound : 2 * (1 / ((p : ℝ) - 1) ^ 2) ≤ 8 / ((p : ℝ) + 1) ^ 2 := by
        rw [mul_one_div, div_le_div_iff₀ hden (by positivity : (0:ℝ) < ((p:ℝ)+1)^2)]
        nlinarith
      linarith
    · rw [if_neg h, Real.log_one, norm_zero]
      positivity
  have hsummable : Summable (fun p : ℕ => Real.log (f p)) := by
    refine Summable.of_norm_bounded ?_ hlog_bound
    have hbase : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
      (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
    have hshift : Summable (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ)) ^ 2) :=
      (summable_nat_add_iff (G := ℝ) 1).mpr hbase
    have hmul := hshift.mul_left 8
    convert hmul using 1 with n
    push_cast
    ring_nf
  rw [← Real.rexp_tsum_eq_tprod hpos hsummable]
  exact Real.exp_pos _
