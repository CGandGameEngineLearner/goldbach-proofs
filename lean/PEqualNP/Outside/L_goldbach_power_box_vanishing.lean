import Mathlib

open Filter
open scoped Topology

theorem PEqualNP.Outside.L_goldbach_power_box_vanishing :
    ∀ ε : ℝ, 0<ε → ∃ X : ℕ, ∀ n≥X, ((Nat.sqrt n:ℝ)*(Nat.log 2 n:ℝ))*Real.log ((n+1:ℕ):ℝ)^2/(n:ℝ)<ε := by
  intro ε hε
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlim : Tendsto (fun n : ℕ => Real.log (n:ℝ)^3 / Real.sqrt n) atTop (𝓝 0) := by
    have h := (isLittleO_log_rpow_rpow_atTop ((3:ℕ):ℝ) (by norm_num : (0:ℝ) < 1/2)).tendsto_div_nhds_zero
    simpa only [Function.comp_def, Real.rpow_natCast, Real.sqrt_eq_rpow] using
      h.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hsmall := hlim.eventually_lt_const (show 0 < ε * Real.log 2 / 4 by positivity)
  apply eventually_atTop.1
  filter_upwards [hsmall, eventually_ge_atTop 2] with n hsmall hn
  have hn2 : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0:ℝ) < n := by linarith
  have hspos := Real.sqrt_pos.2 hnpos
  have hs := Real.sq_sqrt hnpos.le
  have hsbound : (Nat.sqrt n : ℝ) ≤ Real.sqrt n := by
    have hsq : (Nat.sqrt n : ℝ) * Nat.sqrt n ≤ n := by exact_mod_cast Nat.sqrt_le n
    nlinarith
  have hl := Real.log_nonneg (by linarith : (1:ℝ) ≤ n)
  have hlb : (Nat.log 2 n : ℝ) ≤ Real.log (n:ℝ) / Real.log 2 := by
    simpa [Real.logb] using Real.natLog_le_logb n 2
  have harg : ((n+1:ℕ):ℝ) ≤ (n:ℝ)^2 := by
    push_cast
    nlinarith [mul_nonneg (sub_nonneg.mpr hn2) hnpos.le]
  have hinc : Real.log ((n+1:ℕ):ℝ) ≤ 2 * Real.log n := by
    simpa only [Real.log_pow, Nat.cast_ofNat] using Real.log_le_log (by positivity) harg
  have hnn : 0 ≤ Real.log ((n+1:ℕ):ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n+1 by omega))
  have hsquare := pow_le_pow_left₀ hnn hinc 2
  calc
    _ ≤ Real.sqrt n * (Real.log n / Real.log 2) * (2 * Real.log n)^2 / n := by
      gcongr
    _ = (Real.log n ^ 3 / Real.sqrt n) * 4 / Real.log 2 := by
      field_simp
      linear_combination (4 * Real.log (n:ℝ)^3) * hs
    _ < ε := by
      apply (div_lt_iff₀ hlog2).mpr
      linarith
