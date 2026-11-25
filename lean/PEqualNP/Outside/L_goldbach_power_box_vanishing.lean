import Mathlib

open Finset

theorem PEqualNP.Outside.L_goldbach_power_box_vanishing :
    ∀ ε : ℝ, 0<ε → ∃ X : ℕ, ∀ n≥X, ((Nat.sqrt n:ℝ)*(Nat.log 2 n:ℝ))*Real.log ((n+1:ℕ):ℝ)^2/(n:ℝ)<ε := by
  intro ε hε
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlim : Filter.Tendsto (fun n : ℕ => Real.log (n:ℝ)^3 / Real.sqrt (n:ℝ))
      Filter.atTop (nhds 0) := by
    have h := (isLittleO_log_rpow_rpow_atTop (3:ℝ) (by norm_num : 0 < (1/2:ℝ))).tendsto_div_nhds_zero
    simpa [Function.comp_def, Real.sqrt_eq_rpow] using h.comp tendsto_natCast_atTop_atTop
  obtain ⟨X, hX⟩ := Filter.eventually_atTop.mp
    ((tendsto_order.mp hlim).2 (ε*Real.log 2/4) (by positivity))
  refine ⟨max X 2, fun n hn => ?_⟩
  have hN : (2:ℝ) ≤ n := by exact_mod_cast (le_trans (le_max_right X 2) hn)
  have hpos : (0:ℝ) < n := by linarith
  have hlog : 0 ≤ Real.log (n:ℝ) := Real.log_nonneg (by linarith)
  have hs := Real.sq_sqrt hpos.le
  have hspos := Real.sqrt_pos.mpr hpos
  have hg : Real.log ((n+1:ℕ):ℝ) ≤ 2*Real.log (n:ℝ) := by
    rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, ← Real.log_pow]
    apply Real.log_le_log (by positivity)
    push_cast
    nlinarith
  have hb : (Nat.log 2 n : ℝ) ≤ Real.log (n:ℝ)/Real.log 2 := by
    simpa only [Real.logb, Nat.cast_ofNat] using Real.natLog_le_logb n 2
  have hz : 0 ≤ Real.log ((n+1:ℕ):ℝ) := Real.log_nonneg (by push_cast; linarith)
  have hsmall := hX n (le_trans (le_max_left X 2) hn)
  change Real.log (n:ℝ)^3 / Real.sqrt (n:ℝ) < ε * Real.log 2 / 4 at hsmall
  calc
    _ ≤ Real.sqrt (n:ℝ) * (Real.log (n:ℝ)/Real.log 2) * (2*Real.log (n:ℝ))^2 / n := by
      apply div_le_div_of_nonneg_right _ hpos.le
      exact mul_le_mul (mul_le_mul Real.nat_sqrt_le_real_sqrt hb (by positivity) hspos.le)
        (pow_le_pow_left₀ hz hg 2) (by positivity) (by positivity)
    _ = (Real.log (n:ℝ)^3 / Real.sqrt (n:ℝ)) * (4 / Real.log 2) := by
      field_simp
      linear_combination 4 * Real.log (n:ℝ)^3 * hs
    _ < ε := by
      apply (mul_lt_mul_of_pos_right hsmall (by positivity : 0 < 4 / Real.log 2)).trans_eq
      field_simp
