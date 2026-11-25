import Mathlib

open Filter
open scoped Topology

namespace PEqualNP.Outside

theorem L_goldbach_power_box_vanishing :
    ∀ ε : ℝ, 0<ε → ∃ X : ℕ, ∀ n≥X, ((Nat.sqrt n:ℝ)*(Nat.log 2 n:ℝ))*Real.log ((n+1:ℕ):ℝ)^2/(n:ℝ)<ε := by
  intro ε hε
  have hlim : Tendsto (fun n : ℕ => (Real.log n)^3 / Real.sqrt n) atTop (𝓝 0) := by
    have ht := (isLittleO_log_rpow_rpow_atTop 3 (show 0 < (1/2 : ℝ) by norm_num)).tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
    simpa only [Function.comp_def, ← Real.sqrt_eq_rpow, show (3:ℝ) = (3:ℕ) by norm_num, Real.rpow_natCast] using ht
  obtain ⟨X, hX⟩ := eventually_atTop.mp (hlim.eventually_lt_const (show 0 < ε/8 by positivity))
  refine ⟨max X 2, ?_⟩
  intro n hn
  have hn2 := (le_max_right X 2).trans hn
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hn₀ : 0 < (n : ℝ) := by linarith
  have hs := Real.sq_sqrt hn₀.le
  have hroot : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn₀
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
  have hnat : (Nat.log 2 n : ℝ) ≤ 2 * Real.log n := by
    have hp : (2:ℝ)^(Nat.log 2 n) ≤ n := by exact_mod_cast Nat.pow_log_le_self 2 (by omega : n ≠ 0)
    have hp' := Real.log_le_log (by positivity) hp
    rw [Real.log_pow] at hp'
    nlinarith [Real.log_two_gt_d9, mul_nonneg (show (0:ℝ) ≤ Nat.log 2 n by positivity) (show 0 ≤ Real.log 2-1/2 by linarith [Real.log_two_gt_d9])]
  have hsucc : Real.log ((n+1:ℕ):ℝ) ≤ 2 * Real.log n := by
    have h := Real.log_le_log (by positivity : 0 < ((n+1:ℕ):ℝ)) (show ((n+1:ℕ):ℝ) ≤ (n:ℝ)^2 by push_cast; nlinarith [mul_nonneg hn₀.le (sub_nonneg.mpr hn')])
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  have hsq := pow_le_pow_left₀ (Real.log_nonneg (show 1 ≤ ((n+1:ℕ):ℝ) by exact_mod_cast Nat.le_add_left 1 n)) hsucc 2
  have hbound := mul_le_mul_of_nonneg_right (mul_le_mul Real.nat_sqrt_le_real_sqrt hnat (by positivity) (by positivity)) (sq_nonneg (Real.log ((n+1:ℕ):ℝ)))
  have hsmall := (div_lt_iff₀ hroot).mp (hX n ((le_max_left X 2).trans hn))
  apply (div_lt_iff₀ hn₀).mpr
  calc
    _ ≤ Real.sqrt n * (2*Real.log n) * (2*Real.log n)^2 := hbound.trans (mul_le_mul_of_nonneg_left hsq (by positivity))
    _ = Real.sqrt n * (8 * (Real.log n)^3) := by ring
    _ < Real.sqrt n * (ε*Real.sqrt n) := by apply mul_lt_mul_of_pos_left _ hroot; linarith
    _ = _ := by nlinarith [congrArg (fun u : ℝ => ε*u) hs]

end PEqualNP.Outside
