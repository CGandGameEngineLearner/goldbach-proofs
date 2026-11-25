import Mathlib

open Finset

theorem PEqualNP.Outside.L_goldbach_ap_power_box_scale :
    ∃ C : ℝ, 0<C ∧ ∀ n : ℕ, 2≤n → (Nat.sqrt n:ℝ)*(Nat.log 2 n:ℝ)*Real.log (n:ℝ) ≤ C*Real.sqrt (n:ℝ)*(Real.log (2*(n:ℝ)))^2 := by
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨(Real.log 2)⁻¹, inv_pos.mpr htwo, ?_⟩
  intro n hn
  have hn' : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hpos : (0:ℝ) < n := by linarith
  have hlog : 0 ≤ Real.log (n:ℝ) := Real.log_nonneg (by linarith)
  have hmono : Real.log (n:ℝ) ≤ Real.log (2*(n:ℝ)) :=
    Real.log_le_log hpos (by linarith)
  have hbase : (Nat.log 2 n : ℝ) ≤ Real.log (n:ℝ)/Real.log 2 := by
    simpa only [Real.logb, Nat.cast_ofNat] using Real.natLog_le_logb n 2
  calc
    _ ≤ Real.sqrt (n:ℝ) * (Real.log (n:ℝ)/Real.log 2) * Real.log (n:ℝ) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul Real.nat_sqrt_le_real_sqrt hbase (by positivity) (Real.sqrt_nonneg _)) hlog
    _ = (Real.log 2)⁻¹ * Real.sqrt (n:ℝ) * (Real.log (n:ℝ))^2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlog hmono 2) (by positivity)
