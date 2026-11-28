import Mathlib

open Filter Asymptotics

theorem Conjectures.Cuts.Taskb8f3b776f2f6296cd812dafa : (∃ (x1 : ℕ), ∀ x2 ≥ x1, (↑(Nat.log (2 : ℕ) x2 / (2 : ℕ)) : ℝ) ≤ (↑x2 : ℝ) ^ (1 / 100 : ℝ)) := by
  apply eventually_atTop.mp
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 100)).def h2
  filter_upwards [h.natCast_atTop, eventually_ge_atTop 1] with n hn hn1
  have hnlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn1)
  have bound : Real.log (n : ℝ) ≤ Real.log 2 * (n : ℝ) ^ (1 / 100 : ℝ) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hnlog,
      abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)] using hn
  calc
    _ ≤ ((Nat.log 2 n : ℕ) : ℝ) := by exact_mod_cast Nat.div_le_self (Nat.log 2 n) 2
    _ ≤ Real.log (n : ℝ) / Real.log 2 := by
      rw [← Real.natFloor_logb_natCast]
      exact Nat.floor_le (show 0 ≤ Real.logb (2 : ℝ) n from div_nonneg hnlog h2.le)
    _ ≤ _ := (div_le_iff₀ h2).mpr (by simpa [mul_comm] using bound)
