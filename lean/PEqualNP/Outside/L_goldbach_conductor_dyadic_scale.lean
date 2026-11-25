import Mathlib

theorem PEqualNP.Outside.L_goldbach_conductor_dyadic_scale :
    ∀ (c ε : ℝ), 0<c → 0<ε → ∀ k : ℕ, 4*c*Real.log 2/ε < (2:ℝ)^k → |4*c*Real.log 2/(2:ℝ)^k|<ε := by
  intro c e hc he k hk
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hnum : 0 < 4*c*Real.log 2 := by positivity
  have h2k : 0 < (2:ℝ)^k := by positivity
  rw [abs_of_pos (by positivity)]
  rw [div_lt_iff₀ h2k]
  have h := hk
  rw [div_lt_iff₀ he] at h
  linarith
