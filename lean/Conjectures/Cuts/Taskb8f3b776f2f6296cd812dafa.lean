import Mathlib

/-!
Absorb the number of allowed binary shifts into a power saving.
The asymptotic input is Mathlib's `isLittleO_log_rpow_atTop`;
the integer logarithm is compared using `Nat.pow_log_le_self`.
-/

open Filter

theorem Conjectures.Cuts.Taskb8f3b776f2f6296cd812dafa :
    (∃ (x1 : ℕ), ∀ x2 ≥ x1, (↑(Nat.log (2 : ℕ) x2 / (2 : ℕ)) : ℝ) ≤ (↑x2 : ℝ) ^ (1 / 100 : ℝ)) := by
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hreal := (isLittleO_log_rpow_atTop
    (by norm_num : (0:ℝ) < 1/100)).bound htwo
  have hnat : ∀ᶠ n : ℕ in atTop,
      ‖Real.log (n:ℝ)‖ ≤ Real.log 2 * ‖(n:ℝ)^(1/100:ℝ)‖ :=
    Filter.Tendsto.eventually tendsto_natCast_atTop_atTop hreal
  obtain ⟨T, hT⟩ := eventually_atTop.mp hnat
  refine ⟨max T 1, ?_⟩
  intro X hX
  have hTX : T ≤ X := (le_max_left T 1).trans hX
  have hX1 : 1 ≤ X := (le_max_right T 1).trans hX
  have hX0 : X ≠ 0 := by omega
  have hXreal : (1:ℝ) ≤ X := by exact_mod_cast hX1
  have hpow : (2:ℝ)^(Nat.log 2 X) ≤ (X:ℝ) := by
    exact_mod_cast Nat.pow_log_le_self 2 hX0
  have hlog := Real.log_le_log (pow_pos (by norm_num : (0:ℝ) < 2) _) hpow
  rw [Real.log_pow] at hlog
  have hsmall := hT X hTX
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hXreal),
    Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by positivity) _)] at hsmall
  have hbound : (Nat.log 2 X:ℝ) ≤ (X:ℝ)^(1/100:ℝ) := by
    apply (mul_le_mul_iff_right₀ htwo).mp
    simpa only [mul_comm] using hlog.trans hsmall
  exact (show ((Nat.log 2 X / 2 : ℕ):ℝ) ≤ (Nat.log 2 X:ℝ) by
    exact_mod_cast Nat.div_le_self (Nat.log 2 X) 2).trans hbound
