import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_levent_rh_zero_line :
    RiemannHypothesis → ∀ (ρ : ℂ) (u : ℝ), 0 < ρ.re → ρ.re < 1 → riemannZeta ρ = 0 → 1 ≤ u → ‖(u : ℂ)^ρ / ρ‖ = Real.sqrt u / ‖ρ‖ := by
  intro hRH ρ u h0 h1 hz hu
  have hre : ρ.re = 1/2 := by
    refine hRH ρ hz ?_ ?_
    · rintro ⟨n, hn⟩
      have hneg : ρ.re = -(2 * ((n : ℝ) + 1)) := by
        rw [hn]
        simp
      have hn0 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
      nlinarith
    · intro h1c
      rw [h1c] at h1
      norm_num at h1
  rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : (0:ℝ) < u), hre,
    Real.sqrt_eq_rpow]
