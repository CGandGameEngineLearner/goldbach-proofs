import Mathlib

theorem Conjectures.Cuts.Task73e6e827f085acdd80625f66 : (have x1 : ℕ → ℝ → ℂ := fun (x1 : ℕ) (x2 : ℝ) => ∑ x3 ∈ Finset.range x1, Complex.exp (↑((2 : ℝ) * Real.pi * (2 : ℝ) ^ x3 * x2) * Complex.I); have x2 : ℕ → ℝ → ℂ := fun (x2 : ℕ) (x3 : ℝ) => ∑ x4 ∈ Finset.range x2, Complex.exp (↑((2 : ℝ) * Real.pi * ↑⌊(65536 : ℝ) * (2 : ℝ) ^ x4 * x3⌋ / (65536 : ℝ)) * Complex.I); ∀ (x3 : ℕ) (x4 : ℝ), ‖x2 x3 x4 - x1 x3 x4‖ ≤ (2 : ℝ) * Real.pi / (65536 : ℝ) * ↑x3) := by
  intro original truncated L x
  have angle (a b : ℝ) :
      ‖Complex.exp ((a : ℂ) * Complex.I) - Complex.exp ((b : ℂ) * Complex.I)‖ ≤ |a - b| := by
    have h := (convex_halfSpace_re_le 0).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun z _ => (Complex.hasDerivAt_exp z).hasDerivWithinAt)
      (fun z hz => show ‖Complex.exp z‖ ≤ (1 : ℝ) by
        rw [Complex.norm_exp]; exact Real.exp_le_one_iff.mpr hz)
      (x := (b : ℂ) * Complex.I) (y := (a : ℂ) * Complex.I) (by simp) (by simp)
    simpa [← sub_mul, ← Complex.ofReal_sub, norm_mul, Real.norm_eq_abs] using h
  dsimp only [truncated, original]
  rw [← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _j ∈ Finset.range L, 2 * Real.pi / 65536 := by
      apply Finset.sum_le_sum
      intro j _
      apply (angle _ _).trans
      let t : ℝ := 65536 * 2 ^ j * x
      have h₁ := Int.floor_le t
      have h₂ := Int.lt_floor_add_one t
      have herr : |(⌊t⌋ : ℝ) - t| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
      have hscale : 2 * Real.pi / 65536 * ((⌊t⌋ : ℝ) - t) =
          2 * Real.pi * ↑⌊65536 * (2 : ℝ)^j * x⌋ / 65536 - 2 * Real.pi * 2^j * x := by
        dsimp [t]; ring
      rw [← hscale, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * Real.pi / 65536)]
      exact (mul_le_mul_of_nonneg_left herr (by positivity)).trans_eq (mul_one _)
    _ = _ := by simp [mul_comm]
