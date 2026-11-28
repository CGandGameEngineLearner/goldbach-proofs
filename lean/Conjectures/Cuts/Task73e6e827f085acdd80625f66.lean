import Mathlib

private lemma norm_exp_I_sub_exp_I_le (a b : ℝ) :
    ‖Complex.exp ((a : ℂ) * Complex.I) - Complex.exp ((b : ℂ) * Complex.I)‖ ≤ |a - b| := by
  have hfac : Complex.exp ((a : ℂ) * Complex.I) - Complex.exp ((b : ℂ) * Complex.I) =
      Complex.exp ((b : ℂ) * Complex.I) * (Complex.exp (((a - b : ℝ) : ℂ) * Complex.I) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hfac, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  set t : ℝ := a - b
  have hre : (Complex.exp ((t : ℂ) * Complex.I) - 1).re = Real.cos t - 1 := by
    rw [Complex.sub_re, Complex.one_re, Complex.exp_ofReal_mul_I_re]
  have him : (Complex.exp ((t : ℂ) * Complex.I) - 1).im = Real.sin t := by
    rw [Complex.sub_im, Complex.one_im, Complex.exp_ofReal_mul_I_im, sub_zero]
  have hsq : ‖Complex.exp ((t : ℂ) * Complex.I) - 1‖ ^ 2 = 4 * Real.sin (t / 2) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    have hcos : Real.cos t = 1 - 2 * Real.sin (t / 2) ^ 2 := by
      have h1 := Real.cos_two_mul' (t / 2)
      have h2 : 2 * (t / 2) = t := by ring
      rw [h2] at h1
      have h3 := Real.sin_sq_add_cos_sq (t / 2)
      linarith
    have hsin : Real.sin t = 2 * Real.sin (t / 2) * Real.cos (t / 2) := by
      have h1 := Real.sin_two_mul (t / 2)
      have h2 : 2 * (t / 2) = t := by ring
      rw [h2] at h1
      exact h1
    rw [hcos, hsin]
    have hsc : Real.sin (t / 2) ^ 2 + Real.cos (t / 2) ^ 2 = 1 := Real.sin_sq_add_cos_sq (t / 2)
    calc
      (1 - 2 * Real.sin (t / 2) ^ 2 - 1) * (1 - 2 * Real.sin (t / 2) ^ 2 - 1) +
          2 * Real.sin (t / 2) * Real.cos (t / 2) * (2 * Real.sin (t / 2) * Real.cos (t / 2))
        = 4 * Real.sin (t / 2) ^ 2 * (Real.sin (t / 2) ^ 2 + Real.cos (t / 2) ^ 2) := by ring
      _ = 4 * Real.sin (t / 2) ^ 2 * 1 := by rw [hsc]
      _ = 4 * Real.sin (t / 2) ^ 2 := by ring
  have hsin_le : |Real.sin (t / 2)| ≤ |t / 2| := Real.abs_sin_le_abs
  have hsin_sq : Real.sin (t / 2) ^ 2 ≤ (t / 2) ^ 2 := by
    have h := mul_self_le_mul_self (abs_nonneg _) hsin_le
    simpa [sq, abs_mul_abs_self] using h
  have hle_sq : ‖Complex.exp ((t : ℂ) * Complex.I) - 1‖ ^ 2 ≤ |t| ^ 2 := by
    rw [hsq, sq_abs]
    linarith
  by_contra hlt
  push_neg at hlt
  have h0 : 0 ≤ |t| := abs_nonneg t
  nlinarith

theorem Conjectures.Cuts.Task73e6e827f085acdd80625f66 : (have x1 : ℕ → ℝ → ℂ := fun (x1 : ℕ) (x2 : ℝ) => ∑ x3 ∈ Finset.range x1, Complex.exp (↑((2 : ℝ) * Real.pi * (2 : ℝ) ^ x3 * x2) * Complex.I); have x2 : ℕ → ℝ → ℂ := fun (x2 : ℕ) (x3 : ℝ) => ∑ x4 ∈ Finset.range x2, Complex.exp (↑((2 : ℝ) * Real.pi * ↑⌊(65536 : ℝ) * (2 : ℝ) ^ x4 * x3⌋ / (65536 : ℝ)) * Complex.I); ∀ (x3 : ℕ) (x4 : ℝ), ‖x2 x3 x4 - x1 x3 x4‖ ≤ (2 : ℝ) * Real.pi / (65536 : ℝ) * ↑x3) := by
  dsimp only
  intro L x
  rw [← Finset.sum_sub_distrib]
  calc
    ‖∑ k ∈ Finset.range L,
        (Complex.exp (↑((2 : ℝ) * Real.pi * ↑⌊(65536 : ℝ) * (2 : ℝ) ^ k * x⌋ / (65536 : ℝ)) * Complex.I) -
         Complex.exp (↑((2 : ℝ) * Real.pi * (2 : ℝ) ^ k * x) * Complex.I))‖
      ≤ ∑ k ∈ Finset.range L,
        ‖Complex.exp (↑((2 : ℝ) * Real.pi * ↑⌊(65536 : ℝ) * (2 : ℝ) ^ k * x⌋ / (65536 : ℝ)) * Complex.I) -
         Complex.exp (↑((2 : ℝ) * Real.pi * (2 : ℝ) ^ k * x) * Complex.I)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _k ∈ Finset.range L, ((2 : ℝ) * Real.pi / (65536 : ℝ)) := by
        apply Finset.sum_le_sum
        intro k _
        have hstep := norm_exp_I_sub_exp_I_le
          ((2 : ℝ) * Real.pi * ↑⌊(65536 : ℝ) * (2 : ℝ) ^ k * x⌋ / (65536 : ℝ))
          ((2 : ℝ) * Real.pi * (2 : ℝ) ^ k * x)
        refine hstep.trans ?_
        set u : ℝ := (65536 : ℝ) * (2 : ℝ) ^ k * x
        have hfl_le : (⌊u⌋ : ℝ) ≤ u := Int.floor_le u
        have hlt_fl : u - 1 < (⌊u⌋ : ℝ) := Int.sub_one_lt_floor u
        have hdiff :
            (2 : ℝ) * Real.pi * ↑⌊u⌋ / (65536 : ℝ) - (2 : ℝ) * Real.pi * (2 : ℝ) ^ k * x =
            ((2 : ℝ) * Real.pi / (65536 : ℝ)) * ((⌊u⌋ : ℝ) - u) := by
          dsimp [u]
          ring
        rw [hdiff, abs_mul]
        have hc : 0 ≤ (2 : ℝ) * Real.pi / (65536 : ℝ) := by linarith [Real.pi_pos]
        rw [abs_of_nonneg hc]
        have habs : |(⌊u⌋ : ℝ) - u| ≤ 1 := by
          rw [abs_le]
          constructor <;> linarith
        nlinarith
    _ = (2 : ℝ) * Real.pi / (65536 : ℝ) * ↑L := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm]
