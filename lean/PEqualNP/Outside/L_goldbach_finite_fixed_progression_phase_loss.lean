import Mathlib

theorem PEqualNP.Outside.L_goldbach_finite_fixed_progression_phase_loss :
    ∀ (N : ℕ) (b : ℕ → ℂ) (θ : ℝ) (E : ℝ), 0 ≤ E → (∀ m ≤ N, ‖∑ k ∈ Finset.range m, b k‖ ≤ E) → ‖∑ k ∈ Finset.range N, b k * Complex.exp (Complex.I*((2*Real.pi*θ*(k:ℝ):ℝ):ℂ))‖ ≤ E*(1+2*Real.pi*N*|θ|) := by
  intro N b θ E hE hprefix
  let a : ℝ := 2 * Real.pi * θ
  let z : ℕ → ℂ := fun m => Complex.exp (Complex.I * ((a * (m : ℝ) : ℝ) : ℂ))
  let z₁ : ℂ := Complex.exp (Complex.I * (a : ℂ))
  let P : ℕ → ℂ := fun m => ∑ k ∈ Finset.range m, b k
  let T : ℕ → ℂ := fun m => ∑ k ∈ Finset.range m, b k * z k
  have hz (m : ℕ) : ‖z m‖ = 1 := Complex.norm_exp_I_mul_ofReal _
  have hzstep (m : ℕ) : z (m + 1) = z m * z₁ := by
    dsimp only [z, z₁]
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hstep (m : ℕ) : ‖z m - z (m + 1)‖ ≤ |a| := by
    rw [norm_sub_rev, hzstep, show z m * z₁ - z m = z m * (z₁ - 1) by ring,
      norm_mul, hz, one_mul]
    simpa only [z₁, Real.norm_eq_abs] using (Real.norm_exp_I_mul_ofReal_sub_one_le (x := a))
  have herror : ∀ m ≤ N, ‖T m - P m * z m‖ ≤ (m : ℝ) * E * |a| := by
    intro m
    induction m with
    | zero => simp [P, T]
    | succ m ih =>
      intro hm
      have hsplit : T (m + 1) - P (m + 1) * z (m + 1) =
          (T m - P m * z m) + P (m + 1) * (z m - z (m + 1)) := by
        have hT : T (m + 1) = T m + b m * z m := by
          simp only [T, Finset.sum_range_succ]
        have hP : P (m + 1) = P m + b m := by
          simp only [P, Finset.sum_range_succ]
        rw [hT, hP]
        ring
      rw [hsplit]
      calc
        _ ≤ ‖T m - P m * z m‖ + ‖P (m + 1) * (z m - z (m + 1))‖ := norm_add_le _ _
        _ ≤ (m : ℝ) * E * |a| + E * |a| := by
          rw [norm_mul]
          exact add_le_add (ih (Nat.le_of_succ_le hm))
            (mul_le_mul (hprefix (m + 1) hm) (hstep m) (norm_nonneg _) hE)
        _ = ((m + 1 : ℕ) : ℝ) * E * |a| := by push_cast; ring
  have ha : |a| = 2 * Real.pi * |θ| := by
    dsimp only [a]
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * Real.pi)]
  change ‖T N‖ ≤ _
  calc
    ‖T N‖ = ‖(T N - P N * z N) + P N * z N‖ := by rw [sub_add_cancel]
    _ ≤ ‖T N - P N * z N‖ + ‖P N * z N‖ := norm_add_le _ _
    _ ≤ (N : ℝ) * E * |a| + E := by
      rw [norm_mul, hz, mul_one]
      exact add_le_add (herror N le_rfl) (hprefix N le_rfl)
    _ = E * (1 + 2 * Real.pi * (N : ℝ) * |θ|) := by rw [ha]; ring
