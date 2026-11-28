import Mathlib

/-!
Frequency-perturbation transfer via Abel summation (summation by parts):
any uniform bound on all prefix trigonometric sums at frequency `α` transfers to
`α + e` with multiplicative loss at most `1 + 2 * π * N * |e|`.
-/

namespace Conjectures.Cuts.Taskedf57c34465900af937f8755_aux

private noncomputable def prefSum (f : ℕ → ℝ) (n : ℕ) (θ : ℝ) : ℂ :=
  ∑ j ∈ Finset.range n, (f j : ℂ) * Complex.exp (((2 : ℝ) * Real.pi * (j : ℝ) * θ : ℝ) * Complex.I)

private noncomputable def phase (x : ℝ) : ℂ :=
  Complex.exp (((2 : ℝ) * Real.pi * x : ℝ) * Complex.I)

private lemma phase_add (x y : ℝ) : phase (x + y) = phase x * phase y := by
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private lemma norm_phase (x : ℝ) : ‖phase x‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

private lemma phase_step (j : ℕ) (e : ℝ) :
    ‖phase ((j : ℝ) * e) - phase (((j + 1 : ℕ) : ℝ) * e)‖ ≤ 2 * Real.pi * |e| := by
  have shift : ((j + 1 : ℕ) : ℝ) * e = (j : ℝ) * e + e := by push_cast; ring
  rw [norm_sub_rev, shift, phase_add, ← mul_sub_one, norm_mul, norm_phase, one_mul]
  unfold phase
  rw [mul_comm _ Complex.I]
  calc
    ‖Complex.exp (Complex.I * (((2 : ℝ) * Real.pi * e : ℝ) : ℂ)) - 1‖
        ≤ ‖2 * Real.pi * e‖ := Real.norm_exp_I_mul_ofReal_sub_one_le
    _ = 2 * Real.pi * |e| := by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]

private lemma sum_by_parts (g w : ℕ → ℂ) (hg0 : g 0 = 0) :
    ∀ n : ℕ, ∑ j ∈ Finset.range (n + 1), (g (j + 1) - g j) * w j =
      g (n + 1) * w n + ∑ j ∈ Finset.range n, g (j + 1) * (w j - w (j + 1))
  | 0 => by simp [hg0]
  | n + 1 => by
      rw [Finset.sum_range_succ, sum_by_parts g w hg0 n, Finset.sum_range_succ]
      ring

theorem transfer_bound (f : ℕ → ℝ) (N : ℕ) (α e M : ℝ) (hM : 0 ≤ M)
    (hpref : ∀ k ≤ N, ‖prefSum f k α‖ ≤ M) :
    ‖prefSum f N (α + e)‖ ≤ ((1 : ℝ) + (2 : ℝ) * Real.pi * (N : ℝ) * |e|) * M := by
  cases N with
  | zero =>
      simp [prefSum, hM]
  | succ n =>
      let g : ℕ → ℂ := fun k => prefSum f k α
      let w : ℕ → ℂ := fun j => phase ((j : ℝ) * e)
      have hg0 : g 0 = 0 := by simp [g, prefSum]
      have hterm : ∀ j : ℕ,
          (f j : ℂ) * Complex.exp (((2 : ℝ) * Real.pi * (j : ℝ) * (α + e) : ℝ) * Complex.I) =
            (g (j + 1) - g j) * w j := by
        intro j
        have hdiff : g (j + 1) - g j =
            (f j : ℂ) * Complex.exp (((2 : ℝ) * Real.pi * (j : ℝ) * α : ℝ) * Complex.I) := by
          simp [g, prefSum, Finset.sum_range_succ]
        rw [hdiff]
        have hexp :
            Complex.exp (((2 : ℝ) * Real.pi * (j : ℝ) * (α + e) : ℝ) * Complex.I) =
              Complex.exp (((2 : ℝ) * Real.pi * (j : ℝ) * α : ℝ) * Complex.I) * w j := by
          unfold w phase
          rw [← Complex.exp_add]
          congr 1
          push_cast
          ring
        rw [hexp]
        ring
      have hsum : prefSum f (n + 1) (α + e) =
          g (n + 1) * w n + ∑ j ∈ Finset.range n, g (j + 1) * (w j - w (j + 1)) := by
        unfold prefSum
        simp_rw [hterm]
        exact sum_by_parts g w hg0 n
      rw [hsum]
      have h1 : ‖g (n + 1) * w n‖ ≤ M := by
        rw [norm_mul]
        have hw : ‖w n‖ = 1 := norm_phase _
        rw [hw, mul_one]
        exact hpref (n + 1) (le_refl _)
      have h2 : ‖∑ j ∈ Finset.range n, g (j + 1) * (w j - w (j + 1))‖ ≤
          ((n : ℝ) * (2 * Real.pi * |e|)) * M := by
        calc
          ‖∑ j ∈ Finset.range n, g (j + 1) * (w j - w (j + 1))‖
              ≤ ∑ j ∈ Finset.range n, ‖g (j + 1) * (w j - w (j + 1))‖ := norm_sum_le _ _
          _ ≤ ∑ _j ∈ Finset.range n, M * (2 * Real.pi * |e|) := by
              refine Finset.sum_le_sum fun j hj => ?_
              have hj_lt : j < n := Finset.mem_range.mp hj
              rw [norm_mul]
              exact mul_le_mul (hpref (j + 1) (by omega)) (phase_step j e)
                (norm_nonneg _) hM
          _ = ((n : ℝ) * (2 * Real.pi * |e|)) * M := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
              ring
      have hn : ((n : ℝ) * (2 * Real.pi * |e|)) * M ≤
          (((n + 1 : ℕ) : ℝ) * (2 * Real.pi * |e|)) * M := by
        refine mul_le_mul_of_nonneg_right ?_ hM
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        push_cast
        linarith
      calc
        ‖g (n + 1) * w n + ∑ j ∈ Finset.range n, g (j + 1) * (w j - w (j + 1))‖
            ≤ ‖g (n + 1) * w n‖ + ‖∑ j ∈ Finset.range n, g (j + 1) * (w j - w (j + 1))‖ :=
          norm_add_le _ _
        _ ≤ M + ((n : ℝ) * (2 * Real.pi * |e|)) * M := add_le_add h1 h2
        _ ≤ M + (((n + 1 : ℕ) : ℝ) * (2 * Real.pi * |e|)) * M := by linarith only [hn]
        _ = ((1 : ℝ) + (2 : ℝ) * Real.pi * ((n + 1 : ℕ) : ℝ) * |e|) * M := by ring

end Conjectures.Cuts.Taskedf57c34465900af937f8755_aux

theorem Conjectures.Cuts.Taskedf57c34465900af937f8755 : (have x1 : (ℕ → ℝ) → ℕ → ℝ → ℂ := fun (x1 : ℕ → ℝ) (x2 : ℕ) (x3 : ℝ) => ∑ x4 ∈ Finset.range x2, ↑(x1 x4) * Complex.exp (↑((2 : ℝ) * Real.pi * ↑x4 * x3) * Complex.I); ∀ (x2 : ℕ → ℝ) (x3 : ℕ) (x4 x5 x6 : ℝ), (0 : ℝ) ≤ x6 → (∀ x8 ≤ x3, ‖x1 x2 x8 x4‖ ≤ x6) → ‖x1 x2 x3 (x4 + x5)‖ ≤ ((1 : ℝ) + (2 : ℝ) * Real.pi * ↑x3 * |x5|) * x6) := by
  exact Conjectures.Cuts.Taskedf57c34465900af937f8755_aux.transfer_bound
