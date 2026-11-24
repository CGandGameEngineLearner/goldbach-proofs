import Mathlib

theorem PEqualNP.Outside.L_goldbach_abel_total_variation :
    ∀ (N : ℕ) (A g : ℕ → ℂ) (e : ℝ), A 0=0 → (∀ k≤N, ‖A k‖≤e) → ‖Finset.sum (Finset.range N) (fun k => (A (k+1)-A k)*g k)‖ ≤ e*(‖g N‖+Finset.sum (Finset.range N) (fun k => ‖g (k+1)-g k‖)) := by
  intro N A g e hzero hbound
  have abel (m : ℕ) :
      ∑ k ∈ Finset.range m, (A (k+1) - A k) * g k =
        A m * g m - A 0 * g 0 - ∑ k ∈ Finset.range m, A (k+1) * (g (k+1) - g k) := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
      ring
  have endpoint : ‖A N * g N‖ ≤ e * ‖g N‖ := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hbound N le_rfl) (norm_nonneg _)
  rw [abel, hzero, zero_mul, sub_zero, mul_add, Finset.mul_sum]
  apply (norm_sub_le _ _).trans
  apply add_le_add endpoint
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro k hk
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hbound (k+1) (Finset.mem_range.mp hk)) (norm_nonneg _)
