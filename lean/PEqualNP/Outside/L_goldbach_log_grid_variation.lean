import Mathlib

theorem L_goldbach_log_grid_variation :
    ∀ n : ℕ, 1 ≤ n →
      (∑ k ∈ Finset.range n, |Real.log ((k+1:ℕ):ℝ) - Real.log (k:ℝ)|) = Real.log (n:ℝ) := by
  intro n hn
  have hterm : ∀ k ∈ Finset.range n,
      |Real.log ((k+1:ℕ):ℝ) - Real.log (k:ℝ)| = Real.log ((k+1:ℕ):ℝ) - Real.log (k:ℝ) := by
    intro k hk
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · subst hk0
      simp [Real.log_one, Real.log_zero]
    · apply abs_of_nonneg
      apply sub_nonneg.mpr
      have hkR : (0:ℝ) < (k:ℝ) := by exact_mod_cast hkpos
      have hle : (k:ℝ) ≤ ((k+1:ℕ):ℝ) := by push_cast; linarith
      exact Real.log_le_log hkR hle
  rw [Finset.sum_congr rfl hterm]
  have htel := Finset.sum_range_sub (fun k : ℕ => Real.log (k:ℝ)) n
  simpa [Real.log_zero] using htel
