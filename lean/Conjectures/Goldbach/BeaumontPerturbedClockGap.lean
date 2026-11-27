import Mathlib

open scoped BigOperators

theorem Conjectures.Goldbach.BeaumontPerturbedClockGap :
    ∀ (n : ℕ) (s : ℤ) (x : ℝ), |x-(s:ℝ)| < 1/2 → |x-(n:ℝ)| ≤ 1/2 → s=(n:ℤ) := by
  intro n s x hx hxn
  have h3 : |(s : ℝ) - (n : ℝ)| < 1 := by
    have h := abs_add_le ((s : ℝ) - x) (x - (n : ℝ))
    have h' : |(s : ℝ) - (n : ℝ)| ≤ |(s : ℝ) - x| + |x - (n : ℝ)| := by
      simpa only [sub_add_sub_cancel] using h
    have hx' : |(s : ℝ) - x| < 1 / 2 := by
      rwa [abs_sub_comm]
    linarith
  have h4 : |(((s - (n : ℤ)) : ℤ) : ℝ)| < 1 := by
    have hcast : (((s - (n : ℤ)) : ℤ) : ℝ) = (s : ℝ) - (n : ℝ) := by
      push_cast
      ring
    rwa [hcast]
  have h5 : s - (n : ℤ) = 0 := by
    rw [← Int.cast_abs, ← Int.cast_one, Int.cast_lt, Int.abs_lt_one_iff] at h4
    exact h4
  omega
