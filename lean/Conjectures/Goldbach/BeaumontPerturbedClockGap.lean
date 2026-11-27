import Mathlib

theorem Conjectures.Goldbach.BeaumontPerturbedClockGap :
  ∀ (n : ℕ) (s : ℤ) (x : ℝ), |x-(s:ℝ)| < 1/2 → |x-(n:ℝ)| ≤ 1/2 → s=(n:ℤ) := by
  intro n s x hs hn
  have hs' := abs_lt.mp hs
  have hn' := abs_le.mp hn
  by_contra h
  have hc : s ≤ (n:ℤ)-1 ∨ (n:ℤ)+1 ≤ s := by omega
  have hc' : (s:ℝ) ≤ (n:ℝ)-1 ∨ (n:ℝ)+1 ≤ (s:ℝ) := by exact_mod_cast hc
  rcases hc' with h | h <;> linarith [hs'.1, hs'.2, hn'.1, hn'.2]
