import Mathlib

theorem Conjectures.Goldbach.BeaumontPerturbedClockGap :
    ∀ (n : ℕ) (s : ℤ) (x : ℝ), |x-(s:ℝ)| < 1/2 → |x-(n:ℝ)| ≤ 1/2 → s=(n:ℤ) := by
  intro n s x hs hn
  obtain ⟨hs₁, hs₂⟩ := abs_lt.mp hs
  obtain ⟨hn₁, hn₂⟩ := abs_le.mp hn
  have h₁ : s < (n : ℤ) + 1 := by
    exact_mod_cast (show (s : ℝ) < (n : ℝ) + 1 by linarith)
  have h₂ : (n : ℤ) < s + 1 := by
    exact_mod_cast (show (n : ℝ) < (s : ℝ) + 1 by linarith)
  omega
