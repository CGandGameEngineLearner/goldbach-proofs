import Mathlib
import Conjectures.TwinPrimes.SharpWindowContamination

theorem Conjectures.Cuts.Taskdee6cda672ba6d699cb13a19 : (∀ (x1 : ℕ), (1 : ℕ) ≤ x1 → (0 : ℝ) < √((2 : ℝ) * ↑x1) * Real.log ((2 : ℝ) + (2 : ℝ) * ↑x1)) := by
  intro n hn
  have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  apply mul_pos
  · exact Real.sqrt_pos.mpr (by linarith)
  · exact Real.log_pos (by linarith)
