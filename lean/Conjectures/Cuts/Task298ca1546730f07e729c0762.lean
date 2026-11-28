import Mathlib
import Conjectures.Goldbach.MertensSmallRangeCert

theorem Conjectures.Cuts.Task298ca1546730f07e729c0762 : (0.261497 ≤ Real.eulerMascheroniConstant + ∑' (x1 : Nat.Primes), (Real.log ((1 : ℝ) - (1 : ℝ) / ↑↑x1) + (1 : ℝ) / ↑↑x1)) := by
  have h := Conjectures.Goldbach.MertensSmallRangeCert
  dsimp only at h
  exact h.1.1
