import Mathlib
import Conjectures.Cuts.Cutdde1e7ef243203eb1faa06c9
import Conjectures.Cuts.Cut03339a0be313d26b7b5c614e
import Conjectures.Cuts.Task8f9f08650abf4d04bfa7122e
import Conjectures.Cuts.Taskabc64269ad130e923b36a98e
import Conjectures.Cuts.Task8a8d36a7e422aebee73cae54
import Conjectures.Cuts.Taskfe7ba8275bd444832d5c353b
import Conjectures.Cuts.Task866d1277a2f1dde02f2029e1
import Conjectures.Cuts.Tasked4086932a43867e5cb19d77

theorem Conjectures.Goldbach.MertensSmallRangeCert :
    (let M0 : ℝ := Real.eulerMascheroniConstant + ∑' p : Nat.Primes, (Real.log (1 - 1 / (p.1 : ℝ)) + 1 / (p.1 : ℝ)); (0.261497 ≤ M0 ∧ M0 ≤ 0.261498) ∧ ∀ x : ℝ, 2 ≤ x → x ≤ Real.exp 10 → Real.log (Real.log x) + M0 - (2.964e-6 : ℝ) / Real.log x ≤ (∑ p ∈ (Finset.range (Nat.ceil x)).filter Nat.Prime, (1 : ℝ) / (p : ℝ)) ∧ (∑ p ∈ (Finset.range (Nat.ceil x)).filter Nat.Prime, (1 : ℝ) / (p : ℝ)) ≤ Real.log (Real.log x) + M0 + (if Real.log x > 8.9 then (1.614e-3 : ℝ) else (1 : ℝ))) :=
  Conjectures.Cuts.Cutdde1e7ef243203eb1faa06c9
    (Conjectures.Cuts.Cut03339a0be313d26b7b5c614e
      Conjectures.Cuts.Task8a8d36a7e422aebee73cae54
      Conjectures.Cuts.Taskfe7ba8275bd444832d5c353b
      Conjectures.Cuts.Task866d1277a2f1dde02f2029e1
      Conjectures.Cuts.Tasked4086932a43867e5cb19d77)
    Conjectures.Cuts.Task8f9f08650abf4d04bfa7122e
    Conjectures.Cuts.Taskabc64269ad130e923b36a98e
