import Conjectures.Cuts.Cutdde1e7ef243203eb1faa06c9
import Conjectures.Cuts.Taskb182870585b8412c8aff946c
import Conjectures.Cuts.Task8f9f08650abf4d04bfa7122e
import Conjectures.Cuts.Taskabc64269ad130e923b36a98e

theorem Conjectures.Cuts.Taskcefe2059e65427cfde299eb2 :
have x1 : ℝ := Real.eulerMascheroniConstant + ∑' (x1 : Nat.Primes), (Real.log ((1 : ℝ) - (1 : ℝ) / (↑(↑x1 : ℕ) : ℝ)) + (1 : ℝ) / (↑(↑x1 : ℕ) : ℝ)); ∀ (x2 : ℝ), (2 : ℝ) ≤ x2 → x2 ≤ Real.exp (10 : ℝ) → Real.log (Real.log x2) + x1 - 2964e-9 / Real.log x2 ≤ ∑ x5 ∈ Finset.range ⌈x2⌉₊ with Nat.Prime x5, (1 : ℝ) / (↑x5 : ℝ) ∧ ∑ x5 ∈ Finset.range ⌈x2⌉₊ with Nat.Prime x5, (1 : ℝ) / (↑x5 : ℝ) ≤ Real.log (Real.log x2) + x1 + if Real.log x2 > 8.9 then 1614e-6 else (1 : ℝ) := by
  exact (Conjectures.Cuts.Cutdde1e7ef243203eb1faa06c9
    Conjectures.Cuts.Taskb182870585b8412c8aff946c
    Conjectures.Cuts.Task8f9f08650abf4d04bfa7122e
    Conjectures.Cuts.Taskabc64269ad130e923b36a98e).2
