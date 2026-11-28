import Mathlib
import Conjectures.Goldbach.RoughFifthBridge

/-- The cut uses the same candidate set and sign identity as `RoughFifthBridge`.
    Naming the filtered set once makes the three counts refer to the same set. -/
theorem Conjectures.Cuts.Task45089052fcc011deb39a08ad :
    ∀ N : ℕ,
    let C := (Finset.range N).filter (fun p =>
      Nat.Prime p ∧ N < 3 * p ∧ 3 * p < 2 * N ∧ 1 < N - p ∧ N < (N - p).minFac ^ 5)
    2 * (((C.filter (fun p => Nat.Prime (N - p))).card : ℝ)) =
      (C.card : ℝ) - C.sum (fun p => (ArithmeticFunction.liouville (N - p) : ℝ)) -
      2 * (((C.filter (fun p => ArithmeticFunction.cardFactors (N - p) = 3)).card : ℝ)) := by
  intro N
  exact Conjectures.Goldbach.RoughFifthBridge N
