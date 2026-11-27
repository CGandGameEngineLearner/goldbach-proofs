import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Sqrt
import Mathlib.Order.Interval.Finset.Nat

namespace Conjectures.Goldbach

theorem DynIncidenceFirst :
    let E := fun X : ℕ => (Finset.Icc X (2*X)).filter (fun n => Even n); let P := fun X : ℕ => (Finset.Icc (Nat.sqrt X) (2*Nat.sqrt X)).filter Nat.Prime; let H := fun (X n : ℕ) => ((P X).filter (fun p => p ≤ n ∧ Nat.Prime (n-p))).card; ∀ X : ℕ, ∑ n ∈ E X, H X n = ∑ p ∈ P X, ((E X).filter (fun n => p≤n ∧ Nat.Prime (n-p))).card := by
  dsimp only
  intro X
  let E := (Finset.Icc X (2*X)).filter Even
  let P := (Finset.Icc (Nat.sqrt X) (2*Nat.sqrt X)).filter Nat.Prime
  change (∑ n ∈ E, (P.filter (fun p => p ≤ n ∧ Nat.Prime (n-p))).card) =
    ∑ p ∈ P, (E.filter (fun n => p ≤ n ∧ Nat.Prime (n-p))).card
  let indicator := fun n p : ℕ => if p ≤ n ∧ Nat.Prime (n-p) then (1:ℕ) else 0
  calc
    _ = ∑ n ∈ E, ∑ p ∈ P, indicator n p := by
      apply Finset.sum_congr rfl
      intro n _
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    _ = ∑ p ∈ P, ∑ n ∈ E, indicator n p := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro p _
      symm
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]

end Conjectures.Goldbach
