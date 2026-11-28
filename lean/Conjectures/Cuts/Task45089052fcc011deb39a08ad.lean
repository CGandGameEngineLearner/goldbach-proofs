import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Liouville
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

open ArithmeticFunction
open scoped BigOperators

/-- Count the negative Liouville signs on the fifth-rough support by the
number of prime factors of the complement. -/
theorem Conjectures.Cuts.Task45089052fcc011deb39a08ad : (∀ (x1 : ℕ), (2 : ℝ) * ↑{x2 ∈ {x2 ∈ Finset.range x1 | Nat.Prime x2 ∧ x1 < (3 : ℕ) * x2 ∧ (3 : ℕ) * x2 < (2 : ℕ) * x1 ∧ (1 : ℕ) < x1 - x2 ∧ x1 < (x1 - x2).minFac ^ (5 : ℕ)} | Nat.Prime (x1 - x2)}.card = ↑{x2 ∈ Finset.range x1 | Nat.Prime x2 ∧ x1 < (3 : ℕ) * x2 ∧ (3 : ℕ) * x2 < (2 : ℕ) * x1 ∧ (1 : ℕ) < x1 - x2 ∧ x1 < (x1 - x2).minFac ^ (5 : ℕ)}.card - ∑ x2 ∈ Finset.range x1 with Nat.Prime x2 ∧ x1 < (3 : ℕ) * x2 ∧ (3 : ℕ) * x2 < (2 : ℕ) * x1 ∧ (1 : ℕ) < x1 - x2 ∧ x1 < (x1 - x2).minFac ^ (5 : ℕ), ↑(ArithmeticFunction.liouville (x1 - x2)) - (2 : ℝ) * ↑{x2 ∈ {x2 ∈ Finset.range x1 | Nat.Prime x2 ∧ x1 < (3 : ℕ) * x2 ∧ (3 : ℕ) * x2 < (2 : ℕ) * x1 ∧ (1 : ℕ) < x1 - x2 ∧ x1 < (x1 - x2).minFac ^ (5 : ℕ)} | ArithmeticFunction.cardFactors (x1 - x2) = (3 : ℕ)}.card) := by
  dsimp only
  intro N
  let C := (Finset.range N).filter (fun p => p.Prime ∧ N < 3*p ∧ 3*p < 2*N ∧
    1 < N-p ∧ N < (N-p).minFac^5)
  change 2 * ((C.filter (fun p => (N-p).Prime)).card : ℝ) =
    (C.card : ℝ) - (∑ p ∈ C, (liouville (N-p) : ℝ)) -
      2 * ((C.filter (fun p => cardFactors (N-p) = 3)).card : ℝ)
  have point (p : ℕ) (hp : p ∈ C) :
      2 * (if (N-p).Prime then 1 else 0 : ℝ) =
        1 - (liouville (N-p) : ℝ) - 2 * (if cardFactors (N-p) = 3 then 1 else 0) := by
    obtain ⟨_, _, _, _, large, rough⟩ := Finset.mem_filter.mp hp
    let m := N-p
    change 1 < m at large
    change N < m.minFac^5 at rough
    have nonzero : m ≠ 0 := by omega
    have lower : 0 < cardFactors m := cardFactors_pos_iff_one_lt.mpr large
    have lengthBound : m.minFac ^ cardFactors m ≤ m := by
      have productBound := List.pow_length_le_prod m.primeFactorsList m.minFac
        (fun q hq => Nat.minFac_le_of_dvd (Nat.prime_of_mem_primeFactorsList hq).two_le
          (Nat.dvd_of_mem_primeFactorsList hq))
      simpa only [cardFactors_apply, Nat.prod_primeFactorsList nonzero] using productBound
    have upper : cardFactors m ≤ 4 := by
      by_contra h
      have minPos : 1 ≤ m.minFac := Nat.minFac_pos m
      have powBound := pow_le_pow_right' minPos (show 5 ≤ cardFactors m by omega)
      exact (not_le_of_gt rough) (powBound.trans (lengthBound.trans (Nat.sub_le N p)))
    change 2 * (if m.Prime then 1 else 0 : ℝ) =
      1 - (liouville m : ℝ) - 2 * (if cardFactors m = 3 then 1 else 0)
    rw [← cardFactors_eq_one_iff_prime, liouville_apply nonzero]
    have small : cardFactors m = 1 ∨ cardFactors m = 2 ∨
        cardFactors m = 3 ∨ cardFactors m = 4 := by omega
    rcases small with h | h | h | h <;> norm_num [h]
  rw [Finset.natCast_card_filter, Finset.natCast_card_filter]
  simp only [Finset.mul_sum]
  calc
    _ = ∑ p ∈ C, (1 - (liouville (N-p) : ℝ) -
        2 * (if cardFactors (N-p) = 3 then 1 else 0)) :=
      Finset.sum_congr rfl point
    _ = _ := by simp [Finset.sum_sub_distrib]
