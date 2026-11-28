import Mathlib
import PEqualNP.Outside.L_goldbach_power_index_count

/-!
# Cut `L-goldbach-cut-dc6324ac04f6b983d18396d1`

Up to any `N`, there are at most `(⌊√N⌋+1)(⌊log₂ N⌋+1)` distinct proper prime
powers.

Adapted from `PEqualNP.Outside.L_goldbach_power_index_count` (accepted lemma
L-goldbach-power-index-count), which counts the same set with the predicate
`ArithmeticFunction.vonMangoldt k ≠ 0`; that predicate is equivalent to
`IsPrimePow k` by `ArithmeticFunction.vonMangoldt_ne_zero_iff`.
-/

theorem Conjectures.Cuts.Taskdc6324ac04f6b983d18396d1 :
    ∀ (x1 : ℕ), {x2 ∈ Finset.range (x1 + (1 : ℕ)) | IsPrimePow x2 ∧ ¬Nat.Prime x2}.card ≤ (x1.sqrt + (1 : ℕ)) * (Nat.log (2 : ℕ) x1 + (1 : ℕ)) := by
  intro x1
  have h := PEqualNP.Outside.L_goldbach_power_index_count x1
  dsimp only at h
  have hset : {x2 ∈ Finset.range (x1 + 1) | IsPrimePow x2 ∧ ¬Nat.Prime x2} =
      (Finset.range (x1 + 1)).filter
        (fun k => ArithmeticFunction.vonMangoldt k ≠ 0 ∧ ¬Nat.Prime k) := by
    ext k
    simp only [Finset.mem_filter, ArithmeticFunction.vonMangoldt_ne_zero_iff]
  rw [hset]
  exact h
