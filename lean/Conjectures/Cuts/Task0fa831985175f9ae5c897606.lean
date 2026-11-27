import Mathlib

namespace Conjectures.Cuts.Task0fa831985175f9ae5c897606_aux

/-- `1 ≤ log 3`, from the numeric bound `Real.log_three_gt_d9`. -/
lemma one_le_log_three : (1 : ℝ) ≤ Real.log 3 := by
  linarith [Real.log_three_gt_d9]

/-- For `n ≥ 3`, `log n ≥ 1`. -/
lemma one_le_log_of_three_le {n : ℕ} (hn : 3 ≤ n) : (1 : ℝ) ≤ Real.log (n : ℝ) := by
  have hn3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h0 : (0 : ℝ) < (n : ℝ) := by linarith
  have h := Real.log_le_log (by norm_num) hn3
  linarith [one_le_log_three]

/-- Counting is dominated by any pointwise-`≥ 1` weight on the selected points. -/
lemma card_le_sum_ite {s : Finset ℕ} {p : ℕ → Prop} [DecidablePred p] {f : ℕ → ℝ}
    (h : ∀ x ∈ s, p x → 1 ≤ f x) :
    ((s.filter p).card : ℝ) ≤ ∑ x ∈ s, if p x then f x else 0 := by
  rw [Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_le_sum fun x hx => ?_
  split_ifs with hp
  · exact h x hx hp
  · simp

end Conjectures.Cuts.Task0fa831985175f9ae5c897606_aux

open Conjectures.Cuts.Task0fa831985175f9ae5c897606_aux

/-- Count at most mass: inside the strict window every twin prime pair starts at `n ≥ 3`,
so `log n ≥ 1` and `log (n+2) ≥ 1`, and each counted pair contributes at least `1` to the
log-weighted mass. -/
theorem Conjectures.Cuts.Task0fa831985175f9ae5c897606 :
    ∀ (x1 : ℕ), ↑{x2 ∈ Finset.range ((2 : ℕ) * x1 + (1 : ℕ)) | x1 < x2 ∧ (50 : ℕ) * x2 < (51 : ℕ) * x1 ∧ Nat.Prime x2 ∧ Nat.Prime (x2 + (2 : ℕ))}.card ≤ ∑ x2 ∈ Finset.range ((2 : ℕ) * x1 + (1 : ℕ)), if x1 < x2 ∧ (50 : ℕ) * x2 < (51 : ℕ) * x1 ∧ Nat.Prime x2 ∧ Nat.Prime (x2 + (2 : ℕ)) then Real.log ↑x2 * Real.log ↑(x2 + (2 : ℕ)) else (0 : ℝ) := by
  intro x1
  refine card_le_sum_ite (f := fun x2 : ℕ => Real.log (x2 : ℝ) * Real.log ((x2 + 2 : ℕ) : ℝ)) ?_
  intro x2 _ hx
  have hp : Nat.Prime x2 := hx.2.2.1
  have hp2 : Nat.Prime (x2 + 2) := hx.2.2.2
  have h2 : 2 ≤ x2 := hp.two_le
  have hne : x2 ≠ 2 := by
    intro h
    have : x2 + 2 = 4 := by omega
    rw [this] at hp2
    exact (by decide : ¬ Nat.Prime 4) hp2
  have h3 : 3 ≤ x2 := by omega
  have h5 : 3 ≤ x2 + 2 := by omega
  have hlog1 : (1 : ℝ) ≤ Real.log (x2 : ℝ) := one_le_log_of_three_le h3
  have hlog2 : (1 : ℝ) ≤ Real.log ((x2 + 2 : ℕ) : ℝ) := one_le_log_of_three_le h5
  nlinarith
