import Mathlib

/-- Squared log of the left end times the twin-pair count is at most the log-weighted mass:
inside the window every counted pair starts at `x3 > x1 ≥ 3`, so `log x3 ≥ log x1` and
`log (x3+2) ≥ log x1`, and each counted pair contributes at least `(log x1)^2`. -/
theorem Conjectures.Cuts.Taskf66d06f7b29c0f33233b4b7a :
    ∀ (x1 : ℕ), (3 : ℕ) ≤ x1 → Real.log ↑x1 ^ (2 : ℕ) * ↑{x3 ∈ Finset.range ((2 : ℕ) * x1 + (1 : ℕ)) | x1 < x3 ∧ (50 : ℕ) * x3 < (51 : ℕ) * x1 ∧ Nat.Prime x3 ∧ Nat.Prime (x3 + (2 : ℕ))}.card ≤ ∑ x3 ∈ Finset.range ((2 : ℕ) * x1 + (1 : ℕ)), if x1 < x3 ∧ (50 : ℕ) * x3 < (51 : ℕ) * x1 ∧ Nat.Prime x3 ∧ Nat.Prime (x3 + (2 : ℕ)) then Real.log ↑x3 * Real.log ↑(x3 + (2 : ℕ)) else (0 : ℝ) := by
  intro x1 hx1
  have hx1pos : (0 : ℝ) < (x1 : ℝ) := by exact_mod_cast (show 0 < x1 by omega)
  have hlog0 : (0 : ℝ) ≤ Real.log (x1 : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ x1 by omega))
  have hcard : ((Finset.range ((2 : ℕ) * x1 + (1 : ℕ))).filter
      (fun x3 => x1 < x3 ∧ (50 : ℕ) * x3 < (51 : ℕ) * x1 ∧ Nat.Prime x3 ∧ Nat.Prime (x3 + (2 : ℕ)))).card
      = ∑ x3 ∈ Finset.range ((2 : ℕ) * x1 + (1 : ℕ)),
          if x1 < x3 ∧ (50 : ℕ) * x3 < (51 : ℕ) * x1 ∧ Nat.Prime x3 ∧ Nat.Prime (x3 + (2 : ℕ))
          then (1 : ℕ) else 0 := by
    rw [Finset.card_filter]
  have hcardR : (((Finset.range ((2 : ℕ) * x1 + (1 : ℕ))).filter
      (fun x3 => x1 < x3 ∧ (50 : ℕ) * x3 < (51 : ℕ) * x1 ∧ Nat.Prime x3 ∧ Nat.Prime (x3 + (2 : ℕ)))).card : ℝ)
      = ∑ x3 ∈ Finset.range ((2 : ℕ) * x1 + (1 : ℕ)),
          if x1 < x3 ∧ (50 : ℕ) * x3 < (51 : ℕ) * x1 ∧ Nat.Prime x3 ∧ Nat.Prime (x3 + (2 : ℕ))
          then (1 : ℝ) else 0 := by
    rw [hcard, Nat.cast_sum]
    refine Finset.sum_congr rfl fun x3 _ => ?_
    split_ifs <;> simp
  rw [hcardR, Finset.mul_sum]
  refine Finset.sum_le_sum fun x3 _ => ?_
  split_ifs with hp
  · have h1 : Real.log (x1 : ℝ) ≤ Real.log (x3 : ℝ) :=
      Real.log_le_log hx1pos (by exact_mod_cast (le_of_lt hp.1))
    have h2 : Real.log (x1 : ℝ) ≤ Real.log ((x3 + (2 : ℕ) : ℕ) : ℝ) :=
      Real.log_le_log hx1pos (by exact_mod_cast (show x1 ≤ x3 + 2 by omega))
    have hmul : Real.log (x1 : ℝ) * Real.log (x1 : ℝ) ≤
        Real.log (x3 : ℝ) * Real.log ((x3 + (2 : ℕ) : ℕ) : ℝ) :=
      mul_le_mul h1 h2 hlog0 (le_trans hlog0 h1)
    calc Real.log (x1 : ℝ) ^ (2 : ℕ) * (1 : ℝ)
        = Real.log (x1 : ℝ) * Real.log (x1 : ℝ) := by ring
      _ ≤ Real.log (x3 : ℝ) * Real.log ((x3 + (2 : ℕ) : ℕ) : ℝ) := hmul
  · simp
