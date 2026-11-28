import Mathlib

theorem Conjectures.Cuts.Taskad0851702797dad16ccbb0f5 : (∃ (x1 : ℕ),   ∀ (x2 : ℕ),     x1 ≤ x2 →       have x4 : ℕ := (2 : ℕ) ^ x2;       ∀ (x5 : ℕ), x4 ≤ (3 : ℕ) * x5 → (3 : ℕ) * x5 ≤ (2 : ℕ) * x4 → Nat.Prime x5 → Nat.Prime (x4 - x5) → Real.log ↑x4 ^ (2 : ℕ) / (4 : ℝ) ≤ (if Nat.Prime x5 then Real.log ↑x5 else (0 : ℝ)) * if Nat.Prime (x4 - x5) then Real.log ↑(x4 - x5) else (0 : ℝ)) := by
  refine ⟨4, ?_⟩
  intro k hk
  let n : ℕ := 2 ^ k
  change ∀ p : ℕ, n ≤ 3 * p → 3 * p ≤ 2 * n → Nat.Prime p → Nat.Prime (n-p) → _
  intro p hp hq pp pq
  have hn : 16 ≤ n := by
    exact Nat.pow_le_pow_right (by decide : 0 < 2) hk
  have hp' : p ≤ n := by omega
  have hlow (u : ℕ) (hu : n ≤ 3*u) : Real.log (n : ℝ) / 2 ≤ Real.log (u : ℝ) := by
    have hu3 : 3 ≤ u := by omega
    have hn2 : n ≤ u^2 := by
      exact hu.trans (by simpa [pow_two] using Nat.mul_le_mul_right u hu3)
    have hl := Real.log_le_log (by positivity : (0 : ℝ) < n) (show (n : ℝ) ≤ (u : ℝ)^2 by exact_mod_cast hn2)
    rw [Real.log_pow] at hl
    exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2 (by simpa [mul_comm] using hl)
  have hleft := hlow p hp
  have hright := hlow (n-p) (by omega)
  have hlog : 0 ≤ Real.log (n : ℝ) / 2 := by
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    exact div_nonneg (Real.log_nonneg hn1) (by norm_num)
  change Real.log (n : ℝ)^2 / 4 ≤ (if Nat.Prime p then Real.log (p : ℝ) else 0) *
    (if Nat.Prime (n-p) then Real.log ((n-p : ℕ) : ℝ) else 0)
  simp only [if_pos pp, if_pos pq]
  nlinarith only [mul_le_mul hleft hright hlog (hlog.trans hleft)]
