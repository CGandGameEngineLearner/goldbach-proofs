import Mathlib

theorem Conjectures.Cuts.Taskad0851702797dad16ccbb0f5 : (∃ (x1 : ℕ),   ∀ (x2 : ℕ),     x1 ≤ x2 →       have x4 : ℕ := (2 : ℕ) ^ x2;       ∀ (x5 : ℕ), x4 ≤ (3 : ℕ) * x5 → (3 : ℕ) * x5 ≤ (2 : ℕ) * x4 → Nat.Prime x5 → Nat.Prime (x4 - x5) → Real.log ↑x4 ^ (2 : ℕ) / (4 : ℝ) ≤ (if Nat.Prime x5 then Real.log ↑x5 else (0 : ℝ)) * if Nat.Prime (x4 - x5) then Real.log ↑(x4 - x5) else (0 : ℝ)) := by
  refine ⟨4, ?_⟩
  intro k hk
  dsimp only
  intro p hp₁ hp₂ hp hq
  let n : ℕ := 2 ^ k
  change n ≤ 3 * p at hp₁
  change 3 * p ≤ 2 * n at hp₂
  change Nat.Prime (n - p) at hq
  change Real.log (n : ℝ) ^ 2 / 4 ≤
    (if Nat.Prime p then Real.log (p : ℝ) else 0) *
      (if Nat.Prime (n - p) then Real.log ((n - p : ℕ) : ℝ) else 0)
  have hn : 16 ≤ n := calc
    16 = (2 : ℕ) ^ 4 := by norm_num
    _ ≤ n := pow_le_pow_right₀ (by decide : (1 : ℕ) ≤ 2) hk
  have hlog (x : ℕ) (hx : n ≤ 3 * x) : Real.log (n : ℝ) / 2 ≤ Real.log (x : ℝ) := by
    have hx₃ : 3 ≤ x := by omega
    have hsq : n ≤ x ^ 2 := hx.trans (by
      rw [pow_two]
      exact Nat.mul_le_mul_right x hx₃)
    have hpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hh := Real.log_le_log hpos (by exact_mod_cast hsq : (n : ℝ) ≤ (x : ℝ) ^ 2)
    rw [Real.log_pow] at hh
    norm_num at hh
    linarith
  have hq₁ : n ≤ 3 * (n - p) := by omega
  have hL₀ : 0 ≤ Real.log (n : ℝ) / 2 := by
    exact div_nonneg (Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))) (by norm_num)
  have hpL := hlog p hp₁
  have hqL := hlog (n - p) hq₁
  simp only [if_pos hp, if_pos hq]
  calc
    Real.log (n : ℝ) ^ 2 / 4 = (Real.log (n : ℝ) / 2) * (Real.log (n : ℝ) / 2) := by ring
    _ ≤ Real.log (p : ℝ) * Real.log ((n - p : ℕ) : ℝ) :=
      mul_le_mul hpL hqL hL₀ (hL₀.trans hpL)
