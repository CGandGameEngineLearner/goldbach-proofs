import Mathlib

theorem Conjectures.Cuts.Taskad0851702797dad16ccbb0f5 : (∃ (x1 : ℕ),   ∀ (x2 : ℕ),     x1 ≤ x2 →       have x4 : ℕ := (2 : ℕ) ^ x2;       ∀ (x5 : ℕ), x4 ≤ (3 : ℕ) * x5 → (3 : ℕ) * x5 ≤ (2 : ℕ) * x4 → Nat.Prime x5 → Nat.Prime (x4 - x5) → Real.log ↑x4 ^ (2 : ℕ) / (4 : ℝ) ≤ (if Nat.Prime x5 then Real.log ↑x5 else (0 : ℝ)) * if Nat.Prime (x4 - x5) then Real.log ↑(x4 - x5) else (0 : ℝ)) := by
  refine ⟨4, ?_⟩
  intro k hk p hpL hpU hp hq
  dsimp
  simp only [if_pos hp, if_pos hq]
  let n : ℕ := 2 ^ k
  have hk4 : 4 ≤ k := hk
  have hn16 : 16 ≤ n := by
    dsimp [n]
    exact Nat.pow_le_pow_right (by decide : 1 < 2) (by omega)
  have hnpos : 0 < n := by omega
  have hnp : 0 < n - p := by
    have : p < n := by
      have hp' : 3 * p ≤ 2 * n := hpU
      omega
    omega
  have hlogn : 0 < Real.log (n : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < n by omega)
  have hlog3 : Real.log (3 : ℝ) ≤ Real.log (4 : ℝ) := by
    exact Real.strictMonoOn_log.monotoneOn (by norm_num) (by norm_num) (by norm_num)
  have hlog16 : Real.log (16 : ℝ) = 2 * Real.log (4 : ℝ) := by
    rw [show (16 : ℝ) = 4 * 4 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    ring
  have hlog16n : Real.log (16 : ℝ) ≤ Real.log (n : ℝ) := by
    apply Real.strictMonoOn_log.monotoneOn (by norm_num) (by positivity)
    exact_mod_cast hn16
  have hlog3half : Real.log (3 : ℝ) ≤ Real.log (n : ℝ) / 2 := by
    nlinarith [hlog3, hlog16, hlog16n]
  have hlogp : Real.log (n : ℝ) / 2 ≤ Real.log (p : ℝ) := by
    have hnp3 : (n : ℝ) / 3 ≤ (p : ℝ) := by
      exact_mod_cast (show n ≤ 3 * p by omega)
    have hlog := Real.strictMonoOn_log.monotoneOn (by positivity : 0 < (n : ℝ) / 3)
      (by exact_mod_cast hp.pos) hnp3
    rw [Real.log_div (by positivity) (by norm_num : (3 : ℝ) ≠ 0)] at hlog
    nlinarith [hlog3half]
  have hlogq : Real.log (n : ℝ) / 2 ≤ Real.log (n - p : ℝ) := by
    have hnq3 : (n : ℝ) / 3 ≤ (n - p : ℝ) := by
      exact_mod_cast (show n ≤ 3 * (n - p) by omega)
    have hlog := Real.strictMonoOn_log.monotoneOn (by positivity : 0 < (n : ℝ) / 3)
      (by exact_mod_cast hnp) hnq3
    rw [Real.log_div (by positivity) (by norm_num : (3 : ℝ) ≠ 0)] at hlog
    nlinarith [hlog3half]
  have hprod : 0 ≤ (Real.log (p : ℝ) - Real.log (n : ℝ) / 2) *
      (Real.log (n - p : ℝ) - Real.log (n : ℝ) / 2) :=
    mul_nonneg (sub_nonneg.mpr hlogp) (sub_nonneg.mpr hlogq)
  nlinarith [hprod]
