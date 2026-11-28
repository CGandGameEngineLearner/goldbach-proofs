import Mathlib

theorem Conjectures.Cuts.Taskad0851702797dad16ccbb0f5 : (∃ (x1 : ℕ),   ∀ (x2 : ℕ),     x1 ≤ x2 →       have x4 : ℕ := (2 : ℕ) ^ x2;       ∀ (x5 : ℕ), x4 ≤ (3 : ℕ) * x5 → (3 : ℕ) * x5 ≤ (2 : ℕ) * x4 → Nat.Prime x5 → Nat.Prime (x4 - x5) → Real.log ↑x4 ^ (2 : ℕ) / (4 : ℝ) ≤ (if Nat.Prime x5 then Real.log ↑x5 else (0 : ℝ)) * if Nat.Prime (x4 - x5) then Real.log ↑(x4 - x5) else (0 : ℝ)) := by
  refine ⟨4, ?_⟩
  intro k hk
  dsimp only
  set n : ℕ := 2 ^ k
  intro p hpLower hpUpper hpPrime hqPrime
  have hn : 16 ≤ n := by
    change 16 ≤ (2 : ℕ) ^ k
    calc
      16 = (2 : ℕ) ^ 4 := by norm_num
      _ ≤ (2 : ℕ) ^ k := Nat.pow_le_pow_right (by decide) hk
  have halfLog (a : ℕ) (ha : n ≤ 3 * a) :
      Real.log (n : ℝ) / 2 ≤ Real.log (a : ℝ) := by
    have haThree : 3 ≤ a := by omega
    have haSquare : n ≤ a ^ 2 := by
      rw [pow_two]
      exact ha.trans (Nat.mul_le_mul_right a haThree)
    have hpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    have hbound : (n : ℝ) ≤ (a : ℝ) ^ 2 := by exact_mod_cast haSquare
    have hlog := Real.log_le_log hpos hbound
    rw [Real.log_pow] at hlog
    norm_num at hlog
    linarith only [hlog]
  have hp := halfLog p hpLower
  have hq : Real.log (n : ℝ) / 2 ≤ Real.log ((n - p : ℕ) : ℝ) :=
    halfLog (n - p) (by omega)
  have hnonneg : 0 ≤ Real.log (n : ℝ) / 2 :=
    div_nonneg (Real.log_natCast_nonneg n) (by norm_num)
  simp only [if_pos hpPrime, if_pos hqPrime]
  calc
    Real.log (n : ℝ) ^ 2 / 4 =
        (Real.log (n : ℝ) / 2) * (Real.log (n : ℝ) / 2) := by ring
    _ ≤ Real.log (p : ℝ) * Real.log ((n - p : ℕ) : ℝ) :=
      mul_le_mul hp hq hnonneg (hnonneg.trans hp)
