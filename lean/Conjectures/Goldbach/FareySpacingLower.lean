import Mathlib

theorem Conjectures.Goldbach.FareySpacingLower :
    ∀ (Q a b q r : ℕ), 1 ≤ q → q ≤ Q → 1 ≤ r → r ≤ Q → Nat.Coprime a q → Nat.Coprime b r → (q ≠ r ∨ a % q ≠ b % r) → ∀ m : ℤ, 1 / (Q : ℝ) ^ 2 ≤ |(a : ℝ) / q - (b : ℝ) / r - (m : ℝ)| := by
  intro Q a b q r hq hqQ hr hrQ ha hb hdistinct m
  let d : ℤ := a * (r : ℤ) - b * (q : ℤ) - m * q * r
  have hd : d ≠ 0 := by
    intro heq
    change (a : ℤ) * r - b * q - m * q * r = 0 at heq
    have hqr : q ∣ a * r := by
      have : (q : ℤ) ∣ (a : ℤ) * r := ⟨b + m * r, by linarith only [heq]⟩
      exact_mod_cast this
    have hrq : r ∣ b * q := by
      have : (r : ℤ) ∣ (b : ℤ) * q := ⟨a - m * q, by linarith only [heq]⟩
      exact_mod_cast this
    have hsame := Nat.dvd_antisymm (ha.symm.dvd_of_dvd_mul_left hqr) (hb.symm.dvd_of_dvd_mul_left hrq)
    subst r
    have hqi : (q : ℤ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
    have he : ((a : ℤ) - b - m * q) * q = 0 := by linarith only [heq]
    have hab := (mul_eq_zero.mp he).resolve_right hqi
    have hmod : (a : ℤ) ≡ b [ZMOD (q : ℤ)] := Int.modEq_iff_dvd.mpr ⟨-m, by linarith only [hab]⟩
    exact hdistinct.elim (fun h => h rfl) (fun h => h (Int.natCast_modEq_iff.mp hmod))
  have hq' : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hr' : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hD : (1 : ℝ) ≤ |(d : ℝ)| := by exact_mod_cast (show (1 : ℤ) ≤ |d| by have := abs_pos.mpr hd; omega)
  have hden : (q : ℝ) * r ≤ (Q : ℝ) ^ 2 := by rw [sq]; exact_mod_cast Nat.mul_le_mul hqQ hrQ
  calc 1 / (Q : ℝ)^2 ≤ 1 / ((q : ℝ) * r) := one_div_le_one_div_of_le (mul_pos hq' hr') hden
    _ ≤ |(d : ℝ)| / ((q : ℝ) * r) := div_le_div_of_nonneg_right hD (mul_pos hq' hr').le
    _ = _ := by
      rw [← abs_of_pos (mul_pos hq' hr'), ← abs_div]
      congr 1
      dsimp [d]; push_cast; field_simp
