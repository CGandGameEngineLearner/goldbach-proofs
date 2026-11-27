import Mathlib

open scoped BigOperators

theorem Conjectures.Goldbach.FareySpacingLower :
    ∀ (Q a b q r : ℕ), 1 ≤ q → q ≤ Q → 1 ≤ r → r ≤ Q → Nat.Coprime a q →
      Nat.Coprime b r → (q ≠ r ∨ a % q ≠ b % r) → ∀ m : ℤ,
        1 / (Q : ℝ) ^ 2 ≤ |(a : ℝ) / q - (b : ℝ) / r - (m : ℝ)| := by
  intro Q a b q r hq1 hqQ hr1 hrQ haq hbr hne m
  set N : ℤ := (a : ℤ) * (r : ℤ) - (b : ℤ) * (q : ℤ) - m * (q : ℤ) * (r : ℤ) with hN
  have hqpos : 0 < q := Nat.lt_of_lt_of_le Nat.zero_lt_one hq1
  have hrpos : 0 < r := Nat.lt_of_lt_of_le Nat.zero_lt_one hr1
  have hq0 : (q : ℝ) ≠ 0 := by
    have : q ≠ 0 := ne_of_gt hqpos
    exact_mod_cast this
  have hr0 : (r : ℝ) ≠ 0 := by
    have : r ≠ 0 := ne_of_gt hrpos
    exact_mod_cast this
  have hqZ : (q : ℤ) ≠ 0 := by
    have : q ≠ 0 := ne_of_gt hqpos
    exact_mod_cast this
  -- Main claim: the integer N is nonzero.
  have hNne : N ≠ 0 := by
    intro hN0
    -- Cast to integers: a*r = b*q + m*q*r.
    have heq : (a : ℤ) * (r : ℤ) = (b : ℤ) * (q : ℤ) + m * (q : ℤ) * (r : ℤ) := by
      have h := hN
      rw [hN0] at h
      linarith
    -- q ∣ r
    have hq_dvd_Z : (q : ℤ) ∣ (a : ℤ) * (r : ℤ) := by
      refine ⟨(b : ℤ) + m * (r : ℤ), ?_⟩
      rw [heq]
      ring
    have hq_dvd : q ∣ a * r := by
      rw [← Int.natCast_dvd_natCast]
      push_cast
      exact hq_dvd_Z
    have hqr_dvd : q ∣ r := haq.symm.dvd_of_dvd_mul_left hq_dvd
    -- r ∣ q
    have hr_dvd_Z : (r : ℤ) ∣ (b : ℤ) * (q : ℤ) := by
      refine ⟨(a : ℤ) - m * (q : ℤ), ?_⟩
      have hbq : (b : ℤ) * (q : ℤ) = (a : ℤ) * (r : ℤ) - m * (q : ℤ) * (r : ℤ) := by
        linarith
      rw [hbq]
      ring
    have hr_dvd : r ∣ b * q := by
      rw [← Int.natCast_dvd_natCast]
      push_cast
      exact hr_dvd_Z
    have hrq_dvd : r ∣ q := hbr.symm.dvd_of_dvd_mul_left hr_dvd
    have hqr : q = r := Nat.dvd_antisymm hqr_dvd hrq_dvd
    -- Hence a*q = b*q + m*q*q, so a = b + m*q.
    have hqrZ : (q : ℤ) = (r : ℤ) := by exact_mod_cast hqr
    have heq' : (a : ℤ) * (q : ℤ) = (b : ℤ) * (q : ℤ) + m * (q : ℤ) * (q : ℤ) := by
      have h1 := heq
      rw [← hqrZ] at h1
      exact h1
    have hcancel : (a : ℤ) = (b : ℤ) + m * (q : ℤ) := by
      apply mul_right_cancel₀ hqZ
      show (a : ℤ) * (q : ℤ) = ((b : ℤ) + m * (q : ℤ)) * (q : ℤ)
      rw [heq']
      ring
    -- q ∣ b - a, so a ≡ b mod q
    have hdvd : (q : ℤ) ∣ (b : ℤ) - (a : ℤ) := by
      have h : (b : ℤ) - (a : ℤ) = -(m * (q : ℤ)) := by linarith
      rw [h]
      exact dvd_neg.mpr (dvd_mul_left (q : ℤ) m)
    have hmodeq : a ≡ b [MOD q] := Nat.modEq_iff_dvd.mpr hdvd
    have hab : a % q = b % r := by
      have h1 : a % q = b % q := hmodeq
      have h2 : b % q = b % r := by rw [hqr]
      rw [h1, h2]
    rcases hne with h | h
    · exact h hqr
    · exact h hab
  -- |N| ≥ 1
  have hNabs : (1 : ℝ) ≤ |(N : ℝ)| := by
    rw [← Int.cast_abs]
    have h : (1 : ℤ) ≤ |N| := by
      have hpos : (0 : ℤ) < |N| := abs_pos.mpr hNne
      omega
    exact_mod_cast h
  -- Rewrite the target quantity as N / (q * r).
  have hNcast : (N : ℝ)
      = (a : ℝ) * (r : ℝ) - (b : ℝ) * (q : ℝ) - (m : ℝ) * (q : ℝ) * (r : ℝ) := by
    rw [hN]
    push_cast
    ring
  have hqrpos : (0 : ℝ) < (q : ℝ) * (r : ℝ) := by positivity
  have hQ2pos : (0 : ℝ) < (Q : ℝ) ^ 2 := by
    have hQpos : 0 < Q := Nat.lt_of_lt_of_le hqpos hqQ
    have hQ' : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQpos
    positivity
  have hden_le : (q : ℝ) * (r : ℝ) ≤ (Q : ℝ) ^ 2 := by
    have hqR : (q : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hqQ
    have hrR : (r : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hrQ
    have hq0' : (0 : ℝ) ≤ (q : ℝ) := by positivity
    have hr0' : (0 : ℝ) ≤ (r : ℝ) := by positivity
    nlinarith [hqR, hrR, hq0', hr0', hQ2pos]
  have hgoal_eq : (a : ℝ) / (q : ℝ) - (b : ℝ) / (r : ℝ) - (m : ℝ)
      = (N : ℝ) / ((q : ℝ) * (r : ℝ)) := by
    rw [hNcast]
    field_simp
  rw [hgoal_eq, abs_div, abs_of_pos hqrpos]
  -- 1/Q² ≤ 1/(q*r) ≤ |N|/(q*r)
  have h1 : 1 / (Q : ℝ) ^ 2 ≤ 1 / ((q : ℝ) * (r : ℝ)) :=
    one_div_le_one_div_of_le hqrpos hden_le
  have h2 : 1 / ((q : ℝ) * (r : ℝ)) ≤ |(N : ℝ)| / ((q : ℝ) * (r : ℝ)) := by
    have hinv : (0 : ℝ) ≤ 1 / ((q : ℝ) * (r : ℝ)) := by positivity
    calc 1 / ((q : ℝ) * (r : ℝ)) = 1 * (1 / ((q : ℝ) * (r : ℝ))) := by ring
      _ ≤ |(N : ℝ)| * (1 / ((q : ℝ) * (r : ℝ))) :=
            mul_le_mul_of_nonneg_right hNabs hinv
      _ = |(N : ℝ)| / ((q : ℝ) * (r : ℝ)) := by ring
  exact le_trans h1 h2
