import Mathlib

open scoped BigOperators

namespace Conjectures.Goldbach

/-- Distinct reduced fractions with denominators at most `Q` are at least `1/Q²` apart modulo
one, including across the end of the period. -/
theorem FareySpacingLower :
    ∀ (Q a b q r : ℕ), 1 ≤ q → q ≤ Q → 1 ≤ r → r ≤ Q → Nat.Coprime a q → Nat.Coprime b r →
      (q ≠ r ∨ a % q ≠ b % r) → ∀ m : ℤ,
        1 / (Q : ℝ) ^ 2 ≤ |(a : ℝ) / q - (b : ℝ) / r - (m : ℝ)| := by
  intro Q a b q r hq1 hqQ hr1 hrQ hca hcb hne m
  have hq0 : q ≠ 0 := by omega
  have hr0 : r ≠ 0 := by omega
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq0
  have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast hr0
  set num : ℤ := (a : ℤ) * (r : ℤ) - (b : ℤ) * (q : ℤ) - m * ((q : ℤ) * (r : ℤ)) with hnumdef
  have hnum_ne : num ≠ 0 := by
    intro h0
    have h0' : (a : ℤ) * (r : ℤ) = (b : ℤ) * (q : ℤ) + m * ((q : ℤ) * (r : ℤ)) := by
      have h := h0
      rw [hnumdef] at h
      linarith
    have hqZ : (q : ℤ) ∣ (a : ℤ) * (r : ℤ) := by
      refine ⟨(b : ℤ) + m * (r : ℤ), ?_⟩
      rw [h0']
      ring
    have hq_dvd : q ∣ a * r := by
      have h := hqZ
      push_cast at h
      exact Int.natCast_dvd_natCast.mp h
    have hqr : q ∣ r := by
      have h : q ∣ r * a := by
        rw [mul_comm]
        exact hq_dvd
      exact (hca.symm.dvd_mul_right).mp h
    have hrZ : (r : ℤ) ∣ (b : ℤ) * (q : ℤ) := by
      refine ⟨(a : ℤ) - m * (q : ℤ), ?_⟩
      linear_combination -h0'
    have hr_dvd : r ∣ b * q := by
      have h := hrZ
      push_cast at h
      exact Int.natCast_dvd_natCast.mp h
    have hrq : r ∣ q := by
      have h : r ∣ q * b := by
        rw [mul_comm]
        exact hr_dvd
      exact (hcb.symm.dvd_mul_right).mp h
    have hqreq : q = r := Nat.dvd_antisymm hqr hrq
    have hex : (a : ℤ) - (b : ℤ) = m * (q : ℤ) := by
      have hkey : (q : ℤ) * ((a : ℤ) - (b : ℤ)) = (q : ℤ) * (m * (q : ℤ)) := by
        rw [← hqreq] at h0'
        linear_combination h0'
      exact mul_left_cancel₀ (by exact_mod_cast hq0) hkey
    have hmod : a % q = b % r := by
      have hdvd : (q : ℤ) ∣ (b : ℤ) - (a : ℤ) := by
        refine ⟨-m, ?_⟩
        linear_combination -hex
      have hmodeq : a ≡ b [MOD q] := Nat.modEq_iff_dvd.mpr hdvd
      rw [← hqreq]
      exact hmodeq
    rcases hne with h | h
    · exact h hqreq
    · exact h hmod
  have hnum_abs : (1 : ℝ) ≤ |((num : ℤ) : ℝ)| := by
    obtain ⟨k, hk | hk⟩ := Int.eq_nat_or_neg num
    · have hk0 : k ≠ 0 := by
        rintro rfl
        exact hnum_ne (by rw [hk]; simp)
      have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk0
      rw [hk]
      push_cast
      simpa using hk1
    · have hk0 : k ≠ 0 := by
        rintro rfl
        exact hnum_ne (by rw [hk]; simp)
      have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk0
      rw [hk]
      push_cast
      simpa using hk1
  have hqR0 : (0 : ℝ) < (q : ℝ) := lt_of_le_of_ne (by positivity) (Ne.symm hqR)
  have hrR0 : (0 : ℝ) < (r : ℝ) := lt_of_le_of_ne (by positivity) (Ne.symm hrR)
  have hden : (0 : ℝ) < (q : ℝ) * (r : ℝ) := mul_pos hqR0 hrR0
  have hnumcast :
      ((num : ℤ) : ℝ) = (a : ℝ) * (r : ℝ) - (b : ℝ) * (q : ℝ) - (m : ℝ) * ((q : ℝ) * (r : ℝ)) := by
    rw [hnumdef]
    push_cast
    ring
  have hx : (a : ℝ) / q - (b : ℝ) / r - (m : ℝ) = ((num : ℤ) : ℝ) / ((q : ℝ) * (r : ℝ)) := by
    rw [hnumcast]
    field_simp
  have hqrle : (q : ℝ) * (r : ℝ) ≤ (Q : ℝ) ^ 2 := by
    have hqle : (q : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hqQ
    have hrle : (r : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hrQ
    nlinarith [mul_nonneg (le_of_lt hqR0) (le_of_lt hrR0)]
  have hone : 1 / (Q : ℝ) ^ 2 ≤ 1 / ((q : ℝ) * (r : ℝ)) := one_div_le_one_div_of_le hden hqrle
  have hstep : 1 / ((q : ℝ) * (r : ℝ)) ≤ |((num : ℤ) : ℝ)| / ((q : ℝ) * (r : ℝ)) :=
    (div_le_div_iff_of_pos_right hden).mpr hnum_abs
  rw [hx, abs_div, abs_of_pos hden]
  exact le_trans hone hstep

end Conjectures.Goldbach
