import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_1549 :
    ∀ n : ℕ, 1549 ∣ n ^ 2 + 1 ↔ n % 1549 = 88 ∨ n % 1549 = 1461 := by
  intro n
  haveI : Fact (1549).Prime := ⟨by norm_num⟩
  have hcast : ((n ^ 2 + 1 : ℕ) : ZMod 1549) = (n : ZMod 1549) ^ 2 + 1 := by
    push_cast
    ring
  have ha : (88 : ZMod 1549) ^ 2 + 1 = 0 := by
    rw [show (88 : ZMod 1549) ^ 2 + 1 = ((88 ^ 2 + 1 : ℕ) : ZMod 1549) by
      push_cast
      ring]
    exact (ZMod.natCast_eq_zero_iff (88 ^ 2 + 1) 1549).mpr (by norm_num)
  have hb : (1461 : ZMod 1549) ^ 2 + 1 = 0 := by
    rw [show (1461 : ZMod 1549) ^ 2 + 1 = ((1461 ^ 2 + 1 : ℕ) : ZMod 1549) by
      push_cast
      ring]
    exact (ZMod.natCast_eq_zero_iff (1461 ^ 2 + 1) 1549).mpr (by norm_num)
  have hsum : (88 : ZMod 1549) + (1461 : ZMod 1549) = 0 := by
    rw [show (88 : ZMod 1549) + (1461 : ZMod 1549) = ((88 + 1461 : ℕ) : ZMod 1549) by
      push_cast
      ring]
    exact (ZMod.natCast_eq_zero_iff (88 + 1461) 1549).mpr (by norm_num)
  have hprod : (88 : ZMod 1549) * (1461 : ZMod 1549) = 1 := by
    rw [← Nat.cast_one]
    rw [show (88 : ZMod 1549) * (1461 : ZMod 1549) = ((88 * 1461 : ℕ) : ZMod 1549) by
      push_cast
      ring]
    exact (ZMod.natCast_eq_natCast_iff' (88 * 1461) 1 1549).mpr (by norm_num)
  have hroot : ∀ r : ZMod 1549, r ^ 2 + 1 = 0 ↔ r = (88 : ZMod 1549) ∨ r = (1461 : ZMod 1549) := by
    intro r
    constructor
    · intro h
      have hfac : (r - (88 : ZMod 1549)) * (r - (1461 : ZMod 1549)) = 0 := by
        have hid : (r - (88 : ZMod 1549)) * (r - (1461 : ZMod 1549)) = r ^ 2 + 1 := by
          calc (r - (88 : ZMod 1549)) * (r - (1461 : ZMod 1549))
              = r ^ 2 - ((88 : ZMod 1549) + (1461 : ZMod 1549)) * r
                  + (88 : ZMod 1549) * (1461 : ZMod 1549) := by ring
            _ = r ^ 2 + 1 := by rw [hsum, hprod]; ring
        rw [hid]
        exact h
      rcases mul_eq_zero.mp hfac with h' | h'
      · left
        exact sub_eq_zero.mp h'
      · right
        exact sub_eq_zero.mp h'
    · rintro (h | h)
      · rw [h]
        exact ha
      · rw [h]
        exact hb
  rw [← ZMod.natCast_eq_zero_iff (n ^ 2 + 1) 1549, hcast, hroot (n : ZMod 1549)]
  constructor
  · rintro (h | h)
    · left
      have h' := (ZMod.natCast_eq_natCast_iff' n 88 1549).mp h
      rw [Nat.mod_eq_of_lt (by norm_num : 88 < 1549)] at h'
      exact h'
    · right
      have h' := (ZMod.natCast_eq_natCast_iff' n 1461 1549).mp h
      rw [Nat.mod_eq_of_lt (by norm_num : 1461 < 1549)] at h'
      exact h' 
  · rintro (h | h)
    · left
      exact (ZMod.natCast_eq_natCast_iff' n 88 1549).mpr (by
        rw [Nat.mod_eq_of_lt (by norm_num : 88 < 1549)]
        exact h)
    · right
      exact (ZMod.natCast_eq_natCast_iff' n 1461 1549).mpr (by
        rw [Nat.mod_eq_of_lt (by norm_num : 1461 < 1549)]
        exact h)
