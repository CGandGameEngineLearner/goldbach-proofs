import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_1609 :
    ∀ n : ℕ, 1609 ∣ n ^ 2 + 1 ↔ n % 1609 = 523 ∨ n % 1609 = 1086 := by
  intro n
  haveI : Fact (1609).Prime := ⟨by norm_num⟩
  have hcast : ((n ^ 2 + 1 : ℕ) : ZMod 1609) = (n : ZMod 1609) ^ 2 + 1 := by
    push_cast
    ring
  have ha : (523 : ZMod 1609) ^ 2 + 1 = 0 := by
    rw [show (523 : ZMod 1609) ^ 2 + 1 = ((523 ^ 2 + 1 : ℕ) : ZMod 1609) by
      push_cast
      ring]
    exact (ZMod.natCast_eq_zero_iff (523 ^ 2 + 1) 1609).mpr (by norm_num)
  have hb : (1086 : ZMod 1609) ^ 2 + 1 = 0 := by
    rw [show (1086 : ZMod 1609) ^ 2 + 1 = ((1086 ^ 2 + 1 : ℕ) : ZMod 1609) by
      push_cast
      ring]
    exact (ZMod.natCast_eq_zero_iff (1086 ^ 2 + 1) 1609).mpr (by norm_num)
  have hsum : (523 : ZMod 1609) + (1086 : ZMod 1609) = 0 := by
    rw [show (523 : ZMod 1609) + (1086 : ZMod 1609) = ((523 + 1086 : ℕ) : ZMod 1609) by
      push_cast
      ring]
    exact (ZMod.natCast_eq_zero_iff (523 + 1086) 1609).mpr (by norm_num)
  have hprod : (523 : ZMod 1609) * (1086 : ZMod 1609) = 1 := by
    rw [← Nat.cast_one]
    rw [show (523 : ZMod 1609) * (1086 : ZMod 1609) = ((523 * 1086 : ℕ) : ZMod 1609) by
      push_cast
      ring]
    exact (ZMod.natCast_eq_natCast_iff' (523 * 1086) 1 1609).mpr (by norm_num)
  have hroot : ∀ r : ZMod 1609, r ^ 2 + 1 = 0 ↔ r = (523 : ZMod 1609) ∨ r = (1086 : ZMod 1609) := by
    intro r
    constructor
    · intro h
      have hfac : (r - (523 : ZMod 1609)) * (r - (1086 : ZMod 1609)) = 0 := by
        have hid : (r - (523 : ZMod 1609)) * (r - (1086 : ZMod 1609)) = r ^ 2 + 1 := by
          calc (r - (523 : ZMod 1609)) * (r - (1086 : ZMod 1609))
              = r ^ 2 - ((523 : ZMod 1609) + (1086 : ZMod 1609)) * r
                  + (523 : ZMod 1609) * (1086 : ZMod 1609) := by ring
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
  rw [← ZMod.natCast_eq_zero_iff (n ^ 2 + 1) 1609, hcast, hroot (n : ZMod 1609)]
  constructor
  · rintro (h | h)
    · left
      have h' := (ZMod.natCast_eq_natCast_iff' n 523 1609).mp h
      rw [Nat.mod_eq_of_lt (by norm_num : 523 < 1609)] at h'
      exact h'
    · right
      have h' := (ZMod.natCast_eq_natCast_iff' n 1086 1609).mp h
      rw [Nat.mod_eq_of_lt (by norm_num : 1086 < 1609)] at h'
      exact h' 
  · rintro (h | h)
    · left
      exact (ZMod.natCast_eq_natCast_iff' n 523 1609).mpr (by
        rw [Nat.mod_eq_of_lt (by norm_num : 523 < 1609)]
        exact h)
    · right
      exact (ZMod.natCast_eq_natCast_iff' n 1086 1609).mpr (by
        rw [Nat.mod_eq_of_lt (by norm_num : 1086 < 1609)]
        exact h)
