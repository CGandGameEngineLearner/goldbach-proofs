import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_1277 :
    ∀ n : ℕ, 1277 ∣ n ^ 2 + 1 ↔ n % 1277 = 113 ∨ n % 1277 = 1164 := by
  intro n
  haveI : Fact (1277).Prime := ⟨by norm_num⟩
  have hcast : ((n ^ 2 + 1 : ℕ) : ZMod 1277) = (n : ZMod 1277) ^ 2 + 1 := by
    push_cast
    ring
  have ha : (113 : ZMod 1277) ^ 2 + 1 = 0 := by
    rw [show (113 : ZMod 1277) ^ 2 + 1 = ((113 ^ 2 + 1 : ℕ) : ZMod 1277) by
      push_cast
      ring]
    exact (ZMod.natCast_eq_zero_iff (113 ^ 2 + 1) 1277).mpr (by norm_num)
  have hb : (1164 : ZMod 1277) ^ 2 + 1 = 0 := by
    rw [show (1164 : ZMod 1277) ^ 2 + 1 = ((1164 ^ 2 + 1 : ℕ) : ZMod 1277) by
      push_cast
      ring]
    exact (ZMod.natCast_eq_zero_iff (1164 ^ 2 + 1) 1277).mpr (by norm_num)
  have hsum : (113 : ZMod 1277) + (1164 : ZMod 1277) = 0 := by
    rw [show (113 : ZMod 1277) + (1164 : ZMod 1277) = ((113 + 1164 : ℕ) : ZMod 1277) by
      push_cast
      ring]
    exact (ZMod.natCast_eq_zero_iff (113 + 1164) 1277).mpr (by norm_num)
  have hprod : (113 : ZMod 1277) * (1164 : ZMod 1277) = 1 := by
    rw [← Nat.cast_one]
    rw [show (113 : ZMod 1277) * (1164 : ZMod 1277) = ((113 * 1164 : ℕ) : ZMod 1277) by
      push_cast
      ring]
    exact (ZMod.natCast_eq_natCast_iff' (113 * 1164) 1 1277).mpr (by norm_num)
  have hroot : ∀ r : ZMod 1277, r ^ 2 + 1 = 0 ↔ r = (113 : ZMod 1277) ∨ r = (1164 : ZMod 1277) := by
    intro r
    constructor
    · intro h
      have hfac : (r - (113 : ZMod 1277)) * (r - (1164 : ZMod 1277)) = 0 := by
        have hid : (r - (113 : ZMod 1277)) * (r - (1164 : ZMod 1277)) = r ^ 2 + 1 := by
          calc (r - (113 : ZMod 1277)) * (r - (1164 : ZMod 1277))
              = r ^ 2 - ((113 : ZMod 1277) + (1164 : ZMod 1277)) * r
                  + (113 : ZMod 1277) * (1164 : ZMod 1277) := by ring
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
  rw [← ZMod.natCast_eq_zero_iff (n ^ 2 + 1) 1277, hcast, hroot (n : ZMod 1277)]
  constructor
  · rintro (h | h)
    · left
      have h' := (ZMod.natCast_eq_natCast_iff' n 113 1277).mp h
      rw [Nat.mod_eq_of_lt (by norm_num : 113 < 1277)] at h'
      exact h'
    · right
      have h' := (ZMod.natCast_eq_natCast_iff' n 1164 1277).mp h
      rw [Nat.mod_eq_of_lt (by norm_num : 1164 < 1277)] at h'
      exact h' 
  · rintro (h | h)
    · left
      exact (ZMod.natCast_eq_natCast_iff' n 113 1277).mpr (by
        rw [Nat.mod_eq_of_lt (by norm_num : 113 < 1277)]
        exact h)
    · right
      exact (ZMod.natCast_eq_natCast_iff' n 1164 1277).mpr (by
        rw [Nat.mod_eq_of_lt (by norm_num : 1164 < 1277)]
        exact h)
