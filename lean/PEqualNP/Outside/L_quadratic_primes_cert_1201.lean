import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_1201 :
    ∀ n : ℕ, 1201 ∣ n ^ 2 + 1 ↔ n % 1201 = 49 ∨ n % 1201 = 1152 := by
  intro n
  haveI : Fact (1201).Prime := ⟨by norm_num⟩
  have hcast : ((n ^ 2 + 1 : ℕ) : ZMod 1201) = (n : ZMod 1201) ^ 2 + 1 := by
    push_cast
    ring
  have ha : (49 : ZMod 1201) ^ 2 + 1 = 0 := by
    rw [show (49 : ZMod 1201) ^ 2 + 1 = ((49 ^ 2 + 1 : ℕ) : ZMod 1201) by
      push_cast
      ring]
    exact (ZMod.natCast_eq_zero_iff (49 ^ 2 + 1) 1201).mpr (by norm_num)
  have hb : (1152 : ZMod 1201) ^ 2 + 1 = 0 := by
    rw [show (1152 : ZMod 1201) ^ 2 + 1 = ((1152 ^ 2 + 1 : ℕ) : ZMod 1201) by
      push_cast
      ring]
    exact (ZMod.natCast_eq_zero_iff (1152 ^ 2 + 1) 1201).mpr (by norm_num)
  have hsum : (49 : ZMod 1201) + (1152 : ZMod 1201) = 0 := by
    rw [show (49 : ZMod 1201) + (1152 : ZMod 1201) = ((49 + 1152 : ℕ) : ZMod 1201) by
      push_cast
      ring]
    exact (ZMod.natCast_eq_zero_iff (49 + 1152) 1201).mpr (by norm_num)
  have hprod : (49 : ZMod 1201) * (1152 : ZMod 1201) = 1 := by
    rw [← Nat.cast_one]
    rw [show (49 : ZMod 1201) * (1152 : ZMod 1201) = ((49 * 1152 : ℕ) : ZMod 1201) by
      push_cast
      ring]
    exact (ZMod.natCast_eq_natCast_iff' (49 * 1152) 1 1201).mpr (by norm_num)
  have hroot : ∀ r : ZMod 1201, r ^ 2 + 1 = 0 ↔ r = (49 : ZMod 1201) ∨ r = (1152 : ZMod 1201) := by
    intro r
    constructor
    · intro h
      have hfac : (r - (49 : ZMod 1201)) * (r - (1152 : ZMod 1201)) = 0 := by
        have hid : (r - (49 : ZMod 1201)) * (r - (1152 : ZMod 1201)) = r ^ 2 + 1 := by
          calc (r - (49 : ZMod 1201)) * (r - (1152 : ZMod 1201))
              = r ^ 2 - ((49 : ZMod 1201) + (1152 : ZMod 1201)) * r
                  + (49 : ZMod 1201) * (1152 : ZMod 1201) := by ring
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
  rw [← ZMod.natCast_eq_zero_iff (n ^ 2 + 1) 1201, hcast, hroot (n : ZMod 1201)]
  constructor
  · rintro (h | h)
    · left
      have h' := (ZMod.natCast_eq_natCast_iff' n 49 1201).mp h
      rw [Nat.mod_eq_of_lt (by norm_num : 49 < 1201)] at h'
      exact h'
    · right
      have h' := (ZMod.natCast_eq_natCast_iff' n 1152 1201).mp h
      rw [Nat.mod_eq_of_lt (by norm_num : 1152 < 1201)] at h'
      exact h' 
  · rintro (h | h)
    · left
      exact (ZMod.natCast_eq_natCast_iff' n 49 1201).mpr (by
        rw [Nat.mod_eq_of_lt (by norm_num : 49 < 1201)]
        exact h)
    · right
      exact (ZMod.natCast_eq_natCast_iff' n 1152 1201).mpr (by
        rw [Nat.mod_eq_of_lt (by norm_num : 1152 < 1201)]
        exact h)
