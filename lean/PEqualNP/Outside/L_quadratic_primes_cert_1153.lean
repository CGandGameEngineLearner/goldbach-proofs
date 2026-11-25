import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_1153 :
    ∀ n : ℕ, 1153 ∣ n ^ 2 + 1 ↔ n % 1153 = 140 ∨ n % 1153 = 1013 := by
  intro n
  haveI : Fact (1153).Prime := ⟨by norm_num⟩
  have hcast : ((n ^ 2 + 1 : ℕ) : ZMod 1153) = (n : ZMod 1153) ^ 2 + 1 := by
    push_cast
    ring
  have ha : (140 : ZMod 1153) ^ 2 + 1 = 0 := by
    rw [show (140 : ZMod 1153) ^ 2 + 1 = ((140 ^ 2 + 1 : ℕ) : ZMod 1153) by
      push_cast
      ring]
    exact (ZMod.natCast_eq_zero_iff (140 ^ 2 + 1) 1153).mpr (by norm_num)
  have hb : (1013 : ZMod 1153) ^ 2 + 1 = 0 := by
    rw [show (1013 : ZMod 1153) ^ 2 + 1 = ((1013 ^ 2 + 1 : ℕ) : ZMod 1153) by
      push_cast
      ring]
    exact (ZMod.natCast_eq_zero_iff (1013 ^ 2 + 1) 1153).mpr (by norm_num)
  have hsum : (140 : ZMod 1153) + (1013 : ZMod 1153) = 0 := by
    rw [show (140 : ZMod 1153) + (1013 : ZMod 1153) = ((140 + 1013 : ℕ) : ZMod 1153) by
      push_cast
      ring]
    exact (ZMod.natCast_eq_zero_iff (140 + 1013) 1153).mpr (by norm_num)
  have hprod : (140 : ZMod 1153) * (1013 : ZMod 1153) = 1 := by
    rw [← Nat.cast_one]
    rw [show (140 : ZMod 1153) * (1013 : ZMod 1153) = ((140 * 1013 : ℕ) : ZMod 1153) by
      push_cast
      ring]
    exact (ZMod.natCast_eq_natCast_iff' (140 * 1013) 1 1153).mpr (by norm_num)
  have hroot : ∀ r : ZMod 1153, r ^ 2 + 1 = 0 ↔ r = (140 : ZMod 1153) ∨ r = (1013 : ZMod 1153) := by
    intro r
    constructor
    · intro h
      have hfac : (r - (140 : ZMod 1153)) * (r - (1013 : ZMod 1153)) = 0 := by
        have hid : (r - (140 : ZMod 1153)) * (r - (1013 : ZMod 1153)) = r ^ 2 + 1 := by
          calc (r - (140 : ZMod 1153)) * (r - (1013 : ZMod 1153))
              = r ^ 2 - ((140 : ZMod 1153) + (1013 : ZMod 1153)) * r
                  + (140 : ZMod 1153) * (1013 : ZMod 1153) := by ring
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
  rw [← ZMod.natCast_eq_zero_iff (n ^ 2 + 1) 1153, hcast, hroot (n : ZMod 1153)]
  constructor
  · rintro (h | h)
    · left
      have h' := (ZMod.natCast_eq_natCast_iff' n 140 1153).mp h
      rw [Nat.mod_eq_of_lt (by norm_num : 140 < 1153)] at h'
      exact h'
    · right
      have h' := (ZMod.natCast_eq_natCast_iff' n 1013 1153).mp h
      rw [Nat.mod_eq_of_lt (by norm_num : 1013 < 1153)] at h'
      exact h' 
  · rintro (h | h)
    · left
      exact (ZMod.natCast_eq_natCast_iff' n 140 1153).mpr (by
        rw [Nat.mod_eq_of_lt (by norm_num : 140 < 1153)]
        exact h)
    · right
      exact (ZMod.natCast_eq_natCast_iff' n 1013 1153).mpr (by
        rw [Nat.mod_eq_of_lt (by norm_num : 1013 < 1153)]
        exact h)
