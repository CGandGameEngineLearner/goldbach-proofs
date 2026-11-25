import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_1481 :
    ∀ n : ℕ, 1481 ∣ n ^ 2 + 1 ↔ n % 1481 = 465 ∨ n % 1481 = 1016 := by
  intro n
  haveI : Fact (1481).Prime := ⟨by norm_num⟩
  have hcast : ((n ^ 2 + 1 : ℕ) : ZMod 1481) = (n : ZMod 1481) ^ 2 + 1 := by
    push_cast
    ring
  have ha : (465 : ZMod 1481) ^ 2 + 1 = 0 := by
    rw [show (465 : ZMod 1481) ^ 2 + 1 = ((465 ^ 2 + 1 : ℕ) : ZMod 1481) by
      push_cast
      ring]
    exact (ZMod.natCast_eq_zero_iff (465 ^ 2 + 1) 1481).mpr (by norm_num)
  have hb : (1016 : ZMod 1481) ^ 2 + 1 = 0 := by
    rw [show (1016 : ZMod 1481) ^ 2 + 1 = ((1016 ^ 2 + 1 : ℕ) : ZMod 1481) by
      push_cast
      ring]
    exact (ZMod.natCast_eq_zero_iff (1016 ^ 2 + 1) 1481).mpr (by norm_num)
  have hsum : (465 : ZMod 1481) + (1016 : ZMod 1481) = 0 := by
    rw [show (465 : ZMod 1481) + (1016 : ZMod 1481) = ((465 + 1016 : ℕ) : ZMod 1481) by
      push_cast
      ring]
    exact (ZMod.natCast_eq_zero_iff (465 + 1016) 1481).mpr (by norm_num)
  have hprod : (465 : ZMod 1481) * (1016 : ZMod 1481) = 1 := by
    rw [← Nat.cast_one]
    rw [show (465 : ZMod 1481) * (1016 : ZMod 1481) = ((465 * 1016 : ℕ) : ZMod 1481) by
      push_cast
      ring]
    exact (ZMod.natCast_eq_natCast_iff' (465 * 1016) 1 1481).mpr (by norm_num)
  have hroot : ∀ r : ZMod 1481, r ^ 2 + 1 = 0 ↔ r = (465 : ZMod 1481) ∨ r = (1016 : ZMod 1481) := by
    intro r
    constructor
    · intro h
      have hfac : (r - (465 : ZMod 1481)) * (r - (1016 : ZMod 1481)) = 0 := by
        have hid : (r - (465 : ZMod 1481)) * (r - (1016 : ZMod 1481)) = r ^ 2 + 1 := by
          calc (r - (465 : ZMod 1481)) * (r - (1016 : ZMod 1481))
              = r ^ 2 - ((465 : ZMod 1481) + (1016 : ZMod 1481)) * r
                  + (465 : ZMod 1481) * (1016 : ZMod 1481) := by ring
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
  rw [← ZMod.natCast_eq_zero_iff (n ^ 2 + 1) 1481, hcast, hroot (n : ZMod 1481)]
  constructor
  · rintro (h | h)
    · left
      have h' := (ZMod.natCast_eq_natCast_iff' n 465 1481).mp h
      rw [Nat.mod_eq_of_lt (by norm_num : 465 < 1481)] at h'
      exact h'
    · right
      have h' := (ZMod.natCast_eq_natCast_iff' n 1016 1481).mp h
      rw [Nat.mod_eq_of_lt (by norm_num : 1016 < 1481)] at h'
      exact h' 
  · rintro (h | h)
    · left
      exact (ZMod.natCast_eq_natCast_iff' n 465 1481).mpr (by
        rw [Nat.mod_eq_of_lt (by norm_num : 465 < 1481)]
        exact h)
    · right
      exact (ZMod.natCast_eq_natCast_iff' n 1016 1481).mpr (by
        rw [Nat.mod_eq_of_lt (by norm_num : 1016 < 1481)]
        exact h)
