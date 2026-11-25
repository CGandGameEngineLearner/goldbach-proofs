import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_1237 :
    ∀ n : ℕ, 1237 ∣ n ^ 2 + 1 ↔ n % 1237 = 546 ∨ n % 1237 = 691 := by
  intro n
  haveI : Fact (1237).Prime := ⟨by norm_num⟩
  have hcast : ((n ^ 2 + 1 : ℕ) : ZMod 1237) = (n : ZMod 1237) ^ 2 + 1 := by
    push_cast
    ring
  have ha : (546 : ZMod 1237) ^ 2 + 1 = 0 := by
    rw [show (546 : ZMod 1237) ^ 2 + 1 = ((546 ^ 2 + 1 : ℕ) : ZMod 1237) by
      push_cast
      ring]
    exact (ZMod.natCast_eq_zero_iff (546 ^ 2 + 1) 1237).mpr (by norm_num)
  have hb : (691 : ZMod 1237) ^ 2 + 1 = 0 := by
    rw [show (691 : ZMod 1237) ^ 2 + 1 = ((691 ^ 2 + 1 : ℕ) : ZMod 1237) by
      push_cast
      ring]
    exact (ZMod.natCast_eq_zero_iff (691 ^ 2 + 1) 1237).mpr (by norm_num)
  have hsum : (546 : ZMod 1237) + (691 : ZMod 1237) = 0 := by
    rw [show (546 : ZMod 1237) + (691 : ZMod 1237) = ((546 + 691 : ℕ) : ZMod 1237) by
      push_cast
      ring]
    exact (ZMod.natCast_eq_zero_iff (546 + 691) 1237).mpr (by norm_num)
  have hprod : (546 : ZMod 1237) * (691 : ZMod 1237) = 1 := by
    rw [← Nat.cast_one]
    rw [show (546 : ZMod 1237) * (691 : ZMod 1237) = ((546 * 691 : ℕ) : ZMod 1237) by
      push_cast
      ring]
    exact (ZMod.natCast_eq_natCast_iff' (546 * 691) 1 1237).mpr (by norm_num)
  have hroot : ∀ r : ZMod 1237, r ^ 2 + 1 = 0 ↔ r = (546 : ZMod 1237) ∨ r = (691 : ZMod 1237) := by
    intro r
    constructor
    · intro h
      have hfac : (r - (546 : ZMod 1237)) * (r - (691 : ZMod 1237)) = 0 := by
        have hid : (r - (546 : ZMod 1237)) * (r - (691 : ZMod 1237)) = r ^ 2 + 1 := by
          calc (r - (546 : ZMod 1237)) * (r - (691 : ZMod 1237))
              = r ^ 2 - ((546 : ZMod 1237) + (691 : ZMod 1237)) * r
                  + (546 : ZMod 1237) * (691 : ZMod 1237) := by ring
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
  rw [← ZMod.natCast_eq_zero_iff (n ^ 2 + 1) 1237, hcast, hroot (n : ZMod 1237)]
  constructor
  · rintro (h | h)
    · left
      have h' := (ZMod.natCast_eq_natCast_iff' n 546 1237).mp h
      rw [Nat.mod_eq_of_lt (by norm_num : 546 < 1237)] at h'
      exact h'
    · right
      have h' := (ZMod.natCast_eq_natCast_iff' n 691 1237).mp h
      rw [Nat.mod_eq_of_lt (by norm_num : 691 < 1237)] at h'
      exact h' 
  · rintro (h | h)
    · left
      exact (ZMod.natCast_eq_natCast_iff' n 546 1237).mpr (by
        rw [Nat.mod_eq_of_lt (by norm_num : 546 < 1237)]
        exact h)
    · right
      exact (ZMod.natCast_eq_natCast_iff' n 691 1237).mpr (by
        rw [Nat.mod_eq_of_lt (by norm_num : 691 < 1237)]
        exact h)
