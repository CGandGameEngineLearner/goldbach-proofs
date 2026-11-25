import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_1489 :
    ∀ n : ℕ, 1489 ∣ n ^ 2 + 1 ↔ n % 1489 = 225 ∨ n % 1489 = 1264 := by
  intro n
  haveI : Fact (1489).Prime := ⟨by norm_num⟩
  have hcast : ((n ^ 2 + 1 : ℕ) : ZMod 1489) = (n : ZMod 1489) ^ 2 + 1 := by
    push_cast
    ring
  have ha : (225 : ZMod 1489) ^ 2 + 1 = 0 := by
    rw [show (225 : ZMod 1489) ^ 2 + 1 = ((225 ^ 2 + 1 : ℕ) : ZMod 1489) by
      push_cast
      ring]
    exact (ZMod.natCast_eq_zero_iff (225 ^ 2 + 1) 1489).mpr (by norm_num)
  have hb : (1264 : ZMod 1489) ^ 2 + 1 = 0 := by
    rw [show (1264 : ZMod 1489) ^ 2 + 1 = ((1264 ^ 2 + 1 : ℕ) : ZMod 1489) by
      push_cast
      ring]
    exact (ZMod.natCast_eq_zero_iff (1264 ^ 2 + 1) 1489).mpr (by norm_num)
  have hsum : (225 : ZMod 1489) + (1264 : ZMod 1489) = 0 := by
    rw [show (225 : ZMod 1489) + (1264 : ZMod 1489) = ((225 + 1264 : ℕ) : ZMod 1489) by
      push_cast
      ring]
    exact (ZMod.natCast_eq_zero_iff (225 + 1264) 1489).mpr (by norm_num)
  have hprod : (225 : ZMod 1489) * (1264 : ZMod 1489) = 1 := by
    rw [← Nat.cast_one]
    rw [show (225 : ZMod 1489) * (1264 : ZMod 1489) = ((225 * 1264 : ℕ) : ZMod 1489) by
      push_cast
      ring]
    exact (ZMod.natCast_eq_natCast_iff' (225 * 1264) 1 1489).mpr (by norm_num)
  have hroot : ∀ r : ZMod 1489, r ^ 2 + 1 = 0 ↔ r = (225 : ZMod 1489) ∨ r = (1264 : ZMod 1489) := by
    intro r
    constructor
    · intro h
      have hfac : (r - (225 : ZMod 1489)) * (r - (1264 : ZMod 1489)) = 0 := by
        have hid : (r - (225 : ZMod 1489)) * (r - (1264 : ZMod 1489)) = r ^ 2 + 1 := by
          calc (r - (225 : ZMod 1489)) * (r - (1264 : ZMod 1489))
              = r ^ 2 - ((225 : ZMod 1489) + (1264 : ZMod 1489)) * r
                  + (225 : ZMod 1489) * (1264 : ZMod 1489) := by ring
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
  rw [← ZMod.natCast_eq_zero_iff (n ^ 2 + 1) 1489, hcast, hroot (n : ZMod 1489)]
  constructor
  · rintro (h | h)
    · left
      have h' := (ZMod.natCast_eq_natCast_iff' n 225 1489).mp h
      rw [Nat.mod_eq_of_lt (by norm_num : 225 < 1489)] at h'
      exact h'
    · right
      have h' := (ZMod.natCast_eq_natCast_iff' n 1264 1489).mp h
      rw [Nat.mod_eq_of_lt (by norm_num : 1264 < 1489)] at h'
      exact h' 
  · rintro (h | h)
    · left
      exact (ZMod.natCast_eq_natCast_iff' n 225 1489).mpr (by
        rw [Nat.mod_eq_of_lt (by norm_num : 225 < 1489)]
        exact h)
    · right
      exact (ZMod.natCast_eq_natCast_iff' n 1264 1489).mpr (by
        rw [Nat.mod_eq_of_lt (by norm_num : 1264 < 1489)]
        exact h)
