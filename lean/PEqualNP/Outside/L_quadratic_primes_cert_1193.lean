import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_1193 :
    ∀ n : ℕ, 1193 ∣ n ^ 2 + 1 ↔ n % 1193 = 186 ∨ n % 1193 = 1007 := by
  intro n
  haveI : Fact (1193).Prime := ⟨by norm_num⟩
  have hcast : ((n ^ 2 + 1 : ℕ) : ZMod 1193) = (n : ZMod 1193) ^ 2 + 1 := by
    push_cast
    ring
  have ha : (186 : ZMod 1193) ^ 2 + 1 = 0 := by
    rw [show (186 : ZMod 1193) ^ 2 + 1 = ((186 ^ 2 + 1 : ℕ) : ZMod 1193) by
      push_cast
      ring]
    exact (ZMod.natCast_eq_zero_iff (186 ^ 2 + 1) 1193).mpr (by norm_num)
  have hb : (1007 : ZMod 1193) ^ 2 + 1 = 0 := by
    rw [show (1007 : ZMod 1193) ^ 2 + 1 = ((1007 ^ 2 + 1 : ℕ) : ZMod 1193) by
      push_cast
      ring]
    exact (ZMod.natCast_eq_zero_iff (1007 ^ 2 + 1) 1193).mpr (by norm_num)
  have hsum : (186 : ZMod 1193) + (1007 : ZMod 1193) = 0 := by
    rw [show (186 : ZMod 1193) + (1007 : ZMod 1193) = ((186 + 1007 : ℕ) : ZMod 1193) by
      push_cast
      ring]
    exact (ZMod.natCast_eq_zero_iff (186 + 1007) 1193).mpr (by norm_num)
  have hprod : (186 : ZMod 1193) * (1007 : ZMod 1193) = 1 := by
    rw [← Nat.cast_one]
    rw [show (186 : ZMod 1193) * (1007 : ZMod 1193) = ((186 * 1007 : ℕ) : ZMod 1193) by
      push_cast
      ring]
    exact (ZMod.natCast_eq_natCast_iff' (186 * 1007) 1 1193).mpr (by norm_num)
  have hroot : ∀ r : ZMod 1193, r ^ 2 + 1 = 0 ↔ r = (186 : ZMod 1193) ∨ r = (1007 : ZMod 1193) := by
    intro r
    constructor
    · intro h
      have hfac : (r - (186 : ZMod 1193)) * (r - (1007 : ZMod 1193)) = 0 := by
        have hid : (r - (186 : ZMod 1193)) * (r - (1007 : ZMod 1193)) = r ^ 2 + 1 := by
          calc (r - (186 : ZMod 1193)) * (r - (1007 : ZMod 1193))
              = r ^ 2 - ((186 : ZMod 1193) + (1007 : ZMod 1193)) * r
                  + (186 : ZMod 1193) * (1007 : ZMod 1193) := by ring
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
  rw [← ZMod.natCast_eq_zero_iff (n ^ 2 + 1) 1193, hcast, hroot (n : ZMod 1193)]
  constructor
  · rintro (h | h)
    · left
      have h' := (ZMod.natCast_eq_natCast_iff' n 186 1193).mp h
      rw [Nat.mod_eq_of_lt (by norm_num : 186 < 1193)] at h'
      exact h'
    · right
      have h' := (ZMod.natCast_eq_natCast_iff' n 1007 1193).mp h
      rw [Nat.mod_eq_of_lt (by norm_num : 1007 < 1193)] at h'
      exact h' 
  · rintro (h | h)
    · left
      exact (ZMod.natCast_eq_natCast_iff' n 186 1193).mpr (by
        rw [Nat.mod_eq_of_lt (by norm_num : 186 < 1193)]
        exact h)
    · right
      exact (ZMod.natCast_eq_natCast_iff' n 1007 1193).mpr (by
        rw [Nat.mod_eq_of_lt (by norm_num : 1007 < 1193)]
        exact h)
