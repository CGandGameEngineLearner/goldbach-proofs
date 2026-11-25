import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_1217 :
    ∀ n : ℕ, 1217 ∣ n ^ 2 + 1 ↔ n % 1217 = 78 ∨ n % 1217 = 1139 := by
  intro n
  haveI : Fact (1217).Prime := ⟨by norm_num⟩
  have hcast : ((n ^ 2 + 1 : ℕ) : ZMod 1217) = (n : ZMod 1217) ^ 2 + 1 := by
    push_cast
    ring
  have ha : (78 : ZMod 1217) ^ 2 + 1 = 0 := by
    rw [show (78 : ZMod 1217) ^ 2 + 1 = ((78 ^ 2 + 1 : ℕ) : ZMod 1217) by
      push_cast
      ring]
    exact (ZMod.natCast_eq_zero_iff (78 ^ 2 + 1) 1217).mpr (by norm_num)
  have hb : (1139 : ZMod 1217) ^ 2 + 1 = 0 := by
    rw [show (1139 : ZMod 1217) ^ 2 + 1 = ((1139 ^ 2 + 1 : ℕ) : ZMod 1217) by
      push_cast
      ring]
    exact (ZMod.natCast_eq_zero_iff (1139 ^ 2 + 1) 1217).mpr (by norm_num)
  have hsum : (78 : ZMod 1217) + (1139 : ZMod 1217) = 0 := by
    rw [show (78 : ZMod 1217) + (1139 : ZMod 1217) = ((78 + 1139 : ℕ) : ZMod 1217) by
      push_cast
      ring]
    exact (ZMod.natCast_eq_zero_iff (78 + 1139) 1217).mpr (by norm_num)
  have hprod : (78 : ZMod 1217) * (1139 : ZMod 1217) = 1 := by
    rw [← Nat.cast_one]
    rw [show (78 : ZMod 1217) * (1139 : ZMod 1217) = ((78 * 1139 : ℕ) : ZMod 1217) by
      push_cast
      ring]
    exact (ZMod.natCast_eq_natCast_iff' (78 * 1139) 1 1217).mpr (by norm_num)
  have hroot : ∀ r : ZMod 1217, r ^ 2 + 1 = 0 ↔ r = (78 : ZMod 1217) ∨ r = (1139 : ZMod 1217) := by
    intro r
    constructor
    · intro h
      have hfac : (r - (78 : ZMod 1217)) * (r - (1139 : ZMod 1217)) = 0 := by
        have hid : (r - (78 : ZMod 1217)) * (r - (1139 : ZMod 1217)) = r ^ 2 + 1 := by
          calc (r - (78 : ZMod 1217)) * (r - (1139 : ZMod 1217))
              = r ^ 2 - ((78 : ZMod 1217) + (1139 : ZMod 1217)) * r
                  + (78 : ZMod 1217) * (1139 : ZMod 1217) := by ring
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
  rw [← ZMod.natCast_eq_zero_iff (n ^ 2 + 1) 1217, hcast, hroot (n : ZMod 1217)]
  constructor
  · rintro (h | h)
    · left
      have h' := (ZMod.natCast_eq_natCast_iff' n 78 1217).mp h
      rw [Nat.mod_eq_of_lt (by norm_num : 78 < 1217)] at h'
      exact h'
    · right
      have h' := (ZMod.natCast_eq_natCast_iff' n 1139 1217).mp h
      rw [Nat.mod_eq_of_lt (by norm_num : 1139 < 1217)] at h'
      exact h' 
  · rintro (h | h)
    · left
      exact (ZMod.natCast_eq_natCast_iff' n 78 1217).mpr (by
        rw [Nat.mod_eq_of_lt (by norm_num : 78 < 1217)]
        exact h)
    · right
      exact (ZMod.natCast_eq_natCast_iff' n 1139 1217).mpr (by
        rw [Nat.mod_eq_of_lt (by norm_num : 1139 < 1217)]
        exact h)
