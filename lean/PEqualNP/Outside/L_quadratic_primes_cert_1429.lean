import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_1429 :
    ∀ n : ℕ, 1429 ∣ n ^ 2 + 1 ↔ n % 1429 = 620 ∨ n % 1429 = 809 := by
  intro n
  haveI : Fact (1429).Prime := ⟨by norm_num⟩
  have hcast : ((n ^ 2 + 1 : ℕ) : ZMod 1429) = (n : ZMod 1429) ^ 2 + 1 := by
    push_cast
    ring
  have ha : (620 : ZMod 1429) ^ 2 + 1 = 0 := by
    rw [show (620 : ZMod 1429) ^ 2 + 1 = ((620 ^ 2 + 1 : ℕ) : ZMod 1429) by
      push_cast
      ring]
    exact (ZMod.natCast_eq_zero_iff (620 ^ 2 + 1) 1429).mpr (by norm_num)
  have hb : (809 : ZMod 1429) ^ 2 + 1 = 0 := by
    rw [show (809 : ZMod 1429) ^ 2 + 1 = ((809 ^ 2 + 1 : ℕ) : ZMod 1429) by
      push_cast
      ring]
    exact (ZMod.natCast_eq_zero_iff (809 ^ 2 + 1) 1429).mpr (by norm_num)
  have hsum : (620 : ZMod 1429) + (809 : ZMod 1429) = 0 := by
    rw [show (620 : ZMod 1429) + (809 : ZMod 1429) = ((620 + 809 : ℕ) : ZMod 1429) by
      push_cast
      ring]
    exact (ZMod.natCast_eq_zero_iff (620 + 809) 1429).mpr (by norm_num)
  have hprod : (620 : ZMod 1429) * (809 : ZMod 1429) = 1 := by
    rw [← Nat.cast_one]
    rw [show (620 : ZMod 1429) * (809 : ZMod 1429) = ((620 * 809 : ℕ) : ZMod 1429) by
      push_cast
      ring]
    exact (ZMod.natCast_eq_natCast_iff' (620 * 809) 1 1429).mpr (by norm_num)
  have hroot : ∀ r : ZMod 1429, r ^ 2 + 1 = 0 ↔ r = (620 : ZMod 1429) ∨ r = (809 : ZMod 1429) := by
    intro r
    constructor
    · intro h
      have hfac : (r - (620 : ZMod 1429)) * (r - (809 : ZMod 1429)) = 0 := by
        have hid : (r - (620 : ZMod 1429)) * (r - (809 : ZMod 1429)) = r ^ 2 + 1 := by
          calc (r - (620 : ZMod 1429)) * (r - (809 : ZMod 1429))
              = r ^ 2 - ((620 : ZMod 1429) + (809 : ZMod 1429)) * r
                  + (620 : ZMod 1429) * (809 : ZMod 1429) := by ring
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
  rw [← ZMod.natCast_eq_zero_iff (n ^ 2 + 1) 1429, hcast, hroot (n : ZMod 1429)]
  constructor
  · rintro (h | h)
    · left
      have h' := (ZMod.natCast_eq_natCast_iff' n 620 1429).mp h
      rw [Nat.mod_eq_of_lt (by norm_num : 620 < 1429)] at h'
      exact h'
    · right
      have h' := (ZMod.natCast_eq_natCast_iff' n 809 1429).mp h
      rw [Nat.mod_eq_of_lt (by norm_num : 809 < 1429)] at h'
      exact h' 
  · rintro (h | h)
    · left
      exact (ZMod.natCast_eq_natCast_iff' n 620 1429).mpr (by
        rw [Nat.mod_eq_of_lt (by norm_num : 620 < 1429)]
        exact h)
    · right
      exact (ZMod.natCast_eq_natCast_iff' n 809 1429).mpr (by
        rw [Nat.mod_eq_of_lt (by norm_num : 809 < 1429)]
        exact h)
