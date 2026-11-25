import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_1213 :
    ∀ n : ℕ, 1213 ∣ n ^ 2 + 1 ↔ n % 1213 = 495 ∨ n % 1213 = 718 := by
  intro n
  haveI : Fact (1213).Prime := ⟨by norm_num⟩
  have hcast : ((n ^ 2 + 1 : ℕ) : ZMod 1213) = (n : ZMod 1213) ^ 2 + 1 := by
    push_cast
    ring
  have ha : (495 : ZMod 1213) ^ 2 + 1 = 0 := by
    rw [show (495 : ZMod 1213) ^ 2 + 1 = ((495 ^ 2 + 1 : ℕ) : ZMod 1213) by
      push_cast
      ring]
    exact (ZMod.natCast_eq_zero_iff (495 ^ 2 + 1) 1213).mpr (by norm_num)
  have hb : (718 : ZMod 1213) ^ 2 + 1 = 0 := by
    rw [show (718 : ZMod 1213) ^ 2 + 1 = ((718 ^ 2 + 1 : ℕ) : ZMod 1213) by
      push_cast
      ring]
    exact (ZMod.natCast_eq_zero_iff (718 ^ 2 + 1) 1213).mpr (by norm_num)
  have hsum : (495 : ZMod 1213) + (718 : ZMod 1213) = 0 := by
    rw [show (495 : ZMod 1213) + (718 : ZMod 1213) = ((495 + 718 : ℕ) : ZMod 1213) by
      push_cast
      ring]
    exact (ZMod.natCast_eq_zero_iff (495 + 718) 1213).mpr (by norm_num)
  have hprod : (495 : ZMod 1213) * (718 : ZMod 1213) = 1 := by
    rw [← Nat.cast_one]
    rw [show (495 : ZMod 1213) * (718 : ZMod 1213) = ((495 * 718 : ℕ) : ZMod 1213) by
      push_cast
      ring]
    exact (ZMod.natCast_eq_natCast_iff' (495 * 718) 1 1213).mpr (by norm_num)
  have hroot : ∀ r : ZMod 1213, r ^ 2 + 1 = 0 ↔ r = (495 : ZMod 1213) ∨ r = (718 : ZMod 1213) := by
    intro r
    constructor
    · intro h
      have hfac : (r - (495 : ZMod 1213)) * (r - (718 : ZMod 1213)) = 0 := by
        have hid : (r - (495 : ZMod 1213)) * (r - (718 : ZMod 1213)) = r ^ 2 + 1 := by
          calc (r - (495 : ZMod 1213)) * (r - (718 : ZMod 1213))
              = r ^ 2 - ((495 : ZMod 1213) + (718 : ZMod 1213)) * r
                  + (495 : ZMod 1213) * (718 : ZMod 1213) := by ring
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
  rw [← ZMod.natCast_eq_zero_iff (n ^ 2 + 1) 1213, hcast, hroot (n : ZMod 1213)]
  constructor
  · rintro (h | h)
    · left
      have h' := (ZMod.natCast_eq_natCast_iff' n 495 1213).mp h
      rw [Nat.mod_eq_of_lt (by norm_num : 495 < 1213)] at h'
      exact h'
    · right
      have h' := (ZMod.natCast_eq_natCast_iff' n 718 1213).mp h
      rw [Nat.mod_eq_of_lt (by norm_num : 718 < 1213)] at h'
      exact h' 
  · rintro (h | h)
    · left
      exact (ZMod.natCast_eq_natCast_iff' n 495 1213).mpr (by
        rw [Nat.mod_eq_of_lt (by norm_num : 495 < 1213)]
        exact h)
    · right
      exact (ZMod.natCast_eq_natCast_iff' n 718 1213).mpr (by
        rw [Nat.mod_eq_of_lt (by norm_num : 718 < 1213)]
        exact h)
