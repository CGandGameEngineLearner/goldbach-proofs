import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_1117 :
    ∀ n : ℕ, 1117 ∣ n ^ 2 + 1 ↔ n % 1117 = 214 ∨ n % 1117 = 903 := by
  intro n
  haveI : Fact (1117).Prime := ⟨by norm_num⟩
  have hcast : ((n ^ 2 + 1 : ℕ) : ZMod 1117) = (n : ZMod 1117) ^ 2 + 1 := by
    push_cast
    ring
  have ha : (214 : ZMod 1117) ^ 2 + 1 = 0 := by
    rw [show (214 : ZMod 1117) ^ 2 + 1 = ((214 ^ 2 + 1 : ℕ) : ZMod 1117) by
      push_cast
      ring]
    exact (ZMod.natCast_eq_zero_iff (214 ^ 2 + 1) 1117).mpr (by norm_num)
  have hb : (903 : ZMod 1117) ^ 2 + 1 = 0 := by
    rw [show (903 : ZMod 1117) ^ 2 + 1 = ((903 ^ 2 + 1 : ℕ) : ZMod 1117) by
      push_cast
      ring]
    exact (ZMod.natCast_eq_zero_iff (903 ^ 2 + 1) 1117).mpr (by norm_num)
  have hsum : (214 : ZMod 1117) + (903 : ZMod 1117) = 0 := by
    rw [show (214 : ZMod 1117) + (903 : ZMod 1117) = ((214 + 903 : ℕ) : ZMod 1117) by
      push_cast
      ring]
    exact (ZMod.natCast_eq_zero_iff (214 + 903) 1117).mpr (by norm_num)
  have hprod : (214 : ZMod 1117) * (903 : ZMod 1117) = 1 := by
    rw [← Nat.cast_one]
    rw [show (214 : ZMod 1117) * (903 : ZMod 1117) = ((214 * 903 : ℕ) : ZMod 1117) by
      push_cast
      ring]
    exact (ZMod.natCast_eq_natCast_iff' (214 * 903) 1 1117).mpr (by norm_num)
  have hroot : ∀ r : ZMod 1117, r ^ 2 + 1 = 0 ↔ r = (214 : ZMod 1117) ∨ r = (903 : ZMod 1117) := by
    intro r
    constructor
    · intro h
      have hfac : (r - (214 : ZMod 1117)) * (r - (903 : ZMod 1117)) = 0 := by
        have hid : (r - (214 : ZMod 1117)) * (r - (903 : ZMod 1117)) = r ^ 2 + 1 := by
          calc (r - (214 : ZMod 1117)) * (r - (903 : ZMod 1117))
              = r ^ 2 - ((214 : ZMod 1117) + (903 : ZMod 1117)) * r
                  + (214 : ZMod 1117) * (903 : ZMod 1117) := by ring
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
  rw [← ZMod.natCast_eq_zero_iff (n ^ 2 + 1) 1117, hcast, hroot (n : ZMod 1117)]
  constructor
  · rintro (h | h)
    · left
      have h' := (ZMod.natCast_eq_natCast_iff' n 214 1117).mp h
      rw [Nat.mod_eq_of_lt (by norm_num : 214 < 1117)] at h'
      exact h'
    · right
      have h' := (ZMod.natCast_eq_natCast_iff' n 903 1117).mp h
      rw [Nat.mod_eq_of_lt (by norm_num : 903 < 1117)] at h'
      exact h' 
  · rintro (h | h)
    · left
      exact (ZMod.natCast_eq_natCast_iff' n 214 1117).mpr (by
        rw [Nat.mod_eq_of_lt (by norm_num : 214 < 1117)]
        exact h)
    · right
      exact (ZMod.natCast_eq_natCast_iff' n 903 1117).mpr (by
        rw [Nat.mod_eq_of_lt (by norm_num : 903 < 1117)]
        exact h)
