import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_1493 :
    ∀ n : ℕ, 1493 ∣ n ^ 2 + 1 ↔ n % 1493 = 432 ∨ n % 1493 = 1061 := by
  intro n
  haveI : Fact (1493).Prime := ⟨by norm_num⟩
  have hcast : ((n ^ 2 + 1 : ℕ) : ZMod 1493) = (n : ZMod 1493) ^ 2 + 1 := by
    push_cast
    ring
  have ha : (432 : ZMod 1493) ^ 2 + 1 = 0 := by
    rw [show (432 : ZMod 1493) ^ 2 + 1 = ((432 ^ 2 + 1 : ℕ) : ZMod 1493) by
      push_cast
      ring]
    exact (ZMod.natCast_eq_zero_iff (432 ^ 2 + 1) 1493).mpr (by norm_num)
  have hb : (1061 : ZMod 1493) ^ 2 + 1 = 0 := by
    rw [show (1061 : ZMod 1493) ^ 2 + 1 = ((1061 ^ 2 + 1 : ℕ) : ZMod 1493) by
      push_cast
      ring]
    exact (ZMod.natCast_eq_zero_iff (1061 ^ 2 + 1) 1493).mpr (by norm_num)
  have hsum : (432 : ZMod 1493) + (1061 : ZMod 1493) = 0 := by
    rw [show (432 : ZMod 1493) + (1061 : ZMod 1493) = ((432 + 1061 : ℕ) : ZMod 1493) by
      push_cast
      ring]
    exact (ZMod.natCast_eq_zero_iff (432 + 1061) 1493).mpr (by norm_num)
  have hprod : (432 : ZMod 1493) * (1061 : ZMod 1493) = 1 := by
    rw [← Nat.cast_one]
    rw [show (432 : ZMod 1493) * (1061 : ZMod 1493) = ((432 * 1061 : ℕ) : ZMod 1493) by
      push_cast
      ring]
    exact (ZMod.natCast_eq_natCast_iff' (432 * 1061) 1 1493).mpr (by norm_num)
  have hroot : ∀ r : ZMod 1493, r ^ 2 + 1 = 0 ↔ r = (432 : ZMod 1493) ∨ r = (1061 : ZMod 1493) := by
    intro r
    constructor
    · intro h
      have hfac : (r - (432 : ZMod 1493)) * (r - (1061 : ZMod 1493)) = 0 := by
        have hid : (r - (432 : ZMod 1493)) * (r - (1061 : ZMod 1493)) = r ^ 2 + 1 := by
          calc (r - (432 : ZMod 1493)) * (r - (1061 : ZMod 1493))
              = r ^ 2 - ((432 : ZMod 1493) + (1061 : ZMod 1493)) * r
                  + (432 : ZMod 1493) * (1061 : ZMod 1493) := by ring
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
  rw [← ZMod.natCast_eq_zero_iff (n ^ 2 + 1) 1493, hcast, hroot (n : ZMod 1493)]
  constructor
  · rintro (h | h)
    · left
      have h' := (ZMod.natCast_eq_natCast_iff' n 432 1493).mp h
      rw [Nat.mod_eq_of_lt (by norm_num : 432 < 1493)] at h'
      exact h'
    · right
      have h' := (ZMod.natCast_eq_natCast_iff' n 1061 1493).mp h
      rw [Nat.mod_eq_of_lt (by norm_num : 1061 < 1493)] at h'
      exact h' 
  · rintro (h | h)
    · left
      exact (ZMod.natCast_eq_natCast_iff' n 432 1493).mpr (by
        rw [Nat.mod_eq_of_lt (by norm_num : 432 < 1493)]
        exact h)
    · right
      exact (ZMod.natCast_eq_natCast_iff' n 1061 1493).mpr (by
        rw [Nat.mod_eq_of_lt (by norm_num : 1061 < 1493)]
        exact h)
