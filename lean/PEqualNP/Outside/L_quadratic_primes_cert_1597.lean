import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_1597 :
    ∀ n : ℕ, 1597 ∣ n ^ 2 + 1 ↔ n % 1597 = 610 ∨ n % 1597 = 987 := by
  intro n
  haveI : Fact (1597).Prime := ⟨by norm_num⟩
  have hcast : ((n ^ 2 + 1 : ℕ) : ZMod 1597) = (n : ZMod 1597) ^ 2 + 1 := by
    push_cast
    ring
  have ha : (610 : ZMod 1597) ^ 2 + 1 = 0 := by
    rw [show (610 : ZMod 1597) ^ 2 + 1 = ((610 ^ 2 + 1 : ℕ) : ZMod 1597) by
      push_cast
      ring]
    exact (ZMod.natCast_eq_zero_iff (610 ^ 2 + 1) 1597).mpr (by norm_num)
  have hb : (987 : ZMod 1597) ^ 2 + 1 = 0 := by
    rw [show (987 : ZMod 1597) ^ 2 + 1 = ((987 ^ 2 + 1 : ℕ) : ZMod 1597) by
      push_cast
      ring]
    exact (ZMod.natCast_eq_zero_iff (987 ^ 2 + 1) 1597).mpr (by norm_num)
  have hsum : (610 : ZMod 1597) + (987 : ZMod 1597) = 0 := by
    rw [show (610 : ZMod 1597) + (987 : ZMod 1597) = ((610 + 987 : ℕ) : ZMod 1597) by
      push_cast
      ring]
    exact (ZMod.natCast_eq_zero_iff (610 + 987) 1597).mpr (by norm_num)
  have hprod : (610 : ZMod 1597) * (987 : ZMod 1597) = 1 := by
    rw [← Nat.cast_one]
    rw [show (610 : ZMod 1597) * (987 : ZMod 1597) = ((610 * 987 : ℕ) : ZMod 1597) by
      push_cast
      ring]
    exact (ZMod.natCast_eq_natCast_iff' (610 * 987) 1 1597).mpr (by norm_num)
  have hroot : ∀ r : ZMod 1597, r ^ 2 + 1 = 0 ↔ r = (610 : ZMod 1597) ∨ r = (987 : ZMod 1597) := by
    intro r
    constructor
    · intro h
      have hfac : (r - (610 : ZMod 1597)) * (r - (987 : ZMod 1597)) = 0 := by
        have hid : (r - (610 : ZMod 1597)) * (r - (987 : ZMod 1597)) = r ^ 2 + 1 := by
          calc (r - (610 : ZMod 1597)) * (r - (987 : ZMod 1597))
              = r ^ 2 - ((610 : ZMod 1597) + (987 : ZMod 1597)) * r
                  + (610 : ZMod 1597) * (987 : ZMod 1597) := by ring
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
  rw [← ZMod.natCast_eq_zero_iff (n ^ 2 + 1) 1597, hcast, hroot (n : ZMod 1597)]
  constructor
  · rintro (h | h)
    · left
      have h' := (ZMod.natCast_eq_natCast_iff' n 610 1597).mp h
      rw [Nat.mod_eq_of_lt (by norm_num : 610 < 1597)] at h'
      exact h'
    · right
      have h' := (ZMod.natCast_eq_natCast_iff' n 987 1597).mp h
      rw [Nat.mod_eq_of_lt (by norm_num : 987 < 1597)] at h'
      exact h' 
  · rintro (h | h)
    · left
      exact (ZMod.natCast_eq_natCast_iff' n 610 1597).mpr (by
        rw [Nat.mod_eq_of_lt (by norm_num : 610 < 1597)]
        exact h)
    · right
      exact (ZMod.natCast_eq_natCast_iff' n 987 1597).mpr (by
        rw [Nat.mod_eq_of_lt (by norm_num : 987 < 1597)]
        exact h)
