import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_1453 :
    ∀ n : ℕ, 1453 ∣ n ^ 2 + 1 ↔ n % 1453 = 497 ∨ n % 1453 = 956 := by
  intro n
  haveI : Fact (1453).Prime := ⟨by norm_num⟩
  have hcast : ((n ^ 2 + 1 : ℕ) : ZMod 1453) = (n : ZMod 1453) ^ 2 + 1 := by
    push_cast
    ring
  have ha : (497 : ZMod 1453) ^ 2 + 1 = 0 := by
    rw [show (497 : ZMod 1453) ^ 2 + 1 = ((497 ^ 2 + 1 : ℕ) : ZMod 1453) by
      push_cast
      ring]
    exact (ZMod.natCast_eq_zero_iff (497 ^ 2 + 1) 1453).mpr (by norm_num)
  have hb : (956 : ZMod 1453) ^ 2 + 1 = 0 := by
    rw [show (956 : ZMod 1453) ^ 2 + 1 = ((956 ^ 2 + 1 : ℕ) : ZMod 1453) by
      push_cast
      ring]
    exact (ZMod.natCast_eq_zero_iff (956 ^ 2 + 1) 1453).mpr (by norm_num)
  have hsum : (497 : ZMod 1453) + (956 : ZMod 1453) = 0 := by
    rw [show (497 : ZMod 1453) + (956 : ZMod 1453) = ((497 + 956 : ℕ) : ZMod 1453) by
      push_cast
      ring]
    exact (ZMod.natCast_eq_zero_iff (497 + 956) 1453).mpr (by norm_num)
  have hprod : (497 : ZMod 1453) * (956 : ZMod 1453) = 1 := by
    rw [← Nat.cast_one]
    rw [show (497 : ZMod 1453) * (956 : ZMod 1453) = ((497 * 956 : ℕ) : ZMod 1453) by
      push_cast
      ring]
    exact (ZMod.natCast_eq_natCast_iff' (497 * 956) 1 1453).mpr (by norm_num)
  have hroot : ∀ r : ZMod 1453, r ^ 2 + 1 = 0 ↔ r = (497 : ZMod 1453) ∨ r = (956 : ZMod 1453) := by
    intro r
    constructor
    · intro h
      have hfac : (r - (497 : ZMod 1453)) * (r - (956 : ZMod 1453)) = 0 := by
        have hid : (r - (497 : ZMod 1453)) * (r - (956 : ZMod 1453)) = r ^ 2 + 1 := by
          calc (r - (497 : ZMod 1453)) * (r - (956 : ZMod 1453))
              = r ^ 2 - ((497 : ZMod 1453) + (956 : ZMod 1453)) * r
                  + (497 : ZMod 1453) * (956 : ZMod 1453) := by ring
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
  rw [← ZMod.natCast_eq_zero_iff (n ^ 2 + 1) 1453, hcast, hroot (n : ZMod 1453)]
  constructor
  · rintro (h | h)
    · left
      have h' := (ZMod.natCast_eq_natCast_iff' n 497 1453).mp h
      rw [Nat.mod_eq_of_lt (by norm_num : 497 < 1453)] at h'
      exact h'
    · right
      have h' := (ZMod.natCast_eq_natCast_iff' n 956 1453).mp h
      rw [Nat.mod_eq_of_lt (by norm_num : 956 < 1453)] at h'
      exact h' 
  · rintro (h | h)
    · left
      exact (ZMod.natCast_eq_natCast_iff' n 497 1453).mpr (by
        rw [Nat.mod_eq_of_lt (by norm_num : 497 < 1453)]
        exact h)
    · right
      exact (ZMod.natCast_eq_natCast_iff' n 956 1453).mpr (by
        rw [Nat.mod_eq_of_lt (by norm_num : 956 < 1453)]
        exact h)
