import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_1229 :
    ∀ n : ℕ, 1229 ∣ n ^ 2 + 1 ↔ n % 1229 = 597 ∨ n % 1229 = 632 := by
  intro n
  haveI : Fact (1229).Prime := ⟨by norm_num⟩
  have hcast : ((n ^ 2 + 1 : ℕ) : ZMod 1229) = (n : ZMod 1229) ^ 2 + 1 := by
    push_cast
    ring
  have ha : (597 : ZMod 1229) ^ 2 + 1 = 0 := by
    rw [show (597 : ZMod 1229) ^ 2 + 1 = ((597 ^ 2 + 1 : ℕ) : ZMod 1229) by
      push_cast
      ring]
    exact (ZMod.natCast_eq_zero_iff (597 ^ 2 + 1) 1229).mpr (by norm_num)
  have hb : (632 : ZMod 1229) ^ 2 + 1 = 0 := by
    rw [show (632 : ZMod 1229) ^ 2 + 1 = ((632 ^ 2 + 1 : ℕ) : ZMod 1229) by
      push_cast
      ring]
    exact (ZMod.natCast_eq_zero_iff (632 ^ 2 + 1) 1229).mpr (by norm_num)
  have hsum : (597 : ZMod 1229) + (632 : ZMod 1229) = 0 := by
    rw [show (597 : ZMod 1229) + (632 : ZMod 1229) = ((597 + 632 : ℕ) : ZMod 1229) by
      push_cast
      ring]
    exact (ZMod.natCast_eq_zero_iff (597 + 632) 1229).mpr (by norm_num)
  have hprod : (597 : ZMod 1229) * (632 : ZMod 1229) = 1 := by
    rw [← Nat.cast_one]
    rw [show (597 : ZMod 1229) * (632 : ZMod 1229) = ((597 * 632 : ℕ) : ZMod 1229) by
      push_cast
      ring]
    exact (ZMod.natCast_eq_natCast_iff' (597 * 632) 1 1229).mpr (by norm_num)
  have hroot : ∀ r : ZMod 1229, r ^ 2 + 1 = 0 ↔ r = (597 : ZMod 1229) ∨ r = (632 : ZMod 1229) := by
    intro r
    constructor
    · intro h
      have hfac : (r - (597 : ZMod 1229)) * (r - (632 : ZMod 1229)) = 0 := by
        have hid : (r - (597 : ZMod 1229)) * (r - (632 : ZMod 1229)) = r ^ 2 + 1 := by
          calc (r - (597 : ZMod 1229)) * (r - (632 : ZMod 1229))
              = r ^ 2 - ((597 : ZMod 1229) + (632 : ZMod 1229)) * r
                  + (597 : ZMod 1229) * (632 : ZMod 1229) := by ring
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
  rw [← ZMod.natCast_eq_zero_iff (n ^ 2 + 1) 1229, hcast, hroot (n : ZMod 1229)]
  constructor
  · rintro (h | h)
    · left
      have h' := (ZMod.natCast_eq_natCast_iff' n 597 1229).mp h
      rw [Nat.mod_eq_of_lt (by norm_num : 597 < 1229)] at h'
      exact h'
    · right
      have h' := (ZMod.natCast_eq_natCast_iff' n 632 1229).mp h
      rw [Nat.mod_eq_of_lt (by norm_num : 632 < 1229)] at h'
      exact h' 
  · rintro (h | h)
    · left
      exact (ZMod.natCast_eq_natCast_iff' n 597 1229).mpr (by
        rw [Nat.mod_eq_of_lt (by norm_num : 597 < 1229)]
        exact h)
    · right
      exact (ZMod.natCast_eq_natCast_iff' n 632 1229).mpr (by
        rw [Nat.mod_eq_of_lt (by norm_num : 632 < 1229)]
        exact h)
