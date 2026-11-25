import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_1373 :
    ∀ n : ℕ, 1373 ∣ n ^ 2 + 1 ↔ n % 1373 = 668 ∨ n % 1373 = 705 := by
  intro n
  haveI : Fact (1373).Prime := ⟨by norm_num⟩
  have hcast : ((n ^ 2 + 1 : ℕ) : ZMod 1373) = (n : ZMod 1373) ^ 2 + 1 := by
    push_cast
    ring
  have ha : (668 : ZMod 1373) ^ 2 + 1 = 0 := by
    rw [show (668 : ZMod 1373) ^ 2 + 1 = ((668 ^ 2 + 1 : ℕ) : ZMod 1373) by
      push_cast
      ring]
    exact (ZMod.natCast_eq_zero_iff (668 ^ 2 + 1) 1373).mpr (by norm_num)
  have hb : (705 : ZMod 1373) ^ 2 + 1 = 0 := by
    rw [show (705 : ZMod 1373) ^ 2 + 1 = ((705 ^ 2 + 1 : ℕ) : ZMod 1373) by
      push_cast
      ring]
    exact (ZMod.natCast_eq_zero_iff (705 ^ 2 + 1) 1373).mpr (by norm_num)
  have hsum : (668 : ZMod 1373) + (705 : ZMod 1373) = 0 := by
    rw [show (668 : ZMod 1373) + (705 : ZMod 1373) = ((668 + 705 : ℕ) : ZMod 1373) by
      push_cast
      ring]
    exact (ZMod.natCast_eq_zero_iff (668 + 705) 1373).mpr (by norm_num)
  have hprod : (668 : ZMod 1373) * (705 : ZMod 1373) = 1 := by
    rw [← Nat.cast_one]
    rw [show (668 : ZMod 1373) * (705 : ZMod 1373) = ((668 * 705 : ℕ) : ZMod 1373) by
      push_cast
      ring]
    exact (ZMod.natCast_eq_natCast_iff' (668 * 705) 1 1373).mpr (by norm_num)
  have hroot : ∀ r : ZMod 1373, r ^ 2 + 1 = 0 ↔ r = (668 : ZMod 1373) ∨ r = (705 : ZMod 1373) := by
    intro r
    constructor
    · intro h
      have hfac : (r - (668 : ZMod 1373)) * (r - (705 : ZMod 1373)) = 0 := by
        have hid : (r - (668 : ZMod 1373)) * (r - (705 : ZMod 1373)) = r ^ 2 + 1 := by
          calc (r - (668 : ZMod 1373)) * (r - (705 : ZMod 1373))
              = r ^ 2 - ((668 : ZMod 1373) + (705 : ZMod 1373)) * r
                  + (668 : ZMod 1373) * (705 : ZMod 1373) := by ring
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
  rw [← ZMod.natCast_eq_zero_iff (n ^ 2 + 1) 1373, hcast, hroot (n : ZMod 1373)]
  constructor
  · rintro (h | h)
    · left
      have h' := (ZMod.natCast_eq_natCast_iff' n 668 1373).mp h
      rw [Nat.mod_eq_of_lt (by norm_num : 668 < 1373)] at h'
      exact h'
    · right
      have h' := (ZMod.natCast_eq_natCast_iff' n 705 1373).mp h
      rw [Nat.mod_eq_of_lt (by norm_num : 705 < 1373)] at h'
      exact h' 
  · rintro (h | h)
    · left
      exact (ZMod.natCast_eq_natCast_iff' n 668 1373).mpr (by
        rw [Nat.mod_eq_of_lt (by norm_num : 668 < 1373)]
        exact h)
    · right
      exact (ZMod.natCast_eq_natCast_iff' n 705 1373).mpr (by
        rw [Nat.mod_eq_of_lt (by norm_num : 705 < 1373)]
        exact h)
