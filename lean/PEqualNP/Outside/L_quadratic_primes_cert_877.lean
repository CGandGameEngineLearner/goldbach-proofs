import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_877 :
    ∀ n : ℕ, 877 ∣ n ^ 2 + 1 ↔ n % 877 = 151 ∨ n % 877 = 726 := by
  intro n
  haveI : Fact (877).Prime := ⟨by norm_num⟩
  have hcast : ((n ^ 2 + 1 : ℕ) : ZMod 877) = (n : ZMod 877) ^ 2 + 1 := by
    push_cast
    ring
  have ha : (151 : ZMod 877) ^ 2 + 1 = 0 := by
    rw [show (151 : ZMod 877) ^ 2 + 1 = ((151 ^ 2 + 1 : ℕ) : ZMod 877) by
      push_cast
      ring]
    exact (ZMod.natCast_eq_zero_iff (151 ^ 2 + 1) 877).mpr (by norm_num)
  have hb : (726 : ZMod 877) ^ 2 + 1 = 0 := by
    rw [show (726 : ZMod 877) ^ 2 + 1 = ((726 ^ 2 + 1 : ℕ) : ZMod 877) by
      push_cast
      ring]
    exact (ZMod.natCast_eq_zero_iff (726 ^ 2 + 1) 877).mpr (by norm_num)
  have hsum : (151 : ZMod 877) + (726 : ZMod 877) = 0 := by
    rw [show (151 : ZMod 877) + (726 : ZMod 877) = ((151 + 726 : ℕ) : ZMod 877) by
      push_cast
      ring]
    exact (ZMod.natCast_eq_zero_iff (151 + 726) 877).mpr (by norm_num)
  have hprod : (151 : ZMod 877) * (726 : ZMod 877) = 1 := by
    rw [← Nat.cast_one]
    rw [show (151 : ZMod 877) * (726 : ZMod 877) = ((151 * 726 : ℕ) : ZMod 877) by
      push_cast
      ring]
    exact (ZMod.natCast_eq_natCast_iff' (151 * 726) 1 877).mpr (by norm_num)
  have hroot : ∀ r : ZMod 877, r ^ 2 + 1 = 0 ↔ r = (151 : ZMod 877) ∨ r = (726 : ZMod 877) := by
    intro r
    constructor
    · intro h
      have hfac : (r - (151 : ZMod 877)) * (r - (726 : ZMod 877)) = 0 := by
        have hid : (r - (151 : ZMod 877)) * (r - (726 : ZMod 877)) = r ^ 2 + 1 := by
          calc (r - (151 : ZMod 877)) * (r - (726 : ZMod 877))
              = r ^ 2 - ((151 : ZMod 877) + (726 : ZMod 877)) * r
                  + (151 : ZMod 877) * (726 : ZMod 877) := by ring
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
  rw [← ZMod.natCast_eq_zero_iff (n ^ 2 + 1) 877, hcast, hroot (n : ZMod 877)]
  constructor
  · rintro (h | h)
    · left
      have h' := (ZMod.natCast_eq_natCast_iff' n 151 877).mp h
      rw [Nat.mod_eq_of_lt (by norm_num : 151 < 877)] at h'
      exact h'
    · right
      have h' := (ZMod.natCast_eq_natCast_iff' n 726 877).mp h
      rw [Nat.mod_eq_of_lt (by norm_num : 726 < 877)] at h'
      exact h' 
  · rintro (h | h)
    · left
      exact (ZMod.natCast_eq_natCast_iff' n 151 877).mpr (by
        rw [Nat.mod_eq_of_lt (by norm_num : 151 < 877)]
        exact h)
    · right
      exact (ZMod.natCast_eq_natCast_iff' n 726 877).mpr (by
        rw [Nat.mod_eq_of_lt (by norm_num : 726 < 877)]
        exact h)
