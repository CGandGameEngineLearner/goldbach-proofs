import Mathlib

instance : Fact (Nat.Prime 373) := ⟨by norm_num⟩

theorem PEqualNP.Outside.L_quadratic_primes_cert_373 :
    ∀ n:ℕ, 373∣n^2+1 ↔ n%373=104 ∨ n%373=269 := by
  intro n
  have ha : (104:ZMod 373)^2 = -1 := by decide
  have key : ((n:ZMod 373)^2 + 1 = 0) ↔ ((n:ZMod 373) = 104 ∨ (n:ZMod 373) = -104) := by
    constructor
    · intro h
      have hsq : (n:ZMod 373)^2 - (104:ZMod 373)^2 = 0 := by rw [ha]; simpa using h
      have hfac : (n:ZMod 373)^2 - (104:ZMod 373)^2 = ((n:ZMod 373) - 104) * ((n:ZMod 373) + 104) := by ring
      rw [hfac] at hsq
      rcases mul_eq_zero.mp hsq with h' | h'
      · exact Or.inl (sub_eq_zero.mp h')
      · exact Or.inr (eq_neg_of_add_eq_zero_left h')
    · rintro (h' | h')
      · rw [h']; linear_combination ha
      · rw [h']; linear_combination ha
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  rw [key]
  have hmod : (n : ZMod 373) = ((n % 373 : ℕ) : ZMod 373) := by rw [ZMod.natCast_mod]
  rw [hmod]
  have hlt : n % 373 < 373 := Nat.mod_lt _ (by norm_num)
  constructor
  · rintro (h' | h')
    · have h2 : (n%373) % 373 = 104 % 373 := (ZMod.natCast_eq_natCast_iff (n%373) 104 373).mp h'
      rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (by norm_num : 104<373)] at h2
      exact Or.inl h2
    · have h3 : ((n % 373 : ℕ) : ZMod 373) = (269 : ZMod 373) := by
        rw [h']; decide
      have h2 : (n%373) % 373 = 269 % 373 := (ZMod.natCast_eq_natCast_iff (n%373) 269 373).mp h3
      rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (by norm_num : 269<373)] at h2
      exact Or.inr h2
  · rintro (h' | h')
    · left; rw [h']; decide
    · right; rw [h']; decide
