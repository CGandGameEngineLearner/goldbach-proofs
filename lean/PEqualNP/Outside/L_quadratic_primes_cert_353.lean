import Mathlib

instance : Fact (Nat.Prime 353) := ⟨by norm_num⟩

theorem PEqualNP.Outside.L_quadratic_primes_cert_353 :
    ∀ n:ℕ, 353∣n^2+1 ↔ n%353=42 ∨ n%353=311 := by
  intro n
  have ha : (42:ZMod 353)^2 = -1 := by decide
  have key : ((n:ZMod 353)^2 + 1 = 0) ↔ ((n:ZMod 353) = 42 ∨ (n:ZMod 353) = -42) := by
    constructor
    · intro h
      have hsq : (n:ZMod 353)^2 - (42:ZMod 353)^2 = 0 := by rw [ha]; simpa using h
      have hfac : (n:ZMod 353)^2 - (42:ZMod 353)^2 = ((n:ZMod 353) - 42) * ((n:ZMod 353) + 42) := by ring
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
  have hmod : (n : ZMod 353) = ((n % 353 : ℕ) : ZMod 353) := by rw [ZMod.natCast_mod]
  rw [hmod]
  have hlt : n % 353 < 353 := Nat.mod_lt _ (by norm_num)
  constructor
  · rintro (h' | h')
    · have h2 : (n%353) % 353 = 42 % 353 := (ZMod.natCast_eq_natCast_iff (n%353) 42 353).mp h'
      rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (by norm_num : 42<353)] at h2
      exact Or.inl h2
    · have h3 : ((n % 353 : ℕ) : ZMod 353) = (311 : ZMod 353) := by
        rw [h']; decide
      have h2 : (n%353) % 353 = 311 % 353 := (ZMod.natCast_eq_natCast_iff (n%353) 311 353).mp h3
      rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (by norm_num : 311<353)] at h2
      exact Or.inr h2
  · rintro (h' | h')
    · left; rw [h']; decide
    · right; rw [h']; decide
