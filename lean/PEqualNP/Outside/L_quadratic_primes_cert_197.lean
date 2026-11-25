import Mathlib

instance : Fact (Nat.Prime 197) := ⟨by norm_num⟩

theorem PEqualNP.Outside.L_quadratic_primes_cert_197 :
    ∀ n:ℕ, 197∣n^2+1 ↔ n%197=14 ∨ n%197=183 := by
  intro n
  have ha : (14:ZMod 197)^2 = -1 := by decide
  have key : ((n:ZMod 197)^2 + 1 = 0) ↔ ((n:ZMod 197) = 14 ∨ (n:ZMod 197) = -14) := by
    constructor
    · intro h
      have hsq : (n:ZMod 197)^2 - (14:ZMod 197)^2 = 0 := by rw [ha]; simpa using h
      have hfac : (n:ZMod 197)^2 - (14:ZMod 197)^2 = ((n:ZMod 197) - 14) * ((n:ZMod 197) + 14) := by ring
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
  have hmod : (n : ZMod 197) = ((n % 197 : ℕ) : ZMod 197) := by rw [ZMod.natCast_mod]
  rw [hmod]
  have hlt : n % 197 < 197 := Nat.mod_lt _ (by norm_num)
  constructor
  · rintro (h' | h')
    · have h2 : (n%197) % 197 = 14 % 197 := (ZMod.natCast_eq_natCast_iff (n%197) 14 197).mp h'
      rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (by norm_num : 14<197)] at h2
      exact Or.inl h2
    · have h3 : ((n % 197 : ℕ) : ZMod 197) = (183 : ZMod 197) := by
        rw [h']; decide
      have h2 : (n%197) % 197 = 183 % 197 := (ZMod.natCast_eq_natCast_iff (n%197) 183 197).mp h3
      rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (by norm_num : 183<197)] at h2
      exact Or.inr h2
  · rintro (h' | h')
    · left; rw [h']; decide
    · right; rw [h']; decide
