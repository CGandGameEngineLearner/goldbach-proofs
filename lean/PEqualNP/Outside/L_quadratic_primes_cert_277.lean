import Mathlib

instance : Fact (Nat.Prime 277) := ⟨by norm_num⟩

theorem PEqualNP.Outside.L_quadratic_primes_cert_277 :
    ∀ n:ℕ, 277∣n^2+1 ↔ n%277=60 ∨ n%277=217 := by
  intro n
  have ha : (60:ZMod 277)^2 = -1 := by decide
  have key : ((n:ZMod 277)^2 + 1 = 0) ↔ ((n:ZMod 277) = 60 ∨ (n:ZMod 277) = -60) := by
    constructor
    · intro h
      have hsq : (n:ZMod 277)^2 - (60:ZMod 277)^2 = 0 := by rw [ha]; simpa using h
      have hfac : (n:ZMod 277)^2 - (60:ZMod 277)^2 = ((n:ZMod 277) - 60) * ((n:ZMod 277) + 60) := by ring
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
  have hmod : (n : ZMod 277) = ((n % 277 : ℕ) : ZMod 277) := by rw [ZMod.natCast_mod]
  rw [hmod]
  have hlt : n % 277 < 277 := Nat.mod_lt _ (by norm_num)
  constructor
  · rintro (h' | h')
    · have h2 : (n%277) % 277 = 60 % 277 := (ZMod.natCast_eq_natCast_iff (n%277) 60 277).mp h'
      rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (by norm_num : 60<277)] at h2
      exact Or.inl h2
    · have h3 : ((n % 277 : ℕ) : ZMod 277) = (217 : ZMod 277) := by
        rw [h']; decide
      have h2 : (n%277) % 277 = 217 % 277 := (ZMod.natCast_eq_natCast_iff (n%277) 217 277).mp h3
      rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (by norm_num : 217<277)] at h2
      exact Or.inr h2
  · rintro (h' | h')
    · left; rw [h']; decide
    · right; rw [h']; decide
