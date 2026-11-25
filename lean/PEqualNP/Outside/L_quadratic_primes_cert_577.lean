import Mathlib

instance : Fact (Nat.Prime 577) := ⟨by norm_num⟩

theorem PEqualNP.Outside.L_quadratic_primes_cert_577 :
    ∀ n:ℕ, 577∣n^2+1 ↔ n%577=24 ∨ n%577=553 := by
  intro n
  have ha : (24:ZMod 577)^2 = -1 := by decide
  have key : ((n:ZMod 577)^2 + 1 = 0) ↔ ((n:ZMod 577) = 24 ∨ (n:ZMod 577) = -24) := by
    constructor
    · intro h
      have hsq : (n:ZMod 577)^2 - (24:ZMod 577)^2 = 0 := by rw [ha]; simpa using h
      have hfac : (n:ZMod 577)^2 - (24:ZMod 577)^2 = ((n:ZMod 577) - 24) * ((n:ZMod 577) + 24) := by ring
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
  have hmod : (n : ZMod 577) = ((n % 577 : ℕ) : ZMod 577) := by rw [ZMod.natCast_mod]
  rw [hmod]
  have hlt : n % 577 < 577 := Nat.mod_lt _ (by norm_num)
  constructor
  · rintro (h' | h')
    · have h2 : (n%577) % 577 = 24 % 577 := (ZMod.natCast_eq_natCast_iff (n%577) 24 577).mp h'
      rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (by norm_num : 24<577)] at h2
      exact Or.inl h2
    · have h3 : ((n % 577 : ℕ) : ZMod 577) = (553 : ZMod 577) := by
        rw [h']; decide
      have h2 : (n%577) % 577 = 553 % 577 := (ZMod.natCast_eq_natCast_iff (n%577) 553 577).mp h3
      rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (by norm_num : 553<577)] at h2
      exact Or.inr h2
  · rintro (h' | h')
    · left; rw [h']; decide
    · right; rw [h']; decide
