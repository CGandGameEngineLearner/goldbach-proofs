import Mathlib

instance : Fact (Nat.Prime 269) := ⟨by norm_num⟩

theorem PEqualNP.Outside.L_quadratic_primes_cert_269 :
    ∀ n:ℕ, 269∣n^2+1 ↔ n%269=82 ∨ n%269=187 := by
  intro n
  have ha : (82:ZMod 269)^2 = -1 := by decide
  have key : ((n:ZMod 269)^2 + 1 = 0) ↔ ((n:ZMod 269) = 82 ∨ (n:ZMod 269) = -82) := by
    constructor
    · intro h
      have hsq : (n:ZMod 269)^2 - (82:ZMod 269)^2 = 0 := by rw [ha]; simpa using h
      have hfac : (n:ZMod 269)^2 - (82:ZMod 269)^2 = ((n:ZMod 269) - 82) * ((n:ZMod 269) + 82) := by ring
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
  have hmod : (n : ZMod 269) = ((n % 269 : ℕ) : ZMod 269) := by rw [ZMod.natCast_mod]
  rw [hmod]
  have hlt : n % 269 < 269 := Nat.mod_lt _ (by norm_num)
  constructor
  · rintro (h' | h')
    · have h2 : (n%269) % 269 = 82 % 269 := (ZMod.natCast_eq_natCast_iff (n%269) 82 269).mp h'
      rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (by norm_num : 82<269)] at h2
      exact Or.inl h2
    · have h3 : ((n % 269 : ℕ) : ZMod 269) = (187 : ZMod 269) := by
        rw [h']; decide
      have h2 : (n%269) % 269 = 187 % 269 := (ZMod.natCast_eq_natCast_iff (n%269) 187 269).mp h3
      rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (by norm_num : 187<269)] at h2
      exact Or.inr h2
  · rintro (h' | h')
    · left; rw [h']; decide
    · right; rw [h']; decide
