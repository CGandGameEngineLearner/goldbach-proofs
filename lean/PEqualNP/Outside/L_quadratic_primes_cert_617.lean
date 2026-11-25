import Mathlib

instance : Fact (Nat.Prime 617) := ⟨by norm_num⟩

theorem PEqualNP.Outside.L_quadratic_primes_cert_617 :
    ∀ n:ℕ, 617∣n^2+1 ↔ n%617=194 ∨ n%617=423 := by
  intro n
  have ha : (194:ZMod 617)^2 = -1 := by decide
  have key : ((n:ZMod 617)^2 + 1 = 0) ↔ ((n:ZMod 617) = 194 ∨ (n:ZMod 617) = -194) := by
    constructor
    · intro h
      have hsq : (n:ZMod 617)^2 - (194:ZMod 617)^2 = 0 := by rw [ha]; simpa using h
      have hfac : (n:ZMod 617)^2 - (194:ZMod 617)^2 = ((n:ZMod 617) - 194) * ((n:ZMod 617) + 194) := by ring
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
  have hmod : (n : ZMod 617) = ((n % 617 : ℕ) : ZMod 617) := by rw [ZMod.natCast_mod]
  rw [hmod]
  have hlt : n % 617 < 617 := Nat.mod_lt _ (by norm_num)
  constructor
  · rintro (h' | h')
    · have h2 : (n%617) % 617 = 194 % 617 := (ZMod.natCast_eq_natCast_iff (n%617) 194 617).mp h'
      rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (by norm_num : 194<617)] at h2
      exact Or.inl h2
    · have h3 : ((n % 617 : ℕ) : ZMod 617) = (423 : ZMod 617) := by
        rw [h']; decide
      have h2 : (n%617) % 617 = 423 % 617 := (ZMod.natCast_eq_natCast_iff (n%617) 423 617).mp h3
      rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (by norm_num : 423<617)] at h2
      exact Or.inr h2
  · rintro (h' | h')
    · left; rw [h']; decide
    · right; rw [h']; decide
