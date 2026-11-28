import Mathlib

instance : Fact (Nat.Prime 809) := ⟨by norm_num⟩

theorem PEqualNP.Outside.L_quadratic_primes_cert_809 :
    ∀ n:ℕ, 809∣n^2+1 ↔ n%809=318 ∨ n%809=491 := by
  intro n
  have ha : (318:ZMod 809)^2 = -1 := by decide
  have key : ((n:ZMod 809)^2 + 1 = 0) ↔ ((n:ZMod 809) = 318 ∨ (n:ZMod 809) = -318) := by
    constructor
    · intro h
      have hsq : (n:ZMod 809)^2 - (318:ZMod 809)^2 = 0 := by rw [ha]; simpa using h
      have hfac : (n:ZMod 809)^2 - (318:ZMod 809)^2 = ((n:ZMod 809) - 318) * ((n:ZMod 809) + 318) := by ring
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
  have hmod : (n : ZMod 809) = ((n % 809 : ℕ) : ZMod 809) := by rw [ZMod.natCast_mod]
  rw [hmod]
  have hlt : n % 809 < 809 := Nat.mod_lt _ (by norm_num)
  constructor
  · rintro (h' | h')
    · have h2 : (n%809) % 809 = 318 % 809 := (ZMod.natCast_eq_natCast_iff (n%809) 318 809).mp h'
      rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (by norm_num : 318<809)] at h2
      exact Or.inl h2
    · have h3 : ((n % 809 : ℕ) : ZMod 809) = (491 : ZMod 809) := by
        rw [h']; decide
      have h2 : (n%809) % 809 = 491 % 809 := (ZMod.natCast_eq_natCast_iff (n%809) 491 809).mp h3
      rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (by norm_num : 491<809)] at h2
      exact Or.inr h2
  · rintro (h' | h')
    · left; rw [h']; decide
    · right; rw [h']; decide
