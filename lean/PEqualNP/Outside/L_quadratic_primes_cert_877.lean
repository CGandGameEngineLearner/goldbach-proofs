import Mathlib

instance : Fact (Nat.Prime 877) := ⟨by norm_num⟩

theorem PEqualNP.Outside.L_quadratic_primes_cert_877 :
    ∀ n:ℕ, 877∣n^2+1 ↔ n%877=151 ∨ n%877=726 := by
  intro n
  have ha : (151:ZMod 877)^2 = -1 := by decide
  have key : ((n:ZMod 877)^2 + 1 = 0) ↔ ((n:ZMod 877) = 151 ∨ (n:ZMod 877) = -151) := by
    constructor
    · intro h
      have hsq : (n:ZMod 877)^2 - (151:ZMod 877)^2 = 0 := by rw [ha]; simpa using h
      have hfac : (n:ZMod 877)^2 - (151:ZMod 877)^2 = ((n:ZMod 877) - 151) * ((n:ZMod 877) + 151) := by ring
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
  have hmod : (n : ZMod 877) = ((n % 877 : ℕ) : ZMod 877) := by rw [ZMod.natCast_mod]
  rw [hmod]
  have hlt : n % 877 < 877 := Nat.mod_lt _ (by norm_num)
  constructor
  · rintro (h' | h')
    · have h2 : (n%877) % 877 = 151 % 877 := (ZMod.natCast_eq_natCast_iff (n%877) 151 877).mp h'
      rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (by norm_num : 151<877)] at h2
      exact Or.inl h2
    · have h3 : ((n % 877 : ℕ) : ZMod 877) = (726 : ZMod 877) := by
        rw [h']; decide
      have h2 : (n%877) % 877 = 726 % 877 := (ZMod.natCast_eq_natCast_iff (n%877) 726 877).mp h3
      rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (by norm_num : 726<877)] at h2
      exact Or.inr h2
  · rintro (h' | h')
    · left; rw [h']; decide
    · right; rw [h']; decide
