import Mathlib

instance : Fact (Nat.Prime 769) := ⟨by norm_num⟩

theorem PEqualNP.Outside.L_quadratic_primes_cert_769 :
    ∀ n:ℕ, 769∣n^2+1 ↔ n%769=62 ∨ n%769=707 := by
  intro n
  have ha : (62:ZMod 769)^2 = -1 := by decide
  have key : ((n:ZMod 769)^2 + 1 = 0) ↔ ((n:ZMod 769) = 62 ∨ (n:ZMod 769) = -62) := by
    constructor
    · intro h
      have hsq : (n:ZMod 769)^2 - (62:ZMod 769)^2 = 0 := by rw [ha]; simpa using h
      have hfac : (n:ZMod 769)^2 - (62:ZMod 769)^2 = ((n:ZMod 769) - 62) * ((n:ZMod 769) + 62) := by ring
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
  have hmod : (n : ZMod 769) = ((n % 769 : ℕ) : ZMod 769) := by rw [ZMod.natCast_mod]
  rw [hmod]
  have hlt : n % 769 < 769 := Nat.mod_lt _ (by norm_num)
  constructor
  · rintro (h' | h')
    · have h2 : (n%769) % 769 = 62 % 769 := (ZMod.natCast_eq_natCast_iff (n%769) 62 769).mp h'
      rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (by norm_num : 62<769)] at h2
      exact Or.inl h2
    · have h3 : ((n % 769 : ℕ) : ZMod 769) = (707 : ZMod 769) := by
        rw [h']; decide
      have h2 : (n%769) % 769 = 707 % 769 := (ZMod.natCast_eq_natCast_iff (n%769) 707 769).mp h3
      rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (by norm_num : 707<769)] at h2
      exact Or.inr h2
  · rintro (h' | h')
    · left; rw [h']; decide
    · right; rw [h']; decide
