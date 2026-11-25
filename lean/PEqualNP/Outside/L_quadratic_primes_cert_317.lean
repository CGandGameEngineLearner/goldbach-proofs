import Mathlib

instance : Fact (Nat.Prime 317) := ⟨by norm_num⟩

theorem PEqualNP.Outside.L_quadratic_primes_cert_317 :
    ∀ n:ℕ, 317∣n^2+1 ↔ n%317=114 ∨ n%317=203 := by
  intro n
  have ha : (114:ZMod 317)^2 = -1 := by decide
  have key : ((n:ZMod 317)^2 + 1 = 0) ↔ ((n:ZMod 317) = 114 ∨ (n:ZMod 317) = -114) := by
    constructor
    · intro h
      have hsq : (n:ZMod 317)^2 - (114:ZMod 317)^2 = 0 := by rw [ha]; simpa using h
      have hfac : (n:ZMod 317)^2 - (114:ZMod 317)^2 = ((n:ZMod 317) - 114) * ((n:ZMod 317) + 114) := by ring
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
  have hmod : (n : ZMod 317) = ((n % 317 : ℕ) : ZMod 317) := by rw [ZMod.natCast_mod]
  rw [hmod]
  have hlt : n % 317 < 317 := Nat.mod_lt _ (by norm_num)
  constructor
  · rintro (h' | h')
    · have h2 : (n%317) % 317 = 114 % 317 := (ZMod.natCast_eq_natCast_iff (n%317) 114 317).mp h'
      rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (by norm_num : 114<317)] at h2
      exact Or.inl h2
    · have h3 : ((n % 317 : ℕ) : ZMod 317) = (203 : ZMod 317) := by
        rw [h']; decide
      have h2 : (n%317) % 317 = 203 % 317 := (ZMod.natCast_eq_natCast_iff (n%317) 203 317).mp h3
      rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (by norm_num : 203<317)] at h2
      exact Or.inr h2
  · rintro (h' | h')
    · left; rw [h']; decide
    · right; rw [h']; decide
