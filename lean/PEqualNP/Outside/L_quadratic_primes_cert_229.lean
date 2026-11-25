import Mathlib

instance : Fact (Nat.Prime 229) := ⟨by norm_num⟩

theorem PEqualNP.Outside.L_quadratic_primes_cert_229 :
    ∀ n:ℕ, 229∣n^2+1 ↔ n%229=107 ∨ n%229=122 := by
  intro n
  have ha : (107:ZMod 229)^2 = -1 := by decide
  have key : ((n:ZMod 229)^2 + 1 = 0) ↔ ((n:ZMod 229) = 107 ∨ (n:ZMod 229) = -107) := by
    constructor
    · intro h
      have hsq : (n:ZMod 229)^2 - (107:ZMod 229)^2 = 0 := by rw [ha]; simpa using h
      have hfac : (n:ZMod 229)^2 - (107:ZMod 229)^2 = ((n:ZMod 229) - 107) * ((n:ZMod 229) + 107) := by ring
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
  have hmod : (n : ZMod 229) = ((n % 229 : ℕ) : ZMod 229) := by rw [ZMod.natCast_mod]
  rw [hmod]
  have hlt : n % 229 < 229 := Nat.mod_lt _ (by norm_num)
  constructor
  · rintro (h' | h')
    · have h2 : (n%229) % 229 = 107 % 229 := (ZMod.natCast_eq_natCast_iff (n%229) 107 229).mp h'
      rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (by norm_num : 107<229)] at h2
      exact Or.inl h2
    · have h3 : ((n % 229 : ℕ) : ZMod 229) = (122 : ZMod 229) := by
        rw [h']; decide
      have h2 : (n%229) % 229 = 122 % 229 := (ZMod.natCast_eq_natCast_iff (n%229) 122 229).mp h3
      rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (by norm_num : 122<229)] at h2
      exact Or.inr h2
  · rintro (h' | h')
    · left; rw [h']; decide
    · right; rw [h']; decide
