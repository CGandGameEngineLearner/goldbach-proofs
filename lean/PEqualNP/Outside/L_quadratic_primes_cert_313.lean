import Mathlib

instance : Fact (Nat.Prime 313) := ⟨by norm_num⟩

theorem PEqualNP.Outside.L_quadratic_primes_cert_313 :
    ∀ n:ℕ, 313∣n^2+1 ↔ n%313=25 ∨ n%313=288 := by
  intro n
  have ha : (25:ZMod 313)^2 = -1 := by decide
  have key : ((n:ZMod 313)^2 + 1 = 0) ↔ ((n:ZMod 313) = 25 ∨ (n:ZMod 313) = -25) := by
    constructor
    · intro h
      have hsq : (n:ZMod 313)^2 - (25:ZMod 313)^2 = 0 := by rw [ha]; simpa using h
      have hfac : (n:ZMod 313)^2 - (25:ZMod 313)^2 = ((n:ZMod 313) - 25) * ((n:ZMod 313) + 25) := by ring
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
  have hmod : (n : ZMod 313) = ((n % 313 : ℕ) : ZMod 313) := by rw [ZMod.natCast_mod]
  rw [hmod]
  have hlt : n % 313 < 313 := Nat.mod_lt _ (by norm_num)
  constructor
  · rintro (h' | h')
    · have h2 : (n%313) % 313 = 25 % 313 := (ZMod.natCast_eq_natCast_iff (n%313) 25 313).mp h'
      rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (by norm_num : 25<313)] at h2
      exact Or.inl h2
    · have h3 : ((n % 313 : ℕ) : ZMod 313) = (288 : ZMod 313) := by
        rw [h']; decide
      have h2 : (n%313) % 313 = 288 % 313 := (ZMod.natCast_eq_natCast_iff (n%313) 288 313).mp h3
      rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (by norm_num : 288<313)] at h2
      exact Or.inr h2
  · rintro (h' | h')
    · left; rw [h']; decide
    · right; rw [h']; decide
