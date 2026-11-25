import Mathlib

instance : Fact (Nat.Prime 257) := ⟨by norm_num⟩

theorem PEqualNP.Outside.L_quadratic_primes_cert_257 :
    ∀ n:ℕ, 257∣n^2+1 ↔ n%257=16 ∨ n%257=241 := by
  intro n
  have ha : (16:ZMod 257)^2 = -1 := by decide
  have key : ((n:ZMod 257)^2 + 1 = 0) ↔ ((n:ZMod 257) = 16 ∨ (n:ZMod 257) = -16) := by
    constructor
    · intro h
      have hsq : (n:ZMod 257)^2 - (16:ZMod 257)^2 = 0 := by rw [ha]; simpa using h
      have hfac : (n:ZMod 257)^2 - (16:ZMod 257)^2 = ((n:ZMod 257) - 16) * ((n:ZMod 257) + 16) := by ring
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
  have hmod : (n : ZMod 257) = ((n % 257 : ℕ) : ZMod 257) := by rw [ZMod.natCast_mod]
  rw [hmod]
  have hlt : n % 257 < 257 := Nat.mod_lt _ (by norm_num)
  constructor
  · rintro (h' | h')
    · have h2 : (n%257) % 257 = 16 % 257 := (ZMod.natCast_eq_natCast_iff (n%257) 16 257).mp h'
      rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (by norm_num : 16<257)] at h2
      exact Or.inl h2
    · have h3 : ((n % 257 : ℕ) : ZMod 257) = (241 : ZMod 257) := by
        rw [h']; decide
      have h2 : (n%257) % 257 = 241 % 257 := (ZMod.natCast_eq_natCast_iff (n%257) 241 257).mp h3
      rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (by norm_num : 241<257)] at h2
      exact Or.inr h2
  · rintro (h' | h')
    · left; rw [h']; decide
    · right; rw [h']; decide
