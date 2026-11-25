import Mathlib

instance : Fact (Nat.Prime 281) := ⟨by norm_num⟩

theorem PEqualNP.Outside.L_quadratic_primes_cert_281 :
    ∀ n:ℕ, 281∣n^2+1 ↔ n%281=53 ∨ n%281=228 := by
  intro n
  have ha : (53:ZMod 281)^2 = -1 := by decide
  have key : ((n:ZMod 281)^2 + 1 = 0) ↔ ((n:ZMod 281) = 53 ∨ (n:ZMod 281) = -53) := by
    constructor
    · intro h
      have hsq : (n:ZMod 281)^2 - (53:ZMod 281)^2 = 0 := by rw [ha]; simpa using h
      have hfac : (n:ZMod 281)^2 - (53:ZMod 281)^2 = ((n:ZMod 281) - 53) * ((n:ZMod 281) + 53) := by ring
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
  have hmod : (n : ZMod 281) = ((n % 281 : ℕ) : ZMod 281) := by rw [ZMod.natCast_mod]
  rw [hmod]
  have hlt : n % 281 < 281 := Nat.mod_lt _ (by norm_num)
  constructor
  · rintro (h' | h')
    · have h2 : (n%281) % 281 = 53 % 281 := (ZMod.natCast_eq_natCast_iff (n%281) 53 281).mp h'
      rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (by norm_num : 53<281)] at h2
      exact Or.inl h2
    · have h3 : ((n % 281 : ℕ) : ZMod 281) = (228 : ZMod 281) := by
        rw [h']; decide
      have h2 : (n%281) % 281 = 228 % 281 := (ZMod.natCast_eq_natCast_iff (n%281) 228 281).mp h3
      rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (by norm_num : 228<281)] at h2
      exact Or.inr h2
  · rintro (h' | h')
    · left; rw [h']; decide
    · right; rw [h']; decide
