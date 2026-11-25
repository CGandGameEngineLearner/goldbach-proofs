import Mathlib

instance : Fact (Nat.Prime 677) := ⟨by norm_num⟩

theorem PEqualNP.Outside.L_quadratic_primes_cert_677 :
    ∀ n:ℕ, 677∣n^2+1 ↔ n%677=26 ∨ n%677=651 := by
  intro n
  have ha : (26:ZMod 677)^2 = -1 := by decide
  have key : ((n:ZMod 677)^2 + 1 = 0) ↔ ((n:ZMod 677) = 26 ∨ (n:ZMod 677) = -26) := by
    constructor
    · intro h
      have hsq : (n:ZMod 677)^2 - (26:ZMod 677)^2 = 0 := by rw [ha]; simpa using h
      have hfac : (n:ZMod 677)^2 - (26:ZMod 677)^2 = ((n:ZMod 677) - 26) * ((n:ZMod 677) + 26) := by ring
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
  have hmod : (n : ZMod 677) = ((n % 677 : ℕ) : ZMod 677) := by rw [ZMod.natCast_mod]
  rw [hmod]
  have hlt : n % 677 < 677 := Nat.mod_lt _ (by norm_num)
  constructor
  · rintro (h' | h')
    · have h2 : (n%677) % 677 = 26 % 677 := (ZMod.natCast_eq_natCast_iff (n%677) 26 677).mp h'
      rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (by norm_num : 26<677)] at h2
      exact Or.inl h2
    · have h3 : ((n % 677 : ℕ) : ZMod 677) = (651 : ZMod 677) := by
        rw [h']; decide
      have h2 : (n%677) % 677 = 651 % 677 := (ZMod.natCast_eq_natCast_iff (n%677) 651 677).mp h3
      rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (by norm_num : 651<677)] at h2
      exact Or.inr h2
  · rintro (h' | h')
    · left; rw [h']; decide
    · right; rw [h']; decide
