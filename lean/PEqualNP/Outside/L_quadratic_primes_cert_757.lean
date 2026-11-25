import Mathlib

instance : Fact (Nat.Prime 757) := ⟨by norm_num⟩

theorem PEqualNP.Outside.L_quadratic_primes_cert_757 :
    ∀ n:ℕ, 757∣n^2+1 ↔ n%757=87 ∨ n%757=670 := by
  intro n
  have ha : (87:ZMod 757)^2 = -1 := by decide
  have key : ((n:ZMod 757)^2 + 1 = 0) ↔ ((n:ZMod 757) = 87 ∨ (n:ZMod 757) = -87) := by
    constructor
    · intro h
      have hsq : (n:ZMod 757)^2 - (87:ZMod 757)^2 = 0 := by rw [ha]; simpa using h
      have hfac : (n:ZMod 757)^2 - (87:ZMod 757)^2 = ((n:ZMod 757) - 87) * ((n:ZMod 757) + 87) := by ring
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
  have hmod : (n : ZMod 757) = ((n % 757 : ℕ) : ZMod 757) := by rw [ZMod.natCast_mod]
  rw [hmod]
  have hlt : n % 757 < 757 := Nat.mod_lt _ (by norm_num)
  constructor
  · rintro (h' | h')
    · have h2 : (n%757) % 757 = 87 % 757 := (ZMod.natCast_eq_natCast_iff (n%757) 87 757).mp h'
      rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (by norm_num : 87<757)] at h2
      exact Or.inl h2
    · have h3 : ((n % 757 : ℕ) : ZMod 757) = (670 : ZMod 757) := by
        rw [h']; decide
      have h2 : (n%757) % 757 = 670 % 757 := (ZMod.natCast_eq_natCast_iff (n%757) 670 757).mp h3
      rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (by norm_num : 670<757)] at h2
      exact Or.inr h2
  · rintro (h' | h')
    · left; rw [h']; decide
    · right; rw [h']; decide
