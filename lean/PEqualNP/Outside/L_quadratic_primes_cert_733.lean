import Mathlib

instance : Fact (Nat.Prime 733) := ⟨by norm_num⟩

theorem PEqualNP.Outside.L_quadratic_primes_cert_733 :
    ∀ n:ℕ, 733∣n^2+1 ↔ n%733=353 ∨ n%733=380 := by
  intro n
  have ha : (353:ZMod 733)^2 = -1 := by decide
  have key : ((n:ZMod 733)^2 + 1 = 0) ↔ ((n:ZMod 733) = 353 ∨ (n:ZMod 733) = -353) := by
    constructor
    · intro h
      have hsq : (n:ZMod 733)^2 - (353:ZMod 733)^2 = 0 := by rw [ha]; simpa using h
      have hfac : (n:ZMod 733)^2 - (353:ZMod 733)^2 = ((n:ZMod 733) - 353) * ((n:ZMod 733) + 353) := by ring
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
  have hmod : (n : ZMod 733) = ((n % 733 : ℕ) : ZMod 733) := by rw [ZMod.natCast_mod]
  rw [hmod]
  have hlt : n % 733 < 733 := Nat.mod_lt _ (by norm_num)
  constructor
  · rintro (h' | h')
    · have h2 : (n%733) % 733 = 353 % 733 := (ZMod.natCast_eq_natCast_iff (n%733) 353 733).mp h'
      rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (by norm_num : 353<733)] at h2
      exact Or.inl h2
    · have h3 : ((n % 733 : ℕ) : ZMod 733) = (380 : ZMod 733) := by
        rw [h']; decide
      have h2 : (n%733) % 733 = 380 % 733 := (ZMod.natCast_eq_natCast_iff (n%733) 380 733).mp h3
      rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (by norm_num : 380<733)] at h2
      exact Or.inr h2
  · rintro (h' | h')
    · left; rw [h']; decide
    · right; rw [h']; decide
