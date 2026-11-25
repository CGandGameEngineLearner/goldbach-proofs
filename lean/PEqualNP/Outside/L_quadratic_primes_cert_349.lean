import Mathlib

instance : Fact (Nat.Prime 349) := ⟨by norm_num⟩

theorem PEqualNP.Outside.L_quadratic_primes_cert_349 :
    ∀ n:ℕ, 349∣n^2+1 ↔ n%349=136 ∨ n%349=213 := by
  intro n
  have ha : (136:ZMod 349)^2 = -1 := by decide
  have key : ((n:ZMod 349)^2 + 1 = 0) ↔ ((n:ZMod 349) = 136 ∨ (n:ZMod 349) = -136) := by
    constructor
    · intro h
      have hsq : (n:ZMod 349)^2 - (136:ZMod 349)^2 = 0 := by rw [ha]; simpa using h
      have hfac : (n:ZMod 349)^2 - (136:ZMod 349)^2 = ((n:ZMod 349) - 136) * ((n:ZMod 349) + 136) := by ring
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
  have hmod : (n : ZMod 349) = ((n % 349 : ℕ) : ZMod 349) := by rw [ZMod.natCast_mod]
  rw [hmod]
  have hlt : n % 349 < 349 := Nat.mod_lt _ (by norm_num)
  constructor
  · rintro (h' | h')
    · have h2 : (n%349) % 349 = 136 % 349 := (ZMod.natCast_eq_natCast_iff (n%349) 136 349).mp h'
      rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (by norm_num : 136<349)] at h2
      exact Or.inl h2
    · have h3 : ((n % 349 : ℕ) : ZMod 349) = (213 : ZMod 349) := by
        rw [h']; decide
      have h2 : (n%349) % 349 = 213 % 349 := (ZMod.natCast_eq_natCast_iff (n%349) 213 349).mp h3
      rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (by norm_num : 213<349)] at h2
      exact Or.inr h2
  · rintro (h' | h')
    · left; rw [h']; decide
    · right; rw [h']; decide
