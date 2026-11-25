import Mathlib

instance : Fact (Nat.Prime 541) := ⟨by norm_num⟩

theorem PEqualNP.Outside.L_quadratic_primes_cert_541 :
    ∀ n:ℕ, 541∣n^2+1 ↔ n%541=52 ∨ n%541=489 := by
  intro n
  have ha : (52:ZMod 541)^2 = -1 := by decide
  have key : ((n:ZMod 541)^2 + 1 = 0) ↔ ((n:ZMod 541) = 52 ∨ (n:ZMod 541) = -52) := by
    constructor
    · intro h
      have hsq : (n:ZMod 541)^2 - (52:ZMod 541)^2 = 0 := by rw [ha]; simpa using h
      have hfac : (n:ZMod 541)^2 - (52:ZMod 541)^2 = ((n:ZMod 541) - 52) * ((n:ZMod 541) + 52) := by ring
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
  have hmod : (n : ZMod 541) = ((n % 541 : ℕ) : ZMod 541) := by rw [ZMod.natCast_mod]
  rw [hmod]
  have hlt : n % 541 < 541 := Nat.mod_lt _ (by norm_num)
  constructor
  · rintro (h' | h')
    · have h2 : (n%541) % 541 = 52 % 541 := (ZMod.natCast_eq_natCast_iff (n%541) 52 541).mp h'
      rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (by norm_num : 52<541)] at h2
      exact Or.inl h2
    · have h3 : ((n % 541 : ℕ) : ZMod 541) = (489 : ZMod 541) := by
        rw [h']; decide
      have h2 : (n%541) % 541 = 489 % 541 := (ZMod.natCast_eq_natCast_iff (n%541) 489 541).mp h3
      rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (by norm_num : 489<541)] at h2
      exact Or.inr h2
  · rintro (h' | h')
    · left; rw [h']; decide
    · right; rw [h']; decide
