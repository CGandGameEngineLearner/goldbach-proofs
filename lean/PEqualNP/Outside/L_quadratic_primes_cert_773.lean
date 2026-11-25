import Mathlib

instance : Fact (Nat.Prime 773) := ⟨by norm_num⟩

theorem PEqualNP.Outside.L_quadratic_primes_cert_773 :
    ∀ n:ℕ, 773∣n^2+1 ↔ n%773=317 ∨ n%773=456 := by
  intro n
  have ha : (317:ZMod 773)^2 = -1 := by decide
  have key : ((n:ZMod 773)^2 + 1 = 0) ↔ ((n:ZMod 773) = 317 ∨ (n:ZMod 773) = -317) := by
    constructor
    · intro h
      have hsq : (n:ZMod 773)^2 - (317:ZMod 773)^2 = 0 := by rw [ha]; simpa using h
      have hfac : (n:ZMod 773)^2 - (317:ZMod 773)^2 = ((n:ZMod 773) - 317) * ((n:ZMod 773) + 317) := by ring
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
  have hmod : (n : ZMod 773) = ((n % 773 : ℕ) : ZMod 773) := by rw [ZMod.natCast_mod]
  rw [hmod]
  have hlt : n % 773 < 773 := Nat.mod_lt _ (by norm_num)
  constructor
  · rintro (h' | h')
    · have h2 : (n%773) % 773 = 317 % 773 := (ZMod.natCast_eq_natCast_iff (n%773) 317 773).mp h'
      rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (by norm_num : 317<773)] at h2
      exact Or.inl h2
    · have h3 : ((n % 773 : ℕ) : ZMod 773) = (456 : ZMod 773) := by
        rw [h']; decide
      have h2 : (n%773) % 773 = 456 % 773 := (ZMod.natCast_eq_natCast_iff (n%773) 456 773).mp h3
      rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (by norm_num : 456<773)] at h2
      exact Or.inr h2
  · rintro (h' | h')
    · left; rw [h']; decide
    · right; rw [h']; decide
