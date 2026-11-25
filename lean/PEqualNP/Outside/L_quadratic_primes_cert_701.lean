import Mathlib

instance : Fact (Nat.Prime 701) := ⟨by norm_num⟩

theorem PEqualNP.Outside.L_quadratic_primes_cert_701 :
    ∀ n:ℕ, 701∣n^2+1 ↔ n%701=135 ∨ n%701=566 := by
  intro n
  have ha : (135:ZMod 701)^2 = -1 := by decide
  have key : ((n:ZMod 701)^2 + 1 = 0) ↔ ((n:ZMod 701) = 135 ∨ (n:ZMod 701) = -135) := by
    constructor
    · intro h
      have hsq : (n:ZMod 701)^2 - (135:ZMod 701)^2 = 0 := by rw [ha]; simpa using h
      have hfac : (n:ZMod 701)^2 - (135:ZMod 701)^2 = ((n:ZMod 701) - 135) * ((n:ZMod 701) + 135) := by ring
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
  have hmod : (n : ZMod 701) = ((n % 701 : ℕ) : ZMod 701) := by rw [ZMod.natCast_mod]
  rw [hmod]
  have hlt : n % 701 < 701 := Nat.mod_lt _ (by norm_num)
  constructor
  · rintro (h' | h')
    · have h2 : (n%701) % 701 = 135 % 701 := (ZMod.natCast_eq_natCast_iff (n%701) 135 701).mp h'
      rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (by norm_num : 135<701)] at h2
      exact Or.inl h2
    · have h3 : ((n % 701 : ℕ) : ZMod 701) = (566 : ZMod 701) := by
        rw [h']; decide
      have h2 : (n%701) % 701 = 566 % 701 := (ZMod.natCast_eq_natCast_iff (n%701) 566 701).mp h3
      rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (by norm_num : 566<701)] at h2
      exact Or.inr h2
  · rintro (h' | h')
    · left; rw [h']; decide
    · right; rw [h']; decide
