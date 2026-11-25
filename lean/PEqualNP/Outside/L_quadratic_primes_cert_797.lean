import Mathlib

instance : Fact (Nat.Prime 797) := ⟨by norm_num⟩

theorem PEqualNP.Outside.L_quadratic_primes_cert_797 :
    ∀ n:ℕ, 797∣n^2+1 ↔ n%797=215 ∨ n%797=582 := by
  intro n
  have ha : (215:ZMod 797)^2 = -1 := by decide
  have key : ((n:ZMod 797)^2 + 1 = 0) ↔ ((n:ZMod 797) = 215 ∨ (n:ZMod 797) = -215) := by
    constructor
    · intro h
      have hsq : (n:ZMod 797)^2 - (215:ZMod 797)^2 = 0 := by rw [ha]; simpa using h
      have hfac : (n:ZMod 797)^2 - (215:ZMod 797)^2 = ((n:ZMod 797) - 215) * ((n:ZMod 797) + 215) := by ring
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
  have hmod : (n : ZMod 797) = ((n % 797 : ℕ) : ZMod 797) := by rw [ZMod.natCast_mod]
  rw [hmod]
  have hlt : n % 797 < 797 := Nat.mod_lt _ (by norm_num)
  constructor
  · rintro (h' | h')
    · have h2 : (n%797) % 797 = 215 % 797 := (ZMod.natCast_eq_natCast_iff (n%797) 215 797).mp h'
      rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (by norm_num : 215<797)] at h2
      exact Or.inl h2
    · have h3 : ((n % 797 : ℕ) : ZMod 797) = (582 : ZMod 797) := by
        rw [h']; decide
      have h2 : (n%797) % 797 = 582 % 797 := (ZMod.natCast_eq_natCast_iff (n%797) 582 797).mp h3
      rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (by norm_num : 582<797)] at h2
      exact Or.inr h2
  · rintro (h' | h')
    · left; rw [h']; decide
    · right; rw [h']; decide
