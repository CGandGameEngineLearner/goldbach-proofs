import Mathlib

instance : Fact (Nat.Prime 521) := ⟨by norm_num⟩

theorem PEqualNP.Outside.L_quadratic_primes_cert_521 :
    ∀ n:ℕ, 521∣n^2+1 ↔ n%521=235 ∨ n%521=286 := by
  intro n
  have ha : (235:ZMod 521)^2 = -1 := by decide
  have key : ((n:ZMod 521)^2 + 1 = 0) ↔ ((n:ZMod 521) = 235 ∨ (n:ZMod 521) = -235) := by
    constructor
    · intro h
      have hsq : (n:ZMod 521)^2 - (235:ZMod 521)^2 = 0 := by rw [ha]; simpa using h
      have hfac : (n:ZMod 521)^2 - (235:ZMod 521)^2 = ((n:ZMod 521) - 235) * ((n:ZMod 521) + 235) := by ring
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
  have hmod : (n : ZMod 521) = ((n % 521 : ℕ) : ZMod 521) := by rw [ZMod.natCast_mod]
  rw [hmod]
  have hlt : n % 521 < 521 := Nat.mod_lt _ (by norm_num)
  constructor
  · rintro (h' | h')
    · have h2 : (n%521) % 521 = 235 % 521 := (ZMod.natCast_eq_natCast_iff (n%521) 235 521).mp h'
      rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (by norm_num : 235<521)] at h2
      exact Or.inl h2
    · have h3 : ((n % 521 : ℕ) : ZMod 521) = (286 : ZMod 521) := by
        rw [h']; decide
      have h2 : (n%521) % 521 = 286 % 521 := (ZMod.natCast_eq_natCast_iff (n%521) 286 521).mp h3
      rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (by norm_num : 286<521)] at h2
      exact Or.inr h2
  · rintro (h' | h')
    · left; rw [h']; decide
    · right; rw [h']; decide
