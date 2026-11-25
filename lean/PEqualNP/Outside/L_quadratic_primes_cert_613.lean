import Mathlib

instance : Fact (Nat.Prime 613) := ⟨by norm_num⟩

theorem PEqualNP.Outside.L_quadratic_primes_cert_613 :
    ∀ n:ℕ, 613∣n^2+1 ↔ n%613=35 ∨ n%613=578 := by
  intro n
  have ha : (35:ZMod 613)^2 = -1 := by decide
  have key : ((n:ZMod 613)^2 + 1 = 0) ↔ ((n:ZMod 613) = 35 ∨ (n:ZMod 613) = -35) := by
    constructor
    · intro h
      have hsq : (n:ZMod 613)^2 - (35:ZMod 613)^2 = 0 := by rw [ha]; simpa using h
      have hfac : (n:ZMod 613)^2 - (35:ZMod 613)^2 = ((n:ZMod 613) - 35) * ((n:ZMod 613) + 35) := by ring
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
  have hmod : (n : ZMod 613) = ((n % 613 : ℕ) : ZMod 613) := by rw [ZMod.natCast_mod]
  rw [hmod]
  have hlt : n % 613 < 613 := Nat.mod_lt _ (by norm_num)
  constructor
  · rintro (h' | h')
    · have h2 : (n%613) % 613 = 35 % 613 := (ZMod.natCast_eq_natCast_iff (n%613) 35 613).mp h'
      rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (by norm_num : 35<613)] at h2
      exact Or.inl h2
    · have h3 : ((n % 613 : ℕ) : ZMod 613) = (578 : ZMod 613) := by
        rw [h']; decide
      have h2 : (n%613) % 613 = 578 % 613 := (ZMod.natCast_eq_natCast_iff (n%613) 578 613).mp h3
      rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (by norm_num : 578<613)] at h2
      exact Or.inr h2
  · rintro (h' | h')
    · left; rw [h']; decide
    · right; rw [h']; decide
