import Mathlib

instance : Fact (Nat.Prime 557) := ⟨by norm_num⟩

theorem PEqualNP.Outside.L_quadratic_primes_cert_557 :
    ∀ n:ℕ, 557∣n^2+1 ↔ n%557=118 ∨ n%557=439 := by
  intro n
  have ha : (118:ZMod 557)^2 = -1 := by decide
  have key : ((n:ZMod 557)^2 + 1 = 0) ↔ ((n:ZMod 557) = 118 ∨ (n:ZMod 557) = -118) := by
    constructor
    · intro h
      have hsq : (n:ZMod 557)^2 - (118:ZMod 557)^2 = 0 := by rw [ha]; simpa using h
      have hfac : (n:ZMod 557)^2 - (118:ZMod 557)^2 = ((n:ZMod 557) - 118) * ((n:ZMod 557) + 118) := by ring
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
  have hmod : (n : ZMod 557) = ((n % 557 : ℕ) : ZMod 557) := by rw [ZMod.natCast_mod]
  rw [hmod]
  have hlt : n % 557 < 557 := Nat.mod_lt _ (by norm_num)
  constructor
  · rintro (h' | h')
    · have h2 : (n%557) % 557 = 118 % 557 := (ZMod.natCast_eq_natCast_iff (n%557) 118 557).mp h'
      rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (by norm_num : 118<557)] at h2
      exact Or.inl h2
    · have h3 : ((n % 557 : ℕ) : ZMod 557) = (439 : ZMod 557) := by
        rw [h']; decide
      have h2 : (n%557) % 557 = 439 % 557 := (ZMod.natCast_eq_natCast_iff (n%557) 439 557).mp h3
      rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (by norm_num : 439<557)] at h2
      exact Or.inr h2
  · rintro (h' | h')
    · left; rw [h']; decide
    · right; rw [h']; decide
