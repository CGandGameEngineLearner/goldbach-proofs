import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_877 :
    ∀ n:ℕ, 877∣n^2+1 ↔ n%877=151 ∨ n%877=726 := by
  intro n
  haveI : Fact (Nat.Prime 877) := ⟨by norm_num⟩
  have h151 : ((151 : ℕ) : ZMod 877) ^ 2 = -1 := by decide +revert
  have h726 : ((726 : ℕ) : ZMod 877) ^ 2 = -1 := by decide +revert
  -- Over the prime field, x^2 = -1 factors as (x-151)(x+151), so both roots are explicit.
  have hroot : ∀ x : ZMod 877, x ^ 2 = -1 → x = 151 ∨ x = 726 := by
    intro x hx
    have hsq : x ^ 2 = (151 : ZMod 877) ^ 2 := by linear_combination hx - h151
    have hfac : (x - 151) * (x + 151) = 0 := by
      calc (x - 151) * (x + 151) = x ^ 2 - (151 : ZMod 877) ^ 2 := by ring
        _ = 0 := by rw [hsq]; ring
    rcases mul_eq_zero.mp hfac with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · refine Or.inr ?_
      have hxneg : x = -151 := eq_neg_of_add_eq_zero_right h
      have h726eq : (726 : ZMod 877) = -151 := by decide +revert
      rw [hxneg, h726eq]
  have hdvd : (877 ∣ n ^ 2 + 1) ↔ ((n ^ 2 + 1 : ℕ) : ZMod 877) = 0 := by
    rw [← Nat.cast_zero (R := ZMod 877), ZMod.natCast_eq_natCast_iff, Nat.modEq_zero_iff_dvd]
  have hcast : ((n ^ 2 + 1 : ℕ) : ZMod 877) = (n : ZMod 877) ^ 2 + 1 := by
    push_cast
    ring
  have hiff : (877 ∣ n ^ 2 + 1) ↔ ((n : ZMod 877) ^ 2 = -1) := by
    rw [hdvd, hcast]
    constructor
    · intro h
      linear_combination h
    · intro h
      linear_combination h
  rw [hiff]
  constructor
  · intro hx
    rcases hroot (n : ZMod 877) hx with h | h
    · left
      have hmod := (ZMod.natCast_eq_natCast_iff' n 151 877).mp h
      simpa using hmod
    · right
      have hmod := (ZMod.natCast_eq_natCast_iff' n 726 877).mp h
      simpa using hmod
  · rintro (h | h)
    · have hn : (n : ZMod 877) = (151 : ZMod 877) := by
        refine (ZMod.natCast_eq_natCast_iff' n 151 877).mpr ?_
        simpa using h
      rw [hn]
      exact h151
    · have hn : (n : ZMod 877) = (726 : ZMod 877) := by
        refine (ZMod.natCast_eq_natCast_iff' n 726 877).mpr ?_
        simpa using h
      rw [hn]
      exact h726
