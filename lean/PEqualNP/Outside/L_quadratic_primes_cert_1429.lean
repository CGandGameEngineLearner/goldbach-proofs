import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_1429 :
    ∀ n:ℕ, 1429∣n^2+1 ↔ n%1429=620 ∨ n%1429=809 := by
  have h1 : ((620 : ZMod 1429) + (809 : ZMod 1429)) = 0 := by decide
  have h2 : ((620 : ZMod 1429) * (809 : ZMod 1429)) = 1 := by decide
  haveI : Fact (Nat.Prime 1429) := ⟨by norm_num⟩
  have hfac : ∀ x : ZMod 1429, x^2 + 1 = (x - (620:ZMod 1429)) * (x - (809:ZMod 1429)) := by
    intro x
    linear_combination x * h1 - h2
  have hr : ((620 : ZMod 1429))^2 + 1 = 0 := by linear_combination 620 * h1 - h2
  have hs : ((809 : ZMod 1429))^2 + 1 = 0 := by linear_combination 809 * h1 - h2
  have key : ∀ x : ZMod 1429, x^2 + 1 = 0 ↔ x = (620:ZMod 1429) ∨ x = (809:ZMod 1429) := by
    intro x
    rw [hfac x, mul_eq_zero]
    constructor
    · rintro (h | h)
      · exact Or.inl (sub_eq_zero.mp h)
      · exact Or.inr (sub_eq_zero.mp h)
    · rintro (h | h)
      · rw [h]; simpa using hr
      · rw [h]; simpa using hs
  have hzero : ∀ m : ℕ, ((m : ZMod 1429) = 0) ↔ 1429 ∣ m := by
    intro m
    rw [← Nat.cast_zero, ZMod.natCast_eq_natCast_iff, Nat.modEq_zero_iff_dvd]
  intro n
  constructor
  · intro h
    have hz : ((n : ZMod 1429))^2 + 1 = 0 := by
      have hc : ((n^2+1 : ℕ) : ZMod 1429) = 0 := (hzero _).mpr h
      push_cast at hc ⊢
      exact hc
    rcases (key n).mp hz with h' | h'
    · left
      have h'' : (n : ZMod 1429) = ((620:ℕ) : ZMod 1429) := h'
      have : n % 1429 = 620 % 1429 := (ZMod.natCast_eq_natCast_iff' _ _ _).mp h''
      simpa using this
    · right
      have h'' : (n : ZMod 1429) = ((809:ℕ) : ZMod 1429) := h'
      have : n % 1429 = 809 % 1429 := (ZMod.natCast_eq_natCast_iff' _ _ _).mp h''
      simpa using this
  · rintro (h | h)
    · have hn : (n : ZMod 1429) = ((620:ℕ) : ZMod 1429) := by
        rw [ZMod.natCast_eq_natCast_iff']
        simpa using h
      have hz : ((n : ZMod 1429))^2 + 1 = 0 := (key n).mpr (Or.inl hn)
      have hc : ((n^2+1 : ℕ) : ZMod 1429) = 0 := by push_cast; exact hz
      exact (hzero _).mp hc
    · have hn : (n : ZMod 1429) = ((809:ℕ) : ZMod 1429) := by
        rw [ZMod.natCast_eq_natCast_iff']
        simpa using h
      have hz : ((n : ZMod 1429))^2 + 1 = 0 := (key n).mpr (Or.inr hn)
      have hc : ((n^2+1 : ℕ) : ZMod 1429) = 0 := by push_cast; exact hz
      exact (hzero _).mp hc
