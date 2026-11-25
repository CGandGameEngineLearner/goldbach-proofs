import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_1549 :
    ∀ n:ℕ, 1549∣n^2+1 ↔ n%1549=88 ∨ n%1549=1461 := by
  have h1 : ((88 : ZMod 1549) + (1461 : ZMod 1549)) = 0 := by decide
  have h2 : ((88 : ZMod 1549) * (1461 : ZMod 1549)) = 1 := by decide
  haveI : Fact (Nat.Prime 1549) := ⟨by norm_num⟩
  have hfac : ∀ x : ZMod 1549, x^2 + 1 = (x - (88:ZMod 1549)) * (x - (1461:ZMod 1549)) := by
    intro x
    linear_combination x * h1 - h2
  have hr : ((88 : ZMod 1549))^2 + 1 = 0 := by linear_combination 88 * h1 - h2
  have hs : ((1461 : ZMod 1549))^2 + 1 = 0 := by linear_combination 1461 * h1 - h2
  have key : ∀ x : ZMod 1549, x^2 + 1 = 0 ↔ x = (88:ZMod 1549) ∨ x = (1461:ZMod 1549) := by
    intro x
    rw [hfac x, mul_eq_zero]
    constructor
    · rintro (h | h)
      · exact Or.inl (sub_eq_zero.mp h)
      · exact Or.inr (sub_eq_zero.mp h)
    · rintro (h | h)
      · rw [h]; simpa using hr
      · rw [h]; simpa using hs
  have hzero : ∀ m : ℕ, ((m : ZMod 1549) = 0) ↔ 1549 ∣ m := by
    intro m
    rw [← Nat.cast_zero, ZMod.natCast_eq_natCast_iff, Nat.modEq_zero_iff_dvd]
  intro n
  constructor
  · intro h
    have hz : ((n : ZMod 1549))^2 + 1 = 0 := by
      have hc : ((n^2+1 : ℕ) : ZMod 1549) = 0 := (hzero _).mpr h
      push_cast at hc ⊢
      exact hc
    rcases (key n).mp hz with h' | h'
    · left
      have h'' : (n : ZMod 1549) = ((88:ℕ) : ZMod 1549) := h'
      have : n % 1549 = 88 % 1549 := (ZMod.natCast_eq_natCast_iff' _ _ _).mp h''
      simpa using this
    · right
      have h'' : (n : ZMod 1549) = ((1461:ℕ) : ZMod 1549) := h'
      have : n % 1549 = 1461 % 1549 := (ZMod.natCast_eq_natCast_iff' _ _ _).mp h''
      simpa using this
  · rintro (h | h)
    · have hn : (n : ZMod 1549) = ((88:ℕ) : ZMod 1549) := by
        rw [ZMod.natCast_eq_natCast_iff']
        simpa using h
      have hz : ((n : ZMod 1549))^2 + 1 = 0 := (key n).mpr (Or.inl hn)
      have hc : ((n^2+1 : ℕ) : ZMod 1549) = 0 := by push_cast; exact hz
      exact (hzero _).mp hc
    · have hn : (n : ZMod 1549) = ((1461:ℕ) : ZMod 1549) := by
        rw [ZMod.natCast_eq_natCast_iff']
        simpa using h
      have hz : ((n : ZMod 1549))^2 + 1 = 0 := (key n).mpr (Or.inr hn)
      have hc : ((n^2+1 : ℕ) : ZMod 1549) = 0 := by push_cast; exact hz
      exact (hzero _).mp hc
