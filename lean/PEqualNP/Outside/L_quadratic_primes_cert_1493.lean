import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_1493 :
    ∀ n:ℕ, 1493∣n^2+1 ↔ n%1493=432 ∨ n%1493=1061 := by
  have h1 : ((432 : ZMod 1493) + (1061 : ZMod 1493)) = 0 := by decide
  have h2 : ((432 : ZMod 1493) * (1061 : ZMod 1493)) = 1 := by decide
  haveI : Fact (Nat.Prime 1493) := ⟨by norm_num⟩
  have hfac : ∀ x : ZMod 1493, x^2 + 1 = (x - (432:ZMod 1493)) * (x - (1061:ZMod 1493)) := by
    intro x
    linear_combination x * h1 - h2
  have hr : ((432 : ZMod 1493))^2 + 1 = 0 := by linear_combination 432 * h1 - h2
  have hs : ((1061 : ZMod 1493))^2 + 1 = 0 := by linear_combination 1061 * h1 - h2
  have key : ∀ x : ZMod 1493, x^2 + 1 = 0 ↔ x = (432:ZMod 1493) ∨ x = (1061:ZMod 1493) := by
    intro x
    rw [hfac x, mul_eq_zero]
    constructor
    · rintro (h | h)
      · exact Or.inl (sub_eq_zero.mp h)
      · exact Or.inr (sub_eq_zero.mp h)
    · rintro (h | h)
      · rw [h]; simpa using hr
      · rw [h]; simpa using hs
  have hzero : ∀ m : ℕ, ((m : ZMod 1493) = 0) ↔ 1493 ∣ m := by
    intro m
    rw [← Nat.cast_zero, ZMod.natCast_eq_natCast_iff, Nat.modEq_zero_iff_dvd]
  intro n
  constructor
  · intro h
    have hz : ((n : ZMod 1493))^2 + 1 = 0 := by
      have hc : ((n^2+1 : ℕ) : ZMod 1493) = 0 := (hzero _).mpr h
      push_cast at hc ⊢
      exact hc
    rcases (key n).mp hz with h' | h'
    · left
      have h'' : (n : ZMod 1493) = ((432:ℕ) : ZMod 1493) := h'
      have : n % 1493 = 432 % 1493 := (ZMod.natCast_eq_natCast_iff' _ _ _).mp h''
      simpa using this
    · right
      have h'' : (n : ZMod 1493) = ((1061:ℕ) : ZMod 1493) := h'
      have : n % 1493 = 1061 % 1493 := (ZMod.natCast_eq_natCast_iff' _ _ _).mp h''
      simpa using this
  · rintro (h | h)
    · have hn : (n : ZMod 1493) = ((432:ℕ) : ZMod 1493) := by
        rw [ZMod.natCast_eq_natCast_iff']
        simpa using h
      have hz : ((n : ZMod 1493))^2 + 1 = 0 := (key n).mpr (Or.inl hn)
      have hc : ((n^2+1 : ℕ) : ZMod 1493) = 0 := by push_cast; exact hz
      exact (hzero _).mp hc
    · have hn : (n : ZMod 1493) = ((1061:ℕ) : ZMod 1493) := by
        rw [ZMod.natCast_eq_natCast_iff']
        simpa using h
      have hz : ((n : ZMod 1493))^2 + 1 = 0 := (key n).mpr (Or.inr hn)
      have hc : ((n^2+1 : ℕ) : ZMod 1493) = 0 := by push_cast; exact hz
      exact (hzero _).mp hc
