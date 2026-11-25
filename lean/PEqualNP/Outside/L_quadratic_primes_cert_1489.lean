import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_1489 :
    ∀ n:ℕ, 1489∣n^2+1 ↔ n%1489=225 ∨ n%1489=1264 := by
  have h1 : ((225 : ZMod 1489) + (1264 : ZMod 1489)) = 0 := by decide
  have h2 : ((225 : ZMod 1489) * (1264 : ZMod 1489)) = 1 := by decide
  haveI : Fact (Nat.Prime 1489) := ⟨by norm_num⟩
  have hfac : ∀ x : ZMod 1489, x^2 + 1 = (x - (225:ZMod 1489)) * (x - (1264:ZMod 1489)) := by
    intro x
    linear_combination x * h1 - h2
  have hr : ((225 : ZMod 1489))^2 + 1 = 0 := by linear_combination 225 * h1 - h2
  have hs : ((1264 : ZMod 1489))^2 + 1 = 0 := by linear_combination 1264 * h1 - h2
  have key : ∀ x : ZMod 1489, x^2 + 1 = 0 ↔ x = (225:ZMod 1489) ∨ x = (1264:ZMod 1489) := by
    intro x
    rw [hfac x, mul_eq_zero]
    constructor
    · rintro (h | h)
      · exact Or.inl (sub_eq_zero.mp h)
      · exact Or.inr (sub_eq_zero.mp h)
    · rintro (h | h)
      · rw [h]; simpa using hr
      · rw [h]; simpa using hs
  have hzero : ∀ m : ℕ, ((m : ZMod 1489) = 0) ↔ 1489 ∣ m := by
    intro m
    rw [← Nat.cast_zero, ZMod.natCast_eq_natCast_iff, Nat.modEq_zero_iff_dvd]
  intro n
  constructor
  · intro h
    have hz : ((n : ZMod 1489))^2 + 1 = 0 := by
      have hc : ((n^2+1 : ℕ) : ZMod 1489) = 0 := (hzero _).mpr h
      push_cast at hc ⊢
      exact hc
    rcases (key n).mp hz with h' | h'
    · left
      have h'' : (n : ZMod 1489) = ((225:ℕ) : ZMod 1489) := h'
      have : n % 1489 = 225 % 1489 := (ZMod.natCast_eq_natCast_iff' _ _ _).mp h''
      simpa using this
    · right
      have h'' : (n : ZMod 1489) = ((1264:ℕ) : ZMod 1489) := h'
      have : n % 1489 = 1264 % 1489 := (ZMod.natCast_eq_natCast_iff' _ _ _).mp h''
      simpa using this
  · rintro (h | h)
    · have hn : (n : ZMod 1489) = ((225:ℕ) : ZMod 1489) := by
        rw [ZMod.natCast_eq_natCast_iff']
        simpa using h
      have hz : ((n : ZMod 1489))^2 + 1 = 0 := (key n).mpr (Or.inl hn)
      have hc : ((n^2+1 : ℕ) : ZMod 1489) = 0 := by push_cast; exact hz
      exact (hzero _).mp hc
    · have hn : (n : ZMod 1489) = ((1264:ℕ) : ZMod 1489) := by
        rw [ZMod.natCast_eq_natCast_iff']
        simpa using h
      have hz : ((n : ZMod 1489))^2 + 1 = 0 := (key n).mpr (Or.inr hn)
      have hc : ((n^2+1 : ℕ) : ZMod 1489) = 0 := by push_cast; exact hz
      exact (hzero _).mp hc
