import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_1321 :
    ∀ n:ℕ, 1321∣n^2+1 ↔ n%1321=257 ∨ n%1321=1064 := by
  have h1 : ((257 : ZMod 1321) + (1064 : ZMod 1321)) = 0 := by decide
  have h2 : ((257 : ZMod 1321) * (1064 : ZMod 1321)) = 1 := by decide
  haveI : Fact (Nat.Prime 1321) := ⟨by norm_num⟩
  have hfac : ∀ x : ZMod 1321, x^2 + 1 = (x - (257:ZMod 1321)) * (x - (1064:ZMod 1321)) := by
    intro x
    linear_combination x * h1 - h2
  have hr : ((257 : ZMod 1321))^2 + 1 = 0 := by linear_combination 257 * h1 - h2
  have hs : ((1064 : ZMod 1321))^2 + 1 = 0 := by linear_combination 1064 * h1 - h2
  have key : ∀ x : ZMod 1321, x^2 + 1 = 0 ↔ x = (257:ZMod 1321) ∨ x = (1064:ZMod 1321) := by
    intro x
    rw [hfac x, mul_eq_zero]
    constructor
    · rintro (h | h)
      · exact Or.inl (sub_eq_zero.mp h)
      · exact Or.inr (sub_eq_zero.mp h)
    · rintro (h | h)
      · rw [h]; simpa using hr
      · rw [h]; simpa using hs
  have hzero : ∀ m : ℕ, ((m : ZMod 1321) = 0) ↔ 1321 ∣ m := by
    intro m
    rw [← Nat.cast_zero, ZMod.natCast_eq_natCast_iff, Nat.modEq_zero_iff_dvd]
  intro n
  constructor
  · intro h
    have hz : ((n : ZMod 1321))^2 + 1 = 0 := by
      have hc : ((n^2+1 : ℕ) : ZMod 1321) = 0 := (hzero _).mpr h
      push_cast at hc ⊢
      exact hc
    rcases (key n).mp hz with h' | h'
    · left
      have h'' : (n : ZMod 1321) = ((257:ℕ) : ZMod 1321) := h'
      have : n % 1321 = 257 % 1321 := (ZMod.natCast_eq_natCast_iff' _ _ _).mp h''
      simpa using this
    · right
      have h'' : (n : ZMod 1321) = ((1064:ℕ) : ZMod 1321) := h'
      have : n % 1321 = 1064 % 1321 := (ZMod.natCast_eq_natCast_iff' _ _ _).mp h''
      simpa using this
  · rintro (h | h)
    · have hn : (n : ZMod 1321) = ((257:ℕ) : ZMod 1321) := by
        rw [ZMod.natCast_eq_natCast_iff']
        simpa using h
      have hz : ((n : ZMod 1321))^2 + 1 = 0 := (key n).mpr (Or.inl hn)
      have hc : ((n^2+1 : ℕ) : ZMod 1321) = 0 := by push_cast; exact hz
      exact (hzero _).mp hc
    · have hn : (n : ZMod 1321) = ((1064:ℕ) : ZMod 1321) := by
        rw [ZMod.natCast_eq_natCast_iff']
        simpa using h
      have hz : ((n : ZMod 1321))^2 + 1 = 0 := (key n).mpr (Or.inr hn)
      have hc : ((n^2+1 : ℕ) : ZMod 1321) = 0 := by push_cast; exact hz
      exact (hzero _).mp hc
