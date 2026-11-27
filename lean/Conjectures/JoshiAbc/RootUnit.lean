import Mathlib

theorem Conjectures.JoshiAbc.RootUnit :
    ∀ (p l : ℕ) [Fact p.Prime] (z : ZMod p), p ≠ 2 → Odd l → z^l=1 → z+z⁻¹ ≠ 0 := by
  intro p l _ z hp hl hzl hsum
  have hl0 : l ≠ 0 := by
    rintro rfl
    exact Nat.not_odd_zero hl
  have hz0 : z ≠ 0 := by
    intro hz
    rw [hz, zero_pow hl0] at hzl
    exact zero_ne_one hzl
  have hz2 : z ^ 2 = -1 := by
    have h := congrArg (fun w : ZMod p => z * w) hsum
    rw [mul_add, mul_inv_cancel₀ hz0, mul_zero] at h
    have h' : z * z = -1 := add_eq_zero_iff_eq_neg.mp h
    rw [pow_two]
    exact h'
  have h1 : (z ^ 2) ^ l = -1 := by
    rw [hz2, Odd.neg_one_pow hl]
  have h2 : (z ^ 2) ^ l = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hzl, one_pow]
  have hne : (-1 : ZMod p) = 1 := h1.symm.trans h2
  have hchar : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    exact hp
  exact Ring.neg_one_ne_one_of_char_ne_two hchar hne
