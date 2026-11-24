import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_local_root_pair :
    ∀ (p : ℕ), Nat.Prime p → ∀ (a b : ZMod p), a ^ 2 + 1 = 0 → b ^ 2 + 1 = 0 → a = b ∨ a = -b := by
  intro p hp a b ha hb
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have hzero : (a - b) * (a + b) = 0 := by
    linear_combination ha - hb
  rcases mul_eq_zero.mp hzero with h | h
  · left
    exact sub_eq_zero.mp h
  · right
    exact eq_neg_iff_add_eq_zero.mpr h
