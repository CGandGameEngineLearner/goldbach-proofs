import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_mid_square_mod_three :
    ∀ n p : ℕ, n ^ 2 + 1 ≠ 3 * p ^ 2 := by
  intro n p h
  have h3 : ((n ^ 2 + 1 : ℕ) : ZMod 3) = 0 := by
    rw [h, Nat.cast_mul, Nat.cast_pow]
    have h3z : ((3 : ℕ) : ZMod 3) = 0 := by decide
    rw [h3z, zero_mul]
  have h3' : (n : ZMod 3) ^ 2 + 1 = 0 := by
    have := h3
    push_cast at this
    simpa using this
  have hno : ∀ x : ZMod 3, x ^ 2 + 1 ≠ 0 := by decide
  exact hno (n : ZMod 3) h3'
