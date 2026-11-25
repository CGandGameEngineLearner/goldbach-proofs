import Mathlib

theorem PEqualNP.Outside.L_goldbach_dyadic_conductor_ratio :
    ∀ k j : ℕ, j + 2 ≤ k →
      (Nat.totient (2 ^ k / 2 ^ j) : ℝ) / (Nat.totient (2 ^ k) : ℝ) =
        1 / (2 : ℝ) ^ j := by
  intro k j hj
  have hjk : j ≤ k := by omega
  have hpos : 0 < k - j := by omega
  have hk : 0 < k := by omega
  rw [Nat.pow_div hjk (by decide : 0 < (2 : ℕ)),
    Nat.totient_prime_pow Nat.prime_two hpos, Nat.totient_prime_pow Nat.prime_two hk]
  simp only [show (2 : ℕ) - 1 = 1 by decide, mul_one, Nat.cast_pow, Nat.cast_ofNat]
  rw [show k - 1 = (k - j - 1) + j by omega, pow_add]
  have h₁ : (2 : ℝ) ^ (k - j - 1) ≠ 0 := by positivity
  have h₂ : (2 : ℝ) ^ j ≠ 0 := by positivity
  field_simp [h₁, h₂] <;> ring