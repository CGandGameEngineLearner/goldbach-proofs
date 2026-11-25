import Mathlib

theorem PEqualNP.Outside.L_goldbach_dyadic_conductor_ratio :
    ∀ k j : ℕ, j+2≤k → (Nat.totient (2^k/2^j):ℝ)/(Nat.totient (2^k):ℝ) = 1/(2:ℝ)^j := by
  intro k j hkj
  have hdiv : 2 ^ k / 2 ^ j = 2 ^ (k - j) := by
    have hk : k = (k - j) + j := by omega
    have hpos : 0 < 2 ^ j := pow_pos (by decide) j
    rw [hk, pow_add, Nat.mul_div_cancel _ hpos]
  have ht1 : Nat.totient (2 ^ (k - j)) = 2 ^ (k - j - 1) := by
    rw [Nat.totient_prime_pow Nat.prime_two (by omega)]
    norm_num
  have ht2 : Nat.totient (2 ^ k) = 2 ^ (k - 1) := by
    rw [Nat.totient_prime_pow Nat.prime_two (by omega)]
    norm_num
  have hexp : k - 1 = (k - j - 1) + j := by omega
  rw [hdiv, ht1, ht2]
  push_cast
  rw [hexp, pow_add]
  have hne1 : (2 : ℝ) ^ (k - j - 1) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hne2 : (2 : ℝ) ^ j ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp <;> ring
