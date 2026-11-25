import Mathlib

theorem PEqualNP.Outside.L_goldbach_dyadic_conductor_ratio :
    ∀ k j : ℕ, j+2 ≤ k →
      (Nat.totient (2^k/2^j):ℝ)/(Nat.totient (2^k):ℝ) = 1/(2:ℝ)^j := by
  intro k j h
  have hjk : j ≤ k := by omega
  rw [Nat.pow_div hjk (by norm_num : 0 < 2)]
  have hkj1 : 0 < k - j := by omega
  have hk1 : 0 < k := by omega
  rw [Nat.totient_prime_pow (p:=2) Nat.prime_two hkj1,
      Nat.totient_prime_pow (p:=2) Nat.prime_two hk1]
  have hkj1' : 1 ≤ k - j := hkj1
  have hrel : (2:ℝ)^(k-1) = (2:ℝ)^(k-j-1) * (2:ℝ)^j := by
    rw [← pow_add]
    congr 1
    omega
  have ha : (2:ℝ)^(k-j-1) ≠ 0 := by positivity
  have hb : (2:ℝ)^j ≠ 0 := by positivity
  norm_num [Nat.cast_pow]
  rw [hrel]
  field_simp
