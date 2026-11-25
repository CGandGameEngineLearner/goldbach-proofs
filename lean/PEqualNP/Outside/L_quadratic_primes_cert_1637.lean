import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_1637 :
    ∀ n : ℕ, 1637 ∣ n ^ 2 + 1 ↔ n % 1637 = 316 ∨ n % 1637 = 1321 := by
  intro n
  rw [Nat.dvd_iff_mod_eq_zero]
  have hsq : n ^ 2 % 1637 = (n % 1637) ^ 2 % 1637 := Nat.pow_mod ..
  have hn : (n ^ 2 + 1) % 1637 = ((n % 1637) ^ 2 + 1) % 1637 := by
    conv_rhs => rw [Nat.add_mod]
    rw [Nat.add_mod, hsq]
  rw [hn]
  have hrlt : n % 1637 < 1637 := Nat.mod_lt _ (by norm_num)
  interval_cases h : n % 1637 <;> norm_num
