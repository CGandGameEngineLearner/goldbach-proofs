import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_197 :
    ∀ n : ℕ, 197 ∣ n ^ 2 + 1 ↔ n % 197 = 14 ∨ n % 197 = 183 := by
  intro n
  rw [Nat.dvd_iff_mod_eq_zero]
  have hsq : n ^ 2 % 197 = (n % 197) ^ 2 % 197 := Nat.pow_mod ..
  have hn : (n ^ 2 + 1) % 197 = ((n % 197) ^ 2 + 1) % 197 := by
    conv_rhs => rw [Nat.add_mod]
    rw [Nat.add_mod, hsq]
  rw [hn]
  have hrlt : n % 197 < 197 := Nat.mod_lt _ (by norm_num)
  interval_cases h : n % 197 <;> norm_num
