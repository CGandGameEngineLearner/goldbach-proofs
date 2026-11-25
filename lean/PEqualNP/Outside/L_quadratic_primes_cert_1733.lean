import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_1733 :
    ∀ n : ℕ, 1733 ∣ n ^ 2 + 1 ↔ n % 1733 = 410 ∨ n % 1733 = 1323 := by
  intro n
  rw [Nat.dvd_iff_mod_eq_zero]
  have hsq : n ^ 2 % 1733 = (n % 1733) ^ 2 % 1733 := Nat.pow_mod ..
  have hn : (n ^ 2 + 1) % 1733 = ((n % 1733) ^ 2 + 1) % 1733 := by
    conv_rhs => rw [Nat.add_mod]
    rw [Nat.add_mod, hsq]
  rw [hn]
  have hrlt : n % 1733 < 1733 := Nat.mod_lt _ (by norm_num)
  interval_cases h : n % 1733 <;> norm_num
