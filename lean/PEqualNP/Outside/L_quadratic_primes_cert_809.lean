import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_809 :
    ∀ n : ℕ, 809 ∣ n ^ 2 + 1 ↔ n % 809 = 318 ∨ n % 809 = 491 := by
  intro n
  rw [Nat.dvd_iff_mod_eq_zero]
  have hsq : n ^ 2 % 809 = (n % 809) ^ 2 % 809 := Nat.pow_mod ..
  have hn : (n ^ 2 + 1) % 809 = ((n % 809) ^ 2 + 1) % 809 := by
    conv_rhs => rw [Nat.add_mod]
    rw [Nat.add_mod, hsq]
  rw [hn]
  have hrlt : n % 809 < 809 := Nat.mod_lt _ (by norm_num)
  interval_cases h : n % 809 <;> norm_num
