import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_1697 :
    ∀ n : ℕ, 1697 ∣ n ^ 2 + 1 ↔ n % 1697 = 414 ∨ n % 1697 = 1283 := by
  intro n
  rw [Nat.dvd_iff_mod_eq_zero]
  have hsq : n ^ 2 % 1697 = (n % 1697) ^ 2 % 1697 := Nat.pow_mod ..
  have hn : (n ^ 2 + 1) % 1697 = ((n % 1697) ^ 2 + 1) % 1697 := by
    conv_rhs => rw [Nat.add_mod]
    rw [Nat.add_mod, hsq]
  rw [hn]
  have hrlt : n % 1697 < 1697 := Nat.mod_lt _ (by norm_num)
  interval_cases h : n % 1697 <;> norm_num
