import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_229 :
    ∀ n : ℕ, 229 ∣ n ^ 2 + 1 ↔ n % 229 = 107 ∨ n % 229 = 122 := by
  intro n
  rw [Nat.dvd_iff_mod_eq_zero]
  have hsq : n ^ 2 % 229 = (n % 229) ^ 2 % 229 := Nat.pow_mod ..
  have hn : (n ^ 2 + 1) % 229 = ((n % 229) ^ 2 + 1) % 229 := by
    conv_rhs => rw [Nat.add_mod]
    rw [Nat.add_mod, hsq]
  rw [hn]
  have hrlt : n % 229 < 229 := Nat.mod_lt _ (by norm_num)
  interval_cases h : n % 229 <;> norm_num
