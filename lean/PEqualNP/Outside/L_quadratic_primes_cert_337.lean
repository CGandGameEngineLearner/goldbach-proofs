import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_337 :
    ∀ n : ℕ, 337 ∣ n ^ 2 + 1 ↔ n % 337 = 148 ∨ n % 337 = 189 := by
  intro n
  rw [Nat.dvd_iff_mod_eq_zero]
  have hsq : n ^ 2 % 337 = (n % 337) ^ 2 % 337 := Nat.pow_mod ..
  have hn : (n ^ 2 + 1) % 337 = ((n % 337) ^ 2 + 1) % 337 := by
    conv_rhs => rw [Nat.add_mod]
    rw [Nat.add_mod, hsq]
  rw [hn]
  have hrlt : n % 337 < 337 := Nat.mod_lt _ (by norm_num)
  interval_cases h : n % 337 <;> norm_num
