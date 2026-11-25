import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_1669 :
    ∀ n : ℕ, 1669 ∣ n ^ 2 + 1 ↔ n % 1669 = 220 ∨ n % 1669 = 1449 := by
  intro n
  rw [Nat.dvd_iff_mod_eq_zero]
  have hsq : n ^ 2 % 1669 = (n % 1669) ^ 2 % 1669 := Nat.pow_mod ..
  have hn : (n ^ 2 + 1) % 1669 = ((n % 1669) ^ 2 + 1) % 1669 := by
    conv_rhs => rw [Nat.add_mod]
    rw [Nat.add_mod, hsq]
  rw [hn]
  have hrlt : n % 1669 < 1669 := Nat.mod_lt _ (by norm_num)
  interval_cases h : n % 1669 <;> norm_num
