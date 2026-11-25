import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_1621 :
    ∀ n : ℕ, 1621 ∣ n ^ 2 + 1 ↔ n % 1621 = 166 ∨ n % 1621 = 1455 := by
  intro n
  rw [Nat.dvd_iff_mod_eq_zero]
  have hsq : n ^ 2 % 1621 = (n % 1621) ^ 2 % 1621 := Nat.pow_mod ..
  have hn : (n ^ 2 + 1) % 1621 = ((n % 1621) ^ 2 + 1) % 1621 := by
    conv_rhs => rw [Nat.add_mod]
    rw [Nat.add_mod, hsq]
  rw [hn]
  have hrlt : n % 1621 < 1621 := Nat.mod_lt _ (by norm_num)
  interval_cases h : n % 1621 <;> norm_num
