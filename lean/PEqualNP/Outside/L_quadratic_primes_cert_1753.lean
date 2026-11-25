import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_1753 :
    ∀ n : ℕ, 1753 ∣ n ^ 2 + 1 ↔ n % 1753 = 713 ∨ n % 1753 = 1040 := by
  intro n
  rw [Nat.dvd_iff_mod_eq_zero]
  have hsq : n ^ 2 % 1753 = (n % 1753) ^ 2 % 1753 := Nat.pow_mod ..
  have hn : (n ^ 2 + 1) % 1753 = ((n % 1753) ^ 2 + 1) % 1753 := by
    conv_rhs => rw [Nat.add_mod]
    rw [Nat.add_mod, hsq]
  rw [hn]
  have hrlt : n % 1753 < 1753 := Nat.mod_lt _ (by norm_num)
  interval_cases h : n % 1753 <;> norm_num
