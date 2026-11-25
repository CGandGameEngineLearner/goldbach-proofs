import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_1709 :
    ∀ n : ℕ, 1709 ∣ n ^ 2 + 1 ↔ n % 1709 = 390 ∨ n % 1709 = 1319 := by
  intro n
  rw [Nat.dvd_iff_mod_eq_zero]
  have hsq : n ^ 2 % 1709 = (n % 1709) ^ 2 % 1709 := Nat.pow_mod ..
  have hn : (n ^ 2 + 1) % 1709 = ((n % 1709) ^ 2 + 1) % 1709 := by
    conv_rhs => rw [Nat.add_mod]
    rw [Nat.add_mod, hsq]
  rw [hn]
  have hrlt : n % 1709 < 1709 := Nat.mod_lt _ (by norm_num)
  interval_cases h : n % 1709 <;> norm_num
