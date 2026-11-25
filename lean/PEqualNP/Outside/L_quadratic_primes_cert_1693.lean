import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_1693 :
    ∀ n : ℕ, 1693 ∣ n ^ 2 + 1 ↔ n % 1693 = 92 ∨ n % 1693 = 1601 := by
  intro n
  rw [Nat.dvd_iff_mod_eq_zero]
  have hsq : n ^ 2 % 1693 = (n % 1693) ^ 2 % 1693 := Nat.pow_mod ..
  have hn : (n ^ 2 + 1) % 1693 = ((n % 1693) ^ 2 + 1) % 1693 := by
    conv_rhs => rw [Nat.add_mod]
    rw [Nat.add_mod, hsq]
  rw [hn]
  have hrlt : n % 1693 < 1693 := Nat.mod_lt _ (by norm_num)
  interval_cases h : n % 1693 <;> norm_num
