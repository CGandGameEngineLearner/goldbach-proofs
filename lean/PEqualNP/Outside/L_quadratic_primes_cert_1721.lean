import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_1721 :
    ∀ n : ℕ, 1721 ∣ n ^ 2 + 1 ↔ n % 1721 = 473 ∨ n % 1721 = 1248 := by
  intro n
  rw [Nat.dvd_iff_mod_eq_zero]
  have hsq : n ^ 2 % 1721 = (n % 1721) ^ 2 % 1721 := Nat.pow_mod ..
  have hn : (n ^ 2 + 1) % 1721 = ((n % 1721) ^ 2 + 1) % 1721 := by
    conv_rhs => rw [Nat.add_mod]
    rw [Nat.add_mod, hsq]
  rw [hn]
  have hrlt : n % 1721 < 1721 := Nat.mod_lt _ (by norm_num)
  interval_cases h : n % 1721 <;> norm_num
