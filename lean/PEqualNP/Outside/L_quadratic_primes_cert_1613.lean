import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_1613 :
    ∀ n : ℕ, 1613 ∣ n ^ 2 + 1 ↔ n % 1613 = 127 ∨ n % 1613 = 1486 := by
  intro n
  have e : (n ^ 2 + 1) % 1613 = ((n % 1613) ^ 2 + 1) % 1613 := by
    rw [Nat.add_mod, Nat.pow_mod, Nat.add_mod]
    norm_num
  rw [Nat.dvd_iff_mod_eq_zero, e]
  have h : n % 1613 < 1613 := Nat.mod_lt _ (by norm_num)
  generalize hh : n % 1613 = r at h ⊢
  interval_cases r <;> norm_num
