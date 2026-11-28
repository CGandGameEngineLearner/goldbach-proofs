import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_809 :
    ∀ n:ℕ, 809∣n^2+1 ↔ n %809=318 ∨ n %809=491 := by
  intro n
  have key : ∀ m, m < 809 → (809 ∣ m^2+1 ↔ m = 318 ∨ m = 491) := by decide +kernel
  have hmod : (n % 809)^2+1 ≡ n^2+1 [MOD 809] := ((Nat.mod_modEq n 809).pow 2).add_right 1
  rw [← hmod.dvd_iff dvd_rfl]
  exact key (n % 809) (Nat.mod_lt n (by norm_num))
