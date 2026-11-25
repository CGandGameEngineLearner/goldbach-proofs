import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_521 :
    ∀ n:ℕ, 521∣n^2+1 ↔ n %521=235 ∨ n %521=286 := by
  intro n
  have key : ∀ m, m < 521 → (521 ∣ m^2+1 ↔ m = 235 ∨ m = 286) := by decide +kernel
  have hmod : (n % 521)^2+1 ≡ n^2+1 [MOD 521] := ((Nat.mod_modEq n 521).pow 2).add_right 1
  rw [← hmod.dvd_iff dvd_rfl]
  exact key (n % 521) (Nat.mod_lt n (by norm_num))
