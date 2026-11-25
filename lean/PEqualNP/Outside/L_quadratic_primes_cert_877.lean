import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_877 :
    ∀ n:ℕ, 877∣n^2+1 ↔ n %877=151 ∨ n %877=726 := by
  intro n
  have key : ∀ m, m < 877 → (877 ∣ m^2+1 ↔ m = 151 ∨ m = 726) := by decide +kernel
  have hmod : (n % 877)^2+1 ≡ n^2+1 [MOD 877] := ((Nat.mod_modEq n 877).pow 2).add_right 1
  rw [← hmod.dvd_iff dvd_rfl]
  exact key (n % 877) (Nat.mod_lt n (by norm_num))
