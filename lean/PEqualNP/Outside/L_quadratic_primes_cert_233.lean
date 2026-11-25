import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_233 :
    ∀ n:ℕ, 233∣n^2+1 ↔ n%233=89 ∨ n%233=144 := by
  intro n
  have hexh : ∀ m : Fin 233, ((m : ℕ) ^ 2 + 1) % 233 = 0 ↔ (m : ℕ) = 89 ∨ (m : ℕ) = 144 := by
    decide
  have hmod : n ^ 2 + 1 ≡ (n % 233) ^ 2 + 1 [MOD 233] :=
    ((Nat.mod_modEq n 233).symm.pow 2).add Nat.ModEq.rfl
  constructor
  · intro hdvd
    exact (hexh ⟨n % 233, Nat.mod_lt _ (by norm_num)⟩).mp
      (hmod.symm.trans (Nat.modEq_zero_iff_dvd.mpr hdvd))
  · intro h
    exact Nat.modEq_zero_iff_dvd.mp
      (hmod.trans ((hexh ⟨n % 233, Nat.mod_lt _ (by norm_num)⟩).mpr h))
