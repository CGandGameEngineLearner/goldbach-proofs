import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_229 :
    ∀ n:ℕ, 229∣n^2+1 ↔ n%229=107 ∨ n%229=122 := by
  intro n
  have hexh : ∀ m : Fin 229, ((m : ℕ) ^ 2 + 1) % 229 = 0 ↔ (m : ℕ) = 107 ∨ (m : ℕ) = 122 := by
    decide
  have hmod : n ^ 2 + 1 ≡ (n % 229) ^ 2 + 1 [MOD 229] :=
    ((Nat.mod_modEq n 229).symm.pow 2).add Nat.ModEq.rfl
  constructor
  · intro hdvd
    exact (hexh ⟨n % 229, Nat.mod_lt _ (by norm_num)⟩).mp
      (hmod.symm.trans (Nat.modEq_zero_iff_dvd.mpr hdvd))
  · intro h
    exact Nat.modEq_zero_iff_dvd.mp
      (hmod.trans ((hexh ⟨n % 229, Nat.mod_lt _ (by norm_num)⟩).mpr h))
