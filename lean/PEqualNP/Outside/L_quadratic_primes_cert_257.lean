import Mathlib
set_option maxRecDepth 100000

theorem PEqualNP.Outside.L_quadratic_primes_cert_257 :
    ∀ n:ℕ, 257∣n^2+1 ↔ n%257=16 ∨ n%257=241 := by
  intro n
  have hexh : ∀ m : Fin 257, ((m : ℕ) ^ 2 + 1) % 257 = 0 ↔ (m : ℕ) = 16 ∨ (m : ℕ) = 241 := by
    decide
  have hmod : n ^ 2 + 1 ≡ (n % 257) ^ 2 + 1 [MOD 257] :=
    ((Nat.mod_modEq n 257).symm.pow 2).add Nat.ModEq.rfl
  constructor
  · intro hdvd
    exact (hexh ⟨n % 257, Nat.mod_lt _ (by norm_num)⟩).mp
      (hmod.symm.trans (Nat.modEq_zero_iff_dvd.mpr hdvd))
  · intro h
    exact Nat.modEq_zero_iff_dvd.mp
      (hmod.trans ((hexh ⟨n % 257, Nat.mod_lt _ (by norm_num)⟩).mpr h))
