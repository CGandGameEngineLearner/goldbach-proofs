import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_1297 :
  ∀ n : ℕ, 1297 ∣ n ^ 2 + 1 ↔ n % 1297 = 36 ∨ n % 1297 = 1261 := by
  have h1 : (36 + 1261 : ZMod 1297) = 0 := by decide
  have h2 : (36 * 1261 : ZMod 1297) = 1 := by decide
  have hp : Nat.Prime 1297 := by norm_num
  have : Fact (Nat.Prime 1297) := ⟨hp⟩
  intro n
  rw [← ZMod.natCast_eq_zero_iff (n ^ 2 + 1) 1297]
  push_cast
  have hfac : (n : ZMod 1297) ^ 2 + 1 = ((n : ZMod 1297) - 36) * ((n : ZMod 1297) - 1261) := by
    calc (n : ZMod 1297) ^ 2 + 1
        = (n : ZMod 1297) ^ 2 - (36 + 1261 : ZMod 1297) * (n : ZMod 1297) + (36 * 1261 : ZMod 1297) := by
          rw [h1, h2]; ring
      _ = ((n : ZMod 1297) - 36) * ((n : ZMod 1297) - 1261) := by ring
  rw [hfac, mul_eq_zero, sub_eq_zero, sub_eq_zero]
  have hr1 : ((n : ZMod 1297) = 36) ↔ n % 1297 = 36 := by
    rw [show (36 : ZMod 1297) = ((36 : ℕ) : ZMod 1297) by norm_num, ZMod.natCast_eq_natCast_iff']
  have hr2 : ((n : ZMod 1297) = 1261) ↔ n % 1297 = 1261 := by
    rw [show (1261 : ZMod 1297) = ((1261 : ℕ) : ZMod 1297) by norm_num, ZMod.natCast_eq_natCast_iff']
  rw [hr1, hr2]
