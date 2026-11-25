import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_277 :
    ∀ n:ℕ, 277∣n^2+1 ↔ n % 277=60 ∨ n % 277=217 := by
  intro n
  let : Fact (Nat.Prime 277) := ⟨by norm_num⟩
  have hsum : (60 + 217 : ZMod 277) = 0 := by decide
  have hprod : (60 * 217 : ZMod 277) = 1 := by decide
  have factor (z : ZMod 277) : (z - 60) * (z - 217) = z ^ 2 + 1 := by
    calc
      _ = z ^ 2 - (60 + 217) * z + 60 * 217 := by ring
      _ = _ := by simp only [hsum, hprod, zero_mul, sub_zero]
  have ha : ((n : ZMod 277) = 60) ↔ n % 277 = 60 :=
    ZMod.natCast_eq_natCast_iff' n 60 277
  have hb : ((n : ZMod 277) = 217) ↔ n % 277 = 217 :=
    ZMod.natCast_eq_natCast_iff' n 217 277
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_pow, Nat.cast_one,
    ← factor, mul_eq_zero]
  simp only [sub_eq_zero, ha, hb]
