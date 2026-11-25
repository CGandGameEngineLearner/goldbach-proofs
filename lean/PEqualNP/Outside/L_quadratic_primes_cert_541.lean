import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_541 :
    ∀ n:ℕ, 541∣n^2+1 ↔ n % 541=52 ∨ n % 541=489 := by
  intro n
  let : Fact (Nat.Prime 541) := ⟨by norm_num⟩
  have hsum : (52 + 489 : ZMod 541) = 0 := by decide
  have hprod : (52 * 489 : ZMod 541) = 1 := by decide
  have factor (z : ZMod 541) : (z - 52) * (z - 489) = z ^ 2 + 1 := by
    calc
      _ = z ^ 2 - (52 + 489) * z + 52 * 489 := by ring
      _ = _ := by simp only [hsum, hprod, zero_mul, sub_zero]
  have ha : ((n : ZMod 541) = 52) ↔ n % 541 = 52 :=
    ZMod.natCast_eq_natCast_iff' n 52 541
  have hb : ((n : ZMod 541) = 489) ↔ n % 541 = 489 :=
    ZMod.natCast_eq_natCast_iff' n 489 541
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_pow, Nat.cast_one,
    ← factor, mul_eq_zero]
  simp only [sub_eq_zero, ha, hb]
