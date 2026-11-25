import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_457 :
    ∀ n:ℕ, 457∣n^2+1 ↔ n % 457=109 ∨ n % 457=348 := by
  intro n
  let : Fact (Nat.Prime 457) := ⟨by norm_num⟩
  have hsum : (109 + 348 : ZMod 457) = 0 := by decide
  have hprod : (109 * 348 : ZMod 457) = 1 := by decide
  have factor (z : ZMod 457) : (z - 109) * (z - 348) = z ^ 2 + 1 := by
    calc
      _ = z ^ 2 - (109 + 348) * z + 109 * 348 := by ring
      _ = _ := by simp only [hsum, hprod, zero_mul, sub_zero]
  have ha : ((n : ZMod 457) = 109) ↔ n % 457 = 109 :=
    ZMod.natCast_eq_natCast_iff' n 109 457
  have hb : ((n : ZMod 457) = 348) ↔ n % 457 = 348 :=
    ZMod.natCast_eq_natCast_iff' n 348 457
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_pow, Nat.cast_one,
    ← factor, mul_eq_zero]
  simp only [sub_eq_zero, ha, hb]
