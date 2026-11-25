import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_401 :
    ∀ n:ℕ, 401∣n^2+1 ↔ n % 401=20 ∨ n % 401=381 := by
  intro n
  let : Fact (Nat.Prime 401) := ⟨by norm_num⟩
  have hsum : (20 + 381 : ZMod 401) = 0 := by decide
  have hprod : (20 * 381 : ZMod 401) = 1 := by decide
  have factor (z : ZMod 401) : (z - 20) * (z - 381) = z ^ 2 + 1 := by
    calc
      _ = z ^ 2 - (20 + 381) * z + 20 * 381 := by ring
      _ = _ := by simp only [hsum, hprod, zero_mul, sub_zero]
  have ha : ((n : ZMod 401) = 20) ↔ n % 401 = 20 :=
    ZMod.natCast_eq_natCast_iff' n 20 401
  have hb : ((n : ZMod 401) = 381) ↔ n % 401 = 381 :=
    ZMod.natCast_eq_natCast_iff' n 381 401
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_pow, Nat.cast_one,
    ← factor, mul_eq_zero]
  simp only [sub_eq_zero, ha, hb]
