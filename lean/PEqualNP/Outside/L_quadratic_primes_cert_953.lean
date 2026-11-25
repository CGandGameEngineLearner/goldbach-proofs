import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_953 :
    ∀ n:ℕ, 953∣n^2+1 ↔ n % 953=442 ∨ n % 953=511 := by
  intro n
  let : Fact (Nat.Prime 953) := ⟨by norm_num⟩
  have hsum : (442 + 511 : ZMod 953) = 0 := by decide
  have hprod : (442 * 511 : ZMod 953) = 1 := by decide
  have factor (z : ZMod 953) : (z - 442) * (z - 511) = z ^ 2 + 1 := by
    calc
      _ = z ^ 2 - (442 + 511) * z + 442 * 511 := by ring
      _ = _ := by simp only [hsum, hprod, zero_mul, sub_zero]
  have ha : ((n : ZMod 953) = 442) ↔ n % 953 = 442 :=
    ZMod.natCast_eq_natCast_iff' n 442 953
  have hb : ((n : ZMod 953) = 511) ↔ n % 953 = 511 :=
    ZMod.natCast_eq_natCast_iff' n 511 953
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_pow, Nat.cast_one,
    ← factor, mul_eq_zero]
  simp only [sub_eq_zero, ha, hb]
