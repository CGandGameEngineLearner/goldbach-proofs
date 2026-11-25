import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_389 :
    ∀ n:ℕ, 389∣n^2+1 ↔ n % 389=115 ∨ n % 389=274 := by
  intro n
  let : Fact (Nat.Prime 389) := ⟨by norm_num⟩
  have hsum : (115 + 274 : ZMod 389) = 0 := by decide
  have hprod : (115 * 274 : ZMod 389) = 1 := by decide
  have factor (z : ZMod 389) : (z - 115) * (z - 274) = z ^ 2 + 1 := by
    calc
      _ = z ^ 2 - (115 + 274) * z + 115 * 274 := by ring
      _ = _ := by simp only [hsum, hprod, zero_mul, sub_zero]
  have ha : ((n : ZMod 389) = 115) ↔ n % 389 = 115 :=
    ZMod.natCast_eq_natCast_iff' n 115 389
  have hb : ((n : ZMod 389) = 274) ↔ n % 389 = 274 :=
    ZMod.natCast_eq_natCast_iff' n 274 389
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_pow, Nat.cast_one,
    ← factor, mul_eq_zero]
  simp only [sub_eq_zero, ha, hb]
