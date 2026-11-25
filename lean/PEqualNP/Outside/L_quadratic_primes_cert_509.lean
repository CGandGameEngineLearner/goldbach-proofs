import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_509 :
    ∀ n:ℕ, 509∣n^2+1 ↔ n % 509=208 ∨ n % 509=301 := by
  intro n
  let : Fact (Nat.Prime 509) := ⟨by norm_num⟩
  have hsum : (208 + 301 : ZMod 509) = 0 := by decide
  have hprod : (208 * 301 : ZMod 509) = 1 := by decide
  have factor (z : ZMod 509) : (z - 208) * (z - 301) = z ^ 2 + 1 := by
    calc
      _ = z ^ 2 - (208 + 301) * z + 208 * 301 := by ring
      _ = _ := by simp only [hsum, hprod, zero_mul, sub_zero]
  have ha : ((n : ZMod 509) = 208) ↔ n % 509 = 208 :=
    ZMod.natCast_eq_natCast_iff' n 208 509
  have hb : ((n : ZMod 509) = 301) ↔ n % 509 = 301 :=
    ZMod.natCast_eq_natCast_iff' n 301 509
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_pow, Nat.cast_one,
    ← factor, mul_eq_zero]
  simp only [sub_eq_zero, ha, hb]
