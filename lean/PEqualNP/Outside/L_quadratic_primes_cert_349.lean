import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_349 :
    ∀ n:ℕ, 349∣n^2+1 ↔ n % 349=136 ∨ n % 349=213 := by
  intro n
  let : Fact (Nat.Prime 349) := ⟨by norm_num⟩
  have hsum : (136 + 213 : ZMod 349) = 0 := by decide
  have hprod : (136 * 213 : ZMod 349) = 1 := by decide
  have factor (z : ZMod 349) : (z - 136) * (z - 213) = z ^ 2 + 1 := by
    calc
      _ = z ^ 2 - (136 + 213) * z + 136 * 213 := by ring
      _ = _ := by simp only [hsum, hprod, zero_mul, sub_zero]
  have ha : ((n : ZMod 349) = 136) ↔ n % 349 = 136 :=
    ZMod.natCast_eq_natCast_iff' n 136 349
  have hb : ((n : ZMod 349) = 213) ↔ n % 349 = 213 :=
    ZMod.natCast_eq_natCast_iff' n 213 349
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_pow, Nat.cast_one,
    ← factor, mul_eq_zero]
  simp only [sub_eq_zero, ha, hb]
