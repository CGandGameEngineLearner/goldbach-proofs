import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_173 :
    ∀ n:ℕ, 173∣n^2+1 ↔ n % 173=80 ∨ n % 173=93 := by
  intro n
  letI : Fact (Nat.Prime 173) := ⟨by decide⟩
  have hsum : (80 + 93 : ZMod 173) = 0 := by decide
  have hprod : (80 * 93 : ZMod 173) = 1 := by decide
  have factor (z : ZMod 173) : (z - 80) * (z - 93) = z ^ 2 + 1 := by
    calc
      _ = z ^ 2 - (80 + 93) * z + 80 * 93 := by ring
      _ = _ := by simp only [hsum, hprod, zero_mul, sub_zero]
  have ha : ((n : ZMod 173) = 80) ↔ n % 173 = 80 :=
    ZMod.natCast_eq_natCast_iff' n 80 173
  have hb : ((n : ZMod 173) = 93) ↔ n % 173 = 93 :=
    ZMod.natCast_eq_natCast_iff' n 93 173
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_pow, Nat.cast_one,
    ← factor, mul_eq_zero]
  simp only [sub_eq_zero, ha, hb]
