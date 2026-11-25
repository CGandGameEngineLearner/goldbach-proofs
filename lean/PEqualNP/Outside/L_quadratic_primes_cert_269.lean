import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_269 :
    ∀ n:ℕ, 269∣n^2+1 ↔ n % 269=82 ∨ n % 269=187 := by
  intro n
  let : Fact (Nat.Prime 269) := ⟨by norm_num⟩
  have hsum : (82 + 187 : ZMod 269) = 0 := by decide
  have hprod : (82 * 187 : ZMod 269) = 1 := by decide
  have factor (z : ZMod 269) : (z - 82) * (z - 187) = z ^ 2 + 1 := by
    calc
      _ = z ^ 2 - (82 + 187) * z + 82 * 187 := by ring
      _ = _ := by simp only [hsum, hprod, zero_mul, sub_zero]
  have ha : ((n : ZMod 269) = 82) ↔ n % 269 = 82 :=
    ZMod.natCast_eq_natCast_iff' n 82 269
  have hb : ((n : ZMod 269) = 187) ↔ n % 269 = 187 :=
    ZMod.natCast_eq_natCast_iff' n 187 269
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_pow, Nat.cast_one,
    ← factor, mul_eq_zero]
  simp only [sub_eq_zero, ha, hb]
