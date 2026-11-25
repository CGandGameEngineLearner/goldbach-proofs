import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_797 :
    ∀ n:ℕ, 797∣n^2+1 ↔ n % 797=215 ∨ n % 797=582 := by
  intro n
  let : Fact (Nat.Prime 797) := ⟨by norm_num⟩
  have hsum : (215 + 582 : ZMod 797) = 0 := by decide
  have hprod : (215 * 582 : ZMod 797) = 1 := by decide
  have factor (z : ZMod 797) : (z - 215) * (z - 582) = z ^ 2 + 1 := by
    calc
      _ = z ^ 2 - (215 + 582) * z + 215 * 582 := by ring
      _ = _ := by simp only [hsum, hprod, zero_mul, sub_zero]
  have ha : ((n : ZMod 797) = 215) ↔ n % 797 = 215 :=
    ZMod.natCast_eq_natCast_iff' n 215 797
  have hb : ((n : ZMod 797) = 582) ↔ n % 797 = 582 :=
    ZMod.natCast_eq_natCast_iff' n 582 797
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_pow, Nat.cast_one,
    ← factor, mul_eq_zero]
  simp only [sub_eq_zero, ha, hb]
