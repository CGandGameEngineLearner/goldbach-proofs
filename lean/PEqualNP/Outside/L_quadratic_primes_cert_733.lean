import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_733 :
    ∀ n:ℕ, 733∣n^2+1 ↔ n % 733=353 ∨ n % 733=380 := by
  intro n
  let : Fact (Nat.Prime 733) := ⟨by norm_num⟩
  have hsum : (353 + 380 : ZMod 733) = 0 := by decide
  have hprod : (353 * 380 : ZMod 733) = 1 := by decide
  have factor (z : ZMod 733) : (z - 353) * (z - 380) = z ^ 2 + 1 := by
    calc
      _ = z ^ 2 - (353 + 380) * z + 353 * 380 := by ring
      _ = _ := by simp only [hsum, hprod, zero_mul, sub_zero]
  have ha : ((n : ZMod 733) = 353) ↔ n % 733 = 353 :=
    ZMod.natCast_eq_natCast_iff' n 353 733
  have hb : ((n : ZMod 733) = 380) ↔ n % 733 = 380 :=
    ZMod.natCast_eq_natCast_iff' n 380 733
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_pow, Nat.cast_one,
    ← factor, mul_eq_zero]
  simp only [sub_eq_zero, ha, hb]
