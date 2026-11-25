import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_809 :
    ∀ n:ℕ, 809∣n^2+1 ↔ n % 809=318 ∨ n % 809=491 := by
  intro n
  let : Fact (Nat.Prime 809) := ⟨by norm_num⟩
  have hsum : (318 + 491 : ZMod 809) = 0 := by decide
  have hprod : (318 * 491 : ZMod 809) = 1 := by decide
  have factor (z : ZMod 809) : (z - 318) * (z - 491) = z ^ 2 + 1 := by
    calc
      _ = z ^ 2 - (318 + 491) * z + 318 * 491 := by ring
      _ = _ := by simp only [hsum, hprod, zero_mul, sub_zero]
  have ha : ((n : ZMod 809) = 318) ↔ n % 809 = 318 :=
    ZMod.natCast_eq_natCast_iff' n 318 809
  have hb : ((n : ZMod 809) = 491) ↔ n % 809 = 491 :=
    ZMod.natCast_eq_natCast_iff' n 491 809
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_pow, Nat.cast_one,
    ← factor, mul_eq_zero]
  simp only [sub_eq_zero, ha, hb]
