import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_769 :
    ∀ n:ℕ, 769∣n^2+1 ↔ n % 769=62 ∨ n % 769=707 := by
  intro n
  let : Fact (Nat.Prime 769) := ⟨by norm_num⟩
  have hsum : (62 + 707 : ZMod 769) = 0 := by decide
  have hprod : (62 * 707 : ZMod 769) = 1 := by decide
  have factor (z : ZMod 769) : (z - 62) * (z - 707) = z ^ 2 + 1 := by
    calc
      _ = z ^ 2 - (62 + 707) * z + 62 * 707 := by ring
      _ = _ := by simp only [hsum, hprod, zero_mul, sub_zero]
  have ha : ((n : ZMod 769) = 62) ↔ n % 769 = 62 :=
    ZMod.natCast_eq_natCast_iff' n 62 769
  have hb : ((n : ZMod 769) = 707) ↔ n % 769 = 707 :=
    ZMod.natCast_eq_natCast_iff' n 707 769
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_pow, Nat.cast_one,
    ← factor, mul_eq_zero]
  simp only [sub_eq_zero, ha, hb]
