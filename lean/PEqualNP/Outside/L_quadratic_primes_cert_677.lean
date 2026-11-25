import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_677 :
    ∀ n:ℕ, 677∣n^2+1 ↔ n % 677=26 ∨ n % 677=651 := by
  intro n
  let : Fact (Nat.Prime 677) := ⟨by norm_num⟩
  have hsum : (26 + 651 : ZMod 677) = 0 := by decide
  have hprod : (26 * 651 : ZMod 677) = 1 := by decide
  have factor (z : ZMod 677) : (z - 26) * (z - 651) = z ^ 2 + 1 := by
    calc
      _ = z ^ 2 - (26 + 651) * z + 26 * 651 := by ring
      _ = _ := by simp only [hsum, hprod, zero_mul, sub_zero]
  have ha : ((n : ZMod 677) = 26) ↔ n % 677 = 26 :=
    ZMod.natCast_eq_natCast_iff' n 26 677
  have hb : ((n : ZMod 677) = 651) ↔ n % 677 = 651 :=
    ZMod.natCast_eq_natCast_iff' n 651 677
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_pow, Nat.cast_one,
    ← factor, mul_eq_zero]
  simp only [sub_eq_zero, ha, hb]
