import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_877 :
    ∀ n:ℕ, 877∣n^2+1 ↔ n % 877=151 ∨ n % 877=726 := by
  intro n
  let : Fact (Nat.Prime 877) := ⟨by norm_num⟩
  have hsum : (151 + 726 : ZMod 877) = 0 := by decide
  have hprod : (151 * 726 : ZMod 877) = 1 := by decide
  have factor (z : ZMod 877) : (z - 151) * (z - 726) = z ^ 2 + 1 := by
    calc
      _ = z ^ 2 - (151 + 726) * z + 151 * 726 := by ring
      _ = _ := by simp only [hsum, hprod, zero_mul, sub_zero]
  have ha : ((n : ZMod 877) = 151) ↔ n % 877 = 151 :=
    ZMod.natCast_eq_natCast_iff' n 151 877
  have hb : ((n : ZMod 877) = 726) ↔ n % 877 = 726 :=
    ZMod.natCast_eq_natCast_iff' n 726 877
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_pow, Nat.cast_one,
    ← factor, mul_eq_zero]
  simp only [sub_eq_zero, ha, hb]
