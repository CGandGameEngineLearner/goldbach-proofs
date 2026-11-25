import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_877 :
    ∀ n : ℕ, 877 ∣ n ^ 2 + 1 ↔ n % 877 = 151 ∨ n % 877 = 726 := by
  intro n
  let : Fact (Nat.Prime 877) := ⟨by norm_num⟩
  have factor (x : ZMod 877) : x ^ 2 + 1 = (x - 151) * (x - 726) := by
    have hsum : (151 : ZMod 877) + 726 = 0 := by decide
    have hprod : (151 : ZMod 877) * 726 = 1 := by decide
    calc
      x ^ 2 + 1 = x ^ 2 - x * (151 + 726) + 151 * 726 := by
        rw [hsum, hprod, mul_zero, sub_zero]
      _ = (x - 151) * (x - 726) := by ring
  calc
    877 ∣ n ^ 2 + 1 ↔ (n : ZMod 877) ^ 2 + 1 = 0 := by
      rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_pow, Nat.cast_one]
    _ ↔ (n : ZMod 877) = 151 ∨ (n : ZMod 877) = 726 := by
      rw [factor]
      simp only [mul_eq_zero, sub_eq_zero]
    _ ↔ _ := or_congr (ZMod.natCast_eq_natCast_iff' n 151 877)
      (ZMod.natCast_eq_natCast_iff' n 726 877)
