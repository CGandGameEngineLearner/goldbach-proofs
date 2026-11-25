import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_953 :
    ∀ n : ℕ, 953 ∣ n ^ 2 + 1 ↔ n % 953 = 442 ∨ n % 953 = 511 := by
  intro n
  letI : Fact (Nat.Prime 953) := ⟨by norm_num⟩
  have ha : ((n : ZMod 953) = 442) ↔ n % 953 = 442 :=
    ZMod.natCast_eq_natCast_iff' n 442 953
  have hb : ((n : ZMod 953) = 511) ↔ n % 953 = 511 :=
    ZMod.natCast_eq_natCast_iff' n 511 953
  have hr : (442 : ZMod 953) ^ 2 = -1 := by decide
  have hs : -(442 : ZMod 953) = 511 := by decide
  have hfac (z : ZMod 953) : z ^ 2 + 1 = (z - 442) * (z - 511) := calc
    z ^ 2 + 1 = z ^ 2 - (442 : ZMod 953) ^ 2 := by rw [hr] <;> ring
    _ = (z - 442) * (z - 511) := by rw [← hs] <;> ring
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_pow, Nat.cast_one, hfac]
  simp only [mul_eq_zero, sub_eq_zero, ha, hb]
