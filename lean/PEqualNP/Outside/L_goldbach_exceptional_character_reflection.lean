import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Basic.Complex.Basic

/-! Reflection of a quadratic Dirichlet character at a multiple of its modulus. -/

theorem PEqualNP.Outside.L_goldbach_exceptional_character_reflection :
    ∀ (d n : ℕ) [NeZero d] (χ : DirichletCharacter ℂ d), d ∣ n → χ^2 = 1 → (∑ a : (ZMod d)ˣ, χ (a : ZMod d) * χ ((n : ZMod d) - (a : ZMod d))) = (Nat.totient d : ℂ) * χ (-1) := by
  intro d n _ χ hd hχ
  have hn : (n : ZMod d) = 0 := (ZMod.natCast_eq_zero_iff n d).2 hd
  have href (a : (ZMod d)ˣ) :
      χ (a : ZMod d) * χ ((n : ZMod d) - (a : ZMod d)) = χ (-1) := by
    have hs : χ (a : ZMod d) ^ 2 = 1 := by
      rw [← MulChar.pow_apply_coe, hχ, MulChar.one_apply_coe]
    rw [hn, zero_sub, ← neg_one_mul (a : ZMod d), map_mul]
    calc
      χ (a : ZMod d) * (χ (-1) * χ (a : ZMod d)) =
          χ (-1) * (χ (a : ZMod d) ^ 2) := by rw [pow_two]; ac_rfl
      _ = χ (-1) := by rw [hs, mul_one]
  simp only [href, Finset.sum_const, Finset.card_univ, ZMod.card_units_eq_totient, nsmul_eq_mul]
