import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.DirichletCharacter.Basic

namespace PEqualNP.Outside

theorem L_goldbach_exceptional_character_reflection
    (d n : ℕ) [NeZero d] (χ : DirichletCharacter ℂ d)
    (hd : d ∣ n) (hχ : χ ^ 2 = 1) :
    (∑ a : (ZMod d)ˣ,
      χ (a : ZMod d) * χ ((n : ZMod d) - (a : ZMod d))) =
      (Nat.totient d : ℂ) * χ (-1) := by
  classical
  have hn : (n : ZMod d) = 0 := (ZMod.natCast_eq_zero_iff n d).2 hd
  have hsq (a : (ZMod d)ˣ) : χ (a : ZMod d) * χ (a : ZMod d) = 1 := by
    rw [← pow_two, ← MulChar.pow_apply_coe, hχ, MulChar.one_apply_coe]
  calc
    (∑ a : (ZMod d)ˣ,
        χ (a : ZMod d) * χ ((n : ZMod d) - (a : ZMod d))) =
        ∑ _a : (ZMod d)ˣ, χ (-1) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [hn, zero_sub, ← neg_one_mul (a : ZMod d), map_mul]
      calc
        χ (a : ZMod d) * (χ (-1) * χ (a : ZMod d)) =
            χ (-1) * (χ (a : ZMod d) * χ (a : ZMod d)) := by ac_rfl
        _ = χ (-1) := by rw [hsq a, mul_one]
    _ = (Nat.totient d : ℂ) * χ (-1) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        ZMod.card_units_eq_totient]

end PEqualNP.Outside
