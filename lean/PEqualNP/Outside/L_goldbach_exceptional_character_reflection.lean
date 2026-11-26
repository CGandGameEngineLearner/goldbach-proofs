import Mathlib

theorem PEqualNP.Outside.L_goldbach_exceptional_character_reflection :
    ∀ (d n : ℕ) [NeZero d] (χ : DirichletCharacter ℂ d), d ∣ n → χ^2 = 1 → (∑ a : (ZMod d)ˣ, χ (a : ZMod d) * χ ((n : ZMod d) - (a : ZMod d))) = (Nat.totient d : ℂ) * χ (-1) := by
  intro d n hd χ hdn hχ2
  have hn0 : (n : ZMod d) = 0 := by
    rcases hdn with ⟨k, rfl⟩
    rw [Nat.cast_mul, CharP.cast_eq_zero, zero_mul]
  have hterm : ∀ a : (ZMod d)ˣ, χ (a : ZMod d) * χ ((n : ZMod d) - (a : ZMod d)) = χ (-1) := by
    intro a
    rw [hn0, zero_sub]
    have hneg : (-(a : ZMod d)) = (a : ZMod d) * (-1 : ZMod d) := by ring
    rw [hneg, map_mul, ← mul_assoc]
    have hsq : χ (a : ZMod d) * χ (a : ZMod d) = (χ ^ 2) (a : ZMod d) := by
      rw [sq, MulChar.mul_apply]
    rw [hsq, hχ2, MulChar.one_apply a.isUnit, one_mul]
  simp_rw [hterm, Finset.sum_const, Finset.card_univ, ZMod.card_units_eq_totient, nsmul_eq_mul]
