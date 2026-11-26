import Mathlib

theorem PEqualNP.Outside.L_goldbach_exceptional_character_reflection :
    ∀ (d n : ℕ) [NeZero d] (χ : DirichletCharacter ℂ d), d ∣ n → χ^2 = 1 → (∑ a : (ZMod d)ˣ, χ (a : ZMod d) * χ ((n : ZMod d) - (a : ZMod d))) = (Nat.totient d : ℂ) * χ (-1) := by
  intro d n _ χ hdn h2
  have hn : (n : ZMod d) = 0 := by
    have h : ((n : ℤ) : ZMod d) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd (n : ℤ) d).mpr (by exact_mod_cast hdn)
    simpa using h
  have hterm : ∀ a : (ZMod d)ˣ, χ (a : ZMod d) * χ ((n : ZMod d) - (a : ZMod d)) = χ (-1) := by
    intro a
    have hsub : (n : ZMod d) - (a : ZMod d) = (-1 : ZMod d) * (a : ZMod d) := by
      rw [hn]; ring
    rw [hsub, map_mul]
    have hsq : χ (a : ZMod d) * χ (a : ZMod d) = 1 := by
      have h := congrArg (fun f : DirichletCharacter ℂ d => f (a : ZMod d)) h2
      rw [MulChar.pow_apply_coe, MulChar.one_apply_coe] at h
      rw [pow_two] at h
      exact h
    calc χ (a : ZMod d) * (χ (-1) * χ (a : ZMod d))
        = χ (-1) * (χ (a : ZMod d) * χ (a : ZMod d)) := by ring
      _ = χ (-1) * 1 := by rw [hsq]
      _ = χ (-1) := by ring
  calc (∑ a : (ZMod d)ˣ, χ (a : ZMod d) * χ ((n : ZMod d) - (a : ZMod d)))
      = ∑ a : (ZMod d)ˣ, χ (-1) := Finset.sum_congr rfl (fun a _ => hterm a)
    _ = (Fintype.card (ZMod d)ˣ : ℂ) * χ (-1) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = (Nat.totient d : ℂ) * χ (-1) := by
        rw [ZMod.card_units_eq_totient]
