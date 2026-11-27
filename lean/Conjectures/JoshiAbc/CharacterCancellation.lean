import Mathlib

namespace Conjectures.JoshiAbc.CharacterCancellation_aux

private theorem shift_sum
    {p n : ℕ} (H : Submodule (ZMod p) (Fin n → ZMod p)) [Fintype H]
    (χ : (Fin n → ZMod p) → ℂ) (b : Fin n → ZMod p) (k : H) :
    (∑ h : H, χ (b + (h + k).val)) = ∑ h : H, χ (b + h.val) := by
  apply Fintype.sum_equiv (Equiv.addLeft k)
  intro h
  simp [add_comm]

private theorem shift_term
    {p n : ℕ} (H : Submodule (ZMod p) (Fin n → ZMod p))
    (χ : (Fin n → ZMod p) → ℂ) (b : Fin n → ZMod p)
    (hχ : ∀ x y, χ (x + y) = χ x * χ y) (h k : H) :
    χ (b + (h + k).val) = χ k.val * χ (b + h.val) := by
  calc
    χ (b + (h + k).val) = χ ((b + h.val) + k.val) := by
      rw [Submodule.coe_add]
      congr 1
      abel
    _ = χ (b + h.val) * χ k.val := hχ _ _
    _ = χ k.val * χ (b + h.val) := mul_comm _ _

end Conjectures.JoshiAbc.CharacterCancellation_aux

theorem Conjectures.JoshiAbc.CharacterCancellation :
    ∀ (p n : ℕ) [Fact p.Prime] (H : Submodule (ZMod p) (Fin n → ZMod p)) [Fintype H]
      (χ : (Fin n → ZMod p) → ℂ) (b : Fin n → ZMod p),
      (∀ x y, χ (x + y) = χ x * χ y) →
      (∃ h : H, χ h.val ≠ 1) →
      (∑ h : H, χ (b + h.val)) = 0 := by
  intro p n _ H _ χ b hχ hnontriv
  obtain ⟨k, hk⟩ := hnontriv
  let S := ∑ h : H, χ (b + h.val)
  have hshift := CharacterCancellation_aux.shift_sum H χ b k
  have hterm (h : H) := CharacterCancellation_aux.shift_term H χ b hχ h k
  have hfactor :
      (∑ h : H, χ (b + (h + k).val)) = χ k.val * S := by
    simp_rw [hterm]
    dsimp [S]
    rw [Finset.mul_sum]
  have hEq : S = χ k.val * S := by
    exact hshift.symm.trans hfactor
  have hmul : (1 - χ k.val) * S = 0 := by
    calc
      (1 - χ k.val) * S = S - χ k.val * S := one_sub_mul _ _
      _ = 0 := sub_eq_zero.mpr hEq
  have hne : 1 - χ k.val ≠ 0 := sub_ne_zero.mpr (Ne.symm hk)
  exact (mul_eq_zero.mp hmul).resolve_left hne
