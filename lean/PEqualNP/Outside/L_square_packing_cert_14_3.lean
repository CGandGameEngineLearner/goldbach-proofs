import Mathlib

theorem PEqualNP.Outside.L_square_packing_cert_14_3 :
    ∀ x y L:ℝ, (∀ u v:ℝ, |u|≤1/2 → |v|≤1/2 → 0≤x+(187*u-84*v)/205 ∧ x+(187*u-84*v)/205≤L ∧ 0≤y+(84*u+187*v)/205 ∧ y+(84*u+187*v)/205≤L) ↔ (271:ℝ)/(2*205)≤x ∧ x≤L-(271:ℝ)/(2*205) ∧ (271:ℝ)/(2*205)≤y ∧ y≤L-(271:ℝ)/(2*205) := by
  intro x y L
  constructor
  · intro h
    have e1 := h (1/2) (1/2) (by norm_num) (by norm_num)
    have e2 := h (1/2) (-(1/2)) (by norm_num) (by norm_num)
    have e3 := h (-(1/2)) (1/2) (by norm_num) (by norm_num)
    have e4 := h (-(1/2)) (-(1/2)) (by norm_num) (by norm_num)
    norm_num at e1 e2 e3 e4
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
  · rintro ⟨hx1, hx2, hy1, hy2⟩ u v hu hv
    rw [abs_le] at hu hv
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith [hu.1, hu.2, hv.1, hv.2]
