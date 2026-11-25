import Mathlib

theorem PEqualNP.Outside.L_square_packing_cert_5_2 :
    ∀ x y L:ℝ, (∀ u v:ℝ, |u|≤1/2 → |v|≤1/2 → 0≤x+(21*u-20*v)/29 ∧ x+(21*u-20*v)/29≤L ∧ 0≤y+(20*u+21*v)/29 ∧ y+(20*u+21*v)/29≤L) ↔ (41:ℝ)/(2*29)≤x ∧ x≤L-(41:ℝ)/(2*29) ∧ (41:ℝ)/(2*29)≤y ∧ y≤L-(41:ℝ)/(2*29) := by
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
