import Mathlib

theorem PEqualNP.Outside.L_square_packing_cert_13_5 :
    ∀ x y L:ℝ, (∀ u v:ℝ, |u|≤1/2 → |v|≤1/2 → 0≤x+(144*u-130*v)/194 ∧ x+(144*u-130*v)/194≤L ∧ 0≤y+(130*u+144*v)/194 ∧ y+(130*u+144*v)/194≤L) ↔ (274:ℝ)/(2*194)≤x ∧ x≤L-(274:ℝ)/(2*194) ∧ (274:ℝ)/(2*194)≤y ∧ y≤L-(274:ℝ)/(2*194) := by
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
