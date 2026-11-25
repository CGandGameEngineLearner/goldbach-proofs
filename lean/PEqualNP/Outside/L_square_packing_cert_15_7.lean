import Mathlib

theorem PEqualNP.Outside.L_square_packing_cert_15_7 :
    ∀ x y L:ℝ, (∀ u v:ℝ, |u|≤1/2 → |v|≤1/2 → 0≤x+(176*u-210*v)/274 ∧ x+(176*u-210*v)/274≤L ∧ 0≤y+(210*u+176*v)/274 ∧ y+(210*u+176*v)/274≤L) ↔ (386:ℝ)/(2*274)≤x ∧ x≤L-(386:ℝ)/(2*274) ∧ (386:ℝ)/(2*274)≤y ∧ y≤L-(386:ℝ)/(2*274) := by
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
