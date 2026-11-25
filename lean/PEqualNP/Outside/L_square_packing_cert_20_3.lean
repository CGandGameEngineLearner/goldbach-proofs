import Mathlib

theorem PEqualNP.Outside.L_square_packing_cert_20_3 : ∀ x y L:ℝ,
    (∀ u v:ℝ, |u|≤1/2 → |v|≤1/2 →
      0≤x+(391*u-120*v)/409 ∧ x+(391*u-120*v)/409≤L ∧
      0≤y+(120*u+391*v)/409 ∧ y+(120*u+391*v)/409≤L) ↔
    (511:ℝ)/(2*409)≤x ∧ x≤L-(511:ℝ)/(2*409) ∧
    (511:ℝ)/(2*409)≤y ∧ y≤L-(511:ℝ)/(2*409) := by
  intro x y L
  constructor
  · intro h
    have hA := h (-1/2) (1/2) (by norm_num) (by norm_num)
    have hB := h (1/2) (-1/2) (by norm_num) (by norm_num)
    have hC := h (-1/2) (-1/2) (by norm_num) (by norm_num)
    have hD := h (1/2) (1/2) (by norm_num) (by norm_num)
    norm_num at hA hB hC hD ⊢
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
  · intro h
    rcases h with ⟨hx1,hx2,hy1,hy2⟩
    intro u v hu hv
    have hu1 : -(1/2:ℝ) ≤ u := (abs_le.mp hu).1
    have hu2 : u ≤ 1/2 := (abs_le.mp hu).2
    have hv1 : -(1/2:ℝ) ≤ v := (abs_le.mp hv).1
    have hv2 : v ≤ 1/2 := (abs_le.mp hv).2
    constructor
    · nlinarith [hx1]
    constructor
    · nlinarith [hx2]
    constructor
    · nlinarith [hy1]
    · nlinarith [hy2]
