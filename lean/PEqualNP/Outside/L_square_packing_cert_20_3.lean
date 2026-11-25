import Mathlib

theorem PEqualNP.Outside.L_square_packing_cert_20_3 :
    ∀ x y L:ℝ, (∀ u v:ℝ, |u|≤1/2 → |v|≤1/2 → 0≤x+(391*u-120*v)/409 ∧ x+(391*u-120*v)/409≤L ∧ 0≤y+(120*u+391*v)/409 ∧ y+(120*u+391*v)/409≤L) ↔ (511:ℝ)/(2*409)≤x ∧ x≤L-(511:ℝ)/(2*409) ∧ (511:ℝ)/(2*409)≤y ∧ y≤L-(511:ℝ)/(2*409) := by
  intro x y L
  constructor
  · intro h
    -- The four corners of the half-unit square give the necessary one-sided bounds.
    have hxL : x + (391 * (1/2:ℝ) - 120 * (-1/2:ℝ)) / 409 ≤ L :=
      (h (1/2) (-1/2) (by norm_num) (by norm_num)).2.1
    have hx0 : 0 ≤ x + (391 * (-1/2:ℝ) - 120 * (1/2:ℝ)) / 409 :=
      (h (-1/2) (1/2) (by norm_num) (by norm_num)).1
    have hyL : y + (120 * (1/2:ℝ) + 391 * (1/2:ℝ)) / 409 ≤ L :=
      (h (1/2) (1/2) (by norm_num) (by norm_num)).2.2.2
    have hy0 : 0 ≤ y + (120 * (-1/2:ℝ) + 391 * (-1/2:ℝ)) / 409 :=
      (h (-1/2) (-1/2) (by norm_num) (by norm_num)).2.2.1
    refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith
  · rintro ⟨hx0, hxL, hy0, hyL⟩ u v hu hv
    -- Orthogonality: every corner displacement has modulus at most (391+120)/(2*409).
    have hu := abs_le.mp hu
    have hv := abs_le.mp hv
    refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith
