import Mathlib

theorem PEqualNP.Outside.L_square_packing_cert_20_3 :
    ∀ x y L:ℝ, (∀ u v:ℝ, |u|≤1/2 → |v|≤1/2 → 0≤x+(391*u-120*v)/409 ∧ x+(391*u-120*v)/409≤L ∧ 0≤y+(120*u+391*v)/409 ∧ y+(120*u+391*v)/409≤L) ↔ (511:ℝ)/(2*409)≤x ∧ x≤L-(511:ℝ)/(2*409) ∧ (511:ℝ)/(2*409)≤y ∧ y≤L-(511:ℝ)/(2*409) := by
  intro x y L
  constructor
  · intro h
    have h1 := (h (-(1 / 2)) (1 / 2) (by norm_num) (by norm_num)).1
    have e1 : ((391 : ℝ) * (-(1 / 2)) - (120 : ℝ) * (1 / 2)) / (409 : ℝ) = -((511 : ℝ) / (2 * 409)) := by
      norm_num
    rw [e1] at h1
    have h2 := (h (1 / 2) (-(1 / 2)) (by norm_num) (by norm_num)).2.1
    have e2 : ((391 : ℝ) * (1 / 2) - (120 : ℝ) * (-(1 / 2))) / (409 : ℝ) = (511 : ℝ) / (2 * 409) := by
      norm_num
    rw [e2] at h2
    have h3 := (h (-(1 / 2)) (-(1 / 2)) (by norm_num) (by norm_num)).2.2.1
    have e3 : ((120 : ℝ) * (-(1 / 2)) + (391 : ℝ) * (-(1 / 2))) / (409 : ℝ) = -((511 : ℝ) / (2 * 409)) := by
      norm_num
    rw [e3] at h3
    have h4 := (h (1 / 2) (1 / 2) (by norm_num) (by norm_num)).2.2.2
    have e4 : ((120 : ℝ) * (1 / 2) + (391 : ℝ) * (1 / 2)) / (409 : ℝ) = (511 : ℝ) / (2 * 409) := by
      norm_num
    rw [e4] at h4
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  · rintro ⟨hx0, hxL, hy0, hyL⟩ u v hu hv
    have hu' : -(1 / 2) ≤ u ∧ u ≤ 1 / 2 := abs_le.mp hu
    have hv' : -(1 / 2) ≤ v ∧ v ≤ 1 / 2 := abs_le.mp hv
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      linarith [hu'.1, hu'.2, hv'.1, hv'.2, hx0, hxL, hy0, hyL]
