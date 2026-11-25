import Mathlib.Data.Real.Basic
import Mathlib.Tactic

theorem PEqualNP.Outside.L_square_packing_cert_10_1 :
    ∀ x y L : ℝ,
      (∀ u v : ℝ, |u| ≤ 1 / 2 → |v| ≤ 1 / 2 →
        0 ≤ x + (99 * u - 20 * v) / 101 ∧ x + (99 * u - 20 * v) / 101 ≤ L ∧
        0 ≤ y + (20 * u + 99 * v) / 101 ∧ y + (20 * u + 99 * v) / 101 ≤ L) ↔
      ((119 : ℝ) / (2 * 101) ≤ x ∧ x ≤ L - (119 : ℝ) / (2 * 101) ∧
        (119 : ℝ) / (2 * 101) ≤ y ∧ y ≤ L - (119 : ℝ) / (2 * 101)) := by
  intro x y L
  constructor
  · intro H
    have hx1 := (H (-1 / 2) (1 / 2) (by norm_num) (by norm_num)).1
    have hx2 := (H (1 / 2) (-1 / 2) (by norm_num) (by norm_num)).2.1
    have hy1 := (H (-1 / 2) (-1 / 2) (by norm_num) (by norm_num)).2.2.1
    have hy2 := (H (1 / 2) (1 / 2) (by norm_num) (by norm_num)).2.2.2
    norm_num at hx1 hx2 hy1 hy2
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  · rintro ⟨hx1, hx2, hy1, hy2⟩ u v hu hv
    have hu' := abs_le.mp hu
    have hv' := abs_le.mp hv
    have hxlo : -(119 / 202 : ℝ) ≤ (99 * u - 20 * v) / 101 := by nlinarith [hu'.1, hu'.2, hv'.1, hv'.2]
    have hxhi : (99 * u - 20 * v) / 101 ≤ (119 / 202 : ℝ) := by nlinarith [hu'.1, hu'.2, hv'.1, hv'.2]
    have hylo : -(119 / 202 : ℝ) ≤ (20 * u + 99 * v) / 101 := by nlinarith [hu'.1, hu'.2, hv'.1, hv'.2]
    have hyhi : (20 * u + 99 * v) / 101 ≤ (119 / 202 : ℝ) := by nlinarith [hu'.1, hu'.2, hv'.1, hv'.2]
    constructor
    · linarith
    constructor
    · linarith
    constructor
    · linarith
    · linarith
