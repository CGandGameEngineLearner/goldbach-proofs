import Mathlib.Data.Real.Basic
import Mathlib.Tactic

theorem PEqualNP.Outside.L_square_packing_cert_8_1 :
    ∀ x y L : ℝ,
      (∀ u v : ℝ, |u| ≤ 1 / 2 → |v| ≤ 1 / 2 →
        0 ≤ x + (63 * u - 16 * v) / 65 ∧ x + (63 * u - 16 * v) / 65 ≤ L ∧
        0 ≤ y + (16 * u + 63 * v) / 65 ∧ y + (16 * u + 63 * v) / 65 ≤ L) ↔
      ((79 : ℝ) / (2 * 65) ≤ x ∧ x ≤ L - (79 : ℝ) / (2 * 65) ∧
        (79 : ℝ) / (2 * 65) ≤ y ∧ y ≤ L - (79 : ℝ) / (2 * 65)) := by
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
    have hxlo : -(79 / 130 : ℝ) ≤ (63 * u - 16 * v) / 65 := by nlinarith [hu'.1, hu'.2, hv'.1, hv'.2]
    have hxhi : (63 * u - 16 * v) / 65 ≤ (79 / 130 : ℝ) := by nlinarith [hu'.1, hu'.2, hv'.1, hv'.2]
    have hylo : -(79 / 130 : ℝ) ≤ (16 * u + 63 * v) / 65 := by nlinarith [hu'.1, hu'.2, hv'.1, hv'.2]
    have hyhi : (16 * u + 63 * v) / 65 ≤ (79 / 130 : ℝ) := by nlinarith [hu'.1, hu'.2, hv'.1, hv'.2]
    constructor
    · linarith
    constructor
    · linarith
    constructor
    · linarith
    · linarith
