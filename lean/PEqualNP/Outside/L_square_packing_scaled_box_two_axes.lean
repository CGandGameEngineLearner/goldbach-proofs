import Mathlib

theorem PEqualNP.Outside.L_square_packing_scaled_box_two_axes :
  ∀ A B D x y L : ℝ, 0 ≤ A → 0 ≤ B → 0 < D → (let R := (A + B) / (2 * D); (∀ u v : ℝ, |u| ≤ 1 / 2 → |v| ≤ 1 / 2 → 0 ≤ x + (A * u - B * v) / D ∧ x + (A * u - B * v) / D ≤ L ∧ 0 ≤ y + (B * u + A * v) / D ∧ y + (B * u + A * v) / D ≤ L) ↔ R ≤ x ∧ x ≤ L - R ∧ R ≤ y ∧ y ≤ L - R) := by
  intro A B D x y L hA hB hD
  dsimp only
  constructor
  · intro h
    have h1 := h (-1 / 2) (1 / 2) (by norm_num) (by norm_num)
    have h2 := h (1 / 2) (-1 / 2) (by norm_num) (by norm_num)
    have h3 := h (-1 / 2) (-1 / 2) (by norm_num) (by norm_num)
    have h4 := h (1 / 2) (1 / 2) (by norm_num) (by norm_num)
    have e1 : (A * (-1 / 2) - B * (1 / 2)) / D = -((A + B) / (2 * D)) := by ring
    have e2 : (A * (1 / 2) - B * (-1 / 2)) / D = (A + B) / (2 * D) := by ring
    have e3 : (B * (-1 / 2) + A * (-1 / 2)) / D = -((A + B) / (2 * D)) := by ring
    have e4 : (B * (1 / 2) + A * (1 / 2)) / D = (A + B) / (2 * D) := by ring
    refine ⟨by linarith, by linarith, by linarith, by linarith⟩
  · rintro ⟨hx1, hx2, hy1, hy2⟩ u v hu hv
    have ⟨hu1, hu2⟩ := abs_le.mp hu
    have ⟨hv1, hv2⟩ := abs_le.mp hv
    have hxlo : -((A + B) / (2 * D)) ≤ (A * u - B * v) / D := by
      rw [show -((A + B) / (2 * D)) = (-(A + B) / 2) / D by ring]
      exact div_le_div_of_nonneg_right (by nlinarith) hD.le
    have hxhi : (A * u - B * v) / D ≤ (A + B) / (2 * D) := by
      rw [show (A + B) / (2 * D) = ((A + B) / 2) / D by ring]
      exact div_le_div_of_nonneg_right (by nlinarith) hD.le
    have hylo : -((A + B) / (2 * D)) ≤ (B * u + A * v) / D := by
      rw [show -((A + B) / (2 * D)) = (-(A + B) / 2) / D by ring]
      exact div_le_div_of_nonneg_right (by nlinarith) hD.le
    have hyhi : (B * u + A * v) / D ≤ (A + B) / (2 * D) := by
      rw [show (A + B) / (2 * D) = ((A + B) / 2) / D by ring]
      exact div_le_div_of_nonneg_right (by nlinarith) hD.le
    refine ⟨by linarith, by linarith, by linarith, by linarith⟩
