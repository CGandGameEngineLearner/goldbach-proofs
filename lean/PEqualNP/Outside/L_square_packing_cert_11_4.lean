import Mathlib

theorem PEqualNP.Outside.L_square_packing_cert_11_4 :
    ∀ x y L:ℝ, (∀ u v:ℝ, |u|≤1/2 → |v|≤1/2 → 0≤x+(105*u-88*v)/137 ∧ x+(105*u-88*v)/137≤L ∧ 0≤y+(88*u+105*v)/137 ∧ y+(88*u+105*v)/137≤L) ↔ (193:ℝ)/(2*137)≤x ∧ x≤L-(193:ℝ)/(2*137) ∧ (193:ℝ)/(2*137)≤y ∧ y≤L-(193:ℝ)/(2*137) := by
  intro x y L
  constructor
  · intro h
    obtain ⟨hx1, -, -, -⟩ := h (-(1/2)) (1/2) (by norm_num) (by norm_num)
    obtain ⟨-, hx2, -, -⟩ := h (1/2) (-(1/2)) (by norm_num) (by norm_num)
    obtain ⟨-, -, hy1, -⟩ := h (-(1/2)) (-(1/2)) (by norm_num) (by norm_num)
    obtain ⟨-, -, -, hy2⟩ := h (1/2) (1/2) (by norm_num) (by norm_num)
    norm_num at hx1 hx2 hy1 hy2
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  · intro h u v hu hv
    obtain ⟨hx1, hx2, hy1, hy2⟩ := h
    have hu1 : -((1:ℝ)/2) ≤ u := by linarith [neg_abs_le u]
    have hu2 : u ≤ (1:ℝ)/2 := by linarith [le_abs_self u]
    have hv1 : -((1:ℝ)/2) ≤ v := by linarith [neg_abs_le v]
    have hv2 : v ≤ (1:ℝ)/2 := by linarith [le_abs_self v]
    have hxabs : |(105:ℝ)*u - (88:ℝ)*v| ≤ (193:ℝ)/2 := abs_le.mpr ⟨by linarith, by linarith⟩
    have hyabs : |(88:ℝ)*u + (105:ℝ)*v| ≤ (193:ℝ)/2 := abs_le.mpr ⟨by linarith, by linarith⟩
    have hxdiv : |((105:ℝ)*u - (88:ℝ)*v)/137| ≤ (193:ℝ)/(2*137) := by
      rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < (137:ℝ))]
      linarith
    have hydiv : |((88:ℝ)*u + (105:ℝ)*v)/137| ≤ (193:ℝ)/(2*137) := by
      rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < (137:ℝ))]
      linarith
    obtain ⟨hxa, hxb⟩ := abs_le.mp hxdiv
    obtain ⟨hya, hyb⟩ := abs_le.mp hydiv
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
