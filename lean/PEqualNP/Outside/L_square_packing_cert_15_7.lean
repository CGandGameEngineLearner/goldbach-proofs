import Mathlib

theorem PEqualNP.Outside.L_square_packing_cert_15_7 :
    ∀ x y L:ℝ, (∀ u v:ℝ, |u|≤1/2 → |v|≤1/2 → 0≤x+(176*u-210*v)/274 ∧ x+(176*u-210*v)/274≤L ∧ 0≤y+(210*u+176*v)/274 ∧ y+(210*u+176*v)/274≤L) ↔ (386:ℝ)/(2*274)≤x ∧ x≤L-(386:ℝ)/(2*274) ∧ (386:ℝ)/(2*274)≤y ∧ y≤L-(386:ℝ)/(2*274) := by
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
    have hxabs : |(176:ℝ)*u - (210:ℝ)*v| ≤ (386:ℝ)/2 := abs_le.mpr ⟨by linarith, by linarith⟩
    have hyabs : |(210:ℝ)*u + (176:ℝ)*v| ≤ (386:ℝ)/2 := abs_le.mpr ⟨by linarith, by linarith⟩
    have hxdiv : |((176:ℝ)*u - (210:ℝ)*v)/274| ≤ (386:ℝ)/(2*274) := by
      rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < (274:ℝ))]
      linarith
    have hydiv : |((210:ℝ)*u + (176:ℝ)*v)/274| ≤ (386:ℝ)/(2*274) := by
      rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < (274:ℝ))]
      linarith
    obtain ⟨hxa, hxb⟩ := abs_le.mp hxdiv
    obtain ⟨hya, hyb⟩ := abs_le.mp hydiv
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
