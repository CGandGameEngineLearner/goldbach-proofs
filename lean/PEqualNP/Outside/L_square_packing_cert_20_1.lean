import Mathlib

theorem PEqualNP.Outside.L_square_packing_cert_20_1 :
    ∀ x y L:ℝ, (∀ u v:ℝ, |u|≤1/2 → |v|≤1/2 → 0≤x+(399*u-40*v)/401 ∧ x+(399*u-40*v)/401≤L ∧ 0≤y+(40*u+399*v)/401 ∧ y+(40*u+399*v)/401≤L) ↔ (439:ℝ)/(2*401)≤x ∧ x≤L-(439:ℝ)/(2*401) ∧ (439:ℝ)/(2*401)≤y ∧ y≤L-(439:ℝ)/(2*401) := by
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
    have hxabs : |(399:ℝ)*u - (40:ℝ)*v| ≤ (439:ℝ)/2 := abs_le.mpr ⟨by linarith, by linarith⟩
    have hyabs : |(40:ℝ)*u + (399:ℝ)*v| ≤ (439:ℝ)/2 := abs_le.mpr ⟨by linarith, by linarith⟩
    have hxdiv : |((399:ℝ)*u - (40:ℝ)*v)/401| ≤ (439:ℝ)/(2*401) := by
      rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < (401:ℝ))]
      linarith
    have hydiv : |((40:ℝ)*u + (399:ℝ)*v)/401| ≤ (439:ℝ)/(2*401) := by
      rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < (401:ℝ))]
      linarith
    obtain ⟨hxa, hxb⟩ := abs_le.mp hxdiv
    obtain ⟨hya, hyb⟩ := abs_le.mp hydiv
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
