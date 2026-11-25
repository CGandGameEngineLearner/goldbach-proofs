import Mathlib

theorem PEqualNP.Outside.L_square_packing_scaled_box_extrema :
    ∀ A B D x L : ℝ, 0≤A → 0≤B → 0<D → ((∀ u v : ℝ, |u|≤1/2 → |v|≤1/2 → 0≤x+(A*u-B*v)/D ∧ x+(A*u-B*v)/D≤L) ↔ (A+B)/(2*D)≤x ∧ x≤L-(A+B)/(2*D)) := by
  intro A B D x L hA hB hD
  have hbound : ∀ u v : ℝ, |u| ≤ 1/2 → |v| ≤ 1/2 → |A*u - B*v| ≤ (A+B)/2 := by
    intro u v hu hv
    have h1 : |A*u| ≤ A/2 := by
      rw [abs_mul, abs_of_nonneg hA]
      nlinarith [mul_le_mul_of_nonneg_left hu hA]
    have h2 : |B*v| ≤ B/2 := by
      rw [abs_mul, abs_of_nonneg hB]
      nlinarith [mul_le_mul_of_nonneg_left hv hB]
    calc |A*u - B*v| ≤ |A*u| + |B*v| := abs_sub _ _
      _ ≤ (A+B)/2 := by linarith
  have key1 : -((A+B)/2)/D = -((A+B)/(2*D)) := by field_simp
  have key2 : ((A+B)/2)/D = (A+B)/(2*D) := by field_simp
  constructor
  · intro h
    have hp := (h (-1/2) (1/2) (by norm_num) (by norm_num)).1
    have hq := (h (1/2) (-1/2) (by norm_num) (by norm_num)).2
    have e1 : A*(-1/2) - B*(1/2) = -((A+B)/2) := by ring
    have e2 : A*(1/2) - B*(-1/2) = (A+B)/2 := by ring
    rw [e1] at hp
    rw [e2] at hq
    rw [key1] at hp
    rw [key2] at hq
    constructor
    · linarith
    · linarith
  · rintro ⟨hx0, hxL⟩ u v hu hv
    have hz := abs_le.1 (hbound u v hu hv)
    have hdiv1 : -((A+B)/2)/D ≤ (A*u - B*v)/D :=
      div_le_div_of_nonneg_right hz.1 (le_of_lt hD)
    have hdiv2 : (A*u - B*v)/D ≤ ((A+B)/2)/D :=
      div_le_div_of_nonneg_right hz.2 (le_of_lt hD)
    rw [key1] at hdiv1
    rw [key2] at hdiv2
    constructor
    · linarith
    · linarith