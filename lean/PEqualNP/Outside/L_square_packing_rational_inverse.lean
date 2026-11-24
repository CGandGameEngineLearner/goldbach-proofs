import Mathlib

namespace PEqualNP.Outside

open scoped BigOperators

theorem L_square_packing_rational_inverse :
    ∀ c s:ℝ, c^2+s^2=1 → c≠ -1 → let t:=s/(1+c); (1-t^2)/(1+t^2)=c ∧ 2*t/(1+t^2)=s := by
  intro c s h hc
  have h1c : 1 + c ≠ 0 := by
    intro h0
    apply hc
    linarith
  dsimp only
  have hden : 1 + (s / (1 + c)) ^ 2 ≠ 0 := by positivity
  constructor
  · field_simp [h1c, hden]
    nlinarith [h]
  · field_simp [h1c, hden]
    linear_combination -s * h

end PEqualNP.Outside