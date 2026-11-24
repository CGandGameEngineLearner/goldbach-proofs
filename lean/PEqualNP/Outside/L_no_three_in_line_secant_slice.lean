import Mathlib

namespace PEqualNP.Outside

open scoped BigOperators

theorem L_no_three_in_line_secant_slice :
    let d := fun (a b c : ℤ × ℤ) => (b.1-a.1)*(c.2-a.2)-(b.2-a.2)*(c.1-a.1); let ok := fun (S : Finset (ℤ × ℤ)) => ∀ a∈S, ∀ b∈S, ∀ c∈S, a≠b → b≠c → a≠c → d a b c≠0; ∀ (a b : ℤ × ℤ) (y x u : ℤ), a.2≠b.2 → d a b (x,y)=0 → d a b (u,y)=0 → x=u := by
  intro a b y x u hne h1 h2
  dsimp only at h1 h2
  have h1' : (b.1 - a.1) * (y - a.2) - (b.2 - a.2) * (x - a.1) = 0 := h1
  have h2' : (b.1 - a.1) * (y - a.2) - (b.2 - a.2) * (u - a.1) = 0 := h2
  have hB : b.2 - a.2 ≠ 0 := sub_ne_zero.mpr hne.symm
  have key : (b.2 - a.2) * (u - x) = 0 := by
    linear_combination h1' - h2'
  have hux : u - x = 0 := (mul_eq_zero.mp key).resolve_left hB
  exact (sub_eq_zero.mp hux).symm

end PEqualNP.Outside