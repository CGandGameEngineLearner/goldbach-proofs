import Mathlib

theorem PEqualNP.Outside.L_no_three_in_line_secant_slice :
    let d := fun (a b c : ℤ × ℤ) => (b.1-a.1)*(c.2-a.2)-(b.2-a.2)*(c.1-a.1); let ok := fun (S : Finset (ℤ × ℤ)) => ∀ a∈S, ∀ b∈S, ∀ c∈S, a≠b → b≠c → a≠c → d a b c≠0; ∀ (a b : ℤ × ℤ) (y x u : ℤ), a.2≠b.2 → d a b (x,y)=0 → d a b (u,y)=0 → x=u := by
  dsimp only
  intro a b y x u hab hx hu
  have hba : b.2 - a.2 ≠ 0 := sub_ne_zero.mpr hab.symm
  have hmul : (b.2 - a.2) * (x - u) = 0 := by
    linear_combination hu - hx
  rcases mul_eq_zero.mp hmul with h1 | h2
  · exact absurd h1 hba
  · linarith
