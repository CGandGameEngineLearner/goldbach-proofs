import PEqualNP.Defs

set_option maxRecDepth 80000 in
theorem PEqualNP.Outside.L_goldbach_finite_residue_rough_2310 :
    ∀ a : ℕ, a < 2310 → Even a → ∃ p ∈ ({3,5,7,11,29,61,79} : Finset ℕ), Nat.Coprime ((a+2310-p)%2310) 2310 := by
  decide
