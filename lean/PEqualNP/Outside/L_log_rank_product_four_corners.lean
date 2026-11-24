import Mathlib

theorem PEqualNP.Outside.L_log_rank_product_four_corners :
    ∀ u v s t a : ℤ, u ≠ v → s ≠ t → ¬ ((u+s=a ∨ u+s=a+1) ∧ (u+t=a ∨ u+t=a+1) ∧ (v+s=a ∨ v+s=a+1) ∧ (v+t=a ∨ v+t=a+1)) := by
  intro u v s t a huv hst h
  omega
