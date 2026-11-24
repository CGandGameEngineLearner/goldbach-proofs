import Mathlib

theorem PEqualNP.Outside.L_goldbach_euler_loss_finite_lower :
    ∀ (n : ℕ) (z : Fin n → ℂ), (∀ i,‖z i‖≤1) → (∏ i, (1-‖z i‖))≤‖∏ i,(1-z i)‖ := by
  intro n z hz
  rw [norm_prod]
  refine Finset.prod_le_prod₀ (fun i _ => sub_nonneg.mpr (hz i)) (fun i _ => ?_)
  have htri : (1 : ℝ) ≤ ‖1 - z i‖ + ‖z i‖ := by
    simpa [sub_add_cancel] using norm_add_le (1 - z i) (z i)
  linarith
