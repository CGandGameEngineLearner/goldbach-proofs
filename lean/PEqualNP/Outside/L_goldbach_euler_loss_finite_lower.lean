import Mathlib

/-!
# L-goldbach-euler-loss-finite-lower

Each factor loses at most the norm it carries: `1 - ‖z i‖ ≤ ‖1 - z i‖`, and the
losses compound multiplicatively, so the norm of the full product still bounds
the product of the per-factor margins.
-/

theorem PEqualNP.Outside.L_goldbach_euler_loss_finite_lower :
    ∀ (n : ℕ) (z : Fin n → ℂ), (∀ i,‖z i‖≤1) → (∏ i, (1-‖z i‖))≤‖∏ i,(1-z i)‖ := by
  intro n z hz
  have hpt : ∀ i : Fin n, (1:ℝ) - ‖z i‖ ≤ ‖(1:ℂ) - z i‖ := by
    intro i
    have h2 := norm_sub_norm_le (1:ℂ) (z i)
    rw [norm_one] at h2
    exact h2
  have hnng : ∀ i : Fin n, 0 ≤ (1:ℝ) - ‖z i‖ := by
    intro i
    have hi := hz i
    linarith
  calc (∏ i : Fin n, ((1:ℝ) - ‖z i‖))
      ≤ ∏ i : Fin n, ‖(1:ℂ) - z i‖ :=
        Finset.prod_le_prod₀ (fun i _ ↦ hnng i) (fun i _ ↦ hpt i)
    _ = ‖∏ i : Fin n, ((1:ℂ) - z i)‖ := by rw [norm_prod]
