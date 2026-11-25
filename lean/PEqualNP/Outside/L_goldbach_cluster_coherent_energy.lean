import Mathlib

theorem PEqualNP.Outside.L_goldbach_cluster_coherent_energy :
    ∀ (m : ℕ) (u : Fin m → ℂ), ‖∑ i, u i‖^2 ≤ (m : ℝ)*∑ i, ‖u i‖^2 := by
  intro m u
  have h1 : ‖∑ i, u i‖ ≤ ∑ i, ‖u i‖ := norm_sum_le _ _
  have h2 : (∑ i, ‖u i‖)^2 ≤ (m : ℝ) * ∑ i, ‖u i‖^2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => ‖u i‖)
    simpa using h
  have h3 : ‖∑ i, u i‖^2 ≤ (∑ i, ‖u i‖)^2 :=
    pow_le_pow_left₀ (norm_nonneg _) h1 2
  exact h3.trans h2
