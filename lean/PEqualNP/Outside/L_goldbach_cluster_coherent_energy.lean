import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.Fintype.Card

open scoped BigOperators

/-- Finite coherent energy retains the full index multiplicity, even for an empty family. -/
theorem PEqualNP.Outside.L_goldbach_cluster_coherent_energy :
    ∀ (m : ℕ) (u : Fin m → ℂ), ‖∑ i, u i‖^2 ≤ (m : ℝ)*∑ i, ‖u i‖^2 := by
  intro m u
  have htriangle : ‖∑ i, u i‖ ≤ ∑ i, ‖u i‖ :=
    norm_sum_le (Finset.univ : Finset (Fin m)) u
  have hcauchy : (∑ i, ‖u i‖) ^ 2 ≤ (m : ℝ) * ∑ i, ‖u i‖ ^ 2 := by
    simpa using Finset.sum_mul_sq_le_sq_mul_sq
      (Finset.univ : Finset (Fin m))
      (fun _ : Fin m => (1 : ℝ)) (fun i => ‖u i‖)
  exact (pow_le_pow_left₀ (norm_nonneg _) htriangle 2).trans hcauchy
