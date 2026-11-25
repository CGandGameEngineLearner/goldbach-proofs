import Mathlib

/-!
# Refine the remaining exceptional set

A target `n` left over after the second stage (`n ∉ V`) is handled by the second team if `n ∈ U`; otherwise it was left over after the first stage (`n ∉ U`) and the first team handles it.
-/

theorem PEqualNP.Outside.L_goldbach_finite_exception_cover_refinement :
    ∀ (D U V : Finset ℕ) (G : ℕ → Prop), (∀ n ∈ D, n ∉ U → G n) → (∀ n ∈ U, n ∉ V → G n) → ∀ n ∈ D, n ∉ V → G n := by
  intro D U V G h1 h2 n hn hnV
  by_cases hU : n ∈ U
  · exact h2 n hU hnV
  · exact h1 n hn hU
