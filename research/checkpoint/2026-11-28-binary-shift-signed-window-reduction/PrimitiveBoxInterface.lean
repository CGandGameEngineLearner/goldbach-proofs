import Mathlib

namespace Goldbach.CanonicalLowConductorZeros

/-- A zero-free box formulated only with Mathlib's primitive character,
conductor-level parameters, and actual Dirichlet L-function. -/
def PrimitiveBoxInput (K : ℝ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ (X T : ℝ) (d : ℕ) [NeZero d] (ψ : DirichletCharacter ℂ d),
    ψ.IsPrimitive → ψ ≠ 1 → 1 < X → 2 ≤ T → (d:ℝ) ≤ X^δ → T ≤ X^δ →
    ∀ z : ℂ, 0 < z.re → z.re < 1 → |z.im| ≤ T →
      1 - K/Real.log X ≤ z.re → ψ.LFunction z ≠ 0

end Goldbach.CanonicalLowConductorZeros
