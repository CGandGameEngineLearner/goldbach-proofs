import CanonicalLowConductorZeros
import DeepCompatiblePolynomialBox

namespace Goldbach.CanonicalLowConductorZeros
open Finset DirichletCharacter GoldbachTwistedMellin
noncomputable section
open scoped Classical

theorem zero_set_empty_actual (K : ℝ) (hK : 0 < K) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (X T : ℝ), 1 < X → 2 ≤ T → T ≤ X^δ →
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
    (χ.conductor:ℝ) ≤ X^δ → ∀ B : ℝ, boxZeros χ B K X T = ∅ :=
  zero_set_empty K (primitiveBoxInput_actual K hK)

theorem low_correction_zero_actual (K : ℝ) (hK : 0 < K) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (X T : ℝ), 1 < X → 2 ≤ T → T ≤ X^δ →
    ∀ (q : ℕ) [NeZero q] (n : ℕ) (v : ZMod q) (β : ℝ),
      nonprincipalLowCorrection n v β K X T δ = 0 :=
  low_correction_zero K (primitiveBoxInput_actual K hK)

theorem canonicalCorrection_trimmed_actual (K : ℝ) (hK : 0 < K) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (X T : ℝ), 1 < X → 2 ≤ T → T ≤ X^δ →
    ∀ (q : ℕ) [NeZero q] (n : ℕ) (v : ZMod q) (β : ℝ),
      canonicalCorrection n v β = ((prefixBlocks (n-2)).map fun p =>
        ∑ χ : DirichletCharacter ℂ q, additiveWeight v χ *
          (if χ ≠ 1 ∧ (χ.conductor:ℝ) ≤ X^δ then
            outsideBoxTerm χ p.1 p.2 p.1 (2*Real.pi*β) K X T
           else fixedZeroTerm χ p.1 p.2 p.1 (2*Real.pi*β))).sum :=
  canonicalCorrection_trimmed K (primitiveBoxInput_actual K hK)

end
end Goldbach.CanonicalLowConductorZeros
#print axioms Goldbach.CanonicalLowConductorZeros.canonicalCorrection_trimmed_actual
#print axioms Goldbach.CanonicalLowConductorZeros.low_correction_zero_actual
