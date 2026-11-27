import CanonicalCharacterContraction
import B13GaussProjection

/-! The declarations from B13GaussProjection retain the original names and can
be imported instead from Conjectures.Goldbach.B13NondividingResidueReduction
when the full accepted module is installed. -/

open Finset GoldbachTwistedMellin
namespace Goldbach.B13SignedAmplitudes
open CanonicalCharacterContraction SignedCharacterGauss
open B13NondividingResidueReductionProof.DyadicMixedB4CharacterFactorBound
noncomputable section
variable {q : ℕ} [NeZero q]

/-- Positive-frequency imprimitive Gauss mass at the actual modulus. -/
def divisorMass (c q m : ℕ) : ℝ :=
  ∑ f ∈ m.divisors.filter (fun f => c*f ∣ q), (f:ℝ)

theorem divisorMass_nonneg (c q m : ℕ) : 0 ≤ divisorMass c q m :=
  sum_nonneg fun _ _ => Nat.cast_nonneg _

theorem norm_amplitude (Y : ℕ) (β : ℝ) (χ : DirichletCharacter ℂ q) :
    ‖amplitude Y β χ‖ ≤ ‖blockAmplitude Y β χ‖ * (Real.sqrt χ.conductor / (q.totient:ℝ)) := by
  have h := norm_dirichlet_gauss_standard χ⁻¹
  rw [DirichletCharacter.conductor_inv] at h
  rw [amplitude,norm_mul,weight_gauss,AddChar.mulShift_one,norm_div,Complex.norm_natCast,mul_comm]
  exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right h (Nat.cast_nonneg _)) (norm_nonneg _)

theorem norm_negative_frequency {m : ℕ} (hm : 0 < m) (χ : DirichletCharacter ℂ q) :
    ‖gaussSum χ (ZMod.stdAddChar.mulShift (-(m:ZMod q)))‖ ≤
      Real.sqrt χ.conductor * divisorMass χ.conductor q m := by
  refine (norm_gauss_neg_shift_le χ (m:ZMod q)).trans ?_
  simpa only [DirichletCharacter.changeLevel_self,divisorMass]
    using norm_dirichlet_gauss_induced (dvd_refl q) χ m hm

/-- Each signed linear contribution retains the exact simultaneous divisor
constraints on its positive frequency and denominator. -/
theorem linear_term {m : ℕ} (hm : 0 < m) (Y : ℕ) (β : ℝ) (χ : DirichletCharacter ℂ q) :
    ‖amplitude Y β χ * gaussSum χ (ZMod.stdAddChar.mulShift (-(m:ZMod q)))‖ ≤
      ‖blockAmplitude Y β χ‖ * (χ.conductor:ℝ) / (q.totient:ℝ) * divisorMass χ.conductor q m := by
  rw [norm_mul]
  calc
    _ ≤ (‖blockAmplitude Y β χ‖ * (Real.sqrt χ.conductor / (q.totient:ℝ))) *
          (Real.sqrt χ.conductor * divisorMass χ.conductor q m) :=
      mul_le_mul (norm_amplitude Y β χ) (norm_negative_frequency hm χ) (norm_nonneg _) (by positivity)
    _ = ‖blockAmplitude Y β χ‖ * (Real.sqrt χ.conductor)^2 / (q.totient:ℝ) *
          divisorMass χ.conductor q m := by ring
    _ = _ := by rw [Real.sq_sqrt (Nat.cast_nonneg _)]

/-- Each signed quadratic contribution is controlled by the two block
amplitudes and the separate conductors of χ, ψ and their product. -/
theorem quadratic_term {m : ℕ} (hm : 0 < m) (Y : ℕ) (β : ℝ) (χ ψ : DirichletCharacter ℂ q) :
    ‖(amplitude Y β χ * amplitude Y β ψ) *
      gaussSum (χ*ψ) (ZMod.stdAddChar.mulShift (-(m:ZMod q)))‖ ≤
      ‖blockAmplitude Y β χ * blockAmplitude Y β ψ‖ *
        Real.sqrt χ.conductor * Real.sqrt ψ.conductor * Real.sqrt (χ*ψ).conductor /
        (q.totient:ℝ)^2 * divisorMass (χ*ψ).conductor q m := by
  simp only [norm_mul]
  have hp := mul_le_mul (norm_amplitude Y β χ) (norm_amplitude Y β ψ)
    (norm_nonneg _) (by positivity)
  refine (mul_le_mul hp (norm_negative_frequency hm (χ*ψ)) (norm_nonneg _) (by positivity)).trans_eq ?_
  ring

end
end Goldbach.B13SignedAmplitudes

#print axioms Goldbach.B13SignedAmplitudes.linear_term
#print axioms Goldbach.B13SignedAmplitudes.quadratic_term
