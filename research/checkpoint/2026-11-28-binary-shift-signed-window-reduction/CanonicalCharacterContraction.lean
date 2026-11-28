import SignedCharacterGauss

open Finset Goldbach GoldbachTwistedMellin Goldbach.SignedCharacterGauss
namespace Goldbach.CanonicalCharacterContraction
noncomputable section
variable {q : ℕ} [NeZero q]

def blockAmplitude (Y : ℕ) (β : ℝ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ((prefixBlocks (Y-2)).map fun p =>
    fixedZeroTerm χ p.1 p.2 p.1 (2*Real.pi*β)).sum

/-- The block correction contains exactly the multiplicity-weighted residues
at the existing height cutoff of each block. -/
theorem blockAmplitude_residues (Y : ℕ) (β : ℝ) (χ : DirichletCharacter ℂ q) :
    blockAmplitude Y β χ = ((prefixBlocks (Y-2)).map fun p =>
      ∑ z ∈ exceptionalZeros χ (heightCut p.1),
        (analyticOrderNatAt (regularizedL χ) z : ℂ) * transform p.1 p.2 (2*Real.pi*β) z).sum := rfl

def amplitude (Y : ℕ) (β : ℝ) (χ : DirichletCharacter ℂ q) :=
  additiveWeight (1:ZMod q) χ * blockAmplitude Y β χ

theorem canonical_unit (Y : ℕ) (β : ℝ) (u : (ZMod q)ˣ) :
    canonicalCorrection Y (u:ZMod q) β = ∑ χ : DirichletCharacter ℂ q, χ u * amplitude Y β χ := by
  classical
  let f (p : ℕ × ℕ) (χ : DirichletCharacter ℂ q) := fixedZeroTerm χ p.1 p.2 p.1 (2*Real.pi*β)
  have reorder (l : List (ℕ × ℕ)) :
      (l.map fun p => ∑ χ : DirichletCharacter ℂ q, additiveWeight u χ * f p χ).sum =
        ∑ χ : DirichletCharacter ℂ q, additiveWeight u χ * (l.map fun p => f p χ).sum := by
    induction l with
    | nil => simp
    | cons p l ih => simp only [List.map_cons,List.sum_cons,ih,mul_add,sum_add_distrib]
  calc
    _ = ∑ χ : DirichletCharacter ℂ q, additiveWeight u χ * blockAmplitude Y β χ :=
      reorder (prefixBlocks (Y-2))
    _ = _ := by
      refine sum_congr rfl fun χ _ => ?_
      rw [weight_unit u χ, amplitude, mul_assoc]

/-- A single correction factor at its actual negative Fourier frequency. -/
theorem canonical_linear (Y m : ℕ) (β : ℝ) :
    (∑ u : (ZMod q)ˣ, canonicalCorrection Y (u:ZMod q) β * ZMod.stdAddChar (-(m:ZMod q)*(u:ZMod q))) =
      ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter
          (fun χ => χ.conductor ∣ q/q.gcd m),
        amplitude Y β χ * gaussSum χ (ZMod.stdAddChar.mulShift (-(m:ZMod q))) := by
  classical
  let e (u : (ZMod q)ˣ) := ZMod.stdAddChar (-(m:ZMod q)*(u:ZMod q))
  calc
    _ = ∑ χ : DirichletCharacter ℂ q, ∑ u : (ZMod q)ˣ, (χ u * amplitude Y β χ) * e u := by
      simp_rw [canonical_unit, Finset.sum_mul]
      rw [sum_comm]
    _ = ∑ χ : DirichletCharacter ℂ q, amplitude Y β χ * gaussSum χ
        (ZMod.stdAddChar.mulShift (-(m:ZMod q))) := by
      refine sum_congr rfl fun χ _ => ?_
      rw [← unit_frequency, Finset.mul_sum]
      refine sum_congr rfl fun u _ => ?_
      dsimp only [e]; ring
    _ = _ := by
      symm
      apply sum_subset (filter_subset ..)
      intro χ _ h
      have hc : ¬χ.conductor ∣ q/q.gcd m := by simpa using h
      rw [frequency_eq_zero_of_conductor m _ hc, mul_zero]

/-- Exact quadratic contraction, filtering character pairs by the conductor
of their product before any absolute values are taken. -/
theorem canonical_square (Y m : ℕ) (β : ℝ) :
    (∑ u : (ZMod q)ˣ, (canonicalCorrection Y (u:ZMod q) β)^2 * ZMod.stdAddChar (-(m:ZMod q)*(u:ZMod q))) =
      ∑ χ : DirichletCharacter ℂ q, ∑ ψ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter
          (fun ψ => (χ*ψ).conductor ∣ q/q.gcd m),
        (amplitude Y β χ * amplitude Y β ψ) *
          gaussSum (χ*ψ) (ZMod.stdAddChar.mulShift (-(m:ZMod q))) := by
  classical
  let A := amplitude (q:=q) Y β
  let e (u : (ZMod q)ˣ) := ZMod.stdAddChar (-(m:ZMod q)*(u:ZMod q))
  calc
    _ = ∑ u : (ZMod q)ˣ, ∑ χ : DirichletCharacter ℂ q, ∑ ψ : DirichletCharacter ℂ q,
        (A χ*A ψ)*((χ*ψ) u*e u) := by
      refine sum_congr rfl fun u _ => ?_
      rw [canonical_unit, sq, sum_mul_sum]
      simp_rw [Finset.sum_mul]
      refine sum_congr rfl fun χ _ => ?_
      refine sum_congr rfl fun ψ _ => ?_
      dsimp only [A,e,MulChar.mul_apply]; ring
    _ = ∑ χ : DirichletCharacter ℂ q, ∑ ψ : DirichletCharacter ℂ q, ∑ u : (ZMod q)ˣ,
        (A χ*A ψ)*((χ*ψ) u*e u) := by
      rw [sum_comm]
      exact sum_congr rfl fun _ _ => sum_comm
    _ = ∑ χ : DirichletCharacter ℂ q, ∑ ψ : DirichletCharacter ℂ q,
        (A χ*A ψ)*gaussSum (χ*ψ) (ZMod.stdAddChar.mulShift (-(m:ZMod q))) := by
      refine sum_congr rfl fun χ _ => ?_
      refine sum_congr rfl fun ψ _ => ?_
      rw [← unit_frequency, Finset.mul_sum]
    _ = _ := by
      refine sum_congr rfl fun χ _ => Eq.symm ?_
      apply sum_subset (filter_subset ..)
      intro ψ _ h
      have hc : ¬(χ*ψ).conductor ∣ q/q.gcd m := by simpa using h
      rw [frequency_eq_zero_of_conductor m _ hc, mul_zero]

end
end Goldbach.CanonicalCharacterContraction
#print axioms Goldbach.CanonicalCharacterContraction.canonical_linear
#print axioms Goldbach.CanonicalCharacterContraction.canonical_square
