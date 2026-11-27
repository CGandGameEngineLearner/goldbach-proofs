import CanonicalCharacterContraction
import PrincipalZeroOffset

open Finset GoldbachTwistedMellin
namespace Goldbach.ArithmeticSignedRow
open PrincipalZeroOffset SignedCharacterGauss CanonicalCharacterContraction
noncomputable section
open scoped Classical

/-- The same β is used for every reduced numerator at level q. The unweighted
term is the Ramanujan sum, written with the same additive character. -/
def frequency {q : ℕ} [NeZero q] (m : ℕ) (χ : DirichletCharacter ℂ q) :=
  gaussSum χ (ZMod.stdAddChar.mulShift (-(m:ZMod q)))

def linear (Y q m : ℕ) [NeZero q] (β : ℝ) :=
  ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.conductor ∣ q/q.gcd m),
    amplitude Y β χ * frequency m χ

def quadratic (Y q m : ℕ) [NeZero q] (β : ℝ) :=
  ∑ χ : DirichletCharacter ℂ q, ∑ ψ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter
    (fun ψ => (χ*ψ).conductor ∣ q/q.gcd m),
      (amplitude Y β χ * amplitude Y β ψ) * frequency m (χ*ψ)

/-- The entire signed correction at level q, contracted across all reduced
numerators. All terms retain their complex phases. -/
theorem contracted_row (Y q m : ℕ) [NeZero q] (β : ℝ) :
    let c := (ArithmeticFunction.moebius q : ℂ)/(q.totient:ℂ)
    let k := GB6Kernel.kernel Y β
    (∑ u : (ZMod q)ˣ, rowTerm Y q (u:ZMod q).val β *
      GB6Kernel.phase (-(m:ℝ)*(((u:ZMod q).val:ℝ)/q))) =
      quadratic Y q m β + (2*c-2*c*k)*linear Y q m β +
        (c^2-2*c^2*k)*frequency m (1 : DirichletCharacter ℂ q) := by
  intro c k
  let z (u : (ZMod q)ˣ) := canonicalCorrection Y (u:ZMod q) β
  let e (u : (ZMod q)ˣ) := ZMod.stdAddChar (-(m:ZMod q)*(u:ZMod q))
  have h (u : (ZMod q)ˣ) : rowTerm Y q (u:ZMod q).val β *
      GB6Kernel.phase (-(m:ℝ)*(((u:ZMod q).val:ℝ)/q)) =
      (z u)^2 * e u + (2*c-2*c*k)*(z u*e u) + (c^2-2*c^2*k)*e u := by
    have he : GB6Kernel.phase (-(m:ℝ)*(((u:ZMod q).val:ℝ)/q)) = e u :=
      (negative_phase (u:ZMod q) m).symm
    rw [he,rowTerm,dif_neg (NeZero.ne q),mean_eq_moebius (ZMod.val_coe_unit_coprime u), ZMod.natCast_zmod_val]
    dsimp only [c,k,z]
    ring
  have h0 : (∑ u : (ZMod q)ˣ, e u) = frequency m (1 : DirichletCharacter ℂ q) := by
    rw [frequency, ← unit_frequency]
    apply sum_congr rfl
    intro u _
    simp [e]
  simp_rw [h, sum_add_distrib, ← mul_sum]
  rw [h0]
  have h1 : (∑ u : (ZMod q)ˣ, z u*e u) = linear Y q m β := canonical_linear Y m β
  have h2 : (∑ u : (ZMod q)ˣ, (z u)^2*e u) = quadratic Y q m β := canonical_square Y m β
  rw [h1,h2]

end
end Goldbach.ArithmeticSignedRow
#print axioms Goldbach.ArithmeticSignedRow.contracted_row
