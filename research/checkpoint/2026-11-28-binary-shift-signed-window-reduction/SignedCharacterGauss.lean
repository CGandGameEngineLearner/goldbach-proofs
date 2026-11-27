import Conjectures.Goldbach.DeepThreeQuartersExceptionalZeroCriterion
import Mathlib.NumberTheory.DirichletCharacter.GaussSum

open Finset GoldbachTwistedMellin GoldbachGRHWindow
namespace Goldbach.SignedCharacterGauss
noncomputable section
variable {q : ℕ} [NeZero q]

/-- All the dependence of the normalized additive Fourier weight on a unit
numerator is through the original (unconjugated) character. -/
theorem weight_gauss (a : ZMod q) (χ : DirichletCharacter ℂ q) :
    additiveWeight a χ = gaussSum χ⁻¹ (ZMod.stdAddChar.mulShift a) / (q.totient:ℂ) := by
  rw [weight_expansion, gaussSum]
  congr 1
  refine sum_congr rfl fun r _ => ?_
  change ZMod.stdAddChar (a*r) * star (χ r) = χ⁻¹ r * ZMod.stdAddChar (a*r)
  rw [MulChar.star_apply', mul_comm]

theorem weight_unit (u : (ZMod q)ˣ) (χ : DirichletCharacter ℂ q) :
    additiveWeight u χ = χ u * additiveWeight (1 : ZMod q) χ := by
  rw [weight_gauss, weight_gauss, gaussSum_mulShift_eq _ _ u,
    AddChar.mulShift_one, inv_inv, mul_div_assoc]

/-- Convert the finite additive character to the actual phase in the
Fourier integral. This fixes the sign when contracting a rational window. -/
theorem negative_phase (a : ZMod q) (m : ℕ) :
    ZMod.stdAddChar (-(m:ZMod q)*a) =
      Complex.exp (((2*Real.pi*(-(m:ℝ)*((a.val:ℝ)/(q:ℝ))) : ℝ) : ℂ)*Complex.I) := by
  have ha : ((-(m:ℤ)*(a.val:ℤ):ℤ):ZMod q) = -(m:ZMod q)*a := by
    push_cast
    rw [ZMod.natCast_zmod_val]
  rw [←ha,ZMod.stdAddChar_coe]
  congr 1
  push_cast
  ring

/-- The negative sign is the negative Fourier frequency of the Goldbach
coefficient. Nonunits contribute zero to the Dirichlet Gauss sum. -/
theorem unit_frequency (m : ZMod q) (χ : DirichletCharacter ℂ q) :
    (∑ u : (ZMod q)ˣ, χ u * ZMod.stdAddChar (-m*(u:ZMod q))) =
      gaussSum χ (ZMod.stdAddChar.mulShift (-m)) := by
  classical
  let F := fun r : ZMod q => χ r * ZMod.stdAddChar (-m*r)
  change (∑ u : (ZMod q)ˣ, F u) = ∑ r : ZMod q, F r
  have h : (univ : Finset (ZMod q)).filter IsUnit =
      (univ : Finset (ZMod q)ˣ).map ⟨(↑),Units.val_injective⟩ := by
    ext r
    simp [IsUnit]
  calc
    _ = ∑ r ∈ (univ : Finset (ZMod q)).filter IsUnit, F r := by rw [h,Finset.sum_map]; rfl
    _ = _ := by
      refine sum_subset (filter_subset ..) ?_
      intro r _ hr
      have hr' : ¬IsUnit r := by simpa using hr
      simp [F,MulChar.map_nonunit _ hr']

/-- Exact quadratic numerator contraction, valid for arbitrary complex
Dirichlet characters including imprimitive characters. -/
theorem pair_sum (m : ZMod q) (χ ψ : DirichletCharacter ℂ q) :
    (∑ u : (ZMod q)ˣ, additiveWeight u χ * additiveWeight u ψ *
      ZMod.stdAddChar (-m*(u:ZMod q))) =
    (additiveWeight (1:ZMod q) χ * additiveWeight (1:ZMod q) ψ) *
      gaussSum (χ*ψ) (ZMod.stdAddChar.mulShift (-m)) := by
  rw [← unit_frequency, Finset.mul_sum]
  refine sum_congr rfl fun u _ => ?_
  rw [weight_unit, weight_unit, MulChar.mul_apply]
  ring

/-- The main-term times correction contraction. -/
theorem mixed_sum (m : ZMod q) (χ : DirichletCharacter ℂ q) :
    (∑ u : (ZMod q)ˣ, additiveModel q u * additiveWeight u χ *
      ZMod.stdAddChar (-m*(u:ZMod q))) =
    (additiveModel q 1 * additiveWeight (1:ZMod q) χ) *
      gaussSum χ (ZMod.stdAddChar.mulShift (-m)) := by
  simpa only [additiveWeight_one, one_mul] using pair_sum m (1 : DirichletCharacter ℂ q) χ

/-- The sharp elementary obstruction applies to imprimitive products as
well: the conductor must divide q/gcd(q,m). -/
theorem frequency_eq_zero_of_conductor (m : ℕ) (χ : DirichletCharacter ℂ q)
    (hc : ¬χ.conductor ∣ q / q.gcd m) :
    gaussSum χ (ZMod.stdAddChar.mulShift (-(m:ZMod q))) = 0 := by
  by_contra hn
  let g := q.gcd m
  let d := q/g
  have hgq : g ∣ q := Nat.gcd_dvd_left q m
  have hgd : d*g = q := Nat.div_mul_cancel hgq
  have hdq : d ∣ q := ⟨g,hgd.symm⟩
  have hdiv : q ∣ m*d := by
    obtain ⟨k,hk⟩ := Nat.gcd_dvd_right q m
    refine ⟨k,?_⟩
    change m*d = q*k
    calc
      m*d = (g*k)*d := congrArg (fun t => t*d) hk
      _ = (d*g)*k := by ring
      _ = q*k := by rw [hgd]
  have hz : (m:ZMod q)*(d:ZMod q) = 0 := by
    rw [← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
    exact hdiv
  have he : (ZMod.stdAddChar.mulShift (-(m:ZMod q))).mulShift (d:ZMod q) = 1 := by
    rw [AddChar.mulShift_mulShift, neg_mul, hz, neg_zero, AddChar.mulShift_zero]
  have hfactor := factorsThrough_of_gaussSum_ne_zero
    (ZMod.stdAddChar.mulShift (-(m:ZMod q))) hdq he hn
  exact hc (χ.conductor_dvd_of_mem_conductorSet hfactor)

theorem pair_sum_zero (m : ℕ) (χ ψ : DirichletCharacter ℂ q)
    (hc : ¬ (χ*ψ).conductor ∣ q / q.gcd m) :
    (∑ u : (ZMod q)ˣ, additiveWeight u χ * additiveWeight u ψ *
      ZMod.stdAddChar (-(m:ZMod q)*(u:ZMod q))) = 0 := by
  rw [pair_sum, frequency_eq_zero_of_conductor m _ hc, mul_zero]

theorem mixed_sum_zero (m : ℕ) (χ : DirichletCharacter ℂ q)
    (hc : ¬χ.conductor ∣ q / q.gcd m) :
    (∑ u : (ZMod q)ˣ, additiveModel q u * additiveWeight u χ *
      ZMod.stdAddChar (-(m:ZMod q)*(u:ZMod q))) = 0 := by
  rw [mixed_sum, frequency_eq_zero_of_conductor m _ hc, mul_zero]

/-- If the product is primitive, every nonunit frequency cancels. -/
theorem primitive_pair_sum_zero (m : ZMod q) (χ ψ : DirichletCharacter ℂ q)
    (hp : (χ*ψ).IsPrimitive) (hm : ¬IsUnit m) :
    (∑ u : (ZMod q)ˣ, additiveWeight u χ * additiveWeight u ψ *
      ZMod.stdAddChar (-m*(u:ZMod q))) = 0 := by
  have hn : ¬IsUnit (-m) := fun h => hm (neg_neg m ▸ h.neg)
  rw [pair_sum, gaussSum_mulShift_of_isPrimitive ZMod.stdAddChar hp,
    MulChar.map_nonunit _ hn, zero_mul, mul_zero]

end
end Goldbach.SignedCharacterGauss
#print axioms Goldbach.SignedCharacterGauss.pair_sum_zero
#print axioms Goldbach.SignedCharacterGauss.mixed_sum_zero
