import PrimitiveBoxInterface
import Conjectures.Goldbach.DeepThreeQuartersExceptionalZeroCriterion

namespace Goldbach.CanonicalLowConductorZeros
open Finset DirichletCharacter GoldbachTwistedMellin
noncomputable section
open scoped Classical

theorem primitive_ne_one {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hn : χ ≠ 1) :
    χ.primitiveCharacter ≠ 1 := by
  intro h
  apply hn
  rw [← χ.changeLevel_primitiveCharacter,h,changeLevel_one]

/-- The Euler factors removed in changing level have no zeros in Re(s)>0. -/
theorem euler_nonzero {d p : ℕ} [NeZero d] (χ : DirichletCharacter ℂ d)
    (hp : p.Prime) {z : ℂ} (hz : 0 < z.re) :
    1 - χ (p : ZMod d) * (p : ℂ)^(-z) ≠ 0 := by
  have hs : ‖(p : ℂ)^(-z)‖ < 1 := by
    rw [Complex.norm_natCast_cpow_of_re_ne_zero p (by rw [Complex.neg_re]; linarith only [hz]),
      Complex.neg_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (neg_neg_of_pos hz)
  have hnorm : ‖χ (p : ZMod d) * (p : ℂ)^(-z)‖ < 1 := by
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one _)).trans_lt hs
  intro h
  have he := sub_eq_zero.mp h
  rw [← he,norm_one] at hnorm
  exact (lt_irrefl _ hnorm)

/-- In the open right half-plane the actual nonprincipal zero survives at
primitive conductor. The principal character is excluded explicitly. -/
theorem primitive_zero_of_regularized {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hn : χ ≠ 1) {z : ℂ} (hz : 0 < z.re) (hL : Goldbach.regularizedL χ z = 0) :
    @DirichletCharacter.LFunction χ.conductor ⟨χ.conductor_ne_zero⟩ χ.primitiveCharacter z = 0 := by
  letI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have h := LFunction_changeLevel χ.conductor_dvd_level χ.primitiveCharacter
    (s := z) (.inl (primitive_ne_one hn))
  rw [χ.changeLevel_primitiveCharacter] at h
  have hzero : χ.LFunction z = 0 := by simpa only [Goldbach.regularizedL,if_neg hn] using hL
  have hprod : (∏ p ∈ q.primeFactors, (1 - χ.primitiveCharacter (p : ZMod χ.conductor) *
      (p : ℂ)^(-z))) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun p hp =>
        euler_nonzero χ.primitiveCharacter (Nat.prime_of_mem_primeFactors hp) hz
  exact (mul_eq_zero.mp (h.symm.trans hzero)).resolve_right hprod

/-- The principal character has its own zeta zeros on Re(z)>0 away from 1.
No nonprincipal zero-free estimate is used in this equivalence. -/
theorem principal_regularized_iff_zeta (q : ℕ) [NeZero q] {z : ℂ}
    (hr : 0 < z.re) (hne : z ≠ 1) :
    Goldbach.regularizedL (1 : DirichletCharacter ℂ q) z = 0 ↔ riemannZeta z = 0 := by
  have hprod : (∏ p ∈ q.primeFactors, (1 - (p : ℂ)^(-z))) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro p hp
    have h := euler_nonzero (1 : DirichletCharacter ℂ 1) (Nat.prime_of_mem_primeFactors hp) hr
    simpa only [MulChar.one_apply (isUnit_of_subsingleton (p : ZMod 1)),one_mul] using h
  simp only [Goldbach.regularizedL,if_true,LFunctionTrivChar₁,Function.update_of_ne hne]
  rw [LFunctionTrivChar_eq_mul_riemannZeta hne]
  simp [sub_ne_zero.mpr hne,hprod]

/-- This is a subset of precisely the finite zero set used in each canonical
dyadic block. The block height B and the box height T are independent. -/
def boxZeros {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (B K X T : ℝ) : Finset ℂ :=
  (exceptionalZeros χ B).filter (fun z => 1-K/Real.log X ≤ z.re ∧ |z.im| ≤ T)

theorem zero_set_empty (K : ℝ) (hbox : PrimitiveBoxInput K) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (X T : ℝ), 1 < X → 2 ≤ T → T ≤ X^δ →
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
    (χ.conductor:ℝ) ≤ X^δ → ∀ B : ℝ, boxZeros χ B K X T = ∅ := by
  obtain ⟨δ,hd,hfree⟩ := hbox
  refine ⟨δ,hd,?_⟩
  intro X T hX hT hTX q _ χ hχ hcond B
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro z hz
  obtain ⟨hz',hcut,hIm⟩ := mem_filter.mp hz
  obtain ⟨hr,_,hL⟩ := (mem_exceptionalZeros χ B z).mp hz'
  have hr₀ : 0 < z.re := by linarith only [hr]
  have hf : χ.LFunction z = 0 := by simpa only [Goldbach.regularizedL,if_neg hχ] using hL
  have hr₁ : z.re < 1 := lt_of_not_ge fun hu =>
    (LFunction_ne_zero_of_one_le_re χ (.inl hχ) hu) hf
  letI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  apply hfree X T χ.conductor χ.primitiveCharacter χ.primitiveCharacter_isPrimitive
    (primitive_ne_one hχ) hX hT hcond hTX z hr₀ hr₁ hIm hcut
  exact primitive_zero_of_regularized hχ hr₀ hL

def boxTerm {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (a b A β K X T : ℝ) : ℂ :=
  ∑ z ∈ boxZeros χ (heightCut A) K X T,
    (analyticOrderNatAt (Goldbach.regularizedL χ) z:ℂ)*transform a b β z

def outsideBoxTerm {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (a b A β K X T : ℝ) : ℂ :=
  ∑ z ∈ (exceptionalZeros χ (heightCut A)).filter
      (fun z => ¬ (1-K/Real.log X ≤ z.re ∧ |z.im| ≤ T)),
    (analyticOrderNatAt (Goldbach.regularizedL χ) z:ℂ)*transform a b β z

theorem fixedZeroTerm_split {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (a b A β K X T : ℝ) :
    fixedZeroTerm χ a b A β = boxTerm χ a b A β K X T + outsideBoxTerm χ a b A β K X T := by
  exact (Finset.sum_filter_add_sum_filter_not (exceptionalZeros χ (heightCut A))
    (fun z => 1-K/Real.log X ≤ z.re ∧ |z.im| ≤ T)
    (fun z => (analyticOrderNatAt (Goldbach.regularizedL χ) z:ℂ)*transform a b β z)).symm

/-- Contribution to the genuine canonical correction from low-conductor
nonprincipal characters and low-height near-one zeros at each dyadic block. -/
def nonprincipalLowCorrection {q : ℕ} [NeZero q] (n : ℕ) (v : ZMod q)
    (β K X T δ : ℝ) : ℂ :=
  ((prefixBlocks (n-2)).map fun p =>
    ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter
        (fun χ => χ ≠ 1 ∧ (χ.conductor:ℝ) ≤ X^δ),
      additiveWeight v χ * boxTerm χ p.1 p.2 p.1 (2*Real.pi*β) K X T).sum

theorem low_correction_zero (K : ℝ) (hbox : PrimitiveBoxInput K) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (X T : ℝ), 1 < X → 2 ≤ T → T ≤ X^δ →
    ∀ (q : ℕ) [NeZero q] (n : ℕ) (v : ZMod q) (β : ℝ),
      nonprincipalLowCorrection n v β K X T δ = 0 := by
  obtain ⟨δ,hd,h⟩ := zero_set_empty K hbox
  refine ⟨δ,hd,?_⟩
  intro X T hX hT hTX q _ n v β
  let F := (univ : Finset (DirichletCharacter ℂ q)).filter
    (fun χ => χ ≠ 1 ∧ (χ.conductor:ℝ) ≤ X^δ)
  have hrow (p : ℕ × ℕ) : (∑ χ ∈ F,
      additiveWeight v χ * boxTerm χ p.1 p.2 p.1 (2*Real.pi*β) K X T) = 0 := by
    apply sum_eq_zero
    intro χ hχ
    obtain ⟨hn,hc⟩ := (mem_filter.mp hχ).2
    simp [boxTerm,h X T hX hT hTX q χ hn hc]
  unfold nonprincipalLowCorrection
  change ((prefixBlocks (n-2)).map (fun p => ∑ χ ∈ F,
      additiveWeight v χ * boxTerm χ p.1 p.2 p.1 (2*Real.pi*β) K X T)).sum = 0
  simp_rw [hrow]
  simp

/-- Exact evaluation of the original canonicalCorrection after removing
the empty part. The principal character and larger conductors retain their
full original fixedZeroTerm. -/
theorem canonicalCorrection_trimmed (K : ℝ) (hbox : PrimitiveBoxInput K) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (X T : ℝ), 1 < X → 2 ≤ T → T ≤ X^δ →
    ∀ (q : ℕ) [NeZero q] (n : ℕ) (v : ZMod q) (β : ℝ),
      canonicalCorrection n v β = ((prefixBlocks (n-2)).map fun p =>
        ∑ χ : DirichletCharacter ℂ q, additiveWeight v χ *
          (if χ ≠ 1 ∧ (χ.conductor:ℝ) ≤ X^δ then
            outsideBoxTerm χ p.1 p.2 p.1 (2*Real.pi*β) K X T
           else fixedZeroTerm χ p.1 p.2 p.1 (2*Real.pi*β))).sum := by
  obtain ⟨δ,hd,h⟩ := zero_set_empty K hbox
  refine ⟨δ,hd,?_⟩
  intro X T hX hT hTX q _ n v β
  unfold canonicalCorrection
  apply congrArg List.sum
  apply List.map_congr_left
  intro p _
  apply Finset.sum_congr rfl
  intro χ _
  apply congrArg (fun z : ℂ => additiveWeight v χ*z)
  by_cases hb : χ ≠ 1 ∧ (χ.conductor:ℝ) ≤ X^δ
  · rw [if_pos hb,fixedZeroTerm_split χ p.1 p.2 p.1 (2*Real.pi*β) K X T]
    simp [boxTerm,h X T hX hT hTX q χ hb.1 hb.2]
  · rw [if_neg hb]

end
end Goldbach.CanonicalLowConductorZeros
#print axioms Goldbach.CanonicalLowConductorZeros.low_correction_zero
#print axioms Goldbach.CanonicalLowConductorZeros.canonicalCorrection_trimmed
