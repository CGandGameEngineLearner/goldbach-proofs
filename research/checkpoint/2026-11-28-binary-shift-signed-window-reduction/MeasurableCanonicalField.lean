import MiddleCanonicalModel
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Integral.Prod

open Finset Filter MeasureTheory
namespace Goldbach.MiddleCanonicalModel
open ShiftWideArc
noncomputable section
open scoped Classical

private theorem transform_measurable (a b : ℝ) (s : ℂ) :
    StronglyMeasurable (fun β : ℝ => GoldbachTwistedMellin.transform a b β s) := by
  let f (p : ℝ × ℝ) := (p.2:ℂ)^(s-1) • GoldbachTwistedMellin.test a b p.1 p.2
  have h : StronglyMeasurable f := by
    apply Measurable.stronglyMeasurable
    unfold f GoldbachTwistedMellin.test GoldbachTwistedMellin.phase GoldbachTwistedMellin.taper
    fun_prop
  exact h.integral_prod_right' (ν := volume.restrict (Set.Ioi (0:ℝ)))

private theorem fixedZero_measurable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (a b X : ℝ) :
    StronglyMeasurable (GoldbachTwistedMellin.fixedZeroTerm χ a b X) := by
  unfold GoldbachTwistedMellin.fixedZeroTerm
  exact Finset.stronglyMeasurable_fun_sum _ fun z _ => stronglyMeasurable_const.mul (transform_measurable a b z)

private theorem correction_measurable {q : ℕ} [NeZero q] (Y : ℕ) (v : ZMod q) :
    StronglyMeasurable (GoldbachTwistedMellin.canonicalCorrection Y v) := by
  let term (p : ℕ × ℕ) (β : ℝ) :=
    ∑ χ : DirichletCharacter ℂ q, GoldbachTwistedMellin.additiveWeight v χ *
      GoldbachTwistedMellin.fixedZeroTerm χ p.1 p.2 p.1 (2*Real.pi*β)
  have hterm (p : ℕ × ℕ) : StronglyMeasurable (term p) := by
    apply Finset.stronglyMeasurable_fun_sum
    intro χ _
    exact stronglyMeasurable_const.mul
      ((fixedZero_measurable χ p.1 p.2 p.1).comp_measurable (by fun_prop))
  have hlist (l : List (ℕ × ℕ)) : StronglyMeasurable (fun β => (l.map (fun p => term p β)).sum) := by
    induction l with
    | nil => simpa only [List.map_nil,List.sum_nil] using (stronglyMeasurable_const (b:=(0:ℂ)) (α:=ℝ))
    | cons p l ih =>
      simp only [List.map_cons,List.sum_cons]
      have h := (hterm p).add ih
      exact h.measurable.stronglyMeasurable
  exact hlist (GoldbachTwistedMellin.prefixBlocks (Y-2))

theorem centerValue_stronglyMeasurable (Y q a : ℕ) : StronglyMeasurable (centerValue Y q a) := by
  by_cases hq : q = 0
  · have hz : centerValue Y q a = fun _ => 0 := by funext β; simp [centerValue,hq]
    rw [hz]
    exact stronglyMeasurable_const
  · let _ : NeZero q := ⟨hq⟩
    have hr : Continuous (DeepThreeQuarters.rationalModel Y q) := by
      unfold DeepThreeQuarters.rationalModel DeepThreeQuarters.positiveGeometricSum DeepThreeQuarters.geometricPhase
      fun_prop
    have he : centerValue Y q a = DeepThreeQuarters.rationalModel Y q -
        GoldbachTwistedMellin.canonicalCorrection Y (a:ZMod q) := by
      funext β
      simp only [centerValue,dite_eq_right hq,Pi.sub_apply]
    rw [he]
    exact hr.stronglyMeasurable.sub (correction_measurable Y (a : ZMod q))

def bandSet (Y : ℕ) := {t : ℝ | ∃ q a, bandCenter Y t q a}

private theorem fixed_guard {f : ℝ → Prop} (p : Prop) (h : MeasurableSet {t | f t}) :
    MeasurableSet {t : ℝ | p ∧ f t} := by
  by_cases hp : p
  · simpa only [hp,true_and] using h
  · simp [hp]

theorem measurable_center_set (Y q a : ℕ) : MeasurableSet {t : ℝ | bandCenter Y t q a} := by
  unfold bandCenter
  apply fixed_guard
  apply fixed_guard
  apply fixed_guard
  apply fixed_guard
  apply fixed_guard
  exact measurableSet_le (show Continuous (fun t : ℝ => |t-(a:ℝ)/q|) by fun_prop).measurable measurable_const

theorem measurable_bandSet (Y : ℕ) : MeasurableSet (bandSet Y) := by
  unfold bandSet
  simp only [Set.ofPred_exists]
  exact MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun a => measurable_center_set Y q a

def field (Y : ℕ) (t : ℝ) :=
  ∑ i ∈ GB6Geometry.indices (Q Y), {u : ℝ | bandCenter Y u i.1 i.2}.indicator
    (fun u => centerValue Y i.1 i.2 (u-(i.2:ℝ)/i.1)) t

theorem field_stronglyMeasurable (Y : ℕ) : StronglyMeasurable (field Y) := by
  apply Finset.stronglyMeasurable_fun_sum
  intro i _
  exact ((centerValue_stronglyMeasurable Y i.1 i.2).comp_measurable
    (by fun_prop)).indicator (measurable_center_set Y i.1 i.2)

private theorem geometric_mem {Y q a : ℕ} {t : ℝ} (hw : bandCenter Y t q a) :
    (⟨q,a⟩:GB6Geometry.Idx) ∈ GB6Geometry.indices (Q Y) ∧
    t ∈ GB6Geometry.window (H Y) Y q a := by
  obtain ⟨hq,_,hu,ha,hc,ht⟩ := hw
  have hqQ := (hu.trans (min_le_left ..)).trans_eq (GB6Growth.grid_eq_floor Y)
  exact ⟨mem_sigma.mpr ⟨mem_Icc.mpr ⟨hq,hqQ⟩,mem_filter.mpr ⟨mem_range.mpr (by change a < q+1; omega),hc⟩⟩,
    (GB6Geometry.mem_window Y q a t).mpr ht⟩

theorem field_eq_center {Y q a : ℕ} (hs : 2*(H Y)^2 < Y) (hQ : Q Y ≤ H Y)
    {t : ℝ} (hw : bandCenter Y t q a) : field Y t = centerValue Y q a (t-(a:ℝ)/q) := by
  let i : GB6Geometry.Idx := ⟨q,a⟩
  obtain ⟨hi,hti⟩ := geometric_mem hw
  unfold field
  rw [sum_eq_single_of_mem i hi]
  · exact Set.indicator_of_mem hw _
  · intro j hj hne
    apply Set.indicator_of_notMem
    intro hwj
    have hgj := geometric_mem hwj
    exact hne (GB6Geometry.unique_window hs hQ t ⟨hj,hgj.2⟩ ⟨hi,hti⟩)

theorem field_zero_outside {Y : ℕ} {t : ℝ} (ht : t ∉ bandSet Y) : field Y t = 0 := by
  apply sum_eq_zero
  intro i _
  exact Set.indicator_of_notMem (fun h => ht ⟨i.1,i.2,h⟩) _

theorem eventual_field_bound :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ Y : ℕ in atTop, ∀ t ∈ bandSet Y, ‖S Y t-field Y t‖ ≤
      C*(Y:ℝ)^(49/64:ℝ)*(GoldbachTwistedMellin.logScale Y)^4 := by
  obtain ⟨C,hC,h⟩ := eventual_band_center_bound
  refine ⟨C,hC,?_⟩
  filter_upwards [GB6Growth.eventual_geometry,h] with Y hg hY
  have hq : GB6Growth.grid Y = Q Y := GB6Growth.grid_eq_floor Y
  have hH : GB6Growth.height Y = H Y := by simp only [GB6Growth.height,H,hq]
  obtain ⟨_,hqH,_,_,hs⟩ := hg
  rw [hH] at hs
  rw [hH,hq] at hqH
  rintro t ⟨q,a,hw⟩
  rw [field_eq_center hs hqH hw]
  exact hY t q a hw

private theorem eventually_bounded : ∀ᶠ Y : ℕ in atTop,
    ∃ A : ℝ, 0 ≤ A ∧ ∀ t, ‖field Y t‖ ≤ A := by
  obtain ⟨C,hC,h⟩ := eventual_field_bound
  filter_upwards [h] with Y hY
  let D := C*(Y:ℝ)^(49/64:ℝ)*(GoldbachTwistedMellin.logScale Y)^4
  let B := ∑ k ∈ range (Y+1), ‖(weight k:ℂ)‖
  have hph (x : ℝ) : ‖phase x‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have hp (t : ℝ) : ‖S Y t‖ ≤ B := (norm_sum_le ..).trans_eq (by
    simp only [B,norm_mul,hph,mul_one])
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hB : 0 ≤ B := sum_nonneg fun _ _ => norm_nonneg _
  refine ⟨D+B,add_nonneg hD hB,?_⟩
  intro t
  by_cases ht : t ∈ bandSet Y
  · have hh := norm_sub_le (S Y t) (S Y t-field Y t)
    rw [sub_sub_cancel] at hh
    exact (hh.trans (add_le_add (hp t) (hY t ht))).trans_eq (add_comm ..)
  · rw [field_zero_outside ht,norm_zero]
    linarith

theorem eventually_field_mem : ∀ᶠ Y : ℕ in atTop, MemLp (field Y) 2 GB5Variance.unitMeasure := by
  filter_upwards [eventually_bounded] with Y h
  obtain ⟨A,_,hA⟩ := h
  exact MemLp.of_bound (field_stronglyMeasurable Y).aestronglyMeasurable A (Eventually.of_forall hA)

private theorem square_mem_of_bound {f : ℝ → ℂ} (hf : StronglyMeasurable f)
    (A : ℝ) (hA : ∀ t, ‖f t‖ ≤ A) :
    MemLp (fun t => (f t)^2) 2 GB5Variance.unitMeasure := by
  apply MemLp.of_bound (f:=fun t => (f t)^2) (hf.pow 2).aestronglyMeasurable (A^2)
  exact Eventually.of_forall fun t =>
    (norm_pow (f t) 2).le.trans (pow_le_pow_left₀ (norm_nonneg _) (hA t) 2)

private theorem mask_difference {f g : ℝ → ℂ} {B : Set ℝ} (hB : MeasurableSet B)
    (hf : MemLp f 2 GB5Variance.unitMeasure) (hg : MemLp g 2 GB5Variance.unitMeasure) :
    MemLp (B.indicator (fun t => f t-g t)) 2 GB5Variance.unitMeasure :=
  (hf.sub hg).indicator hB.nullMeasurableSet

set_option maxHeartbeats 600000 in
theorem eventually_masked_square_mem : ∀ᶠ Y : ℕ in atTop,
    MemLp ((bandSet Y).indicator (fun t => (S Y t)^2-(field Y t)^2)) 2 GB5Variance.unitMeasure := by
  filter_upwards [eventually_bounded] with Y h
  obtain ⟨A,_,hA⟩ := h
  have hc : Continuous (fun t => (S Y t)^2) := by unfold S phase; fun_prop
  have hp : MemLp (fun t => (S Y t)^2) 2 GB5Variance.unitMeasure :=
    (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).2
      (((hc.norm.pow 2).intervalIntegrable (μ:=volume) 0 1).1)
  exact mask_difference (measurable_bandSet Y) hp
    (square_mem_of_bound (field_stronglyMeasurable Y) A hA)

def fieldCoefficient (Y m : ℕ) : ℂ := GB5Variance.modeCoeff (fun t => (field Y t)^2) m

/-- The signed Fourier discrepancy is exactly the mode of the masked square
difference. The cell boundary convention is inherited from the closed windows. -/
theorem coefficient_difference {Y : ℕ} (hm : MemLp (field Y) 2 GB5Variance.unitMeasure) (m : ℕ) :
    coefficient (bandSet Y) Y m - fieldCoefficient Y m =
      GB5Variance.modeCoeff ((bandSet Y).indicator (fun t => (S Y t)^2-(field Y t)^2)) m := by
  have hc : Continuous (integrand Y m) := by unfold integrand S phase; fun_prop
  have h1 : IntervalIntegrable ((bandSet Y).indicator (integrand Y m)) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr
      ((hc.intervalIntegrable (μ:=volume) 0 1).1.indicator (measurable_bandSet Y))
  have ha : AEStronglyMeasurable (fun t => (field Y t)^2*GB5Variance.phase (-(m:ℝ)*t)) GB5Variance.unitMeasure :=
    (hm.aestronglyMeasurable.pow 2).mul (by unfold GB5Variance.phase; fun_prop)
  have h2 : IntervalIntegrable (fun t => (field Y t)^2*GB5Variance.phase (-(m:ℝ)*t)) volume 0 1 := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr
    apply (integrable_norm_iff ha).mp
    simp only [norm_mul,norm_pow,GB5Variance.phase,Complex.norm_exp_ofReal_mul_I,mul_one]
    exact (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm
  unfold coefficient fieldCoefficient GB5Variance.modeCoeff
  rw [← intervalIntegral.integral_sub h1 h2]
  apply intervalIntegral.integral_congr
  intro t _
  by_cases ht : t ∈ bandSet Y
  · simp only [Set.indicator_of_mem ht,integrand,sub_mul]; rfl
  · simp [ht,field_zero_outside ht]

theorem bessel_difference {Y : ℕ} (hm : MemLp (field Y) 2 GB5Variance.unitMeasure)
    (h2 : MemLp ((bandSet Y).indicator (fun t => (S Y t)^2-(field Y t)^2)) 2 GB5Variance.unitMeasure)
    (s : Finset ℕ) :
    (∑ m ∈ s, ‖coefficient (bandSet Y) Y m - fieldCoefficient Y m‖^2) ≤
      ∫ t in (0:ℝ)..1, ‖(bandSet Y).indicator (fun u => (S Y u)^2-(field Y u)^2) t‖^2 := by
  simp_rw [coefficient_difference hm]
  exact GB5Variance.finite_bessel s _ h2

/-- Bessel's inequality for these actual and signed model coefficients holds
for every finite frequency set at all sufficiently large cutoffs. -/
theorem eventual_bessel_difference : ∀ᶠ Y : ℕ in atTop, ∀ s : Finset ℕ,
    (∑ m ∈ s, ‖coefficient (bandSet Y) Y m - fieldCoefficient Y m‖^2) ≤
      ∫ t in (0:ℝ)..1, ‖(bandSet Y).indicator (fun u => (S Y u)^2-(field Y u)^2) t‖^2 := by
  filter_upwards [eventually_field_mem,eventually_masked_square_mem] with Y hm h2
  exact bessel_difference hm h2

end
end Goldbach.MiddleCanonicalModel
