import MeasurableCanonicalField

open Finset Filter MeasureTheory
namespace Goldbach.PrincipalZeroOffset
open MiddleCanonicalModel ShiftWideArc
noncomputable section
open scoped Classical

/-- The positive-index kernel and the full geometric kernel differ by the
constant Fourier mode, including at cutoff zero. -/
theorem kernel_split (Y : ℕ) (β : ℝ) :
    GB6Kernel.kernel Y β = 1 + DeepThreeQuarters.positiveGeometricSum Y β := by
  unfold GB6Kernel.kernel DeepThreeQuarters.positiveGeometricSum
  rw [Nat.range_succ_eq_Icc_zero, ← Finset.add_sum_Ioc_eq_sum_Icc (Nat.zero_le Y)]
  have hI : Ioc 0 Y = Icc 1 Y := by
    ext k
    simp only [mem_Ioc,mem_Icc]
    omega
  rw [hI]
  simp only [Nat.cast_zero,zero_mul,GB6Kernel.phase,Complex.ofReal_zero,mul_zero,
    Complex.exp_zero,DeepThreeQuarters.geometricPhase]

theorem mean_eq_moebius {q a : ℕ} (ha : a.Coprime q) :
    ThreeQArith.mean q a = (ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ) := by
  rw [ThreeQArith.mean_eq_ram ha]
  exact congrArg (fun z : ℂ => z / (q.totient : ℂ)) (GoldbachExplicitModeledMajor.ram_one_eq_moebius q)

theorem center_eq {q a : ℕ} [NeZero q] (ha : a.Coprime q) (Y : ℕ) (β : ℝ) :
    centerValue Y q a β = ThreeQArith.mean q a * GB6Kernel.kernel Y β -
      (GoldbachTwistedMellin.canonicalCorrection Y (a : ZMod q) β + ThreeQArith.mean q a) := by
  simp only [centerValue,dif_neg (NeZero.ne q),DeepThreeQuarters.rationalModel]
  rw [← mean_eq_moebius ha,kernel_split]
  ring

/-- The sign and the constant mode are retained before the frequency integral. -/
theorem center_square_offset {q a : ℕ} [NeZero q] (ha : a.Coprime q) (Y : ℕ) (β : ℝ) :
    let c := ThreeQArith.mean q a
    let M := c * GB6Kernel.kernel Y β
    let z := GoldbachTwistedMellin.canonicalCorrection Y (a : ZMod q) β + c
    (centerValue Y q a β)^2 - M^2 = z^2 - 2*M*z := by
  dsimp only
  rw [center_eq ha]
  ring

def rowTerm (Y q a : ℕ) (β : ℝ) : ℂ :=
  if hq : q = 0 then 0 else
    letI : NeZero q := ⟨hq⟩
    let c := ThreeQArith.mean q a
    let M := c * GB6Kernel.kernel Y β
    let z := GoldbachTwistedMellin.canonicalCorrection Y (a : ZMod q) β + c
    z^2 - 2*M*z

def signedRows (Y : ℕ) (t : ℝ) : ℂ :=
  ∑ i ∈ GB6Geometry.indices (Q Y), {u : ℝ | bandCenter Y u i.1 i.2}.indicator
    (fun u => rowTerm Y i.1 i.2 (u-(i.2:ℝ)/i.1)) t

def pureField (Y : ℕ) : ℝ → ℂ := (bandSet Y).indicator (GB6Var.G (Q Y) (H Y) Y)

private theorem geometry {Y q a : ℕ} {t : ℝ} (hw : bandCenter Y t q a) :
    (⟨q,a⟩:GB6Geometry.Idx) ∈ GB6Geometry.indices (Q Y) ∧
    t ∈ GB6Geometry.window (H Y) Y q a := by
  obtain ⟨hq,_,hu,ha,hc,ht⟩ := hw
  have hqQ := (hu.trans (min_le_left ..)).trans_eq (GB6Growth.grid_eq_floor Y)
  exact ⟨mem_sigma.mpr ⟨mem_Icc.mpr ⟨hq,hqQ⟩,mem_filter.mpr ⟨mem_range.mpr (by change a < q+1; omega),hc⟩⟩,
    (GB6Geometry.mem_window Y q a t).mpr ht⟩

theorem field_square_difference {Y : ℕ} (hs : 2*(H Y)^2 < Y) (hQ : Q Y ≤ H Y) (t : ℝ) :
    (field Y t)^2 - (pureField Y t)^2 = signedRows Y t := by
  by_cases ht : t ∈ bandSet Y
  · obtain ⟨q,a,hw⟩ := ht
    let i : GB6Geometry.Idx := ⟨q,a⟩
    obtain ⟨hi,hwin⟩ := geometry hw
    have hq := hw.1
    letI : NeZero q := ⟨by omega⟩
    have hc := hw.2.2.2.2.1
    have hband : t ∈ bandSet Y := ⟨q,a,hw⟩
    have hr : signedRows Y t = rowTerm Y q a (t-(a:ℝ)/q) := by
      unfold signedRows
      rw [sum_eq_single_of_mem i hi]
      · exact Set.indicator_of_mem hw _
      · intro j hj hn
        apply Set.indicator_of_notMem
        intro h
        exact hn (GB6Geometry.unique_window hs hQ t ⟨hj,(geometry h).2⟩ ⟨hi,hwin⟩)
    have hp : pureField Y t = ThreeQArith.mean q a * GB6Kernel.kernel Y (t-(a:ℝ)/q) := by
      unfold pureField
      rw [Set.indicator_of_mem hband,GB6Var.G,GB6Geometry.model_sigma,sum_eq_single_of_mem i hi]
      · exact Set.indicator_of_mem hwin _
      · intro j hj hne
        apply Set.indicator_of_notMem
        intro hjwin
        exact hne (GB6Geometry.unique_window hs hQ t ⟨hj,hjwin⟩ ⟨hi,hwin⟩)
    rw [field_eq_center hs hQ hw,hp,hr]
    simpa only [rowTerm,dif_neg (NeZero.ne q)] using center_square_offset hc Y (t-(a:ℝ)/q)
  · have hr : signedRows Y t = 0 := by
      apply sum_eq_zero
      intro i _
      exact Set.indicator_of_notMem (fun h => ht ⟨i.1,i.2,h⟩) _
    simp [field_zero_outside ht,pureField,ht,hr]

private theorem mode_integrable {F : ℝ → ℂ} (hm : MemLp F 2 GB5Variance.unitMeasure) (m : ℕ) :
    IntervalIntegrable (fun t => (F t)^2*GB5Variance.phase (-(m:ℝ)*t)) volume (0:ℝ) 1 := by
  have ha : AEStronglyMeasurable (fun t => (F t)^2*GB5Variance.phase (-(m:ℝ)*t)) GB5Variance.unitMeasure :=
    (hm.aestronglyMeasurable.pow 2).mul (by unfold GB5Variance.phase; fun_prop)
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr
  apply (integrable_norm_iff ha).mp
  simp only [norm_mul,norm_pow,GB5Variance.phase,Complex.norm_exp_ofReal_mul_I,mul_one]
  exact (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm

/-- At the same frequency, the corrected-model coefficient minus the pure
principal coefficient is exactly the signed sum of the center corrections. -/
theorem coefficient_offset : ∀ᶠ Y : ℕ in atTop, ∀ m : ℕ,
    fieldCoefficient Y m - GB5Variance.modeCoeff (fun t => (pureField Y t)^2) m =
      GB5Variance.modeCoeff (signedRows Y) m := by
  filter_upwards [GB6Growth.eventual_geometry,eventually_field_mem] with Y hg hmem
  have hgrid : GB6Growth.grid Y = Q Y := GB6Growth.grid_eq_floor Y
  have hheight : GB6Growth.height Y = H Y := by simp only [GB6Growth.height,H,hgrid]
  have hsep : 2*(H Y)^2 < Y := by simpa only [hheight] using hg.2.2.2.2
  have hQ : Q Y ≤ H Y := by simpa only [hgrid,hheight] using hg.2.1
  have hp : MemLp (pureField Y) 2 GB5Variance.unitMeasure :=
    (GB6Var.G_memLp (Q Y) (H Y) Y).indicator (measurable_bandSet Y).nullMeasurableSet
  intro m
  unfold fieldCoefficient GB5Variance.modeCoeff
  rw [← intervalIntegral.integral_sub (mode_integrable hmem m) (mode_integrable hp m)]
  apply intervalIntegral.integral_congr
  intro t _
  change (field Y t)^2 * GB5Variance.phase (-(m:ℝ)*t) -
    (pureField Y t)^2 * GB5Variance.phase (-(m:ℝ)*t) =
      signedRows Y t * GB5Variance.phase (-(m:ℝ)*t)
  rw [← sub_mul,field_square_difference hsep hQ t]

/-- This expression also occurs, with the same grid and widths, in the pure
middle-denominator floor. The indicator is on the entire twisted integrand. -/
theorem mode_pureField_eq_masked (Y m : ℕ) :
    GB5Variance.modeCoeff (fun t => (pureField Y t)^2) m =
      ∫ t in (0:ℝ)..1, (bandSet Y).indicator (fun u =>
        (GB6Var.G (GB6Growth.grid Y) (GB6Growth.height Y) Y u)^2 *
          GB6Kernel.phase (-(m:ℝ)*u)) t := by
  have hgrid : GB6Growth.grid Y = Q Y := GB6Growth.grid_eq_floor Y
  have hheight : GB6Growth.height Y = H Y := by simp only [GB6Growth.height,H,hgrid]
  rw [hgrid,hheight]
  unfold GB5Variance.modeCoeff
  apply intervalIntegral.integral_congr
  intro t _
  by_cases ht : t ∈ bandSet Y
  · simp only [pureField,Set.indicator_of_mem ht]; rfl
  · simp [pureField,ht]

theorem coefficient_offset_masked : ∀ᶠ Y : ℕ in atTop, ∀ m : ℕ,
    fieldCoefficient Y m -
      (∫ t in (0:ℝ)..1, (bandSet Y).indicator (fun u =>
        (GB6Var.G (GB6Growth.grid Y) (GB6Growth.height Y) Y u)^2 *
          GB6Kernel.phase (-(m:ℝ)*u)) t) =
      GB5Variance.modeCoeff (signedRows Y) m := by
  filter_upwards [coefficient_offset] with Y h
  intro m
  rw [← mode_pureField_eq_masked]
  exact h m

end
end Goldbach.PrincipalZeroOffset
#print axioms Goldbach.PrincipalZeroOffset.coefficient_offset_masked
