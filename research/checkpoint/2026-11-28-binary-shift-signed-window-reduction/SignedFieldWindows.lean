import MeasurableCanonicalField

open Filter Finset MeasureTheory
namespace Goldbach.MiddleCanonicalModel
open ShiftWideArc
noncomputable section
open scoped Classical

/-- All and only the denominators in the intermediate band. -/
def bandDenominators (Y : ℕ) :=
  Icc ((Nat.log 2 (Y+2))^2+1)
    (min (GB6Growth.grid Y) (⌈(Y:ℝ)^(1/4:ℝ)⌉₊-1))

private abbrev centers (Y : ℕ) := (bandDenominators Y).sigma GB6Geometry.numerators

private theorem mem_iff {Y : ℕ} {i : GB6Geometry.Idx} {t : ℝ} :
    bandCenter Y t i.1 i.2 ↔ i ∈ centers Y ∧ t ∈ GB6Geometry.window (H Y) Y i.1 i.2 := by
  obtain ⟨q,a⟩ := i
  change bandCenter Y t q a ↔ (⟨q,a⟩ : GB6Geometry.Idx) ∈ centers Y ∧
    t ∈ GB6Geometry.window (H Y) Y q a
  constructor
  · rintro ⟨_,hl,hu,ha,hc,hw⟩
    have hq : q ∈ bandDenominators Y := mem_Icc.mpr ⟨Nat.succ_le_of_lt hl,hu⟩
    have han : a ∈ GB6Geometry.numerators q := mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le ha),hc⟩
    exact ⟨mem_sigma.mpr ⟨hq,han⟩,(GB6Geometry.mem_window Y q a t).mpr hw⟩
  · rintro ⟨hi,ht⟩
    obtain ⟨hq,han⟩ := mem_sigma.mp hi
    have hq' : ((Nat.log 2 (Y+2))^2+1 ≤ q ∧
        q ≤ min (GB6Growth.grid Y) (⌈(Y:ℝ)^(1/4:ℝ)⌉₊-1)) := mem_Icc.mp hq
    have ha' : a ∈ GB6Geometry.numerators q := han
    obtain ⟨ham,hc⟩ := mem_filter.mp ha'
    have hh : a < q+1 := mem_range.mp ham
    exact ⟨(Nat.zero_lt_succ _).trans_le hq'.1,Nat.lt_of_succ_le hq'.1,hq'.2,
      Nat.le_of_lt_succ hh,hc,(GB6Geometry.mem_window Y q a t).mp ht⟩

private theorem geometric_index {Y : ℕ} {i : GB6Geometry.Idx} (hi : i ∈ centers Y) :
    i ∈ GB6Geometry.indices (Q Y) := by
  obtain ⟨hq,ha⟩ := mem_sigma.mp hi
  obtain ⟨hl,hu⟩ := mem_Icc.mp hq
  have hu' := (hu.trans (min_le_left ..)).trans_eq (GB6Growth.grid_eq_floor Y)
  exact mem_sigma.mpr ⟨mem_Icc.mpr ⟨by omega,hu'⟩,ha⟩

/-- Both endpoints lie inside [0,1]. This uses that every center here has
denominator strictly bigger than one and a coprime numerator. -/
theorem band_window_uncut {Y q a : ℕ} (hsep : 2*(H Y)^2 < Y)
    (hq : q ∈ bandDenominators Y) (ha : a ∈ GB6Geometry.numerators q) :
    GB6Geometry.leftEnd (H Y) Y q a = -GB6Geometry.width (H Y) Y q ∧
    GB6Geometry.rightEnd (H Y) Y q a = GB6Geometry.width (H Y) Y q := by
  have hlog : 1 ≤ Nat.log 2 (Y+2) := Nat.le_log_of_pow_le (by decide) (by simp)
  have hq' : 1<q := by
    have hh := (mem_Icc.mp hq).1
    have hp : 1 ≤ (Nat.log 2 (Y+2))^2 := one_le_pow₀ hlog
    omega
  obtain ⟨hb,hc⟩ := mem_filter.mp ha
  have hle : a ≤ q := Nat.le_of_lt_succ (mem_range.mp hb)
  have ha₁ : 0 < a := by
    by_contra! h
    obtain rfl : a=0 := by omega
    simp [Nat.Coprime] at hc
    omega
  have haq : a < q := by
    have hne : a ≠ q := by rintro rfl; simp [Nat.Coprime] at hc; omega
    omega
  have hqr : 0 < (q:ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hw := GB6Geometry.width_le_unit hsep (by omega : 0 < q)
  have hc₁ : 1/(q:ℝ) ≤ GB6Geometry.center q a :=
    div_le_div_of_nonneg_right (by exact_mod_cast ha₁) hqr.le
  have hc₂ : GB6Geometry.center q a + 1/q ≤ 1 := by
    rw [GB6Geometry.center, ← add_div, div_le_one hqr]
    exact_mod_cast (Nat.succ_le_of_lt haq)
  unfold GB6Geometry.leftEnd GB6Geometry.rightEnd
  rw [max_eq_left (by linarith), min_eq_left (by linarith)]
  constructor <;> ring

private theorem phase_add (x y : ℝ) : phase (x+y) = phase x * phase y := by
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Local signed square at its original denominator, in translated coordinates. -/
def centeredMode (Y q a m : ℕ) : ℂ :=
  ∫ β in -(GB6Geometry.width (H Y) Y q)..GB6Geometry.width (H Y) Y q,
    (centerValue Y q a β)^2 * phase (-(m:ℝ)*β)

/-- Each individual band window contributes a single centered integral times
its exact Fourier translation phase. -/
theorem single_window {Y q a : ℕ} (hsep : 2*(H Y)^2 < Y) (hQ : Q Y ≤ H Y)
    (hq : q ∈ bandDenominators Y) (ha : a ∈ GB6Geometry.numerators q) (m : ℕ) :
    (∫ t in (0:ℝ)..1, (GB6Geometry.window (H Y) Y q a).indicator
      (fun u => (field Y u)^2 * phase (-(m:ℝ)*u)) t) =
    phase (-(m:ℝ)*((a:ℝ)/q)) * centeredMode Y q a m := by
  let c := GB6Geometry.center q a
  let w := GB6Geometry.width (H Y) Y q
  have hq0 : 0 < q := by have := (mem_Icc.mp hq).1; omega
  have haq := Nat.le_of_lt_succ (mem_range.mp (mem_filter.mp ha).1)
  obtain ⟨hl,hr⟩ := band_window_uncut hsep hq ha
  rw [GB6Geometry.indicator_clipped hq0 haq,hl,hr]
  unfold centeredMode
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro β hβ
  have hw : 0 ≤ w := GB6Geometry.width_nonneg Y q
  change β ∈ Set.uIcc (-w) w at hβ
  rw [Set.uIcc_of_le (by linarith : -w ≤ w)] at hβ
  have hδ : c+β-c=β := by ring
  have ht : c+β ∈ GB6Geometry.window (H Y) Y q a := by
    apply (GB6Geometry.mem_window Y q a _).mpr
    change |c+β-c| ≤ w
    rw [hδ]
    exact abs_le.mpr hβ
  have hb := (mem_iff (i:=⟨q,a⟩)).mpr ⟨mem_sigma.mpr ⟨hq,ha⟩,ht⟩
  have hfield := field_eq_center hsep hQ hb
  change field Y (c+β) = centerValue Y q a (c+β-c) at hfield
  change (field Y (c+β))^2 * phase (-(m:ℝ)*(c+β)) =
    phase (-(m:ℝ)*c) * ((centerValue Y q a β)^2 * phase (-(m:ℝ)*β))
  rw [hδ] at hfield
  rw [hfield,mul_add,phase_add]
  ring

private theorem field_assembly {Y : ℕ} (hsep : 2*(H Y)^2 < Y) (hQ : Q Y ≤ H Y)
    (hm : MemLp (field Y) 2 GB5Variance.unitMeasure) (m : ℕ) :
    fieldCoefficient Y m = ∑ i ∈ centers Y,
      ∫ t in (0:ℝ)..1, (GB6Geometry.window (H Y) Y i.1 i.2).indicator
        (fun u => (field Y u)^2 * phase (-(m:ℝ)*u)) t := by
  let V (u : ℝ) := (field Y u)^2 * phase (-(m:ℝ)*u)
  let term (i : GB6Geometry.Idx) := (GB6Geometry.window (H Y) Y i.1 i.2).indicator V
  have ha : AEStronglyMeasurable V GB5Variance.unitMeasure :=
    (hm.aestronglyMeasurable.pow 2).mul (by unfold phase; fun_prop)
  have hI : Integrable V GB5Variance.unitMeasure := by
    apply (integrable_norm_iff ha).mp
    simp only [V,norm_mul,norm_pow,phase,Complex.norm_exp_ofReal_mul_I,mul_one]
    exact (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm
  have hin (i : GB6Geometry.Idx) : IntervalIntegrable (term i) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr
      (hI.indicator (show MeasurableSet (GB6Geometry.window (H Y) Y i.1 i.2) from measurableSet_Icc))
  have heq (t : ℝ) : V t = ∑ i ∈ centers Y, term i t := by
    by_cases ht : t ∈ bandSet Y
    · obtain ⟨q,a,hw⟩ := ht
      let i : GB6Geometry.Idx := ⟨q,a⟩
      obtain ⟨hi,hit⟩ := (mem_iff (i:=i)).mp hw
      rw [sum_eq_single_of_mem i hi]
      · exact (Set.indicator_of_mem hit _).symm
      · intro j hj hne
        apply Set.indicator_of_notMem
        intro hjt
        exact hne (GB6Geometry.unique_window hsep hQ t ⟨geometric_index hj,hjt⟩ ⟨geometric_index hi,hit⟩)
    · have hz (j : GB6Geometry.Idx) (hj : j ∈ centers Y) : term j t = 0 := by
        apply Set.indicator_of_notMem
        intro hjt
        exact ht ⟨j.1,j.2,mem_iff.mpr ⟨hj,hjt⟩⟩
      rw [sum_eq_zero hz]
      simp [V,field_zero_outside ht]
  change (∫ t in (0:ℝ)..1, V t) = ∑ i ∈ centers Y, ∫ t in (0:ℝ)..1, term i t
  rw [← intervalIntegral.integral_finsetSum (fun i _ => hin i)]
  exact intervalIntegral.integral_congr (fun t _ => heq t)

/-- Exact centered Fourier expansion for every frequency simultaneously.
The outer phase, the Mellin zero terms, and the complex square retain their signs. -/
theorem eventual_fieldCoefficient_by_window : ∀ᶠ Y : ℕ in atTop, ∀ m : ℕ,
    fieldCoefficient Y m = ∑ q ∈ bandDenominators Y, ∑ a ∈ GB6Geometry.numerators q,
      phase (-(m:ℝ)*((a:ℝ)/q)) * centeredMode Y q a m := by
  filter_upwards [GB6Growth.eventual_geometry,eventually_field_mem] with Y hg hm
  have hq : GB6Growth.grid Y = Q Y := GB6Growth.grid_eq_floor Y
  have hH : GB6Growth.height Y = H Y := by simp only [GB6Growth.height,H,hq]
  obtain ⟨_,hqH,_,_,hs⟩ := hg
  rw [hH] at hs
  rw [hH,hq] at hqH
  intro m
  rw [field_assembly hs hqH hm m,centers,sum_sigma]
  apply sum_congr rfl
  intro q hqi
  apply sum_congr rfl
  intro a hai
  exact single_window hs hqH hqi hai m

end
end Goldbach.MiddleCanonicalModel
