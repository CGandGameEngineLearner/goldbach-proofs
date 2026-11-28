import ShiftSignedCommonLow
import CanonicalDyadicPairs
import PrincipalZeroOffset


open Filter Finset MeasureTheory
namespace Goldbach.PrincipalMiddleFloor
open ShiftWideArc InnerArcCriterion LowWideMiddleBand
noncomputable section
open scoped Classical

private abbrev I (Y m : ℕ) := coefficient (inner OuterPrimeArc.outer Y) Y m
private abbrev F (Y m : ℕ) := coefficient (arcs Y) Y m

/-- Pure principal band coefficient, with the common physical width at both cutoffs. -/
def principal (Y m : ℕ) : ℂ :=
  ReflectedArcModel.truncatedCoefficient (ReflectedArcModel.innerCutoff Y) Y m - FullLowWide.modelCoeff Y m

/-- The Ramanujan factor is evaluated at the actual frequency, including
when the analytic kernel has been reflected. -/
def principalTerm (Y m q : ℕ) : ℂ := ThreeQArith.coefficient q m *
  ∫ t in -(GB6Geometry.width (GB6Growth.height Y) Y q)..GB6Geometry.width (GB6Growth.height Y) Y q,
    GB6Kernel.twisted Y m t

private theorem trunc_sum {Y r m : ℕ} (hs : 2*(GB6Growth.height Y)^2<Y) (hr : r ≤ GB6Growth.height Y) :
    ReflectedArcModel.truncatedCoefficient r Y m = ∑ q ∈ Icc 1 r, principalTerm Y m q := by
  unfold ReflectedArcModel.truncatedCoefficient
  rw [GB6Geometry.exact_model_coeff ThreeQArith.mean (by simp [ThreeQArith.mean,ThreeQArith.phase]) hs hr]
  apply sum_congr rfl
  intro q hq
  unfold principalTerm
  congr 1
  exact ThreeQArith.sum_centers_eq_coefficient q m

/-- Exact denominator-by-denominator formula on the intermediate band. -/
theorem principal_eq_band :
    ∀ᶠ Y : ℕ in atTop, ∀ m : ℕ, principal Y m =
      ∑ q ∈ Ioc (GoldbachGRHBudget.narrow Y) (ReflectedArcModel.innerCutoff Y), principalTerm Y m q := by
  filter_upwards [GB6Growth.eventual_geometry, GoldbachGRHBudget.eventual_geometry,
    GB6Growth.polylog_le_power 2 (by norm_num) 2 (1/4) (by norm_num)] with Y hg hb hsmall
  intro m
  have hQ : GB6Growth.grid Y = GoldbachGRHBudget.cutoff Y := GB6Growth.grid_eq_floor Y
  have hH : GB6Growth.height Y = GoldbachGRHBudget.width Y := by
    simp only [GB6Growth.height,GoldbachGRHBudget.width,hQ,GoldbachGRHBudget.narrow]
  have hD : 1 ≤ GoldbachGRHBudget.narrow Y := hb.2.1
  have hDQ : GoldbachGRHBudget.narrow Y ≤ GB6Growth.grid Y := hb.2.2.1.trans_eq hQ.symm
  have hd : GoldbachGRHBudget.narrow Y ≤ ReflectedArcModel.innerCutoff Y := by
    apply (ReflectedArcModel.mem_innerCutoff hD).mpr
    refine ⟨hDQ,?_⟩
    have hlog := GB6Growth.L_le_logFactor Y
    have h0 : 0≤GB6Growth.L Y := (GB6Growth.L_one Y).trans' zero_le_one
    have hh := pow_le_pow_left₀ h0 hlog 2
    have hp : 0<(GoldbachGRHBudget.narrow Y:ℝ) := by exact_mod_cast hD
    have hh' : (GoldbachGRHBudget.narrow Y:ℝ) ≤ (GB6Growth.logFactor Y)^2 := by simpa [GoldbachGRHBudget.narrow,GB6Growth.L] using hh
    linarith only [hsmall,hh',hp]
  have hi : ReflectedArcModel.innerCutoff Y ≤ GB6Growth.grid Y := min_le_left ..
  rw [principal,←FullLowWide.model_assembly m (by simpa only [hH] using hg.2.2.2.2)
    (hDQ.trans (hg.2.1.trans_eq hH)) hH,
    trunc_sum hg.2.2.2.2 (hi.trans hg.2.1),trunc_sum hg.2.2.2.2 (hDQ.trans hg.2.1)]
  have hu : Icc 1 (ReflectedArcModel.innerCutoff Y) =
      Icc 1 (GoldbachGRHBudget.narrow Y) ∪ Ioc (GoldbachGRHBudget.narrow Y) (ReflectedArcModel.innerCutoff Y) := by
    ext q
    simp only [mem_union,mem_Icc,mem_Ioc]
    omega
  have hdj : Disjoint (Icc 1 (GoldbachGRHBudget.narrow Y))
      (Ioc (GoldbachGRHBudget.narrow Y) (ReflectedArcModel.innerCutoff Y)) := by
    refine disjoint_left.mpr ?_
    intro q hq hq'
    exact (not_lt_of_ge (mem_Icc.mp hq).2) (mem_Ioc.mp hq').1
  rw [hu,sum_union hdj,add_sub_cancel_left]

/-- The full rational model agrees with a truncation inside its cap and the
truncation vanishes outside. All windows use the original scale's width. -/
private theorem mask_model {Y : ℕ} (hsep : 2*(GB6Growth.height Y)^2<Y)
    (hQH : GB6Growth.grid Y ≤ GB6Growth.height Y) {r : ℕ} (hr : r ≤ GB6Growth.grid Y) (t : ℝ) :
    GB6Geometry.model r (GB6Growth.height Y) Y ThreeQArith.mean t =
    (InnerArcGeometry.windowsTo r Y).indicator
      (GB6Geometry.model (GB6Growth.grid Y) (GB6Growth.height Y) Y ThreeQArith.mean) t := by
  classical
  let H := GB6Growth.height Y
  let Q := GB6Growth.grid Y
  have hH : H = ShiftWideArc.H Y := by
    simp only [H,GB6Growth.height,ShiftWideArc.H,ShiftWideArc.Q,GB6Growth.grid_eq_floor]
  have hmem {i : GB6Geometry.Idx} (hi : i ∈ GB6Geometry.indices r)
      (hw : t ∈ GB6Geometry.window H Y i.1 i.2) :
      t ∈ InnerArcGeometry.windowsTo r Y := by
    obtain ⟨h1,h2⟩ := mem_sigma.mp hi
    obtain ⟨ha,hc⟩ := mem_filter.mp h2
    refine ⟨i.1,i.2,(mem_Icc.mp h1).1,(mem_Icc.mp h1).2,
      Nat.le_of_lt_succ (mem_range.mp ha),hc,?_⟩
    simpa only [GB6Geometry.center,GB6Geometry.width,hH] using (GB6Geometry.mem_window Y i.1 i.2 t).mp hw
  by_cases ht : t ∈ InnerArcGeometry.windowsTo r Y
  · rw [Set.indicator_of_mem ht]
    obtain ⟨q,a,hq,hqr,ha,hc,hw⟩ := ht
    let i : GB6Geometry.Idx := ⟨q,a⟩
    have hi : i ∈ GB6Geometry.indices r := mem_sigma.mpr ⟨mem_Icc.mpr ⟨hq,hqr⟩,
      mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le ha),hc⟩⟩
    have lift {j : GB6Geometry.Idx} (h : j ∈ GB6Geometry.indices r) : j ∈ GB6Geometry.indices Q := by
      obtain ⟨hq,ha⟩ := mem_sigma.mp h
      exact mem_sigma.mpr ⟨mem_Icc.mpr ⟨(mem_Icc.mp hq).1,(mem_Icc.mp hq).2.trans hr⟩,ha⟩
    have hwi : t ∈ GB6Geometry.window H Y i.1 i.2 := (GB6Geometry.mem_window Y q a t).mpr
      (by simpa only [GB6Geometry.center, GB6Geometry.width,hH] using hw)
    have hnot (j : GB6Geometry.Idx) (hj : j ∈ GB6Geometry.indices Q) (hne : j ≠ i) :
        t ∉ GB6Geometry.window H Y j.1 j.2 := fun hw' =>
      hne (GB6Geometry.unique_window hsep hQH t ⟨hj,hw'⟩ ⟨lift hi,hwi⟩)
    rw [GB6Geometry.model_sigma,GB6Geometry.model_sigma,
        sum_eq_single_of_mem i hi (fun j hj hne => Set.indicator_of_notMem (hnot j (lift hj) hne) _),
        sum_eq_single_of_mem i (lift hi) (fun j hj hne => Set.indicator_of_notMem (hnot j hj hne) _)]
  · rw [Set.indicator_of_notMem ht,GB6Geometry.model_sigma]
    exact sum_eq_zero fun i hi => Set.indicator_of_notMem (fun h => ht (hmem hi h)) _

def maskedPrincipal (Y m : ℕ) : ℂ := ∫ t in (0:ℝ)..1,
  (denominatorBand Y).indicator (fun u => (ShiftTimeEnergy.M Y u)^2 * GB6Kernel.phase (-(m:ℝ)*u)) t

/-- The pure coefficient is literally the square of the model masked to the
intermediate band, with numerator-endpoint arcs treated consistently. -/
theorem principal_eq_masked : ∀ᶠ Y : ℕ in atTop, ∀ m : ℕ, principal Y m = maskedPrincipal Y m := by
  filter_upwards [GB6Growth.eventual_geometry,GoldbachGRHBudget.eventual_geometry,
    InnerArcGeometry.eventual_inner_eq,eventual_middle_eq_band,eventual_low_subset] with Y hg hb hinner hband hsub
  intro m
  have hQ : GB6Growth.grid Y = GoldbachGRHBudget.cutoff Y := GB6Growth.grid_eq_floor Y
  have hH : GB6Growth.height Y = GoldbachGRHBudget.width Y := by
    simp only [GB6Growth.height,GoldbachGRHBudget.width,hQ,GoldbachGRHBudget.narrow]
  have hDQ := hb.2.2.1.trans_eq hQ.symm
  have hloe : InnerArcGeometry.windowsTo (GoldbachGRHBudget.narrow Y) Y = low Y := by rfl
  have hinner' : InnerArcGeometry.windowsTo (ReflectedArcModel.innerCutoff Y) Y = inner OuterPrimeArc.outer Y := hinner.symm
  have hmem : MeasurableSet (inner OuterPrimeArc.outer Y) :=
    (EffectiveArcEndpoint.frontierMeasurable _ _ _).diff (OuterPrimeArc.outer_measurable Y)
  let P := fun t => (ShiftTimeEnergy.M Y t)^2 * GB6Kernel.phase (-(m:ℝ)*t)
  have hi : IntervalIntegrable P volume 0 1 := by
    have hLp := GB6Var.G_memLp (GB6Growth.grid Y) (GB6Growth.height Y) Y
    have ha : AEStronglyMeasurable P GB5Variance.unitMeasure := (hLp.aestronglyMeasurable.pow 2).mul
      (by unfold GB6Kernel.phase; fun_prop)
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr
    apply (integrable_norm_iff ha).mp
    have hsq := (memLp_two_iff_integrable_sq_norm hLp.aestronglyMeasurable).mp hLp
    simpa only [P,norm_mul,norm_pow,GB6Kernel.phase,Complex.norm_exp_ofReal_mul_I,mul_one] using hsq
  have hi' (A : Set ℝ) (hA : MeasurableSet A) : IntervalIntegrable (A.indicator P) volume 0 1 :=
    ⟨hi.1.indicator hA,hi.2.indicator hA⟩
  have heq (r : ℕ) (hr : r ≤ GB6Growth.grid Y) :
      ReflectedArcModel.truncatedCoefficient r Y m = ∫ t in (0:ℝ)..1, (InnerArcGeometry.windowsTo r Y).indicator P t := by
    apply intervalIntegral.integral_congr
    intro t _
    change (GB6Geometry.model r (GB6Growth.height Y) Y ThreeQArith.mean t)^2 * _ = _
    rw [mask_model hg.2.2.2.2 hg.2.1 hr]
    by_cases h : t ∈ InnerArcGeometry.windowsTo r Y <;> simp [h,P]
  rw [principal,←FullLowWide.model_assembly m (by simpa only [hH] using hg.2.2.2.2)
      (hDQ.trans (hg.2.1.trans_eq hH)) hH,heq (ReflectedArcModel.innerCutoff Y) (min_le_left ..),heq (GoldbachGRHBudget.narrow Y) hDQ,hloe,hinner',
      ←intervalIntegral.integral_sub (hi' _ hmem) (hi' (low Y) (show MeasurableSet (low Y) from GoldbachGRHArcs.measurable_cap ..))]
  apply intervalIntegral.integral_congr
  intro t _
  change _ = (denominatorBand Y).indicator P t
  rw [←hband]
  by_cases h : t ∈ low Y
  · simp [middle,h,hsub h]
  · by_cases h' : t ∈ inner OuterPrimeArc.outer Y <;> simp [middle,h,h']

/-- Count failing pairs (Y,m) with m even and Y an interior scale for m. -/
def bad (Y m : ℕ) : Prop := Even m ∧ (coefficient (denominatorBand Y) Y m - principal Y m).re < -(Y:ℝ)/64

def badPairCount (X : ℕ) : ℕ :=
  ∑ m ∈ Icc (X/2) (2*X), ((interiorScales m).filter (fun Y => bad Y m)).card

private def patch (Y m : ℕ) := Even m ∧ ‖I Y m‖ < 3*(Y:ℝ)/32
private def T (Y m : ℕ) : ℂ := if patch Y m then (((Y:ℝ)/8:ℝ):ℂ) else I Y m

theorem principal_plus_actual_low (hp : GBSkirtVariance.PaperInput) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ Y : ℕ in atTop, ∀ m : ℕ, Y ≤ m → 2*m ≤ 3*Y → Even m →
    (Y:ℝ)/8 - ε*Y ≤ (principal Y m + coefficient (low Y) Y m).re := by
  obtain ⟨N,hN⟩ := ReflectedArcModel.inner_model_floor
  filter_upwards [FullLowWide.eventual_error_uniform_of_short_ap hp ε hε,
    eventually_ge_atTop N] with Y herr hY
  intro m hlo hhi he
  have hf := hN Y hY m hlo hhi he
  have hzero : GoldbachGRHArcs.cap Y 0 0 = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro t ⟨q,a,hq,hq',_⟩
    omega
  have ha : FullLowWide.actualCoeff Y m = coefficient (low Y) Y m := by
    simp only [FullLowWide.actualCoeff,hzero,Set.sdiff_empty]
    rfl
  have hh := (Complex.abs_re_le_norm _).trans (herr m)
  rw [Complex.sub_re,ha] at hh
  simp only [principal,Complex.add_re,Complex.sub_re]
  linarith only [hf,(abs_le.mp hh).1]

private theorem floor_geometry (hp : GBSkirtVariance.PaperInput) :
    ∀ᶠ Y : ℕ in atTop, ∀ m : ℕ, Y ≤ m → 2*m ≤ 3*Y → patch Y m → bad Y m := by
  filter_upwards [eventual_low_subset,eventual_middle_eq_band,
    principal_plus_actual_low hp (by norm_num : 0<(1/64:ℝ))] with Y hs hb hlow
  intro m h1 h2 h
  obtain ⟨he,hsml⟩ := h
  refine ⟨he,?_⟩
  have hl := hlow m h1 h2 he
  rw [Complex.add_re] at hl
  have hi : I Y m = coefficient (middle Y) Y m + coefficient (low Y) Y m := by
    have ha : MeasurableSet (inner OuterPrimeArc.outer Y) :=
      (EffectiveArcEndpoint.frontierMeasurable _ _ _).diff (OuterPrimeArc.outer_measurable Y)
    have hlm : MeasurableSet (low Y) := GoldbachGRHArcs.measurable_cap ..
    have hc : Continuous (integrand Y m) := by unfold integrand S phase; fun_prop
    have hm (D : Set ℝ) (hD : MeasurableSet D) : IntervalIntegrable (D.indicator (integrand Y m)) volume 0 1 :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr ((hc.intervalIntegrable (μ:=volume) 0 1).1.indicator hD)
    unfold I coefficient
    rw [← intervalIntegral.integral_add (hm (middle Y) (ha.diff hlm)) (hm _ hlm)]
    apply intervalIntegral.integral_congr
    intro t _
    by_cases ht : t ∈ low Y
    · simp [middle,ht,hs ht]
    · by_cases ht' : t ∈ inner OuterPrimeArc.outer Y <;> simp [middle,ht,ht']
  have hr := (Complex.re_le_norm (I Y m)).trans_lt hsml
  rw [hi,Complex.add_re,hb] at hr
  rw [Complex.sub_re]
  linarith only [hl,hr]

private theorem patch_floor :
    ∃ N : ℕ, ∀ Y ≥ N, ∀ m : ℕ, Y ≤ m → 2*m ≤ 3*Y → Even m →
      ∀ z : ℂ, ‖z‖ ≤ (Y:ℝ)^(23/24:ℝ) → (Y:ℝ)/16 ≤ ‖T Y m-z‖ := by
  have hg := ((tendsto_rpow_atTop (by norm_num : 0 < (1/24:ℝ))).comp
    (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop 32
  apply eventually_atTop.mp
  filter_upwards [hg,eventually_ge_atTop (1:ℕ)] with Y hY hy
  intro m _ _ he z hz
  have hp : 0 < (Y:ℝ) := by exact_mod_cast (show 0<Y by omega)
  have hs : (Y:ℝ)^(23/24:ℝ)*(Y:ℝ)^(1/24:ℝ) = Y := by rw [← Real.rpow_add hp]; norm_num
  have hn : 32*‖z‖ ≤ Y := by
    rw [← hs,mul_comm (32:ℝ)]
    exact mul_le_mul hz hY (by norm_num) (by positivity)
  have ht : 3*(Y:ℝ)/32 ≤ ‖T Y m‖ := by
    by_cases hh : patch Y m
    · rw [T,ite_eq_left hh,Complex.norm_real,Real.norm_of_nonneg (by positivity)]; linarith
    · rw [T,ite_eq_right hh]
      exact le_of_not_gt (fun h => hh ⟨he,h⟩)
  have hh := norm_sub_norm_le (T Y m) z
  linarith

private theorem patch_energy (hp : GBSkirtVariance.PaperInput) :
    ∀ᶠ X : ℕ in atTop, WideArcCriterion.energy T X ≤
      2 * WideArcCriterion.energy I X + (badPairCount X:ℝ)*(8*(X:ℝ)^2) := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp (floor_geometry hp)
  filter_upwards [eventually_ge_atTop (4*N)] with X hX
  let e (m Y : ℕ) := ‖I Y m-F Y m‖^2
  let c := 8*(X:ℝ)^2
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have pair (m : ℕ) (hm : m ∈ Icc (X/2) (2*X)) (Y : ℕ) (hy : Y ∈ interiorScales m) :
      ‖T Y m - F Y m‖^2 ≤ 2*e m Y + (if bad Y m then c else 0) := by
    obtain ⟨hl,hh⟩ := mem_Icc.mp hm
    obtain ⟨h1,h2⟩ := mem_Icc.mp hy
    by_cases h : patch Y m
    · have hb := hN Y (by omega) m (by omega) (by omega) h
      rw [ite_eq_left hb]
      have hs : ‖I Y m‖ < 3*(Y:ℝ)/32 := h.2
      have hxy : (Y:ℝ) ≤ 2*(X:ℝ) := by exact_mod_cast (show Y ≤ 2*X by omega)
      have hnorm : ‖T Y m‖ = (Y:ℝ)/8 := by
        rw [T,ite_eq_left h, Complex.norm_real,Real.norm_of_nonneg (by positivity)]
      have hdiff : ‖T Y m-I Y m‖ ≤ 2*(X:ℝ) := by
        have ha := norm_sub_le (T Y m) (I Y m)
        rw [hnorm] at ha
        linarith
      have htri := norm_add_le (T Y m-I Y m) (I Y m-F Y m)
      rw [sub_add_sub_cancel] at htri
      have hsq := pow_le_pow_left₀ (norm_nonneg _) htri 2
      have hD := pow_le_pow_left₀ (norm_nonneg _) hdiff 2
      dsimp [e,c]
      nlinarith only [hsq,hD,sq_nonneg (‖T Y m-I Y m‖ - ‖I Y m-F Y m‖)]
    · rw [T,ite_eq_right h]
      have h0 : 0 ≤ (if bad Y m then c else 0) := by split <;> positivity
      dsimp [e]
      linarith [sq_nonneg ‖I Y m-F Y m‖]
  have row (m : ℕ) (hm : m ∈ Icc (X/2) (2*X)) :
      (∑ Y ∈ interiorScales m, ‖T Y m-F Y m‖^2) ≤ 2*(∑ Y ∈ interiorScales m, e m Y) +
        (((interiorScales m).filter (fun Y => bad Y m)).card:ℝ)*c := by
    refine (sum_le_sum (pair m hm)).trans_eq ?_
    rw [sum_add_distrib, ← mul_sum, ← sum_filter]
    simp
  unfold WideArcCriterion.energy
  refine (sum_le_sum row).trans_eq ?_
  simp only [sum_add_distrib, ← mul_sum, ← sum_mul, badPairCount,Nat.cast_sum]
  rfl

/-- A power-saving count of signed middle-band failures suffices even when the
individual failing Fourier coefficients are arbitrarily negative. -/
theorem frozen_of_principal_discrepancy_count (hp : GBSkirtVariance.PaperInput)
    {α K : ℝ} (hα : α < 4/5) (hK : 0 < K)
    (hc : ∃ N : ℕ, ∀ X ≥ N, (badPairCount X:ℝ) ≤ K*(X:ℝ)^(1+α)) :
    ∃ N : ℕ, ∀ X ≥ N, (missed X).card^5 ≤ X^4 := by
  let β := max α (79/100:ℝ)
  let C := 3*(2:ℝ)^(279/100:ℝ)
  have hC : 0<C := by dsimp [C]; positivity
  have hβ : 0 ≤ β := (by norm_num : (0:ℝ) ≤ 79/100).trans (le_max_right ..)
  have hβ' : β < 4/5 := max_lt hα (by norm_num)
  apply WideArcCriterion.frozen_of_energy patch_floor hβ hβ' (K:=2*C+8*K) (by positivity)
  obtain ⟨NB,hB⟩ := hc
  obtain ⟨NE,hE⟩ := dyadic_actual_fourth _ OuterPrimeArc.outer_measurable OuterPrimeArc.outer_sup_bound
  apply eventually_atTop.mp
  filter_upwards [patch_energy hp,eventually_ge_atTop (max 1 (max NE NB))] with X hpatch hX
  have hpos : 0<(X:ℝ) := by exact_mod_cast (show 0<X by omega)
  have hone : 1≤(X:ℝ) := by exact_mod_cast (show 1≤X by omega)
  have hlow := (multiscale_outer_bessel _ OuterPrimeArc.outer_measurable OuterPrimeArc.outer_subset X).trans (hE X (by omega))
  have h1 : WideArcCriterion.energy I X ≤ C*(X:ℝ)^(3+β) :=
    hlow.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hone
      (add_le_add (le_refl (3:ℝ)) (le_max_right α (79/100:ℝ)))) hC.le)
  have h2 : (badPairCount X:ℝ)*(8*(X:ℝ)^2) ≤ 8*K*(X:ℝ)^(3+β) := by
    calc
      _ ≤ (K*(X:ℝ)^(1+α))*(8*(X:ℝ)^2) :=
        mul_le_mul_of_nonneg_right (hB X (by omega)) (by positivity)
      _ = 8*K*(X:ℝ)^(3+α) := by
        rw [show (3+α:ℝ) = (1+α)+2 by ring,Real.rpow_add hpos (1+α) 2,Real.rpow_ofNat]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hone
        (add_le_add (le_refl (3:ℝ)) (le_max_left α (79/100:ℝ)))) (by positivity)
  linarith only [hpatch,h1,h2]

end
end Goldbach.PrincipalMiddleFloor


namespace Goldbach.JointSignedResidual
open PrincipalMiddleFloor CanonicalDyadicPairs

/-- Both reductions charge exactly the same even frequencies and interior
cutoffs. The equality includes the dyadic endpoints, the strict threshold,
and the model-centering convention. -/
theorem same_actual_pairs (X : ℕ) : badPairCount X = centeredActualBadPairs principal X := by
  classical
  unfold PrincipalMiddleFloor.badPairCount centeredActualBadPairs pairs
  apply Finset.sum_congr rfl
  intro m _
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro Y _
  rfl

/-- The required real-part count now concerns only the correction to the
principal model. All analytic comparison errors are included in the proof. -/
theorem frozen_of_centered_model_pairs {α C : ℝ} (hα : α < 4/5) (hC : 0 < C)
    (h : ∃ N : ℕ, ∀ X ≥ N,
      (centeredModelBadPairs principal X : ℝ) ≤ C * (X : ℝ) ^ (1+α)) :
    ∃ N : ℕ, ∀ X ≥ N, (ShiftWideArc.missed X).card ^ 5 ≤ X ^ 4 := by
  obtain ⟨β,K,hβ,hK,hbound⟩ := centered_actual_power_of_model principal hα hC h
  exact frozen_of_principal_discrepancy_count Conjectures.Goldbach.ShortProgressionsMeanTheta hβ hK (by simpa only [same_actual_pairs] using hbound)

end Goldbach.JointSignedResidual
#print axioms Goldbach.JointSignedResidual.same_actual_pairs
#print axioms Goldbach.JointSignedResidual.frozen_of_centered_model_pairs


open Filter Finset
namespace Goldbach.JointSignedResidual
open PrincipalMiddleFloor CanonicalDyadicPairs MiddleCanonicalModel PrincipalZeroOffset
noncomputable section
open scoped Classical

/-- The coefficient whose lower tail is left to control consists only of
signed correction terms, with the exact k=0 convention built in. -/
theorem model_sub_principal : ∀ᶠ Y : ℕ in atTop, ∀ m : ℕ,
    fieldCoefficient Y m - principal Y m = GB5Variance.modeCoeff (signedRows Y) m := by
  filter_upwards [principal_eq_masked, coefficient_offset_masked] with Y hp hz
  intro m
  rw [hp m]
  exact hz m

def correctionPairs (X : ℕ) := pairs X (fun Y m =>
  (GB5Variance.modeCoeff (signedRows Y) m).re < -(Y:ℝ)/128)

theorem count_eq_correction : ∀ᶠ X : ℕ in atTop,
    centeredModelBadPairs principal X = correctionPairs X := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp model_sub_principal
  filter_upwards [eventually_ge_atTop (4*N)] with X hx
  unfold centeredModelBadPairs correctionPairs pairs
  apply sum_congr rfl
  intro m hm
  apply congrArg Finset.card
  apply filter_congr
  intro Y hy
  obtain ⟨h1,h2⟩ := mem_Icc.mp hm
  obtain ⟨h3,h4⟩ := mem_Icc.mp hy
  change (Even m ∧ (fieldCoefficient Y m - principal Y m).re < -(Y:ℝ)/128) ↔
    (Even m ∧ (GB5Variance.modeCoeff (signedRows Y) m).re < -(Y:ℝ)/128)
  rw [hN Y (by omega) m]

/-- The signed zero-correction row count alone suffices for the exact frozen
binary-shift exception exponent. -/
theorem frozen_of_correction_pairs {α C : ℝ} (hα : α < 4/5) (hC : 0 < C)
    (h : ∃ N : ℕ, ∀ X ≥ N, (correctionPairs X : ℝ) ≤ C*(X:ℝ)^(1+α)) :
    ∃ N : ℕ, ∀ X ≥ N, (ShiftWideArc.missed X).card^5 ≤ X^4 := by
  obtain ⟨N,hN⟩ := h
  apply frozen_of_centered_model_pairs hα hC
  apply eventually_atTop.mp
  filter_upwards [count_eq_correction,eventually_ge_atTop N] with X he hx
  rw [he]
  exact hN X hx

end
end Goldbach.JointSignedResidual
#print axioms Goldbach.JointSignedResidual.frozen_of_correction_pairs
