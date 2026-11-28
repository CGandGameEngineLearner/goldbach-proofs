import ShiftSignedCommonLowBase
import ShiftIntermediateReduction
import Conjectures.Goldbach.ShortProgressionsMeanTheta
import ActualCanonicalCount

/- Research module LowWideFromShortAP -/

/- The common-window variance estimate and its reduction to short progressions
are adapted from the verified LowSkirtFromShortProgressions module and the
uniform-in-frequency extension. Taking the excision parameter to be zero
keeps the full low-denominator windows, including their centers. -/
open Finset MeasureTheory Filter
open scoped Interval Topology Classical
namespace Goldbach.FullLowWide
noncomputable section
open GoldbachGRHBudget (narrow width)
open GoldbachGRHArcs (cap centers cell radius)
open GoldbachGRHModel (model model_continuous)
open GoldbachFourthMoment (phase primeSum)
open GoldbachWindow (poly)
open GoldbachGRHAnalytic (errorCoeff)
open GBSkirtVariance
theorem full_common_window (n Q H h : ℕ) (hn : 0<n) (hh : 0<h) (hw : 6*h*H ≤ n) :
    (h:ℝ)^2 * (∑ i ∈ centers Q, cellError n 0 H i) ≤ 8*variance n Q h := by
  rw [GoldbachGRHArcs.sum_centers_eq, Finset.mul_sum,variance,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro q hq
  have hpos := (mem_Icc.mp hq).1
  have hqn : q ≠ 0 := by omega
  letI : NeZero q := ⟨hqn⟩
  let δ := radius n H q
  let E (a : ZMod q) := ∫ t in (-δ)..δ, ‖poly (n+1) (errorCoeff a) t‖^2
  have hd : 0 ≤ δ := by dsimp [δ,radius]; positivity
  have hnR : 0<(n:ℝ) := by exact_mod_cast hn
  have hqR : (1:ℝ)≤q := by exact_mod_cast hpos
  have hwidth : 6*(h:ℝ)*δ ≤ 1 := by
    dsimp [δ,radius]
    rw [← mul_div_assoc,div_le_iff₀ (by positivity : 0<(q:ℝ)*(n:ℝ)),one_mul]
    exact (by exact_mod_cast hw : 6*(h:ℝ)*H≤n).trans (by nlinarith only [mul_le_mul_of_nonneg_right hqR hnR.le])
  have hE (a : ZMod q) : 0 ≤ E a :=
    intervalIntegral.integral_nonneg (by linarith) (fun _ _ => by positivity)
  have hcells : (∑ a ∈ (range (q+1)).filter (fun a => a.Coprime q), cellError n 0 H (q,a)) ≤
      2*∑ a : ZMod q, E a :=
    (sum_le_sum (fun a ha => cell_to_poly n 0 H a (mem_filter.mp ha).2)).trans
      (GoldbachGRHArcs.sum_numerators_le_real q E hE)
  have hden := denominator_bound (q:=q) n h δ hh hd hwidth
  change (h:ℝ)^2/4 * (∑ a : ZMod q, E a) ≤ _ at hden
  rw [mass,dite_eq_right hqn]
  linarith only [mul_le_mul_of_nonneg_left hcells (sq_nonneg (h:ℝ)),hden]

def summand (Y m : ℕ) (t : ℝ) : ℂ := (primeSum Y t)^2 * phase (-(m:ℝ)*t)

def actualCoeff (Y m : ℕ) : ℂ :=
  ∫ t in (0:ℝ)..1, (cap Y (narrow Y) (width Y) \ cap Y 0 0).indicator
    (summand Y m) t

def modelCoeff (Y m : ℕ) : ℂ :=
  ∑ i ∈ centers (narrow Y), ∫ t in cell Y 0 (width Y) i,
    model Y i t ^ 2 * phase (-(m:ℝ)*t)

set_option maxHeartbeats 1200000 in
theorem signed_error_bound (m : ℕ) {n : ℕ} (hn : 2 ≤ n) (_hQH : narrow n ≤ width n)
    (hbudgetLow : 2 * width n * narrow n < n) {η : ℝ} (hη : 0 < η) :
    ‖actualCoeff n m - modelCoeff n m‖ ≤ (1+1/η)*(∑ i ∈ centers (narrow n),
      cellError n 0 (width n) i) + η*(((n:ℝ)+1)*(Real.log (n:ℝ))^2) := by
  let osc (t : ℝ) := phase (-(m:ℝ)*t)
  have hOsc : Continuous osc := by unfold osc phase; fun_prop
  have hS : Continuous (primeSum n) := by unfold primeSum phase; fun_prop
  have hF : Continuous (summand n m) := (hS.pow 2).mul hOsc
  rw [actualCoeff, GoldbachGRHArcs.integrate_difference_eq_sum (Nat.zero_le _) (Nat.zero_le _) hbudgetLow _ hF,
    modelCoeff, ← Finset.sum_sub_distrib]
  have hsplit (i : ℕ × ℕ) :
      (∫ t in cell n 0 (width n) i, summand n m t) -
        (∫ t in cell n 0 (width n) i, model n i t ^ 2 * osc t) =
      ∫ t in cell n 0 (width n) i,
        (primeSum n t ^ 2 - model n i t ^ 2) * osc t := by
    have hpart : cell n 0 (width n) i ⊆ Set.Ioc (0:ℝ) 1 :=
      Set.inter_subset_right
    have h₁ : IntegrableOn (summand n m) (cell n 0 (width n) i) volume :=
      (hF.intervalIntegrable 0 1).1.mono_set hpart
    have hm : Continuous (fun t => model n i t ^ 2 * osc t) :=
      ((model_continuous n i).pow 2).mul hOsc
    have h₂ : IntegrableOn (fun t => model n i t ^ 2 * osc t)
        (cell n 0 (width n) i) volume :=
      (hm.intervalIntegrable 0 1).1.mono_set hpart
    rw [← integral_sub h₁ h₂]
    simp [summand, osc, sub_mul]
  dsimp only [osc] at hsplit
  simp_rw [hsplit]
  apply (norm_sum_le _ _).trans
  apply (GoldbachGRHWindowEnergy.sum_setIntegral_square_difference_le
    (centers (narrow n)) (cell n 0 (width n))
    (fun i _ => GoldbachGRHArcs.measurable_cell _ _ _ i)
    (fun _ _ => Set.inter_subset_right) (GoldbachGRHArcs.cell_disjoint hbudgetLow)
    (primeSum n) (model n) osc hS (fun i _ => model_continuous n i) hOsc
    (fun t => le_of_eq (Complex.norm_exp_ofReal_mul_I (2 * Real.pi * (-(m:ℝ)*t)))) hη).trans
  exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_left (GoldbachGRHAnalytic.prime_sum_energy_le n hn) hη.le)

theorem eventual_error_uniform_of_short_ap (hp : GBSkirtVariance.PaperInput) (ε : ℝ) (he : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ m : ℕ, ‖actualCoeff n m - modelCoeff n m‖ ≤ ε*(n:ℝ) := by
  have hv := variance_of_full_average (full_average_of_dyadic (integer_of_paper hp))
  have ht : Tendsto (fun n : ℕ => Real.log (n:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [GoldbachGRHBudget.eventual_geometry, length_ok, hv,
    ht.eventually (eventually_ge_atTop (max 1 (18/ε)))] with n hg hl hvn hL
  intro m
  obtain ⟨hn,hQ,hQU,_,_,hbudget⟩ := hg
  let L := Real.log (n:ℝ)
  have hL1 : 1 ≤ L := (le_max_left _ _).trans hL
  have hLe : 18/ε ≤ L := (le_max_right _ _).trans hL
  have hL0 : 0<L := by linarith
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hh : 0 < (length n:ℝ) := by exact_mod_cast hl.1
  have hQH := hQU.trans (GoldbachGRHBudget.width_ge_cutoff n hQ)
  have hbud := (Nat.mul_le_mul_left (2 * width n) hQU).trans_lt hbudget
  let D := ∑ i ∈ centers (narrow n), cellError n 0 (width n) i
  have hD : D ≤ 8*(n:ℝ)/L^8 := by
    have hC := full_common_window n (narrow n) (width n) (length n) (by omega) hl.1 hl.2
    have h₁ := hC.trans (mul_le_mul_of_nonneg_left hvn (by norm_num : (0:ℝ)≤8))
    change (length n:ℝ)^2 * D ≤ 8*((n:ℝ)*(length n:ℝ)^2/L^8) at h₁
    apply le_of_mul_le_mul_left (a:=(length n:ℝ)^2) _ (by positivity)
    linarith only [show (length n:ℝ)^2 * D ≤ (length n:ℝ)^2 * (8*(n:ℝ)/L^8) from h₁.trans_eq (by ring)]
  have hη : 0<1/L^3 := by positivity
  have hS := signed_error_bound m hn hQH hbud hη
  change ‖_‖ ≤ (1+1/(1/L^3))*D + (1/L^3)*(((n:ℝ)+1)*L^2) at hS
  calc
    _ ≤ _ := hS
    _ ≤ (1+1/(1/L^3))*(8*(n:ℝ)/L^8) + (1/L^3)*((n+1:ℝ)*L^2) := by
      gcongr
    _ ≤ 18*(n:ℝ)/L := by
      have hpow3 : 1≤L^3 := one_le_pow₀ hL1
      have hpow4 : 1≤L^4 := one_le_pow₀ hL1
      have hp : L^3≤L^7 := by
        calc
          _ = L^3*1 := by ring
          _ ≤ L^3*L^4 := by gcongr
          _ = _ := by ring
      have ha : (1+L^3)*(8*(n:ℝ)) ≤ (16*(n:ℝ))*L^7 := by
        nlinarith only [mul_le_mul_of_nonneg_right hpow3 (by positivity : 0≤(n:ℝ)),
          mul_le_mul_of_nonneg_right hp (by positivity : 0≤(n:ℝ))]
      have hb : (1+1/(1/L^3))*(8*(n:ℝ)/L^8) ≤ 16*(n:ℝ)/L := by
        rw [one_div_one_div, ← mul_div_assoc, div_le_div_iff₀ (by positivity) hL0]
        convert mul_le_mul_of_nonneg_right ha hL0.le using 1 <;> ring
      have hc : (1/L^3)*((n+1:ℝ)*L^2) ≤ 2*(n:ℝ)/L := by
        have heq : (1/L^3)*((n+1:ℝ)*L^2) = ((n:ℝ)+1)/L := by field_simp <;> ring
        rw [heq]
        gcongr
        linarith
      exact (add_le_add hb hc).trans_eq (by ring)
    _ ≤ _ := by
      apply (div_le_iff₀ hL0).2
      have hε := (div_le_iff₀ he).1 hLe
      nlinarith only [mul_le_mul_of_nonneg_right hε (by positivity : 0≤(n:ℝ))]

private theorem cap_zero (Y : ℕ) : cap Y 0 0 = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro t ⟨q,a,hq,hq',_⟩
  omega

private theorem sigma_mem (r : ℕ) (q a : ℕ) :
    (⟨q,a⟩ : GB6Geometry.Idx) ∈ GB6Geometry.indices r ↔ (q,a) ∈ centers r := by
  rw [GoldbachGRHArcs.mem_centers]
  change _ ↔ 1≤q ∧ q≤r ∧ a≤q ∧ a.Coprime q
  simp only [GB6Geometry.indices,mem_sigma,mem_Icc,GB6Geometry.numerators,mem_filter,mem_range] <;> omega

private theorem window_eq (H Y q a : ℕ) : GB6Geometry.window H Y q a = GoldbachGRHArcs.arc Y H (q,a) := by
  rw [GoldbachGRHArcs.arc_eq_Icc]; rfl

private theorem localModel_eq (Y q a : ℕ) (hc : a.Coprime q) (t : ℝ) :
    ThreeQArith.mean q a * GB6Kernel.kernel Y (t - GB6Geometry.center q a) = model Y (q,a) t := by
  unfold GoldbachGRHModel.model
  rw [ThreeQArith.mean_eq_ram hc, GoldbachGRHKernel.kernel_eq_sum]
  have hr : ThreeQArith.ram q 1 = (ArithmeticFunction.moebius q : ℂ) :=
    BinaryShiftLocalGoldbachExplicitModeledMajor.ram_one_eq_moebius q
  rw [hr]; rfl

set_option maxHeartbeats 2000000 in
/-- Identify the clipped, Möbius-weighted collection of arcs with the rational
model on the whole low family, retaining both endpoint halves. -/
theorem model_assembly {Y : ℕ} (m : ℕ) (hs : 2*(width Y)^2 < Y) (hDH : narrow Y ≤ width Y)
    (hH : GB6Growth.height Y = width Y) :
    ReflectedArcModel.truncatedCoefficient (narrow Y) Y m = modelCoeff Y m := by
  let D := narrow Y
  let H := width Y
  let piece (i : ℕ × ℕ) := (GoldbachGRHArcs.arc Y H i).indicator
    (fun t => model Y i t ^ 2 * phase (-(m:ℝ)*t))
  have pc (i : ℕ × ℕ) : Continuous (fun t => model Y i t ^ 2 * phase (-(m:ℝ)*t)) :=
    ((model_continuous Y i).pow 2).mul (by unfold phase; fun_prop)
  have hi (i : ℕ × ℕ) : IntervalIntegrable (piece i) volume 0 1 :=
    ⟨((pc i).intervalIntegrable 0 1).1.indicator (GoldbachGRHArcs.measurable_arc ..),
      ((pc i).intervalIntegrable 0 1).2.indicator (GoldbachGRHArcs.measurable_arc ..)⟩
  have hp (t : ℝ) : (GB6Geometry.model D H Y ThreeQArith.mean t)^2 * GB6Kernel.phase (-(m:ℝ)*t) =
      ∑ i ∈ centers D, piece i t := by
    rw [GB6Geometry.model_sigma]
    by_cases hh : ∃ i ∈ centers D, t ∈ GoldbachGRHArcs.arc Y H i
    · obtain ⟨⟨q,a⟩,hiC,ht⟩ := hh
      have hii := (sigma_mem D q a).mpr hiC
      have hit : t ∈ GB6Geometry.window H Y q a := (window_eq ..).symm ▸ ht
      have hu := GB6Geometry.unique_window hs hDH t
      have hn (j : GB6Geometry.Idx) (hj : j∈GB6Geometry.indices D) (hji : j≠⟨q,a⟩) :
          t ∉ GB6Geometry.window H Y j.1 j.2 := fun hw => hji (hu ⟨hj,hw⟩ ⟨hii,hit⟩)
      have hn' (i : ℕ × ℕ) (hc : i ∈ centers D) (hne : i≠(q,a)) : t ∉ GoldbachGRHArcs.arc Y H i := by
        rcases i with ⟨r,b⟩
        intro hw
        apply hn ⟨r,b⟩ ((sigma_mem ..).mpr hc) (fun he => hne (by cases he; rfl))
        rwa [window_eq]
      rw [sum_eq_single_of_mem _ hii (fun j hj hne => Set.indicator_of_notMem (hn j hj hne) _),
        sum_eq_single_of_mem _ hiC (fun j hj hne => Set.indicator_of_notMem (hn' j hj hne) _)]
      simp only [Set.indicator_of_mem hit,piece,Set.indicator_of_mem ht]
      rw [localModel_eq Y q a (GoldbachGRHArcs.mem_centers.mp hiC).2.2.2] <;> rfl
    · have hn (r a : ℕ) (hiC : (r,a) ∈ centers D) : t ∉ GoldbachGRHArcs.arc Y H (r,a) :=
        fun hr => hh ⟨(r,a),hiC,hr⟩
      have hz (i : GB6Geometry.Idx) (hiC : i∈GB6Geometry.indices D) : t ∉ GB6Geometry.window H Y i.1 i.2 := by
        rcases i with ⟨r,a⟩
        rw [window_eq]; exact hn r a ((sigma_mem D r a).mp hiC)
      rw [sum_eq_zero (fun i hiC => Set.indicator_of_notMem (hz i hiC) _),
        sum_eq_zero (fun i hiC => Set.indicator_of_notMem (fun ht => hh ⟨i,hiC,ht⟩) _)]
      simp
  unfold ReflectedArcModel.truncatedCoefficient modelCoeff
  rw [hH]
  change (∫ t in (0:ℝ)..1, (GB6Geometry.model D H Y ThreeQArith.mean t)^2 * GB6Kernel.phase (-(m:ℝ)*t)) = _
  simp_rw [hp]
  rw [intervalIntegral.integral_finsetSum (fun i _ => hi i)]
  apply sum_congr rfl
  intro i hc
  have hpos := (GoldbachGRHArcs.mem_centers.mp hc).1
  have hc' : cell Y 0 H i = GoldbachGRHArcs.arc Y H i ∩ Set.Ioc 0 1 := by
    simp [GoldbachGRHArcs.cell,show ¬ i.1≤0 by omega]
  rw [hc',intervalIntegral.integral_of_le zero_le_one,Set.inter_comm]
  exact setIntegral_indicator (GoldbachGRHArcs.measurable_arc ..)

theorem actual_low_wide_floor_of_short_ap (hp : GBSkirtVariance.PaperInput) : ∀ᶠ Y : ℕ in atTop,
    ∀ m : ℕ, Y ≤ m → 2*m ≤ 3*Y → Even m →
      (7:ℝ)*Y/64 ≤ (ShiftWideArc.coefficient (cap Y (narrow Y) (width Y)) Y m).re := by
  obtain ⟨N,hN⟩ := ReflectedArcModel.uniform_truncated_model_floor
  filter_upwards [eventual_error_uniform_of_short_ap hp (1/64) (by norm_num), GB6Growth.eventual_geometry,
    GoldbachGRHBudget.eventual_geometry, eventually_ge_atTop N] with Y her hg hgeo hy
  intro m hlo hhi he
  obtain ⟨_,hD,hDQ,_,_,_⟩ := hgeo
  obtain ⟨_,hQH,_,_,hsep⟩ := hg
  have hQ : GB6Growth.grid Y = GoldbachGRHBudget.cutoff Y := GB6Growth.grid_eq_floor Y
  have hH : GB6Growth.height Y = width Y := by simp only [GB6Growth.height,width,hQ,GoldbachGRHBudget.narrow]
  have hl := hN Y hy (narrow Y) hD (hDQ.trans_eq hQ.symm) m hlo hhi he
  have hDH : narrow Y ≤ width Y := hDQ.trans (by simpa only [hQ,hH] using hQH)
  rw [model_assembly m (by simpa only [hH] using hsep) hDH hH] at hl
  have ha := (Complex.abs_re_le_norm (actualCoeff Y m - modelCoeff Y m)).trans (her m)
  rw [Complex.sub_re] at ha
  have ha' : actualCoeff Y m = ShiftWideArc.coefficient (cap Y (narrow Y) (width Y)) Y m := by
    simp only [actualCoeff,cap_zero,Set.diff_empty] <;> rfl
  rw [ha'] at ha
  linarith [(abs_le.mp ha).1]
end
end Goldbach.FullLowWide

section
open Filter Finset MeasureTheory GB6Growth
namespace Goldbach.LowWideMiddleBand
open ShiftWideArc InnerArcCriterion ReflectedArcModel
noncomputable section
open scoped Classical

/-- The whole wide principal-arc family for small denominators. -/
def low (Y : ℕ) := GoldbachGRHArcs.cap Y (GoldbachGRHBudget.narrow Y) (GoldbachGRHBudget.width Y)

def middle (Y : ℕ) := inner OuterPrimeArc.outer Y \ low Y

/-- Each rational center in this family has denominator strictly between
logarithm squared and the real fourth root, with the original wide radius. -/
def denominatorBand (Y : ℕ) : Set ℝ := {t | ∃ q a : ℕ,
  1 ≤ q ∧ GoldbachGRHBudget.narrow Y < q ∧ q ≤ innerCutoff Y ∧ a ≤ q ∧ a.Coprime q ∧
    |t-(a:ℝ)/q| ≤ (H Y:ℝ)/((q:ℝ)*Y)}

private theorem eventual_low_denominator : ∀ᶠ Y : ℕ in atTop,
    GoldbachGRHBudget.narrow Y ≤ innerCutoff Y := by
  filter_upwards [GB6Growth.polylog_le_power 2 (by norm_num) 2 (1/4) (by norm_num),
    GoldbachGRHBudget.eventual_geometry] with Y h hg
  have hL := L_le_logFactor Y
  have hL0 : 0 ≤ L Y := (L_one Y).trans' zero_le_one
  have hsq : (GoldbachGRHBudget.narrow Y:ℝ) ≤ (logFactor Y)^2 := by
    change (((Nat.log 2 (Y+2))^2:ℕ):ℝ) ≤ _
    push_cast
    exact pow_le_pow_left₀ hL0 hL _
  have hp : 0 < (GoldbachGRHBudget.narrow Y:ℝ) := by exact_mod_cast hg.2.1
  apply (mem_innerCutoff hg.2.1).mpr
  refine ⟨hg.2.2.1.trans_eq (grid_eq_floor Y).symm,?_⟩
  linarith

theorem eventual_low_subset : ∀ᶠ Y : ℕ in atTop, low Y ⊆ inner OuterPrimeArc.outer Y := by
  filter_upwards [InnerArcGeometry.eventual_inner_eq,eventual_low_denominator] with Y he hd
  change low Y ⊆ ShiftWideArc.arcs Y \ OuterPrimeArc.outer Y
  rw [he]
  rintro t ⟨q,a,hq,hlo,ha,hc,ht⟩
  exact ⟨q,a,hq,hlo.trans hd,ha,hc,ht⟩

theorem eventual_middle_eq_band : ∀ᶠ Y : ℕ in atTop, middle Y = denominatorBand Y := by
  filter_upwards [InnerArcGeometry.eventual_inner_eq,GoldbachGRHBudget.eventual_geometry] with Y he hgeo
  have hD := hgeo.2.2.1
  have hU : innerCutoff Y ≤ GoldbachGRHBudget.cutoff Y := (min_le_left ..).trans_eq (grid_eq_floor Y)
  change (ShiftWideArc.arcs Y \ OuterPrimeArc.outer Y) \ low Y = denominatorBand Y
  rw [he]
  ext t
  constructor
  · rintro ⟨⟨q,a,hl,hq,ha,hc,ht⟩,hout⟩
    have hg : GoldbachGRHBudget.narrow Y < q := by
      by_contra! hh
      exact hout ⟨q,a,hl,hh,ha,hc,ht⟩
    exact ⟨q,a,hl,hg,hq,ha,hc,ht⟩
  · rintro ⟨q,a,hl,hg,hq,ha,hc,ht⟩
    refine ⟨⟨q,a,hl,hq,ha,hc,ht⟩,?_⟩
    rintro ⟨r,b,hr,hrD,hb,hbc,ht'⟩
    have hi := (GoldbachGRHArcs.mem_centers (i := (q,a)) (U:=GoldbachGRHBudget.cutoff Y)).mpr ⟨hl,hq.trans hU,ha,hc⟩
    have hj := (GoldbachGRHArcs.mem_centers (i := (r,b)) (U:=GoldbachGRHBudget.cutoff Y)).mpr ⟨hr,hrD.trans hD,hb,hbc⟩
    have eq := GoldbachGRHArcs.common_arc_unique hgeo.2.2.2.2.2 hi hj (t:=t) ht ht'
    have e : q = r := congrArg Prod.fst eq
    omega

private theorem coefficient_split {Y : ℕ} (hs : low Y ⊆ inner OuterPrimeArc.outer Y) (m : ℕ) :
    coefficient (inner OuterPrimeArc.outer Y) Y m = coefficient (middle Y) Y m + coefficient (low Y) Y m := by
  have ha : MeasurableSet (ShiftWideArc.arcs Y) := EffectiveArcEndpoint.frontierMeasurable _ _ _
  have hi : MeasurableSet (inner OuterPrimeArc.outer Y) := ha.diff (OuterPrimeArc.outer_measurable Y)
  have hl : MeasurableSet (low Y) := GoldbachGRHArcs.measurable_cap ..
  have hc : Continuous (integrand Y m) := by unfold integrand S ShiftWideArc.phase; fun_prop
  have hm (D : Set ℝ) (hD : MeasurableSet D) : IntervalIntegrable (D.indicator (integrand Y m)) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr ((hc.intervalIntegrable (μ:=volume) 0 1).1.indicator hD)
  unfold coefficient
  rw [← intervalIntegral.integral_add (hm (middle Y) (hi.diff hl)) (hm _ hl)]
  apply intervalIntegral.integral_congr
  intro t _
  by_cases ht : t ∈ low Y
  · simp [middle,ht,hs ht]
  · by_cases hi' : t ∈ inner OuterPrimeArc.outer Y <;> simp [middle,ht,hi']

theorem frozen_of_middle_band_floor_of_short_ap (hp : GBSkirtVariance.PaperInput)
    (h : ∃ N : ℕ, ∀ Y ≥ N, ∀ m : ℕ, Y ≤ m → 2*m ≤ 3*Y → Even m →
      -(Y:ℝ)/64 ≤ (coefficient (denominatorBand Y) Y m).re) :
    ∃ N : ℕ, ∀ X ≥ N, (missed X).card^5 ≤ X^4 := by
  obtain ⟨N,hN⟩ := h
  apply frozen_of_actual_inner_floor
  apply eventually_atTop.mp
  filter_upwards [eventual_low_subset,eventual_middle_eq_band,FullLowWide.actual_low_wide_floor_of_short_ap hp,
    eventually_ge_atTop N] with Y hs hb hlow hy
  intro m h1 h2 he
  rw [coefficient_split hs m,hb,Complex.add_re]
  have hf : 7*(Y:ℝ)/64 ≤ (coefficient (low Y) Y m).re := hlow m h1 h2 he
  linarith [hN Y hy m h1 h2 he]

end
end Goldbach.LowWideMiddleBand

end

/- Research module MiddlePairCount -/

open Filter Finset MeasureTheory
namespace Goldbach.MiddlePairCount
open ShiftWideArc InnerArcCriterion LowWideMiddleBand
noncomputable section
open scoped Classical

private abbrev I (Y m : ℕ) := coefficient (inner OuterPrimeArc.outer Y) Y m
private abbrev F (Y m : ℕ) := coefficient (arcs Y) Y m

/-- Count failing pairs (Y,m) with m even and Y an interior scale for m. -/
def bad (Y m : ℕ) : Prop := Even m ∧ (coefficient (denominatorBand Y) Y m).re < -(Y:ℝ)/64

def badPairCount (X : ℕ) : ℕ :=
  ∑ m ∈ Icc (X/2) (2*X), ((interiorScales m).filter (fun Y => bad Y m)).card

private def patch (Y m : ℕ) := Even m ∧ ‖I Y m‖ < 3*(Y:ℝ)/32
private def T (Y m : ℕ) : ℂ := if patch Y m then (((Y:ℝ)/8:ℝ):ℂ) else I Y m

private theorem floor_geometry (hp : GBSkirtVariance.PaperInput) :
    ∀ᶠ Y : ℕ in atTop, ∀ m : ℕ, Y ≤ m → 2*m ≤ 3*Y → patch Y m → bad Y m := by
  filter_upwards [eventual_low_subset,eventual_middle_eq_band,
      FullLowWide.actual_low_wide_floor_of_short_ap hp] with Y hs hb hlow
  intro m h1 h2 h
  obtain ⟨he,hsml⟩ := h
  refine ⟨he,?_⟩
  have hl : 7*(Y:ℝ)/64 ≤ (coefficient (low Y) Y m).re := hlow m h1 h2 he
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
  linarith

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
theorem frozen_of_middle_bad_pair_count (hp : GBSkirtVariance.PaperInput)
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
end Goldbach.MiddlePairCount

/- Research module FullLowWideAccepted -/

open Filter GoldbachGRHArcs GoldbachGRHBudget
namespace Goldbach.FullLowWide

theorem actual_low_wide_floor : ∀ᶠ Y : ℕ in atTop,
    ∀ m : ℕ, Y ≤ m → 2*m ≤ 3*Y → Even m →
      (7:ℝ)*Y/64 ≤ (ShiftWideArc.coefficient (cap Y (narrow Y) (width Y)) Y m).re :=
  actual_low_wide_floor_of_short_ap Conjectures.Goldbach.ShortProgressionsMeanTheta

end Goldbach.FullLowWide

namespace Goldbach.LowWideMiddleBand
open ShiftWideArc
theorem frozen_of_middle_band_floor
    (h : ∃ N : ℕ, ∀ Y ≥ N, ∀ m : ℕ, Y ≤ m → 2*m ≤ 3*Y → Even m →
      -(Y:ℝ)/64 ≤ (coefficient (denominatorBand Y) Y m).re) :
    ∃ N : ℕ, ∀ X ≥ N, (missed X).card^5 ≤ X^4 :=
  frozen_of_middle_band_floor_of_short_ap Conjectures.Goldbach.ShortProgressionsMeanTheta h
end Goldbach.LowWideMiddleBand

#print axioms Goldbach.FullLowWide.actual_low_wide_floor
#print axioms Goldbach.LowWideMiddleBand.frozen_of_middle_band_floor

/- Research module MiddlePairAccepted -/

namespace Goldbach.MiddlePairCount

/-- It suffices to bound the number of interior scale-frequency pairs at which
    the intermediate-denominator Fourier coefficient has a large negative real part. -/
theorem frozen_of_bad_pair_count {α K : ℝ} (hα : α < 4/5) (hK : 0 < K)
    (h : ∃ N : ℕ, ∀ X ≥ N, (badPairCount X : ℝ) ≤ K * (X : ℝ) ^ (1+α)) :
    ∃ N : ℕ, ∀ X ≥ N, (ShiftWideArc.missed X).card ^ 5 ≤ X ^ 4 :=
  frozen_of_middle_bad_pair_count Conjectures.Goldbach.ShortProgressionsMeanTheta hα hK h

end Goldbach.MiddlePairCount

#print axioms Goldbach.MiddlePairCount.frozen_of_bad_pair_count

