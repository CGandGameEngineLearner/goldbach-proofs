import MiddleCanonicalModel
import CanonicalPerturbation

open Filter Finset MeasureTheory
namespace Goldbach.CanonicalBandCount
open ShiftWideArc MiddleCanonicalModel CanonicalPerturbation
open GB5Variance (unitMeasure modeCoeff)
noncomputable section
open scoped Classical

def band (Y : ℕ) := {t : ℝ | ∃ q a, bandCenter Y t q a}

private abbrev innerCutoff (Y : ℕ) := min (GB6Growth.grid Y) (⌈(Y:ℝ)^(1/4:ℝ)⌉₊-1)

private theorem mem_innerCutoff {Y q : ℕ} (hq : 0<q) :
    q ≤ innerCutoff Y ↔ q ≤ GB6Growth.grid Y ∧ (q:ℝ) < (Y:ℝ)^(1/4:ℝ) := by
  have hh : q ≤ ⌈(Y:ℝ)^(1/4:ℝ)⌉₊-1 ↔ q < ⌈(Y:ℝ)^(1/4:ℝ)⌉₊ := by omega
  rw [innerCutoff,le_min_iff,hh,Nat.lt_ceil]

/-- Lebesgue measure of the middle arcs inside [0,1]. Each denominator q
supplies at most q+1 windows of length 2H/(qY), including endpoint windows. -/
theorem measure_middle_le {Y : ℕ} (hy : 0 < Y) :
    volume.real (band Y ∩ Set.Icc 0 1) ≤ 4*(H Y:ℝ)*(innerCutoff Y:ℝ)/Y := by
  have hY : (0:ℝ) < Y := by exact_mod_cast hy
  let I := Set.Icc (0:ℝ) 1
  let d (q : ℕ) : ℝ := (H Y:ℝ)/((q:ℝ)*Y)
  let win (q a : ℕ) : Set ℝ := Set.Icc ((a:ℝ)/q - d q) ((a:ℝ)/q + d q) ∩ I
  let row (q : ℕ) := ⋃ a ∈ range (q+1), win q a
  let R := Icc 1 (innerCutoff Y)
  have hw (q a : ℕ) : volume.real (win q a) ≤ 2*d q := by
    have hd : 0 ≤ d q := by dsimp [d]; positivity
    calc
      _ ≤ volume.real (Set.Icc ((a:ℝ)/q - d q) ((a:ℝ)/q + d q)) := measureReal_mono Set.inter_subset_left (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
      _ = _ := by rw [Real.volume_real_Icc_of_le (by linarith)]; ring
  have hr (q : ℕ) (hq : q ∈ R) : volume.real (row q) ≤ 4*(H Y:ℝ)/Y := by
    have hq1 : (1:ℝ) ≤ q := by exact_mod_cast (mem_Icc.mp hq).1
    have hq0 : 0 < (q:ℝ) := by linarith
    calc
      _ ≤ ∑ a ∈ range (q+1), volume.real (win q a) := measureReal_biUnion_finset_le _ _
      _ ≤ ∑ _a ∈ range (q+1), 2*d q := sum_le_sum (fun a _ => hw q a)
      _ = ((q:ℝ)+1)*(2*d q) := by simp
      _ ≤ (2*(q:ℝ))*(2*d q) := mul_le_mul_of_nonneg_right (by linarith) (by dsimp [d]; positivity)
      _ = _ := by dsimp [d]; field_simp; ring
  have hsub : band Y ∩ I ⊆ ⋃ q ∈ R, row q := by
    rintro t ⟨⟨q,a,hq,_,hu,ha,_,hw'⟩,ht⟩
    refine Set.mem_iUnion.mpr ⟨q,Set.mem_iUnion.mpr ⟨mem_Icc.mpr ⟨hq,hu⟩,?_⟩⟩
    refine Set.mem_iUnion.mpr ⟨a,Set.mem_iUnion.mpr ⟨mem_range.mpr (by omega),?_⟩⟩
    obtain ⟨hl,hh⟩ := abs_le.mp hw'
    exact ⟨⟨by dsimp [d]; linarith,by dsimp [d]; linarith⟩,ht⟩
  have hc : (⋃ q ∈ R, row q) ⊆ I := by
    intro t ht
    obtain ⟨q,hq⟩ := Set.mem_iUnion.mp ht
    obtain ⟨_,ha⟩ := Set.mem_iUnion.mp hq
    obtain ⟨a,ha'⟩ := Set.mem_iUnion.mp ha
    obtain ⟨_,hw'⟩ := Set.mem_iUnion.mp ha'
    exact hw'.2
  have hfin : volume (⋃ q ∈ R, row q) ≠ ⊤ :=
    (lt_of_le_of_lt (measure_mono hc) (by dsimp [I]; rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top)).ne
  calc
    _ ≤ volume.real (⋃ q ∈ R,row q) := measureReal_mono hsub hfin
    _ ≤ ∑ q ∈ R, volume.real (row q) := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _q ∈ R, 4*(H Y:ℝ)/Y := sum_le_sum hr
    _ = _ := by simp [R]; ring

/-- Quantitative power saving before the elementary dyadic logarithm is
absorbed. This holds at every positive integer cutoff. -/
theorem measure_middle_power {Y : ℕ} (hy : 0 < Y) :
    volume.real (band Y ∩ Set.Icc 0 1) ≤
      1024*(Nat.log 2 (Y+2):ℝ)^2*(Y:ℝ)^(-(5/12):ℝ) := by
  have hY : 0 < (Y:ℝ) := by exact_mod_cast hy
  have hI : (innerCutoff Y:ℝ) ≤ (Y:ℝ)^(1/4:ℝ) := by
    by_cases hp : 0 < innerCutoff Y
    · exact ((mem_innerCutoff hp).mp (le_refl _)).2.le
    · simp [show innerCutoff Y=0 by omega, Real.rpow_nonneg hY.le]
  have hQ : (Q Y:ℝ) ≤ (Y:ℝ)^(1/3:ℝ) := Nat.floor_le (Real.rpow_nonneg hY.le _)
  calc
    _ ≤ 4*(H Y:ℝ)*(innerCutoff Y:ℝ)/Y := measure_middle_le hy
    _ = 1024*(Nat.log 2 (Y+2):ℝ)^2*((Q Y:ℝ)*(innerCutoff Y:ℝ))/(Y:ℝ) := by simp only [H,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]; ring
    _ ≤ 1024*(Nat.log 2 (Y+2):ℝ)^2*((Y:ℝ)^(1/3:ℝ)*(Y:ℝ)^(1/4:ℝ))/(Y:ℝ) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (mul_le_mul hQ hI (by positivity) (by positivity)) (by positivity)) hY.le
    _ = _ := by
      rw [← Real.rpow_add hY, mul_div_assoc, ← Real.rpow_sub_one hY.ne']
      norm_num

theorem measurable_band (Y : ℕ) : MeasurableSet (band Y) := by
  unfold band MiddleCanonicalModel.bandCenter
  simp only [Set.ofPred_exists]
  apply MeasurableSet.iUnion
  intro q
  apply MeasurableSet.iUnion
  intro a
  by_cases h : 1 ≤ q ∧ (Nat.log 2 (Y+2))^2 < q ∧ q ≤ innerCutoff Y ∧ a ≤ q ∧ a.Coprime q
  · obtain ⟨h1,h2,h3,h4,h5⟩ := h
    have hM : MeasurableSet {t : ℝ | |t-(a:ℝ)/q| ≤ (H Y:ℝ)/((q:ℝ)*Y)} :=
      measurableSet_le (show Continuous (fun t : ℝ => |t-(a:ℝ)/q|) by fun_prop).measurable measurable_const
    convert hM using 1
    ext t
    exact ⟨fun h => h.2.2.2.2.2, fun hw => ⟨h1,h2,h3,h4,h5,hw⟩⟩
  · have he : {t : ℝ | 1 ≤ q ∧ (Nat.log 2 (Y+2))^2 < q ∧ q ≤ innerCutoff Y ∧ a ≤ q ∧ a.Coprime q ∧
        |t-(a:ℝ)/q| ≤ (H Y:ℝ)/((q:ℝ)*Y)} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro t ⟨h1,h2,h3,h4,h5,_⟩
      exact h ⟨h1,h2,h3,h4,h5⟩
    rw [he]; exact MeasurableSet.empty

/-- Form used by the L² perturbation estimate. -/
theorem unit_measure_middle_power {Y : ℕ} (hy : 0 < Y) :
    GB5Variance.unitMeasure.real (band Y) ≤
      1024*(Nat.log 2 (Y+2):ℝ)^2*(Y:ℝ)^(-(5/12):ℝ) := by
  rw [measureReal_restrict_apply (measurable_band Y)]
  apply le_trans _ (measure_middle_power hy)
  exact measureReal_mono (Set.inter_subset_inter_right _ Set.Ioc_subset_Icc_self)
    ((measure_mono Set.inter_subset_right).trans_lt (by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top)).ne

/-- Any measurable approximation at the canonical discrepancy rate has
at most this many large Fourier errors in any finite frequency set. -/
theorem exceptional_at_128 {C : ℝ} (hC : 0 ≤ C) :
    ∀ᶠ Y : ℕ in atTop, ∀ (T : ℝ → ℂ), AEStronglyMeasurable T unitMeasure →
      (∀ t ∈ Set.Icc (0:ℝ) 1 ∩ band Y, ‖S Y t - T t‖ ≤
        C*(Y:ℝ)^(49/64:ℝ)*(GoldbachTwistedMellin.logScale Y)^4) →
      ∀ I : Finset ℕ,
        ((I.filter (fun m => (Y:ℝ)/128 ≤ ‖modeCoeff (masked (band Y) (S Y) T) m‖)).card:ℝ)
          ≤ (18*128^2:ℝ)*(Y:ℝ)^(2/3:ℝ) := by
  let D (Y : ℕ) := C*(Y:ℝ)^(49/64:ℝ)*(GoldbachTwistedMellin.logScale Y)^4
  have hD : ∀ᶠ Y : ℕ in atTop, 0 ≤ D Y ∧ D Y ≤ (C*(GB6Growth.logFactor Y)^4)*(Y:ℝ)^(49/64:ℝ) := by
    filter_upwards [eventually_ge_atTop (1:ℕ)] with Y hY
    have hL : 0 ≤ GoldbachTwistedMellin.logScale Y := zero_le_one.trans (GoldbachTwistedMellin.logScale_one (by exact_mod_cast hY))
    have hscale := pow_le_pow_left₀ hL (logScale_le_logFactor hY) 4
    constructor
    · dsimp [D]; positivity
    · dsimp [D]
      calc
        _ ≤ C*(Y:ℝ)^(49/64:ℝ)*(GB6Growth.logFactor Y)^4 := mul_le_mul_of_nonneg_left hscale (by positivity)
        _ = _ := by ring
  have hV : ∀ᶠ Y : ℕ in atTop, volume.real (band Y ∩ Set.Icc 0 1) ≤
      1024*(Nat.log 2 (Y+2):ℝ)^2*(Y:ℝ)^(-(5/12):ℝ) := by
    filter_upwards [eventually_ge_atTop (1:ℕ)] with Y hy
    exact measure_middle_power hy
  have hB := budget_at_49_64 measurable_band hC 4 hD hV
  filter_upwards [hB,hD,eventually_ge_atTop (1:ℕ)] with Y hb hd hY
  intro T ht hp I
  have hy : 0 < (Y:ℝ) := by exact_mod_cast hY
  have he := exceptional_frequencies (band Y) (measurable_band Y) (S Y) T
    (GB6Var.S_memLp Y) ht hd.1 hp I (by positivity : 0 ≤ (Y:ℝ)/128)
  apply le_of_mul_le_mul_right (a:=(Y:ℝ)^2) _ (by positivity)
  have hpow : (Y:ℝ)^(8/3:ℝ) = (Y:ℝ)^(2/3:ℝ)*(Y:ℝ)^2 := by
    rw [show (8/3:ℝ) = 2/3+2 by norm_num,Real.rpow_add hy,Real.rpow_ofNat]
  have h := he.trans hb
  rw [hpow] at h
  linarith only [h]
end
end Goldbach.CanonicalBandCount
