import Mathlib
import Conjectures.Goldbach.LowSkirtFromShortProgressions
import Conjectures.Goldbach.ShortProgressionsMeanTheta

open Filter Finset MeasureTheory
open scoped Topology Interval BigOperators Classical

namespace Conjectures.Cuts.Task6af0a69f44e255854c404689_aux
open GoldbachGRHBudget (narrow cutoff width)
open GoldbachGRHArcs (cap cell centers arc radius center)

noncomputable def Ccap (n : ℕ) : ℕ := min (cutoff n) ((narrow n) ^ 2)

theorem narrow_le_Ccap (n : ℕ) (hQ : 1 ≤ narrow n) (hQU : narrow n ≤ cutoff n) :
    narrow n ≤ Ccap n := le_min hQU (by nlinarith)

noncomputable def bandIdx (n : ℕ) : Finset (ℕ × ℕ) :=
  (centers (Ccap n)).filter (fun i => narrow n < i.1)

theorem bandIdx_subset (n : ℕ) : bandIdx n ⊆ centers (Ccap n) :=
  Finset.filter_subset _ _

theorem mem_bandIdx {n : ℕ} {i : ℕ × ℕ} (hi : i ∈ bandIdx n) :
    i ∈ centers (Ccap n) ∧ narrow n < i.1 := Finset.mem_filter.mp hi

theorem cell_of_band {n : ℕ} {i : ℕ × ℕ} (hi : i ∈ bandIdx n) :
    cell n (narrow n) (width n) i = arc n (width n) i ∩ Set.Ioc 0 1 := by
  unfold cell
  rw [ite_eq_right (not_le.mpr (mem_bandIdx hi).2), Set.sdiff_empty]

theorem band_disjoint {n : ℕ} (hbudget : 2 * width n * Ccap n < n) :
    (↑(bandIdx n) : Set (ℕ × ℕ)).PairwiseDisjoint (cell n (narrow n) (width n)) := by
  intro i hi j hj hij
  exact GoldbachGRHArcs.cell_disjoint hbudget (mem_bandIdx (Finset.mem_coe.mp hi)).1
    (mem_bandIdx (Finset.mem_coe.mp hj)).1 hij

theorem band_cells_eq {n : ℕ} (hQ : narrow n ≤ Ccap n) (hbudget : 2 * width n * Ccap n < n) :
    (⋃ i ∈ bandIdx n, cell n (narrow n) (width n) i) =
      (cap n (Ccap n) (width n) \ cap n (narrow n) (width n)) ∩ Set.Ioc 0 1 := by
  ext t
  simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_sdiff]
  constructor
  · rintro ⟨i, hi, ht⟩
    have hcell := cell_of_band hi
    rw [hcell] at ht
    refine ⟨⟨GoldbachGRHArcs.mem_cap.mpr ⟨i, (mem_bandIdx hi).1, ht.1⟩, ?_⟩, ht.2⟩
    intro hN
    obtain ⟨j, hj, htj⟩ := GoldbachGRHArcs.mem_cap.mp hN
    have hjC : j ∈ centers (Ccap n) := GoldbachGRHArcs.centers_mono hQ hj
    have hjQ : j.1 ≤ narrow n := (GoldbachGRHArcs.mem_centers.mp hj).2.1
    have he := GoldbachGRHArcs.common_arc_unique hbudget (mem_bandIdx hi).1 hjC ht.1 htj
    subst j
    exact absurd hjQ (not_le.mpr (mem_bandIdx hi).2)
  · rintro ⟨⟨ht, hnot⟩, hunit⟩
    obtain ⟨i, hi, hti⟩ := GoldbachGRHArcs.mem_cap.mp ht
    have hgt : narrow n < i.1 := by
      by_contra hle
      apply hnot
      exact GoldbachGRHArcs.mem_cap.mpr ⟨i, GoldbachGRHArcs.mem_centers.mpr
        ⟨(GoldbachGRHArcs.mem_centers.mp hi).1, Nat.le_of_not_lt hle,
         (GoldbachGRHArcs.mem_centers.mp hi).2.2.1,
         (GoldbachGRHArcs.mem_centers.mp hi).2.2.2⟩, hti⟩
    refine ⟨i, Finset.mem_filter.mpr ⟨hi, hgt⟩, ?_⟩
    rw [cell_of_band (Finset.mem_filter.mpr ⟨hi, hgt⟩)]
    exact ⟨hti, hunit⟩

theorem band_integral_eq_sum {n : ℕ} (hQ : narrow n ≤ Ccap n)
    (hbudget : 2 * width n * Ccap n < n) (F : ℝ → ℂ) (hF : Continuous F) :
    (∫ t in (0 : ℝ)..1,
        (cap n (Ccap n) (width n) \ cap n (narrow n) (width n)).indicator F t) =
      ∑ i ∈ bandIdx n, ∫ t in cell n (narrow n) (width n) i, F t := by
  have hm := (GoldbachGRHArcs.measurable_cap n (Ccap n) (width n)).diff
    (GoldbachGRHArcs.measurable_cap n (narrow n) (width n))
  have hint : IntegrableOn F (Set.Ioc (0 : ℝ) 1) volume :=
    (hF.intervalIntegrable (0 : ℝ) 1).1
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), setIntegral_indicator hm,
    Set.inter_comm, ← band_cells_eq hQ hbudget]
  exact integral_biUnion_finset (bandIdx n)
    (fun i _ => GoldbachGRHArcs.measurable_cell n (narrow n) (width n) i)
    (band_disjoint hbudget) (fun i _ => hint.mono_set Set.inter_subset_right)


section Band

open GoldbachFourthMoment (phase primeSum)
open GoldbachGRHModel (model model_continuous)
open GoldbachGRHApproximation (integrand)
open GoldbachGRHArcs (centers cell cap arc radius center)
open GoldbachGRHKernel (mass)
open GoldbachExplicitModeledMajor (coefficient)
open GoldbachWindow (poly)
open GBSkirtVariance (cellError variance length)
open GoldbachGRHAnalytic (errorCoeff)

theorem band_signed_bound {n : ℕ} (hn : 2 ≤ n) (hbudget : 2 * width n * Ccap n < n)
    {η : ℝ} (hη : 0 < η) :
    ‖(∑ i ∈ bandIdx n, ∫ t in cell n (narrow n) (width n) i, integrand n t) -
      (∑ i ∈ bandIdx n, ∫ t in cell n (narrow n) (width n) i,
        model n i t ^ 2 * phase (-(n:ℝ)*t))‖ ≤
      (1+1/η) * (∑ i ∈ bandIdx n, cellError n (narrow n) (width n) i) +
        η * (((n:ℝ)+1) * (Real.log (n:ℝ))^2) := by
  let osc (t : ℝ) := phase (-(n:ℝ)*t)
  have hOsc : Continuous osc := by unfold osc phase; fun_prop
  have hS : Continuous (primeSum n) := by unfold primeSum phase; fun_prop
  have hF : Continuous (integrand n) := (hS.pow 2).mul hOsc
  rw [← Finset.sum_sub_distrib]
  have hsplit (i : ℕ × ℕ) :
      (∫ t in cell n (narrow n) (width n) i, integrand n t) -
        (∫ t in cell n (narrow n) (width n) i, model n i t ^ 2 * osc t) =
      ∫ t in cell n (narrow n) (width n) i,
        (primeSum n t ^ 2 - model n i t ^ 2) * osc t := by
    have hpart : cell n (narrow n) (width n) i ⊆ Set.Ioc (0:ℝ) 1 :=
      Set.inter_subset_right
    have h₁ : IntegrableOn (integrand n) (cell n (narrow n) (width n) i) volume :=
      (hF.intervalIntegrable 0 1).1.mono_set hpart
    have hm : Continuous (fun t => model n i t ^ 2 * osc t) :=
      ((model_continuous n i).pow 2).mul hOsc
    have h₂ : IntegrableOn (fun t => model n i t ^ 2 * osc t)
        (cell n (narrow n) (width n) i) volume :=
      (hm.intervalIntegrable 0 1).1.mono_set hpart
    rw [← integral_sub h₁ h₂]
    simp [integrand, osc, sub_mul]
  dsimp only [osc] at hsplit
  simp_rw [hsplit]
  apply (norm_sum_le _ _).trans
  apply (GoldbachGRHWindowEnergy.sum_setIntegral_square_difference_le
    (bandIdx n) (cell n (narrow n) (width n))
    (fun i _ => GoldbachGRHArcs.measurable_cell _ _ _ i)
    (fun _ _ => Set.inter_subset_right) (band_disjoint hbudget)
    (primeSum n) (model n) osc hS (fun i _ => model_continuous n i) hOsc
    (fun t => le_of_eq (Complex.norm_exp_ofReal_mul_I (2 * Real.pi * (-(n:ℝ)*t)))) hη).trans
  exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_left
    (GoldbachGRHAnalytic.prime_sum_energy_le n hn) hη.le)

theorem common_window_band (n Q Q' H h : ℕ) (hn : 0<n) (hh : 0<h) (hw : 6*h*H ≤ n) :
    (h:ℝ)^2 * (∑ i ∈ centers Q, cellError n Q' H i) ≤ 8*variance n Q h := by
  rw [GoldbachGRHArcs.sum_centers_eq, Finset.mul_sum, variance, Finset.mul_sum]
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
  have hcells : (∑ a ∈ (range (q+1)).filter (fun a => a.Coprime q), cellError n Q' H (q,a)) ≤
      2*∑ a : ZMod q, E a :=
    (sum_le_sum (fun a ha => GBSkirtVariance.cell_to_poly n Q' H a (mem_filter.mp ha).2)).trans
      (GoldbachGRHArcs.sum_numerators_le_real q E hE)
  have hden := GBSkirtVariance.denominator_bound (q:=q) n h δ hh hd hwidth
  change (h:ℝ)^2/4 * (∑ a : ZMod q, E a) ≤ _ at hden
  rw [GBSkirtVariance.mass,dite_eq_right hqn]
  linarith only [mul_le_mul_of_nonneg_left hcells (sq_nonneg (h:ℝ)),hden]

theorem band_error_le {n : ℕ} (hn : 0 < n) (hh : 0 < length n)
    (hw : 6 * length n * width n ≤ n) :
    (∑ i ∈ bandIdx n, cellError n (narrow n) (width n) i) ≤
      8 * variance n (Ccap n) (length n) / ((length n : ℝ)^2) := by
  have hcell_nonneg (i : ℕ × ℕ) : 0 ≤ cellError n (narrow n) (width n) i := by
    unfold cellError
    exact MeasureTheory.setIntegral_nonneg (GoldbachGRHArcs.measurable_cell _ _ _ i)
      (fun _ _ => sq_nonneg _)
  have h1 : (∑ i ∈ bandIdx n, cellError n (narrow n) (width n) i) ≤
      ∑ i ∈ centers (Ccap n), cellError n (narrow n) (width n) i :=
    Finset.sum_le_sum_of_subset_of_nonneg (bandIdx_subset n)
      (fun i _ _ => hcell_nonneg i)
  have h2 := common_window_band n (Ccap n) (narrow n) (width n) (length n) hn hh hw
  have hpos : (0:ℝ) < ((length n : ℝ)^2) := by positivity
  refine h1.trans ?_
  apply (le_div_iff₀ hpos).2
  rw [mul_comm]
  exact h2

end Band


section BandModel

open GoldbachFourthMoment (phase primeSum)
open GoldbachGRHModel (model model_continuous)
open GoldbachGRHApproximation (integrand)
open GoldbachGRHArcs (centers cell cap arc radius center)
open GoldbachGRHKernel (mass)
open GoldbachExplicitModeledMajor (coefficient)
open GoldbachWindow (poly)
open GBSkirtVariance (cellError variance length)
open GoldbachGRHAnalytic (errorCoeff)

theorem band_model_re {n : ℕ} (hQ : narrow n ≤ Ccap n) (hQH : narrow n ≤ width n)
    (hHn : width n ≤ n) (h1 : 1 ≤ Ccap n) (hQ1 : 1 ≤ narrow n) :
    (∑ i ∈ bandIdx n, ∫ t in cell n (narrow n) (width n) i,
        model n i t ^ 2 * phase (-(n:ℝ)*t)).re =
      ∑ q ∈ Ioc (narrow n) (Ccap n), (coefficient q n).re * mass n (radius n (width n) q) := by
  let f : ℕ × ℕ → ℂ := fun i =>
    ∫ t in cell n (narrow n) (width n) i, model n i t ^ 2 * phase (-(n:ℝ)*t)
  have hdiff : centers (Ccap n) \ bandIdx n = centers (narrow n) := by
    ext i
    simp only [Finset.mem_sdiff, bandIdx, Finset.mem_filter, GoldbachGRHArcs.mem_centers]
    constructor
    · rintro ⟨hi, hnot⟩; exact ⟨hi.1, by omega, hi.2.2.1, hi.2.2.2⟩
    · rintro ⟨h₁, h₂, h₃, h₄⟩
      exact ⟨⟨h₁, h₂.trans hQ, h₃, h₄⟩, by omega⟩
  have hsum : (∑ i ∈ bandIdx n, f i) =
      (∑ i ∈ centers (Ccap n), f i) - (∑ i ∈ centers (narrow n), f i) := by
    have hsd := Finset.sum_sdiff (f := f) (bandIdx_subset n)
    rw [hdiff] at hsd
    rw [← hsd] <;> ring
  have hsub2 : Ioc (narrow n) (Ccap n) ⊆ Icc 1 (Ccap n) := by
    intro q hq
    exact Finset.mem_Icc.mpr ⟨hQ1.trans (Finset.mem_Ioc.mp hq).1.le, (Finset.mem_Ioc.mp hq).2⟩
  have hdiff2 : Icc 1 (Ccap n) \ Ioc (narrow n) (Ccap n) = Icc 1 (narrow n) := by
    ext q
    simp only [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨h₁, h₂⟩, h₃⟩; exact ⟨h₁, by omega⟩
    · rintro ⟨h₁, h₂⟩; exact ⟨⟨h₁, h₂.trans hQ⟩, by omega⟩
  let g : ℕ → ℝ := fun q => (coefficient q n).re *
    GoldbachGRHModelAssembly.massDifference n (narrow n) (width n) q
  have hsplit : (∑ q ∈ Icc 1 (Ccap n), g q) =
      (∑ q ∈ Icc 1 (narrow n), g q) + (∑ q ∈ Ioc (narrow n) (Ccap n), g q) := by
    have hsd := Finset.sum_sdiff (f := g) hsub2
    rw [hdiff2] at hsd
    rw [← hsd] <;> ring
  change (∑ i ∈ bandIdx n, f i).re = _
  rw [hsum, Complex.sub_re, GoldbachGRHModelAssembly.sum_cell_model_re h1 hQH hHn,
    GoldbachGRHModelAssembly.sum_cell_model_re hQ1 hQH hHn]
  change (∑ q ∈ Icc 1 (Ccap n), g q) - (∑ q ∈ Icc 1 (narrow n), g q) = _
  rw [hsplit, add_sub_cancel_left]
  refine Finset.sum_congr rfl fun q hq => ?_
  have hqn : ¬ q ≤ narrow n := by have := (Finset.mem_Ioc.mp hq).1; omega
  dsimp only [g]
  rw [GoldbachGRHModelAssembly.massDifference, ite_eq_right hqn, sub_zero]

theorem band_model_floor (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, Even n → -(ε * ((n:ℝ)+1)) ≤
      (∑ i ∈ bandIdx n, ∫ t in cell n (narrow n) (width n) i,
        model n i t ^ 2 * phase (-(n:ℝ)*t)).re := by
  obtain ⟨K₀, hK₀⟩ := GoldbachGRHSignedModel.harmonic_suffix_floor ε hε
  filter_upwards [GoldbachGRHBudget.eventual_geometry,
    GoldbachLowSkirt7.eventually_narrow_ge K₀] with n hg hK
  intro hEven
  obtain ⟨hn, hQ1, hQU, hUn, hbudget24, hbudget⟩ := hg
  have hQC : narrow n ≤ Ccap n := narrow_le_Ccap n hQ1 hQU
  have h1 : 1 ≤ Ccap n := hQ1.trans hQC
  have hQH : narrow n ≤ width n := hQU.trans (GoldbachGRHBudget.width_ge_cutoff n hQ1)
  have hHn : width n ≤ n := by change 24 * width n ≤ n at hbudget24; omega
  rw [band_model_re hQC hQH hHn h1 hQ1]
  let w : ℕ → ℝ := fun q => mass n (radius n (width n) q)
  have hW : 0 < width n := by omega
  have hn0 : 0 < n := by omega
  have hradius_nonneg (i : ℕ) : 0 ≤ radius n (width n) i := by
    unfold radius
    exact div_nonneg (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg i) (Nat.cast_nonneg n))
  have hradius_pos (i : ℕ) (hi : 1 ≤ i) : 0 < radius n (width n) i := by
    unfold radius
    have hi' : (0:ℝ) < i := by exact_mod_cast (by omega : 0 < i)
    have hn' : (0:ℝ) < n := by exact_mod_cast hn0
    have hW' : (0:ℝ) < width n := by exact_mod_cast hW
    exact div_pos hW' (mul_pos hi' hn')
  have hw0 : ∀ i ≥ narrow n, 0 ≤ w i := fun i _ =>
    GoldbachGRHKernel.mass_nonneg n (hradius_nonneg i)
  have hwmono : ∀ i ≥ narrow n, w (i+1) ≤ w i := by
    intro i hi
    apply GoldbachGRHKernel.mass_mono n
    · exact hradius_nonneg (i+1)
    · unfold radius
      exact div_le_div_of_nonneg_left (Nat.cast_nonneg _)
        (mul_pos (by exact_mod_cast (by omega : 0 < i)) (by exact_mod_cast hn0))
        (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ i) (Nat.cast_nonneg n))
  have hprefix : ∀ i ≥ narrow n, i ≤ Ccap n → -ε ≤ ∑ j ∈ Ioc (narrow n) i, (coefficient j n).re := by
    intro i hi _
    have hh := hK₀ (narrow n) hK n i hEven hi
    rw [Finset.sum_congr rfl (fun q hq =>
      (GoldbachGRHSignedModel.coefficient_re_eq n q
        (by have := (Finset.mem_Ioc.mp hq).1; omega)).symm)] at hh
    exact hh
  have hmain := BandTail.weighted_prefix_lower (narrow n) (Ccap n)
    (fun q => (coefficient q n).re) w ε hQC hε.le hw0 hwmono hprefix
  have hwQ : w (narrow n) ≤ (n:ℝ) + 1 := by
    have hr : 0 < radius n (width n) (narrow n) := hradius_pos (narrow n) hQ1
    have hh : radius n (width n) (narrow n) ≤ 1/2 := by
      unfold radius
      have h24 : (24:ℝ) * (width n : ℝ) ≤ (n : ℝ) := by exact_mod_cast hbudget24
      have hq1 : (1:ℝ) ≤ (narrow n : ℝ) := by exact_mod_cast hQ1
      have hnR : (0:ℝ) < n := by exact_mod_cast hn0
      have hW' : (0:ℝ) < width n := by exact_mod_cast hW
      have h1' : (width n : ℝ) / (n : ℝ) ≤ 1/24 := by
        rw [div_le_iff₀ hnR]; linarith
      have h2' : (width n : ℝ) / ((narrow n : ℝ) * (n : ℝ)) ≤ (width n : ℝ) / (n : ℝ) := by
        apply div_le_div_of_nonneg_left hW'.le hnR
        nlinarith
      linarith
    have hloss := (GoldbachGRHKernel.mass_loss n hr hh).1
    linarith
  dsimp only [w] at hmain hwQ
  have hmul : -(ε * ((n:ℝ)+1)) ≤ -(ε * mass n (radius n (width n) (narrow n))) := by
    have := mul_le_mul_of_nonneg_left hwQ hε.le
    linarith
  linarith

end BandModel


section BandVariance

open GoldbachGRHBudget (narrow cutoff width)
open GBSkirtVariance (variance length fullL1 clippedL1 row)

theorem paper_scales_band : ∀ᶠ n : ℕ in atTop,
    ((Ccap n : ℝ))^2 * (n:ℝ)^(1/4:ℝ) ≤ (length n:ℝ) := by
  filter_upwards [GoldbachGRHBudget.eventual_geometry, GBSkirtVariance.paper_scales,
    GBSkirtVariance.eventual_scales,
    GoldbachGRHBudget.eventually_log_pow_le 8 (3/8) (1/65536) (by norm_num) (by norm_num)]
    with n hg hs hsc h₈
  obtain ⟨hn, _, _, _, _, _⟩ := hg
  obtain ⟨hL, hQN, _, _⟩ := hsc
  let L := Real.log (n:ℝ)
  have hn0 : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hC : (Ccap n : ℝ) ≤ (narrow n : ℝ)^2 := by
    unfold Ccap
    exact_mod_cast min_le_right (cutoff n) ((narrow n)^2)
  have hQ2 : (narrow n : ℝ)^2 ≤ 256 * L^4 := by
    calc (narrow n : ℝ)^2 ≤ (16*L^2)^2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hQN 2
      _ = 256*L^4 := by ring
  have hQ4 : (narrow n : ℝ)^4 ≤ 65536*L^8 := by
    calc (narrow n : ℝ)^4 = ((narrow n : ℝ)^2)^2 := by ring
      _ ≤ (256*L^4)^2 := pow_le_pow_left₀ (by positivity) hQ2 2
      _ = 65536*L^8 := by ring
  have h8 : 65536*L^8 ≤ (n:ℝ)^(3/8:ℝ) := by
    have hlog : L^8 ≤ (1/65536:ℝ) * (n:ℝ)^(3/8:ℝ) := h₈
    linarith
  calc
    ((Ccap n : ℝ))^2 * (n:ℝ)^(1/4:ℝ) ≤ ((narrow n : ℝ)^2)^2 * (n:ℝ)^(1/4:ℝ) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hC 2)
        (Real.rpow_nonneg hn0.le _)
    _ = (narrow n : ℝ)^4 * (n:ℝ)^(1/4:ℝ) := by ring
    _ ≤ 65536*L^8 * (n:ℝ)^(1/4:ℝ) :=
      mul_le_mul_of_nonneg_right hQ4 (Real.rpow_nonneg hn0.le _)
    _ ≤ (n:ℝ)^(3/8:ℝ) * (n:ℝ)^(1/4:ℝ) :=
      mul_le_mul_of_nonneg_right h8 (Real.rpow_nonneg hn0.le _)
    _ = (n:ℝ)^(5/8:ℝ) := by rw [← Real.rpow_add hn0]; norm_num
    _ ≤ (length n : ℝ) := hs.1

theorem eventually_log21_le_width : ∀ᶠ n : ℕ in atTop,
    (Real.log (n:ℝ))^21 ≤ (cutoff n : ℝ) * (narrow n : ℝ) := by
  filter_upwards [GoldbachGRHBudget.eventual_geometry, eventually_ge_atTop 8,
    GoldbachGRHBudget.eventually_log_pow_le 21 (1/3) (1/2) (by norm_num) (by norm_num)]
    with n hg hn8 hlog
  obtain ⟨_, hQ1, _, _, _, _⟩ := hg
  have hnR : (8:ℝ) ≤ n := by exact_mod_cast hn8
  have hroot : (2:ℝ) ≤ (n:ℝ)^(1/3:ℝ) := by
    have := Real.rpow_le_rpow (by norm_num) hnR (by norm_num : (0:ℝ) ≤ 1/3)
    norm_num at this
    linarith
  have hcut : (n:ℝ)^(1/3:ℝ) - 1 ≤ (cutoff n : ℝ) := by
    have hf := Nat.lt_floor_add_one ((n:ℝ)^(1/3:ℝ))
    change _ < (cutoff n : ℝ)+1 at hf
    linarith
  have hnar : (1:ℝ) ≤ (narrow n : ℝ) := by exact_mod_cast hQ1
  have hprod : (n:ℝ)^(1/3:ℝ)/2 ≤ (cutoff n : ℝ) * (narrow n : ℝ) := by
    have h1 : (n:ℝ)^(1/3:ℝ)/2 ≤ (cutoff n : ℝ) := by linarith
    calc (n:ℝ)^(1/3:ℝ)/2 = (n:ℝ)^(1/3:ℝ)/2 * 1 := by ring
      _ ≤ (cutoff n : ℝ) * (narrow n : ℝ) := by gcongr
  linarith

theorem band_full_average (hyp : GBSkirtVariance.IntegerDyadicAP) :
    ∀ᶠ n : ℕ in atTop,
      GBSkirtVariance.fullL1 n (Ccap n) (length n) ≤
        (n:ℝ) * (length n:ℝ) / (Real.log (n:ℝ))^16 := by
  obtain ⟨C,hC,X,hX⟩ := hyp
  have ht : Tendsto (fun n : ℕ => Real.log (n:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have ht' := (tendsto_rpow_atTop (by norm_num : (0:ℝ)<5/8)).comp
    (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [GoldbachGRHBudget.eventual_geometry, GBSkirtVariance.eventual_scales,
    GBSkirtVariance.paper_scales, GBSkirtVariance.length_ok, paper_scales_band,
    eventually_log21_le_width,
    ht.eventually (eventually_ge_atTop (8*C*2^18)),
    ht'.eventually (eventually_ge_atTop (X:ℝ))] with n hg hs hscale hl hband h21 hbig hX'
  let L := Real.log (n:ℝ)
  let H := (length n:ℝ)
  let Q := Ccap n
  let K := C*(2:ℝ)^18*H/L^18
  obtain ⟨hn,hQ,hQU,_,_,_⟩ := hg
  obtain ⟨hL,hQN,_,hbudget⟩ := hs
  change 16 ≤ L at hL
  change 1000000*L^20*H ≤ (n:ℝ) at hbudget
  change 8*C*2^18 ≤ L at hbig
  change (X:ℝ) ≤ (n:ℝ)^(5/8:ℝ) at hX'
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (by omega : 1≤n)
  have hn0 : 0 < (n:ℝ) := by linarith
  have hL1 : 1≤L := by linarith
  have hL0 : 0<L := by linarith
  have hH : 0<H := by dsimp [H]; exact_mod_cast hl.1
  have hhn : length n ≤ n := Nat.div_le_self _ _
  have hK : 0≤K := by dsimp [K]; positivity
  have hQ1 : 1 ≤ Q := hQ.trans (narrow_le_Ccap n hQ hQU)
  have hQC : (Q:ℝ) ≤ 256*L^4 := by
    have hCq : (Ccap n : ℝ) ≤ (narrow n : ℝ)^2 := by
      unfold Ccap
      exact_mod_cast min_le_right (cutoff n) ((narrow n)^2)
    have hQ2 : (narrow n : ℝ)^2 ≤ 256 * L^4 := by
      calc (narrow n : ℝ)^2 ≤ (16*L^2)^2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hQN 2
        _ = 256*L^4 := by ring
    exact hCq.trans hQ2
  have hlocal (x : ℕ) (hx : length n ≤ x) (hxn : x ≤ n) :
      (∑ y ∈ Ico x (2*x), GBSkirtVariance.row Q (length n) y) ≤ (x:ℝ)*K := by
    have hxr : (x:ℝ) ≤ n := by exact_mod_cast hxn
    have hhx : H ≤ (x:ℝ) := by dsimp [H]; exact_mod_cast hx
    have hxl : (n:ℝ)^(5/8:ℝ) ≤ (x:ℝ) := hscale.1.trans hhx
    have hlog : L ≤ 2*Real.log (x:ℝ) := by
      have ht := Real.log_le_log (Real.rpow_pos_of_pos hn0 _) hxl
      rw [Real.log_rpow hn0] at ht
      change (5/8:ℝ)*L ≤ _ at ht
      linarith
    have hxp : 0 < Real.log (x:ℝ) := by linarith
    have he := hX x (length n) Q (by exact_mod_cast hX'.trans hxl) hQ1
      ((Real.rpow_le_rpow (by positivity) hxr (by norm_num)).trans hscale.1) hx
      ((mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hxr (by norm_num))
        (sq_nonneg (Q:ℝ))).trans hband)
    have hpow := pow_le_pow_left₀ hL0.le hlog 18
    rw [mul_pow] at hpow
    apply he.trans
    change C*(x:ℝ)*H/(Real.log (x:ℝ))^18 ≤ (x:ℝ)*(C*2^18*H/L^18)
    rw [← mul_div_assoc,div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith only [mul_le_mul_of_nonneg_right hpow (by positivity : 0≤C*(x:ℝ)*H)]
  have hcov := GBSkirtVariance.dyadic_cover (GBSkirtVariance.row Q (length n))
    (GBSkirtVariance.row_nonneg Q _) n (length n) hl.1 K hK hlocal
  have hinit := GBSkirtVariance.initial_rows n Q (length n) hn hhn
  have hlog3 : Real.log (3*(n:ℝ))+1 ≤ 3*L := by
    rw [Real.log_mul (by norm_num) hn0.ne']
    have ha := Real.log_le_sub_one_of_pos (by norm_num : 0 < (3:ℝ))
    change Real.log 3 + L + 1 ≤ _
    linarith
  have hnon : 0 ≤ Real.log (3*(n:ℝ))+1 := by
    have := Real.log_nonneg (by linarith only [hn1] : 1≤3*(n:ℝ))
    linarith
  have hi : (∑ y ∈ range (2*length n), GBSkirtVariance.row Q (length n) y)*L^16 ≤ (n:ℝ)*H/2 := by
    have ha : (∑ y ∈ range (2*length n), GBSkirtVariance.row Q (length n) y) ≤ 1536*H^2*L^5 := by
      apply hinit.trans
      calc
        _ ≤ 2*(256*L^4)*H^2*(3*L) := by gcongr
        _ = _ := by ring
    have hlen : H * ((12 * width n : ℕ):ℝ) ≤ (n:ℝ) := by
      have h' : (length n : ℝ) * ((12 * width n : ℕ):ℝ) ≤ (n:ℝ) := by
        exact_mod_cast Nat.div_mul_le_self n (12 * width n)
      exact h'
    have hw21 : 256*L^21 ≤ ((width n : ℕ):ℝ) := by
      have hwid : ((width n : ℕ):ℝ) = 256 * ((cutoff n : ℝ) * (narrow n : ℝ)) := by
        unfold width; push_cast; ring
      have h21' : L^21 ≤ (cutoff n : ℝ) * (narrow n : ℝ) := h21
      rw [hwid]
      linarith
    have hkey : 3072*H*L^21 ≤ (n:ℝ) := by
      calc 3072*H*L^21 = H * (12*(256*L^21)) := by ring
        _ ≤ H * (12*((width n : ℕ):ℝ)) := by gcongr
        _ = H * ((12 * width n : ℕ):ℝ) := by push_cast; ring
        _ ≤ (n:ℝ) := hlen
    nlinarith only [mul_le_mul_of_nonneg_right ha (by positivity : 0≤L^16), hkey, hH]
  have he : (2*((n+1:ℕ):ℝ)*K)*L^16 ≤ (n:ℝ)*H/2 := by
    have hcoeff : 8*C*2^18 ≤ L^2 := by nlinarith only [hbig,mul_le_mul_of_nonneg_right hL1 hL0.le]
    have hc : 2*((n+1:ℕ):ℝ) ≤ 4*(n:ℝ) := by push_cast; linarith
    have hx : (2*((n+1:ℕ):ℝ)*K)*L^16 ≤ (4*(n:ℝ)*K)*L^16 := by gcongr
    apply hx.trans
    have hid : (4*(n:ℝ)*K)*L^16 = (4*(n:ℝ)*C*2^18*H)/L^2 := by
      unfold K; field_simp [hL0.ne'] <;> ring
    rw [hid,div_le_iff₀ (by positivity)]
    nlinarith only [mul_le_mul_of_nonneg_right hcoeff (by positivity : 0≤(n:ℝ)*H)]
  rw [GBSkirtVariance.fullL1_rows]
  apply (le_div_iff₀ (by positivity : 0<L^16)).2
  nlinarith only [mul_le_mul_of_nonneg_right hcov (by positivity : 0≤L^16),hi,he]

theorem number_budget_band (N h Q L : ℝ) (hN : 1≤N) (hh : 1≤h) (hQ : 0≤Q)
    (hL : 16≤L) (hQN : Q ≤ 256*L^4) (hb : 1000000*L^20 ≤ h) (hc : 1000000*L^20*h ≤ N) :
    Q^2*(h*(L+1))*(N*h/L^16 + Q*2*h^2*(L+1)) + Q^2*(3*N)*L^2 ≤ 1048576*N*h^2/L^6 := by
  have hL1 : 1 ≤ L := by linarith
  have hL0 : 0 < L := by linarith
  have hhn : 0 ≤ h := by linarith
  have hn : 0 ≤ N := by linarith
  have hL20 : 0 ≤ L^20 := by positivity
  have hL16 : L^16 ≤ h^2 := by
    have h1 : L^16 ≤ L^20 := pow_le_pow_right₀ hL1 (by decide)
    have h2 : L^20 ≤ h := by linarith
    nlinarith
  have hQ2 : Q^2 ≤ 65536*L^8 := by
    calc Q^2 ≤ (256*L^4)^2 := pow_le_pow_left₀ hQ hQN 2
      _ = 65536*L^8 := by ring
  have hQ3 : Q^3 ≤ 16777216*L^12 := by
    calc Q^3 ≤ (256*L^4)^3 := pow_le_pow_left₀ hQ hQN 3
      _ = 16777216*L^12 := by ring
  have hsum : Q^2*(h*(L+1))*(N*h/L^16 + Q*2*h^2*(L+1)) =
      Q^2*(h*(L+1))*(N*h/L^16) + Q^2*(h*(L+1))*(Q*2*h^2*(L+1)) := by ring
  have hA : Q^2*(h*(L+1))*(N*h/L^16) ≤ 262144*N*h^2/L^6 := by
    have hstep : Q^2*(h*(L+1))*(N*h/L^16) ≤ 131072*N*h^2/L^7 := by
      calc Q^2*(h*(L+1))*(N*h/L^16) ≤ (65536*L^8)*(h*(2*L))*(N*h/L^16) := by
            gcongr
            linarith
        _ = 131072*N*h^2/L^7 := by field_simp [hL0.ne'] <;> ring
    have hcore : (131072:ℝ)*N*h^2 ≤ 262144*N*h^2*L := by
      calc (131072:ℝ)*N*h^2 = (131072:ℝ)*(N*h^2) := by ring
        _ ≤ (262144:ℝ)*(N*h^2) := mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
        _ = (262144:ℝ)*(N*h^2)*1 := by ring
        _ ≤ (262144:ℝ)*(N*h^2)*L := mul_le_mul_of_nonneg_left hL1 (by positivity)
        _ = 262144*N*h^2*L := by ring
    calc Q^2*(h*(L+1))*(N*h/L^16) ≤ 131072*N*h^2/L^7 := hstep
      _ = (131072*N*h^2)/L^7 := by ring
      _ ≤ (262144*N*h^2*L)/L^7 := div_le_div_of_nonneg_right hcore (by positivity)
      _ = 262144*N*h^2/L^6 := by field_simp [hL0.ne'] <;> ring
  have hB : Q^2*(3*N)*L^2 ≤ 262144*N*h^2/L^6 := by
    have hstep : Q^2*(3*N)*L^2 ≤ 196608*N*L^10 := by
      calc Q^2*(3*N)*L^2 ≤ (65536*L^8)*(3*N)*L^2 := by gcongr
        _ = 196608*N*L^10 := by ring
    have hcore : (196608:ℝ)*N*L^16 ≤ 262144*N*h^2 := by
      calc (196608:ℝ)*N*L^16 = (196608:ℝ)*(N*L^16) := by ring
        _ ≤ (262144:ℝ)*(N*L^16) := mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
        _ ≤ (262144:ℝ)*(N*h^2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hL16 hn) (by norm_num)
        _ = 262144*N*h^2 := by ring
    calc Q^2*(3*N)*L^2 ≤ 196608*N*L^10 := hstep
      _ = (196608*N*L^16)/L^6 := by field_simp [hL0.ne'] <;> ring
      _ ≤ (262144*N*h^2)/L^6 := div_le_div_of_nonneg_right hcore (by positivity)
      _ = 262144*N*h^2/L^6 := by ring
  have hC : Q^2*(h*(L+1))*(Q*2*h^2*(L+1)) ≤ 262144*N*h^2/L^6 := by
    have hstep : Q^2*(h*(L+1))*(Q*2*h^2*(L+1)) = 2*Q^3*h^3*(L+1)^2 := by ring
    rw [hstep]
    have hstep2 : 2*Q^3*h^3*(L+1)^2 ≤ 134217728*h^3*L^14 := by
      calc 2*Q^3*h^3*(L+1)^2 ≤ 2*(16777216*L^12)*h^3*(2*L)^2 := by
            gcongr
            linarith
        _ = 134217728*h^3*L^14 := by ring
    have hcore : (134217728:ℝ)*h^3*L^20 ≤ 262144*N*h^2 := by
      calc (134217728:ℝ)*h^3*L^20 = (134217728:ℝ)*(h^3*L^20) := by ring
        _ ≤ (262144*1000000:ℝ)*(h^3*L^20) := mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
        _ = (262144*h^2)*(1000000*L^20*h) := by ring
        _ ≤ (262144*h^2)*N := mul_le_mul_of_nonneg_left hc (by positivity)
        _ = 262144*N*h^2 := by ring
    calc 2*Q^3*h^3*(L+1)^2 ≤ 134217728*h^3*L^14 := hstep2
      _ = (134217728*h^3*L^20)/L^6 := by field_simp [hL0.ne'] <;> ring
      _ ≤ (262144*N*h^2)/L^6 := div_le_div_of_nonneg_right hcore (by positivity)
      _ = 262144*N*h^2/L^6 := by ring
  rw [hsum]
  have hT : (0:ℝ) ≤ N*h^2/L^6 := by positivity
  have hthree : (262144:ℝ)*N*h^2/L^6 + (262144:ℝ)*N*h^2/L^6 + (262144:ℝ)*N*h^2/L^6 ≤
      1048576*N*h^2/L^6 := by
    calc (262144:ℝ)*N*h^2/L^6 + (262144:ℝ)*N*h^2/L^6 + (262144:ℝ)*N*h^2/L^6 =
        (786432:ℝ)*(N*h^2/L^6) := by ring
      _ ≤ (1048576:ℝ)*(N*h^2/L^6) := mul_le_mul_of_nonneg_right (by norm_num) hT
      _ = 1048576*N*h^2/L^6 := by ring
  linarith

theorem band_variance (hyp : GBSkirtVariance.IntegerDyadicAP) : ∀ᶠ n : ℕ in atTop,
    variance n (Ccap n) (length n) ≤ 1048576 * (n:ℝ) * (length n:ℝ)^2 / (Real.log (n:ℝ))^6 := by
  filter_upwards [GoldbachGRHBudget.eventual_geometry, GBSkirtVariance.length_ok,
    GBSkirtVariance.eventual_scales, band_full_average hyp] with n hg hl hs hav
  obtain ⟨hn,hQ1,hQU,hUn,_,_⟩ := hg
  obtain ⟨hL,hQN,hb,hc⟩ := hs
  let L := Real.log (n:ℝ)
  let H := (length n:ℝ)
  have hCU : Ccap n ≤ n := (min_le_left _ _).trans hUn
  have hnat : length n ≤ n := Nat.div_le_self _ _
  have hM : (((n+1+length n : ℕ):ℝ)) ≤ 3*(n:ℝ) := by exact_mod_cast (by omega : n+1+length n≤3*n)
  have hclip := (GBSkirtVariance.clipped_to_full n (Ccap n) (length n) hn hnat).trans
    (add_le_add hav (le_refl _))
  have hV := GBSkirtVariance.variance_of_L1 n (Ccap n) (length n) hn hCU
  have hQC : (Ccap n : ℝ) ≤ 256*L^4 := by
    have hCq : (Ccap n : ℝ) ≤ (narrow n : ℝ)^2 := by
      unfold Ccap
      exact_mod_cast min_le_right (cutoff n) ((narrow n)^2)
    have hQ2 : (narrow n : ℝ)^2 ≤ 256 * L^4 := by
      calc (narrow n : ℝ)^2 ≤ (16*L^2)^2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hQN 2
        _ = 256*L^4 := by ring
    exact hCq.trans hQ2
  have hx := number_budget_band (n:ℝ) (length n:ℝ) (Ccap n:ℝ) L
    (by exact_mod_cast (by omega : 1≤n)) (by exact_mod_cast (show 1 ≤ length n by omega))
    (by positivity) hL hQC hb hc
  dsimp only [L] at hx
  exact hV.trans ((add_le_add (mul_le_mul_of_nonneg_left hclip (by positivity))
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hM (sq_nonneg _)) (sq_nonneg _))).trans hx)

end BandVariance

section BandFinal

open GoldbachFourthMoment (phase primeSum)
open GoldbachGRHModel (model model_continuous)
open GoldbachGRHApproximation (integrand)
open GoldbachGRHArcs (centers cell cap arc radius center)
open GoldbachGRHKernel (mass)
open GoldbachExplicitModeledMajor (coefficient)
open GBSkirtVariance (cellError variance length)

theorem band_main (hyp : GBSkirtVariance.IntegerDyadicAP) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, Even n → -(ε*(n:ℝ)) ≤
      (∫ t in (0:ℝ)..1,
        (cap n (Ccap n) (width n) \ cap n (narrow n) (width n)).indicator (integrand n) t).re := by
  have ht : Tendsto (fun n : ℕ => Real.log (n:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [GoldbachGRHBudget.eventual_geometry, GBSkirtVariance.length_ok,
    band_model_floor (ε/4) (by positivity), band_variance hyp,
    ht.eventually (eventually_ge_atTop (max 1 (1073741824/ε)))] with n hg hl hm hv hLmax
  intro hEven
  obtain ⟨hn, hQ1, hQU, hUn, hbud24, hbud⟩ := hg
  let L := Real.log (n:ℝ)
  have hL1 : 1 ≤ L := (le_max_left _ _).trans hLmax
  have hL0 : 0 < L := by linarith
  have hLe : 1073741824/ε ≤ L := (le_max_right _ _).trans hLmax
  have hQC : narrow n ≤ Ccap n := narrow_le_Ccap n hQ1 hQU
  have hCU : Ccap n ≤ cutoff n := min_le_left _ _
  have hbudget : 2 * width n * Ccap n < n := by
    have := Nat.mul_le_mul_left (2 * width n) hCU
    omega
  have hF : Continuous (integrand n) := by
    have hS : Continuous (primeSum n) := by unfold primeSum phase; fun_prop
    have hOsc : Continuous (fun t => phase (-(n:ℝ)*t)) := by unfold phase; fun_prop
    exact (hS.pow 2).mul hOsc
  rw [band_integral_eq_sum hQC hbudget _ hF]
  have hη : (0:ℝ) < 1/L^4 := by positivity
  have hnorm := band_signed_bound hn hbudget hη
  have herr := band_error_le (by omega) hl.1 hl.2
  have hcell_nonneg (i : ℕ × ℕ) : 0 ≤ cellError n (narrow n) (width n) i := by
    unfold cellError
    exact MeasureTheory.setIntegral_nonneg (GoldbachGRHArcs.measurable_cell _ _ _ i)
      (fun _ _ => sq_nonneg _)
  have hD0 : 0 ≤ ∑ i ∈ bandIdx n, cellError n (narrow n) (width n) i :=
    Finset.sum_nonneg (fun i _ => hcell_nonneg i)
  have hhl : (0:ℝ) < (length n : ℝ) := by exact_mod_cast hl.1
  have hhh : (0:ℝ) < (length n : ℝ)^2 := by positivity
  have hhl0 : (length n : ℝ) ≠ 0 := hhl.ne'
  have hD : (∑ i ∈ bandIdx n, cellError n (narrow n) (width n) i) ≤ 8388608*(n:ℝ)/L^6 := by
    calc (∑ i ∈ bandIdx n, cellError n (narrow n) (width n) i)
        ≤ 8 * variance n (Ccap n) (length n) / ((length n : ℝ)^2) := herr
      _ = (8 / ((length n : ℝ)^2)) * variance n (Ccap n) (length n) := by ring
      _ ≤ (8 / ((length n : ℝ)^2)) * (1048576 * (n:ℝ) * (length n:ℝ)^2 / L^6) :=
        mul_le_mul_of_nonneg_left hv (by positivity)
      _ = 8388608*(n:ℝ)/L^6 := by field_simp [hhh.ne', hhl0, hL0.ne'] <;> ring
  have hE : (1+1/(1/L^4)) * (∑ i ∈ bandIdx n, cellError n (narrow n) (width n) i) +
      (1/L^4)*(((n:ℝ)+1)*L^2) ≤ (ε/2)*(n:ℝ) := by
    have h1 : (1+1/(1/L^4)) ≤ 2*L^4 := by
      rw [one_div_one_div]
      have hL4 : 1 ≤ L^4 := one_le_pow₀ hL1
      linarith
    have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
    have hstep : (1+1/(1/L^4)) * (∑ i ∈ bandIdx n, cellError n (narrow n) (width n) i) +
        (1/L^4)*(((n:ℝ)+1)*L^2) ≤
        (2*L^4) * (8388608*(n:ℝ)/L^6) + (1/L^4)*(((n:ℝ)+1)*L^2) :=
      (add_le_add (mul_le_mul h1 hD hD0 (by positivity)) le_rfl)
    have h2 : ((n:ℝ)+1)/L^2 ≤ 2*(n:ℝ)/L^2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    calc
      (1+1/(1/L^4)) * (∑ i ∈ bandIdx n, cellError n (narrow n) (width n) i) +
          (1/L^4)*(((n:ℝ)+1)*L^2)
        ≤ (2*L^4) * (8388608*(n:ℝ)/L^6) + (1/L^4)*(((n:ℝ)+1)*L^2) := hstep
      _ = 16777216*(n:ℝ)/L^2 + ((n:ℝ)+1)/L^2 := by field_simp [hL0.ne'] <;> ring
      _ ≤ 16777216*(n:ℝ)/L^2 + 2*(n:ℝ)/L^2 := add_le_add le_rfl h2
      _ = 16777218*(n:ℝ)/L^2 := by ring
      _ ≤ (ε/2)*(n:ℝ) := by
        rw [div_le_iff₀ (by positivity)]
        have hεL : (33554436:ℝ) ≤ ε*L^2 := by
          have h3 : (1073741824:ℝ) ≤ ε*L := by
            have := (div_le_iff₀ hε).1 hLe
            linarith
          calc (33554436:ℝ) ≤ 1073741824 := by norm_num
            _ ≤ ε*L := h3
            _ = ε*L*1 := by ring
            _ ≤ ε*L*L := by gcongr
            _ = ε*L^2 := by ring
        have h4 := mul_le_mul_of_nonneg_left hεL (by positivity : (0:ℝ) ≤ (n:ℝ)/2)
        linarith
  have hre := (abs_le.mp ((Complex.abs_re_le_norm _).trans hnorm)).1
  rw [Complex.sub_re] at hre
  have hm' := hm hEven
  have hmod : -(ε/2)*(n:ℝ) ≤
      (∑ i ∈ bandIdx n, ∫ t in cell n (narrow n) (width n) i,
        model n i t ^ 2 * phase (-(n:ℝ)*t)).re := by
    have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
    have hk : (ε/4)*((n:ℝ)+1) ≤ (ε/2)*(n:ℝ) := by
      have : (n:ℝ)+1 ≤ 2*(n:ℝ) := by linarith
      nlinarith [mul_le_mul_of_nonneg_left this hε.le]
    linarith
  dsimp only [L] at hE hre
  linarith

end BandFinal

end Conjectures.Cuts.Task6af0a69f44e255854c404689_aux

theorem Conjectures.Cuts.Task6af0a69f44e255854c404689 :
    have x1 : ℕ → ℕ := fun (x1 : ℕ) => Nat.log (2 : ℕ) (x1 + (2 : ℕ)) ^ (2 : ℕ); have x2 : ℕ → ℕ := fun (x2 : ℕ) => ⌊(↑x2 : ℝ) ^ (1 / 3 : ℝ)⌋₊; have x3 : ℕ → ℕ := fun (x3 : ℕ) => (256 : ℕ) * x2 x3 * x1 x3; have x4 : ℕ → ℕ := fun (x4 : ℕ) => Min.min (x2 x4) (x1 x4 ^ (2 : ℕ)); have x5 : ℕ → ℕ → ℕ → Set ℝ := fun (x5 x6 x7 : ℕ) => {x8 : ℝ | ∃ (x9 : ℕ) (x10 : ℕ), (1 : ℕ) ≤ x9 ∧ x9 ≤ x6 ∧ x10 ≤ x9 ∧ x10.Coprime x9 ∧ |x8 - (↑x10 : ℝ) / (↑x9 : ℝ)| ≤ (↑x7 : ℝ) / ((↑x9 : ℝ) * (↑x5 : ℝ))}; have x6 : ℕ → ℝ := fun (x6 : ℕ) => if Nat.Prime x6 then Real.log (↑x6 : ℝ) else (0 : ℝ); have x7 : ℝ → ℂ := fun (x7 : ℝ) => Complex.exp ((↑((2 : ℝ) * Real.pi * x7) : ℂ) * Complex.I); have x8 : ℕ → ℝ → ℂ := fun (x8 : ℕ) (x9 : ℝ) => (∑ x10 ∈ Finset.range (x8 + (1 : ℕ)), (↑(x6 x10) : ℂ) * x7 ((↑x10 : ℝ) * x9)) ^ (2 : ℕ) * x7 (-(↑x8 : ℝ) * x9); ∀ (x9 : ℝ), (0 : ℝ) < x9 → ∃ (x11 : ℕ), ∀ (x12 : ℕ), x11 ≤ x12 → Even x12 → -(x9 * (↑x12 : ℝ)) ≤ (∫ (x15 : ℝ) in (0 : ℝ)..(1 : ℝ), (x5 x12 (x4 x12) (x3 x12) \ x5 x12 (x1 x12) (x3 x12)).indicator (x8 x12) x15).re := by
  have hmain := Conjectures.Cuts.Task6af0a69f44e255854c404689_aux.band_main
    (GBSkirtVariance.integer_of_paper Conjectures.Goldbach.ShortProgressionsMeanTheta)
  exact fun x9 hx9 => eventually_atTop.mp (hmain x9 hx9)
