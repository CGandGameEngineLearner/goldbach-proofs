import Mathlib

/-!
Signed Ramanujan model on the square-root modulus band.
The unconditional kernel, Farey geometry, and arithmetic estimates are adapted
from goldbach-proofs PR 2486. Its arithmetic foundation credits muxkin's PR
2458 (25c1ef60495052eb22212b5560f90bbc6a4a0917) and DFQDZZ's PR 316
(e4ab24712555ae8c2c926adf19d368a9fb392c35), Apache-2.0. The elementary
separation estimates are adapted from the verified project task CW-8007.
The outer model is integrated over both clipped caps. New denominators use
a uniform signed suffix bound, and loss from truncating the kernels is
summed separately for the old and new denominator ranges.
-/

namespace SqrtArcModelProof29fa

section GoldbachDeepFourthPrimeDenominator
namespace GoldbachFourthMoment
open Finset
noncomputable def phase (x : ℝ) : ℂ := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

theorem phase_add (x y : ℝ) : phase (x + y) = phase x * phase y := by
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

end GoldbachFourthMoment

end GoldbachDeepFourthPrimeDenominator

section GoldbachWideArcSeparation
open Filter
open scoped Topology
namespace GoldbachWideArcs
/-- The triangle inequality and spacing of rational centers give this general width condition.
    This uses the rational-separation argument from goldbach-proofs PR 153. -/
theorem reduced_centers_eq_of_common_point {n H B q r a b : ℕ} {t : ℝ}
    (hn : 2 * H * B < n) (hq : 1 ≤ q) (hr : 1 ≤ r) (hqB : q ≤ B) (hrB : r ≤ B)
    (hca : a.Coprime q) (hcb : b.Coprime r)
    (ha : |t - (a : ℝ)/q| ≤ (H : ℝ)/((q : ℝ)*n))
    (hb : |t - (b : ℝ)/r| ≤ (H : ℝ)/((r : ℝ)*n)) : q = r ∧ a = b := by
  have hqr : 0 < (q : ℝ) := by exact_mod_cast hq
  have hrr : 0 < (r : ℝ) := by exact_mod_cast hr
  have hnr : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hsmall : H*r + H*q < n := by
    nlinarith only [hn, Nat.mul_le_mul_left H hrB, Nat.mul_le_mul_left H hqB]
  have hradii : (H : ℝ)/(q*n) + H/(r*n) < 1/(q*r) := calc
    _ = ((H : ℝ)*r+H*q)/(q*r*n) := by field_simp
    _ < (n : ℝ)/(q*r*n) := (div_lt_div_iff_of_pos_right (by positivity)).mpr (by exact_mod_cast hsmall)
    _ = _ := by field_simp
  have he : a*r = b*q := by
    by_contra hne
    have hsep : 1/((q : ℝ)*r) ≤ |(a : ℝ)/q - b/r| := by
      rw [show (a:ℝ)/q - b/r = (a*r-b*q)/(q*r) by field_simp, abs_div, abs_of_pos (mul_pos hqr hrr)]
      apply (div_le_div_iff_of_pos_right (mul_pos hqr hrr)).mpr
      rcases lt_or_gt_of_ne hne with hab | hba
      · have hgap : (a:ℝ)*r + 1 ≤ b*q := by exact_mod_cast Nat.succ_le_of_lt hab
        linarith [neg_le_abs ((a:ℝ)*r - b*q)]
      · have hgap : (b:ℝ)*q + 1 ≤ a*r := by exact_mod_cast Nat.succ_le_of_lt hba
        linarith [le_abs_self ((a:ℝ)*r - b*q)]
    have htriangle := abs_sub_le ((a:ℝ)/q) t ((b:ℝ)/r)
    rw [abs_sub_comm ((a:ℝ)/q) t] at htriangle
    linarith
  have hdiv₁ : q ∣ r := hca.symm.dvd_of_dvd_mul_left (he ▸ dvd_mul_left q b)
  have hdiv₂ : r ∣ q := hcb.symm.dvd_of_dvd_mul_left (he.symm ▸ dvd_mul_left r a)
  obtain rfl := Nat.dvd_antisymm hdiv₁ hdiv₂
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_right hq he⟩

end GoldbachWideArcs

end GoldbachWideArcSeparation

section GoldbachDeepFourthGeometry
open Filter
open scoped Topology
open Set
namespace GoldbachFourthGeometry
noncomputable def wide (n R H : ℕ) : Set ℝ :=
  {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤R ∧ a≤q ∧ Nat.Coprime a q ∧
    |t - (a:ℝ)/q| ≤ (H:ℝ)/((q:ℝ)*n)}

end GoldbachFourthGeometry

end GoldbachDeepFourthGeometry

section GoldbachDiscreteWindowEstimate
open Finset MeasureTheory
open scoped ComplexConjugate Interval
namespace GoldbachWindow
open GoldbachFourthMoment (phase phase_add)
/-- The finite Fourier series with coefficient list indexed by `range N`. -/
noncomputable def poly (N : ℕ) (b : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ j ∈ range N, b j * phase ((j : ℝ) * t)

private theorem mode_integral (m : ℤ) :
    (∫ t in (0 : ℝ)..1, phase ((m : ℝ) * t)) = if m = 0 then 1 else 0 := by
  by_cases hm : m = 0
  · subst m
    simp [phase]
  let c : ℂ := (m : ℂ) * (2 * Real.pi * Complex.I)
  have he (t : ℝ) : phase ((m : ℝ) * t) = Complex.exp (c * (t : ℂ)) := by
    unfold phase c
    congr 1
    push_cast
    ring
  have hc : c ≠ 0 := by
    dsimp [c]
    exact mul_ne_zero (by exact_mod_cast hm)
      (mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero))
        Complex.I_ne_zero)
  simp_rw [he]
  rw [integral_exp_mul_complex hc]
  simp [hm, c, Complex.exp_int_mul_two_pi_mul_I]

private theorem phase_conj (t : ℝ) : conj (phase t) = phase (-t) := by
  unfold phase
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

theorem parseval (N : ℕ) (b : ℕ → ℂ) :
    (∫ t in (0 : ℝ)..1, ‖poly N b t‖^2) = ∑ k ∈ range N, ‖b k‖^2 := by
  let term (k j : ℕ) (t : ℝ) :=
    (conj (b k) * b j) * phase ((((j : ℤ) - (k : ℤ)) : ℝ) * t)
  let cross (t : ℝ) := ∑ k ∈ range N, ∑ j ∈ range N, term k j t
  have hc (k j : ℕ) : Continuous (term k j) := by
    unfold term phase
    fun_prop
  have hcross : Continuous cross := continuous_finsetSum _ fun k _ =>
    continuous_finsetSum _ fun j _ => hc k j
  have hexpand (t : ℝ) : ((‖poly N b t‖^2 : ℝ) : ℂ) = cross t := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
    simp only [poly, cross, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
    dsimp [term]
    simp only [map_mul, phase_conj]
    simp only [Int.cast_natCast]
    rw [show ((j : ℝ) - (k : ℝ)) * t =
      -((k : ℝ) * t) + (j : ℝ) * t by ring, phase_add]
    ring
  have hint : (∫ t in (0 : ℝ)..1, cross t) = (↑(∑ k ∈ range N, ‖b k‖^2) : ℂ) := by
    dsimp only [cross]
    rw [intervalIntegral.integral_finsetSum
      (fun k _ => (continuous_finsetSum _ fun j _ => hc k j).intervalIntegrable _ _),
      Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [intervalIntegral.integral_finsetSum fun j _ => (hc k j).intervalIntegrable _ _]
    have hmode (j : ℕ) : (∫ t in (0 : ℝ)..1, term k j t) =
        (conj (b k) * b j) * (if j = k then 1 else 0) := by
      have hm : (∫ t in (0 : ℝ)..1, phase (((j : ℝ) - (k : ℝ)) * t)) =
          if j = k then 1 else 0 := by
        simpa only [Int.cast_sub, Int.cast_natCast, sub_eq_zero, Int.ofNat_inj]
          using mode_integral ((j : ℤ) - (k : ℤ))
      unfold term
      rw [intervalIntegral.integral_const_mul]
      exact congrArg ((conj (b k) * b j) * ·) hm
    simp only [hmode]
    rw [Finset.sum_eq_single_of_mem k hk]
    · simp [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
    · intro j _ hne
      simp [hne]
  have hre :
      (∫ t in (0 : ℝ)..1, (cross t).re) = (∫ t in (0 : ℝ)..1, cross t).re := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact integral_re (hcross.intervalIntegrable (0 : ℝ) 1).1
  calc
    _ = ∫ t in (0 : ℝ)..1, (cross t).re := by
      apply intervalIntegral.integral_congr
      intro t _
      simpa only [Complex.ofReal_re] using congrArg Complex.re (hexpand t)
    _ = _ := by rw [hre, hint, Complex.ofReal_re]

end GoldbachWindow

end GoldbachDiscreteWindowEstimate

section GoldbachMinorArcAbelTail
open scoped BigOperators
theorem goldbach_geometric_sum_le_inv_twice_round_distance (θ : ℝ) (K : ℕ)
    (hθ : 0 < |θ - (round θ : ℝ)|) :
    ‖∑ j ∈ Finset.range K, Complex.exp (((2 * Real.pi * (j : ℝ) * θ : ℝ) : ℂ) * Complex.I)‖ ≤
      1 / (2 * |θ - (round θ : ℝ)|) := by
  let k : ℤ := round θ
  let d : ℝ := θ - (k : ℝ)
  let z : ℂ := Complex.exp (((2 * Real.pi * θ : ℝ) : ℂ) * Complex.I)
  have hpos : 0 < |d| := hθ
  have habs : |d| ≤ 1 / 2 := abs_sub_round θ
  have hphase : z = Complex.exp (Complex.I * ((2 * Real.pi * d : ℝ) : ℂ)) := by
    have hsplit :
        (((2 * Real.pi * θ : ℝ) : ℂ) * Complex.I) =
          Complex.I * ((2 * Real.pi * d : ℝ) : ℂ) +
            (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      dsimp [d]
      push_cast
      ring
    dsimp only [z]
    rw [hsplit, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  have harg : |Real.pi * d| ≤ Real.pi / 2 := by
    rw [abs_mul, abs_of_pos Real.pi_pos, show Real.pi / 2 = Real.pi * (1 / 2) by ring]
    exact mul_le_mul_of_nonneg_left habs Real.pi_pos.le
  have hsin : 2 * |d| ≤ |Real.sin (Real.pi * d)| := calc
    _ = 2 / Real.pi * |Real.pi * d| := by
      rw [abs_mul, abs_of_pos Real.pi_pos]
      field_simp [Real.pi_pos.ne']
    _ ≤ _ := Real.mul_abs_le_abs_sin harg
  have hdenom : 4 * |d| ≤ ‖z - 1‖ := by
    rw [hphase, Complex.norm_exp_I_mul_ofReal_sub_one]
    rw [show (2 * Real.pi * d) / 2 = Real.pi * d by ring,
      Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    linarith only [hsin]
  have hunit : ‖z‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have hprod : ‖∑ j ∈ Finset.range K, z ^ j‖ * ‖z - 1‖ ≤ 2 := by
    rw [← norm_mul, geom_sum_mul]
    calc
      _ ≤ ‖z ^ K‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by norm_num [norm_pow, hunit]
  have hscaled : ‖∑ j ∈ Finset.range K, z ^ j‖ * (4 * |d|) ≤ 2 :=
    (mul_le_mul_of_nonneg_left hdenom (norm_nonneg _)).trans hprod
  have hterm (j : ℕ) :
      Complex.exp (((2 * Real.pi * (j : ℝ) * θ : ℝ) : ℂ) * Complex.I) = z^j := by
    have he : (((2 * Real.pi * (j : ℝ) * θ : ℝ) : ℂ) * Complex.I) =
      (j : ℂ) * ((((2 * Real.pi * θ : ℝ) : ℂ)) * Complex.I) := by
      push_cast
      ring
    simpa only [z, he] using Complex.exp_nat_mul
      ((((2 * Real.pi * θ : ℝ) : ℂ)) * Complex.I) j
  simp_rw [hterm]
  change ‖∑ j ∈ Finset.range K, z ^ j‖ ≤ 1 / (2 * |d|)
  apply (le_div_iff₀ (mul_pos (by norm_num) hpos)).2
  nlinarith only [hscaled]

open MeasureTheory
theorem goldbach_periodic_integral_mul_nat
    (g : ℝ → ℝ) (hg : Function.Periodic g 1)
    (hi : IntervalIntegrable g volume 0 1) (m : ℕ) (hm : 0 < m) :
    (∫ t in (0 : ℝ)..1, g ((m : ℝ) * t)) = ∫ t in (0 : ℝ)..1, g t := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hperiod := hg.intervalIntegral_add_zsmul_eq (m : ℤ) 0
    (fun a b => hg.intervalIntegrable₀ (by norm_num) hi a b)
  have hscaled : (∫ t in (0 : ℝ)..(m : ℝ), g t) =
      (m : ℝ) * ∫ t in (0 : ℝ)..1, g t := by
    simpa only [zsmul_eq_mul, Int.cast_natCast, mul_one, zero_add] using hperiod
  rw [intervalIntegral.integral_comp_mul_left g hmR, mul_zero, mul_one, hscaled,
    smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hmR, one_mul]

open Set
noncomputable def goldbach_round_tail (δ x : ℝ) : ℝ :=
  if δ ≤ |x - (round x : ℝ)| then 1 / |x - (round x : ℝ)| ^ 2 else 0

theorem goldbach_round_tail_periodic (δ : ℝ) : Function.Periodic (goldbach_round_tail δ) 1 := by
  intro x
  simp only [goldbach_round_tail, round_add_one, Int.cast_add, Int.cast_one, add_sub_add_right_eq_sub]

theorem goldbach_round_tail_integral (δ : ℝ) (hδ : 0 < δ) (hd : δ ≤ 1 / 2) :
    IntervalIntegrable (goldbach_round_tail δ) volume 0 1 ∧
      (∫ x in (0 : ℝ)..1, goldbach_round_tail δ x) = 2 / δ - 4 := by
  let g := goldbach_round_tail δ
  let f : ℝ → ℝ := fun x => x ^ (-2 : ℤ)
  have hr {x : ℝ} (hx : x ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2)) : round x = 0 :=
    round_eq_zero_iff.2 ⟨hx.1.le, hx.2⟩
  have hpow (x : ℝ) : f x = 1 / |x| ^ 2 := by
    simp [f, zpow_neg, sq_abs, one_div]
  have heL : (Ioo (-(1 / 2 : ℝ)) (-δ)).EqOn g f := by
    intro x hx
    have hxr : x < 1 / 2 := by linarith only [hx.2, hδ]
    have hx0 : x < 0 := by linarith only [hx.2, hδ]
    have hxd : δ ≤ |x| := by rw [abs_of_neg hx0]; linarith only [hx.2]
    rw [hpow]
    simp only [g, goldbach_round_tail, hr ⟨hx.1,hxr⟩, Int.cast_zero, sub_zero, ite_eq_left hxd]
  have heR : (Ioo δ (1 / 2 : ℝ)).EqOn g f := by
    intro x hx
    have hxl : -(1 / 2 : ℝ) < x := by linarith only [hx.1, hδ]
    have hx0 : 0 < x := by linarith only [hx.1, hδ]
    have hxd : δ ≤ |x| := by rw [abs_of_pos hx0]; exact hx.1.le
    rw [hpow]
    simp only [g, goldbach_round_tail, hr ⟨hxl,hx.2⟩, Int.cast_zero, sub_zero, ite_eq_left hxd]
  have heC : (Ioo (-δ) δ).EqOn g (fun _ : ℝ => (0 : ℝ)) := by
    intro x hx
    have hx₁ : -(1 / 2 : ℝ) < x := by linarith only [hd, hx.1]
    have hx₂ : x < (1 / 2 : ℝ) := hx.2.trans_le hd
    have hxd : |x| < δ := abs_lt.2 ⟨hx.1, hx.2⟩
    simp only [g, goldbach_round_tail, hr ⟨hx₁,hx₂⟩, Int.cast_zero, sub_zero,
      ite_eq_right hxd.not_ge]
  have hAway (l r : ℝ) (hab : l ≤ r) (h0 : (0 : ℝ) ∉ Icc l r) (he : (Ioo l r).EqOn g f) :
      IntervalIntegrable g volume l r ∧ (∫ x in l..r, g x) = l⁻¹ - r⁻¹ := by
    have hz : (0 : ℝ) ∉ uIcc l r := by simpa only [uIcc_of_le hab] using h0
    have hIf : IntervalIntegrable f volume l r :=
      intervalIntegral.intervalIntegrable_zpow (n := -2) (Or.inr hz)
    refine ⟨hIf.congr_uIoo (by simpa only [uIoo_of_le hab] using he.symm), ?_⟩
    rw [intervalIntegral.integral_congr_Ioo_of_le hab he]
    change (∫ x in l..r, x ^ (-2 : ℤ)) = _
    rw [integral_zpow (Or.inr ⟨by norm_num, hz⟩)]
    norm_num
    ring
  obtain ⟨hIL,hVL⟩ := hAway (-(1/2)) (-δ) (by linarith only [hd])
    (by intro hz; have hh := (mem_Icc.mp hz).2; linarith only [hh,hδ]) heL
  obtain ⟨hIR,hVR⟩ := hAway δ (1/2) hd
    (by intro hz; have hh := (mem_Icc.mp hz).1; linarith only [hh,hδ]) heR
  have hcent : -δ ≤ δ := by linarith only [hδ]
  have hIC : IntervalIntegrable g volume (-δ) δ :=
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume (-δ) δ).congr_uIoo
      (by simpa only [uIoo_of_le hcent] using heC.symm)
  have hVC : (∫ x in -δ..δ, g x) = 0 := by
    rw [intervalIntegral.integral_congr_Ioo_of_le hcent heC]
    exact intervalIntegral.integral_zero
  have hp := goldbach_round_tail_periodic δ
  have hiBase : IntervalIntegrable g volume (-(1/2)) (1/2) := hIL.trans (hIC.trans hIR)
  have hBaseEnd : -(1/2 : ℝ) + 1 = 1/2 := by norm_num
  have hInt : IntervalIntegrable g volume 0 1 :=
    hp.intervalIntegrable (by norm_num) (t := -(1/2 : ℝ)) (by simpa only [hBaseEnd] using hiBase) 0 1
  refine ⟨hInt, ?_⟩
  have hperiod := hp.intervalIntegral_add_eq (-(1/2 : ℝ)) 0
  change (∫ x in (0 : ℝ)..1, g x) = _
  rw [show (∫ x in (0 : ℝ)..1, g x) = ∫ x in (-(1/2 : ℝ))..(1/2), g x by
      simpa only [hBaseEnd, zero_add] using hperiod.symm,
      ← intervalIntegral.integral_add_adjacent_intervals hIL (hIC.trans hIR),
      ← intervalIntegral.integral_add_adjacent_intervals hIC hIR,
      hVL, hVC, hVR]
  norm_num [inv_neg, div_eq_mul_inv]
  ring

theorem goldbach_truncated_square_comparison (F : ℝ → ℝ) (hF : Continuous F)
    (A : ℝ) (hA : 0 ≤ A) (m : ℕ) (hm : 0 < m) (δ : ℝ)
    (hδ : 0 < δ) (hd : δ ≤ 1 / 2) (s : Set ℝ) (hs : MeasurableSet s)
    (hcut : ∀ t ∈ Icc (0 : ℝ) 1, t ∈ s →
      δ ≤ |(m : ℝ) * t - (round ((m : ℝ) * t) : ℝ)|)
    (hpoint : ∀ t ∈ Icc (0 : ℝ) 1, t ∈ s →
      F t ≤ A * (1 / |(m : ℝ) * t - (round ((m : ℝ) * t) : ℝ)| ^ 2)) :
    (∫ t in (0 : ℝ)..1, s.indicator F t) ≤ A * (2/δ - 4) := by
  let g := goldbach_round_tail δ
  have hi : IntervalIntegrable F volume 0 1 := hF.intervalIntegrable 0 1
  have hiind : IntervalIntegrable (s.indicator F) volume 0 1 := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).2
    exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1 hi).indicator hs
  obtain ⟨hiUnit, hvalue⟩ := goldbach_round_tail_integral δ hδ hd
  have hp := goldbach_round_tail_periodic δ
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hiWide : IntervalIntegrable g volume 0 (m : ℝ) :=
    hp.intervalIntegrable₀ one_ne_zero hiUnit 0 (m : ℝ)
  have hiScaled : IntervalIntegrable (fun t => g ((m : ℝ) * t)) volume 0 1 := by
    simpa only [zero_div, div_self hmR] using hiWide.comp_mul_left (c := (m : ℝ))
  have hnonneg (t : ℝ) : 0 ≤ g t := by dsimp [g, goldbach_round_tail]; split <;> positivity
  calc
    _ ≤ ∫ t in (0 : ℝ)..1, A * g ((m : ℝ)*t) := by
      apply intervalIntegral.integral_mono_on zero_le_one hiind (hiScaled.const_mul A)
      intro t ht
      by_cases hb : t ∈ s
      · rw [indicator_of_mem hb]
        dsimp [g]
        rw [goldbach_round_tail, ite_eq_left (hcut t ht hb)]
        exact hpoint t ht hb
      · rw [indicator_of_notMem hb]
        exact mul_nonneg hA (hnonneg _)
    _ = _ := by
      rw [intervalIntegral.integral_const_mul,
        goldbach_periodic_integral_mul_nat g hp hiUnit m hm, hvalue]

theorem goldbach_geometric_tail_l2 (K m : ℕ) (hm : 0 < m) (δ : ℝ)
    (hδ : 0 < δ) (hd : δ ≤ 1 / 2) (s : Set ℝ) (hs : MeasurableSet s)
    (hcut : ∀ t ∈ Icc (0 : ℝ) 1, t ∈ s →
      δ ≤ |(m : ℝ) * t - (round ((m : ℝ) * t) : ℝ)|) :
    (∫ t in (0 : ℝ)..1, s.indicator (fun t =>
      ‖∑ j ∈ Finset.range K,
        Complex.exp (((2 * Real.pi * (j : ℝ) * ((m : ℝ) * t) : ℝ) : ℂ) * Complex.I)‖ ^ 2) t)
      ≤ 1 / (2 * δ) := by
  let F : ℝ → ℝ := fun t =>
    ‖∑ j ∈ Finset.range K,
      Complex.exp (((2 * Real.pi * (j : ℝ) * ((m : ℝ) * t) : ℝ) : ℂ) * Complex.I)‖ ^ 2
  have hF : Continuous F := by dsimp [F]; fun_prop
  have hI : (∫ t in (0 : ℝ)..1, s.indicator F t) ≤ (1/4 : ℝ) * (2/δ - 4) := by
    apply goldbach_truncated_square_comparison F hF (1/4) (by norm_num) m hm δ hδ hd s hs hcut
    intro t ht hb
    have hpos := hδ.trans_le (hcut t ht hb)
    have hgeo := goldbach_geometric_sum_le_inv_twice_round_distance ((m : ℝ)*t) K hpos
    let d : ℝ := |(m : ℝ)*t - (round ((m : ℝ)*t) : ℝ)|
    have hn : 0 < d := hpos
    calc
      _ ≤ (1 / (2 * d)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hgeo 2
      _ = (1/4 : ℝ) * (1 / d^2) := by
        field_simp [hn.ne']
        ring
  change (∫ t in (0 : ℝ)..1, s.indicator F t) ≤ _
  have hEq : (1/4 : ℝ) * (2/δ - 4) = 1/(2*δ) - 1 := by
    field_simp [hδ.ne']
    ring
  rw [hEq] at hI
  linarith only [hI]

end GoldbachMinorArcAbelTail

section FrontierMedcoreModelHelpers
open scoped BigOperators ComplexConjugate
private noncomputable def frontierMedcorePhase (x : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

theorem frontierMedcoreKernelReflection (n : ℕ) (β : ℝ) :
    let E := fun x : ℝ => Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)
    let K := ∑ k ∈ Finset.range (n+1), E ((k : ℝ) * β)
    K^2 * E (-(n : ℝ) * β) = (Complex.normSq K : ℂ) := by
  dsimp only
  let F : ℕ → ℂ := fun k => frontierMedcorePhase ((k : ℝ) * β)
  change (∑ k ∈ Finset.range (n+1), F k)^2 * frontierMedcorePhase (-(n : ℝ) * β) =
    (Complex.normSq (∑ k ∈ Finset.range (n+1), F k) : ℂ)
  have hPhaseAdd (x y : ℝ) : frontierMedcorePhase (x + y) =
      frontierMedcorePhase x * frontierMedcorePhase y := by
    unfold frontierMedcorePhase
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hPhaseConj (x : ℝ) : conj (frontierMedcorePhase x) = frontierMedcorePhase (-x) := by
    unfold frontierMedcorePhase
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  have hConj : (∑ k ∈ Finset.range (n+1), F k) * frontierMedcorePhase (-(n : ℝ) * β) =
      conj (∑ k ∈ Finset.range (n+1), F k) := by
    rw [Finset.sum_mul, map_sum, ← Finset.sum_range_reflect (fun k => F k * _)]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : k ≤ n := by
      have := Finset.mem_range.mp hk
      omega
    have hIdx : n + 1 - 1 - k = n - k := by omega
    rw [hIdx]
    dsimp only [F]
    rw [← hPhaseAdd, hPhaseConj, Nat.cast_sub hk']
    congr 1
    ring
  rw [pow_two, mul_assoc, hConj, Complex.normSq_eq_conj_mul_self, mul_comm]

end FrontierMedcoreModelHelpers

section GoldbachGRHBandBase
section
open Finset Filter MeasureTheory
namespace GoldbachExplicitModeledMajor
noncomputable section
def phase (x : ℝ) : ℂ := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

end

end GoldbachExplicitModeledMajor

namespace GoldbachExplicitModeledMajor.RamanujanCRT
private def unitsBelow (m : ℕ) := (Finset.range m).filter (fun a => Nat.Coprime a m)

private theorem unitsBelow_card (m : ℕ) : (unitsBelow m).card = m.totient := by
  unfold unitsBelow
  rw [Nat.totient_eq_card_coprime]
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_range]
  exact and_congr_right (fun _ => Nat.coprime_comm)

private noncomputable def phase (m h a : ℕ) : ℂ :=
  Complex.exp (((2 * Real.pi * ((h : ℝ) * a / m) : ℝ) : ℂ) * Complex.I)

private theorem phase_character (m h a : ℕ) [NeZero m] :
    phase m h a = ZMod.stdAddChar ((h : ZMod m) * (a : ZMod m)) := by
  have ch := ZMod.stdAddChar_coe (N := m) ((h * a : ℕ) : ℤ)
  push_cast at ch
  rw [ch]
  unfold phase
  push_cast
  congr 1
  ring

private theorem phase_modulus (m h a : ℕ) [NeZero m] :
    phase m h (a % m) = phase m h a := by
  simp only [phase_character, ZMod.natCast_mod]

private theorem phase_pair (q r h a b : ℕ) (hq : 0 < q) (hr : 0 < r) :
    phase (q*r) h ((r*a + q*b) % (q*r)) = phase q h a * phase r h b := by
  have : NeZero (q*r) := ⟨Nat.ne_of_gt (Nat.mul_pos hq hr)⟩
  rw [phase_modulus]
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  have qnz : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have rnz : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  field_simp

theorem crt :
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let ram := fun (q h : ℕ) => Finset.sum ((Finset.range q).filter (fun a => Nat.Coprime a q)) (fun a => E ((h:ℝ)*(a:ℝ)/(q:ℝ))); ∀ q r h, 0<q → 0<r → Nat.Coprime q r → ram (q*r) h=ram q h*ram r h := by
  dsimp only
  intro q r h hq hr cop
  let combine (x : ℕ × ℕ) := (r*x.1 + q*x.2) % (q*r)
  let pairs := unitsBelow q ×ˢ unitsBelow r
  have member {m a : ℕ} : a ∈ unitsBelow m ↔ a < m ∧ Nat.Coprime a m := by
    simp only [unitsBelow, Finset.mem_filter, Finset.mem_range]
  have maps : pairs.image combine ⊆ unitsBelow (q*r) := by
    intro z hz
    obtain ⟨⟨a,b⟩, hab, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp hab
    apply member.mpr
    refine ⟨Nat.mod_lt _ (Nat.mul_pos hq hr), ?_⟩
    change Nat.gcd ((r*a + q*b) % (q*r)) (q*r) = 1
    rw [← Nat.gcd_rec]
    change Nat.Coprime (q*r) (r*a + q*b)
    apply Nat.coprime_mul_iff_left.mpr
    constructor
    · rw [Nat.coprime_add_mul_left_right]
      exact cop.mul_right (member.mp ha).2.symm
    · rw [add_comm, Nat.coprime_add_mul_left_right]
      exact cop.symm.mul_right (member.mp hb).2.symm
  have injective : Set.InjOn combine (↑pairs) := by
    rintro ⟨a,b⟩ hab ⟨c,d⟩ hcd he
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp hab
    obtain ⟨hc,hd⟩ := Finset.mem_product.mp hcd
    have congruence : r*a + q*b ≡ r*c + q*d [MOD q*r] := he
    apply Prod.ext
    · have hmod := congruence.of_dvd (dvd_mul_right q r)
      have reduced : r*a ≡ r*c [MOD q] := by
        simpa only [Nat.ModEq, Nat.add_mod, Nat.mul_mod_right, add_zero, Nat.mod_mod] using hmod
      exact (Nat.ModEq.cancel_left_of_coprime cop reduced).eq_of_lt_of_lt
        (member.mp ha).1 (member.mp hc).1
    · have hmod := congruence.of_dvd (dvd_mul_left r q)
      have reduced : q*b ≡ q*d [MOD r] := by
        simpa only [Nat.ModEq, Nat.add_mod, Nat.mul_mod_right, zero_add, Nat.mod_mod] using hmod
      exact (Nat.ModEq.cancel_left_of_coprime cop.symm reduced).eq_of_lt_of_lt
        (member.mp hb).1 (member.mp hd).1
  have covers : pairs.image combine = unitsBelow (q*r) := by
    apply Finset.eq_of_subset_of_card_le maps
    rw [Finset.card_image_of_injOn injective, unitsBelow_card, Nat.totient_mul cop]
    simp only [pairs, Finset.card_product, unitsBelow_card]
    exact le_rfl
  change (∑ z ∈ unitsBelow (q*r), phase (q*r) h z) =
    (∑ a ∈ unitsBelow q, phase q h a) * ∑ b ∈ unitsBelow r, phase r h b
  rw [← covers, Finset.sum_image injective, Finset.sum_mul_sum]
  rw [← Finset.sum_product']
  exact Finset.sum_congr rfl (fun x _ => phase_pair q r h x.1 x.2 hq hr)

end GoldbachExplicitModeledMajor.RamanujanCRT

namespace GoldbachExplicitModeledMajor.RamanujanPower
open Finset
theorem primePower :
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let ram := fun (q h : ℕ) => Finset.sum ((Finset.range q).filter (fun a => Nat.Coprime a q)) (fun a => E ((h:ℝ)*(a:ℝ)/(q:ℝ))); ∀ p j h, Nat.Prime p → ram (p^(j+1)) h = (if p^(j+1) ∣ h then ((p^(j+1):ℕ):ℂ) else 0) - (if p^j ∣ h then ((p^j:ℕ):ℂ) else 0) := by
  intro E ram p j h hp
  have full (q : ℕ) (hq : 0 < q) :
      ∑ a ∈ range q, E ((h:ℝ) * a / q) = if q ∣ h then (q:ℂ) else 0 := by
    let : NeZero q := ⟨hq.ne'⟩
    calc
      _ = ∑ x : ZMod q, ZMod.stdAddChar ((h : ZMod q) * x) := by
        apply Finset.sum_bij (fun (a : ℕ) _ => (a : ZMod q))
        · intro a ha
          exact mem_univ _
        · intro a ha b hb hab
          simpa only [ZMod.val_natCast_of_lt (mem_range.mp ha),
            ZMod.val_natCast_of_lt (mem_range.mp hb)] using congrArg ZMod.val hab
        · intro x _
          exact ⟨x.val, mem_range.mpr x.val_lt, ZMod.natCast_zmod_val x⟩
        · intro a _
          have cast_eq : (h : ZMod q) * a = ((h * a : ℕ) : ℤ) := by push_cast; rfl
          rw [cast_eq, ZMod.stdAddChar_coe]
          dsimp [E]
          congr 1
          push_cast
          ring
      _ = _ := by
        by_cases hd : q ∣ h
        · have hz : (h : ZMod q) = 0 := (ZMod.natCast_eq_zero_iff h q).mpr hd
          simp [hd, hz, ZMod.card]
        · have hz : (h : ZMod q) ≠ 0 := fun hz => hd ((ZMod.natCast_eq_zero_iff h q).mp hz)
          rw [ite_eq_right hd]
          exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar q hz)
  let m := p ^ j
  have hm : 0 < m := pow_pos hp.pos _
  let mult := (range m).image (fun b => p * b)
  have hsub : mult ⊆ range (p^(j+1)) := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := mem_image.mp ha
    rw [mem_range, pow_succ']
    exact Nat.mul_lt_mul_of_pos_left (mem_range.mp hb) hp.pos
  have hfilter : (range (p^(j+1))).filter (fun a => Nat.Coprime a (p^(j+1))) =
      range (p^(j+1)) \ mult := by
    rw [sdiff_eq_filter]
    apply filter_congr
    intro a ha
    rw [Nat.coprime_pow_right_iff (Nat.succ_pos j), Nat.coprime_comm, hp.coprime_iff_not_dvd]
    apply not_congr
    constructor
    · rintro ⟨b, rfl⟩
      apply mem_image.mpr
      refine ⟨b, mem_range.mpr ?_, rfl⟩
      rw [mem_range, pow_succ'] at ha
      exact (Nat.mul_lt_mul_left hp.pos).mp ha
    · intro ha'
      obtain ⟨b, _, rfl⟩ := mem_image.mp ha'
      exact dvd_mul_right _ _
  have removed : ∑ a ∈ mult, E ((h:ℝ)*a/(p^(j+1):ℕ)) =
      ∑ b ∈ range m, E ((h:ℝ)*b/m) := by
    rw [show mult = (range m).image (fun b => p * b) from rfl,
      sum_image (mul_right_injective₀ hp.ne_zero).injOn]
    apply sum_congr rfl
    intro b _
    congr 1
    rw [pow_succ']
    push_cast
    dsimp [m]
    push_cast
    field_simp [show (p : ℝ) ≠ 0 by exact_mod_cast hp.ne_zero]
  change ∑ a ∈ (range (p^(j+1))).filter _, E ((h:ℝ)*a/(p^(j+1):ℕ)) = _
  rw [hfilter, ← full _ (pow_pos hp.pos (j+1)), ← full _ hm, ← removed]
  exact eq_sub_of_add_eq (sum_sdiff hsub)

end GoldbachExplicitModeledMajor.RamanujanPower

namespace GoldbachExplicitModeledMajor
open Finset
open scoped ComplexConjugate
noncomputable section
def ram (q h : ℕ) : ℂ :=
  ∑ a ∈ (range q).filter (fun a => a.Coprime q), phase ((h : ℝ) * a / q)

theorem ram_mul {q r : ℕ} (hq : 0 < q) (hr : 0 < r) (hc : q.Coprime r) (h : ℕ) :
    ram (q * r) h = ram q h * ram r h := RamanujanCRT.crt q r h hq hr hc

theorem ram_primePower (p j h : ℕ) (hp : p.Prime) :
    ram (p ^ (j + 1)) h = (if p ^ (j + 1) ∣ h then ((p ^ (j + 1) : ℕ) : ℂ) else 0) -
      (if p ^ j ∣ h then ((p ^ j : ℕ) : ℂ) else 0) := RamanujanPower.primePower p j h hp

theorem ram_one (h : ℕ) : ram 1 h = 1 := by simp [ram, phase]

theorem ram_prime {p : ℕ} (hp : p.Prime) (h : ℕ) :
    ram p h = (if p ∣ h then (p : ℂ) else 0) - 1 := by
  simpa using ram_primePower p 0 h hp

private theorem ram_unit_power {p : ℕ} (hp : p.Prime) (j h : ℕ) (hc : h.Coprime p) :
    ram (p ^ (j + 1)) h = if j = 0 then -1 else 0 := by
  have hd := hp.coprime_iff_not_dvd.mp hc.symm
  have hpow (k : ℕ) : ¬ p ^ (k + 1) ∣ h :=
    fun hh => hd ((dvd_pow_self p (Nat.succ_ne_zero k)).trans hh)
  rw [ram_primePower p j h hp, ite_eq_right (hpow j)]
  cases j with
  | zero => simp
  | succ k => simp [hpow k]

def localCoefficient (p n : ℕ) : ℝ :=
  if p ∣ n then 1 / ((p : ℝ) - 1) else -(1 / ((p : ℝ) - 1) ^ 2)

def coefficient (q n : ℕ) : ℂ := (ram q 1 / (q.totient : ℂ)) ^ 2 * conj (ram q n)

theorem coefficient_one (n : ℕ) : coefficient 1 n = 1 := by simp [coefficient, ram_one]

theorem coefficient_mul {q r : ℕ} (hq : 0 < q) (hr : 0 < r) (hc : q.Coprime r) (n : ℕ) :
    coefficient (q * r) n = coefficient q n * coefficient r n := by
  unfold coefficient
  rw [ram_mul hq hr hc, ram_mul hq hr hc, Nat.totient_mul hc, Nat.cast_mul, map_mul]
  ring

theorem coefficient_prime {p : ℕ} (hp : p.Prime) (n : ℕ) :
    coefficient p n = (localCoefficient p n : ℂ) := by
  have hone : ¬ p ∣ 1 := fun h => hp.ne_one (Nat.dvd_one.mp h)
  have hne : (p : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hp.ne_one)
  rw [coefficient, ram_prime hp, ram_prime hp, ite_eq_right hone, Nat.totient_prime hp,
    Nat.cast_sub hp.one_le, Nat.cast_one]
  by_cases hd : p ∣ n <;> simp [localCoefficient, hd] <;> field_simp

theorem coefficient_higher_power {p : ℕ} (hp : p.Prime) (k n : ℕ) :
    coefficient (p ^ (k + 2)) n = 0 := by
  have h := ram_unit_power hp (k + 1) 1 (by simp)
  simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false] at h
  simp [coefficient, h]

end

end GoldbachExplicitModeledMajor

namespace GoldbachExplicitModeledMajor
open Finset
noncomputable section
theorem coefficient_not_squarefree {q : ℕ} (n : ℕ) (hq : 0 < q)
    (hs : ¬ Squarefree q) : coefficient q n = 0 := by
  induction q using Nat.recOnPosPrimePosCoprime with
  | zero => omega
  | one => exact (hs squarefree_one).elim
  | prime_pow p k hp hk =>
    cases k with
    | zero => omega
    | succ k =>
      cases k with
      | zero => exact (hs (by simpa using hp.squarefree)).elim
      | succ j => exact coefficient_higher_power hp j n
  | coprime a b ha hb hab ia ib =>
    rw [coefficient_mul (by omega) (by omega) hab]
    by_cases h : Squarefree a
    · rw [ib (by omega) (fun h' => hs ((Nat.squarefree_mul hab).mpr ⟨h,h'⟩)), mul_zero]
    · rw [ia (by omega) h, zero_mul]

theorem coefficient_prime_product (n : ℕ) (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime) :
    coefficient (∏ p ∈ s, p) n = ((∏ p ∈ s, localCoefficient p n : ℝ) : ℂ) := by
  induction s using Finset.induction_on with
  | empty => simp [coefficient_one]
  | @insert p s hp ih =>
    have hprime := hs p (mem_insert_self _ _)
    have hs' : ∀ r ∈ s, r.Prime := fun r hr => hs r (mem_insert_of_mem hr)
    have hcop : p.Coprime (∏ r ∈ s, r) := Nat.coprime_prod_right_iff.mpr fun r hr =>
      (Nat.coprime_primes hprime (hs' r hr)).mpr fun he => hp (he ▸ hr)
    rw [prod_insert hp, prod_insert hp, coefficient_mul hprime.pos (prod_pos fun r hr => (hs' r hr).pos) hcop,
      coefficient_prime hprime, ih hs', Complex.ofReal_mul]

end

end GoldbachExplicitModeledMajor

end

section
namespace BandTail
open Finset ArithmeticFunction GoldbachExplicitModeledMajor
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta
noncomputable section
def smooth (n k : ℕ) : Prop := ∀ p ∈ k.primeFactors, p∣n

instance smoothDec (n k : ℕ) : Decidable (smooth n k) := by unfold smooth; infer_instance

def g (n : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun k => if k=0 then 0 else if smooth n k then 1 else 0,by simp⟩

@[simp] theorem g_one (n : ℕ) : g n 1=1 := by simp [g,smooth]

theorem g_mul (n a b : ℕ) : g n (a*b)=g n a*g n b := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  rcases eq_or_ne b 0 with rfl | hb
  · simp
  have hs : smooth n (a*b) ↔ smooth n a ∧ smooth n b := by
    simp only [smooth,Nat.primeFactors_mul ha hb,mem_union]
    constructor
    · intro h; exact ⟨fun p hp => h p (Or.inl hp),fun p hp => h p (Or.inr hp)⟩
    · rintro ⟨x,y⟩ p (h|h)
      · exact x p h
      · exact y p h
  simp only [g,coe_mk, mul_ne_zero ha hb,ha,hb,ite_false]
  by_cases h1 : smooth n a <;> by_cases h2 : smooth n b <;> simp [hs,h1,h2]

theorem g_mult (n : ℕ) : IsMultiplicative (g n) := ⟨g_one n, fun {_ _} _ => g_mul n _ _⟩

theorem g_prime (n p : ℕ) (hp : p.Prime) : g n p=if p∣n then 1 else 0 := by
  simp [g,smooth,hp.ne_zero,hp.primeFactors]

def F (n : ℕ) : ArithmeticFunction ℝ := ⟨fun q => (q:ℝ)*(coefficient q n).re,by simp⟩

theorem coeff_real {q : ℕ} (hq : 0<q) (n : ℕ) : coefficient q n = (((coefficient q n).re:ℝ):ℂ) := by
  by_cases hsf : Squarefree q
  · have he := coefficient_prime_product n q.primeFactors (fun _ hp => Nat.prime_of_mem_primeFactors hp)
    rw [Nat.prod_primeFactors_of_squarefree hsf] at he
    rw [he]; rfl
  · rw [coefficient_not_squarefree n hq hsf]; simp

theorem F_mult (n : ℕ) : IsMultiplicative (F n) := by
  refine ⟨by simp [F,coefficient_one],fun {a b} hab => ?_⟩
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  rcases eq_or_ne b 0 with rfl | hb
  · simp
  have hzero : (coefficient a n).im=0 := by rw [coeff_real ha.bot_lt n]; rfl
  simp [F,coefficient_mul ha.bot_lt hb.bot_lt hab,Complex.mul_re,hzero]
  ring

theorem F_prime (n p : ℕ) (hp : p.Prime) : F n p=(p:ℝ)*localCoefficient p n := by simp [F,coefficient_prime hp]

theorem F_higher (n p j : ℕ) (hp : p.Prime) : F n (p^(j+2))=0 := by simp [F,coefficient_higher_power hp j n]

def invG (n : ℕ) : ArithmeticFunction ℝ := pmul (μ : ArithmeticFunction ℝ) (g n)

def h (n : ℕ) : ArithmeticFunction ℝ := invG n * F n

theorem h_mult (n : ℕ) : IsMultiplicative (h n) :=
  (isMultiplicative_moebius.intCast.pmul (g_mult n)).mul (F_mult n)

theorem inverse_id (n : ℕ) : g n * invG n = 1 := by
  ext k
  have heq : (g n*invG n) k = g n k * (((ζ : ArithmeticFunction ℝ)*μ) k) := by
    simp only [ArithmeticFunction.mul_apply,Finset.mul_sum,invG,pmul_apply]
    apply Finset.sum_congr rfl
    intro ab hab
    have h0 : 0<ab.1 := Nat.pos_of_mem_divisors (Nat.fst_mem_divisors_of_mem_antidiagonal hab)
    have hG : g n k=g n ab.1*g n ab.2 := (Nat.mem_divisorsAntidiagonal.mp hab).1 ▸ g_mul n ab.1 ab.2
    rw [hG]
    simp [zeta_apply,h0.ne']; ring
  rw [heq,coe_zeta_mul_coe_moebius]
  by_cases hk : k=1 <;> simp [ArithmeticFunction.one_apply,hk]

theorem convolution (n : ℕ) : F n = g n*h n := by rw [h,←mul_assoc,inverse_id,one_mul]

theorem h_prime_recurrence (n p j : ℕ) (hp : p.Prime) :
    h n (p^(j+1))=F n (p^(j+1))-g n p*F n (p^j) := by
  let q := p^(j+1)
  have hq : q≠0 := pow_ne_zero _ hp.ne_zero
  let v := fun d : ℕ => invG n d * F n (q/d)
  have hv : h n q = ∑ d ∈ q.divisors, v d := by
    rw [h,ArithmeticFunction.mul_apply,Nat.sum_divisorsAntidiagonal (fun a b : ℕ => invG n a * F n b)]
  have h1 : ({1,p}:Finset ℕ) ⊆ q.divisors := by
    intro a ha
    simp only [mem_insert,mem_singleton] at ha
    rcases ha with rfl | rfl
    · exact Nat.mem_divisors.mpr ⟨one_dvd _,hq⟩
    · exact Nat.mem_divisors.mpr ⟨dvd_pow_self _ (by omega),hq⟩
  have hsum : ∑ d ∈ q.divisors,v d = ∑ d ∈ ({1,p}:Finset ℕ),v d := by
    symm; apply sum_subset h1
    intro d hd hn
    obtain ⟨i,hi,he⟩ := (Nat.dvd_prime_pow hp).mp (Nat.dvd_of_mem_divisors hd)
    by_cases hi0 : i=0
    · exfalso; apply hn; simp [he,hi0]
    by_cases hi1 : i=1
    · exfalso; apply hn; simp [he,hi1]
    have hm : μ d=0 := by rw [he, moebius_apply_prime_pow hp hi0,if_neg hi1]
    simp [v,invG,pmul_apply,intCoe_apply,hm]
  have hdiv : q/p=p^j := by dsimp [q]; rw [pow_succ,Nat.mul_div_cancel _ hp.pos]
  change h n q = _
  rw [hv,hsum,Finset.sum_insert (by simpa using hp.ne_one.symm : (1:ℕ)∉({p}:Finset ℕ)),Finset.sum_singleton]
  simp [v,invG,pmul_apply,intCoe_apply,moebius_apply_prime hp,hdiv,q]
  ring

theorem h_prime (n p : ℕ) (hp : p.Prime) : h n p =
    if p∣n then 1/((p:ℝ)-1) else -(p:ℝ)/((p:ℝ)-1)^2 := by
  have he := h_prime_recurrence n p 0 hp
  have he1 : F n 1=1 := (F_mult n).map_one
  simp only [Nat.zero_add,pow_one,pow_zero,he1,F_prime n p hp,g_prime n p hp,mul_one] at he
  rw [he]; dsimp [localCoefficient]
  have hr1 : (p:ℝ)-1≠0 := by
    have ht : (2:ℝ)≤p := by exact_mod_cast hp.two_le
    linarith
  split_ifs <;> field_simp <;> ring

theorem h_square (n p : ℕ) (hp : p.Prime) : h n (p^2) =
    if p∣n then -(p:ℝ)/((p:ℝ)-1) else 0 := by
  have he := h_prime_recurrence n p 1 hp
  rw [F_higher n p 0 hp,pow_one,g_prime n p hp,F_prime n p hp] at he
  rw [he]; dsimp [localCoefficient]; split_ifs <;> ring

theorem h_cube (n p j : ℕ) (hp : p.Prime) : h n (p^(j+3))=0 := by
  have he := h_prime_recurrence n p (j+2) hp
  rw [F_higher n p j hp,show j+2+1=(j+1)+2 by omega,F_higher n p (j+1) hp] at he
  simpa [show j+2+1=j+3 by omega] using he

end

end BandTail

end

section
namespace BandTail
open Finset GoldbachExplicitModeledMajor MeasureTheory Filter Topology
noncomputable section
theorem weighted_prefix_lower (A B : ℕ) (f w : ℕ → ℝ) (k : ℝ)
    (hab : A ≤ B) (hk : 0 ≤ k) (hw : ∀ i ≥ A,0 ≤ w i) (hm : ∀ i ≥ A,w (i+1) ≤ w i)
    (hp : ∀ i ≥ A,i ≤ B → -k ≤ ∑ j ∈ Ioc A i,f j) :
    -(k*w A) ≤ ∑ j ∈ Ioc A B,f j*w j := by
  have strong (i : ℕ) (hi : A ≤ i) (hiB : i ≤ B) :
      w i*((∑ j ∈ Ioc A i,f j)+k) ≤ (∑ j ∈ Ioc A i,f j*w j)+k*w A := by
    induction i,hi using Nat.le_induction with
    | base => simp [mul_comm]
    | succ i hi ih =>
      have h := ih (by omega)
      have hmono := hm i hi
      have hx := hp i hi (by omega)
      rw [sum_Ioc_succ_top hi,sum_Ioc_succ_top hi]
      nlinarith only [h,mul_nonneg (sub_nonneg.mpr hmono) (show 0 ≤ (∑ j ∈ Ioc A i,f j)+k by linarith)]
  have h := strong B hab le_rfl
  have v := hp B hab le_rfl
  nlinarith only [h,mul_nonneg (hw B hab) (show 0 ≤ (∑ j ∈ Ioc A B, f j)+k by linarith)]

end

end BandTail

end

section
namespace BandTail
open Finset ArithmeticFunction
open scoped ArithmeticFunction.zeta
noncomputable section
def w (n : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun d => |h n d|/(d:ℝ)^(3/4:ℝ),by simp⟩

def z (n : ℕ) : ArithmeticFunction ℝ := ⟨fun d => h n d/(d:ℝ),by simp⟩

theorem w_mult (n : ℕ) : IsMultiplicative (w n) := by
  refine ⟨by simp [w,(h_mult n).map_one],fun {a b} hab => ?_⟩
  simp only [w,coe_mk,(h_mult n).map_mul_of_coprime hab,Nat.cast_mul,abs_mul,Real.mul_rpow (Nat.cast_nonneg a) (Nat.cast_nonneg b)]
  ring

theorem z_mult (n : ℕ) : IsMultiplicative (z n) := by
  refine ⟨by simp [z,(h_mult n).map_one],fun {a b} hab => ?_⟩
  simp [z,(h_mult n).map_mul_of_coprime hab]; ring

theorem w_nonneg (n d : ℕ) : 0≤w n d := by dsimp [w]; positivity

theorem localReduce (f : ℕ → ℝ) (hf : ∀ j, f (j+3)=0) (k : ℕ) :
    (∑ i ∈ range (k+1), f i)=f 0 + (if k≥1 then f 1 else 0) + (if k≥2 then f 2 else 0) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ,ih]
    rcases k with _ | _ | j
    · simp
    · simp
    · simp [hf,show 2≤j+1+1 by omega,show 2≤j+1+1+1 by omega]

theorem wLocal (p n k : ℕ) (hp : p.Prime) :
    (∑ d ∈ (p^k).divisors, w n d) ≤ 1+6/((p:ℝ)^(3/2:ℝ)) := by
  have hp2 : (2:ℝ)≤p := by exact_mod_cast hp.two_le
  have hp1 : 0<(p:ℝ)-1 := by linarith
  have hpr : 0<(p:ℝ) := by linarith
  have hW1 : w n p ≤ 4/((p:ℝ)^(3/2:ℝ)) := by
    have h₁ : |h n p| ≤ 4/(p:ℝ) := by
      rw [h_prime n p hp]
      split_ifs
      · rw [abs_of_nonneg (by positivity)]; field_simp; linarith
      · rw [abs_div,abs_neg,abs_of_nonneg hpr.le,abs_of_nonneg (sq_nonneg _)]
        field_simp
        nlinarith [mul_nonneg (show 0≤(p:ℝ)-2 by linarith) (show 0≤3*(p:ℝ)-2 by linarith)]
    dsimp [w]
    calc
      _ ≤ (4/(p:ℝ))/((p:ℝ)^(3/4:ℝ)) := div_le_div_of_nonneg_right h₁ (by positivity)
      _ = 4/(p:ℝ)^(1+(3/4):ℝ) := by rw [Real.rpow_add hpr,Real.rpow_one,div_div]
      _ ≤ _ := by apply div_le_div_of_nonneg_left (by norm_num) (by positivity); exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hW2 : w n (p^2) ≤ 2/(p:ℝ)^(3/2:ℝ) := by
    have he : |h n (p^2)| ≤ 2 := by
      rw [h_square n p hp]; split_ifs
      · rw [abs_div,abs_neg,abs_of_nonneg hpr.le,abs_of_nonneg hp1.le]; apply (div_le_iff₀ hp1).mpr; linarith
      · norm_num
    change |h n (p^2)| / ((p^2:ℕ):ℝ)^(3/4:ℝ) ≤ _
    rw [Nat.cast_pow,←Real.rpow_natCast_mul hpr.le,show (↑(2:ℕ):ℝ)*(3/4)=3/2 by norm_num]
    exact div_le_div_of_nonneg_right he (by positivity)
  rw [Nat.sum_divisors_prime_pow hp,localReduce (fun j => w n (p^j)) (fun j => by simp [w,h_cube n p j hp])]
  simp only [pow_zero,pow_one,(w_mult n).map_one]
  simp only [div_eq_mul_inv] at hW1 hW2 ⊢
  split_ifs <;> linarith [w_nonneg n p,w_nonneg n (p^2)]

theorem zLocal (p n k : ℕ) (hp : p.Prime) : 0≤∑ d ∈ (p^k).divisors,z n d := by
  rw [Nat.sum_divisors_prime_pow hp,localReduce (fun j => z n (p^j)) (fun j => by simp [z,h_cube n p j hp])]
  simp only [pow_zero,pow_one,(z_mult n).map_one]
  have h2 : (2:ℝ)≤p := by exact_mod_cast hp.two_le
  have hp1 : 0<(p:ℝ)-1 := by linarith
  have hpr : 0<(p:ℝ) := by linarith
  have hsq : 1≤((p:ℝ)-1)^2 := by nlinarith [mul_nonneg (show 0≤(p:ℝ)-2 by linarith) (show 0≤(p:ℝ) by linarith)]
  simp only [z,coe_mk,h_prime n p hp,h_square n p hp,Nat.cast_pow]
  by_cases hpn : p∣n
  · simp only [hpn,ite_true]
    split_ifs with hk hk2
    · field_simp; nlinarith [mul_pos hpr hp1]
    · positivity
    · omega
    · norm_num
  · simp only [hpn,ite_false,zero_div,ite_self,add_zero]
    split_ifs
    · field_simp; nlinarith [mul_le_mul_of_nonneg_right hsq hpr.le]
    · norm_num

def universal : ℝ := Real.exp (6*∑' j : ℕ, ((j:ℝ)^(3/2:ℝ))⁻¹)

theorem uniformDivisors (n M : ℕ) (hM : 0<M) :
    (∑ d ∈ M.divisors, w n d) ≤ universal := by
  let A : ArithmeticFunction ℝ := w n * (ζ : ArithmeticFunction ℝ)
  have hA : IsMultiplicative A := (w_mult n).mul isMultiplicative_zeta.natCast
  have he (m : ℕ) : A m = ∑ d ∈ m.divisors,w n d := coe_mul_zeta_apply
  have hprod := hA.multiplicative_factorization A hM.ne'
  rw [he] at hprod
  rw [hprod,Finsupp.prod]
  calc
    _ ≤ ∏ p ∈ M.factorization.support, Real.exp (6/((p:ℝ)^(3/2:ℝ))) := by
      refine Finset.prod_le_prod₀ (fun p hp => ?_) (fun p hp => ?_)
      · rw [he]; exact sum_nonneg fun d _ => w_nonneg n d
      · rw [he]
        have hh : p ∈ M.primeFactors := M.support_factorization ▸ hp
        exact (wLocal p n _ (Nat.prime_of_mem_primeFactors hh)).trans (by linarith [Real.add_one_le_exp (6/((p:ℝ)^(3/2:ℝ)))])
    _ ≤ universal := by
      rw [←Real.exp_sum,universal]
      apply Real.exp_le_exp.mpr
      simp_rw [div_eq_mul_inv,←mul_sum]
      apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ)≤6)
      exact (Real.summable_nat_rpow_inv.mpr (by norm_num : (1:ℝ)<3/2)).sum_le_tsum _ (by intro _ _; positivity)

theorem signedDivisors (n M : ℕ) (hM : 0<M) :
    0 ≤ ∑ d ∈ M.divisors, z n d := by
  let A : ArithmeticFunction ℝ := z n * (ζ : ArithmeticFunction ℝ)
  have hA : IsMultiplicative A := (z_mult n).mul isMultiplicative_zeta.natCast
  have he (m : ℕ) : A m = ∑ d ∈ m.divisors,z n d := coe_mul_zeta_apply
  have hh := hA.multiplicative_factorization A hM.ne'
  rw [he] at hh
  rw [hh,Finsupp.prod]
  apply Finset.prod_nonneg
  intro p hp
  rw [he]
  exact zLocal p n _ (Nat.prime_of_mem_primeFactors (M.support_factorization ▸ hp))

theorem prefixDiv (J : ℕ) : Icc 1 J ⊆ J.factorial.divisors := by
  intro d hd
  obtain ⟨hd1, hdJ⟩ := mem_Icc.mp hd
  exact Nat.mem_divisors.mpr ⟨Nat.dvd_factorial hd1 hdJ,J.factorial_pos.ne'⟩

theorem uniformPrefix (n J : ℕ) : (∑ d ∈ Icc 1 J, w n d)≤universal :=
  (sum_le_sum_of_subset_of_nonneg (prefixDiv J) (fun d _ _ => w_nonneg n d)).trans
    (uniformDivisors n _ J.factorial_pos)

theorem tailTerm (n J d : ℕ) (hJ : 0<J) (hJd : J≤d) :
    |z n d| ≤ w n d / ((J:ℝ)^(1/4:ℝ)) := by
  have hd : 0<(d:ℝ) := by exact_mod_cast hJ.trans_le hJd
  have hJr : 0<(J:ℝ) := by exact_mod_cast hJ
  have he : (d:ℝ)^(3/4:ℝ)*(d:ℝ)^(1/4:ℝ)=d := by
    rw [←Real.rpow_add hd,show (3/4:ℝ)+1/4=1 by norm_num,Real.rpow_one]
  change |h n d / (d:ℝ)| ≤ |h n d| / _ / _
  rw [abs_div,abs_of_pos hd,div_div]
  apply div_le_div_of_nonneg_left (abs_nonneg _) (mul_pos (Real.rpow_pos_of_pos hd _) (Real.rpow_pos_of_pos hJr _))
  apply le_trans _ he.le
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) (by exact_mod_cast hJd) (by norm_num)) (by positivity)

theorem uniformTail (n J : ℕ) (s : Finset ℕ) (hJ : 0<J) (hs : ∀ d ∈ s,J≤d) :
    (∑ d ∈ s, |z n d|) ≤ universal / (J:ℝ)^(1/4:ℝ) := by
  have hb : s⊆Icc 1 (s.sup id) := by
    intro d hd
    exact mem_Icc.mpr ⟨by have := hs d hd; omega, le_sup (f:=id) hd⟩
  calc
    _ ≤ ∑ d ∈ s, w n d / (J:ℝ)^(1/4:ℝ) := sum_le_sum fun d hd => tailTerm n J d hJ (hs d hd)
    _ = _ := (sum_div _ _ _).symm
    _ ≤ _ := div_le_div_of_nonneg_right ((sum_le_sum_of_subset_of_nonneg hb (fun d _ _ => w_nonneg n d)).trans (uniformPrefix n _)) (by positivity)

theorem signedPrefix (n J : ℕ) (hJ : 0<J) :
    -(universal / (J:ℝ)^(1/4:ℝ)) ≤ ∑ d ∈ Icc 1 J, z n d := by
  have hu := uniformTail n J (J.factorial.divisors \ Icc 1 J) hJ (by
    intro d hd
    obtain ⟨hd,hd'⟩ := mem_sdiff.mp hd
    have hpos := Nat.pos_of_mem_divisors hd
    simp only [mem_Icc,not_and] at hd'
    omega)
  have hh := signedDivisors n J.factorial J.factorial_pos
  rw [←sum_sdiff (s₁:=Icc 1 J) (s₂:=J.factorial.divisors) (prefixDiv J)] at hh
  have ht := sum_le_sum (s:=J.factorial.divisors \ Icc 1 J) (fun d _ => le_abs_self (z n d))
  linarith

end

end BandTail

end

section
namespace BandTail
open Finset ArithmeticFunction
noncomputable section
def gSum (n X : ℕ) : ℝ := ∑ k ∈ Icc 1 X, g n k

def gAvg (n X : ℕ) : ℝ := gSum n X / X

def fSum (n X : ℕ) : ℝ := ∑ k ∈ Icc 1 X, F n k

theorem g_sum_bounds (n X : ℕ) : 0≤gSum n X ∧ gSum n X≤X := by
  constructor
  · apply sum_nonneg
    intro k hk
    simp [g]; split_ifs <;> norm_num
  · calc
      _ ≤ ∑ k ∈ Icc 1 X,(1:ℝ) := by
        apply sum_le_sum
        intro k hk
        simp [g]; split_ifs <;> norm_num
      _ = _ := by simp

theorem g_avg_bounds (n X : ℕ) : 0≤gAvg n X ∧ gAvg n X≤1 := by
  have hb := g_sum_bounds n X
  exact ⟨div_nonneg hb.1 (Nat.cast_nonneg _),div_le_one_of_le₀ hb.2 (Nat.cast_nonneg _)⟩

theorem fSum_convolution (n X : ℕ) :
    fSum n X = ∑ d ∈ Icc 1 X,h n d * gSum n (X/d) := by
  classical
  let S := Icc 1 X
  let f := fun v : ℕ × ℕ => h n v.1 * g n v.2
  have hf (q : ℕ) (hq : q ∈ S) :
      q.divisorsAntidiagonal = (S ×ˢ S).filter (fun ab : ℕ × ℕ => ab.1*ab.2=q) := by
    obtain ⟨hq0,hqQ⟩ := mem_Icc.mp hq
    ext ab
    constructor
    · intro hab
      have hm (a : ℕ) (ha : a ∈ q.divisors) : a ∈ S :=
        mem_Icc.mpr ⟨Nat.pos_of_mem_divisors ha,(Nat.le_of_dvd hq0 (Nat.dvd_of_mem_divisors ha)).trans hqQ⟩
      exact mem_filter.mpr ⟨mem_product.mpr ⟨hm _ (Nat.fst_mem_divisors_of_mem_antidiagonal hab),
        hm _ (Nat.snd_mem_divisors_of_mem_antidiagonal hab)⟩,(Nat.mem_divisorsAntidiagonal.mp hab).1⟩
    · intro hh; exact Nat.mem_divisorsAntidiagonal.mpr ⟨(mem_filter.mp hh).2,by omega⟩
  calc
    _ = ∑ q ∈ S,∑ v ∈ q.divisorsAntidiagonal,f v := by
      simp [fSum,S,convolution n,mul_comm (g n) (h n),ArithmeticFunction.mul_apply,f]
    _ = ∑ q ∈ S, ∑ v ∈ (S ×ˢ S).filter (fun ab : ℕ × ℕ => ab.1*ab.2=q), f v :=
      sum_congr rfl (fun q hq => by rw [hf q hq])
    _ = ∑ v ∈ (S ×ˢ S).filter (fun ab : ℕ × ℕ => ab.1*ab.2 ∈ S), f v :=
      sum_fiberwise_eq_sum_filter _ _ _ _
    _ = _ := by
      rw [sum_filter,sum_product]
      apply sum_congr rfl
      intro d hd
      have hd0 := (mem_Icc.mp hd).1
      have hkd : (S.filter fun k => d*k∈S)=Icc 1 (X/d) := by
        ext k
        simp only [S,mem_filter,mem_Icc]
        constructor
        · rintro ⟨⟨hk,_⟩,_,hdk⟩
          exact ⟨hk,(Nat.le_div_iff_mul_le hd0).mpr (by simpa [mul_comm] using hdk)⟩
        · rintro ⟨hk,hkx⟩
          exact ⟨⟨hk,hkx.trans (Nat.div_le_self _ _)⟩,Nat.mul_pos hd0 hk, by simpa [mul_comm] using (Nat.le_div_iff_mul_le hd0).mp hkx⟩
      simp only [f,gSum,mul_sum]
      rw [←sum_filter,hkd]

theorem prefix_split (f : ℕ→ℝ) {J X : ℕ} (hJX : J≤X) :
    (∑ d ∈ Icc 1 X,f d)=(∑ d ∈ Icc 1 J,f d)+(∑ d ∈ Ioc J X,f d) := by
  have he : Icc 1 X=Icc 1 J ∪ Ioc J X := by ext k; simp only [mem_union,mem_Icc,mem_Ioc]; omega
  rw [he,sum_union (by rw [Finset.disjoint_left]; intro k hk hj; have := (mem_Icc.mp hk).2; have := (mem_Ioc.mp hj).1; omega)]

def scaleFactor (X d : ℕ) : ℝ := (d:ℝ)*(X/d:ℕ)/X

theorem scale_bounds (X d : ℕ) (hX : 0<X) (hd : 0<d) :
    0≤ scaleFactor X d ∧ scaleFactor X d ≤ 1 ∧ 1-scaleFactor X d ≤ (d:ℝ)/X := by
  have hx : 0<(X:ℝ) := by exact_mod_cast hX
  have hx0 : (d:ℝ)*(X/d:ℕ) ≤ X := by exact_mod_cast Nat.mul_div_le X d
  have hx1 : (X:ℝ) < (d:ℝ)*((X/d:ℕ)+1:ℝ) := by exact_mod_cast Nat.lt_mul_div_succ X hd
  unfold scaleFactor
  refine ⟨by positivity,(div_le_iff₀ hx).mpr (by linarith),?_⟩
  rw [sub_div' hx.ne',div_le_div_iff_of_pos_right hx]
  linarith

theorem scaled_piece (n X d : ℕ) (hd : 0<d) :
    h n d * gSum n (X/d) / X = z n d * (scaleFactor X d * gAvg n (X/d)) := by
  have hdr : (d:ℝ)≠0 := by exact_mod_cast hd.ne'
  by_cases hy : X/d=0
  · simp [gSum,gAvg,scaleFactor,hy]
  · have hyr : ((X/d:ℕ):ℝ)≠0 := by exact_mod_cast hy
    simp only [z,coe_mk,scaleFactor,gAvg]
    field_simp

theorem piece_approx (n X d : ℕ) (hX : 0<X) (hd : 0<d) (t e : ℝ)
    (he : |gAvg n (X/d)-t|≤e) (hdX : (d:ℝ)/X≤e) :
    |h n d * gSum n (X/d) / X - z n d * t| ≤ |z n d| *(2*e) := by
  obtain ⟨_,hs,hs'⟩ := scale_bounds X d hX hd
  have hg := g_avg_bounds n (X/d)
  have hc : |scaleFactor X d * gAvg n (X/d)-gAvg n (X/d)| ≤ e := by
    rw [←sub_one_mul,abs_mul,abs_of_nonpos (sub_nonpos.mpr hs),abs_of_nonneg hg.1]
    calc
      _ ≤ -(scaleFactor X d-1)*1 := mul_le_mul_of_nonneg_left hg.2 (by linarith)
      _ ≤ e := by linarith
  rw [scaled_piece n X d hd,←mul_sub,abs_mul]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  exact (abs_sub_le _ (gAvg n (X/d)) _).trans (by linarith)

theorem dyadic_approx (n X J : ℕ) (hX : 0<X) (hJ : 0<J) (hJX : J≤X) (t e : ℝ) (he : 0≤e)
    (hne : ∀ d ∈ Icc 1 J,|gAvg n (X/d)-t|≤e) (hJr : (J:ℝ)/X ≤ e) :
    |fSum n X / X - (∑ d ∈ Icc 1 J,z n d)*t| ≤
      universal*(2*e)+universal/(J:ℝ)^(1/4:ℝ) := by
  let a := fun d => h n d * gSum n (X/d) / X
  have hsmall : |∑ d ∈ Icc 1 J,(a d-z n d*t)|≤universal*(2*e) := by
    apply (abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ d ∈ Icc 1 J, |z n d| *(2*e) := by
        refine sum_le_sum fun d hd => piece_approx n X d hX (mem_Icc.mp hd).1 t e (hne _ hd) ?_
        exact (div_le_div_of_nonneg_right (by exact_mod_cast (mem_Icc.mp hd).2) (Nat.cast_nonneg _)).trans hJr
      _ = _ := (sum_mul _ _ _).symm
      _ ≤ _ := by
        have hu := uniformTail n 1 (Icc 1 J) (by decide) (fun d hd => (mem_Icc.mp hd).1)
        norm_num at hu
        exact mul_le_mul_of_nonneg_right hu (by positivity)
  have hlarge : |∑ d ∈ Ioc J X,a d| ≤ universal/(J:ℝ)^(1/4:ℝ) := by
    apply (abs_sum_le_sum_abs _ _).trans
    apply le_trans _ (uniformTail n J (Ioc J X) hJ (fun d hd => (mem_Ioc.mp hd).1.le))
    apply sum_le_sum
    intro d hd
    have hd0 : 0<d := hJ.trans (mem_Ioc.mp hd).1
    obtain ⟨hs,hs',_⟩ := scale_bounds X d hX hd0
    have hg := g_avg_bounds n (X/d)
    dsimp only [a]; rw [scaled_piece n X d hd0,abs_mul,abs_of_nonneg (mul_nonneg hs hg.1)]
    exact mul_le_of_le_one_right (abs_nonneg _) (mul_le_one₀ hs' hg.1 hg.2)
  have htotal : fSum n X / X = (∑ d ∈ Icc 1 J,a d)+(∑ d ∈ Ioc J X,a d) := by
    rw [fSum_convolution,sum_div]
    exact prefix_split a hJX
  rw [htotal,sum_mul]
  rw [show (∑ d ∈ Icc 1 J,a d)+(∑ d ∈ Ioc J X,a d)-(∑ d ∈ Icc 1 J,z n d*t)=
      (∑ d ∈ Icc 1 J,(a d-z n d*t))+(∑ d ∈ Ioc J X,a d) by rw [sum_sub_distrib]; ring]
  exact (abs_add_le _ _).trans (add_le_add hsmall hlarge)

end

end BandTail

end

section
namespace GoldbachModelMean
open Finset Filter Topology
private def modProd (s : Finset Nat.Primes) : ℕ := ∏ p ∈ s, (p:ℕ)

private theorem modProd_pos (s : Finset Nat.Primes) : 0 < modProd s :=
  Finset.prod_pos (fun p _ => p.property.pos)

private theorem totientProd (s : Finset Nat.Primes) :
    ((modProd s).totient:ℝ)*(1+∑ p ∈ s, 1/(p:ℝ)) ≤ modProd s := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [modProd]
  | @insert p s hps ih =>
    have hcop : (p:ℕ).Coprime (modProd s) := by
      apply Nat.coprime_prod_right_iff.mpr
      intro q hq
      apply (Nat.coprime_primes p.property q.property).mpr
      intro h
      exact hps ((Subtype.ext h : p=q) ▸ hq)
    have heq : modProd (insert p s) = (p:ℕ)*modProd s := Finset.prod_insert hps
    have hp : (1:ℕ)≤p.val := p.property.one_lt.le
    have hp' : (0:ℝ)<p := by exact_mod_cast p.property.pos
    have hsum : 0 ≤ ∑ q ∈ s, (1:ℝ)/(q:ℝ) := sum_nonneg fun q _ => by positivity
    rw [heq,Nat.totient_mul hcop,Nat.totient_prime p.property,Finset.sum_insert hps]
    push_cast [Nat.cast_sub hp]
    calc
      _ ≤ (p:ℝ)*(((modProd s).totient:ℝ)*(1+∑ q ∈ s, 1/(q:ℝ))) := by
        have : ((p:ℝ)-1)*(1+(1/(p:ℝ)+∑ q ∈ s, 1/(q:ℝ))) ≤ (p:ℝ)*(1+∑ q ∈ s, 1/(q:ℝ)) := by
          field_simp
          nlinarith [mul_nonneg hp'.le hsum]
        nlinarith only [mul_le_mul_of_nonneg_right this (Nat.cast_nonneg (modProd s).totient (α:=ℝ))]
      _ ≤ _ := mul_le_mul_of_nonneg_left ih hp'.le

theorem exists_thin_modulus (e : ℝ) (he : 0<e) :
    ∃ D : ℕ, 0<D ∧ (D.totient:ℝ)/(D:ℝ)<e := by
  classical
  have hs : ∃ s : Finset Nat.Primes, (1/e:ℝ) < ∑ p ∈ s, 1/(p:ℝ) := by
    by_contra! h
    exact Nat.Primes.not_summable_one_div (summable_of_sum_le (fun p => by positivity) h)
  obtain ⟨s,hs⟩ := hs
  refine ⟨modProd s,modProd_pos s,(div_lt_iff₀ (by exact_mod_cast modProd_pos s)).mpr ?_⟩
  have h := totientProd s
  have ht : (0:ℝ) < (modProd s).totient := by exact_mod_cast Nat.totient_pos.mpr (modProd_pos s)
  have h1 := (div_lt_iff₀ he).mp hs
  nlinarith only [mul_le_mul_of_nonneg_right h he.le,
    mul_lt_mul_of_pos_right h1 ht,mul_pos he ht]

def fewFactors (k X : ℕ) : Finset ℕ :=
  (range X).filter fun n => 0 < n ∧ n.primeFactorsList.length ≤ k

private theorem few_step (k X D : ℕ) (hD : 0<D) :
    (fewFactors (k+1) X).card ≤ D.totient*(X/D+1)+(D+1)*(fewFactors k X).card := by
  classical
  let R := (range X).filter fun n => D.Coprime n
  let cover := (range (D+1)).biUnion fun p => (fewFactors k X).image fun y => p*y
  have hsub : fewFactors (k+1) X ⊆ R ∪ cover := by
    intro x hx
    obtain ⟨hxX,hxp,hxk⟩ := mem_filter.mp hx
    by_cases hc : D.Coprime x
    · exact mem_union_left _ (mem_filter.mpr ⟨hxX,hc⟩)
    obtain ⟨p,hp,hpd,hpx⟩ := Nat.Prime.not_coprime_iff_dvd.mp hc
    obtain ⟨y,rfl⟩ := hpx
    have hy : y ≠ 0 := by intro hz; simp [hz] at hxp
    have hlen := (Nat.perm_primeFactorsList_mul hp.ne_zero hy).length_eq
    simp [Nat.primeFactorsList_prime hp] at hlen
    have hyX : y < X := lt_of_le_of_lt (by simpa [Nat.mul_comm] using Nat.le_mul_of_pos_left y hp.pos) (mem_range.mp hxX)
    exact mem_union_right _ (mem_biUnion.mpr ⟨p,mem_range.mpr (by have := Nat.le_of_dvd hD hpd; omega),
      mem_image.mpr ⟨y,mem_filter.mpr ⟨mem_range.mpr hyX,by omega,by omega⟩,rfl⟩⟩)
  have hR : R.card ≤ D.totient*(X/D+1) := by
    simpa only [R,zero_add,← range_eq_Ico] using Nat.Ico_filter_coprime_le 0 X hD.ne'
  have hc : cover.card ≤ (D+1)*(fewFactors k X).card := calc
    _ ≤ ∑ p ∈ range (D+1), ((fewFactors k X).image fun y => p*y).card := card_biUnion_le
    _ ≤ ∑ _ ∈ range (D+1), (fewFactors k X).card := by exact Finset.sum_le_sum (fun p _ => card_image_le)
    _ = _ := by simp
  exact (card_le_card hsub).trans ((card_union_le _ _).trans (Nat.add_le_add hR hc))

theorem fewFactors_eventually (k : ℕ) (e : ℝ) (he : 0<e) :
    ∀ᶠ X : ℕ in atTop, ((fewFactors k X).card:ℝ) ≤ e*X := by
  induction k generalizing e with
  | zero =>
    filter_upwards [(tendsto_natCast_atTop_atTop (R:=ℝ)).eventually_ge_atTop (1/e)] with X hX
    have hsub : fewFactors 0 X ⊆ {1} := by
      intro x hx
      obtain ⟨_,hp,hl⟩ := mem_filter.mp hx
      have hn := (Nat.primeFactorsList_eq_nil x).mp (List.length_eq_zero_iff.mp (by omega))
      simp only [mem_singleton]
      omega
    have hc : (fewFactors 0 X).card ≤ 1 := by simpa using card_le_card hsub
    change 1/e ≤ (X:ℝ) at hX
    have hh := (div_le_iff₀ he).mp hX
    exact (by exact_mod_cast hc : ((fewFactors 0 X).card:ℝ) ≤ 1) |>.trans (by linarith)
  | succ k ih =>
    obtain ⟨D,hD,hphi⟩ := exists_thin_modulus (e/4) (by positivity)
    have hD' : (0:ℝ)<D := by exact_mod_cast hD
    filter_upwards [ih (e/(4*(D+1))) (by positivity),
      (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually_ge_atTop (4*(D.totient:ℝ)/e)] with X hprev hlarge
    change 4*(D.totient:ℝ)/e ≤ X at hlarge
    have hr := (div_le_iff₀ he).mp hlarge
    have hp := (div_lt_iff₀ hD').mp hphi
    have hquot : ((X/D:ℕ):ℝ) ≤ (X:ℝ)/D := by
      apply (le_div_iff₀ hD').mpr
      exact_mod_cast Nat.div_mul_le_self X D
    have h := few_step k X D hD
    have h' : ((fewFactors (k+1) X).card:ℝ) ≤ D.totient*(((X/D:ℕ):ℝ)+1)+((D:ℝ)+1)*(fewFactors k X).card := by exact_mod_cast h
    have hf : ((D:ℝ)+1)*((fewFactors k X).card:ℝ) ≤ (e/4)*X := by
      calc
        _ ≤ ((D:ℝ)+1)*(e/(4*(D+1))*X) := mul_le_mul_of_nonneg_left hprev (by positivity)
        _ = _ := by field_simp
    have hg : (D.totient:ℝ)*((X/D:ℕ):ℝ) ≤ (e/4)*X := calc
      _ ≤ (D.totient:ℝ)*((X:ℝ)/D) := mul_le_mul_of_nonneg_left hquot (by positivity)
      _ = ((D.totient:ℝ)/D)*X := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hphi.le (by positivity)
    nlinarith only [h',hf,hg,hr,mul_nonneg he.le (Nat.cast_nonneg X (α:=ℝ))]

end GoldbachModelMean

end

section
noncomputable section
namespace GoldbachModelMean.Brun
open Finset Filter
def product (s : Finset ℕ) := ∏ p ∈ s, p

def hits (P : Finset ℕ) (m : ℕ) := P.filter (fun p => p ∣ m)

def count (P : Finset ℕ) (X : ℕ) : ℝ := ∑ m ∈ Ioc 0 X, if (hits P m).card=0 then 1 else 0

def harmonic (P : Finset ℕ) : ℝ := ∑ p ∈ P, 1/(p:ℝ)

def divisCount (P : Finset ℕ) (j X : ℕ) : ℝ :=
  ∑ s ∈ P.powersetCard j, ((X / product s : ℕ):ℝ)

def trunc (P : Finset ℕ) (r X : ℕ) : ℝ :=
  ∑ j ∈ range (r+1), (-1:ℝ)^j*divisCount P j X

lemma prodPos (s : Finset ℕ) (hp : ∀ p ∈ s, p.Prime) : 0<product s :=
  prod_pos (fun p h => (hp p h).pos)

lemma prodDvd (s : Finset ℕ) (hp : ∀ p ∈ s, p.Prime) (m : ℕ) :
    product s ∣ m ↔ ∀ p ∈ s, p ∣ m := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [product]
  | @insert p s hps ih =>
    have hp' := hp p (mem_insert_self _ _)
    have hs := fun q (hq : q∈s) => hp q (mem_insert_of_mem hq)
    have hc : p.Coprime (product s) := Nat.coprime_prod_right_iff.mpr (fun q hq =>
      (Nat.coprime_primes hp' (hs q hq)).mpr fun he => hps (he ▸ hq))
    rw [product,prod_insert hps,forall_mem_insert]
    change p*product s ∣ m ↔ _
    exact ⟨fun h => ⟨(dvd_mul_right p _).trans h,(ih hs).mp ((dvd_mul_left (product s) p).trans h)⟩,
      fun h => hc.mul_dvd_of_dvd_of_dvd h.1 ((ih hs).mpr h.2)⟩

lemma omegaProd (s : Finset ℕ) (hp : ∀ p ∈ s, p.Prime) : (product s).primeFactorsList.length=s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [product]
  | @insert p s hps ih =>
    have hp' := hp p (mem_insert_self _ _)
    have hs := fun q (hq : q∈s) => hp q (mem_insert_of_mem hq)
    have he := (Nat.perm_primeFactorsList_mul hp'.ne_zero (prodPos s hs).ne').length_eq
    change (∏ q ∈ insert p s,q).primeFactorsList.length=_
    rw [prod_insert hps,card_insert_of_notMem hps]
    change (p*product s).primeFactorsList.length=_
    simpa [Nat.primeFactorsList_prime hp',ih hs,Nat.add_comm] using he

theorem divisAsChoose (P : Finset ℕ) (hp : ∀ p∈P, p.Prime) (j X : ℕ) :
    divisCount P j X = ∑ m ∈ Ioc 0 X, (((hits P m).card.choose j:ℕ):ℝ) := by
  classical
  have hs (m : ℕ) :
      (P.powersetCard j).filter (fun s => product s ∣ m) = (hits P m).powersetCard j := by
    ext s
    simp only [mem_filter,mem_powersetCard]
    constructor
    · rintro ⟨⟨hsub,hj⟩,hd⟩
      exact ⟨fun q hq => mem_filter.mpr ⟨hsub hq,(prodDvd s (fun p h => hp p (hsub h)) m).mp hd q hq⟩,hj⟩
    · rintro ⟨hsub,hj⟩
      have hP (q) (hq:q∈s) := (mem_filter.mp (hsub hq)).1
      exact ⟨⟨fun q hq => hP q hq,hj⟩,(prodDvd s (fun p h => hp p (hP p h)) m).mpr
        (fun q hq => (mem_filter.mp (hsub hq)).2)⟩
  unfold divisCount
  simp_rw [←Nat.Ioc_filter_dvd_card_eq_div, ←Finset.sum_boole]
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro m _
  rw [Finset.sum_boole,hs,card_powersetCard]

private theorem localTrunc (k r : ℕ) :
    |(if k=0 then (1:ℝ) else 0) - ∑ j ∈ range (r+1), (-1:ℝ)^j*(k.choose j:ℕ)| ≤ k.choose r := by
  cases k with
  | zero =>
    have hy : (∑ j ∈ range (r+1), (-1:ℝ)^j*(((0:ℕ).choose j):ℕ))=1 := by
      rw [sum_eq_single 0]
      · simp
      · intro j _ hj
        have hh : (0:ℕ).choose j=0 := Nat.choose_eq_zero_of_lt (by omega)
        rw [hh];simp
      · simp
    simp [hy]
  | succ k =>
    have hi := @Int.alternating_sum_range_choose_eq_choose k r
    have hr : (∑ j ∈ range (r+1), (-1:ℝ)^j*(((k+1).choose j):ℕ))=(-1:ℝ)^r*(k.choose r:ℕ) := by exact_mod_cast hi
    rw [if_neg (by omega),zero_sub,abs_neg,hr,abs_mul,abs_pow]
    simpa using (show ((k.choose r:ℕ):ℝ) ≤ ((k+1).choose r:ℕ) by exact_mod_cast Nat.choose_le_succ k r)

theorem truncateError (P : Finset ℕ) (hp : ∀ p∈P, p.Prime) (r X : ℕ) :
    |count P X-trunc P r X| ≤ divisCount P r X := by
  unfold count trunc
  simp_rw [divisAsChoose P hp,Finset.mul_sum]
  rw [Finset.sum_comm (s:=range (r+1)),←sum_sub_distrib]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (sum_le_sum (fun m _ => localTrunc (hits P m).card r))

theorem reciprocalLayer (P : Finset ℕ) (hp : ∀ p∈P, p.Prime) (r : ℕ) :
    (∑ s ∈ P.powersetCard r, 1/(product s:ℝ)) ≤ Real.exp (2*harmonic P)/(2:ℝ)^r := by
  apply (le_div_iff₀ (by positivity)).mpr
  rw [Finset.sum_mul]
  calc
    _ = ∑ s ∈ P.powersetCard r, ∏ p ∈ s, (2/(p:ℝ)) := by
      apply sum_congr rfl
      intro s hs
      rw [prod_div_distrib,prod_const,(mem_powersetCard.mp hs).2]
      simp [product,div_eq_mul_inv,mul_comm]
    _ ≤ ∑ s ∈ P.powerset, ∏ p ∈ s, (2/(p:ℝ)) :=
      sum_le_sum_of_subset_of_nonneg (fun s hs => mem_powerset.mpr (mem_powersetCard.mp hs).1)
        (fun s _ _ => prod_nonneg (fun _ _ => by positivity))
    _ = ∏ p ∈ P, (1+2/(p:ℝ)) := (prod_one_add ..).symm
    _ ≤ ∏ p ∈ P, Real.exp (2/(p:ℝ)) := by
      apply Finset.prod_le_prod₀ (fun p _ => by positivity)
      intro p hp
      simpa [add_comm] using (Real.add_one_le_exp (2/(p:ℝ)))
    _ = _ := by rw [←Real.exp_sum]; congr 1;unfold harmonic;rw [mul_sum];apply sum_congr rfl;intros;ring

theorem errorEnvelope (P : Finset ℕ) (hp : ∀ p∈P, p.Prime) (r X : ℕ) :
    |count P X-trunc P r X| ≤ (X:ℝ)*Real.exp (2*harmonic P)/(2:ℝ)^r := by
  apply (truncateError P hp r X).trans
  calc
    divisCount P r X ≤ (X:ℝ)*(∑ s ∈ P.powersetCard r, 1/(product s:ℝ)) := by
      unfold divisCount
      rw [mul_sum]
      apply sum_le_sum
      intro s _
      simpa only [mul_one_div] using (Nat.cast_div_le (m:=X) (n:=product s) : ((X/product s:ℕ):ℝ)≤X/(product s:ℝ))
    _ ≤ (X:ℝ)*(Real.exp (2*harmonic P)/(2:ℝ)^r) :=
      mul_le_mul_of_nonneg_left (reciprocalLayer P hp r) (Nat.cast_nonneg _)
    _ = _ := by ring

end GoldbachModelMean.Brun

end

section
noncomputable section
namespace GoldbachModelMean.Brun
open Finset Filter
private lemma floorIneq (m d : ℕ) (hd : 0<d) :
    (m:ℝ)/d-1 ≤ ((m/d:ℕ):ℝ) ∧ ((m/d:ℕ):ℝ) ≤ m/(d:ℝ) := by
  refine ⟨?_,Nat.cast_div_le⟩
  have h : (m:ℝ) < d * (((m/d:ℕ):ℝ)+1) := by exact_mod_cast Nat.lt_mul_div_succ m hd
  have hh : (m:ℝ)/d < ((m/d:ℕ):ℝ)+1 := (div_lt_iff₀ (by exact_mod_cast hd)).mpr (by linarith)
  linarith

private lemma floorDiff (X Y d : ℕ) (hd : 0<d) (hY : 0<Y) :
    |((X/d:ℕ):ℝ)-(X:ℝ)/Y*((Y/d:ℕ):ℝ)| ≤ 1+(X:ℝ)/Y := by
  have hY' : (0:ℝ)<Y := by exact_mod_cast hY
  have hpos : 0≤(X:ℝ)/Y := by positivity
  obtain ⟨a,b⟩ := floorIneq X d hd
  obtain ⟨c,e⟩ := floorIneq Y d hd
  have h : (X:ℝ)/Y*(Y/(d:ℝ))=X/(d:ℝ) := by field_simp
  have h1 := mul_le_mul_of_nonneg_left c hpos
  have h2 := mul_le_mul_of_nonneg_left e hpos
  rw [h] at h2
  rw [mul_sub,h,mul_one] at h1
  rw [abs_le]
  constructor <;> linarith

private lemma layerCard (P : Finset ℕ) (hp : ∀ p∈P,p.Prime) (r j X : ℕ) (hj : j≤r) :
    ((P.powersetCard j).filter (fun s => product s ≤ X)).card ≤
      (GoldbachModelMean.fewFactors r (X+1)).card := by
  apply Finset.card_le_card_of_injOn product
  · intro s hs
    obtain ⟨hP,hX⟩ := mem_filter.mp hs
    obtain ⟨hsub,hcard⟩ := mem_powersetCard.mp hP
    have hPrime (q) (hq:q∈s) := hp q (hsub hq)
    exact mem_filter.mpr ⟨mem_range.mpr (by omega),prodPos s hPrime,(omegaProd s hPrime).trans_le (hcard.trans_le hj)⟩
  · intro s hs t ht e
    have h1 := (mem_powersetCard.mp (mem_filter.mp hs).1).1
    have h2 := (mem_powersetCard.mp (mem_filter.mp ht).1).1
    have hs' : (product s).primeFactors=s := Nat.primeFactors_prod (fun q hq => hp q (h1 hq))
    have ht' : (product t).primeFactors=t := Nat.primeFactors_prod (fun q hq => hp q (h2 hq))
    rw [←hs',e,ht']

private lemma layerDiff (P : Finset ℕ) (hp : ∀ p∈P,p.Prime) (r j X Y : ℕ)
    (hj : j≤r) (hY : 0<Y) (hYX : Y≤X) :
    |divisCount P j X-(X:ℝ)/Y*divisCount P j Y| ≤
      ((GoldbachModelMean.fewFactors r (X+1)).card:ℝ)*(1+(X:ℝ)/Y) := by
  classical
  unfold divisCount
  rw [mul_sum,←sum_sub_distrib]
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ s ∈ P.powersetCard j, if product s≤X then 1+(X:ℝ)/Y else 0 := by
      apply sum_le_sum
      intro s hs
      split_ifs with h
      · exact floorDiff X Y (product s) (prodPos s (fun q hq => hp q ((mem_powersetCard.mp hs).1 hq))) hY
      · have hx : X<product s := by omega
        simp [Nat.div_eq_of_lt hx,Nat.div_eq_of_lt (hYX.trans_lt hx)]
    _ = (((P.powersetCard j).filter (fun s => product s ≤ X)).card:ℝ)*(1+(X:ℝ)/Y) := by
      rw [←sum_filter];simp;ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast layerCard P hp r j X hj) (by positivity)

theorem truncDiff (P : Finset ℕ) (hp : ∀ p∈P,p.Prime) (r X Y : ℕ)
    (hY : 0<Y) (hYX : Y≤X) :
    |trunc P r X-(X:ℝ)/Y*trunc P r Y| ≤
      ((r:ℝ)+1)*((GoldbachModelMean.fewFactors r (X+1)).card:ℝ)*(1+(X:ℝ)/Y) := by
  unfold trunc
  rw [mul_sum,←sum_sub_distrib]
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ j ∈ range (r+1), ((GoldbachModelMean.fewFactors r (X+1)).card:ℝ)*(1+(X:ℝ)/Y) := by
      apply sum_le_sum
      intro j hj
      have hh := layerDiff P hp r j X Y (by have := mem_range.mp hj;omega) hY hYX
      rw [show (X:ℝ)/Y*((-1:ℝ)^j*divisCount P j Y)=(-1:ℝ)^j*((X:ℝ)/Y*divisCount P j Y) by ring,
        ←mul_sub,abs_mul,abs_pow]
      simpa using hh
    _ = _ := by simp [mul_assoc]

end GoldbachModelMean.Brun

end

section
noncomputable section
namespace GoldbachModelMean.Brun
open Finset Filter
theorem uniform_lowH (H C e : ℝ) (hC : 1≤C) (he : 0<e) :
    ∀ᶠ X : ℕ in atTop, ∀ Y : ℕ, 0<Y → Y≤X → (X:ℝ)≤C*Y →
    ∀ P : Finset ℕ, (∀ p∈P,p.Prime) → harmonic P≤H →
    |count P X/X - count P Y/Y| ≤ e := by
  obtain ⟨r,hr⟩ := pow_unbounded_of_one_lt (4*Real.exp (2*H)/e) (show (1:ℝ)<2 by norm_num)
  let A : ℝ := ((r:ℝ)+1)*(1+C)
  have hA : 0<A := by dsimp [A];positivity
  have heps : 0<e/(4*A) := by positivity
  obtain ⟨x₀,hx⟩ := eventually_atTop.mp (GoldbachModelMean.fewFactors_eventually r (e/(4*A)) heps)
  filter_upwards [eventually_ge_atTop x₀,eventually_ge_atTop 1] with X hX hX1
  intro Y hY hYX hscale P hp hH
  have hY' : (0:ℝ)<Y := by exact_mod_cast hY
  have hX' : (0:ℝ)<X := by exact_mod_cast hX1
  have hx1 : (1:ℝ)≤X := by exact_mod_cast hX1
  have hRatio : (X:ℝ)/Y≤C := (div_le_iff₀ hY').mpr hscale
  have hR : 0≤(X:ℝ)/Y := by positivity
  have hExp := Real.exp_le_exp.mpr (show 2*harmonic P≤2*H by linarith)
  have hcoeff : Real.exp (2*harmonic P)/(2:ℝ)^r ≤ e/4 := by
    apply (div_le_iff₀ (by positivity)).mpr
    have := (div_lt_iff₀ he).mp hr
    nlinarith
  have err (W : ℕ) : |count P W-trunc P r W| ≤ (W:ℝ)*(e/4) := by
    refine (errorEnvelope P hp r W).trans ?_
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hcoeff (Nat.cast_nonneg _)
  have hf := hx (X+1) (by omega)
  push_cast at hf
  have hL : ((r:ℝ)+1)*((GoldbachModelMean.fewFactors r (X+1)).card:ℝ)*(1+(X:ℝ)/Y) ≤ (X:ℝ)*(e/2) := by
    calc
      _ ≤ ((r:ℝ)+1)*((GoldbachModelMean.fewFactors r (X+1)).card:ℝ)*(1+C) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = A*((GoldbachModelMean.fewFactors r (X+1)).card:ℝ) := by dsimp [A];ring
      _ ≤ A*(e/(4*A)*((X:ℝ)+1)) := mul_le_mul_of_nonneg_left hf hA.le
      _ = e/4*((X:ℝ)+1) := by field_simp
      _ ≤ _ := by nlinarith [mul_nonneg he.le (sub_nonneg.mpr hx1)]
  have ht := (truncDiff P hp r X Y hY hYX).trans hL
  have hE : |(X:ℝ)/Y*trunc P r Y-(X:ℝ)/Y*count P Y| ≤ (X:ℝ)*(e/4) := by
    rw [←mul_sub,abs_mul,abs_of_nonneg hR,abs_sub_comm]
    calc
      _ ≤ ((X:ℝ)/Y)*(Y*(e/4)) := mul_le_mul_of_nonneg_left (err _) hR
      _ = _ := by field_simp
  have hT := abs_sub_le (count P X) (trunc P r X) ((X:ℝ)/Y*count P Y)
  have hU := abs_sub_le (trunc P r X) ((X:ℝ)/Y*trunc P r Y) ((X:ℝ)/Y*count P Y)
  have hab : |count P X-(X:ℝ)/Y*count P Y|≤e*X := by linarith [err X]
  rw [show count P X/(X:ℝ)-count P Y/Y=(count P X-(X:ℝ)/Y*count P Y)/X by field_simp,
    abs_div,abs_of_pos hX']
  exact (div_le_iff₀ hX').mpr hab

end GoldbachModelMean.Brun

end

section
noncomputable section
namespace BandTail
open Finset Filter GoldbachModelMean.Brun
def exceptionalPrimes (n X : ℕ) : Finset ℕ := (Icc 1 X).filter (fun p => p.Prime ∧ ¬p∣n)

def meanG (n X : ℕ) : ℝ := (∑ k ∈ Icc 1 X,g n k)/X

theorem count_eq_g (n X T : ℕ) (hT : T≤X) :
    count (exceptionalPrimes n X) T = ∑ k ∈ Icc 1 T,g n k := by
  unfold count
  have hset : Ioc 0 T=Icc 1 T := by ext k;simp;omega
  rw [hset]
  apply sum_congr rfl
  intro k hk
  obtain ⟨hk1,hkT⟩ := mem_Icc.mp hk
  have h0 : k≠0 := by omega
  have he : (hits (exceptionalPrimes n X) k).card=0 ↔ smooth n k := by
    rw [Finset.card_eq_zero]
    constructor
    · intro h p hp
      by_contra hn
      obtain ⟨hp',hpk,_⟩ := Nat.mem_primeFactors.mp hp
      have hpX := (Nat.le_of_dvd (by omega : 0<k) hpk).trans (hkT.trans hT)
      have hmem : p ∈ hits (exceptionalPrimes n X) k := mem_filter.mpr
        ⟨mem_filter.mpr ⟨mem_Icc.mpr ⟨hp'.one_lt.le,hpX⟩,hp',hn⟩,hpk⟩
      simp [h] at hmem
    · intro hs
      apply eq_empty_iff_forall_notMem.mpr
      intro p hpm
      obtain ⟨hP,hpk⟩ := mem_filter.mp hpm
      obtain ⟨_,hp,hn⟩ := mem_filter.mp hP
      exact hn (hs p (Nat.mem_primeFactors.mpr ⟨hp,hpk,h0⟩))
  simp [g,h0,he]

theorem meanG_nonneg (n X : ℕ) : 0≤ meanG n X := by
  apply div_nonneg _ (Nat.cast_nonneg _)
  apply sum_nonneg
  intro k _
  simp only [g,ArithmeticFunction.coe_mk];split_ifs <;> norm_num

end BandTail

end

section
namespace BandTail
open Finset
noncomputable section
def frequency (P : Finset ℕ) : ℝ := ∑ p ∈ P, (p:ℝ)⁻¹

def hit (p k : ℕ) : ℝ := if p ∣ k then 1 else 0

def hitCount (P : Finset ℕ) (k : ℕ) : ℝ := ∑ p ∈ P, hit p k

theorem hit_sum (p X : ℕ) : (∑ k ∈ Icc 1 X, hit p k) = (X/p : ℕ) := by
  have he : Icc 1 X=Ioc 0 X := by ext k; simp only [mem_Icc,mem_Ioc]; omega
  unfold hit
  rw [he,Finset.sum_boole,Nat.Ioc_filter_dvd_card_eq_div]

theorem firstMoment (P : Finset ℕ) (X : ℕ) (hP : ∀ p ∈ P, 0<p) :
    (X:ℝ)*frequency P-P.card ≤ ∑ k ∈ Icc 1 X,hitCount P k := by
  simp only [hitCount,Finset.sum_comm (s:=Icc 1 X) (t:=P),hit_sum]
  calc
    _ = ∑ p ∈ P, ((X:ℝ)*(p:ℝ)⁻¹-1) := by simp [frequency,mul_sum,sum_sub_distrib]
    _ ≤ _ := by
      apply sum_le_sum
      intro p hp
      have hpr : 0<(p:ℝ) := by exact_mod_cast hP p hp
      have hc : (X:ℝ) < (p:ℝ)*((X/p:ℕ)+1:ℝ) := by exact_mod_cast Nat.lt_mul_div_succ X (hP p hp)
      have hh : (X:ℝ)/(p:ℝ) ≤ ((X/p:ℕ):ℝ)+1 := (div_le_iff₀ hpr).mpr (by linarith)
      linarith [show (X:ℝ)*(p:ℝ)⁻¹ = X/p by rw [div_eq_mul_inv]]

theorem hitPair (X p r : ℕ) (hp : p.Prime) (hr : r.Prime) :
    (∑ k ∈ Icc 1 X,hit p k * hit r k) ≤
      (X:ℝ)*((p:ℝ)⁻¹*(r:ℝ)⁻¹) + (if p=r then (X:ℝ)*(p:ℝ)⁻¹ else 0) := by
  by_cases he : p=r
  · subst r
    have hh (k : ℕ) : hit p k*hit p k=hit p k := by by_cases hk : p∣k <;> simp [hit,hk]
    simp only [hh,hit_sum,ite_true]
    exact (Nat.cast_div_le (α:=ℝ)).trans (by rw [div_eq_mul_inv]; exact le_add_of_nonneg_left (by positivity))
  · have hh (k : ℕ) : hit p k*hit r k=hit (p*r) k := by
      have hc := (Nat.coprime_primes hp hr).mpr he
      have eqv : p*r∣k ↔ p∣k ∧ r∣k := ⟨fun hk => ⟨(dvd_mul_right p r).trans hk,(dvd_mul_left r p).trans hk⟩,fun hk => hc.mul_dvd_of_dvd_of_dvd hk.1 hk.2⟩
      by_cases ha : p∣k <;> by_cases hb : r∣k <;> simp [hit,eqv,ha,hb]
    simp only [hh,hit_sum,if_neg he,add_zero]
    exact (Nat.cast_div_le (α:=ℝ)).trans_eq (by simp [div_eq_mul_inv,mul_comm])

theorem secondMoment (P : Finset ℕ) (X : ℕ) (hP : ∀ p ∈ P, p.Prime) :
    (∑ k ∈ Icc 1 X,(hitCount P k)^2) ≤ (X:ℝ)*(frequency P)^2+X*frequency P := by
  have hswap (f : ℕ → ℕ → ℕ → ℝ) :
      (∑ k ∈ Icc 1 X,∑ p ∈ P,∑ r ∈ P,f k p r)=∑ p ∈ P,∑ r ∈ P,∑ k ∈ Icc 1 X,f k p r := by
    rw [sum_comm]
    exact sum_congr rfl fun _ _ => sum_comm
  simp only [hitCount,sq,sum_mul_sum,hswap]
  calc
    _ ≤ ∑ p ∈ P,∑ r ∈ P, ((X:ℝ)*((p:ℝ)⁻¹*(r:ℝ)⁻¹)+(if p=r then (X:ℝ)*(p:ℝ)⁻¹ else 0)) :=
      sum_le_sum fun p hp => sum_le_sum fun r hr => hitPair X p r (hP p hp) (hP r hr)
    _ = _ := by
      simp only [sum_add_distrib,←mul_sum,sum_ite_eq]
      unfold frequency
      congr 1
      · rw [←Finset.sum_mul]
      · rw [mul_sum]
        exact sum_congr rfl fun p hp => by simp [hp]

theorem highH (n X : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ ¬p∣n) :
    frequency P * (∑ k ∈ Icc 1 X, g n k) ≤ (X:ℝ) + 2*P.card := by
  let H := frequency P
  have hH : 0≤H := sum_nonneg fun p _ => inv_nonneg.mpr (Nat.cast_nonneg p)
  rcases hH.eq_or_lt with hz | hpos
  · change H*_ ≤ _
    rw [←hz,zero_mul]; positivity
  have h1 := firstMoment P X (fun p hp => (hP p hp).1.pos)
  have h2 := secondMoment P X (fun p hp => (hP p hp).1)
  have hdom : (∑ k ∈ Icc 1 X, g n k * H^2) ≤ ∑ k ∈ Icc 1 X, (hitCount P k-H)^2 := by
    apply sum_le_sum
    intro k hk
    have hk0 : k≠0 := by have := (mem_Icc.mp hk).1; omega
    by_cases hsm : smooth n k
    · have h0 : hitCount P k=0 := by
        apply sum_eq_zero
        intro p hp
        have hn := (hP p hp).2
        have hpk : ¬p∣k := fun hpk => hn (hsm p (Nat.mem_primeFactors.mpr ⟨(hP p hp).1,hpk,hk0⟩))
        simp [hit,hpk]
      simp [g,hk0,hsm,h0]
    · simp [g,hk0,hsm,sq_nonneg]
  have he (k : ℕ) : (hitCount P k-H)^2=(hitCount P k)^2 - hitCount P k*(2*H)+ H^2 := by ring
  simp only [he,sum_add_distrib,sum_sub_distrib,←sum_mul,sum_const,nsmul_eq_mul,Nat.card_Icc,Nat.add_sub_cancel] at hdom
  change (X:ℝ)*H-_≤_ at h1
  change _≤(X:ℝ)*H^2+X*H at h2
  have h3 := mul_le_mul_of_nonneg_right h1 (mul_nonneg (by norm_num : (0:ℝ)≤2) hpos.le)
  apply le_of_mul_le_mul_right (a:=H) _ hpos
  nlinarith only [hdom,h3,h2]

end

end BandTail

end

section
noncomputable section
namespace BandTail
open Finset Filter GoldbachModelMean.Brun
theorem mean_slow (C e : ℝ) (hC : 1≤C) (he : 0<e) :
    ∀ᶠ X : ℕ in atTop, ∀ Y : ℕ, 0<Y → Y≤X → (X:ℝ)≤C*Y →
    ∀ n, |meanG n X-meanG n Y|≤e := by
  let H : ℝ := (1+2*C)/e
  have hHpos : 0<H := by dsimp [H];positivity
  filter_upwards [uniform_lowH H C e hC he] with X hlow
  intro Y hY hYX hscale n
  let P := exceptionalPrimes n X
  have hprime (p) (hp : p∈P) : p.Prime ∧ ¬p∣n := (mem_filter.mp hp).2
  have hh : harmonic P=frequency P := by simp [GoldbachModelMean.Brun.harmonic,frequency,one_div]
  by_cases hc : harmonic P≤H
  · have hh := hlow Y hY hYX hscale P (fun p h => (hprime p h).1) hc
    rwa [count_eq_g n X X le_rfl,count_eq_g n X Y hYX] at hh
  · have hPH := lt_of_not_ge hc
    rw [hh] at hPH
    have hPcard : P.card≤X := (card_filter_le ..).trans_eq (by simp)
    have hX' : (0:ℝ)<X := by exact_mod_cast hY.trans_le hYX
    have hyp : (0:ℝ)<Y := by exact_mod_cast hY
    have hscaleX : (X:ℝ)≤C*X := by simpa using (mul_le_mul_of_nonneg_right hC hX'.le)
    have hb (T : ℕ) (ht : (0:ℝ)<T) (hscaleT : (X:ℝ)≤C*T) : meanG n T≤e := by
      have hcard' : (P.card:ℝ) ≤ C*T := (show (P.card:ℝ)≤X by exact_mod_cast hPcard).trans hscaleT
      have hbound := highH n T P hprime
      have hp : 0≤∑ k ∈ Icc 1 T,g n k := by
        have hh := meanG_nonneg n T
        unfold meanG at hh
        simpa [ht.ne'] using mul_nonneg hh ht.le
      have hlo := mul_le_mul_of_nonneg_right hPH.le hp
      have hHS : H*(∑ k ∈ Icc 1 T,g n k) ≤ (1+2*C)*T := by linarith
      have hid : (1+2*C)*T=H*(e*T) := by dsimp [H];field_simp
      rw [hid] at hHS
      exact (div_le_iff₀ ht).mpr ((mul_le_mul_iff_right₀ hHpos).mp hHS)
    have hx := hb X hX' hscaleX
    have hy := hb Y hyp hscale
    rw [abs_le]
    constructor <;> linarith [meanG_nonneg n X, meanG_nonneg n Y]

end BandTail

end

section
namespace BandTail
open Finset Filter
noncomputable section
theorem uniform_prefix_floor (R : ℕ) (hR : 1 ≤ R) (δ : ℝ) (hδ : 0<δ) :
    ∃ A₀ : ℕ, ∀ A ≥ A₀, ∀ n i : ℕ, A ≤ i → i ≤ R*A →
      -(δ*(A:ℝ))  ≤  ∑ q ∈ Finset.Ioc A i,F n q := by
  have hr : (1:ℝ) ≤ R := by exact_mod_cast hR
  have hu : 0<universal := Real.exp_pos _
  let τ : ℝ := δ/(8*((R:ℝ)+1))
  have hτ : 0<τ := by dsimp [τ]; positivity
  let e : ℝ := τ/(universal+1)
  have he : 0<e := by dsimp [e]; positivity
  have heu : universal*e  ≤  τ := by
    have heq : e*(universal+1)=τ := by dsimp [e]; field_simp
    nlinarith
  obtain ⟨N,hN⟩ := exists_nat_ge (universal/τ)
  let J := (N+1)^4
  have hJ : 0<J := by dsimp [J]; positivity
  have hj : (J:ℝ)^(1/4:ℝ)=(N:ℝ)+1 := by
    dsimp [J]; push_cast
    rw [←Real.rpow_natCast_mul (by positivity),show (↑(4:ℕ):ℝ)*(1/4)=1 by norm_num,Real.rpow_one]
  have ht : universal/(J:ℝ)^(1/4:ℝ)  ≤  τ := by
    rw [hj]
    apply (div_le_iff₀ (by positivity)).mpr
    have := (div_le_iff₀ hτ).mp hN
    nlinarith
  let C : ℝ := 2*(R:ℝ)*J
  have hjr : (1:ℝ) ≤ J := by exact_mod_cast hJ
  have hC : 1 ≤ C := by dsimp [C]; nlinarith [mul_le_mul hr hjr (by norm_num) (by positivity)]
  obtain ⟨M,hM⟩ := eventually_atTop.mp (mean_slow C e hC he)
  obtain ⟨L,hL⟩ := exists_nat_ge ((J:ℝ)/e)
  refine ⟨max J (max M L),?_⟩
  intro A hA n i hAi hiA
  have hJA : J ≤ A := by omega
  have hA0 : 0<A := hJ.trans_le hJA
  have hAr : (0:ℝ)<A := by exact_mod_cast hA0
  have hi0 : 0 < i := hA0.trans_le hAi
  have hir : (0:ℝ) < i := by exact_mod_cast hi0
  have hscale : (i:ℝ) ≤ R*(A:ℝ) := by exact_mod_cast hiA
  let t := gAvg n i
  let Z := ∑ d ∈ Icc 1 J,z n d
  have ht01 : 0 ≤ t ∧ t ≤ 1 := g_avg_bounds n i
  have hz : -τ ≤ Z := by have hz' := signedPrefix n J hJ; dsimp [Z]; linarith
  have hlin (X : ℕ) (hAX : A ≤ X) (hXi : X ≤ i) :
      |fSum n X-(X:ℝ)*(Z*t)|  ≤  X*(3*τ) := by
    have hX : 0<X := hA0.trans_le hAX
    have hxr : (0:ℝ)<X := by exact_mod_cast hX
    have hjx : (J:ℝ)/X ≤ e := by
      apply (div_le_iff₀ hxr).mpr
      have hLX : (L:ℝ) ≤ X := by exact_mod_cast (show L ≤ X by omega)
      have := (div_le_iff₀ he).mp (hL.trans hLX)
      linarith
    have hnear (d : ℕ) (hd : d∈Icc 1 J) : |gAvg n (X/d)-t| ≤ e := by
      obtain ⟨hd0,hdJ⟩ := mem_Icc.mp hd
      have hdX : d ≤ X := by omega
      have hy : 0<X/d := Nat.div_pos hdX hd0
      have hii : i ≤ R*X := hiA.trans (Nat.mul_le_mul_left R hAX)
      have hratio : X ≤ (2*J)*(X/d) := by
        calc
          X  ≤  d*(X/d+1) := (Nat.lt_mul_div_succ X hd0).le
          _  ≤  J*(2*(X/d)) := Nat.mul_le_mul hdJ (by omega)
          _ = _ := by ring
      have hcxy : (i:ℝ) ≤ C*(X/d:ℕ) := by
        dsimp [C]
        exact_mod_cast (show i ≤ 2*R*J*(X/d) from hii.trans (by calc
          R*X  ≤  R*((2*J)*(X/d)) := Nat.mul_le_mul_left R hratio
          _ = _ := by ring))
      rw [abs_sub_comm]
      exact hM i (by omega) (X/d) hy ((Nat.div_le_self X d).trans hXi) hcxy n
    have h := dyadic_approx n X J hX hJ (by omega) t e he.le hnear hjx
    have ha : |fSum n X / X - Z*t| ≤ 3*τ := h.trans (by linarith)
    have eqv : fSum n X-(X:ℝ)*(Z*t)=(X:ℝ)*(fSum n X/X-Z*t) := by field_simp
    rw [eqv,abs_mul,abs_of_pos hxr]
    exact mul_le_mul_of_nonneg_left ha hxr.le
  have ha := abs_le.mp (hlin A le_rfl hAi)
  have hb := abs_le.mp (hlin i hAi le_rfl)
  have htZ : -τ  ≤  Z*t := by
    calc
      -τ  ≤  -τ*t := by nlinarith [mul_nonneg hτ.le (sub_nonneg.mpr ht01.2)]
      _  ≤  _ := mul_le_mul_of_nonneg_right hz ht01.1
  have hia : (A:ℝ) ≤ i := by exact_mod_cast hAi
  have hdiff := mul_le_mul_of_nonneg_left htZ (sub_nonneg.mpr hia)
  have heqτ : (8*((R:ℝ)+1))*τ=δ := by dsimp [τ]; field_simp
  have htot : (i:ℝ)*τ  ≤  R*A*τ := mul_le_mul_of_nonneg_right hscale hτ.le
  have hgood : -(δ*(A:ℝ)) ≤ fSum n i-fSum n A := by
    have δeq : δ*(A:ℝ)=(8*((R:ℝ)+1))*τ*A := by rw [heqτ]
    nlinarith only [ha.1,ha.2,hb.1,hb.2,hdiff,htot,δeq,
      mul_nonneg (Nat.cast_nonneg R) (mul_nonneg hAr.le hτ.le),mul_nonneg hAr.le hτ.le]
  have hsplit := prefix_split (fun q => F n q) hAi
  change fSum n i=fSum n A+_ at hsplit
  linarith

end

end BandTail

end

end

end

end

end

end

end GoldbachGRHBandBase

section GoldbachGRHRamanujanMobius
open scoped BigOperators
namespace GoldbachExplicitModeledMajor
/-- The reduced-residue exponential sum at numerator one is the Möbius value. -/
theorem ram_one_eq_moebius (q : ℕ) :
    ram q 1 = (ArithmeticFunction.moebius q : ℂ) := by
  induction q using Nat.recOnPrimeCoprime with
  | zero => simp [ram]
  | prime_pow p j hp =>
    cases j with
    | zero => simp [ram_one]
    | succ k =>
      have hd (a : ℕ) : ¬ p ^ (a + 1) ∣ 1 := by
        intro ha
        exact (Nat.one_lt_pow (Nat.succ_ne_zero a) hp.one_lt).ne' (Nat.dvd_one.mp ha)
      rw [ram_primePower p k 1 hp,
        ArithmeticFunction.moebius_apply_prime_pow hp (Nat.succ_ne_zero k), ite_eq_right (hd k)]
      cases k with
      | zero => norm_num
      | succ k => simp [hd k]
  | coprime q r hq hr hqr iq ir =>
    rw [ram_mul (by omega) (by omega) hqr, iq, ir,
      ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hqr, Int.cast_mul]

end GoldbachExplicitModeledMajor

end GoldbachGRHRamanujanMobius

section GoldbachGRHKernel
open MeasureTheory Set Finset
open scoped Interval
namespace GoldbachGRHKernel
open GoldbachFourthMoment (phase phase_add)
noncomputable def kernel (n : ℕ) : ℝ → ℂ :=
  GoldbachWindow.poly (n + 1) fun _ => 1

noncomputable def mass (n : ℕ) (r : ℝ) : ℝ :=
  ∫ t in (-r)..r, ‖kernel n t‖ ^ 2

theorem kernel_eq_sum (n : ℕ) (t : ℝ) :
    kernel n t = ∑ k ∈ range (n + 1), phase ((k : ℝ) * t) := by
  simp [kernel, GoldbachWindow.poly]

theorem phase_nat (k : ℕ) : phase (k : ℝ) = 1 := by
  unfold phase
  have h : (((2 * Real.pi * (k : ℝ) : ℝ) : ℂ) * Complex.I) =
      (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [h]
  exact_mod_cast Complex.exp_int_mul_two_pi_mul_I (k : ℤ)

theorem kernel_periodic (n : ℕ) : Function.Periodic (kernel n) 1 := by
  intro t
  simp only [kernel_eq_sum, mul_add, mul_one, phase_add, phase_nat, mul_one]

theorem kernel_continuous (n : ℕ) : Continuous (kernel n) := by
  rw [show kernel n = fun t => ∑ k ∈ range (n + 1), phase ((k : ℝ) * t) from
    funext (kernel_eq_sum n)]
  unfold phase
  fun_prop

theorem reflect (n : ℕ) (t : ℝ) :
    kernel n t ^ 2 * phase (-(n : ℝ) * t) = (↑(‖kernel n t‖ ^ 2) : ℂ) := by
  simp only [kernel_eq_sum, ← Complex.normSq_eq_norm_sq]
  exact frontierMedcoreKernelReflection n t

theorem full_parseval (n : ℕ) :
    (∫ t in (0 : ℝ)..1, ‖kernel n t‖ ^ 2) = (n : ℝ) + 1 := by
  simpa [kernel] using GoldbachWindow.parseval (n + 1) (fun _ => (1 : ℂ))

theorem mass_mono (n : ℕ) {r s : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) :
    mass n r ≤ mass n s := by
  apply intervalIntegral.integral_mono_interval (by linarith) (by linarith) hrs
  · exact Filter.Eventually.of_forall fun _ => sq_nonneg _
  · exact ((kernel_continuous n).norm.pow 2).intervalIntegrable _ _

theorem mass_loss (n : ℕ) {r : ℝ} (hr : 0 < r) (hh : r ≤ 1 / 2) :
    0 ≤ (n : ℝ) + 1 - mass n r ∧
      (n : ℝ) + 1 - mass n r ≤ 1 / (2 * r) := by
  let F : ℝ → ℝ := fun t => ‖kernel n t‖ ^ 2
  have hF : Continuous F := (kernel_continuous n).norm.pow 2
  have hp : Function.Periodic F 1 := by
    intro t
    simp only [F, kernel_periodic n t]
  have hfull : (∫ t in (-r)..(1 - r), F t) = (n : ℝ) + 1 := by
    have h := hp.intervalIntegral_add_eq (-r) 0
    rw [show -r + 1 = 1 - r by ring, zero_add] at h
    exact h.trans (full_parseval n)
  have hsplit :
      mass n r + (∫ t in r..(1 - r), F t) = (n : ℝ) + 1 := by
    have h := intervalIntegral.integral_add_adjacent_intervals
      (hF.intervalIntegrable (μ := volume) (-r) r) (hF.intervalIntegrable r (1 - r))
    exact h.trans hfull
  have htail : (n : ℝ) + 1 - mass n r = ∫ t in r..(1 - r), F t := by
    linarith only [hsplit]
  have hordered : r ≤ 1 - r := by linarith only [hh]
  have hrepr : (∫ t in (0 : ℝ)..1, (Ioc r (1 - r)).indicator F t) =
      ∫ t in r..(1 - r), F t := by
    rw [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le hordered,
      MeasureTheory.integral_indicator measurableSet_Ioc,
      Measure.restrict_restrict measurableSet_Ioc]
    rw [inter_eq_left.mpr (Ioc_subset_Ioc hr.le (by linarith only [hr]))]
  have hcut : ∀ t ∈ Icc (0 : ℝ) 1, t ∈ Ioc r (1 - r) →
      r ≤ |(1 : ℝ) * t - (round ((1 : ℝ) * t) : ℝ)| := by
    intro t ht hz
    rw [one_mul]
    by_cases hhalf : t < 1 / 2
    · have hround : round t = 0 :=
        round_eq_zero_iff.mpr ⟨by linarith only [ht.1], hhalf⟩
      simp only [hround, Int.cast_zero, sub_zero, abs_of_nonneg ht.1]
      exact hz.1.le
    · have hround : round t = 1 := round_eq_iff.mpr (by
        change ((1 : ℤ) : ℝ) - 1 / 2 ≤ t ∧ t < ((1 : ℤ) : ℝ) + 1 / 2
        push_cast
        constructor <;> linarith only [hhalf, ht.2])
      simp only [hround, Int.cast_one, abs_of_nonpos (sub_nonpos.mpr ht.2)]
      linarith only [hz.2]
  have hbound := goldbach_geometric_tail_l2 (n + 1) 1 Nat.one_pos r hr hh
    (Ioc r (1 - r)) measurableSet_Ioc hcut
  simp only [Nat.cast_one, one_mul] at hbound
  have hboundF : (∫ t in (0 : ℝ)..1, (Ioc r (1 - r)).indicator F t) ≤ 1 / (2 * r) := by
    simpa only [F, kernel_eq_sum, phase, mul_assoc] using hbound
  rw [hrepr] at hboundF
  rw [htail]
  exact ⟨intervalIntegral.integral_nonneg_of_forall hordered (fun _ => sq_nonneg _), hboundF⟩

end GoldbachGRHKernel

end GoldbachGRHKernel

section GoldbachGRHArcs
open Finset MeasureTheory Set
open scoped Interval
namespace GoldbachGRHArcs
noncomputable abbrev cap := GoldbachFourthGeometry.wide

/-- Indices of reduced fractions in the closed unit interval. The two endpoints are both
present when the denominator is one. -/
def centers (U : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 U) ×ˢ (Finset.range (U+1))).filter
    (fun i => i.2 ≤ i.1 ∧ Nat.Coprime i.2 i.1)

theorem mem_centers {U : ℕ} {i : ℕ × ℕ} :
    i ∈ centers U ↔ 1 ≤ i.1 ∧ i.1 ≤ U ∧ i.2 ≤ i.1 ∧ Nat.Coprime i.2 i.1 := by
  simp only [centers, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_range]
  constructor
  · rintro ⟨⟨⟨h₁, h₂⟩, _⟩, h₃, h₄⟩
    exact ⟨h₁,h₂,h₃,h₄⟩
  · rintro ⟨h₁,h₂,h₃,h₄⟩
    exact ⟨⟨⟨h₁,h₂⟩, by omega⟩,h₃,h₄⟩

theorem centers_mono {Q U : ℕ} (h : Q ≤ U) : centers Q ⊆ centers U := by
  intro i hi
  obtain ⟨h₁,h₂,h₃,h₄⟩ := mem_centers.mp hi
  exact mem_centers.mpr ⟨h₁,h₂.trans h,h₃,h₄⟩

noncomputable def radius (n H q : ℕ) : ℝ := (H : ℝ) / ((q : ℝ) * (n : ℝ))

noncomputable def center (i : ℕ × ℕ) : ℝ := (i.2 : ℝ) / (i.1 : ℝ)

noncomputable def arc (n H : ℕ) (i : ℕ × ℕ) : Set ℝ :=
  {t | |t - center i| ≤ radius n H i.1}

theorem measurable_arc (n H : ℕ) (i : ℕ × ℕ) : MeasurableSet (arc n H i) := by
  unfold arc
  exact measurableSet_le (show Continuous (fun t : ℝ => |t - center i|) by fun_prop).measurable
    measurable_const

theorem arc_eq_Icc (n H : ℕ) (i : ℕ × ℕ) :
    arc n H i = Set.Icc (center i - radius n H i.1) (center i + radius n H i.1) := by
  ext t
  change |t - center i| ≤ radius n H i.1 ↔ _
  rw [abs_le, Set.mem_Icc]
  constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith

theorem mem_cap {n U H : ℕ} {t : ℝ} :
    t ∈ cap n U H ↔ ∃ i ∈ centers U, t ∈ arc n H i := by
  constructor
  · rintro ⟨q,a,h₁,h₂,h₃,h₄,h₅⟩
    exact ⟨(q,a),mem_centers.mpr ⟨h₁,h₂,h₃,h₄⟩,h₅⟩
  · rintro ⟨⟨q,a⟩,hi,ht⟩
    obtain ⟨h₁,h₂,h₃,h₄⟩ := mem_centers.mp hi
    exact ⟨q,a,h₁,h₂,h₃,h₄,ht⟩

theorem measurable_cap (n U H : ℕ) : MeasurableSet (cap n U H) := by
  have h : cap n U H = ⋃ i ∈ centers U, arc n H i := by
    ext t
    rw [mem_cap]
    simp only [Set.mem_iUnion]
    constructor <;> rintro ⟨i,hi,ht⟩ <;> exact ⟨i,hi,ht⟩
  rw [h]
  exact MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun _ => measurable_arc n H i

theorem arc_mono {n R H : ℕ} (h : R ≤ H) (i : ℕ × ℕ) : arc n R i ⊆ arc n H i := by
  intro t ht
  change |t - center i| ≤ radius n R i.1 at ht
  change |t - center i| ≤ radius n H i.1
  exact ht.trans (div_le_div_of_nonneg_right (by exact_mod_cast h) (by positivity))

theorem cap_mono {n Q U R H : ℕ} (hQ : Q ≤ U) (hH : R ≤ H) :
    cap n Q R ⊆ cap n U H := by
  intro t ht
  obtain ⟨i,hi,hit⟩ := mem_cap.mp ht
  exact mem_cap.mpr ⟨i,centers_mono hQ hi,arc_mono hH i hit⟩

theorem common_arc_unique {n U H : ℕ} (hbudget : 2 * H * U < n)
    {i j : ℕ × ℕ} (hi : i ∈ centers U) (hj : j ∈ centers U) {t : ℝ}
    (hti : t ∈ arc n H i) (htj : t ∈ arc n H j) : i = j := by
  obtain ⟨hi₁,hi₂,_,hi₄⟩ := mem_centers.mp hi
  obtain ⟨hj₁,hj₂,_,hj₄⟩ := mem_centers.mp hj
  obtain ⟨h₁,h₂⟩ := GoldbachWideArcs.reduced_centers_eq_of_common_point
    hbudget hi₁ hj₁ hi₂ hj₂ hi₄ hj₄ hti htj
  exact Prod.ext h₁ h₂

/-- A wide arc clipped to the unit interval, with its narrow interval removed when appropriate. -/
noncomputable def cell (n Q H : ℕ) (i : ℕ × ℕ) : Set ℝ :=
  (arc n H i \ (if i.1 ≤ Q then arc n Q i else ∅)) ∩ Set.Ioc 0 1

theorem measurable_cell (n Q H : ℕ) (i : ℕ × ℕ) : MeasurableSet (cell n Q H i) := by
  unfold cell
  apply MeasurableSet.inter _ measurableSet_Ioc
  apply (measurable_arc n H i).diff
  split
  · exact measurable_arc n Q i
  · exact MeasurableSet.empty

theorem cell_disjoint {n Q U H : ℕ} (hbudget : 2 * H * U < n) :
    (↑(centers U) : Set (ℕ × ℕ)).PairwiseDisjoint (cell n Q H) := by
  intro i hi j hj hij
  apply Set.disjoint_left.mpr
  intro t hti htj
  exact hij (common_arc_unique hbudget hi hj hti.1.1 htj.1.1)

theorem cells_eq {n Q U H : ℕ} (hQ : Q ≤ U) (hH : Q ≤ H) (hbudget : 2 * H * U < n) :
    (⋃ i ∈ centers U, cell n Q H i) = (cap n U H \ cap n Q Q) ∩ Set.Ioc 0 1 := by
  ext t
  simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_sdiff]
  constructor
  · rintro ⟨i,hi,ht⟩
    refine ⟨⟨mem_cap.mpr ⟨i,hi,ht.1.1⟩,?_⟩, ht.2⟩
    intro hN
    obtain ⟨j,hj,htj⟩ := mem_cap.mp hN
    have he := common_arc_unique hbudget hi (centers_mono hQ hj) ht.1.1 (arc_mono hH j htj)
    subst j
    apply ht.1.2
    rw [ite_eq_left (mem_centers.mp hj).2.1]
    exact htj
  · rintro ⟨⟨ht,hnot⟩,hunit⟩
    obtain ⟨i,hi,hti⟩ := mem_cap.mp ht
    refine ⟨i,hi,⟨⟨hti,?_⟩,hunit⟩⟩
    by_cases hic : i.1 ≤ Q
    · rw [ite_eq_left hic]
      intro hnarrow
      apply hnot
      obtain ⟨h₁,_,h₃,h₄⟩ := mem_centers.mp hi
      exact mem_cap.mpr ⟨i,mem_centers.mpr ⟨h₁,hic,h₃,h₄⟩,hnarrow⟩
    · simp [hic]

end GoldbachGRHArcs

end GoldbachGRHArcs

section GoldbachGRHCenterSums
open scoped BigOperators
namespace GoldbachGRHArcs
/-- Group the reduced arc centers by denominator. -/
theorem sum_centers_eq (U : ℕ) {A : Type*} [AddCommMonoid A] (F : ℕ × ℕ → A) :
    (∑ i ∈ centers U, F i) =
      ∑ q ∈ Finset.Icc 1 U, ∑ a ∈ (Finset.range (q + 1)).filter (fun a => a.Coprime q),
        F (q, a) := by
  rw [centers, Finset.sum_filter, Finset.sum_product]
  refine Finset.sum_congr rfl fun q hq => ?_
  change (∑ a ∈ Finset.range (U + 1), if a ≤ q ∧ a.Coprime q then F (q, a) else 0) = _
  rw [← Finset.sum_filter]
  have hqU := (Finset.mem_Icc.mp hq).2
  have hs : (Finset.range (U + 1)).filter (fun a => a ≤ q ∧ a.Coprime q) =
      (Finset.range (q + 1)).filter (fun a => a.Coprime q) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨_, ha, hcop⟩
      exact ⟨Nat.lt_succ_of_le ha, hcop⟩
    · rintro ⟨ha, hcop⟩
      exact ⟨by omega, by omega, hcop⟩
  rw [hs]

end GoldbachGRHArcs

end GoldbachGRHCenterSums

section GoldbachGRHArcTransport
open MeasureTheory
open Set hiding center
open scoped Interval
namespace GoldbachGRHArcTransport
open GoldbachGRHArcs
private theorem radius_nonnegative (n H q : ℕ) : 0 ≤ radius n H q := by
  unfold radius
  positivity

private theorem continuous_translate {E : Type*} [TopologicalSpace E]
    {G : ℝ → E} (hG : Continuous G) (c : ℝ) : Continuous (fun t => G (t - c)) :=
  hG.comp (continuous_id.sub continuous_const)

section Integral
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
theorem arc_integral (n H : ℕ) (i : ℕ × ℕ) (G : ℝ → E) :
    (∫ t in arc n H i, G (t - center i)) =
      ∫ t in (-(radius n H i.1))..(radius n H i.1), G t := by
  have hr := radius_nonnegative n H i.1
  rw [arc_eq_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith only [hr] :
      center i - radius n H i.1 ≤ center i + radius n H i.1),
    intervalIntegral.integral_comp_sub_right]
  congr 2 <;> ring

private theorem clipped_arc_integral_closed (n H : ℕ) (i : ℕ × ℕ) (G : ℝ → E) :
    (∫ t in arc n H i ∩ Ioc 0 1, G (t - center i)) =
      ∫ t in arc n H i ∩ Icc 0 1, G (t - center i) := by
  apply setIntegral_congr_set
  have h : Ioc (0 : ℝ) 1 =ᵐ[volume] Icc (0 : ℝ) 1 := Ioc_ae_eq_Icc
  filter_upwards [h] with t ht
  simp only [mem_inter_iff, ht]

theorem clipped_arc_integral_of_interior (n H : ℕ) (i : ℕ × ℕ) (G : ℝ → E)
    (hleft : radius n H i.1 ≤ center i) (hright : center i + radius n H i.1 ≤ 1) :
    (∫ t in arc n H i ∩ Ioc 0 1, G (t - center i)) =
      ∫ t in (-(radius n H i.1))..(radius n H i.1), G t := by
  rw [clipped_arc_integral_closed, inter_eq_left.mpr, arc_integral]
  rw [arc_eq_Icc]
  exact Icc_subset_Icc (sub_nonneg.mpr hleft) hright

theorem clipped_arc_integral_zero (n H : ℕ) (G : ℝ → E)
    (hr : radius n H 1 ≤ 1) :
    (∫ t in arc n H (1, 0) ∩ Ioc 0 1, G (t - center (1, 0))) =
      ∫ t in (0 : ℝ)..(radius n H 1), G t := by
  have hnonneg := radius_nonnegative n H 1
  rw [clipped_arc_integral_closed, arc_eq_Icc]
  simp only [show center (1, 0) = 0 by norm_num [center], zero_sub, zero_add, sub_zero]
  rw [Icc_inter_Icc, sup_eq_right.mpr (neg_nonpos.mpr hnonneg), inf_eq_left.mpr hr,
    integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hnonneg]

theorem clipped_arc_integral_one (n H : ℕ) (G : ℝ → E)
    (hr : radius n H 1 ≤ 1) :
    (∫ t in arc n H (1, 1) ∩ Ioc 0 1, G (t - center (1, 1))) =
      ∫ t in (-(radius n H 1))..(0 : ℝ), G t := by
  have hnonneg := radius_nonnegative n H 1
  rw [clipped_arc_integral_closed, arc_eq_Icc]
  simp only [show center (1, 1) = 1 by norm_num [center] ]
  rw [Icc_inter_Icc, sup_eq_left.mpr (sub_nonneg.mpr hr),
    inf_eq_right.mpr (by linarith only [hnonneg] : (1 : ℝ) ≤ 1 + radius n H 1),
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith only [hnonneg] :
      1 - radius n H 1 ≤ 1), intervalIntegral.integral_comp_sub_right]
  congr 2 <;> ring

theorem cell_integral_eq_clipped_sub {n Q H : ℕ} (hQH : Q ≤ H) (i : ℕ × ℕ)
    (G : ℝ → E) (hG : Continuous G) :
    (∫ t in cell n Q H i, G (t - center i)) =
      (∫ t in arc n H i ∩ Ioc 0 1, G (t - center i)) -
        if i.1 ≤ Q then (∫ t in arc n Q i ∩ Ioc 0 1, G (t - center i)) else 0 := by
  by_cases hq : i.1 ≤ Q
  · simp only [cell, ite_eq_left hq]
    rw [show (arc n H i \ arc n Q i) ∩ Ioc (0 : ℝ) 1 =
        (arc n H i ∩ Ioc 0 1) \ (arc n Q i ∩ Ioc 0 1) by
      ext t
      simp only [mem_inter_iff, mem_sdiff]
      tauto]
    apply setIntegral_sdiff ((measurable_arc n Q i).inter measurableSet_Ioc)
    · exact ((continuous_translate hG (center i)).intervalIntegrable 0 1).1.mono_set inter_subset_right
    · exact inter_subset_inter_left _ (arc_mono hQH i)
  · simp [cell, hq]

end Integral

theorem arc_interior_bounds {n H q a : ℕ} (hH : H ≤ n) (hq : 2 ≤ q) (ha : a ≤ q)
    (hcop : Nat.Coprime a q) :
    radius n H q ≤ center (q, a) ∧ center (q, a) + radius n H q ≤ 1 := by
  have ha0 : 1 ≤ a := by
    by_contra! hn
    have ha' : a = 0 := by omega
    subst a
    have h := (Nat.coprime_zero_left q).mp hcop
    omega
  have haq : a + 1 ≤ q := by
    by_contra! hn
    have ha' : a = q := by omega
    subst a
    have h : q = 1 := by simpa [Nat.Coprime] using hcop
    omega
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hr : radius n H q ≤ 1 / (q : ℝ) := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [radius]
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hHn : (H : ℝ) ≤ (n : ℝ) := by exact_mod_cast hH
    unfold radius
    apply (div_le_iff₀ (mul_pos hqR hnR)).mpr
    rw [← mul_assoc, one_div_mul_cancel hqR.ne', one_mul]
    exact hHn
  refine ⟨hr.trans ?_, (add_le_add_right hr (center (q, a))).trans ?_⟩
  · unfold center
    exact div_le_div_of_nonneg_right (by exact_mod_cast ha0) hqR.le
  · unfold center
    rw [← add_div]
    apply (div_le_iff₀ hqR).mpr
    simpa only [one_mul, Nat.cast_add, Nat.cast_one] using (show ((a + 1 : ℕ) : ℝ) ≤ q by
      exact_mod_cast haq)

theorem radius_one_le {n H : ℕ} (hH : H ≤ n) : radius n H 1 ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [radius]
  · simpa [radius] using (div_le_one (by exact_mod_cast hn : (0:ℝ) < n)).mpr
      (show (H : ℝ) ≤ n by exact_mod_cast hH)

theorem cell_integral_interior {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n Q H q a : ℕ} (hQH : Q ≤ H) (hHn : H ≤ n) (hq : 2 ≤ q) (ha : a ≤ q)
    (hcop : Nat.Coprime a q) (G : ℝ → E) (hG : Continuous G) :
    (∫ t in cell n Q H (q, a), G (t - center (q, a))) =
      (∫ t in (-(radius n H q))..(radius n H q), G t) -
        if q ≤ Q then (∫ t in (-(radius n Q q))..(radius n Q q), G t) else 0 := by
  obtain ⟨hHl, hHr⟩ := arc_interior_bounds hHn hq ha hcop
  obtain ⟨hQl, hQr⟩ := arc_interior_bounds (hQH.trans hHn) hq ha hcop
  rw [cell_integral_eq_clipped_sub hQH (q, a) G hG,
    clipped_arc_integral_of_interior n H (q, a) G hHl hHr,
    clipped_arc_integral_of_interior n Q (q, a) G hQl hQr]

/-- The two denominator-one cells assemble to a full translated window. -/
theorem cell_integral_endpoints {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n Q H : ℕ} (hQH : Q ≤ H) (hHn : H ≤ n) (G : ℝ → E) (hG : Continuous G) :
    (∫ t in cell n Q H (1, 0), G (t - center (1, 0))) +
      (∫ t in cell n Q H (1, 1), G (t - center (1, 1))) =
      (∫ t in (-(radius n H 1))..(radius n H 1), G t) -
        if 1 ≤ Q then (∫ t in (-(radius n Q 1))..(radius n Q 1), G t) else 0 := by
  have hQn := hQH.trans hHn
  have hfull (R : ℕ) :
      (∫ t in (0 : ℝ)..(radius n R 1), G t) +
        (∫ t in (-(radius n R 1))..(0 : ℝ), G t) =
          ∫ t in (-(radius n R 1))..(radius n R 1), G t := by
    rw [add_comm]
    exact intervalIntegral.integral_add_adjacent_intervals (hG.intervalIntegrable _ _)
      (hG.intervalIntegrable _ _)
  simp only [cell_integral_eq_clipped_sub hQH _ G hG,
    clipped_arc_integral_zero n H G (radius_one_le hHn),
    clipped_arc_integral_zero n Q G (radius_one_le hQn),
    clipped_arc_integral_one n H G (radius_one_le hHn),
    clipped_arc_integral_one n Q G (radius_one_le hQn)]
  by_cases h : 1 ≤ Q
  · simp only [ite_eq_left h]
    rw [← hfull H, ← hfull Q]
    abel
  · simpa only [ite_eq_right h, sub_zero] using hfull H

theorem cell_kernel_interior {n Q H q a : ℕ} (hQH : Q ≤ H) (hHn : H ≤ n)
    (hq : 2 ≤ q) (ha : a ≤ q) (hcop : Nat.Coprime a q) :
    (∫ t in cell n Q H (q, a), ‖GoldbachGRHKernel.kernel n (t - center (q, a))‖ ^ 2) =
      GoldbachGRHKernel.mass n (radius n H q) -
        if q ≤ Q then GoldbachGRHKernel.mass n (radius n Q q) else 0 :=
  cell_integral_interior hQH hHn hq ha hcop _
    ((GoldbachGRHKernel.kernel_continuous n).norm.pow 2)

theorem cell_kernel_endpoints {n Q H : ℕ} (hQH : Q ≤ H) (hHn : H ≤ n) :
    (∫ t in cell n Q H (1, 0), ‖GoldbachGRHKernel.kernel n (t - center (1, 0))‖ ^ 2) +
      (∫ t in cell n Q H (1, 1), ‖GoldbachGRHKernel.kernel n (t - center (1, 1))‖ ^ 2) =
      GoldbachGRHKernel.mass n (radius n H 1) -
        if 1 ≤ Q then GoldbachGRHKernel.mass n (radius n Q 1) else 0 :=
  cell_integral_endpoints hQH hHn _ ((GoldbachGRHKernel.kernel_continuous n).norm.pow 2)

end GoldbachGRHArcTransport

end GoldbachGRHArcTransport

section GoldbachGRHModelDef
namespace GoldbachGRHModel
/-- The principal model on a single reduced rational arc. -/
noncomputable def model (n : ℕ) (i : ℕ × ℕ) (t : ℝ) : ℂ :=
  ((ArithmeticFunction.moebius i.1 : ℂ) / (i.1.totient : ℂ)) *
    GoldbachGRHKernel.kernel n (t - GoldbachGRHArcs.center i)

theorem model_continuous (n : ℕ) (i : ℕ × ℕ) : Continuous (model n i) :=
  continuous_const.mul ((GoldbachGRHKernel.kernel_continuous n).comp
    (continuous_id.sub continuous_const))

end GoldbachGRHModel

end GoldbachGRHModelDef

section GoldbachGRHModelAssembly
open Finset MeasureTheory
open scoped ComplexConjugate
namespace GoldbachGRHModelAssembly
open GoldbachGRHArcs (cell centers center radius)
open GoldbachGRHKernel (kernel mass)
open GoldbachFourthMoment (phase phase_add)
open GoldbachGRHModel (model)
open GoldbachExplicitModeledMajor (coefficient ram ram_one_eq_moebius)
noncomputable def massDifference (n Q H q : ℕ) : ℝ :=
  mass n (radius n H q) - if q ≤ Q then mass n (radius n Q q) else 0

private noncomputable def signedFactor (n q a : ℕ) : ℂ :=
  ((ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ)) ^ 2 *
    phase (-(n : ℝ) * center (q, a))

private theorem phase_neg (x : ℝ) : phase (-x) = conj (phase x) := by
  symm
  unfold phase
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

private theorem signedFactor_zero (n : ℕ) : signedFactor n 1 0 = 1 := by
  simp [signedFactor, center, phase]

private theorem signedFactor_one (n : ℕ) : signedFactor n 1 1 = 1 := by
  simp [signedFactor, center, phase_neg, GoldbachGRHKernel.phase_nat]

private theorem model_square_eq (n q a : ℕ) (t : ℝ) :
    model n (q, a) t ^ 2 * phase (-(n : ℝ) * t) =
      signedFactor n q a * (↑(‖kernel n (t - center (q, a))‖ ^ 2) : ℂ) := by
  have hphase : -(n : ℝ) * t =
      -(n : ℝ) * center (q, a) + -(n : ℝ) * (t - center (q, a)) := by ring
  rw [← GoldbachGRHKernel.reflect n (t - center (q, a)), model, hphase, phase_add]
  unfold signedFactor
  ring

private theorem cell_model_integral (n Q H q a : ℕ) :
    (∫ t in cell n Q H (q, a), model n (q, a) t ^ 2 * phase (-(n : ℝ) * t)) =
      signedFactor n q a *
        (↑(∫ t in cell n Q H (q, a), ‖kernel n (t - center (q, a))‖ ^ 2) : ℂ) := by
  simp_rw [model_square_eq]
  rw [MeasureTheory.integral_const_mul, integral_complex_ofReal]

private theorem sum_signedFactor (n q : ℕ) :
    (∑ a ∈ (range q).filter (fun a => Nat.Coprime a q), signedFactor n q a) =
      coefficient q n := by
  rw [coefficient, ram_one_eq_moebius, ram, map_sum, Finset.mul_sum]
  refine sum_congr rfl fun a _ => ?_
  unfold signedFactor
  congr 1
  have h : -(n : ℝ) * center (q, a) = -((n : ℝ) * a / q) := by
    simp only [center, ← mul_div_assoc, neg_mul, neg_div]
  rw [h, phase_neg]
  rfl

/-- Grouping the centered kernels by denominator recovers the exact Ramanujan model. -/
theorem sum_cell_model {n Q H U : ℕ} (_hU : 1 ≤ U) (hQH : Q ≤ H) (hHn : H ≤ n) :
    (∑ i ∈ centers U, ∫ t in cell n Q H i, model n i t ^ 2 * phase (-(n : ℝ) * t)) =
      ∑ q ∈ Icc 1 U, coefficient q n * (massDifference n Q H q : ℂ) := by
  classical
  rw [GoldbachGRHArcs.sum_centers_eq]
  refine sum_congr rfl fun q hq => ?_
  have hq1 := (mem_Icc.mp hq).1
  by_cases hqOne : q = 1
  · subst q
    have hf : ((range (1 + 1)).filter (fun a : ℕ => Nat.Coprime a 1)) =
        ({0, 1} : Finset ℕ) := by
      ext a
      simp only [mem_filter, mem_range, Nat.coprime_one_right_iff, and_true,
        mem_insert, mem_singleton]
      omega
    rw [hf, sum_pair (by decide : (0 : ℕ) ≠ 1)]
    simp only [cell_model_integral, signedFactor_zero, signedFactor_one, one_mul,
      ← Complex.ofReal_add, GoldbachGRHArcTransport.cell_kernel_endpoints hQH hHn,
      GoldbachExplicitModeledMajor.coefficient_one, massDifference]
  · have hq2 : 2 ≤ q := by omega
    have hf : ((range (q + 1)).filter (fun a => Nat.Coprime a q)) =
        (range q).filter (fun a => Nat.Coprime a q) := by
      ext a
      simp only [mem_filter, mem_range]
      constructor
      · rintro ⟨haq, hcop⟩
        have hne : a ≠ q := by
          intro heq
          subst a
          have h : q = 1 := by simpa [Nat.Coprime] using hcop
          exact hqOne h
        exact ⟨lt_of_le_of_ne (Nat.lt_succ_iff.mp haq) hne, hcop⟩
      · rintro ⟨haq, hcop⟩
        exact ⟨haq.trans (Nat.lt_succ_self q), hcop⟩
    rw [hf, ← sum_signedFactor, Finset.sum_mul]
    refine sum_congr rfl fun a ha => ?_
    obtain ⟨haq, hcop⟩ := mem_filter.mp ha
    rw [cell_model_integral, GoldbachGRHArcTransport.cell_kernel_interior hQH hHn hq2
      (mem_range.mp haq).le hcop, massDifference]

end GoldbachGRHModelAssembly

end GoldbachGRHModelAssembly

section GoldbachGRHSignedModel
open Filter
open scoped Topology BigOperators ComplexConjugate
namespace GoldbachGRHSignedModel
open Finset Filter ArithmeticFunction
open scoped Topology ArithmeticFunction.zeta
private theorem inverse_squares_ge_two_le (X : ℕ) :
    (∑ j ∈ Icc 2 X, ((j : ℝ)^2)⁻¹) ≤ 3/4 := by
  by_cases hX : 2 ≤ X
  · rw [← sum_Ioc_add_eq_sum_Icc hX]
    have hh := sum_Ioc_inv_sq_le_sub (α := ℝ) (by decide : (2 : ℕ) ≠ 0) hX
    norm_num at hh ⊢
    linarith [show 0 ≤ ((X : ℝ))⁻¹ by positivity]
  · norm_num [Icc_eq_empty_of_lt (lt_of_not_ge hX)]

private theorem product_one_sub_ge {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i ∧ f i ≤ 1) :
    1 - (∑ i ∈ s, f i) ≤ ∏ i ∈ s, (1-f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have haF := hf a (mem_insert_self _ _)
    have hs : ∀ i ∈ s, 0 ≤ f i ∧ f i ≤ 1 := fun i hi => hf i (mem_insert_of_mem hi)
    rw [sum_insert ha, prod_insert ha]
    have hsum : 0 ≤ ∑ i ∈ s, f i := sum_nonneg fun i hi => (hs i hi).1
    have hh := mul_le_mul_of_nonneg_left (ih hs) (sub_nonneg.mpr haF.2)
    nlinarith only [hh, mul_nonneg haF.1 hsum]

private noncomputable def correctionLoss (n p : ℕ) : ℝ :=
  if p ∣ n then 0 else (((p : ℝ)-1)^2)⁻¹

private theorem odd_prime_ge_three {n p : ℕ} (hn : Even n) (hp : p.Prime)
    (hpn : ¬ p ∣ n) : 3 ≤ p := by
  have hp2 := hp.two_le
  by_contra! hh
  have hp₂ : p = 2 := by omega
  apply hpn
  rw [hp₂]
  obtain ⟨k, hk⟩ := hn
  exact ⟨k, by omega⟩

private theorem correctionLoss_bounds {n p : ℕ} (hn : Even n) (hp : p.Prime) :
    0 ≤ correctionLoss n p ∧ correctionLoss n p ≤ 1 := by
  unfold correctionLoss
  by_cases hpN : p ∣ n
  · simp [hpN]
  · have h3 : (3 : ℝ) ≤ p := by exact_mod_cast odd_prime_ge_three hn hp hpN
    rw [ite_eq_right hpN]
    exact ⟨by positivity, inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg ((p:ℝ)-2)])⟩

private theorem local_correction_floor (n p k : ℕ) (hp : p.Prime) :
    1 - correctionLoss n p ≤ ∑ d ∈ (p^k).divisors, BandTail.z n d := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp1 : 0 < (p : ℝ) - 1 := by linarith
  rw [Nat.sum_divisors_prime_pow hp,
    BandTail.localReduce (fun j => BandTail.z n (p^j))
      (fun j => by simp [BandTail.z,BandTail.h_cube n p j hp])]
  simp only [pow_zero,pow_one,(BandTail.z_mult n).map_one]
  simp only [correctionLoss,BandTail.z,ArithmeticFunction.coe_mk,
    BandTail.h_prime n p hp,BandTail.h_square n p hp,Nat.cast_pow]
  by_cases hpn : p ∣ n
  · simp only [hpn, ite_true, sub_zero]
    have hpos : 0 ≤ (1 / ((p : ℝ)-1)) / (p : ℝ) := by positivity
    have hcancel : (1 / ((p : ℝ)-1)) / (p : ℝ) +
        (-(p : ℝ) / ((p : ℝ)-1)) / (p : ℝ)^2 = 0 := by
      field_simp; ring
    split_ifs <;> first | omega | linarith only [hpos,hcancel]
  · simp only [hpn, ite_false, zero_div, ite_self, add_zero]
    have hneg : (-(p : ℝ) / ((p : ℝ)-1)^2) / (p : ℝ) = -(((p : ℝ)-1)^2)⁻¹ := by
      field_simp
    rw [hneg]
    split_ifs <;> linarith [show 0 ≤ (((p : ℝ)-1)^2)⁻¹ by positivity]

theorem signed_divisors_quarter (n M : ℕ) (hn : Even n) (hM : 0 < M) :
    (1/4 : ℝ) ≤ ∑ d ∈ M.divisors, BandTail.z n d := by
  classical
  let s := M.factorization.support
  let P := s.filter (fun p => ¬ p ∣ n)
  have hprime (p : ℕ) (hp : p ∈ s) : p.Prime :=
    Nat.prime_of_mem_primeFactors (M.support_factorization ▸
      (show p ∈ M.factorization.support from hp))
  have hle (p : ℕ) (hp : p ∈ s) : p ≤ M :=
    Nat.le_of_dvd hM (Nat.dvd_of_mem_primeFactors (M.support_factorization ▸
      (show p ∈ M.factorization.support from hp)))
  have hM' (p : ℕ) (hp : p ∈ P) : 3 ≤ p :=
    odd_prime_ge_three hn (hprime p (mem_filter.mp hp).1) (mem_filter.mp hp).2
  have hinj : Set.InjOn (fun p : ℕ => p-1) (↑P : Set ℕ) := by
    intro p hp q hq he
    have h1 := hM' p hp
    have h2 := hM' q hq
    change p - 1 = q - 1 at he
    omega
  have himage : P.image (fun p => p-1) ⊆ Icc 2 M := by
    intro j hj
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hj
    have h1 := hM' p hp
    have h2 := hle p (mem_filter.mp hp).1
    exact mem_Icc.mpr ⟨by omega, by omega⟩
  have hsum : (∑ p ∈ s, correctionLoss n p) ≤ 3/4 := by
    calc
      _ = ∑ p ∈ P, (((p : ℝ)-1)^2)⁻¹ := by
        rw [sum_filter]
        apply sum_congr rfl
        intro p hp
        by_cases hpN : p ∣ n <;> simp [correctionLoss,hpN]
      _ = ∑ p ∈ P, ((((p-1 : ℕ) : ℝ)^2))⁻¹ := by
        apply sum_congr rfl
        intro p hp
        rw [Nat.cast_sub (by have := hM' p hp; omega)]
        norm_cast
      _ = ∑ j ∈ P.image (fun p : ℕ => p-1), ((j : ℝ)^2)⁻¹ := by rw [sum_image hinj]
      _ ≤ ∑ j ∈ Icc 2 M, ((j : ℝ)^2)⁻¹ :=
        sum_le_sum_of_subset_of_nonneg himage (fun _ _ _ => by positivity)
      _ ≤ _ := inverse_squares_ge_two_le M
  let A : ArithmeticFunction ℝ := BandTail.z n * (ζ : ArithmeticFunction ℝ)
  have hA : IsMultiplicative A := (BandTail.z_mult n).mul isMultiplicative_zeta.natCast
  have he (m : ℕ) : A m = ∑ d ∈ m.divisors,BandTail.z n d := coe_mul_zeta_apply
  have hprod := hA.multiplicative_factorization A hM.ne'
  rw [he] at hprod
  rw [hprod,Finsupp.prod]
  change _ ≤ ∏ p ∈ s, A (p^M.factorization p)
  calc
    _ ≤ 1 - ∑ p ∈ s, correctionLoss n p := by linarith
    _ ≤ ∏ p ∈ s, (1 - correctionLoss n p) :=
      product_one_sub_ge s _ (fun p hp => correctionLoss_bounds hn (hprime p hp))
    _ ≤ _ := by
      apply prod_le_prod₀
      · exact fun p hp => sub_nonneg.mpr (correctionLoss_bounds hn (hprime p hp)).2
      · intro p hp
        rw [he]
        exact local_correction_floor n p _ (hprime p hp)

theorem correction_prefix_eighth :
    ∀ᶠ J : ℕ in atTop, 0 < J ∧ ∀ n : ℕ, Even n →
      (1/8 : ℝ) ≤ ∑ d ∈ Icc 1 J, BandTail.z n d := by
  have ht := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/4)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [eventually_ge_atTop (1 : ℕ), ht.eventually_ge_atTop (8 * BandTail.universal)]
    with J hJ hlarge
  refine ⟨hJ, ?_⟩
  intro n hn
  have hJ' : 0 < J := hJ
  have hu := BandTail.uniformTail n J (J.factorial.divisors \ Icc 1 J) hJ' (by
    intro d hd
    obtain ⟨hd, hd'⟩ := mem_sdiff.mp hd
    have hpos := Nat.pos_of_mem_divisors hd
    simp only [mem_Icc, not_and] at hd'
    omega)
  have hh := signed_divisors_quarter n J.factorial hn J.factorial_pos
  rw [← sum_sdiff (s₁ := Icc 1 J) (s₂ := J.factorial.divisors) (BandTail.prefixDiv J)] at hh
  have ht := sum_le_sum (s := J.factorial.divisors \ Icc 1 J) (fun d _ => le_abs_self (BandTail.z n d))
  have hsmall : BandTail.universal / (J : ℝ)^(1/4 : ℝ) ≤ 1/8 := by
    apply (div_le_iff₀ (by positivity)).mpr
    change 8 * BandTail.universal ≤ (J : ℝ)^(1/4 : ℝ) at hlarge
    linarith
  linarith

end GoldbachGRHSignedModel

namespace GoldbachGRHSignedModel
open Finset Filter ArithmeticFunction
open scoped Topology
noncomputable def harmonicG (n X : ℕ) : ℝ :=
  ∑ k ∈ Icc 1 X, BandTail.g n k / (k : ℝ)

noncomputable def harmonicF (n X : ℕ) : ℝ :=
  ∑ q ∈ Icc 1 X, BandTail.F n q / (q : ℝ)

theorem g_unit_interval (n k : ℕ) : 0 ≤ BandTail.g n k ∧ BandTail.g n k ≤ 1 := by
  simp [BandTail.g]
  split_ifs <;> norm_num

private theorem harmonicG_sub (n : ℕ) {A B : ℕ} (hAB : A ≤ B) :
    harmonicG n B - harmonicG n A =
      ∑ k ∈ Ioc A B, BandTail.g n k / (k : ℝ) := by
  have h := BandTail.prefix_split (fun k => BandTail.g n k / (k : ℝ)) hAB
  unfold harmonicG
  linarith

theorem harmonicG_mono (n : ℕ) : Monotone (harmonicG n) := by
  intro A B hAB
  have h := harmonicG_sub n hAB
  have hn : 0 ≤ ∑ k ∈ Ioc A B, BandTail.g n k / (k : ℝ) :=
    sum_nonneg fun k _ => div_nonneg (g_unit_interval n k).1 (Nat.cast_nonneg _)
  linarith

theorem g_boundary_le_mean (n X d : ℕ) (hX : 0 < X) (hd : 0 < d) :
    harmonicG n X - harmonicG n (X/d) ≤ (d : ℝ) * BandTail.gAvg n X := by
  have hXR : (0 : ℝ) < X := by exact_mod_cast hX
  have hsub : Ioc (X/d) X ⊆ Icc 1 X := by
    intro k hk
    exact mem_Icc.mpr ⟨Nat.succ_le_of_lt ((Nat.zero_le (X/d)).trans_lt (mem_Ioc.mp hk).1), (mem_Ioc.mp hk).2⟩
  rw [harmonicG_sub n (Nat.div_le_self X d)]
  calc
    _ ≤ ∑ k ∈ Ioc (X/d) X, BandTail.g n k * ((d : ℝ)/X) := by
      apply sum_le_sum
      intro k hk
      have hkR : (0 : ℝ) < k := by exact_mod_cast Nat.zero_lt_of_lt (mem_Ioc.mp hk).1
      have hxk := (Nat.div_lt_iff_lt_mul hd).mp (mem_Ioc.mp hk).1
      have hxkR : (X : ℝ) ≤ k * d := by exact_mod_cast hxk.le
      have hcoeff : (1 : ℝ)/(k : ℝ) ≤ (d : ℝ)/X :=
        (div_le_div_iff₀ hkR hXR).mpr (by nlinarith)
      simpa only [div_eq_mul_inv, one_mul] using
        mul_le_mul_of_nonneg_left hcoeff (g_unit_interval n k).1
    _ ≤ ∑ k ∈ Icc 1 X, BandTail.g n k * ((d : ℝ)/X) :=
      sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => mul_nonneg (g_unit_interval n k).1 (by positivity))
    _ = _ := by
      rw [← sum_mul]
      unfold BandTail.gAvg BandTail.gSum
      ring

theorem g_boundary_le_log (n X d : ℕ) (hd : 0 < d) :
    harmonicG n X - harmonicG n (X/d) ≤ 1 + Real.log d := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hlogd : 0 ≤ Real.log (d : ℝ) := Real.log_nonneg (by exact_mod_cast hd)
  by_cases hX : X = 0
  · simp [hX, harmonicG]
    positivity
  have hXR : (0 : ℝ) < X := by exact_mod_cast Nat.pos_of_ne_zero hX
  have hfloor := Nat.div_le_self X d
  have hQ : (0 : ℝ) < ((X / d : ℕ) : ℝ) + 1 := by positivity
  have hdiv : (X : ℝ) / (((X / d : ℕ) : ℝ) + 1) ≤ d := by
    apply (div_le_iff₀ hQ).mpr
    exact_mod_cast (Nat.lt_mul_div_succ X hd).le
  have hlogs : Real.log (X : ℝ) - Real.log (((X / d : ℕ) : ℝ) + 1) ≤ Real.log d := by
    rw [← Real.log_div hXR.ne' hQ.ne']
    exact Real.log_le_log (div_pos hXR hQ) hdiv
  have hH := harmonic_le_one_add_log X
  have hL := log_add_one_le_harmonic (X/d)
  have hsum : (∑ k ∈ Ioc (X/d) X, (k : ℝ)⁻¹) =
      (harmonic X:ℝ) - (harmonic (X/d):ℝ) := by
    simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    have hp := BandTail.prefix_split (fun k : ℕ => (k : ℝ)⁻¹) hfloor
    linarith
  rw [harmonicG_sub n hfloor]
  calc
    _ ≤ ∑ k ∈ Ioc (X/d) X, (k : ℝ)⁻¹ := by
      apply sum_le_sum
      intro k _
      rw [div_eq_mul_inv]
      exact mul_le_of_le_one_left (inv_nonneg.mpr (Nat.cast_nonneg k)) (g_unit_interval n k).2
    _ = _ := hsum
    _ ≤ _ := by
      rw [Nat.cast_add, Nat.cast_one] at hL
      linarith

theorem harmonic_doubling_lower (n A : ℕ) (hA : 0 < A) (t η : ℝ)
    (hlo : |BandTail.gAvg n A - t| ≤ η)
    (hhi : |BandTail.gAvg n (2*A) - t| ≤ η) :
    t/2 - (3/2)*η ≤ harmonicG n (2*A) - harmonicG n A := by
  have hAB : A ≤ 2*A := by omega
  have hAR : (0 : ℝ) < A := by exact_mod_cast hA
  have hBA := BandTail.prefix_split (BandTail.g n) hAB
  change BandTail.gSum n (2*A) = BandTail.gSum n A + _ at hBA
  have hweak : BandTail.gAvg n (2*A) - BandTail.gAvg n A / 2 ≤
      harmonicG n (2*A) - harmonicG n A := by
    rw [harmonicG_sub n hAB]
    calc
      _ = (∑ j ∈ Ioc A (2*A), BandTail.g n j) / ((2*A : ℕ) : ℝ) := by
        unfold BandTail.gAvg
        rw [← sub_eq_of_eq_add hBA]
        push_cast
        field_simp; ring
      _ ≤ _ := by
        rw [sum_div]
        apply sum_le_sum
        intro k hk
        apply div_le_div_of_nonneg_left (g_unit_interval n k).1
        · exact_mod_cast hA.trans (mem_Ioc.mp hk).1
        · exact_mod_cast (mem_Ioc.mp hk).2
  linarith [(abs_le.mp hlo).2, (abs_le.mp hhi).1]

theorem harmonic_dyadic_lower (n : ℕ) (t η : ℝ) :
    ∀ (L A : ℕ), 0 < A →
      (∀ j ≤ L, |BandTail.gAvg n (2^j*A) - t| ≤ η) →
      (L : ℝ) * (t/2 - (3/2)*η) ≤ harmonicG n (2^L*A) - harmonicG n A := by
  intro L
  induction L with
  | zero => simp
  | succ L ih =>
    intro A hA hnear
    have hm := ih A hA (fun j hj => hnear j (by omega))
    have ht : 0 < 2^L*A := Nat.mul_pos (pow_pos (by decide) _) hA
    have hh := harmonic_doubling_lower n (2^L*A) ht t η (hnear L (by omega)) (by
      simpa only [pow_succ', mul_assoc] using hnear (L+1) le_rfl)
    push_cast
    rw [pow_succ', mul_assoc]
    linarith

end GoldbachGRHSignedModel

namespace GoldbachGRHSignedModel
open Finset Filter ArithmeticFunction
open scoped Topology
private theorem sum_divisors_reindex (X : ℕ) (f : ℕ × ℕ → ℝ) :
    (∑ q ∈ Icc 1 X, ∑ v ∈ q.divisorsAntidiagonal, f v) =
      ∑ d ∈ Icc 1 X, ∑ k ∈ Icc 1 (X/d), f (d,k) := by
  classical
  let S := Icc 1 X
  have hf (q : ℕ) (hq : q ∈ S) :
      q.divisorsAntidiagonal = (S ×ˢ S).filter (fun ab : ℕ × ℕ => ab.1*ab.2=q) := by
    obtain ⟨hq0,hqQ⟩ := mem_Icc.mp hq
    ext ab
    constructor
    · intro hab
      have hm (a : ℕ) (ha : a ∈ q.divisors) : a ∈ S :=
        mem_Icc.mpr ⟨Nat.pos_of_mem_divisors ha,(Nat.le_of_dvd hq0 (Nat.dvd_of_mem_divisors ha)).trans hqQ⟩
      exact mem_filter.mpr ⟨mem_product.mpr ⟨hm _ (Nat.fst_mem_divisors_of_mem_antidiagonal hab),
        hm _ (Nat.snd_mem_divisors_of_mem_antidiagonal hab)⟩,(Nat.mem_divisorsAntidiagonal.mp hab).1⟩
    · intro hh; exact Nat.mem_divisorsAntidiagonal.mpr ⟨(mem_filter.mp hh).2,by omega⟩
  calc
    _ = ∑ q ∈ S, ∑ v ∈ (S ×ˢ S).filter (fun ab : ℕ × ℕ => ab.1*ab.2=q), f v :=
      sum_congr rfl (fun q hq => by rw [hf q hq])
    _ = ∑ v ∈ (S ×ˢ S).filter (fun ab : ℕ × ℕ => ab.1*ab.2 ∈ S), f v :=
      sum_fiberwise_eq_sum_filter _ _ _ _
    _ = _ := by
      rw [sum_filter,sum_product]
      apply sum_congr rfl
      intro d hd
      have hd0 := (mem_Icc.mp hd).1
      have hkd : (S.filter fun k => d*k∈S)=Icc 1 (X/d) := by
        ext k
        simp only [S,mem_filter,mem_Icc]
        constructor
        · rintro ⟨⟨hk,_⟩,_,hdk⟩
          exact ⟨hk,(Nat.le_div_iff_mul_le hd0).mpr (by simpa [mul_comm] using hdk)⟩
        · rintro ⟨hk,hkx⟩
          exact ⟨⟨hk,hkx.trans (Nat.div_le_self _ _)⟩,Nat.mul_pos hd0 hk,by simpa [mul_comm] using (Nat.le_div_iff_mul_le hd0).mp hkx⟩
      rw [←sum_filter,hkd]

theorem harmonicF_convolution (n X : ℕ) :
    harmonicF n X = ∑ d ∈ Icc 1 X, BandTail.z n d * harmonicG n (X/d) := by
  let f := fun v : ℕ × ℕ => BandTail.z n v.1 * (BandTail.g n v.2 / (v.2 : ℝ))
  calc
    _ = ∑ q ∈ Icc 1 X, ∑ v ∈ q.divisorsAntidiagonal, f v := by
      apply sum_congr rfl
      intro q _
      rw [BandTail.convolution n,mul_comm (BandTail.g n) (BandTail.h n),ArithmeticFunction.mul_apply,sum_div]
      apply sum_congr rfl
      intro v hv
      change BandTail.h n v.1*BandTail.g n v.2/(q:ℝ) =
        (BandTail.h n v.1/(v.1:ℝ))*(BandTail.g n v.2/(v.2:ℝ))
      rw [←(Nat.mem_divisorsAntidiagonal.mp hv).1, Nat.cast_mul,div_eq_mul_inv,mul_inv]
      simp only [div_eq_mul_inv]
      ring
    _ = ∑ d ∈ Icc 1 X, ∑ k ∈ Icc 1 (X/d), f (d,k) := sum_divisors_reindex X f
    _ = _ := by simp [f,harmonicG,mul_sum]

theorem absolute_prefix_le (n X : ℕ) :
    (∑ q ∈ Icc 1 X, |BandTail.F n q|) ≤ BandTail.universal * (X:ℝ) := by
  classical
  let f : ℕ × ℕ → ℝ := fun v => |BandTail.h n v.1|
  calc
    _ ≤ ∑ q ∈ Icc 1 X, ∑ v ∈ q.divisorsAntidiagonal, f v := by
      apply sum_le_sum
      intro q _
      rw [BandTail.convolution n,mul_comm (BandTail.g n) (BandTail.h n),ArithmeticFunction.mul_apply]
      refine (abs_sum_le_sum_abs _ _).trans ?_
      apply sum_le_sum
      intro v _
      rw [abs_mul,abs_of_nonneg (g_unit_interval n v.2).1]
      exact mul_le_of_le_one_right (abs_nonneg _) (g_unit_interval n v.2).2
    _ = ∑ d ∈ Icc 1 X, ∑ k ∈ Icc 1 (X/d), f (d,k) := sum_divisors_reindex X f
    _ ≤ ∑ d ∈ Icc 1 X, |BandTail.z n d| * (X:ℝ) := by
      apply sum_le_sum
      intro d hd
      have hd0 := (mem_Icc.mp hd).1
      have hdR : (0:ℝ)<d := by exact_mod_cast hd0
      have hdiv : ((X/d:ℕ):ℝ) ≤ (X:ℝ)/(d:ℝ) := by
        apply (le_div_iff₀ hdR).2
        exact_mod_cast Nat.div_mul_le_self X d
      calc
        _ = ((X/d:ℕ):ℝ)*|BandTail.h n d| := by
          simp [f,Nat.card_Icc,nsmul_eq_mul]
        _ ≤ ((X:ℝ)/(d:ℝ))*|BandTail.h n d| := mul_le_mul_of_nonneg_right hdiv (abs_nonneg _)
        _ = _ := by
          rw [BandTail.z,ArithmeticFunction.coe_mk,abs_div,abs_of_pos hdR]
          ring
    _ = (∑ d ∈ Icc 1 X, |BandTail.z n d|) * (X:ℝ) := (sum_mul ..).symm
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      simpa using BandTail.uniformTail n 1 (Icc 1 X) (by decide) (fun d hd => (mem_Icc.mp hd).1)

theorem harmonic_convolution_interval (n K X : ℕ) (hKX : K ≤ X) :
    (∑ q ∈ Ioc K X, BandTail.F n q / (q:ℝ)) =
      ∑ d ∈ Icc 1 X, BandTail.z n d * (harmonicG n (X/d)-harmonicG n (K/d)) := by
  have hsub := BandTail.prefix_split (fun q => BandTail.F n q / (q:ℝ)) hKX
  have hsub' : (∑ q ∈ Ioc K X, BandTail.F n q / (q:ℝ)) = harmonicF n X-harmonicF n K := by
    unfold harmonicF
    linarith
  have hK :
      ∑ d ∈ Icc 1 K, BandTail.z n d * harmonicG n (K/d) =
        ∑ d ∈ Icc 1 X, BandTail.z n d * harmonicG n (K/d) := by
    apply sum_subset (Icc_subset_Icc_right hKX)
    intro d hd hnot
    have hdK : K<d := by
      simp only [mem_Icc,not_and] at hnot
      have hd' := mem_Icc.mp hd
      omega
    simp [Nat.div_eq_of_lt hdK,harmonicG]
  rw [hsub',harmonicF_convolution n X,harmonicF_convolution n K,hK,←sum_sub_distrib]
  apply sum_congr rfl
  intro d _
  ring

theorem uniform_log_tail (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ J : ℕ in atTop, 0 < J ∧ ∀ n : ℕ, ∀ s : Finset ℕ, (∀ d ∈ s, J ≤ d) →
      (∑ d ∈ s, |BandTail.z n d| *(1+Real.log d)) ≤ ε := by
  have hC : 0 < BandTail.universal := Real.exp_pos _
  let τ := ε/(2*BandTail.universal)
  have hτ : 0<τ := by dsimp [τ]; positivity
  have hc := tendsto_natCast_atTop_atTop (R:=ℝ)
  have hm := ((isLittleO_log_rpow_rpow_atTop (1:ℝ) (by norm_num : (0:ℝ)<1/4)).comp_tendsto hc).bound hτ
  have hlog := (Real.tendsto_log_atTop.comp hc).eventually_ge_atTop (1:ℝ)
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hm.and hlog)
  filter_upwards [eventually_ge_atTop (max N 1)] with J hJ
  have hJ' : 0<J := lt_of_lt_of_le (by decide : 0<1) ((le_max_right N 1).trans hJ)
  refine ⟨hJ',?_⟩
  intro n s hs
  have hbound (d : ℕ) (hd : d ∈ s) : |BandTail.z n d| *(1+Real.log d) ≤
      (ε/BandTail.universal)*BandTail.w n d := by
    have hdJ := hs d hd
    have hd0 := hJ'.trans_le hdJ
    have hz : (0:ℝ)<(d:ℝ)^(1/4:ℝ) := Real.rpow_pos_of_pos (by exact_mod_cast hd0) _
    obtain ⟨ha,hb⟩ := hN d ((le_max_left N 1).trans (hJ.trans hdJ))
    change ‖(Real.log (d:ℝ))^(1:ℝ)‖ ≤ τ*‖(d:ℝ)^(1/4:ℝ)‖ at ha
    change 1 ≤ Real.log (d:ℝ) at hb
    rw [Real.rpow_one,Real.norm_eq_abs,abs_of_nonneg (by linarith : 0≤Real.log (d:ℝ)),
      Real.norm_eq_abs,abs_of_pos hz] at ha
    have hh : 1+Real.log (d:ℝ) ≤ (ε/BandTail.universal)*(d:ℝ)^(1/4:ℝ) := by
      have hτ' : 2*τ=ε/BandTail.universal := by dsimp [τ]; ring
      rw [←hτ',mul_assoc]
      linarith
    calc
      _ ≤ (BandTail.w n d/(d:ℝ)^(1/4:ℝ))*(1+Real.log d) :=
        mul_le_mul_of_nonneg_right (BandTail.tailTerm n d d hd0 le_rfl) (by linarith)
      _ ≤ (BandTail.w n d/(d:ℝ)^(1/4:ℝ))*((ε/BandTail.universal)*(d:ℝ)^(1/4:ℝ)) :=
        mul_le_mul_of_nonneg_left hh (div_nonneg (BandTail.w_nonneg n d) hz.le)
      _ = _ := by field_simp
  have hu : ∑ d ∈ s, BandTail.w n d ≤ BandTail.universal := by
    apply le_trans _ (BandTail.uniformPrefix n (s.sup id))
    apply sum_le_sum_of_subset_of_nonneg
    · intro d hd
      exact mem_Icc.mpr ⟨hJ'.trans_le (hs d hd),le_sup (f:=id) hd⟩
    · intro d _ _
      exact BandTail.w_nonneg n d
  calc
    _ ≤ ∑ d ∈ s, (ε/BandTail.universal)*BandTail.w n d := sum_le_sum hbound
    _ = (ε/BandTail.universal)*(∑ d ∈ s,BandTail.w n d) := (mul_sum ..).symm
    _ ≤ (ε/BandTail.universal)*BandTail.universal := mul_le_mul_of_nonneg_left hu (by positivity)
    _ = _ := by field_simp

end GoldbachGRHSignedModel

namespace GoldbachGRHSignedModel
open Finset Filter
open scoped Topology
private theorem harmonic_diff_boundary (n K X d : ℕ) :
    harmonicG n (X/d) - harmonicG n (K/d) -
      (harmonicG n X - harmonicG n K) =
      (harmonicG n K - harmonicG n (K/d)) -
      (harmonicG n X - harmonicG n (X/d)) := by ring

private theorem harmonic_diff_abs (n K X d : ℕ) :
    |harmonicG n (X/d) - harmonicG n (K/d) -
      (harmonicG n X - harmonicG n K)| ≤
      (harmonicG n K - harmonicG n (K/d)) +
      (harmonicG n X - harmonicG n (X/d)) := by
  rw [harmonic_diff_boundary]
  have hK := sub_nonneg.mpr (harmonicG_mono n (Nat.div_le_self K d))
  have hX := sub_nonneg.mpr (harmonicG_mono n (Nat.div_le_self X d))
  exact abs_le.mpr ⟨by linarith, by linarith⟩

private theorem gAvg_nonneg (n X : ℕ) : 0 ≤ BandTail.gAvg n X := by
  unfold BandTail.gAvg BandTail.gSum
  exact div_nonneg (sum_nonneg fun k _ => (g_unit_interval n k).1) (by positivity)

theorem harmonic_convolution_lower (n K X J : ℕ) (hK : 0 < K) (hKX : K ≤ X)
    (hJX : J ≤ X) (e : ℝ)
    (hZ : (1/8 : ℝ) ≤ ∑ d ∈ Icc 1 X, BandTail.z n d)
    (hlog : (∑ d ∈ Ioc J X, |BandTail.z n d| * (1 + Real.log d)) ≤ e) :
    (1/8 : ℝ) * (harmonicG n X - harmonicG n K) -
      (J : ℝ) * BandTail.universal * (BandTail.gAvg n K + BandTail.gAvg n X) - 2*e ≤
      ∑ q ∈ Ioc K X, BandTail.F n q / (q:ℝ) := by
  let A := harmonicG n X - harmonicG n K
  let D (d : ℕ) := harmonicG n (X/d) - harmonicG n (K/d) - A
  let t := BandTail.gAvg n K + BandTail.gAvg n X
  have ht := add_nonneg (gAvg_nonneg n K) (gAvg_nonneg n X)
  have hpos := sub_nonneg.mpr (harmonicG_mono n hKX)
  have hlow (d : ℕ) : -(abs (BandTail.z n d) * abs (D d)) ≤ BandTail.z n d * D d := by
    rw [← abs_mul]
    exact neg_abs_le _
  have hsmall : -((J : ℝ) * BandTail.universal * t) ≤ ∑ d ∈ Icc 1 J, BandTail.z n d * D d := by
    have habs (d : ℕ) (hd : d ∈ Icc 1 J) : |D d| ≤ (J : ℝ) * t := by
      have hd0 := (mem_Icc.mp hd).1
      calc
        _ ≤ _ := harmonic_diff_abs n K X d
        _ ≤ (d : ℝ) * t := by
          dsimp [t]
          rw [mul_add]
          exact add_le_add (g_boundary_le_mean n K d hK hd0)
            (g_boundary_le_mean n X d (hK.trans_le hKX) hd0)
        _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast (mem_Icc.mp hd).2) ht
    have hU : (∑ d ∈ Icc 1 J, |BandTail.z n d|) ≤ BandTail.universal := by
      simpa using BandTail.uniformTail n 1 (Icc 1 J) (by decide) (fun d hd => (mem_Icc.mp hd).1)
    calc
      _ = -(BandTail.universal * ((J : ℝ) * t)) := by ring
      _ ≤ -((∑ d ∈ Icc 1 J, |BandTail.z n d|) * ((J : ℝ) * t)) :=
        neg_le_neg (mul_le_mul_of_nonneg_right hU (mul_nonneg (Nat.cast_nonneg J) ht))
      _ = ∑ d ∈ Icc 1 J, -(|BandTail.z n d| * ((J : ℝ) * t)) := by rw [sum_neg_distrib, sum_mul]
      _ ≤ _ := sum_le_sum fun d hd =>
        (neg_le_neg (mul_le_mul_of_nonneg_left (habs d hd) (abs_nonneg _))).trans (hlow d)
  have hlarge : -(2*e) ≤ ∑ d ∈ Ioc J X, BandTail.z n d * D d := by
    have habs (d : ℕ) (hd : d ∈ Ioc J X) : |D d| ≤ 2 * (1 + Real.log d) := by
      have hd0 := (Nat.zero_le J).trans_lt (mem_Ioc.mp hd).1
      calc
        _ ≤ _ := harmonic_diff_abs n K X d
        _ ≤ (1 + Real.log d) + (1 + Real.log d) := by
          exact add_le_add (g_boundary_le_log n K d hd0) (g_boundary_le_log n X d hd0)
        _ = _ := by ring
    calc
      _ ≤ -(2*(∑ d ∈ Ioc J X, |BandTail.z n d| * (1 + Real.log d))) :=
        neg_le_neg (mul_le_mul_of_nonneg_left hlog (by norm_num))
      _ = ∑ d ∈ Ioc J X, -(|BandTail.z n d| * (2 * (1 + Real.log d))) := by
        rw [sum_neg_distrib, mul_sum]
        congr 1
        apply sum_congr rfl
        intro d _
        ring
      _ ≤ _ := sum_le_sum fun d hd =>
        (neg_le_neg (mul_le_mul_of_nonneg_left (habs d hd) (abs_nonneg _))).trans (hlow d)
  have hsplit := BandTail.prefix_split (fun d => BandTail.z n d * D d) hJX
  rw [harmonic_convolution_interval n K X hKX]
  have hrewrite : (∑ d ∈ Icc 1 X, BandTail.z n d *
      (harmonicG n (X/d) - harmonicG n (K/d))) =
      (∑ d ∈ Icc 1 X, BandTail.z n d) * A + ∑ d ∈ Icc 1 X, BandTail.z n d * D d := by
    rw [sum_mul, ←sum_add_distrib]
    apply sum_congr rfl
    intro d _
    dsimp [D]
    ring
  rw [hrewrite, hsplit]
  change (1/8 : ℝ) * A - (J : ℝ)*BandTail.universal*t - 2*e ≤ _
  linarith [mul_le_mul_of_nonneg_right hZ hpos]

end GoldbachGRHSignedModel

namespace GoldbachGRHSignedModel
open Finset Filter
open scoped Topology
theorem harmonic_suffix_floor (ε : ℝ) (hε : 0 < ε) :
    ∃ K₀ : ℕ, ∀ K ≥ K₀, ∀ n X : ℕ, Even n → K ≤ X →
      -ε ≤ ∑ q ∈ Ioc K X, BandTail.F n q / (q:ℝ) := by
  obtain ⟨J,hJ⟩ := eventually_atTop.mp
    (correction_prefix_eighth.and (uniform_log_tail (ε/4) (by positivity)))
  obtain ⟨hJ₀,_⟩ := (hJ J le_rfl).1
  obtain ⟨m,hm⟩ := exists_nat_ge (16 * ((J:ℝ) * BandTail.universal))
  let L := m+1
  let T : ℕ := 2^L
  have hT : 0 < T := pow_pos (by decide) _
  have hC : (1:ℝ) ≤ 2*(T:ℝ) := by
    have ht' : (1:ℝ) ≤ T := by exact_mod_cast hT
    linarith
  have hL : (0:ℝ) < L := by exact_mod_cast (Nat.zero_lt_succ m)
  have hLJ : (J:ℝ)*BandTail.universal ≤ (L:ℝ)/16 := by
    change (J:ℝ)*BandTail.universal ≤ ((m+1:ℕ):ℝ)/16
    push_cast
    linarith
  let η := ε/(L:ℝ)
  have hη : 0 < η := div_pos hε hL
  have hLη : (L:ℝ)*η=ε := by dsimp [η]; field_simp
  obtain ⟨M,hM⟩ := eventually_atTop.mp (BandTail.mean_slow (2*(T:ℝ)) η hC hη)
  have hR : 1 ≤ T*T := Nat.mul_pos hT hT
  obtain ⟨N,hN⟩ := BandTail.uniform_prefix_floor (T*T) hR ε hε
  refine ⟨max J (max M N),?_⟩
  intro K hK₀ n X hn hKX
  have hJK : J ≤ K := (le_max_left J (max M N)).trans hK₀
  have hMK : M ≤ K := ((le_max_left M N).trans (le_max_right J (max M N))).trans hK₀
  have hNK : N ≤ K := ((le_max_right M N).trans (le_max_right J (max M N))).trans hK₀
  have hK : 0 < K := hJ₀.trans_le hJK
  have hKR : (0:ℝ)<K := by exact_mod_cast hK
  by_cases hnear : X ≤ (T*T)*K
  · have hh := BandTail.weighted_prefix_lower K X (BandTail.F n)
      (fun q => (q:ℝ)⁻¹) (ε*(K:ℝ)) hKX (by positivity)
      (fun i _ => by positivity)
      (fun i hi => by
        apply inv_anti₀
        · exact_mod_cast hK.trans_le hi
        · exact_mod_cast Nat.le_succ i)
      (fun i hi hiX => hN K hNK n i hi (hiX.trans hnear))
    have hEq : -(ε*(K:ℝ)*(K:ℝ)⁻¹) = -ε := by field_simp
    rw [hEq] at hh
    simpa [div_eq_mul_inv] using hh
  · let B := X/T
    have hfar : (T*T)*K ≤ X := le_of_lt (lt_of_not_ge hnear)
    have hKB : T*K ≤ B := by
      apply (Nat.le_div_iff_mul_le hT).2
      calc
        T*K*T = (T*T)*K := by ring
        _ ≤ X := hfar
    have hB : 0<B := (Nat.mul_pos hT hK).trans_le hKB
    have hBX : T*B ≤ X := Nat.mul_div_le X T
    have hXT : X ≤ 2*T*B := by
      have hmod := Nat.mod_lt X hT
      have hdiv : X % T + T * B = X := Nat.mod_add_div X T
      have hTB : T ≤ T*B := by
        simpa using Nat.mul_le_mul_left T (show 1≤B from hB)
      have he : 2*T*B=T*B+T*B := by ring
      rw [he]
      omega
    have hdT (j : ℕ) (hj : j≤L) : (2:ℕ)^j≤T := Nat.pow_le_pow_right (by decide) hj
    have hd1 (j : ℕ) : 1≤(2:ℕ)^j := pow_pos (by decide : 0<(2:ℕ)) j
    have hKm (j : ℕ) : K ≤ 2^j*K := by simpa using Nat.mul_le_mul_right K (hd1 j)
    have hBm (j : ℕ) : B ≤ 2^j*B := by simpa using Nat.mul_le_mul_right B (hd1 j)
    have hslowK (j : ℕ) (hj : j≤L) : |BandTail.gAvg n (2^j*K)-BandTail.gAvg n K| ≤ η := by
      apply hM (2^j*K) (hMK.trans (hKm j)) K hK (hKm j) _ n
      have hx : (2:ℕ)^j*K≤T*K := Nat.mul_le_mul_right K (hdT j hj)
      have hx' : (((2:ℕ)^j*K : ℕ):ℝ) ≤ (T:ℝ)*(K:ℝ) := by exact_mod_cast hx
      nlinarith [show (0:ℝ)≤(T:ℝ)*(K:ℝ) by positivity]
    have hslowX (j : ℕ) (hj : j≤L) : |BandTail.gAvg n (2^j*B)-BandTail.gAvg n X| ≤ η := by
      rw [abs_sub_comm]
      apply hM X (hMK.trans hKX) (2^j*B) (hB.trans_le (hBm j))
        ((Nat.mul_le_mul_right B (hdT j hj)).trans hBX) _ n
      have hXj : X ≤ 2*T*(2^j*B) := hXT.trans (Nat.mul_le_mul_left (2*T) (hBm j))
      exact_mod_cast hXj
    have hnearK := harmonic_dyadic_lower n (BandTail.gAvg n K) η L K hK hslowK
    have hnearX := harmonic_dyadic_lower n (BandTail.gAvg n X) η L B hB hslowX
    have hmid := harmonicG_mono n hKB
    have hlast := harmonicG_mono n hBX
    change (L:ℝ)*(BandTail.gAvg n K/2 - (3/2)*η) ≤ harmonicG n (T*K)-harmonicG n K at hnearK
    change (L:ℝ)*(BandTail.gAvg n X/2 - (3/2)*η) ≤ harmonicG n (T*B)-harmonicG n B at hnearX
    have hlong : ((L:ℝ)/2)*(BandTail.gAvg n K+BandTail.gAvg n X)-3*ε ≤
      harmonicG n X-harmonicG n K := by linarith
    have hJX := hJK.trans hKX
    have hZ := (hJ X hJX).1.2 n hn
    have hlog := (hJ J le_rfl).2.2 n (Ioc J X) (fun d hd => (mem_Ioc.mp hd).1.le)
    have hlower := harmonic_convolution_lower n K X J hK hKX hJX (ε/4) hZ hlog
    have hdom := mul_le_mul_of_nonneg_right hLJ
      (add_nonneg (gAvg_nonneg n K) (gAvg_nonneg n X))
    linarith

end GoldbachGRHSignedModel

namespace GoldbachGRHSignedModel
open Finset
theorem coefficient_re_eq (n q : ℕ) (hq : 0 < q) :
    (GoldbachExplicitModeledMajor.coefficient q n).re = BandTail.F n q / (q:ℝ) := by
  have hqR : (q:ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  simp [BandTail.F,hqR]

end GoldbachGRHSignedModel

end GoldbachGRHSignedModel


namespace SqrtArcPrimeEnergy
open Finset MeasureTheory
noncomputable section
noncomputable def phase (x : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

end

end SqrtArcPrimeEnergy

namespace SqrtArcSignedTransfer
noncomputable section
open MeasureTheory Set Finset
open SqrtArcPrimeEnergy (phase)
def ell (n : ℕ) := (Nat.log 2 (n+2))^2

def oldQ (n : ℕ) := ⌊(n:ℝ)^(1/3:ℝ)⌋₊

def newQ (n : ℕ) := ⌊Real.sqrt (n : ℝ) / ((Nat.log 2 (n+2) : ℝ)^4)⌋₊

def width (n Q : ℕ) := 256 * Q * ell n

def cell (n K q a : ℕ) : Set ℝ :=
  {t | |t - (a:ℝ)/q| ≤ (K:ℝ)/((q:ℝ)*n)}

def arcs (n Q : ℕ) : Set ℝ :=
  {t | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Q ∧ a ≤ q ∧ Nat.Coprime a q ∧ t ∈ cell n (width n Q) q a}

def band (n : ℕ) := arcs n (newQ n) \ arcs n (oldQ n)

def region (n : ℕ) := Set.Ioc (0:ℝ) 1 ∩ band n

def μ (n : ℕ) : Measure ℝ := volume.restrict (region n)

def wave (n : ℕ) (t : ℝ) := phase (-(n:ℝ)*t)

def kernel (n : ℕ) (β : ℝ) : ℂ := ∑ k ∈ range (n+1), phase ((k:ℝ)*β)

def localModel (n q a : ℕ) (t : ℝ) : ℂ :=
  (ArithmeticFunction.moebius q : ℂ)/(q.totient : ℂ) * kernel n (t-(a:ℝ)/q)

def model (n : ℕ) : ℝ → ℂ := by
  classical
  exact fun t => ∑ q ∈ Finset.Icc 1 (newQ n), ∑ a ∈ (range (q+1)).filter (Nat.Coprime · q),
    (cell n (width n (newQ n)) q a).indicator (localModel n q a) t

def signed (n : ℕ) (F : ℝ → ℂ) := ∫ t, F t ^ 2 * wave n t ∂μ n

/-- The arithmetic child concerns only a rational model, with no prime weights. -/
def ModelFloorChild : Prop := ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n →
  -(δ * (n:ℝ)) ≤ (signed n (model n)).re

end

end SqrtArcSignedTransfer


namespace SqrtArcScales
private theorem pow_mono {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (n : ℕ) :
    a ^ n ≤ b ^ n := by
  rw [← Real.rpow_natCast, ← Real.rpow_natCast]
  exact Real.rpow_le_rpow ha hab (Nat.cast_nonneg n)

private theorem pow24_step (L : ℕ) (hL : 200 ≤ L) :
    ((L + 1 : ℕ) : ℝ) ^ 24 ≤ 2 * (L : ℝ) ^ 24 := by
  have hLr : (200 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have h1 : ((L + 1 : ℕ) : ℝ) ≤ (201 / 200 : ℝ) * (L : ℝ) := by
    push_cast
    nlinarith
  have h2 : ((L + 1 : ℕ) : ℝ) ^ 24 ≤ ((201 / 200 : ℝ) * (L : ℝ)) ^ 24 :=
    pow_mono (by positivity) h1 24
  rw [mul_pow] at h2
  have h3 : (201 / 200 : ℝ) ^ 24 ≤ 2 := by norm_num
  calc ((L + 1 : ℕ) : ℝ) ^ 24 ≤ (201 / 200 : ℝ) ^ 24 * (L : ℝ) ^ 24 := h2
    _ ≤ 2 * (L : ℝ) ^ 24 := mul_le_mul_of_nonneg_right h3 (by positivity)

private theorem key_aux :
    ∀ k : ℕ, 64 * ((200 + k : ℕ) : ℝ) ^ 24 ≤ (2 : ℝ) ^ ((200 + k : ℕ) - 1) := by
  intro k
  induction k with
  | zero => norm_num
  | succ k ih =>
    have hL : (200 : ℕ) ≤ 200 + k := by omega
    have hstep := pow24_step (200 + k) hL
    have hrw : (200 + (k + 1) : ℕ) = (200 + k) + 1 := by omega
    rw [hrw]
    calc 64 * (((200 + k) + 1 : ℕ) : ℝ) ^ 24 ≤ 64 * (2 * ((200 + k : ℕ) : ℝ) ^ 24) :=
          mul_le_mul_of_nonneg_left hstep (by norm_num)
      _ = 2 * (64 * ((200 + k : ℕ) : ℝ) ^ 24) := by ring
      _ ≤ 2 * (2 : ℝ) ^ ((200 + k : ℕ) - 1) :=
          mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = (2 : ℝ) ^ (((200 + k) + 1 : ℕ) - 1) := by
          calc 2 * (2 : ℝ) ^ ((200 + k : ℕ) - 1) = (2 : ℝ) ^ (((200 + k : ℕ) - 1) + 1) := by
                rw [pow_succ]; ring
            _ = (2 : ℝ) ^ (((200 + k) + 1 : ℕ) - 1) := by congr 1; omega

private theorem key (L : ℕ) (hL : 200 ≤ L) :
    64 * (L : ℝ) ^ 24 ≤ (2 : ℝ) ^ (L - 1) := by
  have h := key_aux (L - 200)
  rwa [Nat.add_sub_of_le hL] at h

noncomputable def X (n : ℕ) := ⌊(n : ℝ) ^ (1/3 : ℝ)⌋₊

noncomputable def U (n : ℕ) := ⌊Real.sqrt (n : ℝ) / ((Nat.log 2 (n+2) : ℝ) ^ 4)⌋₊

def L (n : ℕ) := (Nat.log 2 (n+2)) ^ 2

noncomputable def K (n : ℕ) := 256 * U n * L n

private theorem separation (n : ℕ) (hn : 2 ^ 200 ≤ n) :
    X n < U n ∧ 2 * K n * U n < n := by
  unfold X K U L
  set L := Nat.log 2 (n + 2) with hLdef
  set m := ⌊Real.sqrt (n:ℝ) / ((L:ℝ)^4)⌋₊ with hmdef
  have hp200 : (0:ℕ) < 2 ^ 200 := by positivity
  have hn0 : 0 < n := lt_of_lt_of_le hp200 hn
  have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn0
  have hn2 : (2:ℕ)^200 ≤ n + 2 := by omega
  have hL200 : 200 ≤ L := Nat.le_log_of_pow_le (by norm_num) hn2
  have hL200r : (200:ℝ) ≤ (L:ℝ) := by exact_mod_cast hL200
  have hLpos : (0:ℝ) < (L:ℝ) := by exact_mod_cast (by omega : 0 < L)
  have hLne : (L:ℝ) ≠ 0 := ne_of_gt hLpos
  have hpow : (2:ℕ)^L ≤ n + 2 := Nat.pow_log_le_self 2 (by omega)
  have hkey : 64 * (L:ℝ)^24 ≤ (2:ℝ)^(L-1) := key L hL200
  have h2L : (2:ℝ)^L = 2 * (2:ℝ)^(L-1) := by
    have h : (L - 1) + 1 = L := by omega
    conv_lhs => rw [← h]
    rw [pow_succ]
    ring
  have hcastL : ((2:ℕ)^L : ℝ) = (2:ℝ)^L := by push_cast; ring
  have hlow : 128 * (L:ℝ)^24 ≤ (n:ℝ) + 2 := by
    have h1 : (128:ℝ) * (L:ℝ)^24 ≤ (2:ℝ)^L := by
      rw [h2L]; linarith
    have h2 : ((2:ℕ)^L : ℝ) ≤ (n:ℝ) + 2 := by exact_mod_cast hpow
    rw [hcastL] at h2
    linarith
  have h64 : (2:ℝ) ≤ 64 * (L:ℝ)^24 := by
    have h1 : (200:ℝ)^24 ≤ (L:ℝ)^24 := pow_mono (by norm_num) hL200r 24
    have h2 : (1:ℝ) ≤ (200:ℝ)^24 := by norm_num
    linarith
  have hnreal : (64:ℝ) * (L:ℝ)^24 ≤ (n:ℝ) := by linarith
  have h64r : (64:ℝ)^(1/6:ℝ) = 2 := by
    rw [show (64:ℝ) = (2:ℝ)^6 by norm_num, ← Real.rpow_natCast,
      ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ (2:ℝ)),
      show ((6:ℕ):ℝ) * (1/6:ℝ) = 1 by norm_num, Real.rpow_one]
  have hL24 : ((L:ℝ)^24)^(1/6:ℝ) = (L:ℝ)^4 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0:ℝ) ≤ (L:ℝ)),
      show ((24:ℕ):ℝ) * (1/6:ℝ) = ((4:ℕ):ℝ) by norm_num]
    rw [Real.rpow_natCast]
  have hroot : 2 * (L:ℝ)^4 ≤ (n:ℝ)^(1/6:ℝ) := by
    have h1 : (64 * (L:ℝ)^24)^(1/6:ℝ) ≤ (n:ℝ)^(1/6:ℝ) :=
      Real.rpow_le_rpow (by positivity) hnreal (by norm_num)
    rw [Real.mul_rpow (by norm_num) (by positivity), h64r, hL24] at h1
    exact h1
  have hn13 : 1 ≤ (n:ℝ)^(1/3:ℝ) := by
    have h1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
    calc (1:ℝ) = (1:ℝ)^(1/3:ℝ) := by rw [Real.one_rpow]
      _ ≤ (n:ℝ)^(1/3:ℝ) := Real.rpow_le_rpow (by norm_num) h1 (by norm_num)
  have hsqrt : Real.sqrt (n:ℝ) = (n:ℝ)^(1/3:ℝ) * (n:ℝ)^(1/6:ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add (by positivity : (0:ℝ) < (n:ℝ))]
    congr 1
    norm_num
  have hmain : (n:ℝ)^(1/3:ℝ) + 1 ≤ Real.sqrt (n:ℝ) / ((L:ℝ)^4) := by
    rw [hsqrt, le_div_iff₀ (by positivity : (0:ℝ) < (L:ℝ)^4)]
    have hA : (0:ℝ) ≤ (n:ℝ)^(1/3:ℝ) := by positivity
    have hL4 : (0:ℝ) ≤ (L:ℝ)^4 := by positivity
    have key1 : (L:ℝ)^4 ≤ (n:ℝ)^(1/3:ℝ) * (L:ℝ)^4 := by
      calc (L:ℝ)^4 = 1 * (L:ℝ)^4 := by ring
        _ ≤ (n:ℝ)^(1/3:ℝ) * (L:ℝ)^4 := mul_le_mul_of_nonneg_right hn13 hL4
    have key2 : (n:ℝ)^(1/3:ℝ) * (2 * (L:ℝ)^4) ≤ (n:ℝ)^(1/3:ℝ) * (n:ℝ)^(1/6:ℝ) :=
      mul_le_mul_of_nonneg_left hroot hA
    calc ((n:ℝ)^(1/3:ℝ) + 1) * (L:ℝ)^4
        = (n:ℝ)^(1/3:ℝ) * (L:ℝ)^4 + (L:ℝ)^4 := by ring
      _ ≤ (n:ℝ)^(1/3:ℝ) * (L:ℝ)^4 + (n:ℝ)^(1/3:ℝ) * (L:ℝ)^4 := by
          linarith [key1]
      _ = (n:ℝ)^(1/3:ℝ) * (2 * (L:ℝ)^4) := by ring
      _ ≤ (n:ℝ)^(1/3:ℝ) * (n:ℝ)^(1/6:ℝ) := key2
  have hfloor1 : ⌊(n:ℝ)^(1/3:ℝ)⌋₊ < m := by
    have h1 := Nat.floor_le (by positivity : (0:ℝ) ≤ (n:ℝ)^(1/3:ℝ))
    have h2 := Nat.lt_floor_add_one (Real.sqrt (n:ℝ) / ((L:ℝ)^4))
    have h3 : ((⌊(n:ℝ)^(1/3:ℝ)⌋₊ : ℕ) : ℝ) + 1 ≤ Real.sqrt (n:ℝ) / ((L:ℝ)^4) := by
      linarith
    have h4 : Real.sqrt (n:ℝ) / ((L:ℝ)^4) < ((m : ℕ) : ℝ) + 1 := h2
    have h6 : ((⌊(n:ℝ)^(1/3:ℝ)⌋₊ : ℕ) : ℝ) < ((m : ℕ) : ℝ) := by linarith
    exact_mod_cast h6
  have hbound : 512 * (m:ℝ)^2 * (L:ℝ)^2 < (n:ℝ) := by
    have hmle : (m:ℝ) ≤ Real.sqrt (n:ℝ) / ((L:ℝ)^4) := Nat.floor_le (by positivity)
    have hm0 : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg _
    have hy0 : (0:ℝ) ≤ Real.sqrt (n:ℝ) / ((L:ℝ)^4) := by positivity
    have hm2 : (m:ℝ)^2 ≤ (Real.sqrt (n:ℝ) / ((L:ℝ)^4))^2 := by
      have hx := mul_self_le_mul_self hm0 hmle
      simpa [pow_two] using hx
    have hsq : (Real.sqrt (n:ℝ))^2 = (n:ℝ) := Real.sq_sqrt (by positivity)
    have hL6 : (512:ℝ) < (L:ℝ)^6 := by
      have h1 : (200:ℝ)^6 ≤ (L:ℝ)^6 := pow_mono (by norm_num) hL200r 6
      have h2 : (512:ℝ) < (200:ℝ)^6 := by norm_num
      linarith
    calc 512 * (m:ℝ)^2 * (L:ℝ)^2 ≤ 512 * ((Real.sqrt (n:ℝ) / ((L:ℝ)^4))^2) * (L:ℝ)^2 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm2 (by norm_num)) (by positivity)
      _ = 512 * (n:ℝ) / (L:ℝ)^6 := by
          rw [div_pow, hsq]
          field_simp [hLne]
      _ < (n:ℝ) := by
          rw [div_lt_iff₀ (by positivity : (0:ℝ) < (L:ℝ)^6)]
          have h3 := mul_lt_mul_of_pos_right hL6 hnpos
          linarith
  have hfloor2 : 2 * (256 * m * (L^2)) * m < n := by
    have hcast : ((2 * (256 * m * (L^2)) * m : ℕ) : ℝ) = 512 * (m:ℝ)^2 * (L:ℝ)^2 := by
      push_cast
      ring
    have h1 : ((2 * (256 * m * (L^2)) * m : ℕ) : ℝ) < (n:ℝ) := by
      rw [hcast]; exact hbound
    exact_mod_cast h1
  exact ⟨hfloor1, hfloor2⟩

/-- A single explicit starting point for any requested old denominator and
squared binary-log cutoff. -/
def cutoff (B T : ℕ) := max (2 ^ 200) (max ((max B 1)^3) (2^T))

theorem bounds (B T n : ℕ) (hn : cutoff B T ≤ n) :
    B ≤ X n ∧ T ≤ L n ∧ 1 ≤ X n ∧ X n ≤ U n ∧ 0 < n ∧
      2 * K n * U n < n ∧ 2 * K n ≤ n := by
  have hsep := separation n ((le_max_left _ _).trans hn)
  have hmax := (le_max_right _ _).trans hn
  have hc : (max B 1)^3 ≤ n := (le_max_left _ _).trans hmax
  have ht : 2^T ≤ n := (le_max_right _ _).trans hmax
  have hcube : (max B 1 : ℕ) ≤ X n := by
    apply Nat.le_floor
    have hcR : ((max B 1 : ℕ) : ℝ)^3 ≤ (n : ℝ) := by exact_mod_cast hc
    have hr := Real.rpow_le_rpow (by positivity : (0:ℝ) ≤ ((max B 1 : ℕ) : ℝ)^3)
      hcR (by norm_num : (0:ℝ) ≤ 1/3)
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _),
      show ((3 : ℕ) : ℝ) * (1/3 : ℝ) = 1 by norm_num, Real.rpow_one] at hr
    exact hr
  have hlog : T ≤ Nat.log 2 (n+2) := Nat.le_log_of_pow_le (by norm_num) (by omega)
  have hsquare : T ≤ L n := hlog.trans (Nat.le_self_pow (by decide) _)
  have hX := (le_max_right B 1).trans hcube
  have hU := hX.trans hsep.1.le
  have hpos : 0 < n := Nat.zero_lt_of_lt hsep.2
  have hK : 2 * K n ≤ 2 * K n * U n := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (2 * K n) hU
  exact ⟨(le_max_left B 1).trans hcube, hsquare, hX, hsep.1.le, hpos, hsep.2, hK.trans hsep.2.le⟩

end SqrtArcScales


namespace SqrtArcModelBridge
noncomputable section
open Finset MeasureTheory
open GoldbachGRHArcs (arc cap centers cell radius)
open GoldbachGRHKernel (mass)
open GoldbachExplicitModeledMajor (coefficient)
open GoldbachFourthMoment (phase)
def patched (n U K : ℕ) (t : ℝ) : ℂ := by
  classical
  exact ∑ i ∈ centers U, (arc n K i).indicator (GoldbachGRHModel.model n i) t

def integrand (n : ℕ) (F : ℝ → ℂ) (t : ℝ) : ℂ := F t ^ 2 * phase (-(n:ℝ)*t)

def clipped (n X H : ℕ) := Set.Ioc (0:ℝ) 1 ∩ cap n X H

def massSum (n X H : ℕ) : ℂ :=
  ∑ q ∈ Icc 1 X, coefficient q n * (mass n (radius n H q) : ℂ)

/-- On every inner arc the outer piecewise model equals the same local kernel. -/
theorem patched_on_arc {n X H U K : ℕ} (hXU : X ≤ U) (hHK : H ≤ K)
    (hbudget : 2*K*U < n) {i : ℕ × ℕ} (hi : i ∈ centers X) {t : ℝ}
    (hit : t ∈ arc n H i) : patched n U K t = GoldbachGRHModel.model n i t := by
  classical
  have hi' := GoldbachGRHArcs.centers_mono hXU hi
  have hit' := GoldbachGRHArcs.arc_mono hHK i hit
  unfold patched
  rw [sum_eq_single_of_mem i hi']
  · exact Set.indicator_of_mem hit' _
  · intro j hj hji
    apply Set.indicator_of_notMem
    intro hjt
    exact hji (GoldbachGRHArcs.common_arc_unique hbudget hj hi' hjt hit')

theorem frozen_model (n : ℕ) :
    patched n (SqrtArcSignedTransfer.newQ n)
      (SqrtArcSignedTransfer.width n (SqrtArcSignedTransfer.newQ n)) =
    SqrtArcSignedTransfer.model n := by
  classical
  funext t
  unfold patched SqrtArcSignedTransfer.model
  rw [GoldbachGRHArcs.sum_centers_eq]
  refine sum_congr rfl fun q _ => sum_congr rfl fun a _ => ?_
  have hm : GoldbachGRHModel.model n (q,a) = SqrtArcSignedTransfer.localModel n q a := by
    funext u
    unfold GoldbachGRHModel.model SqrtArcSignedTransfer.localModel
    rw [GoldbachGRHKernel.kernel_eq_sum]
    rfl
  rw [hm]
  rfl

private theorem clipped_union {n X H : ℕ} (hb : 2*H*X < n) :
    clipped n X H = ⋃ i ∈ centers X, cell n 0 H i := by
  have hempty : cap n 0 0 = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro t ht
    obtain ⟨i,hi,_⟩ := GoldbachGRHArcs.mem_cap.mp ht
    obtain ⟨h1,h0,_⟩ := GoldbachGRHArcs.mem_centers.mp hi
    omega
  rw [GoldbachGRHArcs.cells_eq (Nat.zero_le X) (Nat.zero_le H) hb, hempty,
    Set.sdiff_empty, clipped, Set.inter_comm]

private theorem local_integrable {n X H U K : ℕ} (hXU : X ≤ U) (hHK : H ≤ K)
    (hbudget : 2*K*U < n) {i : ℕ × ℕ} (hi : i ∈ centers X) :
    IntegrableOn (integrand n (patched n U K)) (cell n 0 H i) := by
  have hc : Continuous (integrand n (GoldbachGRHModel.model n i)) := by
    unfold integrand phase
    have hm := GoldbachGRHModel.model_continuous n i
    fun_prop
  have h := (hc.intervalIntegrable (μ := volume) 0 1).1.mono_set
    (show cell n 0 H i ⊆ Set.Ioc (0:ℝ) 1 from Set.inter_subset_right)
  refine h.congr_fun (fun t ht => ?_) (GoldbachGRHArcs.measurable_cell ..)
  unfold integrand
  rw [patched_on_arc hXU hHK hbudget hi ht.1.1]

/-- Integrate the outer model over either cap, using its own denominator cutoff
and radius in the exact coefficient sum. -/
theorem cap_model {n X H U K : ℕ} (hX : 1 ≤ X) (hXU : X ≤ U) (hHK : H ≤ K)
    (hbudget : 2*K*U < n) :
    (∫ t in clipped n X H, integrand n (patched n U K) t) = massSum n X H := by
  have hb : 2*H*X < n := lt_of_le_of_lt (by gcongr) hbudget
  have hHn : H ≤ n := by nlinarith [Nat.mul_le_mul_right (2*H) hX]
  rw [clipped_union hb, integral_biUnion_finset (centers X)
    (fun i _ => GoldbachGRHArcs.measurable_cell n 0 H i) (GoldbachGRHArcs.cell_disjoint hb)
    (fun _ hi => local_integrable hXU hHK hbudget hi)]
  calc
    _ = ∑ i ∈ centers X, ∫ t in cell n 0 H i,
        GoldbachGRHModel.model n i t ^ 2 * phase (-(n:ℝ)*t) := by
      refine sum_congr rfl fun i hi => setIntegral_congr_fun
        (GoldbachGRHArcs.measurable_cell ..) (fun t ht => ?_)
      unfold integrand
      rw [patched_on_arc hXU hHK hbudget hi ht.1.1]
    _ = _ := by
      rw [GoldbachGRHModelAssembly.sum_cell_model hX (Nat.zero_le H) hHn]
      refine sum_congr rfl fun q hq => ?_
      have hq₀ : ¬q ≤ 0 := by have := (mem_Icc.mp hq).1; omega
      simp [GoldbachGRHModelAssembly.massDifference, hq₀]

/-- The nested-band signed model integral is exactly the difference of the
two grouped Ramanujan model sums; this holds in the complex numbers. -/
theorem band_model {n X H U K : ℕ} (hX : 1 ≤ X) (hXU : X ≤ U) (hHK : H ≤ K)
    (hbudget : 2*K*U < n) :
    (∫ t in Set.Ioc (0:ℝ) 1 ∩ (cap n U K \ cap n X H), integrand n (patched n U K) t) =
      massSum n U K - massSum n X H := by
  have hs : clipped n X H ⊆ clipped n U K :=
    Set.inter_subset_inter_right _ (GoldbachGRHArcs.cap_mono hXU hHK)
  have hm : MeasurableSet (clipped n X H) :=
    measurableSet_Ioc.inter (GoldbachGRHArcs.measurable_cap ..)
  have hi : IntegrableOn (integrand n (patched n U K)) (clipped n U K) := by
    rw [clipped_union hbudget, integrableOn_finset_iUnion]
    exact fun _ hj => local_integrable le_rfl le_rfl hbudget hj
  rw [Set.inter_sdiff_distrib_left]
  change (∫ t in clipped n U K \ clipped n X H, _) = _
  rw [setIntegral_sdiff hm hi hs, cap_model (hX.trans hXU) le_rfl le_rfl hbudget,
    cap_model hX hXU hHK hbudget]

/-- Specialization to the frozen square-root-modulus band and its exact model. -/
theorem signed_model_eq (n : ℕ)
    (hX : 1 ≤ SqrtArcSignedTransfer.oldQ n)
    (hXU : SqrtArcSignedTransfer.oldQ n ≤ SqrtArcSignedTransfer.newQ n)
    (hbudget : 2*SqrtArcSignedTransfer.width n (SqrtArcSignedTransfer.newQ n)*
      SqrtArcSignedTransfer.newQ n < n) :
    SqrtArcSignedTransfer.signed n (SqrtArcSignedTransfer.model n) =
      massSum n (SqrtArcSignedTransfer.newQ n) (SqrtArcSignedTransfer.width n (SqrtArcSignedTransfer.newQ n)) -
      massSum n (SqrtArcSignedTransfer.oldQ n) (SqrtArcSignedTransfer.width n (SqrtArcSignedTransfer.oldQ n)) := by
  have hHK : SqrtArcSignedTransfer.width n (SqrtArcSignedTransfer.oldQ n) ≤
      SqrtArcSignedTransfer.width n (SqrtArcSignedTransfer.newQ n) := by
    unfold SqrtArcSignedTransfer.width
    gcongr
  rw [← frozen_model]
  exact band_model hX hXU hHK hbudget

theorem massSum_re (n X H : ℕ) :
    (massSum n X H).re = ∑ q ∈ Icc 1 X, (coefficient q n).re * mass n (radius n H q) := by
  simp [massSum, Complex.re_sum, Complex.mul_re]

open SqrtArcSignedTransfer (oldQ newQ width signed model)
theorem signed_model_re (n : ℕ) (hX : 1 ≤ oldQ n) (hXU : oldQ n ≤ newQ n)
    (hbudget : 2 * width n (newQ n) * newQ n < n) :
    (signed n (model n)).re =
      (∑ q ∈ Icc 1 (newQ n), (coefficient q n).re * mass n (radius n (width n (newQ n)) q)) -
      (∑ q ∈ Icc 1 (oldQ n), (coefficient q n).re * mass n (radius n (width n (oldQ n)) q)) := by
  rw [signed_model_eq n hX hXU hbudget, Complex.sub_re, massSum_re, massSum_re]

end

end SqrtArcModelBridge


namespace SqrtArcModelOld
open Finset
open GoldbachGRHArcs (radius)
open GoldbachGRHKernel (mass)
open GoldbachExplicitModeledMajor (coefficient)
/-- Enlarging the width from H to K recovers at most the missing kernel mass. -/
theorem mass_gain (n q H K : ℕ) (hn : 0 < n) (hq : 0 < q) (hH : 0 < H)
    (hHK : H ≤ K) (hK : 2 * K ≤ n) :
    |mass n (radius n K q) - mass n (radius n H q)| ≤
      (q : ℝ) * n / (2 * H) := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hq' : 0 < (q : ℝ) := by exact_mod_cast hq
  have hH' : 0 < (H : ℝ) := by exact_mod_cast hH
  have hHK' : (H : ℝ) ≤ K := by exact_mod_cast hHK
  have hK' : 2 * (K : ℝ) ≤ n := by exact_mod_cast hK
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hd := mul_pos hq' hn'
  have hr : 0 < radius n H q := div_pos hH' hd
  have hle : radius n H q ≤ radius n K q := div_le_div_of_nonneg_right hHK' hd.le
  have hhalf : radius n K q ≤ 1 / 2 := by
    apply (div_le_iff₀ hd).2
    nlinarith only [hK', mul_le_mul_of_nonneg_right hq1 hn'.le]
  have houter := (GoldbachGRHKernel.mass_loss n (hr.trans_le hle) hhalf).1
  have hinner := (GoldbachGRHKernel.mass_loss n hr (hle.trans hhalf)).2
  rw [abs_of_nonneg (sub_nonneg.mpr (GoldbachGRHKernel.mass_mono n hr.le hle))]
  calc
    _ ≤ 1 / (2 * radius n H q) := by linarith
    _ = _ := by unfold radius; field_simp

/-- Absolute sum of the signed, denominator-grouped rational-model gains.
This holds for every n, with no restriction on divisibility or parity of n. -/
theorem old_model_gain (n X H K : ℕ) (hn : 0 < n) (hH : 0 < H)
    (hHK : H ≤ K) (hK : 2 * K ≤ n) :
    (∑ q ∈ Icc 1 X, |(coefficient q n).re *
      (mass n (radius n K q) - mass n (radius n H q))|) ≤
        (n : ℝ) / (2 * H) * (BandTail.universal * X) := by
  have hH' : 0 < (H : ℝ) := by exact_mod_cast hH
  calc
    _ ≤ ∑ q ∈ Icc 1 X, ((n : ℝ) / (2 * H)) * |BandTail.F n q| := by
      apply sum_le_sum
      intro q hqmem
      have hq : 0 < q := (mem_Icc.mp hqmem).1
      have hq' : 0 < (q : ℝ) := by exact_mod_cast hq
      rw [abs_mul, GoldbachGRHSignedModel.coefficient_re_eq n q hq, abs_div,
        abs_of_pos hq']
      calc
        _ ≤ (|BandTail.F n q| / (q : ℝ)) * ((q : ℝ) * n / (2 * H)) :=
          mul_le_mul_of_nonneg_left (mass_gain n q H K hn hq hH hHK hK)
            (div_nonneg (abs_nonneg _) hq'.le)
        _ = _ := by field_simp
    _ = ((n : ℝ) / (2 * H)) * ∑ q ∈ Icc 1 X, |BandTail.F n q| := by
      rw [mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (GoldbachGRHSignedModel.absolute_prefix_le n X)
      (by positivity)

/-- Substituting the frozen inner width H = 256 X L, where X is the old
cutoff and L is the square of the binary logarithm, saves the factor 1/L. -/
theorem old_model_gain_sqrt_band (n X L K : ℕ) (hn : 0 < n) (hX : 0 < X)
    (hL : 0 < L) (hHK : 256 * X * L ≤ K) (hK : 2 * K ≤ n) :
    (∑ q ∈ Icc 1 X, |(coefficient q n).re *
      (mass n (radius n K q) - mass n (radius n (256 * X * L) q))|) ≤
        BandTail.universal * n / (512 * L) := by
  have hX' : (X : ℝ) ≠ 0 := by exact_mod_cast hX.ne'
  have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  refine (old_model_gain n X (256 * X * L) K hn (by positivity) hHK hK).trans_eq ?_
  push_cast
  field_simp
  ring

/-- Truncating the full kernel mass at the outer radius costs at most
the first absolute moment of the arithmetic coefficients over the cutoff. -/
theorem model_loss_on (n X K : ℕ) (s : Finset ℕ) (hs : s ⊆ Icc 1 X)
    (hn : 0 < n) (hK : 0 < K) (hsmall : 2 * K ≤ n) :
    (∑ q ∈ s, |(coefficient q n).re * ((n : ℝ) + 1 - mass n (radius n K q))|) ≤
      (n : ℝ) / (2 * K) * (BandTail.universal * X) := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hK' : 0 < (K : ℝ) := by exact_mod_cast hK
  have hsmall' : 2 * (K : ℝ) ≤ n := by exact_mod_cast hsmall
  calc
    _ ≤ ∑ q ∈ s, ((n : ℝ) / (2 * K)) * |BandTail.F n q| := by
      apply sum_le_sum
      intro q hqs
      have hq : 0 < q := (mem_Icc.mp (hs hqs)).1
      have hq' : 0 < (q : ℝ) := by exact_mod_cast hq
      have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
      have hd := mul_pos hq' hn'
      have hr : 0 < radius n K q := div_pos hK' hd
      have hhalf : radius n K q ≤ 1 / 2 := by
        apply (div_le_iff₀ hd).2
        nlinarith only [hsmall', mul_le_mul_of_nonneg_right hq1 hn'.le]
      obtain ⟨hloss, hbound⟩ := GoldbachGRHKernel.mass_loss n hr hhalf
      rw [abs_mul, abs_of_nonneg hloss, GoldbachGRHSignedModel.coefficient_re_eq n q hq,
        abs_div, abs_of_pos hq']
      calc
        _ ≤ (|BandTail.F n q| / (q : ℝ)) * (1 / (2 * radius n K q)) :=
          mul_le_mul_of_nonneg_left hbound (div_nonneg (abs_nonneg _) hq'.le)
        _ = _ := by unfold radius; field_simp
    _ = ((n : ℝ) / (2 * K)) * ∑ q ∈ s, |BandTail.F n q| := by rw [mul_sum]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      refine (sum_le_sum_of_subset_of_nonneg hs (fun q _ _ => abs_nonneg (BandTail.F n q))).trans ?_
      exact GoldbachGRHSignedModel.absolute_prefix_le n X

/-- Real part of the rational model grouped by denominator.  Old denominators
contribute a difference of two widths.  New ones contribute their outer mass. -/
noncomputable def groupedGain (n Q U L : ℕ) : ℝ :=
    (∑ q ∈ Icc 1 Q, (coefficient q n).re *
      (mass n (radius n (256 * U * L) q) - mass n (radius n (256 * Q * L) q))) +
    ∑ q ∈ Ioc Q U, (coefficient q n).re * mass n (radius n (256 * U * L) q)

/-- A uniform one-sided lower bound for both grouped model pieces together.
The harmonic-suffix threshold is independent of n and of the outer cutoff U. -/
theorem grouped_model_floor (δ : ℝ) (hδ : 0 < δ) :
    ∃ Q₀ : ℕ, ∀ Q ≥ Q₀, ∀ n U L : ℕ, Even n → 0 < n → 0 < Q → Q ≤ U →
      0 < L → 2 * (256 * U * L) ≤ n →
      -δ * ((n : ℝ) + 1) - BandTail.universal * n / (256 * L) ≤ groupedGain n Q U L := by
  obtain ⟨Q₀, hQ₀⟩ := GoldbachGRHSignedModel.harmonic_suffix_floor δ hδ
  refine ⟨Q₀, ?_⟩
  intro Q hQ n U L heven hn hQpos hQU hL hsmall
  have hU := hQpos.trans_le hQU
  have hU' : (U : ℝ) ≠ 0 := by exact_mod_cast hU.ne'
  have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  let H := 256 * Q * L
  let K := 256 * U * L
  let c := fun q => (coefficient q n).re
  let M := fun q => mass n (radius n K q)
  let A := ∑ q ∈ Icc 1 Q, c q * (M q - mass n (radius n H q))
  let B := ∑ q ∈ Ioc Q U, c q * ((n : ℝ) + 1 - M q)
  let t := BandTail.universal * n / (512 * L)
  have hHK : H ≤ K := by dsimp [H, K]; gcongr
  have hold : |A| ≤ t :=
    (abs_sum_le_sum_abs _ _).trans (old_model_gain_sqrt_band n Q L K hn hQpos hL hHK hsmall)
  have hs : Ioc Q U ⊆ Icc 1 U := by
    intro q hq
    exact mem_Icc.mpr ⟨hQpos.trans_le (mem_Ioc.mp hq).1.le, (mem_Ioc.mp hq).2⟩
  have hnew : |B| ≤ t := by
    refine (abs_sum_le_sum_abs _ _).trans ((model_loss_on n U K _ hs hn (by dsimp [K]; positivity)
      hsmall).trans_eq ?_)
    dsimp [K, t]
    push_cast
    field_simp
    ring
  have hfloor : -δ ≤ ∑ q ∈ Ioc Q U, c q := by
    convert hQ₀ Q hQ n U heven hQU using 1
    apply sum_congr rfl
    intro q hq
    exact GoldbachGRHSignedModel.coefficient_re_eq n q (hQpos.trans (mem_Ioc.mp hq).1)
  have hdec : groupedGain n Q U L = A + ((n : ℝ) + 1) * (∑ q ∈ Ioc Q U, c q) - B := by
    unfold groupedGain
    change A + ∑ q ∈ Ioc Q U, c q * M q = _
    dsimp only [B]
    rw [mul_sum, add_sub_assoc, ← sum_sub_distrib]
    congr 1
    apply sum_congr rfl
    intro q _
    ring
  have hw := mul_le_mul_of_nonneg_left hfloor (by positivity : 0 ≤ (n : ℝ) + 1)
  rw [hdec]
  have ha := (abs_le.mp hold).1
  have hb := (abs_le.mp hnew).2
  have ht : 2 * t = BandTail.universal * n / (256 * L) := by dsimp [t]; ring
  linarith only [ha, hb, hw, ht]

theorem groupedGain_eq_difference (n Q U L : ℕ) (hQU : Q ≤ U) :
    groupedGain n Q U L =
      (∑ q ∈ Icc 1 U, (coefficient q n).re * mass n (radius n (256 * U * L) q)) -
      (∑ q ∈ Icc 1 Q, (coefficient q n).re * mass n (radius n (256 * Q * L) q)) := by
  unfold groupedGain
  rw [BandTail.prefix_split (fun q => (coefficient q n).re * mass n (radius n (256 * U * L) q)) hQU]
  simp_rw [mul_sub]
  rw [sum_sub_distrib]
  ring

/-- The square-root and cube-root cutoffs used in the frozen task give an
unconditional one-sided o(n) bound for the difference of the signed models. -/
theorem frozen_floor (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, Even n → -ε * (n : ℝ) ≤
      (∑ q ∈ Icc 1 (SqrtArcScales.U n), (coefficient q n).re *
        mass n (radius n (SqrtArcScales.K n) q)) -
      (∑ q ∈ Icc 1 (SqrtArcScales.X n), (coefficient q n).re *
        mass n (radius n (256 * SqrtArcScales.X n * SqrtArcScales.L n) q)) := by
  obtain ⟨Q₀, hQ₀⟩ := grouped_model_floor (ε / 4) (by positivity)
  obtain ⟨J, hJ⟩ := exists_nat_ge (BandTail.universal / ε)
  refine ⟨SqrtArcScales.cutoff Q₀ (max 1 J), ?_⟩
  intro n hn heven
  obtain ⟨hQ, hT, hX, hXU, hn', _, hsmall⟩ := SqrtArcScales.bounds Q₀ (max 1 J) n hn
  have hL : 0 < SqrtArcScales.L n := (le_max_left 1 J).trans hT
  have hL' : 0 < (SqrtArcScales.L n : ℝ) := by exact_mod_cast hL
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn'
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hJL : J ≤ SqrtArcScales.L n := (le_max_right 1 J).trans hT
  have hC : BandTail.universal ≤ (SqrtArcScales.L n : ℝ) * ε :=
    (div_le_iff₀ hε).mp (hJ.trans (by exact_mod_cast hJL))
  have hsave : BandTail.universal * n / (256 * SqrtArcScales.L n) ≤ ε * n / 2 := by
    apply (div_le_iff₀ (by positivity)).2
    nlinarith only [mul_le_mul_of_nonneg_right hC hn0,
      mul_nonneg (mul_nonneg hε.le hn0) hL'.le]
  have hbase := hQ₀ _ hQ n _ _ heven hn' hX hXU hL hsmall
  rw [SqrtArcScales.K, ← groupedGain_eq_difference n _ _ (SqrtArcScales.L n) hXU]
  apply le_trans _ hbase
  nlinarith only [hsave, mul_le_mul_of_nonneg_left hn1 hε.le]

end SqrtArcModelOld


namespace SqrtArcModelFloor
open SqrtArcSignedTransfer
theorem model_floor : ModelFloorChild := by
  intro ε hε
  obtain ⟨Nm, hm⟩ := SqrtArcModelOld.frozen_floor ε hε
  refine ⟨max Nm (SqrtArcScales.cutoff 1 1), ?_⟩
  intro n hn heven
  obtain ⟨_, _, hx, hxu, _, hb, _⟩ :=
    SqrtArcScales.bounds 1 1 n ((le_max_right ..).trans hn)
  rw [SqrtArcModelBridge.signed_model_re n hx hxu hb]
  simpa only [neg_mul, SqrtArcScales.K, SqrtArcScales.U, SqrtArcScales.X, SqrtArcScales.L,
    newQ, oldQ, width, ell] using hm n ((le_max_left ..).trans hn) heven

end SqrtArcModelFloor


end SqrtArcModelProof29fa

/-- One-sided bound for the exact signed rational model on the frozen band. -/
theorem Conjectures.Cuts.Task29fa2aa6b48b75de06bb2b25 : SqrtArcModelProof29fa.SqrtArcSignedTransfer.ModelFloorChild :=
  SqrtArcModelProof29fa.SqrtArcModelFloor.model_floor
