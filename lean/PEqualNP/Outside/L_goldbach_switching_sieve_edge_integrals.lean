import Mathlib

/-!
# Explicit edge-integral bounds for the switching sieve (W07)

This file formalizes `L-goldbach-switching-sieve-edge-integrals` under the
`representations` track feeding `L-goldbach-binary-pointwise-positivity` via
the Li–Liu 1+1.9 weighted sieve (`g3`, `g8` in `进度审计1`).

Specifically:
1. `8 * Real.log (10 / 9) ≤ 84289 / 100000` (from the degree-5 Taylor lower bound
   of `Real.exp (84289 / 800000)` via `Real.sum_le_exp_of_nonneg`).
2. `8 * ∫ t in (2 : ℝ)..(8 / 3 : ℝ), Real.log (t - 1) / t ≤ 60962 / 100000`
   (from the degree-17 alternating Taylor upper bound of `log (1 + u)` on `[0, 2/3]`,
   exact division of `u^(k+1)` by `u + 2`, and the degree-18 lower bound of `log (4/3)`).
-/

namespace SwitchingSieveEdgeIntegrals

open Finset MeasureTheory Real

noncomputable section

private lemma alt_geom_identity (M : ℕ) (s : ℝ) :
    (1 + s) * (∑ k ∈ Finset.range M, (-s) ^ k) = 1 - (-s) ^ M := by
  induction M with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, mul_add, ih, pow_succ]
    ring

private lemma integral_one_div_one_add (u : ℝ) (hu : 0 ≤ u) :
    ∫ s in (0 : ℝ)..u, (1 + s)⁻¹ = Real.log (1 + u) := by
  have hderiv : ∀ s ∈ Set.uIcc (0 : ℝ) u, HasDerivAt (fun x => Real.log (1 + x)) (1 + s)⁻¹ s := by
    intro s hs
    rw [Set.uIcc_of_le hu] at hs
    have hpos : 1 + s ≠ 0 := ne_of_gt (add_pos_of_pos_of_nonneg one_pos hs.1)
    simpa using ((hasDerivAt_id s).const_add 1).log hpos
  have hcont : ContinuousOn (fun s : ℝ => (1 + s)⁻¹) (Set.uIcc 0 u) := by
    refine ContinuousOn.inv₀ (continuous_const.add continuous_id).continuousOn fun s hs => ?_
    rw [Set.uIcc_of_le hu] at hs
    exact ne_of_gt (add_pos_of_pos_of_nonneg one_pos hs.1)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable)]
  simp

private lemma integral_alt_poly (M : ℕ) (u : ℝ) :
    ∫ s in (0 : ℝ)..u, (∑ k ∈ Finset.range M, (-s) ^ k) =
      ∑ k ∈ Finset.range M, (-1 : ℝ) ^ k * u ^ (k + 1) / ((k : ℝ) + 1) := by
  have hrew : (fun s : ℝ => ∑ k ∈ Finset.range M, (-s) ^ k) =
      fun s : ℝ => ∑ k ∈ Finset.range M, (-1 : ℝ) ^ k * s ^ k := by
    ext s
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [neg_eq_neg_one_mul, mul_pow]
  rw [hrew, intervalIntegral.integral_finsetSum
    (f := fun k s => (-1 : ℝ) ^ k * s ^ k)
    (fun k _ => (continuous_const.mul (continuous_pow k)).intervalIntegrable 0 u)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [intervalIntegral.integral_const_mul, integral_pow, zero_pow (Nat.succ_ne_zero k), sub_zero]
  ring

private lemma alt_sum_le_log (M : ℕ) (hM : Even M) (u : ℝ) (hu : 0 ≤ u) :
    ∑ k ∈ Finset.range M, (-1 : ℝ) ^ k * u ^ (k + 1) / ((k : ℝ) + 1) ≤ Real.log (1 + u) := by
  rw [← integral_alt_poly M u, ← integral_one_div_one_add u hu]
  refine intervalIntegral.integral_mono_on hu
    ((Continuous.intervalIntegrable (by fun_prop) 0 u))
    (?_) fun s hs => ?_
  · refine ContinuousOn.intervalIntegrable ?_
    refine ContinuousOn.inv₀ (continuous_const.add continuous_id).continuousOn fun s hs => ?_
    rw [Set.uIcc_of_le hu] at hs
    exact ne_of_gt (add_pos_of_pos_of_nonneg one_pos hs.1)
  · have hpos : 0 < 1 + s := add_pos_of_pos_of_nonneg one_pos hs.1
    rw [← one_div, le_div_iff₀ hpos, mul_comm, alt_geom_identity, hM.neg_pow]
    have hsM : 0 ≤ s ^ M := pow_nonneg hs.1 M
    linarith

private lemma log_le_alt_sum (M : ℕ) (hM : Odd M) (u : ℝ) (hu : 0 ≤ u) :
    Real.log (1 + u) ≤ ∑ k ∈ Finset.range M, (-1 : ℝ) ^ k * u ^ (k + 1) / ((k : ℝ) + 1) := by
  rw [← integral_alt_poly M u, ← integral_one_div_one_add u hu]
  refine intervalIntegral.integral_mono_on hu ?_
    ((Continuous.intervalIntegrable (by fun_prop) 0 u)) fun s hs => ?_
  · refine ContinuousOn.intervalIntegrable ?_
    refine ContinuousOn.inv₀ (continuous_const.add continuous_id).continuousOn fun s hs => ?_
    rw [Set.uIcc_of_le hu] at hs
    exact ne_of_gt (add_pos_of_pos_of_nonneg one_pos hs.1)
  · have hpos : 0 < 1 + s := add_pos_of_pos_of_nonneg one_pos hs.1
    rw [← one_div, div_le_iff₀ hpos, mul_comm, alt_geom_identity, hM.neg_pow]
    have hsM : 0 ≤ s ^ M := pow_nonneg hs.1 M
    linarith

private lemma part_one : 8 * Real.log (10 / 9) ≤ (84289 / 100000 : ℝ) := by
  set r : ℝ := 84289 / 800000
  have hr0 : 0 ≤ r := by norm_num [r]
  have hsum : (∑ i ∈ Finset.range 6, r ^ i / (Nat.factorial i : ℝ)) ≤ Real.exp r :=
    Real.sum_le_exp_of_nonneg hr0 6
  have hnum : (10 / 9 : ℝ) ≤ ∑ i ∈ Finset.range 6, r ^ i / (Nat.factorial i : ℝ) := by
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
      Nat.factorial]
    norm_num [r]
  have hlog : Real.log (10 / 9) ≤ r := by
    calc Real.log (10 / 9) ≤ Real.log (Real.exp r) := Real.log_le_log (by norm_num) (hnum.trans hsum)
      _ = r := Real.log_exp r
  linarith

private lemma poly_div_two_add (k : ℕ) (u : ℝ) (hu : 0 ≤ u) :
    u ^ (k + 1) / (2 + u) =
      (-2 : ℝ) ^ (k + 1) / (2 + u) + ∑ j ∈ Finset.range (k + 1), (-2 : ℝ) ^ (k - j) * u ^ j := by
  have h2u : 2 + u ≠ 0 := by linarith
  have hid : u ^ (k + 1) - (-2 : ℝ) ^ (k + 1) =
      (u + 2) * ∑ j ∈ Finset.range (k + 1), (-2 : ℝ) ^ (k - j) * u ^ j := by
    have hmul : (∑ j ∈ Finset.range (k + 1), u ^ j * (-2 : ℝ) ^ (k - j)) * (u - (-2 : ℝ)) =
        u ^ (k + 1) - (-2 : ℝ) ^ (k + 1) := by
      have hg := geom_sum₂_mul u (-2 : ℝ) (k + 1)
      simpa [Nat.add_sub_cancel] using hg
    rw [← hmul]
    have heq : ∑ j ∈ Finset.range (k + 1), (-2 : ℝ) ^ (k - j) * u ^ j =
        ∑ j ∈ Finset.range (k + 1), u ^ j * (-2 : ℝ) ^ (k - j) :=
      Finset.sum_congr rfl fun j _ => mul_comm _ _
    rw [heq]
    ring
  have hsub : u ^ (k + 1) / (2 + u) - (-2 : ℝ) ^ (k + 1) / (2 + u) =
      ∑ j ∈ Finset.range (k + 1), (-2 : ℝ) ^ (k - j) * u ^ j := by
    rw [← sub_div, hid, add_comm u 2, mul_div_cancel_left₀ _ h2u]
  linarith

private lemma integral_one_div_two_add :
    ∫ u in (0 : ℝ)..(2 / 3 : ℝ), (2 + u)⁻¹ = Real.log (4 / 3) := by
  have hderiv : ∀ u ∈ Set.uIcc (0 : ℝ) (2 / 3 : ℝ),
      HasDerivAt (fun x => Real.log (2 + x)) (2 + u)⁻¹ u := by
    intro u hu
    rw [Set.uIcc_of_le (by norm_num)] at hu
    have hpos : 2 + u ≠ 0 := ne_of_gt (add_pos_of_pos_of_nonneg (by norm_num : (0 : ℝ) < 2) hu.1)
    simpa using ((hasDerivAt_id u).const_add 2).log hpos
  have hcont : ContinuousOn (fun u : ℝ => (2 + u)⁻¹) (Set.uIcc 0 (2 / 3 : ℝ)) := by
    refine ContinuousOn.inv₀ (continuous_const.add continuous_id).continuousOn fun u hu => ?_
    rw [Set.uIcc_of_le (by norm_num)] at hu
    exact ne_of_gt (add_pos_of_pos_of_nonneg (by norm_num : (0 : ℝ) < 2) hu.1)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable)]
  have harg : (2 : ℝ) + 2 / 3 = 2 * (4 / 3 : ℝ) := by norm_num
  rw [add_zero, harg, Real.log_mul (by norm_num) (by norm_num)]
  ring

private lemma integral_monomial_div_two_add (k : ℕ) :
    ∫ u in (0 : ℝ)..(2 / 3 : ℝ), u ^ (k + 1) / (2 + u) =
      (-2 : ℝ) ^ (k + 1) * Real.log (4 / 3) +
        ∑ j ∈ Finset.range (k + 1), (-2 : ℝ) ^ (k - j) * ((2 / 3 : ℝ) ^ (j + 1) / ((j : ℝ) + 1)) := by
  have hcongr : ∀ u ∈ Set.uIcc (0 : ℝ) (2 / 3 : ℝ),
      u ^ (k + 1) / (2 + u) =
        (-2 : ℝ) ^ (k + 1) * (2 + u)⁻¹ +
          ∑ j ∈ Finset.range (k + 1), (-2 : ℝ) ^ (k - j) * u ^ j := by
    intro u hu
    rw [Set.uIcc_of_le (by norm_num)] at hu
    simpa [div_eq_mul_inv] using poly_div_two_add k u hu.1
  rw [intervalIntegral.integral_congr hcongr]
  have hc1 : IntervalIntegrable (fun u : ℝ => (-2 : ℝ) ^ (k + 1) * (2 + u)⁻¹)
      MeasureTheory.volume 0 (2 / 3 : ℝ) := by
    refine ContinuousOn.intervalIntegrable ?_
    refine continuousOn_const.mul (ContinuousOn.inv₀ (continuous_const.add continuous_id).continuousOn
      fun u hu => ?_)
    rw [Set.uIcc_of_le (by norm_num)] at hu
    exact ne_of_gt (add_pos_of_pos_of_nonneg (by norm_num : (0 : ℝ) < 2) hu.1)
  have hc2 : IntervalIntegrable
      (fun u : ℝ => ∑ j ∈ Finset.range (k + 1), (-2 : ℝ) ^ (k - j) * u ^ j)
      MeasureTheory.volume 0 (2 / 3 : ℝ) := by
    have hcont : ∀ m : ℕ, Continuous (fun u : ℝ => ∑ j ∈ Finset.range m, (-2 : ℝ) ^ (k - j) * u ^ j) := by
      intro m
      induction m with
      | zero => simp; exact continuous_const
      | succ j ih => simp only [Finset.sum_range_succ]; fun_prop
    exact (hcont (k + 1)).intervalIntegrable 0 (2 / 3 : ℝ)
  rw [intervalIntegral.integral_add hc1 hc2, intervalIntegral.integral_const_mul,
    integral_one_div_two_add]
  congr 1
  rw [intervalIntegral.integral_finsetSum
    (f := fun j u => (-2 : ℝ) ^ (k - j) * u ^ j)
    (fun j _ => (continuous_const.mul (continuous_pow j)).intervalIntegrable 0 (2 / 3 : ℝ))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [intervalIntegral.integral_const_mul, integral_pow, zero_pow (Nat.succ_ne_zero j), sub_zero]

private def A0Q : ℚ :=
  ∑ k ∈ Finset.range 17, ((-1 : ℚ) ^ k / ((k : ℚ) + 1)) * (-2 : ℚ) ^ (k + 1)

private def BQ : ℚ :=
  ∑ k ∈ Finset.range 17, ((-1 : ℚ) ^ k / ((k : ℚ) + 1)) *
    ∑ j ∈ Finset.range (k + 1), (-2 : ℚ) ^ (k - j) * ((2 / 3 : ℚ) ^ (j + 1) / ((j : ℚ) + 1))

private def LQ : ℚ :=
  ∑ k ∈ Finset.range 18, (-1 : ℚ) ^ k * (1 / 3 : ℚ) ^ (k + 1) / ((k : ℚ) + 1)

private lemma A0Q_eq : A0Q = (-2535587840 / 153153 : ℚ) := by
  unfold A0Q
  norm_num [Finset.sum_range_succ]

private lemma LQ_eq : LQ = (1365560289164177 / 4746768812145360 : ℚ) := by
  unfold LQ
  norm_num [Finset.sum_range_succ]

private lemma BQ_eq : BQ = (890574450026919714536 / 186980937213605535 : ℚ) := by
  unfold BQ
  norm_num [Finset.sum_range_succ]

private lemma hnumQ_le : 8 * (A0Q * LQ + BQ) ≤ (60962 / 100000 : ℚ) := by
  rw [A0Q_eq, LQ_eq, BQ_eq]
  norm_num

private lemma part_two :
    8 * ∫ t in (2 : ℝ)..(8 / 3 : ℝ), Real.log (t - 1) / t ≤ (60962 / 100000 : ℝ) := by
  have hshift : ∫ t in (2 : ℝ)..(8 / 3 : ℝ), Real.log (t - 1) / t =
      ∫ u in (0 : ℝ)..(2 / 3 : ℝ), Real.log (1 + u) / (2 + u) := by
    have h := intervalIntegral.integral_comp_add_right
      (fun u : ℝ => Real.log (u - 1) / u) (2 : ℝ) (a := (0 : ℝ)) (b := (2 / 3 : ℝ))
    have h1 : (0 : ℝ) + 2 = 2 := by norm_num
    have h2 : (2 / 3 : ℝ) + 2 = 8 / 3 := by norm_num
    rw [h1, h2] at h
    rw [← h]
    refine intervalIntegral.integral_congr fun u _ => ?_
    congr 1 <;> ring
  rw [hshift]
  let P : ℝ → ℝ := fun u =>
    ∑ k ∈ Finset.range 17, (-1 : ℝ) ^ k * u ^ (k + 1) / ((k : ℝ) + 1)
  have hint_log : IntervalIntegrable (fun u : ℝ => Real.log (1 + u) / (2 + u))
      MeasureTheory.volume 0 (2 / 3 : ℝ) := by
    refine ContinuousOn.intervalIntegrable ?_
    refine ContinuousOn.div ?_ (continuous_const.add continuous_id).continuousOn ?_
    · refine ContinuousOn.log (continuous_const.add continuous_id).continuousOn fun u hu => ?_
      rw [Set.uIcc_of_le (by norm_num)] at hu
      exact ne_of_gt (add_pos_of_pos_of_nonneg one_pos hu.1)
    · intro u hu
      rw [Set.uIcc_of_le (by norm_num)] at hu
      exact ne_of_gt (add_pos_of_pos_of_nonneg (by norm_num : (0 : ℝ) < 2) hu.1)
  have hint_P : IntervalIntegrable (fun u : ℝ => P u / (2 + u))
      MeasureTheory.volume 0 (2 / 3 : ℝ) := by
    refine ContinuousOn.intervalIntegrable ?_
    have hcP : Continuous P := by
      have hm : ∀ m : ℕ, Continuous (fun u : ℝ =>
          ∑ k ∈ Finset.range m, (-1 : ℝ) ^ k * u ^ (k + 1) / ((k : ℝ) + 1)) := by
        intro m
        induction m with
        | zero => simp; exact continuous_const
        | succ k ih => simp only [Finset.sum_range_succ]; fun_prop
      exact hm 17
    refine ContinuousOn.div hcP.continuousOn (continuous_const.add continuous_id).continuousOn ?_
    intro u hu
    rw [Set.uIcc_of_le (by norm_num)] at hu
    exact ne_of_gt (add_pos_of_pos_of_nonneg (by norm_num : (0 : ℝ) < 2) hu.1)
  have hmono : ∫ u in (0 : ℝ)..(2 / 3 : ℝ), Real.log (1 + u) / (2 + u) ≤
      ∫ u in (0 : ℝ)..(2 / 3 : ℝ), P u / (2 + u) := by
    refine intervalIntegral.integral_mono_on (by norm_num) hint_log hint_P fun u hu => ?_
    have hu0 : 0 ≤ u := hu.1
    have h2u : 0 ≤ 2 + u := by linarith
    exact div_le_div_of_nonneg_right (log_le_alt_sum 17 (by decide) u hu0) h2u
  have heval : ∫ u in (0 : ℝ)..(2 / 3 : ℝ), P u / (2 + u) =
      ∑ k ∈ Finset.range 17,
        ((-1 : ℝ) ^ k / ((k : ℝ) + 1)) *
          ((-2 : ℝ) ^ (k + 1) * Real.log (4 / 3) +
            ∑ j ∈ Finset.range (k + 1), (-2 : ℝ) ^ (k - j) * ((2 / 3 : ℝ) ^ (j + 1) / ((j : ℝ) + 1))) := by
    have hrew : (fun u : ℝ => P u / (2 + u)) =
        fun u : ℝ => ∑ k ∈ Finset.range 17,
          ((-1 : ℝ) ^ k / ((k : ℝ) + 1)) * (u ^ (k + 1) / (2 + u)) := by
      ext u
      dsimp [P]
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    have hsum_int := intervalIntegral.integral_finsetSum
      (s := Finset.range 17)
      (f := fun (k : ℕ) (u : ℝ) => ((-1 : ℝ) ^ k / ((k : ℝ) + 1)) * (u ^ (k + 1) / (2 + u)))
      (a := (0 : ℝ)) (b := (2 / 3 : ℝ)) (μ := MeasureTheory.volume) fun k _ => by
        refine ContinuousOn.intervalIntegrable ?_
        refine continuousOn_const.mul (ContinuousOn.div (continuous_pow (k + 1)).continuousOn
          (continuous_const.add continuous_id).continuousOn fun u hu => ?_)
        rw [Set.uIcc_of_le (by norm_num)] at hu
        exact ne_of_gt (add_pos_of_pos_of_nonneg (by norm_num : (0 : ℝ) < 2) hu.1)
    rw [hrew, hsum_int]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [intervalIntegral.integral_const_mul, integral_monomial_div_two_add k]
  let A0 : ℝ := ∑ k ∈ Finset.range 17, ((-1 : ℝ) ^ k / ((k : ℝ) + 1)) * (-2 : ℝ) ^ (k + 1)
  let B : ℝ := ∑ k ∈ Finset.range 17, ((-1 : ℝ) ^ k / ((k : ℝ) + 1)) *
      ∑ j ∈ Finset.range (k + 1), (-2 : ℝ) ^ (k - j) * ((2 / 3 : ℝ) ^ (j + 1) / ((j : ℝ) + 1))
  have hsplit_sum :
      (∑ k ∈ Finset.range 17, ((-1 : ℝ) ^ k / ((k : ℝ) + 1)) *
        ((-2 : ℝ) ^ (k + 1) * Real.log (4 / 3) +
          ∑ j ∈ Finset.range (k + 1), (-2 : ℝ) ^ (k - j) * ((2 / 3 : ℝ) ^ (j + 1) / ((j : ℝ) + 1)))) =
        A0 * Real.log (4 / 3) + B := by
    have hterm : ∀ k ∈ Finset.range 17,
        ((-1 : ℝ) ^ k / ((k : ℝ) + 1)) *
          ((-2 : ℝ) ^ (k + 1) * Real.log (4 / 3) +
            ∑ j ∈ Finset.range (k + 1), (-2 : ℝ) ^ (k - j) * ((2 / 3 : ℝ) ^ (j + 1) / ((j : ℝ) + 1))) =
          (((-1 : ℝ) ^ k / ((k : ℝ) + 1)) * (-2 : ℝ) ^ (k + 1)) * Real.log (4 / 3) +
            ((-1 : ℝ) ^ k / ((k : ℝ) + 1)) *
              ∑ j ∈ Finset.range (k + 1), (-2 : ℝ) ^ (k - j) * ((2 / 3 : ℝ) ^ (j + 1) / ((j : ℝ) + 1)) := by
      intro k _
      ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.sum_mul]
  let L : ℝ := ∑ k ∈ Finset.range 18, (-1 : ℝ) ^ k * (1 / 3 : ℝ) ^ (k + 1) / ((k : ℝ) + 1)
  have hlog_lb : L ≤ Real.log (4 / 3) := by
    have h43 : (4 / 3 : ℝ) = 1 + 1 / 3 := by norm_num
    rw [h43]
    exact alt_sum_le_log 18 (by decide) (1 / 3) (by norm_num)
  have hA0_neg : A0 ≤ 0 := by
    dsimp [A0]
    refine Finset.sum_nonpos fun k _ => ?_
    have hpow : (-1 : ℝ) ^ k * (-2 : ℝ) ^ (k + 1) = - (2 : ℝ) ^ (k + 1) := by
      rw [show (-2 : ℝ) = (-1 : ℝ) * 2 by norm_num, mul_pow, pow_succ]
      have hsq : (-1 : ℝ) ^ k * (-1 : ℝ) ^ k = 1 := by
        rw [← mul_pow]
        norm_num
      calc (-1 : ℝ) ^ k * ((-1 : ℝ) ^ k * (-1 : ℝ) * 2 ^ (k + 1))
          = ((-1 : ℝ) ^ k * (-1 : ℝ) ^ k) * (-1 : ℝ) * 2 ^ (k + 1) := by ring
        _ = - (2 : ℝ) ^ (k + 1) := by rw [hsq]; ring
    have heq : ((-1 : ℝ) ^ k / ((k : ℝ) + 1)) * (-2 : ℝ) ^ (k + 1) =
        -((2 : ℝ) ^ (k + 1) / ((k : ℝ) + 1)) := by
      calc ((-1 : ℝ) ^ k / ((k : ℝ) + 1)) * (-2 : ℝ) ^ (k + 1)
          = ((-1 : ℝ) ^ k * (-2 : ℝ) ^ (k + 1)) / ((k : ℝ) + 1) := by ring
        _ = -(2 : ℝ) ^ (k + 1) / ((k : ℝ) + 1) := by rw [hpow]
        _ = -((2 : ℝ) ^ (k + 1) / ((k : ℝ) + 1)) := by ring
    rw [heq]
    have hpos : 0 ≤ (2 : ℝ) ^ (k + 1) / ((k : ℝ) + 1) := by positivity
    linarith
  have hA0_eq : A0 = (A0Q : ℝ) := by dsimp [A0, A0Q]; push_cast; rfl
  have hB_eq : B = (BQ : ℝ) := by dsimp [B, BQ]; push_cast; rfl
  have hL_eq : L = (LQ : ℝ) := by dsimp [L, LQ]; push_cast; rfl
  have hnum : 8 * (A0 * L + B) ≤ (60962 / 100000 : ℝ) := by
    rw [hA0_eq, hB_eq, hL_eq]
    have hcast := (Rat.cast_le (K := ℝ)).mpr hnumQ_le
    simpa using hcast
  have hbound : 8 * (A0 * Real.log (4 / 3) + B) ≤ 8 * (A0 * L + B) := by
    nlinarith [mul_le_mul_of_nonpos_left hlog_lb hA0_neg]
  calc
    8 * ∫ u in (0 : ℝ)..(2 / 3 : ℝ), Real.log (1 + u) / (2 + u)
        ≤ 8 * ∫ u in (0 : ℝ)..(2 / 3 : ℝ), P u / (2 + u) := by linarith
    _ = 8 * (A0 * Real.log (4 / 3) + B) := by rw [heval, hsplit_sum]
    _ ≤ 8 * (A0 * L + B) := hbound
    _ ≤ (60962 / 100000 : ℝ) := hnum

theorem main :
    8 * Real.log (10 / 9) ≤ (0.84289 : ℝ) ∧
      8 * ∫ t in (2 : ℝ)..(8 / 3 : ℝ), Real.log (t - 1) / t ≤ (0.60962 : ℝ) := by
  exact ⟨part_one.trans (by norm_num), part_two.trans (by norm_num)⟩

end

end SwitchingSieveEdgeIntegrals

theorem PEqualNP.Outside.L_goldbach_switching_sieve_edge_integrals :
    8 * Real.log (10 / 9) ≤ (0.84289 : ℝ) ∧
      8 * ∫ t in (2 : ℝ)..(8 / 3 : ℝ), Real.log (t - 1) / t ≤ (0.60962 : ℝ) := by
  exact SwitchingSieveEdgeIntegrals.main
