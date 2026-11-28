import Mathlib

/-!
# Schoenfeld's explicit bound for the Chebyshev function under the Riemann hypothesis

Adapted from Andrew V. Sutherland, Schoenfeld's bound for psi, revision 0e52d7b1.
Analytic preliminaries from the Prime Number Theorem And project, revision a4fb6989.
Zero symmetry argument from RHPrimeError, revision c55887da.
Adapted for the present toolchain and the closed summation interval in the statement.

Copyright 2026 Andrew V. Sutherland.
Copyright (c) 2024 James Sundstrom. All rights reserved.
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Licensed under the Apache License, Version 2.0. See LICENSE in this repository.
-/


-- Upstream module SchoenfeldRH.Lemmas.p6.Perron
section File1


open Complex MeasureTheory Set

namespace SchoenfeldRH.Lemmas.p6

lemma norm_lb (z : ℂ) {m : ℝ} (hm1 : m ≤ 1) (hre : m ≤ z.re) :
    m / 2 * (1 + |z.im|) ≤ ‖z‖ := by
  have h1 : z.re ≤ ‖z‖ := Complex.re_le_norm z
  have h2 : |z.im| ≤ ‖z‖ := Complex.abs_im_le_norm z
  have h3 : 0 ≤ |z.im| := abs_nonneg _
  nlinarith

lemma integrable_rpow_shift (e r : ℝ) (hr : 1 < r) :
    Integrable (fun t : ℝ => (1 + |t + e|) ^ (-r)) := by
  have := (integrable_one_add_norm (E := ℝ) (μ := volume) (r := r)
    (by simpa using hr)).comp_add_right e
  simpa [Real.norm_eq_abs] using this

lemma integrable_rpow_sub (e r : ℝ) (hr : 1 < r) :
    Integrable (fun t : ℝ => (1 + |t - e|) ^ (-r)) := by
  have := (integrable_one_add_norm (E := ℝ) (μ := volume) (r := r)
    (by simpa using hr)).comp_sub_right e
  simpa [Real.norm_eq_abs] using this

lemma integral_rpow_sub (e r : ℝ) :
    ∫ t : ℝ, (1 + |t - e|) ^ (-r) = ∫ t : ℝ, (1 + |t|) ^ (-r) :=
  integral_sub_right_eq_self (μ := volume) (fun t : ℝ => (1 + |t|) ^ (-r)) e

lemma inv_sq_le (z : ℂ) {m : ℝ} (hm0 : 0 < m) (hm1 : m ≤ 1) (hre : m ≤ z.re) :
    ‖z‖⁻¹ ^ 2 ≤ (2 / m) ^ 2 * (1 + |z.im|) ^ (-(2:ℝ)) := by
  have hlb := norm_lb z hm1 hre
  have hp : 0 < m / 2 * (1 + |z.im|) := by positivity
  have e1 : (2 / m) ^ 2 * (1 + |z.im|) ^ (-(2:ℝ)) = ((m / 2 * (1 + |z.im|)) ^ 2)⁻¹ := by
    rw [Real.rpow_neg (by positivity), Real.rpow_two]
    field_simp
  rw [e1, inv_pow]
  exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hp.le hlb 2)

lemma norm_sub_inv_le (u v : ℂ) (hu : u ≠ 0) (hv : v ≠ 0) :
    ‖1 / u - 1 / v‖ ≤ ‖v - u‖ * (‖u‖⁻¹ ^ 2 + ‖v‖⁻¹ ^ 2) := by
  have e : 1 / u - 1 / v = (v - u) * (u⁻¹ * v⁻¹) := by field_simp
  rw [e, norm_mul, norm_mul, norm_inv, norm_inv]
  gcongr
  nlinarith [sq_nonneg (‖u‖⁻¹ - ‖v‖⁻¹)]

lemma integrable_diff {σ : ℝ} {a b : ℂ} (ha : 0 < σ + a.re) (hb : 0 < σ + b.re) :
    Integrable fun t : ℝ => 1 / ((σ : ℂ) + t * I + a) - 1 / ((σ : ℂ) + t * I + b) := by
  set m := min (min (σ + a.re) (σ + b.re)) 1 with hm
  have hm0 : 0 < m := lt_min (lt_min ha hb) one_pos
  have hm1 : m ≤ 1 := min_le_right _ _
  have hma : m ≤ σ + a.re := (min_le_left _ _).trans (min_le_left _ _)
  have hmb : m ≤ σ + b.re := (min_le_left _ _).trans (min_le_right _ _)
  have hG : Integrable fun t : ℝ => ‖b - a‖ * ((2 / m) ^ 2 * (1 + |t + a.im|) ^ (-(2:ℝ)) +
      (2 / m) ^ 2 * (1 + |t + b.im|) ^ (-(2:ℝ))) :=
    (((integrable_rpow_shift a.im 2 one_lt_two).const_mul _).add
      ((integrable_rpow_shift b.im 2 one_lt_two).const_mul _)).const_mul _
  refine hG.mono' ?_ (Filter.Eventually.of_forall fun t => ?_)
  · exact (by fun_prop : Measurable fun t : ℝ =>
      1 / ((σ : ℂ) + t * I + a) - 1 / ((σ : ℂ) + t * I + b)).aestronglyMeasurable
  · have ra : ((σ : ℂ) + t * I + a).re = σ + a.re := by simp
    have rb : ((σ : ℂ) + t * I + b).re = σ + b.re := by simp
    have ia : ((σ : ℂ) + t * I + a).im = t + a.im := by simp
    have ib : ((σ : ℂ) + t * I + b).im = t + b.im := by simp
    have nza : ((σ : ℂ) + t * I + a) ≠ 0 := fun h => by
      have := congrArg Complex.re h; rw [ra] at this; simp at this; linarith
    have nzb : ((σ : ℂ) + t * I + b) ≠ 0 := fun h => by
      have := congrArg Complex.re h; rw [rb] at this; simp at this; linarith
    refine (norm_sub_inv_le _ _ nza nzb).trans ?_
    have e : ((σ : ℂ) + t * I + b) - ((σ : ℂ) + t * I + a) = b - a := by ring
    rw [e]
    gcongr
    · have := inv_sq_le _ hm0 hm1 (by rw [ra]; exact hma); rwa [ia] at this
    · have := inv_sq_le _ hm0 hm1 (by rw [rb]; exact hmb); rwa [ib] at this

lemma mellin_f_eq {a b s : ℂ} (ha : 0 < s.re + a.re) (hb : 0 < s.re + b.re) :
    HasMellin (fun t : ℝ => indicator (Ioc 0 1) (fun t : ℝ => (t : ℂ) ^ a) t -
      indicator (Ioc 0 1) (fun t : ℝ => (t : ℂ) ^ b) t) s (1 / (s + a) - 1 / (s + b)) := by
  have h1 := hasMellin_cpow_Ioc a ha
  have h2 := hasMellin_cpow_Ioc b hb
  have := hasMellin_sub h1.1 h2.1
  rw [h1.2, h2.2] at this
  exact this

lemma contAt_f {a b : ℂ} {u : ℝ} (hu : 0 < u) :
    ContinuousAt (fun t : ℝ => indicator (Ioc 0 1) (fun t : ℝ => (t : ℂ) ^ a) t -
      indicator (Ioc 0 1) (fun t : ℝ => (t : ℂ) ^ b) t) u := by
  have hm : 0 < min u 1 := lt_min hu one_pos
  have c1 : ContinuousAt (fun t : ℝ => (t : ℂ) ^ a - (t : ℂ) ^ b) (min u 1) :=
    (continuousAt_ofReal_cpow_const _ _ (Or.inr hm.ne')).sub
      (continuousAt_ofReal_cpow_const _ _ (Or.inr hm.ne'))
  have hg : ContinuousAt (fun t : ℝ => ((min t 1 : ℝ) : ℂ) ^ a - ((min t 1 : ℝ) : ℂ) ^ b) u :=
    c1.comp (f := fun t : ℝ => min t 1) (continuous_id.min continuous_const).continuousAt
  refine hg.congr ?_
  filter_upwards [Ioi_mem_nhds hu] with t ht
  rw [mem_Ioi] at ht
  simp only [indicator, mem_Ioc]
  by_cases h1 : t ≤ 1
  · simp [ht, h1]
  · have : min t 1 = 1 := min_eq_right (le_of_not_ge h1)
    simp [this, h1]

lemma perron_diff {σ : ℝ} {a b : ℂ} (ha : 0 < σ + a.re) (hb : 0 < σ + b.re) {x : ℝ}
    (hx : 0 < x) :
    (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, (x : ℂ) ^ ((σ : ℂ) + t * I) *
        (1 / ((σ : ℂ) + t * I + a) - 1 / ((σ : ℂ) + t * I + b))
      = if 1 ≤ x then (x : ℂ) ^ (-a) - (x : ℂ) ^ (-b) else 0 := by
  set f := (fun t : ℝ => indicator (Ioc 0 1) (fun t : ℝ => (t : ℂ) ^ a) t -
      indicator (Ioc 0 1) (fun t : ℝ => (t : ℂ) ^ b) t) with hf
  have hM : ∀ s : ℂ, s.re = σ → mellin f s = 1 / (s + a) - 1 / (s + b) := by
    intro s hs
    exact (mellin_f_eq (by rw [hs]; exact ha) (by rw [hs]; exact hb)).2
  have hconv : MellinConvergent f σ :=
    (mellin_f_eq (s := (σ : ℂ)) (by simpa using ha) (by simpa using hb)).1
  have hvert : VerticalIntegrable (mellin f) σ := by
    unfold VerticalIntegrable
    have : (fun y : ℝ => mellin f ((σ : ℂ) + y * I)) =
        fun y : ℝ => 1 / ((σ : ℂ) + y * I + a) - 1 / ((σ : ℂ) + y * I + b) := by
      funext y; exact hM _ (by simp)
    rw [this]; exact integrable_diff ha hb
  have hxi : 0 < x⁻¹ := inv_pos.mpr hx
  have harg : (x : ℂ).arg ≠ Real.pi := by
    rw [arg_ofReal_of_nonneg hx.le]; exact Real.pi_ne_zero.symm
  have key := mellinInv_mellin_eq σ f hxi hconv hvert (contAt_f hxi)
  rw [mellinInv] at key
  have hint : (fun y : ℝ => ((x⁻¹ : ℝ) : ℂ) ^ (-((σ : ℂ) + y * I)) • mellin f ((σ : ℂ) + y * I)) =
      fun t : ℝ => (x : ℂ) ^ ((σ : ℂ) + t * I) *
        (1 / ((σ : ℂ) + t * I + a) - 1 / ((σ : ℂ) + t * I + b)) := by
    funext y
    rw [hM _ (by simp), smul_eq_mul, ofReal_inv, inv_cpow _ _ harg, cpow_neg, inv_inv]
  rw [hint, Complex.real_smul] at key
  have e2 : (((1 / (2 * Real.pi)) : ℝ) : ℂ) = (1 / (2 * Real.pi) : ℂ) := by push_cast; ring
  rw [e2] at key
  rw [key, hf]
  simp only [indicator, mem_Ioc]
  by_cases h1 : 1 ≤ x
  · have : x⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h1
    simp only [hxi, this, and_self, ite_true, h1]
    rw [ofReal_inv, inv_cpow _ _ harg, inv_cpow _ _ harg, cpow_neg, cpow_neg]
  · have : ¬ x⁻¹ ≤ 1 := by
      rw [not_le] at h1 ⊢; exact (one_lt_inv₀ hx).mpr h1
    simp [this, h1]

lemma rpow_neg_three_halves {x : ℝ} (hx : 0 ≤ x) : x ^ (-(3 / 2 : ℝ)) = (√x ^ 3)⁻¹ := by
  rw [Real.rpow_neg hx, Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast hx]
  norm_num

lemma key_ineq {N A B M m : ℝ} (hm : 0 < m) (hA : m ≤ A) (hB : m ≤ B) (hN : 0 < N)
    (hM : 1 ≤ M) (hNle : N ≤ A + B + M) :
    1 / (N * A * B) ≤ (1 + 1 / √m) * √M *
      (N ^ (-(3 / 2 : ℝ)) * (A ^ (-(3 / 2 : ℝ)) + B ^ (-(3 / 2 : ℝ)))) := by
  have hA0 : 0 < A := hm.trans_le hA
  have hB0 : 0 < B := hm.trans_le hB
  rw [rpow_neg_three_halves hN.le, rpow_neg_three_halves hA0.le, rpow_neg_three_halves hB0.le]
  set n := √N with hn
  set p := √A with hp
  set q := √B with hq
  set r := √M with hr
  set s := √m with hs
  have hn0 : 0 < n := Real.sqrt_pos.mpr hN
  have hp0 : 0 < p := Real.sqrt_pos.mpr hA0
  have hq0 : 0 < q := Real.sqrt_pos.mpr hB0
  have hs0 : 0 < s := Real.sqrt_pos.mpr hm
  have hr1 : 1 ≤ r := by rw [hr]; exact Real.one_le_sqrt.mpr hM
  have hsp : s ≤ p := Real.sqrt_le_sqrt hA
  have hsq : s ≤ q := Real.sqrt_le_sqrt hB
  have eN : N = n ^ 2 := (Real.sq_sqrt hN.le).symm
  have eA : A = p ^ 2 := (Real.sq_sqrt hA0.le).symm
  have eB : B = q ^ 2 := (Real.sq_sqrt hB0.le).symm
  have eM : M = r ^ 2 := (Real.sq_sqrt (by linarith)).symm
  rw [eN, eA, eB, eM] at hNle
  rw [eN, eA, eB]
  have h1 : n ≤ p + q + r := by nlinarith
  have h2 : p ^ 2 * q + p * q ^ 2 ≤ p ^ 3 + q ^ 3 := by nlinarith [sq_nonneg (p - q)]
  have h3 : s * (p * q) ≤ p ^ 3 + q ^ 3 := by
    have : s * p ^ 2 ≤ p ^ 3 := by nlinarith
    have : s * q ^ 2 ≤ q ^ 3 := by nlinarith
    nlinarith [sq_nonneg (p - q)]
  have h4 : n * p * q ≤ (1 + 1 / s) * r * (p ^ 3 + q ^ 3) := by
    have e1 : n * p * q ≤ (p ^ 2 * q + p * q ^ 2) + r * (p * q) := by
      have := mul_le_mul_of_nonneg_right h1 (by positivity : 0 ≤ p * q); nlinarith
    have e2 : r * (p * q) ≤ r * ((p ^ 3 + q ^ 3) / s) := by
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      rw [le_div_iff₀ hs0]; linarith
    have e3 : p ^ 3 + q ^ 3 ≤ r * (p ^ 3 + q ^ 3) := by
      nlinarith [pow_pos hp0 3, pow_pos hq0 3]
    have e4 : (1 + 1 / s) * r * (p ^ 3 + q ^ 3) = r * (p ^ 3 + q ^ 3) + r * ((p ^ 3 + q ^ 3) / s) := by
      ring
    rw [e4]; linarith
  have eL : 1 / (n ^ 2 * p ^ 2 * q ^ 2) = (n * p * q) / (n ^ 3 * p ^ 3 * q ^ 3) := by
    field_simp
  have eR : (1 + 1 / s) * r * ((n ^ 3)⁻¹ * ((p ^ 3)⁻¹ + (q ^ 3)⁻¹)) =
      ((1 + 1 / s) * r * (p ^ 3 + q ^ 3)) / (n ^ 3 * p ^ 3 * q ^ 3) := by
    field_simp
    ring
  rw [eL, eR]
  exact div_le_div_of_nonneg_right h4 (by positivity)

end SchoenfeldRH.Lemmas.p6
end File1

-- Upstream module SchoenfeldRH.Explicit.Kernel
section File2


open Complex MeasureTheory Set

namespace SchoenfeldRH.Explicit

open SchoenfeldRH.Lemmas.p6

lemma integrable_kappa {c μ : ℝ} (hc : 0 < c) (hμ : 1 < c + μ) :
    Integrable fun t : ℝ => 1 / ((c : ℂ) + t * I) - 1 / ((c : ℂ) + t * I + μ) := by
  have := integrable_diff (σ := c) (a := 0) (b := (μ : ℂ)) (by simpa using hc)
    (by simp only [ofReal_re]; linarith)
  simpa only [add_zero] using this

theorem perron_kernel (y c μ : ℝ) (hy : 0 < y) (hc : 0 < c) (hμ : 1 < c + μ) :
    (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, (y : ℂ) ^ ((c : ℂ) + t * I) *
        (1 / ((c : ℂ) + t * I) - 1 / ((c : ℂ) + t * I + μ))
      = if 1 ≤ y then ((1 - y ^ (-μ) : ℝ) : ℂ) else 0 := by
  have key := perron_diff (σ := c) (a := 0) (b := (μ : ℂ)) (by simpa using hc)
    (by simp only [ofReal_re]; linarith) hy
  simp only [add_zero] at key
  rw [key]
  split_ifs with h
  · rw [neg_zero, cpow_zero, ofReal_sub, ofReal_one, ofReal_cpow hy.le, ofReal_neg]
  · rfl

noncomputable def pairK (x c μ : ℝ) (w : ℂ) (t : ℝ) : ℂ :=
  (x : ℂ) ^ ((c : ℂ) + t * I) * ((μ : ℂ) / (w * ((c : ℂ) + t * I - w) * ((c : ℂ) + t * I + μ)))

noncomputable def pairE (x μ : ℝ) (w : ℂ) : ℂ :=
  μ * ((x : ℂ) ^ w - (x : ℂ) ^ (-(μ : ℂ))) / (w * (w + μ))

lemma pair_mul_kappa {x c μ : ℝ} (hc : 0 < c) (hμ : 0 < c + μ) {w : ℂ} (hw : w.re < c) (hw0 : w ≠ 0)
    (t : ℝ) :
    (1 / ((c : ℂ) + t * I - w) + 1 / w) * ((x : ℂ) ^ ((c : ℂ) + t * I) *
        (1 / ((c : ℂ) + t * I) - 1 / ((c : ℂ) + t * I + μ))) = pairK x c μ w t := by
  have hs0 : (c : ℂ) + t * I ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have hsw : (c : ℂ) + t * I - w ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have hsm : (c : ℂ) + t * I + μ ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  unfold pairK
  field_simp
  ring

theorem integral_pairK (x c μ : ℝ) (hx : 1 ≤ x) (hc : 0 < c) (hμ : 1 < c + μ) (w : ℂ)
    (hw : w.re < c) (hw0 : w ≠ 0) (hwμ : w + μ ≠ 0) :
    ∫ t : ℝ, pairK x c μ w t = 2 * Real.pi * pairE x μ w := by
  have hpt : ∀ t : ℝ, pairK x c μ w t = ((μ : ℂ) / (w * (w + μ))) *
      ((x : ℂ) ^ ((c : ℂ) + t * I) *
        (1 / ((c : ℂ) + t * I + -w) - 1 / ((c : ℂ) + t * I + (μ : ℂ)))) := by
    intro t
    have hsw : (c : ℂ) + t * I + -w ≠ 0 := fun h => by
      have := congrArg Complex.re h; simp at this; linarith
    have hsw' : (c : ℂ) + t * I - w ≠ 0 := by rwa [← sub_eq_add_neg] at hsw
    have hsm : (c : ℂ) + t * I + μ ≠ 0 := fun h => by
      have := congrArg Complex.re h; simp at this; linarith
    unfold pairK
    field_simp
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul]
  have key := perron_diff (σ := c) (a := -w) (b := (μ : ℂ)) (by simp only [neg_re]; linarith)
    (by simp only [ofReal_re]; linarith) (by linarith : (0 : ℝ) < x)
  simp only [hx, ↓reduceIte, neg_neg] at key
  set J := ∫ t : ℝ, (x : ℂ) ^ ((c : ℂ) + t * I) *
        (1 / ((c : ℂ) + t * I + -w) - 1 / ((c : ℂ) + t * I + (μ : ℂ))) with hJdef
  have hπ : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hJ : J = 2 * Real.pi * ((x : ℂ) ^ w - (x : ℂ) ^ (-(μ : ℂ))) := by
    rw [← key]; field_simp
  rw [hJ]
  unfold pairE
  field_simp

theorem integral_norm_pairK_le {δ : ℝ} (hδ : 0 < δ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x c μ : ℝ, 0 < x → 1 < c + μ → ∀ w : ℂ, w ≠ 0 → w.re ≤ c - δ →
      Integrable (pairK x c μ w) ∧
      ∫ t : ℝ, ‖pairK x c μ w t‖
        ≤ K * x ^ c * |μ| * (1 + |μ - 1|) ^ (1 / 2 : ℝ) * ‖w‖ ^ (-(3 / 2 : ℝ)) := by
  set m := min δ 1 with hm
  have hm0 : 0 < m := lt_min hδ one_pos
  have hm1 : m ≤ 1 := min_le_right _ _
  have hmδ : m ≤ δ := min_le_left _ _
  set J0 := ∫ t : ℝ, (1 + |t|) ^ (-(3 / 2 : ℝ)) with hJ0
  have hJ0nn : 0 ≤ J0 := integral_nonneg fun t => by positivity
  set C := (1 + 1 / √m) * (m / 2) ^ (-(3 / 2 : ℝ)) with hC
  have hCnn : 0 ≤ C := by positivity
  refine ⟨C * (2 * J0), by positivity, ?_⟩
  intro x c μ hx hcμ w hw0 hwc
  set R := (1 + |μ - 1|) ^ (1 / 2 : ℝ) with hR
  set N := ‖w‖ with hNdef
  have hN : 0 < N := norm_pos_iff.mpr hw0
  set D := x ^ c * |μ| * R * N ^ (-(3 / 2 : ℝ)) * C with hD
  have hFint : Integrable fun t : ℝ =>
      D * ((1 + |t - w.im|) ^ (-(3 / 2 : ℝ)) + (1 + |t - 0|) ^ (-(3 / 2 : ℝ))) :=
    ((integrable_rpow_sub w.im _ (by norm_num)).add
      (integrable_rpow_sub 0 _ (by norm_num))).const_mul D
  have hpt : ∀ t : ℝ, ‖pairK x c μ w t‖ ≤
      D * ((1 + |t - w.im|) ^ (-(3 / 2 : ℝ)) + (1 + |t - 0|) ^ (-(3 / 2 : ℝ))) := by
    intro t
    obtain ⟨s, hs⟩ : ∃ s : ℂ, s = (c : ℂ) + t * I := ⟨_, rfl⟩
    have hsre : s.re = c := by rw [hs]; simp
    have hsw_re : (s - w).re = c - w.re := by rw [sub_re, hsre]
    have hsw_im : (s - w).im = t - w.im := by rw [hs]; simp
    have hsm_re : (s + μ).re = c + μ := by rw [add_re, hsre]; simp
    have hsm_im : (s + μ).im = t := by rw [hs]; simp
    have hA := norm_lb (s - w) hm1 (by rw [hsw_re]; linarith)
    have hB := norm_lb (s + μ) hm1 (by rw [hsm_re]; linarith)
    rw [hsw_im] at hA
    rw [hsm_im] at hB
    have hAm : m ≤ ‖s - w‖ := le_trans (by rw [hsw_re]; linarith) (Complex.re_le_norm _)
    have hBm : m ≤ ‖s + μ‖ := le_trans (by rw [hsm_re]; linarith) (Complex.re_le_norm _)
    have hNle : N ≤ ‖s - w‖ + ‖s + μ‖ + (1 + |μ - 1|) := by
      have e : w = (s + μ) - (s - w) - (μ : ℂ) := by ring
      have h1 : ‖w‖ ≤ ‖s + μ‖ + ‖s - w‖ + ‖(μ : ℂ)‖ := by
        calc ‖w‖ = ‖(s + μ) - (s - w) - (μ : ℂ)‖ := by rw [← e]
          _ ≤ ‖(s + μ) - (s - w)‖ + ‖(μ : ℂ)‖ := norm_sub_le _ _
          _ ≤ ‖s + μ‖ + ‖s - w‖ + ‖(μ : ℂ)‖ := by gcongr; exact norm_sub_le _ _
      have h2 : ‖(μ : ℂ)‖ = |μ| := by rw [Complex.norm_real, Real.norm_eq_abs]
      have h3 : |μ| ≤ 1 + |μ - 1| := by
        have := abs_sub_abs_le_abs_sub μ 1; rw [abs_one] at this; linarith
      rw [hNdef]; linarith
    have hnorm : ‖pairK x c μ w t‖ = x ^ c * |μ| * (1 / (N * ‖s - w‖ * ‖s + μ‖)) := by
      have : pairK x c μ w t = (x : ℂ) ^ s * ((μ : ℂ) / (w * (s - w) * (s + μ))) := by
        rw [hs]; rfl
      rw [this, norm_mul, norm_cpow_eq_rpow_re_of_pos hx, norm_div, norm_mul, norm_mul,
        Complex.norm_real, Real.norm_eq_abs, hsre]
      ring
    have hk := key_ineq hm0 hAm hBm hN (by linarith [abs_nonneg (μ - 1)]) hNle
    have hsq : √(1 + |μ - 1|) = R := by rw [Real.sqrt_eq_rpow]
    rw [hsq] at hk
    have hA' : ‖s - w‖ ^ (-(3 / 2 : ℝ)) ≤
        (m / 2) ^ (-(3 / 2 : ℝ)) * (1 + |t - w.im|) ^ (-(3 / 2 : ℝ)) := by
      rw [← Real.mul_rpow (by positivity) (by positivity)]
      exact Real.rpow_le_rpow_of_nonpos (by positivity) hA (by norm_num)
    have hB' : ‖s + μ‖ ^ (-(3 / 2 : ℝ)) ≤
        (m / 2) ^ (-(3 / 2 : ℝ)) * (1 + |t - 0|) ^ (-(3 / 2 : ℝ)) := by
      rw [sub_zero, ← Real.mul_rpow (by positivity) (by positivity)]
      exact Real.rpow_le_rpow_of_nonpos (by positivity) hB (by norm_num)
    rw [hnorm]
    calc x ^ c * |μ| * (1 / (N * ‖s - w‖ * ‖s + μ‖))
        ≤ x ^ c * |μ| * ((1 + 1 / √m) * R * (N ^ (-(3 / 2 : ℝ)) *
            (‖s - w‖ ^ (-(3 / 2 : ℝ)) + ‖s + μ‖ ^ (-(3 / 2 : ℝ))))) :=
          mul_le_mul_of_nonneg_left hk (by positivity)
      _ ≤ x ^ c * |μ| * ((1 + 1 / √m) * R * (N ^ (-(3 / 2 : ℝ)) *
            ((m / 2) ^ (-(3 / 2 : ℝ)) * (1 + |t - w.im|) ^ (-(3 / 2 : ℝ)) +
              (m / 2) ^ (-(3 / 2 : ℝ)) * (1 + |t - 0|) ^ (-(3 / 2 : ℝ))))) := by
          gcongr
      _ = D * ((1 + |t - w.im|) ^ (-(3 / 2 : ℝ)) + (1 + |t - 0|) ^ (-(3 / 2 : ℝ))) := by
          rw [hD, hC]; ring
  have hmeas : Measurable (pairK x c μ w) := by
    show Measurable (fun t : ℝ => (x : ℂ) ^ ((c : ℂ) + t * I) *
      ((μ : ℂ) / (w * ((c : ℂ) + t * I - w) * ((c : ℂ) + t * I + μ))))
    fun_prop
  have hInt : Integrable (pairK x c μ w) :=
    hFint.mono' hmeas.aestronglyMeasurable (Filter.Eventually.of_forall hpt)
  refine ⟨hInt, ?_⟩
  calc ∫ t : ℝ, ‖pairK x c μ w t‖
      ≤ ∫ t : ℝ, D * ((1 + |t - w.im|) ^ (-(3 / 2 : ℝ)) + (1 + |t - 0|) ^ (-(3 / 2 : ℝ))) :=
        integral_mono hInt.norm hFint hpt
    _ = D * (J0 + J0) := by
        rw [integral_const_mul, integral_add (integrable_rpow_sub w.im _ (by norm_num))
          (integrable_rpow_sub 0 _ (by norm_num)), integral_rpow_sub, integral_rpow_sub]
    _ = C * (2 * J0) * x ^ c * |μ| * R * N ^ (-(3 / 2 : ℝ)) := by rw [hD]; ring

end SchoenfeldRH.Explicit
end File2

-- Upstream module SchoenfeldRH.Explicit.Weighted
section File3


open Complex MeasureTheory Set Filter

namespace SchoenfeldRH.Explicit

noncomputable def Kmu (c μ y t : ℝ) : ℂ :=
  (y : ℂ) ^ ((c : ℂ) + t * I) * (1 / ((c : ℂ) + t * I) - 1 / ((c : ℂ) + t * I + μ))

lemma norm_Kmu {c μ y : ℝ} (hy : 0 < y) (t : ℝ) :
    ‖Kmu c μ y t‖ = y ^ c * ‖1 / ((c : ℂ) + t * I) - 1 / ((c : ℂ) + t * I + μ)‖ := by
  rw [Kmu, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy]
  simp

lemma integrable_Kmu {c μ : ℝ} (hc : 0 < c) (hμ : 1 < c + μ) {y : ℝ} (hy : 0 < y) :
    Integrable (Kmu c μ y) := by
  have hcont : Continuous fun t : ℝ => (y : ℂ) ^ ((c : ℂ) + t * I) :=
    Continuous.const_cpow (by fun_prop) (Or.inl (by exact_mod_cast hy.ne'))
  refine (integrable_kappa hc hμ).bdd_mul (c := y ^ c) hcont.aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun t => ?_
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hy]
  simp

lemma integral_Kmu (y c μ : ℝ) (hy : 0 < y) (hc : 0 < c) (hμ : 1 < c + μ) :
    ∫ t : ℝ, Kmu c μ y t = 2 * Real.pi * (if 1 ≤ y then ((1 - y ^ (-μ) : ℝ) : ℂ) else 0) := by
  have h := perron_kernel y c μ hy hc hμ
  rw [← h]
  have hpi : (2 * Real.pi : ℂ) ≠ 0 := by
    have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
    exact mul_ne_zero two_ne_zero this
  rw [← mul_assoc, mul_one_div_cancel hpi, one_mul]
  rfl

lemma cpow_split {N n : ℕ} (hn : n ≠ 0) (s : ℂ) :
    (N : ℂ) ^ s = ((((N : ℝ) / (n : ℝ) : ℝ)) : ℂ) ^ s * (n : ℂ) ^ s := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  rw [← Complex.ofReal_natCast n, ← Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity)]
  congr 1
  rw [← Complex.ofReal_mul, div_mul_cancel₀ _ hn']
  simp

theorem perron_weighted_mu (a : ℕ → ℂ) (c μ : ℝ) (hc : 0 < c) (hμ : 1 < c + μ)
    (ha : Summable fun n : ℕ => ‖a n‖ / (n : ℝ) ^ c) (N : ℕ) (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Ioo 0 N, a n * ((1 - ((n : ℝ) / N) ^ μ : ℝ) : ℂ)
      = (1 / (2 * Real.pi)) * ∫ t : ℝ, LSeries a ((c : ℂ) + t * I) * ((N : ℂ) ^ ((c : ℂ) + t * I)
          * (1 / ((c : ℂ) + t * I) - 1 / ((c : ℂ) + t * I + μ))) := by
  set F : ℕ → ℝ → ℂ := fun n t => if n = 0 then 0 else a n * Kmu c μ ((N : ℝ) / n) t with hF
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hpos : ∀ n : ℕ, n ≠ 0 → (0 : ℝ) < (N : ℝ) / n := fun n hn =>
    div_pos hNpos (by exact_mod_cast Nat.pos_of_ne_zero hn)
  
  have hpt : ∀ t : ℝ, LSeries a ((c : ℂ) + t * I) * ((N : ℂ) ^ ((c : ℂ) + t * I)
          * (1 / ((c : ℂ) + t * I) - 1 / ((c : ℂ) + t * I + μ))) = ∑' n, F n t := by
    intro t
    rw [LSeries, ← tsum_mul_right]
    congr 1
    funext n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [hF]
    · simp only [hF, ite_eq_right hn, LSeries.term_of_ne_zero hn, Kmu]
      have hns : (n : ℂ) ^ ((c : ℂ) + t * I) ≠ 0 := by
        rw [Ne, Complex.cpow_eq_zero_iff]
        exact fun h => hn (by exact_mod_cast h.1)
      rw [cpow_split (N := N) hn, div_mul_eq_mul_div, div_eq_iff hns]
      ring
  have hint : ∀ n, Integrable (F n) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [hF]
    · simp only [hF, ite_eq_right hn]
      exact (integrable_Kmu hc hμ (hpos n hn)).const_mul _
  set Ik : ℝ := ∫ t : ℝ, ‖1 / ((c : ℂ) + t * I) - 1 / ((c : ℂ) + t * I + μ)‖ with hIk
  have hnorm : ∀ n, ∫ t, ‖F n t‖ = ‖a n‖ / (n : ℝ) ^ c * ((N : ℝ) ^ c * Ik) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [hF, Real.zero_rpow hc.ne']
    · simp only [hF, ite_eq_right hn, norm_mul, norm_Kmu (hpos n hn)]
      rw [hIk, ← integral_const_mul, ← integral_const_mul]
      congr 1
      funext t
      rw [Real.div_rpow hNpos.le (Nat.cast_nonneg n)]
      ring
  have hsum : Summable fun n => ∫ t, ‖F n t‖ := by
    simp only [hnorm]
    exact ha.mul_right _
  have hkey : ∀ n, (1 / (2 * Real.pi) : ℂ) * ∫ t, F n t
      = if n ∈ Finset.Ioo 0 N then a n * ((1 - ((n : ℝ) / N) ^ μ : ℝ) : ℂ) else 0 := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [hF]
    have hpi : (2 * Real.pi : ℂ) ≠ 0 := by
      have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
      exact mul_ne_zero two_ne_zero this
    simp only [hF, ite_eq_right hn]
    rw [integral_const_mul, integral_Kmu _ _ _ (hpos n hn) hc hμ]
    have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    rcases lt_trichotomy n N with h | h | h
    · have hmem : n ∈ Finset.Ioo 0 N := Finset.mem_Ioo.mpr ⟨Nat.pos_of_ne_zero hn, h⟩
      have h1 : 1 ≤ (N : ℝ) / n := by
        rw [le_div_iff₀ hn0, one_mul]; exact_mod_cast (by omega : n ≤ N)
      rw [ite_eq_left h1, ite_eq_left hmem]
      have h2 : ((N : ℝ) / n) ^ (-μ) = ((n : ℝ) / N) ^ μ := by
        rw [Real.rpow_neg (hpos n hn).le, ← Real.inv_rpow (hpos n hn).le, inv_div]
      rw [h2]
      field_simp
    · subst h
      have hmem : n ∉ Finset.Ioo 0 n := by simp
      rw [ite_eq_right hmem, div_self hn0.ne', ite_eq_left le_rfl]
      simp
    · have hmem : n ∉ Finset.Ioo 0 N := by simp; omega
      have h1 : ¬ 1 ≤ (N : ℝ) / n := by
        rw [le_div_iff₀ hn0, one_mul, not_le]; exact_mod_cast h
      rw [ite_eq_right h1, ite_eq_right hmem]
      simp
  rw [funext hpt, ← integral_tsum_of_summable_integral_norm hint hsum, ← tsum_mul_left]
  simp only [hkey]
  rw [tsum_eq_sum (s := Finset.Ioo 0 N)]
  · exact Finset.sum_congr rfl fun n hn => (ite_eq_left hn).symm
  · intro n hn
    exact ite_eq_right hn

end SchoenfeldRH.Explicit
end File3

-- Upstream module SchoenfeldRH.Lemmas.p4.DigammaAux
section File4


namespace SchoenfeldRH.P4

open Filter Topology Set

lemma re_ne_neg_nat {w : ℂ} (hw : 0 < w.re) (m : ℕ) : w ≠ -(m : ℂ) := by
  rintro rfl
  simp at hw
  linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)]

lemma real_ne_neg_nat {x : ℝ} (hx : 0 < x) (m : ℕ) : x ≠ -(m : ℝ) := by
  intro h
  have := (Nat.cast_nonneg m : (0:ℝ) ≤ m)
  linarith

lemma deriv_Gamma_ofReal {x : ℝ} (hx : 0 < x) :
    deriv Complex.Gamma (x : ℂ) = ((deriv Real.Gamma x : ℝ) : ℂ) := by
  have hf : DifferentiableAt ℂ Complex.Gamma (x : ℂ) :=
    Complex.differentiableAt_Gamma _ (re_ne_neg_nat (by simpa using hx))
  have hg : HasDerivAt Real.Gamma (deriv Real.Gamma x) x :=
    (Real.differentiableAt_Gamma (real_ne_neg_nat hx)).hasDerivAt
  have h1 := hf.hasDerivAt.comp_ofReal
  have h2 := hg.ofReal_comp
  have h3 : (fun y : ℝ => Complex.Gamma (y : ℂ)) = fun y : ℝ => ((Real.Gamma y : ℝ) : ℂ) :=
    funext Complex.Gamma_ofReal
  rw [h3] at h1
  exact h1.unique h2

lemma digamma_ofReal_eq {x : ℝ} (hx : 0 < x) :
    Complex.digamma (x : ℂ) = ((deriv Real.Gamma x / Real.Gamma x : ℝ) : ℂ) := by
  rw [Complex.digamma_def, logDeriv_apply, deriv_Gamma_ofReal hx, Complex.Gamma_ofReal,
    Complex.ofReal_div]

lemma bounds {x : ℝ} (hx : 1 < x) :
    Real.log (x - 1) ≤ deriv Real.Gamma x / Real.Gamma x ∧
      deriv Real.Gamma x / Real.Gamma x ≤ Real.log x := by
  have hx0 : 0 < x := by linarith
  have hc := Real.convexOn_log_Gamma
  have hd : HasDerivAt (Real.log ∘ Real.Gamma) (deriv Real.Gamma x / Real.Gamma x) x :=
    ((Real.differentiableAt_Gamma (real_ne_neg_nat hx0)).hasDerivAt).log
      (Real.Gamma_pos_of_pos hx0).ne'
  have hrec : ∀ y : ℝ, 0 < y →
      (Real.log ∘ Real.Gamma) (y + 1) = (Real.log ∘ Real.Gamma) y + Real.log y := by
    intro y hy
    simp only [Function.comp_apply, Real.Gamma_add_one hy.ne',
      Real.log_mul hy.ne' (Real.Gamma_pos_of_pos hy).ne']
    ring
  constructor
  · have h := hc.slope_le_of_hasDerivAt (x := x - 1) (y := x) (mem_Ioi.mpr (by linarith))
      (mem_Ioi.mpr hx0) (by linarith) hd
    rw [slope_def_field] at h
    have h2 := hrec (x - 1) (by linarith)
    rw [sub_add_cancel] at h2
    rw [h2, show x - (x - 1) = (1:ℝ) by ring, div_one] at h
    linarith
  · have h := hc.le_slope_of_hasDerivAt (x := x) (y := x + 1) (mem_Ioi.mpr hx0)
      (mem_Ioi.mpr (by linarith)) (by linarith) hd
    rw [slope_def_field, hrec x hx0, show x + 1 - x = (1:ℝ) by ring, div_one] at h
    linarith

lemma add_ne_zero' (k : ℕ) {w : ℂ} (hw : 0 < w.re) : (k : ℂ) + w ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this
  linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]

lemma term_eq (k : ℕ) {w : ℂ} (hw : 0 < w.re) :
    1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + w) = (w - 1) / (((k : ℂ) + 1) * ((k : ℂ) + w)) := by
  have h1 : (k : ℂ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero k
  have h2 := add_ne_zero' k hw
  field_simp
  ring

lemma summable_base : Summable (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2) := by
  have h := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
  simpa [Nat.cast_add, Nat.cast_one] using h

lemma summable_u (R : ℝ) : Summable (fun k : ℕ => 2 * (R + 1) * (1 / ((k : ℝ) + 1) ^ 2)) :=
  summable_base.mul_left _

lemma term_norm_le {R : ℝ} {w : ℂ} (hw : 1 / 2 < w.re) (hR : ‖w‖ ≤ R) (k : ℕ) :
    ‖1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + w)‖ ≤ 2 * (R + 1) * (1 / ((k : ℝ) + 1) ^ 2) := by
  have hk : (0:ℝ) ≤ k := Nat.cast_nonneg k
  rw [term_eq k (by linarith), norm_div, norm_mul]
  have e1 : ‖(k : ℂ) + 1‖ = (k:ℝ) + 1 := by
    rw [show (k:ℂ) + 1 = ((k + 1 : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast]
    push_cast; ring
  have e2 : (k:ℝ) + 1 / 2 ≤ ‖(k : ℂ) + w‖ := by
    have := Complex.re_le_norm ((k : ℂ) + w)
    simp at this
    linarith
  have e3 : ‖w - 1‖ ≤ R + 1 := by
    calc ‖w - 1‖ ≤ ‖w‖ + ‖(1:ℂ)‖ := norm_sub_le _ _
      _ ≤ R + 1 := by simp; linarith
  have hR1 : 0 ≤ R + 1 := by linarith [norm_nonneg w]
  rw [e1]
  calc ‖w - 1‖ / (((k:ℝ) + 1) * ‖(k : ℂ) + w‖)
        ≤ (R + 1) / (((k:ℝ) + 1) * ((k:ℝ) + 1 / 2)) := by
        apply div_le_div₀ hR1 e3 (by positivity)
        exact mul_le_mul_of_nonneg_left e2 (by positivity)
    _ ≤ 2 * (R + 1) * (1 / ((k : ℝ) + 1) ^ 2) := by
        rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [mul_nonneg (mul_nonneg hR1 hk) (by positivity : (0:ℝ) ≤ k + 1)]

lemma summable_term {w : ℂ} (hw : 1 / 2 < w.re) :
    Summable (fun k : ℕ => 1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + w)) :=
  Summable.of_norm_bounded (summable_u ‖w‖) (fun k => term_norm_le hw le_rfl k)

lemma isOpen_U : IsOpen {w : ℂ | 1 / 2 < w.re} :=
  isOpen_lt continuous_const Complex.continuous_re

lemma differentiableOn_S :
    DifferentiableOn ℂ (fun w : ℂ => ∑' k : ℕ, (1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + w)))
      {w : ℂ | 1 / 2 < w.re} := by
  intro z hz
  set R := ‖z‖ + 1 with hRdef
  have hV : IsOpen ({w : ℂ | 1 / 2 < w.re} ∩ Metric.ball 0 R) :=
    isOpen_U.inter Metric.isOpen_ball
  have hD := Complex.differentiableOn_tsum_of_summable_norm
    (U := {w : ℂ | 1 / 2 < w.re} ∩ Metric.ball 0 R)
    (F := fun (k : ℕ) (w : ℂ) => 1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + w))
    (summable_u R) ?_ hV ?_
  · have hzV : z ∈ {w : ℂ | 1 / 2 < w.re} ∩ Metric.ball 0 R := ⟨hz, by simp [R]⟩
    exact (hD.differentiableAt (hV.mem_nhds hzV)).differentiableWithinAt
  · intro k w hw
    have hre : (1:ℝ) / 2 < w.re := hw.1
    have hne := add_ne_zero' k (w := w) (by linarith)
    apply DifferentiableAt.differentiableWithinAt
    fun_prop (disch := exact hne)
  · intro k w hw
    have hre : (1:ℝ) / 2 < w.re := hw.1
    have hb : ‖w‖ < R := by simpa using hw.2
    exact term_norm_le hre hb.le k

lemma analytic_digamma : AnalyticOnNhd ℂ Complex.digamma {w : ℂ | 1 / 2 < w.re} := by
  have hG : DifferentiableOn ℂ Complex.Gamma {w : ℂ | 1 / 2 < w.re} := fun z hz =>
    (Complex.differentiableAt_Gamma z
      (re_ne_neg_nat (by have h : (1:ℝ) / 2 < z.re := hz; linarith))).differentiableWithinAt
  have hGa : AnalyticOnNhd ℂ Complex.Gamma {w : ℂ | 1 / 2 < w.re} := hG.analyticOnNhd isOpen_U
  have : Complex.digamma = fun w => deriv Complex.Gamma w / Complex.Gamma w := by
    funext w; rw [Complex.digamma_def, logDeriv_apply]
  rw [this]
  exact hGa.deriv.div hGa fun z hz =>
    Complex.Gamma_ne_zero_of_re_pos (by have h : (1:ℝ) / 2 < z.re := hz; linarith)

lemma partial_sum (w : ℂ) (hw : 0 < w.re) (N : ℕ) :
    ∑ k ∈ Finset.range N, (1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + w)) =
      (Complex.digamma w - Complex.digamma 1) +
        (Complex.digamma (1 + N) - Complex.digamma (w + N)) := by
  have e1 : ∀ k : ℕ, 1 / ((k : ℂ) + 1) = (1 + (k : ℂ))⁻¹ := by
    intro k; rw [one_div, add_comm]
  have e2 : ∀ k : ℕ, 1 / ((k : ℂ) + w) = (w + (k : ℂ))⁻¹ := by
    intro k; rw [one_div, add_comm]
  simp_rw [e1, e2]
  rw [Finset.sum_sub_distrib, Complex.digamma_apply_add_nat (re_ne_neg_nat (by simp)) N,
    Complex.digamma_apply_add_nat (re_ne_neg_nat hw) N]
  ring

lemma real_limit {x : ℝ} (hx : 0 < x) :
    Tendsto (fun N : ℕ => deriv Real.Gamma (1 + N) / Real.Gamma (1 + N) -
      deriv Real.Gamma (x + N) / Real.Gamma (x + N)) atTop (𝓝 0) := by
  have hN : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hl : Tendsto (fun N : ℕ => -(Real.log ((N:ℝ) + x) - Real.log N)) atTop (𝓝 0) := by
    have := ((Real.tendsto_log_comp_add_sub_log x).comp hN).neg
    rw [neg_zero] at this
    exact this
  have hu : Tendsto (fun N : ℕ => (Real.log ((N:ℝ) + 1) - Real.log N) -
      (Real.log ((N:ℝ) + (x - 1)) - Real.log N)) atTop (𝓝 0) := by
    have := ((Real.tendsto_log_comp_add_sub_log 1).comp hN).sub
      ((Real.tendsto_log_comp_add_sub_log (x - 1)).comp hN)
    rw [sub_zero] at this
    exact this
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl hu
  · filter_upwards [eventually_ge_atTop 1] with N hN1
    have hN1' : (1:ℝ) ≤ N := by exact_mod_cast hN1
    have b1 := (bounds (x := 1 + N) (by linarith)).1
    have b2 := (bounds (x := x + N) (by linarith)).2
    rw [show (1:ℝ) + N - 1 = N by ring] at b1
    have e : Real.log ((N:ℝ) + x) = Real.log (x + N) := by rw [add_comm]
    linarith
  · filter_upwards [eventually_ge_atTop 1] with N hN1
    have hN1' : (1:ℝ) ≤ N := by exact_mod_cast hN1
    have b1 := (bounds (x := 1 + N) (by linarith)).2
    have b2 := (bounds (x := x + N) (by linarith)).1
    have e1 : Real.log ((N:ℝ) + 1) = Real.log (1 + N) := by rw [add_comm]
    have e2 : Real.log ((N:ℝ) + (x - 1)) = Real.log (x + N - 1) := by ring_nf
    linarith

lemma hasSum_real {x : ℝ} (hx : 1 / 2 < x) :
    HasSum (fun k : ℕ => 1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + x))
      (Complex.digamma x - Complex.digamma 1) := by
  have hx0 : 0 < x := by linarith
  have hs := summable_term (w := (x:ℂ)) (by simpa using hx)
  have key : Tendsto (fun N : ℕ => Complex.digamma (1 + N) - Complex.digamma ((x:ℂ) + N))
      atTop (𝓝 0) := by
    have h := (Complex.continuous_ofReal.tendsto 0).comp (real_limit hx0)
    rw [Complex.ofReal_zero] at h
    refine h.congr' (Eventually.of_forall fun N => ?_)
    simp only [Function.comp_apply, Complex.ofReal_sub]
    rw [← digamma_ofReal_eq (x := 1 + N) (by positivity),
      ← digamma_ofReal_eq (x := x + N) (by positivity)]
    push_cast
    rfl
  have hlim := (tendsto_const_nhds (x := Complex.digamma x - Complex.digamma 1)).add key
  rw [add_zero] at hlim
  have hlim' : Tendsto (fun N : ℕ => ∑ k ∈ Finset.range N,
      (1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + x))) atTop
      (𝓝 (Complex.digamma x - Complex.digamma 1)) := by
    simp_rw [partial_sum (x:ℂ) (by simpa using hx0)]
    exact hlim
  have := tendsto_nhds_unique hs.hasSum.tendsto_sum_nat hlim'
  rw [← this]
  exact hs.hasSum

theorem hasSum_digamma {w : ℂ} (hw : 1 / 2 < w.re) :
    HasSum (fun k : ℕ => 1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + w))
      (Complex.digamma w - Complex.digamma 1) := by
  have hU : IsPreconnected {w : ℂ | 1 / 2 < w.re} :=
    (convex_halfSpace_re_gt (1 / 2)).isPreconnected
  have hS := differentiableOn_S.analyticOnNhd isOpen_U
  have hP : AnalyticOnNhd ℂ (fun w => Complex.digamma w - Complex.digamma 1)
      {w : ℂ | 1 / 2 < w.re} :=
    analytic_digamma.sub analyticOnNhd_const
  have h1U : (1:ℂ) ∈ {w : ℂ | 1 / 2 < w.re} := by
    show (1:ℝ) / 2 < (1:ℂ).re
    norm_num
  have hfreq : ∃ᶠ z in 𝓝[≠] (1:ℂ),
      (∑' k : ℕ, (1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + z))) =
        Complex.digamma z - Complex.digamma 1 := by
    let f : ℕ → ℂ := fun n => ((1 + 1 / ((n:ℝ) + 1) : ℝ) : ℂ)
    have hf : Tendsto f atTop (𝓝[≠] (1:ℂ)) := by
      rw [tendsto_nhdsWithin_iff]
      constructor
      · have h0 : Tendsto (fun n : ℕ => (1 + 1 / ((n:ℝ) + 1) : ℝ)) atTop (𝓝 (1 + 0)) :=
          tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
        rw [add_zero] at h0
        have h1 := (Complex.continuous_ofReal.tendsto 1).comp h0
        rw [Complex.ofReal_one] at h1
        exact h1
      · refine Eventually.of_forall fun n => ?_
        simp only [f, Set.mem_compl_iff, Set.mem_singleton_iff]
        rw [← Complex.ofReal_one, Complex.ofReal_inj]
        have : 0 < 1 / ((n:ℝ) + 1) := by positivity
        intro h
        linarith
    refine hf.frequently (Eventually.frequently (Eventually.of_forall fun n => ?_))
    have : 0 < 1 / ((n:ℝ) + 1) := by positivity
    exact (hasSum_real (x := 1 + 1 / ((n:ℝ) + 1)) (by linarith)).tsum_eq
  have hEq := hS.eqOn_of_preconnected_of_frequently_eq hP hU h1U hfreq
  have e : (∑' k : ℕ, (1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + w))) =
      Complex.digamma w - Complex.digamma 1 := hEq hw
  rw [← e]
  exact (summable_term hw).hasSum

end SchoenfeldRH.P4
end File4

-- Upstream module PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
section File5
 

section
open scoped BigOperators

namespace Real

lemma pow_div_one_sub_le_two_mul {r : ℝ} (hr : 0 ≤ r) (hrhalf : r ≤ 1 / 2) (m : ℕ) :
    r ^ (m + 1) / (1 - r) ≤ 2 * r ^ (m + 1) := by
  have hpow : 0 ≤ r ^ (m + 1) := pow_nonneg hr _
  have hhalf' : (1 / 2 : ℝ) ≤ 1 - r := by linarith
  calc
    r ^ (m + 1) / (1 - r) ≤ r ^ (m + 1) / (1 / 2 : ℝ) := by
      exact div_le_div_of_nonneg_left hpow (by positivity) hhalf'
    _ = 2 * r ^ (m + 1) := by ring

end Real

namespace Complex

open scoped BigOperators in
 
lemma neg_log_one_sub_eq_tsum {z : ℂ} (hz : ‖z‖ < 1) :
    -log (1 - z) = ∑' n : ℕ, z ^ (n + 1) / (n + 1) := by
  have h := hasSum_taylorSeries_neg_log hz
  rw [← h.tsum_eq, h.summable.tsum_eq_zero_add]
  simp only [pow_zero, Nat.cast_zero, div_zero, zero_add, Nat.cast_add, Nat.cast_one]

noncomputable
def partialLogSum (m : ℕ) (z : ℂ) : ℂ :=
  -logTaylor (m + 1) (-z)

@[simp]
lemma partialLogSum_zero (z : ℂ) : partialLogSum 0 z = 0 := by
  simp [partialLogSum, logTaylor_succ, logTaylor_zero]

@[simp]
lemma partialLogSum_at_zero (m : ℕ) : partialLogSum m 0 = 0 := by
  simp [partialLogSum, logTaylor_at_zero]

lemma logTaylor_succ_neg (n : ℕ) (z : ℂ) :
    logTaylor (n + 1) (-z) = logTaylor n (-z) - z ^ n / n := by
  rw [logTaylor_succ, Pi.add_apply]
  have hsign : (-1 : ℂ) ^ (n + 1) * (-z) ^ n = -z ^ n := by
    have hzpow : (-z) ^ n = (((-1 : ℂ) * z) ^ n) := by simp
    rw [hzpow, mul_pow, ← mul_assoc, ← pow_add]
    have hpow : (-1 : ℂ) ^ (n + 1 + n) = (-1 : ℂ) := by
      rw [show n + 1 + n = 2 * n + 1 by omega, pow_add, pow_mul]
      norm_num
    rw [hpow]
    ring
  rw [show (-1 : ℂ) ^ (n + 1) * (-z) ^ n / n = -(z ^ n / n) by
    rw [hsign]
    ring]
  abel

lemma partialLogSum_succ (m : ℕ) :
    partialLogSum (m + 1) = partialLogSum m + (fun z : ℂ ↦ z ^ (m + 1) / (m + 1)) := by
  funext z
  simpa [partialLogSum, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
    congrArg Neg.neg (logTaylor_succ_neg (m + 1) z)

lemma logTaylor_neg_eq_neg_sum (m : ℕ) (z : ℂ) :
    logTaylor (m + 1) (-z) = -∑ k ∈ Finset.range m, z ^ (k + 1) / (k + 1) := by
  induction m with
  | zero =>
      simp [logTaylor_succ, logTaylor_zero]
  | succ m hm =>
      rw [logTaylor_succ_neg, hm, Finset.sum_range_succ]
      have hcast : ((m + 1 : ℕ) : ℂ) = (1 + (m : ℂ)) := by
        simp [Nat.cast_add, Nat.cast_one, add_comm]
      rw [hcast]
      ring_nf

lemma partialLogSum_eq_sum (m : ℕ) (z : ℂ) :
    partialLogSum m z = ∑ k ∈ Finset.range m, z ^ (k + 1) / (k + 1) := by
  simpa [partialLogSum] using congrArg Neg.neg (logTaylor_neg_eq_neg_sum m z)

lemma hasDerivAt_partialLogSum (m : ℕ) (z : ℂ) :
    HasDerivAt (partialLogSum m) (∑ j ∈ Finset.range m, z ^ j) z := by
  cases m with
  | zero =>
      have hzero : partialLogSum 0 = fun _ : ℂ ↦ (0 : ℂ) := by
        funext w
        exact partialLogSum_zero w
      simpa [hzero] using (hasDerivAt_const z (c := (0 : ℂ)))
  | succ m =>
      have hsum :
          (∑ j ∈ Finset.range (m + 1), z ^ j) =
            ∑ j ∈ Finset.range (m + 1), (-1) ^ j * (-z) ^ j := by
        refine Finset.sum_congr rfl ?_
        intro j hj
        symm
        calc
          (-1 : ℂ) ^ j * (-z) ^ j = (-1 : ℂ) ^ j * (((-1 : ℂ) * z) ^ j) := by simp
          _ = ((-1 : ℂ) ^ j * (-1 : ℂ) ^ j) * z ^ j := by rw [mul_pow]; ring
          _ = z ^ j := by
                rw [← pow_add, show j + j = 2 * j by omega, pow_mul]
                norm_num
      rw [hsum]
      simpa [partialLogSum] using!
        (((hasDerivAt_logTaylor (m + 1) (-z)).comp z (hasDerivAt_neg z)).neg)

lemma differentiable_partialLogSum (m : ℕ) :
    Differentiable ℂ (fun z : ℂ => partialLogSum m z) := by
  intro z
  exact (hasDerivAt_partialLogSum m z).differentiableAt

noncomputable
def logTail (m : ℕ) (z : ℂ) : ℂ :=
  ∑' k, z ^ (m + 1 + k) / (m + 1 + k)

lemma summable_logTail {z : ℂ} (hz : ‖z‖ < 1) (m : ℕ) :
    Summable (fun k => z ^ (m + 1 + k) / ((m + 1 + k) : ℂ)) := by
  have h_geom : Summable (fun k : ℕ => ‖z‖ ^ k) :=
    summable_geometric_of_lt_one (norm_nonneg z) hz
  refine Summable.of_norm_bounded (g := fun k => ‖z‖ ^ k) h_geom ?_
  intro k
  rw [norm_div, norm_pow]
  have h1 : (1 : ℝ) ≤ (m + 1 + k : ℝ) := by
    have : (0 : ℝ) ≤ (m + k : ℝ) := by positivity
    nlinarith
  have hnorm : ‖(↑m + 1 + ↑k : ℂ)‖ = (m + 1 + k : ℝ) := by
    simpa [Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using
      (Complex.norm_natCast (m + 1 + k))
  rw [hnorm]
  calc
    ‖z‖ ^ (m + 1 + k) / (m + 1 + k : ℝ) ≤ ‖z‖ ^ (m + 1 + k) := by
      exact div_le_self (pow_nonneg (norm_nonneg z) _) h1
    _ = ‖z‖ ^ (m + 1) * ‖z‖ ^ k := by rw [pow_add]
    _ ≤ 1 * ‖z‖ ^ k := by
          refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg (norm_nonneg z) k)
          exact pow_le_one₀ (norm_nonneg z) (le_of_lt hz)
    _ = ‖z‖ ^ k := one_mul _

lemma norm_logTail_le {z : ℂ} (hz : ‖z‖ < 1) (m : ℕ) :
    ‖logTail m z‖ ≤ ‖z‖ ^ (m + 1) / (1 - ‖z‖) := by
  dsimp only [logTail]
  have h_rhs_summable : Summable (fun k => ‖z‖ ^ (m + 1 + k)) := by
    simpa [pow_add] using
      (summable_geometric_of_lt_one (norm_nonneg z) hz).mul_left (‖z‖ ^ (m + 1))
  have h_norm_summable : Summable (fun k => ‖z ^ (m + 1 + k) / ((m + 1 + k) : ℂ)‖) := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) ?_ h_rhs_summable
    intro k
    rw [norm_div, norm_pow]
    have hnorm : ‖(↑m + 1 + ↑k : ℂ)‖ = (m + 1 + k : ℝ) := by
      simpa [Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using
        (Complex.norm_natCast (m + 1 + k))
    rw [hnorm]
    have hm : 1 ≤ (m + 1 + k : ℝ) := by
      have : (0 : ℝ) ≤ (m + k : ℝ) := by positivity
      nlinarith
    exact div_le_self (pow_nonneg (norm_nonneg z) _) hm
  calc
    ‖∑' k, z ^ (m + 1 + k) / ((m + 1 + k) : ℂ)‖
        ≤ ∑' k, ‖z ^ (m + 1 + k) / ((m + 1 + k) : ℂ)‖ :=
          norm_tsum_le_tsum_norm h_norm_summable
    _ ≤ ∑' k, ‖z‖ ^ (m + 1 + k) := by
          refine h_norm_summable.tsum_le_tsum ?_ h_rhs_summable
          intro k
          rw [norm_div, norm_pow]
          have hm : 1 ≤ (m + 1 + k : ℝ) := by
            have : (0 : ℝ) ≤ (m + k : ℝ) := by positivity
            nlinarith
          have hnorm : ‖(↑m + 1 + ↑k : ℂ)‖ = (m + 1 + k : ℝ) := by
            simpa [Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using
              (Complex.norm_natCast (m + 1 + k))
          rw [hnorm]
          exact div_le_self (pow_nonneg (norm_nonneg z) _) hm
    _ = ‖z‖ ^ (m + 1) / (1 - ‖z‖) := by
          have h_eq :
              (fun k => ‖z‖ ^ (m + 1 + k)) = fun k => ‖z‖ ^ (m + 1) * ‖z‖ ^ k := by
            ext k
            rw [pow_add]
          rw [h_eq, tsum_mul_left]
          have h_geom := hasSum_geometric_of_lt_one (norm_nonneg z) hz
          rw [h_geom.tsum_eq, div_eq_mul_inv]

lemma norm_logTail_le_two_mul_norm_pow {z : ℂ} (hz : ‖z‖ < 1) (hzhalf : ‖z‖ ≤ 1 / 2) (m : ℕ) :
    ‖logTail m z‖ ≤ 2 * ‖z‖ ^ (m + 1) :=
  (norm_logTail_le hz m).trans (Real.pow_div_one_sub_le_two_mul (norm_nonneg z) hzhalf m)

lemma norm_partialLogSum_le_nat_mul_max_one_norm_pow (m : ℕ) (z : ℂ) :
    ‖partialLogSum m z‖ ≤ (m : ℝ) * max 1 (‖z‖ ^ m) := by
  have hsum :
      ‖partialLogSum m z‖ ≤ ∑ k ∈ Finset.range m, ‖z ^ (k + 1) / (k + 1)‖ := by
    rw [partialLogSum_eq_sum]
    exact norm_sum_le _ _
  have hterm : ∀ k ∈ Finset.range m, ‖z ^ (k + 1) / (k + 1)‖ ≤ max 1 (‖z‖ ^ m) := by
    intro k hk
    rw [norm_div, norm_pow]
    have hk1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by
      have hk1_nat : (1 : ℕ) ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le k)
      exact_mod_cast hk1_nat
    have hdenom : ‖((k : ℂ) + 1)‖ = (k : ℝ) + 1 := by
      simpa [Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using
        (Complex.norm_natCast (k + 1))
    have hk_le : k + 1 ≤ m := Nat.succ_le_iff.2 (Finset.mem_range.1 hk)
    have hpow_le : ‖z‖ ^ (k + 1) ≤ max 1 (‖z‖ ^ m) := by
      have hz0 : 0 ≤ ‖z‖ := norm_nonneg z
      by_cases hz1 : ‖z‖ ≤ (1 : ℝ)
      · have : ‖z‖ ^ (k + 1) ≤ 1 := by exact pow_le_one₀ hz0 hz1
        exact this.trans (le_max_left _ _)
      · have hz1' : (1 : ℝ) ≤ ‖z‖ := le_of_lt (lt_of_not_ge hz1)
        have : ‖z‖ ^ (k + 1) ≤ ‖z‖ ^ m := pow_le_pow_right₀ hz1' hk_le
        exact this.trans (le_max_right _ _)
    calc
      ‖z‖ ^ (k + 1) / ‖((k : ℂ) + 1)‖ = ‖z‖ ^ (k + 1) / ((k : ℝ) + 1) := by simp [hdenom]
      _ ≤ ‖z‖ ^ (k + 1) := by
            exact div_le_self (pow_nonneg (norm_nonneg z) _) hk1
      _ ≤ max 1 (‖z‖ ^ m) := hpow_le
  have hsum_le :
      (∑ k ∈ Finset.range m, ‖z ^ (k + 1) / (k + 1)‖) ≤
        ∑ _k ∈ Finset.range m, max 1 (‖z‖ ^ m) :=
    Finset.sum_le_sum (fun k hk => hterm k hk)
  have hcard : ∑ _k ∈ Finset.range m, max 1 (‖z‖ ^ m) = (m : ℝ) * max 1 (‖z‖ ^ m) := by
    simp [Finset.sum_const]
  exact hsum.trans (hsum_le.trans_eq hcard)

lemma neg_log_one_sub_eq_partialLogSum_add_logTail {z : ℂ} (hz : ‖z‖ < 1) (m : ℕ) :
    -log (1 - z) = partialLogSum m z + logTail m z := by
  let f : ℕ → ℂ := fun k ↦ z ^ (k + 1) / ((k : ℂ) + 1)
  have h_summable : Summable f := by
    simpa [f, Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using
      (summable_logTail hz 0)
  have h_decomp := h_summable.sum_add_tsum_nat_add m
  rw [neg_log_one_sub_eq_tsum hz, partialLogSum_eq_sum, ← h_decomp]
  congr 1
  dsimp only [logTail]
  refine tsum_congr fun k ↦ ?_
  simp only [f, Nat.cast_add]
  ring_nf

end Complex
end
end File5

-- Upstream module PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.Norm
section File6

section
noncomputable section

namespace Complex

variable {z : ℂ}

theorem neg_norm_le_re (z : ℂ) : -‖z‖ ≤ z.re :=
  neg_le_of_abs_le (abs_re_le_norm z)

lemma norm_sub_one_le_one_add_norm (z : ℂ) : ‖z - 1‖ ≤ 1 + ‖z‖ := by
  have hone : ‖(1 : ℂ)‖ = (1 : ℝ) := by simpa using Complex.norm_natCast 1
  simpa [hone, add_comm] using norm_sub_le z (1 : ℂ)

lemma norm_one_sub_le_one_add_norm (z : ℂ) : ‖1 - z‖ ≤ 1 + ‖z‖ := by
  have hone : ‖(1 : ℂ)‖ = (1 : ℝ) := by simpa using Complex.norm_natCast 1
  simpa [hone] using norm_sub_le (1 : ℂ) z

lemma one_le_norm_one_sub_of_norm_gt_three {z : ℂ} (hz : 3 < ‖z‖) : (1 : ℝ) ≤ ‖1 - z‖ := by
  have hge : (‖z‖ - 1 : ℝ) ≤ ‖1 - z‖ := by
    have hone : ‖(1 : ℂ)‖ = (1 : ℝ) := by simpa using Complex.norm_natCast 1
    have h := norm_sub_norm_le z (1 : ℂ)
    rw [hone, norm_sub_rev] at h
    linarith
  linarith

lemma norm_inv_pow_le_one_of_one_le_norm (u : ℂ) (n : ℕ) (hu : (1 : ℝ) ≤ ‖u‖) :
    ‖(u ^ n)⁻¹‖ ≤ 1 := by
  have hge : (1 : ℝ) ≤ ‖u ^ n‖ := by
    rw [Complex.norm_pow]
    exact one_le_pow₀ hu
  calc ‖(u ^ n)⁻¹‖ = ‖(1 : ℂ) / u ^ n‖ := by rw [inv_eq_one_div]
    _ = 1 / ‖u ^ n‖ := by
        have hone : ‖(1 : ℂ)‖ = (1 : ℝ) := by simpa using Complex.norm_natCast 1
        rw [Complex.norm_div, hone]
    _ ≤ 1 := by simpa [one_div] using inv_le_one_of_one_le₀ hge

lemma one_sub_ne_one_of_norm_pos {z : ℂ} (hz : 0 < ‖z‖) : 1 - z ≠ 1 := by
  intro h
  exact hz.ne' (by simpa using sub_eq_self.mp h)

lemma ne_neg_nat_of_re_pos {w : ℂ} (hw : 0 < w.re) : ∀ n : ℕ, w ≠ -n := by
  intro n hn
  have hre : w.re = -(n : ℝ) := by
    have := congrArg Complex.re hn
    simpa using this
  nlinarith

end Complex
end
end
end File6

-- Upstream module PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.WeierstrassFactor
section File7
 

section
noncomputable section

open scoped BigOperators
open Set

namespace Complex

def weierstrassFactor (m : ℕ) (z : ℂ) : ℂ :=
  (1 - z) * exp (partialLogSum m z)

lemma weierstrassFactor_def (m : ℕ) (z : ℂ) :
    weierstrassFactor m z = (1 - z) * exp (partialLogSum m z) := by
  simp [weierstrassFactor]

@[simp]
lemma weierstrassFactor_zero (z : ℂ) : weierstrassFactor 0 z = 1 - z := by
  simp [weierstrassFactor]

@[simp]
lemma weierstrassFactor_at_zero (m : ℕ) : weierstrassFactor m 0 = 1 := by
  simp [weierstrassFactor, partialLogSum_at_zero]

@[simp]
lemma weierstrassFactor_at_one (m : ℕ) : weierstrassFactor m 1 = 0 := by
  simp [weierstrassFactor]

lemma weierstrassFactor_eq_zero_iff (m : ℕ) (z : ℂ) :
    weierstrassFactor m z = 0 ↔ z = 1 := by
  constructor
  · intro hz
    rw [weierstrassFactor] at hz
    rcases mul_eq_zero.mp hz with h1 | h2
    · exact (sub_eq_zero.mp h1).symm
    · exact absurd h2 (exp_ne_zero _)
  · rintro rfl
    simp [weierstrassFactor]

lemma weierstrassFactor_ne_zero_iff (m : ℕ) (z : ℂ) :
    weierstrassFactor m z ≠ 0 ↔ z ≠ 1 := by
  simpa [ne_eq] using (not_congr (weierstrassFactor_eq_zero_iff (m := m) (z := z)))

lemma weierstrassFactor_ne_zero_of_ne_one (m : ℕ) {z : ℂ} (hz : z ≠ 1) :
    weierstrassFactor m z ≠ 0 :=
  (weierstrassFactor_ne_zero_iff (m := m) (z := z)).2 hz

lemma weierstrassFactor_div_eq_zero_iff (m : ℕ) {a z : ℂ} (ha : a ≠ 0) :
    weierstrassFactor m (z / a) = 0 ↔ z = a := by
  rw [weierstrassFactor_eq_zero_iff]
  constructor
  · intro hz
    simpa using (div_eq_iff ha).mp hz
  · intro hz
    exact (div_eq_iff ha).mpr (by simpa only [one_mul] using hz)

lemma weierstrassFactor_div_ne_zero_iff (m : ℕ) {a z : ℂ} (ha : a ≠ 0) :
    weierstrassFactor m (z / a) ≠ 0 ↔ z ≠ a := by
  rw [not_iff_not]
  exact weierstrassFactor_div_eq_zero_iff m ha

lemma differentiable_weierstrassFactor (m : ℕ) :
    Differentiable ℂ (fun z : ℂ => weierstrassFactor m z) := by
  simpa [weierstrassFactor] using!
    ((differentiable_const (c := (1 : ℂ))).sub differentiable_id).mul
      (differentiable_exp.comp (differentiable_partialLogSum m))

lemma hasDerivAt_weierstrassFactor_at_one (m : ℕ) :
    HasDerivAt (weierstrassFactor m) (-Complex.exp (partialLogSum m 1)) 1 := by
  have hsub : HasDerivAt (fun z : ℂ => 1 - z) (-1) 1 := by
    simpa using! (hasDerivAt_const (1 : ℂ) (c := (1 : ℂ))).sub (hasDerivAt_id 1)
  have hexp :
      HasDerivAt (fun z : ℂ => Complex.exp (partialLogSum m z))
        ((∑ j ∈ Finset.range m, (1 : ℂ) ^ j) * Complex.exp (partialLogSum m 1)) 1 := by
    simpa [mul_comm] using!
      (Complex.hasDerivAt_exp (partialLogSum m 1)).comp 1 (hasDerivAt_partialLogSum m 1)
  simpa [weierstrassFactor] using! hsub.mul hexp

@[simp]
lemma deriv_weierstrassFactor_at_one (m : ℕ) :
    deriv (weierstrassFactor m) 1 = -Complex.exp (partialLogSum m 1) :=
  (hasDerivAt_weierstrassFactor_at_one m).deriv

lemma deriv_weierstrassFactor_at_one_ne_zero (m : ℕ) :
    deriv (weierstrassFactor m) 1 ≠ 0 := by
  simp [deriv_weierstrassFactor_at_one]

lemma hasDerivAt_weierstrassFactor_div_at_self (m : ℕ) {a : ℂ} (ha : a ≠ 0) :
    HasDerivAt (fun z : ℂ ↦ weierstrassFactor m (z / a))
      ((-Complex.exp (partialLogSum m 1)) / a) a := by
  have hcomp :
      HasDerivAt ((weierstrassFactor m) ∘ fun z : ℂ ↦ z / a)
        ((-Complex.exp (partialLogSum m 1)) * (1 / a)) a :=
    HasDerivAt.comp (x := a) (h := fun z : ℂ ↦ z / a) (h₂ := weierstrassFactor m)
      (by simpa [ha] using hasDerivAt_weierstrassFactor_at_one m)
      ((hasDerivAt_id a).div_const a)
  simpa [Function.comp, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using! hcomp

@[simp]
lemma deriv_weierstrassFactor_div_at_self (m : ℕ) {a : ℂ} (ha : a ≠ 0) :
    deriv (fun z : ℂ ↦ weierstrassFactor m (z / a)) a =
      (-Complex.exp (partialLogSum m 1)) / a :=
  (hasDerivAt_weierstrassFactor_div_at_self m ha).deriv

lemma deriv_weierstrassFactor_div_at_self_ne_zero (m : ℕ) {a : ℂ} (ha : a ≠ 0) :
    deriv (fun z : ℂ ↦ weierstrassFactor m (z / a)) a ≠ 0 := by
  simp [deriv_weierstrassFactor_div_at_self, ha]

theorem analyticOrderAt_weierstrassFactor_div_self (m : ℕ) {a : ℂ} (ha : a ≠ 0) :
    analyticOrderAt (fun z : ℂ => weierstrassFactor m (z / a)) a = (1 : ℕ∞) := by
  set F : ℂ → ℂ := fun z => weierstrassFactor m (z / a)
  have hF : AnalyticAt ℂ F a := by
    have hdiv : Differentiable ℂ (fun z : ℂ => z / a) := by
      simp [div_eq_mul_inv]
    have hdiff : Differentiable ℂ F := (differentiable_weierstrassFactor m).comp hdiv
    exact Differentiable.analyticAt (f := F) hdiff a
  let g : ℂ → ℂ := fun z => (-a⁻¹) * Complex.exp (partialLogSum m (z / a))
  have hg : AnalyticAt ℂ g a := by
    have hdiv : Differentiable ℂ (fun z : ℂ => z / a) := by
      simp [div_eq_mul_inv]
    have hpls : Differentiable ℂ (fun z : ℂ => partialLogSum m (z / a)) :=
      (differentiable_partialLogSum m).comp hdiv
    have hexp : Differentiable ℂ (fun z : ℂ => Complex.exp (partialLogSum m (z / a))) :=
      (Complex.differentiable_exp).comp hpls
    have hdiffg : Differentiable ℂ g := by
      simpa [g] using hexp.const_mul (-a⁻¹ : ℂ)
    exact Differentiable.analyticAt (f := g) hdiffg a
  have hg0 : g a ≠ 0 := by
    have hconst : (-a⁻¹ : ℂ) ≠ 0 := by simp [ha]
    have hexp0 : Complex.exp (partialLogSum m (a / a)) ≠ 0 :=
      Complex.exp_ne_zero (partialLogSum m (a / a))
    simpa [g] using mul_ne_zero hconst hexp0
  refine (hF.analyticOrderAt_eq_natCast (n := 1)).2 ?_
  refine ⟨g, hg, hg0, ?_⟩
  refine Filter.Eventually.of_forall ?_
  intro z
  have hlin : (1 - z / a) = (z - a) * (-a⁻¹) := by
    have h1 : (1 : ℂ) = a * a⁻¹ := by simp [ha]
    simp [div_eq_mul_inv, h1]
    ring
  simp only [F, g, pow_one, smul_eq_mul]
  rw [weierstrassFactor_def]
  simp [hlin, mul_assoc]

theorem analyticOrderNatAt_weierstrassFactor_div_self (m : ℕ) {a : ℂ} (ha : a ≠ 0) :
    analyticOrderNatAt (fun z : ℂ => weierstrassFactor m (z / a)) a = 1 := by
  simp [analyticOrderNatAt, analyticOrderAt_weierstrassFactor_div_self (m := m) ha]

lemma weierstrassFactor_eq_exp_neg_tail (m : ℕ) {z : ℂ} (hz : ‖z‖ < 1) (hz1 : z ≠ 1) :
    weierstrassFactor m z = exp (-logTail m z) := by
  unfold weierstrassFactor
  have hz_ne_1 : 1 - z ≠ 0 := sub_ne_zero.mpr hz1.symm
  rw [← exp_log hz_ne_1, ← Complex.exp_add]
  have hsum : log (1 - z) + partialLogSum m z = -logTail m z := by
    have hdecomp := neg_log_one_sub_eq_partialLogSum_add_logTail hz m
    calc
      log (1 - z) + partialLogSum m z
          = log (1 - z) + (partialLogSum m z + logTail m z) - logTail m z := by ring
      _ = log (1 - z) + (-log (1 - z)) - logTail m z := by rw [hdecomp]
      _ = -logTail m z := by ring
  simp [hsum]

theorem weierstrassFactor_sub_one_pow_bound {m : ℕ} {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    ‖weierstrassFactor m z - 1‖ ≤ 4 * ‖z‖ ^ (m + 1) := by
  by_cases hm : m = 0
  · subst hm
    have hmain : ‖(1 - z) - 1‖ ≤ 4 * ‖z‖ ^ 1 := by
      have h : (1 - z) - 1 = -z := by ring
      calc
        ‖(1 - z) - 1‖ = ‖-z‖ := by simp [h]
        _ = ‖z‖ := norm_neg z
        _ = ‖z‖ ^ 1 := by simp
        _ ≤ 4 * ‖z‖ ^ 1 := by nlinarith [pow_nonneg (norm_nonneg z) 1]
    simpa [weierstrassFactor] using hmain
  · have hz_lt : ‖z‖ < 1 := lt_of_le_of_lt hz (by norm_num)
    by_cases hz1 : z = 1
    · exfalso; rw [hz1] at hz; norm_num at hz
    have h_eq : weierstrassFactor m z = exp (-logTail m z) :=
      weierstrassFactor_eq_exp_neg_tail m hz_lt hz1
    rw [h_eq]
    have h_tail_bound := norm_logTail_le_two_mul_norm_pow hz_lt hz m
    have hw_le_one : ‖-logTail m z‖ ≤ 1 := by
      simp only [norm_neg]
      have : ‖logTail m z‖ ≤ 1 := by
        have hm_pos : 0 < m := Nat.pos_of_ne_zero hm
        have h2 : 2 ≤ m + 1 := by
          exact Nat.succ_le_succ (Nat.succ_le_iff.2 hm_pos)
        have hpow : (‖z‖ ^ (m + 1)) ≤ (‖z‖ ^ 2) := by
          have hz1' : ‖z‖ ≤ 1 := by nlinarith [hz]
          have hz0' : 0 ≤ ‖z‖ := norm_nonneg z
          exact pow_le_pow_of_le_one hz0' hz1' h2
        have hmul : 2 * ‖z‖ ^ (m + 1) ≤ 2 * ‖z‖ ^ 2 := by gcongr
        have hsq : 2 * ‖z‖ ^ 2 ≤ 1 := by
          have hz0 : 0 ≤ ‖z‖ := norm_nonneg z
          have hz_sq : ‖z‖ ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := pow_le_pow_left₀ hz0 hz 2
          nlinarith
        exact (h_tail_bound.trans hmul).trans hsq
      linarith
    have h_exp_sub_one : ‖exp (-logTail m z) - 1‖ ≤ 2 * ‖-logTail m z‖ :=
      Complex.norm_exp_sub_one_le hw_le_one
    simp only [norm_neg] at h_exp_sub_one
    calc
      ‖exp (-logTail m z) - 1‖ ≤ 2 * ‖logTail m z‖ := h_exp_sub_one
      _ ≤ 2 * (2 * ‖z‖ ^ (m + 1)) := by gcongr
      _ = 4 * ‖z‖ ^ (m + 1) := by ring

lemma log_norm_weierstrassFactor_ge_log_norm_one_sub_sub (m : ℕ) (z : ℂ) :
    Real.log ‖1 - z‖ - ‖partialLogSum m z‖ ≤ Real.log ‖weierstrassFactor m z‖ := by
  by_cases hz1 : z = (1 : ℂ)
  · subst hz1
    simp [weierstrassFactor]
  set S : ℂ := partialLogSum m z
  have hS : weierstrassFactor m z = (1 - z) * Complex.exp S := by
    simp [weierstrassFactor, S]
  have hnorm_pos : 0 < ‖(1 : ℂ) - z‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hz1))
  have hlog :
      Real.log ‖weierstrassFactor m z‖ = Real.log ‖1 - z‖ + S.re := by
    have hne : ‖(1 : ℂ) - z‖ ≠ 0 := ne_of_gt hnorm_pos
    calc
      Real.log ‖weierstrassFactor m z‖
          = Real.log (‖(1 : ℂ) - z‖ * ‖Complex.exp S‖) := by
              simp [hS]
      _ = Real.log ‖(1 : ℂ) - z‖ + Real.log ‖Complex.exp S‖ := by
            simpa using (Real.log_mul hne (ne_of_gt (by simp)))
      _ = Real.log ‖(1 : ℂ) - z‖ + S.re := by
            simp [Complex.norm_exp, Real.log_exp]
      _ = Real.log ‖1 - z‖ + S.re := by simp [sub_eq_add_neg, add_comm]
  have hre : S.re ≥ -‖S‖ := Complex.neg_norm_le_re S
  have : Real.log ‖weierstrassFactor m z‖ ≥ Real.log ‖1 - z‖ - ‖S‖ := by
    linarith [hlog, hre]
  simpa [S] using this

lemma log_norm_weierstrassFactor_ge_neg_two_pow {m : ℕ} {z : ℂ} (hz : ‖z‖ ≤ (1 / 2 : ℝ)) :
    (-2 : ℝ) * ‖z‖ ^ (m + 1) ≤ Real.log ‖weierstrassFactor m z‖ := by
  have hz_lt : ‖z‖ < (1 : ℝ) := lt_of_le_of_lt hz (by norm_num)
  have hz1 : z ≠ (1 : ℂ) := by
    intro h
    have : (1 : ℝ) ≤ (1 / 2 : ℝ) := by
      simpa [h] using hz
    norm_num at this
  have hEq : weierstrassFactor m z = Complex.exp (-logTail m z) :=
    weierstrassFactor_eq_exp_neg_tail m hz_lt hz1
  have hlog :
      Real.log ‖weierstrassFactor m z‖ = (-logTail m z).re := by
    simp [hEq, Complex.norm_exp, Real.log_exp]
  have hre : (-logTail m z).re ≥ -‖logTail m z‖ := by
    simpa [norm_neg] using Complex.neg_norm_le_re (-logTail m z)
  have htail := norm_logTail_le_two_mul_norm_pow hz_lt hz m
  have : (-logTail m z).re ≥ (-2 : ℝ) * ‖z‖ ^ (m + 1) := by
    calc
      (-logTail m z).re ≥ -‖logTail m z‖ := hre
      _ ≥ (-2 : ℝ) * ‖z‖ ^ (m + 1) := by
            nlinarith [htail]
  simpa [hlog, mul_assoc, mul_left_comm, mul_comm] using this

lemma log_norm_weierstrassFactor_ge_log_norm_one_sub_nat_mul_max_one_norm_pow
    (m : ℕ) (z : ℂ) :
    Real.log ‖1 - z‖ - (m : ℝ) * max 1 (‖z‖ ^ m) ≤ Real.log ‖weierstrassFactor m z‖ := by
  calc
    Real.log ‖1 - z‖ - (m : ℝ) * max 1 (‖z‖ ^ m)
        ≤ Real.log ‖1 - z‖ - ‖partialLogSum m z‖ := by
          gcongr
          exact norm_partialLogSum_le_nat_mul_max_one_norm_pow m z
    _ ≤ Real.log ‖weierstrassFactor m z‖ :=
      log_norm_weierstrassFactor_ge_log_norm_one_sub_sub m z

private lemma eventually_le_norm_div_two_of_summable_inv_pow {m : ℕ} {a : ℕ → ℂ}
    (h_sum : Summable (fun n : ℕ => ‖a n‖⁻¹ ^ (m + 1))) (h_nonzero : ∀ n, a n ≠ 0) :
    ∀ R ≥ 0, ∀ᶠ n in Filter.atTop, R ≤ ‖a n‖ / 2 := by
  intro R hR
  by_cases hR0 : R = 0
  · subst hR0
    exact Filter.Eventually.of_forall fun _ => by positivity
  have hRpos : 0 < R := lt_of_le_of_ne hR (by simpa [eq_comm] using hR0)
  have htend : Filter.Tendsto (fun n : ℕ => ‖a n‖⁻¹ ^ (m + 1)) Filter.atTop (nhds (0 : ℝ)) := by
    simpa [Nat.cofinite_eq_atTop] using h_sum.tendsto_cofinite_zero
  have hεpos : 0 < (1 / (2 * R) : ℝ) ^ (m + 1) := by
    have : 0 < (1 / (2 * R) : ℝ) := by
      have : 0 < (2 * R : ℝ) := by positivity
      exact one_div_pos.mpr this
    exact pow_pos this _
  filter_upwards [htend.eventually (eventually_lt_nhds hεpos)] with n hn
  by_contra h
  have hlt : ‖a n‖ / 2 < R := lt_of_not_ge h
  have hle : ‖a n‖ ≤ 2 * R := by nlinarith
  have hanorm_pos : 0 < ‖a n‖ := norm_pos_iff.mpr (h_nonzero n)
  have hinv : (1 / (2 * R : ℝ)) ≤ ‖a n‖⁻¹ := by
    simpa [one_div] using (one_div_le_one_div_of_le hanorm_pos hle)
  have hpow :
      (1 / (2 * R : ℝ)) ^ (m + 1) ≤ ‖a n‖⁻¹ ^ (m + 1) :=
    pow_le_pow_left₀ (by positivity) hinv _
  exact (not_lt_of_ge hpow) hn

private lemma summable_scaled_bound_of_summable_inv_pow {m : ℕ} {a : ℕ → ℂ}
    (h_sum : Summable (fun n : ℕ => ‖a n‖⁻¹ ^ (m + 1))) :
    ∀ R ≥ 0, Summable (fun n : ℕ => 4 * R ^ (m + 1) / ‖a n‖ ^ (m + 1)) := by
  intro R _hR
  simpa [div_eq_mul_inv, inv_pow, mul_assoc, mul_left_comm, mul_comm] using
    h_sum.mul_left (4 * R ^ (m + 1))

lemma continuousOn_weierstrassFactor_div (m : ℕ) (a : ℂ) (s : Set ℂ) :
    ContinuousOn (fun z : ℂ ↦ weierstrassFactor m (z / a)) s := by
  simpa using! (differentiable_weierstrassFactor m).continuous.continuousOn.comp
    (continuous_id.div_const a).continuousOn (mapsTo_univ (fun z : ℂ ↦ z / a) s)

lemma norm_weierstrassFactor_div_sub_one_le_pow_div (m : ℕ) {a z : ℂ}
    (hza : ‖z‖ ≤ ‖a‖ / 2) :
    ‖weierstrassFactor m (z / a) - 1‖ ≤ 4 * ‖z‖ ^ (m + 1) / ‖a‖ ^ (m + 1) := by
  by_cases ha : a = 0
  · have hz : z = 0 := by
      apply norm_eq_zero.mp
      rw [ha] at hza
      simpa using hza
    subst z
    simp [ha]
  · have ha' : 0 < ‖a‖ := norm_pos_iff.mpr ha
    have hza' : ‖z / a‖ ≤ 1 / 2 := by
      rw [Complex.norm_div, div_le_iff₀ ha']
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hza
    have hbase := weierstrassFactor_sub_one_pow_bound (m := m) (z := z / a) hza'
    calc
      ‖weierstrassFactor m (z / a) - 1‖ ≤ ‖z‖ ^ (m + 1) / ‖a‖ ^ (m + 1) * 4 := by
        simpa [Complex.norm_div, div_pow, mul_comm, mul_left_comm, mul_assoc] using hbase
      _ = 4 * ‖z‖ ^ (m + 1) / ‖a‖ ^ (m + 1) := by ring

lemma summable_norm_weierstrassFactor_div_sub_one_of_summable_inv_pow {m : ℕ} {a : ℕ → ℂ}
    (h_sum : Summable (fun n : ℕ => ‖a n‖⁻¹ ^ (m + 1))) (h_nonzero : ∀ n, a n ≠ 0) (z : ℂ) :
    Summable (fun n : ℕ ↦ ‖weierstrassFactor m (z / a n) - 1‖) := by
  refine Summable.of_norm_bounded_eventually_nat
    (summable_scaled_bound_of_summable_inv_pow h_sum ‖z‖ (norm_nonneg z)) ?_
  filter_upwards
    [eventually_le_norm_div_two_of_summable_inv_pow h_sum h_nonzero ‖z‖ (norm_nonneg z)]
    with n hn
  simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using
    norm_weierstrassFactor_div_sub_one_le_pow_div (m := m) (a := a n) (z := z) hn

lemma hasProdUniformlyOn_weierstrassFactor_div_of_bound {K : Set ℂ} (hK : IsCompact K)
    {m : ℕ → ℕ} {a : ℕ → ℂ} {R : ℝ}
    (hR : ∀ z ∈ K, ‖z‖ ≤ R) (hsmall : ∀ᶠ n in Filter.atTop, R ≤ ‖a n‖ / 2)
    (hsumm : Summable (fun n : ℕ ↦ 4 * R ^ (m n + 1) / ‖a n‖ ^ (m n + 1))) :
    HasProdUniformlyOn (fun n z ↦ weierstrassFactor (m n) (z / a n))
      (fun z ↦ ∏' n, weierstrassFactor (m n) (z / a n)) K := by
  have hbound :
      ∀ᶠ n in Filter.atTop,
        ∀ z ∈ K,
          ‖weierstrassFactor (m n) (z / a n) - 1‖ ≤ 4 * R ^ (m n + 1) / ‖a n‖ ^ (m n + 1) := by
    filter_upwards [hsmall] with n hn z hz
    refine (norm_weierstrassFactor_div_sub_one_le_pow_div (m := m n) ?_).trans ?_
    · exact (hR z hz).trans hn
    · have hpow : ‖z‖ ^ (m n + 1) ≤ R ^ (m n + 1) :=
        pow_le_pow_left₀ (norm_nonneg z) (hR z hz) (m n + 1)
      refine div_le_div_of_nonneg_right ?_ (pow_nonneg (norm_nonneg (a n)) _)
      exact mul_le_mul_of_nonneg_left hpow (by positivity)
  have hcts :
      ∀ n, ContinuousOn (fun z ↦ weierstrassFactor (m n) (z / a n) - 1) K := by
    intro n
    exact (continuousOn_weierstrassFactor_div (m n) (a n) K).fun_sub continuousOn_const
  simpa using hsumm.hasProdUniformlyOn_nat_one_add (K := K)
    (f := fun n z ↦ weierstrassFactor (m n) (z / a n) - 1) hK hbound hcts

lemma hasProdLocallyUniformlyOn_weierstrassFactor_div {s : Set ℂ} (hs : IsOpen s)
    {m : ℕ → ℕ} {a : ℕ → ℂ}
    (hsmall : ∀ R ≥ 0, ∀ᶠ n in Filter.atTop, R ≤ ‖a n‖ / 2)
    (hsumm : ∀ R ≥ 0, Summable (fun n : ℕ ↦ 4 * R ^ (m n + 1) / ‖a n‖ ^ (m n + 1))) :
    HasProdLocallyUniformlyOn (fun n z ↦ weierstrassFactor (m n) (z / a n))
      (fun z ↦ ∏' n, weierstrassFactor (m n) (z / a n)) s := by
  apply hasProdLocallyUniformlyOn_of_forall_compact hs
  intro K hKs hK
  obtain ⟨R, hR⟩ : ∃ R, ∀ z ∈ K, ‖z‖ ≤ R := by
    by_cases hKe : K.Nonempty
    · obtain ⟨z, hzK, hzmax⟩ := hK.exists_isMaxOn hKe continuous_norm.continuousOn
      exact ⟨‖z‖, fun w hw ↦ (isMaxOn_iff.mp hzmax) w hw⟩
    · exact ⟨0, fun z hz ↦ False.elim <| hKe ⟨z, hz⟩⟩
  let R' := max R 0
  have hR'0 : 0 ≤ R' := le_max_right _ _
  have hR' : ∀ z ∈ K, ‖z‖ ≤ R' := by
    intro z hz
    exact (hR z hz).trans (le_max_left _ _)
  exact hasProdUniformlyOn_weierstrassFactor_div_of_bound hK hR'
    (hsmall R' hR'0) (hsumm R' hR'0)

lemma hasProdLocallyUniformlyOn_weierstrassFactor_div_of_summable_inv_pow {m : ℕ} {a : ℕ → ℂ}
    (h_sum : Summable (fun n : ℕ => ‖a n‖⁻¹ ^ (m + 1))) (h_nonzero : ∀ n, a n ≠ 0) :
    HasProdLocallyUniformlyOn (fun n z ↦ weierstrassFactor m (z / a n))
      (fun z ↦ ∏' n, weierstrassFactor m (z / a n)) Set.univ := by
  simpa using
    hasProdLocallyUniformlyOn_weierstrassFactor_div (s := (Set.univ : Set ℂ)) isOpen_univ
      (m := fun _ => m) (a := a)
      (eventually_le_norm_div_two_of_summable_inv_pow h_sum h_nonzero)
      (summable_scaled_bound_of_summable_inv_pow h_sum)

lemma multipliableLocallyUniformlyOn_weierstrassFactor_div {s : Set ℂ} (hs : IsOpen s)
    {m : ℕ → ℕ} {a : ℕ → ℂ}
    (hsmall : ∀ R ≥ 0, ∀ᶠ n in Filter.atTop, R ≤ ‖a n‖ / 2)
    (hsumm : ∀ R ≥ 0, Summable (fun n : ℕ ↦ 4 * R ^ (m n + 1) / ‖a n‖ ^ (m n + 1))) :
    MultipliableLocallyUniformlyOn (fun n z ↦ weierstrassFactor (m n) (z / a n)) s :=
  ⟨_, hasProdLocallyUniformlyOn_weierstrassFactor_div hs hsmall hsumm⟩

lemma multipliableLocallyUniformlyOn_weierstrassFactor_div_of_summable_inv_pow {m : ℕ}
    {a : ℕ → ℂ} (h_sum : Summable (fun n : ℕ => ‖a n‖⁻¹ ^ (m + 1)))
    (h_nonzero : ∀ n, a n ≠ 0) :
    MultipliableLocallyUniformlyOn (fun n z ↦ weierstrassFactor m (z / a n)) Set.univ :=
  ⟨_, hasProdLocallyUniformlyOn_weierstrassFactor_div_of_summable_inv_pow h_sum h_nonzero⟩

end Complex
end
end
end File7

-- Upstream module PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.CanonicalProduct
section File8
 

section
noncomputable section

open Filter Topology

namespace Complex

def canonicalProduct (m : ℕ) (a : ℕ → ℂ) (z : ℂ) : ℂ :=
  ∏' n : ℕ, weierstrassFactor m (z / a n)

@[simp] theorem canonicalProduct_def (m : ℕ) (a : ℕ → ℂ) (z : ℂ) :
    canonicalProduct m a z = ∏' n : ℕ, weierstrassFactor m (z / a n) :=
  rfl

theorem hasProdLocallyUniformlyOn_canonicalProduct {m : ℕ} {a : ℕ → ℂ}
    (h_sum : Summable (fun n : ℕ => ‖a n‖⁻¹ ^ (m + 1))) (h_nonzero : ∀ n, a n ≠ 0) :
    HasProdLocallyUniformlyOn (fun n z ↦ weierstrassFactor m (z / a n))
      (canonicalProduct m a) Set.univ := by
  simpa [canonicalProduct] using!
    hasProdLocallyUniformlyOn_weierstrassFactor_div_of_summable_inv_pow
      (m := m) (a := a) h_sum h_nonzero

theorem multipliableLocallyUniformlyOn_canonicalProduct {m : ℕ} {a : ℕ → ℂ}
    (h_sum : Summable (fun n : ℕ => ‖a n‖⁻¹ ^ (m + 1))) (h_nonzero : ∀ n, a n ≠ 0) :
    MultipliableLocallyUniformlyOn (fun n z ↦ weierstrassFactor m (z / a n))
      (Set.univ : Set ℂ) := by
  simpa using
    (hasProdLocallyUniformlyOn_canonicalProduct h_sum h_nonzero).multipliableLocallyUniformlyOn

theorem hasProdUniformlyOn_canonicalProduct_compact {m : ℕ} {a : ℕ → ℂ}
    (h_sum : Summable (fun n : ℕ => ‖a n‖⁻¹ ^ (m + 1))) (h_nonzero : ∀ n, a n ≠ 0)
    {K : Set ℂ} (hK : IsCompact K) :
    HasProdUniformlyOn (fun n z ↦ weierstrassFactor m (z / a n)) (canonicalProduct m a) K := by
  have hloc :
      HasProdLocallyUniformlyOn (fun n z ↦ weierstrassFactor m (z / a n))
        (canonicalProduct m a) K :=
    (hasProdLocallyUniformlyOn_canonicalProduct h_sum h_nonzero).mono (by simp : K ⊆ Set.univ)
  exact hloc.hasProdUniformlyOn_of_isCompact hK

theorem canonicalProduct_converges_uniformOn_compact {m : ℕ} {a : ℕ → ℂ}
    (h_sum : Summable (fun n : ℕ => ‖a n‖⁻¹ ^ (m + 1))) (h_nonzero : ∀ n, a n ≠ 0) :
    ∀ K : Set ℂ, IsCompact K →
      TendstoUniformlyOn (fun s z => ∏ n ∈ s, weierstrassFactor m (z / a n))
        (canonicalProduct m a) Filter.atTop K := by
  intro K hK
  exact (hasProdUniformlyOn_iff_tendstoUniformlyOn.1
    (hasProdUniformlyOn_canonicalProduct_compact h_sum h_nonzero hK))

theorem differentiable_canonicalProduct {m : ℕ} {a : ℕ → ℂ}
    (h_sum : Summable (fun n : ℕ => ‖a n‖⁻¹ ^ (m + 1))) (h_nonzero : ∀ n, a n ≠ 0) :
    Differentiable ℂ (canonicalProduct m a) := by
  have hloc :=
    HasProdLocallyUniformlyOn.tendstoLocallyUniformlyOn_finsetRange
      (hasProdLocallyUniformlyOn_canonicalProduct h_sum h_nonzero)
  have hfactor : ∀ i : ℕ, Differentiable ℂ (fun z ↦ weierstrassFactor m (z / a i)) := by
    intro i
    simpa using! (differentiable_weierstrassFactor m).comp (differentiable_id.div_const (a i))
  have hpartial :
      ∀ᶠ N in Filter.atTop,
        DifferentiableOn ℂ (fun z ↦ ∏ n ∈ Finset.range N, weierstrassFactor m (z / a n))
          Set.univ := by
    filter_upwards with N
    simpa [differentiableOn_univ] using
      (Differentiable.fun_finsetProd (u := Finset.range N) fun i hi ↦ hfactor i)
  exact differentiableOn_univ.mp <| hloc.differentiableOn hpartial isOpen_univ

theorem analyticOnNhd_canonicalProduct {m : ℕ} {a : ℕ → ℂ}
    (h_sum : Summable (fun n : ℕ => ‖a n‖⁻¹ ^ (m + 1))) (h_nonzero : ∀ n, a n ≠ 0) :
    AnalyticOnNhd ℂ (canonicalProduct m a) Set.univ := by
  exact DifferentiableOn.analyticOnNhd
    (differentiableOn_univ.mpr (differentiable_canonicalProduct h_sum h_nonzero)) isOpen_univ

theorem logDeriv_weierstrassFactor_one_div {a z : ℂ} (ha : a ≠ 0) (hz : z ≠ a) :
    logDeriv (fun w : ℂ => weierstrassFactor 1 (w / a)) z =
      1 / (z - a) + 1 / a := by
  have hE :
      (fun w : ℂ => weierstrassFactor 1 (w / a)) =
        fun w : ℂ => (1 - w / a) * exp (w / a) := by
    ext w
    simp [weierstrassFactor_def, partialLogSum_eq_sum]
  have hf : (1 - z / a) ≠ 0 := by
    intro hzero
    have hdiv : z / a = 1 := by
      exact (sub_eq_zero.mp hzero).symm
    exact hz ((div_eq_one_iff_eq ha).1 hdiv)
  rw [hE, show (fun w : ℂ => (1 - w / a) * exp (w / a)) =
      (fun w : ℂ => 1 - w / a) * fun w : ℂ => exp (w / a) from rfl,
    logDeriv_mul z hf (exp_ne_zero (z / a)) (by fun_prop) (by fun_prop)]
  have hleft : logDeriv (fun w : ℂ => 1 - w / a) z = 1 / (z - a) := by
    rw [logDeriv_apply]
    have hderiv : deriv (fun w : ℂ => 1 - w / a) z = -(1 / a) := by
      simp [one_div]
    rw [hderiv]
    have haz : -z + a ≠ 0 := by
      simpa [sub_eq_add_neg, add_comm] using sub_ne_zero.mpr (Ne.symm hz)
    field_simp [ha, sub_ne_zero.mpr hz, haz]
    have haz' : a - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
    have hza : z - a = -(a - z) := by ring
    rw [hza]
    field_simp [haz']
  have hright : logDeriv (fun w : ℂ => exp (w / a)) z = 1 / a := by
    rw [logDeriv_apply]
    have hderiv : deriv (fun w : ℂ => exp (w / a)) z =
        exp (z / a) * (1 / a) := by
      simp [one_div]
    rw [hderiv]
    field_simp [exp_ne_zero (z / a)]
  rw [hleft, hright]

@[simp]
theorem canonicalProduct_apply_eq_zero {m : ℕ} {a : ℕ → ℂ}
    (h_sum : Summable (fun n : ℕ => ‖a n‖⁻¹ ^ (m + 1))) (h_nonzero : ∀ n, a n ≠ 0) (n : ℕ) :
    canonicalProduct m a (a n) = 0 := by
  let f : ℕ → ℂ := fun k ↦ weierstrassFactor m (a n / a k)
  have hmult : Multipliable f :=
    (multipliableLocallyUniformlyOn_canonicalProduct h_sum h_nonzero).multipliable (by simp)
  have htend :
      Tendsto (fun N : ℕ ↦ ∏ k ∈ Finset.range N, f k) Filter.atTop
        (𝓝 (canonicalProduct m a (a n))) := by
    simpa [f, canonicalProduct] using hmult.hasProd.tendsto_prod_nat
  have hzero :
      (fun N : ℕ ↦ ∏ k ∈ Finset.range N, f k) =ᶠ[Filter.atTop] fun _ ↦ (0 : ℂ) := by
    refine Filter.eventually_atTop.2 ⟨n + 1, fun N hN ↦ ?_⟩
    have hnN : n ∈ Finset.range N := Finset.mem_range.mpr <| lt_of_lt_of_le (Nat.lt_succ_self n) hN
    apply Finset.prod_eq_zero hnN
    simp [f, h_nonzero n, weierstrassFactor_at_one]
  exact tendsto_nhds_unique_of_eventuallyEq htend tendsto_const_nhds hzero

theorem canonicalProduct_eq_zero_of_mem_range {m : ℕ} {a : ℕ → ℂ}
    (h_sum : Summable (fun n : ℕ => ‖a n‖⁻¹ ^ (m + 1))) (h_nonzero : ∀ n, a n ≠ 0)
    {z : ℂ} (hz : z ∈ Set.range a) :
    canonicalProduct m a z = 0 := by
  rcases hz with ⟨n, rfl⟩
  exact canonicalProduct_apply_eq_zero h_sum h_nonzero n

theorem canonicalProduct_ne_zero {m : ℕ} {a : ℕ → ℂ}
    (h_sum : Summable (fun n : ℕ => ‖a n‖⁻¹ ^ (m + 1))) (h_nonzero : ∀ n, a n ≠ 0)
    {z : ℂ} (hz : z ∉ Set.range a) :
    canonicalProduct m a z ≠ 0 := by
  let f : ℕ → ℂ := fun n ↦ weierstrassFactor m (z / a n) - 1
  have hfn : ∀ n, 1 + f n ≠ 0 := by
    intro n
    have hza : z ≠ a n := by
      intro hza
      exact hz ⟨n, hza.symm⟩
    simpa [f] using (weierstrassFactor_div_ne_zero_iff (m := m) (a := a n) (z := z)
      (h_nonzero n)).2 hza
  have hnormsumm :
      Summable (fun n : ℕ ↦ ‖weierstrassFactor m (z / a n) - 1‖) :=
    summable_norm_weierstrassFactor_div_sub_one_of_summable_inv_pow
      (m := m) (a := a) h_sum h_nonzero z
  simpa [canonicalProduct, f] using
    (tprod_one_add_ne_zero_of_summable (f := f) hfn hnormsumm)

theorem differentiableOn_canonicalPartialProduct (m : ℕ) (a : ℕ → ℂ) (N : ℕ) :
    DifferentiableOn ℂ (fun z ↦ ∏ k ∈ Finset.range N, weierstrassFactor m (z / a k)) Set.univ := by
  simpa [differentiableOn_univ] using
    (Differentiable.fun_finsetProd (u := Finset.range N) fun i _ =>
      (differentiable_weierstrassFactor m).comp (differentiable_id.div_const (a i)))

private theorem tendsto_deriv_canonicalPartialProduct {m : ℕ} {a : ℕ → ℂ}
    (h_sum : Summable (fun n : ℕ => ‖a n‖⁻¹ ^ (m + 1))) (h_nonzero : ∀ n, a n ≠ 0) (n : ℕ) :
    Tendsto (fun N ↦ deriv (fun z ↦ ∏ k ∈ Finset.range N, weierstrassFactor m (z / a k)) (a n))
      Filter.atTop
      (𝓝 (deriv (canonicalProduct m a) (a n))) := by
  have hloc :=
    HasProdLocallyUniformlyOn.tendstoLocallyUniformlyOn_finsetRange
      (hasProdLocallyUniformlyOn_weierstrassFactor_div_of_summable_inv_pow
        (m := m) (a := a) h_sum h_nonzero)
  have hpartial :
      ∀ᶠ N in Filter.atTop,
        DifferentiableOn ℂ
          (fun z ↦ ∏ k ∈ Finset.range N, weierstrassFactor m (z / a k)) Set.univ := by
    filter_upwards with N
    exact differentiableOn_canonicalPartialProduct m a N
  simpa [canonicalProduct] using!
    (hloc.deriv hpartial isOpen_univ).tendsto_at (by simp)

theorem canonicalProduct_eq_zero_iff {m : ℕ} {a : ℕ → ℂ}
    (h_sum : Summable (fun n : ℕ => ‖a n‖⁻¹ ^ (m + 1))) (h_nonzero : ∀ n, a n ≠ 0)
    {z : ℂ} :
    canonicalProduct m a z = 0 ↔ z ∈ Set.range a := by
  constructor
  · intro hz0
    by_contra hzrange
    exact (canonicalProduct_ne_zero h_sum h_nonzero hzrange) hz0
  · exact canonicalProduct_eq_zero_of_mem_range h_sum h_nonzero

theorem canonicalProduct_ne_zero_iff {m : ℕ} {a : ℕ → ℂ}
    (h_sum : Summable (fun n : ℕ => ‖a n‖⁻¹ ^ (m + 1))) (h_nonzero : ∀ n, a n ≠ 0)
    {z : ℂ} :
    canonicalProduct m a z ≠ 0 ↔ z ∉ Set.range a := by
  rw [not_iff_not]
  exact canonicalProduct_eq_zero_iff h_sum h_nonzero

theorem logDeriv_canonicalProduct_one_eq_tsum {a : ℕ → ℂ}
    (h_sum : Summable (fun n : ℕ => ‖a n‖⁻¹ ^ (2 : ℕ))) (h_nonzero : ∀ n, a n ≠ 0)
    {z : ℂ} (hz : z ∉ Set.range a)
    (hm : Summable (fun n : ℕ => 1 / (z - a n) + 1 / a n)) :
    logDeriv (canonicalProduct 1 a) z =
      ∑' n : ℕ, (1 / (z - a n) + 1 / a n) := by
  let Φ : ℕ → ℂ → ℂ := fun n w => weierstrassFactor 1 (w / a n)
  have hf : ∀ n, Φ n z ≠ 0 := by
    intro n
    refine weierstrassFactor_ne_zero_of_ne_one 1 ?_
    intro h
    have hza : z = a n := (div_eq_one_iff_eq (h_nonzero n)).1 h
    exact hz ⟨n, hza.symm⟩
  have hd : ∀ n, DifferentiableOn ℂ (Φ n) (Set.univ : Set ℂ) := by
    intro n
    exact ((differentiable_weierstrassFactor 1).comp
      (differentiable_id.div_const (a n))).differentiableOn
  have hm' : Summable fun n => logDeriv (Φ n) z := by
    refine hm.congr ?_
    intro n
    have hza : z ≠ a n := by
      intro h
      exact hz ⟨n, h.symm⟩
    simpa [Φ] using
      (logDeriv_weierstrassFactor_one_div (a := a n) (z := z) (h_nonzero n) hza).symm
  have htend : MultipliableLocallyUniformlyOn Φ (Set.univ : Set ℂ) := by
    simpa [Φ] using multipliableLocallyUniformlyOn_canonicalProduct h_sum h_nonzero
  have hnez : (∏' n, Φ n z) ≠ 0 := by
    simpa [Φ, canonicalProduct] using canonicalProduct_ne_zero h_sum h_nonzero hz
  have hlog :
      logDeriv (∏' n, Φ n ·) z = ∑' n, logDeriv (Φ n) z :=
    logDeriv_tprod_eq_tsum (s := (Set.univ : Set ℂ)) isOpen_univ (by simp)
      hf hd hm' htend hnez
  calc
    logDeriv (canonicalProduct 1 a) z = ∑' n, logDeriv (Φ n) z := by
      simpa [Φ, canonicalProduct] using! hlog
    _ = ∑' n : ℕ, (1 / (z - a n) + 1 / a n) := by
      refine tsum_congr fun n => ?_
      have hza : z ≠ a n := by
        intro h
        exact hz ⟨n, h.symm⟩
      simpa [Φ] using logDeriv_weierstrassFactor_one_div (a := a n) (z := z) (h_nonzero n) hza

end Complex
end
end
end File8

-- Upstream module PrimeNumberTheoremAnd.Mathlib.Analysis.Meromorphic.DivisorSupport
section File9
 

section
open Filter Topology Set

namespace MeromorphicOn

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {U K : Set 𝕜} {z : 𝕜}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

lemma divisor_support_discrete (f : 𝕜 → E) (U : Set 𝕜) :
    IsDiscrete (MeromorphicOn.divisor f U).support := by
  classical
  simpa using
    (Function.locallyFinsuppWithin.discreteSupport (D := MeromorphicOn.divisor f U))

lemma divisor_support_countable [HereditarilyLindelofSpace 𝕜] (f : 𝕜 → E) (U : Set 𝕜) :
    (MeromorphicOn.divisor f U).support.Countable := by
  classical
  have hdisc : IsDiscrete (MeromorphicOn.divisor f U).support := divisor_support_discrete (f := f) U
  have hlin : IsLindelof (MeromorphicOn.divisor f U).support :=
    HereditarilyLindelofSpace.isLindelof _
  exact hlin.countable_of_isDiscrete hdisc

lemma divisor_support_inter_compact_finite (f : 𝕜 → E) {U K : Set 𝕜}
    (hK : IsCompact K) (hKU : K ⊆ U) :
    (K ∩ (MeromorphicOn.divisor f U).support).Finite := by
  classical
  set D : Function.locallyFinsuppWithin U ℤ := MeromorphicOn.divisor f U
  have hloc :
      ∀ x ∈ K, ∃ V : Set 𝕜, V ∈ 𝓝 x ∧ Set.Finite (V ∩ D.support) := by
    intro x hxK
    rcases D.supportLocallyFiniteWithinDomain x (hKU hxK) with ⟨V, hV, hfin⟩
    exact ⟨V, hV, hfin⟩
  choose V hVnhds hVfin using hloc
  rcases hK.elim_nhds_subcover' (U := fun x hx => V x hx) (hU := fun x hx => hVnhds x hx) with
    ⟨t, ht⟩
  have hsub :
      K ∩ D.support ⊆ ⋃ x ∈ t, (V (x : 𝕜) x.2 ∩ D.support) := by
    intro y hy
    rcases hy with ⟨hyK, hyS⟩
    have hycov : y ∈ ⋃ x ∈ t, V (x : 𝕜) x.2 := ht hyK
    rcases Set.mem_iUnion.1 hycov with ⟨x, hycov'⟩
    rcases Set.mem_iUnion.1 hycov' with ⟨hxT, hyV⟩
    refine Set.mem_iUnion.2 ⟨x, Set.mem_iUnion.2 ?_⟩
    exact ⟨hxT, ⟨hyV, hyS⟩⟩
  have hfinU : Set.Finite (⋃ x ∈ t, (V (x : 𝕜) x.2 ∩ D.support)) := by
    classical
    refine (t.finite_toSet).biUnion ?_
    intro x hx
    simpa using (hVfin (x : 𝕜) x.2)
  exact hfinU.subset hsub

lemma exists_ball_inter_divisor_support_eq_singleton {f : 𝕜 → E} (z₀ : 𝕜)
    (hz₀ : z₀ ∈ (MeromorphicOn.divisor f (Set.univ : Set 𝕜)).support) :
    ∃ ε > 0, Metric.ball z₀ ε ∩ (MeromorphicOn.divisor f (Set.univ : Set 𝕜)).support = {z₀} := by
  simpa using
    Metric.exists_ball_inter_eq_singleton_of_mem_discrete
      (hs := MeromorphicOn.divisor_support_discrete (f := f) (U := (Set.univ : Set 𝕜))) hz₀

lemma exists_seq_eq_range_divisor_support [HereditarilyLindelofSpace 𝕜] {f : 𝕜 → E} {U : Set 𝕜}
    (hne : (MeromorphicOn.divisor f U).support.Nonempty) :
    ∃ a : ℕ → 𝕜, (MeromorphicOn.divisor f U).support = Set.range a :=
  by
    classical
    simpa using
      (MeromorphicOn.divisor_support_countable (f := f) (U := U)).exists_eq_range hne

lemma exists_nonzero_seq_divisor_support_diff_zero [HereditarilyLindelofSpace 𝕜]
    {f : 𝕜 → E} {U : Set 𝕜} :
    ∃ a : ℕ → 𝕜,
      (∀ n, a n ≠ 0) ∧ (MeromorphicOn.divisor f U).support \ {0} ⊆ Set.range a := by
  classical
  set s : Set 𝕜 := (MeromorphicOn.divisor f U).support \ {0}
  by_cases hs : s.Nonempty
  · have hs_count : s.Countable := by
      have hsup : (MeromorphicOn.divisor f U).support.Countable :=
        MeromorphicOn.divisor_support_countable (f := f) (U := U)
      refine hsup.mono ?_
      intro x hx
      exact hx.1
    rcases hs_count.exists_eq_range hs with ⟨a, ha⟩
    refine ⟨a, ?_, ?_⟩
    · intro n
      have : a n ∈ s := by
        simp [ha]
      exact fun h0 => this.2 (by simpa [Set.mem_singleton_iff] using h0)
    · simp [ha]
  · refine ⟨fun _ => (1 : 𝕜), ?_, ?_⟩
    · intro _; simp
    · have : s = ∅ := Set.not_nonempty_iff_eq_empty.1 hs
      simp [this]

end MeromorphicOn
end
end File9

-- Upstream module PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.DivisorIndex
section File10
 

section
open Set

namespace Complex.Hadamard

def divisorZeroIndex (f : ℂ → ℂ) (U : Set ℂ) : Type :=
  Σ z : ℂ, Fin (Int.toNat (MeromorphicOn.divisor f U z))

abbrev divisorZeroIndex₀ (f : ℂ → ℂ) (U : Set ℂ) : Type :=
  {p : divisorZeroIndex f U // p.1 ≠ 0}

abbrev divisorZeroIndex₀_val {f : ℂ → ℂ} {U : Set ℂ} (p : divisorZeroIndex₀ f U) : ℂ :=
  p.1.1

@[simp]
lemma divisorZeroIndex₀_val_ne_zero {f : ℂ → ℂ} {U : Set ℂ} (p : divisorZeroIndex₀ f U) :
    divisorZeroIndex₀_val p ≠ 0 := p.2

@[simp]
lemma divisorZeroIndex₀_val_mem_divisor_support {f : ℂ → ℂ} {U : Set ℂ}
    (p : divisorZeroIndex₀ f U) :
    MeromorphicOn.divisor f U (divisorZeroIndex₀_val p) ≠ 0 := by
  have hn :
      Int.toNat (MeromorphicOn.divisor f U (divisorZeroIndex₀_val p)) ≠ 0 := by
    intro h0
    have q0 : Fin 0 := by
      simpa [divisorZeroIndex₀_val, h0] using p.1.2
    exact Fin.elim0 q0
  intro hdiv
  have : Int.toNat (MeromorphicOn.divisor f U (divisorZeroIndex₀_val p)) = 0 := by
    simp [hdiv]
  exact hn this

lemma divisorZeroIndex₀_val_mem_divisor_support' {f : ℂ → ℂ} {U : Set ℂ}
    (p : divisorZeroIndex₀ f U) :
    divisorZeroIndex₀_val p ∈ (MeromorphicOn.divisor f U).support := by
  simp [Function.mem_support]

lemma exists_ball_inter_divisor_support_eq_singleton_of_index
    {f : ℂ → ℂ} (p : divisorZeroIndex₀ f (Set.univ : Set ℂ)) :
    ∃ ε > 0,
      Metric.ball (divisorZeroIndex₀_val p) ε ∩
          (MeromorphicOn.divisor f (Set.univ : Set ℂ)).support =
        {divisorZeroIndex₀_val p} := by
  simpa using
    Metric.exists_ball_inter_eq_singleton_of_mem_discrete
      (hs := MeromorphicOn.divisor_support_discrete (f := f) (U := (Set.univ : Set ℂ)))
      (divisorZeroIndex₀_val_mem_divisor_support' (p := p))

noncomputable def divisorCanonicalProduct (m : ℕ) (f : ℂ → ℂ) (U : Set ℂ) (z : ℂ) : ℂ :=
  ∏' p : divisorZeroIndex₀ f U, weierstrassFactor m (z / divisorZeroIndex₀_val p)

theorem divisorCanonicalProduct_eq_tprod_of_equiv
    {ι : Type*} (m : ℕ) (f : ℂ → ℂ) (U : Set ℂ)
    (e : ι ≃ divisorZeroIndex₀ f U) (z : ℂ) :
    divisorCanonicalProduct m f U z =
      ∏' i : ι, weierstrassFactor m (z / divisorZeroIndex₀_val (e i)) := by
  simpa [divisorCanonicalProduct] using
    (e.tprod_eq (fun p : divisorZeroIndex₀ f U =>
      weierstrassFactor m (z / divisorZeroIndex₀_val p))).symm

theorem divisorCanonicalProduct_eq_canonicalProduct_of_equiv
    (m : ℕ) (f : ℂ → ℂ) (U : Set ℂ) (e : ℕ ≃ divisorZeroIndex₀ f U) (z : ℂ) :
    divisorCanonicalProduct m f U z =
      Complex.canonicalProduct m (fun n : ℕ => divisorZeroIndex₀_val (e n)) z := by
  simpa [Complex.canonicalProduct_def] using
    divisorCanonicalProduct_eq_tprod_of_equiv (m := m) (f := f) (U := U) e z

@[simp]
lemma divisorCanonicalProduct_zero (m : ℕ) (f : ℂ → ℂ) (U : Set ℂ) :
    divisorCanonicalProduct m f U 0 = 1 := by
  simp [divisorCanonicalProduct]

lemma divisorCanonicalProduct_ne_zero_at_zero (m : ℕ) (f : ℂ → ℂ) (U : Set ℂ) :
    divisorCanonicalProduct m f U 0 ≠ 0 := by
  simp [divisorCanonicalProduct_zero]

end Complex.Hadamard
end
end File10

-- Upstream module PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.LocallyUniformLimit
section File11
 

section
namespace Complex

section UniformMul

theorem tendstoUniformlyOn_mul_left_bounded {ι : Type*} {p : Filter ι} {K : Set ℂ}
    {F : ι → ℂ → ℂ} {f : ℂ → ℂ} {h : ℂ → ℂ}
    (hF : TendstoUniformlyOn F f p K) (hh : ∃ C, ∀ z ∈ K, ‖h z‖ ≤ C) :
    TendstoUniformlyOn (fun n z => h z * F n z) (fun z => h z * f z) p K := by
  intro u hu
  rcases Metric.mem_uniformity_dist.1 hu with ⟨ε, hεpos, hεu⟩
  rcases hh with ⟨C, hC⟩
  set C' : ℝ := max C 1
  have hC'pos : 0 < C' := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_right _ _)
  have hC' : ∀ z ∈ K, ‖h z‖ ≤ C' := fun z hz => le_trans (hC z hz) (le_max_left _ _)
  have hv : {p : ℂ × ℂ | dist p.1 p.2 < ε / C'} ∈ uniformity ℂ :=
    Metric.mem_uniformity_dist.2 ⟨ε / C', div_pos hεpos hC'pos, fun _ _ hab => hab⟩
  have hF' : ∀ᶠ n in p, ∀ z : ℂ, z ∈ K → dist (f z) (F n z) < ε / C' := hF _ hv
  filter_upwards [hF'] with n hn z hzK
  have hn' : ‖f z - F n z‖ < ε / C' := by simpa [dist_eq_norm] using hn z hzK
  have hle : ‖h z‖ * ‖f z - F n z‖ ≤ C' * ‖f z - F n z‖ :=
    mul_le_mul_of_nonneg_right (hC' z hzK) (norm_nonneg _)
  have hlt : C' * ‖f z - F n z‖ < C' * (ε / C') := mul_lt_mul_of_pos_left hn' hC'pos
  have hnorm :
      ‖h z * f z - h z * F n z‖ = ‖h z‖ * ‖f z - F n z‖ := by
    calc
      ‖h z * f z - h z * F n z‖ = ‖h z * (f z - F n z)‖ := by simp [mul_sub]
      _ = ‖h z‖ * ‖f z - F n z‖ := by simp
  have hdist : dist (h z * f z) (h z * F n z) < ε := by
    rw [dist_eq_norm, hnorm]
    have hlt' : ‖h z‖ * ‖f z - F n z‖ < ε := by
      calc
        ‖h z‖ * ‖f z - F n z‖ ≤ C' * ‖f z - F n z‖ := hle
        _ < C' * (ε / C') := hlt
        _ = ε := by field_simp [hC'pos.ne']
    exact hlt'
  exact hεu hdist

end UniformMul

end Complex
end
end File11

-- Upstream module PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.DivisorConvergence
section File12
 

section
open Filter Function Complex Finset Topology
open scoped Topology BigOperators
open Set

namespace Complex.Hadamard

lemma finite_divisorZeroIndex₀_subtype_norm_le {f : ℂ → ℂ} {U : Set ℂ} (B : ℝ)
    (hBU : Metric.closedBall (0 : ℂ) B ⊆ U) :
    Finite {p : divisorZeroIndex₀ f U // ‖divisorZeroIndex₀_val p‖ ≤ B} := by
  set D : Function.locallyFinsuppWithin U ℤ := MeromorphicOn.divisor f U
  have hK : IsCompact (Metric.closedBall (0 : ℂ) B) := isCompact_closedBall _ _
  have hpts0 : ((Metric.closedBall (0 : ℂ) B) ∩ D.support).Finite :=
    MeromorphicOn.divisor_support_inter_compact_finite (f := f) (U := U)
      (K := Metric.closedBall (0 : ℂ) B) hK hBU
  set pts : Set ℂ := ((Metric.closedBall (0 : ℂ) B) ∩ D.support) \ {0}
  have hpts : pts.Finite := hpts0.sdiff
  let : Fintype pts := hpts.fintype
  let T : Type := Σ z : pts, Fin (Int.toNat (D z.1))
  have : Finite T := by infer_instance
  let F :
      {p : divisorZeroIndex₀ f U // ‖divisorZeroIndex₀_val p‖ ≤ B} → T := fun p =>
    ⟨⟨divisorZeroIndex₀_val p.1, by
        have hball : divisorZeroIndex₀_val p.1 ∈ Metric.closedBall (0 : ℂ) B := by
          simpa [Metric.mem_closedBall, dist_zero_right] using p.2
        have hsupport : divisorZeroIndex₀_val p.1 ∈ D.support := by
          have hne_toNat :
              Int.toNat (MeromorphicOn.divisor f U (divisorZeroIndex₀_val p.1)) ≠ 0 := by
            intro h0
            have hpfin :
                Fin (Int.toNat (MeromorphicOn.divisor f U (divisorZeroIndex₀_val p.1))) := by
              simpa [D] using p.1.1.2
            have : Fin 0 := by simpa [h0] using hpfin
            exact Fin.elim0 this
          have hne_D : D (divisorZeroIndex₀_val p.1) ≠ 0 := by
            intro hD0
            apply hne_toNat
            simp [D, hD0]
          simp [D, Function.locallyFinsuppWithin.support, Function.support]
        have hne0 : divisorZeroIndex₀_val p.1 ≠ 0 := divisorZeroIndex₀_val_ne_zero p.1
        exact ⟨⟨hball, hsupport⟩, by simp [Set.mem_singleton_iff]⟩⟩,
      p.1.1.2⟩
  refine Finite.of_injective F ?_
  intro p q hpq
  apply Subtype.ext
  apply Subtype.ext
  have h' := (Sigma.mk.inj_iff.1 hpq)
  have hz : divisorZeroIndex₀_val p.1 = divisorZeroIndex₀_val q.1 := congrArg Subtype.val h'.1
  apply (Sigma.mk.inj_iff).2
  refine ⟨hz, ?_⟩
  exact h'.2

lemma divisorZeroIndex₀_norm_le_finite {f : ℂ → ℂ} {U : Set ℂ} (B : ℝ)
    (hBU : Metric.closedBall (0 : ℂ) B ⊆ U) :
    ({p : divisorZeroIndex₀ f U | ‖divisorZeroIndex₀_val p‖ ≤ B} : Set _).Finite := by
  let s : Set (divisorZeroIndex₀ f U) := {p | ‖divisorZeroIndex₀_val p‖ ≤ B}
  have : Finite (↥s) :=
    finite_divisorZeroIndex₀_subtype_norm_le (f := f) (U := U) B hBU
  exact Set.toFinite s

lemma norm_div_le_half_of_norm_le_of_two_mul_lt {z a : ℂ} {R : ℝ}
    (hR : 0 < R) (hz : ‖z‖ ≤ R) (ha : (2 * R : ℝ) < ‖a‖) :
    ‖z / a‖ ≤ (1 / 2 : ℝ) := by
  have h2R_pos : 0 < (2 * R : ℝ) := by nlinarith [hR]
  have hinv : ‖a‖⁻¹ < (2 * R)⁻¹ := by
    simpa [one_div] using one_div_lt_one_div_of_lt h2R_pos ha
  have hmul_le : ‖z‖ * ‖a‖⁻¹ ≤ R * ‖a‖⁻¹ :=
    mul_le_mul_of_nonneg_right hz (inv_nonneg.2 (norm_nonneg a))
  have hmul_lt : R * ‖a‖⁻¹ < R * (2 * R)⁻¹ :=
    mul_lt_mul_of_pos_left hinv hR
  have hRhalf : R * (2 * R)⁻¹ = (1 / 2 : ℝ) := by
    have hRne : (R : ℝ) ≠ 0 := hR.ne'
    rw [show R * (2 * R)⁻¹ = R / (2 * R) by simp [div_eq_mul_inv]]
    field_simp [hRne]
  have hnorm : ‖z / a‖ = ‖z‖ * ‖a‖⁻¹ := by
    simp [div_eq_mul_inv]
  exact le_of_lt <| by
    calc
      ‖z / a‖ = ‖z‖ * ‖a‖⁻¹ := hnorm
      _ ≤ R * ‖a‖⁻¹ := hmul_le
      _ < R * (2 * R)⁻¹ := hmul_lt
      _ = (1 / 2 : ℝ) := hRhalf

theorem summable_logDerivTerms_divisorZeroIndex₀_of_summable_inv_sq
    {f : ℂ → ℂ} {z : ℂ}
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (2 : ℕ)))
    (hz : ∀ p : divisorZeroIndex₀ f (Set.univ : Set ℂ), z ≠ divisorZeroIndex₀_val p) :
    Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      1 / (z - divisorZeroIndex₀_val p) + 1 / divisorZeroIndex₀_val p) := by
  let R : ℝ := max ‖z‖ 1
  have hRpos : 0 < R := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_right _ _)
  have hzle : ‖z‖ ≤ R := le_max_left _ _
  let u : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ :=
    fun p => (2 * R) * (‖divisorZeroIndex₀_val p‖⁻¹ ^ (2 : ℕ))
  have hu : Summable u := h_sum.mul_left (2 * R)
  refine hu.of_norm_bounded_eventually ?_
  have h_big :
      ∀ᶠ p : divisorZeroIndex₀ f (Set.univ : Set ℂ) in Filter.cofinite,
        (2 * R : ℝ) < ‖divisorZeroIndex₀_val p‖ := by
    have hfin :
        ({p : divisorZeroIndex₀ f (Set.univ : Set ℂ) | ‖divisorZeroIndex₀_val p‖ ≤
          2 * R} : Set _).Finite := by
      have : Metric.closedBall (0 : ℂ) (2 * R) ⊆ (Set.univ : Set ℂ) := by simp
      exact divisorZeroIndex₀_norm_le_finite
        (f := f) (U := (Set.univ : Set ℂ)) (B := 2 * R) this
    have := hfin.eventually_cofinite_notMem
    filter_upwards [this] with p hp
    have : ¬ ‖divisorZeroIndex₀_val p‖ ≤ 2 * R := by simpa using hp
    exact lt_of_not_ge this
  filter_upwards [h_big] with p hp
  let a : ℂ := divisorZeroIndex₀_val p
  have ha0 : a ≠ 0 := divisorZeroIndex₀_val_ne_zero p
  have hza0 : z - a ≠ 0 := sub_ne_zero.mpr (hz p)
  have hterm : 1 / (z - a) + 1 / a = z / (a * (z - a)) := by
    field_simp [ha0, hza0]
    ring
  have htri : ‖a‖ ≤ ‖z‖ + ‖z - a‖ := by
    have hraw : ‖a‖ ≤ ‖z‖ + ‖a - z‖ := by
      have h := norm_add_le z (a - z)
      simpa [a, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h
    simpa [norm_sub_rev] using hraw
  have hza_lower : ‖a‖ / 2 ≤ ‖z - a‖ := by
    nlinarith [htri, hzle, hp]
  have hnorm : ‖1 / (z - a) + 1 / a‖ ≤ (2 * R) * (‖a‖⁻¹ ^ (2 : ℕ)) := by
    rw [hterm, norm_div, norm_mul]
    have ha_norm_pos : 0 < ‖a‖ := norm_pos_iff.mpr ha0
    have hza_norm_pos : 0 < ‖z - a‖ := norm_pos_iff.mpr hza0
    rw [div_eq_mul_inv]
    calc
      ‖z‖ * (‖a‖ * ‖z - a‖)⁻¹
          = ‖z‖ * ‖a‖⁻¹ * ‖z - a‖⁻¹ := by
              field_simp [ha_norm_pos.ne', hza_norm_pos.ne']
      _ ≤ R * ‖a‖⁻¹ * ‖z - a‖⁻¹ := by
              gcongr
      _ ≤ R * ‖a‖⁻¹ * (2 * ‖a‖⁻¹) := by
              gcongr
              have hhalf_pos : 0 < ‖a‖ / 2 := by positivity
              have hinv : ‖z - a‖⁻¹ ≤ (‖a‖ / 2)⁻¹ := by
                simpa [one_div] using one_div_le_one_div_of_le hhalf_pos hza_lower
              have hhalf_inv : (‖a‖ / 2)⁻¹ = 2 * ‖a‖⁻¹ := by field_simp [ha_norm_pos.ne']
              simpa [hhalf_inv] using hinv
      _ = (2 * R) * (‖a‖⁻¹ ^ (2 : ℕ)) := by ring
  simpa [u, a] using hnorm

theorem hasProdUniformlyOn_divisorCanonicalProduct_univ
    (m : ℕ) (f : ℂ → ℂ) {K : Set ℂ} (hK : IsCompact K)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1))) :
    HasProdUniformlyOn
      (fun (p : divisorZeroIndex₀ f (Set.univ : Set ℂ)) (z : ℂ) =>
        weierstrassFactor m (z / divisorZeroIndex₀_val p))
      (divisorCanonicalProduct m f (Set.univ : Set ℂ)) K := by
  rcases (isBounded_iff_forall_norm_le.1 hK.isBounded) with ⟨R0, hR0⟩
  set R : ℝ := max R0 1
  have hRpos : 0 < R := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_right _ _)
  have hnormK : ∀ z ∈ K, ‖z‖ ≤ R := fun z hzK => le_trans (hR0 z hzK) (le_max_left _ _)
  let g : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℂ → ℂ :=
    fun p z => weierstrassFactor m (z / divisorZeroIndex₀_val p) - 1
  let u : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ :=
    fun p => (4 * R ^ (m + 1)) * (‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1))
  have hu : Summable u := h_sum.mul_left (4 * R ^ (m + 1))
  have h_big :
      ∀ᶠ p : divisorZeroIndex₀ f (Set.univ : Set ℂ) in Filter.cofinite,
        (2 * R : ℝ) < ‖divisorZeroIndex₀_val p‖ := by
    have hfin :
        ({p : divisorZeroIndex₀ f (Set.univ : Set ℂ) | ‖divisorZeroIndex₀_val p‖ ≤ 2 * R} :
            Set _).Finite := by
      have : Metric.closedBall (0 : ℂ) (2 * R) ⊆ (Set.univ : Set ℂ) := by simp
      exact divisorZeroIndex₀_norm_le_finite (f := f) (U := (Set.univ : Set ℂ)) (B := 2 * R) this
    have := hfin.eventually_cofinite_notMem
    filter_upwards [this] with p hp
    have : ¬ ‖divisorZeroIndex₀_val p‖ ≤ 2 * R := by simpa using hp
    exact lt_of_not_ge this
  have hBound :
      ∀ᶠ p in Filter.cofinite, ∀ z ∈ K, ‖g p z‖ ≤ u p := by
    filter_upwards [h_big] with p hp z hzK
    have hzle : ‖z‖ ≤ R := hnormK z hzK
    have hz_div : ‖z / divisorZeroIndex₀_val p‖ ≤ (1 / 2 : ℝ) := by
      exact norm_div_le_half_of_norm_le_of_two_mul_lt hRpos hzle hp
    have hE :
        ‖weierstrassFactor m (z / divisorZeroIndex₀_val p) - 1‖ ≤
          4 * ‖z / divisorZeroIndex₀_val p‖ ^ (m + 1) :=
      weierstrassFactor_sub_one_pow_bound (m := m) (z := z / divisorZeroIndex₀_val p) hz_div
    have hz_pow :
        ‖z / divisorZeroIndex₀_val p‖ ^ (m + 1) ≤
          (R ^ (m + 1)) * (‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1)) := by
      have : ‖z / divisorZeroIndex₀_val p‖ = ‖z‖ * ‖divisorZeroIndex₀_val p‖⁻¹ := by
        simp [div_eq_mul_inv]
      rw [this]
      have : (‖z‖ * ‖divisorZeroIndex₀_val p‖⁻¹) ^ (m + 1) =
          ‖z‖ ^ (m + 1) * (‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1)) := by
        simp [mul_pow]
      rw [this]
      have hzle_pow : ‖z‖ ^ (m + 1) ≤ R ^ (m + 1) :=
        pow_le_pow_left₀ (norm_nonneg z) hzle (m + 1)
      gcongr
    dsimp [g, u]
    nlinarith [hE, hz_pow]
  have hcts : ∀ p, ContinuousOn (g p) K := by
    intro p
    have hcontE : Continuous (fun z : ℂ => weierstrassFactor m z) :=
      (differentiable_weierstrassFactor m).continuous
    have hdiv : Continuous fun z : ℂ => z / divisorZeroIndex₀_val p := by
      simpa [div_eq_mul_inv] using! (continuous_id.mul continuous_const)
    have hcont : Continuous fun z : ℂ => weierstrassFactor m (z / divisorZeroIndex₀_val p) :=
      hcontE.comp hdiv
    simpa only [g] using hcont.continuousOn.fun_sub continuous_const.continuousOn
  have hprod :
      HasProdUniformlyOn (fun p z ↦ 1 + g p z) (fun z ↦ ∏' p, (1 + g p z)) K := by
    simpa using
      Summable.hasProdUniformlyOn_one_add (f := g) (u := u) (K := K) hK hu hBound hcts
  simpa [g, divisorCanonicalProduct, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    using! hprod

theorem hasProdLocallyUniformlyOn_divisorCanonicalProduct_univ
    (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1))) :
    HasProdLocallyUniformlyOn
      (fun (p : divisorZeroIndex₀ f (Set.univ : Set ℂ)) (z : ℂ) =>
        weierstrassFactor m (z / divisorZeroIndex₀_val p))
      (divisorCanonicalProduct m f (Set.univ : Set ℂ))
      (Set.univ : Set ℂ) := by
  refine hasProdLocallyUniformlyOn_of_forall_compact
      (f := fun p z => weierstrassFactor m (z / divisorZeroIndex₀_val p))
      (g := divisorCanonicalProduct m f (Set.univ : Set ℂ))
      (s := (Set.univ : Set ℂ)) isOpen_univ ?_
  intro K hKU hK
  simpa using
    (hasProdUniformlyOn_divisorCanonicalProduct_univ (m := m) (f := f) (K := K) hK h_sum)

theorem differentiableOn_divisorCanonicalProduct_univ
    (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1))) :
    DifferentiableOn ℂ (divisorCanonicalProduct m f (Set.univ : Set ℂ)) (Set.univ : Set ℂ) := by
  have hloc :
      TendstoLocallyUniformlyOn
        (fun (s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ))) (z : ℂ) =>
          ∏ p ∈ s, weierstrassFactor m (z / divisorZeroIndex₀_val p))
        (divisorCanonicalProduct m f (Set.univ : Set ℂ))
        Filter.atTop (Set.univ : Set ℂ) := by
    simpa [HasProdLocallyUniformlyOn] using
      (hasProdLocallyUniformlyOn_divisorCanonicalProduct_univ (m := m) (f := f) h_sum)
  have hF :
      ∀ᶠ s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) in Filter.atTop,
        DifferentiableOn ℂ
          (fun z : ℂ => ∏ p ∈ s, weierstrassFactor m (z / divisorZeroIndex₀_val p))
          (Set.univ : Set ℂ) := by
    refine Filter.Eventually.of_forall ?_
    intro s
    have hdiff :
        Differentiable ℂ
          (fun z : ℂ => ∏ p ∈ s, weierstrassFactor m (z / divisorZeroIndex₀_val p)) := by
      let F : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℂ → ℂ :=
        fun p z => weierstrassFactor m (z / divisorZeroIndex₀_val p)
      have hF' : ∀ p ∈ s, Differentiable ℂ (F p) := by
        intro p hp
        have hdiv : Differentiable ℂ (fun z : ℂ => z / divisorZeroIndex₀_val p) := by
          have : Differentiable ℂ (fun z : ℂ => z * ((divisorZeroIndex₀_val p)⁻¹)) :=
            (differentiable_id : Differentiable ℂ (fun z : ℂ => z)).mul_const
              ((divisorZeroIndex₀_val p)⁻¹)
          simp [div_eq_mul_inv]
        exact (differentiable_weierstrassFactor m).comp hdiv
      simpa [F] using (Differentiable.fun_finsetProd (𝕜 := ℂ) (f := F) (u := s) hF')
    simpa using hdiff.differentiableOn
  have : (Filter.atTop : Filter (Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)))).NeBot :=
    Filter.atTop_neBot
  exact hloc.differentiableOn hF isOpen_univ

theorem differentiableAt_divisorCanonicalProduct_univ
    (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1))) (z : ℂ) :
    DifferentiableAt ℂ (divisorCanonicalProduct m f (Set.univ : Set ℂ)) z :=
  ((differentiableOn_divisorCanonicalProduct_univ m f h_sum) z (by simp)).differentiableAt
    (by simp)

theorem logDeriv_divisorCanonicalProduct_one_eq_tsum
    {f : ℂ → ℂ} {z : ℂ}
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (2 : ℕ)))
    (hz : ∀ p : divisorZeroIndex₀ f (Set.univ : Set ℂ), z ≠ divisorZeroIndex₀_val p)
    (hprod_ne : divisorCanonicalProduct 1 f (Set.univ : Set ℂ) z ≠ 0) :
    logDeriv (divisorCanonicalProduct 1 f (Set.univ : Set ℂ)) z =
      ∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ),
        (1 / (z - divisorZeroIndex₀_val p) + 1 / divisorZeroIndex₀_val p) := by
  let Φ : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℂ → ℂ :=
    fun p w => weierstrassFactor 1 (w / divisorZeroIndex₀_val p)
  have hf : ∀ p, Φ p z ≠ 0 := by
    intro p
    have hp0 : divisorZeroIndex₀_val p ≠ 0 := divisorZeroIndex₀_val_ne_zero p
    refine weierstrassFactor_ne_zero_of_ne_one 1 ?_
    intro h
    exact hz p ((div_eq_one_iff_eq hp0).1 h)
  have hd : ∀ p, DifferentiableOn ℂ (Φ p) (Set.univ : Set ℂ) := by
    intro p
    have hdiv : Differentiable ℂ (fun w : ℂ => w / divisorZeroIndex₀_val p) := by
      have : Differentiable ℂ (fun w : ℂ => w * ((divisorZeroIndex₀_val p)⁻¹)) :=
        (differentiable_id : Differentiable ℂ (fun w : ℂ => w)).mul_const
          ((divisorZeroIndex₀_val p)⁻¹)
      simp [div_eq_mul_inv]
    exact ((differentiable_weierstrassFactor 1).comp hdiv).differentiableOn
  have hm' : Summable fun p => logDeriv (Φ p) z := by
    have hm :
        Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
          1 / (z - divisorZeroIndex₀_val p) + 1 / divisorZeroIndex₀_val p) :=
      summable_logDerivTerms_divisorZeroIndex₀_of_summable_inv_sq h_sum hz
    refine hm.congr ?_
    intro p
    have hp0 : divisorZeroIndex₀_val p ≠ 0 := divisorZeroIndex₀_val_ne_zero p
    simpa [Φ] using
      (Complex.logDeriv_weierstrassFactor_one_div
        (a := divisorZeroIndex₀_val p) (z := z) hp0 (hz p)).symm
  have htend : MultipliableLocallyUniformlyOn Φ (Set.univ : Set ℂ) := by
    have hprod := hasProdLocallyUniformlyOn_divisorCanonicalProduct_univ
      (m := 1) (f := f) h_sum
    simpa [Φ, divisorCanonicalProduct] using hprod.multipliableLocallyUniformlyOn
  have hnez : (∏' p, Φ p z) ≠ 0 := by
    simpa [Φ, divisorCanonicalProduct] using hprod_ne
  have hlog : logDeriv (∏' p, Φ p ·) z = ∑' p, logDeriv (Φ p) z :=
    logDeriv_tprod_eq_tsum (s := (Set.univ : Set ℂ)) isOpen_univ (by simp)
      hf hd hm' htend hnez
  calc
    logDeriv (divisorCanonicalProduct 1 f (Set.univ : Set ℂ)) z
        = ∑' p, logDeriv (Φ p) z := by
          simpa [Φ, divisorCanonicalProduct] using! hlog
    _ = ∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ),
          (1 / (z - divisorZeroIndex₀_val p) + 1 / divisorZeroIndex₀_val p) := by
          refine tsum_congr fun p => ?_
          have hp0 : divisorZeroIndex₀_val p ≠ 0 := divisorZeroIndex₀_val_ne_zero p
          simpa [Φ] using
            Complex.logDeriv_weierstrassFactor_one_div
              (a := divisorZeroIndex₀_val p) (z := z) hp0 (hz p)

end Complex.Hadamard
end
end File12

-- Upstream module PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.DivisorUnits
section File13
 

section
open Set

namespace Complex.Hadamard

lemma divisorZeroIndex₀_val_eq_of_mem_ball
    {f : ℂ → ℂ} {z₀ : ℂ} {ε : ℝ}
    (hball : Metric.ball z₀ ε ∩ (MeromorphicOn.divisor f (Set.univ : Set ℂ)).support = {z₀})
    (p : divisorZeroIndex₀ f (Set.univ : Set ℂ))
    (hp : divisorZeroIndex₀_val p ∈ Metric.ball z₀ ε) :
    divisorZeroIndex₀_val p = z₀ := by
  have hsupp : divisorZeroIndex₀_val p ∈ (MeromorphicOn.divisor f (Set.univ : Set ℂ)).support :=
    divisorZeroIndex₀_val_mem_divisor_support' (p := p)
  have : divisorZeroIndex₀_val p ∈
      Metric.ball z₀ ε ∩ (MeromorphicOn.divisor f (Set.univ : Set ℂ)).support := ⟨hp, hsupp⟩
  simp [hball] at this
  simpa using this

lemma weierstrassFactor_div_ne_zero_on_ball_of_val_ne
    (m : ℕ) {f : ℂ → ℂ} {z₀ : ℂ} {ε : ℝ}
    (hball : Metric.ball z₀ ε ∩ (MeromorphicOn.divisor f (Set.univ : Set ℂ)).support = {z₀})
    (p : divisorZeroIndex₀ f (Set.univ : Set ℂ)) (hp : divisorZeroIndex₀_val p ≠ z₀) :
    ∀ z ∈ Metric.ball z₀ ε, weierstrassFactor m (z / divisorZeroIndex₀_val p) ≠ 0 := by
  intro z hzball h0
  have hz_eq : z = divisorZeroIndex₀_val p := by
    have hdiv1 : z / divisorZeroIndex₀_val p = 1 := by
      simpa [weierstrassFactor_eq_zero_iff (m := m)] using h0
    have ha : divisorZeroIndex₀_val p ≠ 0 := divisorZeroIndex₀_val_ne_zero p
    exact (div_eq_one_iff_eq ha).1 hdiv1
  have hz_support : z ∈ (MeromorphicOn.divisor f (Set.univ : Set ℂ)).support := by
    simp [hz_eq]
  have hz0 : z = z₀ := by
    have : z ∈ Metric.ball z₀ ε ∩ (MeromorphicOn.divisor f (Set.univ : Set ℂ)).support :=
      ⟨hzball, hz_support⟩
    simp [hball] at this
    simpa using this
  have : divisorZeroIndex₀_val p = z₀ := by
    calc
      divisorZeroIndex₀_val p = z := by simp [hz_eq]
      _ = z₀ := hz0
  exact hp this

lemma weierstrassFactor_div_ne_zero_on_ball_punctured
    (m : ℕ) {f : ℂ → ℂ} {z₀ : ℂ} {ε : ℝ}
    (hball : Metric.ball z₀ ε ∩ (MeromorphicOn.divisor f (Set.univ : Set ℂ)).support = {z₀}) :
    ∀ z ∈ Metric.ball z₀ ε, z ≠ z₀ →
      ∀ p : divisorZeroIndex₀ f (Set.univ : Set ℂ),
        weierstrassFactor m (z / divisorZeroIndex₀_val p) ≠ 0 := by
  intro z hz hz0 p
  by_cases hp : divisorZeroIndex₀_val p = z₀
  · have hz1 : z / divisorZeroIndex₀_val p ≠ (1 : ℂ) := by
      have ha : divisorZeroIndex₀_val p ≠ 0 := divisorZeroIndex₀_val_ne_zero p
      simpa [hp] using (mt (div_eq_one_iff_eq ha).1 (by simpa [hp] using hz0))
    exact Complex.weierstrassFactor_ne_zero_of_ne_one (m := m) hz1
  · exact weierstrassFactor_div_ne_zero_on_ball_of_val_ne (m := m) (f := f) (z₀ := z₀)
        (ε := ε) hball p (by simpa using hp) z hz

end Complex.Hadamard
end
end File13

-- Upstream module PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.DivisorFiber
section File14
 

section
noncomputable section

open Set
open scoped Topology BigOperators

namespace Complex.Hadamard

lemma divisor_univ_eq_analyticOrderNatAt_int {f : ℂ → ℂ} (hf : Differentiable ℂ f) (z : ℂ) :
    MeromorphicOn.divisor f (Set.univ : Set ℂ) z = (analyticOrderNatAt f z : ℤ) := by
  have hmero : MeromorphicOn f (Set.univ : Set ℂ) := by
    intro w hw
    exact (Differentiable.analyticAt (f := f) hf w).meromorphicAt
  simp only
    [MeromorphicOn.divisor_apply hmero (by simp : z ∈ (Set.univ : Set ℂ)), analyticOrderNatAt]
  have han : AnalyticAt ℂ f z := Differentiable.analyticAt (f := f) hf z
  cases h : analyticOrderAt f z with
  | top =>
      simp [han.meromorphicOrderAt_eq, h]
  | coe n =>
      simp [han.meromorphicOrderAt_eq, h]

theorem divisorZeroIndex₀_fiber_finite (f : ℂ → ℂ) (z₀ : ℂ) :
    ({p : divisorZeroIndex₀ f (Set.univ : Set ℂ) | divisorZeroIndex₀_val p = z₀} :
      Set _).Finite := by
  have hsub :
      ({p : divisorZeroIndex₀ f (Set.univ : Set ℂ) | divisorZeroIndex₀_val p = z₀} : Set _)
        ⊆ ({p : divisorZeroIndex₀ f (Set.univ : Set ℂ) | ‖divisorZeroIndex₀_val p‖ ≤ ‖z₀‖} :
          Set _) := by
    intro p hp
    have : divisorZeroIndex₀_val p = z₀ := hp
    simp [this]
  have hfin :
      ({p : divisorZeroIndex₀ f (Set.univ : Set ℂ) | ‖divisorZeroIndex₀_val p‖ ≤ ‖z₀‖} :
        Set _).Finite := by
    have : Metric.closedBall (0 : ℂ) ‖z₀‖ ⊆ (Set.univ : Set ℂ) := by simp
    simpa using (divisorZeroIndex₀_norm_le_finite (f := f) (U := (Set.univ : Set ℂ))
      (B := ‖z₀‖) this)
  exact hfin.subset hsub

def divisorZeroIndex₀_fiberFinset (f : ℂ → ℂ) (z₀ : ℂ) :
    Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) :=
  (divisorZeroIndex₀_fiber_finite (f := f) z₀).toFinset

@[simp]
lemma mem_divisorZeroIndex₀_fiberFinset (f : ℂ → ℂ) (z₀ : ℂ)
    (p : divisorZeroIndex₀ f (Set.univ : Set ℂ)) :
    p ∈ divisorZeroIndex₀_fiberFinset (f := f) z₀ ↔ divisorZeroIndex₀_val p = z₀ := by
  simp [divisorZeroIndex₀_fiberFinset]

theorem eventually_atTop_subset_fiberFinset
    (f : ℂ → ℂ) (z₀ : ℂ) :
    ∀ᶠ s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) in (Filter.atTop : Filter _),
      divisorZeroIndex₀_fiberFinset (f := f) z₀ ⊆ s := by
  refine (Filter.eventually_atTop.2 ?_)
  refine ⟨divisorZeroIndex₀_fiberFinset (f := f) z₀, ?_⟩
  intro s hs
  exact hs

lemma divisorZeroIndex₀_fiberFinset_card_eq_toNat_divisor (f : ℂ → ℂ) {z₀ : ℂ} (hz₀ : z₀ ≠ 0) :
    (divisorZeroIndex₀_fiberFinset (f := f) z₀).card =
      Int.toNat (MeromorphicOn.divisor f (Set.univ : Set ℂ) z₀) := by
  let S : Set (divisorZeroIndex₀ f (Set.univ : Set ℂ)) := {p | divisorZeroIndex₀_val p = z₀}
  have hS : S.Finite := divisorZeroIndex₀_fiber_finite (f := f) z₀
  set n : ℕ := Int.toNat (MeromorphicOn.divisor f (Set.univ : Set ℂ) z₀)
  have hcard : Nat.card S = n := by
    classical
    have : Fintype S := hS.fintype
    
    let e : S ≃ Fin n :=
      { toFun := by
          intro x
          rcases x with ⟨p, hp⟩
          rcases p with ⟨⟨z, q⟩, hz⟩
          have hzEq : z = z₀ := by simpa [divisorZeroIndex₀_val] using! hp
          subst hzEq
          simpa [n] using q
        invFun := by
          intro q
          refine ⟨⟨⟨z₀, ?_⟩, hz₀⟩, ?_⟩
          · simpa [n] using q
          · simp [S, divisorZeroIndex₀_val]
        left_inv := by
          rintro ⟨p, hp⟩
          rcases p with ⟨⟨z, q⟩, hz⟩
          have hzEq : z = z₀ := by simpa [divisorZeroIndex₀_val] using! hp
          subst hzEq
          (ext; rfl)
        right_inv := by
          intro q
          rfl }
    have h := Nat.card_congr (α := S) (β := Fin n) e
    simpa using (h.trans (by simp))
  have hSncard : S.ncard = n := by
    simpa [Nat.card_coe_set_eq] using hcard
  have hto : hS.toFinset = divisorZeroIndex₀_fiberFinset (f := f) z₀ := by
    rfl
  have htoFinset : S.ncard = (divisorZeroIndex₀_fiberFinset (f := f) z₀).card := by
    have h' : S.ncard = hS.toFinset.card := Set.ncard_eq_toFinset_card S hS
    simpa [hto] using h'
  exact htoFinset.symm.trans hSncard

lemma divisorZeroIndex₀_fiberFinset_card_eq_analyticOrderNatAt
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) {z₀ : ℂ} (hz₀ : z₀ ≠ 0) :
    (divisorZeroIndex₀_fiberFinset (f := f) z₀).card = analyticOrderNatAt f z₀ := by
  have hdiv :
      MeromorphicOn.divisor f (Set.univ : Set ℂ) z₀ = (analyticOrderNatAt f z₀ : ℤ) :=
    divisor_univ_eq_analyticOrderNatAt_int (f := f) hf z₀
  have htoNat : Int.toNat (MeromorphicOn.divisor f (Set.univ : Set ℂ) z₀) =
    analyticOrderNatAt f z₀ := by
    simp [hdiv]
  exact (divisorZeroIndex₀_fiberFinset_card_eq_toNat_divisor (f := f) (z₀ := z₀) hz₀).trans htoNat

lemma mem_divisorZeroIndex₀_fiberFinset_of_val_mem_ball
    {f : ℂ → ℂ} {z₀ : ℂ} {ε : ℝ}
    (hball : Metric.ball z₀ ε ∩ (MeromorphicOn.divisor f (Set.univ : Set ℂ)).support = {z₀})
    (p : divisorZeroIndex₀ f (Set.univ : Set ℂ))
    (hp : divisorZeroIndex₀_val p ∈ Metric.ball z₀ ε) :
    p ∈ divisorZeroIndex₀_fiberFinset (f := f) z₀ := by
  have : divisorZeroIndex₀_val p = z₀ :=
    divisorZeroIndex₀_val_eq_of_mem_ball (f := f) (z₀ := z₀) (ε := ε) hball p hp
  exact (mem_divisorZeroIndex₀_fiberFinset (f := f) (z₀ := z₀) p).2 this

lemma mem_divisorZeroIndex₀_fiberFinset_iff_val_mem_ball
    {f : ℂ → ℂ} {z₀ : ℂ} {ε : ℝ}
    (hε : 0 < ε)
    (hball :
      Metric.ball z₀ ε ∩ (MeromorphicOn.divisor f (Set.univ : Set ℂ)).support = {z₀})
    (p : divisorZeroIndex₀ f (Set.univ : Set ℂ)) :
    p ∈ divisorZeroIndex₀_fiberFinset (f := f) z₀ ↔ divisorZeroIndex₀_val p ∈ Metric.ball z₀ ε := by
  constructor
  · intro hp
    have : divisorZeroIndex₀_val p = z₀ :=
      (mem_divisorZeroIndex₀_fiberFinset (f := f) (z₀ := z₀) p).1 hp
    simpa [this] using (Metric.mem_ball_self hε : z₀ ∈ Metric.ball z₀ ε)
  · intro hp
    exact mem_divisorZeroIndex₀_fiberFinset_of_val_mem_ball (f := f) (z₀ := z₀) (ε := ε) hball p hp

lemma not_mem_divisorZeroIndex₀_fiberFinset_iff_val_ne
    {f : ℂ → ℂ} (z₀ : ℂ) (p : divisorZeroIndex₀ f (Set.univ : Set ℂ)) :
    p ∉ divisorZeroIndex₀_fiberFinset (f := f) z₀ ↔ divisorZeroIndex₀_val p ≠ z₀ := by
  simp [mem_divisorZeroIndex₀_fiberFinset]

lemma val_not_mem_ball_of_not_mem_fiberFinset
    {f : ℂ → ℂ} {z₀ : ℂ} {ε : ℝ} (hε : 0 < ε) (hball :
      Metric.ball z₀ ε ∩ (MeromorphicOn.divisor f (Set.univ : Set ℂ)).support = {z₀})
    (p : divisorZeroIndex₀ f (Set.univ : Set ℂ))
    (hp : p ∉ divisorZeroIndex₀_fiberFinset (f := f) z₀) :
    divisorZeroIndex₀_val p ∉ Metric.ball z₀ ε := by
  intro hpball
  exact hp ((mem_divisorZeroIndex₀_fiberFinset_iff_val_mem_ball (f := f)
    (z₀ := z₀) (ε := ε) hε hball p).2 hpball)

lemma weierstrassFactor_div_ne_zero_on_ball_of_not_mem_fiberFinset
    (m : ℕ) {f : ℂ → ℂ} {z₀ : ℂ} {ε : ℝ}
    (hball :
      Metric.ball z₀ ε ∩ (MeromorphicOn.divisor f (Set.univ : Set ℂ)).support = {z₀})
    (p : divisorZeroIndex₀ f (Set.univ : Set ℂ))
    (hp : p ∉ divisorZeroIndex₀_fiberFinset (f := f) z₀) :
    ∀ z ∈ Metric.ball z₀ ε, weierstrassFactor m (z / divisorZeroIndex₀_val p) ≠ 0 := by
  have hp' : divisorZeroIndex₀_val p ≠ z₀ :=
    (not_mem_divisorZeroIndex₀_fiberFinset_iff_val_ne (f := f) z₀ p).1 hp
  exact weierstrassFactor_div_ne_zero_on_ball_of_val_ne (m := m) (f := f) (z₀ := z₀)
    (ε := ε) hball p hp'

end Complex.Hadamard
end
end
end File14

-- Upstream module PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.DivisorComplement
section File15
 

section
open Filter Function Complex Finset Topology
open scoped Topology BigOperators
open Set

namespace Complex.Hadamard

noncomputable def divisorComplementFactor
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ)
    (p : divisorZeroIndex₀ f (Set.univ : Set ℂ)) (z : ℂ) : ℂ := by
  classical
  exact if p ∈ divisorZeroIndex₀_fiberFinset (f := f) z₀ then (1 : ℂ)
    else weierstrassFactor m (z / divisorZeroIndex₀_val p)

@[simp]
theorem divisorComplementFactor_eq_one_of_mem
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ)
    (p : divisorZeroIndex₀ f (Set.univ : Set ℂ)) (z : ℂ)
    (hp : p ∈ divisorZeroIndex₀_fiberFinset (f := f) z₀) :
    divisorComplementFactor m f z₀ p z = 1 := by
  classical
  simp [divisorComplementFactor, hp]

@[simp]
theorem divisorComplementFactor_eq_weierstrassFactor_of_not_mem
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ)
    (p : divisorZeroIndex₀ f (Set.univ : Set ℂ)) (z : ℂ)
    (hp : p ∉ divisorZeroIndex₀_fiberFinset (f := f) z₀) :
    divisorComplementFactor m f z₀ p z =
      weierstrassFactor m (z / divisorZeroIndex₀_val p) := by
  classical
  simp [divisorComplementFactor, hp]

lemma divisorComplementFactor_def
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ)
    (p : divisorZeroIndex₀ f (Set.univ : Set ℂ)) (z : ℂ) :
    divisorComplementFactor m f z₀ p z =
      if divisorZeroIndex₀_val p = z₀ then (1 : ℂ)
      else weierstrassFactor m (z / divisorZeroIndex₀_val p) := by
  classical
  by_cases h : divisorZeroIndex₀_val p = z₀
  · have hp : p ∈ divisorZeroIndex₀_fiberFinset (f := f) z₀ := by
      simpa [mem_divisorZeroIndex₀_fiberFinset] using h
    simp [divisorComplementFactor_eq_one_of_mem, hp, h]
  · have hp : p ∉ divisorZeroIndex₀_fiberFinset (f := f) z₀ := by
      intro hmem
      exact h ((mem_divisorZeroIndex₀_fiberFinset f z₀ p).1 hmem)
    simp [divisorComplementFactor_eq_weierstrassFactor_of_not_mem, hp, h]

noncomputable def divisorPartialProduct (m : ℕ) (f : ℂ → ℂ)
    (s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ))) (z : ℂ) : ℂ :=
  ∏ p ∈ s, weierstrassFactor m (z / divisorZeroIndex₀_val p)

@[simp]
lemma divisorPartialProduct_def (m : ℕ) (f : ℂ → ℂ)
    (s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ))) (z : ℂ) :
    divisorPartialProduct m f s z = ∏ p ∈ s, weierstrassFactor m (z / divisorZeroIndex₀_val p) :=
  rfl

theorem differentiable_weierstrassFactor_divisorZeroIndex₀ (m : ℕ) {f : ℂ → ℂ}
    (p : divisorZeroIndex₀ f (Set.univ : Set ℂ)) :
    Differentiable ℂ (fun z : ℂ => weierstrassFactor m (z / divisorZeroIndex₀_val p)) := by
  have hdiv : Differentiable ℂ (fun z : ℂ => z / divisorZeroIndex₀_val p) := by
    simp [div_eq_mul_inv]
  exact (differentiable_weierstrassFactor m).comp hdiv

theorem differentiable_divisorPartialProduct (m : ℕ) (f : ℂ → ℂ)
    (s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ))) :
    Differentiable ℂ (divisorPartialProduct m f s) := by
  let Φ : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℂ → ℂ :=
    fun p z => weierstrassFactor m (z / divisorZeroIndex₀_val p)
  have hΦ : ∀ p ∈ s, Differentiable ℂ (Φ p) := by
    intro p _hp
    exact differentiable_weierstrassFactor_divisorZeroIndex₀ m p
  simpa [divisorPartialProduct, Φ] using!
    (Differentiable.fun_finsetProd (𝕜 := ℂ) (f := Φ) (u := s) hΦ)

theorem analyticAt_divisorPartialProduct (m : ℕ) (f : ℂ → ℂ)
    (s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ))) (z₀ : ℂ) :
    AnalyticAt ℂ (divisorPartialProduct m f s) z₀ :=
  (differentiable_divisorPartialProduct m f s).analyticAt z₀

noncomputable def divisorComplementPartialProduct
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ)
    (s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ))) (z : ℂ) : ℂ :=
  ∏ p ∈ s, divisorComplementFactor m f z₀ p z

@[simp]
lemma divisorComplementPartialProduct_def
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ)
    (s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ))) (z : ℂ) :
    divisorComplementPartialProduct m f z₀ s z =
      ∏ p ∈ s, if divisorZeroIndex₀_val p = z₀ then (1 : ℂ)
        else weierstrassFactor m (z / divisorZeroIndex₀_val p) := by
  simp [divisorComplementPartialProduct, divisorComplementFactor,
    mem_divisorZeroIndex₀_fiberFinset]

theorem differentiable_divisorComplementPartialProduct
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ)
    (s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ))) :
    Differentiable ℂ (divisorComplementPartialProduct m f z₀ s) := by
  let Φ : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℂ → ℂ :=
    fun p z => divisorComplementFactor m f z₀ p z
  have hΦ : ∀ p ∈ s, Differentiable ℂ (Φ p) := by
    intro p _hp
    by_cases hpF : p ∈ divisorZeroIndex₀_fiberFinset (f := f) z₀
    · have hΦp : Φ p = fun _ => (1 : ℂ) := by
        ext z
        simp only [Φ, divisorComplementFactor_eq_one_of_mem m f z₀ p z hpF]
      rw [hΦp]
      exact differentiable_const (1 : ℂ)
    · have hΦp : Φ p = fun z => weierstrassFactor m (z / divisorZeroIndex₀_val p) := by
        ext z
        simp only [Φ, divisorComplementFactor_eq_weierstrassFactor_of_not_mem m f z₀ p z hpF]
      rw [hΦp]
      exact differentiable_weierstrassFactor_divisorZeroIndex₀ m p
  have hEq : (fun z : ℂ => ∏ p ∈ s, Φ p z) =
      divisorComplementPartialProduct m f z₀ s := by
    ext z
    simp [Φ, divisorComplementPartialProduct]
  have : Differentiable ℂ (fun z : ℂ => ∏ p ∈ s, Φ p z) := by
    simpa using (Differentiable.fun_finsetProd (𝕜 := ℂ) (f := Φ) (u := s) hΦ)
  simpa [hEq] using this

noncomputable def divisorComplementCanonicalProduct
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ) (z : ℂ) : ℂ :=
  ∏' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), divisorComplementFactor m f z₀ p z

theorem hasProdUniformlyOn_divisorComplementCanonicalProduct_univ
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ) {K : Set ℂ} (hK : IsCompact K)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1))) :
    HasProdUniformlyOn (fun (p : divisorZeroIndex₀ f (Set.univ : Set ℂ)) (z : ℂ) =>
        divisorComplementFactor m f z₀ p z) (divisorComplementCanonicalProduct m f z₀)
      K := by
  rcases (isBounded_iff_forall_norm_le.1 hK.isBounded) with ⟨R0, hR0⟩
  set R : ℝ := max R0 1
  have hRpos : 0 < R := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_right _ _)
  have hnormK : ∀ z ∈ K, ‖z‖ ≤ R := fun z hzK => le_trans (hR0 z hzK) (le_max_left _ _)
  let term : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℂ → ℂ := fun p z =>
    divisorComplementFactor m f z₀ p z
  let g : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℂ → ℂ := fun p z => term p z - 1
  let u : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ :=
    fun p => (4 * R ^ (m + 1)) * (‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1))
  have hu : Summable u := h_sum.mul_left (4 * R ^ (m + 1))
  have h_big :
      ∀ᶠ p : divisorZeroIndex₀ f (Set.univ : Set ℂ) in Filter.cofinite,
        (2 * R : ℝ) < ‖divisorZeroIndex₀_val p‖ := by
    have hfin :
        ({p : divisorZeroIndex₀ f (Set.univ : Set ℂ) | ‖divisorZeroIndex₀_val p‖ ≤ 2 * R} :
          Set _).Finite := by
      have : Metric.closedBall (0 : ℂ) (2 * R) ⊆ (Set.univ : Set ℂ) := by simp
      exact divisorZeroIndex₀_norm_le_finite (f := f) (U := (Set.univ : Set ℂ)) (B := 2 * R) this
    have := hfin.eventually_cofinite_notMem
    filter_upwards [this] with p hp
    have : ¬ ‖divisorZeroIndex₀_val p‖ ≤ 2 * R := by simpa using hp
    exact lt_of_not_ge this
  have hBound :
      ∀ᶠ p in Filter.cofinite, ∀ z ∈ K, ‖g p z‖ ≤ u p := by
    filter_upwards [h_big] with p hp z hzK
    by_cases hpF : p ∈ divisorZeroIndex₀_fiberFinset (f := f) z₀
    · have hval : divisorZeroIndex₀_val p = z₀ :=
        (mem_divisorZeroIndex₀_fiberFinset (f := f) (z₀ := z₀) p).1 hpF
      have hu0 : 0 ≤ u p := by
        dsimp [u]
        refine mul_nonneg ?_ ?_
        · nlinarith [pow_nonneg (show 0 ≤ R from le_of_lt hRpos) (m + 1)]
        · exact pow_nonneg (inv_nonneg.2 (norm_nonneg _)) (m + 1)
      simp [g, term, divisorComplementFactor, hval, hu0, sub_eq_add_neg]
    · have hzle : ‖z‖ ≤ R := hnormK z hzK
      have hz_div : ‖z / divisorZeroIndex₀_val p‖ ≤ (1 / 2 : ℝ) := by
        have h2R_pos : 0 < (2 * R : ℝ) := by nlinarith [hRpos]
        have hinv : ‖divisorZeroIndex₀_val p‖⁻¹ < (2 * R)⁻¹ := by
          simpa [one_div] using (one_div_lt_one_div_of_lt h2R_pos hp)
        have hmul_le : ‖z‖ * ‖divisorZeroIndex₀_val p‖⁻¹ ≤ R * ‖divisorZeroIndex₀_val p‖⁻¹ := by
          refine mul_le_mul_of_nonneg_right hzle ?_
          exact inv_nonneg.2 (norm_nonneg _)
        have hmul_lt : R * ‖divisorZeroIndex₀_val p‖⁻¹ < R * (2 * R)⁻¹ :=
          mul_lt_mul_of_pos_left hinv hRpos
        have hlt : ‖z‖ * ‖divisorZeroIndex₀_val p‖⁻¹ < R * (2 * R)⁻¹ :=
          lt_of_le_of_lt hmul_le hmul_lt
        have hRhalf : R * (2 * R)⁻¹ = (1 / 2 : ℝ) := by
          have hRne : (R : ℝ) ≠ 0 := hRpos.ne'
          have : R * (2 * R)⁻¹ = R / (2 * R) := by simp [div_eq_mul_inv]
          rw [this]
          field_simp [hRne]
        have hnorm : ‖z / divisorZeroIndex₀_val p‖ = ‖z‖ * ‖divisorZeroIndex₀_val p‖⁻¹ := by
          simp [div_eq_mul_inv]
        have hzlt : ‖z / divisorZeroIndex₀_val p‖ < (1 / 2 : ℝ) := by
          calc
            ‖z / divisorZeroIndex₀_val p‖ = ‖z‖ * ‖divisorZeroIndex₀_val p‖⁻¹ := hnorm
            _ < R * (2 * R)⁻¹ := hlt
            _ = (1 / 2 : ℝ) := hRhalf
        exact le_of_lt hzlt
      have hE : ‖weierstrassFactor m (z / divisorZeroIndex₀_val p) - 1‖ ≤
            4 * ‖z / divisorZeroIndex₀_val p‖ ^ (m + 1) :=
        weierstrassFactor_sub_one_pow_bound (m := m) (z := z / divisorZeroIndex₀_val p) hz_div
      have hz_pow : ‖z / divisorZeroIndex₀_val p‖ ^ (m + 1) ≤
            (R ^ (m + 1)) * (‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1)) := by
        have : ‖z / divisorZeroIndex₀_val p‖ = ‖z‖ * ‖divisorZeroIndex₀_val p‖⁻¹ := by
          simp [div_eq_mul_inv]
        rw [this]
        have : (‖z‖ * ‖divisorZeroIndex₀_val p‖⁻¹) ^ (m + 1) =
            ‖z‖ ^ (m + 1) * (‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1)) := by
          simp [mul_pow]
        rw [this]
        have hzle_pow : ‖z‖ ^ (m + 1) ≤ R ^ (m + 1) :=
          pow_le_pow_left₀ (norm_nonneg z) hzle (m + 1)
        gcongr
      dsimp [g, term, u]
      simp [divisorComplementFactor, hpF] at *
      nlinarith [hE, hz_pow]
  have hcts : ∀ p, ContinuousOn (g p) K := by
    intro p
    by_cases hpF : p ∈ divisorZeroIndex₀_fiberFinset (f := f) z₀
    · have hval : divisorZeroIndex₀_val p = z₀ :=
        (mem_divisorZeroIndex₀_fiberFinset (f := f) (z₀ := z₀) p).1 hpF
      simpa [g, term, divisorComplementFactor, hval] using
        (continuousOn_const : ContinuousOn (fun _ : ℂ => (0 : ℂ)) K)
    · have hvalne : divisorZeroIndex₀_val p ≠ z₀ :=
        (not_mem_divisorZeroIndex₀_fiberFinset_iff_val_ne (f := f) z₀ p).1 hpF
      have hcontE : Continuous (fun z : ℂ => weierstrassFactor m z) :=
        (differentiable_weierstrassFactor m).continuous
      have hdiv : Continuous fun z : ℂ => z / divisorZeroIndex₀_val p := by
        simpa [div_eq_mul_inv] using! (continuous_id.mul continuous_const)
      have hcont : Continuous fun z : ℂ => weierstrassFactor m (z / divisorZeroIndex₀_val p) :=
        hcontE.comp hdiv
      have : ContinuousOn (fun z : ℂ => weierstrassFactor m (z / divisorZeroIndex₀_val p) - 1) K :=
        (hcont.continuousOn.sub continuous_const.continuousOn)
      simpa [g, term, divisorComplementFactor, mem_divisorZeroIndex₀_fiberFinset, hvalne] using this
  have hprod :
      HasProdUniformlyOn (fun p z ↦ 1 + g p z) (fun z ↦ ∏' p, (1 + g p z)) K := by
    simpa using
      Summable.hasProdUniformlyOn_one_add (f := g) (u := u) (K := K) hK hu hBound hcts
  have hterm :
      HasProdUniformlyOn (fun p z ↦ term p z) (fun z ↦ ∏' p, term p z) K := by
    simpa [g, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hprod
  refine hterm.congr_right ?_
  intro z hz
  simp [term, divisorComplementCanonicalProduct, divisorComplementFactor]

theorem hasProdLocallyUniformlyOn_divisorComplementCanonicalProduct_univ
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1))) :
    HasProdLocallyUniformlyOn
      (fun (p : divisorZeroIndex₀ f (Set.univ : Set ℂ)) (z : ℂ) =>
        divisorComplementFactor m f z₀ p z)
      (divisorComplementCanonicalProduct m f z₀)
      (Set.univ : Set ℂ) := by
  refine hasProdLocallyUniformlyOn_of_forall_compact
      (f := fun p z => divisorComplementFactor m f z₀ p z)
      (g := divisorComplementCanonicalProduct m f z₀) (s := (Set.univ : Set ℂ))
      isOpen_univ ?_
  intro K hKU hK
  simpa using
    (hasProdUniformlyOn_divisorComplementCanonicalProduct_univ (m := m) (f := f) (z₀ := z₀)
      (K := K) hK h_sum)

theorem tendstoLocallyUniformlyOn_divisorComplementPartialProduct_univ
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1))) :
    TendstoLocallyUniformlyOn
      (fun s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) =>
        divisorComplementPartialProduct m f z₀ s)
      (divisorComplementCanonicalProduct m f z₀)
      Filter.atTop
      (Set.univ : Set ℂ) := by
  have hprod :
      HasProdLocallyUniformlyOn
        (fun (p : divisorZeroIndex₀ f (Set.univ : Set ℂ)) (z : ℂ) =>
          divisorComplementFactor m f z₀ p z)
        (divisorComplementCanonicalProduct m f z₀)
        (Set.univ : Set ℂ) :=
    hasProdLocallyUniformlyOn_divisorComplementCanonicalProduct_univ (m := m) (f := f)
      (z₀ := z₀) h_sum
  have h :
      TendstoLocallyUniformlyOn
        (fun (s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ))) (z : ℂ) =>
          ∏ p ∈ s,
            if divisorZeroIndex₀_val p = z₀ then (1 : ℂ)
            else weierstrassFactor m (z / divisorZeroIndex₀_val p))
        (divisorComplementCanonicalProduct m f z₀)
        Filter.atTop
        (Set.univ : Set ℂ) := by
    simpa [HasProdLocallyUniformlyOn, divisorComplementFactor, mem_divisorZeroIndex₀_fiberFinset]
      using hprod
  refine h.congr (G := fun s z => divisorComplementPartialProduct m f z₀ s z) ?_
  intro s z hz
  simp [divisorComplementPartialProduct_def]

theorem differentiableOn_divisorComplementCanonicalProduct_univ
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1))) :
    DifferentiableOn ℂ (divisorComplementCanonicalProduct m f z₀) (Set.univ : Set ℂ) := by
  have hloc :
      TendstoLocallyUniformlyOn
        (fun s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) =>
          divisorComplementPartialProduct m f z₀ s)
        (divisorComplementCanonicalProduct m f z₀)
        Filter.atTop
        (Set.univ : Set ℂ) :=
    tendstoLocallyUniformlyOn_divisorComplementPartialProduct_univ (m := m) (f := f)
      (z₀ := z₀) h_sum
  have hF :
      ∀ᶠ s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) in Filter.atTop,
        DifferentiableOn ℂ (divisorComplementPartialProduct m f z₀ s) (Set.univ : Set ℂ) := by
    refine Filter.Eventually.of_forall ?_
    intro s
    exact (differentiable_divisorComplementPartialProduct m f z₀ s).differentiableOn
  have : (Filter.atTop : Filter (Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)))).NeBot :=
    Filter.atTop_neBot
  exact hloc.differentiableOn hF isOpen_univ

lemma divisorPartialProduct_eq_fiber_mul_complement_of_subset
    (m : ℕ) (f : ℂ → ℂ) (z₀ z : ℂ)
    (s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)))
    (hs : divisorZeroIndex₀_fiberFinset (f := f) z₀ ⊆ s) :
    divisorPartialProduct m f s z =
      divisorPartialProduct m f (divisorZeroIndex₀_fiberFinset (f := f) z₀) z *
        divisorComplementPartialProduct m f z₀ s z := by
  classical 
  let fiber : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) :=
    divisorZeroIndex₀_fiberFinset (f := f) z₀
  let P : divisorZeroIndex₀ f (Set.univ : Set ℂ) → Prop := fun p => p ∈ fiber
  let term : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℂ :=
    fun p => weierstrassFactor m (z / divisorZeroIndex₀_val p)
  have hfilter : s.filter P = fiber := by
    ext p
    constructor
    · intro hp
      exact (Finset.mem_filter.mp hp).2
    · intro hp
      exact Finset.mem_filter.mpr ⟨hs hp, hp⟩
  have hsplit :
      (∏ p ∈ s with P p, term p) * (∏ p ∈ s with ¬ P p, term p) = ∏ p ∈ s, term p := by
    simpa [term] using
      (Finset.prod_filter_mul_prod_filter_not (s := s) (p := P) (f := term))
  have hP : (∏ p ∈ s with P p, term p) = divisorPartialProduct m f fiber z := by
    have hg : ∀ x ∈ s \ fiber, (if x ∈ fiber then term x else (1 : ℂ)) = 1 := by
      intro x hx
      have hxnot : x ∉ fiber := (Finset.mem_sdiff.mp hx).2
      simp [hxnot]
    have hfg :
        ∀ x ∈ fiber, term x = (if x ∈ fiber then term x else (1 : ℂ)) := by
      intro x hx
      simp [hx]
    have hsub := (Finset.prod_subset_one_on_sdiff (s₁ := fiber) (s₂ := s)
        (f := term) (g := fun x => if x ∈ fiber then term x else (1 : ℂ)) hs hg hfg)
    simpa [divisorPartialProduct, term, P, fiber, Finset.prod_filter] using hsub.symm
  have hnotP : (∏ p ∈ s with ¬ P p, term p) = divisorComplementPartialProduct m f z₀ s z := by
    simp [divisorComplementPartialProduct, divisorComplementFactor, term, P, fiber,
      Finset.prod_filter, mem_divisorZeroIndex₀_fiberFinset]
  have hsplit' : ∏ p ∈ s, term p = (∏ p ∈ s with P p, term p) * (∏ p ∈ s with ¬ P p, term p) :=
    hsplit.symm
  calc
    divisorPartialProduct m f s z
        = ∏ p ∈ s, term p := by simp [divisorPartialProduct, term]
    _ = (∏ p ∈ s with P p, term p) * (∏ p ∈ s with ¬ P p, term p) := hsplit'
    _ = divisorPartialProduct m f fiber z * divisorComplementPartialProduct m f z₀ s z := by
      simp [hP, hnotP, fiber]

lemma divisorComplementPartialProduct_ne_zero_on_ball
    (m : ℕ) {f : ℂ → ℂ} {z₀ : ℂ} {ε : ℝ}
    (hball :
      Metric.ball z₀ ε ∩ (MeromorphicOn.divisor f (Set.univ : Set ℂ)).support = {z₀})
    (s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ))) :
    ∀ z ∈ Metric.ball z₀ ε,
      divisorComplementPartialProduct m f z₀ s z ≠ 0 := by
  intro z hz
  have hfac :
      ∀ p ∈ s, divisorComplementFactor m f z₀ p z ≠ 0 := by
    intro p hp
    by_cases hpF : p ∈ divisorZeroIndex₀_fiberFinset (f := f) z₀
    · simp only [divisorComplementFactor_eq_one_of_mem m f z₀ p z hpF]
      exact one_ne_zero
    · have hne : weierstrassFactor m (z / divisorZeroIndex₀_val p) ≠ 0 :=
        weierstrassFactor_div_ne_zero_on_ball_of_not_mem_fiberFinset
          (m := m) (f := f) (z₀ := z₀) (ε := ε) hball p hpF z hz
      rw [divisorComplementFactor_eq_weierstrassFactor_of_not_mem m f z₀ p z hpF]
      exact hne
  simpa [divisorComplementPartialProduct, Finset.prod_ne_zero_iff] using hfac

theorem eventually_eq_fiber_mul_divisorComplementPartialProduct
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ) :
    ∀ᶠ s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) in (Filter.atTop : Filter _),
      ∀ z : ℂ, divisorPartialProduct m f s z = divisorPartialProduct m f
        (divisorZeroIndex₀_fiberFinset (f := f) z₀) z *
          divisorComplementPartialProduct m f z₀ s z := by
  refine (eventually_atTop_subset_fiberFinset (f := f) z₀).mono ?_
  intro s hs z
  simpa using
    (divisorPartialProduct_eq_fiber_mul_complement_of_subset (m := m) (f := f) (z₀ := z₀)
      (z := z) (s := s) hs)

end Complex.Hadamard
end
end File15

-- Upstream module PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.DivisorPartialProductFactor
section File16
 

section
noncomputable section

open Complex Filter Function Finset Topology
open scoped Topology BigOperators
open Set

namespace Complex.Hadamard

theorem analyticOrderAt_finset_prod_weierstrassFactor_divisorZeroIndex₀
    (m : ℕ) (f : ℂ → ℂ)
    (s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ))) (z₀ : ℂ) :
    analyticOrderAt (fun z : ℂ => ∏ p ∈ s, weierstrassFactor m (z / divisorZeroIndex₀_val p))
        z₀ = ((s.filter (fun p => divisorZeroIndex₀_val p = z₀)).card : ℕ∞) := by
  classical 
  refine Finset.induction_on s ?base ?step
  · simp [analyticOrderAt_eq_zero]
  · intro p s hp hs
    by_cases hEq : divisorZeroIndex₀_val p = z₀
    · have hp0 : divisorZeroIndex₀_val p ≠ 0 := p.property
      have han_fac :
          AnalyticAt ℂ (fun z : ℂ => weierstrassFactor m (z / divisorZeroIndex₀_val p)) z₀ := by
        exact (differentiable_weierstrassFactor_divisorZeroIndex₀ m p).analyticAt z₀
      have han_rest : AnalyticAt ℂ (fun z : ℂ => ∏ q ∈ s, weierstrassFactor m
          (z / divisorZeroIndex₀_val q)) z₀ := by
        simpa [divisorPartialProduct] using! analyticAt_divisorPartialProduct m f s z₀
      let fac : ℂ → ℂ := fun z : ℂ => weierstrassFactor m (z / divisorZeroIndex₀_val p)
      let rest : ℂ → ℂ := fun z : ℂ => ∏ q ∈ s, weierstrassFactor m (z / divisorZeroIndex₀_val q)
      have hmul :
          analyticOrderAt (fac * rest) z₀ =
            analyticOrderAt fac z₀ + analyticOrderAt rest z₀ := by
        simpa [fac, rest] using (analyticOrderAt_mul (z₀ := z₀) han_fac han_rest)
      have hcard :
          (Finset.filter (fun q => divisorZeroIndex₀_val q = z₀) (insert p s)).card =
            (Finset.filter (fun q => divisorZeroIndex₀_val q = z₀) s).card + 1 := by
        simp [hEq, hp, Finset.filter_insert]
      have hfac : analyticOrderAt fac z₀ = (1 : ℕ∞) := by
        simpa [fac, hEq] using
          (analyticOrderAt_weierstrassFactor_div_self (m := m) (a := divisorZeroIndex₀_val p) hp0)
      have hrest : analyticOrderAt rest z₀ = ((s.filter
          (fun q => divisorZeroIndex₀_val q = z₀)).card : ℕ∞) := by
        simpa [rest] using hs
      have hcongr :
          (fun z : ℂ => ∏ q ∈ insert p s, weierstrassFactor m (z / divisorZeroIndex₀_val q))
            =ᶠ[𝓝 z₀] (fac * rest) := by
        refine Filter.Eventually.of_forall ?_
        intro z
        simp [fac, rest, Finset.prod_insert, hp, Pi.mul_apply]
      calc
        analyticOrderAt (fun z : ℂ => ∏ q ∈ insert p s, weierstrassFactor m
            (z / divisorZeroIndex₀_val q)) z₀ = analyticOrderAt (fac * rest) z₀ := by
              simpa using (analyticOrderAt_congr hcongr)
        _ = analyticOrderAt fac z₀ + analyticOrderAt rest z₀ := hmul
        _ = (1 : ℕ∞) + ((s.filter (fun q => divisorZeroIndex₀_val q = z₀)).card : ℕ∞) := by
              simp [hfac, hrest]
        _ = (((insert p s).filter (fun q => divisorZeroIndex₀_val q = z₀)).card : ℕ∞) := by
              simp [hcard, Nat.add_comm]
    · have han_fac :
          AnalyticAt ℂ (fun z : ℂ => weierstrassFactor m (z / divisorZeroIndex₀_val p)) z₀ := by
        exact (differentiable_weierstrassFactor_divisorZeroIndex₀ m p).analyticAt z₀
      have hfac0 : analyticOrderAt (fun z : ℂ => weierstrassFactor m
          (z / divisorZeroIndex₀_val p)) z₀ = 0 := by
        have hp0 : divisorZeroIndex₀_val p ≠ 0 := p.property
        have hval : weierstrassFactor m (z₀ / divisorZeroIndex₀_val p) ≠ 0 := by
          have : (z₀ / divisorZeroIndex₀_val p) ≠ 1 := by
            intro h1
            have : z₀ = divisorZeroIndex₀_val p := by
              have : z₀ = (z₀ / divisorZeroIndex₀_val p) * (divisorZeroIndex₀_val p) := by
                simp [div_eq_mul_inv]
              simpa [h1, div_eq_mul_inv, hp0] using this
            exact hEq (this.symm)
          exact (weierstrassFactor_ne_zero_iff m (z₀ / divisorZeroIndex₀_val p)).2 this
        simpa using (han_fac.analyticOrderAt_eq_zero).2 (by simpa using hval)
      have hcard :
          (Finset.filter (fun q => divisorZeroIndex₀_val q = z₀) (insert p s)).card =
            (Finset.filter (fun q => divisorZeroIndex₀_val q = z₀) s).card := by
        simp [hEq, Finset.filter_insert]
      have han_rest : AnalyticAt ℂ (fun z : ℂ => ∏ q ∈ s, weierstrassFactor m
          (z / divisorZeroIndex₀_val q)) z₀ := by
        simpa [divisorPartialProduct] using! analyticAt_divisorPartialProduct m f s z₀
      let fac : ℂ → ℂ := fun z : ℂ => weierstrassFactor m (z / divisorZeroIndex₀_val p)
      let rest : ℂ → ℂ := fun z : ℂ => ∏ q ∈ s, weierstrassFactor m (z / divisorZeroIndex₀_val q)
      have hmul :
          analyticOrderAt (fac * rest) z₀ =
            analyticOrderAt fac z₀ + analyticOrderAt rest z₀ := by
        simpa [fac, rest] using (analyticOrderAt_mul (z₀ := z₀) han_fac han_rest)
      have hcongr :
          (fun z : ℂ => ∏ q ∈ insert p s, weierstrassFactor m (z / divisorZeroIndex₀_val q))
            =ᶠ[𝓝 z₀] (fac * rest) := by
        refine Filter.Eventually.of_forall ?_
        intro z
        simp [fac, rest, Finset.prod_insert, hp, Pi.mul_apply]
      calc
        analyticOrderAt (fun z : ℂ => ∏ q ∈ insert p s, weierstrassFactor m
        (z / divisorZeroIndex₀_val q)) z₀
            = analyticOrderAt (fac * rest) z₀ := by
              simpa using (analyticOrderAt_congr hcongr)
        _ = analyticOrderAt rest z₀ := by
              calc
                analyticOrderAt (fac * rest) z₀ = analyticOrderAt fac z₀ +
                    analyticOrderAt rest z₀ := hmul
                _ = analyticOrderAt rest z₀ := by
                      have hfac0' : analyticOrderAt fac z₀ = 0 := by
                        simpa [fac] using hfac0
                      simp [hfac0']
        _ = ((s.filter (fun q => divisorZeroIndex₀_val q = z₀)).card : ℕ∞) := by
              simpa [rest] using hs
        _ = (((insert p s).filter (fun q => divisorZeroIndex₀_val q = z₀)).card : ℕ∞) := by
              simpa using congrArg (fun n : ℕ => (n : ℕ∞)) hcard.symm

theorem analyticOrderNatAt_finset_prod_weierstrassFactor_divisorZeroIndex₀
    (m : ℕ) (f : ℂ → ℂ)
    (s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ))) (z₀ : ℂ) :
    analyticOrderNatAt
        (fun z : ℂ => ∏ p ∈ s, weierstrassFactor m (z / divisorZeroIndex₀_val p)) z₀ =
      (s.filter (fun p => divisorZeroIndex₀_val p = z₀)).card := by
  simpa [analyticOrderNatAt] using
    (congrArg ENat.toNat
      (analyticOrderAt_finset_prod_weierstrassFactor_divisorZeroIndex₀ (m := m) (f := f) (s := s)
      (z₀ := z₀)))

theorem analyticOrderAt_partialProduct_eq_fiberCard_of_subset
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ)
    (s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)))
    (hs : divisorZeroIndex₀_fiberFinset (f := f) z₀ ⊆ s) :
    analyticOrderAt
        (fun z : ℂ => ∏ p ∈ s, weierstrassFactor m (z / divisorZeroIndex₀_val p))
        z₀ = ((divisorZeroIndex₀_fiberFinset (f := f) z₀).card : ℕ∞) := by
  have h :=
    analyticOrderAt_finset_prod_weierstrassFactor_divisorZeroIndex₀
      (m := m) (f := f) (s := s) (z₀ := z₀)
  have hfilter :
      s.filter (fun p => divisorZeroIndex₀_val p = z₀) =
        divisorZeroIndex₀_fiberFinset (f := f) z₀ := by
    ext p
    constructor
    · intro hp'
      have hpv : divisorZeroIndex₀_val p = z₀ := (Finset.mem_filter.mp hp').2
      simpa [mem_divisorZeroIndex₀_fiberFinset] using hpv
    · intro hp_fiber
      have hpv : divisorZeroIndex₀_val p = z₀ :=
        (mem_divisorZeroIndex₀_fiberFinset (f := f) (z₀ := z₀) p).1 hp_fiber
      have hps : p ∈ s := hs (by simpa [mem_divisorZeroIndex₀_fiberFinset] using hpv)
      exact Finset.mem_filter.2 ⟨hps, hpv⟩
  simpa [hfilter] using h

theorem exists_analyticAt_eq_pow_smul_of_partialProduct_contains_fiber
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ)
    (s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)))
    (hs : divisorZeroIndex₀_fiberFinset (f := f) z₀ ⊆ s) :
    ∃ g : ℂ → ℂ,
      AnalyticAt ℂ g z₀ ∧ g z₀ ≠ 0 ∧
        (fun z : ℂ => ∏ p ∈ s, weierstrassFactor m (z / divisorZeroIndex₀_val p))
          =ᶠ[𝓝 z₀]
          fun z : ℂ => (z - z₀) ^ (divisorZeroIndex₀_fiberFinset (f := f) z₀).card • g z := by
  let F : ℂ → ℂ := fun z : ℂ => ∏ p ∈ s, weierstrassFactor m (z / divisorZeroIndex₀_val p)
  have hF_ana : AnalyticAt ℂ F z₀ := by
    simpa [F, divisorPartialProduct] using! analyticAt_divisorPartialProduct m f s z₀
  have hOrder :
      analyticOrderAt F z₀ =
        ((divisorZeroIndex₀_fiberFinset (f := f) z₀).card : ℕ∞) := by
    simpa [F] using
      (analyticOrderAt_partialProduct_eq_fiberCard_of_subset (m := m)
      (f := f) (z₀ := z₀) (s := s) hs)
  refine (hF_ana.analyticOrderAt_eq_natCast (n := (divisorZeroIndex₀_fiberFinset
    (f := f) z₀).card)).1 ?_
  simp [hOrder]

end Complex.Hadamard
end
end
end File16

-- Upstream module PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.DivisorQuotientConvergence
section File17
 

section
open Filter Function Complex Finset Topology
open scoped Topology BigOperators
open Set

namespace Complex.Hadamard

theorem tendstoLocallyUniformlyOn_divisorPartialProduct_univ
    (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1))) :
    TendstoLocallyUniformlyOn
      (fun s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) => divisorPartialProduct m f s)
      (divisorCanonicalProduct m f (Set.univ : Set ℂ))
      Filter.atTop
      (Set.univ : Set ℂ) := by
  have hprod :
      HasProdLocallyUniformlyOn
        (fun (p : divisorZeroIndex₀ f (Set.univ : Set ℂ)) (z : ℂ) =>
          weierstrassFactor m (z / divisorZeroIndex₀_val p))
        (divisorCanonicalProduct m f (Set.univ : Set ℂ))
        (Set.univ : Set ℂ) :=
    hasProdLocallyUniformlyOn_divisorCanonicalProduct_univ (m := m) (f := f) h_sum
  simpa [HasProdLocallyUniformlyOn, divisorPartialProduct] using! hprod

theorem tendstoUniformlyOn_divisorPartialProduct_div_pow_sub
    (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1)))
    (z₀ : ℂ) (k : ℕ) {K : Set ℂ} (hK : IsCompact K) (hKz : ∀ z ∈ K, z ≠ z₀) :
    TendstoUniformlyOn
      (fun s z => (divisorPartialProduct m f s z) / (z - z₀) ^ k)
      (fun z => (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) / (z - z₀) ^ k)
      (Filter.atTop : Filter (Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ))))
      K := by
  have hloc :
      TendstoLocallyUniformlyOn
        (fun s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) => divisorPartialProduct m f s)
        (divisorCanonicalProduct m f (Set.univ : Set ℂ))
        Filter.atTop
        K :=
    (tendstoLocallyUniformlyOn_divisorPartialProduct_univ (m := m) (f := f) h_sum).mono
      (by intro z hz; simp)
  have hunif :
      TendstoUniformlyOn
        (fun s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) => divisorPartialProduct m f s)
        (divisorCanonicalProduct m f (Set.univ : Set ℂ))
        Filter.atTop
        K :=
    (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).1 hloc
  let h : ℂ → ℂ := fun z => ((z - z₀) ^ k)⁻¹
  have hh : ∃ C, ∀ z ∈ K, ‖h z‖ ≤ C := by
    have hcont : ContinuousOn h K := by
      have hpow : ContinuousOn (fun z : ℂ => (z - z₀) ^ k) K := by
        fun_prop
      refine hpow.inv₀ ?_
      intro z hz
      have hz0 : z - z₀ ≠ 0 := sub_ne_zero.mpr (hKz z hz)
      exact pow_ne_zero k hz0
    have hKimg : IsCompact (h '' K) := hK.image_of_continuousOn hcont
    rcases (isBounded_iff_forall_norm_le.1 hKimg.isBounded) with ⟨C, hC⟩
    refine ⟨C, ?_⟩
    intro z hz
    exact hC (h z) ⟨z, hz, rfl⟩
  have hunif' :=
    (Complex.tendstoUniformlyOn_mul_left_bounded (p := (Filter.atTop : Filter (Finset (divisorZeroIndex₀ f
    (Set.univ : Set ℂ)))))
        (K := K)
        (F := fun s z => divisorPartialProduct m f s z)
        (f := fun z => divisorCanonicalProduct m f (Set.univ : Set ℂ) z)
        (h := h)
        hunif hh)
  simpa [h, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hunif'

theorem tendstoLocallyUniformlyOn_divisorPartialProduct_div_pow_sub
    (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1)))
    (z₀ : ℂ) (k : ℕ) :
    TendstoLocallyUniformlyOn
      (fun s z => (divisorPartialProduct m f s z) / (z - z₀) ^ k)
      (fun z => (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) / (z - z₀) ^ k)
      (Filter.atTop : Filter (Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ))))
      ((Set.univ : Set ℂ) \ {z₀}) := by
  have hopen : IsOpen ((Set.univ : Set ℂ) \ {z₀}) := by
    have hset : ((Set.univ : Set ℂ) \ {z₀}) = ({z₀} : Set ℂ)ᶜ := by
      ext z
      simp
    simp [hset]
  refine (tendstoLocallyUniformlyOn_iff_forall_isCompact hopen).2 ?_
  intro K hKsub hK
  have hKz : ∀ z ∈ K, z ≠ z₀ := by
    intro z hzK
    have : z ∈ (Set.univ : Set ℂ) \ {z₀} := hKsub hzK
    exact by simpa [Set.mem_sdiff, Set.mem_singleton_iff] using this.2
  exact tendstoUniformlyOn_divisorPartialProduct_div_pow_sub
    (m := m) (f := f) h_sum (z₀ := z₀) (k := k) (hK := hK) hKz

open Filter

theorem exists_ball_eq_divisorCanonicalProduct_div_pow_eq
    (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1)))
    (z₀ : ℂ) :
    ∃ ε > 0, ∃ u : ℂ → ℂ, AnalyticAt ℂ u z₀ ∧
      u z₀ ≠ 0 ∧
        ∀ z : ℂ, z ∈ Metric.ball z₀ ε → z ≠ z₀ →
          (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) /
              (z - z₀) ^ (divisorZeroIndex₀_fiberFinset (f := f) z₀).card =
            (divisorComplementCanonicalProduct m f z₀ z) * u z := by
  let fiber : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) :=
    divisorZeroIndex₀_fiberFinset (f := f) z₀
  have hfib : ∃ u : ℂ → ℂ, AnalyticAt ℂ u z₀ ∧ u z₀ ≠ 0 ∧
          (fun z : ℂ => divisorPartialProduct m f fiber z) =ᶠ[𝓝 z₀]
            fun z : ℂ => (z - z₀) ^ fiber.card • u z := by
    simpa [fiber, divisorPartialProduct] using
      (exists_analyticAt_eq_pow_smul_of_partialProduct_contains_fiber (m := m) (f := f) (z₀ := z₀)
        (s := fiber) (by rfl : fiber ⊆ fiber))
  rcases hfib with ⟨u, huA, hu0, huEq⟩
  have hmem : {z : ℂ | divisorPartialProduct m f fiber z =
      (z - z₀) ^ fiber.card • u z} ∈ 𝓝 z₀ := huEq
  rcases Metric.mem_nhds_iff.1 hmem with ⟨ε, hε, hball⟩
  refine ⟨ε, hε, u, huA, hu0, ?_⟩
  have hq :
      TendstoLocallyUniformlyOn (fun s z => (divisorPartialProduct m f s z) / (z - z₀) ^ fiber.card)
        (fun z => (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) / (z - z₀) ^ fiber.card)
        (Filter.atTop : Filter (Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ))))
        ((Set.univ : Set ℂ) \ {z₀}) :=
    tendstoLocallyUniformlyOn_divisorPartialProduct_div_pow_sub
      (m := m) (f := f) (h_sum := h_sum) (z₀ := z₀) (k := fiber.card)
  have hcomp :
      TendstoLocallyUniformlyOn
        (fun s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) =>
          divisorComplementPartialProduct m f z₀ s)
        (divisorComplementCanonicalProduct m f z₀)
        Filter.atTop
        (Set.univ : Set ℂ) :=
    tendstoLocallyUniformlyOn_divisorComplementPartialProduct_univ (m := m) (f := f)
    (z₀ := z₀) h_sum
  intro z hz hzne
  have hz' : z ∈ ((Set.univ : Set ℂ) \ {z₀}) := by
    refine ⟨by simp, ?_⟩
    simpa [Set.mem_singleton_iff] using hzne
  have hF : Tendsto (fun s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) =>
          (divisorPartialProduct m f s z) / (z - z₀) ^ fiber.card) (Filter.atTop : Filter _)
        (𝓝 ((divisorCanonicalProduct m f (Set.univ : Set ℂ) z) / (z - z₀) ^ fiber.card)) :=
    hq.tendsto_at hz'
  have hG0 : Tendsto  (fun s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) =>
          divisorComplementPartialProduct m f z₀ s z) (Filter.atTop : Filter _)
        (𝓝 (divisorComplementCanonicalProduct m f z₀ z)) :=
    hcomp.tendsto_at (by simp : z ∈ (Set.univ : Set ℂ))
  have hG : Tendsto (fun s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) =>
          (divisorComplementPartialProduct m f z₀ s z) * u z) (Filter.atTop : Filter _)
        (𝓝 ((divisorComplementCanonicalProduct m f z₀ z) * u z)) :=
    (hG0.mul tendsto_const_nhds)
  have hsub : ∀ᶠ s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) in (Filter.atTop : Filter _),
      fiber ⊆ s := eventually_atTop_subset_fiberFinset (f := f) z₀
  have heq_eventually :
      ∀ᶠ s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) in (Filter.atTop : Filter _),
        (divisorPartialProduct m f s z) / (z - z₀) ^ fiber.card
          = (divisorComplementPartialProduct m f z₀ s z) * u z := by
    filter_upwards [hsub] with s hs
    have hsplit :
        divisorPartialProduct m f s z =
          divisorPartialProduct m f fiber z * divisorComplementPartialProduct m f z₀ s z := by
      simpa [fiber] using
        (divisorPartialProduct_eq_fiber_mul_complement_of_subset (m := m) (f := f) (z₀ := z₀)
          (z := z) (s := s) hs)
    have hfibz :
        divisorPartialProduct m f fiber z = (z - z₀) ^ fiber.card • u z := by
      exact hball hz
    have hzpow : (z - z₀) ^ fiber.card ≠ 0 :=
      pow_ne_zero _ (sub_ne_zero.mpr hzne)
    set a : ℂ := (z - z₀) ^ fiber.card
    have ha : a ≠ 0 := by simpa [a] using hzpow
    set c : ℂ := divisorComplementPartialProduct m f z₀ s z with hc
    rw [hsplit, hfibz, smul_eq_mul]
    calc
      ((a * u z) * c) / a
          = (a * (u z * c)) / a := by simp [mul_assoc]
      _ = u z * c := by
            simpa [mul_assoc] using (mul_div_cancel_left₀ (u z * c) ha)
      _ = c * u z := by ac_rfl
      _ = (divisorComplementPartialProduct m f z₀ s z) * u z := by
            simp [c]
  have hG' :
      Tendsto
        (fun s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) =>
          (divisorPartialProduct m f s z) / (z - z₀) ^ fiber.card)
        (Filter.atTop : Filter _)
        (𝓝 ((divisorComplementCanonicalProduct m f z₀ z) * u z)) := by
    have heq' :
        ∀ᶠ s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) in (Filter.atTop : Filter _),
          (divisorComplementPartialProduct m f z₀ s z) * u z
            = (divisorPartialProduct m f s z) / (z - z₀) ^ fiber.card := by
      filter_upwards [heq_eventually] with s hs
      exact hs.symm
    exact (hG.congr' heq')
  exact tendsto_nhds_unique hF hG'

theorem bddAbove_norm_divisorCanonicalProduct_div_pow_puncturedBall
    (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1)))
    (z₀ : ℂ) : ∃ r > 0, BddAbove (norm ∘ (fun z : ℂ =>
      (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) /
        (z - z₀) ^ (divisorZeroIndex₀_fiberFinset (f := f) z₀).card) ''
      ((Metric.ball z₀ r) \ {z₀})) := by
  rcases exists_ball_eq_divisorCanonicalProduct_div_pow_eq (m := m) (f := f) (h_sum := h_sum)
    (z₀ := z₀) with ⟨ε, hε, u, huA, hu0, hEq⟩
  have huC : ContinuousAt u z₀ := huA.continuousAt
  have hpre : {z : ℂ | ‖u z - u z₀‖ < 1} ∈ 𝓝 z₀ := by
    have : u ⁻¹' Metric.ball (u z₀) (1 : ℝ) ∈ 𝓝 z₀ :=
      huC.preimage_mem_nhds (Metric.ball_mem_nhds (u z₀) (by norm_num))
    simpa [Metric.ball, dist_eq_norm, Set.preimage] using this
  rcases Metric.mem_nhds_iff.1 hpre with ⟨r0, hr0pos, hr0sub⟩
  set r : ℝ := min (ε / 2) r0
  have hrpos : 0 < r := lt_min (by nlinarith [hε]) hr0pos
  have hr_lt_ε : r < ε := lt_of_le_of_lt (min_le_left _ _) (by nlinarith [hε])
  have huBound : ∀ z ∈ Metric.ball z₀ r, ‖u z‖ ≤ ‖u z₀‖ + 1 := by
    intro z hz
    have hz0 : z ∈ Metric.ball z₀ r0 := by
      have : r ≤ r0 := min_le_right _ _
      exact Metric.ball_subset_ball this hz
    have hdiff : ‖u z - u z₀‖ < 1 := hr0sub hz0
    have htri : ‖u z‖ ≤ ‖u z - u z₀‖ + ‖u z₀‖ := by
      simpa [sub_eq_add_neg, add_assoc] using
        (norm_add_le (u z - u z₀) (u z₀))
    have : ‖u z‖ ≤ 1 + ‖u z₀‖ := le_trans htri (by nlinarith [le_of_lt hdiff])
    nlinarith [this]
  have hdiffC :
      DifferentiableOn ℂ (divisorComplementCanonicalProduct m f z₀) (Set.univ : Set ℂ) :=
    differentiableOn_divisorComplementCanonicalProduct_univ (m := m) (f := f) (z₀ := z₀) h_sum
  have hcontC : ContinuousOn (divisorComplementCanonicalProduct m f z₀) (Metric.closedBall z₀ r) :=
    (hdiffC.continuousOn).mono (by intro z hz; simp)
  have hK : IsCompact (Metric.closedBall z₀ r) := isCompact_closedBall _ _
  rcases (isBounded_iff_forall_norm_le.1 (hK.image_of_continuousOn hcontC).isBounded) with ⟨C, hC⟩
  refine ⟨r, hrpos, ⟨C * (‖u z₀‖ + 1), ?_⟩⟩
  rintro _ ⟨z, hzset, rfl⟩
  rcases hzset with ⟨hzr, hzne⟩
  have hz_in_ε : z ∈ Metric.ball z₀ ε := Metric.ball_subset_ball hr_lt_ε.le hzr
  have hz_ne : z ≠ z₀ := by simpa [Set.mem_singleton_iff] using hzne
  have hq :
      (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) /
          (z - z₀) ^ (divisorZeroIndex₀_fiberFinset (f := f) z₀).card
        = divisorComplementCanonicalProduct m f z₀ z * u z :=
    hEq z hz_in_ε hz_ne
  have hCz : ‖divisorComplementCanonicalProduct m f z₀ z‖ ≤ C := by
    have hzK : z ∈ Metric.closedBall z₀ r := Metric.mem_closedBall.2 (le_of_lt hzr)
    exact hC _ ⟨z, hzK, rfl⟩
  have huZ : ‖u z‖ ≤ ‖u z₀‖ + 1 := huBound z hzr
  have hCnonneg : 0 ≤ C := le_trans (norm_nonneg _) hCz
  have hmul : ‖divisorComplementCanonicalProduct m f z₀ z * u z‖ ≤ C * (‖u z₀‖ + 1) := by
    calc
      ‖divisorComplementCanonicalProduct m f z₀ z * u z‖
          = ‖divisorComplementCanonicalProduct m f z₀ z‖ * ‖u z‖ := by simp
      _ ≤ C * (‖u z₀‖ + 1) := by
            exact mul_le_mul hCz huZ (norm_nonneg _) hCnonneg
  simpa [Function.comp, hq] using hmul

theorem divisorComplementCanonicalProduct_ne_zero_at
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1))) :
    divisorComplementCanonicalProduct m f z₀ z₀ ≠ 0 := by
  let Φ : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℂ :=
    fun p => if divisorZeroIndex₀_val p = z₀ then (1 : ℂ)
      else weierstrassFactor m (z₀ / divisorZeroIndex₀_val p)
  let a : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℂ := fun p => Φ p - 1
  have hΦ_ne : ∀ p, Φ p ≠ 0 := by
    intro p
    by_cases hp : divisorZeroIndex₀_val p = z₀
    · simp [Φ, hp]
    · have hval : divisorZeroIndex₀_val p ≠ z₀ := hp
      have hz : z₀ / divisorZeroIndex₀_val p ≠ (1 : ℂ) := by
        intro h
        by_cases hp0 : divisorZeroIndex₀_val p = 0
        · have : z₀ / divisorZeroIndex₀_val p = (0 : ℂ) := by simp [hp0]
          have h01 := h
          rw [this] at h01
          exact (show False from (by simpa using (show (0 : ℂ) ≠ (1 : ℂ) from by simp) h01))
        · have : z₀ = divisorZeroIndex₀_val p := (div_eq_one_iff_eq hp0).1 h
          exact hval this.symm
      have hE : weierstrassFactor m (z₀ / divisorZeroIndex₀_val p) ≠ 0 := by
        intro h0
        have : z₀ / divisorZeroIndex₀_val p = (1 : ℂ) :=
          (weierstrassFactor_eq_zero_iff (m := m) (z := z₀ / divisorZeroIndex₀_val p)).1 h0
        exact hz this
      simp [Φ, hp, hE]
  have hz0_le : ‖z₀‖ ≤ max ‖z₀‖ 1 := le_max_left _ _
  set R : ℝ := max ‖z₀‖ 1
  have hRpos : 0 < R := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_right _ _)
  let u : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ :=
    fun p => (4 * R ^ (m + 1)) * (‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1))
  have hu : Summable u := h_sum.mul_left (4 * R ^ (m + 1))
  have h_big :
      ∀ᶠ p : divisorZeroIndex₀ f (Set.univ : Set ℂ) in Filter.cofinite,
        (2 * R : ℝ) < ‖divisorZeroIndex₀_val p‖ := by
    have hfin : ({p : divisorZeroIndex₀ f (Set.univ : Set ℂ) | ‖divisorZeroIndex₀_val p‖ ≤
        2 * R} : Set _).Finite := by
      have : Metric.closedBall (0 : ℂ) (2 * R) ⊆ (Set.univ : Set ℂ) := by simp
      exact divisorZeroIndex₀_norm_le_finite (f := f) (U := (Set.univ : Set ℂ)) (B := 2 * R) this
    have := hfin.eventually_cofinite_notMem
    filter_upwards [this] with p hp
    have : ¬ ‖divisorZeroIndex₀_val p‖ ≤ 2 * R := by simpa using hp
    exact lt_of_not_ge this
  have hBound :
      ∀ᶠ p in Filter.cofinite, ‖a p‖ ≤ u p := by
    filter_upwards [h_big] with p hp
    have ha_pos : 0 < ‖divisorZeroIndex₀_val p‖ := lt_trans (by nlinarith [hRpos]) hp
    have hz_div : ‖z₀ / divisorZeroIndex₀_val p‖ ≤ (1 / 2 : ℝ) := by
      have h2R_pos : 0 < (2 * R : ℝ) := by nlinarith [hRpos]
      have hinv : ‖divisorZeroIndex₀_val p‖⁻¹ < (2 * R)⁻¹ := by
        simpa [one_div] using (one_div_lt_one_div_of_lt h2R_pos hp)
      have hmul_le : ‖z₀‖ * ‖divisorZeroIndex₀_val p‖⁻¹ ≤ R * ‖divisorZeroIndex₀_val p‖⁻¹ := by
        refine mul_le_mul_of_nonneg_right ?_ (inv_nonneg.2 (norm_nonneg _))
        exact hz0_le
      have hmul_lt : R * ‖divisorZeroIndex₀_val p‖⁻¹ < R * (2 * R)⁻¹ :=
        mul_lt_mul_of_pos_left hinv hRpos
      have hlt : ‖z₀‖ * ‖divisorZeroIndex₀_val p‖⁻¹ < R * (2 * R)⁻¹ :=
        lt_of_le_of_lt hmul_le hmul_lt
      have hRhalf : R * (2 * R)⁻¹ = (1 / 2 : ℝ) := by
        have hRne : (R : ℝ) ≠ 0 := hRpos.ne'
        have : R * (2 * R)⁻¹ = R / (2 * R) := by simp [div_eq_mul_inv]
        rw [this]
        field_simp [hRne]
      have hnorm : ‖z₀ / divisorZeroIndex₀_val p‖ = ‖z₀‖ * ‖divisorZeroIndex₀_val p‖⁻¹ := by
        simp [div_eq_mul_inv]
      have hzlt : ‖z₀ / divisorZeroIndex₀_val p‖ < (1 / 2 : ℝ) := by
        calc
          ‖z₀ / divisorZeroIndex₀_val p‖ = ‖z₀‖ * ‖divisorZeroIndex₀_val p‖⁻¹ := hnorm
          _ < R * (2 * R)⁻¹ := hlt
          _ = (1 / 2 : ℝ) := hRhalf
      exact le_of_lt hzlt
    have hE :
        ‖weierstrassFactor m (z₀ / divisorZeroIndex₀_val p) - 1‖ ≤
          4 * ‖z₀ / divisorZeroIndex₀_val p‖ ^ (m + 1) :=
      weierstrassFactor_sub_one_pow_bound (m := m) (z := z₀ / divisorZeroIndex₀_val p) hz_div
    have hz_pow :
        ‖z₀ / divisorZeroIndex₀_val p‖ ^ (m + 1) ≤
          (R ^ (m + 1)) * (‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1)) := by
      have : ‖z₀ / divisorZeroIndex₀_val p‖ = ‖z₀‖ * ‖divisorZeroIndex₀_val p‖⁻¹ := by
        simp [div_eq_mul_inv]
      rw [this]
      have : (‖z₀‖ * ‖divisorZeroIndex₀_val p‖⁻¹) ^ (m + 1) =
          ‖z₀‖ ^ (m + 1) * (‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1)) := by
        simp [mul_pow]
      rw [this]
      have hzle_pow : ‖z₀‖ ^ (m + 1) ≤ R ^ (m + 1) :=
        pow_le_pow_left₀ (norm_nonneg z₀) hz0_le (m + 1)
      gcongr
    have hp_ne : divisorZeroIndex₀_val p ≠ z₀ := by
      intro h
      have : ‖divisorZeroIndex₀_val p‖ ≤ R := by
        simp [h, R]  
      exact (not_lt_of_ge this) (lt_trans (by nlinarith [hRpos]) hp)
    have ha : ‖a p‖ = ‖weierstrassFactor m (z₀ / divisorZeroIndex₀_val p) - 1‖ := by
      simp [a, Φ, hp_ne, sub_eq_add_neg]
    calc
      ‖a p‖ = ‖weierstrassFactor m (z₀ / divisorZeroIndex₀_val p) - 1‖ := ha
      _ ≤ 4 * ‖z₀ / divisorZeroIndex₀_val p‖ ^ (m + 1) := by
            simpa [sub_eq_add_neg, add_comm] using hE
      _ ≤ 4 * (R ^ (m + 1) * (‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1))) := by
            gcongr
      _ = u p := by
            simp [u, mul_assoc, mul_comm]
  have hsum_norm : Summable (fun p => ‖a p‖) := by
    refine (Summable.of_norm_bounded_eventually (E := ℝ) (f := fun p => ‖a p‖) (g := u) hu ?_)
    filter_upwards [hBound] with p hp
    simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg (a p))] using hp
  have htprod_ne :
      (∏' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), (1 + a p)) ≠ 0 :=
    tprod_one_add_ne_zero_of_summable (R := ℂ) (f := a) (hf := fun p => by
      simpa [a, Φ, add_sub_cancel] using hΦ_ne p) hsum_norm
  have : (∏' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), (1 + a p)) =
      divisorComplementCanonicalProduct m f z₀ z₀ := by
    simp [a, Φ, divisorComplementCanonicalProduct, divisorComplementFactor_def]
  exact by
    intro h0
    exact htprod_ne (by simpa [this] using h0)

theorem exists_ball_divisorComplementCanonicalProduct_ne_zero
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1))) :
    ∃ r > 0, ∀ z ∈ Metric.ball z₀ r, divisorComplementCanonicalProduct m f z₀ z ≠ 0 := by
  have hdiff :
      DifferentiableOn ℂ (divisorComplementCanonicalProduct m f z₀) (Set.univ : Set ℂ) :=
    differentiableOn_divisorComplementCanonicalProduct_univ (m := m) (f := f) (z₀ := z₀) h_sum
  have hdiffAt : DifferentiableAt ℂ (divisorComplementCanonicalProduct m f z₀) z₀ := by
    exact (hdiff z₀ (by simp)).differentiableAt (by simp)
  have hcont : ContinuousAt (divisorComplementCanonicalProduct m f z₀) z₀ :=
    hdiffAt.continuousAt
  have h0 : divisorComplementCanonicalProduct m f z₀ z₀ ≠ 0 :=
    divisorComplementCanonicalProduct_ne_zero_at (m := m) (f := f) (z₀ := z₀) h_sum
  have hopen : IsOpen (({0} : Set ℂ)ᶜ) := isClosed_singleton.isOpen_compl
  have hmem : divisorComplementCanonicalProduct m f z₀ z₀ ∈ (({0} : Set ℂ)ᶜ) := by
    simp [h0]
  rcases (Metric.mem_nhds_iff.1 (hcont (hopen.mem_nhds hmem))) with ⟨r, hrpos, hr⟩
  refine ⟨r, hrpos, ?_⟩
  intro z hz
  have : divisorComplementCanonicalProduct m f z₀ z ∈ ({0} : Set ℂ)ᶜ := hr hz
  simpa using this

theorem eventually_exists_analyticAt_eq_pow_smul_divisorPartialProduct
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ) :
    ∀ᶠ s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) in (Filter.atTop : Filter _),
      ∃ g : ℂ → ℂ, AnalyticAt ℂ g z₀ ∧ g z₀ ≠ 0 ∧ (fun z : ℂ => divisorPartialProduct m f s z)
        =ᶠ[𝓝 z₀] fun z : ℂ =>
          (z - z₀) ^ (divisorZeroIndex₀_fiberFinset (f := f) z₀).card • g z := by
  refine (eventually_atTop_subset_fiberFinset (f := f) z₀).mono ?_
  intro s hs
  rcases
      exists_analyticAt_eq_pow_smul_of_partialProduct_contains_fiber
        (m := m) (f := f) (z₀ := z₀) (s := s) hs with
    ⟨g, hg, hg0, hEq⟩
  refine ⟨g, hg, hg0, ?_⟩
  simpa [divisorPartialProduct] using hEq

theorem eventually_eq_punctured_quotient_of_factorization
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ) :
    ∀ᶠ s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) in (Filter.atTop : Filter _),
      ∃ g : ℂ → ℂ, AnalyticAt ℂ g z₀ ∧ (fun z : ℂ => (divisorPartialProduct m f s z) /
            (z - z₀) ^ (divisorZeroIndex₀_fiberFinset (f := f) z₀).card)
            =ᶠ[𝓝[≠] z₀] g := by
  refine (eventually_exists_analyticAt_eq_pow_smul_divisorPartialProduct (m := m)
    (f := f) z₀).mono ?_
  intro s hs
  rcases hs with ⟨g, hg, hg0, hEq⟩
  refine ⟨g, hg, ?_⟩
  have hEq' : (fun z : ℂ => divisorPartialProduct m f s z) =ᶠ[𝓝[≠] z₀]
        fun z : ℂ => (z - z₀) ^ (divisorZeroIndex₀_fiberFinset (f := f) z₀).card • g z :=
    hEq.filter_mono nhdsWithin_le_nhds
  have hne : ∀ᶠ z : ℂ in 𝓝[≠] z₀, z ≠ z₀ := by
    simpa [Filter.Eventually] using! (self_mem_nhdsWithin : {z : ℂ | z ≠ z₀} ∈ 𝓝[≠] z₀)
  filter_upwards [hEq', hne] with z hz hzne
  have hz0 : (z - z₀) ^ (divisorZeroIndex₀_fiberFinset (f := f) z₀).card ≠ 0 :=
    pow_ne_zero _ (sub_ne_zero.mpr hzne)
  have : (divisorPartialProduct m f s z) / (z - z₀) ^ (divisorZeroIndex₀_fiberFinset
      (f := f) z₀).card = g z := by
    rw [hz]
    simpa [smul_eq_mul] using (mul_div_cancel_left₀ (g z) hz0)
  simpa [divisorPartialProduct] using this

theorem eventually_exists_ball_eq_punctured_quotient_of_factorization
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ) :
    ∀ᶠ s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) in (Filter.atTop : Filter _),
      ∃ ε > 0, ∃ g : ℂ → ℂ, AnalyticAt ℂ g z₀ ∧
        ∀ z : ℂ, z ∈ Metric.ball z₀ ε → z ≠ z₀ → (divisorPartialProduct m f s z) /
              (z - z₀) ^ (divisorZeroIndex₀_fiberFinset (f := f) z₀).card
            = g z := by
  refine (eventually_eq_punctured_quotient_of_factorization (m := m) (f := f) z₀).mono ?_
  intro s hs
  rcases hs with ⟨g, hg, hEq⟩
  rcases (Metric.nhdsWithin_basis_ball (x := z₀) (s := {z : ℂ | z ≠ z₀})).mem_iff.1 hEq with
    ⟨ε, hε, hball⟩
  refine ⟨ε, hε, g, hg, ?_⟩
  intro z hz hz0
  have hz' : z ∈ Metric.ball z₀ ε ∩ {z : ℂ | z ≠ z₀} := ⟨hz, hz0⟩
  exact hball hz'

end Complex.Hadamard
end
end File17

-- Upstream module PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.DivisorQuotientRemovable
section File18
 

section
open Filter Function Complex Finset Topology
open scoped Topology BigOperators
open Set

namespace Complex.Hadamard

theorem differentiableOn_divisorPartialProduct_div_pow_sub
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ) (k : ℕ)
    (s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ))) :
    DifferentiableOn ℂ (fun z : ℂ => (divisorPartialProduct m f s z) / (z - z₀) ^ k)
      ((Set.univ : Set ℂ) \ {z₀}) := by
  have hdiff_prod : DifferentiableOn ℂ (divisorPartialProduct m f s) (Set.univ : Set ℂ) := by
    exact (differentiable_divisorPartialProduct m f s).differentiableOn
  have hdiff_den : DifferentiableOn ℂ (fun z : ℂ => (z - z₀) ^ k) ((Set.univ : Set ℂ) \ {z₀}) := by
    have : Differentiable ℂ (fun z : ℂ => (z - z₀) ^ k) := by
      fun_prop
    exact this.differentiableOn
  by_cases hk : k = 0
  · subst hk
    simpa [pow_zero] using! (hdiff_prod.mono (by intro z hz; exact hz.1))
  · have hne : ∀ z ∈ ((Set.univ : Set ℂ) \ {z₀}), (fun z : ℂ => (z - z₀) ^ k) z ≠ 0 := by
      intro z hz
      have hz' : z ≠ z₀ := by
        simpa [Set.mem_sdiff, Set.mem_singleton_iff] using hz.2
      exact pow_ne_zero _ (sub_ne_zero.mpr hz')
    have hdiff_inv :
        DifferentiableOn ℂ (fun z : ℂ => ((z - z₀) ^ k)⁻¹) ((Set.univ : Set ℂ) \ {z₀}) :=
      hdiff_den.inv hne
    simpa [div_eq_mul_inv] using! (hdiff_prod.mono (by intro z hz; exact hz.1)).mul hdiff_inv

theorem differentiableOn_divisorCanonicalProduct_div_pow_sub
    (m : ℕ) (f : ℂ → ℂ) (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1)))
    (z₀ : ℂ) (k : ℕ) : DifferentiableOn ℂ
      (fun z : ℂ => (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) / (z - z₀) ^ k)
      ((Set.univ : Set ℂ) \ {z₀}) := by
  have hopen : IsOpen ((Set.univ : Set ℂ) \ {z₀}) := by
    have hset : ((Set.univ : Set ℂ) \ {z₀}) = ({z₀} : Set ℂ)ᶜ := by
      ext z; simp
    simp [hset]
  have hconv :=
    tendstoLocallyUniformlyOn_divisorPartialProduct_div_pow_sub
      (m := m) (f := f) h_sum (z₀ := z₀) (k := k)
  refine hconv.differentiableOn ?_ hopen
  refine Filter.Eventually.of_forall ?_
  intro s
  exact differentiableOn_divisorPartialProduct_div_pow_sub (m := m) (f := f) (z₀ := z₀) (k := k) s

theorem differentiableOn_update_limUnder_divisorCanonicalProduct_div_pow
    (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1)))
    (z₀ : ℂ) : ∃ r > 0, DifferentiableOn ℂ (Function.update
          (fun z : ℂ => (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) /
            (z - z₀) ^ (divisorZeroIndex₀_fiberFinset (f := f) z₀).card) z₀
          (limUnder (𝓝[≠] z₀) (fun z : ℂ => (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) /
                (z - z₀) ^ (divisorZeroIndex₀_fiberFinset (f := f) z₀).card)))
        (Metric.ball z₀ r) := by
  rcases bddAbove_norm_divisorCanonicalProduct_div_pow_puncturedBall (m := m) (f := f)
      (h_sum := h_sum) (z₀ := z₀) with ⟨r, hrpos, hbdd⟩
  refine ⟨r, hrpos, ?_⟩
  have hnhds : Metric.ball z₀ r ∈ 𝓝 z₀ := Metric.ball_mem_nhds z₀ hrpos
  have hdiff : DifferentiableOn ℂ (fun z : ℂ =>
        (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) /
          (z - z₀) ^ (divisorZeroIndex₀_fiberFinset (f := f) z₀).card)
      ((Metric.ball z₀ r) \ {z₀}) := by
    have hglob :=
      differentiableOn_divisorCanonicalProduct_div_pow_sub
        (m := m) (f := f) h_sum (z₀ := z₀)
        (k := (divisorZeroIndex₀_fiberFinset (f := f) z₀).card)
    refine hglob.mono ?_
    intro z hz
    exact ⟨by simp, hz.2⟩
  have hb : BddAbove (norm ∘ (fun z : ℂ => (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) /
      (z - z₀) ^ (divisorZeroIndex₀_fiberFinset (f := f) z₀).card) ''
    ((Metric.ball z₀ r) \ {z₀})) := hbdd
  simpa using
    (Complex.differentiableOn_update_limUnder_of_bddAbove (f := fun z : ℂ =>
        (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) /
          (z - z₀) ^ (divisorZeroIndex₀_fiberFinset (f := f) z₀).card)
      (s := Metric.ball z₀ r) (c := z₀) hnhds hdiff hb)

theorem analyticAt_update_limUnder_divisorCanonicalProduct_div_pow
    (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1)))
    (z₀ : ℂ) : AnalyticAt ℂ (Function.update (fun z : ℂ =>
          (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) /
        (z - z₀) ^ (divisorZeroIndex₀_fiberFinset (f := f) z₀).card) z₀
        (limUnder (𝓝[≠] z₀) (fun z : ℂ => (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) /
              (z - z₀) ^ (divisorZeroIndex₀_fiberFinset (f := f) z₀).card)))
      z₀ := by
  rcases
      differentiableOn_update_limUnder_divisorCanonicalProduct_div_pow
        (m := m) (f := f) h_sum (z₀ := z₀) with ⟨r, hrpos, hdiff⟩
  let g : ℂ → ℂ :=
    Function.update
      (fun z : ℂ =>
        (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) /
          (z - z₀) ^ (divisorZeroIndex₀_fiberFinset (f := f) z₀).card)
      z₀
      (limUnder (𝓝[≠] z₀) fun z : ℂ =>
        (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) /
          (z - z₀) ^ (divisorZeroIndex₀_fiberFinset (f := f) z₀).card)
  have hcont : ContinuousAt g z₀ :=
    (hdiff.differentiableAt (Metric.ball_mem_nhds z₀ hrpos)).continuousAt
  have hd :
      ∀ᶠ z in 𝓝[≠] z₀, DifferentiableAt ℂ g z := by
    have hballWithin : Metric.ball z₀ r ∈ 𝓝[≠] z₀ := by
      refine mem_nhdsWithin_iff_exists_mem_nhds_inter.2 ?_
      refine ⟨Metric.ball z₀ r, Metric.ball_mem_nhds z₀ hrpos, ?_⟩
      intro z hz
      exact hz.1
    filter_upwards [hballWithin] with z hz
    exact (hdiff z hz).differentiableAt (Metric.isOpen_ball.mem_nhds hz)
  simpa [g] using Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt hd hcont

theorem exists_analyticAt_divisorCanonicalProduct_quotient
    (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1)))
    (z₀ : ℂ) :
    ∃ q : ℂ → ℂ,
      AnalyticAt ℂ q z₀ ∧
        q z₀ =
          limUnder (𝓝[≠] z₀) (fun z : ℂ =>
            (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) /
              (z - z₀) ^ (divisorZeroIndex₀_fiberFinset (f := f) z₀).card) ∧
        ∀ z : ℂ, z ≠ z₀ →
          q z =
            (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) /
              (z - z₀) ^ (divisorZeroIndex₀_fiberFinset (f := f) z₀).card := by
  let q : ℂ → ℂ :=
    Function.update
      (fun z : ℂ =>
        (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) /
          (z - z₀) ^ (divisorZeroIndex₀_fiberFinset (f := f) z₀).card)
      z₀
      (limUnder (𝓝[≠] z₀) fun z : ℂ =>
        (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) /
          (z - z₀) ^ (divisorZeroIndex₀_fiberFinset (f := f) z₀).card)
  refine ⟨q, ?_, ?_, ?_⟩
  · simpa [q] using
      analyticAt_update_limUnder_divisorCanonicalProduct_div_pow
        (m := m) (f := f) (h_sum := h_sum) (z₀ := z₀)
  · simp [q]
  · intro z hz
    simp [q, Function.update_of_ne hz]

theorem analyticOrderNatAt_divisorCanonicalProduct_eq_fiber_card
    (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1)))
    (z₀ : ℂ) :
    analyticOrderNatAt (divisorCanonicalProduct m f (Set.univ : Set ℂ)) z₀ =
      (divisorZeroIndex₀_fiberFinset (f := f) z₀).card := by
  set k : ℕ := (divisorZeroIndex₀_fiberFinset (f := f) z₀).card
  let F : ℂ → ℂ := divisorCanonicalProduct m f (Set.univ : Set ℂ)
  let q0 : ℂ → ℂ := fun z => F z / (z - z₀) ^ k
  rcases exists_analyticAt_divisorCanonicalProduct_quotient
      (m := m) (f := f) (h_sum := h_sum) (z₀ := z₀) with
    ⟨q, hqA, hq_self, hq_ne⟩
  have hdiff_univ : DifferentiableOn ℂ F (Set.univ : Set ℂ) :=
    differentiableOn_divisorCanonicalProduct_univ (m := m) (f := f) h_sum
  have han : AnalyticAt ℂ F z₀ := by
    refine (Complex.analyticAt_iff_eventually_differentiableAt).2 ?_
    refine Filter.Eventually.of_forall ?_
    intro z
    have : DifferentiableWithinAt ℂ F (Set.univ : Set ℂ) z := hdiff_univ z (by simp)
    exact this.differentiableAt (by simp)
  rcases
      exists_ball_eq_divisorCanonicalProduct_div_pow_eq (m := m) (f := f) (h_sum := h_sum)
      (z₀ := z₀)
    with ⟨ε, hε, u, huA, hu0, hEq⟩
  let g : ℂ → ℂ := fun z => (divisorComplementCanonicalProduct m f z₀ z) * u z
  have hcompDiff : DifferentiableOn ℂ (divisorComplementCanonicalProduct m f z₀)
      (Set.univ : Set ℂ) :=
    differentiableOn_divisorComplementCanonicalProduct_univ (m := m) (f := f) (z₀ := z₀) h_sum
  have hcompCont : ContinuousAt (divisorComplementCanonicalProduct m f z₀) z₀ :=
    (hcompDiff z₀ (by simp)).differentiableAt (by simp) |>.continuousAt
  have hgCont : ContinuousAt g z₀ := (hcompCont.mul huA.continuousAt)
  have hg0 : g z₀ ≠ 0 := by
    have hcomp0 : divisorComplementCanonicalProduct m f z₀ z₀ ≠ 0 :=
      divisorComplementCanonicalProduct_ne_zero_at (m := m) (f := f) (z₀ := z₀) h_sum
    exact mul_ne_zero hcomp0 hu0
  have hne_mem : ∀ᶠ z in 𝓝[≠] z₀, z ∈ (({z₀} : Set ℂ)ᶜ) :=
    Filter.eventually_of_mem
      (self_mem_nhdsWithin : (({z₀} : Set ℂ)ᶜ) ∈ 𝓝[≠] z₀) (fun _ hz => hz)
  have hne : ∀ᶠ z in 𝓝[≠] z₀, z ≠ z₀ := by
    filter_upwards [hne_mem] with z hz
    simpa [Set.mem_compl_singleton_iff] using hz
  have ht_q0 : Tendsto q0 (𝓝[≠] z₀) (𝓝 (g z₀)) := by
    have hball : ∀ᶠ z in 𝓝[≠] z₀, z ∈ Metric.ball z₀ ε :=
      Filter.eventually_of_mem
        (mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds z₀ hε)) (fun _ hz => hz)
    have heq : q0 =ᶠ[𝓝[≠] z₀] g := by
      filter_upwards [hball, hne] with z hz hzne
      have hq := hEq z hz hzne
      simpa [q0, F, k, g, smul_eq_mul] using hq
    exact (hgCont.continuousWithinAt.tendsto.congr' heq.symm)
  have hlim : limUnder (𝓝[≠] z₀) q0 = g z₀ := ht_q0.limUnder_eq
  have hq0 : q z₀ ≠ 0 := by
    have hq_self' : q z₀ = limUnder (𝓝[≠] z₀) q0 := by
      simpa [q0, F, k] using hq_self
    have : q z₀ = g z₀ := hq_self'.trans hlim
    exact this.symm ▸ hg0
  have heq_punct : (fun z : ℂ => F z) =ᶠ[𝓝[≠] z₀] fun z : ℂ => (z - z₀) ^ k • q z := by
    filter_upwards [hne] with z hz
    have hzpow : (z - z₀) ^ k ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hz)
    have hq : q z = q0 z := by simpa [q0, F, k] using hq_ne z hz
    have hmul : (z - z₀) ^ k * q0 z = F z := by
      calc
        (z - z₀) ^ k * q0 z
            = (((z - z₀) ^ k) * F z) / ((z - z₀) ^ k) := by
                simp [q0, div_eq_mul_inv, mul_assoc]
        _ = F z := by
              simpa [mul_assoc] using (mul_div_cancel_left₀ (F z) hzpow)
    have : F z = (z - z₀) ^ k * q z := by
      calc
        F z = (z - z₀) ^ k * q0 z := hmul.symm
        _ = (z - z₀) ^ k * q z := by simp [hq]
    simpa [smul_eq_mul] using this
  have hcontF : ContinuousAt F z₀ :=
    (hdiff_univ z₀ (by simp)).differentiableAt (by simp) |>.continuousAt
  have hcontq : ContinuousAt q z₀ := hqA.continuousAt
  have h_at_z0 : F z₀ = (z₀ - z₀) ^ k • q z₀ := by
    have ht1 : Tendsto F (𝓝[≠] z₀) (𝓝 (F z₀)) := hcontF.continuousWithinAt.tendsto
    have hpow :
        Tendsto (fun z : ℂ => (z - z₀) ^ k) (𝓝[≠] z₀) (𝓝 ((z₀ - z₀) ^ k)) :=
      ((continuousAt_id.sub continuousAt_const).pow k).continuousWithinAt.tendsto
    have ht2 :
        Tendsto (fun z : ℂ => (z - z₀) ^ k • q z) (𝓝[≠] z₀)
          (𝓝 ((z₀ - z₀) ^ k • q z₀)) :=
      hpow.mul (hcontq.continuousWithinAt.tendsto)
    have ht2' : Tendsto F (𝓝[≠] z₀) (𝓝 ((z₀ - z₀) ^ k • q z₀)) :=
      ht2.congr' heq_punct.symm
    exact tendsto_nhds_unique ht1 ht2'
  have hfac : ∀ᶠ z in 𝓝 z₀, F z = (z - z₀) ^ k • q z := by
    have hball1 : Metric.ball z₀ 1 ∈ 𝓝 z₀ := Metric.ball_mem_nhds z₀ (by norm_num)
    have hball1' : ∀ᶠ z in 𝓝 z₀, z ∈ Metric.ball z₀ 1 :=
      Filter.eventually_of_mem hball1 (fun _ hz => hz)
    filter_upwards [hball1'] with z _hz
    by_cases hz0 : z = z₀
    · subst hz0
      simpa using h_at_z0
    · have hzpow : (z - z₀) ^ k ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hz0)
      have hq : q z = q0 z := by simpa [q0, F, k] using hq_ne z hz0
      have hmul : (z - z₀) ^ k * q0 z = F z := by
        calc
          (z - z₀) ^ k * q0 z
              = (((z - z₀) ^ k) * F z) / ((z - z₀) ^ k) := by
                  simp [q0, div_eq_mul_inv, mul_assoc]
          _ = F z := by
                simpa [mul_assoc] using (mul_div_cancel_left₀ (F z) hzpow)
      have : F z = (z - z₀) ^ k * q z := by
        calc
          F z = (z - z₀) ^ k * q0 z := hmul.symm
          _ = (z - z₀) ^ k * q z := by simp [hq]
      simpa [smul_eq_mul] using this
  have hk' : analyticOrderAt F z₀ = k :=
    (han.analyticOrderAt_eq_natCast (n := k)).2 ⟨q, hqA, hq0, hfac⟩
  have hkNat : analyticOrderNatAt F z₀ = k := by
    simp [analyticOrderNatAt, hk']
  simpa [F, k] using hkNat

theorem analyticOrderNatAt_divisorCanonicalProduct_eq_analyticOrderNatAt
    (m : ℕ) {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1)))
    {z₀ : ℂ} (hz₀ : z₀ ≠ 0) :
    analyticOrderNatAt (divisorCanonicalProduct m f (Set.univ : Set ℂ)) z₀ =
      analyticOrderNatAt f z₀ := by
  have hcp :
      analyticOrderNatAt (divisorCanonicalProduct m f (Set.univ : Set ℂ)) z₀ =
        (divisorZeroIndex₀_fiberFinset (f := f) z₀).card :=
    analyticOrderNatAt_divisorCanonicalProduct_eq_fiber_card (m := m) (f := f) (h_sum := h_sum)
      (z₀ := z₀)
  have hfib :
      (divisorZeroIndex₀_fiberFinset (f := f) z₀).card = analyticOrderNatAt f z₀ :=
    divisorZeroIndex₀_fiberFinset_card_eq_analyticOrderNatAt (hf := hf) (z₀ := z₀) hz₀
  simpa [hfib] using hcp

end Complex.Hadamard
end
end File18

-- Upstream module PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.Divisor
section File19
 

section
namespace Complex.Hadamard

open scoped Topology
open Set

lemma analyticOrderAt_ne_top_of_exists_ne_zero {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hnot : ∃ z : ℂ, f z ≠ 0) :
    ∀ z : ℂ, analyticOrderAt f z ≠ ⊤ := by
  rcases hnot with ⟨z1, hz1⟩
  have hf_an : AnalyticOnNhd ℂ f (Set.univ : Set ℂ) := by
    intro z hz
    exact (Differentiable.analyticAt (f := f) hf z)
  have hz1_not_top : analyticOrderAt f z1 ≠ ⊤ := by
    have : analyticOrderAt f z1 = 0 :=
      (hf.analyticAt z1).analyticOrderAt_eq_zero.2 hz1
    simp [this]
  intro z
  exact AnalyticOnNhd.analyticOrderAt_ne_top_of_isPreconnected (hf := hf_an)
    (U := (Set.univ : Set ℂ)) (x := z1) (y := z) (by simpa using isPreconnected_univ)
    (by simp) (by simp) hz1_not_top

lemma no_zero_on_sphere_of_forall_val_norm_ne
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hnot : ∃ z : ℂ, f z ≠ 0)
    {B r : ℝ} (hrpos : 0 < r) (hBr : r ≤ B) (hr_not : ∀ p : divisorZeroIndex₀ f (Set.univ : Set ℂ),
      ‖divisorZeroIndex₀_val p‖ ≤ B → r ≠ ‖divisorZeroIndex₀_val p‖) :
    ∀ u : ℂ, ‖u‖ = r → f u ≠ 0 := by
  intro u hur
  have hu0 : u ≠ 0 := by
    intro hu0
    subst hu0
    have : (0 : ℝ) = r := by simpa using hur
    exact (ne_of_gt hrpos) this.symm
  intro hfu0
  have hnotTop : analyticOrderAt f u ≠ ⊤ :=
    analyticOrderAt_ne_top_of_exists_ne_zero (f := f) hf hnot u
  have hord_ne0 : analyticOrderNatAt f u ≠ 0 := by
    intro h0
    have hEN : (analyticOrderNatAt f u : ENat) = 0 := by simp [h0]
    have hAt0 : analyticOrderAt f u = 0 := by
      have hcast : (analyticOrderNatAt f u : ENat) = analyticOrderAt f u :=
        Nat.cast_analyticOrderNatAt (f := f) (z₀ := u) hnotTop
      simpa [hcast] using hEN
    have han : AnalyticAt ℂ f u := Differentiable.analyticAt (f := f) hf u
    exact ((han.analyticOrderAt_eq_zero).1 hAt0) hfu0
  have hcard_pos : 0 < (divisorZeroIndex₀_fiberFinset (f := f) u).card := by
    have hcard :=
      divisorZeroIndex₀_fiberFinset_card_eq_analyticOrderNatAt (hf := hf) (z₀ := u) hu0
    have : 0 < analyticOrderNatAt f u := Nat.pos_of_ne_zero hord_ne0
    simpa [hcard] using this
  rcases Finset.card_pos.mp hcard_pos with ⟨p, hp⟩
  have hpval : divisorZeroIndex₀_val p = u :=
    (mem_divisorZeroIndex₀_fiberFinset (f := f) (z₀ := u) p).1 hp
  have hpB : ‖divisorZeroIndex₀_val p‖ ≤ B := by
    have : ‖divisorZeroIndex₀_val p‖ = r := by simp [hpval, hur]
    simpa [this] using hBr
  have : r ≠ ‖divisorZeroIndex₀_val p‖ := hr_not p hpB
  exact this (by simp [hpval, hur])

theorem divisorCanonicalProduct_eq_zero_of_exists
    (m : ℕ) (f : ℂ → ℂ) (z : ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1)))
    (h0 : ∃ p : divisorZeroIndex₀ f (Set.univ : Set ℂ),
      weierstrassFactor m (z / divisorZeroIndex₀_val p) = 0) :
    divisorCanonicalProduct m f (Set.univ : Set ℂ) z = 0 := by
  have hloc :
      HasProdLocallyUniformlyOn
        (fun (p : divisorZeroIndex₀ f (Set.univ : Set ℂ)) (w : ℂ) =>
          weierstrassFactor m (w / divisorZeroIndex₀_val p))
        (divisorCanonicalProduct m f (Set.univ : Set ℂ))
        (Set.univ : Set ℂ) :=
    hasProdLocallyUniformlyOn_divisorCanonicalProduct_univ (m := m) (f := f) h_sum
  have hprod :
      HasProd (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
          weierstrassFactor m (z / divisorZeroIndex₀_val p))
        (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) :=
    hloc.hasProd (by simp : z ∈ (Set.univ : Set ℂ))
  have hzero :
      HasProd (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
          weierstrassFactor m (z / divisorZeroIndex₀_val p))
        0 := by
    refine hasProd_zero_of_exists_eq_zero (L := (SummationFilter.unconditional
      (divisorZeroIndex₀ f (Set.univ : Set ℂ)))) ?_
    rcases h0 with ⟨p, hp⟩
    exact ⟨p, hp⟩
  exact (hprod.unique hzero)

theorem divisorCanonicalProduct_eq_zero_at_index
    (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1)))
    (p : divisorZeroIndex₀ f (Set.univ : Set ℂ)) :
    divisorCanonicalProduct m f (Set.univ : Set ℂ) (divisorZeroIndex₀_val p) = 0 := by
  refine divisorCanonicalProduct_eq_zero_of_exists (m := m) (f := f)
    (z := divisorZeroIndex₀_val p) h_sum ?_
  refine ⟨p, ?_⟩
  have hp0 : divisorZeroIndex₀_val p ≠ 0 := p.property
  simp [weierstrassFactor_at_one]

theorem analyticOrderAt_prod_fiberFinset
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ) :
    analyticOrderAt (fun z : ℂ => ∏ p ∈ divisorZeroIndex₀_fiberFinset (f := f) z₀,
            weierstrassFactor m (z / divisorZeroIndex₀_val p))
      z₀ = ((divisorZeroIndex₀_fiberFinset (f := f) z₀).card : ℕ∞) := by
  have h :=
    analyticOrderAt_finset_prod_weierstrassFactor_divisorZeroIndex₀
      (m := m) (f := f) (s := divisorZeroIndex₀_fiberFinset (f := f) z₀) (z₀ := z₀)
  have hfilter :
      (divisorZeroIndex₀_fiberFinset (f := f) z₀).filter (fun p => divisorZeroIndex₀_val p = z₀) =
        divisorZeroIndex₀_fiberFinset (f := f) z₀ := by
    ext p; simp
  simpa [hfilter] using h

theorem analyticOrderNatAt_prod_fiberFinset
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ) : analyticOrderNatAt (fun z : ℂ =>
          ∏ p ∈ divisorZeroIndex₀_fiberFinset (f := f) z₀,
            weierstrassFactor m (z / divisorZeroIndex₀_val p)) z₀ =
      (divisorZeroIndex₀_fiberFinset (f := f) z₀).card := by
  simpa [analyticOrderNatAt] using
    congrArg ENat.toNat (analyticOrderAt_prod_fiberFinset (m := m) (f := f) (z₀ := z₀))

theorem analyticOrderAt_divisorCanonicalProduct_eq_fiber_card
    (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1)))
    (z₀ : ℂ) :
    analyticOrderAt (divisorCanonicalProduct m f (Set.univ : Set ℂ)) z₀ =
      ((divisorZeroIndex₀_fiberFinset (f := f) z₀).card : ℕ∞) := by
  let F : ℂ → ℂ := divisorCanonicalProduct m f (Set.univ : Set ℂ)
  have hNat :
      analyticOrderNatAt F z₀ = (divisorZeroIndex₀_fiberFinset (f := f) z₀).card := by
    simpa [F] using
      (analyticOrderNatAt_divisorCanonicalProduct_eq_fiber_card
        (m := m) (f := f) (h_sum := h_sum) (z₀ := z₀))
  have hdiffOn : DifferentiableOn ℂ F (Set.univ : Set ℂ) := by
    simpa [F] using differentiableOn_divisorCanonicalProduct_univ (m := m) (f := f) h_sum
  have hdiff : Differentiable ℂ F := by
    intro z
    exact (hdiffOn z (by simp)).differentiableAt (by simp)
  have hnotTop : analyticOrderAt F z₀ ≠ ⊤ :=
    analyticOrderAt_ne_top_of_exists_ne_zero (hf := hdiff)
      ⟨0, by simp [F, divisorCanonicalProduct_zero]⟩ z₀
  have hcast : (analyticOrderNatAt F z₀ : ℕ∞) = analyticOrderAt F z₀ :=
    Nat.cast_analyticOrderNatAt (f := F) (z₀ := z₀) hnotTop
  have hNatCast :
      (analyticOrderNatAt F z₀ : ℕ∞) =
        ((divisorZeroIndex₀_fiberFinset (f := f) z₀).card : ℕ∞) := by
    simp [hNat]
  simpa [F, hcast] using hNatCast

theorem divisorCanonicalProduct_ne_zero_of_forall_ne
    (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1)))
    {z : ℂ} (hz : ∀ p : divisorZeroIndex₀ f (Set.univ : Set ℂ), z ≠ divisorZeroIndex₀_val p) :
    divisorCanonicalProduct m f (Set.univ : Set ℂ) z ≠ 0 := by
  let F : ℂ → ℂ := divisorCanonicalProduct m f (Set.univ : Set ℂ)
  have hfiber_empty : divisorZeroIndex₀_fiberFinset (f := f) z = ∅ := by
    ext p
    constructor
    · intro hp
      exact False.elim (hz p ((mem_divisorZeroIndex₀_fiberFinset (f := f) (z₀ := z) p).1 hp).symm)
    · intro hp
      simp at hp
  have horder :
      analyticOrderAt F z = (0 : ℕ∞) := by
    have h :=
      analyticOrderAt_divisorCanonicalProduct_eq_fiber_card
        (m := m) (f := f) (h_sum := h_sum) (z₀ := z)
    simpa [F, hfiber_empty] using h
  have han : AnalyticAt ℂ F z := by
    refine (Complex.analyticAt_iff_eventually_differentiableAt).2 ?_
    refine Filter.Eventually.of_forall ?_
    intro w
    exact (((differentiableOn_divisorCanonicalProduct_univ m f h_sum) w
      (by simp)).differentiableAt (by simp))
  exact (han.analyticOrderAt_eq_zero).1 horder

theorem logDeriv_divisorCanonicalProduct_one_eq_tsum_of_forall_ne
    {f : ℂ → ℂ} {z : ℂ}
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (2 : ℕ)))
    (hz : ∀ p : divisorZeroIndex₀ f (Set.univ : Set ℂ), z ≠ divisorZeroIndex₀_val p) :
    logDeriv (divisorCanonicalProduct 1 f (Set.univ : Set ℂ)) z =
      ∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ),
        (1 / (z - divisorZeroIndex₀_val p) + 1 / divisorZeroIndex₀_val p) :=
  logDeriv_divisorCanonicalProduct_one_eq_tsum h_sum hz
    (divisorCanonicalProduct_ne_zero_of_forall_ne 1 f h_sum hz)

theorem analyticOrderAt_divisorCanonicalProduct_at_index
    (m : ℕ) {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1)))
    (p : divisorZeroIndex₀ f (Set.univ : Set ℂ)) :
    analyticOrderAt (divisorCanonicalProduct m f (Set.univ : Set ℂ)) (divisorZeroIndex₀_val p) =
      (analyticOrderNatAt f (divisorZeroIndex₀_val p) : ℕ∞) := by
  have horder :=
    analyticOrderAt_divisorCanonicalProduct_eq_fiber_card
      (m := m) (f := f) (h_sum := h_sum) (z₀ := divisorZeroIndex₀_val p)
  have hfiber :
      (divisorZeroIndex₀_fiberFinset (f := f) (divisorZeroIndex₀_val p)).card =
        analyticOrderNatAt f (divisorZeroIndex₀_val p) :=
    divisorZeroIndex₀_fiberFinset_card_eq_analyticOrderNatAt
      (hf := hf) (z₀ := divisorZeroIndex₀_val p) p.property
  simpa [hfiber] using horder

theorem eventually_exists_analyticAt_eq_pow_smul_divisorComplementPartialProduct
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ) :
    ∀ᶠ s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) in (Filter.atTop : Filter _),
      ∃ u : ℂ → ℂ, AnalyticAt ℂ u z₀ ∧ u z₀ ≠ 0 ∧ (fun z : ℂ => divisorPartialProduct m f s z)
        =ᶠ[𝓝 z₀] fun z : ℂ => (z - z₀) ^ (divisorZeroIndex₀_fiberFinset (f := f) z₀).card •
          (divisorComplementPartialProduct m f z₀ s z * u z) := by
  let fiber : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) :=
    divisorZeroIndex₀_fiberFinset (f := f) z₀
  have hfib : ∃ u : ℂ → ℂ, AnalyticAt ℂ u z₀ ∧ u z₀ ≠ 0 ∧ (fun z : ℂ =>
      divisorPartialProduct m f fiber z) =ᶠ[𝓝 z₀] fun z : ℂ => (z - z₀) ^ fiber.card • u z := by
    simpa [fiber, divisorPartialProduct] using
      (exists_analyticAt_eq_pow_smul_of_partialProduct_contains_fiber (m := m) (f := f) (z₀ := z₀)
        (s := fiber) (by rfl : fiber ⊆ fiber))
  rcases hfib with ⟨u, huA, hu0, huEq⟩
  refine (eventually_atTop_subset_fiberFinset (f := f) z₀).mono ?_
  intro s hs
  refine ⟨u, huA, hu0, ?_⟩
  have hmul : ∀ z : ℂ, divisorPartialProduct m f s z =
        divisorPartialProduct m f fiber z * divisorComplementPartialProduct m f z₀ s z := by
    intro z
    simpa [fiber] using
      (divisorPartialProduct_eq_fiber_mul_complement_of_subset (m := m) (f := f) (z₀ := z₀)
        (z := z) (s := s) hs)
  have hmul_ev : (fun z : ℂ => divisorPartialProduct m f s z) =ᶠ[𝓝 z₀] fun z : ℂ =>
      ((z - z₀) ^ fiber.card • u z) * divisorComplementPartialProduct m f z₀ s z := by
    filter_upwards [huEq] with z hz
    have hsplit_z : divisorPartialProduct m f s z =
          divisorPartialProduct m f fiber z * divisorComplementPartialProduct m f z₀ s z :=
      hmul z
    calc
      divisorPartialProduct m f s z = divisorPartialProduct m f fiber z *
        divisorComplementPartialProduct m f z₀ s z := hsplit_z
      _ = (((z - z₀) ^ fiber.card • u z) * divisorComplementPartialProduct m f z₀ s z) := by
            simpa [mul_assoc] using congrArg (fun t => t *
              divisorComplementPartialProduct m f z₀ s z) hz
  filter_upwards [hmul_ev] with z hz
  simpa [smul_eq_mul, mul_assoc, mul_left_comm, mul_comm, fiber] using hz

lemma divisorPartialProduct_ne_zero_on_ball_punctured
    (m : ℕ) {f : ℂ → ℂ} {z₀ : ℂ} {ε : ℝ}
    (hball :
      Metric.ball z₀ ε ∩ (MeromorphicOn.divisor f (Set.univ : Set ℂ)).support = {z₀})
    (s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ))) :
    ∀ z ∈ Metric.ball z₀ ε, z ≠ z₀ → divisorPartialProduct m f s z ≠ 0 := by
  intro z hz hz0
  have hfac :
      ∀ p ∈ s, weierstrassFactor m (z / divisorZeroIndex₀_val p) ≠ 0 := by
    intro p hp
    exact weierstrassFactor_div_ne_zero_on_ball_punctured
      (m := m) (f := f) (z₀ := z₀) (ε := ε) hball z hz hz0 p
  simpa [divisorPartialProduct, Finset.prod_ne_zero_iff] using hfac

end Complex.Hadamard
end
end File19

-- Upstream module PrimeNumberTheoremAnd.Mathlib.Topology.MetricSpace.Annulus
section File20
 

section
open Set

open scoped ENNReal

namespace Metric

variable {X : Type*} [PseudoMetricSpace X]

def annulusIoo (x : X) (r R : ℝ) : Set X := (fun y : X ↦ dist y x) ⁻¹' Ioo r R

def annulusIoc (x : X) (r R : ℝ) : Set X := (fun y : X ↦ dist y x) ⁻¹' Ioc r R

def annulusIco (x : X) (r R : ℝ) : Set X := (fun y : X ↦ dist y x) ⁻¹' Ico r R

def annulusIcc (x : X) (r R : ℝ) : Set X := (fun y : X ↦ dist y x) ⁻¹' Icc r R

def annulusIoi (x : X) (r : ℝ) : Set X := (fun y : X ↦ dist y x) ⁻¹' Ioi r

def annulusIci (x : X) (r : ℝ) : Set X := (fun y : X ↦ dist y x) ⁻¹' Ici r

variable {x : X} {r R : ℝ}

lemma annulusIoo_eq :
    annulusIoo x r R = ball x R ∩ (closedBall x r)ᶜ := by
  ext; simp [annulusIoo, ball, closedBall, and_comm]

lemma annulusIoc_eq {x : X} {r R : ℝ} :
    annulusIoc x r R = closedBall x R ∩ (closedBall x r)ᶜ := by
  ext; simp [annulusIoc, closedBall, and_comm]

lemma annulusIco_eq {x : X} {r R : ℝ} :
    annulusIco x r R = ball x R ∩ (ball x r)ᶜ := by
  ext; simp [annulusIco, ball, and_comm]

lemma annulusIcc_eq {x : X} {r R : ℝ} :
    annulusIcc x r R = closedBall x R ∩ (ball x r)ᶜ := by
  ext; simp [annulusIcc, ball, closedBall, and_comm]

lemma annulusIoi_eq {x : X} {r : ℝ} : annulusIoi x r = (closedBall x r)ᶜ := by
  ext; simp [annulusIoi, closedBall]

lemma annulusIci_eq {x : X} {r : ℝ} : annulusIci x r = (ball x r)ᶜ := by
  ext; simp [annulusIci, ball]

@[simp] lemma annulusIoo_eq_empty {x : X} {r R : ℝ} (h : R ≤ r) : annulusIoo x r R = ∅ := by
  simp [annulusIoo, Ioo_eq_empty_of_le h]

@[simp] lemma annulusIoc_eq_empty {x : X} {r R : ℝ} (h : R ≤ r) : annulusIoc x r R = ∅ := by
  simp [annulusIoc, Ioc_eq_empty_of_le h]

@[simp] lemma annulusIco_eq_empty {x : X} {r R : ℝ} (h : R ≤ r) : annulusIco x r R = ∅ := by
  simp [annulusIco, Ico_eq_empty_of_le h]

@[simp] lemma annulusIcc_eq_empty {x : X} {r R : ℝ} (h : R < r) : annulusIcc x r R = ∅ := by
  simp [annulusIcc, Icc_eq_empty_of_lt h]

lemma annulusIoo_mono {x : X} {r₁ R₁ r₂ R₂ : ℝ} (hr : r₂ ≤ r₁) (hR : R₁ ≤ R₂) :
    annulusIoo x r₁ R₁ ⊆ annulusIoo x r₂ R₂ := by
  intro y hy
  exact ⟨lt_of_le_of_lt hr hy.1, lt_of_lt_of_le hy.2 hR⟩

lemma annulusIoc_mono {x : X} {r₁ R₁ r₂ R₂ : ℝ} (hr : r₂ ≤ r₁) (hR : R₁ ≤ R₂) :
    annulusIoc x r₁ R₁ ⊆ annulusIoc x r₂ R₂ := by
  intro y hy
  exact ⟨lt_of_le_of_lt hr hy.1, hy.2.trans hR⟩

lemma annulusIco_mono {x : X} {r₁ R₁ r₂ R₂ : ℝ} (hr : r₂ ≤ r₁) (hR : R₁ ≤ R₂) :
    annulusIco x r₁ R₁ ⊆ annulusIco x r₂ R₂ := by
  intro y hy
  exact ⟨hr.trans hy.1, lt_of_lt_of_le hy.2 hR⟩

lemma annulusIcc_mono {x : X} {r₁ R₁ r₂ R₂ : ℝ} (hr : r₂ ≤ r₁) (hR : R₁ ≤ R₂) :
    annulusIcc x r₁ R₁ ⊆ annulusIcc x r₂ R₂ := by
  intro y hy
  exact ⟨hr.trans hy.1, hy.2.trans hR⟩

lemma annulusIoo_subset_ball {x : X} {r R : ℝ} : annulusIoo x r R ⊆ ball x R := by
  intro y hy
  exact Metric.mem_ball.2 hy.2

lemma annulusIoc_subset_closedBall {x : X} {r R : ℝ} : annulusIoc x r R ⊆ closedBall x R := by
  intro y hy
  exact Metric.mem_closedBall.2 hy.2

lemma annulusIco_subset_ball {x : X} {r R : ℝ} : annulusIco x r R ⊆ ball x R := by
  intro y hy
  exact Metric.mem_ball.2 hy.2

lemma annulusIcc_subset_closedBall {x : X} {r R : ℝ} : annulusIcc x r R ⊆ closedBall x R := by
  intro y hy
  exact Metric.mem_closedBall.2 hy.2

@[simp]
lemma annulusIoc_union_annulusIoo {x : X} {r r' R : ℝ} (h₁ : r ≤ r') (h₂ : r' < R) :
    annulusIoc x r r' ∪ annulusIoo x r' R = annulusIoo x r R := by
  simpa [annulusIoc, annulusIoo, preimage_union] using
    congrArg (fun s : Set ℝ ↦ (fun y : X ↦ dist y x) ⁻¹' s) (Ioc_union_Ioo_eq_Ioo h₁ h₂)

@[simp]
lemma annulusIoc_union_annulusIoc {x : X} {r r' R : ℝ} (h₁ : r ≤ r') (h₂ : r' ≤ R) :
    annulusIoc x r r' ∪ annulusIoc x r' R = annulusIoc x r R := by
  simpa [annulusIoc, preimage_union] using
    congrArg (fun s : Set ℝ ↦ (fun y : X ↦ dist y x) ⁻¹' s) (Ioc_union_Ioc_eq_Ioc h₁ h₂)

@[simp]
lemma annulusIoo_union_annulusIco {x : X} {r r' R : ℝ} (h₁ : r < r') (h₂ : r' ≤ R) :
    annulusIoo x r r' ∪ annulusIco x r' R = annulusIoo x r R := by
  simpa [annulusIoo, annulusIco, preimage_union] using
    congrArg (fun s : Set ℝ ↦ (fun y : X ↦ dist y x) ⁻¹' s) (Ioo_union_Ico_eq_Ioo h₁ h₂)

@[simp]
lemma annulusIoo_union_annulusIcc {x : X} {r r' R : ℝ} (h₁ : r < r') (h₂ : r' ≤ R) :
    annulusIoo x r r' ∪ annulusIcc x r' R = annulusIoc x r R := by
  simpa [annulusIoo, annulusIcc, annulusIoc, preimage_union] using
    congrArg (fun s : Set ℝ ↦ (fun y : X ↦ dist y x) ⁻¹' s) (Ioo_union_Icc_eq_Ioc h₁ h₂)

@[simp]
lemma annulusIcc_union_annulusIoo {x : X} {r r' R : ℝ} (h₁ : r ≤ r') (h₂ : r' < R) :
    annulusIcc x r r' ∪ annulusIoo x r' R = annulusIco x r R := by
  simpa [annulusIcc, annulusIoo, annulusIco, preimage_union] using
    congrArg (fun s : Set ℝ ↦ (fun y : X ↦ dist y x) ⁻¹' s) (Icc_union_Ioo_eq_Ico h₁ h₂)

@[simp]
lemma annulusIcc_union_annulusIoc {x : X} {r r' R : ℝ} (h₁ : r ≤ r') (h₂ : r' ≤ R) :
    annulusIcc x r r' ∪ annulusIoc x r' R = annulusIcc x r R := by
  simpa [annulusIcc, annulusIoc, preimage_union] using
    congrArg (fun s : Set ℝ ↦ (fun y : X ↦ dist y x) ⁻¹' s) (Icc_union_Ioc_eq_Icc h₁ h₂)

@[simp]
lemma annulusIco_union_annulusIco {x : X} {r r' R : ℝ} (h₁ : r ≤ r') (h₂ : r' ≤ R) :
    annulusIco x r r' ∪ annulusIco x r' R = annulusIco x r R := by
  simpa [annulusIco, preimage_union] using
    congrArg (fun s : Set ℝ ↦ (fun y : X ↦ dist y x) ⁻¹' s) (Ico_union_Ico_eq_Ico h₁ h₂)

@[simp]
lemma annulusIco_union_annulusIcc {x : X} {r r' R : ℝ} (h₁ : r ≤ r') (h₂ : r' ≤ R) :
    annulusIco x r r' ∪ annulusIcc x r' R = annulusIcc x r R := by
  simpa [annulusIco, annulusIcc, preimage_union] using
    congrArg (fun s : Set ℝ ↦ (fun y : X ↦ dist y x) ⁻¹' s) (Ico_union_Icc_eq_Icc h₁ h₂)

@[simp]
lemma annulusIoc_union_annulusIoi {x : X} {r R : ℝ} (h : r ≤ R) :
    annulusIoc x r R ∪ annulusIoi x R = annulusIoi x r := by
  simpa [annulusIoc, annulusIoi, preimage_union] using
    congrArg (fun s : Set ℝ ↦ (fun y : X ↦ dist y x) ⁻¹' s) (Ioc_union_Ioi_eq_Ioi h)

@[simp]
lemma annulusIoo_union_annulusIci {x : X} {r R : ℝ} (h : r < R) :
    annulusIoo x r R ∪ annulusIci x R = annulusIoi x r := by
  simpa [annulusIoo, annulusIci, annulusIoi, preimage_union] using
    congrArg (fun s : Set ℝ ↦ (fun y : X ↦ dist y x) ⁻¹' s) (Ioo_union_Ici_eq_Ioi h)

@[simp]
lemma annulusIcc_union_annulusIoi {x : X} {r R : ℝ} (h : r ≤ R) :
    annulusIcc x r R ∪ annulusIoi x R = annulusIci x r := by
  simpa [annulusIcc, annulusIoi, annulusIci, preimage_union] using
    congrArg (fun s : Set ℝ ↦ (fun y : X ↦ dist y x) ⁻¹' s) (Icc_union_Ioi_eq_Ici h)

@[simp]
lemma annulusIco_union_annulusIci {x : X} {r R : ℝ} (h : r ≤ R) :
    annulusIco x r R ∪ annulusIci x R = annulusIci x r := by
  simpa [annulusIco, annulusIci, preimage_union] using
    congrArg (fun s : Set ℝ ↦ (fun y : X ↦ dist y x) ⁻¹' s) (Ico_union_Ici_eq_Ici h)

theorem iUnion_annulusIco_eq_annulusIci {x : X} {f : ℕ → ℝ} (hf : ∀ n, f 0 ≤ f n)
    (h2f : ¬BddAbove (range f)) :
    (⋃ n : ℕ, annulusIco x (f n) (f (Nat.succ n))) = annulusIci x (f 0) := by
  simpa [annulusIco, annulusIci] using
    congrArg (fun s : Set ℝ ↦ (fun y : X ↦ dist y x) ⁻¹' s)
      (iUnion_Ico_map_succ_eq_Ici (β := ℝ) hf h2f)

theorem iUnion_annulusIoc_eq_annulusIoi {x : X} {f : ℕ → ℝ} (hf : ∀ n, f 0 ≤ f n)
    (h2f : ¬BddAbove (range f)) :
    (⋃ n : ℕ, annulusIoc x (f n) (f (Nat.succ n))) = annulusIoi x (f 0) := by
  simpa [annulusIoc, annulusIoi] using
    congrArg (fun s : Set ℝ ↦ (fun y : X ↦ dist y x) ⁻¹' s)
      (iUnion_Ioc_map_succ_eq_Ioi (β := ℝ) hf h2f)

open scoped Function 

variable {ι : Type*} [LinearOrder ι] [SuccOrder ι]

theorem pairwise_disjoint_on_annulusIco_succ {x : X} {f : ι → ℝ} (hf : Monotone f) :
    Pairwise (Disjoint on fun i : ι => annulusIco x (f i) (f (Order.succ i))) := by
  intro i j hij
  have h' :
      Disjoint (Ico (f i) (f (Order.succ i))) (Ico (f j) (f (Order.succ j))) :=
    (hf.pairwise_disjoint_on_Ico_succ) hij
  simpa [annulusIco] using Disjoint.preimage (fun y : X => dist y x) h'

theorem pairwise_disjoint_on_annulusIoc_succ {x : X} {f : ι → ℝ} (hf : Monotone f) :
    Pairwise (Disjoint on fun i : ι => annulusIoc x (f i) (f (Order.succ i))) := by
  intro i j hij
  have h' :
      Disjoint (Ioc (f i) (f (Order.succ i))) (Ioc (f j) (f (Order.succ j))) :=
    (hf.pairwise_disjoint_on_Ioc_succ) hij
  simpa [annulusIoc] using Disjoint.preimage (fun y : X => dist y x) h'

theorem pairwise_disjoint_on_annulusIoo_succ {x : X} {f : ι → ℝ} (hf : Monotone f) :
    Pairwise (Disjoint on fun i : ι => annulusIoo x (f i) (f (Order.succ i))) := by
  intro i j hij
  have h' :
      Disjoint (Ioo (f i) (f (Order.succ i))) (Ioo (f j) (f (Order.succ j))) :=
    (hf.pairwise_disjoint_on_Ioo_succ) hij
  simpa [annulusIoo] using Disjoint.preimage (fun y : X => dist y x) h'

end Metric

namespace Metric

variable {X : Type*} [PseudoEMetricSpace X]

def eannulusIoo (x : X) (r R : ℝ≥0∞) : Set X := (fun y : X ↦ edist y x) ⁻¹' Ioo r R

def eannulusIoc (x : X) (r R : ℝ≥0∞) : Set X := (fun y : X ↦ edist y x) ⁻¹' Ioc r R

def eannulusIco (x : X) (r R : ℝ≥0∞) : Set X := (fun y : X ↦ edist y x) ⁻¹' Ico r R

def eannulusIcc (x : X) (r R : ℝ≥0∞) : Set X := (fun y : X ↦ edist y x) ⁻¹' Icc r R

def eannulusIoi (x : X) (r : ℝ≥0∞) : Set X := (fun y : X ↦ edist y x) ⁻¹' Ioi r

def eannulusIci (x : X) (r : ℝ≥0∞) : Set X := (fun y : X ↦ edist y x) ⁻¹' Ici r

@[simp] lemma eannulusIoo_eq_preimage (x : X) (r R : ℝ≥0∞) :
    eannulusIoo x r R = (fun y : X ↦ edist y x) ⁻¹' Ioo r R := rfl

@[simp] lemma eannulusIoc_eq_preimage (x : X) (r R : ℝ≥0∞) :
    eannulusIoc x r R = (fun y : X ↦ edist y x) ⁻¹' Ioc r R := rfl

@[simp] lemma eannulusIco_eq_preimage (x : X) (r R : ℝ≥0∞) :
    eannulusIco x r R = (fun y : X ↦ edist y x) ⁻¹' Ico r R := rfl

@[simp] lemma eannulusIcc_eq_preimage (x : X) (r R : ℝ≥0∞) :
    eannulusIcc x r R = (fun y : X ↦ edist y x) ⁻¹' Icc r R := rfl

@[simp] lemma eannulusIoi_eq_preimage (x : X) (r : ℝ≥0∞) :
    eannulusIoi x r = (fun y : X ↦ edist y x) ⁻¹' Ioi r := rfl

@[simp] lemma eannulusIci_eq_preimage (x : X) (r : ℝ≥0∞) :
    eannulusIci x r = (fun y : X ↦ edist y x) ⁻¹' Ici r := rfl

lemma eannulusIoo_eq_empty {x : X} {r R : ℝ≥0∞} (h : R ≤ r) : eannulusIoo x r R = ∅ := by
  simp [eannulusIoo, Ioo_eq_empty_of_le h]

lemma eannulusIoc_eq_empty {x : X} {r R : ℝ≥0∞} (h : R ≤ r) : eannulusIoc x r R = ∅ := by
  simp [eannulusIoc, Ioc_eq_empty_of_le h]

lemma eannulusIco_eq_empty {x : X} {r R : ℝ≥0∞} (h : R ≤ r) : eannulusIco x r R = ∅ := by
  simp [eannulusIco, Ico_eq_empty_of_le h]

lemma eannulusIcc_eq_empty {x : X} {r R : ℝ≥0∞} (h : R < r) : eannulusIcc x r R = ∅ := by
  simp [eannulusIcc, Icc_eq_empty_of_lt h]

lemma eannulusIoo_mono {x : X} {r₁ R₁ r₂ R₂ : ℝ≥0∞} (hr : r₂ ≤ r₁) (hR : R₁ ≤ R₂) :
    eannulusIoo x r₁ R₁ ⊆ eannulusIoo x r₂ R₂ := by
  intro y hy
  exact ⟨lt_of_le_of_lt hr hy.1, lt_of_lt_of_le hy.2 hR⟩

lemma eannulusIoc_mono {x : X} {r₁ R₁ r₂ R₂ : ℝ≥0∞} (hr : r₂ ≤ r₁) (hR : R₁ ≤ R₂) :
    eannulusIoc x r₁ R₁ ⊆ eannulusIoc x r₂ R₂ := by
  intro y hy; exact ⟨lt_of_le_of_lt hr hy.1, hy.2.trans hR⟩

lemma eannulusIco_mono {x : X} {r₁ R₁ r₂ R₂ : ℝ≥0∞} (hr : r₂ ≤ r₁) (hR : R₁ ≤ R₂) :
    eannulusIco x r₁ R₁ ⊆ eannulusIco x r₂ R₂ := by
  intro y hy; exact ⟨hr.trans hy.1, lt_of_lt_of_le hy.2 hR⟩

lemma eannulusIcc_mono {x : X} {r₁ R₁ r₂ R₂ : ℝ≥0∞} (hr : r₂ ≤ r₁) (hR : R₁ ≤ R₂) :
    eannulusIcc x r₁ R₁ ⊆ eannulusIcc x r₂ R₂ := by
  intro y hy; exact ⟨hr.trans hy.1, hy.2.trans hR⟩

open scoped Function 

variable {ι : Type*} [LinearOrder ι] [SuccOrder ι]

theorem pairwise_disjoint_on_eannulusIco_succ {x : X} {f : ι → ℝ≥0∞} (hf : Monotone f) :
    Pairwise (Disjoint on fun i : ι => eannulusIco x (f i) (f (Order.succ i))) := by
  intro i j hij
  have h' :
      Disjoint (Ico (f i) (f (Order.succ i))) (Ico (f j) (f (Order.succ j))) :=
    (hf.pairwise_disjoint_on_Ico_succ) hij
  simpa [eannulusIco] using Disjoint.preimage (fun y : X => edist y x) h'

theorem pairwise_disjoint_on_eannulusIoc_succ {x : X} {f : ι → ℝ≥0∞} (hf : Monotone f) :
    Pairwise (Disjoint on fun i : ι => eannulusIoc x (f i) (f (Order.succ i))) := by
  intro i j hij
  have h' :
      Disjoint (Ioc (f i) (f (Order.succ i))) (Ioc (f j) (f (Order.succ j))) :=
    (hf.pairwise_disjoint_on_Ioc_succ) hij
  simpa [eannulusIoc] using Disjoint.preimage (fun y : X => edist y x) h'

theorem pairwise_disjoint_on_eannulusIoo_succ {x : X} {f : ι → ℝ≥0∞} (hf : Monotone f) :
    Pairwise (Disjoint on fun i : ι => eannulusIoo x (f i) (f (Order.succ i))) := by
  intro i j hij
  have h' :
      Disjoint (Ioo (f i) (f (Order.succ i))) (Ioo (f j) (f (Order.succ j))) :=
    (hf.pairwise_disjoint_on_Ioo_succ) hij
  simpa [eannulusIoo] using Disjoint.preimage (fun y : X => edist y x) h'

end Metric

namespace Metric

variable {X : Type*} [PseudoMetricSpace X]
variable {x : X} {r R : ℝ}

lemma eannulusIoo_ofReal (hr : 0 ≤ r) :
    eannulusIoo x (ENNReal.ofReal r) (ENNReal.ofReal R) = annulusIoo x r R := by
  ext y
  simp [eannulusIoo, annulusIoo, edist_dist, mem_Ioo,
    ENNReal.ofReal_lt_ofReal_iff_of_nonneg hr,
    ENNReal.ofReal_lt_ofReal_iff_of_nonneg dist_nonneg]

lemma eannulusIoc_ofReal (hr : 0 ≤ r) :
    eannulusIoc x (ENNReal.ofReal r) (ENNReal.ofReal R) = annulusIoc x r R := by
  ext y
  constructor
  · intro hy
    have hy' :
        ENNReal.ofReal r < ENNReal.ofReal (dist y x) ∧
          ENNReal.ofReal (dist y x) ≤ ENNReal.ofReal R := by
      simpa [eannulusIoc, edist_dist, annulusIoc, mem_Ioc] using hy
    have hrd : r < dist y x :=
      (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hr).1 hy'.1
    have hpos : ¬dist y x ≤ 0 := not_le_of_gt (lt_of_le_of_lt hr hrd)
    have hle : dist y x ≤ R := by
      have hle' : dist y x ≤ R ∨ dist y x ≤ 0 :=
        (ENNReal.ofReal_le_ofReal_iff').1 hy'.2
      exact hle'.resolve_right hpos
    simp [annulusIoc, mem_Ioc, hrd, hle]
  · intro hy
    have hy' : r < dist y x ∧ dist y x ≤ R := by
      simpa [annulusIoc, mem_Ioc] using hy
    have : ENNReal.ofReal r < ENNReal.ofReal (dist y x) :=
      (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hr).2 hy'.1
    have : (ENNReal.ofReal r < ENNReal.ofReal (dist y x)) ∧
        (ENNReal.ofReal (dist y x) ≤ ENNReal.ofReal R) :=
      ⟨this, ENNReal.ofReal_le_ofReal hy'.2⟩
    simpa [eannulusIoc, edist_dist, annulusIoc, mem_Ioc] using this

lemma eannulusIco_ofReal :
    eannulusIco x (ENNReal.ofReal r) (ENNReal.ofReal R) = annulusIco x r R := by
  ext y
  simp [eannulusIco, annulusIco, edist_dist, mem_Ico,
    ENNReal.ofReal_le_ofReal_iff dist_nonneg,
    ENNReal.ofReal_lt_ofReal_iff_of_nonneg dist_nonneg]

lemma eannulusIcc_ofReal (h : 0 < r ∨ 0 ≤ R) :
    eannulusIcc x (ENNReal.ofReal r) (ENNReal.ofReal R) = annulusIcc x r R := by
  by_cases hR : 0 ≤ R
  · ext y
    simp [eannulusIcc, annulusIcc, edist_dist, mem_Icc,
      ENNReal.ofReal_le_ofReal_iff dist_nonneg,
      ENNReal.ofReal_le_ofReal_iff hR]
  · have hr : 0 < r := h.resolve_right hR
    have hR' : R < 0 := lt_of_not_ge hR
    have hRr : R < r := hR'.trans hr
    have hER : ENNReal.ofReal R < ENNReal.ofReal r :=
      (ENNReal.ofReal_lt_ofReal_iff').2 ⟨hRr, hr⟩
    
    simp [annulusIcc, Icc_eq_empty_of_lt hRr, eannulusIcc, Icc_eq_empty_of_lt hER]

lemma eannulusIoi_ofReal (hr : 0 ≤ r) :
    eannulusIoi x (ENNReal.ofReal r) = annulusIoi x r := by
  ext y
  simp [eannulusIoi, annulusIoi, edist_dist, mem_Ioi,
    ENNReal.ofReal_lt_ofReal_iff_of_nonneg hr]

lemma eannulusIci_ofReal :
    eannulusIci x (ENNReal.ofReal r) = annulusIci x r := by
  ext y
  simp [eannulusIci, annulusIci, edist_dist, mem_Ici,
    ENNReal.ofReal_le_ofReal_iff dist_nonneg]

end Metric
end
end File20

-- Upstream module PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.HadamardFactorization
section File21
 

section
namespace Complex.Hadamard

open Filter Topology Set Complex

open scoped BigOperators Topology

noncomputable def hadamardDenom (m : ℕ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  z ^ (analyticOrderNatAt f 0) * divisorCanonicalProduct m f (Set.univ : Set ℂ) z

noncomputable def centeredHadamardDenom (m : ℕ) (c : ℂ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (z - c) ^ (analyticOrderNatAt f c) *
    divisorCanonicalProduct m (fun w : ℂ => f (w + c)) (Set.univ : Set ℂ) (z - c)

noncomputable def centeredHadamardQuotient (m : ℕ) (c : ℂ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  f z / centeredHadamardDenom m c f z

@[simp]
theorem centeredHadamardDenom_center_eq_one {m : ℕ} {c : ℂ} {f : ℂ → ℂ}
    (h : analyticOrderNatAt f c = 0) :
    centeredHadamardDenom m c f c = 1 := by
  simp [centeredHadamardDenom, h, sub_self, divisorCanonicalProduct_zero, pow_zero]

@[simp]
theorem centeredHadamardDenom_center_eq_zero {m : ℕ} {c : ℂ} {f : ℂ → ℂ}
    (h : analyticOrderNatAt f c ≠ 0) : centeredHadamardDenom m c f c = 0 := by
  have hn : 0 < analyticOrderNatAt f c := by
    exact Nat.pos_of_ne_zero h
  simp [centeredHadamardDenom, sub_self, zero_pow hn.ne']

theorem differentiable_divisorCanonicalProduct_univ (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1))) :
    Differentiable ℂ (divisorCanonicalProduct m f (Set.univ : Set ℂ)) := by
  intro z
  have hdiffOn :
      DifferentiableOn ℂ (divisorCanonicalProduct m f (Set.univ : Set ℂ)) (Set.univ : Set ℂ) :=
    differentiableOn_divisorCanonicalProduct_univ (m := m) (f := f) h_sum
  exact (hdiffOn z (by simp)).differentiableAt (by simp)

theorem analyticAt_divisorCanonicalProduct_univ (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1))) (z : ℂ) :
    AnalyticAt ℂ (divisorCanonicalProduct m f (Set.univ : Set ℂ)) z :=
  (differentiable_divisorCanonicalProduct_univ m f h_sum).analyticAt z

theorem differentiable_hadamardDenom (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1))) :
    Differentiable ℂ (hadamardDenom m f) := by
  have hcprod : Differentiable ℂ (divisorCanonicalProduct m f (Set.univ : Set ℂ)) := by
    exact differentiable_divisorCanonicalProduct_univ m f h_sum
  simpa [hadamardDenom] using! (differentiable_id.pow (analyticOrderNatAt f 0)).mul hcprod

theorem hadamardDenom_ne_zero_at {m : ℕ} {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hnot : ∃ z : ℂ, f z ≠ 0) (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1))) {z : ℂ} (hz : f z ≠ 0) : hadamardDenom m f z ≠ 0 := by
  have hf_not_top : ∀ w : ℂ, analyticOrderAt f w ≠ ⊤ :=
    analyticOrderAt_ne_top_of_exists_ne_zero (hf := hf) hnot
  have han_f : AnalyticAt ℂ f z := hf.analyticAt z
  have horder_f : analyticOrderNatAt f z = 0 := by
    have : analyticOrderAt f z = 0 := (han_f.analyticOrderAt_eq_zero).2 hz
    have hcast : (analyticOrderNatAt f z : ℕ∞) = analyticOrderAt f z :=
      Nat.cast_analyticOrderNatAt (f := f) (z₀ := z) (hf_not_top z)
    have : (analyticOrderNatAt f z : ℕ∞) = 0 := by simp [hcast, this]
    exact_mod_cast this
  have han_cprod : AnalyticAt ℂ (divisorCanonicalProduct m f (Set.univ : Set ℂ)) z := by
    exact analyticAt_divisorCanonicalProduct_univ m f h_sum z
  by_cases hz0 : z = 0
  · subst hz0
    have hord0 : analyticOrderNatAt f 0 = 0 := by simpa using horder_f
    simp [hadamardDenom, hord0, divisorCanonicalProduct_zero]
  · have hp : z ^ (analyticOrderNatAt f 0) ≠ 0 := pow_ne_zero _ hz0
    have hcprod_order :
        analyticOrderNatAt (divisorCanonicalProduct m f (Set.univ : Set ℂ)) z = 0 := by
      simpa [horder_f] using
        (analyticOrderNatAt_divisorCanonicalProduct_eq_analyticOrderNatAt (m := m) (hf := hf)
          (h_sum := h_sum) (z₀ := z) hz0)
    have hcprod_ne : divisorCanonicalProduct m f (Set.univ : Set ℂ) z ≠ 0 := by
      have hcprod_entire :
          Differentiable ℂ (divisorCanonicalProduct m f (Set.univ : Set ℂ)) := by
        exact differentiable_divisorCanonicalProduct_univ m f h_sum
      have hcprod_not_top :
          analyticOrderAt (divisorCanonicalProduct m f (Set.univ : Set ℂ)) z ≠ ⊤ :=
        analyticOrderAt_ne_top_of_exists_ne_zero (hf := hcprod_entire)
          ⟨0, by simp [divisorCanonicalProduct_zero]⟩ z
      have hcprod_cast :
          (analyticOrderNatAt (divisorCanonicalProduct m f (Set.univ : Set ℂ)) z : ℕ∞) =
            analyticOrderAt (divisorCanonicalProduct m f (Set.univ : Set ℂ)) z :=
        Nat.cast_analyticOrderNatAt
          (f := divisorCanonicalProduct m f (Set.univ : Set ℂ)) (z₀ := z) hcprod_not_top
      have : analyticOrderAt (divisorCanonicalProduct m f (Set.univ : Set ℂ)) z = 0 := by
        have :
            (analyticOrderNatAt
              (divisorCanonicalProduct m f (Set.univ : Set ℂ)) z : ℕ∞) = 0 := by
          exact_mod_cast hcprod_order
        simp [hcprod_cast] at this
        simpa using this
      exact (han_cprod.analyticOrderAt_eq_zero).1 this
    exact mul_ne_zero hp hcprod_ne

lemma analyticOrderNatAt_divisorCanonicalProduct_zero
    (m : ℕ) (f : ℂ → ℂ) (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1))) :
    analyticOrderNatAt (divisorCanonicalProduct m f (Set.univ : Set ℂ)) 0 = 0 := by
  have hcprod_entire :
      Differentiable ℂ (divisorCanonicalProduct m f (Set.univ : Set ℂ)) := by
    exact differentiable_divisorCanonicalProduct_univ m f h_sum
  have hcprod_not_top :
      analyticOrderAt (divisorCanonicalProduct m f (Set.univ : Set ℂ)) 0 ≠ ⊤ :=
    analyticOrderAt_ne_top_of_exists_ne_zero (hf := hcprod_entire)
      ⟨0, by simp [divisorCanonicalProduct_zero]⟩ 0
  have hcprodA : AnalyticAt ℂ (divisorCanonicalProduct m f (Set.univ : Set ℂ)) 0 :=
    hcprod_entire.analyticAt 0
  have hcprod0 : divisorCanonicalProduct m f (Set.univ : Set ℂ) 0 ≠ 0 := by
    simp [divisorCanonicalProduct_zero]
  have : analyticOrderAt (divisorCanonicalProduct m f (Set.univ : Set ℂ)) 0 = 0 :=
    (hcprodA.analyticOrderAt_eq_zero).2 hcprod0
  have hcast :
      (analyticOrderNatAt (divisorCanonicalProduct m f (Set.univ : Set ℂ)) 0 : ℕ∞) =
        analyticOrderAt (divisorCanonicalProduct m f (Set.univ : Set ℂ)) 0 :=
    Nat.cast_analyticOrderNatAt
      (f := divisorCanonicalProduct m f (Set.univ : Set ℂ)) (z₀ := (0 : ℂ)) hcprod_not_top
  have :
      (analyticOrderNatAt (divisorCanonicalProduct m f (Set.univ : Set ℂ)) 0 : ℕ∞) =
        0 := by
    simp [hcast, this]
  exact_mod_cast this

theorem analyticOrderNatAt_hadamardDenom_eq
    (m : ℕ) {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1))) (z : ℂ) :
    analyticOrderNatAt (hadamardDenom m f) z = analyticOrderNatAt f z := by
  by_cases hz0 : z = 0
  · subst hz0
    have hpowA : AnalyticAt ℂ (fun z : ℂ => z ^ analyticOrderNatAt f 0) 0 := by
      simpa using! (analyticAt_id.pow (analyticOrderNatAt f 0))
    have hpow_not_top :
        analyticOrderAt (fun z : ℂ => z ^ analyticOrderNatAt f 0) 0 ≠ ⊤ :=
      analyticOrderAt_ne_top_of_exists_ne_zero
        (hf := (differentiable_id.pow (analyticOrderNatAt f 0)))
        ⟨1, by simp⟩ 0
    have hcprodA : AnalyticAt ℂ (divisorCanonicalProduct m f (Set.univ : Set ℂ)) 0 := by
      exact analyticAt_divisorCanonicalProduct_univ m f h_sum 0
    have hcprod0 :
        analyticOrderNatAt (divisorCanonicalProduct m f (Set.univ : Set ℂ)) 0 = 0 :=
      analyticOrderNatAt_divisorCanonicalProduct_zero (m := m) (f := f) h_sum
    have hid0 : analyticOrderNatAt (fun z : ℂ => z) 0 = 1 := by
      have hid_entire : Differentiable ℂ (fun z : ℂ => z) := differentiable_id
      have hdiv :
          (MeromorphicOn.divisor (fun z : ℂ => z) (Set.univ : Set ℂ)) 0 =
            (analyticOrderNatAt (fun z : ℂ => z) 0 : ℤ) := by
        simpa using
          (divisor_univ_eq_analyticOrderNatAt_int
            (f := fun z : ℂ => z) hid_entire 0)
      have hdiv1 : (MeromorphicOn.divisor (fun z : ℂ => z) (Set.univ : Set ℂ)) 0 = 1 := by
        simpa using
          (MeromorphicOn.divisor_sub_const_self (z₀ := (0 : ℂ))
            (U := (Set.univ : Set ℂ)) (by simp))
      have : (analyticOrderNatAt (fun z : ℂ => z) 0 : ℤ) = 1 := by
        simpa [hdiv] using hdiv1
      exact_mod_cast this
    have hpow0 :
        analyticOrderNatAt (fun z : ℂ => z ^ analyticOrderNatAt f 0) 0 =
          analyticOrderNatAt f 0 := by
      have hidA : AnalyticAt ℂ (fun z : ℂ => z) 0 := by
        simpa [id] using! (analyticAt_id : AnalyticAt ℂ (id : ℂ → ℂ) 0)
      simpa [hid0] using! (analyticOrderNatAt_pow (hf := hidA) (n := analyticOrderNatAt f 0))
    have hmul :
        analyticOrderNatAt (hadamardDenom m f) 0 =
          analyticOrderNatAt (fun z : ℂ => z ^ analyticOrderNatAt f 0) 0 +
            analyticOrderNatAt (divisorCanonicalProduct m f (Set.univ : Set ℂ)) 0 := by
      have hcprod_not_top' :
          analyticOrderAt (divisorCanonicalProduct m f (Set.univ : Set ℂ)) 0 ≠ ⊤ :=
        analyticOrderAt_ne_top_of_exists_ne_zero
          (hf := differentiable_divisorCanonicalProduct_univ m f h_sum)
          ⟨0, by simp [divisorCanonicalProduct_zero]⟩ 0
      simpa [hadamardDenom] using!
        analyticOrderNatAt_mul (hf := hpowA) (hg := hcprodA)
          (hf' := hpow_not_top) (hg' := hcprod_not_top')
    simp [hmul, hpow0, hcprod0]
  · have hpowA : AnalyticAt ℂ (fun z : ℂ => z ^ analyticOrderNatAt f 0) z := by
      simpa using! (analyticAt_id.pow (analyticOrderNatAt f 0))
    have hpow_not_top :
        analyticOrderAt (fun z : ℂ => z ^ analyticOrderNatAt f 0) z ≠ ⊤ :=
      analyticOrderAt_ne_top_of_exists_ne_zero
        (hf := (differentiable_id.pow (analyticOrderNatAt f 0)))
        ⟨1, by simp⟩ z
    have hpow0 : analyticOrderNatAt (fun z : ℂ => z ^ analyticOrderNatAt f 0) z = 0 := by
      have hz' : (fun z : ℂ => z ^ analyticOrderNatAt f 0) z ≠ 0 := by
        simp [hz0]
      have : analyticOrderAt (fun z : ℂ => z ^ analyticOrderNatAt f 0) z = 0 :=
        ((hpowA).analyticOrderAt_eq_zero).2 hz'
      have hcast : (analyticOrderNatAt (fun z : ℂ => z ^ analyticOrderNatAt f 0) z : ℕ∞) =
          analyticOrderAt (fun z : ℂ => z ^ analyticOrderNatAt f 0) z :=
        Nat.cast_analyticOrderNatAt
          (f := fun z : ℂ => z ^ analyticOrderNatAt f 0) (z₀ := z) hpow_not_top
      have : (analyticOrderNatAt (fun z : ℂ => z ^ analyticOrderNatAt f 0) z : ℕ∞) = 0 := by
        simp [hcast, this]
      exact_mod_cast this
    have hcprod_eq :
        analyticOrderNatAt (divisorCanonicalProduct m f (Set.univ : Set ℂ)) z =
          analyticOrderNatAt f z :=
      analyticOrderNatAt_divisorCanonicalProduct_eq_analyticOrderNatAt
        (m := m) (hf := hf) (h_sum := h_sum) (z₀ := z) hz0
    have hcprodA : AnalyticAt ℂ (divisorCanonicalProduct m f (Set.univ : Set ℂ)) z := by
      exact analyticAt_divisorCanonicalProduct_univ m f h_sum z
    have hcprod_not_top :
        analyticOrderAt (divisorCanonicalProduct m f (Set.univ : Set ℂ)) z ≠ ⊤ :=
      analyticOrderAt_ne_top_of_exists_ne_zero
        (hf := differentiable_divisorCanonicalProduct_univ m f h_sum)
        ⟨0, by simp [divisorCanonicalProduct_zero]⟩ z
    have hmul :
        analyticOrderNatAt (hadamardDenom m f) z =
          analyticOrderNatAt (fun z : ℂ => z ^ analyticOrderNatAt f 0) z +
            analyticOrderNatAt (divisorCanonicalProduct m f (Set.univ : Set ℂ)) z := by
      simpa [hadamardDenom] using!
        analyticOrderNatAt_mul (hf := hpowA) (hg := hcprodA)
          (hf' := hpow_not_top) (hg' := hcprod_not_top)
    simp [hmul, hpow0, hcprod_eq]

theorem divisor_hadamardDenom_eq
    (m : ℕ) {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1))) :
    MeromorphicOn.divisor (hadamardDenom m f) (Set.univ : Set ℂ) =
      MeromorphicOn.divisor f (Set.univ : Set ℂ) := by
  ext z
  have hden_entire : Differentiable ℂ (hadamardDenom m f) :=
    differentiable_hadamardDenom (m := m) f h_sum
  have hf_entire : Differentiable ℂ f := hf
  have hden :
      (MeromorphicOn.divisor (hadamardDenom m f) (Set.univ : Set ℂ)) z =
        (analyticOrderNatAt (hadamardDenom m f) z : ℤ) := by
    simpa using (divisor_univ_eq_analyticOrderNatAt_int (f := hadamardDenom m f) hden_entire z)
  have hfz :
      (MeromorphicOn.divisor f (Set.univ : Set ℂ)) z =
        (analyticOrderNatAt f z : ℤ) := by
    simpa using (divisor_univ_eq_analyticOrderNatAt_int (f := f) hf_entire z)
  simp [hden, hfz, analyticOrderNatAt_hadamardDenom_eq (m := m) (hf := hf) (h_sum := h_sum) z]

theorem divisor_hadamardQuotient_eq_zero
    (m : ℕ) {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hnot : ∃ z : ℂ, f z ≠ 0)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1))) :
    MeromorphicOn.divisor (fun z : ℂ => f z / hadamardDenom m f z) (Set.univ : Set ℂ) = 0 := by
  have hf_mero : MeromorphicOn f (Set.univ : Set ℂ) := by
    intro z hz
    exact (hf.analyticAt z).meromorphicAt
  have hden_entire : Differentiable ℂ (hadamardDenom m f) :=
    differentiable_hadamardDenom (m := m) f h_sum
  have hden_mero : MeromorphicOn (hadamardDenom m f) (Set.univ : Set ℂ) := by
    intro z hz
    exact (hden_entire.analyticAt z).meromorphicAt
  rcases hnot with ⟨z1, hz1⟩
  have hden1 : hadamardDenom m f z1 ≠ 0 :=
    hadamardDenom_ne_zero_at (m := m) (f := f) hf ⟨z1, hz1⟩ h_sum hz1
  have hf_order_ne_top : ∀ z ∈ (Set.univ : Set ℂ), meromorphicOrderAt f z ≠ ⊤ := by
    intro z hzU
    have hz1_ne_top : meromorphicOrderAt f z1 ≠ ⊤ := by
      have hfAt : MeromorphicAt f z1 := hf_mero z1 (by simp)
      have hcont : ContinuousAt f z1 := (hf.differentiableAt).continuousAt
      have hne_nhds : ∀ᶠ w in 𝓝 z1, f w ≠ 0 :=
        (hcont.ne_iff_eventually_ne continuousAt_const).1 hz1
      have hne_nhdsNE : ∀ᶠ w in 𝓝[≠] z1, f w ≠ 0 :=
        eventually_nhdsWithin_of_eventually_nhds hne_nhds
      exact (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hf := hfAt)).2 hne_nhdsNE
    exact MeromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected (hf := hf_mero)
      (x := z1) (hU := isPreconnected_univ) (h₁x := by simp) (hy := by simp) hz1_ne_top
  have hden_order_ne_top :
      ∀ z ∈ (Set.univ : Set ℂ), meromorphicOrderAt (hadamardDenom m f) z ≠ ⊤ := by
    intro z hzU
    have hz1_ne_top : meromorphicOrderAt (hadamardDenom m f) z1 ≠ ⊤ := by
      have hdenAt : MeromorphicAt (hadamardDenom m f) z1 := hden_mero z1 (by simp)
      have hcont : ContinuousAt (hadamardDenom m f) z1 :=
        (hden_entire.differentiableAt).continuousAt
      have hne_nhds : ∀ᶠ w in 𝓝 z1, hadamardDenom m f w ≠ 0 :=
        (hcont.ne_iff_eventually_ne continuousAt_const).1 hden1
      have hne_nhdsNE : ∀ᶠ w in 𝓝[≠] z1, hadamardDenom m f w ≠ 0 :=
        eventually_nhdsWithin_of_eventually_nhds hne_nhds
      exact (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hf := hdenAt)).2 hne_nhdsNE
    exact MeromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected (hf := hden_mero)
      (x := z1) (hU := isPreconnected_univ) (h₁x := by simp) (hy := by simp) hz1_ne_top
  have hinv_order_ne_top :
      ∀ z ∈ (Set.univ : Set ℂ),
        meromorphicOrderAt (fun z : ℂ => (hadamardDenom m f z)⁻¹) z ≠ ⊤ := by
    intro z hzU
    have hinv_mero :
        MeromorphicOn (fun z : ℂ => (hadamardDenom m f z)⁻¹) (Set.univ : Set ℂ) :=
      hden_mero.inv
    have hz1_ne_top :
        meromorphicOrderAt (fun z : ℂ => (hadamardDenom m f z)⁻¹) z1 ≠ ⊤ := by
      have hinvAt : MeromorphicAt (fun z : ℂ => (hadamardDenom m f z)⁻¹) z1 :=
        hinv_mero z1 (by simp)
      have hcont_denom : ContinuousAt (hadamardDenom m f) z1 :=
        (hden_entire.differentiableAt).continuousAt
      have hcont : ContinuousAt (fun z : ℂ => (hadamardDenom m f z)⁻¹) z1 :=
        hcont_denom.inv₀ hden1
      have hinv1 : (fun z : ℂ => (hadamardDenom m f z)⁻¹) z1 ≠ 0 := by
        simpa using inv_ne_zero hden1
      have hne_nhds :
          ∀ᶠ w in 𝓝 z1, (fun z : ℂ => (hadamardDenom m f z)⁻¹) w ≠ 0 :=
        (hcont.ne_iff_eventually_ne continuousAt_const).1 hinv1
      have hne_nhdsNE :
          ∀ᶠ w in 𝓝[≠] z1, (fun z : ℂ => (hadamardDenom m f z)⁻¹) w ≠ 0 :=
        eventually_nhdsWithin_of_eventually_nhds hne_nhds
      exact (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hf := hinvAt)).2 hne_nhdsNE
    exact MeromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected (hf := hinv_mero)
      (x := z1) (hU := isPreconnected_univ) (h₁x := by simp) (hy := by simp) hz1_ne_top
  have hdiv_denom : MeromorphicOn.divisor (hadamardDenom m f) (Set.univ : Set ℂ) =
      MeromorphicOn.divisor f (Set.univ : Set ℂ) :=
    divisor_hadamardDenom_eq (m := m) (hf := hf) (h_sum := h_sum)
  calc
    MeromorphicOn.divisor (fun z : ℂ => f z / hadamardDenom m f z) (Set.univ : Set ℂ)
        = MeromorphicOn.divisor
            (fun z : ℂ => f z * (hadamardDenom m f z)⁻¹) (Set.univ : Set ℂ) := by
            simp [div_eq_mul_inv]
    _ = MeromorphicOn.divisor f (Set.univ : Set ℂ) +
          MeromorphicOn.divisor (fun z : ℂ => (hadamardDenom m f z)⁻¹) (Set.univ : Set ℂ) := by
          simpa using (MeromorphicOn.divisor_fun_mul (U := (Set.univ : Set ℂ))
            (f₁ := f) (f₂ := fun z => (hadamardDenom m f z)⁻¹) hf_mero (hden_mero.inv)
            hf_order_ne_top hinv_order_ne_top)
    _ = MeromorphicOn.divisor f (Set.univ : Set ℂ) -
          MeromorphicOn.divisor (hadamardDenom m f) (Set.univ : Set ℂ) := by
          simp [sub_eq_add_neg]
    _ = 0 := by
          simp [hdiv_denom]

theorem exists_entire_nonzero_hadamardQuotient
    (m : ℕ) {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hnot : ∃ z : ℂ, f z ≠ 0)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1))) :
    ∃ H : ℂ → ℂ, Differentiable ℂ H ∧ (∀ z, H z ≠ 0) ∧ ∀ z : ℂ, f z =
      H z * z ^ (analyticOrderNatAt f 0) * divisorCanonicalProduct m f (Set.univ : Set ℂ) z := by
  let denom : ℂ → ℂ := hadamardDenom m f
  let q : ℂ → ℂ := fun z => f z / denom z
  have hden_entire : Differentiable ℂ denom :=
    differentiable_hadamardDenom (m := m) f h_sum
  have hq_mero : MeromorphicOn q (Set.univ : Set ℂ) := by
    intro z hzU
    have hf_m : MeromorphicAt f z := (hf.analyticAt z).meromorphicAt
    have hden_m : MeromorphicAt denom z := (hden_entire.analyticAt z).meromorphicAt
    simpa [q, denom, div_eq_mul_inv] using! (hf_m.mul hden_m.inv)
  let H : ℂ → ℂ := toMeromorphicNFOn q (Set.univ : Set ℂ)
  have hNF : MeromorphicNFOn H (Set.univ : Set ℂ) :=
    meromorphicNFOn_toMeromorphicNFOn q (Set.univ : Set ℂ)
  have hdivH : MeromorphicOn.divisor H (Set.univ : Set ℂ) = 0 := by
    have hdivq : MeromorphicOn.divisor q (Set.univ : Set ℂ) = 0 :=
      divisor_hadamardQuotient_eq_zero (m := m) (f := f) (hf := hf)
        (hnot := hnot) (h_sum := h_sum)
    simpa [H, hdivq] using
      (MeromorphicOn.divisor_of_toMeromorphicNFOn
        (f := q) (U := (Set.univ : Set ℂ)) hq_mero)
  have hA : AnalyticOnNhd ℂ H (Set.univ : Set ℂ) := by
    have :
        (0 : Function.locallyFinsuppWithin (Set.univ : Set ℂ) ℤ) ≤
          MeromorphicOn.divisor H (Set.univ : Set ℂ) := by
      simp [hdivH]
    exact (MeromorphicNFOn.divisor_nonneg_iff_analyticOnNhd (h₁f := hNF)).1 (by simp [hdivH])
  have hH_entire : Differentiable ℂ H := by
    intro z
    exact (hA z (by simp)).differentiableAt
  rcases hnot with ⟨z1, hz1⟩
  have hden1 : denom z1 ≠ 0 :=
    hadamardDenom_ne_zero_at (m := m) (f := f) hf ⟨z1, hz1⟩ h_sum hz1
  have hqA1 : AnalyticAt ℂ q z1 := by
    have hdenA1 : AnalyticAt ℂ denom z1 := hden_entire.analyticAt z1
    exact (hf.analyticAt z1).div hdenA1 hden1
  have hqNF1 : MeromorphicNFAt q z1 := hqA1.meromorphicNFAt
  have htoEq : toMeromorphicNFAt q z1 = q := (toMeromorphicNFAt_eq_self (f := q) (x := z1)).2 hqNF1
  have hH1 : H z1 = q z1 := by
    have hx : z1 ∈ (Set.univ : Set ℂ) := by simp
    have : toMeromorphicNFOn q (Set.univ : Set ℂ) z1 = toMeromorphicNFAt q z1 z1 :=
      (toMeromorphicNFOn_eq_toMeromorphicNFAt (f := q) (U := (Set.univ : Set ℂ)) hq_mero hx)
    simpa [H, htoEq] using this
  have hH1_ne : H z1 ≠ 0 := by
    have : q z1 ≠ 0 := div_ne_zero hz1 hden1
    simpa [hH1] using this
  have hH_not_top : ∀ z : ℂ, analyticOrderAt H z ≠ ⊤ := by
    exact analyticOrderAt_ne_top_of_exists_ne_zero (hf := hH_entire) ⟨z1, hH1_ne⟩
  have hH_orderNat_zero : ∀ z : ℂ, analyticOrderNatAt H z = 0 := by
    intro z
    have hzdiv :
        (MeromorphicOn.divisor H (Set.univ : Set ℂ)) z = (analyticOrderNatAt H z : ℤ) := by
      simpa using (divisor_univ_eq_analyticOrderNatAt_int (f := H) hH_entire z)
    have : (MeromorphicOn.divisor H (Set.univ : Set ℂ)) z = 0 := by
      simp [hdivH]
    have : (analyticOrderNatAt H z : ℤ) = 0 := by simpa [hzdiv] using this
    exact_mod_cast this
  have hH_ne : ∀ z : ℂ, H z ≠ 0 := by
    intro z
    have hcast : (analyticOrderNatAt H z : ℕ∞) = analyticOrderAt H z :=
      Nat.cast_analyticOrderNatAt (f := H) (z₀ := z) (hH_not_top z)
    have : analyticOrderAt H z = 0 := by
      have : (analyticOrderNatAt H z : ℕ∞) = 0 := by exact_mod_cast (hH_orderNat_zero z)
      simpa [hcast] using this
    exact ((hA z (by simp)).analyticOrderAt_eq_zero).1 this
  have hfA : AnalyticOnNhd ℂ f (Set.univ : Set ℂ) := fun z hzU => hf.analyticAt z
  have hdenA : AnalyticOnNhd ℂ denom (Set.univ : Set ℂ) := fun z hzU => hden_entire.analyticAt z
  have hprodA : AnalyticOnNhd ℂ (fun z => H z * denom z) (Set.univ : Set ℂ) :=
    (hA.mul hdenA)
  have hlocal : f =ᶠ[𝓝 z1] fun z => H z * denom z := by
    have hden_ne : ∀ᶠ z in 𝓝 z1, denom z ≠ 0 :=
      (hden_entire.differentiableAt.continuousAt.ne_iff_eventually_ne continuousAt_const).1 hden1
    have hH_eq_q : H =ᶠ[𝓝 z1] q := by
      have hx : z1 ∈ (Set.univ : Set ℂ) := by simp
      have hloc :
          toMeromorphicNFOn q (Set.univ : Set ℂ) =ᶠ[𝓝 z1] toMeromorphicNFAt q z1 := by
        simpa [H] using (toMeromorphicNFOn_eq_toMeromorphicNFAt_on_nhds (f := q)
          (U := (Set.univ : Set ℂ)) hq_mero hx)
      simpa [H, htoEq] using hloc
    filter_upwards [hden_ne, hH_eq_q] with z hzden hHz
    have hcancel : q z * denom z = f z := by
      dsimp [q]
      field_simp [hzden]
    calc
      f z = q z * denom z := hcancel.symm
      _ = H z * denom z := by simp [hHz]
  have hglob : f = fun z => H z * denom z :=
    AnalyticOnNhd.eq_of_eventuallyEq (hf := hfA) (hg := hprodA) hlocal
  refine ⟨H, hH_entire, hH_ne, ?_⟩
  intro z
  have hglobz : f z = H z * denom z := congrArg (fun g => g z) hglob
  simpa [denom, hadamardDenom, mul_assoc, mul_left_comm, mul_comm] using hglobz

theorem bddAbove_norm_divisorCanonicalProduct_div_pow_annulus
    (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1)))
    (z₀ : ℂ) (k : ℕ) {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) :
    BddAbove
      (norm ∘
        (fun z : ℂ => (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) / (z - z₀) ^ k) ''
          (Metric.annulusIcc z₀ r₁ r₂)) := by
  set K : Set ℂ := Metric.annulusIcc z₀ r₁ r₂
  have hK : IsCompact K := by
    have hclosed : IsClosed (Metric.ball z₀ r₁)ᶜ := Metric.isOpen_ball.isClosed_compl
    simpa [K, Metric.annulusIcc_eq] using (isCompact_closedBall z₀ r₂).inter_right hclosed
  have hKz : ∀ z ∈ K, z ≠ z₀ := by
    intro z hz hzz
    have hzBall : z ∈ Metric.ball z₀ r₁ := by
      simpa [hzz] using (Metric.mem_ball_self hr₁ : z₀ ∈ Metric.ball z₀ r₁)
    have hz' : z ∈ Metric.closedBall z₀ r₂ ∧ z ∉ Metric.ball z₀ r₁ := by
      simpa [K, Metric.annulusIcc_eq] using hz
    exact hz'.2 hzBall
  have hdiff : DifferentiableOn ℂ
        (fun z : ℂ => (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) / (z - z₀) ^ k)
        ((Set.univ : Set ℂ) \ {z₀}) :=
    differentiableOn_divisorCanonicalProduct_div_pow_sub (m := m) (f := f) h_sum (z₀ := z₀) (k := k)
  have hcont : ContinuousOn
      (fun z : ℂ => (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) / (z - z₀) ^ k) K := by
    refine (hdiff.mono ?_).continuousOn
    intro z hz
    refine ⟨by simp, ?_⟩
    exact hKz z hz
  have hKimg :
      IsCompact
        ((fun z : ℂ => (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) / (z - z₀) ^ k) '' K) :=
    hK.image_of_continuousOn hcont
  rcases (isBounded_iff_forall_norm_le.1 hKimg.isBounded) with ⟨C, hC⟩
  refine ⟨C, ?_⟩
  rintro _ ⟨w, hwK, rfl⟩
  exact hC _ ⟨w, hwK, rfl⟩

end Complex.Hadamard
end
end File21

-- Upstream module PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.ValueDistribution.LogCounting.Basic
section File22
 

section
open Filter Function MeromorphicOn Metric Real Set

namespace Function.locallyFinsuppWithin

variable {E : Type*} [NormedAddCommGroup E]

lemma norm_le_abs_of_mem_toClosedBall_support {D : locallyFinsupp E ℤ} {r : ℝ} {z : E}
    (hz : z ∈ (toClosedBall r D).support) : ‖z‖ ≤ |r| := by
  have hz_ball : z ∈ closedBall (0 : E) |r| := (toClosedBall r D).supportWithinDomain hz
  simpa [mem_closedBall, dist_zero_right] using hz_ball

lemma toClosedBall_eval_eq_of_norm_le_abs {D : locallyFinsupp E ℤ} {r : ℝ} {z : E}
    (hz : ‖z‖ ≤ |r|) : toClosedBall r D z = D z := by
  have hz_ball : z ∈ closedBall (0 : E) |r| := by
    simpa [mem_closedBall, dist_zero_right] using hz
  simpa using toClosedBall_eval_within (f := D) hz_ball

lemma mem_toClosedBall_support_of_mem_support_of_norm_le_abs
    {D : locallyFinsupp E ℤ} {r : ℝ} {z : E} (hzD : z ∈ D.support) (hzR : ‖z‖ ≤ |r|) :
    z ∈ (toClosedBall r D).support := by
  rw [Function.mem_support]
  rw [toClosedBall_eval_eq_of_norm_le_abs hzR]
  rwa [Function.mem_support] at hzD

lemma mem_support_of_mem_toClosedBall_support {D : locallyFinsupp E ℤ} {r : ℝ} {z : E}
    (hz : z ∈ (toClosedBall r D).support) : z ∈ D.support := by
  have hnorm : ‖z‖ ≤ |r| := norm_le_abs_of_mem_toClosedBall_support hz
  rw [Function.mem_support] at hz ⊢
  rw [toClosedBall_eval_eq_of_norm_le_abs hnorm] at hz
  exact hz

noncomputable def massClosedBall₀ {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    (D : locallyFinsupp E ℤ) (R : ℝ) : ℝ := by
  classical
  exact
    (((finiteSupport (toClosedBall R D) (isCompact_closedBall (0 : E) |R|)).toFinset).filter
      (fun z => z ≠ (0 : E))).sum fun z => (D z : ℝ)

lemma massClosedBall₀_mono {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    {D : locallyFinsupp E ℤ} (hD : 0 ≤ D) {R₁ R₂ : ℝ} (hR₁ : 0 ≤ R₁) (hR₁₂ : R₁ ≤ R₂) :
    massClosedBall₀ D R₁ ≤ massClosedBall₀ D R₂ := by
  classical
  have hR₂ : 0 ≤ R₂ := le_trans hR₁ hR₁₂
  have habs₁ : |R₁| = R₁ := abs_of_nonneg hR₁
  have habs₂ : |R₂| = R₂ := abs_of_nonneg hR₂
  let SR (R : ℝ) : Finset E :=
    (finiteSupport (toClosedBall R D) (isCompact_closedBall (0 : E) |R|)).toFinset
  let S (R : ℝ) : Finset E := (SR R).filter fun z : E => z ≠ 0
  have hsub : S R₁ ⊆ S R₂ := by
    intro z hz
    have hzSR₁ : z ∈ SR R₁ := (Finset.mem_filter.1 hz).1
    have hz0 : z ≠ 0 := (Finset.mem_filter.1 hz).2
    have hz_sup₁ : z ∈ (toClosedBall R₁ D).support := by
      exact (finiteSupport (toClosedBall R₁ D) (isCompact_closedBall (0 : E) |R₁|)).mem_toFinset.1
        hzSR₁
    have hz_norm₁ : ‖z‖ ≤ R₁ := by
      have h := norm_le_abs_of_mem_toClosedBall_support hz_sup₁
      simpa [habs₁] using h
    have hz_norm₂ : ‖z‖ ≤ R₂ := le_trans hz_norm₁ hR₁₂
    have hz_norm₂_abs : ‖z‖ ≤ |R₂| := by simpa [habs₂] using hz_norm₂
    have hzD : z ∈ D.support := mem_support_of_mem_toClosedBall_support hz_sup₁
    have hz_sup₂ : z ∈ (toClosedBall R₂ D).support :=
      mem_toClosedBall_support_of_mem_support_of_norm_le_abs hzD hz_norm₂_abs
    have hzSR₂ : z ∈ SR R₂ := by
      exact (finiteSupport (toClosedBall R₂ D) (isCompact_closedBall (0 : E) |R₂|)).mem_toFinset.2
        hz_sup₂
    exact Finset.mem_filter.2 ⟨hzSR₂, hz0⟩
  have hterm_nonneg : ∀ z ∈ S R₂, 0 ≤ (D z : ℝ) := by
    intro z _hz
    exact_mod_cast hD z
  simpa [massClosedBall₀, SR, S] using
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun z hz₂ _hznot => hterm_nonneg z hz₂)

end Function.locallyFinsuppWithin

namespace Function.locallyFinsuppWithin

theorem logCounting_divisor_eq_circleAverage_sub_const_of_differentiable
    {R : ℝ} {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hR : R ≠ 0) :
    logCounting (divisor f ⊤) R =
      circleAverage (log ‖f ·‖) 0 R - log ‖meromorphicTrailingCoeffAt f 0‖ := by
  have hmero : Meromorphic f := fun z => (hf.analyticAt z).meromorphicAt
  simpa [top_eq_univ] using
    logCounting_divisor_eq_circleAverage_sub_const (f := f) hmero hR

end Function.locallyFinsuppWithin
end
end File22

-- Upstream module PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Log.PosLog
section File23
 

section
namespace Real

theorem log_one_add_exp_le_add_log_two {x : ℝ} (hx : 0 ≤ x) :
    log (1 + exp x) ≤ x + log 2 := by
  have hexp_one : (1 : ℝ) ≤ exp x := by
    simpa using (one_le_exp_iff.2 hx)
  have hadd : 1 + exp x ≤ 2 * exp x := by linarith
  have hlog : log (1 + exp x) ≤ log (2 * exp x) :=
    log_le_log (by positivity) hadd
  calc
    log (1 + exp x) ≤ log (2 * exp x) := hlog
    _ = log 2 + x := by simp [log_mul, add_comm]
    _ = x + log 2 := by ring

theorem log_one_add_le_add_log_two_of_le_exp {x y : ℝ} (hy : 0 ≤ y) (hx : 0 ≤ x)
    (hxy : y ≤ exp x) :
    log (1 + y) ≤ x + log 2 := by
  have hpos : 0 < (1 : ℝ) + y := by linarith
  have hle : (1 : ℝ) + y ≤ 1 + exp x := by linarith
  exact (log_le_log hpos hle).trans (log_one_add_exp_le_add_log_two hx)

theorem le_exp_of_log_one_add_le {x y : ℝ} (hy : 0 ≤ y) (hxy : log (1 + y) ≤ x) :
    y ≤ exp x := by
  have hpos : 0 < (1 : ℝ) + y := by linarith
  have hone : 1 + y ≤ exp x := (log_le_iff_le_exp hpos).1 hxy
  linarith

theorem neg_posLog_inv_le_log (x : ℝ) : -log⁺ x⁻¹ ≤ log x := by
  linarith [posLog_sub_posLog_inv (x := x), posLog_nonneg (x := x)]

end Real
end
end File23

-- Upstream module PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Exp
section File24
 

section
namespace Real

theorem le_exp_self (x : ℝ) : x ≤ exp x :=
  le_trans (by linarith : x ≤ x + 1) (add_one_le_exp x)

lemma mul_four_le_exp_add {a b c d A B C D : ℝ}
    (hb0 : 0 ≤ b) (hc0 : 0 ≤ c) (hd0 : 0 ≤ d)
    (ha : a ≤ exp A) (hb : b ≤ exp B) (hc : c ≤ exp C) (hd : d ≤ exp D) :
    a * b * c * d ≤ exp (A + B + C + D) := by
  have hab : a * b ≤ exp A * exp B :=
    mul_le_mul ha hb hb0 (exp_pos A).le
  have habc : (a * b) * c ≤ (exp A * exp B) * exp C :=
    mul_le_mul hab hc hc0 (by positivity)
  have hprod : a * b * c * d ≤ exp A * exp B * exp C * exp D :=
    mul_le_mul habc hd hd0 (by positivity)
  calc
    a * b * c * d ≤ exp A * exp B * exp C * exp D := hprod
    _ = exp (A + B + C + D) := by
        rw [← exp_add, ← exp_add, ← exp_add]

lemma two_mul_le_exp_two_mul_sq {x A : ℝ} (hx : x ≤ A) (hA1 : 1 ≤ A) :
    x * 2 ≤ exp (2 * (A * A)) := by
  have h1 : x * 2 ≤ 2 * A := by linarith [hx]
  have hA0 : 0 ≤ A := zero_le_one.trans hA1
  have hA_le_sq : A ≤ A * A := by
    simpa [one_mul] using mul_le_mul_of_nonneg_right hA1 hA0
  have h2 : 2 * A ≤ 2 * (A * A) := by nlinarith [hA_le_sq]
  exact le_trans (le_trans h1 h2) (le_exp_self (2 * (A * A)))

end Real
end
end File24

-- Upstream module PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Log.ExpGrowth
section File25
 

section
namespace Real

variable {α E : Type*} [SeminormedAddCommGroup E]

theorem log_norm_le_log_one_add_norm (w : E) :
    Real.log ‖w‖ ≤ Real.log (1 + ‖w‖) := by
  by_cases h0 : ‖w‖ = 0
  · simp [h0]
  · have hpos : 0 < ‖w‖ := lt_of_le_of_ne (norm_nonneg w) (Ne.symm h0)
    exact Real.log_le_log hpos (by linarith [norm_nonneg w])

variable {F : Type*} [NormedAddCommGroup F]

theorem log_nonneg_mul_inv_norm_of_norm_le {z : F} {r : ℝ} (hz : ‖z‖ ≤ r) :
    0 ≤ Real.log (r * ‖z‖⁻¹) := by
  by_cases hz0 : z = 0
  · simp [hz0]
  · have hzpos : 0 < ‖z‖ := norm_pos_iff.2 hz0
    have : (1 : ℝ) ≤ r * ‖z‖⁻¹ := by
      have : (1 : ℝ) ≤ r / ‖z‖ := (one_le_div hzpos).2 hz
      simpa [div_eq_mul_inv] using this
    exact Real.log_nonneg this

theorem log_two_le_log_two_mul_mul_inv_norm_of_norm_le {z : F} {R : ℝ} (hz0 : z ≠ 0)
    (hz : ‖z‖ ≤ R) :
    Real.log 2 ≤ Real.log ((2 * R) * ‖z‖⁻¹) := by
  have hzpos : 0 < ‖z‖ := norm_pos_iff.2 hz0
  have hRdiv : (1 : ℝ) ≤ R / ‖z‖ := (one_le_div hzpos).2 hz
  have hle2 : (2 : ℝ) ≤ (2 * R) * ‖z‖⁻¹ := by
    have : (2 : ℝ) ≤ 2 * (R / ‖z‖) := by nlinarith
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this
  exact Real.log_le_log (by norm_num) hle2

theorem norm_le_exp_mul_rpow_of_exponent_le
    {f : α → E} {r : α → ℝ} {C ρ τ : ℝ} (hC : 0 ≤ C) (hr : ∀ x, 1 ≤ r x) (hρτ : ρ ≤ τ)
    (hbound : ∀ x, ‖f x‖ ≤ Real.exp (C * (r x) ^ ρ)) : ∀ x, ‖f x‖ ≤ Real.exp (C * (r x) ^ τ) := by
  intro x
  refine (hbound x).trans (Real.exp_le_exp.2 ?_)
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (hr x) hρτ) hC

theorem norm_le_exp_mul_rpow_of_log_growth
    {f : α → E} {r : α → ℝ} {C ρ τ : ℝ} (hC : 0 ≤ C) (hr : ∀ x, 1 ≤ r x) (hρτ : ρ ≤ τ)
    (hlog : ∀ x, Real.log (1 + ‖f x‖) ≤ C * (r x) ^ ρ) : ∀ x, ‖f x‖ ≤ Real.exp (C * (r x) ^ τ) := by
  intro x
  have hpow : (r x) ^ ρ ≤ (r x) ^ τ :=
    Real.rpow_le_rpow_of_exponent_le (hr x) hρτ
  have hlogτ : Real.log (1 + ‖f x‖) ≤ C * (r x) ^ τ :=
    (hlog x).trans (mul_le_mul_of_nonneg_left hpow hC)
  exact Real.le_exp_of_log_one_add_le (norm_nonneg (f x)) hlogτ

theorem log_growth_of_norm_le_exp_mul_rpow
    {f : α → E} {r : α → ℝ} {C τ : ℝ} (hC : 0 < C) (hτ : 0 ≤ τ)
    (hr : ∀ x, 1 ≤ r x) (hbound : ∀ x, ‖f x‖ ≤ Real.exp (C * (r x) ^ τ)) :
    ∃ C' > 0, ∀ x, Real.log (1 + ‖f x‖) ≤ C' * (r x) ^ τ := by
  refine ⟨C + Real.log 2, by
    have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    linarith, ?_⟩
  intro x
  have hX : (1 : ℝ) ≤ (r x) ^ τ := Real.one_le_rpow (hr x) hτ
  have hB : 0 ≤ C * (r x) ^ τ :=
    mul_nonneg hC.le (Real.rpow_nonneg (le_trans zero_le_one (hr x)) _)
  have hlog :
      Real.log (1 + ‖f x‖) ≤ C * (r x) ^ τ + Real.log 2 :=
    Real.log_one_add_le_add_log_two_of_le_exp (norm_nonneg _) hB (hbound x)
  have hlog2_nonneg : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  nlinarith [hlog, hX, hlog2_nonneg]

theorem exists_norm_le_exp_mul_pow_of_rpow_bound
    {f : α → E} {r : α → ℝ} {τ : ℝ} {n : ℕ} (hr : ∀ x, 1 ≤ r x) (hτn : τ < (n : ℝ))
    (hbound : ∃ C > 0, ∀ x, ‖f x‖ ≤ Real.exp (C * (r x) ^ τ)) :
    ∃ C > 0, ∀ x, ‖f x‖ ≤ Real.exp (C * (r x) ^ n) := by
  rcases hbound with ⟨C, hCpos, hC⟩
  have hweak :
      ∀ x, ‖f x‖ ≤ Real.exp (C * (r x) ^ (n : ℝ)) :=
    norm_le_exp_mul_rpow_of_exponent_le
      (f := f) (r := r) hCpos.le hr (le_of_lt hτn) hC
  refine ⟨C, hCpos, ?_⟩
  intro x
  have hpow : (r x) ^ (n : ℝ) = (r x) ^ n := Real.rpow_natCast (r x) n
  simpa [hpow] using hweak x

theorem sq_le_exp_const_mul_rpow {b r : ℝ} (hb : 0 < b) (hr : 1 ≤ r) :
    r ^ 2 ≤ exp ((4 / b) * r ^ b) := by
  have hrpos : 0 < r := zero_lt_one.trans_le hr
  have hcoeff2 : 0 ≤ (2 / b : ℝ) := by positivity
  have hcoeff4 : 0 ≤ (4 / b : ℝ) := by positivity
  have hlog_le : log r ≤ (2 / b) * r ^ (b / 2) := by
    have hle_exp : (b / 2) * log r ≤ exp ((b / 2) * log r) := le_exp_self _
    calc
      log r = (2 / b) * ((b / 2) * log r) := by
        field_simp [ne_of_gt hb]
      _ ≤ (2 / b) * exp ((b / 2) * log r) :=
        mul_le_mul_of_nonneg_left hle_exp hcoeff2
      _ = (2 / b) * r ^ (b / 2) := by
        simp [rpow_def_of_pos hrpos, mul_comm]
  have hpow_le : r ^ (b / 2) ≤ r ^ b :=
    rpow_le_rpow_of_exponent_le hr (by linarith)
  have hlog_sq : log (r ^ 2) ≤ (4 / b) * r ^ b := by
    calc
      log (r ^ 2) = 2 * log r := by
        simp [log_pow]
      _ ≤ 2 * ((2 / b) * r ^ (b / 2)) :=
        mul_le_mul_of_nonneg_left hlog_le (by norm_num)
      _ = (4 / b) * r ^ (b / 2) := by ring
      _ ≤ (4 / b) * r ^ b :=
        mul_le_mul_of_nonneg_left hpow_le hcoeff4
  have hsq_pos : 0 < r ^ 2 := by positivity
  rw [← exp_log hsq_pos]
  exact exp_le_exp.2 hlog_sq

theorem one_add_le_three_mul_one_add_of_le_two_mul_max {x r : ℝ} (hx : 0 ≤ x)
    (hr : r ≤ 2 * max x 1) :  1 + r ≤ 3 * (1 + x) := by
  have hmax : max x 1 ≤ 1 + x := max_le_iff.2 ⟨by linarith, by linarith⟩
  nlinarith

theorem exp_mul_rpow_le_exp_mul_rpow_of_le_mul
    {A B x y τ : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hτ : 0 ≤ τ) (hxy : x ≤ B * y) : Real.exp (A * x ^ τ) ≤ Real.exp ((A * B ^ τ) * y ^ τ) := by
  refine Real.exp_le_exp.2 ?_
  have hpow : x ^ τ ≤ (B * y) ^ τ := Real.rpow_le_rpow hx hxy hτ
  have hsplit : (B * y) ^ τ = B ^ τ * y ^ τ := by
    simpa using (Real.mul_rpow (x := B) (y := y) (z := τ) hB hy)
  simpa [mul_assoc] using mul_le_mul_of_nonneg_left (hpow.trans_eq hsplit) hA

theorem exists_between_self_and_floor_add_one_same_floor {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ∃ τ : ℝ, ρ < τ ∧ τ < (Nat.floor ρ + 1 : ℝ) ∧ 0 ≤ τ ∧ Nat.floor τ = Nat.floor ρ := by
  set m : ℕ := Nat.floor ρ
  set τ : ℝ := (ρ + (m + 1 : ℝ)) / 2
  have hm : ρ < (m + 1 : ℝ) := by simpa [m] using Nat.lt_floor_add_one (a := ρ)
  have hτ : ρ < τ := by dsimp [τ]; linarith
  have hτ_lt : τ < (m + 1 : ℝ) := by dsimp [τ]; linarith
  have hτ_nonneg : 0 ≤ τ := le_trans hρ (le_of_lt hτ)
  have hfloorτ : Nat.floor τ = m := by
    have hm_le_τ : (m : ℝ) ≤ τ := le_trans (Nat.floor_le hρ) (le_of_lt hτ)
    have hτ_lt_m1 : τ < (m : ℝ) + 1 := by simpa [add_assoc, add_comm, add_left_comm] using hτ_lt
    exact (Nat.floor_eq_iff hτ_nonneg).2 ⟨hm_le_τ, hτ_lt_m1⟩
  exact ⟨τ, hτ, by simpa [m] using hτ_lt, hτ_nonneg, by simpa [m] using hfloorτ⟩

open Metric Complex

theorem log_norm_le_of_log_one_add_growth_on_sphere {f : ℂ → ℂ} {C ρ R : ℝ}
    (hC : ∀ z : ℂ, log (1 + ‖f z‖) ≤ C * (1 + ‖z‖) ^ ρ) {z : ℂ}
    (hz : z ∈ sphere (0 : ℂ) |R|) : log ‖f z‖ ≤ C * (1 + |R|) ^ ρ := by
  have hz_norm : ‖z‖ = |R| := by
    simpa [mem_sphere, dist_zero_right] using hz
  simpa [hz_norm] using le_trans (log_norm_le_log_one_add_norm (f z)) (hC z)

end Real
end
end File25

-- Upstream module PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.ValueDistribution.LogCounting.Growth
section File26
 

section
open Filter Function MeromorphicOn Metric Real Set

namespace Function.locallyFinsuppWithin

theorem logCounting_divisor_le_of_log_growth {f : ℂ → ℂ} {ρ C : ℝ} (hf : Differentiable ℂ f)
    (hC : ∀ z : ℂ, log (1 + ‖f z‖) ≤ C * (1 + ‖z‖) ^ ρ) {R : ℝ} (hR0 : 0 < R) :
    logCounting (divisor f (Set.univ : Set ℂ)) R
      ≤ C * (1 + |R|) ^ ρ + |log ‖meromorphicTrailingCoeffAt f 0‖| := by
  have hR : R ≠ 0 := ne_of_gt hR0
  have hEq :=
    logCounting_divisor_eq_circleAverage_sub_const_of_differentiable (f := f) hf hR
  have hf_sphere : MeromorphicOn f (sphere (0 : ℂ) |R|) := by
    intro z hz
    exact (hf.analyticAt z).meromorphicAt
  have hInt : CircleIntegrable (fun z : ℂ => log ‖f z‖) 0 R :=
    MeromorphicOn.circleIntegrable_log_norm hf_sphere
  have hbound_circle : ∀ z ∈ sphere (0 : ℂ) |R|,
      log ‖f z‖ ≤ C * (1 + |R|) ^ ρ := by
    intro z hz
    exact log_norm_le_of_log_one_add_growth_on_sphere hC hz
  have hCircleAvg_le :
      circleAverage (fun z : ℂ => log ‖f z‖) 0 R ≤ C * (1 + |R|) ^ ρ :=
    circleAverage_mono_on_of_le_circle (c := (0 : ℂ)) (R := R)
      (f := fun z => log ‖f z‖) hInt hbound_circle
  calc
    logCounting (divisor f (Set.univ : Set ℂ)) R
        = circleAverage (fun z : ℂ => log ‖f z‖) 0 R
            - log ‖meromorphicTrailingCoeffAt f 0‖ := by
            simpa [top_eq_univ] using hEq
    _ ≤ circleAverage (fun z : ℂ => log ‖f z‖) 0 R
          + |log ‖meromorphicTrailingCoeffAt f 0‖| := by
          have :
              -log ‖meromorphicTrailingCoeffAt f 0‖
                ≤ |log ‖meromorphicTrailingCoeffAt f 0‖| :=
            neg_le_abs (log ‖meromorphicTrailingCoeffAt f 0‖)
          linarith
    _ ≤ C * (1 + |R|) ^ ρ + |log ‖meromorphicTrailingCoeffAt f 0‖| := by
          nlinarith [hCircleAvg_le]

variable {E : Type*} [NormedAddCommGroup E] [ProperSpace E]

theorem log_two_mul_massClosedBall₀_le_logCounting {D : locallyFinsupp E ℤ} (hDnonneg : 0 ≤ D)
    {R : ℝ} (hR : 1 ≤ R) :
    (log 2) * massClosedBall₀ D R ≤ logCounting D (2 * R) := by
  classical
  have hR0 : 0 < R := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hR
  set r : ℝ := 2 * R
  have hrpos : 0 < r := by dsimp [r]; nlinarith
  let Dr := toClosedBall r D
  have hDr_fin : Set.Finite Dr.support := Dr.finiteSupport (isCompact_closedBall (0 : E) |r|)
  let F : Finset E := hDr_fin.toFinset
  let SR : Finset E :=
    (finiteSupport (toClosedBall R D) (isCompact_closedBall (0 : E) |R|)).toFinset
  let S : Finset E := SR.filter fun z => z ≠ (0 : E)
  have hS_sub : S ⊆ F := by
    intro z hzS
    have hz_mem_SR : z ∈ SR := (Finset.mem_filter.1 hzS).1
    have hzR : z ∈ (toClosedBall R D).support := by
      exact (finiteSupport (toClosedBall R D) (isCompact_closedBall (0 : E) |R|)).mem_toFinset.1
        hz_mem_SR
    have hz_norm_le_R : ‖z‖ ≤ R := by
      have := norm_le_abs_of_mem_toClosedBall_support hzR
      simpa [abs_of_pos hR0] using this
    have hz_norm_le_r : ‖z‖ ≤ |r| := by
      have : ‖z‖ ≤ r := le_trans hz_norm_le_R (by dsimp [r]; nlinarith)
      simpa [abs_of_pos hrpos] using this
    have hzD : z ∈ D.support := mem_support_of_mem_toClosedBall_support hzR
    have : z ∈ Dr.support := by
      simpa [Dr] using
        mem_toClosedBall_support_of_mem_support_of_norm_le_abs (D := D) (r := r) hzD hz_norm_le_r
    exact hDr_fin.mem_toFinset.2 this
  have hlogCounting :
      logCounting D r
        = (F.sum fun z => (Dr z : ℝ) * log (r * ‖z‖⁻¹)) + (D 0 : ℝ) * log r := by
    have hsupp : Function.support (fun z => (Dr z : ℝ) * log (r * ‖z‖⁻¹)) ⊆ F := by
      intro z hz
      have : Dr z ≠ 0 := by
        by_contra h0
        simp [Function.mem_support, h0] at hz
      have : z ∈ Dr.support := by simpa [Function.mem_support] using this
      exact hDr_fin.mem_toFinset.2 this
    simp [logCounting, Dr, r,
      finsum_eq_sum_of_support_subset (f := fun z => (Dr z : ℝ) * log (r * ‖z‖⁻¹)) (s := F) hsupp]
  have hsum_le :
      (log 2) * (S.sum fun z => (D z : ℝ))
        ≤ F.sum (fun z => (Dr z : ℝ) * log (r * ‖z‖⁻¹)) := by
    have hterm_nonneg : ∀ z ∈ F, 0 ≤ (Dr z : ℝ) * log (r * ‖z‖⁻¹) := by
      intro z hzF
      have hz_sup : z ∈ Dr.support := hDr_fin.mem_toFinset.1 hzF
      have hDz : 0 ≤ Dr z := by
        have hDz' : 0 ≤ D z := hDnonneg z
        have hDrz : Dr z = D z :=
          toClosedBall_eval_eq_of_norm_le_abs (norm_le_abs_of_mem_toClosedBall_support hz_sup)
        simpa [hDrz] using hDz'
      have hlog : 0 ≤ log (r * ‖z‖⁻¹) := by
        have hzle : ‖z‖ ≤ r := by
          have hnorm := norm_le_abs_of_mem_toClosedBall_support hz_sup
          simpa [abs_of_pos hrpos] using hnorm
        exact log_nonneg_mul_inv_norm_of_norm_le hzle
      exact mul_nonneg (by exact_mod_cast hDz) hlog
    have hsumSF :
        S.sum (fun z => (Dr z : ℝ) * log (r * ‖z‖⁻¹))
          ≤ F.sum (fun z => (Dr z : ℝ) * log (r * ‖z‖⁻¹)) :=
      Finset.sum_le_sum_of_subset_of_nonneg hS_sub (by
        intro z hzF _; exact hterm_nonneg z hzF)
    have hterm_ge : ∀ z ∈ S, (log 2) * (D z : ℝ) ≤ (Dr z : ℝ) * log (r * ‖z‖⁻¹) := by
      intro z hzS
      have hz0 : z ≠ (0 : E) := (Finset.mem_filter.1 hzS).2
      have hz_norm_le_R : ‖z‖ ≤ R := by
        have hz_mem_SR : z ∈ SR := (Finset.mem_filter.1 hzS).1
        have hzRsup : z ∈ (toClosedBall R D).support := by
          exact (finiteSupport (toClosedBall R D) (isCompact_closedBall (0 : E) |R|)).mem_toFinset.1
            hz_mem_SR
        have hnorm := norm_le_abs_of_mem_toClosedBall_support hzRsup
        simpa [abs_of_pos hR0] using hnorm
      have hlog_le : log 2 ≤ log (r * ‖z‖⁻¹) := by
        simpa [r] using log_two_le_log_two_mul_mul_inv_norm_of_norm_le hz0 hz_norm_le_R
      have hDz_nonneg : 0 ≤ D z := hDnonneg z
      have hz_in_ballr : z ∈ closedBall (0 : E) |r| := by
        have : ‖z‖ ≤ r := le_trans hz_norm_le_R (by dsimp [r]; nlinarith)
        simpa [mem_closedBall, dist_zero_right, abs_of_pos hrpos] using this
      have hDrz : Dr z = D z := by
        have hz_norm_le : ‖z‖ ≤ |r| := by
          simpa [mem_closedBall, dist_zero_right] using hz_in_ballr
        simpa [Dr] using toClosedBall_eval_eq_of_norm_le_abs (D := D) (r := r) (z := z) hz_norm_le
      have : (log 2) * (D z : ℝ) ≤ (log (r * ‖z‖⁻¹)) * (D z : ℝ) :=
        mul_le_mul_of_nonneg_right hlog_le (by exact_mod_cast hDz_nonneg)
      simpa [hDrz, mul_assoc, mul_left_comm, mul_comm] using this
    calc
      (log 2) * (S.sum fun z => (D z : ℝ))
          = S.sum (fun z => (log 2) * (D z : ℝ)) := by simp [Finset.mul_sum]
      _ ≤ S.sum (fun z => (Dr z : ℝ) * log (r * ‖z‖⁻¹)) :=
        Finset.sum_le_sum fun z hz => hterm_ge z hz
      _ ≤ F.sum (fun z => (Dr z : ℝ) * log (r * ‖z‖⁻¹)) := hsumSF
  have hcenter_nonneg : 0 ≤ (D 0 : ℝ) * log r := by
    have hD0 : 0 ≤ D 0 := hDnonneg 0
    have hlogr : 0 ≤ log r := log_nonneg (by nlinarith [hR])
    exact mul_nonneg (by exact_mod_cast hD0) hlogr
  have : (log 2) * (S.sum fun z => (D z : ℝ)) ≤ logCounting D r := by
    rw [hlogCounting]
    nlinarith [hsum_le, hcenter_nonneg]
  simpa [massClosedBall₀, r, S, SR] using this

theorem massClosedBall₀_divisor_le_of_log_growth {f : ℂ → ℂ} {ρ C : ℝ}
    (hf : Differentiable ℂ f)
    (hC : ∀ z : ℂ, log (1 + ‖f z‖) ≤ C * (1 + ‖z‖) ^ ρ) {R : ℝ} (hR : 1 ≤ R) :
    massClosedBall₀ (divisor f (Set.univ : Set ℂ)) R
      ≤ (C * (1 + |2 * R|) ^ ρ + |log ‖meromorphicTrailingCoeffAt f 0‖|) / log 2 := by
  have hR0 : 0 < R := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hR
  have hlog2pos : 0 < log 2 := log_pos (by norm_num : (1 : ℝ) < 2)
  have hlow :
      (log 2) * massClosedBall₀ (divisor f (Set.univ : Set ℂ)) R
        ≤ logCounting (divisor f (Set.univ : Set ℂ)) (2 * R) :=
    log_two_mul_massClosedBall₀_le_logCounting
      (D := divisor f (Set.univ : Set ℂ))
      (MeromorphicOn.AnalyticOnNhd.divisor_nonneg
        (hf.differentiableOn.analyticOnNhd isOpen_univ)) hR
  have hupp :
      logCounting (divisor f (Set.univ : Set ℂ)) (2 * R)
        ≤ C * (1 + |2 * R|) ^ ρ + |log ‖meromorphicTrailingCoeffAt f 0‖| := by
    have h2R0 : 0 < 2 * R := by nlinarith [hR0]
    simpa using logCounting_divisor_le_of_log_growth (f := f) (ρ := ρ) (C := C) hf hC
      (R := 2 * R) h2R0
  have hmul :
      (log 2) * massClosedBall₀ (divisor f (Set.univ : Set ℂ)) R
        ≤ C * (1 + |2 * R|) ^ ρ + |log ‖meromorphicTrailingCoeffAt f 0‖| :=
    hlow.trans hupp
  have hmul' :
      massClosedBall₀ (divisor f (Set.univ : Set ℂ)) R * log 2
        ≤ C * (1 + |2 * R|) ^ ρ + |log ‖meromorphicTrailingCoeffAt f 0‖| := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
  exact (le_div_iff₀ hlog2pos).2 hmul'

end Function.locallyFinsuppWithin
end
end File26

-- Upstream module PrimeNumberTheoremAnd.Mathlib.Analysis.Meromorphic.DivisorHolomorphic
section File27
 

section
open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem Differentiable.divisor_nonneg {f : ℂ → E} (hf : Differentiable ℂ f) :
    0 ≤ MeromorphicOn.divisor f (univ : Set ℂ) :=
  MeromorphicOn.AnalyticOnNhd.divisor_nonneg (hf.differentiableOn.analyticOnNhd isOpen_univ)
end
end File27

-- Upstream module PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Log.Dyadic
section File28
 

section
noncomputable section

open scoped BigOperators
open Filter

namespace Real

lemma two_pow_floor_logb_le {x : ℝ} (hx : 1 ≤ x) :
    (2 : ℝ) ^ (⌊Real.logb 2 x⌋₊ : ℝ) ≤ x := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hx
  have hlog_nonneg : 0 ≤ Real.logb 2 x :=
    Real.logb_nonneg (b := (2 : ℝ)) (by norm_num : (1 : ℝ) < 2) hx
  have hfloor_le : (⌊Real.logb 2 x⌋₊ : ℝ) ≤ Real.logb 2 x := by
    simpa using (Nat.floor_le hlog_nonneg)
  exact (Real.le_logb_iff_rpow_le (b := (2 : ℝ))
    (x := (⌊Real.logb 2 x⌋₊ : ℝ)) (y := x)
    (by norm_num : (1 : ℝ) < 2) hx0).1 hfloor_le

lemma lt_two_pow_floor_logb_add_one {x : ℝ} (hx : 1 ≤ x) :
    x < (2 : ℝ) ^ ((⌊Real.logb 2 x⌋₊ : ℝ) + 1) := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hx
  have hlt : Real.logb 2 x < (⌊Real.logb 2 x⌋₊ : ℝ) + 1 := by
    simpa using (Nat.lt_floor_add_one (Real.logb 2 x))
  exact (Real.logb_lt_iff_lt_rpow (b := (2 : ℝ)) (x := x)
    (y := (⌊Real.logb 2 x⌋₊ : ℝ) + 1)
    (by norm_num : (1 : ℝ) < 2) hx0).1 hlt

lemma dyadicShell_lower_bound {r0 x : ℝ} {k : ℕ} (hr0 : 0 < r0) (hx : r0 ≤ x)
    (hk : ⌊Real.logb 2 (x / r0)⌋₊ = k) :
    r0 * (2 : ℝ) ^ (k : ℝ) ≤ x := by
  have hr0ne : r0 ≠ 0 := ne_of_gt hr0
  have hx1 : (1 : ℝ) ≤ x / r0 := by
    have : r0 / r0 ≤ x / r0 := div_le_div_of_nonneg_right hx hr0.le
    simpa [hr0ne] using this
  have hle : (2 : ℝ) ^ (k : ℝ) ≤ x / r0 := by
    have := Real.two_pow_floor_logb_le (x := x / r0) hx1
    simpa [hk] using this
  have := mul_le_mul_of_nonneg_left hle hr0.le
  have hxEq : r0 * (x / r0) = x := by
    field_simp [hr0ne]
  simpa [mul_assoc, hxEq] using this

lemma dyadicShell_upper_bound {r0 x : ℝ} {k : ℕ} (hr0 : 0 < r0) (hx : r0 ≤ x)
    (hk : ⌊Real.logb 2 (x / r0)⌋₊ = k) :
    x ≤ r0 * (2 : ℝ) ^ ((k : ℝ) + 1) := by
  have hr0ne : r0 ≠ 0 := ne_of_gt hr0
  have hx1 : (1 : ℝ) ≤ x / r0 := by
    have : r0 / r0 ≤ x / r0 := div_le_div_of_nonneg_right hx hr0.le
    simpa [hr0ne] using this
  have hlt : x / r0 < (2 : ℝ) ^ ((k : ℝ) + 1) := by
    have := Real.lt_two_pow_floor_logb_add_one (x := x / r0) hx1
    simpa [hk] using this
  have := mul_lt_mul_of_pos_left hlt hr0
  have hxEq : r0 * (x / r0) = x := by
    field_simp [hr0ne]
  exact le_of_lt (by simpa [mul_assoc, hxEq] using this)

lemma exists_nat_le_two_pow (A : ℝ) :
    ∃ k0 : ℕ, ∀ n ≥ k0, A ≤ (2 : ℝ) ^ n := by
  have htend : Tendsto (fun n : ℕ => (2 : ℝ) ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (r := (2 : ℝ)) (by norm_num : (1 : ℝ) < 2)
  exact eventually_atTop.1 ((tendsto_atTop.1 htend) A)

lemma one_le_dyadicRadius_succ_of_inv_le_two_pow
    {r0 : ℝ} {k0 kk : ℕ} (hr0 : 0 < r0)
    (hk0 : ∀ n ≥ k0, (1 / r0 : ℝ) ≤ (2 : ℝ) ^ n) (hkk : k0 ≤ kk + 1) :
    (1 : ℝ) ≤ r0 * (2 : ℝ) ^ ((kk : ℝ) + 1) := by
  have hr0ne : r0 ≠ 0 := ne_of_gt hr0
  have hpow_nat : (1 / r0 : ℝ) ≤ (2 : ℝ) ^ (kk + 1) := hk0 (kk + 1) hkk
  have hpow_rpow : (1 / r0 : ℝ) ≤ (2 : ℝ) ^ ((kk : ℝ) + 1) := by
    have hcast : (2 : ℝ) ^ ((kk : ℝ) + 1) = (2 : ℝ) ^ (kk + 1) := by
      calc
        (2 : ℝ) ^ ((kk : ℝ) + 1) = (2 : ℝ) ^ ((kk + 1 : ℕ) : ℝ) := by
          simp [Nat.cast_add, Nat.cast_one]
        _ = (2 : ℝ) ^ (kk + 1) := by
          simpa using (Real.rpow_natCast (2 : ℝ) (kk + 1))
    simpa [hcast] using hpow_nat
  have : (r0 * (1 / r0) : ℝ) ≤ r0 * (2 : ℝ) ^ ((kk : ℝ) + 1) :=
    mul_le_mul_of_nonneg_left hpow_rpow hr0.le
  simpa [one_div, hr0ne, mul_assoc] using this

lemma one_add_abs_two_mul_dyadicRadius_rpow_le {r0 ρ : ℝ} (k : ℕ)
    (hr0 : 0 < r0) (hρ : 0 ≤ ρ) :
    (1 + |2 * (r0 * (2 : ℝ) ^ ((k : ℝ) + 1))|) ^ ρ
      ≤ (1 + 4 * r0) ^ ρ * ((2 : ℝ) ^ ρ) ^ k := by
  let Rk : ℝ := r0 * (2 : ℝ) ^ ((k : ℝ) + 1)
  have hRk' : |2 * Rk| = 4 * r0 * (2 : ℝ) ^ (k : ℝ) := by
    have hnonneg : 0 ≤ (2 : ℝ) * Rk := by
      have : 0 ≤ Rk := by
        dsimp [Rk]
        exact mul_nonneg hr0.le (le_of_lt (Real.rpow_pos_of_pos (by norm_num) _))
      nlinarith
    have hmul : (2 : ℝ) * Rk = 4 * r0 * (2 : ℝ) ^ (k : ℝ) := by
      dsimp [Rk]
      calc
        (2 : ℝ) * (r0 * (2 : ℝ) ^ ((k : ℝ) + 1))
            = (2 * r0) * (2 : ℝ) ^ ((k : ℝ) + 1) := by ring
        _ = (2 * r0) * ((2 : ℝ) ^ (k : ℝ) * (2 : ℝ) ^ (1 : ℝ)) := by
              simp [Real.rpow_add, mul_assoc]
        _ = (2 * r0) * ((2 : ℝ) ^ (k : ℝ) * 2) := by simp [Real.rpow_one]
        _ = 4 * r0 * (2 : ℝ) ^ (k : ℝ) := by ring
    calc
      |2 * Rk| = 2 * Rk := abs_of_nonneg hnonneg
      _ = 4 * r0 * (2 : ℝ) ^ (k : ℝ) := hmul
  have hbase :
      (1 + |2 * Rk|) ≤ (1 + 4 * r0) * (2 : ℝ) ^ (k : ℝ) := by
    have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ (k : ℝ) := by
      have : (1 : ℝ) ≤ (2 : ℝ) ^ (k : ℕ) := by
        simpa using (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ (2 : ℝ)))
      simpa [Real.rpow_natCast] using this
    have habs :
        1 + |2 * Rk| ≤ (2 : ℝ) ^ (k : ℝ) + (4 * r0) * (2 : ℝ) ^ (k : ℝ) := by
      rw [hRk']
      simpa [add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm] using
        (add_le_add_right h1 ((4 * r0) * (2 : ℝ) ^ (k : ℝ)))
    have hfac :
        (2 : ℝ) ^ (k : ℝ) + (4 * r0) * (2 : ℝ) ^ (k : ℝ)
          = (1 + 4 * r0) * (2 : ℝ) ^ (k : ℝ) := by
      ring
    exact habs.trans (le_of_eq hfac)
  have hRnonneg : 0 ≤ (1 + |2 * Rk|) := by linarith [abs_nonneg (2 * Rk)]
  have :
      (1 + |2 * Rk|) ^ ρ ≤ ((1 + 4 * r0) * (2 : ℝ) ^ (k : ℝ)) ^ ρ :=
    Real.rpow_le_rpow hRnonneg hbase hρ
  have hsplit :
      ((1 + 4 * r0) * (2 : ℝ) ^ (k : ℝ)) ^ ρ
        = (1 + 4 * r0) ^ ρ * ((2 : ℝ) ^ (k : ℝ)) ^ ρ := by
    have h1 : 0 ≤ (1 + 4 * r0) := by nlinarith [hr0.le]
    have h2 : 0 ≤ (2 : ℝ) ^ (k : ℝ) :=
      le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)
    simpa using (Real.mul_rpow h1 h2 (z := ρ))
  have hpow : ((2 : ℝ) ^ (k : ℝ)) ^ ρ = ((2 : ℝ) ^ ρ) ^ k := by
    have h2nonneg : (0 : ℝ) ≤ 2 := by norm_num
    calc
      ((2 : ℝ) ^ (k : ℝ)) ^ ρ = (2 : ℝ) ^ ((k : ℝ) * ρ) := by
        simp [Real.rpow_mul]
      _ = ((2 : ℝ) ^ ρ) ^ (k : ℝ) := by
        simpa [mul_comm] using
          (Real.rpow_mul (x := (2 : ℝ)) (y := ρ) (z := (k : ℝ)) h2nonneg)
      _ = ((2 : ℝ) ^ ρ) ^ k := by
        simp [Real.rpow_natCast]
  calc
    (1 + |2 * (r0 * (2 : ℝ) ^ ((k : ℝ) + 1))|) ^ ρ
        = (1 + |2 * Rk|) ^ ρ := by rfl
    _ ≤ ((1 + 4 * r0) * (2 : ℝ) ^ (k : ℝ)) ^ ρ := this
    _ = (1 + 4 * r0) ^ ρ * ((2 : ℝ) ^ (k : ℝ)) ^ ρ := hsplit
    _ = (1 + 4 * r0) ^ ρ * ((2 : ℝ) ^ ρ) ^ k := by
      simpa [mul_assoc] using congrArg (fun t => (1 + 4 * r0) ^ ρ * t) hpow

lemma tsum_inv_rpow_le_card_mul_of_lower_bound {α : Type*} [Fintype α] {a : α → ℝ}
    {R τ : ℝ} (hR : 0 < R) (hτ : 0 < τ) (ha_nonneg : ∀ x, 0 ≤ a x)
    (ha_lower : ∀ x, R ≤ a x) :
    (∑' x : α, (a x)⁻¹ ^ τ) ≤ (Fintype.card α : ℝ) * (R⁻¹ ^ τ) := by
  have hsum_le :
      (∑ x : α, (a x)⁻¹ ^ τ) ≤ ∑ _x : α, R⁻¹ ^ τ := by
    refine Finset.sum_le_sum ?_
    intro x _hx
    have hinv : (a x)⁻¹ ≤ R⁻¹ := by
      simpa using (inv_anti₀ hR (ha_lower x))
    exact Real.rpow_le_rpow (inv_nonneg.2 (ha_nonneg x)) hinv hτ.le
  simpa [tsum_fintype, Finset.sum_const, nsmul_eq_mul, mul_comm] using hsum_le

lemma inv_dyadicRadius_rpow_eq (r0 τ : ℝ) (k : ℕ) (hr0 : 0 ≤ r0) :
    (r0 * (2 : ℝ) ^ (k : ℝ))⁻¹ ^ τ =
      (r0⁻¹ : ℝ) ^ τ * ((2 : ℝ) ^ (-τ)) ^ k := by
  have h2k_nonneg : 0 ≤ (2 : ℝ) ^ (k : ℝ) :=
    le_of_lt (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _)
  calc
    (r0 * (2 : ℝ) ^ (k : ℝ))⁻¹ ^ τ =
        (r0 * (2 : ℝ) ^ (k : ℝ)) ^ (-τ) := by
      simpa using (Real.rpow_neg_eq_inv_rpow (r0 * (2 : ℝ) ^ (k : ℝ)) τ).symm
    _ = r0 ^ (-τ) * (((2 : ℝ) ^ (k : ℝ)) ^ (-τ)) := by
      simpa using (Real.mul_rpow hr0 h2k_nonneg (z := -τ))
    _ = (r0⁻¹ : ℝ) ^ τ * ((2 : ℝ) ^ (-τ)) ^ k := by
      have hr0' : r0 ^ (-τ) = (r0⁻¹ : ℝ) ^ τ := by
        simp [Real.rpow_neg_eq_inv_rpow]
      have h2' : ((2 : ℝ) ^ (k : ℝ)) ^ (-τ) = ((2 : ℝ) ^ (-τ)) ^ k := by
        have h2nonneg : (0 : ℝ) ≤ (2 : ℝ) := by norm_num
        calc
          ((2 : ℝ) ^ (k : ℝ)) ^ (-τ) = (2 : ℝ) ^ ((k : ℝ) * (-τ)) := by
            exact (Real.rpow_mul (x := (2 : ℝ)) (y := (k : ℝ)) (z := -τ)
              h2nonneg).symm
          _ = (2 : ℝ) ^ ((-τ) * (k : ℝ)) := by ring_nf
          _ = ((2 : ℝ) ^ (-τ)) ^ (k : ℝ) := by
            exact Real.rpow_mul (x := (2 : ℝ)) (y := -τ) (z := (k : ℝ)) h2nonneg
          _ = ((2 : ℝ) ^ (-τ)) ^ k := by
            simp [Real.rpow_natCast]
      calc
        r0 ^ (-τ) * (((2 : ℝ) ^ (k : ℝ)) ^ (-τ))
            = (r0⁻¹ : ℝ) ^ τ * (((2 : ℝ) ^ (k : ℝ)) ^ (-τ)) := by
              rw [hr0']
        _ = (r0⁻¹ : ℝ) ^ τ * ((2 : ℝ) ^ (-τ)) ^ k := by
              rw [h2']

lemma two_rpow_sub_eq_mul_neg (ρ τ : ℝ) :
    (2 : ℝ) ^ (ρ - τ) = (2 : ℝ) ^ ρ * (2 : ℝ) ^ (-τ) := by
  have h2pos : (0 : ℝ) < (2 : ℝ) := by norm_num
  calc
    (2 : ℝ) ^ (ρ - τ) = (2 : ℝ) ^ (ρ + (-τ)) := by ring_nf
    _ = (2 : ℝ) ^ ρ * (2 : ℝ) ^ (-τ) := by
      simp [Real.rpow_add h2pos]

lemma two_rpow_sub_pow_eq_mul_pow (ρ τ : ℝ) (k : ℕ) :
    ((2 : ℝ) ^ (ρ - τ)) ^ k =
      ((2 : ℝ) ^ ρ) ^ k * (((2 : ℝ) ^ (-τ)) ^ k) := by
  simp [two_rpow_sub_eq_mul_neg, mul_pow]

lemma dyadic_growth_inv_term_eq (C L M r0 ρ τ : ℝ) (k : ℕ) (hr0 : 0 ≤ r0) :
    ((C / L) * (M * ((2 : ℝ) ^ ρ) ^ k)) *
        ((r0 * (2 : ℝ) ^ (k : ℝ))⁻¹ ^ τ)
      = (((C / L) * M) * (r0⁻¹ : ℝ) ^ τ) * ((2 : ℝ) ^ (ρ - τ)) ^ k := by
  have hrk_inv :
      (r0 * (2 : ℝ) ^ (k : ℝ))⁻¹ ^ τ =
        (r0⁻¹ : ℝ) ^ τ * (((2 : ℝ) ^ (-τ)) ^ k) :=
    inv_dyadicRadius_rpow_eq r0 τ k hr0
  rw [hrk_inv, two_rpow_sub_pow_eq_mul_pow]
  ac_rfl

lemma dyadic_trailing_inv_term_le (C L r0 τ : ℝ) (k : ℕ) (hr0 : 0 ≤ r0) :
    (C / L) * ((r0 * (2 : ℝ) ^ (k : ℝ))⁻¹ ^ τ)
      ≤ (((C / L) + 1) * (r0⁻¹ : ℝ) ^ τ) * ((2 : ℝ) ^ (-τ)) ^ k := by
  rw [inv_dyadicRadius_rpow_eq r0 τ k hr0]
  have hcoeff : C / L ≤ C / L + 1 := by linarith
  have hr0Inv_nonneg : 0 ≤ (r0⁻¹ : ℝ) ^ τ :=
    Real.rpow_nonneg (inv_nonneg.2 hr0) _
  have hmul :
      (C / L) * ((r0⁻¹ : ℝ) ^ τ)
        ≤ ((C / L) + 1) * ((r0⁻¹ : ℝ) ^ τ) :=
    mul_le_mul_of_nonneg_right hcoeff hr0Inv_nonneg
  have hqpow_nonneg : 0 ≤ ((2 : ℝ) ^ (-τ)) ^ k :=
    pow_nonneg (le_of_lt (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _)) _
  have := mul_le_mul_of_nonneg_right hmul hqpow_nonneg
  simpa [mul_assoc, mul_left_comm, mul_comm] using this

lemma dyadic_growth_mass_mul_inv_le_geometric {C L M X T Ctrail r0 ρ τ : ℝ} {k : ℕ}
    (hL : 0 < L) (hC : 0 ≤ C) (hr0 : 0 ≤ r0)
    (hX : X ≤ M * ((2 : ℝ) ^ ρ) ^ k)
    (hT : T ≤ ((C * X + Ctrail) / L) * ((r0 * (2 : ℝ) ^ (k : ℝ))⁻¹ ^ τ)) :
    T ≤ (((C / L) * M) * (r0⁻¹ : ℝ) ^ τ) * ((2 : ℝ) ^ (ρ - τ)) ^ k
        + (((Ctrail / L) + 1) * (r0⁻¹ : ℝ) ^ τ) * ((2 : ℝ) ^ (-τ)) ^ k := by
  have hmul : C * X ≤ C * (M * ((2 : ℝ) ^ ρ) ^ k) :=
    mul_le_mul_of_nonneg_left hX hC
  have hnum : C * X + Ctrail ≤ C * (M * ((2 : ℝ) ^ ρ) ^ k) + Ctrail :=
    by linarith only [hmul]
  have hdiv :
      (C * X + Ctrail) / L ≤ (C * (M * ((2 : ℝ) ^ ρ) ^ k) + Ctrail) / L :=
    div_le_div_of_nonneg_right hnum hL.le
  have h2k_nonneg : 0 ≤ (2 : ℝ) ^ (k : ℝ) :=
    le_of_lt (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (k : ℝ))
  have hrk_nonneg : 0 ≤ r0 * (2 : ℝ) ^ (k : ℝ) :=
    mul_nonneg hr0 h2k_nonneg
  have hfactor_nonneg : 0 ≤ ((r0 * (2 : ℝ) ^ (k : ℝ))⁻¹ ^ τ) :=
    Real.rpow_nonneg (inv_nonneg.2 hrk_nonneg) τ
  have hmul' :=
    mul_le_mul_of_nonneg_right hdiv hfactor_nonneg
  have hdecomp :
      ((C * (M * ((2 : ℝ) ^ ρ) ^ k) + Ctrail) / L) *
          ((r0 * (2 : ℝ) ^ (k : ℝ))⁻¹ ^ τ)
        =
        ((C / L) * (M * ((2 : ℝ) ^ ρ) ^ k)) *
            ((r0 * (2 : ℝ) ^ (k : ℝ))⁻¹ ^ τ)
          + ((Ctrail / L) * ((r0 * (2 : ℝ) ^ (k : ℝ))⁻¹ ^ τ)) := by
    let Y : ℝ := (r0 * (2 : ℝ) ^ (k : ℝ))⁻¹ ^ τ
    have :
        ((C * (M * ((2 : ℝ) ^ ρ) ^ k) + Ctrail) / L) * Y
          = ((C / L) * (M * ((2 : ℝ) ^ ρ) ^ k)) * Y
            + ((Ctrail / L) * Y) := by
      ring
    simpa [Y]
  have hpre :
      T ≤ ((C / L) * (M * ((2 : ℝ) ^ ρ) ^ k)) *
            ((r0 * (2 : ℝ) ^ (k : ℝ))⁻¹ ^ τ)
          + ((Ctrail / L) * ((r0 * (2 : ℝ) ^ (k : ℝ))⁻¹ ^ τ)) :=
    hT.trans (hmul'.trans_eq hdecomp)
  have hA := le_of_eq (dyadic_growth_inv_term_eq C L M r0 ρ τ k hr0)
  have hB := dyadic_trailing_inv_term_le Ctrail L r0 τ k hr0
  exact hpre.trans (by
    simpa [mul_assoc, mul_left_comm, mul_comm] using add_le_add hA hB)

lemma two_geometric_shift_add (A B q qσ : ℝ) (k k0 : ℕ) :
    A * q ^ (k + k0) + B * qσ ^ (k + k0)
      = (A * q ^ k0) * q ^ k + (B * qσ ^ k0) * qσ ^ k := by
  rw [pow_add, pow_add]
  ac_rfl

end Real
end
end
end File28

-- Upstream module PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.HadamardFactorization.Summability
section File29
 

section
noncomputable section

open Filter Topology Set Complex
open scoped BigOperators Topology

namespace Complex.Hadamard

open scoped Real

noncomputable def divisorMassClosedBall₀ (f : ℂ → ℂ) (R : ℝ) : ℝ :=
  Function.locallyFinsuppWithin.massClosedBall₀ (MeromorphicOn.divisor f (Set.univ : Set ℂ)) R

theorem jensen_formula_logCounting_eq_circleAverage_sub_log_trailingCoeff {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {R : ℝ} (hR : R ≠ 0) :
    Function.locallyFinsuppWithin.logCounting (MeromorphicOn.divisor f (Set.univ : Set ℂ)) R
      = Real.circleAverage (fun z : ℂ => Real.log ‖f z‖) 0 R
        - Real.log ‖meromorphicTrailingCoeffAt f 0‖ :=
  Function.locallyFinsuppWithin.logCounting_divisor_eq_circleAverage_sub_const_of_differentiable
    hf hR

lemma log_two_mul_divisorMassClosedBall₀_le_logCounting_two_mul {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {R : ℝ} (hR : 1 ≤ R) :
    (Real.log 2) * divisorMassClosedBall₀ f R
      ≤ Function.locallyFinsuppWithin.logCounting
          (MeromorphicOn.divisor f (Set.univ : Set ℂ)) (2 * R) :=
  Function.locallyFinsuppWithin.log_two_mul_massClosedBall₀_le_logCounting
    (D := MeromorphicOn.divisor f (Set.univ : Set ℂ))
    (Differentiable.divisor_nonneg hf) hR

lemma divisorMassClosedBall₀_le_of_growth {f : ℂ → ℂ} {ρ C : ℝ}
    (hf : Differentiable ℂ f)
    (hC : ∀ z : ℂ, Real.log (1 + ‖f z‖) ≤ C * (1 + ‖z‖) ^ ρ)
    {R : ℝ} (hR : 1 ≤ R) :
    divisorMassClosedBall₀ f R
      ≤ (C * (1 + |2 * R|) ^ ρ + |Real.log ‖meromorphicTrailingCoeffAt f 0‖|) /
          Real.log 2 := by
  simpa [divisorMassClosedBall₀] using
    (Function.locallyFinsuppWithin.massClosedBall₀_divisor_le_of_log_growth
      (f := f) (ρ := ρ) (C := C) hf hC hR)

lemma divisorMassClosedBall₀_mono {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {R₁ R₂ : ℝ} (hR₁ : 0 ≤ R₁) (hR₁₂ : R₁ ≤ R₂) :
    divisorMassClosedBall₀ f R₁ ≤ divisorMassClosedBall₀ f R₂ := by
  simpa [divisorMassClosedBall₀] using
    Function.locallyFinsuppWithin.massClosedBall₀_mono
      (D := MeromorphicOn.divisor f (Set.univ : Set ℂ))
      (Differentiable.divisor_nonneg hf) hR₁ hR₁₂

lemma exists_r0_le_norm_divisorZeroIndex₀_val {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hnot : ∃ z : ℂ, f z ≠ 0) :
    ∃ r0 : ℝ, 0 < r0 ∧
      ∀ p : divisorZeroIndex₀ f (Set.univ : Set ℂ), r0 ≤ ‖divisorZeroIndex₀_val p‖ := by
  classical
  set U : Set ℂ := (Set.univ : Set ℂ)
  set D : Function.locallyFinsuppWithin U ℤ := MeromorphicOn.divisor f U
  have hDnonneg : 0 ≤ D := by
    simpa [D, U] using (Differentiable.divisor_nonneg (f := f) hf)
  have hzero : ∀ p : divisorZeroIndex₀ f U, f (divisorZeroIndex₀_val p) = 0 := by
    intro p
    set z : ℂ := divisorZeroIndex₀_val p
    have hneTop : meromorphicOrderAt f z ≠ ⊤ := by
      have hzAnal : AnalyticAt ℂ f z := hf.analyticAt z
      have hzA : analyticOrderAt f z ≠ ⊤ :=
        analyticOrderAt_ne_top_of_exists_ne_zero (f := f) (hf := hf) hnot (z := z)
      intro htop
      have hm : meromorphicOrderAt f z = (analyticOrderAt f z).map (↑) :=
        hzAnal.meromorphicOrderAt_eq (𝕜 := ℂ)
      cases h : analyticOrderAt f z with
      | top =>
          exact hzA (by simp [h])
      | coe n =>
          have : (analyticOrderAt f z).map (↑) ≠ (⊤ : WithTop ℤ) := by
            simp [h]
          exact this (by simpa [hm] using htop)
    have hmon : MeromorphicOn f U := by
      intro w hw; exact (hf.analyticAt w).meromorphicAt
    have hdiv : MeromorphicOn.divisor f U z = (meromorphicOrderAt f z).untop₀ := by
      simpa [U] using (MeromorphicOn.divisor_apply (f := f) (U := U) (z := z) hmon (by aesop))
    have hDz : MeromorphicOn.divisor f U z ≠ 0 := by
      have hzsup : z ∈ (MeromorphicOn.divisor f U).support := by
        simp [z]
      simpa [Function.mem_support] using hzsup
    have hposZ : (0 : ℤ) < (meromorphicOrderAt f z).untop₀ := by
      have hge0 : 0 ≤ (meromorphicOrderAt f z).untop₀ := by
        have : 0 ≤ MeromorphicOn.divisor f U z := by
          simpa [D, U, z] using hDnonneg z
        simpa [hdiv] using this
      have hne0 : (meromorphicOrderAt f z).untop₀ ≠ 0 := by
        simpa [hdiv] using hDz
      exact lt_of_le_of_ne hge0 (by simpa [eq_comm] using hne0)
    have hpos : (0 : WithTop ℤ) < meromorphicOrderAt f z := by
      have : (0 : WithTop ℤ) < ((meromorphicOrderAt f z).untop₀ : WithTop ℤ) :=
        WithTop.coe_lt_coe.2 hposZ
      simpa [WithTop.coe_untop₀_of_ne_top hneTop] using this
    have htend0 : Tendsto f (𝓝[≠] z) (𝓝 (0 : ℂ)) :=
      tendsto_zero_of_meromorphicOrderAt_pos (f := f) (x := z) hpos
    have hcontz : ContinuousAt f z := (hf z).continuousAt
    have htendz : Tendsto f (𝓝[≠] z) (𝓝 (f z)) :=
      (hcontz.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[≠] z ≤ 𝓝 z))
    exact tendsto_nhds_unique htendz htend0
  by_cases h0 : f 0 = 0
  · have hD0 : D 0 ≠ 0 := by
      have hmero0 : MeromorphicAt f (0 : ℂ) := (hf.analyticAt 0).meromorphicAt
      have hneTop0 : meromorphicOrderAt f (0 : ℂ) ≠ ⊤ := by
        have hA0 : analyticOrderAt f (0 : ℂ) ≠ ⊤ :=
          analyticOrderAt_ne_top_of_exists_ne_zero (f := f) (hf := hf) hnot (z := 0)
        intro htop
        have hm : meromorphicOrderAt f (0 : ℂ) = (analyticOrderAt f (0 : ℂ)).map (↑) :=
          (hf.analyticAt 0).meromorphicOrderAt_eq (𝕜 := ℂ)
        cases h : analyticOrderAt f (0 : ℂ) with
        | top => exact absurd h hA0
        | coe n =>
            have : (analyticOrderAt f (0 : ℂ)).map (↑) ≠ (⊤ : WithTop ℤ) := by
              simp [h]
            exact this (by simpa [hm] using htop)
      have htend0 : Tendsto f (𝓝[≠] (0 : ℂ)) (𝓝 (0 : ℂ)) := by
        have hcont0 : ContinuousAt f (0 : ℂ) := (hf 0).continuousAt
        have : Tendsto f (𝓝 (0 : ℂ)) (𝓝 (0 : ℂ)) := by simpa [h0] using hcont0.tendsto
        exact this.mono_left (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℂ) ≤ 𝓝 (0 : ℂ))
      have hpos0 : (0 : WithTop ℤ) < meromorphicOrderAt f (0 : ℂ) :=
        (tendsto_zero_iff_meromorphicOrderAt_pos hmero0).1 htend0
      have hpos0' : (0 : ℤ) < (meromorphicOrderAt f (0 : ℂ)).untop₀ := by
        have : (0 : WithTop ℤ) < ((meromorphicOrderAt f (0 : ℂ)).untop₀ : WithTop ℤ) := by
          simpa [WithTop.coe_untop₀_of_ne_top hneTop0] using hpos0
        simpa using (WithTop.coe_lt_coe.1 this)
      have hdiv0 : D 0 = (meromorphicOrderAt f (0 : ℂ)).untop₀ := by
        have hmon : MeromorphicOn f U := by
          intro w hw; exact (hf.analyticAt w).meromorphicAt
        simpa [D, U] using
          (MeromorphicOn.divisor_apply (f := f) (U := U) (z := (0 : ℂ))
            hmon (by aesop))
      exact by
        have : (meromorphicOrderAt f (0 : ℂ)).untop₀ ≠ 0 := ne_of_gt hpos0'
        simpa [hdiv0] using this
    have hmem0 : (0 : ℂ) ∈ D.support := by
      simp [Function.mem_support, hD0]
    have hdisc : IsDiscrete D.support := by
      simpa [D] using (D.discreteSupport)
    rcases Metric.exists_ball_inter_eq_singleton_of_mem_discrete hdisc hmem0 with ⟨r0, hr0pos, hr0⟩
    refine ⟨r0, hr0pos, ?_⟩
    intro p
    have hp : divisorZeroIndex₀_val p ∈ D.support := by
      simp [D, divisorZeroIndex₀_val_mem_divisor_support (f := f) (U := U) p]
    have hnotBall : divisorZeroIndex₀_val p ∉ Metric.ball (0 : ℂ) r0 := by
      intro hball
      have : divisorZeroIndex₀_val p ∈ Metric.ball (0 : ℂ) r0 ∩ D.support := ⟨hball, hp⟩
      have : divisorZeroIndex₀_val p ∈ ({(0 : ℂ)} : Set ℂ) := by simp [hr0] at this
      have : divisorZeroIndex₀_val p = 0 := by simp [Set.mem_singleton_iff] at this
      exact (divisorZeroIndex₀_val_ne_zero p) this
    have : r0 ≤ ‖divisorZeroIndex₀_val p‖ := by
      have : ¬ ‖divisorZeroIndex₀_val p‖ < r0 := by
        intro hlt
        exact hnotBall (by simpa [Metric.mem_ball, dist_zero_right] using hlt)
      exact le_of_not_gt this
    exact this
  · have hcont0 : ContinuousAt f (0 : ℂ) := (hf 0).continuousAt
    have hne : ∀ᶠ z in 𝓝 (0 : ℂ), f z ≠ 0 := hcont0.eventually_ne h0
    rcases Metric.mem_nhds_iff.1 hne with ⟨r0, hr0pos, hr0⟩
    refine ⟨r0, hr0pos, ?_⟩
    intro p
    have : ¬ ‖divisorZeroIndex₀_val p‖ < r0 := by
      intro hlt
      have hzball : divisorZeroIndex₀_val p ∈ Metric.ball (0 : ℂ) r0 := by
        simpa [Metric.mem_ball, dist_zero_right] using hlt
      have : f (divisorZeroIndex₀_val p) ≠ 0 := hr0 hzball
      exact this (hzero p)
    exact le_of_not_gt this

open scoped BigOperators

lemma card_ball_le_divisorMassClosedBall₀
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) {R : ℝ} (hR : 0 < R) :
    (Nat.card {p : divisorZeroIndex₀ f (Set.univ : Set ℂ) // ‖divisorZeroIndex₀_val p‖ ≤ R} : ℝ)
      ≤ divisorMassClosedBall₀ f R := by
  set U : Set ℂ := (Set.univ : Set ℂ)
  set D : Function.locallyFinsuppWithin U ℤ := MeromorphicOn.divisor f U
  have :
      Fintype {p : divisorZeroIndex₀ f U // ‖divisorZeroIndex₀_val p‖ ≤ R} := by
    have : Finite {p : divisorZeroIndex₀ f U // ‖divisorZeroIndex₀_val p‖ ≤ R} := by
      have : Metric.closedBall (0 : ℂ) R ⊆ U := by simp [U]
      simpa using (finite_divisorZeroIndex₀_subtype_norm_le (f := f) (U := U) (B := R) this)
    exact Fintype.ofFinite _
  have hDnonneg : 0 ≤ D := by
    simpa [D, U] using (Differentiable.divisor_nonneg (f := f) hf)
  let SR : Finset ℂ :=
    (Function.locallyFinsuppWithin.finiteSupport (Function.locallyFinsuppWithin.toClosedBall R D)
          (isCompact_closedBall (0 : ℂ) |R|)).toFinset
  let S : Finset ℂ := SR.filter fun z : ℂ => z ≠ 0
  let T : Type :=
    Σ z : S, Fin (Int.toNat (D z.1))
  let φ :
      {p : divisorZeroIndex₀ f U // ‖divisorZeroIndex₀_val p‖ ≤ R} → T := fun p =>
    let z0 : ℂ := divisorZeroIndex₀_val p.1
    have hz0_memSR : z0 ∈ SR := by
      have hz0_norm : ‖z0‖ ≤ |R| := by
        have : ‖z0‖ ≤ R := p.2
        simpa [abs_of_pos hR] using this
      have hz0_support : z0 ∈ (Function.locallyFinsuppWithin.toClosedBall R D).support := by
        have hz0_suppD : z0 ∈ D.support := by
          simp [z0, D]
        exact Function.locallyFinsuppWithin.mem_toClosedBall_support_of_mem_support_of_norm_le_abs
          hz0_suppD hz0_norm
      exact (Set.Finite.mem_toFinset
        (Function.locallyFinsuppWithin.finiteSupport
          (Function.locallyFinsuppWithin.toClosedBall R D)
            (isCompact_closedBall (0 : ℂ) |R|))).2 hz0_support
    have hz0_ne0 : z0 ≠ 0 := divisorZeroIndex₀_val_ne_zero p.1
    have hz0_memS : z0 ∈ S := Finset.mem_filter.2 ⟨hz0_memSR, hz0_ne0⟩
    ⟨⟨z0, hz0_memS⟩, by
        simpa [z0, divisorZeroIndex₀_val, D] using p.1.1.2⟩
  have hφ_inj : Function.Injective φ := by
    intro p q hpq
    have hσ := (Sigma.mk.inj_iff).1 hpq
    have hzS : (φ p).1 = (φ q).1 := hσ.1
    have hz : divisorZeroIndex₀_val p.1 = divisorZeroIndex₀_val q.1 := by
      simpa [φ] using congrArg Subtype.val hzS
    apply Subtype.ext
    apply Subtype.ext
    apply Sigma.ext
    · exact hz
    · simpa [φ] using hσ.2
  have hcard_le :
      Fintype.card {p : divisorZeroIndex₀ f U // ‖divisorZeroIndex₀_val p‖ ≤ R} ≤ Fintype.card T :=
    Fintype.card_le_of_injective φ hφ_inj
  have hT_card :
      (Fintype.card T : ℝ) =
        (S.sum fun z : ℂ => (Int.toNat (D z) : ℝ)) := by
    have hNat :
        Fintype.card T = ∑ z : S, Int.toNat (D z.1) := by
      have h1 :
          Fintype.card T = ∑ z : S, Fintype.card (Fin (Int.toNat (D z.1))) := by
        change Fintype.card (Sigma (fun z : S => Fin (Int.toNat (D z.1))))
            = ∑ z : S, Fintype.card (Fin (Int.toNat (D z.1)))
        exact (Fintype.card_sigma (ι := S) (α := fun z : S => Fin (Int.toNat (D z.1))))
      simpa using h1
    have hR :
        (Fintype.card T : ℝ) = ∑ z : S, (Int.toNat (D z.1) : ℝ) := by
      exact_mod_cast hNat
    have hR' :
        (Fintype.card T : ℝ) = S.attach.sum (fun z : S => (Int.toNat (D z.1) : ℝ)) := by
      simpa [Finset.univ_eq_attach] using hR
    calc
      (Fintype.card T : ℝ) = S.attach.sum (fun z : S => (Int.toNat (D z.1) : ℝ)) := hR'
      _ = S.sum (fun z : ℂ => (Int.toNat (D z) : ℝ)) := by
            simpa using (Finset.sum_attach (s := S) (f := fun z : ℂ => (Int.toNat (D z) : ℝ)))
  have htoNat_le : ∀ z ∈ S, (Int.toNat (D z) : ℝ) ≤ (D z : ℝ) := by
    intro z hz
    have hDz_nonneg : 0 ≤ D z := by simpa [D] using hDnonneg z
    have hEqZ : ((Int.toNat (D z) : ℕ) : ℤ) = D z := by
      simpa using (Int.toNat_of_nonneg hDz_nonneg)
    have hEqR : (Int.toNat (D z) : ℝ) = (D z : ℝ) := by
      exact_mod_cast hEqZ
    exact le_of_eq hEqR
  calc
    (Nat.card {p : divisorZeroIndex₀ f U // ‖divisorZeroIndex₀_val p‖ ≤ R} : ℝ)
        = (Fintype.card {p : divisorZeroIndex₀ f U // ‖divisorZeroIndex₀_val p‖ ≤ R} : ℝ) := by
          simp [Nat.card_eq_fintype_card]
    _ ≤ (Fintype.card T : ℝ) := by exact_mod_cast hcard_le
    _ = S.sum (fun z : ℂ => (Int.toNat (D z) : ℝ)) := hT_card
    _ ≤ S.sum (fun z : ℂ => (D z : ℝ)) := by
      refine Finset.sum_le_sum ?_
      intro z hz
      exact htoNat_le z hz
    _ = divisorMassClosedBall₀ f R := by
      rfl

lemma card_subtype_le_divisorMassClosedBall₀_of_norm_le
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {s : Set (divisorZeroIndex₀ f (Set.univ : Set ℂ))} [Fintype s]
    {R : ℝ} (hR : 0 < R) (hs : ∀ p : s, ‖divisorZeroIndex₀_val p.1‖ ≤ R) :
    (Fintype.card s : ℝ) ≤ divisorMassClosedBall₀ f R := by
  let Aball : Type :=
    {p : divisorZeroIndex₀ f (Set.univ : Set ℂ) // ‖divisorZeroIndex₀_val p‖ ≤ R}
  have : Fintype Aball := by
    have : Finite Aball := by
      have : Metric.closedBall (0 : ℂ) R ⊆ (Set.univ : Set ℂ) := by simp
      simpa [Aball] using
        (finite_divisorZeroIndex₀_subtype_norm_le (f := f) (U := (Set.univ : Set ℂ))
          (B := R) this)
    exact Fintype.ofFinite _
  have hinj : Function.Injective (fun p : s => (⟨p.1, hs p⟩ : Aball)) := by
    intro p q hpq
    apply Subtype.ext
    exact congrArg (fun x : Aball => x.1) hpq
  have hcard_le : Fintype.card s ≤ Fintype.card Aball :=
    Fintype.card_le_of_injective _ hinj
  have hAball : (Nat.card Aball : ℝ) ≤ divisorMassClosedBall₀ f R := by
    simpa [Aball] using card_ball_le_divisorMassClosedBall₀ (f := f) hf hR
  calc
    (Fintype.card s : ℝ) ≤ (Fintype.card Aball : ℝ) := by exact_mod_cast hcard_le
    _ = (Nat.card Aball : ℝ) := by simp [Nat.card_eq_fintype_card]
    _ ≤ divisorMassClosedBall₀ f R := hAball

lemma divisorZeroIndex₀_dyadicShell_upper_bound
    {f : ℂ → ℂ} {r0 : ℝ}
    (hr0pos : 0 < r0)
    (hr0 : ∀ p : divisorZeroIndex₀ f (Set.univ : Set ℂ), r0 ≤ ‖divisorZeroIndex₀_val p‖)
    {k : ℕ} {p : divisorZeroIndex₀ f (Set.univ : Set ℂ)}
    (hp : ⌊Real.logb 2 (‖divisorZeroIndex₀_val p‖ / r0)⌋₊ = k) :
    ‖divisorZeroIndex₀_val p‖ ≤ r0 * (2 : ℝ) ^ ((k : ℝ) + 1) := by
  exact Real.dyadicShell_upper_bound (r0 := r0) (x := ‖divisorZeroIndex₀_val p‖)
    hr0pos (hr0 p) hp

lemma divisorZeroIndex₀_dyadicShell_lower_bound
    {f : ℂ → ℂ} {r0 : ℝ}
    (hr0pos : 0 < r0)
    (hr0 : ∀ p : divisorZeroIndex₀ f (Set.univ : Set ℂ), r0 ≤ ‖divisorZeroIndex₀_val p‖)
    {k : ℕ} {p : divisorZeroIndex₀ f (Set.univ : Set ℂ)}
    (hp : ⌊Real.logb 2 (‖divisorZeroIndex₀_val p‖ / r0)⌋₊ = k) :
    r0 * (2 : ℝ) ^ (k : ℝ) ≤ ‖divisorZeroIndex₀_val p‖ := by
  exact Real.dyadicShell_lower_bound (r0 := r0) (x := ‖divisorZeroIndex₀_val p‖)
    hr0pos (hr0 p) hp

lemma finite_divisorZeroIndex₀_dyadicShell
    {f : ℂ → ℂ} {r0 : ℝ}
    (hr0pos : 0 < r0)
    (hr0 : ∀ p : divisorZeroIndex₀ f (Set.univ : Set ℂ), r0 ≤ ‖divisorZeroIndex₀_val p‖)
    (k : ℕ) :
    ({p : divisorZeroIndex₀ f (Set.univ : Set ℂ) |
      ⌊Real.logb 2 (‖divisorZeroIndex₀_val p‖ / r0)⌋₊ = k} : Set _).Finite := by
  have hsub :
      {p : divisorZeroIndex₀ f (Set.univ : Set ℂ) |
        ⌊Real.logb 2 (‖divisorZeroIndex₀_val p‖ / r0)⌋₊ = k} ⊆
        {p : divisorZeroIndex₀ f (Set.univ : Set ℂ) |
          ‖divisorZeroIndex₀_val p‖ ≤ r0 * (2 : ℝ) ^ ((k : ℝ) + 1)} := by
    intro p hp
    exact divisorZeroIndex₀_dyadicShell_upper_bound hr0pos hr0 hp
  have hfin :
      ({p : divisorZeroIndex₀ f (Set.univ : Set ℂ) |
        ‖divisorZeroIndex₀_val p‖ ≤ r0 * (2 : ℝ) ^ ((k : ℝ) + 1)} : Set _).Finite := by
    have :
        Metric.closedBall (0 : ℂ) (r0 * (2 : ℝ) ^ ((k : ℝ) + 1)) ⊆
          (Set.univ : Set ℂ) := by
      simp
    simpa using
      (divisorZeroIndex₀_norm_le_finite (f := f) (U := (Set.univ : Set ℂ))
        (B := r0 * (2 : ℝ) ^ ((k : ℝ) + 1)) this)
  exact hfin.subset hsub

lemma tsum_divisorZeroIndex₀_dyadicShell_inv_rpow_le_geometric_of_growth
    {f : ℂ → ℂ} {ρ τ r0 Cgrow : ℝ}
    (hρ : 0 ≤ ρ) (hτpos : 0 < τ) (hf : Differentiable ℂ f)
    (hCgrow_pos : 0 < Cgrow)
    (hCgrow : ∀ z : ℂ, Real.log (1 + ‖f z‖) ≤ Cgrow * (1 + ‖z‖) ^ ρ)
    (hr0pos : 0 < r0)
    (hr0 : ∀ p : divisorZeroIndex₀ f (Set.univ : Set ℂ),
      r0 ≤ ‖divisorZeroIndex₀_val p‖)
    (k : ℕ) (hk_ge_one : 1 ≤ r0 * (2 : ℝ) ^ ((k : ℝ) + 1)) :
    let kfun : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℕ :=
      fun p => ⌊Real.logb 2 (‖divisorZeroIndex₀_val p‖ / r0)⌋₊
    let S : Set (divisorZeroIndex₀ f (Set.univ : Set ℂ)) := {p | kfun p = k}
    let Ctrail : ℝ := |Real.log ‖meromorphicTrailingCoeffAt f 0‖|
    let A : ℝ := ((Cgrow / Real.log 2) * (1 + 4 * r0) ^ ρ) * (r0⁻¹) ^ τ
    let B : ℝ := ((Ctrail / Real.log 2) + 1) * (r0⁻¹) ^ τ
    let q : ℝ := (2 : ℝ) ^ (ρ - τ)
    let qσ : ℝ := (2 : ℝ) ^ (-τ)
    (∑' p : S, ‖divisorZeroIndex₀_val p.1‖⁻¹ ^ τ) ≤ A * q ^ k + B * qσ ^ k := by
  classical
  intro kfun S Ctrail A B q qσ
  let rk : ℝ := r0 * (2 : ℝ) ^ (k : ℝ)
  let Rk : ℝ := r0 * (2 : ℝ) ^ ((k : ℝ) + 1)
  have hrk_pos : 0 < rk := mul_pos hr0pos (Real.rpow_pos_of_pos (by norm_num) _)
  have hrk0 : 0 ≤ rk := le_of_lt hrk_pos
  have : Finite S := by
    simpa [S, kfun] using (finite_divisorZeroIndex₀_dyadicShell
      (f := f) hr0pos hr0 k).to_subtype
  have : Fintype S := Fintype.ofFinite S
  have hk_upper : ∀ p : S, ‖divisorZeroIndex₀_val p.1‖ ≤ Rk := by
    intro p
    have hk' : kfun p.1 = k := p.2
    simpa [Rk, kfun] using
      divisorZeroIndex₀_dyadicShell_upper_bound (f := f) hr0pos hr0 hk'
  have hk_lower : ∀ p : S, rk ≤ ‖divisorZeroIndex₀_val p.1‖ := by
    intro p
    have hk' : kfun p.1 = k := p.2
    simpa [rk, kfun] using
      divisorZeroIndex₀_dyadicShell_lower_bound (f := f) hr0pos hr0 hk'
  have htsum_le :
      (∑' p : S, ‖divisorZeroIndex₀_val p.1‖⁻¹ ^ τ)
        ≤ (Fintype.card S : ℝ) * (rk⁻¹ ^ τ) := by
    exact Real.tsum_inv_rpow_le_card_mul_of_lower_bound
      (a := fun p : S => ‖divisorZeroIndex₀_val p.1‖)
      hrk_pos hτpos (fun _ => norm_nonneg _) hk_lower
  have hmass_le_growth :
      divisorMassClosedBall₀ f Rk
        ≤ (Cgrow * (1 + |2 * Rk|) ^ ρ + Ctrail) / (Real.log 2) := by
    simpa [Ctrail, Rk] using
      (divisorMassClosedBall₀_le_of_growth (f := f) (ρ := ρ) (C := Cgrow) hf hCgrow
        (R := Rk) hk_ge_one)
  have hcard_le_mass :
      (Fintype.card S : ℝ) ≤ divisorMassClosedBall₀ f Rk := by
    have hRk_pos : 0 < Rk := lt_of_lt_of_le (by norm_num) hk_ge_one
    exact card_subtype_le_divisorMassClosedBall₀_of_norm_le (f := f) hf hRk_pos hk_upper
  have htsum' :
      (∑' p : S, ‖divisorZeroIndex₀_val p.1‖⁻¹ ^ τ)
        ≤ ((Cgrow * (1 + |2 * Rk|) ^ ρ + Ctrail) / (Real.log 2)) * (rk⁻¹ ^ τ) := by
    have hcard_le_growth :
        (Fintype.card S : ℝ) ≤
          (Cgrow * (1 + |2 * Rk|) ^ ρ + Ctrail) / (Real.log 2) :=
      le_trans hcard_le_mass hmass_le_growth
    exact le_trans htsum_le <|
      mul_le_mul_of_nonneg_right hcard_le_growth (Real.rpow_nonneg (inv_nonneg.2 hrk0) τ)
  have hpow_bound :
      (1 + |2 * Rk|) ^ ρ ≤ (1 + 4 * r0) ^ ρ * ((2 : ℝ) ^ ρ) ^ k := by
    simpa [Rk] using
      Real.one_add_abs_two_mul_dyadicRadius_rpow_le (r0 := r0) (ρ := ρ) k hr0pos hρ
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  simpa [A, B, q, qσ, rk, Ctrail, mul_assoc, mul_left_comm, mul_comm] using
    Real.dyadic_growth_mass_mul_inv_le_geometric
      (C := Cgrow) (L := Real.log 2) (M := (1 + 4 * r0) ^ ρ)
      (X := (1 + |2 * Rk|) ^ ρ)
      (T := ∑' p : S, ‖divisorZeroIndex₀_val p.1‖⁻¹ ^ τ)
      (Ctrail := Ctrail) (r0 := r0) (ρ := ρ) (τ := τ) (k := k)
      hlog2pos hCgrow_pos.le hr0pos.le hpow_bound
      (by simpa [rk] using htsum')

theorem summable_norm_inv_rpow_divisorZeroIndex₀_of_growth {f : ℂ → ℂ} {ρ τ : ℝ}
    (hρ : 0 ≤ ρ) (hτ : ρ < τ) (hf : Differentiable ℂ f) (hnot : ∃ z : ℂ, f z ≠ 0)
    (hgrowth : ∃ C > 0, ∀ z : ℂ, Real.log (1 + ‖f z‖) ≤ C * (1 + ‖z‖) ^ ρ) :
    Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ τ) := by
  rcases hgrowth with ⟨Cgrow, hCgrow_pos, hCgrow⟩
  have hτpos : 0 < τ := lt_of_le_of_lt hρ hτ
  rcases exists_r0_le_norm_divisorZeroIndex₀_val (f := f) hf hnot with ⟨r0, hr0pos, hr0⟩
  have hr0ne : (r0 : ℝ) ≠ 0 := ne_of_gt hr0pos
  let kfun : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℕ :=
    fun p => ⌊Real.logb 2 (‖divisorZeroIndex₀_val p‖ / r0)⌋₊
  let S : ℕ → Set (divisorZeroIndex₀ f (Set.univ : Set ℂ)) :=
    fun k => {p | kfun p = k}
  have hS : ∀ p : divisorZeroIndex₀ f (Set.univ : Set ℂ), ∃! k : ℕ, p ∈ S k := by
    intro p
    refine ⟨kfun p, ?_, ?_⟩
    · simp [S]
    · intro k hk
      simpa [S] using hk.symm
  have hnonneg : 0 ≤ fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ τ := by
    intro p
    exact Real.rpow_nonneg (inv_nonneg.2 (norm_nonneg _)) _
  have hSk_summable : ∀ k : ℕ, Summable fun p : S k => ‖divisorZeroIndex₀_val p.1‖⁻¹ ^ τ := by
    intro k
    have : Finite (S k) := by
      simpa [S, kfun] using (finite_divisorZeroIndex₀_dyadicShell
        (f := f) hr0pos hr0 k).to_subtype
    exact Summable.of_finite
  have hshell_summable :
      Summable fun k : ℕ => ∑' p : S k, ‖divisorZeroIndex₀_val p.1‖⁻¹ ^ τ := by
    let q : ℝ := (2 : ℝ) ^ (ρ - τ)
    let qσ : ℝ := (2 : ℝ) ^ (-τ)
    have hq_nonneg : 0 ≤ q := le_of_lt (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _)
    have hq_lt_one : q < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (x := (2 : ℝ)) (by norm_num : (1 : ℝ) < 2)
        (sub_neg.2 hτ)
    have hqσ_nonneg : 0 ≤ qσ := le_of_lt (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _)
    have hqσ_lt_one : qσ < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (x := (2 : ℝ)) (by norm_num : (1 : ℝ) < 2)
        (by simpa using (neg_neg_of_pos hτpos))
    have hgeom_q : Summable (fun k : ℕ => q ^ k) :=
      summable_geometric_of_lt_one hq_nonneg hq_lt_one
    have hgeom_qσ : Summable (fun k : ℕ => qσ ^ k) :=
      summable_geometric_of_lt_one hqσ_nonneg hqσ_lt_one
    let Ctrail : ℝ := |Real.log ‖meromorphicTrailingCoeffAt f 0‖|
    let A : ℝ := ((Cgrow / Real.log 2) * (1 + 4 * r0) ^ ρ) * (r0⁻¹) ^ τ
    let B : ℝ := ((Ctrail / Real.log 2) + 1) * (r0⁻¹) ^ τ
    rcases Real.exists_nat_le_two_pow (1 / r0) with ⟨k0, hk0⟩
    let A0 : ℝ := A * q ^ k0
    let B0 : ℝ := B * qσ ^ k0
    have hmajor : Summable (fun k : ℕ => A0 * q ^ k + B0 * qσ ^ k) :=
      (hgeom_q.mul_left A0).add (hgeom_qσ.mul_left B0)
    have hshell_summable_shift :
        Summable fun k : ℕ => ∑' p : S (k + k0), ‖divisorZeroIndex₀_val p.1‖⁻¹ ^ τ := by
      refine hmajor.of_nonneg_of_le
        (fun k => by
          have : ∀ p : S (k + k0), 0 ≤ ‖divisorZeroIndex₀_val p.1‖⁻¹ ^ τ := by
            intro p; exact Real.rpow_nonneg (inv_nonneg.2 (norm_nonneg _)) _
          exact tsum_nonneg this)
        (fun k => by
          let kk : ℕ := k + k0
          let Rk : ℝ := r0 * (2 : ℝ) ^ ((kk : ℝ) + 1)
          have hRk_ge_one : (1 : ℝ) ≤ Rk := by
            have hkk : k0 ≤ kk + 1 := by
              simp [kk, Nat.add_assoc, Nat.add_comm]
            simpa [Rk] using
              Real.one_le_dyadicRadius_succ_of_inv_le_two_pow hr0pos hk0 hkk
          have hmain :
              (∑' p : S kk, ‖divisorZeroIndex₀_val p.1‖⁻¹ ^ τ) ≤ A * q ^ kk + B * qσ ^ kk := by
            simpa [S, kfun, Ctrail, A, B, q, qσ] using
              tsum_divisorZeroIndex₀_dyadicShell_inv_rpow_le_geometric_of_growth
                (f := f) (ρ := ρ) (τ := τ) hρ hτpos hf hCgrow_pos hCgrow hr0pos hr0 kk hRk_ge_one
          have : A * q ^ kk + B * qσ ^ kk = A0 * q ^ k + B0 * qσ ^ k := by
            simpa [A0, B0, kk] using Real.two_geometric_shift_add A B q qσ k k0
          simpa [kk] using (hmain.trans_eq this)
        )
    exact (summable_nat_add_iff k0).1 hshell_summable_shift
  have hpart :=
    (summable_partition (f := fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
        ‖divisorZeroIndex₀_val p‖⁻¹ ^ τ) hnonneg (s := S) hS)
  exact (hpart.2 ⟨hSk_summable, hshell_summable⟩)

theorem summable_norm_inv_pow_divisorZeroIndex₀_of_growth {f : ℂ → ℂ} {ρ : ℝ}
    (hρ : 0 ≤ ρ) (hf : Differentiable ℂ f) (hnot : ∃ z : ℂ, f z ≠ 0)
    (hgrowth : ∃ C > 0, ∀ z : ℂ, Real.log (1 + ‖f z‖) ≤ C * (1 + ‖z‖) ^ ρ) :
    Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (Nat.floor ρ + 1)) := by
  have hτ : ρ < (Nat.floor ρ + 1 : ℝ) := by
    simpa [Nat.cast_add, Nat.cast_one] using (Nat.lt_floor_add_one (a := ρ))
  have hs :=
    summable_norm_inv_rpow_divisorZeroIndex₀_of_growth (f := f) (ρ := ρ)
      (τ := (Nat.floor ρ + 1 : ℝ)) hρ hτ hf hnot hgrowth
  exact hs.congr fun p => by
    have hcast : ((Nat.floor ρ : ℝ) + 1) = ((Nat.floor ρ + 1 : ℕ) : ℝ) := by
      norm_num
    rw [hcast, Real.rpow_natCast]

end Complex.Hadamard
end
end
end File29

-- Upstream module PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.AbsMax
section File30

section
namespace Complex

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem norm_le_of_mem_ball_of_forall_sphere_norm_le {f : ℂ → F} {r C : ℝ} {z : ℂ}
    (hd : Differentiable ℂ f) (hrpos : 0 < r)
    (hz : z ∈ Metric.ball (0 : ℂ) r) (hsphere : ∀ u : ℂ, ‖u‖ = r → ‖f u‖ ≤ C) :
    ‖f z‖ ≤ C := by
  let U : Set ℂ := Metric.ball (0 : ℂ) r
  have hfront : ∀ u ∈ frontier U, ‖f u‖ ≤ C := by
    intro u hu
    have hur : ‖u‖ = r := by
      have hfront' : frontier (Metric.ball (0 : ℂ) r) = Metric.sphere (0 : ℂ) r := by
        simpa using (frontier_ball (x := (0 : ℂ)) (r := r) (ne_of_gt hrpos))
      have : u ∈ Metric.sphere (0 : ℂ) r := by simpa [U, hfront'] using hu
      simpa [Metric.mem_sphere, dist_zero_right] using this
    exact hsphere u hur
  exact norm_le_of_forall_mem_frontier_norm_le (f := f) (U := U) Metric.isBounded_ball
    hd.diffContOnCl hfront (subset_closure hz)

end Complex
end
end File30

-- Upstream module PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.CartanBound
section File31
 

section
namespace Complex
namespace CartanBound

open Real MeasureTheory intervalIntegral
open scoped Topology ENNReal

private lemma neg_log_le_sqrt_two_div {x : ℝ} (hx : 0 < x) (hxle : x ≤ 1) :
    -Real.log x ≤ Real.sqrt (2 / x) := by
  have hx0 : 0 ≤ x := le_of_lt hx
  have ht : 0 ≤ -Real.log x := by
    have : Real.log x ≤ 0 := Real.log_nonpos hx0 hxle
    linarith
  have hsq_div_two_le_exp : ∀ {t : ℝ}, 0 ≤ t → t ^ 2 / 2 ≤ Real.exp t := by
    intro t ht
    let g : ℝ → ℝ := fun u => Real.exp u - u ^ 2 / 2
    have hg_cont : ContinuousOn g (Set.Ici (0 : ℝ)) := by
      have : Continuous g := by fun_prop
      simpa using this.continuousOn
    have hg_diff : DifferentiableOn ℝ g (interior (Set.Ici (0 : ℝ))) := by
      intro u hu
      have : DifferentiableAt ℝ g u := by fun_prop
      exact this.differentiableWithinAt
    have hg'_nonneg : ∀ u ∈ interior (Set.Ici (0 : ℝ)), 0 ≤ deriv g u := by
      intro u hu
      have hu0 : 0 < u := by simpa [interior_Ici] using hu
      have hderiv : deriv g u = Real.exp u - u := by
        have hExp : HasDerivAt Real.exp (Real.exp u) u := Real.hasDerivAt_exp u
        have hpow2 : HasDerivAt (fun z : ℝ => z ^ 2) (2 * u) u := by
          simpa using! ((hasDerivAt_id u).pow 2)
        have hpow2_div : HasDerivAt (fun z : ℝ => z ^ 2 / 2) u u := by
          simpa using (hpow2.div_const (2 : ℝ))
        have hG : HasDerivAt g (Real.exp u - u) u := by
          simpa [g] using! hExp.sub hpow2_div
        exact hG.deriv
      have hu_le : u ≤ Real.exp u := by
        have h1 : u + 1 ≤ Real.exp u := Real.add_one_le_exp u
        exact (le_trans (le_add_of_nonneg_right (by norm_num)) h1)
      have : 0 ≤ Real.exp u - u := sub_nonneg.2 hu_le
      simpa [hderiv] using this
    have hg_mono : MonotoneOn g (Set.Ici (0 : ℝ)) :=
      monotoneOn_of_deriv_nonneg (D := Set.Ici (0 : ℝ)) (hD := convex_Ici 0)
        hg_cont hg_diff hg'_nonneg
    have hg0 : g 0 = 1 := by simp [g]
    have hle : g 0 ≤ g t := hg_mono (by simp) (by simpa [Set.mem_Ici] using ht) ht
    have : (1 : ℝ) ≤ Real.exp t - t ^ 2 / 2 := by simpa [g, hg0] using hle
    linarith
  have hmain : (-Real.log x) ^ 2 / 2 ≤ Real.exp (-Real.log x) := hsq_div_two_le_exp ht
  have hexp : Real.exp (-Real.log x) = x⁻¹ := by simp [Real.exp_neg, Real.exp_log hx]
  have hsq2 : (-Real.log x) ^ 2 ≤ 2 * Real.exp (-Real.log x) := by nlinarith [hmain]
  have hsq' : (-Real.log x) ^ 2 ≤ 2 / x := by simpa [hexp, div_eq_mul_inv, mul_assoc] using hsq2
  have hy : 0 ≤ 2 / x := div_nonneg (by norm_num) (le_of_lt hx)
  exact (Real.le_sqrt ht hy).2 hsq'

lemma posLog_log_one_div_abs_one_sub_le_sqrt {t : ℝ} :
    Real.posLog (1 / |1 - t|) ≤ Real.sqrt (2 / |1 - t|) := by
  by_cases ht : |1 - t| ≤ 1
  · by_cases h0 : |1 - t| = 0
    · have : t = 1 := by
        have : 1 - t = 0 := by simpa [abs_eq_zero] using h0
        linarith
      subst this
      simp
    · have hpos : 0 < |1 - t| := lt_of_le_of_ne (abs_nonneg _) (Ne.symm h0)
      have hle : -Real.log |1 - t| ≤ Real.sqrt (2 / |1 - t|) :=
        neg_log_le_sqrt_two_div (x := |1 - t|) hpos ht
      have hlog : Real.log (1 / |1 - t|) = -Real.log |1 - t| := by simp [Real.log_inv]
      have hnonneg : 0 ≤ Real.log (1 / |1 - t|) := by
        exact Real.log_nonneg ((one_le_div hpos).2 ht)
      have hmax : Real.posLog (1 / |1 - t|) = Real.log (1 / |1 - t|) :=
        max_eq_right hnonneg
      calc
        Real.posLog (1 / |1 - t|) = Real.log (1 / |1 - t|) := hmax
        _ = -Real.log |1 - t| := hlog
        _ ≤ Real.sqrt (2 / |1 - t|) := hle
  · have hlt : 1 < |1 - t| := lt_of_not_ge ht
    have hle0 : Real.log (1 / |1 - t|) ≤ 0 := by
      have hpos : 0 < |1 - t| := lt_trans (by norm_num) hlt
      have : (1 / |1 - t| : ℝ) ≤ 1 := (div_le_one hpos).2 (le_of_lt hlt)
      exact le_trans (Real.log_le_log (by positivity) this) (by simp)
    have hmax : Real.posLog (1 / |1 - t|) = 0 := max_eq_left hle0
    have hrhs : 0 ≤ Real.sqrt (2 / |1 - t|) := by
      exact Real.sqrt_nonneg _
    rw [hmax]
    exact hrhs

lemma posLog_one_div_norm_one_sub_le_posLog_one_div_abs_one_sub_norm (w : ℂ) (hw : ‖w‖ ≠ (1 : ℝ)) :
    Real.posLog (1 / ‖(1 : ℂ) - w‖) ≤ Real.posLog (1 / |1 - ‖w‖|) := by
  have hrev : |(‖(1 : ℂ)‖ : ℝ) - ‖w‖| ≤ ‖(1 : ℂ) - w‖ :=
    abs_norm_sub_norm_le (1 : ℂ) w
  have hrev' : |1 - ‖w‖| ≤ ‖(1 : ℂ) - w‖ := by
    simpa using hrev
  have h0 : |1 - ‖w‖| ≠ 0 := by
    have : (1 : ℝ) - ‖w‖ ≠ 0 := by
      intro h
      have : ‖w‖ = (1 : ℝ) := by linarith
      exact hw this
    simpa [abs_eq_zero] using this
  have hpos : 0 < |1 - ‖w‖| := lt_of_le_of_ne (abs_nonneg _) (Ne.symm h0)
  have hdiv :
      (1 / ‖(1 : ℂ) - w‖ : ℝ) ≤ (1 / |1 - ‖w‖| : ℝ) :=
    one_div_le_one_div_of_le hpos hrev'
  exact Real.posLog_le_posLog (neg_one_lt_zero.le.trans (by positivity)) hdiv

lemma posLog_one_div_norm_one_sub_le_posLog_one_div_abs_one_sub
    {t : ℝ} (ht : t ≠ 1) (w : ℂ) (hw : ‖w‖ = t) :
    Real.posLog (1 / ‖(1 : ℂ) - w‖) ≤ Real.posLog (1 / |1 - t|) := by
  have hw' : ‖w‖ ≠ (1 : ℝ) := by
    simpa [hw] using ht
  simpa [hw] using (posLog_one_div_norm_one_sub_le_posLog_one_div_abs_one_sub_norm w hw')

noncomputable def φ (t : ℝ) : ℝ :=
  log⁺ (1 / |1 - t|)

lemma measurable_phi : Measurable φ := by
  unfold φ
  simpa [Real.posLog_def, Real.posLog] using
    (by fun_prop : Measurable fun t : ℝ => max 0 (Real.log (1 / |1 - t|)))

lemma phi_le_log_two_of_le_half {t : ℝ} (ht : t ≤ (1 / 2 : ℝ)) : φ t ≤ Real.log 2 := by
  have hnonneg : 0 ≤ (1 - t : ℝ) := by linarith
  have hden : (1 / 2 : ℝ) ≤ |1 - t| := by
    have : (1 / 2 : ℝ) ≤ (1 - t : ℝ) := by linarith
    simpa [abs_of_nonneg hnonneg] using this
  have hfrac : (1 / |1 - t| : ℝ) ≤ 2 := by
    have hhalfpos : (0 : ℝ) < (1 / 2 : ℝ) := by norm_num
    have := one_div_le_one_div_of_le hhalfpos hden
    simpa [one_div, div_eq_mul_inv] using this
  have hposLog : log⁺ (1 / |1 - t|) ≤ log⁺ (2 : ℝ) :=
    Real.posLog_le_posLog (neg_one_lt_zero.le.trans (by positivity)) hfrac
  have habs : (1 : ℝ) ≤ |(2 : ℝ)| := by
    simp
  have hposLog2 : (log⁺ (2 : ℝ)) = Real.log 2 := by
    simpa using (Real.posLog_eq_log habs)
  simpa [φ, hposLog2] using hposLog

lemma phi_eq_zero_of_one_le_abs_one_sub {t : ℝ} (ht : (1 : ℝ) ≤ |1 - t|) : φ t = 0 := by
  have hpos : 0 < |1 - t| := lt_of_lt_of_le (by norm_num) ht
  have hfrac : (1 / |1 - t| : ℝ) ≤ 1 := (div_le_one hpos).2 ht
  have habs : |(1 / |1 - t| : ℝ)| ≤ 1 := by
    have hnonneg : 0 ≤ (1 / |1 - t| : ℝ) := by positivity
    simpa [abs_of_nonneg hnonneg] using hfrac
  have : log⁺ (1 / |1 - t|) = 0 := (Real.posLog_eq_zero_iff _).2 habs
  simpa [φ] using this

lemma φ_nonneg (t : ℝ) : 0 ≤ φ t := by
  simpa [φ] using (Real.posLog_nonneg (x := (1 / |1 - t|)))

lemma φ_le_sqrt (t : ℝ) : φ t ≤ Real.sqrt (2 / |1 - t|) := by
  simpa [φ, Real.posLog] using
    posLog_log_one_div_abs_one_sub_le_sqrt (t := t)

lemma ae_restrict_norm_phi_le_of_forall_mem {A B : ℝ} (hAB : A ≤ B) {g : ℝ → ℝ}
    (hg : ∀ t, 0 ≤ g t) (h : ∀ t ∈ Set.Icc A B, φ t ≤ g t) :
    (fun t : ℝ => ‖φ t‖) ≤ᶠ[ae (volume.restrict (Set.uIoc A B))] fun t => ‖g t‖ := by
  refine
    MeasureTheory.ae_restrict_of_forall_mem (μ := (volume : MeasureTheory.Measure ℝ))
    (s := Set.uIoc A B)
      (by simpa using (measurableSet_uIoc : MeasurableSet (Set.uIoc A B))) ?_
  intro t ht
  have htIoc : t ∈ Set.Ioc A B := by
    simpa [Set.uIoc_of_le hAB] using ht
  have htIcc : t ∈ Set.Icc A B := ⟨le_of_lt htIoc.1, htIoc.2⟩
  have hle : φ t ≤ g t := h t htIcc
  have hφ0 : 0 ≤ φ t := φ_nonneg t
  have hg0 : 0 ≤ g t := hg t
  simpa [Real.norm_eq_abs, abs_of_nonneg hφ0, abs_of_nonneg hg0] using hle

lemma log_norm_one_sub_div_ge_neg_phi {u a : ℂ} {r : ℝ}
    (hur : ‖u‖ = r) (ha : a ≠ 0) (hr : r ≠ ‖a‖) :
    Real.log ‖(1 : ℂ) - u / a‖ ≥ -φ (r / ‖a‖) := by
  have ha_norm : 0 < ‖a‖ := norm_pos_iff.2 ha
  have hnorm_eq : ‖(1 : ℂ) - u / a‖ = ‖a - u‖ / ‖a‖ := by
    have : (1 : ℂ) - u / a = (a - u) / a := by
      field_simp [ha]
    calc
      ‖(1 : ℂ) - u / a‖ = ‖(a - u) / a‖ := by simp [this]
      _ = ‖a - u‖ / ‖a‖ := by simp
  have hrev : |‖a‖ - ‖u‖| ≤ ‖a - u‖ := by
    simpa using (abs_norm_sub_norm_le a u)
  have hdiv : |‖a‖ - ‖u‖| / ‖a‖ ≤ ‖a - u‖ / ‖a‖ :=
    div_le_div_of_nonneg_right hrev (le_of_lt ha_norm)
  have habs : |1 - (r / ‖a‖)| = |‖a‖ - ‖u‖| / ‖a‖ := by
    have hu : ‖u‖ = r := hur
    have ha0 : (‖a‖ : ℝ) ≠ 0 := ha_norm.ne'
    have h1 : (1 : ℝ) - (r / ‖a‖) = (‖a‖ - r) / ‖a‖ := by
      field_simp [ha0]
    calc
      |1 - (r / ‖a‖)| = |(‖a‖ - r) / ‖a‖| := by simp [h1]
      _ = |‖a‖ - r| / ‖a‖ := by simp [abs_div, abs_of_pos ha_norm]
      _ = |‖a‖ - ‖u‖| / ‖a‖ := by simp [hu]
  have hnorm_ge : |1 - (r / ‖a‖)| ≤ ‖(1 : ℂ) - u / a‖ := by
    have : |1 - (r / ‖a‖)| ≤ ‖a - u‖ / ‖a‖ := by
      rw [habs]
      exact hdiv
    rwa [hnorm_eq]
  have hx0 : 0 < |1 - (r / ‖a‖)| := by
    have : (1 - (r / ‖a‖) : ℝ) ≠ 0 := by
      intro h0
      have : r = ‖a‖ := by
        have : r / ‖a‖ = (1 : ℝ) := by linarith
        simpa using (div_eq_iff ha_norm.ne').1 this
      exact hr this
    have : |1 - (r / ‖a‖)| ≠ 0 := by
      simpa [abs_eq_zero] using this
    exact lt_of_le_of_ne (abs_nonneg _) (Ne.symm this)
  have hlogx :
      Real.log |1 - (r / ‖a‖)| ≥ -φ (r / ‖a‖) := by
    have := Real.neg_posLog_inv_le_log (x := |1 - (r / ‖a‖)|)
    simpa [φ, one_div, inv_inv, abs_sub_comm, sub_eq_add_neg] using this
  have hlog_mono :
      Real.log |1 - (r / ‖a‖)| ≤ Real.log ‖(1 : ℂ) - u / a‖ :=
    Real.log_le_log (by positivity) hnorm_ge
  linarith [hlog_mono, hlogx]

noncomputable def K : ℝ :=
  ∫ (t : ℝ) in (1 / 4 : ℝ)..(4 : ℝ), Real.sqrt (2 / |1 - t|) ∂volume

lemma K_nonneg : 0 ≤ K := by
  have hle : (1 / 4 : ℝ) ≤ (4 : ℝ) := by norm_num
  have hnn : ∀ t ∈ Set.Icc (1 / 4 : ℝ) (4 : ℝ), 0 ≤ Real.sqrt (2 / |1 - t|) := by
    intro _t _ht
    exact Real.sqrt_nonneg _
  simpa [K] using (intervalIntegral.integral_nonneg
    (μ := (volume : MeasureTheory.Measure ℝ)) hle hnn)

noncomputable def Cφ : ℝ :=
  Real.log 2 + 4 * K + 1

lemma Cφ_pos : 0 < Cφ := by
  have hlog : 0 < Real.log 2 := by
    simpa using Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hK : 0 ≤ K := K_nonneg
  have : 0 < Real.log 2 + 4 * K := by nlinarith
  have : 0 < Real.log 2 + 4 * K + 1 := by linarith
  simpa [Cφ] using this

lemma intervalIntegrable_sqrt_two_div_abs_one_sub_Icc :
    IntervalIntegrable
      (fun t : ℝ => Real.sqrt (2 / |1 - t|))
      volume (1 / 4 : ℝ) (4 : ℝ) := by
  let f : ℝ → ℝ := fun u => Real.sqrt (2 / |u|)
  have hf0 : IntervalIntegrable f volume (0 : ℝ) (3 : ℝ) := by
    have hpow :
        IntervalIntegrable (fun u : ℝ => u ^ (- (2⁻¹ : ℝ))) volume (0 : ℝ) (3 : ℝ) := by
      simpa using
        (intervalIntegral.intervalIntegrable_rpow' (a := (0 : ℝ)) (b := (3 : ℝ))
          (r := (- (2⁻¹ : ℝ))) (by linarith : (-1 : ℝ) < - (2⁻¹ : ℝ)))
    have hpow2 :
        IntervalIntegrable (fun u : ℝ => Real.sqrt 2 * u ^ (- (2⁻¹ : ℝ))) volume (0 : ℝ) (3 : ℝ) :=
      hpow.const_mul (Real.sqrt 2)
    have hEq :
        Set.EqOn f (fun u : ℝ => Real.sqrt 2 * u ^ (- (2⁻¹ : ℝ))) (Set.uIoc (0 : ℝ) (3 : ℝ)) := by
      intro u hu
      have hu' : u ∈ Set.Ioc (0 : ℝ) (3 : ℝ) := by
        simpa [Set.uIoc_of_le (show (0 : ℝ) ≤ 3 by norm_num)] using hu
      have hu0 : 0 < u := hu'.1
      have hu0' : 0 ≤ u := le_of_lt hu0
      have habs : |u| = u := abs_of_nonneg hu0'
      have : f u = Real.sqrt (2 / u) := by simp [f, habs]
      calc
        f u = Real.sqrt (2 / u) := this
        _ = Real.sqrt 2 / Real.sqrt u := by simp
        _ = Real.sqrt 2 * (Real.sqrt u)⁻¹ := by simp [div_eq_mul_inv]
        _ = Real.sqrt 2 * (u ^ (2⁻¹ : ℝ))⁻¹ := by simp [Real.sqrt_eq_rpow]
        _ = Real.sqrt 2 * u ^ (- (2⁻¹ : ℝ)) := by
              have h : (u ^ (2⁻¹ : ℝ))⁻¹ = u ^ (- (2⁻¹ : ℝ)) := by
                simpa using (Real.rpow_neg hu0' (2⁻¹ : ℝ)).symm
              simp [h]
    exact
      (IntervalIntegrable.congr (a := (0 : ℝ)) (b := (3 : ℝ))
          (μ := (volume : MeasureTheory.Measure ℝ))
          (f := fun u : ℝ => Real.sqrt 2 * u ^ (- (2⁻¹ : ℝ))) (g := f) hEq.symm)
        hpow2
  have hf0' : IntervalIntegrable f volume (0 : ℝ) (3 / 4 : ℝ) :=
    hf0.mono_set (by
      intro u hu
      have hsub : Set.uIcc (0 : ℝ) (3 / 4 : ℝ) ⊆ Set.uIcc (0 : ℝ) (3 : ℝ) := by
        refine Set.uIcc_subset_uIcc ?_ ?_
        · simp
        · have h0 : (0 : ℝ) ≤ (3 / 4 : ℝ) := by nlinarith
          have h1 : (3 / 4 : ℝ) ≤ (3 : ℝ) := by nlinarith
          exact (Set.mem_uIcc).2 (Or.inl ⟨h0, h1⟩)
      exact hsub hu)
  have hleft :
      IntervalIntegrable (fun t : ℝ => Real.sqrt (2 / |1 - t|)) volume (1 / 4 : ℝ) (1 : ℝ) := by
    have htmp :
        IntervalIntegrable (fun t : ℝ => f (1 - t)) volume (1 : ℝ) ((1 : ℝ) - (3 / 4 : ℝ)) := by
      simpa using (hf0'.comp_sub_left (c := (1 : ℝ)))
    have htmp' :
        IntervalIntegrable (fun t : ℝ => f (1 - t)) volume ((1 : ℝ) - (3 / 4 : ℝ)) (1 : ℝ) :=
      htmp.symm
    have hsub : ((1 : ℝ) - (3 / 4 : ℝ)) = (1 / 4 : ℝ) := by norm_num
    have htmp'' : IntervalIntegrable (fun t : ℝ => f (1 - t)) volume (1 / 4 : ℝ) (1 : ℝ) := by
      simpa [hsub] using htmp'
    simpa [f] using htmp''
  have hright :
      IntervalIntegrable (fun t : ℝ => Real.sqrt (2 / |1 - t|)) volume (1 : ℝ) (4 : ℝ) := by
    have htmp :
        IntervalIntegrable (fun t : ℝ => f (t - 1)) volume (1 : ℝ) ((3 : ℝ) + (1 : ℝ)) := by
      simpa using (hf0.comp_sub_right (c := (1 : ℝ)))
    have hsub : ((3 : ℝ) + (1 : ℝ)) = (4 : ℝ) := by norm_num
    have htmp' : IntervalIntegrable (fun t : ℝ => f (t - 1)) volume (1 : ℝ) (4 : ℝ) := by
      simpa [hsub] using htmp
    have hcongr :
        Set.EqOn (fun t : ℝ => f (t - 1)) (fun t : ℝ => Real.sqrt (2 / |1 - t|))
          (Set.uIoc (1 : ℝ) (4 : ℝ)) := by
      intro t _ht
      simp [f, abs_sub_comm]
    exact
      (IntervalIntegrable.congr (a := (1 : ℝ)) (b := (4 : ℝ))
          (μ := (volume : MeasureTheory.Measure ℝ))
          (f := fun t : ℝ => f (t - 1)) (g := fun t : ℝ => Real.sqrt (2 / |1 - t|)) hcongr)
        htmp'
  exact hleft.trans hright

lemma phi_le_log_two_on_dyadic_of_le_quarter {A t : ℝ} (hA : A ≤ (1 / 4 : ℝ))
    (ht : t ∈ Set.Icc A (2 * A)) :
    φ t ≤ Real.log 2 := by
  have ht_le : t ≤ (1 / 2 : ℝ) := by
    exact ht.2.trans (by nlinarith [hA])
  exact phi_le_log_two_of_le_half ht_le

lemma phi_eq_zero_of_two_le {t : ℝ} (ht : (2 : ℝ) ≤ t) : φ t = 0 := by
  have hden : (1 : ℝ) ≤ |1 - t| := by
    have : (1 : ℝ) ≤ t - 1 := by linarith
    have : (1 : ℝ) ≤ |t - 1| := by
      simpa [abs_of_nonneg (by linarith : 0 ≤ t - 1)] using this
    simpa [abs_sub_comm] using this
  exact phi_eq_zero_of_one_le_abs_one_sub hden

lemma intervalIntegrable_phi_dyadic_small {A : ℝ} (hA0 : 0 ≤ A)
    (hA : A ≤ (1 / 4 : ℝ)) :
    IntervalIntegrable φ volume A (2 * A) := by
  have hA_le : A ≤ 2 * A := by nlinarith
  have hconst : IntervalIntegrable (fun _ : ℝ => (Real.log 2 : ℝ)) volume A (2 * A) :=
    intervalIntegrable_const
  have hmeas :
      AEStronglyMeasurable (fun t : ℝ => φ t) (volume.restrict (Set.uIoc A (2 * A))) :=
    (measurable_phi.aestronglyMeasurable : _)
  have hdom :
      (fun t : ℝ => ‖φ t‖) ≤ᶠ[ae (volume.restrict (Set.uIoc A (2 * A)))]
        fun _ => ‖(Real.log 2 : ℝ)‖ := by
    refine ae_restrict_norm_phi_le_of_forall_mem (A := A) (B := 2 * A) hA_le
      (g := fun _ => (Real.log 2 : ℝ)) (hg := fun _ => ?_) ?_
    · simpa using (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))
    · intro t ht
      exact phi_le_log_two_on_dyadic_of_le_quarter hA ht
  exact IntervalIntegrable.mono_fun hconst hmeas hdom

lemma intervalIntegrable_phi_dyadic_large {A : ℝ} (hA : (2 : ℝ) ≤ A) :
    IntervalIntegrable φ volume A (2 * A) := by
  have hA_le : A ≤ 2 * A := by nlinarith
  have hEq : Set.EqOn (fun t : ℝ => φ t) (fun _ => (0 : ℝ)) (Set.uIoc A (2 * A)) := by
    intro t ht
    have htIoc : t ∈ Set.Ioc A (2 * A) := by
      simpa [Set.uIoc_of_le hA_le] using ht
    exact phi_eq_zero_of_two_le (le_trans hA (le_of_lt htIoc.1))
  have hz : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume A (2 * A) :=
    intervalIntegrable_const
  exact (IntervalIntegrable.congr (a := A) (b := (2 * A))
    (μ := (volume : MeasureTheory.Measure ℝ))
    (f := fun _ => (0 : ℝ)) (g := fun t => φ t) (by
      intro t ht
      simpa using (hEq (x := t) ht).symm)) hz

lemma intervalIntegrable_sqrt_two_div_abs_one_sub_dyadic_middle {A : ℝ}
    (hA_lower : (1 / 4 : ℝ) ≤ A) (hA_upper : A ≤ (2 : ℝ)) :
    IntervalIntegrable (fun t : ℝ => Real.sqrt (2 / |1 - t|)) volume A (2 * A) := by
  have hsqrt_big :
      IntervalIntegrable (fun t : ℝ => Real.sqrt (2 / |1 - t|))
        (volume : MeasureTheory.Measure ℝ) (1 / 4 : ℝ) (4 : ℝ) :=
    intervalIntegrable_sqrt_two_div_abs_one_sub_Icc
  refine hsqrt_big.mono_set ?_
  refine Set.uIcc_subset_uIcc ?_ ?_
  · exact (Set.mem_uIcc).2 (Or.inl ⟨hA_lower, by nlinarith [hA_upper]⟩)
  · exact (Set.mem_uIcc).2 (Or.inl ⟨by nlinarith [hA_lower], by nlinarith [hA_upper]⟩)

lemma intervalIntegrable_phi_dyadic_middle {A : ℝ}
    (hA_lower : (1 / 4 : ℝ) ≤ A) (hA_upper : A ≤ (2 : ℝ)) :
    IntervalIntegrable φ volume A (2 * A) := by
  have hA_le : A ≤ 2 * A := by nlinarith [hA_lower]
  have hsqrt :
      IntervalIntegrable (fun t : ℝ => Real.sqrt (2 / |1 - t|)) volume A (2 * A) :=
    intervalIntegrable_sqrt_two_div_abs_one_sub_dyadic_middle hA_lower hA_upper
  have hmeas :
      AEStronglyMeasurable (fun t : ℝ => φ t) (volume.restrict (Set.uIoc A (2 * A))) :=
    (measurable_phi.aestronglyMeasurable : _)
  have hdom :
      (fun t : ℝ => ‖φ t‖) ≤ᶠ[ae (volume.restrict (Set.uIoc A (2 * A)))]
        fun t => ‖Real.sqrt (2 / |1 - t|)‖ := by
    refine ae_restrict_norm_phi_le_of_forall_mem (A := A) (B := 2 * A) hA_le
      (g := fun t => Real.sqrt (2 / |1 - t|)) (hg := fun _ => Real.sqrt_nonneg _) ?_
    intro t _ht
    exact φ_le_sqrt t
  exact IntervalIntegrable.mono_fun hsqrt hmeas hdom

lemma intervalIntegrable_phi_dyadic {A : ℝ} (hA : 0 ≤ A) :
    IntervalIntegrable φ volume A (2 * A) := by
  by_cases hA0 : A = 0
  · subst hA0
    simp
  cases le_total A (1 / 4 : ℝ) with
  | inl hsmall =>
      exact intervalIntegrable_phi_dyadic_small hA hsmall
  | inr hge_quarter =>
      cases le_total (2 : ℝ) A with
      | inl hbig =>
          exact intervalIntegrable_phi_dyadic_large hbig
      | inr hA_le_two =>
          exact intervalIntegrable_phi_dyadic_middle hge_quarter hA_le_two

lemma intervalIntegrable_phi_div {a R : ℝ} (ha : 0 < a) (hR : 0 ≤ R) :
    IntervalIntegrable (fun r : ℝ => φ (r / a)) volume R (2 * R) := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hRa_nonneg : 0 ≤ R / a := by
    exact div_nonneg hR (le_of_lt ha)
  have hφ : IntervalIntegrable φ volume (R / a) (2 * (R / a)) :=
    intervalIntegrable_phi_dyadic (A := (R / a)) hRa_nonneg
  have := (hφ.comp_mul_right (c := (a⁻¹ : ℝ)))
  have hupper : a * (R * (a⁻¹ * 2)) = (2 * R) := by
    field_simp [ha0]
  simpa [div_eq_mul_inv, ha0, hupper, mul_assoc, mul_left_comm, mul_comm] using this

lemma log_two_le_Cφ : Real.log 2 ≤ Cφ := by
  dsimp [Cφ]
  have hK : 0 ≤ K := K_nonneg
  linarith [hK]

lemma four_mul_K_add_one_le_Cφ : (4 * K + 1 : ℝ) ≤ Cφ := by
  dsimp [Cφ]
  have hlog_nonneg : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  linarith [hlog_nonneg]

lemma integral_phi_le_Cφ_mul_small {A : ℝ} (hA0 : 0 ≤ A) (hA : A ≤ (1 / 4 : ℝ)) :
    (∫ (t : ℝ) in A..(2 * A), φ t ∂volume) ≤ Cφ * A := by
  have hA_le : A ≤ 2 * A := by nlinarith
  have hφ_int : IntervalIntegrable φ volume A (2 * A) :=
    intervalIntegrable_phi_dyadic_small hA0 hA
  have hconst : IntervalIntegrable (fun _ : ℝ => (Real.log 2 : ℝ)) volume A (2 * A) :=
    intervalIntegrable_const
  have hle_int :
      (∫ (t : ℝ) in A..(2 * A), φ t ∂volume)
        ≤ ∫ (t : ℝ) in A..(2 * A), (Real.log 2 : ℝ) ∂volume := by
    refine intervalIntegral.integral_mono_on (μ := (volume : MeasureTheory.Measure ℝ))
      hA_le hφ_int hconst ?_
    intro t ht
    exact phi_le_log_two_on_dyadic_of_le_quarter hA ht
  have hRHS :
      (∫ (t : ℝ) in A..(2 * A), (Real.log 2 : ℝ) ∂volume) = A * Real.log 2 := by
    simp [intervalIntegral.integral_const, sub_eq_add_neg, add_assoc, two_mul]
  have hcoef : A * Real.log 2 ≤ Cφ * A := by
    have := mul_le_mul_of_nonneg_left log_two_le_Cφ hA0
    simpa [mul_assoc, mul_left_comm, mul_comm] using this
  exact le_trans (by simpa [hRHS] using hle_int) hcoef

lemma integral_phi_le_Cφ_mul_large {A : ℝ} (hA : (2 : ℝ) ≤ A) :
    (∫ (t : ℝ) in A..(2 * A), φ t ∂volume) ≤ Cφ * A := by
  have hA_le : A ≤ 2 * A := by nlinarith
  have hφ0 : Set.EqOn (fun t : ℝ => φ t) (fun _ => (0 : ℝ)) (Set.uIcc A (2 * A)) := by
    intro t ht
    have ht' : t ∈ Set.Icc A (2 * A) := by
      simpa [Set.uIcc_of_le hA_le] using ht
    exact phi_eq_zero_of_two_le (le_trans hA ht'.1)
  have hzero : (∫ (t : ℝ) in A..(2 * A), φ t ∂volume) = 0 := by
    simpa using intervalIntegral.integral_congr (μ := (volume : MeasureTheory.Measure ℝ)) hφ0
  have hnonneg : (0 : ℝ) ≤ Cφ * A := mul_nonneg (le_of_lt Cφ_pos) (by linarith)
  simpa [hzero] using hnonneg

lemma integral_sqrt_two_div_abs_one_sub_le_K_dyadic_middle {A : ℝ}
    (hA_lower : (1 / 4 : ℝ) ≤ A) (hA_upper : A ≤ (2 : ℝ)) :
    (∫ (t : ℝ) in A..(2 * A), Real.sqrt (2 / |1 - t|) ∂volume) ≤ K := by
  let s (t : ℝ) : ℝ := Real.sqrt (2 / |1 - t|)
  have hA_le : A ≤ 2 * A := by nlinarith [hA_lower]
  have hA_upper' : (2 * A : ℝ) ≤ 4 := by nlinarith [hA_upper]
  have hsqrt_big : IntervalIntegrable s volume (1 / 4 : ℝ) (4 : ℝ) := by
    simpa [s] using intervalIntegrable_sqrt_two_div_abs_one_sub_Icc
  have hle_K :
      (∫ (t : ℝ) in A..(2 * A), s t ∂volume)
        ≤ ∫ (t : ℝ) in (1 / 4 : ℝ)..(4 : ℝ), s t ∂volume := by
    refine intervalIntegral.integral_mono_interval (μ := (volume : MeasureTheory.Measure ℝ))
      (c := (1 / 4 : ℝ)) (d := (4 : ℝ)) (a := A) (b := (2 * A))
      hA_lower hA_le hA_upper' ?_ hsqrt_big
    exact Filter.Eventually.of_forall (fun _t => Real.sqrt_nonneg _)
  simpa [K, s] using hle_K

lemma K_le_four_mul_K_add_one_mul_of_quarter_le {A : ℝ} (hA : (1 / 4 : ℝ) ≤ A) :
    K ≤ (4 * K + 1) * A := by
  have hcoef : 1 ≤ 4 * A := by nlinarith [hA]
  have hK : 0 ≤ K := K_nonneg
  nlinarith [hK, hcoef]

lemma integral_phi_le_Cφ_mul_middle {A : ℝ}
    (hA_lower : (1 / 4 : ℝ) ≤ A) (hA_upper : A ≤ (2 : ℝ)) :
    (∫ (t : ℝ) in A..(2 * A), φ t ∂volume) ≤ Cφ * A := by
  let s (t : ℝ) : ℝ := Real.sqrt (2 / |1 - t|)
  have hA_le : A ≤ 2 * A := by nlinarith [hA_lower]
  have hφ_int : IntervalIntegrable φ volume A (2 * A) :=
    intervalIntegrable_phi_dyadic_middle hA_lower hA_upper
  have hsqrt : IntervalIntegrable s volume A (2 * A) := by
    simpa [s] using
      intervalIntegrable_sqrt_two_div_abs_one_sub_dyadic_middle hA_lower hA_upper
  have hle_int :
      (∫ (t : ℝ) in A..(2 * A), φ t ∂volume)
        ≤ ∫ (t : ℝ) in A..(2 * A), s t ∂volume := by
    refine intervalIntegral.integral_mono_on
      (μ := (volume : MeasureTheory.Measure ℝ)) hA_le hφ_int hsqrt ?_
    intro t _ht
    exact φ_le_sqrt t
  have hsqrt_le : (∫ (t : ℝ) in A..(2 * A), s t ∂volume) ≤ (4 * K + 1) * A := by
    have hK : (∫ (t : ℝ) in A..(2 * A), s t ∂volume) ≤ K := by
      simpa [s] using integral_sqrt_two_div_abs_one_sub_le_K_dyadic_middle hA_lower hA_upper
    exact le_trans hK (K_le_four_mul_K_add_one_mul_of_quarter_le hA_lower)
  have hcoef : (4 * K + 1 : ℝ) * A ≤ Cφ * A :=
    mul_le_mul_of_nonneg_right four_mul_K_add_one_le_Cφ (by nlinarith [hA_lower])
  exact le_trans hle_int (le_trans hsqrt_le hcoef)

lemma integral_phi_le_Cφ_mul {A : ℝ} (hA : 0 ≤ A) :
    (∫ (t : ℝ) in A..(2 * A), φ t ∂volume) ≤ Cφ * A := by
  by_cases hA0 : A = 0
  · subst hA0
    simp [Cφ, φ, K]
  cases le_total A (1 / 4 : ℝ) with
  | inl hsmall =>
      exact integral_phi_le_Cφ_mul_small hA hsmall
  | inr hge_quarter =>
      cases le_total (2 : ℝ) A with
      | inl hbig =>
          exact integral_phi_le_Cφ_mul_large hbig
      | inr hA_le_two =>
          exact integral_phi_le_Cφ_mul_middle hge_quarter hA_le_two

open scoped BigOperators

lemma volume_Ioc_two_mul_ne_zero {R : ℝ} (hR : 0 < R) :
    (volume : MeasureTheory.Measure ℝ) (Set.Ioc R (2 * R)) ≠ 0 := by
  have hpos : (0 : ℝ) < 2 * R - R := by nlinarith [hR]
  simp [Real.volume_Ioc, ENNReal.ofReal_eq_zero, not_le_of_gt hpos]

lemma volume_Ioc_two_mul_diff_finset_ne_zero (bad : Finset ℝ) {R : ℝ} (hR : 0 < R) :
    (volume : MeasureTheory.Measure ℝ) (Set.Ioc R (2 * R) \ (bad : Set ℝ)) ≠ 0 := by
  have hbad_meas : (volume : MeasureTheory.Measure ℝ) (bad : Set ℝ) = 0 := by
    simpa using (bad.measure_zero (μ := (volume : MeasureTheory.Measure ℝ)))
  have hdiff :
      (volume : MeasureTheory.Measure ℝ) (Set.Ioc R (2 * R) \ (bad : Set ℝ))
        = (volume : MeasureTheory.Measure ℝ) (Set.Ioc R (2 * R)) := by
    simpa [Set.sdiff_eq, Set.inter_assoc, Set.inter_left_comm, Set.inter_comm] using
      (MeasureTheory.measure_sdiff_null (s := Set.Ioc R (2 * R)) (t := (bad : Set ℝ))
        hbad_meas)
  simpa [hdiff] using volume_Ioc_two_mul_ne_zero hR

lemma restrict_volume_Ioc_two_mul_diff_finset_ne_zero (bad : Finset ℝ) {R : ℝ} (hR : 0 < R) :
    (volume.restrict (Set.Ioc R (2 * R))) (Set.Ioc R (2 * R) \ (bad : Set ℝ)) ≠ 0 := by
  have hsubset : Set.Ioc R (2 * R) \ (bad : Set ℝ) ⊆ Set.Ioc R (2 * R) := by
    intro r hr
    exact hr.1
  have hinter :
      (Set.Ioc R (2 * R) \ (bad : Set ℝ)) ∩ Set.Ioc R (2 * R)
        = (Set.Ioc R (2 * R) \ (bad : Set ℝ)) := by
    exact Set.inter_eq_left.mpr hsubset
  simpa [MeasureTheory.Measure.restrict_apply, measurableSet_Ioc, hinter] using
    volume_Ioc_two_mul_diff_finset_ne_zero bad hR

lemma integral_phi_div_le_Cφ_mul {a R : ℝ} (ha : 0 < a) (hR : 0 ≤ R) :
    (∫ (r : ℝ) in R..(2 * R), φ (r / a) ∂volume) ≤ Cφ * R := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hrew :
      (∫ (r : ℝ) in R..(2 * R), φ (r / a) ∂volume)
        = a * (∫ (t : ℝ) in (R / a)..(2 * R / a), φ t ∂volume) := by
    simp [smul_eq_mul, mul_left_comm, mul_comm, div_eq_mul_inv, ha0]
  rw [hrew]
  have hA : 0 ≤ R / a := by
    exact div_nonneg hR ha.le
  have hle : (∫ (t : ℝ) in (R / a)..(2 * (R / a)), φ t ∂volume) ≤ Cφ * (R / a) :=
    integral_phi_le_Cφ_mul (A := R / a) hA
  have hEq : (2 * R / a) = 2 * (R / a) := by ring
  have hle' :
      (∫ (t : ℝ) in (R / a)..(2 * R / a), φ t ∂volume) ≤ Cφ * (R / a) := by
    simpa [hEq] using hle
  have ha_nonneg : 0 ≤ a := ha.le
  have := mul_le_mul_of_nonneg_left hle' ha_nonneg
  have hRHS : a * (Cφ * (R / a)) = Cφ * R := by
    field_simp [ha0]
  simpa [hRHS, mul_assoc, mul_left_comm, mul_comm] using this

lemma intervalIntegrable_sum_mul_phi_div
    {ι : Type} (s : Finset ι) (w : ι → ℝ) (a : ι → ℝ)
    (ha : ∀ i ∈ s, 0 < a i) {R : ℝ} (hR : 0 ≤ R) :
    IntervalIntegrable (∑ i ∈ s, fun r : ℝ => w i * φ (r / a i))
      volume R (2 * R) := by
  refine IntervalIntegrable.sum (μ := volume) (a := R) (b := 2 * R)
    (s := s) (f := fun i : ι => fun r : ℝ => w i * φ (r / a i)) ?_
  intro i hi
  have hφi : IntervalIntegrable (fun r : ℝ => φ (r / a i)) volume R (2 * R) :=
    intervalIntegrable_phi_div (a := a i) (R := R) (ha i hi) hR
  simpa [mul_assoc] using hφi.const_mul (w i)

lemma integral_sum_mul_phi_div_le_Cφ_mul_sum
    {ι : Type} (s : Finset ι) (w : ι → ℝ) (a : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (ha : ∀ i ∈ s, 0 < a i) {R : ℝ} (hR : 0 ≤ R) :
    (∫ r in R..(2 * R), (∑ i ∈ s, fun r : ℝ => w i * φ (r / a i)) r ∂volume)
      ≤ Cφ * (∑ i ∈ s, w i) * R := by
  have hint : ∀ i ∈ s, IntervalIntegrable (fun r : ℝ => w i * φ (r / a i))
      volume R (2 * R) := by
    intro i hi
    have hφi : IntervalIntegrable (fun r : ℝ => φ (r / a i)) volume R (2 * R) :=
      intervalIntegrable_phi_div (a := a i) (R := R) (ha i hi) hR
    simpa [mul_assoc] using hφi.const_mul (w i)
  have hsum_int :
      (∫ r in R..(2 * R), (∑ i ∈ s, fun r : ℝ => w i * φ (r / a i)) r ∂volume)
        = ∑ i ∈ s, ∫ r in R..(2 * R), (fun r : ℝ => w i * φ (r / a i)) r
            ∂volume := by
    simpa using
      (intervalIntegral.integral_finsetSum (μ := volume) (a := R) (b := 2 * R)
        (s := s) (f := fun i : ι => fun r : ℝ => w i * φ (r / a i)) hint)
  rw [hsum_int]
  have hsum_le :
      (∑ i ∈ s, ∫ r in R..(2 * R), (fun r : ℝ => w i * φ (r / a i)) r ∂volume)
        ≤ ∑ i ∈ s, w i * (Cφ * R) := by
    refine Finset.sum_le_sum ?_
    intro i hi
    have hphi :
        (∫ r in R..(2 * R), φ (r / a i) ∂volume) ≤ Cφ * R :=
      integral_phi_div_le_Cφ_mul (a := a i) (R := R) (ha i hi) hR
    have := mul_le_mul_of_nonneg_left hphi (hw i hi)
    simpa [mul_assoc, mul_left_comm, mul_comm] using this
  refine le_trans hsum_le ?_
  have : (∑ i ∈ s, w i * (Cφ * R)) = Cφ * (∑ i ∈ s, w i) * R := by
    calc
      (∑ i ∈ s, w i * (Cφ * R)) = (∑ i ∈ s, w i) * (Cφ * R) := by
        simp [Finset.sum_mul]
      _ = Cφ * (∑ i ∈ s, w i) * R := by
        ac_rfl
  exact le_of_eq this

lemma exists_radius_Ioc_sum_mul_phi_div_le_Cφ_mul_sum_avoid
    {ι : Type} (s : Finset ι) (w : ι → ℝ) (a : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (ha : ∀ i ∈ s, 0 < a i)
    (bad : Finset ℝ) {R : ℝ} (hR : 0 < R) :
    ∃ r ∈ Set.Ioc R (2 * R), r ∉ bad ∧
      (∑ i ∈ s, w i * φ (r / a i)) ≤ Cφ * (∑ i ∈ s, w i) := by
  by_contra hbad
  have hforall :
      ∀ r ∈ Set.Ioc R (2 * R), r ∉ bad →
        Cφ * (∑ i ∈ s, w i) < (∑ i ∈ s, w i * φ (r / a i)) := by
    intro r hr hrbad
    have : ¬(∑ i ∈ s, w i * φ (r / a i)) ≤ Cφ * (∑ i ∈ s, w i) := by
      intro hle
      exact hbad ⟨r, hr, hrbad, hle⟩
    exact lt_of_not_ge this
  let g : ℝ → ℝ := ∑ i ∈ s, fun r : ℝ => w i * φ (r / a i)
  have hg_int : IntervalIntegrable g volume R (2 * R) := by
    simpa [g] using intervalIntegrable_sum_mul_phi_div s w a ha hR.le
  have hconst_int :
      IntervalIntegrable (fun _r : ℝ => Cφ * (∑ i ∈ s, w i)) volume R (2 * R) :=
    intervalIntegrable_const
  have hlt_meas :
      (volume.restrict (Set.Ioc R (2 * R)))
        {r | Cφ * (∑ i ∈ s, w i) < g r} ≠ 0 := by
    have hall : Set.Ioc R (2 * R) \ (bad : Set ℝ) ⊆ {r | Cφ * (∑ i ∈ s, w i) < g r} := by
      intro r hr
      have hrIoc : r ∈ Set.Ioc R (2 * R) := hr.1
      have hrbad : r ∉ bad := by simpa using hr.2
      simpa [g] using hforall r hrIoc hrbad
    have hle :
        (volume.restrict (Set.Ioc R (2 * R))) (Set.Ioc R (2 * R) \ (bad : Set ℝ))
          ≤ (volume.restrict (Set.Ioc R (2 * R))) {r | Cφ * (∑ i ∈ s, w i) < g r} :=
      MeasureTheory.measure_mono hall
    have hpos' :
        (volume.restrict (Set.Ioc R (2 * R))) (Set.Ioc R (2 * R) \ (bad : Set ℝ)) ≠ 0 := by
      exact restrict_volume_Ioc_two_mul_diff_finset_ne_zero bad hR
    intro hzero
    have : (volume.restrict (Set.Ioc R (2 * R))) (Set.Ioc R (2 * R) \ (bad : Set ℝ)) = 0 :=
      le_antisymm (le_trans hle (le_of_eq hzero)) (by positivity)
    exact hpos' this
  have hlt_int :
      (∫ r in R..(2 * R), (Cφ * (∑ i ∈ s, w i)) ∂volume)
        < ∫ r in R..(2 * R), g r ∂volume := by
    have hab : R ≤ 2 * R := by nlinarith [hR.le]
    refine intervalIntegral.integral_lt_integral_of_ae_le_of_measure_setOfPred_lt_ne_zero (μ := volume)
      (a := R) (b := 2 * R) (f := fun _ => (Cφ * (∑ i ∈ s, w i))) (g := g)
      hab hconst_int hg_int ?_ hlt_meas
    have hmem : ∀ᵐ r ∂ (volume.restrict (Set.Ioc R (2 * R))), r ∈ Set.Ioc R (2 * R) :=
      MeasureTheory.ae_restrict_mem (by simp)
    have hnotBad :
        ∀ᵐ r ∂ (volume.restrict (Set.Ioc R (2 * R))), r ∉ (bad : Set ℝ) := by
      simpa using
        (bad.finite_toSet.countable.ae_notMem (μ := (volume.restrict (Set.Ioc R (2 * R)))))
    filter_upwards [hmem, hnotBad] with r hrIoc hrNotBad
    have hrNotBad' : r ∉ bad := by simpa using hrNotBad
    exact le_of_lt (by simpa [g] using hforall r hrIoc hrNotBad')
  have hconst_eval :
      (∫ r in R..(2 * R), (Cφ * (∑ i ∈ s, w i)) ∂volume) = Cφ * (∑ i ∈ s, w i) * R := by
    simp [intervalIntegral.integral_const, sub_eq_add_neg, mul_comm]
    ring
  have hg_le :
      (∫ r in R..(2 * R), g r ∂volume) ≤ Cφ * (∑ i ∈ s, w i) * R := by
    simpa [g] using integral_sum_mul_phi_div_le_Cφ_mul_sum s w a hw ha hR.le
  have : ¬(Cφ * (∑ i ∈ s, w i) * R < Cφ * (∑ i ∈ s, w i) * R) := lt_irrefl _
  have hcontra : Cφ * (∑ i ∈ s, w i) * R < Cφ * (∑ i ∈ s, w i) * R := by
    have := hlt_int
    simpa [hconst_eval] using (this.trans_le hg_le)
  exact this hcontra

lemma exists_radius_Ioc_sum_mul_phi_div_le_Cφ_mul_sum
    {ι : Type} (s : Finset ι) (w : ι → ℝ) (a : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (ha : ∀ i ∈ s, 0 < a i) {R : ℝ} (hR : 0 < R) :
    ∃ r ∈ Set.Ioc R (2 * R), (∑ i ∈ s, w i * φ (r / a i)) ≤ Cφ * (∑ i ∈ s, w i) := by
  rcases exists_radius_Ioc_sum_mul_phi_div_le_Cφ_mul_sum_avoid s w a hw ha ∅ hR with
    ⟨r, hr, -, hle⟩
  exact ⟨r, hr, hle⟩

end CartanBound
end Complex
end
end File31

-- Upstream module PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.CartanInverseFactorBound
section File32
 

section
noncomputable section

namespace Complex.Hadamard

open Complex Real

lemma max_one_norm_div_pow_le_one_add_rpow
    {m : ℕ} {τ r : ℝ} {u a : ℂ}
    (hur : ‖u‖ = r)
    (hmτ : (m : ℝ) ≤ τ) :
    max 1 (‖u / a‖ ^ m) ≤ 1 + (r / ‖a‖) ^ τ := by
  by_cases hx : ‖u / a‖ ≤ 1
  · have hpowm_le1 : ‖u / a‖ ^ m ≤ 1 := pow_le_one₀ (norm_nonneg (u / a)) hx
    have hr0 : 0 ≤ r := by simpa [hur] using (norm_nonneg u)
    have hbase : 0 ≤ r / ‖a‖ := div_nonneg hr0 (norm_nonneg a)
    have hnonneg : 0 ≤ (r / ‖a‖) ^ τ := Real.rpow_nonneg hbase τ
    have hle1 : (1 : ℝ) ≤ 1 + (r / ‖a‖) ^ τ := le_add_of_nonneg_right hnonneg
    have hle2 : ‖u / a‖ ^ m ≤ 1 + (r / ‖a‖) ^ τ := hpowm_le1.trans hle1
    exact (max_le_iff).2 ⟨hle1, hle2⟩
  · have hx1 : 1 < ‖u / a‖ := lt_of_not_ge hx
    have hpow :
        (‖u / a‖ : ℝ) ^ (m : ℝ) ≤ (‖u / a‖ : ℝ) ^ τ :=
      Real.rpow_le_rpow_of_exponent_le (le_of_lt hx1) hmτ
    have hpow' : ‖u / a‖ ^ m ≤ (‖u / a‖ : ℝ) ^ τ := by
      simpa [Real.rpow_natCast] using hpow
    have hmax_add : max 1 (‖u / a‖ ^ m) ≤ 1 + ‖u / a‖ ^ m := by
      refine max_le (le_add_of_nonneg_right (by positivity)) (le_add_of_nonneg_left (by positivity))
    have : max 1 (‖u / a‖ ^ m) ≤ 1 + (‖u / a‖ : ℝ) ^ τ :=
      hmax_add.trans (by nlinarith [hpow'])
    simpa [norm_div, hur] using this

lemma norm_inv_weierstrassFactor_le_exp_near
    {m : ℕ} {τ r : ℝ} {u a : ℂ}
    (hur : ‖u‖ = r) (ha : a ≠ 0) (hr : r ≠ ‖a‖)
    (hmτ : (m : ℝ) ≤ τ) :
    ‖(weierstrassFactor m (u / a))⁻¹‖
      ≤ Real.exp (CartanBound.φ (r / ‖a‖) + (m : ℝ) * (1 + (r / ‖a‖) ^ τ)) := by
  have hlog_one :
      Real.log ‖(1 : ℂ) - u / a‖ ≥ -CartanBound.φ (r / ‖a‖) :=
    CartanBound.log_norm_one_sub_div_ge_neg_phi (hur := hur) (ha := ha) (hr := hr)
  have hbase :=
    log_norm_weierstrassFactor_ge_log_norm_one_sub_sub (m := m) (z := (u / a))
  have hlogE :
      Real.log ‖weierstrassFactor m (u / a)‖
        ≥ -CartanBound.φ (r / ‖a‖) - (m : ℝ) * max 1 (‖u / a‖ ^ m) := by
    have hpls :=
      norm_partialLogSum_le_nat_mul_max_one_norm_pow m (u / a)
    linarith [hbase, hlog_one, hpls]
  have hmax :
      max 1 (‖u / a‖ ^ m) ≤ 1 + (r / ‖a‖) ^ τ :=
    max_one_norm_div_pow_le_one_add_rpow (m := m) (τ := τ) (r := r) (u := u) (a := a) hur hmτ
  have hneglog :
      -Real.log ‖weierstrassFactor m (u / a)‖
        ≤ CartanBound.φ (r / ‖a‖) + (m : ℝ) * (1 + (r / ‖a‖) ^ τ) := by
    have : -Real.log ‖weierstrassFactor m (u / a)‖
        ≤ CartanBound.φ (r / ‖a‖) + (m : ℝ) * max 1 (‖u / a‖ ^ m) := by
      linarith [hlogE]
    have hm0 : 0 ≤ (m : ℝ) := by exact_mod_cast (Nat.zero_le m)
    exact this.trans (by nlinarith [mul_le_mul_of_nonneg_left hmax hm0])
  have hpos : 0 < ‖weierstrassFactor m (u / a)‖ := by
    have : weierstrassFactor m (u / a) ≠ 0 := by
      intro h0
      have : u / a = (1 : ℂ) := (weierstrassFactor_eq_zero_iff m (u / a)).1 h0
      have : u = a := (div_eq_one_iff_eq ha).1 this
      have : r = ‖a‖ := by simpa [this] using hur.symm
      exact (hr this).elim
    exact norm_pos_iff.2 this
  have hEq :
      ‖(weierstrassFactor m (u / a))⁻¹‖ =
        Real.exp (-Real.log ‖weierstrassFactor m (u / a)‖) := by
    simp [norm_inv, Real.exp_neg, Real.exp_log hpos]
  have := Real.exp_le_exp.2 hneglog
  simpa [hEq] using this

lemma norm_inv_weierstrassFactor_le_exp_far
    {m : ℕ} {τ r : ℝ} {u a : ℂ}
    (hur : ‖u‖ = r) (ha : a ≠ 0)
    (hz : ‖u / a‖ ≤ (1 / 2 : ℝ)) (hτ_le : τ ≤ (m + 1 : ℝ)) :
    ‖(weierstrassFactor m (u / a))⁻¹‖ ≤ Real.exp ((2 : ℝ) * (r / ‖a‖) ^ τ) := by
  by_cases hu : u = 0
  · subst hu
    have hr0 : r = 0 := by simpa [hur] using (norm_zero : ‖(0 : ℂ)‖ = 0)
    subst hr0
    have h0 : 0 ≤ ((0 : ℝ) / ‖a‖) ^ τ := by
      exact Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ 0 / ‖a‖) τ
    have h0' : 0 ≤ (2 : ℝ) * ((0 : ℝ) / ‖a‖) ^ τ := mul_nonneg (by norm_num) h0
    have hexp : (1 : ℝ) ≤ Real.exp ((2 : ℝ) * ((0 : ℝ) / ‖a‖) ^ τ) :=
      (Real.one_le_exp_iff).2 h0'
    simpa using hexp
  have hlogE :=
    log_norm_weierstrassFactor_ge_neg_two_pow (m := m) (z := (u / a)) hz
  have hneglog : -Real.log ‖weierstrassFactor m (u / a)‖ ≤ (2 : ℝ) * (r / ‖a‖) ^ τ := by
    have h1 : -Real.log ‖weierstrassFactor m (u / a)‖ ≤ (2 : ℝ) * ‖u / a‖ ^ (m + 1) := by
      linarith [hlogE]
    set x : ℝ := ‖u / a‖
    have hx1 : x ≤ 1 := le_trans (by simpa [x] using hz) (by norm_num)
    have hxpos : 0 < x := by
      simpa [x] using (norm_pos_iff.2 (div_ne_zero hu ha))
    have hτ_le' : τ ≤ ((m + 1 : ℕ) : ℝ) := by
      simpa [Nat.cast_add, Nat.cast_one] using hτ_le
    have hpow_rpow : x ^ ((m + 1 : ℕ) : ℝ) ≤ x ^ τ :=
      Real.rpow_le_rpow_of_exponent_ge hxpos hx1 hτ_le'
    have hpow : x ^ (m + 1) ≤ x ^ τ := by
      simpa [← Real.rpow_natCast] using hpow_rpow
    have h2x : (2 : ℝ) * x ^ (m + 1) ≤ (2 : ℝ) * x ^ τ :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    have h2 : (2 : ℝ) * ‖u / a‖ ^ (m + 1) ≤ (2 : ℝ) * (‖u / a‖ : ℝ) ^ τ := by
      simpa [x] using h2x
    have h3 : (‖u‖ / ‖a‖) ^ τ = (r / ‖a‖) ^ τ := by
      simp [hur]
    exact (h1.trans h2).trans_eq (by simp [h3])
  have hpos : 0 < ‖weierstrassFactor m (u / a)‖ := by
    have : weierstrassFactor m (u / a) ≠ 0 := by
      intro h0
      have : u / a = (1 : ℂ) := (weierstrassFactor_eq_zero_iff m (u / a)).1 h0
      have : u = a := (div_eq_one_iff_eq ha).1 this
      have : (‖u / a‖ : ℝ) = 1 := by simpa [this] using (by simp [ha])
      linarith [hz, this]
    exact norm_pos_iff.2 this
  have hEq :
      ‖(weierstrassFactor m (u / a))⁻¹‖ =
        Real.exp (-Real.log ‖weierstrassFactor m (u / a)‖) := by
    simp [norm_inv, Real.exp_neg, Real.exp_log hpos]
  have := Real.exp_le_exp.2 hneglog
  simpa [hEq] using this

end Complex.Hadamard
end
end
end File32

-- Upstream module PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.CartanMajorantBound
section File33
 

section
noncomputable section

namespace Complex.Hadamard

open scoped BigOperators
open Filter Finset Real Topology

section CartanFiniteSum

variable {α : Type*}

private lemma summable_ite_mem_finset [DecidableEq α] (s : Finset α) (u : α → ℝ) :
    Summable (fun a => if a ∈ s then u a else 0) :=
  summable_of_ne_finset_zero (s := s) fun a ha => by simp [ite_eq_right ha]

private lemma tsum_ite_mem_finset [DecidableEq α] (s : Finset α) (u : α → ℝ) :
    (∑' a, if a ∈ s then u a else 0) = ∑ a ∈ s, u a := by
  classical
  simpa [Finset.sum_ite] using
    (hasSum_sum_of_ne_finset_zero (s := s) (f := fun a => if a ∈ s then u a else 0)
      fun a ha => by simp [ite_eq_right ha]).tsum_eq

private lemma tsum_add_four (u₁ u₂ u₃ u₄ : α → ℝ)
    (h₁ : Summable u₁) (h₂ : Summable u₂) (h₃ : Summable u₃) (h₄ : Summable u₄) :
    tsum (fun a => ((u₁ a + u₂ a) + u₃ a) + u₄ a)
      = tsum u₁ + tsum u₂ + tsum u₃ + tsum u₄ := by
  calc
    tsum (fun a => ((u₁ a + u₂ a) + u₃ a) + u₄ a)
        = tsum (fun a => (u₁ a + u₂ a) + (u₃ a + u₄ a)) := by
          simp [add_comm, add_left_comm]
    _ = tsum (fun a => u₁ a + u₂ a) + tsum (fun a => u₃ a + u₄ a) :=
        Summable.tsum_add (h₁.add h₂) (h₃.add h₄)
    _ = tsum u₁ + tsum u₂ + tsum u₃ + tsum u₄ := by
        rw [Summable.tsum_add h₁ h₂, Summable.tsum_add h₃ h₄]
        ring

end CartanFiniteSum

noncomputable def cartanProductConstant (m : ℕ) (τ Sτ : ℝ) : ℝ :=
  ((CartanBound.Cφ + (2 : ℝ) * m) * (4 : ℝ) ^ τ + 3) * (Sτ + 1)

lemma cartanProductConstant_nonneg {m : ℕ} {τ Sτ : ℝ} (hSτ : 0 ≤ Sτ) :
    0 ≤ cartanProductConstant m τ Sτ := by
  have hS : 0 ≤ Sτ + 1 := by linarith
  have hA : 0 ≤ (CartanBound.Cφ + (2 : ℝ) * m) * (4 : ℝ) ^ τ + 3 := by
    have hCφ : 0 ≤ CartanBound.Cφ := le_of_lt CartanBound.Cφ_pos
    have hm0 : 0 ≤ (m : ℝ) := by exact_mod_cast (Nat.zero_le m)
    have h4τ : 0 ≤ (4 : ℝ) ^ τ := by positivity
    nlinarith [hCφ, hm0, h4τ]
  simpa [cartanProductConstant] using mul_nonneg hA hS

lemma rpow_div_norm_divisorZeroIndex₀_eq
    {f : ℂ → ℂ} {r τ : ℝ} (hr : 0 ≤ r)
    (p : divisorZeroIndex₀ f (Set.univ : Set ℂ)) :
    (r / ‖divisorZeroIndex₀_val p‖) ^ τ =
      (r ^ τ) * ((‖divisorZeroIndex₀_val p‖⁻¹ : ℝ) ^ τ) := by
  have hp : 0 ≤ (‖divisorZeroIndex₀_val p‖⁻¹ : ℝ) := by positivity
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
    (Real.mul_rpow (x := r) (y := (‖divisorZeroIndex₀_val p‖⁻¹ : ℝ)) (z := τ) hr hp)

lemma tsum_rpow_div_norm_divisorZeroIndex₀_eq
    {f : ℂ → ℂ} {r τ : ℝ} (hr : 0 ≤ r) :
    (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ),
        (r / ‖divisorZeroIndex₀_val p‖) ^ τ)
      = (r ^ τ) * ∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ),
          ‖divisorZeroIndex₀_val p‖⁻¹ ^ τ := by
  calc
    (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ),
        (r / ‖divisorZeroIndex₀_val p‖) ^ τ)
        = ∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ),
            (r ^ τ) * (‖divisorZeroIndex₀_val p‖⁻¹ : ℝ) ^ τ := by
            refine tsum_congr ?_
            intro p
            exact rpow_div_norm_divisorZeroIndex₀_eq (f := f) (τ := τ) hr p
    _ = (r ^ τ) * ∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ),
          ‖divisorZeroIndex₀_val p‖⁻¹ ^ τ := by
        simp [tsum_mul_left]

lemma tsum_two_mul_rpow_div_norm_divisorZeroIndex₀_le
    {f : ℂ → ℂ} {r τ : ℝ} (hr : 0 ≤ r) (hτ_nonneg : 0 ≤ τ) :
    (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ),
        (2 : ℝ) * (r / ‖divisorZeroIndex₀_val p‖) ^ τ)
      ≤ (2 : ℝ) * ((∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ),
          ‖divisorZeroIndex₀_val p‖⁻¹ ^ τ) + 1) * (1 + r) ^ τ := by
  set Sτ : ℝ :=
    ∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), ‖divisorZeroIndex₀_val p‖⁻¹ ^ τ
  have htsum :
      (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ),
          (2 : ℝ) * (r / ‖divisorZeroIndex₀_val p‖) ^ τ)
        = (2 : ℝ) * (r ^ τ) * Sτ := by
    calc
      (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ),
          (2 : ℝ) * (r / ‖divisorZeroIndex₀_val p‖) ^ τ)
          = (2 : ℝ) * ∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ),
              (r / ‖divisorZeroIndex₀_val p‖) ^ τ := by
              simp [tsum_mul_left]
      _ = (2 : ℝ) * ((r ^ τ) * Sτ) := by
              rw [tsum_rpow_div_norm_divisorZeroIndex₀_eq (f := f) (τ := τ) hr]
      _ = (2 : ℝ) * (r ^ τ) * Sτ := by ring
  have hSτ_nonneg : 0 ≤ Sτ :=
    tsum_nonneg (fun _ => Real.rpow_nonneg (inv_nonneg.2 (norm_nonneg _)) _)
  have h1r : r ^ τ ≤ (1 + r) ^ τ :=
    Real.rpow_le_rpow (by positivity) (by linarith) hτ_nonneg
  have hS : Sτ ≤ Sτ + 1 := by linarith
  have hle : (r ^ τ) * Sτ ≤ (1 + r) ^ τ * (Sτ + 1) :=
    mul_le_mul h1r hS (by linarith) (by positivity)
  rw [htsum]
  have : (2 : ℝ) * (r ^ τ) * Sτ ≤ (2 : ℝ) * (Sτ + 1) * (1 + r) ^ τ := by
    nlinarith [hle]
  simpa [Sτ, mul_assoc, mul_left_comm, mul_comm] using this

lemma sum_rpow_div_norm_divisorZeroIndex₀_le
    {f : ℂ → ℂ} {r τ : ℝ} (small : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)))
    (hr : 0 ≤ r) (hτ_nonneg : 0 ≤ τ)
    (hsumτ :
      Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
        ‖divisorZeroIndex₀_val p‖⁻¹ ^ τ)) :
    (∑ p ∈ small, (r / ‖divisorZeroIndex₀_val p‖) ^ τ)
      ≤ ((∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ),
          ‖divisorZeroIndex₀_val p‖⁻¹ ^ τ) + 1) * (1 + r) ^ τ := by
  set Sτ : ℝ :=
    ∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), ‖divisorZeroIndex₀_val p‖⁻¹ ^ τ
  have hsum_inv :
      (∑ p ∈ small, (‖divisorZeroIndex₀_val p‖⁻¹ : ℝ) ^ τ) ≤ Sτ := by
    have hnn : ∀ p : divisorZeroIndex₀ f (Set.univ : Set ℂ),
        0 ≤ (‖divisorZeroIndex₀_val p‖⁻¹ : ℝ) ^ τ := by
      intro p
      positivity
    simpa [Sτ] using
      (Summable.sum_le_tsum (s := small)
        (f := fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
          (‖divisorZeroIndex₀_val p‖⁻¹ : ℝ) ^ τ)
        (fun p _ => hnn p) hsumτ)
  have hsum_eq :
      ∑ p ∈ small, (r / ‖divisorZeroIndex₀_val p‖) ^ τ =
        (r ^ τ) * ∑ p ∈ small, (‖divisorZeroIndex₀_val p‖⁻¹ : ℝ) ^ τ := by
    simp [rpow_div_norm_divisorZeroIndex₀_eq (f := f) (τ := τ) hr, Finset.mul_sum]
  have h1r : r ^ τ ≤ (1 + r) ^ τ :=
    Real.rpow_le_rpow (by positivity) (by linarith) hτ_nonneg
  have hS : (∑ p ∈ small, (‖divisorZeroIndex₀_val p‖⁻¹ : ℝ) ^ τ) ≤ Sτ + 1 := by
    linarith [hsum_inv]
  have hle :
      (r ^ τ) * (∑ p ∈ small, (‖divisorZeroIndex₀_val p‖⁻¹ : ℝ) ^ τ)
        ≤ (1 + r) ^ τ * (Sτ + 1) :=
    mul_le_mul h1r hS (by positivity) (by positivity)
  simpa [Sτ, hsum_eq, mul_assoc, mul_left_comm, mul_comm] using hle

lemma add_four_le_add_two_mul_of_le {x₁ x₂ x₃ x₄ A B C : ℝ}
    (h₁ : x₁ ≤ A) (h₂ : x₂ ≤ B) (h₃ : x₃ ≤ B) (h₄ : x₄ ≤ C) :
    x₁ + x₂ + x₃ + x₄ ≤ A + 2 * B + C := by
  nlinarith

lemma cartan_majorant_four_term_bound
    {xφ x0 xm xt Cφ m q Y T : ℝ}
    (hφ : xφ ≤ Cφ * q * Y * T)
    (h0 : x0 ≤ m * q * Y * T)
    (hm : xm ≤ m * q * Y * T)
    (ht : xt ≤ (2 : ℝ) * Y * T) :
    xφ + x0 + xm + xt ≤ (Cφ + (2 : ℝ) * m) * q * Y * T + (2 : ℝ) * Y * T := by
  have h := add_four_le_add_two_mul_of_le hφ h0 hm ht
  have hring :
      Cφ * (q * (Y * T)) + 2 * (m * (q * (Y * T))) + 2 * (Y * T)
        = (Cφ + (2 : ℝ) * m) * (q * (Y * T)) + (2 : ℝ) * (Y * T) := by
    ring
  simpa [mul_assoc, hring] using h

lemma cartan_majorant_add_two_factor (A Y T : ℝ) :
    A * Y * T + (2 : ℝ) * Y * T = ((A + 2) * Y) * T := by
  ring

lemma cartan_majorant_pad_two_to_three {A S T : ℝ} (hS : 0 ≤ S + 1) (hT : 0 ≤ T) :
    ((A + 2) * (S + 1)) * T ≤ ((A + 3) * (S + 1)) * T := by
  have h : (A + 2) * (S + 1) ≤ (A + 3) * (S + 1) := by
    nlinarith
  exact mul_le_mul_of_nonneg_right h hT

lemma cartan_majorant_nonneg
    {f : ℂ → ℂ} {m : ℕ} {τ r : ℝ} (hr : 0 ≤ r)
    (small : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ))) :
    letI : DecidableEq (divisorZeroIndex₀ f (Set.univ : Set ℂ)) := Classical.decEq _
    let ap : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ := fun p => ‖divisorZeroIndex₀_val p‖
    let b : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ :=
      fun p =>
        if p ∈ small then
          CartanBound.φ (r / ap p) + (m : ℝ) * (1 + (r / ap p) ^ τ)
        else
          (2 : ℝ) * (r / ap p) ^ τ
    ∀ p, 0 ≤ b p := by
  classical
  dsimp
  intro p
  let ap : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ := fun q => ‖divisorZeroIndex₀_val q‖
  have hap : ap p = ‖divisorZeroIndex₀_val p‖ := rfl
  by_cases hp : p ∈ small
  · have hφ : 0 ≤ CartanBound.φ (r / ap p) := CartanBound.φ_nonneg (t := r / ap p)
    have hm0 : 0 ≤ (m : ℝ) := by exact_mod_cast (Nat.zero_le m)
    have h1 : 0 ≤ (1 + (r / ap p) ^ τ) := by positivity
    have : 0 ≤ CartanBound.φ (r / ap p) + (m : ℝ) * (1 + (r / ap p) ^ τ) := by
      nlinarith [hφ, hm0, h1]
    simpa [hap, hp, ap] using this
  · have hbase : 0 ≤ r / ap p := div_nonneg hr (by positivity)
    have hpow : 0 ≤ (r / ap p) ^ τ := Real.rpow_nonneg hbase τ
    have : 0 ≤ (2 : ℝ) * (r / ap p) ^ τ := mul_nonneg (by norm_num) hpow
    simpa [hap, hp, ap] using this

lemma cartan_majorant_summable
    {f : ℂ → ℂ} {m : ℕ} {τ r : ℝ} (hr : 0 ≤ r)
    (small : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)))
    (hsumτ :
      Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
        ‖divisorZeroIndex₀_val p‖⁻¹ ^ τ)) :
    letI : DecidableEq (divisorZeroIndex₀ f (Set.univ : Set ℂ)) := Classical.decEq _
    let ap : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ := fun p => ‖divisorZeroIndex₀_val p‖
    let b : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ :=
      fun p =>
        if p ∈ small then
          CartanBound.φ (r / ap p) + (m : ℝ) * (1 + (r / ap p) ^ τ)
        else
          (2 : ℝ) * (r / ap p) ^ τ
    Summable b := by
  classical
  dsimp
  let ap : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ := fun q => ‖divisorZeroIndex₀_val q‖
  let b : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ :=
    fun p =>
      if p ∈ small then
        CartanBound.φ (r / ap p) + (m : ℝ) * (1 + (r / ap p) ^ τ)
      else
        (2 : ℝ) * (r / ap p) ^ τ
  have hb : Summable b := by
    let b₁ : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ :=
      fun p =>
        if p ∈ small then
          CartanBound.φ (r / ap p) + (m : ℝ) * (1 + (r / ap p) ^ τ)
        else 0
    let b₂ : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ :=
      fun p => if p ∈ small then 0 else (2 : ℝ) * (r / ap p) ^ τ
    have hb_decomp : b = fun p => b₁ p + b₂ p := by
      funext p
      by_cases hp : p ∈ small <;> simp [b, b₁, b₂, hp]
    have hb₁ : Summable b₁ := by
      simpa [b₁] using
        summable_ite_mem_finset small
          (fun p => CartanBound.φ (r / ap p) + (m : ℝ) * (1 + (r / ap p) ^ τ))
    have hb₂ : Summable b₂ := by
      have hconst :
          Summable (fun p =>
            (2 : ℝ) * (r ^ τ) * (‖divisorZeroIndex₀_val p‖⁻¹ ^ τ)) :=
        hsumτ.mul_left ((2 : ℝ) * (r ^ τ))
      refine Summable.of_nonneg_of_le
        (fun p => by
          by_cases hp : p ∈ small
          · simp [b₂, hp]
          · have : 0 ≤ (2 : ℝ) * (r / ap p) ^ τ := by positivity
            simpa [b₂, hp] using this)
        (fun p => ?_) hconst
      by_cases hp : p ∈ small
      · have : 0 ≤ (2 : ℝ) * (r ^ τ) * (‖divisorZeroIndex₀_val p‖⁻¹ ^ τ) := by positivity
        simpa [b₂, hp] using this
      · have hrpow : (r / ap p) ^ τ = (r ^ τ) * (‖divisorZeroIndex₀_val p‖⁻¹ ^ τ) := by
          simpa [ap] using rpow_div_norm_divisorZeroIndex₀_eq (f := f) (τ := τ) hr p
        simp [b₂, hp, hrpow, mul_assoc, mul_left_comm, mul_comm]
    simpa [hb_decomp] using hb₁.add hb₂
  refine hb.congr ?_
  intro p
  by_cases hp : p ∈ small <;> simp [b, ap, hp]

lemma cartan_card_small_le
    {f : ℂ → ℂ} {τ R : ℝ} (hRpos : 0 < R) (hτ_nonneg : 0 ≤ τ)
    (small : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)))
    (hsmall : ∀ p ∈ small, ‖divisorZeroIndex₀_val p‖ ≤ 4 * R)
    (hsumτ :
      Summable
        (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
          ‖divisorZeroIndex₀_val p‖⁻¹ ^ τ)) :
    (small.card : ℝ)
      ≤ (4 * R) ^ τ
          * ((∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ),
                ‖divisorZeroIndex₀_val p‖⁻¹ ^ τ) + 1) := by
  classical
  set Sτ : ℝ :=
    ∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), ‖divisorZeroIndex₀_val p‖⁻¹ ^ τ
  have hsum_le : (∑ p ∈ small, ‖divisorZeroIndex₀_val p‖⁻¹ ^ τ) ≤ Sτ := by
    have hnn :
        ∀ p : divisorZeroIndex₀ f (Set.univ : Set ℂ),
          0 ≤ ‖divisorZeroIndex₀_val p‖⁻¹ ^ τ := by
      intro p
      exact Real.rpow_nonneg (inv_nonneg.2 (norm_nonneg _)) _
    simpa [Sτ] using
      (Summable.sum_le_tsum (s := small)
        (f := fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
          ‖divisorZeroIndex₀_val p‖⁻¹ ^ τ)
        (fun p _ => hnn p) hsumτ)
  have hgeom_sum :
      (small.card : ℝ) ≤ ∑ p ∈ small, (4 * R) ^ τ * ‖divisorZeroIndex₀_val p‖⁻¹ ^ τ := by
    have hcard_eq : (small.card : ℝ) = ∑ p ∈ small, (1 : ℝ) := by simp
    rw [hcard_eq]
    refine Finset.sum_le_sum (fun p hp => ?_)
    have hp_le : ‖divisorZeroIndex₀_val p‖ ≤ 4 * R := hsmall p hp
    have hap : 0 < ‖divisorZeroIndex₀_val p‖ :=
      norm_pos_iff.2 (divisorZeroIndex₀_val_ne_zero p)
    have hbase : (1 : ℝ) ≤ (4 * R) / ‖divisorZeroIndex₀_val p‖ := by
      exact (le_div_iff₀ hap).2 (by simpa [mul_one] using hp_le)
    have : (1 : ℝ) ≤ ((4 * R) / ‖divisorZeroIndex₀_val p‖) ^ τ :=
      Real.one_le_rpow hbase hτ_nonneg
    have hdiv :
        ((4 * R) / ‖divisorZeroIndex₀_val p‖) ^ τ =
          (4 * R) ^ τ * (‖divisorZeroIndex₀_val p‖)⁻¹ ^ τ := by
      have h4 : 0 ≤ (4 * R : ℝ) := by nlinarith [le_of_lt hRpos]
      have ha : 0 ≤ (‖divisorZeroIndex₀_val p‖ : ℝ)⁻¹ := by positivity
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
        (Real.mul_rpow (x := (4 * R : ℝ))
          (y := (‖divisorZeroIndex₀_val p‖ : ℝ)⁻¹) (z := τ) h4 ha)
    have : (1 : ℝ) ≤ (4 * R) ^ τ * ‖divisorZeroIndex₀_val p‖⁻¹ ^ τ := by
      simpa [hdiv] using this
    exact this
  have hgeom :
      (small.card : ℝ) ≤ (4 * R) ^ τ * (∑ p ∈ small, ‖divisorZeroIndex₀_val p‖⁻¹ ^ τ) := by
    simpa [Finset.mul_sum] using hgeom_sum
  have hsmall_le : (small.card : ℝ) ≤ (4 * R) ^ τ * Sτ := by
    exact hgeom.trans (mul_le_mul_of_nonneg_left hsum_le (by positivity))
  have hS_le : (4 * R) ^ τ * Sτ ≤ (4 * R) ^ τ * (Sτ + 1) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    linarith
  have : (small.card : ℝ) ≤ (4 * R) ^ τ * (Sτ + 1) := hsmall_le.trans hS_le
  simpa [Sτ, add_comm, add_left_comm, add_assoc, mul_assoc] using this

lemma cartan_rpow_mul_le
    {τ R r : ℝ} (hRpos : 0 < R) (hrpos : 0 < r) (hR_le_r : R ≤ r) (hτ_nonneg : 0 ≤ τ) :
    (4 * R) ^ τ ≤ (4 : ℝ) ^ τ * (1 + r) ^ τ := by
  have hR_le_1r : R ≤ 1 + r := by linarith [hR_le_r, le_of_lt hrpos]
  have hbase0 : 0 ≤ (4 * R : ℝ) := by nlinarith [le_of_lt hRpos]
  have : (4 * R) ^ τ ≤ (4 * (1 + r)) ^ τ := by
    refine Real.rpow_le_rpow hbase0 ?_ hτ_nonneg
    nlinarith [hR_le_1r]
  have hmul : (4 * (1 + r)) ^ τ = (4 : ℝ) ^ τ * (1 + r) ^ τ := by
    have h4 : 0 ≤ (4 : ℝ) := by norm_num
    have h1 : 0 ≤ (1 + r : ℝ) := by positivity
    simpa [mul_assoc] using
      (Real.mul_rpow (x := (4 : ℝ)) (y := (1 + r : ℝ)) (z := τ) h4 h1)
  simpa [hmul] using this

open Classical in
theorem cartan_sum_majorant_le
    {f : ℂ → ℂ} {m : ℕ} {τ R r : ℝ}
    (hRpos : 0 < R)
    (hrpos : 0 < r)
    (hR_le_r : R ≤ r)
    (hτ_nonneg : 0 ≤ τ)
    (smallSet : Set (divisorZeroIndex₀ f (Set.univ : Set ℂ)))
    (hsmall_fin : smallSet.Finite)
    (hsmallSet :
      smallSet = {p : divisorZeroIndex₀ f (Set.univ : Set ℂ) | ‖divisorZeroIndex₀_val p‖ ≤ 4 * R})
    (hsumτ :
      Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) => ‖divisorZeroIndex₀_val p‖⁻¹ ^ τ))
    (hr_phi :
      let small : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) := hsmall_fin.toFinset
      let a : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ := fun p => ‖divisorZeroIndex₀_val p‖
      (∑ p ∈ small, CartanBound.φ (r / a p)) ≤ CartanBound.Cφ * (small.card : ℝ)) :
    let small : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) := hsmall_fin.toFinset
    letI : DecidableEq (divisorZeroIndex₀ f (Set.univ : Set ℂ)) := Classical.decEq _
    let ap : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ := fun p => ‖divisorZeroIndex₀_val p‖
    let b : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ :=
      fun p =>
        if p ∈ small then
          CartanBound.φ (r / ap p) + (m : ℝ) * (1 + (r / ap p) ^ τ)
        else
          (2 : ℝ) * (r / ap p) ^ τ
    let Sτ : ℝ := ∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), ‖divisorZeroIndex₀_val p‖⁻¹ ^ τ
    let Cprod : ℝ := cartanProductConstant m τ Sτ
    ∀ s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)),
      (∑ p ∈ s, b p) ≤ Cprod * (1 + r) ^ τ := by
  classical
  intro small ap b Sτ Cprod s
  have hr : 0 ≤ r := le_of_lt hrpos
  have hSτ_nonneg : 0 ≤ Sτ :=
    tsum_nonneg (fun _ => Real.rpow_nonneg (inv_nonneg.2 (norm_nonneg _)) _)
  have hsmall_mem : ∀ p, p ∈ small ↔ p ∈ smallSet := by
    intro p
    simp [small, hsmall_fin.mem_toFinset]
  have hphi_sum :
      (∑ p ∈ small, CartanBound.φ (r / ap p)) ≤ CartanBound.Cφ * (small.card : ℝ) := by
    simpa [small, ap] using hr_phi
  have hb_nonneg : ∀ p, 0 ≤ b p := by
    simpa [ap, b] using (cartan_majorant_nonneg (f := f) (m := m) (τ := τ) (r := r) hr small)
  have hb_summable : Summable b := by
    simpa [ap, b] using
      (cartan_majorant_summable (f := f) (m := m) (τ := τ) (r := r) hr small hsumτ)
  have hsmall_norm : ∀ p ∈ small, ‖divisorZeroIndex₀_val p‖ ≤ 4 * R := by
    intro p hp
    have : p ∈ smallSet := (hsmall_mem p).1 hp
    simpa [hsmallSet] using this
  have hcard_le : (small.card : ℝ) ≤ (4 * R) ^ τ * (Sτ + 1) := by
    simpa [Sτ, mul_assoc, add_assoc, add_left_comm, add_comm] using
      (cartan_card_small_le (f := f) (τ := τ) (R := R) hRpos hτ_nonneg small hsmall_norm hsumτ)
  have hpowR : (4 * R) ^ τ ≤ (4 : ℝ) ^ τ * (1 + r) ^ τ :=
    cartan_rpow_mul_le (τ := τ) (R := R) (r := r) hRpos hrpos hR_le_r hτ_nonneg
  have hcard_le' : (small.card : ℝ) ≤ (4 : ℝ) ^ τ * (1 + r) ^ τ * (Sτ + 1) := by
    have : (4 * R) ^ τ * (Sτ + 1) ≤ (4 : ℝ) ^ τ * (1 + r) ^ τ * (Sτ + 1) := by
      exact mul_le_mul_of_nonneg_right hpowR (by linarith [hSτ_nonneg])
    exact le_trans hcard_le this
  have hb_tsum_le :
      (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), b p) ≤ Cprod * (1 + r) ^ τ := by
    let bφ : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ :=
      fun p => if p ∈ small then CartanBound.φ (r / ap p) else 0
    let b0 : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ :=
      fun p => if p ∈ small then (m : ℝ) else 0
    let bmτ : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ :=
      fun p => if p ∈ small then (m : ℝ) * (r / ap p) ^ τ else 0
    let bt : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ :=
      fun p => (2 : ℝ) * (r / ap p) ^ τ
    have hb_pointwise : ∀ p, b p ≤ bφ p + b0 p + bmτ p + bt p := by
      intro p
      by_cases hp : p ∈ small
      · have hbase : 0 ≤ r / ap p := div_nonneg hr (by positivity)
        have hx : 0 ≤ (r / ap p) ^ τ := Real.rpow_nonneg hbase τ
        have hpos : 0 ≤ (2 : ℝ) * (r / ap p) ^ τ := mul_nonneg (by norm_num) hx
        simp [b, bφ, b0, bmτ, bt, hp]
        nlinarith
      · simp [b, bφ, b0, bmτ, bt, hp]
    have hmaj_summ : Summable (fun p => bφ p + b0 p + bmτ p + bt p) := by
      have hbφ_summ : Summable bφ := by
        simpa [bφ] using summable_ite_mem_finset small (fun p => CartanBound.φ (r / ap p))
      have hb0_summ : Summable b0 := by
        simpa [b0] using summable_ite_mem_finset small (fun _ => (m : ℝ))
      have hbmτ_summ : Summable bmτ := by
        simpa [bmτ] using summable_ite_mem_finset small (fun p => (m : ℝ) * (r / ap p) ^ τ)
      have hbt_summ : Summable bt := by
        have hconst : Summable (fun p =>
            (2 : ℝ) * (r ^ τ) * (‖divisorZeroIndex₀_val p‖⁻¹ ^ τ)) :=
          hsumτ.mul_left ((2 : ℝ) * (r ^ τ))
        refine hconst.congr ?_
        intro p
        simp [bt, ap, rpow_div_norm_divisorZeroIndex₀_eq (f := f) (τ := τ) hr p,
          mul_assoc, mul_left_comm, mul_comm]
      have h' : Summable (fun p => bφ p + b0 p + (bmτ p + bt p)) :=
        (hbφ_summ.add hb0_summ).add (hbmτ_summ.add hbt_summ)
      simpa [add_assoc] using h'
    have htsum_le :
        (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), b p)
          ≤ ∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), (bφ p + b0 p + bmτ p + bt p) :=
      (hasSum_le hb_pointwise hb_summable.hasSum hmaj_summ.hasSum)
    have htsum_bφ :
        (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), bφ p)
          = ∑ p ∈ small, CartanBound.φ (r / ap p) := by
      classical
      simpa [bφ] using tsum_ite_mem_finset small (fun p => CartanBound.φ (r / ap p))
    have htsum_b0 :
        (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), b0 p)
          = (m : ℝ) * (small.card : ℝ) := by
      classical
      have : (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), b0 p) = ∑ p ∈ small, (m : ℝ) := by
        simpa [b0] using tsum_ite_mem_finset small (fun _ => (m : ℝ))
      simp [this, Finset.sum_const, nsmul_eq_mul, mul_comm]
    have htsum_bmτ :
        (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), bmτ p)
          = (m : ℝ) * ∑ p ∈ small, (r / ap p) ^ τ := by
      classical
      have :
          (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), bmτ p)
            = ∑ p ∈ small, (m : ℝ) * (r / ap p) ^ τ := by
        simpa [bmτ] using tsum_ite_mem_finset small (fun p => (m : ℝ) * (r / ap p) ^ τ)
      simp [this, Finset.mul_sum]
    have htsum_bt :
        (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), bt p)
          ≤ (2 : ℝ) * (Sτ + 1) * (1 + r) ^ τ := by
      simpa [bt, ap, Sτ] using
        tsum_two_mul_rpow_div_norm_divisorZeroIndex₀_le (f := f) (τ := τ) hr hτ_nonneg
    have hsum_small_rpow_le :
        (∑ p ∈ small, (r / ap p) ^ τ) ≤ (Sτ + 1) * (1 + r) ^ τ := by
      simpa [ap, Sτ] using
        sum_rpow_div_norm_divisorZeroIndex₀_le (f := f) (τ := τ) small hr hτ_nonneg hsumτ
    have hm0 : 0 ≤ (m : ℝ) := by exact_mod_cast (Nat.zero_le m)
    have hCφ : 0 ≤ CartanBound.Cφ := le_of_lt CartanBound.Cφ_pos
    have hS : 0 ≤ Sτ + 1 := by linarith [hSτ_nonneg]
    have htsum_majorant :
        (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), (bφ p + b0 p + bmτ p + bt p))
          ≤ (((CartanBound.Cφ + (2 : ℝ) * m) * (4 : ℝ) ^ τ + 2) * (Sτ + 1))
              * (1 + r) ^ τ := by
      have hφ_le :
          (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), bφ p)
            ≤ CartanBound.Cφ * (small.card : ℝ) := by
        simpa [htsum_bφ] using hphi_sum
      have hb0_le :
          (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), b0 p)
            ≤ (m : ℝ) * (small.card : ℝ) := by
        simp [htsum_b0]
      have hbmτ_le :
          (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), bmτ p) ≤
            (m : ℝ) * (4 : ℝ) ^ τ * (Sτ + 1) * (1 + r) ^ τ := by
        have h0 :
            (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), bmτ p)
              ≤ (m : ℝ) * ((Sτ + 1) * (1 + r) ^ τ) := by
          have hmul := mul_le_mul_of_nonneg_left hsum_small_rpow_le hm0
          
          simpa [htsum_bmτ, mul_assoc, mul_left_comm, mul_comm] using hmul
        have h1 : (1 : ℝ) ≤ (4 : ℝ) ^ τ :=
          Real.one_le_rpow (by norm_num) hτ_nonneg
        have hscale :
            (m : ℝ) * ((Sτ + 1) * (1 + r) ^ τ)
              ≤ (m : ℝ) * (4 : ℝ) ^ τ * (Sτ + 1) * (1 + r) ^ τ := by
          have hnonneg : 0 ≤ (m : ℝ) * ((Sτ + 1) * (1 + r) ^ τ) := by
            have : 0 ≤ (Sτ + 1) * (1 + r) ^ τ := by positivity
            exact mul_nonneg hm0 this
          simpa [mul_assoc, mul_left_comm, mul_comm] using (mul_le_mul_of_nonneg_right h1 hnonneg)
        exact h0.trans hscale
      have hbt_le :
          (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), bt p)
            ≤ (2 : ℝ) * (Sτ + 1) * (1 + r) ^ τ := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using htsum_bt
      have hsplit :
          (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), (bφ p + b0 p + bmτ p + bt p))
            = (∑' p, bφ p) + (∑' p, b0 p) + (∑' p, bmτ p) + (∑' p, bt p) := by
        classical
        have hbφ_summ : Summable bφ := by
          simpa [bφ] using summable_ite_mem_finset small (fun p => CartanBound.φ (r / ap p))
        have hb0_summ : Summable b0 := by
          simpa [b0] using summable_ite_mem_finset small (fun _ => (m : ℝ))
        have hbmτ_summ : Summable bmτ := by
          simpa [bmτ] using summable_ite_mem_finset small (fun p => (m : ℝ) * (r / ap p) ^ τ)
        have hbt_summ : Summable bt := by
          have hconst :
              Summable
                (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
                  (2 : ℝ) * (r ^ τ) * ((‖divisorZeroIndex₀_val p‖⁻¹ : ℝ) ^ τ)) :=
            hsumτ.mul_left ((2 : ℝ) * (r ^ τ))
          refine hconst.congr ?_
          intro p
          simp [bt, ap, rpow_div_norm_divisorZeroIndex₀_eq (f := f) (τ := τ) hr p,
            mul_assoc, mul_left_comm, mul_comm]
        exact tsum_add_four bφ b0 bmτ bt hbφ_summ hb0_summ hbmτ_summ hbt_summ
      have hcard_le'' :
          (small.card : ℝ) ≤ (4 : ℝ) ^ τ * (Sτ + 1) * (1 + r) ^ τ := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using hcard_le'
      have hφ_le' :
          (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), bφ p) ≤
            CartanBound.Cφ * (4 : ℝ) ^ τ * (Sτ + 1) * (1 + r) ^ τ := by
        have : CartanBound.Cφ * (small.card : ℝ) ≤
            CartanBound.Cφ * ((4 : ℝ) ^ τ * (Sτ + 1) * (1 + r) ^ τ) :=
          mul_le_mul_of_nonneg_left hcard_le'' hCφ
        exact hφ_le.trans (by simpa [mul_assoc, mul_left_comm, mul_comm] using this)
      have hb0_le' :
          (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), b0 p) ≤
            (m : ℝ) * (4 : ℝ) ^ τ * (Sτ + 1) * (1 + r) ^ τ := by
        have : (m : ℝ) * (small.card : ℝ) ≤ (m : ℝ) * ((4 : ℝ) ^ τ * (Sτ + 1) * (1 + r) ^ τ) :=
          mul_le_mul_of_nonneg_left hcard_le'' hm0
        exact hb0_le.trans (by simpa [mul_assoc, mul_left_comm, mul_comm] using this)
      have htsum_majorant' :
          (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), (bφ p + b0 p + bmτ p + bt p))
            ≤ (CartanBound.Cφ + (2 : ℝ) * m) * (4 : ℝ) ^ τ * (Sτ + 1) * (1 + r) ^ τ
              + (2 : ℝ) * (Sτ + 1) * (1 + r) ^ τ := by
        rw [hsplit]
        set Y : ℝ := Sτ + 1 with hY
        set T : ℝ := (1 + r) ^ τ with hT
        have hφ_leY :
            (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), bφ p)
              ≤ CartanBound.Cφ * (4 : ℝ) ^ τ * Y * T := by
          simpa [hY, hT, mul_assoc] using hφ_le'
        have hb0_leY :
            (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), b0 p)
              ≤ (m : ℝ) * (4 : ℝ) ^ τ * Y * T := by
          simpa [hY, hT, mul_assoc] using hb0_le'
        have hbmτ_leY :
            (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), bmτ p)
              ≤ (m : ℝ) * (4 : ℝ) ^ τ * Y * T := by
          simpa [hY, hT, mul_assoc] using hbmτ_le
        have hbt_leY :
            (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), bt p) ≤ (2 : ℝ) * Y * T := by
          simpa [hY, hT, mul_assoc] using hbt_le
        have hmain :=
          cartan_majorant_four_term_bound
            (q := (4 : ℝ) ^ τ) hφ_leY hb0_leY hbmτ_leY hbt_leY
        simpa [Y, T, add_assoc] using hmain
      have hring :
          (CartanBound.Cφ + (2 : ℝ) * m) * (4 : ℝ) ^ τ * (Sτ + 1) * (1 + r) ^ τ
              + (2 : ℝ) * (Sτ + 1) * (1 + r) ^ τ
            = (((CartanBound.Cφ + (2 : ℝ) * m) * (4 : ℝ) ^ τ + 2) * (Sτ + 1)) * (1 + r) ^ τ := by
        exact cartan_majorant_add_two_factor
          ((CartanBound.Cφ + (2 : ℝ) * m) * (4 : ℝ) ^ τ) (Sτ + 1) ((1 + r) ^ τ)
      rw [← hring]
      exact htsum_majorant'
    have hCprod' :
        (((CartanBound.Cφ + (2 : ℝ) * m) * (4 : ℝ) ^ τ + 2) * (Sτ + 1)) * (1 + r) ^ τ
          ≤ Cprod * (1 + r) ^ τ := by
      simpa [Cprod, cartanProductConstant, mul_assoc, mul_left_comm, mul_comm] using
        cartan_majorant_pad_two_to_three
          (A := (CartanBound.Cφ + (2 : ℝ) * m) * (4 : ℝ) ^ τ)
          (S := Sτ) (T := (1 + r) ^ τ) hS (by positivity)
    exact (le_trans (le_trans htsum_le htsum_majorant) hCprod')
  have hsum_fin_le :
      (∑ p ∈ s, b p) ≤ (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), b p) := by
    simpa using
      (Summable.sum_le_tsum (s := s) (f := b) (fun p _ => hb_nonneg p) hb_summable)
  exact hsum_fin_le.trans hb_tsum_le

end Complex.Hadamard
end
end
end File33

-- Upstream module PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.CartanProductBound
section File34
 

section
noncomputable section

open scoped BigOperators
open Filter Finset Real Topology

lemma Finset.prod_le_exp_sum {α : Type} (s : Finset α) (a : α → ℝ) (b : α → ℝ)
    (ha : ∀ x ∈ s, 0 ≤ a x) (hab : ∀ x ∈ s, a x ≤ Real.exp (b x)) :
    (∏ x ∈ s, a x) ≤ Real.exp (∑ x ∈ s, b x) := by
  calc
    (∏ x ∈ s, a x) ≤ ∏ x ∈ s, Real.exp (b x) := Finset.prod_le_prod₀ ha hab
    _ = Real.exp (∑ x ∈ s, b x) := by
      simpa using (Real.exp_sum (s := s) (f := b)).symm

lemma hasProd_le_of_prod_le_exp {α : Type} {f : α → ℝ} {a : ℝ}
    (hf : HasProd f a (SummationFilter.unconditional α))
    {B : ℝ} (hB : ∀ s : Finset α, (∏ x ∈ s, f x) ≤ Real.exp B) :
    a ≤ Real.exp B :=
  hasProd_le_of_prod_le (L := (SummationFilter.unconditional α)) hf hB

lemma hasProd_inv_unconditional {α : Type} {fac : α → ℂ} {F : ℂ}
    (hfac : HasProd fac F (SummationFilter.unconditional α)) (hF : F ≠ 0) :
    HasProd (fun x => (fac x)⁻¹) (F⁻¹) (SummationFilter.unconditional α) := by
  change
    Tendsto (fun s : Finset α => ∏ x ∈ s, (fac x)⁻¹)
      (SummationFilter.unconditional α).filter (𝓝 (F⁻¹))
  have hprod :
      Tendsto (fun s : Finset α => ∏ x ∈ s, fac x)
        (SummationFilter.unconditional α).filter (𝓝 F) := by
    simpa [HasProd] using hfac
  have hinv :
      Tendsto (fun s : Finset α => (∏ x ∈ s, fac x)⁻¹)
        (SummationFilter.unconditional α).filter (𝓝 (F⁻¹)) :=
    hprod.inv₀ hF
  refine hinv.congr' (Filter.Eventually.of_forall ?_)
  intro s
  simp [Finset.prod_inv_distrib]

lemma hasProd_norm_inv_unconditional {α : Type} {fac : α → ℂ} {F : ℂ}
    (hfac : HasProd fac F (SummationFilter.unconditional α)) (hF : F ≠ 0) :
    HasProd (fun x => ‖(fac x)⁻¹‖) ‖F⁻¹‖ (SummationFilter.unconditional α) := by
  change
    Tendsto (fun s : Finset α => ∏ x ∈ s, ‖(fac x)⁻¹‖)
      (SummationFilter.unconditional α).filter (𝓝 ‖F⁻¹‖)
  have hnorm := (hasProd_inv_unconditional hfac hF).norm
  refine hnorm.congr' (Filter.Eventually.of_forall ?_)
  intro s
  simp [norm_inv, Finset.prod_inv_distrib]

lemma hasProd_norm_inv_le_exp_of_pointwise_le_exp {α : Type} {fac : α → ℂ} {F : ℂ}
    (hfac : HasProd fac F (SummationFilter.unconditional α))
    (b : α → ℝ) (B : ℝ)
    (hterm : ∀ x, ‖(fac x)⁻¹‖ ≤ Real.exp (b x))
    (hsum : ∀ s : Finset α, (∑ x ∈ s, b x) ≤ B) :
    ‖F⁻¹‖ ≤ Real.exp B := by
  by_cases hF : F = 0
  · subst hF
    simpa using exp_nonneg B
  have hnorm :
      HasProd (fun x => ‖(fac x)⁻¹‖) ‖F⁻¹‖ (SummationFilter.unconditional α) :=
    hasProd_norm_inv_unconditional hfac hF
  have hprod : ∀ s : Finset α, (∏ x ∈ s, ‖(fac x)⁻¹‖) ≤ Real.exp B := by
    intro s
    have h0 : ∀ x ∈ s, 0 ≤ ‖(fac x)⁻¹‖ := by intro _ _; positivity
    have h1 : (∏ x ∈ s, ‖(fac x)⁻¹‖) ≤ Real.exp (∑ x ∈ s, b x) := by
      refine Finset.prod_le_exp_sum s (a := fun x => ‖(fac x)⁻¹‖) (b := b) h0 ?_
      intro x hx
      simpa using hterm x
    have h2 : Real.exp (∑ x ∈ s, b x) ≤ Real.exp B :=
      Real.exp_le_exp.2 (hsum s)
    exact h1.trans h2
  exact hasProd_le_of_prod_le_exp hnorm hprod
end
end
end File34

-- Upstream module PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.BorelCaratheodory
section File35

section
open Metric

namespace Complex

theorem borelCaratheodory_zero_closedBall {f : ℂ → ℂ} {M r R : ℝ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    (hr : 0 < r) (hlt : r < R) (hM : 0 < M) (hf0 : f 0 = 0)
    (hf_re : ∀ w, ‖w‖ ≤ R → (f w).re ≤ M) {z : ℂ} (hz : ‖z‖ ≤ r) :
    ‖f z‖ ≤ 2 * M * r / (R - r) := by
  have hR : 0 < R := lt_trans hr hlt
  have hz_ball : z ∈ Metric.ball (0 : ℂ) R := by
    rw [Metric.mem_ball, dist_zero_right]
    exact hz.trans_lt hlt
  have hf_diff : DifferentiableOn ℂ f (Metric.ball (0 : ℂ) R) := by
    intro w hw
    have hw' : w ∈ Metric.closedBall (0 : ℂ) R := ball_subset_closedBall hw
    exact (hf w hw').differentiableAt.differentiableWithinAt
  have hf_map : Set.MapsTo f (Metric.ball (0 : ℂ) R) {w | w.re ≤ M} := by
    intro w hw
    simp only [Set.mem_ofPred_eq]
    have hw' : ‖w‖ < R := by simpa [Metric.mem_ball, dist_zero_right] using hw
    exact hf_re w hw'.le
  have hbc :=
    borelCaratheodory_zero hM hf_diff hf_map hR hz_ball hf0
  have hzR : ‖z‖ < R := by
    rw [Metric.mem_ball, dist_zero_right] at hz_ball
    exact hz_ball
  have hmono : ‖z‖ / (R - ‖z‖) ≤ r / (R - r) := by
    have hrden : 0 < R - r := sub_pos.mpr hlt
    have hden : 0 < R - ‖z‖ := sub_pos.mpr hzR
    rw [div_le_div_iff₀ hden hrden]
    nlinarith [hz, norm_nonneg z]
  have hM' : 0 ≤ 2 * M := mul_nonneg (by norm_num) (le_of_lt hM)
  calc ‖f z‖
      ≤ 2 * M * ‖z‖ / (R - ‖z‖) := hbc
    _ ≤ 2 * M * (r / (R - r)) := by
        simpa [mul_div_assoc] using mul_le_mul_of_nonneg_left hmono hM'
    _ = 2 * M * r / (R - r) := by ring

end Complex
end
end File35

-- Upstream module PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.ExpPoly
section File36
 

section
noncomputable section

namespace Complex
namespace Hadamard

open Complex Real BigOperators Finset Set Filter Topology Metric

open scoped Topology

theorem zero_free_polynomial_growth_is_exp_poly {H : ℂ → ℂ} {n : ℕ}
    (hH : Differentiable ℂ H)
    (h_nonzero : ∀ z, H z ≠ 0)
    (h_bound : ∃ C > 0, ∀ z, ‖H z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ n)) :
    ∃ P : Polynomial ℂ, P.natDegree ≤ n ∧ ∀ z, H z = Complex.exp (Polynomial.eval z P) := by
  classical
  rcases h_bound with ⟨C, hCpos, hC⟩
  let L : ℂ → ℂ := fun z => deriv H z / H z
  have hderivH : Differentiable ℂ (deriv H) := by
    intro z
    exact ((hH.analyticAt z).deriv).differentiableAt
  have hL : Differentiable ℂ L := by
    simpa [L] using! (hderivH.div hH h_nonzero)
  let h : ℂ → ℂ := fun z => Complex.wedgeIntegral (0 : ℂ) z L
  have hh_deriv : ∀ z, HasDerivAt h (L z) z := by
    intro z
    let r : ℝ := ‖z‖ + 1
    have hrpos : 0 < r := by
      dsimp [r]; linarith [norm_nonneg z]
    have hz_ball : z ∈ Metric.ball (0 : ℂ) r := by
      have : dist z (0 : ℂ) < r := by simp [r, dist_zero_right]
      simpa [Metric.mem_ball] using this
    have hconserv : Complex.IsConservativeOn L (Metric.ball (0 : ℂ) r) :=
      (hL.differentiableOn).isConservativeOn
    have hcont : ContinuousOn L (Metric.ball (0 : ℂ) r) :=
      hL.continuous.continuousOn
    simpa [h, r] using hconserv.hasDerivAt_wedgeIntegral (f_cont := hcont) (hz := hz_ball)
  have hh : Differentiable ℂ h := fun z => (hh_deriv z).differentiableAt
  have hderiv_h : ∀ z, deriv h z = L z := fun z => (hh_deriv z).deriv
  let k : ℂ → ℂ := fun z => h z + Complex.log (H 0)
  have hk : Differentiable ℂ k := hh.add_const (Complex.log (H 0))
  have hk_exp : ∀ z, H z = Complex.exp (k z) := by
    let F : ℂ → ℂ := fun z => Complex.exp (k z) / H z
    have hF_deriv : ∀ z, deriv F z = 0 := by
      intro z
      have hH_has : HasDerivAt H (deriv H z) z := (hH z).hasDerivAt
      have hk_has : HasDerivAt k (L z) z := by
        have hh_has : HasDerivAt h (L z) z := hh_deriv z
        simpa [k, L] using hh_has.add_const (Complex.log (H 0))
      have hExp : HasDerivAt (fun w => Complex.exp (k w)) (Complex.exp (k z) * L z) z :=
        (HasDerivAt.cexp hk_has)
      have hDiv := (HasDerivAt.div hExp hH_has (h_nonzero z))
      have :
          deriv F z =
            ((Complex.exp (k z) * L z) * H z - Complex.exp (k z) * deriv H z) / (H z) ^ 2 := by
        simpa [F] using! hDiv.deriv
      rw [this]
      have hnum :
          (Complex.exp (k z) * L z) * H z - Complex.exp (k z) * deriv H z = 0 := by
        dsimp [L]
        field_simp [h_nonzero z]
        ring
      simp [hnum]
    have hF_diff : Differentiable ℂ F := (hk.cexp).div hH h_nonzero
    have hF_const : ∀ z, F z = F 0 := by
      intro z
      exact is_const_of_deriv_eq_zero hF_diff hF_deriv z 0
    have hF0 : F 0 = 1 := by
      have hh0 : h 0 = 0 := by simp [h, Complex.wedgeIntegral]
      have hk0 : k 0 = Complex.log (H 0) := by simp [k, hh0]
      have hH0 : H 0 ≠ 0 := h_nonzero 0
      simp [F, hk0, Complex.exp_log hH0, hH0]
    intro z
    have : F z = 1 := by simpa [hF0] using (hF_const z)
    have hHz : H z ≠ 0 := h_nonzero z
    have : Complex.exp (k z) / H z = 1 := by simpa [F] using this
    have : Complex.exp (k z) = H z := by
      field_simp [hHz] at this
      simpa using this
    exact this.symm
  have hk_re_bound : ∀ z, (k z).re ≤ C * (1 + ‖z‖) ^ n := by
    intro z
    have hHz : H z ≠ 0 := h_nonzero z
    have hpos : 0 < ‖H z‖ := norm_pos_iff.mpr hHz
    have hlog_le : Real.log ‖H z‖ ≤ C * (1 + ‖z‖) ^ n := by
      have := Real.log_le_log hpos (hC z)
      simpa [Real.log_exp] using this
    have hlog_eq : Real.log ‖H z‖ = (k z).re := by
      have : ‖H z‖ = Real.exp (k z).re := by
        simpa [hk_exp z] using (Complex.norm_exp (k z))
      calc
        Real.log ‖H z‖ = Real.log (Real.exp (k z).re) := by simp [this]
        _ = (k z).re := by simp
    simpa [hlog_eq] using hlog_le
  have hk_iteratedDeriv_eq_zero : ∀ m : ℕ, n < m → iteratedDeriv m k 0 = 0 := by
    intro m hm
    have hm' : 0 < (m - n : ℕ) := Nat.sub_pos_of_lt hm
    have hmne : m - n ≠ 0 := (Nat.pos_iff_ne_zero.1 hm')
    let f : ℂ → ℂ := fun z => k z - k 0
    have hf : Differentiable ℂ f := hk.sub_const (k 0)
    have hf0 : f 0 = 0 := by simp [f]
    have hf_re_bound : ∀ R : ℝ, 0 < R →
        ∀ z, ‖z‖ ≤ R → (f z).re ≤ C * (1 + R) ^ n + ‖k 0‖ := by
      intro R hRpos z hzR
      have hkz : (k z).re ≤ C * (1 + ‖z‖) ^ n := hk_re_bound z
      have hkz' : (k z).re ≤ C * (1 + R) ^ n := by
        have h1 : (1 + ‖z‖ : ℝ) ≤ 1 + R := by linarith
        have hpow : (1 + ‖z‖ : ℝ) ^ n ≤ (1 + R) ^ n :=
          pow_le_pow_left₀ (by linarith [norm_nonneg z]) h1 n
        exact hkz.trans (mul_le_mul_of_nonneg_left hpow (le_of_lt hCpos))
      have hRe0 : -(k 0).re ≤ ‖k 0‖ := by
        have habs : |(k 0).re| ≤ ‖k 0‖ := Complex.abs_re_le_norm (k 0)
        have hneg : -(k 0).re ≤ |(k 0).re| := by simpa using (neg_le_abs (k 0).re)
        exact hneg.trans habs
      have : (f z).re ≤ C * (1 + R) ^ n + ‖k 0‖ := by
        have : (f z).re = (k z).re - (k 0).re := by simp [f, sub_eq_add_neg]
        nlinarith [this, hkz', hRe0]
      exact this
    have hf_bound_on_ball : ∀ R : ℝ, 0 < R →
        ∀ z, ‖z‖ ≤ R / 2 → ‖f z‖ ≤ 2 * (C * (1 + R) ^ n + ‖k 0‖ + 1) := by
      intro R hRpos z hz
      have hR2pos : 0 < R / 2 := by nlinarith
      have hlt : R / 2 < R := by nlinarith
      have hMpos : 0 < (C * (1 + R) ^ n + ‖k 0‖ + 1) := by
        have : 0 ≤ C * (1 + R) ^ n := by
          refine mul_nonneg (le_of_lt hCpos) ?_
          exact pow_nonneg (by linarith) _
        nlinarith [this, norm_nonneg (k 0)]
      have hf_anal : AnalyticOnNhd ℂ f (Metric.closedBall 0 R) := by
        intro w _hw
        exact (hf.analyticAt w)
      have hf_re : ∀ w, ‖w‖ ≤ R → (f w).re ≤ (C * (1 + R) ^ n + ‖k 0‖ + 1) := by
        intro w hw
        have := hf_re_bound R hRpos w hw
        linarith
      have hf_bc :=
        borelCaratheodory_zero_closedBall (f := f) (r := R / 2) (R := R)
          (M := (C * (1 + R) ^ n + ‖k 0‖ + 1))
          hf_anal hR2pos hlt hMpos hf0 hf_re (z := z) hz
      have hconst :
          2 * (C * (1 + R) ^ n + ‖k 0‖ + 1) * (R / 2) / (R - R / 2)
            = 2 * (C * (1 + R) ^ n + ‖k 0‖ + 1) := by
        field_simp [hRpos.ne'] ; ring
      simpa [hconst] using hf_bc
    have hCauchy : ∀ R : ℝ, 0 < R →
        ‖iteratedDeriv m f 0‖ ≤
          (m.factorial : ℝ) * (2 * (C * (1 + R) ^ n + ‖k 0‖ + 1)) / (R / 2) ^ m := by
      intro R hRpos
      have hR2pos : 0 < R / 2 := by nlinarith
      have hf_diffCont : DiffContOnCl ℂ f (Metric.ball (0 : ℂ) (R / 2)) := hf.diffContOnCl
      have hbound_sphere :
          ∀ z ∈ Metric.sphere (0 : ℂ) (R / 2),
            ‖f z‖ ≤ 2 * (C * (1 + R) ^ n + ‖k 0‖ + 1) := by
        intro z hz
        have hz' : ‖z‖ ≤ R / 2 := by
          simpa [Metric.mem_sphere, dist_zero_right] using (le_of_eq hz)
        exact hf_bound_on_ball R hRpos z hz'
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
        (Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (n := m) (c := (0 : ℂ))
          (R := R / 2) (C := 2 * (C * (1 + R) ^ n + ‖k 0‖ + 1))
          (hR := hR2pos) hf_diffCont hbound_sphere)
    have hf_iter_eq : iteratedDeriv m f 0 = 0 := by
      by_contra hne
      have ha : 0 < ‖iteratedDeriv m f 0‖ := norm_pos_iff.2 hne
      let RHS : ℝ → ℝ := fun R =>
        (m.factorial : ℝ) * (2 * (C * (1 + R) ^ n + ‖k 0‖ + 1)) / (R / 2) ^ m
      have hle_RHS : ∀ R : ℝ, 0 < R → ‖iteratedDeriv m f 0‖ ≤ RHS R := by
        intro R hRpos
        simpa [RHS] using hCauchy R hRpos
      have hRHS_tendsto : Tendsto RHS atTop (𝓝 0) := by
        let K : ℝ := ‖k 0‖ + 1
        have hmpos : 0 < m := lt_of_le_of_lt (Nat.zero_le n) hm
        have hm0 : m ≠ 0 := ne_of_gt hmpos
        have hratio : Tendsto (fun R : ℝ => R ^ n / (R / 2) ^ m) atTop (𝓝 0) := by
          have hident :
              (fun R : ℝ => R ^ n / (R / 2) ^ m) = fun R : ℝ => (2 : ℝ) ^ m * (R ^ n / R ^ m) := by
            funext R
            simp [div_eq_mul_inv, mul_pow, mul_assoc, mul_comm]
          have hmain : Tendsto (fun R : ℝ => R ^ n / R ^ m) atTop (𝓝 0) := by
            have hp : m - n ≠ 0 := (Nat.pos_iff_ne_zero.1 (Nat.sub_pos_of_lt hm))
            have hmain' : Tendsto (fun R : ℝ => (R ^ (m - n))⁻¹) atTop (𝓝 0) := by
              simpa using (tendsto_pow_neg_atTop (𝕜 := ℝ) (n := m - n) hp)
            have hEq : (fun R : ℝ => (R ^ (m - n))⁻¹) =ᶠ[atTop] fun R : ℝ => R ^ n / R ^ m := by
              have hEq' : (fun R : ℝ => R ^ n / R ^ m) =ᶠ[atTop] fun R : ℝ => (R ^ (m - n))⁻¹ := by
                filter_upwards [eventually_ne_atTop (0 : ℝ)] with R hR
                have hle : n ≤ m := le_of_lt hm
                have hm_eq : n + (m - n) = m := Nat.add_sub_of_le hle
                have hn0 : R ^ n ≠ 0 := pow_ne_zero n hR
                calc
                  R ^ n / R ^ m = R ^ n / R ^ (n + (m - n)) := by simp [hm_eq]
                  _ = R ^ n * ((R ^ (m - n))⁻¹ * (R ^ n)⁻¹) := by
                        simp [pow_add, div_eq_mul_inv, mul_comm]
                  _ = (R ^ (m - n))⁻¹ := by
                        ring_nf
                        simp [hn0]
              exact hEq'.symm
            exact Filter.Tendsto.congr' hEq hmain'
          have : Tendsto (fun R : ℝ => (2 : ℝ) ^ m * (R ^ n / R ^ m)) atTop (𝓝 ((2 : ℝ) ^ m * 0)) :=
            tendsto_const_nhds.mul hmain
          simpa [hident] using this
        have hinv : Tendsto (fun R : ℝ => ((R / 2) ^ m)⁻¹) atTop (𝓝 0) := by
          have hdiv : Tendsto (fun R : ℝ => R / 2) atTop atTop :=
            (tendsto_id.atTop_div_const (r := (2 : ℝ)) (by norm_num : (0 : ℝ) < 2))
          have hpow : Tendsto (fun R : ℝ => (R / 2) ^ m) atTop atTop :=
            (Filter.tendsto_pow_atTop (α := ℝ) (n := m) hm0).comp hdiv
          simpa using! hpow.inv_tendsto_atTop
        have hdiv : Tendsto (fun R : ℝ => (1 + R) / R) atTop (𝓝 (1 : ℝ)) := by
          have hinv' : Tendsto (fun R : ℝ => (R : ℝ)⁻¹) atTop (𝓝 (0 : ℝ)) := tendsto_inv_atTop_zero
          have hadd : Tendsto (fun R : ℝ => (1 : ℝ) + (R : ℝ)⁻¹) atTop (𝓝 (1 : ℝ)) := by
            simpa using (tendsto_const_nhds.add hinv')
          have hEq : (fun R : ℝ => (1 + R) / R) =ᶠ[atTop] fun R : ℝ => (1 : ℝ) + (R : ℝ)⁻¹ := by
            filter_upwards [eventually_ne_atTop (0 : ℝ)] with R hR
            field_simp [hR]; ring
          exact Filter.Tendsto.congr' hEq.symm hadd
        have hdiv_pow : Tendsto (fun R : ℝ => ((1 + R) / R) ^ n) atTop (𝓝 (1 : ℝ)) := by
          simpa using (hdiv.pow n)
        have hone_add_ratio :
            Tendsto (fun R : ℝ => (1 + R) ^ n / (R / 2) ^ m) atTop (𝓝 (0 : ℝ)) := by
          have hEq :
              (fun R : ℝ => (1 + R) ^ n / (R / 2) ^ m)
                =ᶠ[atTop] fun R : ℝ => ((1 + R) / R) ^ n * (R ^ n / (R / 2) ^ m) := by
            filter_upwards [eventually_ne_atTop (0 : ℝ)] with R hR
            have hRpow : (R ^ n : ℝ) ≠ 0 := pow_ne_zero n hR
            have hident :
                ((1 + R) / R) ^ n * (R ^ n / (R / 2) ^ m) = (1 + R) ^ n / (R / 2) ^ m := by
              calc
                ((1 + R) / R) ^ n * (R ^ n / (R / 2) ^ m)
                    = ((1 + R) ^ n / R ^ n) * (R ^ n / (R / 2) ^ m) := by
                        simp [div_pow]
                _ = ((1 + R) ^ n * R ^ n) / (R ^ n * (R / 2) ^ m) := by
                        simp [div_mul_div_comm, mul_comm]
                _ = ((1 + R) ^ n * R ^ n) / ((R / 2) ^ m * R ^ n) := by
                        simp [mul_comm]
                _ = (1 + R) ^ n / (R / 2) ^ m := by
                        simpa [mul_assoc, mul_comm, mul_left_comm] using
                          (mul_div_mul_right (a := (1 + R) ^ n) (b := (R / 2) ^ m) hRpow)
            exact hident.symm
          have hmul :
              Tendsto
                (fun R : ℝ => ((1 + R) / R) ^ n * (R ^ n / (R / 2) ^ m))
                atTop (𝓝 (0 : ℝ)) := by
            simpa [mul_zero] using (hdiv_pow.mul hratio)
          exact Filter.Tendsto.congr' hEq.symm hmul
        have h1 : Tendsto (fun R : ℝ => C * ((1 + R) ^ n / (R / 2) ^ m)) atTop (𝓝 0) := by
          simpa using (tendsto_const_nhds.mul hone_add_ratio)
        have h2 : Tendsto (fun R : ℝ => K * ((R / 2) ^ m)⁻¹) atTop (𝓝 0) := by
          simpa using (tendsto_const_nhds.mul hinv)
        have hsum :
            Tendsto
              (fun R : ℝ => C * ((1 + R) ^ n / (R / 2) ^ m) + K * ((R / 2) ^ m)⁻¹)
              atTop (𝓝 0) := by
          simpa using (h1.add h2)
        have hrew :
            (fun R : ℝ => (C * (1 + R) ^ n + K) / (R / 2) ^ m)
              = fun R : ℝ => C * ((1 + R) ^ n / (R / 2) ^ m) + K * ((R / 2) ^ m)⁻¹ := by
          funext R
          simp [div_eq_mul_inv, mul_add, mul_assoc, mul_comm]
        have hbase : Tendsto (fun R : ℝ => (C * (1 + R) ^ n + K) / (R / 2) ^ m) atTop (𝓝 0) := by
          simpa [hrew] using hsum
        have hconst :
            Tendsto (fun _ : ℝ => (m.factorial : ℝ) * (2 : ℝ)) atTop
              (𝓝 ((m.factorial : ℝ) * (2 : ℝ))) := tendsto_const_nhds
        have hmul : Tendsto (fun R : ℝ => ((m.factorial : ℝ) * (2 : ℝ)) *
              ((C * (1 + R) ^ n + K) / (R / 2) ^ m)) atTop (𝓝 0) := by
          simpa [mul_assoc, mul_left_comm, mul_comm] using (hconst.mul hbase)
        have hRHS_rw : RHS = fun R : ℝ => ((m.factorial : ℝ) * (2 : ℝ)) *
              ((C * (1 + R) ^ n + K) / (R / 2) ^ m) := by
          funext R
          dsimp [RHS, K]
          ring_nf
        simpa [hRHS_rw] using hmul
      have hsmall : ∀ᶠ R in atTop, RHS R < ‖iteratedDeriv m f 0‖ / 2 :=
        (tendsto_order.1 hRHS_tendsto).2 _ (half_pos ha)
      have hle_eventually : ∀ᶠ R in atTop, ‖iteratedDeriv m f 0‖ ≤ RHS R := by
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hRpos
        exact hle_RHS R hRpos
      rcases (hle_eventually.and hsmall).exists with ⟨R, hle, hlt⟩
      have : ‖iteratedDeriv m f 0‖ < ‖iteratedDeriv m f 0‖ :=
        (lt_of_le_of_lt hle hlt).trans (half_lt_self ha)
      exact lt_irrefl _ this
    have hmpos : 0 < m := lt_of_le_of_lt (Nat.zero_le n) hm
    have hm0 : m ≠ 0 := ne_of_gt hmpos
    have hkcd : ContDiffAt ℂ (↑m) k (0 : ℂ) := (hk.analyticAt 0).contDiffAt
    have hccd : ContDiffAt ℂ (↑m) (fun _ : ℂ => k 0) (0 : ℂ) := contDiffAt_const
    have hsub :
        iteratedDeriv m f 0 =
          iteratedDeriv m k 0 - iteratedDeriv m (fun _ : ℂ => k 0) 0 := by
      simpa [f] using! (iteratedDeriv_sub (n := m) (x := (0 : ℂ)) hkcd hccd)
    have hconst0 : iteratedDeriv m (fun _ : ℂ => k 0) 0 = 0 := by
      simp [iteratedDeriv_const, hm0]
    have hf_eq : iteratedDeriv m f 0 = iteratedDeriv m k 0 := by
      simp [hsub, hconst0]
    simpa [hf_eq] using hf_iter_eq
  let P : Polynomial ℂ :=
    ∑ m ∈ Finset.range (n + 1), Polynomial.monomial m ((m.factorial : ℂ)⁻¹ * iteratedDeriv m k 0)
  have hPdeg : P.natDegree ≤ n := by
    have hnat :
        P.natDegree ≤
          Finset.fold max 0
            (fun m : ℕ =>
              (Polynomial.monomial m ((m.factorial : ℂ)⁻¹ * iteratedDeriv m k 0)).natDegree)
            (Finset.range (n + 1)) := by
      simpa [P, Function.comp] using
        (Polynomial.natDegree_sum_le (s := Finset.range (n + 1))
          (f := fun m : ℕ =>
            Polynomial.monomial m ((m.factorial : ℂ)⁻¹ * iteratedDeriv m k 0)))
    have hfold :
        Finset.fold max 0
            (fun m : ℕ =>
              (Polynomial.monomial m ((m.factorial : ℂ)⁻¹ * iteratedDeriv m k 0)).natDegree)
            (Finset.range (n + 1)) ≤ n := by
      refine (Finset.fold_max_le (f := fun m : ℕ =>
        (Polynomial.monomial m ((m.factorial : ℂ)⁻¹ * iteratedDeriv m k 0)).natDegree)
        (b := 0) (s := Finset.range (n + 1)) (c := n)).2 ?_
      refine ⟨Nat.zero_le n, ?_⟩
      intro m hm
      have hmon :
          (Polynomial.monomial m ((m.factorial : ℂ)⁻¹ * iteratedDeriv m k 0)).natDegree ≤ m :=
        Polynomial.natDegree_monomial_le _
      have hm_le : m ≤ n := Nat.le_of_lt_succ (Finset.mem_range.1 hm)
      exact hmon.trans hm_le
    exact hnat.trans hfold
  have hk_poly : ∀ z, k z = Polynomial.eval z P := by
    intro z
    have htaylor := Complex.taylorSeries_eq_of_entire' (c := (0 : ℂ)) (z := z) hk
    have htail : ∀ m : ℕ, m ∉ Finset.range (n + 1) →
        ((m.factorial : ℂ)⁻¹ * iteratedDeriv m k 0 * (z - 0) ^ m) = 0 := by
      intro m hm'
      have hmgt : n < m := by
        have : n + 1 ≤ m := Nat.le_of_not_lt (by simpa [Finset.mem_range] using hm')
        exact Nat.lt_of_lt_of_le (Nat.lt_succ_self n) this
      have hz : iteratedDeriv m k 0 = 0 := hk_iteratedDeriv_eq_zero m hmgt
      simp [hz]
    have htsum :
        (∑' m : ℕ, (m.factorial : ℂ)⁻¹ * iteratedDeriv m k 0 * (z - 0) ^ m)
          = ∑ m ∈ Finset.range (n + 1), (m.factorial : ℂ)⁻¹ * iteratedDeriv m k 0 * z ^ m := by
      simpa [sub_zero] using (tsum_eq_sum (s := Finset.range (n + 1)) htail)
    have hfinite :
        k z = ∑ m ∈ Finset.range (n + 1), (m.factorial : ℂ)⁻¹ * iteratedDeriv m k 0 * z ^ m := by
      calc
        k z = ∑' m : ℕ, (m.factorial : ℂ)⁻¹ * iteratedDeriv m k 0 * (z - 0) ^ m := by
          simpa using htaylor.symm
        _ = _ := htsum
    have hEval :
        Polynomial.eval z P =
          ∑ m ∈ Finset.range (n + 1), z ^ m * ((m.factorial : ℂ)⁻¹ * iteratedDeriv m k 0) := by
      classical
      change Polynomial.eval₂ (RingHom.id ℂ) z P = _
      let φ : Polynomial ℂ →+* ℂ := Polynomial.eval₂RingHom (RingHom.id ℂ) z
      change φ P = _
      simp [P, φ, Polynomial.eval₂_monomial, mul_comm]
    have hfinite' :
        k z = ∑ m ∈ Finset.range (n + 1), z ^ m * ((m.factorial : ℂ)⁻¹ * iteratedDeriv m k 0) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hfinite
    simpa [hEval] using hfinite'
  refine ⟨P, hPdeg, ?_⟩
  intro z
  have : H z = Complex.exp (k z) := by simp [hk_exp z]
  simp [this, hk_poly z]

end Hadamard
end Complex
end
end
end File36

-- Upstream module PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.ExpPoly.Growth
section File37
 

section
noncomputable section

namespace Complex
namespace Hadamard

open Complex Real BigOperators Finset Set Filter Topology Metric

open scoped Topology

open Polynomial

private lemma exists_pow_eq_complex {n : ℕ} (hn : 0 < n) (w : ℂ) : ∃ z : ℂ, z ^ n = w := by
  classical
  by_cases hw : w = 0
  · subst hw
    refine ⟨0, ?_⟩
    have hn0 : n ≠ 0 := Nat.ne_of_gt hn
    simp [hn0]
  · refine ⟨Complex.exp (Complex.log w / n), ?_⟩
    have hn0 : (n : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hn)
    calc
      (Complex.exp (Complex.log w / n)) ^ n
          = Complex.exp ((n : ℂ) * (Complex.log w / n)) := by
              simpa using (Complex.exp_nat_mul (Complex.log w / n) n).symm
      _ = Complex.exp (Complex.log w) := by
            have : (n : ℂ) * (Complex.log w / n) = Complex.log w := by
              field_simp [hn0]
            simp [this]
      _ = w := by simpa using (Complex.exp_log hw)

private lemma mul_conj_div_norm (a : ℂ) (ha : a ≠ 0) :
    a * ((starRingEnd ℂ) a / (‖a‖ : ℂ)) = (‖a‖ : ℂ) := by
  have hnorm_pos : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hnorm_ne : (‖a‖ : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hnorm_pos)
  have hmul : a * (starRingEnd ℂ) a = (Complex.normSq a : ℂ) :=
    Complex.mul_conj a
  have hcast : (Complex.normSq a : ℂ) = ((‖a‖ ^ 2 : ℝ) : ℂ) := by
    exact_mod_cast (Complex.normSq_eq_norm_sq a)
  have hdiv : ((‖a‖ ^ 2 : ℝ) : ℂ) / (‖a‖ : ℂ) = (‖a‖ : ℂ) := by
    have : ((‖a‖ ^ 2 : ℝ) : ℂ) = (‖a‖ : ℂ) * (‖a‖ : ℂ) := by
      simp [pow_two]
    calc
      ((‖a‖ ^ 2 : ℝ) : ℂ) / (‖a‖ : ℂ)
          = ((‖a‖ : ℂ) * (‖a‖ : ℂ)) / (‖a‖ : ℂ) := by simp [this]
      _ = (‖a‖ : ℂ) := by
            field_simp [hnorm_ne]
  calc
    a * ((starRingEnd ℂ) a / (‖a‖ : ℂ))
        = (a * (starRingEnd ℂ) a) / (‖a‖ : ℂ) := by
            simp [div_eq_mul_inv, mul_assoc]
    _ = (Complex.normSq a : ℂ) / (‖a‖ : ℂ) := by simp [hmul]
    _ = ((‖a‖ ^ 2 : ℝ) : ℂ) / (‖a‖ : ℂ) := by simp [hcast]
    _ = (‖a‖ : ℂ) := hdiv

private lemma exists_z_norm_eq_re_eval_ge
    (P : Polynomial ℂ) (hn : 0 < P.natDegree) :
    ∃ R0 : ℝ, 0 < R0 ∧
      ∀ R : ℝ, R0 ≤ R →
        ∃ z : ℂ, ‖z‖ = R ∧
          (‖P.leadingCoeff‖ / 2) * R ^ P.natDegree ≤ (P.eval z).re := by
  classical
  set n : ℕ := P.natDegree
  have hn0 : 0 < n := hn
  have hP0 : P ≠ 0 := by
    intro h0
    simp [n, h0] at hn0
  have hLC : P.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hP0
  set a : ℂ := P.leadingCoeff
  have ha : a ≠ 0 := hLC
  have hnorm_a_pos : 0 < ‖a‖ := norm_pos_iff.mpr ha
  set wtarget : ℂ := (starRingEnd ℂ) a / (‖a‖ : ℂ)
  have hwtarget_norm : ‖wtarget‖ = (1 : ℝ) := by
    calc
      ‖wtarget‖ = ‖(starRingEnd ℂ) a‖ / ‖(‖a‖ : ℂ)‖ := by
        simp [wtarget]
      _ = ‖a‖ / ‖a‖ := by simp
      _ = (1 : ℝ) := by
        field_simp [hnorm_a_pos.ne']
  rcases exists_pow_eq_complex (n := n) hn0 (w := wtarget) with ⟨w, hw⟩
  have hw_norm : ‖w‖ = (1 : ℝ) := by
    have hpow : (‖w‖ : ℝ) ^ n = 1 := by
      have := congrArg (fun z : ℂ => ‖z‖) hw
      simpa [norm_pow, hwtarget_norm] using this
    have hn0' : n ≠ 0 := Nat.ne_of_gt hn0
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg w) hn0').1 hpow
  set S : ℝ := ∑ i ∈ Finset.range n, ‖P.coeff i‖
  set R0 : ℝ := max 1 (2 * S / ‖a‖)
  refine ⟨R0, ?_, ?_⟩
  · have : (0 : ℝ) < (1 : ℝ) := by norm_num
    exact lt_of_lt_of_le this (le_max_left _ _)
  · intro R hR
    have hR_ge1 : (1 : ℝ) ≤ R := by
      exact le_trans (le_max_left _ _) hR
    have hR_nonneg : 0 ≤ R := le_trans (by norm_num) hR_ge1
    set z : ℂ := (R : ℂ) * w
    have hz_norm : ‖z‖ = R := by
      have : ‖z‖ = |R| * ‖w‖ := by
        simp [z]
      simp [this, hw_norm, abs_of_nonneg hR_nonneg]
    have h_eval : P.eval z =
        (∑ i ∈ Finset.range n, P.coeff i * z ^ i) + P.coeff n * z ^ n := by
      have hsum : P.eval z = ∑ i ∈ Finset.range (n + 1), P.coeff i * z ^ i := by
        have : P.natDegree + 1 = n + 1 := by simp [n]
        simpa [this] using (Polynomial.eval_eq_sum_range (p := P) z)
      have hsplit :
          (∑ i ∈ Finset.range (n + 1), P.coeff i * z ^ i)
            = (∑ i ∈ Finset.range n, P.coeff i * z ^ i) + P.coeff n * z ^ n := by
        simpa using (Finset.sum_range_succ (f := fun i => P.coeff i * z ^ i) n)
      exact hsum.trans hsplit
    have h_lower_norm :
        ‖∑ i ∈ Finset.range n, P.coeff i * z ^ i‖ ≤ S * R ^ (n - 1) := by
      have h1 :
          ‖∑ i ∈ Finset.range n, P.coeff i * z ^ i‖
            ≤ ∑ i ∈ Finset.range n, ‖P.coeff i * z ^ i‖ := by
        simpa using (norm_sum_le (Finset.range n) (fun i => P.coeff i * z ^ i))
      have hterm : ∀ i ∈ Finset.range n, ‖P.coeff i * z ^ i‖ ≤ ‖P.coeff i‖ * R ^ (n - 1) := by
        intro i hi
        have hi_lt : i < n := Finset.mem_range.mp hi
        have hi_le : i ≤ n - 1 := Nat.le_pred_of_lt hi_lt
        have hzpow : ‖z‖ ^ i ≤ R ^ (n - 1) := by
          have hmono : ‖z‖ ^ i ≤ ‖z‖ ^ (n - 1) :=
            pow_le_pow_right₀ (by simpa [hz_norm] using hR_ge1) hi_le
          simpa [hz_norm] using hmono
        calc
          ‖P.coeff i * z ^ i‖ = ‖P.coeff i‖ * ‖z‖ ^ i := by
            simp [norm_pow]
          _ ≤ ‖P.coeff i‖ * R ^ (n - 1) := by
            exact mul_le_mul_of_nonneg_left hzpow (norm_nonneg _)
      have h2 :
          ∑ i ∈ Finset.range n, ‖P.coeff i * z ^ i‖
            ≤ ∑ i ∈ Finset.range n, ‖P.coeff i‖ * R ^ (n - 1) := by
        exact Finset.sum_le_sum (fun i hi => hterm i hi)
      have h3 :
          (∑ i ∈ Finset.range n, ‖P.coeff i‖ * R ^ (n - 1))
            = (∑ i ∈ Finset.range n, ‖P.coeff i‖) * R ^ (n - 1) := by
        simp [Finset.sum_mul]
      have hsum_le : (∑ i ∈ Finset.range n, ‖P.coeff i‖) ≤ S := by
        simp [S]
      calc
        ‖∑ i ∈ Finset.range n, P.coeff i * z ^ i‖
            ≤ ∑ i ∈ Finset.range n, ‖P.coeff i * z ^ i‖ := h1
        _ ≤ ∑ i ∈ Finset.range n, ‖P.coeff i‖ * R ^ (n - 1) := h2
        _ = (∑ i ∈ Finset.range n, ‖P.coeff i‖) * R ^ (n - 1) := h3
        _ ≤ S * R ^ (n - 1) := by
              exact mul_le_mul_of_nonneg_right hsum_le (pow_nonneg hR_nonneg _)
    have h_lead_re : (P.coeff n * z ^ n).re = ‖a‖ * R ^ n := by
      have hw_pow : w ^ n = wtarget := hw
      have ha_mul : a * w ^ n = (‖a‖ : ℂ) := by
        have : a * w ^ n = a * wtarget := by simp [hw_pow]
        simpa [wtarget, a] using (this.trans (mul_conj_div_norm a ha))
      have hz_pow : z ^ n = ((R : ℂ) ^ n) * (w ^ n) := by
        simp [z, mul_pow, mul_comm]
      have hcoeffn : P.coeff n = a := by simp [a, n, Polynomial.coeff_natDegree]
      have hreR : ∀ m : ℕ, (((R : ℂ) ^ m).re) = R ^ m := by
        intro m
        induction m with
        | zero => simp
        | succ m ih =>
            simp [pow_succ, ih, mul_re]
      calc
        (P.coeff n * z ^ n).re
            = (a * z ^ n).re := by simp [hcoeffn]
        _ = (a * (((R : ℂ) ^ n) * (w ^ n))).re := by simp [hz_pow]
        _ = (((R : ℂ) ^ n) * (a * (w ^ n))).re := by
              ring_nf
        _ = (((R : ℂ) ^ n) * (‖a‖ : ℂ)).re := by simp [ha_mul]
        _ = (((R : ℂ) ^ n).re) * ‖a‖ := by
              simp [mul_re]
        _ = (R ^ n) * ‖a‖ := by simp [hreR n]
        _ = ‖a‖ * R ^ n := by ring
    refine ⟨z, hz_norm, ?_⟩
    have hre_lower : (∑ i ∈ Finset.range n, P.coeff i * z ^ i).re
        ≥ -‖∑ i ∈ Finset.range n, P.coeff i * z ^ i‖ := by
      have habs : |(∑ i ∈ Finset.range n, P.coeff i * z ^ i).re|
          ≤ ‖∑ i ∈ Finset.range n, P.coeff i * z ^ i‖ :=
        Complex.abs_re_le_norm _
      have := neg_le_of_abs_le habs
      simpa using this
    have hre_main :
        (P.eval z).re ≥ (P.coeff n * z ^ n).re - ‖∑ i ∈ Finset.range n, P.coeff i * z ^ i‖ := by
      have : (P.eval z).re =
          (∑ i ∈ Finset.range n, P.coeff i * z ^ i).re + (P.coeff n * z ^ n).re := by
        simp [h_eval, add_comm]
      linarith [this, hre_lower]
    have hR_ge_R0 : R0 ≤ R := hR
    have hR_ge : 2 * S / ‖a‖ ≤ R := le_trans (le_max_right _ _) hR_ge_R0
    have hRpos : 0 < R := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hR_ge1
    have hR_nonneg' : 0 ≤ R := le_of_lt hRpos
    have hn_ge1 : 1 ≤ n := Nat.succ_le_of_lt hn0
    have hlower_le : S * R ^ (n - 1) ≤ (‖a‖ / 2) * R ^ n := by
      have ha_pos : 0 < ‖a‖ := hnorm_a_pos
      have hS_le : S ≤ (‖a‖ / 2) * R := by
        have : 2 * S ≤ ‖a‖ * R := by
          have := (mul_le_mul_of_nonneg_left hR_ge (by linarith [ha_pos.le] : (0 : ℝ) ≤ ‖a‖))
          have hne : (‖a‖ : ℝ) ≠ 0 := ne_of_gt ha_pos
          simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, hne] using this
        have : S ≤ (‖a‖ * R) / 2 := by linarith
        simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this
      have : S * R ^ (n - 1) ≤ (‖a‖ / 2) * R * R ^ (n - 1) := by
        have hpow_nonneg : 0 ≤ R ^ (n - 1) := pow_nonneg hR_nonneg' _
        exact mul_le_mul_of_nonneg_right hS_le hpow_nonneg
      have hRR : R * R ^ (n - 1) = R ^ n := by
        have : n = (n - 1) + 1 := by
          exact (Nat.sub_add_cancel hn_ge1).symm
        rw [this, pow_succ]
        ring_nf; grind
      simpa [mul_assoc, hRR] using this
    have hfinal_re :
        (‖a‖ / 2) * R ^ n ≤ (P.eval z).re := by
      have hlower' : ‖∑ i ∈ Finset.range n, P.coeff i * z ^ i‖ ≤ (‖a‖ / 2) * R ^ n := by
        exact h_lower_norm.trans hlower_le
      have hlead : (P.coeff n * z ^ n).re = ‖a‖ * R ^ n := by simpa [a] using h_lead_re
      have hre_main' :
          (‖a‖ * R ^ n) - ‖∑ i ∈ Finset.range n, P.coeff i * z ^ i‖ ≤ (P.eval z).re := by
        simpa [hlead] using hre_main
      have hsub :
          (‖a‖ * R ^ n) - (‖a‖ / 2) * R ^ n ≤
            (‖a‖ * R ^ n) - ‖∑ i ∈ Finset.range n, P.coeff i * z ^ i‖ :=
        sub_le_sub_left hlower' (‖a‖ * R ^ n)
      have hsim : (‖a‖ * R ^ n) - (‖a‖ / 2) * R ^ n = (‖a‖ / 2) * R ^ n := by ring
      have : (‖a‖ * R ^ n) - (‖a‖ / 2) * R ^ n ≤ (P.eval z).re :=
        hsub.trans hre_main'
      simpa [hsim] using this
    simpa [a, n] using hfinal_re

theorem natDegree_le_floor_of_growth_exp_eval
    {ρ : ℝ} (hρ : 0 ≤ ρ) (P : Polynomial ℂ)
    (hgrowth :
      ∃ C > 0, ∀ z : ℂ,
        Real.log (1 + ‖Complex.exp (Polynomial.eval z P)‖) ≤ C * (1 + ‖z‖) ^ ρ) :
    P.natDegree ≤ Nat.floor ρ := by
  classical
  by_cases hdeg : P.natDegree = 0
  · simp [hdeg]
  · have hnpos : 0 < P.natDegree := Nat.pos_of_ne_zero hdeg
    rcases exists_z_norm_eq_re_eval_ge (P := P) hnpos with ⟨R0, hR0pos, hray⟩
    rcases hgrowth with ⟨C, hCpos, hC⟩
    have hLCpos : 0 < ‖P.leadingCoeff‖ := by
      have hP0 : P ≠ 0 := by
        intro h0
        simp [h0] at hdeg
      have : P.leadingCoeff ≠ 0 := (Polynomial.leadingCoeff_ne_zero).2 hP0
      exact norm_pos_iff.2 this
    let c : ℝ := ‖P.leadingCoeff‖ / 2
    have hcpos : 0 < c := by
      have : (0 : ℝ) < (2 : ℝ) := by norm_num
      exact (div_pos hLCpos this)
    have hn_le_real : (P.natDegree : ℝ) ≤ ρ := by
      by_contra hnlt
      have hnlt' : ρ < (P.natDegree : ℝ) := lt_of_not_ge hnlt
      let δ : ℝ := (P.natDegree : ℝ) - ρ
      have hδ : 0 < δ := sub_pos.2 hnlt'
      let K0 : ℝ := (C * (2 : ℝ) ^ ρ) / c
      have hK0 : ∃ R1, ∀ R ≥ R1, K0 + 1 ≤ R ^ δ := by
        have h : ∀ᶠ R in (atTop : Filter ℝ), K0 + 1 ≤ R ^ δ :=
          (tendsto_atTop.mp (tendsto_rpow_atTop hδ)) (K0 + 1)
        rcases (eventually_atTop.1 h) with ⟨R1, hR1⟩
        exact ⟨R1, hR1⟩
      rcases hK0 with ⟨R1, hR1⟩
      set R : ℝ := max (max R0 1) R1
      have hR_ge_R0 : R0 ≤ R := le_trans (le_max_left _ _) (le_max_left _ _)
      have hR_ge1 : (1 : ℝ) ≤ R := le_trans (le_max_right _ _) (le_max_left _ _)
      have hR_ge_R1 : R1 ≤ R := le_max_right _ _
      have hR_pos : 0 < R := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hR_ge1
      have hRδ : K0 + 1 ≤ R ^ δ := hR1 R hR_ge_R1
      rcases hray R hR_ge_R0 with ⟨z, hz_norm, hz_re⟩
      have hlog_lower :
          (P.eval z).re ≤ Real.log (1 + ‖Complex.exp (Polynomial.eval z P)‖) := by
        have hpos : 0 < ‖Complex.exp (Polynomial.eval z P)‖ := by
          simp
        have hle :
            ‖Complex.exp (Polynomial.eval z P)‖ ≤
              1 + ‖Complex.exp (Polynomial.eval z P)‖ := by
          linarith [norm_nonneg (Complex.exp (Polynomial.eval z P))]
        have hlog_le : Real.log ‖Complex.exp (Polynomial.eval z P)‖
            ≤ Real.log (1 + ‖Complex.exp (Polynomial.eval z P)‖) :=
          Real.log_le_log hpos hle
        have hlog_eq : Real.log ‖Complex.exp (Polynomial.eval z P)‖ = (P.eval z).re := by
          simp [Complex.norm_exp]
        simpa [hlog_eq] using hlog_le
      have hlog_upper :
          Real.log (1 + ‖Complex.exp (Polynomial.eval z P)‖) ≤ C * (1 + ‖z‖) ^ ρ :=
        hC z
      have hmain : c * R ^ (P.natDegree : ℝ) ≤ C * (1 + R) ^ ρ := by
        have hz_re' : c * R ^ P.natDegree ≤ (P.eval z).re := by
          simpa [c] using hz_re
        have hz_re'' : c * R ^ (P.natDegree : ℝ) ≤ (P.eval z).re := by
          simpa [Real.rpow_natCast, c] using hz_re'
        have : c * R ^ (P.natDegree : ℝ) ≤ Real.log (1 + ‖Complex.exp (Polynomial.eval z P)‖) :=
          hz_re''.trans hlog_lower
        have : c * R ^ (P.natDegree : ℝ) ≤ C * (1 + ‖z‖) ^ ρ :=
          this.trans hlog_upper
        simpa [hz_norm] using this
      have h1R_le : (1 + R : ℝ) ≤ R * 2 := by linarith
      have hpow1 : (1 + R : ℝ) ^ ρ ≤ (R * 2) ^ ρ :=
        Real.rpow_le_rpow (by linarith [hR_pos.le]) h1R_le hρ
      have hR2 : (R * 2) ^ ρ = R ^ ρ * (2 : ℝ) ^ ρ := by
        have hRnonneg : 0 ≤ R := le_of_lt hR_pos
        have h2nonneg : 0 ≤ (2 : ℝ) := by norm_num
        simpa [mul_assoc] using (Real.mul_rpow hRnonneg h2nonneg (z := ρ))
      have hmain' : c * R ^ (P.natDegree : ℝ) ≤ C * (R ^ ρ * (2 : ℝ) ^ ρ) := by
        have := le_trans hmain (mul_le_mul_of_nonneg_left hpow1 (le_of_lt hCpos))
        simpa [hR2, mul_assoc, mul_left_comm, mul_comm] using this
      have hRρ_pos : 0 < R ^ ρ := Real.rpow_pos_of_pos hR_pos _
      have hRρ_ne : (R ^ ρ : ℝ) ≠ 0 := ne_of_gt hRρ_pos
      have hdiv :
          (c * R ^ (P.natDegree : ℝ)) / (R ^ ρ) ≤ C * (2 : ℝ) ^ ρ := by
        have h :=
            div_le_div_of_nonneg_right hmain' (le_of_lt hRρ_pos)
        have hRhs : (C * (R ^ ρ * (2 : ℝ) ^ ρ)) / (R ^ ρ) = C * (2 : ℝ) ^ ρ := by
          field_simp [hRρ_ne]
        simpa [hRhs, mul_assoc, mul_left_comm, mul_comm] using h
      have hRsub : R ^ δ = R ^ (P.natDegree : ℝ) / R ^ ρ := by
        simpa [δ] using (Real.rpow_sub hR_pos (P.natDegree : ℝ) ρ)
      have hRδ_le : c * (R ^ δ) ≤ C * (2 : ℝ) ^ ρ := by
        have hLhs : c * (R ^ δ) = (c * R ^ (P.natDegree : ℝ)) / (R ^ ρ) := by
          simp [hRsub, div_eq_mul_inv, mul_left_comm, mul_comm]
        simpa [hLhs] using hdiv
      have hRδ_le' : R ^ δ ≤ K0 := by
        have : R ^ δ ≤ (C * (2 : ℝ) ^ ρ) / c := by
          refine (le_div_iff₀ hcpos).2 ?_
          simpa [mul_assoc, mul_left_comm, mul_comm] using hRδ_le
        simpa [K0] using this
      have : K0 + 1 ≤ K0 := le_trans hRδ (le_trans hRδ_le' (le_rfl))
      exact (not_lt_of_ge this) (lt_add_of_pos_right _ (by norm_num : (0 : ℝ) < 1))
    exact (Nat.le_floor_iff hρ).2 hn_le_real

theorem natDegree_le_floor_of_exp_eval_norm_bound {τ : ℝ} (hτ : 0 ≤ τ) (P : Polynomial ℂ)
    (hbound :
      ∃ C > 0, ∀ z : ℂ,
        ‖Complex.exp (Polynomial.eval z P)‖ ≤ Real.exp (C * (1 + ‖z‖) ^ τ)) :
    P.natDegree ≤ Nat.floor τ := by
  rcases hbound with ⟨C, hCpos, hC⟩
  have hlog_growth :
      ∃ C > 0, ∀ z : ℂ,
        Real.log (1 + ‖Complex.exp (Polynomial.eval z P)‖) ≤ C * (1 + ‖z‖) ^ τ :=
    Real.log_growth_of_norm_le_exp_mul_rpow
      (f := fun z : ℂ => Complex.exp (Polynomial.eval z P))
      (r := fun z : ℂ => 1 + ‖z‖) hCpos hτ
      (fun z => by linarith [norm_nonneg z]) hC
  exact natDegree_le_floor_of_growth_exp_eval (ρ := τ) hτ P hlog_growth

end Hadamard
end Complex
end
end
end File37

-- Upstream module PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.HadamardFactorization.Growth
section File38
 

section
noncomputable section

open Set Filter Asymptotics
open scoped Topology BigOperators

namespace Complex.Hadamard

lemma no_zero_on_sphere_of_norm_image_avoid
    {f : ℂ → ℂ} (hentire : Differentiable ℂ f) (hnot : ∃ z : ℂ, f z ≠ 0)
    {B r : ℝ} (hrpos : 0 < r) (hr_le_B : r ≤ B)
    (smallSet : Set (divisorZeroIndex₀ f (Set.univ : Set ℂ))) (hsmall_fin : smallSet.Finite)
    (hsmallSet :
      smallSet = {p : divisorZeroIndex₀ f (Set.univ : Set ℂ) | ‖divisorZeroIndex₀_val p‖ ≤ B})
    (hr_not_bad :
      let small : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) := hsmall_fin.toFinset
      let a : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ := fun p => ‖divisorZeroIndex₀_val p‖
      r ∉ small.image a) :
    ∀ u : ℂ, ‖u‖ = r → f u ≠ 0 := by
  classical
  let small : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) := hsmall_fin.toFinset
  let a : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ := fun p => ‖divisorZeroIndex₀_val p‖
  let bad : Finset ℝ := small.image a
  have hr_not_bad' : r ∉ bad := by
    simpa [bad, small, a] using hr_not_bad
  have hr_not :
      ∀ p : divisorZeroIndex₀ f (Set.univ : Set ℂ),
        ‖divisorZeroIndex₀_val p‖ ≤ B → r ≠ ‖divisorZeroIndex₀_val p‖ := by
    intro p hpB hEq
    have hp_small : p ∈ small := by
      have hp_mem : p ∈ smallSet := by
        simpa [hsmallSet] using hpB
      simpa [small] using (hsmall_fin.mem_toFinset.2 hp_mem)
    have : r ∈ bad := Finset.mem_image.2 ⟨p, hp_small, by simpa [a] using hEq.symm⟩
    exact (hr_not_bad' this).elim
  exact no_zero_on_sphere_of_forall_val_norm_ne (f := f) hentire hnot
    (B := B) (r := r) hrpos hr_le_B hr_not

theorem norm_inv_hadamardDenominator_le_exp_on_cartan_circle
    {f : ℂ → ℂ} {ρ τ : ℝ} {m : ℕ}
    (hmρ : (m : ℝ) ≤ ρ) (hτ : ρ < τ) (hτ_lt : τ < (m + 1 : ℝ))
    (hτ_nonneg : 0 ≤ τ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1)))
    (hsumτ : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ τ)) :
    let Sτ : ℝ :=
      ∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), ‖divisorZeroIndex₀_val p‖⁻¹ ^ τ
    let Cprod : ℝ := cartanProductConstant m τ Sτ
    ∀ {R r : ℝ}, 0 < R → 1 ≤ R → R ≤ r → r ≤ 2 * R →
      ∀ (smallSet : Set (divisorZeroIndex₀ f (Set.univ : Set ℂ)))
        (hsmall_fin : smallSet.Finite),
        smallSet =
            {p : divisorZeroIndex₀ f (Set.univ : Set ℂ) |
              ‖divisorZeroIndex₀_val p‖ ≤ 4 * R} →
        (let small : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) := hsmall_fin.toFinset
         let a : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ :=
          fun p => ‖divisorZeroIndex₀_val p‖
         r ∉ small.image a) →
        (let small : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) := hsmall_fin.toFinset
         let a : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ :=
          fun p => ‖divisorZeroIndex₀_val p‖
         (∑ p ∈ small, (1 : ℝ) * CartanBound.φ (r / a p)) ≤
          CartanBound.Cφ * (small.card : ℝ)) →
        ∀ u : ℂ, ‖u‖ = r →
          ‖(u ^ analyticOrderNatAt f 0 *
              divisorCanonicalProduct m f (Set.univ : Set ℂ) u)⁻¹‖
            ≤ Real.exp (Cprod * (1 + r) ^ τ) := by
  classical
  intro Sτ Cprod R r hRpos hRle hR_le_r hr_le_2R smallSet hsmall_fin
    hsmallSet hr_not_bad hr_phi u hur
  let small : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) := hsmall_fin.toFinset
  let a : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ := fun p => ‖divisorZeroIndex₀_val p‖
  let bad : Finset ℝ := small.image a
  have hr_not_bad' : r ∉ bad := by
    simpa [bad, small, a] using hr_not_bad
  have hr1 : (1 : ℝ) ≤ r := le_trans hRle hR_le_r
  have hpow_inv_le1 : ‖(u ^ analyticOrderNatAt f 0)⁻¹‖ ≤ 1 :=
    Complex.norm_inv_pow_le_one_of_one_le_norm u (analyticOrderNatAt f 0) (by simpa [hur] using hr1)
  let fac : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℂ :=
    fun p => weierstrassFactor m (u / divisorZeroIndex₀_val p)
  have hloc :
      HasProdLocallyUniformlyOn
        (fun (p : divisorZeroIndex₀ f (Set.univ : Set ℂ)) (w : ℂ) =>
          weierstrassFactor m (w / divisorZeroIndex₀_val p))
        (divisorCanonicalProduct m f (Set.univ : Set ℂ))
        (Set.univ : Set ℂ) :=
    hasProdLocallyUniformlyOn_divisorCanonicalProduct_univ (m := m) (f := f) h_sum
  have hprod :
      HasProd fac (divisorCanonicalProduct m f (Set.univ : Set ℂ) u) :=
    hloc.hasProd (by simp : u ∈ (Set.univ : Set ℂ))
  let ap : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ := fun p => ‖divisorZeroIndex₀_val p‖
  have : DecidablePred (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) => p ∈ small) :=
    Classical.decPred _
  let b : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ :=
    fun p =>
      if hp : p ∈ small then
        CartanBound.φ (r / ap p) + (m : ℝ) * (1 + (r / ap p) ^ τ)
      else
        (2 : ℝ) * (r / ap p) ^ τ
  have hterm : ∀ p, ‖(fac p)⁻¹‖ ≤ Real.exp (b p) := by
    intro p
    by_cases hp : p ∈ small
    · have hval_ne : r ≠ ap p := by
        intro hEq
        have : r ∈ bad := by
          refine Finset.mem_image.2 ⟨p, hp, ?_⟩
          simp [ap, a, hEq]
        exact (hr_not_bad' this).elim
      have hval0 : divisorZeroIndex₀_val p ≠ 0 := divisorZeroIndex₀_val_ne_zero p
      have hmτ : (m : ℝ) ≤ τ := le_trans hmρ (le_of_lt hτ)
      have hnear :
          ‖(weierstrassFactor m (u / divisorZeroIndex₀_val p))⁻¹‖
            ≤ Real.exp (CartanBound.φ (r / ap p) + (m : ℝ) * (1 + (r / ap p) ^ τ)) := by
        simpa [ap] using
          (norm_inv_weierstrassFactor_le_exp_near (m := m) (τ := τ) (r := r)
              (u := u) (a := divisorZeroIndex₀_val p)
              (hur := hur) (ha := hval0) (hr := by simpa [ap] using hval_ne) hmτ)
      simpa [fac, b, hp] using hnear
    · have hlarge : (4 * R : ℝ) < ap p := by
        have : ¬ap p ≤ 4 * R := by
          intro hle
          have : p ∈ small := by
            have hp_mem : p ∈ smallSet := by
              simpa [hsmallSet, ap] using hle
            simpa [small] using (hsmall_fin.mem_toFinset.2 hp_mem)
          exact hp this
        exact lt_of_not_ge this
      have hz' : ‖u / divisorZeroIndex₀_val p‖ ≤ (1 / 2 : ℝ) :=
        norm_div_le_half_of_norm_le_of_two_mul_lt (z := u) (a := divisorZeroIndex₀_val p)
          (R := 2 * R) (by nlinarith [hRpos]) (by rw [hur]; exact hr_le_2R)
          (by nlinarith [hlarge])
      have hτ_le : τ ≤ (m + 1 : ℝ) := le_of_lt hτ_lt
      have hfar :
          ‖(weierstrassFactor m (u / divisorZeroIndex₀_val p))⁻¹‖ ≤
            Real.exp ((2 : ℝ) * (r / ap p) ^ τ) := by
        simpa [ap] using
          (norm_inv_weierstrassFactor_le_exp_far (m := m) (τ := τ) (r := r)
              (u := u) (a := divisorZeroIndex₀_val p)
              (hur := hur) (ha := divisorZeroIndex₀_val_ne_zero p) (hz := hz') hτ_le)
      simpa [fac, b, hp] using hfar
  have hb_le :
      ∀ s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)),
        (∑ p ∈ s, b p) ≤ Cprod * (1 + r) ^ τ := by
    intro s
    simpa [small, ap, b, Sτ, Cprod, a, hsmallSet] using
      (Complex.Hadamard.cartan_sum_majorant_le (f := f) (m := m) (τ := τ) (R := R) (r := r)
        (hRpos := hRpos) (hrpos := lt_of_lt_of_le hRpos hR_le_r)
        (hR_le_r := hR_le_r) (hτ_nonneg := hτ_nonneg)
        (smallSet := smallSet) (hsmall_fin := hsmall_fin) (hsmallSet := hsmallSet)
        (hsumτ := hsumτ)
        (hr_phi := by
          simpa [small, a, one_mul] using hr_phi)
        s)
  have hcprod_inv :
      ‖(divisorCanonicalProduct m f (Set.univ : Set ℂ) u)⁻¹‖ ≤
        Real.exp (Cprod * (1 + r) ^ τ) := by
    refine hasProd_norm_inv_le_exp_of_pointwise_le_exp
      (α := divisorZeroIndex₀ f (Set.univ : Set ℂ)) (fac := fac)
      (F := divisorCanonicalProduct m f (Set.univ : Set ℂ) u)
      hprod (b := b) (B := Cprod * (1 + r) ^ τ) ?_ ?_
    · exact hterm
    · intro s
      exact hb_le s
  have hmul :
      ‖(u ^ analyticOrderNatAt f 0 *
          divisorCanonicalProduct m f (Set.univ : Set ℂ) u)⁻¹‖
        =
      ‖(u ^ analyticOrderNatAt f 0)⁻¹‖ *
        ‖(divisorCanonicalProduct m f (Set.univ : Set ℂ) u)⁻¹‖ := by
    simp [mul_inv_rev, mul_comm]
  rw [hmul]
  have :
      ‖(u ^ analyticOrderNatAt f 0)⁻¹‖ *
          ‖(divisorCanonicalProduct m f (Set.univ : Set ℂ) u)⁻¹‖
        ≤ 1 * Real.exp (Cprod * (1 + r) ^ τ) :=
    mul_le_mul hpow_inv_le1 hcprod_inv (by positivity) (by positivity)
  simpa using this

theorem hadamardQuotient_norm_le_exp_on_cartan_circle
    {f H : ℂ → ℂ} {ρ τ : ℝ} {m : ℕ} {Cf : ℝ}
    (hmρ : (m : ℝ) ≤ ρ) (hτ : ρ < τ) (hτ_lt : τ < (m + 1 : ℝ))
    (hτ_nonneg : 0 ≤ τ) (hentire : Differentiable ℂ f)
    (hnot : ∃ z : ℂ, f z ≠ 0)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1)))
    (hsumτ : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ τ))
    (hf_boundτ : ∀ z : ℂ, ‖f z‖ ≤ Real.exp (Cf * (1 + ‖z‖) ^ τ))
    (hfactor : ∀ z : ℂ,
      f z =
        H z * z ^ analyticOrderNatAt f 0 *
          divisorCanonicalProduct m f (Set.univ : Set ℂ) z) :
    let Sτ : ℝ :=
      ∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), ‖divisorZeroIndex₀_val p‖⁻¹ ^ τ
    let Cprod : ℝ := cartanProductConstant m τ Sτ
    ∀ {R r : ℝ}, 0 < R → 1 ≤ R → R ≤ r → r ≤ 2 * R → 0 < r →
      ∀ (smallSet : Set (divisorZeroIndex₀ f (Set.univ : Set ℂ)))
        (hsmall_fin : smallSet.Finite),
        smallSet =
            {p : divisorZeroIndex₀ f (Set.univ : Set ℂ) |
              ‖divisorZeroIndex₀_val p‖ ≤ 4 * R} →
        (let small : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) := hsmall_fin.toFinset
         let a : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ :=
          fun p => ‖divisorZeroIndex₀_val p‖
         r ∉ small.image a) →
        (let small : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) := hsmall_fin.toFinset
         let a : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ :=
          fun p => ‖divisorZeroIndex₀_val p‖
         (∑ p ∈ small, (1 : ℝ) * CartanBound.φ (r / a p)) ≤
          CartanBound.Cφ * (small.card : ℝ)) →
        ∀ u : ℂ, ‖u‖ = r → ‖H u‖ ≤ Real.exp ((Cf + Cprod + 10) * (1 + r) ^ τ) := by
  classical
  intro Sτ Cprod R r hRpos hRle hR_le_r hr_le_2R hrpos smallSet hsmall_fin
    hsmallSet hr_not_bad hr_phi u hur
  let small : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) := hsmall_fin.toFinset
  let a : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ := fun p => ‖divisorZeroIndex₀_val p‖
  let bad : Finset ℝ := small.image a
  have hr_not_bad' : r ∉ bad := by
    simpa [bad, small, a] using hr_not_bad
  have hden_eq :
      f u =
        H u * (u ^ analyticOrderNatAt f 0 *
          divisorCanonicalProduct m f (Set.univ : Set ℂ) u) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using (hfactor u)
  have hfu_ne : f u ≠ 0 := by
    have hr_le_4R : r ≤ 4 * R := by nlinarith [hr_le_2R, hRpos]
    exact no_zero_on_sphere_of_norm_image_avoid (f := f) hentire hnot
      (B := 4 * R) (r := r) hrpos hr_le_4R smallSet hsmall_fin hsmallSet
      (by simpa [small, a] using hr_not_bad) u hur
  have hden_ne :
      (u ^ analyticOrderNatAt f 0 *
        divisorCanonicalProduct m f (Set.univ : Set ℂ) u) ≠ 0 := by
    intro hden0
    have : f u = 0 := by simpa [hden0] using hden_eq
    exact hfu_ne this
  have hHu :
      H u =
        f u / (u ^ analyticOrderNatAt f 0 *
          divisorCanonicalProduct m f (Set.univ : Set ℂ) u) := by
    exact eq_div_of_mul_eq hden_ne (Eq.symm hden_eq)
  have hf_u : ‖f u‖ ≤ Real.exp (Cf * (1 + r) ^ τ) := by
    simpa [hur] using hf_boundτ u
  have hden_inv :
      ‖(u ^ analyticOrderNatAt f 0 *
          divisorCanonicalProduct m f (Set.univ : Set ℂ) u)⁻¹‖
        ≤ Real.exp (Cprod * (1 + r) ^ τ) := by
    simpa [Sτ, Cprod] using
      (norm_inv_hadamardDenominator_le_exp_on_cartan_circle
        (f := f) (ρ := ρ) (τ := τ) (m := m)
        hmρ hτ hτ_lt hτ_nonneg h_sum hsumτ
        (R := R) (r := r) hRpos hRle hR_le_r hr_le_2R
        smallSet hsmall_fin hsmallSet
        (by simpa [small, a] using hr_not_bad)
        (by simpa [small, a, one_mul] using hr_phi)
        u hur)
  have :
      ‖H u‖ ≤
        ‖f u‖ *
          ‖(u ^ analyticOrderNatAt f 0 *
            divisorCanonicalProduct m f (Set.univ : Set ℂ) u)⁻¹‖ := by
    have :
        ‖H u‖ =
          ‖f u /
            (u ^ analyticOrderNatAt f 0 *
              divisorCanonicalProduct m f (Set.univ : Set ℂ) u)‖ := by
      simp [hHu]
    simp [div_eq_mul_inv, norm_inv, this]
  have hmul :
      ‖f u‖ *
          ‖(u ^ analyticOrderNatAt f 0 *
            divisorCanonicalProduct m f (Set.univ : Set ℂ) u)⁻¹‖
        ≤ Real.exp (Cf * (1 + r) ^ τ) * Real.exp (Cprod * (1 + r) ^ τ) :=
    mul_le_mul hf_u hden_inv (by positivity) (by positivity)
  have hexp :
      Real.exp (Cf * (1 + r) ^ τ) * Real.exp (Cprod * (1 + r) ^ τ)
        = Real.exp ((Cf + Cprod) * (1 + r) ^ τ) := by
    simp [Real.exp_add, add_mul, add_comm]
  have : ‖H u‖ ≤ Real.exp ((Cf + Cprod) * (1 + r) ^ τ) :=
    (this.trans hmul).trans_eq hexp
  have hslack :
      Real.exp ((Cf + Cprod) * (1 + r) ^ τ) ≤
        Real.exp ((Cf + Cprod + 10) * (1 + r) ^ τ) := by
    refine Real.exp_le_exp.2 ?_
    have hnn : 0 ≤ (1 + r) ^ τ := by positivity
    nlinarith
  exact this.trans hslack

theorem hadamardQuotient_norm_le_exp_rpow_of_growth {f H : ℂ → ℂ} {ρ τ : ℝ} {m : ℕ}
    (hρ : 0 ≤ ρ) (hmρ : (m : ℝ) ≤ ρ) (hτ : ρ < τ) (hτ_lt : τ < (m + 1 : ℝ))
    (hτ_nonneg : 0 ≤ τ) (hentire : Differentiable ℂ f) (hH_entire : Differentiable ℂ H)
    (hnot : ∃ z : ℂ, f z ≠ 0)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1)))
    (hgrowth : ∃ C > 0, ∀ z : ℂ, Real.log (1 + ‖f z‖) ≤ C * (1 + ‖z‖) ^ ρ)
    (hfactor : ∀ z : ℂ,
      f z =
        H z * z ^ analyticOrderNatAt f 0 *
          divisorCanonicalProduct m f (Set.univ : Set ℂ) z) :
    ∃ C > 0, ∀ z : ℂ, ‖H z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ τ) := by
  rcases hgrowth with ⟨Cf, hCfpos, hCf⟩
  have hsumτ :
      Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
        ‖divisorZeroIndex₀_val p‖⁻¹ ^ τ) :=
    summable_norm_inv_rpow_divisorZeroIndex₀_of_growth (f := f) (ρ := ρ) (τ := τ)
      hρ hτ hentire hnot ⟨Cf, hCfpos, hCf⟩
  let Sτ : ℝ := ∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), ‖divisorZeroIndex₀_val p‖⁻¹ ^ τ
  have hSτ_nonneg : 0 ≤ Sτ := tsum_nonneg fun _ =>
    Real.rpow_nonneg (inv_nonneg.2 (norm_nonneg _)) _
  let Cprod : ℝ := cartanProductConstant m τ Sτ
  have hCprod_nonneg : 0 ≤ Cprod := by
    simpa [Cprod] using cartanProductConstant_nonneg (m := m) (τ := τ) hSτ_nonneg
  have hf_boundτ : ∀ z : ℂ, ‖f z‖ ≤ Real.exp (Cf * (1 + ‖z‖) ^ τ) :=
    Real.norm_le_exp_mul_rpow_of_log_growth
      (f := f) (r := fun z : ℂ => 1 + ‖z‖) (C := Cf) (ρ := ρ) (τ := τ)
      hCfpos.le (fun z => by linarith [norm_nonneg z]) (le_of_lt hτ) hCf
  refine ⟨(Cf + Cprod + 10) * (3 : ℝ) ^ τ, by
    have h3τ : 0 < (3 : ℝ) ^ τ := by positivity
    nlinarith [hCfpos, hCprod_nonneg, h3τ], ?_⟩
  intro z
  let R : ℝ := max ‖z‖ 1
  have hRpos : 0 < R := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hRle : (1 : ℝ) ≤ R := le_max_right _ _
  let smallSet : Set (divisorZeroIndex₀ f (Set.univ : Set ℂ)) :=
    {p | ‖divisorZeroIndex₀_val p‖ ≤ 4 * R}
  have hsmall_fin : smallSet.Finite := by
    have : Metric.closedBall (0 : ℂ) (4 * R) ⊆ (Set.univ : Set ℂ) := by simp
    simpa [smallSet] using
      (divisorZeroIndex₀_norm_le_finite (f := f) (U := (Set.univ : Set ℂ))
        (B := 4 * R) this)
  let small : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) := hsmall_fin.toFinset
  let a : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ := fun p => ‖divisorZeroIndex₀_val p‖
  have ha_pos : ∀ p ∈ small, 0 < a p := by
    intro p hp
    exact norm_pos_iff.2 (divisorZeroIndex₀_val_ne_zero p)
  let bad : Finset ℝ := small.image a
  rcases CartanBound.exists_radius_Ioc_sum_mul_phi_div_le_Cφ_mul_sum_avoid
      (s := small) (w := fun _ => (1 : ℝ)) (a := a)
      (hw := by intro _ _; norm_num) (ha := ha_pos) (bad := bad) (R := R) hRpos with
    ⟨r, hr_mem, hr_not_bad, hr_phi⟩
  have hR_le_r : R ≤ r := le_of_lt hr_mem.1
  have hr_le_2R : r ≤ 2 * R := hr_mem.2
  have hrpos : 0 < r := lt_of_lt_of_le hRpos hR_le_r
  have hcircle :
      ∀ u : ℂ, ‖u‖ = r → ‖H u‖ ≤ Real.exp ((Cf + Cprod + 10) * (1 + r) ^ τ) := by
    simpa [Sτ, Cprod] using
      (hadamardQuotient_norm_le_exp_on_cartan_circle
        (f := f) (H := H) (ρ := ρ) (τ := τ) (m := m) (Cf := Cf)
        hmρ hτ hτ_lt hτ_nonneg hentire hnot h_sum hsumτ hf_boundτ hfactor
        (R := R) (r := r) hRpos hRle hR_le_r hr_le_2R hrpos
        smallSet hsmall_fin (by rfl)
        (by simpa [small, a, bad] using hr_not_bad)
        (by simpa [small, a, one_mul, Finset.sum_const, nsmul_eq_mul] using hr_phi))
  have hz_ball : z ∈ Metric.ball (0 : ℂ) r := by
    rw [Metric.mem_ball, dist_zero_right]
    exact lt_of_le_of_lt (le_max_left _ _) hr_mem.1
  have hball :
      ‖H z‖ ≤ Real.exp ((Cf + Cprod + 10) * (1 + r) ^ τ) := by
    exact Complex.norm_le_of_mem_ball_of_forall_sphere_norm_le hH_entire hrpos hz_ball hcircle
  have hr_le_3 : 1 + r ≤ 3 * (1 + ‖z‖) := by
    exact Real.one_add_le_three_mul_one_add_of_le_two_mul_max (norm_nonneg z)
      (by simpa [R] using hr_le_2R)
  have hmain :
      Real.exp ((Cf + Cprod + 10) * (1 + r) ^ τ)
        ≤ Real.exp (((Cf + Cprod + 10) * (3 : ℝ) ^ τ) * (1 + ‖z‖) ^ τ) := by
    have hnn : 0 ≤ (Cf + Cprod + 10) := by nlinarith [le_of_lt hCfpos, hCprod_nonneg]
    exact Real.exp_mul_rpow_le_exp_mul_rpow_of_le_mul hnn (by norm_num)
      (by linarith [le_of_lt hrpos]) (by positivity) hτ_nonneg hr_le_3
  simpa [mul_assoc] using hball.trans hmain

theorem hadamard_factorization_of_growth {f : ℂ → ℂ} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hentire : Differentiable ℂ f)
    (hnot : ∃ z : ℂ, f z ≠ 0)
    (hgrowth : ∃ C > 0, ∀ z : ℂ, Real.log (1 + ‖f z‖) ≤ C * (1 + ‖z‖) ^ ρ) :
    ∃ (P : Polynomial ℂ),
      P.degree ≤ Nat.floor ρ ∧
      ∀ z : ℂ,
        f z =
          Complex.exp (Polynomial.eval z P) *
            z ^ (analyticOrderNatAt f 0) *
            divisorCanonicalProduct (Nat.floor ρ) f (Set.univ : Set ℂ) z := by
  set m : ℕ := Nat.floor ρ
  have h_sum :
      Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
        ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1)) := by
    simpa [m] using
      (summable_norm_inv_pow_divisorZeroIndex₀_of_growth (f := f) (ρ := ρ)
        hρ hentire hnot hgrowth)
  rcases exists_entire_nonzero_hadamardQuotient (m := m) (f := f) hentire hnot h_sum with
    ⟨H, hH_entire, hH_ne, hfactor⟩
  rcases Real.exists_between_self_and_floor_add_one_same_floor hρ with
    ⟨τ, hτ, hτ_lt, hτ_nonneg, hfloorτ'⟩
  have hfloorτ : Nat.floor τ = m := by
    simpa [m] using hfloorτ'
  have hτ_lt_m : τ < (m + 1 : ℝ) := by
    simpa [m] using hτ_lt
  have hτ_lt_nat : τ < ((m + 1 : ℕ) : ℝ) := by
    simpa [Nat.cast_add, Nat.cast_one] using hτ_lt_m
  have hmρ : (m : ℝ) ≤ ρ := by
    have := Nat.floor_le hρ
    simpa [m] using this
  have hH_bound_rpow :
      ∃ C > 0, ∀ z : ℂ, ‖H z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ τ) :=
    hadamardQuotient_norm_le_exp_rpow_of_growth (f := f) (H := H) (ρ := ρ) (τ := τ)
      (m := m) hρ hmρ hτ hτ_lt hτ_nonneg hentire hH_entire hnot h_sum hgrowth hfactor
  have hH_growth_nat :
      ∃ C > 0, ∀ z : ℂ, ‖H z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ (m + 1)) := by
    exact Real.exists_norm_le_exp_mul_pow_of_rpow_bound
      (f := H) (r := fun z : ℂ => 1 + ‖z‖)
      (fun z => by linarith [norm_nonneg z]) hτ_lt_nat hH_bound_rpow
  rcases zero_free_polynomial_growth_is_exp_poly (H := H) (n := m + 1)
      hH_entire hH_ne hH_growth_nat with
    ⟨P, hPn, hHP⟩
  have hPnat : P.natDegree ≤ m := by
    have hbound :
        ∃ C > 0, ∀ z : ℂ,
          ‖Complex.exp (Polynomial.eval z P)‖ ≤ Real.exp (C * (1 + ‖z‖) ^ τ) := by
      rcases hH_bound_rpow with ⟨C, hCpos, hC⟩
      exact ⟨C, hCpos, fun z => by simpa [hHP z] using (hC z)⟩
    have := natDegree_le_floor_of_exp_eval_norm_bound hτ_nonneg P hbound
    simpa [hfloorτ] using this
  refine ⟨P, ?_, ?_⟩
  · have : P.degree ≤ m := Polynomial.degree_le_of_natDegree_le hPnat
    simpa [m] using this
  · intro z
    have hH' : H z = Complex.exp (Polynomial.eval z P) := by simpa using (hHP z)
    simpa [hH', mul_assoc, mul_left_comm, mul_comm, m] using (hfactor z)

end Complex.Hadamard
end
end
end File38

-- Upstream module PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.HadamardFactorization.Order
section File39
 

section
noncomputable section

open Set Filter Asymptotics
open scoped Topology BigOperators

namespace Complex.Hadamard

lemma analyticOrderNatAt_comp_add_const (f : ℂ → ℂ) (c : ℂ) :
    analyticOrderNatAt (fun w : ℂ => f (w + c)) 0 = analyticOrderNatAt f c := by
  let g : ℂ → ℂ := fun w => w + c
  have hg : AnalyticAt ℂ g 0 := by fun_prop
  have hg' : deriv g 0 ≠ 0 := by
    simp [g]
  have h :=
    analyticOrderAt_comp_of_deriv_ne_zero (f := f) (g := g) (z₀ := (0 : ℂ)) hg hg'
  have h' :
      analyticOrderAt ((fun x : ℂ => f x) ∘ g) 0 = analyticOrderAt f c := by
    simpa [g] using h
  simpa [analyticOrderNatAt, g] using! congrArg ENat.toNat h'

lemma analyticOrderNatAt_comp_sub_const (f : ℂ → ℂ) (c : ℂ) :
    analyticOrderNatAt (fun w : ℂ => f (w - c)) 0 = analyticOrderNatAt f (-c) := by
  simpa [sub_eq_add_neg] using analyticOrderNatAt_comp_add_const f (-c)

theorem centeredHadamardDenom_eq_hadamardDenom_translate
    (m : ℕ) (c : ℂ) (f : ℂ → ℂ) (z : ℂ) :
    centeredHadamardDenom m c f z =
      hadamardDenom m (fun w : ℂ => f (w + c)) (z - c) := by
  simp [centeredHadamardDenom, hadamardDenom, analyticOrderNatAt_comp_add_const]

def EntireOfOrderAtMost (ρ : ℝ) (f : ℂ → ℂ) : Prop :=
    Differentiable ℂ f ∧ ∀ ε : ℝ, 0 < ε →
  ∃ C > 0, ∀ z : ℂ, ‖f z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ (ρ + ε))

namespace EntireOfOrderAtMost

theorem differentiable {ρ : ℝ} {f : ℂ → ℂ} (h : EntireOfOrderAtMost ρ f) :
    Differentiable ℂ f :=
  h.1

theorem exists_bound {ρ ε : ℝ} {f : ℂ → ℂ} (h : EntireOfOrderAtMost ρ f)
    (hε : 0 < ε) :
    ∃ C > 0, ∀ z : ℂ, ‖f z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ (ρ + ε)) :=
  h.2 ε hε

theorem of_norm_le_exp {ρ : ℝ} {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hbound : ∃ C > 0, ∀ z : ℂ, ‖f z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ ρ)) :
    EntireOfOrderAtMost ρ f := by
  refine ⟨hf, ?_⟩
  rintro ε hε
  rcases hbound with ⟨C, hC, hCbound⟩
  refine ⟨C, hC, ?_⟩
  exact Real.norm_le_exp_mul_rpow_of_exponent_le (f := f)
    (r := fun z : ℂ => 1 + ‖z‖) hC.le
    (fun z => by linarith [norm_nonneg z]) (by linarith : ρ ≤ ρ + ε) hCbound

theorem exists_log_growth {ρ τ : ℝ} {f : ℂ → ℂ} (h : EntireOfOrderAtMost ρ f)
    (hτ : ρ < τ) (hτ_nonneg : 0 ≤ τ) :
    ∃ C' > 0, ∀ z : ℂ, Real.log (1 + ‖f z‖) ≤ C' * (1 + ‖z‖) ^ τ := by
  rcases h.exists_bound (sub_pos.2 hτ) with ⟨C, hCpos, hC⟩
  have hnorm : ∀ z : ℂ, ‖f z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ τ) := by
    intro z
    simpa [sub_add_cancel] using (hC z)
  exact Real.log_growth_of_norm_le_exp_mul_rpow (f := f)
    (r := fun z : ℂ => 1 + ‖z‖) hCpos hτ_nonneg
    (fun z => by linarith [norm_nonneg z]) hnorm

theorem comp_add_const {ρ : ℝ} {f : ℂ → ℂ} (h : EntireOfOrderAtMost ρ f)
    (hρ : 0 ≤ ρ) (c : ℂ) :
    EntireOfOrderAtMost ρ (fun z : ℂ => f (z + c)) := by
  refine ⟨h.differentiable.comp (differentiable_id.add (differentiable_const c)), ?_⟩
  intro ε hε
  rcases h.exists_bound hε with ⟨C, hC, hCbound⟩
  let A : ℝ := 1 + ‖c‖
  let C' : ℝ := C * A ^ (ρ + ε)
  have hApos : 0 < A := by
    dsimp [A]
    positivity
  have hτnonneg : 0 ≤ ρ + ε := by linarith
  refine ⟨C', mul_pos hC (Real.rpow_pos_of_pos hApos _), ?_⟩
  intro z
  have hbase :
      1 + ‖z + c‖ ≤ A * (1 + ‖z‖) := by
    dsimp [A]
    have hnorm : ‖z + c‖ ≤ ‖z‖ + ‖c‖ := norm_add_le z c
    nlinarith [norm_nonneg z, norm_nonneg c]
  have hpow :
      (1 + ‖z + c‖) ^ (ρ + ε) ≤ (A * (1 + ‖z‖)) ^ (ρ + ε) := by
    exact Real.rpow_le_rpow (by positivity) hbase hτnonneg
  calc
    ‖f (z + c)‖ ≤ Real.exp (C * (1 + ‖z + c‖) ^ (ρ + ε)) := hCbound (z + c)
    _ ≤ Real.exp (C' * (1 + ‖z‖) ^ (ρ + ε)) := by
      refine Real.exp_le_exp.2 ?_
      calc
        C * (1 + ‖z + c‖) ^ (ρ + ε) ≤ C * (A * (1 + ‖z‖)) ^ (ρ + ε) := by
          exact mul_le_mul_of_nonneg_left hpow hC.le
        _ = C' * (1 + ‖z‖) ^ (ρ + ε) := by
          rw [Real.mul_rpow (le_of_lt hApos) (by positivity : 0 ≤ 1 + ‖z‖)]
          ring

theorem comp_sub_const {ρ : ℝ} {f : ℂ → ℂ} (h : EntireOfOrderAtMost ρ f)
    (hρ : 0 ≤ ρ) (c : ℂ) :
    EntireOfOrderAtMost ρ (fun z : ℂ => f (z - c)) := by
  simpa [sub_eq_add_neg] using h.comp_add_const hρ (-c)

theorem summable_norm_inv_pow_divisorZeroIndex₀ {ρ : ℝ} {f : ℂ → ℂ}
    (h : EntireOfOrderAtMost ρ f) (hρ : 0 ≤ ρ) (hnot : ∃ z : ℂ, f z ≠ 0) :
    Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (Nat.floor ρ + 1)) := by
  rcases Real.exists_between_self_and_floor_add_one_same_floor hρ with
    ⟨τ, hτ, _hτ_lt, hτ_nonneg, hfloorτ⟩
  have hgrowthτ :
      ∃ C' > 0, ∀ z : ℂ, Real.log (1 + ‖f z‖) ≤ C' * (1 + ‖z‖) ^ τ :=
    h.exists_log_growth hτ hτ_nonneg
  have hsummable :=
    summable_norm_inv_pow_divisorZeroIndex₀_of_growth
      (f := f) (ρ := τ) hτ_nonneg h.differentiable hnot hgrowthτ
  simpa [hfloorτ] using hsummable

end EntireOfOrderAtMost

theorem hadamard_factorization_of_order {f : ℂ → ℂ} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hnot : ∃ z : ℂ, f z ≠ 0)
    (horder : EntireOfOrderAtMost ρ f) :
    ∃ (P : Polynomial ℂ),
      P.degree ≤ Nat.floor ρ ∧
      ∀ z : ℂ,
        f z =
          Complex.exp (Polynomial.eval z P) *
            z ^ (analyticOrderNatAt f 0) *
            divisorCanonicalProduct (Nat.floor ρ) f (Set.univ : Set ℂ) z := by
  classical
  let hentire : Differentiable ℂ f := horder.differentiable
  set m : ℕ := Nat.floor ρ
  rcases Real.exists_between_self_and_floor_add_one_same_floor hρ with
    ⟨τ, hτ, hτ_lt, hτ_nonneg, hfloorτ'⟩
  have hfloorτ : Nat.floor τ = m := by
    simpa [m] using hfloorτ'
  have hgrowthτ :
      ∃ C' > 0, ∀ z : ℂ, Real.log (1 + ‖f z‖) ≤ C' * (1 + ‖z‖) ^ τ :=
    horder.exists_log_growth hτ hτ_nonneg
  rcases hadamard_factorization_of_growth (f := f) (ρ := τ) hτ_nonneg
      hentire hnot hgrowthτ with
    ⟨P, hdeg, hfac⟩
  refine ⟨P, ?_, ?_⟩
  · simpa [m, hfloorτ] using hdeg
  · intro z
    simpa [m, hfloorτ] using hfac z

theorem hadamard_factorization_of_order_reindex {ι : Type*} {f : ℂ → ℂ} {ρ : ℝ}
    (hρ : 0 ≤ ρ) (hnot : ∃ z : ℂ, f z ≠ 0)
    (horder : EntireOfOrderAtMost ρ f)
    (e : ι ≃ divisorZeroIndex₀ f (Set.univ : Set ℂ)) :
    ∃ (P : Polynomial ℂ),
      P.degree ≤ Nat.floor ρ ∧
      ∀ z : ℂ,
        f z =
          Complex.exp (Polynomial.eval z P) *
            z ^ (analyticOrderNatAt f 0) *
            (∏' i : ι, weierstrassFactor (Nat.floor ρ)
              (z / divisorZeroIndex₀_val (e i))) := by
  classical
  rcases hadamard_factorization_of_order (f := f) (ρ := ρ) hρ hnot horder with
    ⟨P, hdeg, hfac⟩
  refine ⟨P, hdeg, ?_⟩
  intro z
  simpa [divisorCanonicalProduct_eq_tprod_of_equiv (m := Nat.floor ρ)
      (f := f) (U := Set.univ) e z] using hfac z

theorem hadamard_factorization_of_order_sequence {f : ℂ → ℂ} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hnot : ∃ z : ℂ, f z ≠ 0)
    (horder : EntireOfOrderAtMost ρ f)
    (e : ℕ ≃ divisorZeroIndex₀ f (Set.univ : Set ℂ)) :
    ∃ (P : Polynomial ℂ),
      P.degree ≤ Nat.floor ρ ∧
      ∀ z : ℂ,
        f z =
          Complex.exp (Polynomial.eval z P) *
            z ^ (analyticOrderNatAt f 0) *
            Complex.canonicalProduct (Nat.floor ρ)
              (fun n : ℕ => divisorZeroIndex₀_val (e n)) z := by
  classical
  rcases hadamard_factorization_of_order_reindex (f := f) (ρ := ρ) hρ hnot horder e with
    ⟨P, hdeg, hfac⟩
  refine ⟨P, hdeg, ?_⟩
  intro z
  simpa [Complex.canonicalProduct_def] using hfac z

theorem hadamard_factorization_of_order_centered {f : ℂ → ℂ} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (c : ℂ) (hnot : ∃ z : ℂ, f z ≠ 0)
    (horder : EntireOfOrderAtMost ρ f) :
    ∃ (P : Polynomial ℂ),
      P.degree ≤ Nat.floor ρ ∧
      ∀ z : ℂ,
        f z =
          Complex.exp (Polynomial.eval (z - c) P) *
            (z - c) ^ (analyticOrderNatAt f c) *
            divisorCanonicalProduct (Nat.floor ρ) (fun w : ℂ => f (w + c))
              (Set.univ : Set ℂ) (z - c) := by
  classical
  let g : ℂ → ℂ := fun w : ℂ => f (w + c)
  have hnot_g : ∃ w : ℂ, g w ≠ 0 := by
    rcases hnot with ⟨z, hz⟩
    refine ⟨z - c, ?_⟩
    simpa [g] using hz
  have horder_g : EntireOfOrderAtMost ρ g :=
    horder.comp_add_const hρ c
  rcases hadamard_factorization_of_order (f := g) (ρ := ρ) hρ hnot_g horder_g with
    ⟨P, hdeg, hfac⟩
  refine ⟨P, hdeg, ?_⟩
  intro z
  have h := hfac (z - c)
  have horder0 : analyticOrderNatAt g 0 = analyticOrderNatAt f c := by
    simpa [g] using analyticOrderNatAt_comp_add_const f c
  simpa [g, horder0] using h

theorem hadamard_factorization_of_order_centered_reindex {ι : Type*} {f : ℂ → ℂ} {ρ : ℝ}
    (hρ : 0 ≤ ρ) (c : ℂ) (hnot : ∃ z : ℂ, f z ≠ 0)
    (horder : EntireOfOrderAtMost ρ f)
    (e : ι ≃ divisorZeroIndex₀ (fun w : ℂ => f (w + c)) (Set.univ : Set ℂ)) :
    ∃ (P : Polynomial ℂ),
      P.degree ≤ Nat.floor ρ ∧
      ∀ z : ℂ,
        f z =
          Complex.exp (Polynomial.eval (z - c) P) *
            (z - c) ^ (analyticOrderNatAt f c) *
            (∏' i : ι, weierstrassFactor (Nat.floor ρ)
              ((z - c) / divisorZeroIndex₀_val (e i))) := by
  classical
  rcases hadamard_factorization_of_order_centered
      (f := f) (ρ := ρ) hρ c hnot horder with
    ⟨P, hdeg, hfac⟩
  refine ⟨P, hdeg, ?_⟩
  intro z
  simpa [divisorCanonicalProduct_eq_tprod_of_equiv (m := Nat.floor ρ)
      (f := fun w : ℂ => f (w + c)) (U := Set.univ) e (z - c)] using hfac z

theorem hadamard_factorization_of_order_centered_sequence {f : ℂ → ℂ} {ρ : ℝ}
    (hρ : 0 ≤ ρ) (c : ℂ) (hnot : ∃ z : ℂ, f z ≠ 0)
    (horder : EntireOfOrderAtMost ρ f)
    (e : ℕ ≃ divisorZeroIndex₀ (fun w : ℂ => f (w + c)) (Set.univ : Set ℂ)) :
    ∃ (P : Polynomial ℂ),
      P.degree ≤ Nat.floor ρ ∧
      ∀ z : ℂ,
        f z =
          Complex.exp (Polynomial.eval (z - c) P) *
            (z - c) ^ (analyticOrderNatAt f c) *
            Complex.canonicalProduct (Nat.floor ρ)
              (fun n : ℕ => divisorZeroIndex₀_val (e n)) (z - c) := by
  classical
  rcases hadamard_factorization_of_order_centered_reindex
      (f := f) (ρ := ρ) hρ c hnot horder e with
    ⟨P, hdeg, hfac⟩
  refine ⟨P, hdeg, ?_⟩
  intro z
  simpa [Complex.canonicalProduct_def] using hfac z

end Complex.Hadamard
end
end
end File39

-- Upstream module PrimeNumberTheoremAnd.Mathlib.Analysis.Calculus.Deriv.Polynomial
section File40

section
namespace Polynomial

theorem logDeriv_exp_eval (P : ℂ[X]) (z : ℂ) :
    logDeriv (fun w : ℂ => Complex.exp (Polynomial.eval w P)) z =
      Polynomial.eval z P.derivative := by
  have hderiv :
      deriv (fun w : ℂ => Complex.exp (Polynomial.eval w P)) z =
        Complex.exp (Polynomial.eval z P) * Polynomial.eval z P.derivative := by
    simpa [Function.comp_def, mul_comm] using
      ((Complex.hasDerivAt_exp (Polynomial.eval z P)).comp z (P.hasDerivAt z)).deriv
  rw [logDeriv_apply, hderiv]
  field_simp [Complex.exp_ne_zero (Polynomial.eval z P)]

theorem degree_derivative_le_zero_of_degree_le_one {P : Polynomial ℂ}
    (hP : P.degree ≤ 1) :
    P.derivative.degree ≤ 0 := by
  rw [Polynomial.degree_le_iff_coeff_zero]
  intro m hm
  rw [Polynomial.coeff_derivative]
  have hmpos : 0 < m := by exact_mod_cast hm
  have hlt : (1 : WithBot ℕ) < (m + 1 : ℕ) := by
    norm_cast
    exact Nat.succ_lt_succ hmpos
  have hcoeff := (Polynomial.degree_le_iff_coeff_zero P 1).mp hP (m + 1) hlt
  simp [hcoeff]

theorem eval_derivative_eq_eval_derivative_zero_of_degree_le_one {P : Polynomial ℂ}
    (hP : P.degree ≤ 1) (z : ℂ) :
    Polynomial.eval z P.derivative = Polynomial.eval 0 P.derivative := by
  have hder :
      P.derivative.degree ≤ 0 :=
    degree_derivative_le_zero_of_degree_le_one hP
  rw [Polynomial.eq_C_of_degree_le_zero hder]
  simp

end Polynomial
end
end File40

-- Upstream module PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.ZetaFunctionalEquation
section File41
 

noncomputable section

section
open Complex

namespace Complex

theorem zeta_functional_equation (s : ℂ) :
    completedRiemannZeta s = completedRiemannZeta (1 - s) := by
  simpa using (completedRiemannZeta_one_sub s).symm

end Complex
end
end
end File41

-- Upstream module PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.CompletedXi
section File42
 

section
noncomputable section

open Complex

namespace Complex

noncomputable def riemannXi (s : ℂ) : ℂ :=
  (s * (s - 1) * completedRiemannZeta₀ s + 1) / 2

theorem riemannXi_zero : riemannXi 0 = 1 / 2 := by
  simp [riemannXi]

theorem riemannXi_nontrivial : ∃ s : ℂ, riemannXi s ≠ 0 := by
  refine ⟨0, ?_⟩
  simp [riemannXi_zero]

theorem differentiable_riemannXi : Differentiable ℂ riemannXi := by
  exact (((differentiable_id.mul (differentiable_id.sub (differentiable_const (1 : ℂ)))).mul
    differentiable_completedZeta₀).add (differentiable_const (1 : ℂ))).div_const 2

theorem riemannXi_eq_mul_completedRiemannZeta {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    riemannXi s = s * (s - 1) * completedRiemannZeta s / 2 := by
  rw [riemannXi, completedRiemannZeta_eq]
  have h1ms : 1 - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  field_simp [hs0, h1ms]
  ring

theorem riemannXi_one_sub (s : ℂ) : riemannXi (1 - s) = riemannXi s := by
  rw [riemannXi, riemannXi, completedRiemannZeta₀_one_sub]
  ring

end Complex
end
end
end File42

-- Upstream module PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.Basic
section File43
 

section
namespace Complex

theorem div_sub_one_eq_one_add_one_div (z : ℂ) (hz : z ≠ 1) : z / (z - 1) = 1 + (z - 1)⁻¹ := by
  have h : z - 1 ≠ 0 := sub_ne_zero.mpr hz
  calc
    z / (z - 1) = ((z - 1) + 1) / (z - 1) := by ring_nf
    _ = (z - 1) / (z - 1) + 1 / (z - 1) := by rw [add_div]
    _ = 1 + (z - 1)⁻¹ := by simp [div_eq_mul_inv, h]

lemma exists_norm_bound_on_closedBall {f : ℂ → ℂ} {R : ℝ}
    (hcont : ContinuousOn f (Metric.closedBall (0 : ℂ) R)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z : ℂ, ‖z‖ ≤ R → ‖f z‖ ≤ M := by
  have hcomp : IsCompact (Metric.closedBall (0 : ℂ) R) := isCompact_closedBall 0 R
  obtain ⟨M, hM⟩ := hcomp.exists_bound_of_continuousOn hcont
  refine ⟨max M 0, le_max_right _ _, fun z hz => ?_⟩
  exact (hM z (Metric.mem_closedBall.mpr (by simpa using hz))).trans (le_max_left _ _)

theorem exists_pos_radius_forall_mem_ball_re_ge {z₀ : ℂ} {a : ℝ} (ha : a < z₀.re) :
    ∃ δ > 0, ∀ (x y : ℂ), dist x z₀ < δ → dist y x < δ → a ≤ y.re := by
  set δ : ℝ := (z₀.re - a) / 2 with hδdef
  have hpos : 0 < z₀.re - a := sub_pos.mpr ha
  have hδpos : 0 < δ := by simpa [hδdef] using half_pos hpos
  refine ⟨δ, hδpos, ?_⟩
  intro x y hx hy
  have htri : dist y z₀ ≤ dist y x + dist x z₀ := dist_triangle y x z₀
  have hsumlt : dist y x + dist x z₀ < δ + δ := add_lt_add hy hx
  have hnorm_lt : ‖y - z₀‖ < δ + δ := by simpa [dist_eq_norm] using lt_of_le_of_lt htri hsumlt
  have hdeltaSum : δ + δ = z₀.re - a := by simp [hδdef, add_halves]
  have hnorm_lt_re : ‖y - z₀‖ < z₀.re - a := by simpa [hdeltaSum] using hnorm_lt
  have h_eps_lt : a < z₀.re - ‖y - z₀‖ := by
    have hsum' : a + ‖y - z₀‖ < z₀.re := by
      simpa [add_comm, add_left_comm, add_assoc, sub_eq_add_neg] using
        (add_lt_add_left hnorm_lt_re a)
    simpa [lt_sub_iff_add_lt] using hsum'
  have hre_lower : -‖y - z₀‖ ≤ (y - z₀).re := (abs_le.mp (abs_re_le_norm (y - z₀))).1
  have hyge : z₀.re - ‖y - z₀‖ ≤ y.re := by
    have h' : z₀.re + (-‖y - z₀‖) ≤ z₀.re + (y - z₀).re := add_le_add_right hre_lower z₀.re
    have h'' : z₀.re + (y - z₀).re = y.re := by
      simp [sub_eq_add_neg]
    simpa [sub_eq_add_neg, h''] using h'
  exact le_of_lt (lt_of_lt_of_le h_eps_lt hyge)

end Complex
end
end File43

-- Upstream module PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.Trigonometric
section File44

section
namespace Complex

lemma norm_cos_le_exp_abs_im (z : ℂ) : ‖cos z‖ ≤ Real.exp |z.im| := by
  have hcos :
      cos z = (exp (z * I) + exp (-z * I)) / 2 := by
    simp [cos]
  have htri :
      ‖exp (z * I) + exp (-z * I)‖ ≤ ‖exp (z * I)‖ + ‖exp (-z * I)‖ :=
    norm_add_le _ _
  have hdiv :
      ‖(exp (z * I) + exp (-z * I)) / 2‖
        ≤ (‖exp (z * I)‖ + ‖exp (-z * I)‖) / 2 := by
    have : ‖exp (z * I) + exp (-z * I)‖ / 2
          ≤ (‖exp (z * I)‖ + ‖exp (-z * I)‖) / 2 :=
      div_le_div_of_nonneg_right htri (by norm_num)
    simpa [Complex.norm_div, Complex.norm_ofNat] using this
  have h1 : ‖exp (z * I)‖ = Real.exp (-(z.im)) := by
    simp [norm_exp, mul_re, I_re, I_im]
  have h2 : ‖exp (-(z * I))‖ = Real.exp (z.im) := by
    simp [norm_exp, mul_re, I_re, I_im]
  have habs1 : Real.exp (-(z.im)) ≤ Real.exp |z.im| :=
    Real.exp_le_exp.mpr (neg_le_abs z.im)
  have habs2 : Real.exp (z.im) ≤ Real.exp |z.im| :=
    Real.exp_le_exp.mpr (le_abs_self z.im)
  have hsum :
      (‖exp (z * I)‖ + ‖exp (-(z * I))‖) / 2 ≤ Real.exp |z.im| := by
    have : ‖exp (z * I)‖ + ‖exp (-(z * I))‖
        ≤ Real.exp |z.im| + Real.exp |z.im| := by
      simpa [h1, h2] using add_le_add habs1 habs2
    have : (‖exp (z * I)‖ + ‖exp (-(z * I))‖) / 2
        ≤ (Real.exp |z.im| + Real.exp |z.im|) / 2 :=
      div_le_div_of_nonneg_right this (by norm_num)
    simpa [two_mul] using this
  have :
      ‖cos z‖ ≤ (‖exp (z * I)‖ + ‖exp (-(z * I))‖) / 2 := by
    simpa [hcos] using hdiv
  exact le_trans this hsum

end Complex
end
end File44

-- Upstream module PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Gamma.IntegralBounds
section File45
 

open Real Complex Set MeasureTheory

section
noncomputable section

namespace Real
namespace Gamma

theorem le_one_of_mem_Icc {x : ℝ} (hlo : 1 ≤ x) (hhi : x ≤ 2) : Gamma x ≤ 1 := by
  have h_convex := Real.convexOn_Gamma
  have h1 : Gamma 1 = 1 := Gamma_one
  have h2 : Gamma 2 = 1 := Gamma_two
  let t := 2 - x
  have ht_nonneg : 0 ≤ t := by linarith
  have hx_conv : x = t * 1 + (1 - t) * 2 := by field_simp [t]; ring
  have := h_convex.2 (x := (1 : ℝ)) (y := (2 : ℝ)) (by norm_num) (by norm_num)
    ht_nonneg (by linarith : 0 ≤ 1 - t) (by ring : t + (1 - t) = 1)
  rw [smul_eq_mul, smul_eq_mul] at this
  calc
    Gamma x = Gamma (t * 1 + (1 - t) * 2) := by rw [hx_conv]
    _ ≤ t * Gamma 1 + (1 - t) * Gamma 2 := this
    _ = 1 := by rw [h1, h2]; ring

end Gamma
end Real

namespace Complex
namespace Gamma

theorem norm_le_Gamma_re {z : ℂ} (hz : 0 < z.re) : ‖Gamma z‖ ≤ Real.Gamma z.re := by
  rw [Gamma_eq_integral hz, Real.Gamma_eq_integral hz]
  have h_norm_eq : ∀ t ∈ Set.Ioi (0 : ℝ),
      ‖((-t).exp : ℂ) * (t : ℂ) ^ (z - 1)‖ = Real.exp (-t) * t ^ (z.re - 1) := by
    intro t ht
    have hcpow : ‖(t : ℂ) ^ (z - 1)‖ = t ^ (z.re - 1) := by
      simpa using norm_cpow_eq_rpow_re_of_pos ht (z - 1)
    simp [norm_exp, hcpow]
  calc
    ‖GammaIntegral z‖
        ≤ ∫ t in Set.Ioi (0 : ℝ), ‖((-t).exp : ℂ) * (t : ℂ) ^ (z - 1)‖ := by
          unfold GammaIntegral
          exact norm_integral_le_integral_norm _
    _ = ∫ t in Set.Ioi (0 : ℝ), Real.exp (-t) * t ^ (z.re - 1) := by
          exact setIntegral_congr_fun measurableSet_Ioi h_norm_eq

theorem norm_le_one {z : ℂ} (hlo : 1 ≤ z.re) (hhi : z.re ≤ 2) : ‖Gamma z‖ ≤ 1 := by
  have hz_pos : 0 < z.re := by linarith
  calc
    ‖Gamma z‖ ≤ Real.Gamma z.re := norm_le_Gamma_re hz_pos
    _ ≤ 1 := Real.Gamma.le_one_of_mem_Icc hlo hhi

theorem norm_sq_le_Gamma_re_sq {z : ℂ} (hz : 0 < z.re) :
    ‖Gamma z‖ ^ 2 ≤ (Real.Gamma z.re) ^ 2 := by
  have h := norm_le_Gamma_re hz
  have hΓ : 0 ≤ Real.Gamma z.re := (Real.Gamma_pos_of_pos hz).le
  simpa [pow_two] using mul_le_mul h h (norm_nonneg _) hΓ

theorem norm_sq_le_norm_sq_Gamma_re {z : ℂ} (hz : 1 / 2 ≤ z.re) :
    ‖Gamma z‖ ^ 2 ≤ ‖Gamma z.re‖ ^ 2 := by
  have hz_pos : 0 < z.re := by linarith
  have h := norm_sq_le_Gamma_re_sq hz_pos
  have habs : ‖Gamma (z.re : ℂ)‖ = Real.Gamma z.re := by
    rw [Gamma_ofReal z.re, norm_real]
    exact abs_of_pos (Real.Gamma_pos_of_pos hz_pos)
  rw [habs]
  exact h

end Gamma
end Complex

end
end
end File45

-- Upstream module PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.GammaBounds
section File46
 

section
noncomputable section

open Complex Real Set Metric
open Real Set MeasureTheory Filter Asymptotics
open scoped Real Topology

namespace Real
namespace Gamma

private lemma le_Gamma_one_half {a : ℝ} (ha_low : 1 / 2 ≤ a) (ha_high : a ≤ 1) :
    Real.Gamma a ≤ Real.Gamma (1 / 2) := by
  have h_convex := Real.convexOn_Gamma
  have h1 : Real.Gamma 1 = 1 := Real.Gamma_one
  have h_half : Real.Gamma (1 / 2) = Real.sqrt Real.pi := Real.Gamma_one_half_eq
  have h_sqrt_pi_gt_one : 1 < Real.sqrt Real.pi := by
    rw [← Real.sqrt_one, Real.sqrt_lt_sqrt_iff (by aesop)]
    exact (by norm_num : (1 : ℝ) < 3).trans Real.pi_gt_three
  let t := 2 - 2 * a
  have ht_nonneg : 0 ≤ t := by linarith
  have ht_le_one : t ≤ 1 := by linarith
  have ha_conv : a = t * (1 / 2) + (1 - t) * 1 := by
    field_simp [t]
    ring
  have hconv := h_convex.2 (x := (1/2 : ℝ)) (y := (1 : ℝ)) (by norm_num) (by norm_num)
    ht_nonneg (by linarith : 0 ≤ 1 - t) (by linarith : t + (1 - t) = 1)
  rw [smul_eq_mul, smul_eq_mul] at hconv
  calc
    Real.Gamma a = Real.Gamma (t * (1 / 2) + (1 - t) * 1) := by rw [ha_conv]
    _ ≤ t * Real.Gamma (1 / 2) + (1 - t) * Real.Gamma 1 := hconv
    _ = t * Real.Gamma (1 / 2) + (1 - t) * 1 := by rw [h1]
    _ ≤ t * Real.Gamma (1 / 2) + (1 - t) * Real.Gamma (1 / 2) := by
      have hone : 1 ≤ Real.Gamma (1 / 2) := by
        rw [h_half]
        exact le_of_lt h_sqrt_pi_gt_one
      simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left
          (mul_le_mul_of_nonneg_left hone (sub_nonneg_of_le ht_le_one))
          (t * Real.Gamma (1 / 2))
    _ = Real.Gamma (1 / 2) := by ring

end Gamma
end Real

open Gamma Real

private lemma integral_exp_neg_rpow_Ioi_one_le {a : ℝ}
    (ha_low : (1 / 2 : ℝ) ≤ a) (ha_high : a ≤ 1) :
    ∫ t in Ioi 1, Real.exp (-t) * t ^ (a - 1) ≤ Real.sqrt Real.pi := by
  have h_split :
      (∫ x in Ioi 0, Real.exp (-x) * x ^ (a - 1) ∂volume) =
        (∫ x in Ioc 0 1, Real.exp (-x) * x ^ (a - 1) ∂volume) +
        (∫ x in Ioi 1, Real.exp (-x) * x ^ (a - 1) ∂volume) := by
    have h_int_Ioc :
        IntegrableOn (fun t ↦ Real.exp (-t) * t ^ (a - 1)) (Ioc 0 1) :=
      (Real.GammaIntegral_convergent (by linarith : 0 < a)).mono_set Ioc_subset_Ioi_self
    have h_int_Ioi :
        IntegrableOn (fun t ↦ Real.exp (-t) * t ^ (a - 1)) (Ioi 1) :=
      (Real.GammaIntegral_convergent (by linarith : 0 < a)).mono_set (by
        intro x hx
        exact lt_trans (by norm_num : (0 : ℝ) < 1) hx)
    simpa [Ioc_union_Ioi_eq_Ioi zero_le_one] using
      (MeasureTheory.setIntegral_union
          (Ioc_disjoint_Ioi_same (a := (0 : ℝ)) (b := 1))
          measurableSet_Ioi h_int_Ioc h_int_Ioi)
  have h_nonneg :
      (0 : ℝ) ≤ ∫ x in Ioc 0 1, Real.exp (-x) * x ^ (a - 1) := by
    refine MeasureTheory.setIntegral_nonneg measurableSet_Ioc ?_
    intro t ht
    exact mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (le_of_lt ht.1) _)
  have h_step₁ :
      (∫ x in Ioi 1, Real.exp (-x) * x ^ (a - 1))
        ≤ (∫ x in Ioi 1, Real.exp (-x) * x ^ (a - 1)) +
          (∫ x in Ioc 0 1, Real.exp (-x) * x ^ (a - 1)) := by
    exact le_add_of_nonneg_right h_nonneg
  have h_step₂ :
      (∫ x in Ioi 1, Real.exp (-x) * x ^ (a - 1)) +
        (∫ x in Ioc 0 1, Real.exp (-x) * x ^ (a - 1)) =
        ∫ x in Ioi 0, Real.exp (-x) * x ^ (a - 1) := by
    simpa [add_comm] using h_split.symm
  have h_step₃ :
      (∫ x in Ioi 0, Real.exp (-x) * x ^ (a - 1)) = Real.Gamma a := by
    simpa using (Real.Gamma_eq_integral (by linarith : 0 < a)).symm
  have h_le_Gamma :
      (∫ x in Ioi 1, Real.exp (-x) * x ^ (a - 1)) ≤ Real.Gamma a := by
    have := h_step₁
    simpa [h_step₂, h_step₃] using this
  have h_tail :
      (∫ x in Ioi 1, Real.exp (-x) * x ^ (a - 1)) ≤ Real.Gamma (1 / 2) :=
    h_le_Gamma.trans (Gamma.le_Gamma_one_half ha_low ha_high)
  have hGammaHalf : Real.Gamma (1 / 2) = Real.sqrt Real.pi := Real.Gamma_one_half_eq
  have hGammaInv : Real.Gamma (2⁻¹) = Real.sqrt Real.pi := by
    simp_rw [inv_eq_one_div]
    aesop
  simpa [hGammaHalf, hGammaInv] using h_tail

private lemma integral_rpow_Ioc_zero_one {s : ℝ} (hs : 0 < s) :
    ∫ t in Ioc (0 : ℝ) 1, t ^ (s - 1) = 1 / s := by
  have h_eq : ∫ t in Ioc (0 : ℝ) 1, t ^ (s - 1) = ∫ t in (0)..(1), t ^ (s - 1) := by
    rw [intervalIntegral.intervalIntegral_eq_integral_uIoc]
    simp
  rw [h_eq]
  have hne : s - 1 ≠ -1 := by linarith
  have hlt : -1 < s - 1 := by linarith
  have h := (integral_rpow (a := (0 : ℝ)) (b := (1 : ℝ)) (h := Or.inl hlt))
  simp [one_rpow, zero_rpow hs.ne'] at h
  simp only [one_div, h]

namespace Complex
namespace Gamma

lemma norm_le_one_div_add_sqrt_pi_of_re_ge_of_re_le {w : ℂ} {a : ℝ}
    (ha_pos : 0 < a) (hw : a ≤ w.re) (hw_ub : w.re ≤ 1) :
    ‖Complex.Gamma w‖ ≤ 1 / a + Real.sqrt Real.pi := by
  set f : ℝ → ℂ := fun t ↦ Complex.exp (-t) * t ^ (w - 1)
  set g : ℝ → ℝ := fun t ↦ Real.exp (-t) * t ^ (w.re - 1)
  have hw_pos : 0 < w.re := ha_pos.trans_le hw
  have hΓ : Complex.Gamma w = ∫ t in Ioi (0 : ℝ), f t := by
    rw [Complex.Gamma_eq_integral hw_pos]
    simp [Complex.GammaIntegral, f]
  have h_norm :
      ‖Complex.Gamma w‖ =
        ‖∫ t in Ioi (0 : ℝ), f t‖ := by
    simp [hΓ]
  have h_le_int :
      ‖∫ t in Ioi (0 : ℝ), f t‖
        ≤ ∫ t in Ioi (0 : ℝ), ‖f t‖ :=
    MeasureTheory.norm_integral_le_integral_norm _
  have h_int_real :
      ∫ t in Ioi (0 : ℝ), ‖f t‖
        = ∫ t in Ioi (0 : ℝ), g t := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
    intro t ht
    simp [f, g, Complex.norm_exp, Complex.norm_cpow_eq_rpow_re_of_pos ht (w - 1)]
  have h_split :
      (∫ t in Ioi (0 : ℝ), g t)
        = (∫ t in Ioc 0 1, g t) + (∫ t in Ioi 1, g t) := by
    have hIoc : IntegrableOn g (Ioc 0 1) :=
      (Real.GammaIntegral_convergent hw_pos).mono_set Ioc_subset_Ioi_self
    have hIoi : IntegrableOn g (Ioi 1) :=
      (Real.GammaIntegral_convergent hw_pos).mono_set
        (fun t ht => mem_Ioi.mpr (lt_trans zero_lt_one (mem_Ioi.mp ht)))
    simpa [Ioc_union_Ioi_eq_Ioi zero_le_one] using
      (MeasureTheory.setIntegral_union
          (Ioc_disjoint_Ioi_same (a := 0) (b := 1))
          measurableSet_Ioi hIoc hIoi)
  have h_ae_drop :
      (fun t : ℝ ↦ g t) ≤ᵐ[volume.restrict (Ioc 0 1)]
        (fun t : ℝ ↦ t ^ (w.re - 1)) := by
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall ?_)
    intro t ht
    have h_exp : Real.exp (-t) ≤ 1 := by
      have : (-t : ℝ) ≤ 0 := by linarith [ht.1]
      exact exp_le_one_iff.mpr this
    have h_nonneg : (0 : ℝ) ≤ t ^ (w.re - 1) :=
      Real.rpow_nonneg (le_of_lt ht.1) _
    simpa [g] using mul_le_of_le_one_left h_nonneg h_exp
  have hIoc₁ : IntegrableOn g (Ioc 0 1) :=
    (Real.GammaIntegral_convergent hw_pos).mono_set Ioc_subset_Ioi_self
  have hIoc₂ : IntegrableOn (fun t : ℝ ↦ t ^ (w.re - 1)) (Ioc 0 1) := by
    have hInt :
        IntervalIntegrable (fun t : ℝ ↦ t ^ (w.re - 1)) volume 0 1 := by
      simpa using
        intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < w.re - 1)
    simpa using
      (intervalIntegrable_iff_integrableOn_Ioc_of_le
          (a := 0) (b := 1) zero_le_one).1 hInt
  have h_drop_exp :
      (∫ t in Ioc 0 1, g t)
        ≤ ∫ t in Ioc 0 1, t ^ (w.re - 1) :=
    MeasureTheory.setIntegral_mono_ae_restrict hIoc₁ hIoc₂ h_ae_drop
  have h_big :
      ‖Complex.Gamma w‖
        ≤ (∫ t in Ioc 0 1, t ^ (w.re - 1)) + (∫ t in Ioi 1, g t) := by
    have step1 : ‖∫ t in Ioi (0 : ℝ), f t‖
        ≤ (∫ t in Ioc 0 1, g t) + (∫ t in Ioi 1, g t) := by
      simpa [h_int_real, h_split] using h_le_int
    have step2 : (∫ t in Ioc 0 1, g t) + (∫ t in Ioi 1, g t)
        ≤ (∫ t in Ioc 0 1, t ^ (w.re - 1)) + (∫ t in Ioi 1, g t) :=
      by linarith only [h_drop_exp]
    simpa [h_norm] using (le_trans step1 step2)
  have h_Ioc_exact :
      ∫ t in Ioc 0 1, t ^ (w.re - 1) = 1 / w.re :=
    integral_rpow_Ioc_zero_one hw_pos
  have h_tail :
      ∫ t in Ioi 1, g t ≤ Real.sqrt Real.pi := by
    by_cases hhalf : (1 / 2 : ℝ) ≤ w.re
    · have := integral_exp_neg_rpow_Ioi_one_le hhalf hw_ub
      simpa [g] using this
    · have h_ae :
          (fun t : ℝ ↦ g t) ≤ᵐ[volume.restrict (Ioi 1)]
            (fun t : ℝ ↦ Real.exp (-t) * t ^ ((1 / 2 : ℝ) - 1)) := by
        refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall ?_)
        intro t ht
        have ht1 : (1 : ℝ) ≤ t := le_of_lt ht
        have hpow : t ^ (w.re - 1) ≤ t ^ ((1 / 2 : ℝ) - 1) := by
          have : w.re - 1 ≤ (1 / 2 : ℝ) - 1 := by linarith [hhalf]
          exact Real.rpow_le_rpow_of_exponent_le ht1 this
        have hnonneg : (0 : ℝ) ≤ Real.exp (-t) := (Real.exp_pos _).le
        simpa [g] using mul_le_mul_of_nonneg_left hpow hnonneg
      have hIntL : IntegrableOn g (Ioi 1) :=
        (Real.GammaIntegral_convergent hw_pos).mono_set
          (fun x hx => mem_Ioi.mpr (lt_trans zero_lt_one (mem_Ioi.mp hx)))
      have hIntR : IntegrableOn
            (fun t : ℝ ↦ Real.exp (-t) * t ^ ((1 / 2 : ℝ) - 1)) (Ioi 1) :=
        (Real.GammaIntegral_convergent (by norm_num : 0 < (1 / 2 : ℝ))).mono_set
          (fun x hx => mem_Ioi.mpr (lt_trans zero_lt_one (mem_Ioi.mp hx)))
      have h_le : ∫ t in Ioi 1, g t
            ≤ ∫ t in Ioi 1, Real.exp (-t) * t ^ ((1 / 2 : ℝ) - 1) :=
        MeasureTheory.setIntegral_mono_ae_restrict hIntL hIntR h_ae
      have h_upper :
          ∫ t in Ioi 1, Real.exp (-t) * t ^ ((1 / 2 : ℝ) - 1)
            ≤ Real.sqrt Real.pi := by
        have := integral_exp_neg_rpow_Ioi_one_le
                  (by norm_num : (1 / 2 : ℝ) ≤ 1 / 2)
                  (by norm_num : (1 / 2 : ℝ) ≤ (1 : ℝ))
        simpa using this
      exact h_le.trans h_upper
  have h_main :
      ‖Complex.Gamma w‖ ≤ 1 / w.re + Real.sqrt Real.pi := by
    calc
      ‖Complex.Gamma w‖
          ≤ (∫ t in Ioc 0 1, t ^ (w.re - 1)) + (∫ t in Ioi 1, g t) := h_big
      _ = 1 / w.re + (∫ t in Ioi 1, g t) := by rw [h_Ioc_exact]
      _ ≤ 1 / w.re + Real.sqrt Real.pi := by exact add_le_add_right h_tail _
  have h_one_div : (1 / w.re : ℝ) ≤ 1 / a :=
    one_div_le_one_div_of_le ha_pos hw
  have : 1 / w.re + Real.sqrt Real.pi ≤ 1 / a + Real.sqrt Real.pi :=
    by linarith only [h_one_div]
  exact h_main.trans this

end Gamma
end Complex

end
end
end File46

-- Upstream module PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Gamma.GammaStirlingAux
section File47
 

section
open Complex
open scoped Topology BigOperators

namespace Stirling.GammaAux

lemma norm_sub_real_le {s : ℂ} {a : ℝ} (ha_pos : 0 < a) (ha_lt : a < s.re) : ‖s - a‖ ≤ ‖s‖ := by
  have h_sq : (s.re - a) ^ 2 ≤ s.re ^ 2 := by nlinarith
  have h1 : Complex.normSq (s - a) ≤ Complex.normSq s := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.ofReal_re,
               Complex.sub_im, Complex.ofReal_im, sub_zero]
    linarith [sq_nonneg s.im]
  calc
    ‖s - a‖ = Real.sqrt (Complex.normSq (s - a)) := by
      rw [Complex.normSq_eq_norm_sq, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
    _ ≤ Real.sqrt (Complex.normSq s) := Real.sqrt_le_sqrt h1
    _ = ‖s‖ := by
      rw [Complex.normSq_eq_norm_sq, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]

lemma norm_shift_le {s : ℂ} {k : ℕ} (hk : (k : ℝ) + 1 < s.re) : ‖s - 1 - k‖ ≤ ‖s‖ := by
  have ha_pos : (0 : ℝ) < 1 + k := by linarith
  have ha_lt : (1 : ℝ) + k < s.re := by linarith
  simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
    norm_sub_real_le (s := s) (a := (1 + k : ℝ)) ha_pos ha_lt

lemma prod_norm_le_pow {s : ℂ} {m : ℕ} (h : ∀ k < m, (k : ℝ) + 1 < s.re) :
    ‖∏ k ∈ Finset.range m, (s - 1 - k)‖ ≤ ‖s‖ ^ m := by
  calc ‖∏ k ∈ Finset.range m, (s - 1 - k)‖
      = ∏ k ∈ Finset.range m, ‖s - 1 - k‖ := norm_prod _ _
    _ ≤ ∏ _k ∈ Finset.range m, ‖s‖ := by
        apply Finset.prod_le_prod₀ (fun k _ => norm_nonneg _)
        intro k hk; exact norm_shift_le (h k (Finset.mem_range.mp hk))
    _ = ‖s‖ ^ m := by rw [Finset.prod_const, Finset.card_range]

lemma Gamma_iterate {s : ℂ} {n : ℕ} (hs : ∀ k < n, s - 1 - k ≠ 0) :
    Complex.Gamma s = Complex.Gamma (s - n) * ∏ k ∈ Finset.range n, (s - 1 - k) := by
  induction n with
  | zero => simp
  | succ m ih =>
    have h_prev : ∀ k < m, s - 1 - k ≠ 0 := fun k hk => hs k (Nat.lt_succ_of_lt hk)
    have h_curr : s - 1 - m ≠ 0 := hs m (Nat.lt_succ_self m)
    have h_func : Complex.Gamma (s - m) = (s - m - 1) * Complex.Gamma (s - m - 1) := by
      have h_ne : s - ↑m - 1 ≠ 0 := by convert h_curr using 1; ring
      have := Complex.Gamma_add_one (s - m - 1) h_ne
      simp only [sub_add_cancel] at this
      exact this
    have h_cast : s - ↑(m + 1) = s - m - 1 := by simp only [Nat.cast_add, Nat.cast_one]; ring
    have h_prod_eq : (s - m - 1) * ∏ k ∈ Finset.range m, (s - 1 - k) =
        ∏ k ∈ Finset.range (m + 1), (s - 1 - k) := by
      rw [Finset.prod_range_succ]; ring
    calc
      Complex.Gamma s
          = Complex.Gamma (s - m) * ∏ k ∈ Finset.range m, (s - 1 - k) := ih h_prev
      _ = (s - m - 1) * Complex.Gamma (s - m - 1)
            * ∏ k ∈ Finset.range m, (s - 1 - k) := by
          rw [h_func]
      _ = Complex.Gamma (s - m - 1) *
            ((s - m - 1) * ∏ k ∈ Finset.range m, (s - 1 - k)) := by
          ring
      _ = Complex.Gamma (s - m - 1) * ∏ k ∈ Finset.range (m + 1), (s - 1 - k) := by
          rw [h_prod_eq]
      _ = Complex.Gamma (s - ↑(m + 1)) * ∏ k ∈ Finset.range (m + 1), (s - 1 - k) := by
          rw [← h_cast]

end Stirling.GammaAux
end
end File47

-- Upstream module PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Gamma.StripBounds
section File48
 

section
noncomputable section

open Complex Real Set Metric

namespace Real.Stirling

lemma log_one_add_ge_log_two {x : ℝ} (hx : 1 ≤ x) :
    Real.log 2 ≤ Real.log (1 + x) := by
  have h₂ : (0 : ℝ) < 2 := by norm_num
  have hle : (2 : ℝ) ≤ 1 + x := by linarith
  exact Real.log_le_log h₂ hle

lemma log_one_add_pos {x : ℝ} (hx : 1 ≤ x) :
    0 < Real.log (1 + x) := Real.log_pos (by linarith)

lemma sqrt_pi_lt_two : Real.sqrt Real.pi < 2 := by
  have hπ4 : Real.pi < 4 := Real.pi_lt_four
  have h4 : Real.sqrt (4 : ℝ) = (2 : ℝ) := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (2 : ℝ) ≥ 0)]
  calc Real.sqrt Real.pi < Real.sqrt 4 := Real.sqrt_lt_sqrt Real.pi_pos.le hπ4
    _ = 2 := h4

lemma log_two_le_mul_log_one_add {x : ℝ} (hx : 1 ≤ x) :
    Real.log 2 ≤ x * Real.log (1 + x) := by
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hlog2_le := log_one_add_ge_log_two hx
  have hx_mul : x * Real.log 2 ≤ x * Real.log (1 + x) :=
    mul_le_mul_of_nonneg_left hlog2_le (by linarith)
  have hx_ge : Real.log 2 ≤ x * Real.log 2 := by
    simpa [one_mul] using mul_le_mul_of_nonneg_right hx hlog2_pos.le
  exact le_trans hx_ge hx_mul

lemma log_three_le_coef_mul_log_one_add {x : ℝ} (hx : 1 ≤ x) :
    Real.log 3 ≤ (Real.log 3 / Real.log 2) * Real.log (1 + x) := by
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hlog2_ne : Real.log 2 ≠ 0 := ne_of_gt hlog2_pos
  have hlog3_pos : 0 < Real.log 3 := Real.log_pos (by norm_num : (1 : ℝ) < 3)
  have hcoef_nonneg : 0 ≤ Real.log 3 / Real.log 2 := div_nonneg hlog3_pos.le hlog2_pos.le
  have hscaled :
      (Real.log 3 / Real.log 2) * Real.log 2 ≤
        (Real.log 3 / Real.log 2) * Real.log (1 + x) :=
    mul_le_mul_of_nonneg_left (log_one_add_ge_log_two hx) hcoef_nonneg
  simpa [div_mul_cancel₀ _ hlog2_ne] using hscaled

noncomputable def half_shift_log_constant : ℝ :=
  (3 / 2 : ℝ) * (Real.log 3 / Real.log 2 + 1)

lemma half_shift_log_constant_pos : 0 < half_shift_log_constant := by
  have hthree : 0 < (3 / 2 : ℝ) := by norm_num
  have hcoef : 0 < Real.log 3 / Real.log 2 + 1 := by
    have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    have hlog3_pos : 0 < Real.log 3 := Real.log_pos (by norm_num : (1 : ℝ) < 3)
    have hcoef_nonneg : 0 ≤ Real.log 3 / Real.log 2 :=
      div_nonneg hlog3_pos.le hlog2_pos.le
    linarith
  simpa [half_shift_log_constant] using mul_pos hthree hcoef

end Real.Stirling

namespace Complex.Gamma

open Real

lemma norm_add_one_le_two_mul_norm {s : ℂ} (hs : 1 ≤ ‖s‖) :
    ‖s + 1‖ ≤ 2 * ‖s‖ := by
  have h1 : ‖s + 1‖ ≤ ‖s‖ + 1 := by simpa using norm_add_le s (1 : ℂ)
  nlinarith [h1, hs]

lemma norm_div_two_add_one_le_three_halves_mul {s : ℂ} (hs : 1 ≤ ‖s‖) :
    ‖s / 2 + 1‖ ≤ (3 / 2) * ‖s‖ := by
  have h1 : ‖s / 2 + 1‖ ≤ ‖s / 2‖ + 1 := by simpa using norm_add_le (s / 2) (1 : ℂ)
  have h1' : ‖s / 2 + 1‖ ≤ ‖s‖ / 2 + 1 := by simpa using h1
  nlinarith [h1', hs]

lemma log_one_add_norm_add_one_le {s : ℂ} (hs : 1 ≤ ‖s‖) :
    Real.log (1 + ‖s + 1‖) ≤ Real.log 2 + Real.log (1 + ‖s‖) := by
  have hpos : 0 < (1 + ‖s + 1‖ : ℝ) := by linarith [norm_nonneg (s + 1)]
  have hle : (1 + ‖s + 1‖ : ℝ) ≤ 2 * (1 + ‖s‖) := by
    have hn : ‖s + 1‖ ≤ ‖s‖ + 1 := by simpa using norm_add_le s (1 : ℂ)
    nlinarith [hn, hs]
  have hlog' : Real.log (1 + ‖s + 1‖) ≤ Real.log (2 * (1 + ‖s‖)) :=
    Real.log_le_log hpos (by linarith)
  have hmul : Real.log (2 * (1 + ‖s‖)) = Real.log 2 + Real.log (1 + ‖s‖) := by
    have h2 : (2 : ℝ) ≠ 0 := by norm_num
    have h1 : (1 + ‖s‖ : ℝ) ≠ 0 := by linarith [norm_nonneg s]
    simpa [mul_assoc] using Real.log_mul h2 h1
  simpa [hmul] using hlog'

lemma log_one_add_norm_div_two_add_one_le {s : ℂ} (hs : 1 ≤ ‖s‖) :
    Real.log (1 + ‖s / 2 + 1‖) ≤ Real.log 3 + Real.log (1 + ‖s‖) := by
  have hpos : 0 < (1 + ‖s / 2 + 1‖ : ℝ) := by linarith [norm_nonneg (s / 2 + 1)]
  have hle : (1 + ‖s / 2 + 1‖ : ℝ) ≤ 3 * (1 + ‖s‖) := by
    nlinarith [norm_div_two_add_one_le_three_halves_mul hs]
  have hlog' : Real.log (1 + ‖s / 2 + 1‖) ≤ Real.log (3 * (1 + ‖s‖)) :=
    Real.log_le_log hpos (by linarith)
  have hmul : Real.log (3 * (1 + ‖s‖)) = Real.log 3 + Real.log (1 + ‖s‖) := by
    have h3 : (3 : ℝ) ≠ 0 := by norm_num
    have h1 : (1 + ‖s‖ : ℝ) ≠ 0 := by linarith [norm_nonneg s]
    simpa [mul_assoc] using Real.log_mul h3 h1
  simpa [hmul] using hlog'

lemma norm_mul_log_shift_add_one_bound {s : ℂ} (hs : 1 ≤ ‖s‖) :
    ‖s + 1‖ * Real.log (1 + ‖s + 1‖) ≤ 4 * (‖s‖ * Real.log (1 + ‖s‖)) := by
  have hlog2_le := Real.Stirling.log_one_add_ge_log_two hs
  have hlog_add_le : Real.log (1 + ‖s + 1‖) ≤ 2 * Real.log (1 + ‖s‖) := by
    nlinarith [log_one_add_norm_add_one_le hs, hlog2_le]
  have hlog_nonneg : 0 ≤ Real.log (1 + ‖s + 1‖) :=
    Real.log_nonneg (by linarith [norm_nonneg (s + 1)])
  calc
    ‖s + 1‖ * Real.log (1 + ‖s + 1‖)
        ≤ (2 * ‖s‖) * Real.log (1 + ‖s + 1‖) :=
          mul_le_mul_of_nonneg_right (norm_add_one_le_two_mul_norm hs) hlog_nonneg
    _ ≤ (2 * ‖s‖) * (2 * Real.log (1 + ‖s‖)) :=
          mul_le_mul_of_nonneg_left hlog_add_le (by positivity)
    _ = 4 * (‖s‖ * Real.log (1 + ‖s‖)) := by ring

lemma norm_mul_log_shift_half_bound {s : ℂ} (hs : 1 ≤ ‖s‖) :
    ‖s / 2 + 1‖ * Real.log (1 + ‖s / 2 + 1‖) ≤
      Real.Stirling.half_shift_log_constant * (‖s‖ * Real.log (1 + ‖s‖)) := by
  have hlog_nonneg : 0 ≤ Real.log (1 + ‖s / 2 + 1‖) :=
    Real.log_nonneg (by linarith [norm_nonneg (s / 2 + 1)])
  have hlog_w' :
      Real.log (1 + ‖s / 2 + 1‖) ≤
        (Real.log 3 / Real.log 2 + 1) * Real.log (1 + ‖s‖) := by
    nlinarith [log_one_add_norm_div_two_add_one_le hs,
      Real.Stirling.log_three_le_coef_mul_log_one_add hs]
  calc
    ‖s / 2 + 1‖ * Real.log (1 + ‖s / 2 + 1‖)
        ≤ ((3 / 2 : ℝ) * ‖s‖) * Real.log (1 + ‖s / 2 + 1‖) :=
          mul_le_mul_of_nonneg_right (norm_div_two_add_one_le_three_halves_mul hs) hlog_nonneg
    _ ≤ Real.Stirling.half_shift_log_constant * (‖s‖ * Real.log (1 + ‖s‖)) := by
      have hstep2 :
          ((3 / 2 : ℝ) * ‖s‖) * Real.log (1 + ‖s / 2 + 1‖) ≤
            ((3 / 2 : ℝ) * ‖s‖) * ((Real.log 3 / Real.log 2 + 1) * Real.log (1 + ‖s‖)) :=
        mul_le_mul_of_nonneg_left hlog_w' (by positivity)
      have hEq :
          ((3 / 2 : ℝ) * ‖s‖) * ((Real.log 3 / Real.log 2 + 1) * Real.log (1 + ‖s‖)) =
            Real.Stirling.half_shift_log_constant * (‖s‖ * Real.log (1 + ‖s‖)) := by
        simp [Real.Stirling.half_shift_log_constant, mul_assoc, mul_left_comm, mul_comm]
      exact le_trans hstep2 (by simp [hEq])

lemma norm_Gamma_le_two_mul_norm_Gamma_add_one {z : ℂ} (hz : z ≠ 0) (hz_lb : (1 / 2 : ℝ) ≤ ‖z‖) :
    ‖Gamma z‖ ≤ 2 * ‖Gamma (z + 1)‖ := by
  have hfunc := Gamma_add_one z hz
  have hnorm_mul : ‖Gamma (z + 1)‖ = ‖z‖ * ‖Gamma z‖ := by
    calc
      ‖Gamma (z + 1)‖ = ‖z * Gamma z‖ := by simp [hfunc]
      _ = ‖z‖ * ‖Gamma z‖ := by simp
  have hz_pos : 0 < ‖z‖ := lt_of_lt_of_le (by norm_num) hz_lb
  have hz_ne : ‖z‖ ≠ 0 := ne_of_gt hz_pos
  have h_inv : 1 / ‖z‖ ≤ (2 : ℝ) := by
    have hhalf_pos : (0 : ℝ) < (1 / 2 : ℝ) := by norm_num
    simpa using one_div_le_one_div_of_le hhalf_pos hz_lb
  have : ‖Gamma z‖ = ‖Gamma (z + 1)‖ / ‖z‖ := by
    calc
      ‖Gamma z‖ = (‖z‖ * ‖Gamma z‖) / ‖z‖ := by field_simp [hz_ne]
      _ = ‖Gamma (z + 1)‖ / ‖z‖ := by simp [hnorm_mul]
  rw [this, div_eq_mul_inv]
  have :
      (‖Gamma (z + 1)‖ : ℝ) * (1 / ‖z‖) ≤ ‖Gamma (z + 1)‖ * 2 :=
    mul_le_mul_of_nonneg_left h_inv (norm_nonneg _)
  simpa [mul_assoc, mul_left_comm, mul_comm] using this

lemma norm_bounded_on_compact_of_no_poles {K : Set ℂ}
    (hK : IsCompact K)
    (h_poles : ∀ s ∈ K, ∀ n : ℕ, s ≠ -n) :
    ∃ M : ℝ, ∀ s ∈ K, ‖Gamma s‖ ≤ M := by
  have h_cont : ContinuousOn Gamma K := by
    refine continuousOn_of_forall_continuousAt ?_
    intro s hs
    exact (differentiableAt_Gamma s (h_poles s hs)).continuousAt
  rcases hK.exists_bound_of_continuousOn h_cont with ⟨M, hM⟩
  exact ⟨M, fun s hs => hM s hs⟩

theorem norm_le_strip {w : ℂ} {a : ℝ}
    (ha : 0 < a) (hw_lo : a ≤ w.re) (hw_hi : w.re ≤ 1) :
    ‖Gamma w‖ ≤ 1 / a + Real.sqrt Real.pi :=
  Complex.Gamma.norm_le_one_div_add_sqrt_pi_of_re_ge_of_re_le ha hw_lo hw_hi

lemma norm_le_four_of_re_half_to_one {w : ℂ}
    (hw_lo : (1 / 2 : ℝ) ≤ w.re) (hw_hi : w.re ≤ 1) :
    ‖Gamma w‖ ≤ 4 := by
  have h := norm_le_strip (w := w) (a := (1 / 2 : ℝ)) (by norm_num) hw_lo hw_hi
  calc ‖Gamma w‖ ≤ 1 / (1 / 2 : ℝ) + Real.sqrt Real.pi := h
    _ = 2 + Real.sqrt Real.pi := by norm_num
    _ ≤ 2 + 2 := by linarith [Real.Stirling.sqrt_pi_lt_two]
    _ = 4 := by norm_num

lemma floor_shift_re_in_strip {s : ℂ} :
    let s' := s - (⌊s.re⌋ : ℂ)
    0 ≤ s'.re ∧ s'.re < 1 := by
  intro s'
  have h₁ : 0 ≤ s.re - (⌊s.re⌋ : ℝ) := sub_nonneg.mpr (Int.floor_le _)
  have h₂ : s.re - (⌊s.re⌋ : ℝ) < 1 := by
    have h := Int.lt_floor_add_one (s.re)
    exact (sub_lt_iff_lt_add).mpr (by simp [add_comm])
  constructor
  · simp [s']
  · simpa [s'] using h₂

theorem norm_bound_re_ge_one :
    ∃ C : ℝ, 0 < C ∧
      ∀ s : ℂ, 1 ≤ s.re →
        ‖Gamma s‖ ≤ C * (1 + ‖s‖) ^ (‖s‖ + 1) := by
  refine ⟨1, by norm_num, ?_⟩
  intro s hs_re
  classical
  by_cases hs_small : s.re < 2
  · 
    have hΓ : ‖Gamma s‖ ≤ 1 := Complex.Gamma.norm_le_one hs_re
      (le_of_lt hs_small)
    have hpow : (1 : ℝ) ≤ (1 + ‖s‖) ^ (‖s‖ + 1) := by
      have hbase : (1 : ℝ) ≤ 1 + ‖s‖ := by linarith [norm_nonneg s]
      have hexp : (0 : ℝ) ≤ ‖s‖ + 1 := by linarith [norm_nonneg s]
      have h := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hbase hexp
      simpa [Real.one_rpow] using h
    simpa [one_mul] using le_trans hΓ hpow
  · 
    have hs_ge_two : 2 ≤ s.re := le_of_not_gt hs_small
    let m : ℕ := ⌊s.re⌋₊ - 1
    have h_floor_ge2 : 2 ≤ ⌊s.re⌋₊ := Nat.le_floor (by exact_mod_cast hs_ge_two)
    have h_floor_le : (⌊s.re⌋₊ : ℝ) ≤ s.re := Nat.floor_le (by linarith : (0 : ℝ) ≤ s.re)
    have h_floor_gt : s.re < (⌊s.re⌋₊ : ℝ) + 1 := by
      simpa using (Nat.lt_floor_add_one s.re)
    have hm_eq : (m : ℝ) = (⌊s.re⌋₊ : ℝ) - 1 := by
      have : (1 : ℕ) ≤ ⌊s.re⌋₊ := by omega
      simp [m, Nat.cast_sub this, Nat.cast_one]
    have hm_pos : 0 < m := by simp [m]; omega
    have h_re_lo : 1 ≤ (s - (m : ℂ)).re := by
      simp [sub_re, hm_eq]
      linarith [h_floor_le]
    have h_re_hi : (s - (m : ℂ)).re < 2 := by
      simp [sub_re, hm_eq]
      linarith [h_floor_gt]
    have h_k_bound : ∀ k < m, (k : ℝ) + 1 < s.re := by
      intro k hk
      calc (k : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast (Nat.lt_iff_add_one_le.mp hk)
        _ = (⌊s.re⌋₊ : ℝ) - 1 := hm_eq
        _ < (⌊s.re⌋₊ : ℝ) := by linarith
        _ ≤ s.re := h_floor_le
    have prod_norm_le_pow :
        ‖∏ k ∈ Finset.range m, (s - 1 - (k : ℂ))‖ ≤ ‖s‖ ^ m := by
      simpa using Stirling.GammaAux.prod_norm_le_pow (s := s) (m := m) h_k_bound
    have Gamma_iterate :
        Gamma s = Gamma (s - (m : ℂ)) * ∏ k ∈ Finset.range m, (s - 1 - (k : ℂ)) := by
      have hs_nonzero : ∀ k < m, s - 1 - (k : ℂ) ≠ 0 := by
        intro k hk hk0
        have : (s - 1 - (k : ℂ)).re = 0 := by simp [hk0]
        have hk' : (k : ℝ) + 1 < s.re := h_k_bound k hk
        simp [Complex.sub_re] at this
        linarith
      simpa using Stirling.GammaAux.Gamma_iterate (s := s) (n := m) hs_nonzero
    have h_gamma_base : ‖Gamma (s - (m : ℂ))‖ ≤ 1 :=
      Complex.Gamma.norm_le_one h_re_lo (le_of_lt h_re_hi)
    have hΓ_le_pow : ‖Gamma s‖ ≤ ‖s‖ ^ m := by
      calc
        ‖Gamma s‖ =
            ‖Gamma (s - (m : ℂ)) * ∏ k ∈ Finset.range m, (s - 1 - (k : ℂ))‖ := by
              simp [Gamma_iterate]
        _ =
            ‖Gamma (s - (m : ℂ))‖ *
              ‖∏ k ∈ Finset.range m, (s - 1 - (k : ℂ))‖ := by
              simp
        _ ≤ 1 * ‖s‖ ^ m :=
            mul_le_mul h_gamma_base prod_norm_le_pow (norm_nonneg _) (by norm_num)
        _ = ‖s‖ ^ m := by ring
    have hm_le_norm : (m : ℝ) ≤ ‖s‖ := by
      have hm_le_floor : m ≤ ⌊s.re⌋₊ := Nat.sub_le _ _
      have hm_le_re : (m : ℝ) ≤ s.re := by
        have h_floor_le' : (⌊s.re⌋₊ : ℝ) ≤ s.re :=
          Nat.floor_le (by linarith : (0 : ℝ) ≤ s.re)
        exact le_trans (by exact_mod_cast hm_le_floor) h_floor_le'
      exact le_trans hm_le_re (Complex.re_le_norm s)
    have hpow_le : ‖s‖ ^ m ≤ (1 + ‖s‖) ^ (‖s‖ + 1) := by
      have hx0 : (0 : ℝ) ≤ ‖s‖ := norm_nonneg _
      have hm0 : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (Nat.cast_nonneg m)
      have hbase_le : ‖s‖ ≤ 1 + ‖s‖ := by linarith [norm_nonneg s]
      have h1 : (‖s‖ : ℝ) ^ m = (‖s‖ : ℝ) ^ (m : ℝ) := by
        simp [Real.rpow_natCast]
      have h2 : (‖s‖ : ℝ) ^ (m : ℝ) ≤ (1 + ‖s‖) ^ (m : ℝ) :=
        Real.rpow_le_rpow hx0 hbase_le hm0
      have hbase1 : (1 : ℝ) ≤ 1 + ‖s‖ := by linarith [norm_nonneg s]
      have hm_le : (m : ℝ) ≤ ‖s‖ + 1 := by linarith [hm_le_norm]
      have h3 : (1 + ‖s‖) ^ (m : ℝ) ≤ (1 + ‖s‖) ^ (‖s‖ + 1) :=
        Real.rpow_le_rpow_of_exponent_le hbase1 hm_le
      calc
        ‖s‖ ^ m = (‖s‖ : ℝ) ^ (m : ℝ) := h1
        _ ≤ (1 + ‖s‖) ^ (m : ℝ) := h2
        _ ≤ (1 + ‖s‖) ^ (‖s‖ + 1) := h3
    have : ‖Gamma s‖ ≤ (1 + ‖s‖) ^ (‖s‖ + 1) := le_trans hΓ_le_pow hpow_le
    simpa [one_mul] using this

theorem stirling_bound_re_ge_zero :
    ∃ C : ℝ, 0 < C ∧
      ∀ s : ℂ, 0 ≤ s.re → 1 ≤ ‖s‖ →
        ‖Gamma s‖ ≤ Real.exp (C * ‖s‖ * Real.log (1 + ‖s‖)) := by
  classical
  rcases norm_bound_re_ge_one with ⟨C₁, hC₁_pos, hC₁⟩
  have hlog2_pos : 0 < Real.log 2 := by
    have : (1 : ℝ) < 2 := by norm_num
    exact Real.log_pos this
  have hlog2_ne : Real.log 2 ≠ 0 := ne_of_gt hlog2_pos
  let K : ℝ := |Real.log C₁| + 1
  have hK_pos : 0 < K := by
    have : 0 ≤ |Real.log C₁| := abs_nonneg _
    linarith [K]
  have hC₁_exp : C₁ ≤ Real.exp K := by
    have hlog : Real.log C₁ ≤ |Real.log C₁| + 1 := by
      have : Real.log C₁ ≤ |Real.log C₁| := le_abs_self _
      linarith
    have h := Real.exp_le_exp.mpr hlog
    simpa [K, Real.exp_log hC₁_pos] using h
  let Cbase : ℝ := K / Real.log 2 + 2
  have hCbase_pos : 0 < Cbase := by
    have hK_div_nonneg : 0 ≤ K / Real.log 2 := div_nonneg hK_pos.le hlog2_pos.le
    linarith [Cbase, hK_div_nonneg]
  let C : ℝ := 4 * Cbase
  refine ⟨C, by nlinarith [hCbase_pos], ?_⟩
  have h_re_ge_one :
      ∀ z : ℂ, 1 ≤ z.re →
        ‖Gamma z‖ ≤ Real.exp (Cbase * ‖z‖ * Real.log (1 + ‖z‖)) := by
    intro z hz_re
    have hz_norm : (1 : ℝ) ≤ ‖z‖ := le_trans hz_re (Complex.re_le_norm z)
    have hx_pos : 0 < (1 + ‖z‖ : ℝ) := by linarith [norm_nonneg z]
    have hL_nonneg : 0 ≤ Real.log (1 + ‖z‖) := Real.log_nonneg (by linarith [norm_nonneg z])
    have hlog2_le_log : Real.log 2 ≤ Real.log (1 + ‖z‖) :=
      Real.Stirling.log_one_add_ge_log_two hz_norm
    have hlog2_le : Real.log 2 ≤ ‖z‖ * Real.log (1 + ‖z‖) := by
      have hx_mul : ‖z‖ * Real.log 2 ≤ ‖z‖ * Real.log (1 + ‖z‖) :=
        mul_le_mul_of_nonneg_left hlog2_le_log (by linarith)
      have hx_ge : Real.log 2 ≤ ‖z‖ * Real.log 2 := by
        have := mul_le_mul_of_nonneg_right hz_norm hlog2_pos.le
        simpa [one_mul] using this
      exact le_trans hx_ge hx_mul
    have hcoef_nonneg : 0 ≤ K / Real.log 2 := div_nonneg hK_pos.le hlog2_pos.le
    have hscaled :
        (K / Real.log 2) * Real.log 2 ≤ (K / Real.log 2) * (‖z‖ * Real.log (1 + ‖z‖)) :=
      mul_le_mul_of_nonneg_left hlog2_le hcoef_nonneg
    have hK_le : K ≤ (K / Real.log 2) * (‖z‖ * Real.log (1 + ‖z‖)) := by
      have : (K / Real.log 2) * Real.log 2 = K := by field_simp [hlog2_ne]
      simpa [this] using hscaled
    have hlin :
        Real.log (1 + ‖z‖) * (‖z‖ + 1) ≤
          2 * (‖z‖ * Real.log (1 + ‖z‖)) := by
      have hz_le : ‖z‖ + 1 ≤ 2 * ‖z‖ := by linarith [hz_norm]
      have hmul :
          Real.log (1 + ‖z‖) * (‖z‖ + 1) ≤
            Real.log (1 + ‖z‖) * (2 * ‖z‖) :=
        mul_le_mul_of_nonneg_left hz_le hL_nonneg
      
      simpa [mul_assoc, mul_left_comm, mul_comm, two_mul] using hmul
    
    have hpoly : ‖Gamma z‖ ≤ C₁ * (1 + ‖z‖) ^ (‖z‖ + 1) := hC₁ z hz_re
    have hnonneg_rpow : 0 ≤ (1 + ‖z‖) ^ (‖z‖ + 1) :=
      Real.rpow_nonneg (by linarith [norm_nonneg z]) _
    have hmul :
        C₁ * (1 + ‖z‖) ^ (‖z‖ + 1) ≤
          Real.exp K * (1 + ‖z‖) ^ (‖z‖ + 1) :=
      mul_le_mul_of_nonneg_right hC₁_exp hnonneg_rpow
    have hrpow :
        (1 + ‖z‖) ^ (‖z‖ + 1) =
          Real.exp (Real.log (1 + ‖z‖) * (‖z‖ + 1)) := by
      simp [Real.rpow_def_of_pos hx_pos, mul_comm]
    have hexp1 :
        C₁ * (1 + ‖z‖) ^ (‖z‖ + 1) ≤
          Real.exp (K + Real.log (1 + ‖z‖) * (‖z‖ + 1)) := by
      calc
        C₁ * (1 + ‖z‖) ^ (‖z‖ + 1)
            ≤ Real.exp K * (1 + ‖z‖) ^ (‖z‖ + 1) := hmul
        _ = Real.exp K * Real.exp (Real.log (1 + ‖z‖) * (‖z‖ + 1)) := by simp [hrpow]
        _ = Real.exp (K + Real.log (1 + ‖z‖) * (‖z‖ + 1)) := by
              simp [Real.exp_add]
    have hexp2 :
        Real.exp (K + Real.log (1 + ‖z‖) * (‖z‖ + 1))
          ≤ Real.exp (Cbase * (‖z‖ * Real.log (1 + ‖z‖))) := by
      apply Real.exp_le_exp.mpr
      have hsum :
          K + Real.log (1 + ‖z‖) * (‖z‖ + 1)
            ≤ (K / Real.log 2 + 2) * (‖z‖ * Real.log (1 + ‖z‖)) := by
        
        have hK_term : K ≤ (K / Real.log 2) * (‖z‖ * Real.log (1 + ‖z‖)) := by

          simpa [mul_assoc] using hK_le
        have h2_term :
            Real.log (1 + ‖z‖) * (‖z‖ + 1) ≤ 2 * (‖z‖ * Real.log (1 + ‖z‖)) := hlin
        
        have :
            K + Real.log (1 + ‖z‖) * (‖z‖ + 1) ≤
              (K / Real.log 2) * (‖z‖ * Real.log (1 + ‖z‖)) +
                2 * (‖z‖ * Real.log (1 + ‖z‖)) := by
          nlinarith [hK_term, h2_term]
        
        simpa [Cbase, add_mul, mul_add, two_mul, mul_assoc, mul_left_comm, mul_comm] using this
      simpa [Cbase, mul_assoc] using hsum
    have hexp3 :
        Real.exp (Cbase * (‖z‖ * Real.log (1 + ‖z‖)))
          = Real.exp (Cbase * ‖z‖ * Real.log (1 + ‖z‖)) := by ring_nf
    have : ‖Gamma z‖ ≤ Real.exp (Cbase * ‖z‖ * Real.log (1 + ‖z‖)) :=
      le_trans hpoly (le_trans hexp1 (le_trans hexp2 (by simp [hexp3] )))
    simpa [mul_assoc] using this
  intro s hs_re hs_norm
  have hs0 : s ≠ 0 := (norm_pos_iff).1 (lt_of_lt_of_le (by norm_num) hs_norm)
  by_cases hs_ge_one : 1 ≤ s.re
  · have h1 := h_re_ge_one s hs_ge_one
    
    have hmul_nonneg : 0 ≤ ‖s‖ * Real.log (1 + ‖s‖) := by
      have : 0 ≤ Real.log (1 + ‖s‖) := Real.log_nonneg (by linarith [norm_nonneg s])
      exact mul_nonneg (norm_nonneg _) this
    have hC_le : Cbase * (‖s‖ * Real.log (1 + ‖s‖)) ≤ C * (‖s‖ * Real.log (1 + ‖s‖)) := by
      have : Cbase ≤ C := by simp [C, le_mul_of_one_le_left, hCbase_pos.le]
      exact mul_le_mul_of_nonneg_right this hmul_nonneg
    have h2 : Real.exp (Cbase * ‖s‖ * Real.log (1 + ‖s‖))
        ≤ Real.exp (C * ‖s‖ * Real.log (1 + ‖s‖)) := by
      apply Real.exp_le_exp.mpr
      
      have hleft : Cbase * ‖s‖ * Real.log (1 + ‖s‖) = Cbase * (‖s‖ * Real.log (1 + ‖s‖)) := by ring
      have hright : C * ‖s‖ * Real.log (1 + ‖s‖) = C * (‖s‖ * Real.log (1 + ‖s‖)) := by ring
      
      simpa [hleft, hright] using hC_le
    exact le_trans h1 h2
  · have hs_lt_one : s.re < 1 := lt_of_not_ge hs_ge_one
    
    have hnorm_eq : ‖Gamma s‖ = ‖Gamma (s + 1)‖ / ‖s‖ := by
      have h := Complex.Gamma_add_one s hs0
      have hn : ‖Gamma (s + 1)‖ = ‖s‖ * ‖Gamma s‖ := by
        calc
          ‖Gamma (s + 1)‖ = ‖s * Gamma s‖ := by simp [h]
          _ = ‖s‖ * ‖Gamma s‖ := by simp
      have hs_norm_ne : ‖s‖ ≠ 0 := (norm_ne_zero_iff).2 hs0
      calc
        ‖Gamma s‖ = (‖s‖ * ‖Gamma s‖) / ‖s‖ := by field_simp [hs_norm_ne]
        _ = ‖Gamma (s + 1)‖ / ‖s‖ := by simp [hn]
    have hdiv : ‖Gamma s‖ ≤ ‖Gamma (s + 1)‖ := by
      rw [hnorm_eq]
      exact div_le_self (norm_nonneg _) hs_norm
    have hs1 : (1 : ℝ) ≤ (s + 1).re := by
      
      simp [Complex.add_re]
      linarith [hs_re]
    have hG1 : ‖Gamma (s + 1)‖ ≤ Real.exp (C * ‖s‖ * Real.log (1 + ‖s‖)) := by
      have h0 := h_re_ge_one (s + 1) hs1
      have hshift := norm_mul_log_shift_add_one_bound hs_norm
      have hC_nonneg : 0 ≤ Cbase := le_of_lt hCbase_pos
      have hCshift :
          Cbase * (‖s + 1‖ * Real.log (1 + ‖s + 1‖)) ≤ C * (‖s‖ * Real.log (1 + ‖s‖)) := by
        calc
          Cbase * (‖s + 1‖ * Real.log (1 + ‖s + 1‖))
              ≤ Cbase * (4 * (‖s‖ * Real.log (1 + ‖s‖))) := by
                    exact mul_le_mul_of_nonneg_left hshift hC_nonneg
          _ = C * (‖s‖ * Real.log (1 + ‖s‖)) := by simp [C, mul_assoc, mul_left_comm, mul_comm]
      have h0' :
          Cbase * ‖s + 1‖ * Real.log (1 + ‖s + 1‖) =
            Cbase * (‖s + 1‖ * Real.log (1 + ‖s + 1‖)) := by
        ring
      have h1' :
          C * ‖s‖ * Real.log (1 + ‖s‖) =
            C * (‖s‖ * Real.log (1 + ‖s‖)) := by
        ring
      exact le_trans h0 (by
        apply Real.exp_le_exp.mpr
        simpa [h0', h1'] using hCshift)
    exact le_trans hdiv hG1

theorem half_bound_re_ge_zero :
    ∃ C : ℝ, 0 < C ∧
      ∀ s : ℂ, 0 ≤ s.re → 1 ≤ ‖s‖ →
        ‖Gamma (s / 2)‖ ≤ Real.exp (C * ‖s‖ * Real.log (1 + ‖s‖)) := by
  classical
  rcases stirling_bound_re_ge_zero with ⟨C₀, hC₀_pos, hC₀⟩
  let A : ℝ := Real.Stirling.half_shift_log_constant
  have hA_pos := Real.Stirling.half_shift_log_constant_pos
  let C : ℝ := 1 + C₀ * A
  refine ⟨C, by nlinarith [hC₀_pos, hA_pos], ?_⟩
  intro s hs_re hs_norm
  have hs0 : s ≠ 0 := (norm_pos_iff).1 (lt_of_lt_of_le (by norm_num) hs_norm)
  have hs2_neq : s / 2 ≠ 0 := div_ne_zero hs0 (by norm_num : (2 : ℂ) ≠ 0)
  have hs2_lb : (1 / 2 : ℝ) ≤ ‖s / 2‖ := by
    simpa using (show (1 / 2 : ℝ) ≤ ‖s‖ / 2 by nlinarith)
  have hdiv := norm_Gamma_le_two_mul_norm_Gamma_add_one hs2_neq hs2_lb
  have hz_re : 0 ≤ (s / 2 + 1).re := by simp [Complex.add_re]; linarith
  have hz_norm : (1 : ℝ) ≤ ‖s / 2 + 1‖ := by
    have : (1 : ℝ) ≤ (s / 2 + 1).re := by simp [Complex.add_re]; linarith
    exact le_trans this (Complex.re_le_norm (s / 2 + 1))
  have hΓz :
      ‖Gamma (s / 2 + 1)‖ ≤
        Real.exp (C₀ * ‖s / 2 + 1‖ * Real.log (1 + ‖s / 2 + 1‖)) :=
    hC₀ (s / 2 + 1) hz_re hz_norm
  have hprod_w :
      ‖s / 2 + 1‖ * Real.log (1 + ‖s / 2 + 1‖) ≤ A * (‖s‖ * Real.log (1 + ‖s‖)) := by
    simpa [A] using norm_mul_log_shift_half_bound hs_norm
  have hlog2_le_xlog := Real.Stirling.log_two_le_mul_log_one_add hs_norm
  
  have hmain :
      ‖Gamma (s / 2)‖ ≤ Real.exp (C * ‖s‖ * Real.log (1 + ‖s‖)) := by
    
    have htmp :
        ‖Gamma (s / 2)‖ ≤
          2 * Real.exp (C₀ * ‖s / 2 + 1‖ * Real.log (1 + ‖s / 2 + 1‖)) :=
      le_trans hdiv (mul_le_mul_of_nonneg_left hΓz (by norm_num))

    have htmp' :
        2 * Real.exp (C₀ * ‖s / 2 + 1‖ * Real.log (1 + ‖s / 2 + 1‖))
          = Real.exp (Real.log 2 + C₀ * ‖s / 2 + 1‖ * Real.log (1 + ‖s / 2 + 1‖)) := by
      have htwo : Real.exp (Real.log 2) = (2 : ℝ) := by
        have : (0 : ℝ) < 2 := by norm_num
        simp [Real.exp_log this]
      
      calc
        2 * Real.exp (C₀ * ‖s / 2 + 1‖ * Real.log (1 + ‖s / 2 + 1‖))
            = Real.exp (Real.log 2) *
                Real.exp (C₀ * ‖s / 2 + 1‖ * Real.log (1 + ‖s / 2 + 1‖)) := by
                simp [htwo, mul_assoc]
        _ = Real.exp (Real.log 2 + C₀ * ‖s / 2 + 1‖ * Real.log (1 + ‖s / 2 + 1‖)) := by
              simp [Real.exp_add]
    refine le_trans htmp (by
      
      have hexp_le :
          Real.log 2 + C₀ * ‖s / 2 + 1‖ * Real.log (1 + ‖s / 2 + 1‖)
            ≤ C * (‖s‖ * Real.log (1 + ‖s‖)) := by
        have hC0_nonneg : 0 ≤ C₀ := le_of_lt hC₀_pos
        have hA_term :
            C₀ * ‖s / 2 + 1‖ * Real.log (1 + ‖s / 2 + 1‖) ≤
              (C₀ * A) * (‖s‖ * Real.log (1 + ‖s‖)) := by
          
          have := mul_le_mul_of_nonneg_left hprod_w hC0_nonneg
          
          simpa [mul_assoc, mul_left_comm, mul_comm] using this
        have hlog2_term : Real.log 2 ≤ 1 * (‖s‖ * Real.log (1 + ‖s‖)) := by
          simpa using hlog2_le_xlog
        
        nlinarith [hA_term, hlog2_term, C]
      
      have h_exp :
          Real.exp (Real.log 2 + C₀ * ‖s / 2 + 1‖ * Real.log (1 + ‖s / 2 + 1‖))
            ≤ Real.exp (C * (‖s‖ * Real.log (1 + ‖s‖))) :=
        Real.exp_le_exp.mpr hexp_le
      
      have :
          2 * Real.exp (C₀ * ‖s / 2 + 1‖ * Real.log (1 + ‖s / 2 + 1‖))
            ≤ Real.exp (C * (‖s‖ * Real.log (1 + ‖s‖))) := by
        calc
          2 * Real.exp (C₀ * ‖s / 2 + 1‖ * Real.log (1 + ‖s / 2 + 1‖))
              = Real.exp (Real.log 2 + C₀ * ‖s / 2 + 1‖ * Real.log (1 + ‖s / 2 + 1‖)) := htmp'
          _ ≤ Real.exp (C * (‖s‖ * Real.log (1 + ‖s‖))) := h_exp
      simpa [mul_assoc] using this)
  
  simpa [mul_assoc] using hmain

end Complex.Gamma

namespace Complex.Gammaℝ.Stirling

open Real

lemma norm_cpow_pi_neg_half_le_one {s : ℂ} (hs : 0 ≤ s.re) :
    ‖(Real.pi : ℂ) ^ (-s / 2)‖ ≤ 1 := by
  have hpi_pos : (0 : ℝ) < Real.pi := Real.pi_pos
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hpi_pos]
  have h_re : (-s / 2).re = -s.re / 2 := by simp [Complex.neg_re]
  rw [h_re]
  have h_exp : -s.re / 2 ≤ 0 := by linarith
  have hpi_gt_1 : (1 : ℝ) < Real.pi := by
    calc (1 : ℝ) < 3 := by norm_num
      _ < Real.pi := Real.pi_gt_three
  exact Real.rpow_le_one_of_one_le_of_nonpos (le_of_lt hpi_gt_1) h_exp

lemma norm_cpow_two_mul_pi_neg_le_one {w : ℂ} (hw : 0 ≤ w.re) :
    ‖(2 * π : ℂ) ^ (-w)‖ ≤ 1 := by
  have hbase_pos : (0 : ℝ) < 2 * Real.pi := by nlinarith [Real.pi_pos]
  have hbase : (1 : ℝ) ≤ 2 * Real.pi := by
    have : (1 : ℝ) < 2 * Real.pi := by nlinarith [Real.pi_gt_three, Real.pi_pos]
    exact le_of_lt this
  have hnorm : ‖(2 * π : ℂ) ^ (-w)‖ = (2 * Real.pi) ^ ((-w : ℂ).re) := by
    simpa using Complex.norm_cpow_eq_rpow_re_of_pos (x := 2 * Real.pi) hbase_pos (-w)
  rw [hnorm]
  exact Real.rpow_le_one_of_one_le_of_nonpos hbase (neg_nonpos.mpr hw)

theorem bound_re_ge_zero :
    ∃ C : ℝ, 0 < C ∧
      ∀ s : ℂ, 0 ≤ s.re → 1 ≤ ‖s‖ →
        ‖Complex.Gammaℝ s‖ ≤ Real.exp (C * ‖s‖ * Real.log (1 + ‖s‖)) := by
  obtain ⟨C₁, hC₁_pos, hC₁⟩ := Complex.Gamma.half_bound_re_ge_zero
  refine ⟨C₁ + 2, by linarith, ?_⟩
  intro s hs_re hs_norm
  have hdef : Complex.Gammaℝ s = (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2) := by
    simp [Complex.Gammaℝ_def]
  have hΓ : ‖Complex.Gamma (s / 2)‖ ≤ Real.exp (C₁ * ‖s‖ * Real.log (1 + ‖s‖)) :=
    hC₁ s hs_re hs_norm
  have hpi : ‖(Real.pi : ℂ) ^ (-s / 2)‖ ≤ 1 := norm_cpow_pi_neg_half_le_one hs_re
  have h1 : ‖Complex.Gammaℝ s‖ ≤ ‖(Real.pi : ℂ) ^ (-s / 2)‖ * ‖Complex.Gamma (s / 2)‖ := by
    rw [hdef]; exact norm_mul_le _ _
  have h2 : ‖(Real.pi : ℂ) ^ (-s / 2)‖ * ‖Complex.Gamma (s / 2)‖
        ≤ Real.exp (C₁ * ‖s‖ * Real.log (1 + ‖s‖)) := by
    calc ‖(Real.pi : ℂ) ^ (-s / 2)‖ * ‖Complex.Gamma (s / 2)‖
        ≤ 1 * ‖Complex.Gamma (s / 2)‖ := mul_le_mul_of_nonneg_right hpi (norm_nonneg _)
      _ = ‖Complex.Gamma (s / 2)‖ := by ring
      _ ≤ Real.exp (C₁ * ‖s‖ * Real.log (1 + ‖s‖)) := hΓ
  have hlog_nonneg : 0 ≤ Real.log (1 + ‖s‖) := Real.log_nonneg (by linarith [norm_nonneg s])
  have hnorm_nonneg : 0 ≤ ‖s‖ := norm_nonneg _
  have hC_le : C₁ * ‖s‖ * Real.log (1 + ‖s‖) ≤ (C₁ + 2) * ‖s‖ * Real.log (1 + ‖s‖) := by
    apply mul_le_mul_of_nonneg_right _ hlog_nonneg
    apply mul_le_mul_of_nonneg_right _ hnorm_nonneg
    linarith
  exact le_trans (le_trans h1 h2) (Real.exp_le_exp.mpr hC_le)

theorem finite_order :
    ∃ (A B : ℝ), 0 < A ∧ 0 < B ∧
      ∀ s : ℂ, 0 ≤ s.re → 1 ≤ ‖s‖ →
        ‖Complex.Gammaℝ s‖ ≤ Real.exp (A * ‖s‖ ^ B) := by
  obtain ⟨C, hC_pos, hC⟩ := bound_re_ge_zero
  use C + 1, 2
  refine ⟨by linarith, by norm_num, ?_⟩
  intro s hs_re hs_norm
  have h := hC s hs_re hs_norm
  apply le_trans h
  apply Real.exp_le_exp.mpr
  
  have h_log : Real.log (1 + ‖s‖) ≤ ‖s‖ := by
    have h1 : 0 < 1 + ‖s‖ := by linarith [norm_nonneg s]
    have h2 : ‖s‖ + 1 ≤ Real.exp ‖s‖ := Real.add_one_le_exp ‖s‖
    have h2' : 1 + ‖s‖ ≤ Real.exp ‖s‖ := by linarith
    rw [Real.log_le_iff_le_exp (by linarith [norm_nonneg s])]
    exact h2'
  have step1 : C * ‖s‖ * Real.log (1 + ‖s‖) ≤ C * ‖s‖ * ‖s‖ := by
    apply mul_le_mul_of_nonneg_left h_log
    apply mul_nonneg (by linarith) (norm_nonneg s)
  have step2 : C * ‖s‖ * ‖s‖ = C * ‖s‖ ^ 2 := by ring
  have step3 : C * ‖s‖ ^ 2 ≤ (C + 1) * ‖s‖ ^ 2 := by
    apply mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
  have h_combined : C * ‖s‖ * Real.log (1 + ‖s‖) ≤ (C + 1) * ‖s‖ ^ 2 := by
    calc C * ‖s‖ * Real.log (1 + ‖s‖)
        ≤ C * ‖s‖ * ‖s‖ := step1
      _ = C * ‖s‖ ^ 2 := step2
      _ ≤ (C + 1) * ‖s‖ ^ 2 := step3

  have hconv : (C + 1) * ‖s‖ ^ 2 = (C + 1) * ‖s‖ ^ (2 : ℝ) := by norm_cast
  rw [← hconv]
  exact h_combined

end Complex.Gammaℝ.Stirling
end
end
end File48

-- Upstream module PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Pow.Real
section File49

section
namespace Real

theorem log_mul_rpow_neg_le_two_div_mul_rpow_neg {ε : ℝ} (hε : 0 < ε) {u : ℝ} (hu : 1 < u) :
    Real.log u * u ^ (-1 - ε) ≤ (2 / ε) * u ^ (-1 - ε / 2) := by
  have hu0 : 0 < u := lt_trans zero_lt_one hu
  have hεne : ε ≠ 0 := ne_of_gt hε
  have hpos_coeff : 0 < 2 / ε := by
    simpa [one_div, div_eq_mul_inv] using mul_pos (by norm_num : (0 : ℝ) < 2) (inv_pos.mpr hε)
  have hle_exp : (ε / 2) * Real.log u ≤ Real.exp ((ε / 2) * Real.log u) :=
    le_trans (by linarith) (Real.add_one_le_exp ((ε / 2) * Real.log u))
  have hlog_bound : Real.log u ≤ (2 / ε) * Real.exp ((ε / 2) * Real.log u) := by
    calc
      Real.log u = (2 / ε) * ((ε / 2) * Real.log u) := by field_simp [hεne]
      _ ≤ (2 / ε) * Real.exp ((ε / 2) * Real.log u) :=
        mul_le_mul_of_nonneg_left hle_exp (le_of_lt hpos_coeff)
  have hexp_rpow : Real.exp ((ε / 2) * Real.log u) = u ^ (ε / 2) := by
    simp [Real.rpow_def_of_pos hu0, mul_comm]
  have hmul : Real.log u * u ^ (-1 - ε) ≤ ((2 / ε) * u ^ (ε / 2)) * u ^ (-1 - ε) :=
    mul_le_mul_of_nonneg_right (by simpa [hexp_rpow] using hlog_bound)
      (le_of_lt (Real.rpow_pos_of_pos hu0 _))
  have hpow_mul : u ^ (ε / 2) * u ^ (-1 - ε) = u ^ (-1 - ε / 2) := by
    rw [← Real.rpow_add hu0, show ε / 2 + (-1 - ε) = -1 - ε / 2 by ring]
  calc
    Real.log u * u ^ (-1 - ε)
        ≤ ((2 / ε) * u ^ (ε / 2)) * u ^ (-1 - ε) := hmul
    _ = (2 / ε) * u ^ (-1 - ε / 2) := by rw [mul_assoc, hpow_mul]

end Real

namespace Complex

theorem one_le_one_add_norm_rpow (z : ℂ) {p : ℝ} (hp : 0 ≤ p) : (1 : ℝ) ≤ (1 + ‖z‖) ^ p :=
  Real.one_le_rpow (by linarith [norm_nonneg z]) hp

end Complex
end
end File49

-- Upstream module PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.RiemannZeta
section File50
 

section
open scoped BigOperators Topology
open Complex Filter Real Set

def verticalLine (σ t : ℝ) : ℂ := σ + t * Complex.I

lemma verticalLine_re (σ t : ℝ) : (verticalLine σ t).re = σ := by
  simp only [verticalLine, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
    Complex.I_re, Complex.I_im, mul_zero]
  ring

lemma verticalLine_im (σ t : ℝ) : (verticalLine σ t).im = t := by
  simp only [verticalLine, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_im,
    Complex.I_re, Complex.I_im, mul_zero, add_zero]
  ring

lemma verticalLine_add_const (s : ℂ) (h t : ℝ) :
    s + (h : ℂ) + t * Complex.I = verticalLine (s.re + h) (s.im + t) := by
  apply Complex.ext
  · simp [verticalLine, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero, add_assoc, add_comm]
  · simp [verticalLine, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_im,
      Complex.I_re, Complex.I_im, mul_zero, add_assoc, add_comm]

namespace Nat.Primes

lemma norm_cpow_neg_lt_one (p : Nat.Primes) (s : ℂ) (hs : 1 < s.re) :
    ‖((p : ℕ) : ℂ) ^ (-s)‖ < 1 := by
  have hx1 : 1 < ((p : ℕ) : ℝ) := by
    have h2 : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast (p.2.two_le : 2 ≤ (p : ℕ))
    exact lt_of_lt_of_le one_lt_two h2
  have hx0 : 0 < ((p : ℕ) : ℝ) := lt_trans zero_lt_one hx1
  have hnorm : ‖((p : ℕ) : ℂ) ^ (-s)‖ = ((p : ℕ) : ℝ) ^ (-s.re) :=
    Complex.norm_cpow_eq_rpow_re_of_pos hx0 (-s)
  have hz : -s.re < 0 := neg_lt_zero.mpr (lt_trans zero_lt_one hs)
  simpa [hnorm] using Real.rpow_lt_one_of_one_lt_of_neg hx1 hz

lemma norm_cpow_neg_eq_rpow_neg_re (p : Nat.Primes) (s : ℂ) :
    ‖((p : ℕ) : ℂ) ^ (-s)‖ = ((p : ℕ) : ℝ) ^ (-s.re) := by
  have hx : 0 < ((p : ℕ) : ℝ) := Nat.cast_pos.mpr p.property.pos
  simpa [Complex.ofReal_natCast, Complex.neg_re] using
    Complex.norm_cpow_eq_rpow_re_of_pos hx (-s)

lemma cpow_neg_ofReal (p : Nat.Primes) (r : ℝ) :
    (((((p : ℕ) : ℝ) ^ (-r)) : ℝ) : ℂ) = ((p : ℕ) : ℂ) ^ (-((r : ℝ) : ℂ)) := by
  have hp : 0 ≤ ((p : ℕ) : ℝ) := by positivity
  simpa using Complex.ofReal_cpow (x := ((p : ℕ) : ℝ)) (hx := hp) (y := -r)

lemma cast_inv_one_add (p : Nat.Primes) (r : ℝ) :
    ((1 + ((p : ℕ) : ℂ) ^ (-((r : ℝ) : ℂ)))⁻¹) =
      (((1 + ((p : ℕ) : ℝ) ^ (-r))⁻¹ : ℝ) : ℂ) := by
  calc
    ((1 + ((p : ℕ) : ℂ) ^ (-((r : ℝ) : ℂ)))⁻¹)
        = ((1 + (((((p : ℕ) : ℝ) ^ (-r)) : ℝ) : ℂ))⁻¹) := by rw [← cpow_neg_ofReal p r]
    _ = (((1 + ((p : ℕ) : ℝ) ^ (-r))⁻¹ : ℝ) : ℂ) := by
      simp [Complex.ofReal_add, Complex.ofReal_inv, Complex.ofReal_one]

lemma norm_cast_inv_one_add (p : Nat.Primes) (r : ℝ) :
    ‖((1 + ((p : ℕ) : ℂ) ^ (-((r : ℝ) : ℂ)))⁻¹)‖ = (1 + ((p : ℕ) : ℝ) ^ (-r))⁻¹ := by
  have hden : 0 ≤ 1 + ((p : ℕ) : ℝ) ^ (-r) := by positivity
  rw [cast_inv_one_add, Complex.norm_real]
  exact Real.norm_of_nonneg (inv_nonneg.mpr hden)

lemma norm_one_sub_cpow_neg_vertical_le (p : Nat.Primes) (σ t : ℝ) :
    ‖(1 - ((p : ℕ) : ℂ) ^ (-verticalLine σ t))‖ ≤ 1 + ((p : ℕ) : ℝ) ^ (-σ) := by
  set s := verticalLine σ t
  have hre : s.re = σ := verticalLine_re σ t
  calc
    ‖1 - ((p : ℕ) : ℂ) ^ (-s)‖ ≤ 1 + ‖((p : ℕ) : ℂ) ^ (-s)‖ := by
      simpa [sub_eq_add_neg, norm_one, norm_neg] using
        norm_add_le (1 : ℂ) (-((p : ℕ) : ℂ) ^ (-s))
    _ = 1 + ((p : ℕ) : ℝ) ^ (-σ) := by rw [norm_cpow_neg_eq_rpow_neg_re, hre]

lemma one_sub_cpow_neg_vertical_ne_zero (p : Nat.Primes) (σ t : ℝ) (hσ : 1 < σ) :
    1 - ((p : ℕ) : ℂ) ^ (-verticalLine σ t) ≠ 0 := by
  intro h
  set s := verticalLine σ t
  have hs : 1 < s.re := by rw [verticalLine_re]; exact hσ
  have hp_eq_one : ((p : ℕ) : ℂ) ^ (-s) = 1 := by
    rw [sub_eq_zero] at h; exact h.symm
  have h_abs_lt : ‖((p : ℕ) : ℂ) ^ (-s)‖ < 1 := norm_cpow_neg_lt_one p s hs
  rw [hp_eq_one, show ‖(1 : ℂ)‖ = 1 from by simp] at h_abs_lt
  exact lt_irrefl 1 h_abs_lt

lemma inv_one_add_rpow_le_inv_norm_one_sub_cpow_neg_vertical (p : Nat.Primes) (σ t : ℝ)
    (hσ : 1 < σ) :
    (1 + ((p : ℕ) : ℝ) ^ (-σ))⁻¹ ≤
      (‖(1 - ((p : ℕ) : ℂ) ^ (-verticalLine σ t))‖)⁻¹ := by
  have hpos : 0 < ‖(1 - ((p : ℕ) : ℂ) ^ (-verticalLine σ t))‖ :=
    norm_pos_iff.mpr (one_sub_cpow_neg_vertical_ne_zero p σ t hσ)
  simpa [one_div] using one_div_le_one_div_of_le hpos (norm_one_sub_cpow_neg_vertical_le p σ t)

lemma multipliable_inv_one_add (r : ℝ) (hr : 1 < r) :
    Multipliable fun p : Nat.Primes => (1 + ((p : ℕ) : ℝ) ^ (-r))⁻¹ := by
  have hsum : Summable fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-r) := by
    rw [Nat.Primes.summable_rpow]
    linarith
  have hlog : Summable fun p : Nat.Primes => Real.log (1 + ((p : ℕ) : ℝ) ^ (-r)) :=
    Real.summable_log_one_add_of_summable hsum
  exact Real.multipliable_of_summable_log (fun _ => by positivity)
    (by simpa [Real.log_inv, neg_mul] using hlog.neg)

lemma multipliable_complex_inv_one_add (r : ℝ) (hr : 1 < r) :
    Multipliable fun p : Nat.Primes => (1 + ((p : ℕ) : ℂ) ^ (-((r : ℝ) : ℂ)))⁻¹ := by
  have hu := multipliable_inv_one_add r hr
  have hmap := hu.map Complex.ofRealHom Complex.continuous_ofReal
  have h_eq :
      (fun p : Nat.Primes => (1 + ((p : ℕ) : ℂ) ^ (-((r : ℝ) : ℂ)))⁻¹) =
        (fun x : ℝ => (x : ℂ)) ∘ fun p : Nat.Primes => (1 + ((p : ℕ) : ℝ) ^ (-r))⁻¹ := by
    funext p
    exact cast_inv_one_add p r
  simpa [h_eq, Function.comp_def] using hmap

lemma inv_one_sub_sq_eq_mul_inv_one_sub_one_add (z : ℂ) (hz : ‖z‖ < 1) :
    (1 - z ^ 2)⁻¹ = (1 - z)⁻¹ * (1 + z)⁻¹ := by
  have hz0 : 1 - z ≠ 0 := by
    intro h
    have : z = 1 := (sub_eq_zero.mp h).symm
    simp [this, norm_one] at hz
  have hz1 : 1 + z ≠ 0 := by
    intro h
    have : z = -1 := by exact Eq.symm (neg_eq_of_add_eq_zero_right h)
    simp [this, norm_neg, norm_one] at hz
  calc
    (1 - z ^ 2)⁻¹ = ((1 - z) * (1 + z))⁻¹ := by ring
    _ = (1 + z)⁻¹ * (1 - z)⁻¹ := by simp [mul_inv_rev]
    _ = (1 - z)⁻¹ * (1 + z)⁻¹ := by ring

lemma eulerFactor_two_mul (p : Nat.Primes) (s : ℂ) (hs : 1 < s.re) :
    (1 - ((p : ℕ) : ℂ) ^ (-(2 * s)))⁻¹ =
      (1 - ((p : ℕ) : ℂ) ^ (-s))⁻¹ * (1 + ((p : ℕ) : ℂ) ^ (-s))⁻¹ := by
  set z := ((p : ℕ) : ℂ) ^ (-s)
  have hz : ‖z‖ < 1 := norm_cpow_neg_lt_one p s hs
  have hpow : ((p : ℕ) : ℂ) ^ (-(2 * s)) = z ^ 2 := by
    simp only [z]
    rw [show -(2 * s) = (2 : ℂ) * (-s) by ring,
      show (2 : ℂ) * (-s) = ((2 : ℕ) : ℂ) * (-s) by norm_num, Complex.cpow_nat_mul]
  calc
    (1 - ((p : ℕ) : ℂ) ^ (-(2 * s)))⁻¹ = (1 - z ^ 2)⁻¹ := by rw [hpow]
    _ = (1 - z)⁻¹ * (1 + z)⁻¹ := inv_one_sub_sq_eq_mul_inv_one_sub_one_add z hz
    _ = (1 - ((p : ℕ) : ℂ) ^ (-s))⁻¹ * (1 + ((p : ℕ) : ℂ) ^ (-s))⁻¹ := by simp [z]

end Nat.Primes

section RiemannZetaEulerProduct

open Nat.Primes

theorem riemannZeta_eq_mul_tprod_inv_one_add (r : ℝ) (hr : 1 < r) :
    riemannZeta (2 * (r : ℂ)) =
      riemannZeta (r : ℂ) * ∏' p : Nat.Primes, (1 + ((p : ℕ) : ℂ) ^ (-((r : ℝ) : ℂ)))⁻¹ := by
  set s : ℂ := (r : ℂ)
  have hs : 1 < s.re := by simpa [s] using hr
  have hs2 : 1 < (2 * s).re := by
    simp [s, Complex.mul_re, Complex.ofReal_re]
    linarith
  have hζ := (riemannZeta_eulerProduct_hasProd hs).multipliable
  have hμ := multipliable_complex_inv_one_add r hr
  calc
    riemannZeta (2 * s)
        = ∏' p : Nat.Primes, (1 - ((p : ℕ) : ℂ) ^ (-(2 * s)))⁻¹ :=
          (riemannZeta_eulerProduct_tprod hs2).symm
    _ = ∏' p : Nat.Primes, (1 - ((p : ℕ) : ℂ) ^ (-s))⁻¹ * (1 + ((p : ℕ) : ℂ) ^ (-s))⁻¹ := by
      refine tprod_congr fun p => eulerFactor_two_mul p s hs
    _ = (∏' p : Nat.Primes, (1 - ((p : ℕ) : ℂ) ^ (-s))⁻¹) *
          ∏' p : Nat.Primes, (1 + ((p : ℕ) : ℂ) ^ (-s))⁻¹ := by
      rw [Multipliable.tprod_mul hζ hμ]
    _ = riemannZeta s * ∏' p : Nat.Primes, (1 + ((p : ℕ) : ℂ) ^ (-s))⁻¹ := by
      rw [← riemannZeta_eulerProduct_tprod hs]

theorem riemannZeta_div_riemannZeta_eq_tprod_inv_one_add (r : ℝ) (hr : 1 < r) :
    riemannZeta (2 * (r : ℂ)) / riemannZeta (r : ℂ) =
      ∏' p : Nat.Primes, (1 + ((p : ℕ) : ℂ) ^ (-((r : ℝ) : ℂ)))⁻¹ := by
  set s : ℂ := (r : ℂ)
  have hs : 1 < s.re := by simpa [s] using hr
  have hzeta_ne : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
  calc
    riemannZeta (2 * s) / riemannZeta s
        = (riemannZeta s * ∏' p : Nat.Primes, (1 + ((p : ℕ) : ℂ) ^ (-s))⁻¹) / riemannZeta s := by
          rw [riemannZeta_eq_mul_tprod_inv_one_add r hr]
    _ = ∏' p : Nat.Primes, (1 + ((p : ℕ) : ℂ) ^ (-s))⁻¹ := by
      rw [mul_div_cancel_left₀ _ hzeta_ne]

theorem norm_riemannZeta_eulerProduct (s : ℂ) (hs : 1 < s.re) :
    ‖riemannZeta s‖ = ∏' p : Nat.Primes, (‖1 - ((p : ℕ) : ℂ) ^ (-s)‖)⁻¹ := by
  calc
    ‖riemannZeta s‖ = ‖∏' p : Nat.Primes, (1 - ((p : ℕ) : ℂ) ^ (-s))⁻¹‖ := by
      rw [riemannZeta_eulerProduct_tprod hs]
    _ = ∏' p : Nat.Primes, ‖(1 - ((p : ℕ) : ℂ) ^ (-s))⁻¹‖ := by
      exact Multipliable.norm_tprod (riemannZeta_eulerProduct_hasProd hs).multipliable
    _ = ∏' p : Nat.Primes, (‖1 - ((p : ℕ) : ℂ) ^ (-s)‖)⁻¹ := by
      congr 1; ext p; simp [norm_inv]

theorem norm_riemannZeta_div_riemannZeta (r : ℝ) (hr : 1 < r) :
    ‖riemannZeta (2 * (r : ℂ)) / riemannZeta (r : ℂ)‖ =
      ∏' p : Nat.Primes, (1 + ((p : ℕ) : ℝ) ^ (-r))⁻¹ := by
  set s : ℂ := (r : ℂ)
  have hw := multipliable_complex_inv_one_add r hr
  calc
    ‖riemannZeta (2 * s) / riemannZeta s‖ = ‖∏' p : Nat.Primes, (1 + ((p : ℕ) : ℂ) ^ (-s))⁻¹‖ := by
      simpa [s] using congrArg norm (riemannZeta_div_riemannZeta_eq_tprod_inv_one_add r hr)
    _ = ∏' p : Nat.Primes, ‖(1 + ((p : ℕ) : ℂ) ^ (-s))⁻¹‖ := Multipliable.norm_tprod hw
    _ = ∏' p : Nat.Primes, (1 + ((p : ℕ) : ℝ) ^ (-r))⁻¹ := by
      refine tprod_congr fun p => norm_cast_inv_one_add p r

private lemma multipliable_norm_eulerFactor_inv {ι : Type*} (g : ι → ℂ)
    (h : Multipliable fun i => (1 - g i)⁻¹) :
    Multipliable fun i => (‖1 - g i‖)⁻¹ := by
  simpa [norm_inv] using Multipliable.norm h

private lemma hasProd_nonneg_of_pos {ι : Type*} (f : ι → ℝ) (hf₀ : ∀ i, 0 < f i) (a : ℝ)
    (ha : HasProd f a) : 0 ≤ a :=
  ge_of_tendsto ha <| Filter.Eventually.of_forall fun _ =>
    le_of_lt <| Finset.prod_pos fun i _ => hf₀ i

private lemma hasProd_nnreal_of_coe {ι : Type*} (g : ι → NNReal) (b : NNReal)
    (h : HasProd (fun i => (g i : ℝ)) (b : ℝ)) : HasProd g b := by
  have h_eq : (fun s => ∏ i ∈ s, (g i : ℝ)) = fun s => ↑(∏ i ∈ s, g i) := by
    ext s; exact (NNReal.coe_prod s g).symm
  exact
    (NNReal.isEmbedding_coe.tendsto_nhds_iff.mpr <| by
      change Filter.Tendsto (fun s => ↑(∏ i ∈ s, g i)) Filter.atTop (𝓝 (b : ℝ))
      rw [← h_eq]
      exact h)

private lemma multipliable_toNNReal {ι : Type*} (f : ι → ℝ) (hf₀ : ∀ i, 0 < f i)
    (hf : Multipliable f) : Multipliable fun i => (⟨f i, (hf₀ i).le⟩ : NNReal) := by
  obtain ⟨a, ha⟩ := hf
  let a_nnreal : NNReal := ⟨a, hasProd_nonneg_of_pos f hf₀ a ha⟩
  exact ⟨a_nnreal, hasProd_nnreal_of_coe _ _ (by simpa [a_nnreal] using! ha)⟩

private lemma nnreal_coe_tprod {ι : Type*} (f : ι → NNReal) (hf : Multipliable f) :
    ∏' i, (↑(f i) : ℝ) = ↑(∏' i, f i) :=
  (HasProd.map (Multipliable.hasProd hf) NNReal.toRealHom NNReal.continuous_coe).tprod_eq

private lemma nnreal_tprod_le_coe {ι : Type*} (f g : ι → NNReal) (hf : Multipliable f)
    (hg : Multipliable g) (h : ∏' i, f i ≤ ∏' i, g i) :
    ∏' i, (f i : ℝ) ≤ ∏' i, (g i : ℝ) := by
  rw [nnreal_coe_tprod f hf, nnreal_coe_tprod g hg]
  exact NNReal.coe_le_coe.mpr h

theorem tprod_inv_one_add_real_le_riemannZeta_norm_on_verticalLine (σ t : ℝ) (hσ : 1 < σ) :
    ∏' p : Nat.Primes, (1 + ((p : ℕ) : ℝ) ^ (-σ))⁻¹ ≤
      ∏' p : Nat.Primes, (‖1 - ((p : ℕ) : ℂ) ^ (-verticalLine σ t)‖)⁻¹ := by
  set s := verticalLine σ t
  have hs : 1 < s.re := by rw [verticalLine_re]; exact hσ
  have hf₀ : ∀ p : Nat.Primes, 0 < (1 + ((p : ℕ) : ℝ) ^ (-σ))⁻¹ := fun _ => by positivity
  have hg₀ : ∀ p : Nat.Primes, 0 < (‖1 - ((p : ℕ) : ℂ) ^ (-s)‖)⁻¹ := fun p =>
    inv_pos.mpr (norm_pos_iff.mpr (Nat.Primes.one_sub_cpow_neg_vertical_ne_zero p σ t hσ))
  let f : Nat.Primes → NNReal := fun p => ⟨(1 + ((p : ℕ) : ℝ) ^ (-σ))⁻¹, (hf₀ p).le⟩
  let g : Nat.Primes → NNReal := fun p => ⟨(‖1 - ((p : ℕ) : ℂ) ^ (-s)‖)⁻¹, (hg₀ p).le⟩
  have hf := multipliable_toNNReal _ hf₀ <| Nat.Primes.multipliable_inv_one_add σ hσ
  have hg := multipliable_toNNReal _ hg₀ <|
    multipliable_norm_eulerFactor_inv (g := fun p : Nat.Primes => ((p : ℕ) : ℂ) ^ (-s))
      (riemannZeta_eulerProduct_hasProd hs).multipliable
  have hle : ∏' p, f p ≤ ∏' p, g p :=
    Multipliable.tprod_le_tprod (fun p =>
      Nat.Primes.inv_one_add_rpow_le_inv_norm_one_sub_cpow_neg_vertical p σ t hσ) hf hg
  calc
    ∏' p : Nat.Primes, (1 + ((p : ℕ) : ℝ) ^ (-σ))⁻¹
        = ∏' p, (f p : ℝ) := tprod_congr fun p => by unfold f; rfl
    _ ≤ ∏' p, (g p : ℝ) := nnreal_tprod_le_coe f g hf hg hle
    _ = ∏' p : Nat.Primes, (‖1 - ((p : ℕ) : ℂ) ^ (-s)‖)⁻¹ :=
        tprod_congr fun p => by unfold g; rfl

end RiemannZetaEulerProduct

theorem one_div_natCast_cpow_eq_ite_cpow_neg (s : ℂ) (hs : s ≠ 0) (n : ℕ) :
    1 / (n : ℂ) ^ s = if n = 0 then 0 else (n : ℂ) ^ (-s) := by
  by_cases h : n = 0
  · simp [h, Complex.zero_cpow hs]
  · simp [h, one_div, Complex.cpow_neg]

end
end File50

-- Upstream module PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.Convex
section File51
 

section
namespace Complex

theorem isPathConnected_halfSpace_re_gt_diff_singleton (a : ℝ) (p : ℂ) (hp : a < p.re) :
    IsPathConnected ({z : ℂ | a < z.re} \ ({p} : Set ℂ)) := by
  classical
  let S1 : Set ℂ := {z : ℂ | a < z.re ∧ z.im < p.im}
  let S2 : Set ℂ := {z : ℂ | a < z.re ∧ z.re < p.re}
  let S3 : Set ℂ := {z : ℂ | a < z.re ∧ p.im < z.im}
  let S4 : Set ℂ := {z : ℂ | p.re < z.re}
  have hS1conv : Convex ℝ S1 := by
    have h1 : Convex ℝ {z : ℂ | a < z.re} := convex_halfSpace_re_gt (r := a)
    have h2 : Convex ℝ {z : ℂ | z.im < p.im} := convex_halfSpace_im_lt (r := p.im)
    simpa [S1, Set.ofPred_and] using h1.inter h2
  have hS2conv : Convex ℝ S2 := by
    have h1 : Convex ℝ {z : ℂ | a < z.re} := convex_halfSpace_re_gt (r := a)
    have h2 : Convex ℝ {z : ℂ | z.re < p.re} := convex_halfSpace_re_lt (r := p.re)
    simpa [S2, Set.ofPred_and] using h1.inter h2
  have hS3conv : Convex ℝ S3 := by
    have h1 : Convex ℝ {z : ℂ | a < z.re} := convex_halfSpace_re_gt (r := a)
    have h2 : Convex ℝ {z : ℂ | p.im < z.im} := convex_halfSpace_im_gt (r := p.im)
    simpa [S3, Set.ofPred_and] using h1.inter h2
  have hS4conv : Convex ℝ S4 := by
    simpa [S4] using (convex_halfSpace_re_gt (r := p.re))
  have hS1ne : S1.Nonempty := by
    refine ⟨((max a p.re) + 1 : ℝ) + (p.im - 1) * Complex.I, ?_⟩
    have h1 : a < (max a p.re) + 1 := by
      have : a ≤ max a p.re := le_max_left _ _
      exact lt_of_le_of_lt this (by linarith)
    have h2 : (p.im - 1) < p.im := by linarith
    simpa [S1, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
      using And.intro h1 h2
  have hS2ne : S2.Nonempty := by
    refine ⟨((a + p.re) / 2 : ℝ) + (p.im : ℝ) * Complex.I, ?_⟩
    have h1 : a < (a + p.re) / 2 := by linarith
    have h2 : (a + p.re) / 2 < p.re := by linarith
    simpa [S2, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
      using And.intro h1 h2
  have hS3ne : S3.Nonempty := by
    refine ⟨((max a p.re) + 1 : ℝ) + (p.im + 1) * Complex.I, ?_⟩
    have h1 : a < (max a p.re) + 1 := by
      have : a ≤ max a p.re := le_max_left _ _
      exact lt_of_le_of_lt this (by linarith)
    have h2 : p.im < (p.im + 1) := by linarith
    simpa [S3, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
      using And.intro h1 h2
  have hS4ne : S4.Nonempty := by
    refine ⟨(p.re + 1 : ℝ) + (0 : ℝ) * Complex.I, ?_⟩
    have : p.re < p.re + 1 := by linarith
    simp [S4, Complex.add_re]
  have hS1pc : IsPathConnected S1 := (hS1conv.isPathConnected hS1ne)
  have hS2pc : IsPathConnected S2 := (hS2conv.isPathConnected hS2ne)
  have hS3pc : IsPathConnected S3 := (hS3conv.isPathConnected hS3ne)
  have hS4pc : IsPathConnected S4 := (hS4conv.isPathConnected hS4ne)
  let A : Set ℂ := S1 ∪ S2
  let B : Set ℂ := S3 ∪ S4
  have hS1S2_int : (S1 ∩ S2).Nonempty := by
    refine ⟨((a + p.re) / 2 : ℝ) + (p.im - (1/2)) * Complex.I, ?_⟩
    have h1a : a < (a + p.re) / 2 := by linarith
    have h1b : (p.im - (1/2)) < p.im := by linarith
    have h2a : a < (a + p.re) / 2 := by linarith
    have h2b : (a + p.re) / 2 < p.re := by linarith
    constructor
    · simpa [S1, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
        using And.intro h1a h1b
    · simpa [S2, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
        using And.intro h2a h2b
  have hApc : IsPathConnected A :=
    IsPathConnected.union (U := S1) (V := S2) hS1pc hS2pc (by
      rcases hS1S2_int with ⟨z, hz⟩; exact ⟨z, hz⟩)
  have hS3S4_int : (S3 ∩ S4).Nonempty := by
    refine ⟨(p.re + 1 : ℝ) + (p.im + 1) * Complex.I, ?_⟩
    have h3a : a < p.re + 1 := lt_trans hp (by linarith)
    have h3b : p.im < p.im + 1 := by linarith
    have h4 : p.re < p.re + 1 := by linarith
    constructor
    · simpa [S3, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
        using And.intro h3a h3b
    · simp [S4, Complex.add_re, Complex.mul_re]
  have hBpc : IsPathConnected B :=
    IsPathConnected.union (U := S3) (V := S4) hS3pc hS4pc (by
      rcases hS3S4_int with ⟨z, hz⟩; exact ⟨z, hz⟩)
  have hABint : (A ∩ B).Nonempty := by
    refine ⟨(p.re + 1 : ℝ) + (p.im - 1) * Complex.I, ?_⟩
    constructor
    · refine Or.inl ?_
      have h1 : a < p.re + 1 := lt_trans hp (by linarith)
      have h2 : (p.im - 1) < p.im := by linarith
      simpa [S1, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
        using And.intro h1 h2
    · refine Or.inr ?_
      have h4 : p.re < p.re + 1 := by linarith
      simp [S4, Complex.add_re, Complex.mul_re]
  have hUnionPC : IsPathConnected (A ∪ B) :=
    IsPathConnected.union (U := A) (V := B) hApc hBpc (by
      rcases hABint with ⟨z, hz⟩; exact ⟨z, hz⟩)
  have hcover : ({z : ℂ | a < z.re} \ ({p} : Set ℂ)) = A ∪ B := by
    ext z; constructor
    · intro hz
      rcases hz with ⟨hzH, hznot⟩
      rcases lt_trichotomy z.re p.re with hlt | heq | hgt
      · exact Or.inl (Or.inr ⟨hzH, hlt⟩)
      · rcases lt_trichotomy z.im p.im with himlt | himeq | himgt
        · exact Or.inl (Or.inl ⟨hzH, himlt⟩)
        · have hz_eq : z = p := by
            have hzdecomp : (z.re : ℂ) + (z.im : ℝ) * Complex.I = z := by simp
            have hpdecomp : (p.re : ℂ) + (p.im : ℝ) * Complex.I = p := by simp
            have : (z.re : ℂ) + (z.im : ℝ) * Complex.I = (p.re : ℂ) + (p.im : ℝ) * Complex.I := by
              simp [heq, himeq]
            simpa [hzdecomp, hpdecomp] using this
          have : z ∈ ({p} : Set ℂ) := by simp [Set.mem_singleton_iff, hz_eq]
          exact (hznot this).elim
        · exact Or.inr (Or.inl ⟨hzH, himgt⟩)
      · exact Or.inr (Or.inr hgt)
    · intro hz
      have hzH : a < z.re := by
        rcases hz with hA | hB
        · rcases hA with hS1 | hS2
          · exact hS1.1
          · exact hS2.1
        · rcases hB with hS3 | hS4
          · exact hS3.1
          · exact lt_trans hp hS4
      have hzneq : z ≠ p := by
        rcases hz with hA | hB
        · rcases hA with hS1 | hS2
          · intro h
            have : z.im = p.im := by simp [h]
            have : z.im < z.im := by simpa [this] using hS1.2
            exact lt_irrefl _ this
          · intro h
            have : z.re = p.re := by simp [h]
            exact (ne_of_lt hS2.2) this
        · rcases hB with hS3 | hS4
          · intro h
            have : p.im = z.im := by simp [h]
            have : z.im < z.im := by simpa [this] using hS3.2
            exact lt_irrefl _ this
          · intro h
            have : p.re = z.re := by simp [h]
            exact (ne_of_gt hS4) this.symm
      exact And.intro hzH (by intro hzmem; exact hzneq (by simpa [Set.mem_singleton_iff] using hzmem))
  simpa [hcover] using hUnionPC

end Complex
end
end File51

-- Upstream module PrimeNumberTheoremAnd.Mathlib.MeasureTheory.Integral.IntegrableOn
section File52

section
namespace MeasureTheory

variable {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
variable {μ : Measure α} {s : Set α}

lemma IntegrableOn.mono' {f : α → E} {g : α → ℝ} (hg : IntegrableOn g s μ)
    (hf : AEStronglyMeasurable f (μ.restrict s))
    (h : ∀ᵐ x ∂μ.restrict s, ‖f x‖ ≤ g x) : IntegrableOn f s μ := by
  exact Integrable.mono' hg hf h

end MeasureTheory
end
end File52

-- Upstream module PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
section File53
 

section
open Real Set Filter MeasureTheory intervalIntegral
open scoped Topology

theorem integral_interval_rpow_neg_one_sub {ε m n : ℝ} (hε : 0 < ε) (hm : 1 ≤ m) (hmn : m ≤ n) :
    ∫ u in m..n, u ^ (-1 - ε) = (m ^ (-ε) - n ^ (-ε)) / ε := by
  have h0notIcc : (0 : ℝ) ∉ Set.Icc m n := by
    intro hx
    exact (not_le.mpr (lt_of_lt_of_le zero_lt_one hm)) hx.1
  have h0not : (0 : ℝ) ∉ Set.uIcc m n := by simpa [uIcc_of_le hmn] using h0notIcc
  have hrne : (-1 - ε) ≠ (-1 : ℝ) := by
    intro h
    exact (ne_of_gt hε) (by linarith [h])
  have hint : ∫ u in m..n, u ^ (-1 - ε)
      = (n ^ ((-1 - ε) + 1) - m ^ ((-1 - ε) + 1)) / ((-1 - ε) + 1) := by
    simpa using integral_rpow (a := m) (b := n) (r := -1 - ε) (Or.inr ⟨hrne, h0not⟩)
  calc
    ∫ u in m..n, u ^ (-1 - ε)
        = (n ^ ((-1 - ε) + 1) - m ^ ((-1 - ε) + 1)) / ((-1 - ε) + 1) := hint
    _ = (n ^ (-ε) - m ^ (-ε)) / (-ε) := by
      simp [sub_eq_add_neg, add_left_comm, add_comm]
    _ = (m ^ (-ε) - n ^ (-ε)) / ε := by ring

theorem integral_interval_rpow_neg_le {ε m n : ℝ} (hε : 0 < ε) (hm : 1 ≤ m) (hmn : m ≤ n) :
    ∫ u in m..n, u ^ (-1 - ε) ≤ (1 / ε) * m ^ (-ε) := by
  rw [integral_interval_rpow_neg_one_sub hε hm hmn, div_eq_mul_one_div, mul_comm]
  gcongr
  exact sub_le_self _ (Real.rpow_nonneg (le_trans zero_le_one (le_trans hm hmn)) _)

theorem intervalIntegral.tendsto_integral_Ioi_of_ae_norm_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : ℝ → E) (g : ℝ → ℝ) (c : ℝ)
    (hfm : MeasureTheory.AEStronglyMeasurable f (MeasureTheory.volume.restrict (Ioi c)))
    (hbound : ∀ᵐ u ∂MeasureTheory.volume.restrict (Ioi c), ‖f u‖ ≤ g u)
    (hg : MeasureTheory.IntegrableOn g (Ioi c) MeasureTheory.volume) :
    Tendsto (fun N : ℕ => ∫ u in c..N, f u) atTop (𝓝 (∫ u in Ioi c, f u)) :=
  intervalIntegral_tendsto_integral_Ioi c (MeasureTheory.IntegrableOn.mono' hg hfm hbound)
    tendsto_natCast_atTop_atTop

theorem integral_Ioi_rpow_neg_re_sub_one {s : ℂ} (hs : 0 < s.re) :
    ∫ u in Ioi (1 : ℝ), u ^ (-s.re - 1) = 1 / s.re := by
  have ha : (-s.re - 1) < -1 := by linarith
  have hc : 0 < (1 : ℝ) := zero_lt_one
  have h := integral_Ioi_rpow_of_lt (a := (-s.re - 1)) ha (c := (1 : ℝ)) hc
  have h' : ∫ u in Ioi (1 : ℝ), u ^ (-s.re - 1) = - (1 : ℝ) ^ (-s.re) / (-s.re) := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h
  calc
    ∫ u in Ioi (1 : ℝ), u ^ (-s.re - 1)
        = - (1 : ℝ) ^ (-s.re) / (-s.re) := h'
    _ = - (1 : ℝ) / (-s.re) := by simp [Real.one_rpow]
    _ = 1 / s.re := by simp
end
end File53

-- Upstream module PrimeNumberTheoremAnd.Mathlib.Algebra.Order.Floor.Ring
section File54

section
namespace Int

variable {R : Type*} [Ring R] [LinearOrder R] [IsOrderedRing R] [FloorRing R]

theorem fract_abs_le_one (a : R) : |fract a| ≤ 1 := by
  rw [abs_fract]
  exact (fract_lt_one a).le

end Int
end
end File54

-- Upstream module PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Pow.Deriv
section File55

section
namespace Complex

theorem continuousOn_ofReal_cpow {r : ℂ} {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (fun u : ℝ => (u : ℂ) ^ r) (Set.Icc a b) :=
  ((continuous_ofReal.continuousOn : ContinuousOn ((↑) : ℝ → ℂ) (Set.Icc a b)).cpow continuousOn_const
    (fun _ hu => (ofReal_mem_slitPlane).2 (lt_of_lt_of_le ha hu.1))).mono Set.Subset.rfl

theorem deriv_ofReal_cpow_neg (s : ℂ) {x : ℝ} (hx : 0 < x) :
    deriv (fun (t : ℝ) => (t : ℂ) ^ (-s)) x = -s * (x : ℂ) ^ (-s - 1) := by
  by_cases hs : s = 0
  · simp [hs, deriv_const, cpow_zero, sub_eq_add_neg]
  · simpa [sub_eq_add_neg] using deriv_ofReal_cpow_const (-s) hx.ne'

theorem continuousOn_deriv_ofReal_cpow_neg (s : ℂ) {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (deriv (fun (t : ℝ) => (t : ℂ) ^ (-s))) (Set.Icc a b) :=
    ((continuousOn_const : ContinuousOn (fun (_ : ℝ) => (-s : ℂ)) (Set.Icc a b)).mul
      (continuousOn_ofReal_cpow (r := -s - 1) ha)).congr fun _ ht =>
    deriv_ofReal_cpow_neg s (lt_of_lt_of_le ha ht.1)

theorem ofReal_cpow_mul_cpow_neg_sub_one (s : ℂ) {u : ℝ} (hu : 0 < u) :
    (u : ℂ) * (u : ℂ) ^ (-s - 1) = (u : ℂ) ^ (-s) := by
  have hx : (u : ℂ) ≠ 0 := ofReal_ne_zero.mpr hu.ne'
  calc
    (u : ℂ) * (u : ℂ) ^ (-s - 1) = (u : ℂ) ^ (1 : ℂ) * (u : ℂ) ^ (-s - 1) := by simp [cpow_one]
    _ = (u : ℂ) ^ (-s) := by rw [← cpow_add _ _ hx]; ring_nf

theorem natCast_mul_cpow_neg_eq_cpow_one_sub (N : ℕ) (s : ℂ) (hN : N ≠ 0) :
    (N : ℂ) * (N : ℂ) ^ (-s) = (N : ℂ) ^ (1 - s) := by
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  calc
    (N : ℂ) * (N : ℂ) ^ (-s) = (N : ℂ) ^ (1 : ℂ) * (N : ℂ) ^ (-s) := by simp [cpow_one]
    _ = (N : ℂ) ^ (1 - s) := by rw [← cpow_add _ _ hN']; ring_nf

theorem HasDerivAt.const_mul_ofReal_cpow_neg_sub_one (a : ℂ) {u : ℝ} (hu : 0 < u) (z : ℂ) :
    HasDerivAt (fun w => a * (u : ℂ) ^ (-w - 1))
      (-a * (Complex.log u) * (u : ℂ) ^ (-z - 1)) z := by
  set huC : (u : ℂ) ≠ 0 := ofReal_ne_zero.mpr hu.ne'
  have hf : HasDerivAt (fun w => -w - 1) (-1) z := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      (hasDerivAt_id z).neg.sub_const (1 : ℂ)
  have hbase : HasDerivAt (fun w => (u : ℂ) ^ (-w - 1))
      ((u : ℂ) ^ (-z - 1) * Complex.log (u : ℂ) * (-1)) z :=
    HasDerivAt.const_cpow (c := (u : ℂ)) hf (Or.inl huC)
  have hbase' : HasDerivAt (fun w => (u : ℂ) ^ (-w - 1))
      (-(Complex.log (u : ℂ)) * (u : ℂ) ^ (-z - 1)) z := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hbase
  have hlog : (Real.log u : ℂ) = Complex.log (u : ℂ) := by
    simpa using (ofReal_log (x := u) (hx := le_of_lt hu))
  simpa [hlog, mul_comm, mul_left_comm, mul_assoc] using hbase'.const_mul a

end Complex
end
end File55

-- Upstream module PrimeNumberTheoremAnd.Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
section File56

section
open Set MeasureTheory

namespace intervalIntegral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {f g : ℝ → E} {μ : Measure ℝ}

theorem integral_congr_Ioc_of_le {a b : ℝ} (hab : a ≤ b)
    (h : ∀ u ∈ Ioc a b, f u = g u) :
    ∫ u in a..b, f u ∂μ = ∫ u in a..b, g u ∂μ := by
  refine integral_congr_ae' (Filter.Eventually.of_forall ?_) (Filter.Eventually.of_forall ?_) <;>
    intro u hu
  · exact h u hu
  · have hempty : Ioc b a = ∅ := Ioc_eq_empty hab.not_gt
    exact (hempty ▸ hu).elim

end intervalIntegral
end
end File56

-- Upstream module PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.RiemannZetaAbelKernel
section File57
 

section
open scoped Topology
open Real Set Filter Topology MeasureTheory Complex

noncomputable def zetaAbelFractKernel (s : ℂ) (u : ℝ) : ℂ :=
  ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1)

theorem norm_zetaAbelFractKernel_le (u : ℝ) (hu : 1 ≤ u) (s : ℂ) :
    ‖zetaAbelFractKernel s u‖ ≤ u ^ (-s.re - 1) := by
  have hu0 : 0 < u := one_pos.trans_le hu
  have hfract_le1 : ‖((Int.fract u : ℝ) : ℂ)‖ ≤ 1 := by simpa using Int.fract_abs_le_one u
  have hle : ‖zetaAbelFractKernel s u‖ ≤ ‖(u : ℂ) ^ (-s - 1)‖ := by
    calc
      _ = ‖((Int.fract u : ℝ) : ℂ)‖ * ‖(u : ℂ) ^ (-s - 1)‖ := by rw [zetaAbelFractKernel, norm_mul]
      _ ≤ 1 * ‖(u : ℂ) ^ (-s - 1)‖ := by
        exact mul_le_mul_of_nonneg_right hfract_le1 (norm_nonneg _)
      _ = ‖(u : ℂ) ^ (-s - 1)‖ := one_mul _
  have hb : ‖(u : ℂ) ^ (-s - 1)‖ = u ^ (-s.re - 1) := by
    have hre : (-s - 1).re = -s.re - 1 := by
      simp [sub_eq_add_neg]
    simpa [hre] using Complex.norm_cpow_eq_rpow_re_of_pos hu0 (-s - 1)
  exact hle.trans_eq hb

namespace ZetaAbelFractKernel

lemma aestronglyMeasurable (s : ℂ) (S : Set ℝ) (_ : MeasurableSet S) :
    AEStronglyMeasurable (fun u => zetaAbelFractKernel s u) (volume.restrict S) := by
  refine (measurable_fract.complex_ofReal.mul ?_).aestronglyMeasurable
  simpa using Complex.measurable_ofReal.pow_const (-s - 1)

lemma ae_bound_Ioi (s : ℂ) :
    ∀ᵐ u ∂(volume.restrict (Ioi (1 : ℝ))),
      ‖zetaAbelFractKernel s u‖ ≤ u ^ (-s.re - 1) :=
  ae_restrict_iff' measurableSet_Ioi |>.2 <| ae_of_all _ fun u hu =>
    norm_zetaAbelFractKernel_le u (le_of_lt hu) s

lemma intervalIntegrable (s : ℂ) {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun u => zetaAbelFractKernel s u) volume a b := by
  let μ := volume.restrict (Icc a b)
  set g : ℝ → ℝ := fun u => ‖(u : ℂ) ^ (-s - 1)‖
  have hmeas := aestronglyMeasurable s (Icc a b) measurableSet_Icc
  have hbound_ae : ∀ᵐ u ∂μ, ‖zetaAbelFractKernel s u‖ ≤ g u := by
    refine (ae_restrict_iff' measurableSet_Icc).2 (ae_of_all _ ?_)
    intro u huIcc
    have hu0 : 0 < u := lt_of_lt_of_le one_pos (ha.trans huIcc.1)
    have hg_eq : g u = u ^ (-s.re - 1) := by
      simp [g, Complex.norm_cpow_eq_rpow_re_of_pos hu0, sub_eq_add_neg]
    exact (norm_zetaAbelFractKernel_le u (ha.trans huIcc.1) s).trans (le_of_eq hg_eq.symm)
  have hg : Integrable g μ := by
    simpa [μ, g] using!
      (Complex.continuousOn_ofReal_cpow (ha := one_pos.trans_le ha)).norm.integrableOn_compact
        isCompact_Icc
  have hf0 : Integrable (fun _ : ℝ => (0 : ℂ)) μ := by simp [μ]
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le hab).2 <|
    integrable_of_norm_sub_le hmeas hf0 hg
      (hbound_ae.mono fun u hu => by simpa [sub_eq_add_neg, μ, g] using hu)

theorem tendsto_integral_Ioi (s : ℂ) (hs : 1 < s.re) :
    Tendsto (fun N : ℕ => ∫ u in (1 : ℝ)..N, zetaAbelFractKernel s u) atTop
      (𝓝 (∫ u in Ioi (1 : ℝ), zetaAbelFractKernel s u)) :=
  intervalIntegral.tendsto_integral_Ioi_of_ae_norm_le (f := fun u => zetaAbelFractKernel s u)
    (g := fun u => u ^ (-s.re - 1)) 1
    (aestronglyMeasurable s (Ioi (1 : ℝ)) measurableSet_Ioi) (ae_bound_Ioi s)
    (integrableOn_Ioi_rpow_of_lt (by linarith) one_pos)

theorem integrableOn_Ioi (s : ℂ) (hs : 0 < s.re) :
    Integrable (fun u => zetaAbelFractKernel s u) (volume.restrict (Ioi (1 : ℝ))) := by
  set ε : ℝ := s.re / 2
  set g : ℝ → ℝ := fun u => u ^ (-1 - ε)
  have hfm := aestronglyMeasurable s (Ioi (1 : ℝ)) measurableSet_Ioi
  have hε : 0 < ε := half_pos hs
  have hεle : ε ≤ s.re := half_le_self (le_of_lt hs)
  have hbound : ∀ᵐ u ∂(volume.restrict (Ioi (1 : ℝ))), ‖zetaAbelFractKernel s u‖ ≤ g u :=
    ae_restrict_iff' measurableSet_Ioi |>.2 <| ae_of_all _ fun u hu =>
      (norm_zetaAbelFractKernel_le u (le_of_lt hu) s).trans
        (Real.rpow_le_rpow_of_exponent_le (le_of_lt hu) (by linarith [hεle]))
  simpa [IntegrableOn] using
    IntegrableOn.mono' (integrableOn_Ioi_rpow_of_lt (by linarith) one_pos) hfm hbound

lemma aestronglyMeasurable_param_deriv (z : ℂ) :
    AEStronglyMeasurable (fun u : ℝ => -((Real.log u) : ℂ) * zetaAbelFractKernel z u)
      (volume.restrict (Ioi (1 : ℝ))) := by
  have hmeas : Measurable (fun u : ℝ => zetaAbelFractKernel z u) :=
    (measurable_fract.complex_ofReal.mul <| by simpa using Complex.measurable_ofReal.pow_const (-z - 1))
  simpa only [neg_mul] using
    (Real.measurable_log.complex_ofReal.fun_mul hmeas).fun_neg.aestronglyMeasurable

lemma eventually_aestronglyMeasurable_param (s : ℂ) :
    ∀ᶠ z in 𝓝 s,
      AEStronglyMeasurable (fun u : ℝ => zetaAbelFractKernel z u) (volume.restrict (Ioi (1 : ℝ))) :=
  Eventually.of_forall fun z => aestronglyMeasurable z (Ioi (1 : ℝ)) measurableSet_Ioi

theorem hasDerivAt_in_param (u : ℝ) (hu : 1 < u) (z : ℂ) :
    HasDerivAt (fun w => zetaAbelFractKernel w u)
      (-((Real.log u) : ℂ) * zetaAbelFractKernel z u) z := by
  have h := HasDerivAt.const_mul_ofReal_cpow_neg_sub_one ((Int.fract u : ℝ) : ℂ)
    (lt_trans zero_lt_one hu) z
  have hfun : (fun w => zetaAbelFractKernel w u) = fun w => ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-w - 1) := by
    ext w; simp [zetaAbelFractKernel]
  exact (h.congr_of_eventuallyEq (EventuallyEq.of_eq hfun)).congr_deriv (by
    simp [zetaAbelFractKernel, Complex.ofReal_log (x := u) (hx := le_of_lt (lt_trans zero_lt_one hu)),
      mul_comm, mul_assoc, mul_left_comm])

theorem kernel_deriv_norm_bound_on_ball (ε : ℝ) (u : ℝ) (hu : 1 < u) (x : ℂ) (hx : ε ≤ x.re) :
    ‖-((Real.log u) : ℂ) * zetaAbelFractKernel x u‖ ≤ Real.log u * u ^ (-1 - ε) := by
  have hu1 : (1 : ℝ) ≤ u := le_of_lt hu
  have hinner : ‖zetaAbelFractKernel x u‖ ≤ u ^ (-1 - ε) :=
    (norm_zetaAbelFractKernel_le u hu1 x).trans (Real.rpow_le_rpow_of_exponent_le hu1 (by linarith))
  have hlognorm : ‖-((Real.log u) : ℂ)‖ = Real.log u := by
    have hnonneg : 0 ≤ Real.log u := le_of_lt (Real.log_pos hu)
    simp [norm_neg, Complex.norm_real, abs_of_nonneg hnonneg]
  calc
    ‖-((Real.log u) : ℂ) * zetaAbelFractKernel x u‖
        = Real.log u * ‖zetaAbelFractKernel x u‖ := by rw [norm_mul, hlognorm]
    _ ≤ Real.log u * u ^ (-1 - ε) := mul_le_mul_of_nonneg_left hinner (le_of_lt (Real.log_pos hu))

private lemma ae_on_Ioi_of_all {p : ℝ → Prop} (h : ∀ u ∈ Ioi (1 : ℝ), p u) :
    ∀ᵐ u ∂(volume.restrict (Ioi (1 : ℝ))), p u :=
  ae_restrict_iff' measurableSet_Ioi |>.2 (ae_of_all _ fun u hu => h u hu)

private lemma dist_lt_of_mem_ball_half {z s : ℂ} {δ : ℝ} (hz : z ∈ Metric.ball s (δ / 2)) (hδ : 0 < δ) :
    dist z s < δ :=
  lt_trans (Metric.mem_ball.mp hz) (half_lt_self hδ)

lemma hasDerivAt_integral_param_dominated_Ioi
  (F F' : ℂ → ℝ → ℂ) (s : ℂ) (δ : ℝ) (hδ : 0 < δ)
  (hmeas : ∀ᶠ z in 𝓝 s, AEStronglyMeasurable (F z) (volume.restrict (Ioi (1 : ℝ))))
  (hFint : Integrable (F s) (volume.restrict (Ioi (1 : ℝ))))
  (hF'meas : AEStronglyMeasurable (F' s) (volume.restrict (Ioi (1 : ℝ))))
  (bound : ℝ → ℝ) (hbound_int : Integrable bound (volume.restrict (Ioi (1 : ℝ))))
  (hbound : ∀ᵐ u ∂(volume.restrict (Ioi (1 : ℝ))), ∀ z ∈ Metric.ball s δ, ‖F' z u‖ ≤ bound u)
  (hderiv : ∀ᵐ u ∂(volume.restrict (Ioi (1 : ℝ))), ∀ z ∈ Metric.ball s δ,
    HasDerivAt (fun w => F w u) (F' z u) z) :
  HasDerivAt (fun z => ∫ u in Ioi (1 : ℝ), F z u) (∫ u in Ioi (1 : ℝ), F' s u) s := by
  have h :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume.restrict (Ioi (1 : ℝ))) (F := F) (F' := F') (x₀ := s)
      (s := Metric.ball s δ) (bound := bound) (Metric.ball_mem_nhds s hδ)
      (hF_meas := hmeas) (hF_int := hFint) (hF'_meas := hF'meas)
      (h_bound := hbound) (bound_integrable := hbound_int) (h_diff := hderiv)
  rcases h with ⟨_, hDeriv⟩
  exact hDeriv

theorem integral_analytic (s : ℂ) (hs : 0 < s.re) :
    AnalyticAt ℂ (fun z => ∫ u in Ioi (1 : ℝ), zetaAbelFractKernel z u) s := by
  set ε : ℝ := s.re / 2
  have hεpos : 0 < ε := half_pos hs
  obtain ⟨δ, hδpos, hδprop⟩ :=
    Complex.exists_pos_radius_forall_mem_ball_re_ge (z₀ := s) (a := ε) (half_lt_self hs)
  set F : ℂ → ℝ → ℂ := zetaAbelFractKernel
  set F' : ℂ → ℝ → ℂ := fun z u => -((Real.log u) : ℂ) * F z u
  set bound : ℝ → ℝ := fun u => (2 / ε) * u ^ (-1 - ε / 2)
  have hbound_int : Integrable bound (volume.restrict (Ioi (1 : ℝ))) := by
    simpa [bound, IntegrableOn] using
      (integrableOn_Ioi_rpow_of_lt (by linarith [half_pos hεpos]) one_pos).const_mul (2 / ε)
  have hDiff : ∀ᶠ z in 𝓝 s, DifferentiableAt ℂ (fun z0 => ∫ u in Ioi (1 : ℝ), F z0 u) z := by
    refine Filter.eventually_of_mem (Metric.ball_mem_nhds s (half_pos hδpos)) ?_
    intro z hz
    set δ' : ℝ := δ / 2
    have hz_lt : dist z s < δ := dist_lt_of_mem_ball_half hz hδpos
    have hRe : ∀ y ∈ Metric.ball z δ', ε ≤ y.re := fun y hy =>
      hδprop z y hz_lt (dist_lt_of_mem_ball_half hy hδpos)
    have hzRe : ε ≤ z.re := hδprop s z (by simpa [dist_self] using hδpos) hz_lt
    exact (hasDerivAt_integral_param_dominated_Ioi F F' z δ' (half_pos hδpos)
      (eventually_aestronglyMeasurable_param z)
      (by simpa using integrableOn_Ioi z (lt_of_lt_of_le hεpos hzRe))
      (by simpa [F, F'] using aestronglyMeasurable_param_deriv z)
      bound hbound_int
      (ae_on_Ioi_of_all fun u hu w hw =>
        (kernel_deriv_norm_bound_on_ball ε u hu w (hRe w hw)).trans
          (by simpa [bound] using Real.log_mul_rpow_neg_le_two_div_mul_rpow_neg hεpos hu))
      (ae_on_Ioi_of_all fun u hu w hw => by simpa [F, F'] using hasDerivAt_in_param u hu w)).differentiableAt
  exact (Complex.analyticAt_iff_eventually_differentiableAt
    (f := fun z => ∫ u in Ioi (1 : ℝ), zetaAbelFractKernel z u)).2 hDiff

end ZetaAbelFractKernel
end
end File57

-- Upstream module PrimeNumberTheoremAnd.Mathlib.NumberTheory.AbelSummation
section File58
 

section
open Finset
open scoped BigOperators

variable {𝕜 : Type*} [AddCommGroup 𝕜]

theorem Finset.sum_Icc_one_eq_sum_range {N : ℕ} (f : ℕ → 𝕜) :
    ∑ k ∈ Icc 1 N, f k = ∑ n ∈ range N, f (n + 1) := by
  symm
  refine sum_bij (s := range N) (t := Icc 1 N)
    (f := fun n => f (n + 1)) (g := fun k => f k)
    (i := fun n _ => n + 1)
    ?hi ?hinj ?hsurj ?hcongr
  · intro n hn
    have hlt : n < N := mem_range.mp hn
    exact mem_Icc.mpr ⟨Nat.succ_le_succ (Nat.zero_le n), Nat.succ_le_of_lt hlt⟩
  · intro a ha b hb h
    exact Nat.succ_injective h
  · intro k hk
    rcases mem_Icc.mp hk with ⟨hk1, hk2⟩
    refine ⟨k - 1, mem_range.mpr ?_, ?_⟩
    · have hsucc : (k - 1) + 1 = k := Nat.sub_add_cancel hk1
      exact lt_of_lt_of_le (Nat.lt_succ_self _) (by simpa [hsucc] using hk2)
    · simp [Nat.sub_add_cancel hk1]
  · intro n hn
    rfl

theorem Finset.sum_Icc_zero_eq_sum_Icc_one {N : ℕ} {f : ℕ → 𝕜} (h0 : f 0 = 0) :
    ∑ k ∈ Icc 0 N, f k = ∑ k ∈ Icc 1 N, f k := by
  have hdecomp : insert 0 (Icc 1 N) = Icc 0 N := by
    simpa [Nat.succ_eq_add_one] using
      insert_Icc_succ_left_eq_Icc (a := 0) (b := N) (h := Nat.zero_le N)
  have hnotmem : (0 : ℕ) ∉ Icc 1 N := by
    intro h
    exact (not_le.mpr (Nat.lt_succ_self 0)) (mem_Icc.mp h).1
  calc
    ∑ k ∈ Icc 0 N, f k = ∑ k ∈ insert 0 (Icc 1 N), f k := by simp [hdecomp]
    _ = f 0 + ∑ k ∈ Icc 1 N, f k := by simp
    _ = ∑ k ∈ Icc 1 N, f k := by simp [h0]

theorem Finset.sum_Icc_zero_eq_sum_range_succ {m : ℕ} {f : ℕ → 𝕜} (h0 : f 0 = 0) :
    ∑ k ∈ Icc 0 m, f k = ∑ n ∈ range m, f (n + 1) := by
  rw [sum_Icc_zero_eq_sum_Icc_one h0, sum_Icc_one_eq_sum_range]

theorem sum_Icc_zero_floor_eq_sum_range {c : ℕ → 𝕜} (hc0 : c 0 = 0) (t : ℝ) :
    ∑ k ∈ Icc 0 ⌊t⌋₊, c k = ∑ n ∈ range ⌊t⌋₊, c (n + 1) :=
  Finset.sum_Icc_zero_eq_sum_range_succ (m := ⌊t⌋₊) (f := c) hc0
end
end File58

-- Upstream module PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.RiemannZetaPartialSum
section File59
 

section
open scoped BigOperators Topology
open Real Set Filter Topology MeasureTheory Complex Nat ZetaAbelFractKernel

noncomputable def zetaPartialSum (s : ℂ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.range N, (n + 1 : ℂ) ^ (-s)

namespace ZetaPartialSum

private lemma natCast_floor_eq_sub_fract (u : ℝ) (hu : 0 ≤ u) :
    (Nat.floor u : ℂ) = (u : ℂ) - ((Int.fract u : ℝ) : ℂ) := by
  have hfloorR : (Nat.floor u : ℝ) = (Int.floor u : ℝ) := by
    simpa using natCast_floor_eq_intCast_floor (R := ℝ) (a := u) hu
  have hfloorC : (Nat.floor u : ℂ) = ((Int.floor u : ℝ) : ℂ) := congrArg (fun x : ℝ => (x : ℂ)) hfloorR
  have hIFR : (Int.floor u : ℝ) = u - Int.fract u := (eq_sub_iff_add_eq).2 (Int.floor_add_fract u)
  have hIFC : ((Int.floor u : ℝ) : ℂ) = ((u - Int.fract u : ℝ) : ℂ) := congrArg (fun x : ℝ => (x : ℂ)) hIFR
  exact hfloorC.trans (by simpa [sub_eq_add_neg] using hIFC)

private lemma intervalIntegrable_mul_cpow_id (s : ℂ) {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun u : ℝ => (u : ℂ) * (u : ℂ) ^ (-s - 1)) volume a b := by
  have hcont : ContinuousOn (fun u : ℝ => (u : ℂ) * (u : ℂ) ^ (-s - 1)) (Icc a b) :=
    Complex.continuous_ofReal.continuousOn.mul
      (Complex.continuousOn_ofReal_cpow (r := -s - 1) (ha := one_pos.trans_le ha))
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le (μ := volume) (a := a) (b := b)
    (f := fun u : ℝ => (u : ℂ) * (u : ℂ) ^ (-s - 1)) hab).2
    (hcont.integrableOn_compact isCompact_Icc)

private lemma abel_summation (s : ℂ) (N : ℕ) (hN : 1 ≤ N) :
    zetaPartialSum s N
      = (N : ℂ) * (N : ℂ) ^ (-s)
        - ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (-s * (u : ℂ) ^ (-s - 1)) := by
  set f : ℝ → ℂ := fun u => (u : ℂ) ^ (-s)
  let c : ℕ → ℂ := fun k => if k = 0 then 0 else (1 : ℂ)
  have hle : (1 : ℝ) ≤ N := mod_cast hN
  have hdiff : ∀ t ∈ Set.Icc (1 : ℝ) N, DifferentiableAt ℝ f t := fun t ht => by
    by_cases hs : s = 0; · simp [f, hs]
    simpa [f] using (hasDerivAt_ofReal_cpow_const (lt_of_lt_of_le zero_lt_one ht.1).ne'
      (neg_ne_zero.mpr hs)).differentiableAt
  have hint : IntegrableOn (deriv f) (Set.Icc (1 : ℝ) (N : ℝ)) :=
    (Complex.continuousOn_deriv_ofReal_cpow_neg (s := s) (a := (1 : ℝ)) (b := (N : ℝ)) zero_lt_one).integrableOn_compact
      isCompact_Icc
  have habel :=
    sum_mul_eq_sub_integral_mul₀' (c := c) (f := f) (m := N)
      (hc := by simp [c]) (hf_diff := hdiff) (hf_int := hint)
  have hLHS : (∑ k ∈ Finset.Icc 0 N, f k * c k) = zetaPartialSum s N := by
    rw [Finset.sum_Icc_zero_eq_sum_range_succ (by simp [c])]
    simp [zetaPartialSum, f, c]
  have hInt_congr :
      (∫ u in (1 : ℝ)..N, deriv f u * ∑ k ∈ Finset.Icc 0 ⌊u⌋₊, c k)
        = ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (-s * (u : ℂ) ^ (-s - 1)) := by
    apply intervalIntegral.integral_congr_Ioc_of_le hle
    intro u hu
    rw [sum_Icc_zero_floor_eq_sum_range (hc0 := by simp [c]) u, Complex.deriv_ofReal_cpow_neg s (lt_trans zero_lt_one hu.1)]
    simp [c, Finset.sum_const, Finset.card_range, mul_comm, mul_left_comm]
  calc
    zetaPartialSum s N
        = f N * (∑ k ∈ Finset.Icc 0 N, c k)
            - ∫ u in (1 : ℝ)..N, deriv f u * ∑ k ∈ Finset.Icc 0 ⌊u⌋₊, c k := by
          simpa [hLHS] using habel.trans (by rw [← intervalIntegral.integral_of_le hle])
    _ = f N * (∑ k ∈ Finset.Icc 0 N, c k)
            - ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (-s * (u : ℂ) ^ (-s - 1)) := by
          rw [hInt_congr]
    _ = (N : ℂ) * (N : ℂ) ^ (-s)
            - ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (-s * (u : ℂ) ^ (-s - 1)) := by
          have hMain : f N * (∑ k ∈ Finset.Icc 0 N, c k) = (N : ℂ) * f N := by
            rw [Finset.sum_Icc_zero_eq_sum_range_succ (by simp [c])]
            simp [c, f, Finset.sum_const, Finset.card_range, mul_comm]
          rw [hMain]; simp [f]

private lemma abel_split (s : ℂ) (N : ℕ) (hN : 1 ≤ N) :
    zetaPartialSum s N = (N : ℂ) ^ (1 - s) + s * ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (u : ℂ) ^ (-s - 1) := by
  rw [abel_summation s N hN]
  have hInt :
      ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (-s * (u : ℂ) ^ (-s - 1))
        = (-s) * ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (u : ℂ) ^ (-s - 1) := by
    rw [← intervalIntegral.integral_const_mul, intervalIntegral.integral_congr_Ioc_of_le (mod_cast hN)]
    intro u _; simp [neg_mul, mul_left_comm]
  rw [hInt, sub_eq_add_neg, neg_mul, neg_neg]
  simp [Complex.natCast_mul_cpow_neg_eq_cpow_one_sub N s (Nat.ne_of_gt (Nat.succ_le_iff.mp hN))]

private lemma integral_split_fract (s : ℂ) (N : ℕ) (hN : 1 ≤ N) :
    ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (u : ℂ) ^ (-s - 1)
      = (∫ u in (1 : ℝ)..N, (u : ℂ) ^ (-s))
        - ∫ u in (1 : ℝ)..N, zetaAbelFractKernel s u := by
  have hab : (1 : ℝ) ≤ N := mod_cast hN
  have hI1 := intervalIntegrable_mul_cpow_id s le_rfl hab
  have hI2 := ZetaAbelFractKernel.intervalIntegrable s le_rfl hab
  calc
    ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (u : ℂ) ^ (-s - 1)
        = ∫ u in (1 : ℝ)..N, ((u : ℂ) - ((Int.fract u : ℝ) : ℂ)) * (u : ℂ) ^ (-s - 1) := by
          apply intervalIntegral.integral_congr_Ioc_of_le hab
          intro u hu
          simp [natCast_floor_eq_sub_fract u (le_trans zero_le_one (le_of_lt hu.1)), sub_eq_add_neg]
    _ = (∫ u in (1 : ℝ)..N, (u : ℂ) * (u : ℂ) ^ (-s - 1))
          - ∫ u in (1 : ℝ)..N, zetaAbelFractKernel s u := by
          rw [← intervalIntegral.integral_sub hI1 hI2]
          apply intervalIntegral.integral_congr_Ioc_of_le hab
          intro u _; simp [sub_mul, zetaAbelFractKernel]
    _ = (∫ u in (1 : ℝ)..N, (u : ℂ) ^ (-s))
          - ∫ u in (1 : ℝ)..N, zetaAbelFractKernel s u := by
          congr 1
          apply intervalIntegral.integral_congr_Ioc_of_le hab
          intro u hu
          exact Complex.ofReal_cpow_mul_cpow_neg_sub_one (s := s) (hu := lt_trans zero_lt_one hu.1)

private lemma cpow_integral (s : ℂ) (hs : s ≠ 1) (N : ℕ) (hN : 1 ≤ N) :
    s * ∫ u in (1 : ℝ)..N, (u : ℂ) ^ (-s) = s / (1 - s) * ((N : ℂ) ^ (1 - s) - 1) := by
  have h01leN : (1 : ℝ) ≤ (N : ℝ) := mod_cast hN
  have hint : ∫ u in (1 : ℝ)..N, (u : ℂ) ^ (-s)
      = ((N : ℂ) ^ ((-s) + 1) - (1 : ℂ) ^ ((-s) + 1)) / ((-s) + 1) := by
    have hrne : -s ≠ (-1 : ℂ) := fun h => hs (neg_inj.mp h)
    simpa using integral_cpow (a := (1 : ℝ)) (b := (N : ℝ)) (r := -s)
      (Or.inr ⟨hrne, by simp [uIcc_of_le h01leN]⟩)
  calc s * ∫ u in (1 : ℝ)..N, (u : ℂ) ^ (-s)
      = s * (((N : ℂ) ^ ((-s) + 1) - (1 : ℂ) ^ ((-s) + 1)) / ((-s) + 1)) := by
        simpa using congrArg (s * ·) hint
      _ = s * (((N : ℂ) ^ (1 - s) - 1) / (1 - s)) := by
        rw [one_cpow, show (1 : ℂ) - s = -s + 1 from by ring]
      _ = s / (1 - s) * ((N : ℂ) ^ (1 - s) - 1) := by field_simp

private lemma abel_sub_fract (s : ℂ) (N : ℕ) (hN : 1 ≤ N) :
    zetaPartialSum s N
      = (N : ℂ) ^ (1 - s)
        + (s * ∫ u in (1 : ℝ)..N, (u : ℂ) ^ (-s))
        - (s * ∫ u in (1 : ℝ)..N, zetaAbelFractKernel s u) := by
  rw [abel_split s N hN, integral_split_fract s N hN, mul_sub, add_sub_assoc]

theorem abel_formula (s : ℂ) (hs : s ≠ 1) (N : ℕ) (hN : 1 ≤ N) :
    zetaPartialSum s N
      = (N : ℂ) ^ (1 - s) / (1 - s) + 1 + 1 / (s - 1)
        - s * ∫ u in (1 : ℝ)..N, zetaAbelFractKernel s u := by
  have hstep := abel_sub_fract s N hN
  rw [cpow_integral s hs N hN] at hstep
  let A := (N : ℂ) ^ (1 - s)
  have halg : A + s / (1 - s) * (A - 1) = A / (1 - s) + 1 + 1 / (s - 1) := by
    field_simp [sub_ne_zero.mpr hs, sub_ne_zero.mpr hs.symm]; ring
  rwa [halg] at hstep

lemma tendsto_natCast_cpow_zero_of_neg_re (w : ℂ) (hw : w.re < 0) :
    Tendsto (fun N : ℕ => (N : ℂ) ^ w) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h1 : (fun N : ℕ => (N : ℝ) ^ w.re) =ᶠ[atTop] fun N : ℕ => ‖(N : ℂ) ^ w‖ := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    rw [Complex.norm_natCast_cpow_of_pos hN w]
  rw [tendsto_congr' (EventuallyEq.symm h1)]
  rw [show w.re = -(-w.re) from by ring]
  exact (tendsto_rpow_neg_atTop (neg_pos.mpr hw)).comp tendsto_natCast_atTop_atTop

theorem tendsto_riemannZeta (s : ℂ) (hs : 1 < s.re) :
    Tendsto (fun N : ℕ => zetaPartialSum s N) atTop (𝓝 (riemannZeta s)) := by
  set g : ℕ → ℂ := fun n => if n = 0 then 0 else (n : ℂ) ^ (-s)
  set h : ℕ → ℂ := fun n => (n + 1 : ℂ) ^ (-s)
  have hsne : s ≠ 0 := by
    intro h0
    have : (0 : ℝ) < s.re := lt_trans (show (0 : ℝ) < 1 by norm_num) hs
    simpa [h0] using ne_of_gt this
  have hgSumm : Summable g := by
    simpa [g, one_div_natCast_cpow_eq_ite_cpow_neg s hsne] using
      (Complex.summable_one_div_nat_cpow (p := s)).2 hs
  have hhSumm : Summable h := by
    have : Summable (fun n => g (n + 1)) := (summable_nat_add_iff (f := g) (k := 1)).2 hgSumm
    simpa [Function.comp_apply, h, g] using this
  have hg0 : g 0 = 0 := by simp [g]
  have h_tsum_eq : (∑' n, h n) = ∑' n, g n := by
    have : (∑' n, g n) = ∑' n, g (n + 1) := by simpa [hg0, add_comm] using Summable.tsum_eq_zero_add hgSumm
    simpa [h, g] using this.symm
  have hzeta : riemannZeta s = ∑' n, g n := by
    simpa [g, one_div_natCast_cpow_eq_ite_cpow_neg s hsne] using
      zeta_eq_tsum_one_div_nat_cpow (s := s) hs
  simpa [zetaPartialSum, h, h_tsum_eq.trans hzeta.symm] using Summable.tendsto_sum_tsum_nat hhSumm

end ZetaPartialSum
end
end File59

-- Upstream module PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.RiemannZetaAbelContinuation
section File60
 

section
open scoped Topology
open Real Set Filter Topology MeasureTheory Complex ZetaPartialSum ZetaAbelFractKernel

noncomputable def zetaAbelContinuationReLower : ℝ := 1 / 10

theorem zetaAbelContinuationReLower_pos : 0 < zetaAbelContinuationReLower := by
  change 0 < (1 / 10 : ℝ)
  norm_num

theorem one_lt_zetaAbelContinuationReLower : zetaAbelContinuationReLower < (1 : ℝ) := by
  change (1 / 10 : ℝ) < 1
  norm_num

theorem one_sub_zetaAbelContinuationReLower :
    (1 - zetaAbelContinuationReLower : ℝ) = 9 / 10 := by
  change (1 - 1 / 10 : ℝ) = 9 / 10
  norm_num

theorem zetaAbelContinuationReLower_lt_half : zetaAbelContinuationReLower < (2⁻¹ : ℝ) := by
  change (1 / 10 : ℝ) < (2⁻¹ : ℝ)
  norm_num

def zetaAbelContinuationDomain : Set ℂ :=
  {s | s ≠ (1 : ℂ) ∧ zetaAbelContinuationReLower < s.re}

theorem isOpen_zetaAbelContinuationDomain : IsOpen zetaAbelContinuationDomain := by
  change IsOpen ({s : ℂ | s ≠ 1} ∩ {s : ℂ | zetaAbelContinuationReLower < s.re})
  exact isOpen_compl_singleton.inter (isOpen_lt continuous_const Complex.continuous_re)

theorem isPreconnected_zetaAbelContinuationDomain : IsPreconnected zetaAbelContinuationDomain := by
  convert (Complex.isPathConnected_halfSpace_re_gt_diff_singleton
      (a := zetaAbelContinuationReLower) (p := (1 : ℂ)) one_lt_zetaAbelContinuationReLower).isConnected.isPreconnected using 1
  ext z; simp [zetaAbelContinuationDomain, and_comm]

theorem two_mem_zetaAbelContinuationDomain : (2 : ℂ) ∈ zetaAbelContinuationDomain := by
  refine ⟨by norm_num, ?_⟩
  change (1 / 10 : ℝ) < (2 : ℂ).re
  norm_num

theorem zetaAbelContinuationDomain_re_pos {s : ℂ} (hs : s ∈ zetaAbelContinuationDomain) :
    0 < s.re := lt_trans zetaAbelContinuationReLower_pos hs.2

theorem mem_zetaAbelContinuationDomain_of_re {s : ℂ} (hs_ne : s ≠ 1)
    (hs_re : zetaAbelContinuationReLower < s.re) : s ∈ zetaAbelContinuationDomain :=
  ⟨hs_ne, hs_re⟩

theorem norm_div_re_le_ten_mul_norm_of_mem {z : ℂ} (hz : z ∈ zetaAbelContinuationDomain) :
    ‖z‖ / z.re ≤ 10 * ‖z‖ := by
  rw [div_eq_mul_inv, mul_comm]
  gcongr
  calc
    z.re⁻¹ = 1 / z.re := by rw [one_div]
    _ ≤ 1 / zetaAbelContinuationReLower :=
      one_div_le_one_div_of_le zetaAbelContinuationReLower_pos (le_of_lt hz.2)
    _ = 10 := by
      change (1 / (1 / 10 : ℝ)) = 10
      norm_num

noncomputable def zetaAbelContinuationFormula (s : ℂ) : ℂ :=
  1 + 1 / (s - 1) - s * ∫ u in Ioi (1 : ℝ), zetaAbelFractKernel s u

theorem riemannZeta_abel_integral (s : ℂ) (hs : 1 < s.re) :
    riemannZeta s = zetaAbelContinuationFormula s := by
  have hsne : s ≠ 1 := by
    intro h
    have hre : s.re = 1 := by simp [h]
    linarith
  set G : ℕ → ℂ := fun N =>
    (N : ℂ) ^ (1 - s) / (1 - s) + 1 + 1 / (s - 1)
      - s * ∫ u in (1 : ℝ)..N, zetaAbelFractKernel s u
  have hEv : ∀ᶠ N in atTop, zetaPartialSum s N = G N :=
    (eventually_ge_atTop 1).mono fun N hN => (abel_formula s hsne N hN).trans rfl
  have hG_to_zeta := (tendsto_congr' hEv).mp (tendsto_riemannZeta s hs)
  have hA : Tendsto (fun N : ℕ => (N : ℂ) ^ (1 - s) / (1 - s)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv, mul_comm] using
      (Tendsto.const_mul (1 / (1 - s))
        (tendsto_natCast_cpow_zero_of_neg_re (1 - s)
          (by rw [Complex.sub_re, Complex.one_re]; linarith)))
  have hK : Tendsto (fun _ : ℕ => (1 + 1 / (s - 1) : ℂ)) atTop
      (𝓝 (1 + 1 / (s - 1))) := tendsto_const_nhds
  have hIntMul := (tendsto_integral_Ioi s hs).const_mul s
  set Aseq : ℕ → ℂ := fun N => (N : ℂ) ^ (1 - s) / (1 - s)
  set Kseq : ℕ → ℂ := fun _ => (1 + 1 / (s - 1) : ℂ)
  set Iseq : ℕ → ℂ := fun N => s * ∫ u in (1 : ℝ)..N, zetaAbelFractKernel s u
  have hSum : Tendsto (fun N => Aseq N + Kseq N) atTop (𝓝 (1 + 1 / (s - 1))) := by
    simpa using! ((continuous_fst.add continuous_snd).tendsto _).comp (hA.prodMk_nhds hK)
  have hG_limit : Tendsto G atTop
      (𝓝 ((1 + 1 / (s - 1)) - s * ∫ u in Ioi (1 : ℝ), zetaAbelFractKernel s u)) := by
    have hSub : Tendsto (fun N => Aseq N + Kseq N - Iseq N) atTop
        (𝓝 ((1 + 1 / (s - 1)) - s * ∫ u in Ioi (1 : ℝ), zetaAbelFractKernel s u)) := by
      simpa [Function.comp_apply, Function.comp_def, sub_eq_add_neg] using
        ((continuous_fst.add continuous_snd).tendsto _).comp (hSum.prodMk_nhds hIntMul.neg)
    have hGdef : (fun N => Aseq N + Kseq N - Iseq N) = G := by
      funext N
      simp [Aseq, Kseq, Iseq, G, add_comm, add_left_comm, add_assoc, sub_eq_add_neg]
    simpa [hGdef] using hSub
  have huniq := tendsto_nhds_unique hG_to_zeta hG_limit
  simpa [zetaAbelContinuationFormula, sub_eq_add_neg] using huniq

theorem norm_zetaAbelContinuationFormula_le (s : ℂ) (hs : s ∈ zetaAbelContinuationDomain) :
    ‖zetaAbelContinuationFormula s‖ ≤ 1 + ‖1 / (s - 1)‖ + ‖s‖ / s.re := by
  set g : ℝ → ℝ := fun u => u ^ (-s.re - 1)
  let μ := (volume : Measure ℝ).restrict (Ioi (1 : ℝ))
  have hs_re := zetaAbelContinuationDomain_re_pos hs
  have hint :
      ‖s‖ * ‖∫ u in Ioi (1 : ℝ), zetaAbelFractKernel s u‖ ≤ ‖s‖ / s.re :=
    mul_le_mul_of_nonneg_left
      ((MeasureTheory.norm_integral_le_of_norm_le (μ := μ)
        (f := fun u => zetaAbelFractKernel s u) (g := g)
        (by
          simpa [μ, g, IntegrableOn] using
            (integrableOn_Ioi_rpow_of_lt (by linarith) one_pos))
        (by
          refine (ae_restrict_iff' measurableSet_Ioi).2 (MeasureTheory.ae_of_all _ ?_)
          intro u hu
          simpa [g] using norm_zetaAbelFractKernel_le u (le_of_lt hu) s)).trans
        (by change (∫ u in Ioi (1 : ℝ), u ^ (-s.re - 1)) ≤ s.re⁻¹; simpa only [one_div] using (integral_Ioi_rpow_neg_re_sub_one hs_re).le))
      (norm_nonneg s)
  have hsplit :
      ‖zetaAbelContinuationFormula s‖ ≤
        1 + ‖(s - 1)⁻¹‖ + ‖s‖ * ‖∫ u in Ioi (1 : ℝ), zetaAbelFractKernel s u‖ := by
    simp only [zetaAbelContinuationFormula, one_div]
    calc
      ‖1 + (s - 1)⁻¹ - s * ∫ u in Ioi (1 : ℝ), zetaAbelFractKernel s u‖
          ≤ ‖1 + (s - 1)⁻¹‖ + ‖-s * ∫ u in Ioi (1 : ℝ), zetaAbelFractKernel s u‖ := by
            simpa [sub_eq_add_neg] using
              norm_add_le (1 + (s - 1)⁻¹) (-s * ∫ u in Ioi (1 : ℝ), zetaAbelFractKernel s u)
      _ ≤ 1 + ‖(s - 1)⁻¹‖ + ‖s‖ * ‖∫ u in Ioi (1 : ℝ), zetaAbelFractKernel s u‖ := by
        gcongr
        · simpa [norm_one] using norm_add_le (1 : ℂ) ((s - 1)⁻¹)
        · exact (norm_mul_le (-s) (∫ u in Ioi (1 : ℝ), zetaAbelFractKernel s u)).trans_eq
            (by rw [norm_neg])
  calc
    ‖zetaAbelContinuationFormula s‖
        ≤ 1 + ‖(s - 1)⁻¹‖ + ‖s‖ * ‖∫ u in Ioi (1 : ℝ), zetaAbelFractKernel s u‖ := hsplit
    _ ≤ 1 + ‖(s - 1)⁻¹‖ + ‖s‖ / s.re := add_le_add_right hint _
    _ ≤ 1 + ‖1 / (s - 1)‖ + ‖s‖ / s.re := by simp [one_div]

set_option maxHeartbeats 1000000 in
theorem analyticOn_zetaAbelContinuationFormula :
    AnalyticOn ℂ zetaAbelContinuationFormula zetaAbelContinuationDomain := by
  intro s hs
  have ha : AnalyticAt ℂ (fun z : ℂ => z - 1) s :=
    analyticAt_id.sub analyticAt_const
  have hq : AnalyticAt ℂ (fun z : ℂ => 1 / (z - 1)) s :=
    (analyticAt_const (v := (1 : ℂ))).div ha (sub_ne_zero.mpr hs.1)
  have hi := integral_analytic s (zetaAbelContinuationDomain_re_pos hs)
  have hprod : AnalyticAt ℂ (fun z : ℂ => z * ∫ u in Ioi (1 : ℝ), zetaAbelFractKernel z u) s :=
    analyticAt_id.mul hi
  have hsum : AnalyticAt ℂ (fun z : ℂ => 1 + 1 / (z - 1)) s :=
    analyticAt_const.add hq
  exact (hsum.sub hprod).analyticWithinAt

theorem riemannZeta_eq_zetaAbelContinuationFormula (s : ℂ) (hs : s ∈ zetaAbelContinuationDomain) :
    riemannZeta s = zetaAbelContinuationFormula s := by
  have hUo := isOpen_zetaAbelContinuationDomain
  have hζ : AnalyticOnNhd ℂ riemannZeta zetaAbelContinuationDomain := by
    rw [← hUo.analyticOn_iff_analyticOnNhd]
    have h : AnalyticOn ℂ riemannZeta ({1} : Set ℂ)ᶜ :=
      isOpen_compl_singleton.analyticOn_iff_analyticOnNhd.mpr analyticOn_riemannZeta
    exact AnalyticOn.mono h fun _ hz => hz.1
  have hF : AnalyticOnNhd ℂ zetaAbelContinuationFormula zetaAbelContinuationDomain := by
    rw [← hUo.analyticOn_iff_analyticOnNhd]
    exact analyticOn_zetaAbelContinuationFormula
  have hEq : riemannZeta =ᶠ[𝓝 (2 : ℂ)] zetaAbelContinuationFormula := by
    have hopen : IsOpen {w : ℂ | 1 < w.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds (by norm_num : (1 : ℝ) < (2 : ℂ).re)] with w hw
      using riemannZeta_abel_integral w hw
  exact (AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
    hζ hF isPreconnected_zetaAbelContinuationDomain two_mem_zetaAbelContinuationDomain hEq) hs
end
end File60

-- Upstream module PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.RiemannZetaConvexity
section File61
 

section
open scoped BigOperators Topology
open Real Set Filter Topology MeasureTheory Complex

theorem norm_riemannZeta_ratio_le_on_verticalLine (σ t : ℝ) (hσ : 1 < σ) :
    ‖riemannZeta (2 * (σ : ℂ)) / riemannZeta (σ : ℂ)‖ ≤ ‖riemannZeta (verticalLine σ t)‖ := by
  have hs : 1 < (verticalLine σ t).re := by rw [verticalLine_re]; exact hσ
  calc
    ‖riemannZeta (2 * (σ : ℂ)) / riemannZeta (σ : ℂ)‖
        = ∏' p : Nat.Primes, (1 + ((p : ℕ) : ℝ) ^ (-σ))⁻¹ :=
          norm_riemannZeta_div_riemannZeta σ hσ
    _ ≤ ∏' p : Nat.Primes, (‖1 - ((p : ℕ) : ℂ) ^ (-verticalLine σ t)‖)⁻¹ :=
        tprod_inv_one_add_real_le_riemannZeta_norm_on_verticalLine σ t hσ
    _ = ‖riemannZeta (verticalLine σ t)‖ := by
      simpa [verticalLine] using (norm_riemannZeta_eulerProduct (verticalLine σ t) hs).symm

theorem norm_riemannZeta_ratio_le_on_vertical_line (t : ℝ) :
    ‖riemannZeta 3 / riemannZeta ((3 : ℝ) / 2)‖ ≤ ‖riemannZeta (verticalLine (3 / 2 : ℝ) t)‖ := by
  have hσ : 1 < (3 / 2 : ℝ) := by norm_num
  have h2 : (2 : ℂ) * ((3 / 2 : ℝ) : ℂ) = (3 : ℂ) := by norm_num
  simpa [h2, div_eq_mul_inv, mul_comm] using
    norm_riemannZeta_ratio_le_on_verticalLine (3 / 2 : ℝ) t hσ

theorem norm_riemannZeta_le (s : ℂ) (hs : s ∈ zetaAbelContinuationDomain) :
    ‖riemannZeta s‖ ≤ 1 + ‖1 / (s - 1)‖ + ‖s‖ / s.re := by
  rw [riemannZeta_eq_zetaAbelContinuationFormula s hs]
  exact norm_zetaAbelContinuationFormula_le s hs

namespace StripBounds

private lemma three_sq_add_sq_le_sq_add_abs (t : ℝ) :
    (3 : ℝ) ^ 2 + t ^ 2 ≤ (3 + |t|) ^ 2 := by
  nlinarith [abs_nonneg t, sq_abs t, sq_nonneg (3 + |t|)]

private lemma norm_lt_three_add_abs_im (s : ℂ) (hs : (1 / 2 : ℝ) ≤ s.re ∧ s.re < (3 : ℝ)) :
    ‖s‖ < (3 : ℝ) + |s.im| := by
  have hneg : (-(3 : ℝ)) < s.re := by linarith [hs.1]
  have hre : s.re ^ 2 < (3 : ℝ) ^ 2 := sq_lt_sq' hneg hs.2
  have hsum : s.re ^ 2 + s.im ^ 2 < (3 : ℝ) ^ 2 + s.im ^ 2 := (add_lt_add_iff_right _).mpr hre
  have hsq : Complex.normSq s < (3 + |s.im|) ^ 2 := by
    have := lt_of_lt_of_le hsum (three_sq_add_sq_le_sq_add_abs s.im)
    simpa [Complex.normSq_apply, pow_two] using this
  exact (sq_lt_sq₀ (norm_nonneg s) (by positivity)).1 (by rwa [Complex.sq_norm])

private lemma one_div_re_le_two (s : ℂ) (hs : (1 / 2 : ℝ) ≤ s.re ∧ s.re < (3 : ℝ)) :
    1 / s.re ≤ (2 : ℝ) := by
  have hpos : 0 < s.re := by linarith [hs.1]
  calc
    1 / s.re ≤ 1 / (1 / 2 : ℝ) := one_div_le_one_div_of_le (by norm_num) hs.1
    _ = 2 := by norm_num

private lemma one_le_norm_sub_one (s : ℂ) (hs_im : (1 : ℝ) ≤ |s.im|) :
    (1 : ℝ) ≤ ‖s - 1‖ := by
  have : |s.im| ≤ ‖s - 1‖ := by
    simpa [Complex.sub_im, Complex.one_im] using Complex.abs_im_le_norm (s - 1)
  exact le_trans hs_im this

private lemma norm_lt_linear_im (s : ℂ) (hs_re : (1 / 2 : ℝ) ≤ s.re ∧ s.re < (3 : ℝ))
    (hs_im : (1 : ℝ) ≤ |s.im|) :
    ‖riemannZeta s‖ < (1 : ℝ) + 1 + ((3 : ℝ) + |s.im|) * 2 := by
  have hs_ne : s ≠ 1 := by
    intro h; rw [h] at hs_im; simp [Complex.one_im] at hs_im; linarith
  have hσ : zetaAbelContinuationReLower < s.re :=
    lt_of_lt_of_le zetaAbelContinuationReLower_lt_half (by simpa using hs_re.1)
  calc
    ‖riemannZeta s‖
        ≤ 1 + 1 / ‖s - 1‖ + ‖s‖ / s.re := by
          simpa [one_div] using norm_riemannZeta_le s (mem_zetaAbelContinuationDomain_of_re hs_ne hσ)
    _ ≤ 1 + 1 + ‖s‖ / s.re := by
      gcongr
      simpa [one_div] using inv_le_one_of_one_le₀ (one_le_norm_sub_one s hs_im)
    _ ≤ 1 + 1 + ‖s‖ * 2 := by
      gcongr
      rw [div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_left (one_div_re_le_two s hs_re) (norm_nonneg s)
    _ < 1 + 1 + ((3 : ℝ) + |s.im|) * 2 := by
      gcongr
      exact norm_lt_three_add_abs_im s hs_re

end StripBounds

open StripBounds

theorem norm_riemannZeta_lt_linear_im_on_strip (z : ℂ)
    (hz_re : z.re ∈ Ico (1 / 2 : ℝ) (3 : ℝ)) (hz_im : (1 : ℝ) ≤ |z.im|) :
    ‖riemannZeta z‖ < (8 : ℝ) + 2 * |z.im| := by
  have hz_re' : (1 / 2 : ℝ) ≤ z.re ∧ z.re < (3 : ℝ) := by simpa [Ico] using hz_re
  calc
    ‖riemannZeta z‖
        < (1 : ℝ) + 1 + ((3 : ℝ) + |z.im|) * 2 := norm_lt_linear_im z hz_re' hz_im
    _ = (8 : ℝ) + 2 * |z.im| := by ring

private lemma shift_mem_strip (s : ℂ) (t : ℝ) (hs : ‖s‖ ≤ 1) (ht : (2 : ℝ) < |t|) :
    let z := verticalLine (s.re + (3 / 2 : ℝ)) (s.im + t)
    z.re ∈ Ico (1 / 2 : ℝ) (3 : ℝ) ∧ (1 : ℝ) ≤ |z.im| := by
  simp only [verticalLine_re, verticalLine_im, Set.mem_Ico]
  constructor
  · have h := (Complex.abs_re_le_norm s).trans hs
    rw [abs_le] at h
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  · have h := (Complex.abs_im_le_norm s).trans hs
    rw [abs_le] at h
    by_cases ht₀ : 0 ≤ t
    · have ht' : (2 : ℝ) < t := by rwa [abs_of_nonneg ht₀] at ht
      rw [abs_of_nonneg (by linarith : 0 ≤ s.im + t)]
      linarith [h.1, ht']
    · push Not at ht₀
      have ht' : t < (-2 : ℝ) := by
        rw [abs_of_neg ht₀] at ht
        linarith
      have hneg : s.im + t < 0 := by linarith [h.2, ht']
      rw [abs_of_neg hneg]
      linarith [h.2, ht']

theorem norm_riemannZeta_shift_le (t : ℝ) (s : ℂ) (hs : ‖s‖ ≤ 1) (ht : 2 < |t|) :
    ‖riemannZeta (s + (3 / 2 : ℝ) + Complex.I * t)‖ < 10 + 2 * |t| := by
  set z := verticalLine (s.re + (3 / 2 : ℝ)) (s.im + t)
  have hz : s + (3 / 2 : ℝ) + Complex.I * t = z := by
    simp only [z]
    conv_lhs => rw [mul_comm Complex.I t]
    exact verticalLine_add_const s (3 / 2) t
  have ⟨hz_re, hz_im⟩ := shift_mem_strip s t hs ht
  have hz_im_le : |z.im| ≤ 1 + |t| := by
    simp only [z, verticalLine_im]
    linarith [abs_add_le s.im t, (Complex.abs_im_le_norm s).trans hs]
  calc
    ‖riemannZeta (s + (3 / 2 : ℝ) + Complex.I * t)‖ = ‖riemannZeta z‖ := by rw [hz]
    _ < (8 : ℝ) + 2 * |z.im| := norm_riemannZeta_lt_linear_im_on_strip z hz_re hz_im
    _ ≤ (8 : ℝ) + 2 * (1 + |t|) := by gcongr
    _ = (10 : ℝ) + 2 * |t| := by ring
end
end File61

-- Upstream module PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.RiemannZetaStripBound
section File62

end File62

-- Upstream module PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.ZetaFiniteOrder
section File63
 

section
open Complex Set Filter Topology Metric
open scoped Real

namespace Complex

lemma completedRiemannZeta₀_bounded_on_closedBall (R : ℝ) (_hR : 0 < R) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ w : ℂ, ‖w‖ ≤ R → ‖completedRiemannZeta₀ w‖ ≤ M := by
  have hcont : ContinuousOn completedRiemannZeta₀ (Metric.closedBall 0 R) :=
    differentiable_completedZeta₀.continuous.continuousOn
  exact exists_norm_bound_on_closedBall hcont

lemma exists_completedRiemannZeta₀_right_halfPlane (z : ℂ) :
    ∃ w : ℂ,
      completedRiemannZeta₀ w = completedRiemannZeta₀ z ∧
        (2⁻¹ : ℝ) ≤ w.re ∧ ‖w‖ ≤ 1 + ‖z‖ := by
  refine ⟨if z.re < (2⁻¹ : ℝ) then 1 - z else z, ?_, ?_, ?_⟩
  · by_cases hzr : z.re < (2⁻¹ : ℝ)
    · have hw : (if z.re < (2⁻¹ : ℝ) then 1 - z else z) = 1 - z := by
        simp [hzr]
      simpa [hw] using (completedRiemannZeta₀_one_sub z)
    · simp [hzr]
  · by_cases hzr : z.re < (2⁻¹ : ℝ)
    · have : (if z.re < (2⁻¹ : ℝ) then 1 - z else z).re = 1 - z.re := by
        simp [hzr]
      linarith [this, hzr]
    · simpa [hzr] using le_of_not_gt hzr
  · by_cases hzr : z.re < (2⁻¹ : ℝ)
    · have hw : (if z.re < (2⁻¹ : ℝ) then 1 - z else z) = 1 - z := by
        simp [hzr]
      have : ‖1 - z‖ ≤ ‖(1 : ℂ)‖ + ‖z‖ := by
        simpa using (norm_sub_le (1 : ℂ) z)
      simpa [hw, norm_one, add_comm, add_left_comm, add_assoc] using this
    · simp [hzr]

lemma one_sub_re_ge_one_sub_zetaAbelContinuationReLower_of_re_le {z : ℂ}
    (hz : z.re ≤ zetaAbelContinuationReLower) :
    (1 - zetaAbelContinuationReLower) ≤ (1 - z).re := by
  have hz' : z.re ≤ (1 / 10 : ℝ) := by
    dsimp [zetaAbelContinuationReLower] at hz
    exact hz
  have h : (9 / 10 : ℝ) ≤ 1 - z.re := by linarith [hz']
  calc (1 - zetaAbelContinuationReLower : ℝ)
      = (9 / 10 : ℝ) := by
        norm_num [zetaAbelContinuationReLower, one_sub_zetaAbelContinuationReLower]
    _ ≤ 1 - z.re := h
    _ = (1 - z).re := by simp [Complex.sub_re]

lemma riemannZeta_eq_reflected {z w : ℂ} (hw : w = 1 - z)
    (hw_ne_neg : ∀ n : ℕ, w ≠ -n) (hw_ne_one : w ≠ 1) :
    riemannZeta z =
      2 * (2 * π) ^ (-w) * Complex.Gamma w * Complex.cos (π * w / 2) *
        riemannZeta w := by
  have h := riemannZeta_one_sub (s := w) (hs := hw_ne_neg) (hs' := hw_ne_one)
  have hsub : 1 - w = z := by
    rw [hw]
    ring
  simpa [hsub, mul_assoc, mul_left_comm, mul_comm] using h

lemma reflected_zeta_coefficient_le {C CΓ : ℝ} (hCΓ : 0 ≤ CΓ)
    (hC : max (40 : ℝ) (20 * CΓ + 500) ≤ C) :
    (2 + CΓ + 2 + 40 : ℝ) ≤ C := by
  have : (20 * CΓ + 500 : ℝ) ≤ C := le_trans (le_max_right _ _) hC
  nlinarith [this, hCΓ]

lemma norm_mul_riemannZeta_le_exp_of_reflected {z w : ℂ} {A CΓ C : ℝ}
    (hw : w = 1 - z)
    (hzeta_fe : riemannZeta z = 2 * (2 * π) ^ (-w) * Complex.Gamma w * Complex.cos (π * w / 2) *
      riemannZeta w)
    (hpow_le1 : ‖(2 * π : ℂ) ^ (-w)‖ ≤ 1)
    (hw_norm_le : ‖w‖ ≤ A) (hA1 : 1 ≤ A) (hA2_nonneg : 0 ≤ A ^ (2 : ℝ))
    (hΓw : ‖Complex.Gamma w‖ ≤ rexp (CΓ * A ^ (2 : ℝ)))
    (hcosw : ‖Complex.cos (π * w / 2)‖ ≤ rexp (2 * A ^ (2 : ℝ)))
    (hζw : ‖riemannZeta w‖ ≤ rexp (40 * A ^ (2 : ℝ)))
    (hcoef : (2 + CΓ + 2 + 40 : ℝ) ≤ C) :
    ‖(z - 1) * riemannZeta z‖ ≤ rexp (C * A ^ (2 : ℝ)) := by
  have hprod :
      ‖(z - 1) * riemannZeta z‖ ≤
        (‖w‖ * 2) * ‖Complex.Gamma w‖ *
          ‖Complex.cos (π * w / 2)‖ * ‖riemannZeta w‖ := by
    have hz1 : (z - 1 : ℂ) = -w := by
      rw [hw]
      ring
    have hζ :
        ‖riemannZeta z‖ ≤
          ‖2 * (2 * π) ^ (-w) * Complex.Gamma w *
            Complex.cos (π * w / 2) * riemannZeta w‖ := by
      simp [hzeta_fe]
    calc
      ‖(z - 1) * riemannZeta z‖
          ≤ ‖z - 1‖ * ‖riemannZeta z‖ := by simp
      _ ≤ ‖z - 1‖ *
            ‖2 * (2 * π) ^ (-w) * Complex.Gamma w *
              Complex.cos (π * w / 2) * riemannZeta w‖ := by
          gcongr
      _ = ‖w‖ *
            ‖2 * (2 * π) ^ (-w) * Complex.Gamma w *
              Complex.cos (π * w / 2) * riemannZeta w‖ := by
          simp [hz1]
      _ ≤ ‖w‖ * ((2 : ℝ) * ‖(2 * π : ℂ) ^ (-w)‖ *
            ‖Complex.Gamma w‖ * ‖Complex.cos (π * w / 2)‖ *
            ‖riemannZeta w‖) := by
          have :
              ‖2 * (2 * π) ^ (-w) * Complex.Gamma w *
                  Complex.cos (π * w / 2) * riemannZeta w‖
                ≤ (2 : ℝ) * ‖(2 * π : ℂ) ^ (-w)‖ *
                  ‖Complex.Gamma w‖ * ‖Complex.cos (π * w / 2)‖ *
                  ‖riemannZeta w‖ := by
            simp [mul_assoc, mul_left_comm, mul_comm]
          gcongr
      _ ≤ ‖w‖ * ((2 : ℝ) * 1 * ‖Complex.Gamma w‖ *
            ‖Complex.cos (π * w / 2)‖ * ‖riemannZeta w‖) := by
          gcongr
      _ = (‖w‖ * 2) * ‖Complex.Gamma w‖ *
            ‖Complex.cos (π * w / 2)‖ * ‖riemannZeta w‖ := by
          ring
  have hw2 : ‖w‖ * 2 ≤ rexp (2 * A ^ (2 : ℝ)) := by
    simpa [Real.rpow_two, sq] using Real.two_mul_le_exp_two_mul_sq hw_norm_le hA1
  have hmul_exp :
      (‖w‖ * 2) * ‖Complex.Gamma w‖ * ‖Complex.cos (π * w / 2)‖ *
          ‖riemannZeta w‖ ≤
        rexp ((2 + CΓ + 2 + 40) * A ^ (2 : ℝ)) := by
    have h := Real.mul_four_le_exp_add (a := ‖w‖ * 2) (b := ‖Complex.Gamma w‖)
      (c := ‖Complex.cos (π * w / 2)‖) (d := ‖riemannZeta w‖)
      (A := 2 * A ^ (2 : ℝ)) (B := CΓ * A ^ (2 : ℝ))
      (C := 2 * A ^ (2 : ℝ)) (D := 40 * A ^ (2 : ℝ))
      (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hw2 hΓw hcosw hζw
    have hsum :
        2 * A ^ (2 : ℝ) + CΓ * A ^ (2 : ℝ) +
            2 * A ^ (2 : ℝ) + 40 * A ^ (2 : ℝ) =
          (2 + CΓ + 2 + 40) * A ^ (2 : ℝ) := by
      ring
    exact h.trans_eq (congrArg rexp hsum)
  have hdom :
      rexp ((2 + CΓ + 2 + 40) * A ^ (2 : ℝ)) ≤ rexp (C * A ^ (2 : ℝ)) := by
    refine (Real.exp_le_exp).2 ?_
    simpa [mul_assoc] using mul_le_mul_of_nonneg_right hcoef hA2_nonneg
  exact le_trans (le_trans hprod hmul_exp) hdom

theorem completedRiemannZeta₀_order_one :
    ∀ ε : ℝ, 0 < ε → ∃ C > 0, ∀ z : ℂ,  ‖completedRiemannZeta₀ z‖ ≤
      Real.exp (C * (1 + ‖z‖) ^ (1 + ε)) := by
  intro ε hε
  obtain ⟨M, hM_nonneg, hM⟩ := completedRiemannZeta₀_bounded_on_closedBall 3 (by norm_num)
  obtain ⟨CΓ, hCΓ_pos, hΓ⟩ := Complex.Gammaℝ.Stirling.bound_re_ge_zero
  let C : ℝ :=
    max (Real.log (M + 1) + 1) (((2 : ℝ) ^ (1 + ε)) * (10 + CΓ / ε) + 1)
  refine ⟨C, ?_, ?_⟩
  · have : (0 : ℝ) < Real.log (M + 1) + 1 := by
      have hlog : 0 ≤ Real.log (M + 1) := by
        have : (1 : ℝ) ≤ M + 1 := by linarith [hM_nonneg]
        exact Real.log_nonneg this
      linarith
    exact lt_of_lt_of_le this (le_max_left _ _)
  · intro z
    obtain ⟨w, hw_eq, hw_re, hw_norm_le⟩ := exists_completedRiemannZeta₀_right_halfPlane z
    have hw_re0 : 0 ≤ w.re := by linarith
    have htransfer : ‖completedRiemannZeta₀ z‖ = ‖completedRiemannZeta₀ w‖ := by
      simp [hw_eq]
    have hz_base : (1 : ℝ) ≤ (1 + ‖z‖) ^ (1 + ε) :=
      one_le_one_add_norm_rpow (z := z) (by linarith [le_of_lt hε])
    by_cases hw_small : ‖w‖ ≤ 3
    · have hbw : ‖completedRiemannZeta₀ w‖ ≤ M := hM w hw_small
      have hlogC : Real.log (M + 1) ≤ C := by
        have : Real.log (M + 1) + 1 ≤ C := le_max_left _ _
        linarith
      have hpos : 0 < (M + 1 : ℝ) := by linarith [hM_nonneg]
      have hM_le_exp : M ≤ Real.exp (Real.log (M + 1)) := by
        have : Real.exp (Real.log (M + 1)) = M + 1 := by simpa using (Real.exp_log hpos)
        linarith [this]
      have : ‖completedRiemannZeta₀ w‖ ≤ Real.exp (C * (1 + ‖z‖) ^ (1 + ε)) := by
        have h1 : ‖completedRiemannZeta₀ w‖ ≤ Real.exp (Real.log (M + 1)) := by
          exact le_trans hbw hM_le_exp
        have h2 : Real.log (M + 1) ≤ C * (1 + ‖z‖) ^ (1 + ε) := by
          have hlogMC : Real.log (M + 1) ≤ C := hlogC
          have hCmul : C ≤ C * (1 + ‖z‖) ^ (1 + ε) := by
            have hC0 : 0 ≤ C := le_trans (by
              have : (0 : ℝ) < Real.log (M + 1) + 1 := by
                have hlog : 0 ≤ Real.log (M + 1) := Real.log_nonneg (by linarith [hM_nonneg])
                linarith
              exact this.le) (le_max_left _ _)
            have := mul_le_mul_of_nonneg_left hz_base hC0
            simpa [mul_one] using this
          exact le_trans hlogMC hCmul
        exact le_trans h1 (Real.exp_le_exp.2 h2)
      simpa [htransfer] using this
    · have hw_large : 3 < ‖w‖ := lt_of_not_ge hw_small
      have hw_norm1 : 1 ≤ ‖w‖ := le_trans (by norm_num) (le_of_lt hw_large)
      have hw_ne0 : w ≠ 0 := by
        intro h0; have : (‖w‖ : ℝ) = 0 := by simp [h0]
        linarith [hw_large]
      have hw_ne1 : w ≠ 1 := by
        intro h1; have : (‖w‖ : ℝ) = 1 := by simp [h1]
        linarith [hw_large]
      have hGamma : ‖Complex.Gammaℝ w‖ ≤ Real.exp (CΓ * ‖w‖ * Real.log (1 + ‖w‖)) :=
        hΓ w hw_re0 hw_norm1
      have hw_dom := mem_zetaAbelContinuationDomain_of_re hw_ne1
        (lt_of_lt_of_le zetaAbelContinuationReLower_lt_half hw_re)
      have hzeta0 := norm_riemannZeta_le w hw_dom
      have hdist1 : ‖1 / (w - 1)‖ ≤ 1 := by
        have hnorm : ‖w‖ ≤ ‖w - 1‖ + 1 := by
          have : ‖(w - 1) + (1 : ℂ)‖ ≤ ‖w - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
          simpa [sub_add_cancel w (1 : ℂ), norm_one] using this
        have hsub : (2 : ℝ) ≤ ‖w - 1‖ := by
          have : ‖w‖ ≤ ‖w - 1‖ + 1 := by simpa [norm_one] using hnorm
          linarith [hw_large]
        have hsub' : (1 : ℝ) ≤ ‖w - 1‖ := le_trans (by norm_num) hsub
        simpa [one_div, norm_inv] using inv_le_one_of_one_le₀ hsub'
      have hdiv : ‖w‖ / w.re ≤ 2 * ‖w‖ := by
        have hhalf_pos : (0 : ℝ) < (2⁻¹ : ℝ) := by norm_num
        have hinv : (1 / w.re : ℝ) ≤ 2 := by
          have : (1 / w.re : ℝ) ≤ (1 / (2⁻¹ : ℝ)) :=
            one_div_le_one_div_of_le hhalf_pos hw_re
          simpa using this.trans_eq (by norm_num)
        calc
          ‖w‖ / w.re = ‖w‖ * (1 / w.re) := by ring
          _ ≤ ‖w‖ * 2 := mul_le_mul_of_nonneg_left hinv (norm_nonneg _)
          _ = 2 * ‖w‖ := by ring
      have hzeta_le : ‖riemannZeta w‖ ≤ 2 + 2 * ‖w‖ := by
        have hzeta' : ‖riemannZeta w‖ ≤ 1 + ‖1 / (w - 1)‖ + ‖w‖ / w.re := by
          simpa [one_div] using hzeta0
        linarith [hzeta', hdist1, hdiv]
      have hGamma_ne0 : Complex.Gammaℝ w ≠ 0 :=
        Complex.Gammaℝ_ne_zero_of_re_pos (by linarith [hw_re])
      have hΛ_def : completedRiemannZeta w = riemannZeta w * Complex.Gammaℝ w := by
        have hzeta_def := (riemannZeta_def_of_ne_zero (s := w) hw_ne0)
        have hzeta_mul := congrArg (fun x => x * Complex.Gammaℝ w) hzeta_def
        have : riemannZeta w * Complex.Gammaℝ w = completedRiemannZeta w := by
          simpa [div_eq_mul_inv, mul_assoc, hGamma_ne0] using hzeta_mul
        simpa [mul_comm, mul_left_comm, mul_assoc] using this.symm
      have hΛ_bound :
          ‖completedRiemannZeta w‖ ≤ (2 + 2 * ‖w‖) * Real.exp (CΓ * ‖w‖ * Real.log (1 + ‖w‖)) := by
        calc
          ‖completedRiemannZeta w‖ = ‖riemannZeta w * Complex.Gammaℝ w‖ := by simp [hΛ_def]
          _ ≤ ‖riemannZeta w‖ * ‖Complex.Gammaℝ w‖ := norm_mul_le _ _
          _ ≤ (2 + 2 * ‖w‖) * Real.exp (CΓ * ‖w‖ * Real.log (1 + ‖w‖)) := by
            exact mul_le_mul hzeta_le hGamma (by positivity) (by positivity)
      have hΛ0_def : completedRiemannZeta₀ w =
          completedRiemannZeta w + 1 / w + 1 / (1 - w) := by
        have h := completedRiemannZeta_eq w
        have h' := congrArg (fun x => x + (1 / w) + (1 / (1 - w))) h
        simpa [add_assoc, add_left_comm, add_comm, sub_eq_add_neg] using h'.symm
      have hinv1 : ‖1 / w‖ ≤ 1 := by
        have : (1 : ℝ) ≤ ‖w‖ := le_trans (by norm_num) (le_of_lt hw_large)
        simpa [one_div, norm_inv] using inv_le_one_of_one_le₀ this
      have hinv2 : ‖1 / (1 - w)‖ ≤ 1 := by
        have hnorm : ‖w‖ ≤ ‖w - 1‖ + 1 := by
          have : ‖(w - 1) + (1 : ℂ)‖ ≤ ‖w - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
          simpa [sub_add_cancel w (1 : ℂ), norm_one] using this
        have : (2 : ℝ) ≤ ‖w - 1‖ := by linarith [hw_large, hnorm]
        have : (1 : ℝ) ≤ ‖w - 1‖ := le_trans (by norm_num) this
        simpa [one_div, norm_inv, norm_sub_rev] using inv_le_one_of_one_le₀ this
      have hΛ0_bound : ‖completedRiemannZeta₀ w‖ ≤ ‖completedRiemannZeta w‖ + 2 := by
        have : ‖completedRiemannZeta₀ w‖ ≤ ‖completedRiemannZeta w‖ + ‖1 / w‖ + ‖1 / (1 - w)‖ := by
          simpa [hΛ0_def, add_assoc] using
            (norm_add₃_le (a := completedRiemannZeta w) (b := (1 / w)) (c := (1 / (1 - w))))
        linarith [this, hinv1, hinv2]
      have hB_nonneg : 0 ≤ CΓ * ‖w‖ * Real.log (1 + ‖w‖) := by
        have hlog : 0 ≤ Real.log (1 + ‖w‖) := Real.log_nonneg (by linarith [norm_nonneg w])
        have hC0 : 0 ≤ CΓ := le_of_lt hCΓ_pos
        exact mul_nonneg (mul_nonneg hC0 (norm_nonneg w)) hlog
      have hexp_ge_one : (1 : ℝ) ≤ Real.exp (CΓ * ‖w‖ * Real.log (1 + ‖w‖)) := by
        simpa using (Real.one_le_exp_iff.2 hB_nonneg)
      have hΛ0_mul_exp :
          ‖completedRiemannZeta₀ w‖ ≤ (5 + 5 * ‖w‖) * Real.exp (CΓ * ‖w‖ * Real.log (1 + ‖w‖)) := by
        have hw1 : (1 : ℝ) ≤ ‖w‖ := le_trans (by norm_num) (le_of_lt hw_large)
        have h2 : (2 : ℝ) ≤ (3 + 3 * ‖w‖) * Real.exp (CΓ * ‖w‖ * Real.log (1 + ‖w‖)) := by
          nlinarith [hexp_ge_one, hw1]
        have :
            ‖completedRiemannZeta w‖ + 2 ≤
              (5 + 5 * ‖w‖) * Real.exp (CΓ * ‖w‖ * Real.log (1 + ‖w‖)) := by
          nlinarith [hΛ_bound, h2]
        exact le_trans hΛ0_bound this
      have hlog : Real.log (1 + ‖w‖) ≤ (1 + ‖w‖) ^ ε / ε :=
        Real.log_le_rpow_div (by linarith [norm_nonneg w]) hε
      have hB_le : CΓ * ‖w‖ * Real.log (1 + ‖w‖) ≤ (CΓ / ε) * (1 + ‖w‖) ^ (1 + ε) := by
        have hw_le : ‖w‖ ≤ 1 + ‖w‖ := by linarith [norm_nonneg w]
        have hpos : 0 < (1 + ‖w‖ : ℝ) := by linarith [norm_nonneg w]
        have hlog' : Real.log (1 + ‖w‖) ≤ (1 / ε) * (1 + ‖w‖) ^ ε := by
          simpa [div_eq_mul_inv, one_div, mul_assoc, mul_left_comm, mul_comm] using hlog
        have hpowε_nonneg : 0 ≤ (1 + ‖w‖) ^ ε := by positivity
        have hstep1 : ‖w‖ * Real.log (1 + ‖w‖) ≤ ‖w‖ * ((1 / ε) * (1 + ‖w‖) ^ ε) :=
          mul_le_mul_of_nonneg_left hlog' (norm_nonneg w)
        have hfactor_nonneg : 0 ≤ (1 / ε) * (1 + ‖w‖) ^ ε := by
          exact mul_nonneg (by positivity) hpowε_nonneg
        have hstep2 :
            ‖w‖ * ((1 / ε) * (1 + ‖w‖) ^ ε) ≤ (1 + ‖w‖) * ((1 / ε) * (1 + ‖w‖) ^ ε) :=
          mul_le_mul_of_nonneg_right hw_le hfactor_nonneg
        have hmulPow : (1 + ‖w‖) * (1 + ‖w‖) ^ ε = (1 + ‖w‖) ^ (1 + ε) := by
          have h := (Real.rpow_add hpos (1 : ℝ) ε)
          simpa [Real.rpow_one, mul_assoc, mul_left_comm, mul_comm] using h.symm
        have hstep :
            ‖w‖ * Real.log (1 + ‖w‖) ≤ (1 / ε) * (1 + ‖w‖) ^ (1 + ε) := by
          have : ‖w‖ * Real.log (1 + ‖w‖) ≤ (1 + ‖w‖) * ((1 / ε) * (1 + ‖w‖) ^ ε) :=
            le_trans hstep1 hstep2
          calc
            ‖w‖ * Real.log (1 + ‖w‖)
                ≤ (1 + ‖w‖) * ((1 / ε) * (1 + ‖w‖) ^ ε) := this
            _ = (1 / ε) * ((1 + ‖w‖) * (1 + ‖w‖) ^ ε) := by ring
            _ = (1 / ε) * (1 + ‖w‖) ^ (1 + ε) := by simp [hmulPow]
        have hCΓ0 : 0 ≤ CΓ := le_of_lt hCΓ_pos
        have := mul_le_mul_of_nonneg_left hstep hCΓ0
        simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this
      have hpref :
          (5 + 5 * ‖w‖) ≤ Real.exp (10 * (1 + ‖w‖) ^ (1 + ε)) := by
        have hlin : (5 + 5 * ‖w‖ : ℝ) ≤ 10 * (1 + ‖w‖) := by nlinarith [norm_nonneg w]
        have hbase : (1 : ℝ) ≤ (1 + ‖w‖) := by linarith [norm_nonneg w]
        have hexp : (1 + ‖w‖) ≤ (1 + ‖w‖) ^ (1 + ε) := by
          have : (1 : ℝ) ≤ (1 + ε : ℝ) := by linarith [le_of_lt hε]
          simpa [Real.rpow_one] using (Real.rpow_le_rpow_of_exponent_le hbase this)
        have : (10 * (1 + ‖w‖) : ℝ) ≤ 10 * (1 + ‖w‖) ^ (1 + ε) := by nlinarith [hexp]
        exact le_trans hlin (le_trans this (Real.le_exp_self _))
      have hbig :
          ‖completedRiemannZeta₀ w‖ ≤
            Real.exp ((10 + CΓ / ε) * (1 + ‖w‖) ^ (1 + ε)) := by
        set X : ℝ := (1 + ‖w‖) ^ (1 + ε)
        have hexp_replace :
            Real.exp (CΓ * ‖w‖ * Real.log (1 + ‖w‖)) ≤ Real.exp ((CΓ / ε) * X) :=
          Real.exp_le_exp.2 (by simpa [X] using hB_le)
        have hC0 : 0 ≤ (5 + 5 * ‖w‖ : ℝ) := by positivity
        have h1 : ‖completedRiemannZeta₀ w‖ ≤ (5 + 5 * ‖w‖) * Real.exp ((CΓ / ε) * X) :=
          le_trans hΛ0_mul_exp (by
            simpa [mul_assoc] using (mul_le_mul_of_nonneg_left hexp_replace hC0))
        have h2 :
            (5 + 5 * ‖w‖) * Real.exp ((CΓ / ε) * X) ≤
              Real.exp (10 * X) * Real.exp ((CΓ / ε) * X) := by
          have : (5 + 5 * ‖w‖) ≤ Real.exp (10 * X) := by
            simpa [X] using hpref
          exact mul_le_mul_of_nonneg_right this (by positivity)
        have h3 : Real.exp (10 * X) * Real.exp ((CΓ / ε) * X) = Real.exp ((10 + CΓ / ε) * X) := by
          calc
            Real.exp (10 * X) * Real.exp ((CΓ / ε) * X)
                = Real.exp (10 * X + (CΓ / ε) * X) := by
                    simp [Real.exp_add]
            _ = Real.exp ((10 + CΓ / ε) * X) := by ring_nf
        have : ‖completedRiemannZeta₀ w‖ ≤ Real.exp ((10 + CΓ / ε) * X) :=
          le_trans (le_trans h1 h2) (by simp [h3])
        simpa [X] using this
      have hw_le_z : (1 + ‖w‖ : ℝ) ≤ 2 * (1 + ‖z‖) := by linarith [hw_norm_le, norm_nonneg z]
      have hwbase_nonneg : (0 : ℝ) ≤ 1 + ‖w‖ := by linarith [norm_nonneg w]
      have hε' : (0 : ℝ) ≤ 1 + ε := by linarith [le_of_lt hε]
      have hpow_le :
          (1 + ‖w‖) ^ (1 + ε) ≤ (2 * (1 + ‖z‖)) ^ (1 + ε) :=
        Real.rpow_le_rpow hwbase_nonneg hw_le_z hε'
      have hC_ge : ((2 : ℝ) ^ (1 + ε)) * (10 + CΓ / ε) ≤ C := by
        have : ((2 : ℝ) ^ (1 + ε)) * (10 + CΓ / ε) + 1 ≤ C := le_max_right _ _
        linarith
      have hzpos : 0 ≤ (1 + ‖z‖ : ℝ) := by linarith [norm_nonneg z]
      have hmul_rpow :
          (2 * (1 + ‖z‖)) ^ (1 + ε) = (2 : ℝ) ^ (1 + ε) * (1 + ‖z‖) ^ (1 + ε) := by
        simpa [mul_assoc] using
          (Real.mul_rpow (x := (2 : ℝ)) (y := (1 + ‖z‖)) (z := (1 + ε)) (by positivity) hzpos)
      have hdom :
          (10 + CΓ / ε) * (1 + ‖w‖) ^ (1 + ε) ≤ C * (1 + ‖z‖) ^ (1 + ε) := by
        calc
          (10 + CΓ / ε) * (1 + ‖w‖) ^ (1 + ε)
              ≤ (10 + CΓ / ε) * (2 * (1 + ‖z‖)) ^ (1 + ε) := by gcongr
          _ = ((2 : ℝ) ^ (1 + ε)) * (10 + CΓ / ε) * (1 + ‖z‖) ^ (1 + ε) := by
                simp [hmul_rpow]
                ring
          _ ≤ C * (1 + ‖z‖) ^ (1 + ε) := by
                have : ((2 : ℝ) ^ (1 + ε)) * (10 + CΓ / ε) ≤ C := hC_ge
                gcongr
      have : ‖completedRiemannZeta₀ w‖ ≤ Real.exp (C * (1 + ‖z‖) ^ (1 + ε)) := by
        exact le_trans hbig (Real.exp_le_exp.2 hdom)
      simpa [htransfer] using this

noncomputable def zetaTimesSMinusOne_entire (s : ℂ) : ℂ :=
  Function.update (fun s : ℂ => (s - 1) * riemannZeta s) 1 1 s

@[simp]
theorem zetaTimesSMinusOne_entire_one : zetaTimesSMinusOne_entire (1 : ℂ) = 1 := by
  simp [zetaTimesSMinusOne_entire]

theorem zetaTimesSMinusOne_entire_eq_mul_riemannZeta {s : ℂ} (hs : s ≠ 1) :
    zetaTimesSMinusOne_entire s = (s - 1) * riemannZeta s := by
  simp [zetaTimesSMinusOne_entire, Function.update, hs]

theorem completedRiemannZeta_ne_zero_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    completedRiemannZeta s ≠ 0 := by
  have hGamma_ne0 : Gammaℝ s ≠ 0 :=
    Gammaℝ_ne_zero_of_re_pos (zero_lt_one.trans hs)
  have hzeta_ne0 : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
  have hΛ_def : completedRiemannZeta s = riemannZeta s * Gammaℝ s := by
    have hzeta_def := riemannZeta_def_of_ne_zero (s := s) (ne_zero_of_one_lt_re hs)
    have hzeta_mul := congrArg (fun x => x * Gammaℝ s) hzeta_def
    have : riemannZeta s * Gammaℝ s = completedRiemannZeta s := by
      simpa [div_eq_mul_inv, mul_assoc, hGamma_ne0] using hzeta_mul
    exact this.symm
  rw [hΛ_def]
  exact mul_ne_zero hzeta_ne0 hGamma_ne0

theorem eq_zetaTimesSMinusOne_entire_of_eq_on_compl_singleton {g : ℂ → ℂ}
    (h_one : g (1 : ℂ) = 1)
    (h_eq : ∀ ⦃s : ℂ⦄, s ≠ 1 → g s = (s - 1) * riemannZeta s) :
    g = zetaTimesSMinusOne_entire := by
  funext s
  by_cases hs : s = 1
  · subst hs
    simpa using h_one
  · simpa [zetaTimesSMinusOne_entire_eq_mul_riemannZeta hs] using h_eq hs

theorem zetaTimesSMinusOne_entire_differentiableOn_compl_singleton :
    DifferentiableOn ℂ zetaTimesSMinusOne_entire (Set.univ \ ({1} : Set ℂ)) := by
  intro s hs
  have hs1 : s ≠ 1 := by
    simpa [Set.mem_singleton_iff] using hs.2
  have h1 : DifferentiableAt ℂ (fun s => s - 1) s := differentiableAt_id.sub_const 1
  have h2 : DifferentiableAt ℂ riemannZeta s := differentiableAt_riemannZeta hs1
  have hmul : DifferentiableAt ℂ (fun s => (s - 1) * riemannZeta s) s := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using! (h1.mul h2)
  refine (hmul.differentiableWithinAt.congr (fun x hx => ?_) ?_)
  · have hx1 : x ≠ (1 : ℂ) := by
      simpa [Set.mem_singleton_iff] using hx.2
    exact zetaTimesSMinusOne_entire_eq_mul_riemannZeta hx1
  · exact zetaTimesSMinusOne_entire_eq_mul_riemannZeta hs1

theorem zetaTimesSMinusOne_entire_continuousAt_one :
    ContinuousAt zetaTimesSMinusOne_entire (1 : ℂ) := by
  have h :
      ContinuousAt
        (Function.update (fun s : ℂ => (s - 1) * riemannZeta s) (1 : ℂ) (1 : ℂ))
        (1 : ℂ) :=
    (continuousAt_update_same (f := fun s : ℂ => (s - 1) * riemannZeta s)
        (x := (1 : ℂ)) (y := (1 : ℂ))).2
      (riemannZeta_residue_one : Tendsto (fun s : ℂ => (s - 1) * riemannZeta s)
        (𝓝[≠] (1 : ℂ)) (𝓝 (1 : ℂ)))
  change
    ContinuousAt (Function.update (fun s : ℂ => (s - 1) * riemannZeta s) (1 : ℂ) (1 : ℂ))
      (1 : ℂ)
  exact h

theorem zetaTimesSMinusOne_entire_differentiable :
    Differentiable ℂ zetaTimesSMinusOne_entire := by
  have hiff :=
    (Complex.differentiableOn_compl_singleton_and_continuousAt_iff (f := zetaTimesSMinusOne_entire)
      (s := (Set.univ : Set ℂ)) (c := (1 : ℂ)) (by simp))
  have : DifferentiableOn ℂ zetaTimesSMinusOne_entire (Set.univ : Set ℂ) :=
    hiff.1
      ⟨zetaTimesSMinusOne_entire_differentiableOn_compl_singleton,
        zetaTimesSMinusOne_entire_continuousAt_one⟩
  simpa [DifferentiableOn, differentiableWithinAt_univ, zetaTimesSMinusOne_entire] using! this

theorem zeta_minus_pole_entire_growth :
    ∃ C > 0, ∀ z : ℂ,
      Real.log (1 + ‖zetaTimesSMinusOne_entire z‖) ≤ C * (1 + ‖z‖) ^ (2 : ℝ) := by
  have hcont :
      ContinuousOn zetaTimesSMinusOne_entire (Metric.closedBall (0 : ℂ) 3) :=
    zetaTimesSMinusOne_entire_differentiable.continuous.continuousOn
  obtain ⟨M, hM_nonneg, hM⟩ := exists_norm_bound_on_closedBall hcont
  obtain ⟨CΓ, hCΓ_pos, hΓ⟩ := Complex.Gamma.stirling_bound_re_ge_zero
  let C : ℝ := max (Real.log (1 + M) + 10) (max (40 : ℝ) (20 * CΓ + 500))
  refine ⟨C + Real.log 2, ?_, ?_⟩
  · have hCpos : (0 : ℝ) < C := by
      have : (0 : ℝ) < 20 * CΓ + 500 := by nlinarith [hCΓ_pos]
      exact lt_of_lt_of_le this (le_trans (le_max_right _ _) (le_max_right _ _))
    have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    linarith
  · intro z
    set A : ℝ := 1 + ‖z‖
    have hA1 : (1 : ℝ) ≤ A := by dsimp [A]; linarith [norm_nonneg z]
    have hA2_nonneg : 0 ≤ A ^ (2 : ℝ) := by positivity
    by_cases hz_small : ‖z‖ ≤ 3
    · have hnorm : ‖zetaTimesSMinusOne_entire z‖ ≤ M := hM z hz_small
      have hlog :
          Real.log (1 + ‖zetaTimesSMinusOne_entire z‖) ≤ Real.log (1 + M) := by
        refine Real.log_le_log (by positivity) ?_
        linarith
      have hC1 : Real.log (1 + M) ≤ C + Real.log 2 := by
        have : Real.log (1 + M) + 10 ≤ C := by
          simp [C]
        have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
        linarith
      have hpow : (1 : ℝ) ≤ A ^ (2 : ℝ) :=
        Real.one_le_rpow hA1 (by norm_num)
      have hC_nonneg : 0 ≤ C + Real.log 2 := by
        have hCpos : (0 : ℝ) < C := by
          have hpos' : (0 : ℝ) < 20 * CΓ + 500 := by nlinarith [hCΓ_pos]
          have hmax : (0 : ℝ) < max (40 : ℝ) (20 * CΓ + 500) :=
            lt_of_lt_of_le hpos' (le_max_right _ _)
          have hle : max (40 : ℝ) (20 * CΓ + 500) ≤ C := by
            simp [C]
          exact lt_of_lt_of_le hmax hle
        have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
        linarith
      calc
        Real.log (1 + ‖zetaTimesSMinusOne_entire z‖)
            ≤ Real.log (1 + M) := hlog
        _ ≤ C + Real.log 2 := hC1
        _ ≤ (C + Real.log 2) * A ^ (2 : ℝ) := by
              simpa [mul_one] using (mul_le_mul_of_nonneg_left hpow hC_nonneg)
    · have hz_large : 3 < ‖z‖ := lt_of_not_ge hz_small
      have hz_ne1 : z ≠ 1 := by
        intro h
        have : (‖z‖ : ℝ) = 1 := by simp [h]
        linarith [hz_large]
      have hzeta_def : zetaTimesSMinusOne_entire z = (z - 1) * riemannZeta z := by
        exact zetaTimesSMinusOne_entire_eq_mul_riemannZeta hz_ne1
      have hmain :
          ‖zetaTimesSMinusOne_entire z‖ ≤ Real.exp (C * A ^ (2 : ℝ)) := by
        by_cases hz_re : zetaAbelContinuationReLower < z.re
        · have hs_dom := mem_zetaAbelContinuationDomain_of_re hz_ne1
            (by simpa [zetaAbelContinuationReLower] using hz_re)
          have hζ := norm_riemannZeta_le z hs_dom
          have hzm1_le : ‖z - 1‖ ≤ A := by
            simpa [A] using norm_sub_one_le_one_add_norm z
          have hfrac : ‖z‖ / z.re ≤ 10 * ‖z‖ := norm_div_re_le_ten_mul_norm_of_mem hs_dom
          have hpoly :
              ‖(z - 1) * riemannZeta z‖ ≤ (40 : ℝ) * A ^ (2 : ℝ) := by
            have hz0 : 0 ≤ ‖z‖ := norm_nonneg z
            have hz_le_A : ‖z‖ ≤ A := by dsimp [A]; linarith [hz0]
            have hζ' : ‖riemannZeta z‖ ≤ 1 + ‖(1 : ℂ) / (z - 1)‖ + 10 * ‖z‖ := by
              calc
                ‖riemannZeta z‖ ≤ 1 + ‖1 / (z - 1)‖ + ‖z‖ / z.re := hζ
                _ ≤ 1 + ‖1 / (z - 1)‖ + 10 * ‖z‖ := by gcongr
            have hmul_inv : ‖z - 1‖ * ‖(1 : ℂ) / (z - 1)‖ = 1 := by
              have hz1' : z - 1 ≠ (0 : ℂ) := sub_ne_zero.2 hz_ne1
              simp [hz1']
            have hterm3 : ‖z - 1‖ * (10 * ‖z‖) ≤ A * (10 * ‖z‖) :=
              mul_le_mul_of_nonneg_right hzm1_le (by positivity)
            have hApos : (0 : ℝ) ≤ A := le_trans (by norm_num) hA1
            have hA2 : A * (10 * ‖z‖) ≤ 10 * (A ^ (2 : ℕ)) := by
              have : A * ‖z‖ ≤ A * A := by nlinarith [hz_le_A]
              nlinarith [this]
            have hstep : A + 1 + A * (10 * ‖z‖) ≤ (40 : ℝ) * (A ^ (2 : ℕ)) := by
              have hA1' : A + 1 ≤ 2 * A := by nlinarith [hA1]
              have hstep1 : A + 1 + A * (10 * ‖z‖) ≤ 2 * A + 10 * (A ^ (2 : ℕ)) := by
                nlinarith [hA1', hA2]
              have hA_le_sq : A ≤ (A ^ (2 : ℕ)) := by
                simpa [pow_two] using (mul_le_mul_of_nonneg_right hA1 hApos)
              have hstep2 : 2 * A + 10 * (A ^ (2 : ℕ)) ≤ (40 : ℝ) * (A ^ (2 : ℕ)) := by
                nlinarith [hA_le_sq]
              exact le_trans hstep1 hstep2
            calc
              ‖(z - 1) * riemannZeta z‖ ≤ ‖z - 1‖ * ‖riemannZeta z‖ := by simp
              _ ≤ ‖z - 1‖ * (1 + ‖(1 : ℂ) / (z - 1)‖ + 10 * ‖z‖) := by gcongr
              _ = ‖z - 1‖ + (‖z - 1‖ * ‖(1 : ℂ) / (z - 1)‖) + ‖z - 1‖ * (10 * ‖z‖) := by ring
              _ ≤ A + 1 + A * (10 * ‖z‖) := by nlinarith [hzm1_le, hmul_inv, hterm3]
              _ ≤ (40 : ℝ) * (A ^ (2 : ℕ)) := hstep
              _ = (40 : ℝ) * A ^ (2 : ℝ) := by simp
          have hC_ge : (40 : ℝ) ≤ C := by
            have h1 : (40 : ℝ) ≤ max (40 : ℝ) (20 * CΓ + 500) := le_max_left _ _
            have h2 : max (40 : ℝ) (20 * CΓ + 500) ≤ C := by
              simp [C]
            exact le_trans h1 h2
          have hle : (40 : ℝ) * A ^ (2 : ℝ) ≤ C * A ^ (2 : ℝ) := by
            simpa [mul_assoc] using (mul_le_mul_of_nonneg_right hC_ge hA2_nonneg)
          have : ‖(z - 1) * riemannZeta z‖ ≤ Real.exp (C * A ^ (2 : ℝ)) :=
            le_trans (le_trans hpoly hle) (Real.le_exp_self _)
          simpa [hzeta_def] using this
        · have hz_re_le : z.re ≤ zetaAbelContinuationReLower := le_of_not_gt hz_re
          let w : ℂ := 1 - z
          have hw_re_ge : (1 - zetaAbelContinuationReLower) ≤ w.re :=
            one_sub_re_ge_one_sub_zetaAbelContinuationReLower_of_re_le hz_re_le
          have hw_re0 : 0 ≤ w.re := by
            have : (0 : ℝ) < 1 - zetaAbelContinuationReLower := by
              rw [one_sub_zetaAbelContinuationReLower]; norm_num
            linarith [hw_re_ge]
          have hw_re1 : zetaAbelContinuationReLower < w.re :=
            lt_of_lt_of_le
              (by norm_num [zetaAbelContinuationReLower, one_sub_zetaAbelContinuationReLower])
              hw_re_ge
          have hw_ne1 : w ≠ 1 := by
            simpa [w] using Complex.one_sub_ne_one_of_norm_pos (lt_trans (by norm_num) hz_large)
          have hw_ne_neg : ∀ n : ℕ, w ≠ -n := by
            exact Complex.ne_neg_nat_of_re_pos (lt_trans zetaAbelContinuationReLower_pos hw_re1)
          have hzeta_fe :
              riemannZeta z =
                2 * (2 * π) ^ (-w) * Complex.Gamma w * Complex.cos (π * w / 2) * riemannZeta w := by
            exact riemannZeta_eq_reflected (by simp [w]) hw_ne_neg hw_ne1
          have hpow_le1 : ‖(2 * π : ℂ) ^ (-w)‖ ≤ 1 :=
            Complex.Gammaℝ.Stirling.norm_cpow_two_mul_pi_neg_le_one hw_re0
          have hw_norm_le : ‖w‖ ≤ A := by
            simpa [w, A] using norm_one_sub_le_one_add_norm z
          have hw_norm_ge1 : (1 : ℝ) ≤ ‖w‖ := by
            simpa [w] using one_le_norm_one_sub_of_norm_gt_three hz_large
          have hΓw : ‖Complex.Gamma w‖ ≤ Real.exp (CΓ * A ^ (2 : ℝ)) := by
            have hΓ0 := hΓ w hw_re0 hw_norm_ge1
            have hlog_le : Real.log (1 + ‖w‖) ≤ A := by
              have : Real.log (1 + ‖w‖) ≤ (1 + ‖w‖) - 1 := by
                have : (0 : ℝ) < 1 + ‖w‖ := by positivity
                simpa using (Real.log_le_sub_one_of_pos this)
              have : Real.log (1 + ‖w‖) ≤ ‖w‖ := by simpa [sub_eq_add_neg] using this
              exact le_trans this hw_norm_le
            have hmul : ‖w‖ * Real.log (1 + ‖w‖) ≤ A ^ (2 : ℝ) := by
              have : ‖w‖ * Real.log (1 + ‖w‖) ≤ A * A := by nlinarith [hw_norm_le, hlog_le]
              simpa [pow_two] using this
            have hexp : CΓ * ‖w‖ * Real.log (1 + ‖w‖) ≤ CΓ * A ^ (2 : ℝ) := by
              have hC0 : 0 ≤ CΓ := le_of_lt hCΓ_pos
              nlinarith [hmul, hC0]
            exact le_trans hΓ0 (Real.exp_le_exp.mpr hexp)
          have hcosw : ‖Complex.cos (π * w / 2)‖ ≤ Real.exp (2 * A ^ (2 : ℝ)) := by
            have h1 := norm_cos_le_exp_abs_im (π * w / 2)
            have him : |(π * w / 2).im| ≤ 2 * A ^ (2 : ℝ) := by
              have : |(π * w / 2).im| ≤ ‖π * w / 2‖ := Complex.abs_im_le_norm _
              have hnorm : ‖π * w / 2‖ = (Real.pi / 2) * ‖w‖ := by
                have hrew : (π * w / 2 : ℂ) = (π / 2) * w := by
                  simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
                calc
                  ‖π * w / 2‖ = ‖(π / 2) * w‖ := by simp [hrew]
                  _ = ‖(π / 2)‖ * ‖w‖ := by simp
                  _ = (Real.pi / 2) * ‖w‖ := by simp
              have hpi : (Real.pi / 2 : ℝ) ≤ 2 := by
                have : (Real.pi : ℝ) ≤ 4 := by linarith [Real.pi_lt_four.le]
                nlinarith
              have him1 : |(π * w / 2).im| ≤ 2 * ‖w‖ := by
                calc
                  |(π * w / 2).im| ≤ ‖π * w / 2‖ := this
                  _ = (Real.pi / 2) * ‖w‖ := hnorm
                  _ ≤ 2 * ‖w‖ := by gcongr
              have him2 : 2 * ‖w‖ ≤ 2 * A ^ (2 : ℝ) := by
                have : ‖w‖ ≤ A ^ (2 : ℝ) := by
                  have : A ≤ A ^ (2 : ℝ) := by
                    have := Real.rpow_le_rpow_of_exponent_le hA1 (by norm_num : (1 : ℝ) ≤ (2 : ℝ))
                    simpa [Real.rpow_one] using this
                  exact le_trans hw_norm_le this
                nlinarith [this]
              exact le_trans him1 him2
            exact le_trans h1 (Real.exp_le_exp.mpr him)
          have hζw : ‖riemannZeta w‖ ≤ Real.exp (40 * A ^ (2 : ℝ)) := by
            have hw_dom := mem_zetaAbelContinuationDomain_of_re hw_ne1 (by linarith [hw_re1])
            have hζ0 := norm_riemannZeta_le w hw_dom
            have hfrac : ‖w‖ / w.re ≤ 10 * ‖w‖ := norm_div_re_le_ten_mul_norm_of_mem hw_dom
            have hpoly : ‖riemannZeta w‖ ≤ (40 : ℝ) * A ^ (2 : ℝ) := by
              have : ‖riemannZeta w‖ ≤ 2 + 10 * ‖w‖ := by
                calc
                  ‖riemannZeta w‖ ≤ 1 + ‖1 / (w - 1)‖ + ‖w‖ / w.re := hζ0
                  _ ≤ 1 + ‖1 / (w - 1)‖ + 10 * ‖w‖ := by gcongr
                  _ ≤ 2 + 10 * ‖w‖ := by
                        have hw1 : w - 1 = -z := by
                          dsimp [w]
                          ring
                        have hz1 : (1 : ℝ) ≤ ‖z‖ := le_trans (by norm_num) (le_of_lt hz_large)
                        have hinv_le : ‖(1 : ℂ) / (w - 1)‖ ≤ 1 := by
                          have hinv : (‖z‖ : ℝ)⁻¹ ≤ (1 : ℝ) := by
                            simpa using (inv_le_one_of_one_le₀ (a := (‖z‖ : ℝ)) hz1)
                          simpa [div_eq_mul_inv, hw1] using hinv
                        nlinarith [hinv_le]
              calc
                ‖riemannZeta w‖ ≤ 2 + 10 * ‖w‖ := this
                _ ≤ 2 + 10 * A := by gcongr
                _ ≤ (40 : ℝ) * A ^ (2 : ℝ) := by
                      simp [pow_two]
                      nlinarith [hA1]
            exact le_trans hpoly (Real.le_exp_self _)
          have hcoef : (2 + CΓ + 2 + 40 : ℝ) ≤ C := by
            exact reflected_zeta_coefficient_le hCΓ_pos.le (le_max_right _ _)
          have : ‖(z - 1) * riemannZeta z‖ ≤ rexp (C * A ^ (2 : ℝ)) :=
            norm_mul_riemannZeta_le_exp_of_reflected (by simp [w]) hzeta_fe hpow_le1
              hw_norm_le hA1 hA2_nonneg hΓw hcosw hζw hcoef
          simpa [hzeta_def] using this
      have hC0 : 0 ≤ C := by
        have h0 : (0 : ℝ) ≤ max (40 : ℝ) (20 * CΓ + 500) :=
          le_trans (by norm_num) (le_max_left _ _)
        have hle : max (40 : ℝ) (20 * CΓ + 500) ≤ C := by simp [C]
        exact le_trans h0 hle
      have hB0 : 0 ≤ C * A ^ (2 : ℝ) := mul_nonneg hC0 hA2_nonneg
      have hlog :
          Real.log (1 + ‖zetaTimesSMinusOne_entire z‖) ≤
            C * A ^ (2 : ℝ) + Real.log 2 :=
        Real.log_one_add_le_add_log_two_of_le_exp (norm_nonneg _) hB0 hmain
      have hA2_ge1 : (1 : ℝ) ≤ A ^ (2 : ℝ) :=
        Real.one_le_rpow hA1 (by norm_num)
      calc
        Real.log (1 + ‖zetaTimesSMinusOne_entire z‖)
            ≤ C * A ^ (2 : ℝ) + Real.log 2 := hlog
        _ ≤ (C + Real.log 2) * A ^ (2 : ℝ) := by
              have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
              
              have : Real.log 2 ≤ Real.log 2 * A ^ (2 : ℝ) := by
                simpa [one_mul] using (mul_le_mul_of_nonneg_left hA2_ge1 hlog2)
              nlinarith [this]

end Complex
end
end File63

-- Upstream module PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.RiemannZetaValues
section File64
 

section
open Complex Set

open scoped BigOperators

private lemma twenty_seven_div_fifty_lt_eulerMascheroniConstant :
    (27 / 50 : ℝ) < Real.eulerMascheroniConstant := by
  have hseq : (27 / 50 : ℝ) < Real.eulerMascheroniSeq 20 := by
    have hval : Real.eulerMascheroniSeq 20 =
        (55835135 / 15519504 : ℝ) - Real.log 21 := by
      rw [Real.eulerMascheroniSeq]
      norm_num
    rw [hval, lt_sub_iff_add_lt, ← lt_sub_iff_add_lt',
      Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 21)]
    refine lt_of_lt_of_le ?_ (Real.sum_le_exp_of_nonneg (by norm_num) 14)
    norm_num [Finset.sum_range_succ, Nat.factorial]
  exact hseq.trans (Real.eulerMascheroniSeq_lt_eulerMascheroniConstant 20)

private lemma exp_one_hundred_twenty_seven_div_fifty_gt :
    (7854 / 625 : ℝ) < Real.exp (127 / 50 : ℝ) := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : 0 ≤ (127 / 50 : ℝ)) 12
  have hpoly :
      (7854 / 625 : ℝ) <
        ∑ i ∈ Finset.range 12, (127 / 50 : ℝ) ^ i / (i.factorial : ℝ) := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  exact hpoly.trans_le h

private lemma log_four_mul_pi_lt_one_hundred_twenty_seven_div_fifty :
    Real.log (4 * Real.pi) < 127 / 50 := by
  rw [Real.log_lt_iff_lt_exp (by positivity : (0 : ℝ) < 4 * Real.pi)]
  have hpi : 4 * Real.pi < 7854 / 625 := by
    nlinarith [Real.pi_lt_d4]
  exact hpi.trans exp_one_hundred_twenty_seven_div_fifty_gt

theorem completedRiemannZeta_two :
    completedRiemannZeta (2 : ℂ) = (Real.pi : ℂ) / 6 := by
  have hs : (1 : ℝ) < Complex.re (2 : ℂ) := by norm_num
  have hpi0 : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have htsum :
      completedRiemannZeta (2 : ℂ) = (Real.pi : ℂ)⁻¹ * (∑' n : ℕ, ((n : ℂ) ^ 2)⁻¹) := by
    simpa [Complex.cpow_neg_one] using
      (completedZeta_eq_tsum_of_one_lt_re (s := (2 : ℂ)) hs)
  have hzeta : riemannZeta (2 : ℂ) = ∑' n : ℕ, ((n : ℂ) ^ 2)⁻¹ := by
    simpa using (zeta_eq_tsum_one_div_nat_cpow (s := (2 : ℂ)) hs)
  have hζ2 : riemannZeta (2 : ℂ) = (Real.pi : ℂ) ^ 2 / 6 := by
    simpa using (riemannZeta_two : riemannZeta (2 : ℂ) = (Real.pi : ℂ) ^ 2 / 6)
  have hΛ2' : completedRiemannZeta (2 : ℂ) = (Real.pi : ℂ)⁻¹ * riemannZeta (2 : ℂ) := by
    simpa [hzeta] using htsum
  calc
    completedRiemannZeta (2 : ℂ)
        = (Real.pi : ℂ)⁻¹ * ((Real.pi : ℂ) ^ 2 / 6) := by
            simpa [hζ2] using hΛ2'
    _ = (Real.pi : ℂ) / 6 := by
            field_simp [hpi0]

theorem completedRiemannZeta₀_two :
    completedRiemannZeta₀ (2 : ℂ) = ((Real.pi : ℂ) - 3) / 6 := by
  have h := completedRiemannZeta_eq (2 : ℂ)
  have h' :
      completedRiemannZeta (2 : ℂ) + (1 : ℂ) / 2 + (1 : ℂ) / (1 - (2 : ℂ)) =
        completedRiemannZeta₀ (2 : ℂ) := by
    have := congrArg (fun x => x + (1 : ℂ) / 2 + (1 : ℂ) / (1 - (2 : ℂ))) h
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this
  have h'' :
      completedRiemannZeta₀ (2 : ℂ) =
        completedRiemannZeta (2 : ℂ) + (1 : ℂ) / 2 + (1 : ℂ) / (1 - (2 : ℂ)) := by
    simpa [add_assoc, add_left_comm, add_comm] using h'.symm
  have hden : (1 : ℂ) / (1 - (2 : ℂ)) = (-1 : ℂ) := by norm_num
  simpa [h'', completedRiemannZeta_two, hden] using (by ring :
    (Real.pi : ℂ) / 6 + (1 : ℂ) / 2 + (-1 : ℂ) = ((Real.pi : ℂ) - 3) / 6)

theorem completedRiemannZeta₀_nontrivial : ∃ z : ℂ, completedRiemannZeta₀ z ≠ 0 := by
  refine ⟨(2 : ℂ), ?_⟩
  have hpi_ne3 : (Real.pi : ℂ) ≠ (3 : ℂ) := by
    intro h'
    have hpi' : (Real.pi : ℝ) = (3 : ℝ) := by
      simpa using congrArg Complex.re h'
    have hirr : Irrational Real.pi := by simp
    exact (hirr.ne_nat 3) (by simp at hpi')
  have hnum : ((Real.pi : ℂ) - 3) ≠ 0 := sub_ne_zero.2 hpi_ne3
  have hden : (6 : ℂ) ≠ 0 := by norm_num
  have : ((Real.pi : ℂ) - 3) / 6 ≠ 0 := div_ne_zero hnum hden
  simpa [completedRiemannZeta₀_two] using this

theorem completedRiemannZeta₀_zero_eq_one :
    completedRiemannZeta₀ (0 : ℂ) = completedRiemannZeta₀ (1 : ℂ) := by
  have h := completedRiemannZeta₀_one_sub (0 : ℂ)
  simpa using h.symm

theorem completedRiemannZeta₀_one_ne_zero :
    completedRiemannZeta₀ (1 : ℂ) ≠ 0 := by
  have hpos :
      0 < (Real.eulerMascheroniConstant - Real.log (4 * Real.pi)) / 2 + 1 := by
    have hγ : (27 / 50 : ℝ) < Real.eulerMascheroniConstant :=
      twenty_seven_div_fifty_lt_eulerMascheroniConstant
    have hlog : Real.log (4 * Real.pi) < 127 / 50 :=
      log_four_mul_pi_lt_one_hundred_twenty_seven_div_fifty
    linarith
  have hreal :
      ((Real.eulerMascheroniConstant - Real.log (4 * Real.pi)) / 2 + 1 : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt hpos
  rw [completedRiemannZeta₀_one]
  simpa [Complex.ofReal_log (by positivity : (0 : ℝ) ≤ 4 * Real.pi), sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hreal

theorem completedRiemannZeta₀_zero_ne_zero :
    completedRiemannZeta₀ (0 : ℂ) ≠ 0 := by
  simpa [completedRiemannZeta₀_zero_eq_one] using completedRiemannZeta₀_one_ne_zero
end
end File64

-- Upstream module PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.RiemannZetaHadamard
section File65
 

section
noncomputable section

open Complex Set

open scoped BigOperators

theorem completedRiemannZeta₀_entireOfOrderAtMost_one :
    Complex.Hadamard.EntireOfOrderAtMost (1 : ℝ) completedRiemannZeta₀ := by
  refine ⟨differentiable_completedZeta₀, ?_⟩
  intro ε hε
  simpa [add_comm, add_left_comm, add_assoc] using
    (Complex.completedRiemannZeta₀_order_one ε hε)

theorem riemannXi_entireOfOrderAtMost_one :
    Complex.Hadamard.EntireOfOrderAtMost (1 : ℝ) riemannXi := by
  refine ⟨differentiable_riemannXi, ?_⟩
  intro ε hε
  rcases completedRiemannZeta₀_entireOfOrderAtMost_one.exists_bound hε with
    ⟨C, hCpos, hΛ⟩
  let b : ℝ := 1 + ε
  let D : ℝ := 4 / b
  let C' : ℝ := C + D + 1
  have hbpos : 0 < b := by dsimp [b]; linarith
  refine ⟨C', by positivity, ?_⟩
  intro z
  let R : ℝ := 1 + ‖z‖
  have hR1 : 1 ≤ R := by dsimp [R]; linarith [norm_nonneg z]
  have hRpos : 0 < R := zero_lt_one.trans_le hR1
  have hRpow1 : 1 ≤ R ^ b :=
    Real.one_le_rpow hR1 hbpos.le
  have hpoly : ‖z * (z - 1)‖ ≤ R ^ 2 := by
    have hz : ‖z‖ ≤ R := by dsimp [R]; linarith [norm_nonneg z]
    have hz1 : ‖z - 1‖ ≤ R := by
      simpa [R] using Complex.norm_sub_one_le_one_add_norm z
    calc
      ‖z * (z - 1)‖ ≤ ‖z‖ * ‖z - 1‖ := norm_mul_le z (z - 1)
      _ ≤ R * R := mul_le_mul hz hz1 (norm_nonneg _) (by positivity)
      _ = R ^ 2 := by ring
  have hquad : R ^ 2 ≤ Real.exp (D * R ^ b) := by
    simpa [D] using Real.sq_le_exp_const_mul_rpow (b := b) (r := R) hbpos hR1
  have hΛz : ‖completedRiemannZeta₀ z‖ ≤ Real.exp (C * R ^ b) := by
    simpa [R, b, add_assoc] using hΛ z
  have hterm :
      ‖z * (z - 1) * completedRiemannZeta₀ z‖ ≤
        Real.exp ((C + D) * R ^ b) := by
    calc
      ‖z * (z - 1) * completedRiemannZeta₀ z‖
          ≤ ‖z * (z - 1)‖ * ‖completedRiemannZeta₀ z‖ := norm_mul_le _ _
      _ ≤ (R ^ 2) * Real.exp (C * R ^ b) :=
          mul_le_mul hpoly hΛz (norm_nonneg _) (by positivity)
      _ ≤ Real.exp (D * R ^ b) * Real.exp (C * R ^ b) :=
          mul_le_mul_of_nonneg_right hquad (by positivity)
      _ = Real.exp ((C + D) * R ^ b) := by
          rw [← Real.exp_add]
          ring_nf
  have hA_nonneg : 0 ≤ (C + D) * R ^ b := by positivity
  have hone_le : (1 : ℝ) ≤ Real.exp ((C + D) * R ^ b) :=
    Real.one_le_exp_iff.mpr hA_nonneg
  have htwo_exp :
      2 * Real.exp ((C + D) * R ^ b) ≤
        Real.exp (((C + D) * R ^ b) + 1) := by
    calc
      2 * Real.exp ((C + D) * R ^ b)
          = Real.exp (Real.log 2) * Real.exp ((C + D) * R ^ b) := by
              have htwo : Real.exp (Real.log 2) = (2 : ℝ) := by
                exact Real.exp_log (by norm_num)
              rw [htwo]
      _ = Real.exp (Real.log 2 + (C + D) * R ^ b) := by
          rw [Real.exp_add]
      _ ≤ Real.exp (((C + D) * R ^ b) + 1) := by
          refine Real.exp_le_exp.2 ?_
          have hlog2 : Real.log 2 ≤ (1 : ℝ) := by
            rw [Real.log_le_iff_le_exp (by norm_num)]
            have h := Real.add_one_le_exp (1 : ℝ)
            norm_num at h
            exact h
          linarith
  have hxi :
      ‖riemannXi z‖ ≤ Real.exp (((C + D) * R ^ b) + 1) := by
    calc
      ‖riemannXi z‖
          = ‖z * (z - 1) * completedRiemannZeta₀ z + 1‖ / 2 := by
              simp [riemannXi]
      _ ≤ (‖z * (z - 1) * completedRiemannZeta₀ z‖ + 1) / 2 := by
          gcongr
          simpa using norm_add_le (z * (z - 1) * completedRiemannZeta₀ z) (1 : ℂ)
      _ ≤ ‖z * (z - 1) * completedRiemannZeta₀ z‖ + 1 := by
          nlinarith [norm_nonneg (z * (z - 1) * completedRiemannZeta₀ z)]
      _ ≤ Real.exp ((C + D) * R ^ b) + 1 := by
          gcongr
      _ ≤ 2 * Real.exp ((C + D) * R ^ b) := by
          linarith
      _ ≤ Real.exp (((C + D) * R ^ b) + 1) := htwo_exp
  exact hxi.trans (Real.exp_le_exp.2 (by
    calc
      ((C + D) * R ^ b) + 1 ≤ ((C + D) * R ^ b) + R ^ b := by
          gcongr
      _ = C' * R ^ b := by
          ring))

theorem summable_riemannXi_divisorZeroIndex₀_norm_inv_sq :
    Summable (fun p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ) =>
      ‖Complex.Hadamard.divisorZeroIndex₀_val p‖⁻¹ ^ (2 : ℕ)) := by
  simpa using
    (Complex.Hadamard.EntireOfOrderAtMost.summable_norm_inv_pow_divisorZeroIndex₀
      (ρ := (1 : ℝ)) (f := riemannXi) riemannXi_entireOfOrderAtMost_one
      (by norm_num) riemannXi_nontrivial)

theorem analyticOrderNatAt_riemannXi_zero : analyticOrderNatAt riemannXi 0 = 0 := by
  by_contra h
  have hzero : riemannXi 0 = 0 :=
    apply_eq_zero_of_analyticOrderNatAt_ne_zero (f := riemannXi) (z₀ := 0) h
  rw [riemannXi_zero] at hzero
  norm_num at hzero

theorem analyticOrderNatAt_completedRiemannZeta₀_zero :
    analyticOrderNatAt completedRiemannZeta₀ 0 = 0 := by
  by_contra h
  have hzero : completedRiemannZeta₀ 0 = 0 :=
    apply_eq_zero_of_analyticOrderNatAt_ne_zero (f := completedRiemannZeta₀) (z₀ := 0) h
  exact completedRiemannZeta₀_zero_ne_zero hzero

theorem summable_riemannXi_logDerivTerms_divisorZeroIndex₀
    {z : ℂ}
    (hz : ∀ p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ),
      z ≠ Complex.Hadamard.divisorZeroIndex₀_val p) :
    Summable (fun p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ) =>
      1 / (z - Complex.Hadamard.divisorZeroIndex₀_val p) +
        1 / Complex.Hadamard.divisorZeroIndex₀_val p) :=
  Complex.Hadamard.summable_logDerivTerms_divisorZeroIndex₀_of_summable_inv_sq
    summable_riemannXi_divisorZeroIndex₀_norm_inv_sq hz

theorem logDeriv_riemannXi_divisorCanonicalProduct_one_eq_tsum
    {z : ℂ}
    (hz : ∀ p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ),
      z ≠ Complex.Hadamard.divisorZeroIndex₀_val p) :
    logDeriv (Complex.Hadamard.divisorCanonicalProduct 1 riemannXi (Set.univ : Set ℂ)) z =
      ∑' p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ),
        (1 / (z - Complex.Hadamard.divisorZeroIndex₀_val p) +
          1 / Complex.Hadamard.divisorZeroIndex₀_val p) :=
  Complex.Hadamard.logDeriv_divisorCanonicalProduct_one_eq_tsum_of_forall_ne
    summable_riemannXi_divisorZeroIndex₀_norm_inv_sq hz

theorem logDeriv_riemannXi_eq_polynomial_derivative_add_tsum
    {P : Polynomial ℂ} {z : ℂ}
    (hfac : ∀ w : ℂ, riemannXi w =
      Complex.exp (Polynomial.eval w P) *
        Complex.Hadamard.divisorCanonicalProduct 1 riemannXi (Set.univ : Set ℂ) w)
    (hz : ∀ p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ),
      z ≠ Complex.Hadamard.divisorZeroIndex₀_val p) :
    logDeriv riemannXi z =
      Polynomial.eval z P.derivative +
        ∑' p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ),
          (1 / (z - Complex.Hadamard.divisorZeroIndex₀_val p) +
            1 / Complex.Hadamard.divisorZeroIndex₀_val p) := by
  let G : ℂ → ℂ :=
    Complex.Hadamard.divisorCanonicalProduct 1 riemannXi (Set.univ : Set ℂ)
  have hfun : riemannXi = fun w : ℂ => Complex.exp (Polynomial.eval w P) * G w := by
    funext w
    simpa [G] using hfac w
  have hdiff_exp : DifferentiableAt ℂ (fun w : ℂ => Complex.exp (Polynomial.eval w P)) z :=
    by fun_prop
  have hprod_ne :
      Complex.Hadamard.divisorCanonicalProduct 1 riemannXi (Set.univ : Set ℂ) z ≠ 0 :=
    Complex.Hadamard.divisorCanonicalProduct_ne_zero_of_forall_ne
      1 riemannXi summable_riemannXi_divisorZeroIndex₀_norm_inv_sq hz
  calc
    logDeriv riemannXi z =
        logDeriv (fun w : ℂ => Complex.exp (Polynomial.eval w P) * G w) z := by
          rw [hfun]
    _ = logDeriv (fun w : ℂ => Complex.exp (Polynomial.eval w P)) z + logDeriv G z := by
          exact logDeriv_mul z (Complex.exp_ne_zero _) (by simpa [G] using hprod_ne)
            hdiff_exp
            (by
              simpa [G] using
                Complex.Hadamard.differentiableAt_divisorCanonicalProduct_univ
                  1 riemannXi summable_riemannXi_divisorZeroIndex₀_norm_inv_sq z)
    _ = Polynomial.eval z P.derivative +
        ∑' p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ),
          (1 / (z - Complex.Hadamard.divisorZeroIndex₀_val p) +
            1 / Complex.Hadamard.divisorZeroIndex₀_val p) := by
          rw [Polynomial.logDeriv_exp_eval]
          rw [show logDeriv G z =
              ∑' p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ),
                (1 / (z - Complex.Hadamard.divisorZeroIndex₀_val p) +
                  1 / Complex.Hadamard.divisorZeroIndex₀_val p) from
            by
              simpa [G] using
                logDeriv_riemannXi_divisorCanonicalProduct_one_eq_tsum
                  hz]

theorem riemannXi_hadamard_polynomial_derivative_eval_eq
    {P Q : Polynomial ℂ} {z : ℂ} (hPfac : ∀ w : ℂ, riemannXi w = Complex.exp (Polynomial.eval w P) *
        Complex.Hadamard.divisorCanonicalProduct 1 riemannXi (Set.univ : Set ℂ) w)
    (hQfac : ∀ w : ℂ, riemannXi w =
      Complex.exp (Polynomial.eval w Q) *
        Complex.Hadamard.divisorCanonicalProduct 1 riemannXi (Set.univ : Set ℂ) w)
    (hz : ∀ p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ),
      z ≠ Complex.Hadamard.divisorZeroIndex₀_val p) :
    Polynomial.eval z P.derivative = Polynomial.eval z Q.derivative := by
  let S : ℂ := ∑' p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ),
    (1 / (z - Complex.Hadamard.divisorZeroIndex₀_val p) +
      1 / Complex.Hadamard.divisorZeroIndex₀_val p)
  have hP :=
    logDeriv_riemannXi_eq_polynomial_derivative_add_tsum
      (P := P) (z := z) hPfac hz
  have hQ :=
    logDeriv_riemannXi_eq_polynomial_derivative_add_tsum
      (P := Q) (z := z) hQfac hz
  have hsum : Polynomial.eval z P.derivative + S = Polynomial.eval z Q.derivative + S := by
    rw [← hP, ← hQ]
  exact add_right_cancel hsum

theorem riemannXi_hadamard_polynomial_derivative_eval_zero_eq
    {P Q : Polynomial ℂ} (hPfac : ∀ w : ℂ, riemannXi w =
      Complex.exp (Polynomial.eval w P) *
        Complex.Hadamard.divisorCanonicalProduct 1 riemannXi (Set.univ : Set ℂ) w)
    (hQfac : ∀ w : ℂ, riemannXi w = Complex.exp (Polynomial.eval w Q) *
      Complex.Hadamard.divisorCanonicalProduct 1 riemannXi (Set.univ : Set ℂ) w) :
    Polynomial.eval 0 P.derivative = Polynomial.eval 0 Q.derivative := by
  refine riemannXi_hadamard_polynomial_derivative_eval_eq
    (P := P) (Q := Q) (z := 0) hPfac hQfac ?_
  intro p
  exact (Complex.Hadamard.divisorZeroIndex₀_val_ne_zero p).symm

theorem riemannXi_hadamard_factorization :
    ∃ (P : Polynomial ℂ), P.degree ≤ 1 ∧ ∀ z : ℂ, riemannXi z =
        Complex.exp (Polynomial.eval z P) * z ^ (analyticOrderNatAt riemannXi 0) *
      Complex.Hadamard.divisorCanonicalProduct 1 riemannXi (Set.univ : Set ℂ) z := by
  simpa using
    (Complex.Hadamard.hadamard_factorization_of_order
      (f := riemannXi) (ρ := (1 : ℝ))
      (by norm_num) riemannXi_nontrivial
      riemannXi_entireOfOrderAtMost_one)

theorem riemannXi_hadamard_factorization_no_monomial :
    ∃ (P : Polynomial ℂ), P.degree ≤ 1 ∧ ∀ z : ℂ, riemannXi z =
        Complex.exp (Polynomial.eval z P) *
      Complex.Hadamard.divisorCanonicalProduct 1 riemannXi (Set.univ : Set ℂ) z := by
  rcases riemannXi_hadamard_factorization with ⟨P, hdeg, hfac⟩
  refine ⟨P, hdeg, ?_⟩
  intro z
  simpa [analyticOrderNatAt_riemannXi_zero, mul_assoc] using hfac z

theorem existsUnique_riemannXi_hadamard_polynomial_derivative_eval_zero :
    ∃! B : ℂ, ∃ P : Polynomial ℂ, P.degree ≤ 1 ∧ (∀ z : ℂ, riemannXi z =
        Complex.exp (Polynomial.eval z P) *
          Complex.Hadamard.divisorCanonicalProduct 1 riemannXi (Set.univ : Set ℂ) z) ∧
      B = Polynomial.eval 0 P.derivative := by
  rcases riemannXi_hadamard_factorization_no_monomial with ⟨P, hdeg, hfac⟩
  refine ⟨Polynomial.eval 0 P.derivative, ⟨P, hdeg, hfac, rfl⟩, ?_⟩
  intro B hB
  rcases hB with ⟨Q, _hQdeg, hQfac, rfl⟩
  exact (riemannXi_hadamard_polynomial_derivative_eval_zero_eq
    (P := P) (Q := Q) hfac hQfac).symm

theorem exists_riemannXi_logDeriv_eq_polynomial_derivative_add_tsum
    {z : ℂ} (hz : ∀ p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ),
      z ≠ Complex.Hadamard.divisorZeroIndex₀_val p) :  ∃ (P : Polynomial ℂ), P.degree ≤ 1 ∧
      logDeriv riemannXi z = Polynomial.eval z P.derivative +
          ∑' p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ),
            (1 / (z - Complex.Hadamard.divisorZeroIndex₀_val p) +
              1 / Complex.Hadamard.divisorZeroIndex₀_val p) := by
  rcases riemannXi_hadamard_factorization_no_monomial with ⟨P, hdeg, hfac⟩
  exact ⟨P, hdeg, logDeriv_riemannXi_eq_polynomial_derivative_add_tsum hfac hz⟩

theorem riemannXi_hadamard_factorization_reindex
    {ι : Type*} (e : ι ≃ Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ)) :
    ∃ (P : Polynomial ℂ), P.degree ≤ 1 ∧ ∀ z : ℂ, riemannXi z =
        Complex.exp (Polynomial.eval z P) * z ^ (analyticOrderNatAt riemannXi 0) *
      (∏' i : ι, Complex.weierstrassFactor 1
        (z / Complex.Hadamard.divisorZeroIndex₀_val (e i))) := by
  simpa using
    (Complex.Hadamard.hadamard_factorization_of_order_reindex
      (f := riemannXi) (ρ := (1 : ℝ))
      (by norm_num) riemannXi_nontrivial
      riemannXi_entireOfOrderAtMost_one e)

theorem riemannXi_hadamard_factorization_reindex_no_monomial
    {ι : Type*} (e : ι ≃ Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ)) :
    ∃ (P : Polynomial ℂ), P.degree ≤ 1 ∧ ∀ z : ℂ, riemannXi z =
        Complex.exp (Polynomial.eval z P) *
      (∏' i : ι, Complex.weierstrassFactor 1
        (z / Complex.Hadamard.divisorZeroIndex₀_val (e i))) := by
  rcases riemannXi_hadamard_factorization_reindex e with ⟨P, hdeg, hfac⟩
  refine ⟨P, hdeg, ?_⟩
  intro z
  simpa [analyticOrderNatAt_riemannXi_zero, mul_assoc] using hfac z

theorem riemannXi_hadamard_factorization_sequence
    (e : ℕ ≃ Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ)) :
    ∃ (P : Polynomial ℂ), P.degree ≤ 1 ∧ ∀ z : ℂ, riemannXi z =
        Complex.exp (Polynomial.eval z P) * z ^ (analyticOrderNatAt riemannXi 0) *
      Complex.canonicalProduct 1
        (fun n : ℕ => Complex.Hadamard.divisorZeroIndex₀_val (e n)) z := by
  simpa using
    (Complex.Hadamard.hadamard_factorization_of_order_sequence
      (f := riemannXi) (ρ := (1 : ℝ))
      (by norm_num) riemannXi_nontrivial
      riemannXi_entireOfOrderAtMost_one e)

theorem riemannXi_hadamard_factorization_sequence_no_monomial
    (e : ℕ ≃ Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ)) :
    ∃ (P : Polynomial ℂ), P.degree ≤ 1 ∧ ∀ z : ℂ, riemannXi z =
        Complex.exp (Polynomial.eval z P) *
      Complex.canonicalProduct 1
        (fun n : ℕ => Complex.Hadamard.divisorZeroIndex₀_val (e n)) z := by
  rcases riemannXi_hadamard_factorization_sequence e with ⟨P, hdeg, hfac⟩
  refine ⟨P, hdeg, ?_⟩
  intro z
  simpa [analyticOrderNatAt_riemannXi_zero, mul_assoc] using hfac z

theorem completedRiemannZeta₀_hadamard_factorization :
    ∃ (P : Polynomial ℂ), P.degree ≤ 1 ∧ ∀ z : ℂ, completedRiemannZeta₀ z =
        Complex.exp (Polynomial.eval z P) * z ^ (analyticOrderNatAt completedRiemannZeta₀ 0) *
      Complex.Hadamard.divisorCanonicalProduct 1 completedRiemannZeta₀ (Set.univ : Set ℂ) z := by
  simpa using
    (Complex.Hadamard.hadamard_factorization_of_order
      (f := completedRiemannZeta₀) (ρ := (1 : ℝ))
      (by norm_num) completedRiemannZeta₀_nontrivial
      completedRiemannZeta₀_entireOfOrderAtMost_one)

theorem completedRiemannZeta₀_hadamard_factorization_no_monomial :
    ∃ (P : Polynomial ℂ), P.degree ≤ 1 ∧ ∀ z : ℂ, completedRiemannZeta₀ z =
        Complex.exp (Polynomial.eval z P) *
      Complex.Hadamard.divisorCanonicalProduct 1 completedRiemannZeta₀ (Set.univ : Set ℂ) z := by
  rcases completedRiemannZeta₀_hadamard_factorization with ⟨P, hdeg, hfac⟩
  refine ⟨P, hdeg, ?_⟩
  intro z
  simpa [analyticOrderNatAt_completedRiemannZeta₀_zero, mul_assoc] using hfac z

theorem completedRiemannZeta₀_hadamard_factorization_reindex
    {ι : Type*}
    (e : ι ≃ Complex.Hadamard.divisorZeroIndex₀ completedRiemannZeta₀ (Set.univ : Set ℂ)) :
    ∃ (P : Polynomial ℂ), P.degree ≤ 1 ∧ ∀ z : ℂ, completedRiemannZeta₀ z =
        Complex.exp (Polynomial.eval z P) * z ^ (analyticOrderNatAt completedRiemannZeta₀ 0) *
      (∏' i : ι, Complex.weierstrassFactor 1
        (z / Complex.Hadamard.divisorZeroIndex₀_val (e i))) := by
  simpa using
    (Complex.Hadamard.hadamard_factorization_of_order_reindex
      (f := completedRiemannZeta₀) (ρ := (1 : ℝ))
      (by norm_num) completedRiemannZeta₀_nontrivial
      completedRiemannZeta₀_entireOfOrderAtMost_one e)

theorem completedRiemannZeta₀_hadamard_factorization_reindex_no_monomial
    {ι : Type*}
    (e : ι ≃ Complex.Hadamard.divisorZeroIndex₀ completedRiemannZeta₀ (Set.univ : Set ℂ)) :
    ∃ (P : Polynomial ℂ), P.degree ≤ 1 ∧ ∀ z : ℂ, completedRiemannZeta₀ z =
        Complex.exp (Polynomial.eval z P) *
      (∏' i : ι, Complex.weierstrassFactor 1
        (z / Complex.Hadamard.divisorZeroIndex₀_val (e i))) := by
  rcases completedRiemannZeta₀_hadamard_factorization_reindex e with ⟨P, hdeg, hfac⟩
  refine ⟨P, hdeg, ?_⟩
  intro z
  simpa [analyticOrderNatAt_completedRiemannZeta₀_zero, mul_assoc] using hfac z

theorem completedRiemannZeta₀_hadamard_factorization_sequence
    (e : ℕ ≃ Complex.Hadamard.divisorZeroIndex₀ completedRiemannZeta₀ (Set.univ : Set ℂ)) :
    ∃ (P : Polynomial ℂ), P.degree ≤ 1 ∧ ∀ z : ℂ, completedRiemannZeta₀ z =
        Complex.exp (Polynomial.eval z P) * z ^ (analyticOrderNatAt completedRiemannZeta₀ 0) *
      Complex.canonicalProduct 1
        (fun n : ℕ => Complex.Hadamard.divisorZeroIndex₀_val (e n)) z := by
  simpa using
    (Complex.Hadamard.hadamard_factorization_of_order_sequence
      (f := completedRiemannZeta₀) (ρ := (1 : ℝ))
      (by norm_num) completedRiemannZeta₀_nontrivial
      completedRiemannZeta₀_entireOfOrderAtMost_one e)

theorem completedRiemannZeta₀_hadamard_factorization_sequence_no_monomial
    (e : ℕ ≃ Complex.Hadamard.divisorZeroIndex₀ completedRiemannZeta₀ (Set.univ : Set ℂ)) :
    ∃ (P : Polynomial ℂ), P.degree ≤ 1 ∧ ∀ z : ℂ, completedRiemannZeta₀ z =
        Complex.exp (Polynomial.eval z P) *
      Complex.canonicalProduct 1
        (fun n : ℕ => Complex.Hadamard.divisorZeroIndex₀_val (e n)) z := by
  rcases completedRiemannZeta₀_hadamard_factorization_sequence e with ⟨P, hdeg, hfac⟩
  refine ⟨P, hdeg, ?_⟩
  intro z
  simpa [analyticOrderNatAt_completedRiemannZeta₀_zero, mul_assoc] using hfac z
end
end
end File65

-- Upstream module SchoenfeldRH.Xi.Basic
section File66


open Complex

namespace SchoenfeldRH

theorem riemannXi_one : riemannXi 1 = 1 / 2 := by
  simp [riemannXi]

private lemma riemannXi_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) : riemannXi s ≠ 0 := by
  rcases eq_or_ne s 1 with rfl | h1
  · rw [riemannXi_one]; norm_num
  have h0 : s ≠ 0 := by
    rintro rfl
    simp at hs
    linarith
  have hζ := riemannZeta_ne_zero_of_one_le_re hs
  rw [riemannZeta_def_of_ne_zero h0] at hζ
  have hΛ : completedRiemannZeta s ≠ 0 := by
    intro h
    exact hζ (by rw [h, zero_div])
  rw [riemannXi_eq_mul_completedRiemannZeta h0 h1]
  exact div_ne_zero (mul_ne_zero (mul_ne_zero h0 (sub_ne_zero.mpr h1)) hΛ) two_ne_zero

theorem riemannXi_eq_zero_re {ρ : ℂ} (h : riemannXi ρ = 0) : 0 < ρ.re ∧ ρ.re < 1 := by
  constructor
  · by_contra hc
    have h1 : 1 ≤ (1 - ρ).re := by
      simp only [sub_re, one_re]
      linarith [not_lt.mp hc]
    exact riemannXi_ne_zero_of_one_le_re h1 (by rw [riemannXi_one_sub, h])
  · by_contra hc
    exact riemannXi_ne_zero_of_one_le_re (not_lt.mp hc) h

theorem countable_riemannXi_zeros : Countable {ρ : ℂ // riemannXi ρ = 0} := by
  have hana : AnalyticOnNhd ℂ riemannXi Set.univ :=
    (analyticOnNhd_univ_iff_differentiable).mpr differentiable_riemannXi
  have h0 : riemannXi 0 ≠ 0 := by rw [riemannXi_zero]; norm_num
  have hcod : (riemannXi ⁻¹' {0})ᶜ ∈ Filter.codiscreteWithin (Set.univ : Set ℂ) :=
    hana.preimage_zero_mem_codiscrete h0
  have hdisc := isDiscrete_of_codiscreteWithin hcod
  have hc : (riemannXi ⁻¹' {0} ∩ Set.univ).Countable :=
    (HereditarilyLindelofSpace.isLindelof _).countable_of_isDiscrete hdisc
  rw [Set.inter_univ] at hc
  exact hc.to_subtype

private lemma hasDerivAt_riemannXi (s : ℂ) :
    HasDerivAt riemannXi
      (((1 * (s - 1) + s * 1) * completedRiemannZeta₀ s +
        s * (s - 1) * deriv completedRiemannZeta₀ s) / 2) s := by
  have hΛ : HasDerivAt completedRiemannZeta₀ (deriv completedRiemannZeta₀ s) s :=
    (differentiable_completedZeta₀ s).hasDerivAt
  have h1 : HasDerivAt (fun z : ℂ => z * (z - 1)) (1 * (s - 1) + s * 1) s :=
    (hasDerivAt_id s).mul ((hasDerivAt_id s).sub_const 1)
  have h2 := ((h1.mul hΛ).add_const 1).div_const 2
  exact h2

theorem logDeriv_riemannXi_one :
    logDeriv riemannXi 1 =
      ((1 + Real.eulerMascheroniConstant / 2 - Real.log (4 * Real.pi) / 2 : ℝ) : ℂ) := by
  rw [logDeriv_apply, (hasDerivAt_riemannXi 1).deriv, riemannXi_one, completedRiemannZeta₀_one]
  have hlog : Complex.log (4 * (Real.pi : ℂ)) = ((Real.log (4 * Real.pi) : ℝ) : ℂ) := by
    rw [Complex.ofReal_log (by positivity)]
    push_cast
    rfl
  rw [hlog]
  push_cast
  ring

theorem logDeriv_riemannXi_zero :
    logDeriv riemannXi 0 =
      -((1 + Real.eulerMascheroniConstant / 2 - Real.log (4 * Real.pi) / 2 : ℝ) : ℂ) := by
  have h01 : completedRiemannZeta₀ 0 = completedRiemannZeta₀ 1 := by
    have := completedRiemannZeta₀_one_sub 1
    simpa using this
  rw [logDeriv_apply, (hasDerivAt_riemannXi 0).deriv, riemannXi_zero, h01,
    completedRiemannZeta₀_one]
  have hlog : Complex.log (4 * (Real.pi : ℂ)) = ((Real.log (4 * Real.pi) : ℝ) : ℂ) := by
    rw [Complex.ofReal_log (by positivity)]
    push_cast
    rfl
  rw [hlog]
  push_cast
  ring

end SchoenfeldRH
end File66

-- Upstream module SchoenfeldRH.Xi.Hadamard
section File67


open Complex

namespace SchoenfeldRH

open Complex.Hadamard in
private lemma toNat_divisor_riemannXi (z : ℂ) :
    Int.toNat (MeromorphicOn.divisor riemannXi (Set.univ : Set ℂ) z) =
      analyticOrderNatAt riemannXi z := by
  simp [divisor_univ_eq_analyticOrderNatAt_int differentiable_riemannXi z]

private lemma riemannXi_ne_zero_of_eq_zero {ρ : ℂ} (h : riemannXi ρ = 0) : ρ ≠ 0 := by
  rintro rfl
  rw [riemannXi_zero] at h
  norm_num at h

open Complex.Hadamard in
 
private noncomputable def zeroIndexEquiv :
    divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ) ≃
      Σ ρ : {ρ : ℂ // riemannXi ρ = 0}, Fin (analyticOrderNatAt riemannXi ρ) where
  toFun p :=
    ⟨⟨p.1.1, by
        have q : Fin (analyticOrderNatAt riemannXi p.1.1) :=
          Fin.cast (toNat_divisor_riemannXi p.1.1) p.1.2
        exact apply_eq_zero_of_analyticOrderNatAt_ne_zero (Nat.ne_of_gt q.pos)⟩,
      Fin.cast (toNat_divisor_riemannXi p.1.1) p.1.2⟩
  invFun x :=
    ⟨⟨x.1.1, Fin.cast (toNat_divisor_riemannXi x.1.1).symm x.2⟩,
      riemannXi_ne_zero_of_eq_zero x.1.2⟩
  left_inv := by
    rintro ⟨⟨z, q⟩, hz⟩
    rfl
  right_inv := by
    rintro ⟨⟨z, hz⟩, q⟩
    rfl

open Complex.Hadamard in
private lemma zeroIndexEquiv_symm_val
    (x : Σ ρ : {ρ : ℂ // riemannXi ρ = 0}, Fin (analyticOrderNatAt riemannXi ρ)) :
    divisorZeroIndex₀_val (zeroIndexEquiv.symm x) = x.1.1 := rfl

open Complex.Hadamard in
private lemma ne_divisorZeroIndex₀_val {s : ℂ} (hs : riemannXi s ≠ 0)
    (p : divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ)) : s ≠ divisorZeroIndex₀_val p := by
  intro h
  exact hs (h ▸ (zeroIndexEquiv p).1.2)

theorem summable_riemannXi_zeros_rpow {τ : ℝ} (hτ : 1 < τ) :
    Summable fun ρ : {ρ : ℂ // riemannXi ρ = 0} =>
      (analyticOrderNatAt riemannXi ρ : ℝ) / ‖(ρ : ℂ)‖ ^ τ := by
  have hgrowth := riemannXi_entireOfOrderAtMost_one.exists_log_growth
    (τ := (1 + τ) / 2) (by linarith) (by linarith)
  have h1 := Complex.Hadamard.summable_norm_inv_rpow_divisorZeroIndex₀_of_growth
    (f := riemannXi) (ρ := (1 + τ) / 2) (τ := τ) (by linarith) (by linarith)
    differentiable_riemannXi riemannXi_nontrivial hgrowth
  have h2 := (zeroIndexEquiv.symm.summable_iff).2 h1
  have h3 := h2.sigma
  refine h3.congr fun ρ => ?_
  simp only [Function.comp_apply, zeroIndexEquiv_symm_val, tsum_fintype, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [Real.inv_rpow (norm_nonneg _), div_eq_mul_inv]

theorem hasSum_logDeriv_riemannXi {s : ℂ} (hs : riemannXi s ≠ 0) :
    HasSum (fun ρ : {ρ : ℂ // riemannXi ρ = 0} =>
        (analyticOrderNatAt riemannXi ρ : ℂ) * (1 / (s - ρ) + 1 / ρ))
      (logDeriv riemannXi s - logDeriv riemannXi 0) := by
  obtain ⟨P, hdeg, hfac⟩ := riemannXi_hadamard_factorization_no_monomial
  have h0 : riemannXi 0 ≠ 0 := by rw [riemannXi_zero]; norm_num
  have es := logDeriv_riemannXi_eq_polynomial_derivative_add_tsum hfac (ne_divisorZeroIndex₀_val hs)
  have e0 := logDeriv_riemannXi_eq_polynomial_derivative_add_tsum hfac (ne_divisorZeroIndex₀_val h0)
  have hz : (∑' p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ),
      (1 / ((0 : ℂ) - Complex.Hadamard.divisorZeroIndex₀_val p) +
        1 / Complex.Hadamard.divisorZeroIndex₀_val p)) = 0 := by
    have hterm : ∀ p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ),
        1 / ((0 : ℂ) - Complex.Hadamard.divisorZeroIndex₀_val p) +
          1 / Complex.Hadamard.divisorZeroIndex₀_val p = 0 := fun p => by
      rw [zero_sub, one_div, one_div, inv_neg, neg_add_cancel]
    simp only [hterm, tsum_zero]
  have hP : Polynomial.eval s P.derivative = Polynomial.eval 0 P.derivative := by
    rw [Polynomial.eq_X_add_C_of_degree_le_one hdeg]
    simp
  have hsum := (summable_riemannXi_logDerivTerms_divisorZeroIndex₀
    (ne_divisorZeroIndex₀_val hs)).hasSum
  have hval : (∑' p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ),
      (1 / (s - Complex.Hadamard.divisorZeroIndex₀_val p) +
        1 / Complex.Hadamard.divisorZeroIndex₀_val p)) =
      logDeriv riemannXi s - logDeriv riemannXi 0 := by
    rw [es, e0, hz, hP]; ring
  rw [hval] at hsum
  have h2 := (zeroIndexEquiv.symm.hasSum_iff).2 hsum
  have h3 := h2.sigma (fun ρ => hasSum_fintype _)
  refine h3.congr_fun fun ρ => ?_
  simp only [Function.comp_apply, zeroIndexEquiv_symm_val, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]

end SchoenfeldRH
end File67

-- Upstream module SchoenfeldRH.Xi.LogDeriv
section File68


open Complex

namespace SchoenfeldRH

private theorem harmonic_256_le : harmonic 256 ≤ 61244/10000 := by
  rw [harmonic]; decide +kernel

theorem logDeriv_riemannZeta_eq_logDeriv_riemannXi {s : ℂ} (hs : 1 < s.re) :
    logDeriv riemannZeta s =
      logDeriv riemannXi s - 1 / s - 1 / (s - 1) + (Real.log Real.pi : ℂ) / 2 - digamma (s / 2) / 2 := by
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs; linarith
  have hs1 : s ≠ 1 := by rintro rfl; simp at hs
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.2 hs1
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
  have hG : Gamma (s / 2) ≠ 0 := by
    apply Gamma_ne_zero_of_re_pos
    simp; linarith
  have hne : ∀ m : ℕ, s / 2 ≠ -(m : ℂ) := by
    intro m h
    have h' := congrArg Complex.re h
    simp at h'
    have : (0:ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hζ : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
  have hP : (Real.pi : ℂ) ^ (-s / 2) ≠ 0 := by
    simp [hπ]
  have dζ : DifferentiableAt ℂ riemannZeta s := differentiableAt_riemannZeta hs1
  have dG : DifferentiableAt ℂ (fun w : ℂ => Gamma (w / 2)) s := by
    have : DifferentiableAt ℂ Gamma (s / 2) :=
      differentiableAt_Gamma _ hne
    exact this.comp s (differentiableAt_id.div_const 2)
  have dP : HasDerivAt (fun w : ℂ => (Real.pi : ℂ) ^ (-w / 2))
      ((Real.pi : ℂ) ^ (-s / 2) * Complex.log Real.pi * (-1 / 2)) s := by
    have h : HasDerivAt (fun w : ℂ => -w / 2) (-1 / 2) s := by
      simpa using ((hasDerivAt_id s).neg).div_const 2
    exact h.const_cpow (Or.inl hπ)
  have hev : riemannXi =ᶠ[nhds s] fun w => (1 / 2 : ℂ) *
      (w * ((w - 1) * ((Real.pi : ℂ) ^ (-w / 2) * (Gamma (w / 2) * riemannZeta w)))) := by
    have ho : IsOpen {w : ℂ | 1 < w.re} := isOpen_lt continuous_const continuous_re
    filter_upwards [ho.mem_nhds hs] with w hw
    have hw' : (1:ℝ) < w.re := hw
    have hw0 : w ≠ 0 := by rintro rfl; simp at hw'; linarith
    have hw1 : w ≠ 1 := by rintro rfl; simp at hw'
    have hGw : Gammaℝ w ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by linarith)
    rw [riemannXi_eq_mul_completedRiemannZeta hw0 hw1, riemannZeta_def_of_ne_zero hw0]
    have hGw' : Gamma (w / 2) ≠ 0 := by
      apply Gamma_ne_zero_of_re_pos
      simp; linarith
    have hPw : (Real.pi : ℂ) ^ (-w / 2) ≠ 0 := by
      simp [hπ]
    rw [Gammaℝ_def]
    field_simp
  have e1 : logDeriv riemannXi s = logDeriv (fun w => (1 / 2 : ℂ) *
      (w * ((w - 1) * ((Real.pi : ℂ) ^ (-w / 2) * (Gamma (w / 2) * riemannZeta w))))) s := by
    simp only [logDeriv_apply]
    rw [hev.deriv_eq, hev.eq_of_nhds]
  have lG : logDeriv (fun w : ℂ => Gamma (w / 2)) s = digamma (s / 2) / 2 := by
    have := logDeriv_comp (f := Gamma) (g := fun w : ℂ => w / 2) (x := s)
      (differentiableAt_Gamma _ hne) (differentiableAt_id.div_const 2)
    rw [show (Gamma ∘ fun w : ℂ => w / 2) = fun w : ℂ => Gamma (w / 2) from rfl] at this
    rw [this, digamma_def]
    simp [div_eq_mul_inv]
  have lP : logDeriv (fun w : ℂ => (Real.pi : ℂ) ^ (-w / 2)) s = -(Real.log Real.pi : ℂ) / 2 := by
    rw [logDeriv_apply, dP.deriv, Complex.ofReal_log Real.pi_pos.le]
    field_simp
  have d1 : DifferentiableAt ℂ (fun w : ℂ => Gamma (w / 2) * riemannZeta w) s := dG.mul dζ
  have d2 : DifferentiableAt ℂ
      (fun w : ℂ => (Real.pi : ℂ) ^ (-w / 2) * (Gamma (w / 2) * riemannZeta w)) s :=
    dP.differentiableAt.mul d1
  have d3 : DifferentiableAt ℂ
      (fun w : ℂ => (w - 1) * ((Real.pi : ℂ) ^ (-w / 2) * (Gamma (w / 2) * riemannZeta w))) s :=
    (differentiableAt_fun_id.sub_const 1).mul d2
  have lid : logDeriv (fun w : ℂ => w) s = 1 / s := logDeriv_id s
  have lsub : logDeriv (fun w : ℂ => w - 1) s = 1 / (s - 1) := by
    rw [logDeriv_apply]
    simp
  have n1 : Gamma (s / 2) * riemannZeta s ≠ 0 := mul_ne_zero hG hζ
  have n2 : (Real.pi : ℂ) ^ (-s / 2) * (Gamma (s / 2) * riemannZeta s) ≠ 0 := mul_ne_zero hP n1
  have n3 : (s - 1) * ((Real.pi : ℂ) ^ (-s / 2) * (Gamma (s / 2) * riemannZeta s)) ≠ 0 :=
    mul_ne_zero hs1' n2
  have m1 : logDeriv (fun w : ℂ => Gamma (w / 2) * riemannZeta w) s =
      logDeriv (fun w : ℂ => Gamma (w / 2)) s + logDeriv riemannZeta s :=
    logDeriv_fun_mul s hG hζ dG dζ
  have m2 : logDeriv (fun w : ℂ => (Real.pi : ℂ) ^ (-w / 2) * (Gamma (w / 2) * riemannZeta w)) s =
      logDeriv (fun w : ℂ => (Real.pi : ℂ) ^ (-w / 2)) s +
        logDeriv (fun w : ℂ => Gamma (w / 2) * riemannZeta w) s :=
    logDeriv_fun_mul s hP n1 dP.differentiableAt d1
  have m3 : logDeriv
      (fun w : ℂ => (w - 1) * ((Real.pi : ℂ) ^ (-w / 2) * (Gamma (w / 2) * riemannZeta w))) s =
      logDeriv (fun w : ℂ => w - 1) s +
        logDeriv (fun w : ℂ => (Real.pi : ℂ) ^ (-w / 2) * (Gamma (w / 2) * riemannZeta w)) s :=
    logDeriv_fun_mul s hs1' n2 (differentiableAt_fun_id.sub_const 1) d2
  have m4 : logDeriv (fun w : ℂ =>
      w * ((w - 1) * ((Real.pi : ℂ) ^ (-w / 2) * (Gamma (w / 2) * riemannZeta w)))) s =
      logDeriv (fun w : ℂ => w) s + logDeriv
        (fun w : ℂ => (w - 1) * ((Real.pi : ℂ) ^ (-w / 2) * (Gamma (w / 2) * riemannZeta w))) s :=
    logDeriv_fun_mul s hs0 n3 differentiableAt_fun_id d3
  rw [e1, logDeriv_const_mul _ _ (by norm_num), m4, m3, m2, m1, lG, lP, lid, lsub]
  ring

theorem two_add_eulerMascheroni_sub_log_four_pi_lt :
    2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi) < 1 / 20 := by
  have hγ : Real.eulerMascheroniConstant < 61244/10000 - 8 * Real.log 2 := by
    have h := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' 256
    have e : Real.eulerMascheroniSeq' 256 = (harmonic 256 : ℝ) - Real.log 256 := by
      simp only [Real.eulerMascheroniSeq', OfNat.ofNat_ne_zero, ↓reduceIte, Nat.cast_ofNat]
    have l : Real.log (256:ℝ) = 8 * Real.log 2 := by
      rw [show (256:ℝ) = 2 ^ 8 by norm_num, Real.log_pow]; norm_num
    have c : (harmonic 256 : ℝ) ≤ 61244/10000 := by
      have := (Rat.cast_le (K := ℝ)).2 harmonic_256_le
      push_cast at this
      exact this
    linarith
  have hπ : 33 * Real.log 2 + (1 - 1/(102/100:ℝ)) ≤ 20 * Real.log Real.pi := by
    have h1 : (1 - 1/(102/100:ℝ)) ≤ Real.log (102/100) := by
      have := Real.one_sub_inv_le_log_of_pos (show (0:ℝ) < 102/100 by norm_num)
      simpa using this
    have h2 : (2:ℝ)^33 * (102/100) ≤ Real.pi ^ 20 := by
      have : (3.1415:ℝ)^20 ≤ Real.pi ^ 20 := pow_le_pow_left₀ (by norm_num) Real.pi_gt_d4.le 20
      refine le_trans ?_ this
      norm_num
    have h3 := Real.log_le_log (by positivity) h2
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow] at h3
    push_cast at h3
    linarith
  have h4 : Real.log (4 * Real.pi) = 2 * Real.log 2 + Real.log Real.pi := by
    rw [Real.log_mul (by norm_num) Real.pi_pos.ne', show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have := Real.log_two_gt_d9
  have := Real.log_two_lt_d9
  rw [h4]
  norm_num at hπ
  linarith

end SchoenfeldRH
end File68

-- Upstream module SchoenfeldRH.Xi.Compat
section File69


open Complex

namespace SchoenfeldRH

noncomputable def xiConst : ℝ := 1 + Real.eulerMascheroniConstant / 2 - Real.log (4 * Real.pi) / 2

theorem riemannXi_zero_re_mem {ρ : ℂ} (h : riemannXi ρ = 0) : 0 < ρ.re ∧ ρ.re < 1 :=
  riemannXi_eq_zero_re h

theorem deriv_div_riemannXi_one : deriv riemannXi 1 / riemannXi 1 = (xiConst : ℂ) := by
  rw [← logDeriv_apply]; exact logDeriv_riemannXi_one

theorem deriv_div_riemannXi_zero : deriv riemannXi 0 / riemannXi 0 = -(xiConst : ℂ) := by
  rw [← logDeriv_apply]; exact logDeriv_riemannXi_zero

theorem hasSum_hadamard_riemannXi {s : ℂ} (hs : riemannXi s ≠ 0) :
    HasSum (fun ρ : {ρ : ℂ // riemannXi ρ = 0} =>
        (analyticOrderNatAt riemannXi ρ : ℂ) * (1 / (s - ρ) + 1 / ρ))
      (deriv riemannXi s / riemannXi s + (xiConst : ℂ)) := by
  have h := hasSum_logDeriv_riemannXi hs
  rwa [logDeriv_apply, logDeriv_apply, deriv_div_riemannXi_zero, sub_neg_eq_add] at h

theorem logDeriv_riemannZeta_eq {s : ℂ} (hs : 1 < s.re) :
    deriv riemannZeta s / riemannZeta s =
      deriv riemannXi s / riemannXi s - 1 / s - 1 / (s - 1) + (Real.log Real.pi : ℂ) / 2
        - digamma (s / 2) / 2 := by
  have h := logDeriv_riemannZeta_eq_logDeriv_riemannXi hs
  rwa [logDeriv_apply, logDeriv_apply] at h

theorem two_mul_xiConst_lt : 2 * xiConst < 1 / 20 := by
  have := two_add_eulerMascheroni_sub_log_four_pi_lt
  unfold xiConst
  linarith

end SchoenfeldRH
end File69

-- Upstream module SchoenfeldRH.ZeroSum.Defs
section File70


namespace SchoenfeldRH

open Complex

noncomputable def zeroSumW (B : ℝ) : ℝ :=
  ∑' ρ : {ρ : ℂ // riemannXi ρ = 0},
    (analyticOrderNatAt riemannXi ρ : ℝ) / (‖(ρ : ℂ)‖ * ‖((B : ℂ) + 1 / 2) - (ρ : ℂ)‖)

end SchoenfeldRH
end File70

-- Upstream module SchoenfeldRH.ZeroSum.Basic
section File71


namespace SchoenfeldRH

open Complex

theorem riemannXi_zero_re_of_RH (hRH : RiemannHypothesis) {ρ : ℂ} (h : riemannXi ρ = 0) : ρ.re = 1 / 2 := by
  obtain ⟨h0, h1⟩ := riemannXi_zero_re_mem h
  have hρ0 : ρ ≠ 0 := by rintro rfl; simp at h0
  have hρ1 : ρ ≠ 1 := by rintro rfl; simp at h1
  rw [riemannXi_eq_mul_completedRiemannZeta hρ0 hρ1] at h
  have hΛ : completedRiemannZeta ρ = 0 := by
    have h' : ρ * (ρ - 1) * completedRiemannZeta ρ = 0 := by
      rcases div_eq_zero_iff.1 h with h | h
      · exact h
      · exact absurd h two_ne_zero
    rcases mul_eq_zero.1 h' with h | h
    · rcases mul_eq_zero.1 h with h | h
      · exact absurd h hρ0
      · exact absurd (sub_eq_zero.1 h) hρ1
    · exact h
  apply hRH ρ
  · rw [riemannZeta_def_of_ne_zero hρ0, hΛ, zero_div]
  · rintro ⟨n, rfl⟩
    have : (-2 * ((n : ℂ) + 1)).re = -2 * ((n : ℝ) + 1) := by simp
    rw [this] at h0
    have : (0 : ℝ) ≤ n := n.cast_nonneg
    linarith
  · exact hρ1

theorem riemannXi_ne_zero_of_RH (hRH : RiemannHypothesis) {s : ℂ} (hs : s.re ≠ 1 / 2) : riemannXi s ≠ 0 :=
  fun h => hs (riemannXi_zero_re_of_RH hRH h)

theorem riemannXi_zero_ne_zero {ρ : ℂ} (h : riemannXi ρ = 0) : ρ ≠ 0 := by
  rintro rfl
  rw [riemannXi_zero] at h
  norm_num at h

theorem norm_sq_of_re_eq_half {ρ : ℂ} (hρ : ρ.re = 1 / 2) : ‖ρ‖ ^ 2 = 1 / 4 + ρ.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, hρ]
  ring

theorem norm_sq_shift_sub {ρ : ℂ} (hρ : ρ.re = 1 / 2) (B : ℝ) :
    ‖((B : ℂ) + 1 / 2) - ρ‖ ^ 2 = B ^ 2 + ρ.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [hρ]
  ring

theorem one_sub_inv_add_inv_of_re_eq_half {ρ : ℂ} (hρ : ρ.re = 1 / 2) :
    1 / (1 - ρ) + 1 / ρ = ((1 / (1 / 4 + ρ.im ^ 2) : ℝ) : ℂ) := by
  have hpos : (0 : ℝ) < 1 / 4 + ρ.im ^ 2 := by positivity
  have hρ0 : ρ ≠ 0 := by intro h; rw [h] at hρ; norm_num at hρ
  have hρ1 : 1 - ρ ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp [hρ] at this
    norm_num at this
  have key : ρ * (1 - ρ) = ((1 / 4 + ρ.im ^ 2 : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [hρ, pow_two] <;> ring
  have hne : ((1 / 4 + ρ.im ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  rw [Complex.ofReal_div, Complex.ofReal_one, ← key]
  field_simp
  ring

theorem hasSum_zero_inv_norm_sq (hRH : RiemannHypothesis) :
    HasSum (fun ρ : {ρ : ℂ // riemannXi ρ = 0} => (analyticOrderNatAt riemannXi ρ : ℝ) / ‖(ρ : ℂ)‖ ^ 2)
      (2 * xiConst) := by
  have h1 := hasSum_hadamard_riemannXi (s := 1) (by rw [riemannXi_one]; norm_num)
  rw [deriv_div_riemannXi_one] at h1
  have h2 := Complex.hasSum_re h1
  have e : ((xiConst : ℂ) + (xiConst : ℂ)).re = 2 * xiConst := by simp; ring
  rw [e] at h2
  convert h2 using 1
  funext ρ
  have hre := riemannXi_zero_re_of_RH hRH ρ.2
  rw [norm_sq_of_re_eq_half hre, one_sub_inv_add_inv_of_re_eq_half hre, ← Complex.ofReal_natCast,
    ← Complex.ofReal_mul, Complex.ofReal_re]
  ring

theorem summable_zero_inv_norm_sq (hRH : RiemannHypothesis) :
    Summable (fun ρ : {ρ : ℂ // riemannXi ρ = 0} => (analyticOrderNatAt riemannXi ρ : ℝ) / ‖(ρ : ℂ)‖ ^ 2) :=
  (hasSum_zero_inv_norm_sq hRH).summable

theorem tsum_zero_inv_norm_sq_le (hRH : RiemannHypothesis) :
    ∑' ρ : {ρ : ℂ // riemannXi ρ = 0}, (analyticOrderNatAt riemannXi ρ : ℝ) / ‖(ρ : ℂ)‖ ^ 2 ≤ 1 / 20 := by
  rw [(hasSum_zero_inv_norm_sq hRH).tsum_eq]
  exact two_mul_xiConst_lt.le

theorem re_inv_shift_sub_add_inv {ρ : ℂ} (hρ : ρ.re = 1 / 2) {β : ℝ} (hβ : 0 < β) :
    (1 / (((β + 1 / 2 : ℝ) : ℂ) - ρ) + 1 / ρ).re
      = β / (β ^ 2 + ρ.im ^ 2) + 1 / 2 * (1 / (1 / 4 + ρ.im ^ 2)) := by
  have hpos : (0 : ℝ) < 1 / 4 + ρ.im ^ 2 := by positivity
  have hpos2 : (0 : ℝ) < β ^ 2 + ρ.im ^ 2 := by positivity
  have n1 : Complex.normSq (((β + 1 / 2 : ℝ) : ℂ) - ρ) = β ^ 2 + ρ.im ^ 2 := by
    simp [Complex.normSq_apply, hρ]; ring
  have n2 : Complex.normSq ρ = 1 / 4 + ρ.im ^ 2 := by
    simp [Complex.normSq_apply, hρ]; ring
  have e1 : (1 / (((β + 1 / 2 : ℝ) : ℂ) - ρ)).re = β / (β ^ 2 + ρ.im ^ 2) := by
    rw [one_div, Complex.inv_re, n1, Complex.sub_re, Complex.ofReal_re, hρ]
    ring
  have e2 : (1 / ρ).re = 1 / 2 * (1 / (1 / 4 + ρ.im ^ 2)) := by
    rw [one_div, Complex.inv_re, n2, hρ]
    ring
  rw [Complex.add_re, e1, e2]

theorem hasSum_poisson (hRH : RiemannHypothesis) {β : ℝ} (hβ : 0 < β) :
    HasSum (fun ρ : {ρ : ℂ // riemannXi ρ = 0} =>
        (analyticOrderNatAt riemannXi ρ : ℝ) * (β / (β ^ 2 + (ρ : ℂ).im ^ 2)))
      (deriv riemannXi ((β + 1 / 2 : ℝ) : ℂ) / riemannXi ((β + 1 / 2 : ℝ) : ℂ)).re := by
  have hs : riemannXi ((β + 1 / 2 : ℝ) : ℂ) ≠ 0 := by
    apply riemannXi_ne_zero_of_RH hRH
    rw [Complex.ofReal_re]
    linarith
  have h1 := Complex.hasSum_re (hasSum_hadamard_riemannXi hs)
  have h2 := (hasSum_zero_inv_norm_sq hRH).mul_left (1 / 2)
  have h3 := h1.sub h2
  convert h3 using 1
  · funext ρ
    have hre := riemannXi_zero_re_of_RH hRH ρ.2
    rw [norm_sq_of_re_eq_half hre, ← Complex.ofReal_natCast, Complex.re_ofReal_mul,
      re_inv_shift_sub_add_inv hre hβ]
    ring
  · simp

theorem zeroSumW_term_nonneg (B : ℝ) (ρ : {ρ : ℂ // riemannXi ρ = 0}) :
    0 ≤ (analyticOrderNatAt riemannXi ρ : ℝ) / (‖(ρ : ℂ)‖ * ‖((B : ℂ) + 1 / 2) - (ρ : ℂ)‖) := by
  positivity

theorem summable_zeroSumW (hRH : RiemannHypothesis) (B : ℝ) (hB : 0 < B) :
    Summable fun ρ : {ρ : ℂ // riemannXi ρ = 0} =>
      (analyticOrderNatAt riemannXi ρ : ℝ) / (‖(ρ : ℂ)‖ * ‖((B : ℂ) + 1 / 2) - (ρ : ℂ)‖) := by
  set c : ℝ := min 1 (2 * B) with hc
  have hc0 : 0 < c := lt_min one_pos (by linarith)
  have hc1 : c ≤ 1 := min_le_left _ _
  have hc2 : c ≤ 2 * B := min_le_right _ _
  refine Summable.of_nonneg_of_le (fun ρ => zeroSumW_term_nonneg B ρ) (fun ρ => ?_)
    ((summable_zero_inv_norm_sq hRH).mul_left (1 / c))
  have hre := riemannXi_zero_re_of_RH hRH ρ.2
  have hρ0 : (ρ : ℂ) ≠ 0 := riemannXi_zero_ne_zero ρ.2
  have hn : 0 < ‖(ρ : ℂ)‖ := norm_pos_iff.2 hρ0
  have e1 := norm_sq_of_re_eq_half hre
  have e2 := norm_sq_shift_sub hre B
  set a := ‖(ρ : ℂ)‖
  set d := ‖((B : ℂ) + 1 / 2) - (ρ : ℂ)‖
  set y := (ρ : ℂ).im
  have hd0 : 0 ≤ d := norm_nonneg _
  have hsq : (c * a) ^ 2 ≤ d ^ 2 := by
    rw [mul_pow, e1, e2]
    have : c ^ 2 ≤ 1 := by nlinarith
    have : c ^ 2 ≤ 4 * B ^ 2 := by nlinarith
    nlinarith [sq_nonneg y]
  have hcd : c * a ≤ d := by nlinarith [mul_pos hc0 hn]
  have hm : (0 : ℝ) ≤ (analyticOrderNatAt riemannXi ρ : ℝ) := Nat.cast_nonneg _
  have hdpos : 0 < d := lt_of_lt_of_le (mul_pos hc0 hn) hcd
  rw [div_le_iff₀ (mul_pos hn hdpos), show 1 / c * ((analyticOrderNatAt riemannXi ρ : ℝ) / a ^ 2) * (a * d)
    = (analyticOrderNatAt riemannXi ρ : ℝ) * (d / (c * a)) by field_simp]
  have : 1 ≤ d / (c * a) := by rw [le_div_iff₀ (by positivity)]; linarith
  nlinarith

theorem zeroSumW_nonneg (B : ℝ) : 0 ≤ zeroSumW B :=
  tsum_nonneg (fun ρ => zeroSumW_term_nonneg B ρ)

end SchoenfeldRH
end File71

-- Upstream module SchoenfeldRH.Explicit.LogDeriv
section File72


open Complex

namespace SchoenfeldRH.Explicit

noncomputable def trivZero (k : ℕ) : ℂ := -(2 * ((k : ℂ) + 1))

lemma trivZero_re (k : ℕ) : (trivZero k).re = -(2 * ((k : ℝ) + 1)) := by
  simp [trivZero]

lemma trivZero_ne_zero (k : ℕ) : trivZero k ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  rw [trivZero_re] at this
  simp at this
  linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]

lemma norm_trivZero (k : ℕ) : ‖trivZero k‖ = 2 * ((k : ℝ) + 1) := by
  have : trivZero k = ((-(2 * ((k : ℝ) + 1)) : ℝ) : ℂ) := by simp [trivZero]
  rw [this, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos (by positivity)]

theorem hasSum_trivZero {s : ℂ} (hs : 0 < s.re) :
    HasSum (fun k : ℕ => 1 / (s - trivZero k) + 1 / trivZero k)
      (-(1 / 2 * digamma (s / 2) + Real.eulerMascheroniConstant / 2 + 1 / s)) := by
  have hw : 1 / 2 < (s / 2 + 1).re := by
    simp
    linarith
  have h := (P4.hasSum_digamma hw).mul_left (-(1 / 2))
  have hs2 : ∀ m : ℕ, s / 2 ≠ -(m : ℂ) := by
    intro m hm
    have := congrArg Complex.re hm
    simp at this
    linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have hs0 : s ≠ 0 := by
    rintro rfl
    simp at hs
  rw [digamma_apply_add_one _ hs2, digamma_one] at h
  convert h using 1
  · funext k
    have hk : (k : ℂ) + 1 ≠ 0 := by
      intro hk
      have := congrArg Complex.re hk
      simp at this
      linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    have hk2 : (k : ℂ) + (s / 2 + 1) ≠ 0 := by
      intro hk
      have := congrArg Complex.re hk
      simp at this
      linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    have hk3 : s - trivZero k ≠ 0 := by
      intro hk
      have := congrArg Complex.re hk
      simp [trivZero] at this
      linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    have hk4 := trivZero_ne_zero k
    have e1 : s - trivZero k = 2 * ((k : ℂ) + (s / 2 + 1)) := by simp [trivZero]; ring
    have e2 : trivZero k = -(2 * ((k : ℂ) + 1)) := rfl
    rw [e1, e2]
    field_simp
    ring
  · field_simp
    ring

theorem neg_logDeriv_zeta_eq {s : ℂ} (hs : 1 < s.re) :
    -(deriv riemannZeta s / riemannZeta s)
      = (1 / (s - 1) + 1) - (Real.log (2 * Real.pi) : ℂ)
        - (∑' ρ : {ρ : ℂ // riemannXi ρ = 0},
            (analyticOrderNatAt riemannXi ρ : ℂ) * (1 / (s - ρ) + 1 / ρ))
        - ∑' k : ℕ, (1 / (s - trivZero k) + 1 / trivZero k) := by
  have hxi : riemannXi s ≠ 0 := by
    intro h
    have := (riemannXi_zero_re_mem h).2
    linarith
  rw [(hasSum_hadamard_riemannXi hxi).tsum_eq, (hasSum_trivZero (by linarith)).tsum_eq,
    logDeriv_riemannZeta_eq hs]
  have hlog4 : ((Real.log (4 * Real.pi) : ℝ) : ℂ) = 2 * (Real.log 2 : ℂ) + (Real.log Real.pi : ℂ) := by
    rw [Real.log_mul (by norm_num) Real.pi_pos.ne', show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast; ring
  have hlog2 : ((Real.log (2 * Real.pi) : ℝ) : ℂ) = (Real.log 2 : ℂ) + (Real.log Real.pi : ℂ) := by
    rw [Real.log_mul (by norm_num) Real.pi_pos.ne']; push_cast; ring
  have hc : (xiConst : ℂ) = 1 + (Real.eulerMascheroniConstant : ℂ) / 2
      - ((Real.log (4 * Real.pi) : ℝ) : ℂ) / 2 := by
    unfold xiConst; push_cast; ring
  rw [hc, hlog4, hlog2]
  ring

end SchoenfeldRH.Explicit
end File72

-- Upstream module SchoenfeldRH.Lemmas.p8.TsumIntegrable
section File73


open MeasureTheory

namespace SchoenfeldRH.Lemmas.p8

theorem integrable_tsum_of_summable_integral_norm {ι : Type*} [Countable ι] {F : ι → ℝ → ℂ}
    (hF : ∀ i, Integrable (F i)) (hs : Summable fun i => ∫ t, ‖F i t‖) :
    Integrable (fun t => ∑' i, F i t) := by
  refine ⟨AEStronglyMeasurable.tsum (fun i => (hF i).1), ?_⟩
  have h1 : ∀ i, ∫⁻ a, ‖F i a‖ₑ = ENNReal.ofReal (∫ a, ‖F i a‖) := by
    intro i
    rw [ofReal_integral_eq_lintegral_ofReal (hF i).norm
      (Filter.Eventually.of_forall fun _ => norm_nonneg _)]
    simp only [ofReal_norm]
  unfold HasFiniteIntegral
  calc ∫⁻ a, ‖∑' i, F i a‖ₑ ≤ ∫⁻ a, ∑' i, ‖F i a‖ₑ :=
        lintegral_mono fun a => enorm_tsum_le_tsum_enorm
    _ = ∑' i, ∫⁻ a, ‖F i a‖ₑ := lintegral_tsum (fun i => (hF i).1.enorm)
    _ = ∑' i, ENNReal.ofReal (∫ a, ‖F i a‖) := tsum_congr h1
    _ = ENNReal.ofReal (∑' i, ∫ a, ‖F i a‖) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun i => integral_nonneg fun _ => norm_nonneg _) hs).symm
    _ < ⊤ := ENNReal.ofReal_lt_top

end SchoenfeldRH.Lemmas.p8
end File73

-- Upstream module SchoenfeldRH.Explicit.Formula
section File74


open Complex MeasureTheory ArithmeticFunction

namespace SchoenfeldRH.Explicit

theorem explicit_formula_mu (x : ℕ) (hx : 1 ≤ x) (μ : ℝ) (hμ : 0 < μ ∨ μ < -1)
    (hne : ∀ k : ℕ, trivZero k + μ ≠ 0) :
    Summable (fun ρ : {ρ : ℂ // riemannXi ρ = 0} =>
        (analyticOrderNatAt riemannXi ρ : ℂ) * pairE x μ ρ) ∧
    Summable (fun k : ℕ => pairE x μ (trivZero k)) ∧
    (((∑ n ∈ Finset.Ioo 0 x, (Λ n : ℝ) * (1 - ((n : ℝ) / x) ^ μ) : ℝ)) : ℂ)
      = pairE x μ 1 - (Real.log (2 * Real.pi) : ℂ) * ((1 - (x : ℝ) ^ (-μ) : ℝ) : ℂ)
        - (∑' ρ : {ρ : ℂ // riemannXi ρ = 0}, (analyticOrderNatAt riemannXi ρ : ℂ) * pairE x μ ρ)
        - ∑' k : ℕ, pairE x μ (trivZero k) := by
  classical
  have : Countable {ρ : ℂ // riemannXi ρ = 0} := countable_riemannXi_zeros
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  obtain ⟨c, hc_def⟩ : ∃ c : ℝ, c = 2 + |μ| := ⟨_, rfl⟩
  have hc : 0 < c := by rw [hc_def]; positivity
  have hc1 : 1 ≤ c - 1 := by rw [hc_def]; linarith [abs_nonneg μ]
  have hcμ : 1 < c + μ := by
    rcases hμ with h | h
    · rw [hc_def, abs_of_pos h]; linarith
    · rw [hc_def, abs_of_neg (by linarith)]; linarith
  have hcμ0 : 0 < c + μ := by linarith
  have hμ1 : (1 : ℂ) + μ ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    rcases hμ with h' | h' <;> linarith
  have hxpos : (0 : ℝ) < x := by exact_mod_cast hx
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast hx
  obtain ⟨K, hK0, hK⟩ := integral_norm_pairK_le (δ := 1) one_pos
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = K * (x : ℝ) ^ c * |μ| * (1 + |μ - 1|) ^ (1 / 2 : ℝ) := ⟨_, rfl⟩
  have hM0 : 0 ≤ M := by rw [hM]; positivity
  have hKw : ∀ w : ℂ, w ≠ 0 → w.re ≤ c - 1 →
      Integrable (pairK x c μ w) ∧ ∫ t : ℝ, ‖pairK x c μ w t‖ ≤ M * ‖w‖ ^ (-(3 / 2 : ℝ)) := by
    intro w hw0 hw
    rw [hM]
    exact hK x c μ hxpos hcμ w hw0 hw
  
  have hρ : ∀ ρ : {ρ : ℂ // riemannXi ρ = 0},
      (ρ : ℂ) ≠ 0 ∧ (ρ : ℂ).re ≤ c - 1 ∧ (ρ : ℂ).re < c ∧ (ρ : ℂ) + μ ≠ 0 := by
    intro ρ
    obtain ⟨h0, h1⟩ := riemannXi_zero_re_mem ρ.2
    refine ⟨riemannXi_zero_ne_zero ρ.2, by linarith, by linarith, ?_⟩
    intro h
    have := congrArg Complex.re h
    simp at this
    rcases hμ with h' | h' <;> linarith
  have hτ : ∀ k : ℕ, trivZero k ≠ 0 ∧ (trivZero k).re ≤ c - 1 ∧ (trivZero k).re < c := by
    intro k
    have hr := trivZero_re k
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    refine ⟨trivZero_ne_zero k, ?_, ?_⟩ <;> rw [hr] <;> linarith
  
  have hF1int : ∀ ρ : {ρ : ℂ // riemannXi ρ = 0},
      Integrable (fun t => (analyticOrderNatAt riemannXi ρ : ℂ) * pairK x c μ ρ t) :=
    fun ρ => ((hKw ρ (hρ ρ).1 (hρ ρ).2.1).1).const_mul _
  have hF1norm : ∀ ρ : {ρ : ℂ // riemannXi ρ = 0},
      ∫ t, ‖(analyticOrderNatAt riemannXi ρ : ℂ) * pairK x c μ ρ t‖
        = (analyticOrderNatAt riemannXi ρ : ℝ) * ∫ t, ‖pairK x c μ ρ t‖ := by
    intro ρ
    simp_rw [norm_mul, Complex.norm_natCast]
    exact integral_const_mul _ _
  have hsumH := summable_riemannXi_zeros_rpow (τ := 1 + 1 / 2) (by norm_num)
  have hF1sum : Summable fun ρ : {ρ : ℂ // riemannXi ρ = 0} =>
      ∫ t, ‖(analyticOrderNatAt riemannXi ρ : ℂ) * pairK x c μ ρ t‖ := by
    refine (hsumH.mul_left M).of_nonneg_of_le
      (fun ρ => integral_nonneg fun t => norm_nonneg _) (fun ρ => ?_)
    rw [hF1norm]
    have h := (hKw ρ (hρ ρ).1 (hρ ρ).2.1).2
    have e : ‖(ρ : ℂ)‖ ^ (-(3 / 2 : ℝ)) = 1 / ‖(ρ : ℂ)‖ ^ (1 + 1 / 2 : ℝ) := by
      rw [Real.rpow_neg (norm_nonneg _), one_div]; norm_num
    rw [e] at h
    calc (analyticOrderNatAt riemannXi ρ : ℝ) * ∫ t, ‖pairK x c μ ρ t‖
        ≤ (analyticOrderNatAt riemannXi ρ : ℝ) * (M * (1 / ‖(ρ : ℂ)‖ ^ (1 + 1 / 2 : ℝ))) :=
          mul_le_mul_of_nonneg_left h (Nat.cast_nonneg _)
      _ = M * ((analyticOrderNatAt riemannXi ρ : ℝ) / ‖(ρ : ℂ)‖ ^ (1 + 1 / 2 : ℝ)) := by ring
  have hS1 := hasSum_integral_of_summable_integral_norm hF1int hF1sum
  have hS1' : HasSum
      (fun ρ : {ρ : ℂ // riemannXi ρ = 0} => (analyticOrderNatAt riemannXi ρ : ℂ) * pairE x μ ρ)
      ((1 / (2 * Real.pi) : ℂ) * ∫ t, ∑' ρ : {ρ : ℂ // riemannXi ρ = 0},
        (analyticOrderNatAt riemannXi ρ : ℂ) * pairK x c μ ρ t) := by
    have := hS1.mul_left (1 / (2 * Real.pi) : ℂ)
    convert this using 1
    funext ρ
    rw [integral_const_mul, integral_pairK x c μ hx1 hc hcμ ρ (hρ ρ).2.2.1 (hρ ρ).1 (hρ ρ).2.2.2]
    field_simp
  have hS1i := SchoenfeldRH.Lemmas.p8.integrable_tsum_of_summable_integral_norm hF1int hF1sum
  
  have hF2int : ∀ k : ℕ, Integrable (fun t => pairK x c μ (trivZero k) t) :=
    fun k => (hKw _ (hτ k).1 (hτ k).2.1).1
  have hsumk : Summable fun k : ℕ => ((k : ℝ) + 1) ^ (-(3 / 2 : ℝ)) := by
    have := (summable_nat_add_iff 1).mpr
      (Real.summable_nat_rpow.mpr (by norm_num : -(3 / 2 : ℝ) < -1))
    simpa [Nat.cast_add, Nat.cast_one] using this
  have hF2sum : Summable fun k : ℕ => ∫ t, ‖pairK x c μ (trivZero k) t‖ := by
    refine (hsumk.mul_left M).of_nonneg_of_le
      (fun k => integral_nonneg fun t => norm_nonneg _) (fun k => ?_)
    refine (hKw _ (hτ k).1 (hτ k).2.1).2.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ hM0
    rw [norm_trivZero]
    have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    exact Real.rpow_le_rpow_of_nonpos hk (by linarith) (by norm_num)
  have hS2 := hasSum_integral_of_summable_integral_norm hF2int hF2sum
  have hS2' : HasSum (fun k : ℕ => pairE x μ (trivZero k))
      ((1 / (2 * Real.pi) : ℂ) * ∫ t, ∑' k : ℕ, pairK x c μ (trivZero k) t) := by
    have := hS2.mul_left (1 / (2 * Real.pi) : ℂ)
    convert this using 1
    funext k
    rw [integral_pairK x c μ hx1 hc hcμ _ (hτ k).2.2 (hτ k).1 (hne k)]
    field_simp
  have hS2i := SchoenfeldRH.Lemmas.p8.integrable_tsum_of_summable_integral_norm hF2int hF2sum
  refine ⟨hS1'.summable, hS2'.summable, ?_⟩
  
  have hpt : ∀ t : ℝ, LSeries (fun n => (Λ n : ℂ)) ((c : ℂ) + t * I) *
        ((x : ℂ) ^ ((c : ℂ) + t * I) * (1 / ((c : ℂ) + t * I) - 1 / ((c : ℂ) + t * I + μ)))
      = pairK x c μ 1 t - (Real.log (2 * Real.pi) : ℂ) * Kmu c μ x t
        - ∑' ρ : {ρ : ℂ // riemannXi ρ = 0}, (analyticOrderNatAt riemannXi ρ : ℂ) * pairK x c μ ρ t
        - ∑' k : ℕ, pairK x c μ (trivZero k) t := by
    intro t
    have hre : 1 < ((c : ℂ) + t * I).re := by simp; linarith
    have hG : (x : ℂ) ^ ((c : ℂ) + t * I) * (1 / ((c : ℂ) + t * I) - 1 / ((c : ℂ) + t * I + μ))
        = Kmu c μ x t := by
      simp only [Kmu, Complex.ofReal_natCast]
    rw [hG, LSeries_vonMangoldt_eq_deriv_riemannZeta_div hre, neg_div, neg_logDeriv_zeta_eq hre]
    rw [sub_mul, sub_mul, sub_mul, ← tsum_mul_right, ← tsum_mul_right]
    have h1 : (1 / ((c : ℂ) + t * I - 1) + 1 / 1) * Kmu c μ x t = pairK x c μ 1 t :=
      pair_mul_kappa hc hcμ0 (by simp; linarith) one_ne_zero t
    rw [div_one] at h1
    have hρK : ∀ ρ : {ρ : ℂ // riemannXi ρ = 0},
        (analyticOrderNatAt riemannXi ρ : ℂ) * (1 / ((c : ℂ) + t * I - ρ) + 1 / ρ) * Kmu c μ x t
          = (analyticOrderNatAt riemannXi ρ : ℂ) * pairK x c μ ρ t := by
      intro ρ
      rw [mul_assoc]
      exact congrArg _ (pair_mul_kappa hc hcμ0 (hρ ρ).2.2.1 (hρ ρ).1 t)
    have hτK : ∀ k : ℕ, (1 / ((c : ℂ) + t * I - trivZero k) + 1 / trivZero k) * Kmu c μ x t
        = pairK x c μ (trivZero k) t := fun k => pair_mul_kappa hc hcμ0 (hτ k).2.2 (hτ k).1 t
    rw [h1]
    simp only [hρK, hτK]
  have hP := perron_weighted_mu (fun n => (Λ n : ℂ)) c μ hc hcμ ?_ x hx
  swap
  · have := (LSeriesSummable_vonMangoldt (s := (c : ℂ)) (by simp; linarith))
    rw [LSeriesSummable, ← summable_norm_iff] at this
    refine this.congr fun n => ?_
    rw [LSeries.norm_term_eq]
    split_ifs with hn
    · subst hn; simp
    · simp
  simp only [hpt] at hP
  have hA : Integrable (pairK x c μ 1) := (hKw 1 one_ne_zero (by simp; linarith)).1
  have hB : Integrable (fun t => (Real.log (2 * Real.pi) : ℂ) * Kmu c μ x t) :=
    (integrable_Kmu hc hcμ hxpos).const_mul _
  have hAB : Integrable (fun t => pairK x c μ 1 t - (Real.log (2 * Real.pi) : ℂ) * Kmu c μ x t) :=
    hA.sub hB
  have hABC : Integrable (fun t => pairK x c μ 1 t - (Real.log (2 * Real.pi) : ℂ) * Kmu c μ x t
      - ∑' ρ : {ρ : ℂ // riemannXi ρ = 0}, (analyticOrderNatAt riemannXi ρ : ℂ) * pairK x c μ ρ t) :=
    hAB.sub hS1i
  rw [integral_sub hABC hS2i, integral_sub hAB hS1i,
    integral_sub hA hB, integral_const_mul, integral_Kmu _ _ _ hxpos hc hcμ,
    integral_pairK x c μ hx1 hc hcμ 1 (by simp; linarith) one_ne_zero hμ1] at hP
  simp only [hx1, ↓reduceIte] at hP
  rw [hS1'.tsum_eq, hS2'.tsum_eq]
  have hL : ((∑ n ∈ Finset.Ioo 0 x, (Λ n : ℝ) * (1 - ((n : ℝ) / x) ^ μ) : ℝ) : ℂ)
      = ∑ n ∈ Finset.Ioo 0 x, (Λ n : ℂ) * ((1 - ((n : ℝ) / x) ^ μ : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    simp only [Complex.ofReal_mul]
  rw [hL, hP]
  field_simp

end SchoenfeldRH.Explicit
end File74

-- Upstream module SchoenfeldRH.Explicit
section File75


open Complex ArithmeticFunction

namespace SchoenfeldRH

open Explicit

namespace Explicit

lemma pairE_ofReal {x : ℝ} (hx : 0 < x) (μ r : ℝ) :
    pairE x μ (r : ℂ) = ((μ * (x ^ r - x ^ (-μ)) / (r * (r + μ)) : ℝ) : ℂ) := by
  unfold pairE
  rw [← ofReal_neg, ← ofReal_cpow hx.le, ← ofReal_cpow hx.le]
  push_cast
  ring

lemma trivZero_eq_ofReal (k : ℕ) : trivZero k = ((-(2 * ((k : ℝ) + 1)) : ℝ) : ℂ) := by
  simp [trivZero]

lemma sum_Ioo_eq_sum_Ioc (x : ℕ) (hx : 1 ≤ x) (μ : ℝ) :
    ∑ n ∈ Finset.Ioo 0 x, (Λ n : ℝ) * (1 - ((n : ℝ) / x) ^ μ)
      = ∑ n ∈ Finset.Ioc 0 x, (Λ n : ℝ) * (1 - ((n : ℝ) / x) ^ μ) := by
  have hx0 : (x : ℝ) ≠ 0 := by exact_mod_cast (show x ≠ 0 by omega)
  rw [← Finset.Ioo_insert_right (show 0 < x by omega), Finset.sum_insert (by simp)]
  simp [div_self hx0]

lemma norm_tsum_zero_le (hRH : RiemannHypothesis) {B : ℝ} (hB : 0 < B) (C : ℝ)
    (f : {ρ : ℂ // riemannXi ρ = 0} → ℂ)
    (hf : ∀ ρ : {ρ : ℂ // riemannXi ρ = 0}, ‖f ρ‖ ≤ C * ((analyticOrderNatAt riemannXi ρ : ℝ) /
      (‖(ρ : ℂ)‖ * ‖((B : ℂ) + 1 / 2) - (ρ : ℂ)‖))) :
    ‖∑' ρ, f ρ‖ ≤ C * zeroSumW B := by
  have hsW := (summable_zeroSumW hRH B hB).mul_left C
  have hsn : Summable (fun ρ => ‖f ρ‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hf hsW
  calc ‖∑' ρ, f ρ‖ ≤ ∑' ρ, ‖f ρ‖ := norm_tsum_le_tsum_norm hsn
    _ ≤ ∑' ρ : {ρ : ℂ // riemannXi ρ = 0}, C * ((analyticOrderNatAt riemannXi ρ : ℝ) /
          (‖(ρ : ℂ)‖ * ‖((B : ℂ) + 1 / 2) - (ρ : ℂ)‖)) := hsn.tsum_le_tsum hf hsW
    _ = C * zeroSumW B := by rw [tsum_mul_left]; rfl

lemma log_two_pi_nonneg : 0 ≤ Real.log (2 * Real.pi) :=
  Real.log_nonneg (by linarith [Real.pi_gt_three])

lemma log_two_pi_le_two : Real.log (2 * Real.pi) ≤ 2 := by
  rw [Real.log_le_iff_le_exp (by positivity)]
  have h1 := Real.exp_one_gt_d9
  have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  have h3 := Real.pi_lt_d2
  rw [h2]
  nlinarith

end Explicit

theorem sub_psi_le_of_RH (hRH : RiemannHypothesis) (x : ℕ) (hx : 2 ≤ x) (lam : ℝ) (hlam : 2 < lam)
    (hne : ∀ k : ℕ, lam ≠ 2 * k) :
    x - Chebyshev.psi x ≤ x / (lam + 1) + (Real.sqrt x + 1) * (lam * zeroSumW (lam + 1 / 2)) + 3 := by
  have hX : (1 : ℝ) ≤ x := by exact_mod_cast (show 1 ≤ x by omega)
  have hX0 : (0 : ℝ) < x := by linarith
  have hl0 : 0 ≤ lam := by linarith
  have hne' : ∀ k : ℕ, trivZero k + (lam : ℂ) ≠ 0 := by
    intro k h
    apply hne (k + 1)
    have := congrArg re h
    rw [add_re, trivZero_re, ofReal_re, zero_re] at this
    push_cast
    linarith
  obtain ⟨hZs, hTs, hE⟩ := explicit_formula_mu x (by omega) lam (Or.inl (by linarith)) hne'
  set S : ℝ := ∑ n ∈ Finset.Ioo 0 x, (Λ n : ℝ) * (1 - ((n : ℝ) / x) ^ lam) with hS
  set Z : ℂ := ∑' ρ : {ρ : ℂ // riemannXi ρ = 0}, (analyticOrderNatAt riemannXi ρ : ℂ) * pairE x lam ρ
    with hZdef
  set T : ℂ := ∑' k : ℕ, pairE x lam (trivZero k) with hTdef
   
  have h1 : pairE x lam 1 = ((lam * ((x : ℝ) - (x : ℝ) ^ (-lam)) / (1 + lam) : ℝ) : ℂ) := by
    have := pairE_ofReal hX0 lam 1
    rw [ofReal_one] at this
    rw [this, Real.rpow_one, one_mul]
  have hre : S = lam * ((x : ℝ) - (x : ℝ) ^ (-lam)) / (1 + lam)
      - Real.log (2 * Real.pi) * (1 - (x : ℝ) ^ (-lam)) - Z.re - T.re := by
    rw [h1, ← ofReal_mul, ← ofReal_sub] at hE
    have := congrArg re hE
    simpa only [sub_re, ofReal_re] using this
   
  have hT : T.re ≤ 0 := by
    rw [hTdef, Complex.re_tsum hTs]
    refine tsum_nonpos fun k => ?_
    rw [trivZero_eq_ofReal, pairE_ofReal hX0, ofReal_re]
    set r : ℝ := -(2 * ((k : ℝ) + 1)) with hr_def
    have hr : r < 0 := by rw [hr_def]; have : (0 : ℝ) ≤ k := k.cast_nonneg; linarith
    have hrl : r + lam ≠ 0 := by
      intro h
      apply hne (k + 1)
      push_cast
      rw [hr_def] at h
      linarith
    have hq : 0 ≤ ((x : ℝ) ^ r - (x : ℝ) ^ (-lam)) / (r + lam) := by
      rcases lt_or_gt_of_ne hrl with h | h
      · exact div_nonneg_of_nonpos
          (sub_nonpos.2 (Real.rpow_le_rpow_of_exponent_le hX (by linarith))) h.le
      · exact div_nonneg (sub_nonneg.2 (Real.rpow_le_rpow_of_exponent_le hX (by linarith))) h.le
    have e : lam * ((x : ℝ) ^ r - (x : ℝ) ^ (-lam)) / (r * (r + lam))
        = (lam / r) * (((x : ℝ) ^ r - (x : ℝ) ^ (-lam)) / (r + lam)) := by
      field_simp
    rw [e]
    exact mul_nonpos_of_nonpos_of_nonneg (div_nonpos_of_nonneg_of_nonpos hl0 hr.le) hq
   
  have hZ : ‖Z‖ ≤ lam * (Real.sqrt x + 1) * zeroSumW (lam + 1 / 2) := by
    refine norm_tsum_zero_le hRH (by linarith) _ _ fun ρ => ?_
    have hρ := riemannXi_zero_re_of_RH hRH ρ.2
    have hnum : ‖((x : ℝ) : ℂ) ^ (ρ : ℂ) - ((x : ℝ) : ℂ) ^ (-(lam : ℂ))‖ ≤ Real.sqrt x + 1 := by
      refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_cpow_eq_rpow_re_of_pos hX0, hρ, Real.sqrt_eq_rpow]
      · rw [norm_cpow_eq_rpow_re_of_pos hX0, neg_re, ofReal_re]
        exact Real.rpow_le_one_of_one_le_of_nonpos hX (by linarith)
    have hden : ‖(ρ : ℂ) + lam‖ = ‖(((lam + 1 / 2 : ℝ) : ℂ) + 1 / 2) - (ρ : ℂ)‖ := by
      rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), Complex.sq_norm, Complex.sq_norm,
        normSq_apply, normSq_apply]
      simp [hρ]
      ring
    unfold pairE
    rw [norm_mul, Complex.norm_natCast, norm_div, norm_mul, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hl0, hden]
    calc _ ≤ (analyticOrderNatAt riemannXi ρ : ℝ) * (lam * (Real.sqrt x + 1) /
          (‖(ρ : ℂ)‖ * ‖(((lam + 1 / 2 : ℝ) : ℂ) + 1 / 2) - (ρ : ℂ)‖)) := by gcongr
      _ = _ := by ring
   
  have hψ : S ≤ Chebyshev.psi x := by
    rw [hS, sum_Ioo_eq_sum_Ioc x (by omega), Chebyshev.psi, Nat.floor_natCast]
    refine Finset.sum_le_sum fun n _ => ?_
    have h1 : 0 ≤ ((n : ℝ) / x) ^ lam := by positivity
    have h2 : 0 ≤ (Λ n : ℝ) := vonMangoldt_nonneg
    nlinarith
  have hxl0 : 0 ≤ (x : ℝ) ^ (-lam) := by positivity
  have hxl1 : (x : ℝ) ^ (-lam) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hX (by linarith)
  have hlog0 := log_two_pi_nonneg
  have hlog2 := log_two_pi_le_two
  have hZre : Z.re ≤ ‖Z‖ := re_le_norm Z
  have e1 : (x : ℝ) - lam * ((x : ℝ) - (x : ℝ) ^ (-lam)) / (1 + lam)
      = x / (lam + 1) + lam / (1 + lam) * (x : ℝ) ^ (-lam) := by
    field_simp
    ring
  have e2 : lam / (1 + lam) * (x : ℝ) ^ (-lam) ≤ 1 := by
    have : lam / (1 + lam) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    have h0 : 0 ≤ lam / (1 + lam) := by positivity
    nlinarith
  have e3 : Real.log (2 * Real.pi) * (1 - (x : ℝ) ^ (-lam)) ≤ 2 := by nlinarith
  have e4 : (Real.sqrt x + 1) * (lam * zeroSumW (lam + 1 / 2))
      = lam * (Real.sqrt x + 1) * zeroSumW (lam + 1 / 2) := by ring
  linarith

theorem psi_sub_le_of_RH (hRH : RiemannHypothesis) (x : ℕ) (hx : 2 ≤ x) (lam : ℝ) (hlam : 2 < lam) :
    Chebyshev.psi x - x ≤ x / (lam - 1) + Real.sqrt x * (lam * zeroSumW (lam - 1 / 2)) + 3 := by
  have hX2 : (2 : ℝ) ≤ x := by exact_mod_cast hx
  have hX : (1 : ℝ) ≤ x := by linarith
  have hX0 : (0 : ℝ) < x := by linarith
  have hl0 : 0 ≤ lam := by linarith
  have hne' : ∀ k : ℕ, trivZero k + ((-lam : ℝ) : ℂ) ≠ 0 := by
    intro k h
    have := congrArg re h
    rw [add_re, trivZero_re, ofReal_re, zero_re] at this
    have hk : (0 : ℝ) ≤ k := k.cast_nonneg
    linarith
  obtain ⟨hZs, hTs, hE⟩ := explicit_formula_mu x (by omega) (-lam) (Or.inr (by linarith)) hne'
  set S : ℝ := ∑ n ∈ Finset.Ioo 0 x, (Λ n : ℝ) * (1 - ((n : ℝ) / x) ^ (-lam)) with hS
   
  have hs : 1 < ((lam : ℝ) : ℂ).re := by rw [ofReal_re]; linarith
  have hξ : riemannXi (lam : ℂ) ≠ 0 := fun h => by linarith [(riemannXi_zero_re_mem h).2]
  have hPZ := (hasSum_hadamard_riemannXi hξ).summable.hasSum
  have hPT := (hasSum_trivZero (s := (lam : ℂ)) (by rw [ofReal_re]; linarith)).summable.hasSum
  have hL := neg_logDeriv_zeta_eq hs
  set a : ℕ → ℂ := fun n => ((Λ n : ℝ) : ℂ) with ha
  have hLS : LSeries a lam = -(deriv riemannZeta lam / riemannZeta lam) := by
    have h1 := LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs
    change LSeries a lam = _ at h1
    rw [h1, neg_div]
  set XL : ℂ := (((x : ℝ) ^ lam : ℝ) : ℂ) with hXL
  set Q : ℂ → ℂ := fun w => lam * ((x : ℝ) : ℂ) ^ w / (w * (lam - w)) with hQdef
  have hQ : ∀ w : ℂ, w ≠ 0 → (lam : ℂ) - w ≠ 0 →
      pairE x (-lam) w + XL * (1 / (lam - w) + 1 / w) = Q w := by
    intro w hw0 hwl
    have e : ((x : ℝ) : ℂ) ^ (-(((-lam : ℝ)) : ℂ)) = XL := by
      rw [hXL, ofReal_cpow hX0.le, ofReal_neg, neg_neg]
    have hwl' : w + -(lam : ℂ) ≠ 0 := fun h => hwl (by linear_combination -h)
    have hwl'' : w - (lam : ℂ) ≠ 0 := fun h => hwl (by linear_combination -h)
    unfold pairE
    rw [e]
    simp only [hQdef, ofReal_neg]
    field_simp
    ring
  set Z : ℂ := ∑' ρ : {ρ : ℂ // riemannXi ρ = 0},
    (analyticOrderNatAt riemannXi ρ : ℂ) * pairE x (-lam) ρ with hZdef
  set T : ℂ := ∑' k : ℕ, pairE x (-lam) (trivZero k) with hTdef
  have hρre : ∀ ρ : {ρ : ℂ // riemannXi ρ = 0}, (lam : ℂ) - (ρ : ℂ) ≠ 0 := fun ρ h => by
    have := congrArg re h
    rw [sub_re, ofReal_re, zero_re] at this
    linarith [(riemannXi_zero_re_mem ρ.2).2]
  have hkre : ∀ k : ℕ, (lam : ℂ) - trivZero k ≠ 0 := fun k h => by
    have := congrArg re h
    rw [sub_re, ofReal_re, zero_re, trivZero_re] at this
    have hk : (0 : ℝ) ≤ k := k.cast_nonneg
    linarith
  have hZQ : HasSum (fun ρ : {ρ : ℂ // riemannXi ρ = 0} => (analyticOrderNatAt riemannXi ρ : ℂ) * Q ρ)
      (Z + XL * ∑' ρ : {ρ : ℂ // riemannXi ρ = 0},
        (analyticOrderNatAt riemannXi ρ : ℂ) * (1 / ((lam : ℂ) - ρ) + 1 / ρ)) := by
    have := hZs.hasSum.add (hPZ.mul_left XL)
    have key : (fun ρ : {ρ : ℂ // riemannXi ρ = 0} => (analyticOrderNatAt riemannXi ρ : ℂ) * Q ρ)
        = fun ρ : {ρ : ℂ // riemannXi ρ = 0} => (analyticOrderNatAt riemannXi ρ : ℂ) * pairE x (-lam) ρ
          + XL * ((analyticOrderNatAt riemannXi ρ : ℂ) * (1 / ((lam : ℂ) - ρ) + 1 / ρ)) :=
      funext fun ρ => by rw [← hQ ρ (riemannXi_zero_ne_zero ρ.2) (hρre ρ)]; ring
    rw [key]
    exact this
  have hTQ : HasSum (fun k : ℕ => Q (trivZero k))
      (T + XL * ∑' k : ℕ, (1 / ((lam : ℂ) - trivZero k) + 1 / trivZero k)) := by
    have := hTs.hasSum.add (hPT.mul_left XL)
    have key : (fun k : ℕ => Q (trivZero k))
        = fun k => pairE x (-lam) (trivZero k)
          + XL * (1 / ((lam : ℂ) - trivZero k) + 1 / trivZero k) :=
      funext fun k => (hQ _ (trivZero_ne_zero k) (hkre k)).symm
    rw [key]
    exact this
  have h1l : (lam : ℂ) - 1 ≠ 0 := fun h => by
    have := congrArg re h
    rw [sub_re, ofReal_re, zero_re, one_re] at this
    linarith
  have hmain : (S : ℂ) + XL * LSeries a lam
      = Q 1 - (Real.log (2 * Real.pi) : ℂ)
        - (∑' ρ : {ρ : ℂ // riemannXi ρ = 0}, (analyticOrderNatAt riemannXi ρ : ℂ) * Q ρ)
        - ∑' k : ℕ, Q (trivZero k) := by
    have e1 : ((1 - (x : ℝ) ^ (-(-lam)) : ℝ) : ℂ) = 1 - XL := by
      rw [hXL, neg_neg]; push_cast; ring
    rw [hZQ.tsum_eq, hTQ.tsum_eq, ← hQ 1 one_ne_zero h1l, hE, e1, hLS, hL]
    ring
   
  set ZQ : ℂ := ∑' ρ : {ρ : ℂ // riemannXi ρ = 0}, (analyticOrderNatAt riemannXi ρ : ℂ) * Q ρ with hZQdef
  set TQ : ℂ := ∑' k : ℕ, Q (trivZero k) with hTQdef
  set Lre : ℝ := (LSeries a lam).re with hLre
  have hQ1 : Q 1 = ((lam * x / (lam - 1) : ℝ) : ℂ) := by
    simp only [hQdef, cpow_one]
    push_cast
    ring
  have hre : S + (x : ℝ) ^ lam * Lre
      = lam * x / (lam - 1) - Real.log (2 * Real.pi) - ZQ.re - TQ.re := by
    have hXLre : (XL * LSeries a lam).re = (x : ℝ) ^ lam * Lre := by rw [hXL, re_ofReal_mul]
    have := congrArg re hmain
    rw [hQ1, ← ofReal_sub] at this
    simp only [add_re, sub_re, ofReal_re, hXLre] at this
    exact this
   
  have hterm : ∀ n : ℕ, (LSeries.term a lam n).re
      = if n = 0 then 0 else (Λ n : ℝ) / (n : ℝ) ^ lam := by
    intro n
    rw [LSeries.term_def]
    split_ifs with hn
    · simp
    · have : (n : ℂ) ^ (lam : ℂ) = (((n : ℝ) ^ lam : ℝ) : ℂ) := by
        rw [ofReal_cpow (Nat.cast_nonneg n), ofReal_natCast]
      rw [this, ← ofReal_div, ofReal_re]
  have hsumL : HasSum (fun n : ℕ => (LSeries.term a lam n).re) Lre := by
    have hsm : Summable (LSeries.term a lam) := LSeriesSummable_vonMangoldt hs
    have := Complex.reCLM.hasSum hsm.hasSum
    simp only [Complex.reCLM_apply] at this
    exact this
  have hterm0 : ∀ n : ℕ, 0 ≤ (LSeries.term a lam n).re := by
    intro n
    rw [hterm]
    split_ifs
    · exact le_rfl
    · exact div_nonneg vonMangoldt_nonneg (by positivity)
  have hpart : ∑ n ∈ Finset.Ioc 0 x, (LSeries.term a lam n).re ≤ Lre :=
    sum_le_hasSum _ (fun n _ => hterm0 n) hsumL
  have hxl : (0 : ℝ) < (x : ℝ) ^ lam := by positivity
  have hψ : Chebyshev.psi x ≤ S + (x : ℝ) ^ lam * Lre := by
    have e : Chebyshev.psi x = S + (x : ℝ) ^ lam * ∑ n ∈ Finset.Ioc 0 x, (LSeries.term a lam n).re := by
      rw [hS, sum_Ioo_eq_sum_Ioc x (by omega), Chebyshev.psi, Nat.floor_natCast, Finset.mul_sum,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun n hn => ?_
      rw [Finset.mem_Ioc] at hn
      have hn0 : n ≠ 0 := by omega
      have hnpos : (0 : ℝ) < n := Nat.cast_pos.2 (by omega)
      have hnl : (0 : ℝ) < (n : ℝ) ^ lam := by positivity
      rw [hterm]
      simp only [hn0, ↓reduceIte]
      rw [Real.rpow_neg (by positivity), Real.div_rpow hnpos.le hX0.le]
      field_simp
      ring
    rw [e]
    gcongr
   
  have hZ : ‖ZQ‖ ≤ lam * Real.sqrt x * zeroSumW (lam - 1 / 2) := by
    refine norm_tsum_zero_le hRH (by linarith) _ _ fun ρ => ?_
    have hρ := riemannXi_zero_re_of_RH hRH ρ.2
    have hnum : ‖((x : ℝ) : ℂ) ^ (ρ : ℂ)‖ = Real.sqrt x := by
      rw [norm_cpow_eq_rpow_re_of_pos hX0, hρ, Real.sqrt_eq_rpow]
    have hden : (lam : ℂ) - (ρ : ℂ) = (((lam - 1 / 2 : ℝ) : ℂ) + 1 / 2) - (ρ : ℂ) := by
      push_cast; ring
    simp only [hQdef]
    rw [norm_mul, Complex.norm_natCast, norm_div, norm_mul, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hl0, hnum, hden]
    apply le_of_eq
    ring
   
  have hT : -(1 / 3 : ℝ) ≤ TQ.re := by
    have hg : HasSum (fun k : ℕ => -(1 / 4 : ℝ) * (1 / 4 : ℝ) ^ k) (-(1 / 4 : ℝ) * (1 - 1 / 4)⁻¹) :=
      (hasSum_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
    have hq : HasSum (fun k : ℕ => (Q (trivZero k)).re) TQ.re := by
      have := Complex.reCLM.hasSum hTQ.summable.hasSum
      simpa only [Complex.reCLM_apply] using this
    have hQreal : ∀ r : ℝ, Q (r : ℂ) = ((lam * (x : ℝ) ^ r / (r * (lam - r)) : ℝ) : ℂ) := by
      intro r
      simp only [hQdef]
      rw [← ofReal_cpow hX0.le]
      push_cast
      ring
    have hle : ∀ k : ℕ, -(1 / 4 : ℝ) * (1 / 4 : ℝ) ^ k ≤ (Q (trivZero k)).re := by
      intro k
      rw [trivZero_eq_ofReal, hQreal, ofReal_re]
      set r : ℝ := -(2 * ((k : ℝ) + 1)) with hr_def
      have hk : (0 : ℝ) ≤ k := k.cast_nonneg
      have hr : r ≤ -2 := by rw [hr_def]; linarith
      have h2r : (2 : ℝ) ^ r = 1 / 4 * (1 / 4 : ℝ) ^ k := by
        have e : r = -(((2 * (k + 1) : ℕ)) : ℝ) := by rw [hr_def]; push_cast; ring
        rw [e, Real.rpow_neg (by norm_num), Real.rpow_natCast, pow_mul, ← pow_succ' (1 / 4 : ℝ) k,
          ← inv_pow]
        norm_num
      have hxr : (x : ℝ) ^ r ≤ 1 / 4 * (1 / 4 : ℝ) ^ k := by
        rw [← h2r]
        exact Real.rpow_le_rpow_of_nonpos (by norm_num) hX2 (by linarith)
      have hxr0 : 0 ≤ (x : ℝ) ^ r := by positivity
      have e : lam * (x : ℝ) ^ r / (r * (lam - r))
          = -((lam / (lam - r)) * (1 / (-r)) * (x : ℝ) ^ r) := by
        have h1 : r ≠ 0 := by linarith
        have h2 : lam - r ≠ 0 := by linarith
        field_simp
      rw [e, neg_mul, neg_le_neg_iff]
      have hA : lam / (lam - r) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
      have hA0 : 0 ≤ lam / (lam - r) := div_nonneg hl0 (by linarith)
      have hB : 1 / (-r) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
      have hB0 : 0 ≤ 1 / (-r) := div_nonneg zero_le_one (by linarith)
      calc lam / (lam - r) * (1 / (-r)) * (x : ℝ) ^ r ≤ 1 * 1 * (1 / 4 * (1 / 4 : ℝ) ^ k) := by
            gcongr
        _ = _ := by ring
    have := hasSum_le hle hg hq
    norm_num at this
    linarith
   
  have hlog0 := log_two_pi_nonneg
  have hZre : -ZQ.re ≤ ‖ZQ‖ := by
    have := abs_re_le_norm ZQ
    linarith [neg_abs_le ZQ.re]
  have e1 : lam * (x : ℝ) / (lam - 1) - x = x / (lam - 1) := by
    have : lam - 1 ≠ 0 := by linarith
    field_simp
    ring
  have e4 : Real.sqrt x * (lam * zeroSumW (lam - 1 / 2))
      = lam * Real.sqrt x * zeroSumW (lam - 1 / 2) := by ring
  linarith

end SchoenfeldRH
end File75

-- Upstream module SchoenfeldRH.ZeroSum.RealAxis
section File76


namespace SchoenfeldRH

open Complex

private lemma p9_re_LSeries_vonMangoldt_nonneg (x : ℝ) :
    0 ≤ (LSeries (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) (x : ℂ)).re := by
  open scoped ComplexOrder in
  have h : 0 ≤ LSeries (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) (x : ℂ) := by
    unfold LSeries
    refine tsum_nonneg fun n => LSeries.term_nonneg ?_ x
    exact Complex.zero_le_real.mpr ArithmeticFunction.vonMangoldt_nonneg
  exact (Complex.nonneg_iff.mp h).1

private lemma p9_rat_ineq {β : ℝ} (hβ : 5 / 2 ≤ β) :
    1 / (β + 1 / 2) + 1 / (β - 1 / 2) + 1 / (4 * β) ≤ 7 / 3 / β := by
  have hb : 0 < β := by linarith
  have h1 : 0 < β - 1 / 2 := by linarith
  have h2 : 0 < β + 1 / 2 := by linarith
  have h3 : (2 : ℝ) * β - 1 ≠ 0 := (by linarith : (0 : ℝ) < 2 * β - 1).ne'
  have h4 : (-1 : ℝ) + β * 2 ≠ 0 := (by linarith : (0 : ℝ) < -1 + β * 2).ne'
  have h5 : (2 : ℝ) * β + 1 ≠ 0 := (by linarith : (0 : ℝ) < 2 * β + 1).ne'
  have heq : 7 / 3 / β - (1 / (β + 1 / 2) + 1 / (β - 1 / 2) + 1 / (4 * β)) =
      (β ^ 2 - 25 / 4) / (12 * β * ((β + 1 / 2) * (β - 1 / 2))) := by
    have n1 := h1.ne'
    have n2 := h2.ne'
    have n12 : (β + 1 / 2) * (β - 1 / 2) ≠ 0 := mul_ne_zero n2 n1
    have n4 : (4 : ℝ) * β ≠ 0 := by positivity
    have n3 : (3 : ℝ) * β ≠ 0 := by positivity
    have nd : (β + 1 / 2) * (β - 1 / 2) * (4 * β) ≠ 0 := mul_ne_zero n12 n4
    have nr : 12 * β * ((β + 1 / 2) * (β - 1 / 2)) ≠ 0 := mul_ne_zero (by positivity) n12
    rw [div_add_div _ _ n2 n1, div_add_div _ _ n12 n4, div_div, div_sub_div _ _ n3 nd,
      div_eq_div_iff (mul_ne_zero n3 nd) nr]
    ring
  have hnum : 0 ≤ β ^ 2 - 25 / 4 := by nlinarith
  have : 0 ≤ (β ^ 2 - 25 / 4) / (12 * β * ((β + 1 / 2) * (β - 1 / 2))) := by positivity
  linarith

theorem re_logDeriv_riemannXi_le {β : ℝ} (hβ : 5 / 2 ≤ β) :
    (deriv riemannXi ((β + 1 / 2 : ℝ) : ℂ) / riemannXi ((β + 1 / 2 : ℝ) : ℂ)).re
      ≤ Real.log (β / (2 * Real.pi)) / 2 + 7 / 3 / β := by
  set s : ℂ := ((β + 1 / 2 : ℝ) : ℂ) with hs_def
  have hs : 1 < s.re := by rw [hs_def, Complex.ofReal_re]; linarith
  have key := logDeriv_riemannZeta_eq hs
  have hL := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs
  set L := LSeries (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) s with hL_def
  have hLnn : 0 ≤ L.re := p9_re_LSeries_vonMangoldt_nonneg (β + 1 / 2)
  have hxpos : 0 < (β + 1 / 2) / 2 := by linarith
  have hhalf : s / 2 = (((β + 1 / 2) / 2 : ℝ) : ℂ) := by rw [hs_def]; push_cast; ring
  set d : ℝ := deriv Real.Gamma ((β + 1 / 2) / 2) / Real.Gamma ((β + 1 / 2) / 2) with hd_def
  have hψ : Complex.digamma (s / 2) = (d : ℂ) := by
    rw [hhalf]; exact P4.digamma_ofReal_eq hxpos
  have hξ : deriv riemannXi s / riemannXi s = -L +
      ((1 / (β + 1 / 2) + 1 / (β - 1 / 2) - 1 / 2 * Real.log Real.pi
        + 1 / 2 * d : ℝ) : ℂ) := by
    have e : deriv riemannXi s / riemannXi s = -L + 1 / s + 1 / (s - 1) +
        (-(1 / 2) * (Real.log Real.pi : ℂ) + 1 / 2 * Complex.digamma (s / 2)) := by
      linear_combination (-1 : ℂ) * key + hL
    rw [e, hψ, hs_def]
    push_cast
    ring_nf
  rw [hξ, Complex.add_re, Complex.neg_re, Complex.ofReal_re]
  have hψle : d ≤ Real.log ((β + 1 / 2) / 2) := (P4.bounds (x := (β + 1 / 2) / 2) (by linarith)).2
  have hb : 0 < β := by linarith
  have hpi := Real.pi_pos
  have hlog1 : Real.log ((β + 1 / 2) / 2) = Real.log (β + 1 / 2) - Real.log 2 :=
    Real.log_div (by linarith) (by norm_num)
  have hlog2 : Real.log (β / (2 * Real.pi)) = Real.log β - (Real.log 2 + Real.log Real.pi) := by
    rw [Real.log_div hb.ne' (by positivity), Real.log_mul (by norm_num) hpi.ne']
  have hlog3 : Real.log ((β + 1 / 2) / β) = Real.log (β + 1 / 2) - Real.log β :=
    Real.log_div (by linarith) hb.ne'
  have hlog4 : Real.log ((β + 1 / 2) / β) ≤ (β + 1 / 2) / β - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have hfrac : (β + 1 / 2) / β - 1 = 1 / (2 * β) := by field_simp; ring
  have hrat := p9_rat_ineq hβ
  have h4 : 1 / (2 * β) / 2 = 1 / (4 * β) := by field_simp; ring
  nlinarith [hψle, hlog1, hlog2, hlog3, hlog4, hfrac, hrat, h4]

end SchoenfeldRH
end File76

-- Upstream module SchoenfeldRH.ZeroSum.Bound
section File77


namespace SchoenfeldRH

open Complex

theorem sum_poisson_le (hRH : RiemannHypothesis) {u : ℝ} (hu : 5 / 2 ≤ u)
    (S : Finset {ρ : ℂ // riemannXi ρ = 0}) :
    ∑ ρ ∈ S, (analyticOrderNatAt riemannXi (ρ : ℂ) : ℝ) * (u / (u ^ 2 + (ρ : ℂ).im ^ 2))
      ≤ Real.log (u / (2 * Real.pi)) / 2 + 7 / 3 / u := by
  have hu0 : 0 < u := by linarith
  refine (sum_le_hasSum S (fun ρ _ => ?_) (hasSum_poisson hRH hu0)).trans (re_logDeriv_riemannXi_le hu)
  exact mul_nonneg (Nat.cast_nonneg _) (div_nonneg hu0.le (by positivity))

noncomputable def gAux (P Q t : ℝ) : ℝ := -Real.arctan (P * (1 - t ^ 2) / (2 * Q * t)) / (P * Q)

theorem gAux_one (P Q : ℝ) : gAux P Q 1 = 0 := by simp [gAux]

theorem hasDerivAt_gAux {P Q t : ℝ} (hP : 0 < P) (hQ : 0 < Q) (ht : 0 < t) :
    HasDerivAt (gAux P Q) (2 * (1 + t ^ 2) / (P ^ 2 * (1 - t ^ 2) ^ 2 + 4 * Q ^ 2 * t ^ 2)) t := by
  have hn : HasDerivAt (fun t : ℝ => P * (1 - t ^ 2)) (P * (-(2 * t))) t := by
    have := ((hasDerivAt_pow 2 t).const_sub 1).const_mul P
    simpa using this
  have hd : HasDerivAt (fun t : ℝ => 2 * Q * t) (2 * Q) t := by
    simpa using (hasDerivAt_id t).const_mul (2 * Q)
  have h1 : HasDerivAt (fun t : ℝ => P * (1 - t ^ 2) / (2 * Q * t))
      ((P * (-(2 * t)) * (2 * Q * t) - P * (1 - t ^ 2) * (2 * Q)) / (2 * Q * t) ^ 2) t :=
    hn.fun_div hd (by positivity)
  have h2 : HasDerivAt (fun t : ℝ => -Real.arctan (P * (1 - t ^ 2) / (2 * Q * t)) / (P * Q))
      (-(1 / (1 + (P * (1 - t ^ 2) / (2 * Q * t)) ^ 2) *
        ((P * (-(2 * t)) * (2 * Q * t) - P * (1 - t ^ 2) * (2 * Q)) / (2 * Q * t) ^ 2)) / (P * Q)) t :=
    (h1.arctan.neg).div_const (P * Q)
  have hden : 0 < P ^ 2 * (1 - t ^ 2) ^ 2 + 4 * Q ^ 2 * t ^ 2 := by positivity
  have hden' : 0 < (2 * Q * t) ^ 2 + (P * (1 - t ^ 2)) ^ 2 := by positivity
  have e : 2 * (1 + t ^ 2) / (P ^ 2 * (1 - t ^ 2) ^ 2 + 4 * Q ^ 2 * t ^ 2)
      = -(1 / (1 + (P * (1 - t ^ 2) / (2 * Q * t)) ^ 2) *
        ((P * (-(2 * t)) * (2 * Q * t) - P * (1 - t ^ 2) * (2 * Q)) / (2 * Q * t) ^ 2)) / (P * Q) := by
    field_simp
    ring
  rw [e]
  exact h2

noncomputable def psiAux (B C t : ℝ) : ℝ :=
  Real.log (B * t / Real.pi) ^ 2 / (4 * B) + C / (2 * B ^ 2) * (t - t⁻¹)

theorem hasDerivAt_psiAux {B C t : ℝ} (hB : 0 < B) (ht : 0 < t) :
    HasDerivAt (psiAux B C)
      (Real.log (B * t / Real.pi) / (2 * B * t) + C / (2 * B ^ 2) * (1 + 1 / t ^ 2)) t := by
  have hpi := Real.pi_pos
  have h0 : HasDerivAt (fun t : ℝ => B * t / Real.pi) (B / Real.pi) t := by
    simpa using ((hasDerivAt_id t).const_mul B).div_const Real.pi
  have h1 : HasDerivAt (fun t : ℝ => Real.log (B * t / Real.pi) ^ 2)
      (((2 : ℕ) : ℝ) * Real.log (B * t / Real.pi) ^ (2 - 1) * (B / Real.pi / (B * t / Real.pi))) t :=
    (h0.log (by positivity)).fun_pow 2
  have h3 : HasDerivAt (fun t : ℝ => t - t⁻¹) (1 - -(t ^ 2)⁻¹) t :=
    (hasDerivAt_id t).fun_sub (hasDerivAt_inv ht.ne')
  have h4 : HasDerivAt (fun t : ℝ => Real.log (B * t / Real.pi) ^ 2 / (4 * B)
        + C / (2 * B ^ 2) * (t - t⁻¹))
      (((2 : ℕ) : ℝ) * Real.log (B * t / Real.pi) ^ (2 - 1) * (B / Real.pi / (B * t / Real.pi)) / (4 * B)
        + C / (2 * B ^ 2) * (1 - -(t ^ 2)⁻¹)) t :=
    (h1.div_const (4 * B)).fun_add (h3.const_mul (C / (2 * B ^ 2)))
  have e : Real.log (B * t / Real.pi) / (2 * B * t) + C / (2 * B ^ 2) * (1 + 1 / t ^ 2)
      = ((2 : ℕ) : ℝ) * Real.log (B * t / Real.pi) ^ (2 - 1) * (B / Real.pi / (B * t / Real.pi)) / (4 * B)
        + C / (2 * B ^ 2) * (1 - -(t ^ 2)⁻¹) := by
    norm_num
    field_simp
    ring
  rw [e]
  exact h4

theorem sum_deriv_le (hRH : RiemannHypothesis) {B : ℝ} (hB : 50 ≤ B)
    (S : Finset {ρ : ℂ // riemannXi ρ = 0}) {t : ℝ} (ht1 : 3 / B ≤ t) (ht2 : t ≤ 1) :
    ∑ ρ ∈ S, (analyticOrderNatAt riemannXi (ρ : ℂ) : ℝ) *
        (2 * (1 + t ^ 2) / (‖(ρ : ℂ)‖ ^ 2 * (1 - t ^ 2) ^ 2
          + 4 * ‖((B : ℂ) + 1 / 2) - (ρ : ℂ)‖ ^ 2 * t ^ 2))
      ≤ Real.log (B * t / Real.pi) / (2 * B * t) + 7 / 3 / (2 * B ^ 2) * (1 + 1 / t ^ 2) := by
  have hB0 : 0 < B := by linarith
  have hpi := Real.pi_pos
  have ht0 : 0 < t := lt_of_lt_of_le (by positivity) ht1
  have hBt : 3 ≤ B * t := by
    have := mul_le_mul_of_nonneg_left ht1 hB0.le
    rwa [mul_div_cancel₀ _ hB0.ne'] at this
  set u : ℝ := 2 * B * t / (1 + t ^ 2) with hu
  have hu3 : 5 / 2 ≤ u := by
    rw [hu, le_div_iff₀ (by positivity)]
    nlinarith
  have hu0 : 0 < u := by linarith
  have hS := sum_poisson_le hRH hu3 S
  
  have hterm : ∀ ρ ∈ S, (analyticOrderNatAt riemannXi (ρ : ℂ) : ℝ) *
        (2 * (1 + t ^ 2) / (‖(ρ : ℂ)‖ ^ 2 * (1 - t ^ 2) ^ 2
          + 4 * ‖((B : ℂ) + 1 / 2) - (ρ : ℂ)‖ ^ 2 * t ^ 2))
      ≤ 1 / (B * t) * ((analyticOrderNatAt riemannXi (ρ : ℂ) : ℝ) * (u / (u ^ 2 + (ρ : ℂ).im ^ 2))) := by
    intro ρ _
    have hρ := riemannXi_zero_re_of_RH hRH ρ.2
    rw [norm_sq_of_re_eq_half hρ, norm_sq_shift_sub hρ B]
    set γ := (ρ : ℂ).im
    have e : 1 / (B * t) * ((analyticOrderNatAt riemannXi (ρ : ℂ) : ℝ) * (u / (u ^ 2 + γ ^ 2)))
        = (analyticOrderNatAt riemannXi (ρ : ℂ) : ℝ) *
          (2 * (1 + t ^ 2) / (γ ^ 2 * (1 + t ^ 2) ^ 2 + 4 * B ^ 2 * t ^ 2)) := by
      have h1 : 0 < u ^ 2 + γ ^ 2 := by positivity
      have h2 : 0 < γ ^ 2 * (1 + t ^ 2) ^ 2 + 4 * B ^ 2 * t ^ 2 := by positivity
      have h3 : u ^ 2 + γ ^ 2 = (γ ^ 2 * (1 + t ^ 2) ^ 2 + 4 * B ^ 2 * t ^ 2) / (1 + t ^ 2) ^ 2 := by
        rw [hu]; field_simp; ring
      rw [h3, hu]
      field_simp
    rw [e]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
    nlinarith [sq_nonneg (1 - t ^ 2)]
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum]
  have hBt0 : 0 < B * t := by positivity
  have h1 : 1 / (B * t) * ∑ ρ ∈ S, (analyticOrderNatAt riemannXi (ρ : ℂ) : ℝ) *
      (u / (u ^ 2 + (ρ : ℂ).im ^ 2)) ≤ 1 / (B * t) * (Real.log (u / (2 * Real.pi)) / 2 + 7 / 3 / u) :=
    mul_le_mul_of_nonneg_left hS (by positivity)
  refine h1.trans ?_
  have hlog : Real.log (u / (2 * Real.pi)) ≤ Real.log (B * t / Real.pi) := by
    refine Real.log_le_log (by positivity) ?_
    rw [hu, div_div, div_le_div_iff₀ (by positivity) hpi]
    nlinarith [mul_pos hBt0 hpi, sq_nonneg t]
  have e2 : 1 / (B * t) * (7 / 3 / u) = 7 / 3 / (2 * B ^ 2) * (1 + 1 / t ^ 2) := by
    rw [hu]; field_simp; ring
  have e3 : 1 / (B * t) * (Real.log (u / (2 * Real.pi)) / 2)
      ≤ Real.log (B * t / Real.pi) / (2 * B * t) := by
    rw [show Real.log (B * t / Real.pi) / (2 * B * t)
        = 1 / (B * t) * (Real.log (B * t / Real.pi) / 2) by field_simp]
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  rw [mul_add, e2]
  linarith

theorem sum_zeroSumW_le (hRH : RiemannHypothesis) {B : ℝ} (hB : 50 ≤ B)
    (S : Finset {ρ : ℂ // riemannXi ρ = 0}) :
    Real.pi / 2 * ∑ ρ ∈ S, (analyticOrderNatAt riemannXi (ρ : ℂ) : ℝ) /
        (‖(ρ : ℂ)‖ * ‖((B : ℂ) + 1 / 2) - (ρ : ℂ)‖)
      ≤ 2 * (3 / B) / (1 - (3 / B) ^ 2) * (1 / 20) + (psiAux B (7 / 3) 1 - psiAux B (7 / 3) (3 / B)) := by
  have hB0 : 0 < B := by linarith
  set t₁ : ℝ := 3 / B with ht₁
  have ht₁0 : 0 < t₁ := by positivity
  have ht₁1 : t₁ < 1 := by rw [ht₁, div_lt_one hB0]; linarith
  have ht₁sq : 0 < 1 - t₁ ^ 2 := by nlinarith
  have hPpos : ∀ ρ : {ρ : ℂ // riemannXi ρ = 0}, 0 < ‖(ρ : ℂ)‖ := fun ρ =>
    norm_pos_iff.2 (riemannXi_zero_ne_zero ρ.2)
  have hQpos : ∀ ρ : {ρ : ℂ // riemannXi ρ = 0}, 0 < ‖((B : ℂ) + 1 / 2) - (ρ : ℂ)‖ := fun ρ => by
    have h := norm_sq_shift_sub (riemannXi_zero_re_of_RH hRH ρ.2) B
    have : 0 < ‖((B : ℂ) + 1 / 2) - (ρ : ℂ)‖ ^ 2 := by rw [h]; positivity
    have hne : ‖((B : ℂ) + 1 / 2) - (ρ : ℂ)‖ ≠ 0 := fun h0 => by rw [h0] at this; norm_num at this
    exact lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
  
  set F : ℝ → ℝ := fun t => psiAux B (7 / 3) t - ∑ ρ ∈ S, (analyticOrderNatAt riemannXi (ρ : ℂ) : ℝ) *
    gAux ‖(ρ : ℂ)‖ ‖((B : ℂ) + 1 / 2) - (ρ : ℂ)‖ t with hF
  have hFd : ∀ t : ℝ, 0 < t → HasDerivAt F
      ((Real.log (B * t / Real.pi) / (2 * B * t) + 7 / 3 / (2 * B ^ 2) * (1 + 1 / t ^ 2))
        - ∑ ρ ∈ S, (analyticOrderNatAt riemannXi (ρ : ℂ) : ℝ) *
        (2 * (1 + t ^ 2) / (‖(ρ : ℂ)‖ ^ 2 * (1 - t ^ 2) ^ 2
          + 4 * ‖((B : ℂ) + 1 / 2) - (ρ : ℂ)‖ ^ 2 * t ^ 2))) t := by
    intro t ht
    exact (hasDerivAt_psiAux hB0 ht).sub
      (HasDerivAt.fun_sum fun ρ _ => (hasDerivAt_gAux (hPpos ρ) (hQpos ρ) ht).const_mul _)
  have hmono : MonotoneOn F (Set.Icc t₁ 1) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc _ _) (fun t ht => ?_) (fun t ht => ?_)
      (fun t ht => ?_)
    · exact (hFd t (lt_of_lt_of_le ht₁0 ht.1)).continuousAt.continuousWithinAt
    · rw [interior_Icc] at ht
      exact (hFd t (lt_trans ht₁0 ht.1)).differentiableAt.differentiableWithinAt
    · rw [interior_Icc] at ht
      rw [(hFd t (lt_trans ht₁0 ht.1)).deriv, sub_nonneg]
      exact sum_deriv_le hRH hB S ht.1.le ht.2.le
  have hF1 := hmono (Set.left_mem_Icc.mpr ht₁1.le) (Set.right_mem_Icc.mpr ht₁1.le) ht₁1.le
  simp only [hF, gAux_one, mul_zero, Finset.sum_const_zero, sub_zero] at hF1
  
  have hterm : ∀ ρ ∈ S, Real.pi / 2 * ((analyticOrderNatAt riemannXi (ρ : ℂ) : ℝ) /
        (‖(ρ : ℂ)‖ * ‖((B : ℂ) + 1 / 2) - (ρ : ℂ)‖))
      ≤ 2 * t₁ / (1 - t₁ ^ 2) * ((analyticOrderNatAt riemannXi (ρ : ℂ) : ℝ) / ‖(ρ : ℂ)‖ ^ 2)
        - (analyticOrderNatAt riemannXi (ρ : ℂ) : ℝ) *
          gAux ‖(ρ : ℂ)‖ ‖((B : ℂ) + 1 / 2) - (ρ : ℂ)‖ t₁ := by
    intro ρ _
    have hP := hPpos ρ
    have hQ := hQpos ρ
    set P := ‖(ρ : ℂ)‖
    set Q := ‖((B : ℂ) + 1 / 2) - (ρ : ℂ)‖
    set m : ℝ := (analyticOrderNatAt riemannXi (ρ : ℂ) : ℝ)
    have hm : 0 ≤ m := Nat.cast_nonneg _
    set x : ℝ := P * (1 - t₁ ^ 2) / (2 * Q * t₁) with hx
    have hx0 : 0 < x := by positivity
    have h1 : Real.pi / 2 - Real.arctan x ≤ x⁻¹ := by
      rw [← Real.arctan_inv_of_pos hx0]
      exact Real.arctan_le_self (by positivity)
    have h2 : Real.pi / 2 * (m / (P * Q)) = m / (P * Q) * (Real.pi / 2 - Real.arctan x)
        - m * gAux P Q t₁ := by
      rw [gAux, ← hx]; ring
    have h3 : m / (P * Q) * x⁻¹ = 2 * t₁ / (1 - t₁ ^ 2) * (m / P ^ 2) := by
      rw [hx]; field_simp
    rw [h2, ← h3]
    have := mul_le_mul_of_nonneg_left h1 (show 0 ≤ m / (P * Q) by positivity)
    linarith
  rw [Finset.mul_sum]
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hsum : ∑ ρ ∈ S, (analyticOrderNatAt riemannXi (ρ : ℂ) : ℝ) / ‖(ρ : ℂ)‖ ^ 2 ≤ 1 / 20 :=
    ((summable_zero_inv_norm_sq hRH).sum_le_tsum S (fun ρ _ => by positivity)).trans
      (tsum_zero_inv_norm_sq_le hRH)
  have := mul_le_mul_of_nonneg_left hsum (show 0 ≤ 2 * t₁ / (1 - t₁ ^ 2) by positivity)
  linarith

theorem zeroSumW_le_of_RH' (hRH : RiemannHypothesis) (B : ℝ) (hB : 50 ≤ B) :
    B * zeroSumW B ≤ Real.log (B / Real.pi) ^ 2 / (2 * Real.pi) + 9 / 20 := by
  have hB0 : 0 < B := by linarith
  have hpi := Real.pi_pos
  have hpi3 := Real.pi_gt_d2
  have key : zeroSumW B ≤ (Real.log (B / Real.pi) ^ 2 / (2 * Real.pi) + 9 / 20) / B := by
    refine Real.tsum_le_of_sum_le (fun ρ => zeroSumW_term_nonneg B ρ) fun S => ?_
    have h := sum_zeroSumW_le hRH hB S
    set T := ∑ ρ ∈ S, (analyticOrderNatAt riemannXi (ρ : ℂ) : ℝ) /
        (‖(ρ : ℂ)‖ * ‖((B : ℂ) + 1 / 2) - (ρ : ℂ)‖)
    set L := Real.log (B / Real.pi)
    
    have h1 : 2 * (3 / B) / (1 - (3 / B) ^ 2) * (1 / 20) ≤ 31 / 100 / B := by
      have hx0 : 0 < 3 / B := by positivity
      have hx1 : 3 / B ≤ 3 / 50 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hB
      have hxB : 3 / B * B = 3 := div_mul_cancel₀ _ hB0.ne'
      have hx2 : (3 / B) ^ 2 ≤ 9 / 2500 := by nlinarith
      have hd : 0 < 1 - (3 / B) ^ 2 := by linarith
      rw [div_mul_eq_mul_div, div_le_div_iff₀ hd hB0,
        show 2 * (3 / B) * (1 / 20) * B = 3 / B * B / 10 by ring, hxB]
      linarith
    
    have h2 : psiAux B (7 / 3) 1 - psiAux B (7 / 3) (3 / B) ≤ L ^ 2 / (4 * B) + 7 / 18 / B := by
      unfold psiAux
      rw [mul_one, mul_div_cancel₀ _ hB0.ne']
      have hsq : 0 ≤ Real.log (3 / Real.pi) ^ 2 / (4 * B) := by positivity
      have e : 7 / 3 / (2 * B ^ 2) * (1 - 1⁻¹) - 7 / 3 / (2 * B ^ 2) * (3 / B - (3 / B)⁻¹)
          = 7 / 18 / B - 7 / (2 * B ^ 3) := by
        field_simp; ring
      have hpos : 0 ≤ 7 / (2 * B ^ 3) := by positivity
      linarith
    rw [le_div_iff₀ hB0]
    have h3 : Real.pi / 2 * T ≤ (L ^ 2 / 4 + 7 / 10) / B := by
      have : 31 / 100 / B + (L ^ 2 / (4 * B) + 7 / 18 / B) ≤ (L ^ 2 / 4 + 7 / 10) / B := by
        rw [show 31 / 100 / B + (L ^ 2 / (4 * B) + 7 / 18 / B) = (L ^ 2 / 4 + 31 / 100 + 7 / 18) / B by
          field_simp; ring]
        exact div_le_div_of_nonneg_right (by linarith) hB0.le
      linarith
    rw [le_div_iff₀ hB0] at h3
    
    have h4 : T * B ≤ 2 / Real.pi * (L ^ 2 / 4 + 7 / 10) := by
      rw [show T * B = 2 / Real.pi * (Real.pi / 2 * T * B) by field_simp]
      exact mul_le_mul_of_nonneg_left h3 (by positivity)
    have h5 : 2 / Real.pi * (L ^ 2 / 4 + 7 / 10) ≤ L ^ 2 / (2 * Real.pi) + 9 / 20 := by
      rw [show 2 / Real.pi * (L ^ 2 / 4 + 7 / 10) = L ^ 2 / (2 * Real.pi) + 7 / 5 / Real.pi by
        field_simp; ring]
      have : 7 / 5 / Real.pi ≤ 9 / 20 := by
        rw [div_le_div_iff₀ hpi (by norm_num)]; linarith
      linarith
    linarith
  calc B * zeroSumW B
      ≤ B * ((Real.log (B / Real.pi) ^ 2 / (2 * Real.pi) + 9 / 20) / B) :=
        mul_le_mul_of_nonneg_left key hB0.le
    _ = Real.log (B / Real.pi) ^ 2 / (2 * Real.pi) + 9 / 20 := by field_simp

theorem zeroSumW_le_of_RH (hRH : RiemannHypothesis) (B : ℝ) (hB : 50 ≤ B) :
    B * zeroSumW B ≤ Real.log (B / Real.pi) ^ 2 / (2 * Real.pi) + 1 / 2 := by
  have := zeroSumW_le_of_RH' hRH B hB
  linarith

end SchoenfeldRH
end File77

-- Upstream module SchoenfeldRH.Large
section File78


namespace SchoenfeldRH

namespace Large

open Real

lemma log_pi_gt : (1.134 : ℝ) ≤ Real.log π := by
  have he := Real.exp_one_lt_d9
  have he' := Real.exp_one_gt_d9
  have hp := Real.pi_gt_d4
  have hpe : 0 < π / Real.exp 1 := by positivity
  have h1 := Real.one_sub_inv_le_log_of_pos hpe
  rw [Real.log_div Real.pi_pos.ne' (Real.exp_pos 1).ne', Real.log_exp, inv_div] at h1
  have h2 : Real.exp 1 / π ≤ 0.866 := by
    rw [div_le_iff₀ Real.pi_pos]; nlinarith
  linarith

lemma exp_four_lt : Real.exp 4 < 55 := by
  have he := Real.exp_one_lt_d9
  have h0 := (Real.exp_pos 1).le
  have : Real.exp 4 = Real.exp 1 ^ 4 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [this]
  calc Real.exp 1 ^ 4 ≤ (2.7182818286 : ℝ) ^ 4 := by gcongr
    _ < 55 := by norm_num

lemma log_le_two_sqrt_div_e {t : ℝ} (ht : 0 < t) : Real.log t ≤ 2 * Real.sqrt t / Real.exp 1 := by
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have he := Real.exp_pos 1
  have h1 := Real.log_le_sub_one_of_pos (div_pos hs he)
  rw [Real.log_div hs.ne' he.ne', Real.log_exp, Real.log_sqrt ht.le] at h1
  have : Real.log t ≤ 2 * (Real.sqrt t / Real.exp 1) := by linarith
  calc Real.log t ≤ 2 * (Real.sqrt t / Real.exp 1) := this
    _ = 2 * Real.sqrt t / Real.exp 1 := by ring

lemma key {y : ℝ} (hy : 173.2 ≤ y) :
    y + (y + 1) * (Real.log (y / π) ^ 2 / (2 * π) + 1 / 2) + 4
      < y * Real.log y ^ 2 / (2 * π) := by
  have hpi := Real.pi_gt_d4
  have hpi' := Real.pi_lt_d4
  have hpi0 := Real.pi_pos
  have hy0 : 0 < y := by linarith
  set t := y / π with ht_def
  have ht0 : 0 < t := by positivity
  have hyt : y = π * t := by rw [ht_def]; field_simp
  
  set L := Real.log t with hL_def
  set p := Real.log π with hp_def
  have hlogy : Real.log y = L + p := by
    rw [hyt, Real.log_mul hpi0.ne' ht0.ne', add_comm]
  have hp := log_pi_gt
  
  have ht55 : 55 ≤ t := by
    rw [ht_def, le_div_iff₀ hpi0]; nlinarith
  have hL4 : 4 ≤ L := by
    rw [hL_def, Real.le_log_iff_exp_le ht0]; linarith [exp_four_lt]
  
  have hLs := log_le_two_sqrt_div_e ht0
  have he := Real.exp_one_gt_d9
  have he0 := Real.exp_pos 1
  have hsq : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht0.le
  have hLsq : L ^ 2 * Real.exp 1 ^ 2 ≤ 4 * t := by
    have h1 : L * Real.exp 1 ≤ 2 * Real.sqrt t := by
      rw [le_div_iff₀ he0] at hLs; exact hLs
    have h2 : 0 ≤ L * Real.exp 1 := by positivity
    nlinarith
  have hL2 : L ^ 2 ≤ 0.55 * t := by
    have : (7.38 : ℝ) ≤ Real.exp 1 ^ 2 := by nlinarith
    nlinarith
  
  rw [hlogy, ← sub_pos]
  have h2pi : 0 < 2 * π := by positivity
  have hexpr : y * (L + p) ^ 2 / (2 * π) -
      (y + (y + 1) * (L ^ 2 / (2 * π) + 1 / 2) + 4)
      = (y * p * (2 * L + p) - 3 * π * y - L ^ 2 - 9 * π) / (2 * π) := by
    field_simp; ring
  rw [hexpr]
  apply div_pos _ h2pi
  have hpp : 10.35 ≤ p * (2 * L + p) := by nlinarith
  have : 10.35 * y ≤ y * p * (2 * L + p) := by nlinarith
  
  have hL2y : L ^ 2 ≤ 0.18 * y := by
    have : 0.55 * t ≤ 0.18 * y := by
      rw [ht_def, mul_div_assoc', div_le_iff₀ hpi0]; nlinarith
    linarith
  nlinarith

lemma sqrt_ne (n k : ℕ) : Real.sqrt n - 1 / 2 ≠ 2 * k := by
  intro h
  have hs : Real.sqrt n = 2 * k + 1 / 2 := by linarith
  have h2 : ((n : ℕ) : ℝ) = (2 * k + 1 / 2) ^ 2 := by
    rw [← hs, Real.sq_sqrt (Nat.cast_nonneg _)]
  have h3 : ((4 * n : ℕ) : ℝ) = ((4 * (4 * k ^ 2 + 2 * k) + 1 : ℕ) : ℝ) := by
    push_cast; rw [h2]; ring
  have h4 : 4 * n = 4 * (4 * k ^ 2 + 2 * k) + 1 := by exact_mod_cast h3
  omega

lemma nat_bound (W : ℝ → ℝ)
    (hU : ∀ (x : ℕ) (lam : ℝ), 2 ≤ x → 2 < lam →
      Chebyshev.psi x - x ≤ x / (lam - 1) + Real.sqrt x * (lam * W (lam - 1 / 2)) + 3)
    (hL : ∀ (x : ℕ) (lam : ℝ), 2 ≤ x → 2 < lam → (∀ k : ℕ, lam ≠ 2 * k) →
      x - Chebyshev.psi x ≤ x / (lam + 1) + (Real.sqrt x + 1) * (lam * W (lam + 1 / 2)) + 3)
    (hZ : ∀ B : ℝ, 50 ≤ B → B * W B ≤ Real.log (B / Real.pi) ^ 2 / (2 * Real.pi) + 1 / 2)
    (hW : ∀ B : ℝ, 0 ≤ W B) (n : ℕ) (hn : 30000 ≤ n) :
    let y := Real.sqrt n
    let Z := Real.log (y / π) ^ 2 / (2 * π) + 1 / 2
    173.2 ≤ y ∧ Chebyshev.psi n - n ≤ y + (y + 1) * Z + 4 ∧
      (n : ℝ) - Chebyshev.psi n ≤ y + (y + 1) * Z + 3 := by
  intro y Z
  have hn' : (30000 : ℝ) ≤ n := by exact_mod_cast hn
  have hy : 173.2 ≤ y := Real.le_sqrt_of_sq_le (by linarith)
  have hy0 : 0 < y := by linarith
  have hyy : y ^ 2 = n := Real.sq_sqrt (Nat.cast_nonneg _)
  have hZ0 : 0 ≤ Z := by positivity
  have hWy := hW y
  have hZy : y * W y ≤ Z := hZ y (by linarith)
  have h2 : 2 ≤ n := by omega
  have hUy := hU n (y + 1 / 2) h2 (by linarith)
  have hLy := hL n (y - 1 / 2) h2 (by linarith) (sqrt_ne n)
  have hsy : Real.sqrt (n : ℝ) = y := rfl
  rw [hsy] at hUy hLy
  clear_value Z y
  refine ⟨hy, ?_, ?_⟩
  · have h := hUy
    rw [show y + 1 / 2 - 1 / 2 = y by ring] at h
    have hd : (n : ℝ) / (y + 1 / 2 - 1) ≤ y + 1 := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    have hm : y * ((y + 1 / 2) * W y) ≤ (y + 1) * Z := by
      have : y * ((y + 1 / 2) * W y) = (y + 1 / 2) * (y * W y) := by ring
      rw [this]
      calc (y + 1 / 2) * (y * W y) ≤ (y + 1 / 2) * Z := by gcongr
        _ ≤ (y + 1) * Z := by gcongr; linarith
    linarith
  · have h := hLy
    rw [show y - 1 / 2 + 1 / 2 = y by ring] at h
    have hd : (n : ℝ) / (y - 1 / 2 + 1) ≤ y := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    have hm : (y + 1) * ((y - 1 / 2) * W y) ≤ (y + 1) * Z := by
      gcongr
      nlinarith
    linarith

end Large

open Large in
theorem schoenfeld_large_of_contracts (W : ℝ → ℝ)
    (hU : ∀ (x : ℕ) (lam : ℝ), 2 ≤ x → 2 < lam →
      Chebyshev.psi x - x ≤ x / (lam - 1) + Real.sqrt x * (lam * W (lam - 1 / 2)) + 3)
    (hL : ∀ (x : ℕ) (lam : ℝ), 2 ≤ x → 2 < lam → (∀ k : ℕ, lam ≠ 2 * k) →
      x - Chebyshev.psi x ≤ x / (lam + 1) + (Real.sqrt x + 1) * (lam * W (lam + 1 / 2)) + 3)
    (hZ : ∀ B : ℝ, 50 ≤ B → B * W B ≤ Real.log (B / Real.pi) ^ 2 / (2 * Real.pi) + 1 / 2)
    (hW : ∀ B : ℝ, 0 ≤ W B) :
    ∀ x : ℝ, 30000 ≤ x → |Chebyshev.psi x - x| < Real.sqrt x * Real.log x ^ 2 / (8 * Real.pi) := by
  intro x hx
  set n := ⌊x⌋₊ with hn_def
  have hx0 : 0 ≤ x := by linarith
  have hn : 30000 ≤ n := Nat.le_floor (by exact_mod_cast hx)
  have hnx : (n : ℝ) ≤ x := Nat.floor_le hx0
  have hxn : x < n + 1 := Nat.lt_floor_add_one x
  obtain ⟨hy, hup, hlo⟩ := nat_bound W hU hL hZ hW n hn
  set y := Real.sqrt n with hy_def
  have hk := key hy
  have hpsi : Chebyshev.psi x = Chebyshev.psi n := Chebyshev.psi_eq_psi_coe_floor x
  
  have hn0 : (0 : ℝ) < n := by
    have : (30000 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hfn : Real.sqrt n * Real.log n ^ 2 / (8 * Real.pi) = y * Real.log y ^ 2 / (2 * Real.pi) := by
    have : Real.log n = 2 * Real.log y := by
      rw [hy_def, Real.log_sqrt hn0.le]; ring
    rw [this]; field_simp; ring
  have hfmono : Real.sqrt n * Real.log n ^ 2 / (8 * Real.pi) ≤ Real.sqrt x * Real.log x ^ 2 / (8 * Real.pi) := by
    have hl0 : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
    have hl : Real.log n ≤ Real.log x := Real.log_le_log hn0 hnx
    gcongr
  rw [hpsi, abs_lt]
  constructor <;> linarith

end SchoenfeldRH
end File78

-- Upstream module SchoenfeldRH.LargeRH
section File79


namespace SchoenfeldRH

theorem schoenfeld_large_of_RH (hRH : RiemannHypothesis) (x : ℝ) (hx : 30000 ≤ x) :
    |Chebyshev.psi x - x| < Real.sqrt x * Real.log x ^ 2 / (8 * Real.pi) :=
  schoenfeld_large_of_contracts zeroSumW
    (fun n lam hn hlam => psi_sub_le_of_RH hRH n hn lam hlam)
    (fun n lam hn hlam hne => sub_psi_le_of_RH hRH n hn lam hlam hne)
    (fun B hB => zeroSumW_le_of_RH hRH B hB)
    zeroSumW_nonneg x hx

end SchoenfeldRH
end File79

-- Upstream module SchoenfeldRH.Small.Check
section File80


namespace SchoenfeldRH.Small

open Chebyshev
open Nat (lcmUpto)

noncomputable def forceNat (n : ℕ) (k : ℕ → ℕ) : ℕ :=
  Nat.rec (k 0) (fun n' _ => k (Nat.succ n')) n

theorem forceNat_eq (n : ℕ) (k : ℕ → ℕ) : forceNat n k = k n := by
  cases n <;> rfl

noncomputable def forceB (n : ℕ) (k : ℕ → Bool) : Bool :=
  Nat.rec (k 0) (fun n' _ => k (Nat.succ n')) n

theorem forceB_eq (n : ℕ) (k : ℕ → Bool) : forceB n k = k n := by
  cases n <;> rfl

def incStep (R I n : ℕ) : ℕ :=
  Nat.mul I (Nat.div n (Nat.gcd n (Nat.mod (Nat.mul R I) n)))

noncomputable def incRun (R N c : ℕ) : ℕ → ℕ :=
  Nat.rec (fun I => I) (fun c ih I => forceNat (incStep R I (Nat.sub N c)) ih) c

noncomputable def prodRun (N c : ℕ) : ℕ → ℕ :=
  Nat.rec (fun P => P) (fun c ih P => forceNat (Nat.mul P (Nat.sub N c)) ih) c

noncomputable def lcmBatch (L N c : ℕ) : ℕ :=
  forceNat (prodRun N c 1) fun P => forceNat (Nat.mod L P) fun R => Nat.mul L (incRun R N c 1)

noncomputable def lcmRunB (k N q : ℕ) : ℕ → ℕ :=
  Nat.rec (fun L => L) (fun q ih L => forceNat (lcmBatch L (Nat.sub N (Nat.mul q k)) k) ih) q

def batchSize : ℕ := 32

noncomputable def lcmRun (b cnt L : ℕ) : ℕ :=
  forceNat (lcmBatch L (Nat.sub b (Nat.mul (Nat.div cnt batchSize) batchSize)) (Nat.mod cnt batchSize))
    (lcmRunB batchSize b (Nat.div cnt batchSize))

theorem incStep_eq (R I n : ℕ) : incStep R I n = I * (n / Nat.gcd n (R * I % n)) := rfl

theorem incRun_zero (R N I : ℕ) : incRun R N 0 I = I := rfl

theorem incRun_succ (R N c I : ℕ) : incRun R N (c + 1) I = incRun R N c (incStep R I (N - c)) :=
  forceNat_eq (incStep R I (N - c)) (incRun R N c)

theorem prodRun_zero (N P : ℕ) : prodRun N 0 P = P := rfl

theorem prodRun_succ (N c P : ℕ) : prodRun N (c + 1) P = prodRun N c (P * (N - c)) :=
  forceNat_eq (P * (N - c)) (prodRun N c)

theorem lcmBatch_eq (L N c : ℕ) : lcmBatch L N c = L * incRun (L % prodRun N c 1) N c 1 := by
  simp only [lcmBatch, forceNat_eq]; rfl

theorem lcmRunB_zero (k N L : ℕ) : lcmRunB k N 0 L = L := rfl

theorem lcmRunB_succ (k N q L : ℕ) :
    lcmRunB k N (q + 1) L = lcmRunB k N q (lcmBatch L (N - q * k) k) :=
  forceNat_eq (lcmBatch L (N - q * k) k) (lcmRunB k N q)

theorem lcmRun_eq (b cnt L : ℕ) :
    lcmRun b cnt L = lcmRunB 32 b (cnt / 32) (lcmBatch L (b - cnt / 32 * 32) (cnt % 32)) := by
  simp only [lcmRun, forceNat_eq]; rfl

theorem lcmUpto_zero : lcmUpto 0 = 1 := by simp [lcmUpto]

theorem lcmUpto_succ (n : ℕ) : lcmUpto (n + 1) = Nat.lcm (lcmUpto n) (n + 1) := by
  rw [lcmUpto, lcmUpto, ← Finset.insert_Icc_right_eq_Icc_add_one (by omega), Finset.lcm_insert,
    id, lcm_eq_nat_lcm, Nat.lcm_comm]

theorem mul_incStep {L P R I n : ℕ} (hR : R = L % P) (hn : n ∣ P) :
    L * incStep R I n = Nat.lcm (L * I) n := by
  have h1 : R * I ≡ L * I [MOD n] := by
    rw [hR]; exact ((Nat.mod_modEq L P).of_dvd hn).mul_right I
  have h2 : Nat.gcd n (R * I % n) = Nat.gcd (L * I) n := by
    rw [Nat.gcd_comm n, ← Nat.gcd_rec, Nat.gcd_comm n, h1.gcd_eq]
  rw [incStep_eq, h2, ← mul_assoc, Nat.lcm, Nat.mul_div_assoc _ (Nat.gcd_dvd_right _ _)]

theorem prodRun_dvd (N : ℕ) : ∀ c P : ℕ, P ∣ prodRun N c P ∧ ∀ j < c, (N - j) ∣ prodRun N c P := by
  intro c
  induction c with
  | zero => intro P; exact ⟨dvd_rfl, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  | succ c ih =>
    intro P
    rw [prodRun_succ]
    obtain ⟨h1, h2⟩ := ih (P * (N - c))
    refine ⟨(Dvd.intro _ rfl).trans h1, fun j hj => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · exact h2 j hj
    · exact (Dvd.intro_left _ rfl).trans h1

theorem mul_incRun {L P R N : ℕ} (hR : R = L % P) :
    ∀ c I : ℕ, c ≤ N → (∀ j < c, (N - j) ∣ P) → L * I = lcmUpto (N - c) →
      L * incRun R N c I = lcmUpto N := by
  intro c
  induction c with
  | zero => intro I _ _ h; simpa [incRun_zero] using h
  | succ c ih =>
    intro I hc hP h
    rw [incRun_succ]
    refine ih _ (by omega) (fun j hj => hP j (by omega)) ?_
    rw [mul_incStep hR (hP c (by omega)), h]
    have : N - c = (N - (c + 1)) + 1 := by omega
    rw [this, lcmUpto_succ]

theorem lcmBatch_lcmUpto {N c : ℕ} (hc : c ≤ N) : lcmBatch (lcmUpto (N - c)) N c = lcmUpto N := by
  rw [lcmBatch_eq]
  exact mul_incRun rfl c 1 hc (prodRun_dvd N c 1).2 (mul_one _)

theorem lcmRunB_lcmUpto (k N : ℕ) :
    ∀ q : ℕ, q * k ≤ N → lcmRunB k N q (lcmUpto (N - q * k)) = lcmUpto N := by
  intro q
  induction q with
  | zero => intro _; simp [lcmRunB_zero]
  | succ q ih =>
    intro hq
    have hq' : (q + 1) * k = q * k + k := Nat.succ_mul q k
    rw [lcmRunB_succ]
    have h1 : N - (q + 1) * k = (N - q * k) - k := by omega
    rw [h1, lcmBatch_lcmUpto (by omega)]
    exact ih (by omega)

theorem lcmRun_lcmUpto {b cnt : ℕ} (h : cnt ≤ b) : lcmRun b cnt (lcmUpto (b - cnt)) = lcmUpto b := by
  have hdm : cnt / 32 * 32 + cnt % 32 = cnt := Nat.div_add_mod' cnt 32
  rw [lcmRun_eq]
  have h1 : b - cnt = (b - cnt / 32 * 32) - cnt % 32 := by omega
  rw [h1, lcmBatch_lcmUpto (by omega)]
  exact lcmRunB_lcmUpto 32 b (cnt / 32) (by omega)

def checkIv (a b s kp ka kb La Lb : ℕ) : Bool :=
  Nat.ble a b && Nat.ble (s * s) (a * 2 ^ 20) && Nat.ble (2 ^ kp) (a ^ 64) &&
  Nat.ble (2 ^ ka) La && Nat.blt Lb (2 ^ kb) &&
  Nat.blt (kb * 6931471808 * (2 ^ 10 * 4096 * 10 ^ 10 * 10 ^ 10 * 8 * 31416))
    (s * kp * kp * 6931471803 * 6931471803 * 10000 * 10 ^ 10
      + a * 10 ^ 10 * (2 ^ 10 * 4096 * 10 ^ 10 * 10 ^ 10 * 8 * 31416)) &&
  Nat.blt ((b + 1) * 10 ^ 10 * (2 ^ 10 * 4096 * 10 ^ 10 * 10 ^ 10 * 8 * 31416))
    (s * kp * kp * 6931471803 * 6931471803 * 10000 * 10 ^ 10
      + ka * 6931471803 * (2 ^ 10 * 4096 * 10 ^ 10 * 10 ^ 10 * 8 * 31416))

theorem checkIv_iff {a b s kp ka kb La Lb : ℕ} :
    checkIv a b s kp ka kb La Lb = true ↔
      a ≤ b ∧ s * s ≤ a * 2 ^ 20 ∧ 2 ^ kp ≤ a ^ 64 ∧ 2 ^ ka ≤ La ∧ Lb < 2 ^ kb ∧
      kb * 6931471808 * (2 ^ 10 * 4096 * 10 ^ 10 * 10 ^ 10 * 8 * 31416)
        < s * kp * kp * 6931471803 * 6931471803 * 10000 * 10 ^ 10
          + a * 10 ^ 10 * (2 ^ 10 * 4096 * 10 ^ 10 * 10 ^ 10 * 8 * 31416) ∧
      (b + 1) * 10 ^ 10 * (2 ^ 10 * 4096 * 10 ^ 10 * 10 ^ 10 * 8 * 31416)
        < s * kp * kp * 6931471803 * 6931471803 * 10000 * 10 ^ 10
          + ka * 6931471803 * (2 ^ 10 * 4096 * 10 ^ 10 * 10 ^ 10 * 8 * 31416) := by
  simp only [checkIv, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq, and_assoc]

theorem bound_of_checkIv {a b s kp ka kb : ℕ}
    (h : checkIv a b s kp ka kb (lcmUpto a) (lcmUpto b) = true) {x : ℝ}
    (hx1 : (a : ℝ) ≤ x) (hx2 : x < (b : ℝ) + 1) :
    |ψ x - x| < Real.sqrt x * Real.log x ^ 2 / (8 * Real.pi) := by
  obtain ⟨-, hs, hkp, hka, hkb, hU, hL⟩ := checkIv_iff.mp h
  have ha0 : 0 < a := by
    rcases Nat.eq_zero_or_pos a with rfl | h
    · simp at hkp
    · exact h
  have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast ha0
  have hx0 : 0 < x := by linarith
  
  have hψa : (ka : ℝ) * Real.log 2 ≤ ψ x := by
    calc (ka : ℝ) * Real.log 2 = Real.log ((2 : ℝ) ^ ka) := by rw [Real.log_pow]
      _ ≤ Real.log (lcmUpto a) := Real.log_le_log (by positivity) (by exact_mod_cast hka)
      _ = ψ a := (psi_eq_log_lcmUpto a).symm
      _ ≤ ψ x := psi_mono hx1
  have hψb : ψ x < (kb : ℝ) * Real.log 2 := by
    have hfl : ⌊x⌋₊ ≤ b := by
      have : ⌊x⌋₊ < b + 1 := (Nat.floor_lt hx0.le).mpr (by exact_mod_cast hx2)
      omega
    calc ψ x = ψ ⌊x⌋₊ := psi_eq_psi_coe_floor x
      _ ≤ ψ b := psi_mono (by exact_mod_cast hfl)
      _ = Real.log (lcmUpto b) := psi_eq_log_lcmUpto b
      _ < Real.log ((2 : ℝ) ^ kb) :=
          Real.log_lt_log (by exact_mod_cast Nat.lcmUpto_pos b) (by exact_mod_cast hkb)
      _ = kb * Real.log 2 := Real.log_pow _ _
  
  have hloga : (kp : ℝ) * Real.log 2 ≤ 64 * Real.log a := by
    calc (kp : ℝ) * Real.log 2 = Real.log ((2 : ℝ) ^ kp) := by rw [Real.log_pow]
      _ ≤ Real.log ((a : ℝ) ^ 64) := Real.log_le_log (by positivity) (by exact_mod_cast hkp)
      _ = 64 * Real.log a := by rw [Real.log_pow]; norm_num
  have hsq : (s : ℝ) / 2 ^ 10 ≤ Real.sqrt a := by
    apply Real.le_sqrt_of_sq_le
    have hs' : (s : ℝ) * s ≤ a * 2 ^ 20 := by exact_mod_cast hs
    rw [div_pow, div_le_iff₀ (by positivity)]
    nlinarith
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  have hpi := Real.pi_lt_d4
  
  have hF : (s : ℝ) / 2 ^ 10 * ((kp : ℝ) * 0.6931471803 / 64) ^ 2 / (8 * 3.1416)
      ≤ Real.sqrt x * Real.log x ^ 2 / (8 * Real.pi) := by
    have h1 : (kp : ℝ) * 0.6931471803 / 64 ≤ Real.log a := by
      have : (kp : ℝ) * 0.6931471803 ≤ kp * Real.log 2 :=
        mul_le_mul_of_nonneg_left hl2.le (Nat.cast_nonneg _)
      linarith
    have h2 : Real.log a ≤ Real.log x := Real.log_le_log (by linarith) hx1
    have h3 : Real.sqrt a ≤ Real.sqrt x := Real.sqrt_le_sqrt hx1
    have h0 : (0 : ℝ) ≤ (kp : ℝ) * 0.6931471803 / 64 := by positivity
    have hlx : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
    calc (s : ℝ) / 2 ^ 10 * ((kp : ℝ) * 0.6931471803 / 64) ^ 2 / (8 * 3.1416)
        ≤ Real.sqrt x * Real.log x ^ 2 / (8 * 3.1416) := by
          gcongr
          · exact hsq.trans h3
          · exact h1.trans h2
      _ ≤ Real.sqrt x * Real.log x ^ 2 / (8 * Real.pi) := by
          gcongr
  
  have hUr : (kb : ℝ) * 0.6931471808 - a
      < (s : ℝ) / 2 ^ 10 * ((kp : ℝ) * 0.6931471803 / 64) ^ 2 / (8 * 3.1416) := by
    have hU' : (kb : ℝ) * 6931471808 * (2 ^ 10 * 4096 * 10 ^ 10 * 10 ^ 10 * 8 * 31416)
        < s * kp * kp * 6931471803 * 6931471803 * 10000 * 10 ^ 10
          + a * 10 ^ 10 * (2 ^ 10 * 4096 * 10 ^ 10 * 10 ^ 10 * 8 * 31416) := by exact_mod_cast hU
    norm_num at hU' ⊢
    linarith
  have hLr : (b : ℝ) + 1 - ka * 0.6931471803
      < (s : ℝ) / 2 ^ 10 * ((kp : ℝ) * 0.6931471803 / 64) ^ 2 / (8 * 3.1416) := by
    have hL' : ((b : ℝ) + 1) * 10 ^ 10 * (2 ^ 10 * 4096 * 10 ^ 10 * 10 ^ 10 * 8 * 31416)
        < s * kp * kp * 6931471803 * 6931471803 * 10000 * 10 ^ 10
          + ka * 6931471803 * (2 ^ 10 * 4096 * 10 ^ 10 * 10 ^ 10 * 8 * 31416) := by exact_mod_cast hL
    norm_num at hL' ⊢
    linarith
  have hka' : (ka : ℝ) * 0.6931471803 ≤ ka * Real.log 2 :=
    mul_le_mul_of_nonneg_left hl2.le (Nat.cast_nonneg _)
  have hkb' : (kb : ℝ) * Real.log 2 ≤ kb * 0.6931471808 :=
    mul_le_mul_of_nonneg_left hl2'.le (Nat.cast_nonneg _)
  rw [abs_lt]
  constructor <;> linarith

noncomputable def walk (final : ℕ) : List (ℕ × ℕ × ℕ × ℕ × ℕ) → ℕ → ℕ → Bool
  | [], a, _ => Nat.beq a final
  | (b, s, kp, ka, kb) :: rest, a, La =>
    forceB (lcmRun b (b - a) La) fun Lb =>
      checkIv a b s kp ka kb La Lb &&
        forceB (lcmBatch Lb (b + 1) 1) fun L' => walk final rest (b + 1) L'

theorem bound_of_walk (final : ℕ) :
    ∀ (data : List (ℕ × ℕ × ℕ × ℕ × ℕ)) (a : ℕ), walk final data a (lcmUpto a) = true →
      ∀ x : ℝ, (a : ℝ) ≤ x → x < (final : ℝ) →
        |ψ x - x| < Real.sqrt x * Real.log x ^ 2 / (8 * Real.pi) := by
  intro data
  induction data with
  | nil =>
    intro a h x hx1 hx2
    have : a = final := Nat.eq_of_beq_eq_true (by simpa [walk] using h)
    subst this
    exact absurd hx2 (not_lt.mpr hx1)
  | cons e rest ih =>
    obtain ⟨b, s, kp, ka, kb⟩ := e
    intro a h x hx1 hx2
    simp only [walk, forceB_eq, Bool.and_eq_true] at h
    obtain ⟨hc, hw⟩ := h
    have hab : a ≤ b := (checkIv_iff.mp hc).1
    have h1 : lcmRun b (b - a) (lcmUpto a) = lcmUpto b := by
      have := lcmRun_lcmUpto (b := b) (cnt := b - a) (Nat.sub_le _ _)
      rwa [Nat.sub_sub_self hab] at this
    have h2 : lcmBatch (lcmUpto b) (b + 1) 1 = lcmUpto (b + 1) := by
      have := lcmBatch_lcmUpto (N := b + 1) (c := 1) (by omega)
      rwa [Nat.add_sub_cancel] at this
    rw [h1] at hc hw
    rw [h2] at hw
    rcases lt_or_ge x ((b : ℝ) + 1) with hx | hx
    · exact bound_of_checkIv hc hx1 hx
    · exact ih (b + 1) hw x (by exact_mod_cast hx) hx2

end SchoenfeldRH.Small
end File80

-- Upstream module SchoenfeldRH.Small.Data
section File81
 

namespace SchoenfeldRH.Small

def data : List (Nat × Nat × Nat × Nat × Nat) := [
  (78, 8749, 396, 108, 109),
  (84, 9101, 403, 114, 123),
  (90, 9440, 410, 122, 130),
  (96, 9768, 416, 129, 130),
  (100, 10085, 422, 135, 136),
  (105, 10291, 426, 142, 150),
  (111, 10542, 430, 149, 163),
  (120, 10836, 435, 162, 170),
  (128, 11264, 442, 172, 184),
  (136, 11630, 448, 183, 191),
  (146, 11985, 454, 197, 205),
  (152, 12415, 460, 204, 219),
  (162, 12666, 464, 218, 227),
  (173, 13073, 470, 233, 252),
  (186, 13507, 476, 251, 267),
  (198, 14002, 483, 266, 290),
  (220, 14445, 488, 297, 306),
  (227, 15222, 498, 305, 321),
  (238, 15462, 501, 320, 337),
  (255, 15830, 505, 344, 362),
  (269, 16384, 512, 362, 387),
  (282, 16826, 516, 386, 412),
  (306, 17226, 521, 419, 432),
  (326, 17941, 528, 439, 465),
  (344, 18517, 534, 464, 485),
  (359, 19019, 539, 484, 519),
  (384, 19429, 543, 518, 557),
  (411, 20092, 549, 556, 592),
  (437, 20784, 555, 591, 627),
  (462, 21430, 561, 626, 671),
  (490, 22033, 566, 679, 706),
  (522, 22690, 572, 714, 752),
  (561, 23418, 577, 760, 793),
  (585, 24275, 584, 792, 830),
  (612, 24788, 588, 829, 876),
  (646, 25353, 592, 884, 934),
  (682, 26046, 597, 942, 990),
  (732, 26761, 602, 999, 1048),
  (778, 27723, 609, 1057, 1125),
  (827, 28580, 614, 1124, 1193),
  (876, 29465, 620, 1192, 1256),
  (929, 30324, 625, 1265, 1334),
  (979, 31227, 631, 1333, 1409),
  (1032, 32056, 635, 1408, 1489),
  (1090, 32911, 640, 1498, 1570),
  (1152, 33823, 645, 1579, 1661),
  (1222, 34770, 650, 1670, 1753),
  (1290, 35810, 656, 1762, 1856),
  (1364, 36792, 661, 1865, 1952),
  (1427, 37832, 666, 1951, 2031),
  (1485, 38695, 670, 2030, 2136),
  (1560, 39473, 674, 2135, 2252),
  (1626, 40457, 678, 2251, 2369),
  (1708, 41304, 682, 2379, 2471),
  (1788, 42332, 687, 2481, 2589),
  (1878, 43311, 691, 2599, 2714),
  (1985, 44387, 696, 2724, 2834),
  (2064, 45634, 701, 2833, 2967),
  (2159, 46532, 704, 2966, 3121),
  (2270, 47591, 708, 3120, 3266),
  (2375, 48798, 713, 3265, 3422),
  (2476, 49914, 717, 3421, 3594),
  (2616, 50963, 721, 3604, 3741),
  (2724, 52384, 726, 3751, 3946),
  (2836, 53454, 730, 3945, 4112),
  (2962, 54541, 734, 4122, 4284),
  (3108, 55739, 738, 4295, 4469),
  (3247, 57096, 742, 4480, 4646),
  (3366, 58359, 746, 4645, 4845),
  (3508, 59418, 749, 4844, 5027),
  (3639, 60658, 753, 5026, 5263),
  (3796, 61780, 757, 5262, 5482),
  (3942, 63098, 761, 5493, 5709),
  (4098, 64300, 764, 5720, 5925),
  (4260, 65559, 768, 5936, 6166),
  (4450, 66842, 771, 6177, 6407),
  (4635, 68316, 775, 6419, 6656),
  (4804, 69722, 779, 6655, 6937),
  (5002, 70981, 782, 6936, 7211),
  (5208, 72429, 786, 7222, 7500),
  (5416, 73905, 790, 7512, 7779),
  (5614, 75366, 793, 7790, 8077),
  (5819, 76731, 797, 8076, 8389),
  (6040, 78119, 800, 8388, 8690),
  (6255, 79589, 803, 8689, 9011),
  (6480, 80993, 807, 9010, 9364),
  (6718, 82436, 810, 9376, 9696),
  (6960, 83936, 813, 9708, 10050),
  (7212, 85434, 816, 10062, 10409),
  (7488, 86967, 820, 10420, 10755),
  (7735, 88615, 823, 10767, 11181),
  (8028, 90065, 826, 11180, 11563),
  (8301, 91755, 830, 11562, 11980),
  (8597, 93302, 833, 11979, 12345),
  (8857, 94950, 836, 12344, 12777),
  (9163, 96375, 839, 12776, 13210),
  (9460, 98026, 842, 13209, 13665),
  (9768, 99602, 845, 13677, 14115),
  (10092, 101210, 848, 14127, 14566),
  (10398, 102875, 851, 14579, 15039),
  (10728, 104422, 854, 15052, 15501),
  (11086, 106066, 856, 15513, 15983),
  (11449, 107821, 859, 15996, 16502),
  (11807, 109572, 862, 16501, 16961),
  (12134, 111272, 865, 16960, 17469),
  (12494, 112802, 868, 17468, 18003),
  (12871, 114463, 870, 18002, 18569),
  (13248, 116177, 873, 18568, 19143),
  (13680, 117866, 876, 19156, 19705),
  (14086, 119772, 879, 19718, 20338),
  (14536, 121537, 882, 20351, 20891),
  (14927, 123463, 884, 20903, 21531),
  (15358, 125112, 887, 21530, 22170),
  (15772, 126905, 890, 22183, 22813),
  (16192, 128604, 892, 22826, 23420),
  (16656, 130305, 894, 23433, 24037),
  (17153, 132159, 897, 24050, 24728),
  (17626, 134116, 900, 24727, 25454),
  (18120, 135953, 902, 25467, 26146),
  (18592, 137845, 905, 26159, 26882),
  (19165, 139628, 907, 26896, 27557),
  (19634, 141763, 910, 27556, 28291),
  (20152, 143487, 912, 28290, 29078),
  (20708, 145368, 915, 29077, 29808),
  (21224, 147359, 917, 29807, 30598),
  (21781, 149184, 919, 30597, 31418),
  (22348, 151129, 922, 31417, 32262),
  (22936, 153083, 924, 32276, 33094),
  (23554, 155084, 927, 33107, 33964),
  (24096, 157159, 929, 33963, 34866),
  (24696, 158957, 931, 34879, 35665),
  (25342, 160924, 933, 35678, 36541),
  (25987, 163015, 936, 36555, 37479),
  (26638, 165076, 938, 37478, 38396),
  (27285, 167131, 940, 38395, 39397),
  (27966, 169149, 943, 39396, 40349),
  (28648, 171246, 945, 40363, 41344),
  (29338, 173322, 947, 41357, 42352),
  (30000, 175397, 949, 42365, 43226)
]

def dataEnd : Nat := 30001

end SchoenfeldRH.Small
end File81

-- Upstream module SchoenfeldRH.Small
section File82


namespace SchoenfeldRH

open Chebyshev

namespace Small

theorem walk_data : walk dataEnd data 73 (lcmRun 73 73 1) = true := by decide +kernel

end Small

theorem schoenfeld_small (x : ℝ) (h1 : 73.2 ≤ x) (h2 : x ≤ 30000) :
    |Chebyshev.psi x - x| < Real.sqrt x * Real.log x ^ 2 / (8 * Real.pi) := by
  have h0 : Small.lcmRun 73 73 1 = Nat.lcmUpto 73 := by
    have := Small.lcmRun_lcmUpto (b := 73) (cnt := 73) le_rfl
    rwa [Nat.sub_self, Small.lcmUpto_zero] at this
  have hw := Small.walk_data
  rw [h0] at hw
  refine Small.bound_of_walk Small.dataEnd Small.data 73 hw x ?_ ?_
  · norm_num at h1 ⊢; linarith
  · norm_num [Small.dataEnd]; linarith

end SchoenfeldRH
end File82
section
open Complex Real
-- The functional-equation bridge is adapted from RHPrimeError/Converse.lean.
private theorem schoenfeldRH_of_halfPlane
    (h : ∀ s : ℂ, 1 / 2 < s.re → s ≠ 1 → riemannZeta s ≠ 0) : RiemannHypothesis := by
  intro s hzero htriv hs1
  by_contra hre
  rcases lt_or_gt_of_ne hre with hlt | hgt
  swap
  · exact h s hgt hs1 hzero
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [riemannZeta_zero] at hzero
    norm_num at hzero
  have hw : 1 / 2 < (1 - s).re := by
    rw [sub_re, one_re]
    linarith
  have hw1 : 1 - s ≠ 1 := fun h0 => hs0 (by linear_combination -h0)
  have hwn : ∀ n : ℕ, 1 - s ≠ -n := by
    intro n h0
    have := congrArg re h0
    rw [neg_re, natCast_re] at this
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hfe := riemannZeta_one_sub hwn hw1
  rw [sub_sub_cancel, hzero] at hfe
  have hζ : riemannZeta (1 - s) ≠ 0 := h _ hw hw1
  have hΓ : Gamma (1 - s) ≠ 0 := Gamma_ne_zero hwn
  have hpow : (2 * (π : ℂ)) ^ (-(1 - s)) ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff]
    exact fun h0 => mul_ne_zero two_ne_zero (ofReal_ne_zero.2 Real.pi_ne_zero) h0.1
  have hcos : cos (π * (1 - s) / 2) = 0 := by
    by_contra hc
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hpow) hΓ) hc) hζ hfe.symm
  obtain ⟨k, hk⟩ := Complex.cos_eq_zero_iff.1 hcos
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  have hsk : s = -2 * (k : ℂ) := by
    have h3 : (π : ℂ) * (s + 2 * k) = 0 := by linear_combination -2 * hk
    have h4 := (mul_eq_zero.1 h3).resolve_left hπ
    linear_combination h4
  have hk1 : 1 ≤ k := by
    by_contra hk1
    have hk0 : k ≤ 0 := by omega
    rcases eq_or_lt_of_le hk0 with hk0 | hk0
    · exact hs0 (by simp [hsk, hk0])
    · have hk' : (k : ℝ) ≤ -1 := by exact_mod_cast (by omega : k ≤ -1)
      have : s.re = -2 * (k : ℝ) := by simp [hsk]
      linarith
  refine htriv ⟨(k - 1).toNat, ?_⟩
  have hcast : (((k - 1).toNat : ℤ) : ℂ) = ((k - 1 : ℤ) : ℂ) := by
    rw [Int.toNat_of_nonneg (by omega)]
  rw [Int.cast_natCast] at hcast
  rw [hcast, hsk]
  push_cast
  ring


end

theorem Conjectures.Goldbach.RhSchoenfeldPsi : ((∀ s : ℂ, 1 / 2 < s.re → s ≠ 1 → riemannZeta s ≠ 0) → ∀ x : ℝ, (73.2 : ℝ) ≤ x → |(∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n) - x| ≤ Real.sqrt x * (Real.log x) ^ 2 / (8 * Real.pi)) := by
  intro h x hx
  have bound : |Chebyshev.psi x - x| < Real.sqrt x * Real.log x ^ 2 / (8 * Real.pi) := by
    by_cases hsmall : x ≤ 30000
    · exact SchoenfeldRH.schoenfeld_small x hx hsmall
    · exact SchoenfeldRH.schoenfeld_large_of_RH (schoenfeldRH_of_halfPlane h) x (le_of_not_ge hsmall)
  have rng : Finset.Ioc 0 ⌊x⌋₊ = Finset.Icc 1 ⌊x⌋₊ := by ext n; simp [Nat.succ_le_iff]
  simpa only [Chebyshev.psi,rng] using bound.le
