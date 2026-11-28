import Conjectures.Goldbach.RhSchoenfeldPsi
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.LSeries.ZetaZeros
import Mathlib.Analysis.SpecialFunctions.Log.Deriv


/-
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


namespace ZeroReciprocalConstant

private noncomputable def kernel (w : ℂ) : ℝ := (1 / (1-w) + 1/w).re

private lemma kernel_floor (w : ℂ) (h₀ : 0 < w.re) (h₁ : w.re < 1) :
    1 / (1+w.im^2) ≤ kernel w := by
  have h₁' : 0 < 1-w.re := by linarith
  have H (s : ℝ) (hs : 0 < s) (hs' : s ≤ 1) :
      s/(1+w.im^2) ≤ s/(s^2+w.im^2) := by
    apply div_le_div_of_nonneg_left hs.le (by positivity)
    nlinarith [mul_nonneg hs.le (sub_nonneg.mpr hs')]
  have a := H w.re h₀ h₁.le
  have b := H (1-w.re) h₁' (by linarith)
  unfold kernel
  simp only [one_div, Complex.add_re, Complex.inv_re, Complex.normSq_apply,
    Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, zero_sub,
    neg_mul_neg]
  simp only [← pow_two]
  calc
    _ = (1-w.re)/(1+w.im^2) + w.re/(1+w.im^2) := by ring
    _ ≤ _ := add_le_add b a

theorem norm_sum_bound {ι : Type*} (w : ι → ℂ) (m : ι → ℕ) {c : ℝ}
    (hstrip : ∀ i, 0 < (w i).re ∧ (w i).re < 1)
    (hc : c < 1/20)
    (hs : HasSum (fun i => (m i : ℂ) * (1/(1-w i) + 1/w i)) (c:ℂ)) :
    Summable (fun i => (m i : ℂ) / (w i*(w i+1))) ∧
      ‖∑' i, (m i : ℂ) / (w i*(w i+1))‖ ≤ 1/10 := by
  let k := fun i => kernel (w i)
  have hlow (i) : 1/(1+(w i).im^2) ≤ k i := kernel_floor _ (hstrip i).1 (hstrip i).2
  have hn (i) : 0 ≤ k i := le_trans (by positivity) (hlow i)
  have ht : HasSum (fun i => (m i:ℝ)*k i) c := by
    simpa only [k, kernel, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
      zero_mul, sub_zero, Complex.ofReal_re] using Complex.hasSum_re hs
  have hb (i) : ‖(m i:ℂ)/(w i*(w i+1))‖ ≤ 2*((m i:ℝ)*k i) := by
    rw [norm_div, norm_mul, Complex.norm_natCast]
    by_cases hm : m i = 0
    · simp [hm]
    have hmass : (1:ℝ) ≤ m i := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hm
    have hk : k i ≤ c := by
      apply le_trans (b := (m i:ℝ)*k i)
      · simpa only [one_mul] using mul_le_mul_of_nonneg_right hmass (hn i)
      · rw [← ht.tsum_eq]
        exact ht.summable.le_tsum i (fun j _ => mul_nonneg (Nat.cast_nonneg _) (hn j))
    have hden : (0:ℝ) < 1+(w i).im^2 := by positivity
    have hsq : 1 ≤ (w i).im^2 := by
      have h := (div_lt_iff₀ hden).mp ((hlow i).trans_lt (hk.trans_lt hc))
      linarith
    have hnorm : (w i).im^2 ≤ ‖w i‖*‖w i+1‖ := by
      rw [← sq_abs, pow_two]
      apply mul_le_mul (Complex.abs_im_le_norm _)
      · simpa using Complex.abs_im_le_norm (w i+1)
      · exact abs_nonneg _
      · exact norm_nonneg _
    have hpos : 0 < (w i).im^2 := lt_of_lt_of_le zero_lt_one hsq
    calc
      (m i:ℝ)/(‖w i‖*‖w i+1‖) ≤ (m i:ℝ)/(w i).im^2 :=
        div_le_div_of_nonneg_left (Nat.cast_nonneg _) hpos hnorm
      _ ≤ (m i:ℝ)*(2/(1+(w i).im^2)) := by
        rw [mul_div_assoc', div_le_div_iff₀ hpos hden]
        nlinarith [mul_nonneg (Nat.cast_nonneg (m i) (α:=ℝ)) (sub_nonneg.mpr hsq)]
      _ ≤ _ := by
        have h := mul_le_mul_of_nonneg_left (hlow i) (Nat.cast_nonneg (m i) (α:=ℝ))
        simp only [div_eq_mul_inv, one_mul] at h ⊢
        linarith only [h]
  have hmj := ht.summable.mul_left 2
  have hnorm := Summable.of_nonneg_of_le (fun i => norm_nonneg _) hb hmj
  refine ⟨hnorm.of_norm, (norm_tsum_le_tsum_norm hnorm).trans ?_⟩
  have h := hnorm.tsum_le_tsum hb hmj
  rw [tsum_mul_left, ht.tsum_eq] at h
  linarith

end ZeroReciprocalConstant

open Complex Filter
open scoped Topology

namespace XiZetaOrder

section
variable (xi : ℂ → ℂ)
variable (hform : ∀ s : ℂ, s ≠ 0 → s ≠ 1 →
    xi s = s*(s-1)*completedRiemannZeta s/2)

private noncomputable def unitFactor (s : ℂ) := 2/(s*(s-1)) * (Gammaℝ s)⁻¹

private lemma nonzero (s : ℂ) (h : 0 < s.re ∧ s.re < 1) :
    s ≠ 0 ∧ s ≠ 1 := by
  constructor
  · intro e; simpa [e] using h.1
  · intro e; simpa [e] using h.2

include hform in
private lemma factorization (s : ℂ) (h0 : s ≠ 0) (h1 : s ≠ 1) :
    riemannZeta s = xi s * unitFactor s := by
  rw [riemannZeta_def_of_ne_zero h0, hform s h0 h1]
  unfold unitFactor
  field_simp [h0, sub_ne_zero.mpr h1]

private lemma factor_ne_zero (s : ℂ) (h : 0 < s.re ∧ s.re < 1) : unitFactor s ≠ 0 := by
  obtain ⟨h0,h1⟩ := nonzero s h
  exact mul_ne_zero (div_ne_zero two_ne_zero (mul_ne_zero h0 (sub_ne_zero.mpr h1)))
    (inv_ne_zero (Gammaℝ_ne_zero_of_re_pos h.1))

include hform in
theorem zero_iff (s : ℂ) (h : 0 < s.re ∧ s.re < 1) :
    riemannZeta s = 0 ↔ xi s = 0 := by
  obtain ⟨h0,h1⟩ := nonzero s h
  rw [factorization xi hform s h0 h1, mul_eq_zero]
  simp [factor_ne_zero s h]

include hform in
theorem order_eq (ha : Differentiable ℂ xi) (s : ℂ) (h : 0 < s.re ∧ s.re < 1) :
    analyticOrderNatAt riemannZeta s = analyticOrderNatAt xi s := by
  obtain ⟨h0,h1⟩ := nonzero s h
  have H : riemannZeta =ᶠ[𝓝 s] xi * unitFactor := by
    filter_upwards [eventually_ne_nhds h0, eventually_ne_nhds h1] with w hw0 hw1
    exact factorization xi hform w hw0 hw1
  have hu : AnalyticAt ℂ unitFactor s := by
    unfold unitFactor
    exact (analyticAt_const.div (analyticAt_id.mul (analyticAt_id.sub analyticAt_const))
      (mul_ne_zero h0 (sub_ne_zero.mpr h1))).mul (differentiable_Gammaℝ_inv.analyticAt s)
  unfold analyticOrderNatAt
  rw [analyticOrderAt_congr H, analyticOrderAt_mul (ha.analyticAt _) hu,
    analyticOrderAt_eq_zero.mpr (.inr (factor_ne_zero s h)), add_zero]

variable (hstrip : ∀ {w}, xi w = 0 → 0 < w.re ∧ w.re < 1)

def zeroEquiv : {w : ℂ // xi w = 0} ≃
    {w : ℂ // 0 < w.re ∧ w.re < 1 ∧ riemannZeta w = 0} where
  toFun w := ⟨w, (hstrip w.property).1, (hstrip w.property).2,
    (zero_iff xi hform w (hstrip w.property)).mpr w.property⟩
  invFun w := ⟨w, (zero_iff xi hform w ⟨w.property.1,w.property.2.1⟩).mp w.property.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

end
end XiZetaOrder

namespace ZetaTrivialSeries

noncomputable def point (k : ℕ) : ℂ := -(2*((k:ℂ)+1))
noncomputable def correction (x : ℝ) (k : ℕ) : ℂ :=
  ((x:ℂ) ^ (point k+1) - 1) / (point k*(point k+1))

private lemma term_bound (x : ℝ) (hx : 1 ≤ x) (k : ℕ) :
    ‖correction x k‖ ≤ 1/((k:ℝ)+1) - 1/((k:ℝ)+2) := by
  let t : ℝ := 2*((k:ℝ)+1)
  have h : 2 ≤ t := by dsimp [t]; linarith [k.cast_nonneg (α:=ℝ)]
  have hpt : point k = ((-t:ℝ):ℂ) := by simp [point,t]
  have hpt' : point k + 1 = ((1-t:ℝ):ℂ) := by rw [hpt]; push_cast; ring
  have hu := Real.rpow_nonneg (show 0 ≤ x by linarith) (1-t)
  have hle : x^(1-t) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx (by linarith)
  have hd : 0 < t*(t-1) := mul_pos (by linarith) (by linarith)
  have hrepr : correction x k =
      (((x^(1-t) - 1)/(t*(t-1)):ℝ):ℂ) := by
    unfold correction
    rw [hpt',hpt,← Complex.ofReal_cpow (by linarith : 0 ≤ x)]
    push_cast; ring
  rw [hrepr, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hd, abs_of_nonpos (by linarith : x^(1-t)-1 ≤ 0)]
  apply le_trans (b:=1/(t*(t-1)))
  · apply div_le_div_of_nonneg_right _ hd.le
    linarith
  · dsimp [t]
    have hk : 0 ≤ (k:ℝ) := k.cast_nonneg
    have hfac : 0 < 2*((k:ℝ)+1)-1 := by linarith
    field_simp [hfac]
    nlinarith

theorem bound (x : ℝ) (hx : 1 ≤ x) :
    Summable (correction x) ∧ ‖∑' k, correction x k‖ ≤ 1 := by
  have hpart (N : ℕ) :
      ∑ k ∈ Finset.range N, ‖correction x k‖ ≤ 1 - 1/((N:ℝ)+1) := by
    induction N with
    | zero => norm_num
    | succ n ih =>
      rw [Finset.sum_range_succ, Nat.cast_add_one]
      have h := term_bound x hx n
      rw [show (n:ℝ)+1+1 = n+2 by ring]
      linarith only [h,ih]
  have H (N : ℕ) : ∑ k ∈ Finset.range N, ‖correction x k‖ ≤ 1 :=
    (hpart N).trans (sub_le_self _ (by positivity))
  have hs := summable_of_sum_range_le (fun k => norm_nonneg (correction x k)) H
  exact ⟨hs.of_norm,(norm_tsum_le_tsum_norm hs).trans (Real.tsum_le_of_sum_range_le (fun _ => norm_nonneg _) H)⟩

end ZetaTrivialSeries

namespace RealPsiAlgebra

open Complex
noncomputable section
def e (x : ℝ) (w : ℂ) := ((x:ℂ)^w-(x:ℂ)⁻¹)/(w*(w+1))

private lemma scaled (x : ℝ) (hx : 0 < x) (w : ℂ) :
    (x:ℂ)*e x w = ((x:ℂ)^(w+1)-1)/(w*(w+1)) := by
  have hx0 : (x:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  rw [e, Complex.cpow_add _ _ hx0, Complex.cpow_one, ← mul_div_assoc, mul_sub,
    mul_inv_cancel₀ hx0, mul_comm (x:ℂ) ((x:ℂ)^w)]

private lemma budget (x : ℝ) (hx : 2 ≤ x) (C T : ℂ) (hC : ‖C‖ ≤ 1/10) (hT : ‖T‖ ≤ 1) :
    ‖-(1/2:ℂ) - (Real.log (2*Real.pi):ℂ) * ((x:ℂ)-1) + C - T‖ ≤ 4*x := by
  have hl : 0 ≤ Real.log (2*Real.pi) := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hu : Real.log (2*Real.pi) ≤ 2 := by
    rw [Real.log_le_iff_le_exp (by positivity)]
    have he : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    rw [he]
    nlinarith [Real.exp_one_gt_d9,Real.pi_lt_d2]
  have hprod : ‖(Real.log (2*Real.pi):ℂ)*((x:ℂ)-1)‖ ≤ 2*(x-1) := by
    rw [norm_mul, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hl, abs_of_nonneg (by linarith : 0 ≤ x-1)]
    exact mul_le_mul_of_nonneg_right hu (by linarith)
  calc
    _ ≤ (‖-(1/2:ℂ) - (Real.log (2*Real.pi):ℂ)*((x:ℂ)-1)‖ + ‖C‖) + ‖T‖ :=
      (norm_sub_le _ _).trans (add_le_add_left (norm_add_le _ _) _)
    _ ≤ ((‖-(1/2:ℂ)‖ + ‖(Real.log (2*Real.pi):ℂ)*((x:ℂ)-1)‖) + ‖C‖) + ‖T‖ := by
      gcongr; apply norm_sub_le
    _ ≤ _ := by norm_num at *; linarith only [hprod,hC,hT,hx]

theorem assemble {ι : Type*} (x : ℝ) (hx : 2 ≤ x) (w : ι → ℂ) (m : ι → ℕ)
    (P : ℂ)
    (hconst : Summable (fun i => (m i:ℂ)/(w i*(w i+1))) ∧
      ‖∑' i, (m i:ℂ)/(w i*(w i+1))‖ ≤ 1/10)
    (hpair : Summable (fun i => (m i:ℂ)*e x (w i)))
    (hP : P = (x:ℂ)*(e x 1 - (Real.log (2*Real.pi):ℂ) * (1-(x:ℂ)⁻¹)
       - (∑' i, (m i:ℂ)*e x (w i)) - ∑' n, e x (ZetaTrivialSeries.point n))) :
    let term := fun i => (m i:ℂ)*(x:ℂ)^(w i+1)/(w i*(w i+1))
    Summable term ∧ ‖P-(((x^2/2:ℝ):ℂ)-∑' i,term i)‖ ≤ 4*x := by
  dsimp only
  have h0 : 0 < x := by linarith
  have h0C : (x:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h0.ne'
  let C := ∑' i, (m i:ℂ)/(w i*(w i+1))
  let T := ∑' n, ZetaTrivialSeries.correction x n
  have h := (hpair.hasSum.mul_left (x:ℂ)).add hconst.1.hasSum
  have H : HasSum (fun i => (m i:ℂ)*(x:ℂ)^(w i+1)/(w i*(w i+1)))
      ((x:ℂ)*(∑' i, (m i:ℂ)*e x (w i)) + C) := by
    apply h.congr_fun
    intro i
    change _ = (x:ℂ)*((m i:ℂ)*e x (w i)) + (m i:ℂ)/(w i*(w i+1))
    rw [mul_left_comm, scaled x h0]
    ring
  have hT : (x:ℂ)*(∑' n, e x (ZetaTrivialSeries.point n)) = T := by
    rw [← tsum_mul_left]
    exact tsum_congr fun n => scaled x h0 _
  have h1 : (x:ℂ)*e x 1 = (x:ℂ)^2/2-1/2 := by
    rw [scaled x h0, show (1+1:ℂ)=2 by norm_num, Complex.cpow_ofNat]
    ring
  have hlog : (x:ℂ)*((Real.log (2*Real.pi):ℂ)*(1-(x:ℂ)⁻¹)) =
      (Real.log (2*Real.pi):ℂ)*((x:ℂ)-1) := by
    rw [mul_left_comm, mul_sub, mul_one, mul_inv_cancel₀ h0C]
  refine ⟨H.summable,?_⟩
  rw [hP, mul_sub,mul_sub,mul_sub,h1,hlog,hT,H.tsum_eq]
  have hEq (A B D F : ℂ) : (A-1/2-B-D-T)-(A-(D+C)) = -(1/2)-B+C-T := by ring
  push_cast
  rw [hEq _ _ _ 0]
  exact budget x hx C T hconst.2 (ZetaTrivialSeries.bound x (by linarith)).2

end
end RealPsiAlgebra


namespace RealPsiFinish
open Complex ArithmeticFunction
noncomputable section

theorem from_real_formula (xi : ℂ → ℂ) (ha : Differentiable ℂ xi)
    (hform : ∀ s : ℂ, s ≠ 0 → s ≠ 1 → xi s = s*(s-1)*completedRiemannZeta s/2)
    (strip : ∀ {s}, xi s = 0 → 0 < s.re ∧ s.re < 1)
    (c : ℝ) (hc : c < 1/20)
    (hH : HasSum (fun z : {w : ℂ // xi w = 0} => (analyticOrderNatAt xi z.val:ℂ)*
      (1/(1-z.val)+1/z.val)) (c:ℂ))
    (hP : ∀ x : ℝ, 2 ≤ x →
      Summable (fun z : {w : ℂ // xi w = 0} => (analyticOrderNatAt xi z.val:ℂ) * RealPsiAlgebra.e x z.val) ∧
      (((∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (vonMangoldt n:ℝ)*(1-(n:ℝ)/x)):ℝ):ℂ) =
        RealPsiAlgebra.e x 1 - (Real.log (2*Real.pi):ℂ)*(1-(x:ℂ)⁻¹) -
        (∑' z : {w : ℂ // xi w = 0}, (analyticOrderNatAt xi z.val:ℂ) * RealPsiAlgebra.e x z.val) -
        ∑' k, RealPsiAlgebra.e x (ZetaTrivialSeries.point k)) :
    let K := {z : ℂ // 0 < z.re ∧ z.re < 1 ∧ riemannZeta z = 0}
    let f (x : ℝ) (z : K) := (analyticOrderNatAt riemannZeta z.val : ℂ) *
      (x : ℂ)^(z.val+1)/(z.val*(z.val+1))
    ∀ x : ℝ, 2 ≤ x → Summable (f x) ∧
       ‖((∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (x - (n : ℝ)) * vonMangoldt n : ℝ) : ℂ) -
         (((x^2/2 : ℝ) : ℂ) - ∑' z, f x z)‖ ≤ 4*x := by
  dsimp only
  intro x hx
  let I := {s : ℂ // xi s = 0}
  let J := {s : ℂ // 0 < s.re ∧ s.re < 1 ∧ riemannZeta s = 0}
  let E : I ≃ J := XiZetaOrder.zeroEquiv xi hform strip
  let m := fun z : I => analyticOrderNatAt xi z.val
  let w := fun z : I => z.val
  let P : ℝ := ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (x-(n:ℝ))*vonMangoldt n
  have H := ZeroReciprocalConstant.norm_sum_bound w m (fun z => strip z.property) hc hH
  obtain ⟨hp,he⟩ := hP x hx
  have hs : P = x * ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (vonMangoldt n:ℝ)*(1-(n:ℝ)/x) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    have hx0 : x ≠ 0 := by linarith
    field_simp
  have hSc :
      (P:ℂ) = (x:ℂ)*(RealPsiAlgebra.e x 1 - (Real.log (2*Real.pi):ℂ)*(1-(x:ℂ)⁻¹) -
        (∑' z : I, (m z:ℂ) * RealPsiAlgebra.e x (w z)) -
        ∑' k, RealPsiAlgebra.e x (ZetaTrivialSeries.point k)) := by
    rw [← he,hs,Complex.ofReal_mul]
  obtain ⟨hSum,hErr⟩ := RealPsiAlgebra.assemble x hx w m P H hp hSc
  let f := fun u : J => (analyticOrderNatAt riemannZeta u.val:ℂ) * (x:ℂ)^(u.val+1)/(u.val*(u.val+1))
  let g := fun u : I => (m u:ℂ)*(x:ℂ)^(w u+1)/(w u*(w u+1))
  have hfg : f ∘ E = g := by
    funext u
    change (analyticOrderNatAt riemannZeta u.val:ℂ) * _ / _ = (analyticOrderNatAt xi u.val:ℂ) * _ / _
    rw [XiZetaOrder.order_eq xi hform ha u.val (strip u.property)]
    rfl
  change Summable f ∧ ‖(P:ℂ) - (((x^2/2:ℝ):ℂ)-∑' z,f z)‖ ≤ 4*x
  constructor
  · exact E.summable_iff.mp (hfg.symm ▸ hSum : Summable (f ∘ E))
  · have h := E.tsum_eq f
    change (∑' u, (f ∘ E) u) = _ at h
    rw [hfg] at h
    rw [← h]
    exact hErr

end
end RealPsiFinish

-- Adapted from Andrew V. Sutherland, Schoenfeld RH 0e52d7b1, Apache 2.0.
-- Integer truncation is replaced by the closed interval through the floor of a real cutoff.
open Complex MeasureTheory Set Filter ArithmeticFunction
namespace SchoenfeldRH.Explicit

private lemma cpow_split_real {n : ℕ} (x : ℝ) (hx : 0 ≤ x) (hn : n ≠ 0) (s : ℂ) :
    (x : ℂ) ^ s = (((x / (n : ℝ) : ℝ)) : ℂ) ^ s * (n : ℂ) ^ s := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  rw [← Complex.ofReal_natCast n, ← Complex.mul_cpow_ofReal_nonneg (div_nonneg hx (Nat.cast_nonneg _)) (Nat.cast_nonneg _)]
  congr 1
  rw [← Complex.ofReal_mul, div_mul_cancel₀ _ hn']

theorem perron_weighted_real (a : ℕ → ℂ) (c μ : ℝ) (hc : 0 < c) (hμ : 1 < c + μ)
    (ha : Summable fun n : ℕ => ‖a n‖ / (n : ℝ) ^ c) (N : ℝ) (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Icc 1 ⌊N⌋₊, a n * ((1 - ((n : ℝ) / N) ^ μ : ℝ) : ℂ)
      = (1 / (2 * Real.pi)) * ∫ t : ℝ, LSeries a ((c : ℂ) + t * I) * ((N : ℂ) ^ ((c : ℂ) + t * I)
          * (1 / ((c : ℂ) + t * I) - 1 / ((c : ℂ) + t * I + μ))) := by
  set F : ℕ → ℝ → ℂ := fun n t => if n = 0 then 0 else a n * Kmu c μ ((N : ℝ) / n) t with hF
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le zero_lt_one hN
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
      rw [cpow_split_real N hNpos.le hn, div_mul_eq_mul_div, div_eq_iff hns]
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
      = if n ∈ Finset.Icc 1 ⌊N⌋₊ then a n * ((1 - ((n : ℝ) / N) ^ μ : ℝ) : ℂ) else 0 := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [hF]
    have hpi : (2 * Real.pi : ℂ) ≠ 0 := by
      have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
      exact mul_ne_zero two_ne_zero this
    simp only [hF, ite_eq_right hn]
    rw [integral_const_mul, integral_Kmu _ _ _ (hpos n hn) hc hμ]
    have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    by_cases h : (n : ℝ) ≤ N
    · have hmem : n ∈ Finset.Icc 1 ⌊N⌋₊ :=
        Finset.mem_Icc.mpr ⟨Nat.pos_of_ne_zero hn, (Nat.le_floor_iff hNpos.le).mpr h⟩
      have h1 : 1 ≤ N/n := (le_div_iff₀ hn0).2 (by simpa)
      rw [ite_eq_left h1, ite_eq_left hmem]
      have h2 : (N / n) ^ (-μ) = ((n : ℝ) / N) ^ μ := by
        rw [Real.rpow_neg (hpos n hn).le, ← Real.inv_rpow (hpos n hn).le, inv_div]
      rw [h2]
      field_simp
    · have hmem : n ∉ Finset.Icc 1 ⌊N⌋₊ :=
        fun hm => h ((Nat.le_floor_iff hNpos.le).mp (Finset.mem_Icc.mp hm).2)
      have h1 : ¬ 1 ≤ N/n := fun he => h (by simpa using (le_div_iff₀ hn0).mp he)
      rw [ite_eq_right h1, ite_eq_right hmem]
      simp
  rw [funext hpt, ← integral_tsum_of_summable_integral_norm hint hsum, ← tsum_mul_left]
  simp only [hkey]
  rw [tsum_eq_sum (s := Finset.Icc 1 ⌊N⌋₊)]
  · exact Finset.sum_congr rfl fun n hn => (ite_eq_left hn).symm
  · intro n hn
    exact ite_eq_right hn

theorem explicit_formula_real (x : ℝ) (hx : 1 ≤ x) (μ : ℝ) (hμ : 0 < μ ∨ μ < -1)
    (hne : ∀ k : ℕ, trivZero k + μ ≠ 0) :
    Summable (fun ρ : {ρ : ℂ // riemannXi ρ = 0} =>
        (analyticOrderNatAt riemannXi ρ : ℂ) * pairE x μ ρ) ∧
    Summable (fun k : ℕ => pairE x μ (trivZero k)) ∧
    (((∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (Λ n : ℝ) * (1 - ((n : ℝ) / x) ^ μ) : ℝ)) : ℂ)
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
  have hxpos : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx
  have hx1 : (1 : ℝ) ≤ x := hx
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
      simp only [Kmu]
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
  have hP := perron_weighted_real (fun n => (Λ n : ℂ)) c μ hc hcμ ?_ x hx
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
  have hL : ((∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (Λ n : ℝ) * (1 - ((n : ℝ) / x) ^ μ) : ℝ) : ℂ)
      = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (Λ n : ℂ) * ((1 - ((n : ℝ) / x) ^ μ : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    simp only [Complex.ofReal_mul]
  rw [hL, hP]
  field_simp


end SchoenfeldRH.Explicit

namespace GoldbachRealPsi
open Complex ArithmeticFunction SchoenfeldRH SchoenfeldRH.Explicit

theorem first_premise :
    let K := {z : ℂ // 0 < z.re ∧ z.re < 1 ∧ riemannZeta z = 0}
    let f (x : ℝ) (z : K) := (analyticOrderNatAt riemannZeta z.val : ℂ) *
      (x : ℂ)^(z.val+1)/(z.val*(z.val+1))
    ∀ x : ℝ, 2 ≤ x → Summable (f x) ∧
       ‖((∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (x - (n : ℝ)) * vonMangoldt n : ℝ) : ℂ) -
         (((x^2/2 : ℝ) : ℂ) - ∑' z, f x z)‖ ≤ 4*x := by
  apply RealPsiFinish.from_real_formula riemannXi differentiable_riemannXi
    (fun _ h0 h1 => riemannXi_eq_mul_completedRiemannZeta h0 h1)
    riemannXi_zero_re_mem (2*xiConst) two_mul_xiConst_lt
  · have H := hasSum_hadamard_riemannXi (s := 1) (by rw [riemannXi_one]; norm_num)
    rw [deriv_div_riemannXi_one] at H
    simpa only [two_mul, Complex.ofReal_add] using H
  · intro x hx
    have hne (k : ℕ) : trivZero k + (1:ℝ) ≠ 0 := by
      intro he
      have H := congrArg Complex.re he
      simp only [Complex.add_re, trivZero_re, Complex.ofReal_re, Complex.zero_re] at H
      linarith [k.cast_nonneg (α:=ℝ)]
    obtain ⟨hS,_,hE⟩ := explicit_formula_real x (by linarith) 1 (Or.inl zero_lt_one) hne
    constructor
    · simpa only [pairE, RealPsiAlgebra.e, Complex.ofReal_one, one_mul, Complex.cpow_neg_one] using hS
    · simpa only [pairE, RealPsiAlgebra.e, Complex.ofReal_one, one_mul, Complex.cpow_neg_one,
        Real.rpow_one, Real.rpow_neg_one, Complex.ofReal_sub, Complex.ofReal_inv,
        trivZero, ZetaTrivialSeries.point] using hE

end GoldbachRealPsi

namespace UnconditionalZeroTail

noncomputable def kernel (t : ℝ) (z : ℂ) : ℝ :=
  (1 / (((t + 1/2 : ℝ) : ℂ) - z) + 1/z).re

private lemma kernel_ge {t : ℝ} (_ht : 3 ≤ t) (z : ℂ) (hre : 0 < z.re ∧ z.re < 1) :
    (t + 1/2 - z.re)/((t + 1/2 - z.re)^2 + z.im^2) ≤ kernel t z := by
  simp only [kernel, Complex.add_re, one_div, Complex.inv_re, Complex.normSq_apply,
    Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, zero_sub,
    ← pow_two, neg_sq]
  have : 0 ≤ z.re/(z.re^2 + z.im^2) := div_nonneg hre.1.le (by positivity)
  linarith

private lemma kernel_nonneg {t : ℝ} (ht : 3 ≤ t) (z : ℂ) (hre : 0 < z.re ∧ z.re < 1) :
    0 ≤ kernel t z :=
  (div_nonneg (by linarith [hre.2]) (by positivity)).trans (kernel_ge ht z hre)

private lemma tail_term {t : ℝ} (ht : 3 ≤ t) (z : ℂ) (hre : 0 < z.re ∧ z.re < 1)
    (him : t < |z.im|) : 1/z.im^2 ≤ (3/t) * kernel t z := by
  let a := t + 1/2 - z.re
  have ht0 : 0 < t := by linarith
  have ha : 0 < a := by dsimp [a]; linarith [hre.2]
  have ha' : a ≤ (6/5)*|z.im| := by dsimp [a]; linarith [hre.1]
  have hs := pow_le_pow_left₀ ha.le ha' 2
  have habs : |z.im|^2 = z.im^2 := sq_abs _
  have hs' : 2*a^2 ≤ 3*z.im^2 := by nlinarith [hs, habs, sq_nonneg z.im]
  have hlin : (5/2)*t ≤ 3*a := by dsimp [a]; linarith [hre.2]
  have hγ : 0 < z.im^2 := by rw [← sq_abs]; exact sq_pos_of_pos (by linarith)
  have hmul := mul_le_mul_of_nonneg_right hlin hγ.le
  have hmul' := mul_le_mul_of_nonneg_left hs' ht0.le
  calc
    1/z.im^2 ≤ (3/t)*(a/(a^2+z.im^2)) := by
      rw [div_mul_div_comm, div_le_div_iff₀ hγ (mul_pos ht0 (by positivity))]
      linarith only [show t*(a^2+z.im^2) ≤ 3*a*z.im^2 by nlinarith only [hmul,hmul']]
    _ ≤ _ := mul_le_mul_of_nonneg_left (kernel_ge ht z hre) (by positivity)

theorem finite_tail {ι : Type*} (z : ι → ℂ) (m : ι → ℕ) {t c : ℝ} (ht : 3 ≤ t)
    (strip : ∀ i, 0 < (z i).re ∧ (z i).re < 1)
    (H : HasSum (fun i => (m i : ℝ)*kernel t (z i)) c)
    (hc : c ≤ Real.log t / 2 + 2)
    (F : Finset ι) (hF : ∀ i ∈ F, t < |(z i).im|) :
    ∑ i ∈ F, (m i:ℝ)/|(z i).im|^2 ≤ 2*(Real.log t+5)/t := by
  have ht0 : 0 < t := by linarith
  have hnon (i : ι) : 0 ≤ (m i : ℝ)*kernel t (z i) :=
    mul_nonneg (Nat.cast_nonneg _) (kernel_nonneg ht _ (strip i))
  have hs := sum_le_hasSum F (fun i _ => hnon i) H
  calc
    _ ≤ ∑ i ∈ F, (3/t)*((m i:ℝ)*kernel t (z i)) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [sq_abs]
      have h := mul_le_mul_of_nonneg_left (tail_term ht _ (strip i) (hF i hi)) (Nat.cast_nonneg (m i) (α:=ℝ))
      simpa only [mul_div_assoc', mul_one, mul_left_comm] using h
    _ = (3/t)* ∑ i ∈ F, (m i:ℝ)*kernel t (z i) := (Finset.mul_sum ..).symm
    _ ≤ (3/t)*(Real.log t/2+2) := mul_le_mul_of_nonneg_left (hs.trans hc) (by positivity)
    _ ≤ _ := by
      rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right ht0]
      linarith [Real.log_nonneg (by linarith : 1 ≤ t)]

end UnconditionalZeroTail
namespace UnconditionalZeroTail

abbrev CriticalZero := {z : ℂ // 0 < z.re ∧ z.re < 1 ∧ riemannZeta z = 0}

theorem transported_tail (xi : ℂ → ℂ) (hd : Differentiable ℂ xi)
    (hf : ∀ s : ℂ, s ≠ 0 → s ≠ 1 → xi s = s*(s-1)*completedRiemannZeta s/2)
    (hstrip : ∀ {z}, xi z = 0 → 0 < z.re ∧ z.re < 1)
    (b : ℝ) (hb : 2*b < 1/20)
    (t : ℝ) (ht : 3 ≤ t)
    (hh : ∀ s : ℂ, xi s ≠ 0 →
      HasSum (fun j : {z : ℂ // xi z = 0} => (analyticOrderNatAt xi j.val : ℂ) *
        (1 / (s-j.val) + 1/j.val)) (deriv xi s / xi s + (b:ℂ)))
    (hdlog : (deriv xi ((t+1/2:ℝ):ℂ) / xi ((t+1/2:ℝ):ℂ)).re ≤
        Real.log (t/(2*Real.pi))/2 + 7/3/t)
    (F : Finset CriticalZero) (hF : ∀ j ∈ F, t < |j.val.im|) :
    ∑ j ∈ F, (analyticOrderNatAt riemannZeta j.val : ℝ)/|j.val.im|^2 ≤
      2*(Real.log t+5)/t := by
  let E := XiZetaOrder.zeroEquiv xi hf hstrip
  let s : ℂ := ((t+1/2:ℝ):ℂ)
  have hne : xi s ≠ 0 := by
    intro h
    have h' := (hstrip h).2
    change t+1/2 < 1 at h'
    linarith
  have H := Complex.hasSum_re (hh s hne)
  let c := (deriv xi s / xi s).re + b
  have H' : HasSum (fun j : {z : ℂ // xi z = 0} =>
      (analyticOrderNatAt xi j.val:ℝ)*kernel t j.val) c := by
    simpa only [c,s,kernel, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero] using H
  have hc : c ≤ Real.log t / 2 + 2 := by
    have hlog : Real.log (t/(2*Real.pi)) ≤ Real.log t :=
      Real.log_le_log (by positivity) (div_le_self (by linarith) (by linarith [Real.pi_gt_three]))
    have hrat : (7:ℝ)/3/t ≤ 1 := (div_le_iff₀ (by linarith : 0 < t)).mpr (by linarith)
    dsimp only [c,s]
    linarith
  have bound := finite_tail (fun j : {z : ℂ // xi z = 0} => j.val)
    (fun j => analyticOrderNatAt xi j.val) ht (fun j => hstrip j.property) H' hc
    (F.map E.symm.toEmbedding) (by
      rw [Finset.forall_mem_map]
      exact hF)
  rw [Finset.sum_map] at bound
  exact le_trans (by
    apply le_of_eq
    apply Finset.sum_congr rfl
    intro j hj
    change (analyticOrderNatAt riemannZeta j.val : ℝ)/|j.val.im|^2 =
      (analyticOrderNatAt xi j.val : ℝ)/|j.val.im|^2
    rw [XiZetaOrder.order_eq xi hf hd j.val ⟨j.property.1,j.property.2.1⟩]) bound

end UnconditionalZeroTail

theorem psi_from_positive_kernel
    (hFull : let K := {z : ℂ // 0 < z.re ∧ z.re < 1 ∧ riemannZeta z = 0}
      let f (x : ℝ) (z : K) := (analyticOrderNatAt riemannZeta z.val : ℂ) *
        (x : ℂ)^(z.val+1)/(z.val*(z.val+1))
      ∀ x : ℝ, 2 ≤ x → Summable (f x) ∧
        ‖((∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (x - (n : ℝ)) * ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) -
          (((x^2/2 : ℝ) : ℂ) - ∑' z, f x z)‖ ≤ 4*x)
    (hTail : ∀ t : ℝ, 3 ≤ t → ∀ F : Finset UnconditionalZeroTail.CriticalZero,
        (∀ j ∈ F, t < |j.val.im|) → ∑ j ∈ F, (analyticOrderNatAt riemannZeta j.val:ℝ)/|j.val.im|^2
          ≤ 2*(Real.log t+5)/t) :
    (∀ x T : ℝ, 2 ≤ x → 3 ≤ T → ∃ Z : Finset ℂ, (∀ s : ℂ, s ∈ Z ↔ 0 < s.re ∧ s.re < 1 ∧ |s.im| ≤ T ∧ riemannZeta s = 0) ∧ ‖((∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (x - (n : ℝ)) * ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) - (((x ^ 2 / 2 : ℝ) : ℂ) - ∑ ρ ∈ Z, ((analyticOrderNatAt riemannZeta ρ : ℕ) : ℂ) * (x : ℂ) ^ (ρ + 1) / (ρ * (ρ + 1)))‖ ≤ 2 * x ^ 2 * (Real.log T + 5) / T + 4 * x) := by
  classical
  let Crit := {z : ℂ // 0 < z.re ∧ z.re < 1 ∧ riemannZeta z = 0}
  let mass (z : Crit) : ℝ := analyticOrderNatAt riemannZeta z.val
  let coef (x : ℝ) (z : Crit) : ℂ :=
    (analyticOrderNatAt riemannZeta z.val : ℂ) * (x : ℂ)^(z.val+1) / (z.val*(z.val+1))

  have coef_norm {x : ℝ} (hx : 2 ≤ x) (z : Crit) (hi : 0 < |z.val.im|) :
      ‖coef x z‖ ≤ x^2 * (mass z / |z.val.im|^2) := by
    have h1 := Complex.abs_im_le_norm z.val
    have h2 : |z.val.im| ≤ ‖z.val+1‖ := by simpa using Complex.abs_im_le_norm (z.val+1)
    have hpow : x^(z.val.re+1) ≤ x^2 := by
      rw [← Real.rpow_two]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith [z.property.2.1])
    have hden : |z.val.im|^2 ≤ ‖z.val‖ * ‖z.val+1‖ := by
      rw [pow_two]
      exact mul_le_mul h1 h2 hi.le (norm_nonneg _)
    unfold coef mass
    rw [norm_div, norm_mul, norm_mul, Complex.norm_natCast,
        Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : 0 < x), Complex.add_re, Complex.one_re]
    calc
      _ ≤ ((analyticOrderNatAt riemannZeta z.val : ℝ)*x^2)/|z.val.im|^2 :=
        div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hpow (by positivity)) (by positivity) hden
      _ = _ := by ring

  have truncate {x T : ℝ} (hx : 2 ≤ x) (hT : 3 ≤ T)
      (hs : Summable (coef x))
      :
      ∃ Z : Finset ℂ, (∀ z : ℂ, z ∈ Z ↔ 0 < z.re ∧ z.re < 1 ∧ |z.im| ≤ T ∧ riemannZeta z = 0) ∧
        ‖(∑' z, coef x z) - ∑ z ∈ Z, (analyticOrderNatAt riemannZeta z : ℂ) * (x:ℂ)^(z+1)/(z*(z+1))‖ ≤
          2*x^2*(Real.log T+5)/T := by
    classical
    let S : Set ℂ := {z | 0 < z.re ∧ z.re < 1 ∧ |z.im| ≤ T ∧ riemannZeta z = 0}
    have hS : S.Finite := by
      apply ((isCompact_closedBall (0:ℂ) (1+T)).inter_riemannZetaZeros_finite).subset
      intro z hz
      obtain ⟨ha,hb,hc,hd⟩ := hz
      refine ⟨?_,hd⟩
      rw [Metric.mem_closedBall, dist_zero_right]
      exact (Complex.norm_le_abs_re_add_abs_im z).trans (by rw [abs_of_pos ha]; linarith)
    let E := hS.toFinset
    let F : Finset Crit := E.subtype (fun z : ℂ => 0 < z.re ∧ z.re < 1 ∧ riemannZeta z = 0)
    have hmem (z : Crit) : z ∈ F ↔ |z.val.im| ≤ T := by
      refine (Finset.mem_subtype (p := fun u : ℂ => 0 < u.re ∧ u.re < 1 ∧ riemannZeta u = 0) (s := E) (a := z)).trans ?_
      rw [show z.val ∈ E ↔ z.val ∈ S from hS.mem_toFinset]
      change (0 < z.val.re ∧ z.val.re < 1 ∧ |z.val.im| ≤ T ∧ riemannZeta z.val = 0) ↔ _
      simp [z.property.1,z.property.2.1,z.property.2.2]
    let K := ↑((F : Set Crit)ᶜ)
    let emb : K ↪ Crit := Function.Embedding.subtype _
    have hgt (i : K) : T < |(emb i).val.im| := lt_of_not_ge (fun h => i.property ((hmem _).mpr h))
    have hfin (P : Finset K) :
        ∑ i ∈ P, mass (emb i) / |(emb i).val.im|^2 ≤ 2*(Real.log T+5)/T := by
      have H := hTail T hT (P.map emb) (by
        rw [Finset.forall_mem_map]
        exact fun j _ => hgt j)
      simpa only [Finset.sum_map] using H
    have hn : 0 ≤ (fun i : K => mass (emb i) / |(emb i).val.im|^2) :=
      fun i => div_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
    have hsm := summable_of_sum_le hn hfin
    have hbd := Real.tsum_le_of_sum_le hn hfin
    have ht (i : K) : ‖coef x (emb i)‖ ≤ x^2 * (mass (emb i) / |(emb i).val.im|^2) :=
      coef_norm hx _ (by linarith [hgt i])
    have hsn := (hsm.mul_left (x^2)).of_nonneg_of_le (fun i => norm_nonneg _) ht
    have hlim := (norm_tsum_le_tsum_norm hsn).trans (hsn.tsum_le_tsum ht (hsm.mul_left (x^2)))
    rw [tsum_mul_left] at hlim
    have eqsum : ∑ z ∈ F, coef x z = ∑ z ∈ E, (analyticOrderNatAt riemannZeta z : ℂ) *
        (x:ℂ)^(z+1)/(z*(z+1)) := by
      dsimp only [F, coef]
      apply Finset.sum_subtype_of_mem (fun z : ℂ => (analyticOrderNatAt riemannZeta z : ℂ) *
          (x:ℂ)^(z+1)/(z*(z+1)))
      intro z hz
      exact ⟨(hS.mem_toFinset.mp hz).1,(hS.mem_toFinset.mp hz).2.1,(hS.mem_toFinset.mp hz).2.2.2⟩
    refine ⟨E, fun z => hS.mem_toFinset, ?_⟩
    rw [← eqsum, ← hs.sum_add_tsum_compl (s := F), add_sub_cancel_left]
    calc
      _ ≤ x^2 * (∑' i : K, mass (emb i)/|(emb i).val.im|^2) := hlim
      _ ≤ x^2*(2*(Real.log T+5)/T) := mul_le_mul_of_nonneg_left hbd (sq_nonneg _)
      _ = _ := by ring
  intro x T hx hT
  obtain ⟨hs, her⟩ := hFull x hx
  obtain ⟨Z,hZ,herr⟩ := truncate hx hT hs
  refine ⟨Z,hZ,?_⟩
  let A : ℂ := ((∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (x - (n : ℝ)) * ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)
  let M : ℂ := ((x^2/2 : ℝ) : ℂ)
  let B := ∑' z, coef x z
  let C := ∑ z ∈ Z, (analyticOrderNatAt riemannZeta z : ℂ)*(x:ℂ)^(z+1)/(z*(z+1))
  change ‖A-(M-B)‖ ≤ 4*x at her
  change ‖B-C‖ ≤ _ at herr
  change ‖A-(M-C)‖ ≤ _
  have eq : A-(M-C) = (A-(M-B)) + -(B-C) := by abel
  rw [eq]
  have htriangle := norm_add_le (A-(M-B)) (-(B-C))
  rw [norm_neg] at htriangle
  linarith

open SchoenfeldRH in
theorem Conjectures.Goldbach.ZetaTruncatedExplicitPsi :
    (∀ x T : ℝ, 2 ≤ x → 3 ≤ T → ∃ Z : Finset ℂ, (∀ s : ℂ, s ∈ Z ↔ 0 < s.re ∧ s.re < 1 ∧ |s.im| ≤ T ∧ riemannZeta s = 0) ∧ ‖((∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (x - (n : ℝ)) * ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) - (((x ^ 2 / 2 : ℝ) : ℂ) - ∑ ρ ∈ Z, ((analyticOrderNatAt riemannZeta ρ : ℕ) : ℂ) * (x : ℂ) ^ (ρ + 1) / (ρ * (ρ + 1)))‖ ≤ 2 * x ^ 2 * (Real.log T + 5) / T + 4 * x) := by
  classical
  apply psi_from_positive_kernel GoldbachRealPsi.first_premise
  intro t ht F hF
  apply UnconditionalZeroTail.transported_tail riemannXi differentiable_riemannXi
    (fun s h0 h1 => riemannXi_eq_mul_completedRiemannZeta h0 h1)
    riemannXi_zero_re_mem xiConst two_mul_xiConst_lt t ht
    (fun _ h => hasSum_hadamard_riemannXi h)
    (re_logDeriv_riemannXi_le (by linarith)) F hF
