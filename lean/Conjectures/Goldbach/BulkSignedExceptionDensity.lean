import Mathlib

/-!
# Dyadic density of signed high-prime minor-arc exceptions

The fixed and moving spectra have the same full Fourier coefficient. Truncating both major-arc models at a fixed denominator leaves an averaged Ramanujan tail, while the fixed minor-arc coefficients satisfy a fourth-moment bound. Sources and their original credits follow below.
-/

/- Project proof adapted from BulkCount, revision dd80d09448e9ede6a255f1fc66cfea49cf50909b (Apache-2.0). Original attributions preserved. -/


namespace MovingBulk.Original

namespace ConvSum
open MeasureTheory

noncomputable def E (x : ℝ) : ℂ := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

lemma phase_add (u v : ℝ) : E (u + v) = E u * E v := by
  unfold E
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma fourier_mode (m : ℤ) :
    (∫ t in (0 : ℝ)..1, E ((m : ℝ) * t)) = if m = 0 then 1 else 0 := by
  by_cases hm : m = 0
  · subst m
    simp [E]
  let c : ℂ := (m : ℂ) * (2 * Real.pi * Complex.I)
  have he (t : ℝ) : E ((m : ℝ) * t) = Complex.exp (c * (t : ℂ)) := by
    unfold E c
    congr 1
    push_cast
    ring
  have hc : c ≠ 0 := by
    dsimp [c]
    exact mul_ne_zero (by exact_mod_cast hm)
      (mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero)
  simp_rw [he]
  rw [integral_exp_mul_complex hc]
  simp [hm, c, Complex.exp_int_mul_two_pi_mul_I]

lemma coefficient (w : ℕ → ℝ) (n : ℕ) :
    (∫ t in (0 : ℝ)..1, (∑ k ∈ Finset.range (n + 1), (w k : ℂ) * E ((k : ℝ) * t)) ^ 2 *
      E (-(n : ℝ) * t)) = ((∑ k ∈ Finset.range (n + 1), w k * w (n - k) : ℝ) : ℂ) := by
  let I := Finset.range (n + 1)
  let term := fun (k j : ℕ) (t : ℝ) =>
    ((w k : ℂ) * (w j : ℂ)) * E (((((k : ℤ) + j - n) : ℤ) : ℝ) * t)
  have hcont (k j : ℕ) : Continuous (term k j) := by dsimp [term, E]; fun_prop
  have hpoint (t : ℝ) : (∑ k ∈ I, (w k : ℂ) * E ((k : ℝ) * t)) ^ 2 * E (-(n : ℝ) * t) =
      ∑ k ∈ I, ∑ j ∈ I, term k j t := by
    simp only [sq, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun j _ => ?_))
    dsimp [term]
    push_cast
    rw [show ((k : ℝ) + j - n) * t = ((k : ℝ) * t + j * t) + -(n : ℝ) * t by ring,
      phase_add, phase_add]
    ring
  have hrow (k : ℕ) (hk : k ∈ I) :
      (∫ t in (0 : ℝ)..1, ∑ j ∈ I, term k j t) = (w k : ℂ) * (w (n - k) : ℂ) := by
    rw [intervalIntegral.integral_finsetSum (fun j _ => (hcont k j).intervalIntegrable _ _)]
    have hk' : k < n + 1 := Finset.mem_range.mp hk
    have hsub : n - k ∈ I := Finset.mem_range.mpr (by omega)
    simp only [term, intervalIntegral.integral_const_mul, fourier_mode]
    rw [Finset.sum_eq_single_of_mem (n - k) hsub]
    · simp [show (k : ℤ) + ((n - k : ℕ) : ℤ) - n = 0 by omega]
    · intro j _ hne
      simp [show (k : ℤ) + j - n ≠ 0 by omega]
  change (∫ t in (0 : ℝ)..1, (∑ k ∈ I, (w k : ℂ) * E ((k : ℝ) * t)) ^ 2 *
    E (-(n : ℝ) * t)) = _
  simp_rw [hpoint]
  rw [intervalIntegral.integral_finsetSum (fun k _ =>
    (continuous_finsetSum I (fun j _ => hcont k j)).intervalIntegrable _ _)]
  push_cast
  exact Finset.sum_congr rfl hrow

/-- Rational neighborhoods of any prescribed cutoff and radius form a measurable set. -/
theorem measurable_rational_arcs (Q n : ℕ) :
    MeasurableSet {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Q ∧ a ≤ q ∧ Nat.Coprime a q ∧
      |t - (a : ℝ) / (q : ℝ)| ≤ (Q : ℝ) / ((q : ℝ) * (n : ℝ))} := by
  simp only [Set.ofPred_exists]
  apply MeasurableSet.iUnion
  intro q
  apply MeasurableSet.iUnion
  intro a
  by_cases h : 1 ≤ q ∧ q ≤ Q ∧ a ≤ q ∧ Nat.Coprime a q
  · obtain ⟨h₁, h₂, h₃, h₄⟩ := h
    have hmeas : MeasurableSet {t : ℝ | |t - (a : ℝ) / (q : ℝ)| ≤ (Q : ℝ) / (q * n)} :=
      measurableSet_le (show Continuous (fun t : ℝ => |t - (a : ℝ) / (q : ℝ)|) by fun_prop).measurable
        measurable_const
    convert hmeas using 1
    ext t
    exact ⟨fun h => h.2.2.2.2, fun h => ⟨h₁, h₂, h₃, h₄, h⟩⟩
  · convert MeasurableSet.empty (α := ℝ) using 1
    ext t
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨h₁, h₂, h₃, h₄, _⟩
    exact h ⟨h₁, h₂, h₃, h₄⟩

/-- Split any interval-integrable complex coefficient at an arbitrary measurable set. -/
theorem indicator_integral_split {f : ℝ → ℂ} {s : Set ℝ} (hs : MeasurableSet s)
    {a b : ℝ} (hf : IntervalIntegrable f volume a b) :
    intervalIntegral (s.indicator f) a b volume +
      intervalIntegral (sᶜ.indicator f) a b volume = intervalIntegral f a b volume := by
  have hi {u : Set ℝ} (hu : MeasurableSet u) :
      IntervalIntegrable (u.indicator f) volume a b :=
    ⟨hf.1.indicator hu, hf.2.indicator hu⟩
  rw [← intervalIntegral.integral_add (hi hs) (hi hs.compl)]
  apply congrArg (fun g : ℝ → ℂ => intervalIntegral g a b volume)
  funext t
  by_cases ht : t ∈ s <;> simp [ht]


end ConvSum


/-!
# Major-arc estimates for the prime logarithmic sum

For the exact logarithmic cutoff and the prime logarithmic weights, the main result
gives the constant 1/144 for every sufficiently large even target. A small-modulus
Siegel--Walfisz estimate and summation by parts bound the sum of the integrated
approximation errors by o(n). The squared geometric sum gives a decreasing
denominator weight. Finite Ramanujan sums and the evenness of the target give
a lower bound of one third of the mass at denominator one. The two endpoint
intervals together give the full mass at that denominator.

The analytic material in the namespaces OAI.LargePrimeGaps is selected and adapted
from OpenAI's openai/math, lean/OAI/NumberTheory/PrimeGaps, at revision
f5702854040e97fa7675c21ba37a9608f5f92dd3, licensed under Apache 2.0 (see LICENSE).
It is specialized to the declarations required for the small-modulus estimate and
ported from toolchain 4.34.1 to the version locked by this repository.
-/

section

-- Source module: CharacterErrors
namespace OAI
namespace LargePrimeGaps
open Filter
open Set Filter MeasureTheory
open scoped Topology ContDiff
open Asymptotics
open scoped Classical
open scoped ContDiff
open Topology
open scoped Convolution ContDiff Pointwise
noncomputable def primeCharacterPrefix (x : ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ n∈Finset.Ioc 0 ⌊x⌋₊, χ (n:ZMod q)*(ArithmeticFunction.vonMangoldt n:ℂ)

noncomputable def primeCharacterError (x : ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) : ℂ :=
  primeCharacterPrefix x χ-if χ=1 then (x:ℂ) else 0

end LargePrimeGaps
end OAI

-- Source module: ConductorBounds
namespace OAI
namespace LargePrimeGaps
open Filter
open Set Filter MeasureTheory
open scoped Topology ContDiff
open Asymptotics
open scoped Classical
open scoped ContDiff
open Topology
open scoped Convolution ContDiff Pointwise
open scoped ComplexConjugate
open Filter Topology
def SiegelWalfisz : Prop :=
  ∀ A B : ℝ, 0 < A → 0 < B → ∃ M : ℝ, 0 < M ∧ ∃ x₀ : ℝ, 1 < x₀ ∧
    ∀ x : ℝ, x₀ ≤ x → ∀ d : ℕ, 0 < d → (d:ℝ) ≤ (Real.log x)^B →
      ∀ χ : DirichletCharacter ℂ d, χ.IsPrimitive →
        ‖primeCharacterError x χ‖ ≤ M*x*(Real.log x)^(-A)

theorem eventually_log_rpow_le_rpow (a : ℝ) {s : ℝ} (hs : 0 < s) :
    ∀ᶠ x : ℝ in atTop, (Real.log x)^a ≤ x^s := by
  filter_upwards [(isLittleO_log_rpow_rpow_atTop a hs).bound (by norm_num : (0:ℝ)<1),
    eventually_ge_atTop (1:ℝ)] with x h hx
  simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Real.log_nonneg hx) _),
    abs_of_nonneg (Real.rpow_nonneg (by linarith : 0≤x) _),one_mul] using h

end LargePrimeGaps
end OAI

-- Source module: LogParameters
namespace OAI
namespace LargePrimeGaps
open Filter
open Set Filter MeasureTheory
open scoped Topology ContDiff
open Asymptotics
open scoped Classical
open scoped ContDiff
open Topology
open scoped Convolution ContDiff Pointwise
open scoped ComplexConjugate
open Filter Topology
open Complex Filter Topology
noncomputable def poleRemovedL {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) : ℂ → ℂ :=
  if χ = 1 then DirichletCharacter.LFunctionTrivChar₁ q else χ.LFunction

noncomputable def primeLogDerivativeRegular {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  -deriv (poleRemovedL χ) s / poleRemovedL χ s

theorem poleRemovedL_differentiable {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) : Differentiable ℂ (poleRemovedL χ) := by
  unfold poleRemovedL
  split_ifs with hχ
  · exact DirichletCharacter.differentiable_LFunctionTrivChar₁ q
  · exact DirichletCharacter.differentiable_LFunction hχ

theorem poleRemovedL_ne_zero {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 ≤ s.re) :
    poleRemovedL χ s ≠ 0 := by
  unfold poleRemovedL
  split_ifs with hχ
  · rcases eq_or_ne s 1 with rfl | hs1
    · exact DirichletCharacter.LFunctionTrivChar₁_apply_one_ne_zero q
    · rw [DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hs1]
      refine mul_ne_zero (sub_ne_zero.mpr hs1) ?_
      exact DirichletCharacter.LFunction_ne_zero_of_one_le_re 1 (.inr hs1) hs
  · exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (.inl hχ) hs

theorem primeLogDerivativeRegular_analyticAt {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : poleRemovedL χ s ≠ 0) :
    AnalyticAt ℂ (primeLogDerivativeRegular χ) s := by
  have h := (poleRemovedL_differentiable χ).analyticAt s
  exact h.deriv.neg.div h hs

theorem primeLogDerivativeRegular_eq {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    primeLogDerivativeRegular χ s =
      LSeries (fun n : ℕ => χ (n : ZMod q) * (ArithmeticFunction.vonMangoldt n : ℂ)) s -
        (if χ = 1 then 1 / (s - 1) else 0) := by
  have hs1 : s ≠ 1 := by intro h; simp [h] at hs
  have hL := DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hs
  change LSeries (fun n : ℕ => χ (n : ZMod q) * (ArithmeticFunction.vonMangoldt n : ℂ)) s =
    -deriv (LSeries (fun n : ℕ => χ (n : ZMod q))) s /
      LSeries (fun n : ℕ => χ (n : ZMod q)) s at hL
  rw [hL, ← DirichletCharacter.LFunction_eq_LSeries χ hs,
    ← DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ hs]
  by_cases hχ : χ = 1
  · subst χ
    have hn := DirichletCharacter.LFunction_ne_zero_of_one_le_re
      (1 : DirichletCharacter ℂ q) (.inr hs1) hs.le
    simp only [primeLogDerivativeRegular, poleRemovedL, ↓reduceIte]
    rw [DirichletCharacter.deriv_LFunctionTrivChar₁_apply_of_ne_one q hs1,
      DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hs1]
    change -((s-1)*deriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)) s +
      DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) s) /
      ((s-1)*DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) s) = _
    field_simp
    ring
  · simp [primeLogDerivativeRegular, poleRemovedL, hχ]

end LargePrimeGaps
end OAI

-- Source module: DirichletGrowth
namespace OAI
namespace LargePrimeGaps
open Filter
open Set Filter MeasureTheory
open scoped Topology ContDiff
open Asymptotics
open scoped Classical
open scoped ContDiff
open Topology
open scoped Convolution ContDiff Pointwise
open scoped ComplexConjugate
open Filter Topology
open Complex Filter Topology
open Complex Filter Topology Set MeasureTheory Asymptotics
noncomputable def discrepancyTail (A : ℝ → ℂ) (u : ℝ) (s : ℂ) : ℂ :=
  ∫ t in Ioi u, A t * (t:ℂ)^(-(s+1))

lemma discrepancyTail_integrable {A : ℝ → ℂ} {u D : ℝ} (hu : 0 < u) (hD : 0 ≤ D)
    (hA : Measurable A) (hbound : ∀ t, u < t → ‖A t‖ ≤ D) {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun t => A t * (t:ℂ)^(-(s+1))) (Ioi u) := by
  have hp : (-(s+1)).re < -1 := by simp only [neg_re,add_re,one_re]; linarith
  have hi := (integrableOn_Ioi_norm_cpow_of_lt hp hu).const_mul D
  have hm := (integrableOn_Ioi_cpow_of_lt hp hu).aestronglyMeasurable
  refine hi.mono (hA.aestronglyMeasurable.restrict.mul hm) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hD (norm_nonneg _))]
  exact mul_le_mul_of_nonneg_right (hbound t ht) (norm_nonneg _)

lemma discrepancyTail_norm_le {A : ℝ → ℂ} {u D : ℝ} (hu : 0 < u) (_hD : 0 ≤ D)
    (_hA : Measurable A) (hbound : ∀ t, u < t → ‖A t‖ ≤ D) {s : ℂ} (hs : 0 < s.re) :
    ‖discrepancyTail A u s‖ ≤ D * u^(-s.re)/s.re := by
  have hi := (integrableOn_Ioi_rpow_of_lt (by linarith : -s.re-1 < -1) hu).const_mul D
  calc
    _ ≤ ∫ t in Ioi u, D*t^(-s.re-1) := by
      apply norm_integral_le_of_norm_le hi
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [norm_mul, norm_cpow_eq_rpow_re_of_pos (hu.trans ht)]
      simp only [neg_re,add_re,one_re,neg_add_rev]
      have he : -1 + -s.re = -s.re-1 := by ring
      rw [he]
      exact mul_le_mul_of_nonneg_right (hbound t ht) (Real.rpow_nonneg (hu.trans ht).le _)
    _ = _ := by
      rw [integral_const_mul,integral_Ioi_rpow_of_lt (by linarith : -s.re-1 < -1) hu]
      ring_nf

lemma discrepancyTail_eq_mellin {A : ℝ → ℂ} {u : ℝ} (hu : 0 ≤ u) (s : ℂ) :
    discrepancyTail A u s = mellin ((Ioi u).indicator A) (-s) := by
  rw [mellin]
  simp_rw [←Set.indicator_smul]
  rw [integral_indicator measurableSet_Ioi,Measure.restrict_restrict measurableSet_Ioi]
  have he : Ioi u ∩ Ioi 0 = Ioi u := Set.inter_eq_left.mpr (fun t ht => hu.trans_lt ht)
  rw [he]
  unfold discrepancyTail
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  simp only [smul_eq_mul]
  rw [mul_comm]
  congr 2
  ring

lemma discrepancyTail_differentiableAt {A : ℝ → ℂ} {u D : ℝ} (hu : 0 < u) (hD : 0 ≤ D)
    (hA : Measurable A) (hbound : ∀ t, u < t → ‖A t‖ ≤ D) {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (discrepancyTail A u) s := by
  let B := (Ioi u).indicator A
  have hm : Measurable B := hA.indicator measurableSet_Ioi
  have hb : ∀ t, ‖B t‖ ≤ D := by
    intro t
    by_cases ht : u < t
    · simpa [B,ht] using hbound t ht
    · simpa [B,ht] using hD
  have hloc : LocallyIntegrableOn B (Ioi 0) :=
    ((locallyIntegrable_const D).mono hm.aestronglyMeasurable
      (.of_forall (fun t => (hb t).trans (le_abs_self D)))).locallyIntegrableOn _
  have htop : B =O[atTop] (fun t : ℝ => t^(-(0:ℝ))) := by
    refine isBigO_iff.mpr ⟨D,Eventually.of_forall ?_⟩
    intro t
    simpa using hb t
  have hbot : B =O[𝓝[>] 0] (fun t : ℝ => t^(-(-s.re-1))) := by
    refine isBigO_iff.mpr ⟨0,?_⟩
    filter_upwards [nhdsWithin_le_nhds (gt_mem_nhds hu)] with t ht
    simp [B,not_lt.mpr ht.le]
  have hd := mellin_differentiableAt_of_isBigO_rpow hloc htop
    (by simpa using hs : (-s).re < 0) hbot (by simp : -s.re-1 < (-s).re)
  have he : discrepancyTail A u = fun z => mellin B (-z) := funext (discrepancyTail_eq_mellin hu.le)
  rw [he]
  exact hd.comp s differentiableAt_id.neg

open Finset
lemma periodic_sum_norm_le {f : ℕ → ℂ} {q : ℕ} (hq : 0 < q)
    (hp : ∀ n, f (q+n) = f n) (hz : ∑ n ∈ range q, f n = 0)
    (hb : ∀ n, ‖f n‖ ≤ 1) (N : ℕ) : ‖∑ n ∈ range N, f n‖ ≤ q := by
  induction N using Nat.strong_induction_on with
  | ind N ih =>
    by_cases hN : N < q
    · calc
        _ ≤ ∑ n ∈ range N, ‖f n‖ := norm_sum_le _ _
        _ ≤ ∑ _n ∈ range N, (1:ℝ) := sum_le_sum (fun n _ => hb n)
        _ = N := by simp
        _ ≤ q := by exact_mod_cast hN.le
    · have he : q+(N-q) = N := Nat.add_sub_of_le (not_lt.mp hN)
      rw [←he, sum_range_add, hz, zero_add]
      simp_rw [hp]
      exact ih _ (Nat.sub_lt (lt_of_lt_of_le hq (not_lt.mp hN)) hq)

lemma char_sum_range_zero {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) : ∑ n ∈ range q, χ (n : ZMod q) = 0 := by
  rw [←Fin.sum_univ_eq_sum_range]
  have he := (ZMod.finEquiv q).toEquiv.sum_comp χ
  cases q with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ q =>
    have hz := he.trans (MulChar.sum_eq_zero_of_ne_one hχ)
    change (∑ i : Fin (q+1), χ i) = 0 at hz
    calc
      _ = ∑ i : Fin (q+1), χ (i : Fin (q+1)) := by
        apply Finset.sum_congr rfl
        intro i hi
        congr 1
        exact Fin.cast_val_eq_self i
      _ = 0 := hz

lemma char_sum_Icc_norm_le {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (N : ℕ) : ‖∑ n ∈ Icc 1 N, χ (n : ZMod q)‖ ≤ q+1 := by
  have hr := periodic_sum_norm_le (NeZero.pos q)
    (f := fun n => χ (n : ZMod q)) (by intro n; simp)
    (char_sum_range_zero hχ) (fun n => χ.norm_le_one _) (N+1)
  have he : ∑ n ∈ range (N+1), χ (n : ZMod q) =
      χ (0 : ZMod q) + ∑ n ∈ Icc 1 N, χ (n : ZMod q) := by
    rw [Nat.range_succ_eq_Icc_zero, ←Finset.insert_Icc_add_one_left_eq_Icc (Nat.zero_le N)]
    simp
  rw [he] at hr
  calc
    _ = ‖(χ (0 : ZMod q) + ∑ n ∈ Icc 1 N, χ (n : ZMod q)) - χ 0‖ := by congr 1; ring
    _ ≤ ‖χ (0 : ZMod q) + ∑ n ∈ Icc 1 N, χ (n : ZMod q)‖ + ‖χ 0‖ := norm_sub_le _ _
    _ ≤ q+1 := add_le_add hr (χ.norm_le_one _)

noncomputable def seriesDiscrepancy (f : ℕ → ℂ) (c : ℂ) (t : ℝ) : ℂ :=
  (∑ n ∈ Icc 1 ⌊t⌋₊, f n) - c*t

lemma measurable_seriesDiscrepancy (f : ℕ → ℂ) (c : ℂ) :
    Measurable (seriesDiscrepancy f c) := by
  exact ((measurable_of_countable (fun N : ℕ => ∑ n ∈ Icc 1 N, f n)).comp
    Nat.measurable_floor).sub (measurable_const.mul Complex.continuous_ofReal.measurable)

noncomputable def regularSeries (f : ℕ → ℂ) (c : ℂ) (s : ℂ) : ℂ :=
  c+s*discrepancyTail (seriesDiscrepancy f c) 1 s

lemma regularSeries_differentiableAt {f : ℕ → ℂ} {c : ℂ} {D : ℝ} (hD : 0 ≤ D)
    (hb : ∀ t, 1 < t → ‖seriesDiscrepancy f c t‖ ≤ D) {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (regularSeries f c) s := by
  exact (differentiableAt_const c).add (differentiableAt_id.mul
    (discrepancyTail_differentiableAt zero_lt_one hD (measurable_seriesDiscrepancy f c) hb hs))

lemma regularSeries_eq_LSeries_sub {f : ℕ → ℂ} {c : ℂ} {D : ℝ}
    (hf : ∀ n, ‖f n‖ ≤ 1) (hD : 0 ≤ D)
    (hb : ∀ t, 1 < t → ‖seriesDiscrepancy f c t‖ ≤ D) {s : ℂ} (hs : 1 < s.re) :
    regularSeries f c s = LSeries f s - c/(s-1) := by
  have hO : (fun n => ∑ k ∈ Icc 1 n, ‖f k‖) =O[atTop] (fun n => (n:ℝ)^(1:ℝ)) := by
    refine isBigO_iff.mpr ⟨1, .of_forall (fun n => ?_)⟩
    simp only [Real.rpow_one, one_mul, Real.norm_eq_abs]
    rw [abs_of_nonneg (sum_nonneg (fun _ _ => norm_nonneg _))]
    calc
      _ ≤ ∑ _k ∈ Icc 1 n, (1:ℝ) := sum_le_sum (fun n _ => hf n)
      _ ≤ |(n:ℝ)| := by simp
  rw [LSeries_eq_mul_integral' f zero_le_one hs hO]
  have hiA := discrepancyTail_integrable zero_lt_one hD (measurable_seriesDiscrepancy f c) hb
    (zero_lt_one.trans hs)
  have hi := integrableOn_Ioi_cpow_of_lt (by simpa using neg_lt_neg hs : (-s).re < -1) zero_lt_one
  have he (t : ℝ) (ht : 1 < t) :
      (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * (t:ℂ)^(-(s+1)) =
      seriesDiscrepancy f c t * (t:ℂ)^(-(s+1)) + c*(t:ℂ)^(-s) := by
    have ht0 : (t:ℂ) ≠ 0 := by exact_mod_cast (zero_lt_one.trans ht).ne'
    have ht1 : (t:ℂ)*(t:ℂ)^(-(s+1)) = (t:ℂ)^(-s) := by
      nth_rw 1 [←Complex.cpow_one (t:ℂ)]
      rw [←Complex.cpow_add _ _ ht0]
      congr 1
      ring
    dsimp [seriesDiscrepancy]
    rw [sub_mul, mul_assoc c, ht1]
    ring
  have hs0 : s-1 ≠ 0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
  have hv : ∫ t in Ioi (1:ℝ), (t:ℂ)^(-s) = 1/(s-1) := by
    rw [integral_Ioi_cpow_of_lt (by simpa using neg_lt_neg hs : (-s).re < -1) zero_lt_one]
    simp only [ofReal_one, one_cpow]
    have he : -s+1 = -(s-1) := by ring
    rw [he, neg_div_neg_eq]
  have hint : (∫ t in Ioi (1:ℝ), (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * (t:ℂ)^(-(s+1))) =
      ∫ t in Ioi (1:ℝ), seriesDiscrepancy f c t * (t:ℂ)^(-(s+1)) + c*(t:ℂ)^(-s) :=
    setIntegral_congr_fun measurableSet_Ioi (fun {t} ht => he t ht)
  rw [hint,
    integral_add hiA (hi.const_mul c), integral_const_mul, hv]
  dsimp [regularSeries,discrepancyTail]
  field_simp [hs0]
  ring

lemma sum_Icc_zero_eq {f : ℕ → ℂ} (hf : f 0 = 0) (N : ℕ) :
    ∑ k ∈ Icc 0 N, f k = ∑ k ∈ Icc 1 N, f k := by
  rw [←Finset.insert_Icc_add_one_left_eq_Icc (Nat.zero_le N)]
  simp [hf]

lemma weighted_sum_abel {f : ℕ → ℂ} (hf : f 0 = 0) {N : ℕ} (hN : 1 ≤ N)
    {s : ℂ} (hs : 0 < s.re) :
    ∑ n ∈ Icc 1 N, f n * (n:ℂ)^(-s) =
      (∑ n ∈ Icc 1 N, f n)*(N:ℂ)^(-s) +
        s*∫ t in (1:ℝ)..N, (∑ n ∈ Icc 1 ⌊t⌋₊, f n)*(t:ℂ)^(-(s+1)) := by
  have hNR : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hs0 : s ≠ 0 := Complex.ne_zero_of_re_pos hs
  have hd (t:ℝ) (ht : t ∈ Set.Icc 1 (N:ℝ)) :
      HasDerivAt (fun t : ℝ => (t:ℂ)^(-s)) ((-s)*(t:ℂ)^(-(s+1))) t := by
    rw [show -(s+1) = -s-1 by ring]
    exact hasDerivAt_ofReal_cpow_const ((zero_lt_one.trans_le ht.1).ne') (neg_ne_zero.mpr hs0)
  have hcont : ContinuousOn (fun t : ℝ => (-s)*(t:ℂ)^(-(s+1))) (Set.Icc 1 (N:ℝ)) := by
    intro t ht
    exact (continuousAt_const.mul (Complex.continuousAt_ofReal_cpow_const _ _
      (.inr (zero_lt_one.trans_le ht.1).ne'))).continuousWithinAt
  have hi : IntegrableOn (deriv (fun t:ℝ => (t:ℂ)^(-s))) (Set.Icc 1 (N:ℝ)) :=
    hcont.integrableOn_Icc.congr_fun (fun t ht => (hd t ht).deriv.symm) measurableSet_Icc
  have ha := sum_mul_eq_sub_sub_integral_mul' f hN (fun t ht => (hd t (by simpa using ht)).differentiableAt) (by simpa using hi)
  have he : (insert 1 (Finset.Ioc 1 N) : Finset ℕ) = Finset.Icc 1 N := by
    ext k
    simp only [Finset.mem_insert,Finset.mem_Ioc,Finset.mem_Icc]
    omega
  have hint : (∫ t in Set.Ioc (1:ℝ) (N:ℝ),
      deriv (fun t:ℝ => (t:ℂ)^(-s)) t * ∑ k ∈ Icc 0 ⌊t⌋₊, f k) =
      (-s)*∫ t in (1:ℝ)..N, (∑ k ∈ Icc 1 ⌊t⌋₊, f k)*(t:ℂ)^(-(s+1)) := by
    rw [intervalIntegral.integral_of_le hNR, ←integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    dsimp only
    rw [(hd t ⟨ht.1.le,ht.2⟩).deriv,sum_Icc_zero_eq hf]
    ring
  simp only [Nat.cast_one, Complex.ofReal_natCast, Complex.ofReal_one] at ha
  rw [hint] at ha
  simp only [one_cpow,one_mul,sum_Icc_zero_eq hf,Finset.Icc_self,sum_singleton] at ha
  conv_lhs => rw [←he,sum_insert (by simp)]
  simp only [Nat.cast_one,one_cpow,mul_one]
  simp_rw [mul_comm (f _) ((_:ℂ)^(-s))]
  rw [ha]
  ring

lemma cpow_sub_eq_mul_intervalIntegral {N : ℝ} (hN : 1 ≤ N) (s : ℂ) :
    (N:ℂ)^(1-s)-1 = (1-s)*∫ t in (1:ℝ)..N, (t:ℂ)^(-s) := by
  by_cases hs : s = 1
  · subst s
    simp
  · have hn : (0:ℝ) ∉ Set.uIcc 1 N := by rw [Set.uIcc_of_le hN]; simp
    rw [integral_cpow (.inr ⟨by simpa using hs,hn⟩)]
    simp only [Complex.ofReal_one,one_cpow]
    have he : -s+1 = 1-s := by ring
    rw [he]
    field_simp

lemma regularSeries_cutoff {f : ℕ → ℂ} {c : ℂ} {D : ℝ} (hf : f 0 = 0)
    (hD : 0 ≤ D) (hb : ∀ t, 1 < t → ‖seriesDiscrepancy f c t‖ ≤ D)
    {N : ℕ} (hN : 1 ≤ N) {s : ℂ} (hs : 0 < s.re) :
    regularSeries f c s = (∑ n ∈ Icc 1 N, f n*(n:ℂ)^(-s)) -
      seriesDiscrepancy f c N * (N:ℂ)^(-s) +
      s*discrepancyTail (seriesDiscrepancy f c) N s -
      c*∫ t in (1:ℝ)..N, (t:ℂ)^(-s) := by
  have hNR : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hn0 : (N:ℂ) ≠ 0 := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN).ne'
  have hi := discrepancyTail_integrable zero_lt_one hD (measurable_seriesDiscrepancy f c) hb hs
  have htail := intervalIntegral.integral_Ioi_sub_Ioi hi hNR
  have hp : ∀ t ∈ Set.Icc (1:ℝ) (N:ℝ),
      (t:ℂ)*(t:ℂ)^(-(s+1)) = (t:ℂ)^(-s) := by
    intro t ht
    have ht0 : (t:ℂ) ≠ 0 := by exact_mod_cast (zero_lt_one.trans_le ht.1).ne'
    nth_rw 1 [←Complex.cpow_one (t:ℂ)]
    rw [←Complex.cpow_add _ _ ht0]
    congr 1
    ring
  have hip : IntervalIntegrable (fun t:ℝ => (t:ℂ)^(-s)) volume 1 N :=
    intervalIntegral.intervalIntegrable_cpow (.inr (by rw [Set.uIcc_of_le hNR]; simp))
  have hiA : IntervalIntegrable (fun t:ℝ => seriesDiscrepancy f c t*(t:ℂ)^(-(s+1))) volume 1 N :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hNR).mpr (hi.mono_set Set.Ioc_subset_Ioi_self)
  have hint : (∫ t in (1:ℝ)..N, (∑ n ∈ Icc 1 ⌊t⌋₊, f n)*(t:ℂ)^(-(s+1))) =
      (∫ t in (1:ℝ)..N, seriesDiscrepancy f c t*(t:ℂ)^(-(s+1))) +
        c*∫ t in (1:ℝ)..N, (t:ℂ)^(-s) := by
    rw [←intervalIntegral.integral_const_mul, ←intervalIntegral.integral_add hiA (hip.const_mul c)]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hNR] at ht
    dsimp [seriesDiscrepancy]
    rw [sub_mul,mul_assoc c,hp t ht]
    ring
  have hab := weighted_sum_abel hf hN hs
  rw [hint, ←htail] at hab
  have hpow : (N:ℂ)*(N:ℂ)^(-s) = (N:ℂ)^(1-s) := by
    nth_rw 1 [←Complex.cpow_one (N:ℂ)]
    rw [←Complex.cpow_add _ _ hn0]
    congr 1
  have hc := cpow_sub_eq_mul_intervalIntegral hNR s
  simp only [Complex.ofReal_natCast] at hc
  dsimp [regularSeries,discrepancyTail]
  rw [hab]
  simp only [seriesDiscrepancy,Nat.floor_natCast,Complex.ofReal_natCast]
  rw [sub_mul,mul_assoc c,hpow,sub_eq_iff_eq_add.mp hc]
  ring

lemma sum_cpow_norm_le {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) {ε : ℝ} (hε : 0 < ε)
    {s : ℂ} (hs : 1-ε ≤ s.re) {N : ℕ} (_hN : 1 ≤ N) :
    ‖∑ n ∈ Icc 1 N, f n*(n:ℂ)^(-s)‖ ≤
      (∑' n : ℕ, (n:ℝ)^(-1-ε)) * (N:ℝ)^(2*ε) := by
  have hsumm : Summable (fun n : ℕ => (n:ℝ)^(-1-ε)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  calc
    _ ≤ ∑ n ∈ Icc 1 N, ‖f n*(n:ℂ)^(-s)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Icc 1 N, (n:ℝ)^(-1-ε)*(N:ℝ)^(2*ε) := by
      apply sum_le_sum
      intro n hn
      have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (mem_Icc.mp hn).1
      have hnN : (n:ℝ) ≤ N := by exact_mod_cast (mem_Icc.mp hn).2
      have hn0 := zero_lt_one.trans_le hn1
      rw [norm_mul]
      have hn0C : (n:ℂ) = ((n:ℝ):ℂ) := by simp
      rw [hn0C,Complex.norm_cpow_eq_rpow_re_of_pos hn0,Complex.neg_re]
      calc
        _ ≤ (n:ℝ)^(-s.re) := by
          simpa using mul_le_mul_of_nonneg_right (hf n) (Real.rpow_nonneg hn0.le (-s.re))
        _ ≤ (n:ℝ)^(-1+ε) := Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
        _ = (n:ℝ)^(-1-ε)*(n:ℝ)^(2*ε) := by rw [←Real.rpow_add hn0]; congr 1; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hn0.le hnN (by positivity))
          (Real.rpow_nonneg hn0.le _)
    _ = (∑ n ∈ Icc 1 N, (n:ℝ)^(-1-ε))*(N:ℝ)^(2*ε) := by rw [sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (hsumm.sum_le_tsum _ (fun n _ => Real.rpow_nonneg n.cast_nonneg _))
      (Real.rpow_nonneg N.cast_nonneg _)

lemma norm_intervalIntegral_cpow_le {ε N : ℝ} (hε : 0 < ε) (hN : 1 ≤ N)
    {s : ℂ} (hs : 1-ε ≤ s.re) :
    ‖∫ t in (1:ℝ)..N, (t:ℂ)^(-s)‖ ≤ N^ε/ε := by
  have hn : (0:ℝ) ∉ Set.uIcc 1 N := by rw [Set.uIcc_of_le hN]; simp
  calc
    _ ≤ ∫ t in (1:ℝ)..N, t^(-1+ε) := by
      apply intervalIntegral.norm_integral_le_of_norm_le hN
        (.of_forall (fun t ht => ?_)) (intervalIntegral.intervalIntegrable_rpow (.inr hn))
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans ht.1),Complex.neg_re]
      exact Real.rpow_le_rpow_of_exponent_le ht.1.le (by linarith)
    _ = (N^ε-1)/ε := by
      rw [integral_rpow (.inl (by linarith : -1 < -1+ε))]
      have he : -1+ε+1 = ε := by ring
      simp [he]
    _ ≤ _ := div_le_div_of_nonneg_right (by linarith) hε.le

lemma regularSeries_norm_cutoff {f : ℕ → ℂ} {c : ℂ} {D ε : ℝ}
    (hf0 : f 0 = 0) (hf : ∀ n, ‖f n‖ ≤ 1) (hc : ‖c‖ ≤ 1) (hD : 0 ≤ D)
    (hb : ∀ t, 1 ≤ t → ‖seriesDiscrepancy f c t‖ ≤ D)
    (hε : 0 < ε) (hε1 : ε ≤ 1/2) {N : ℕ} (hN : 1 ≤ N) {s : ℂ}
    (hs : 1-ε ≤ s.re) (hNs : D*(1+‖s‖) ≤ N) :
    ‖regularSeries f c s‖ ≤ ((∑' n : ℕ, (n:ℝ)^(-1-ε))+2+1/ε)*(N:ℝ)^(2*ε) := by
  have hNR : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hNP := zero_lt_one.trans_le hNR
  have hs0 : 0 < s.re := by linarith
  have hhalf : 1/2 ≤ s.re := by linarith
  have htail := discrepancyTail_norm_le hNP hD (measurable_seriesDiscrepancy f c)
    (fun t ht => hb t (hNR.trans ht.le)) hs0
  have hboundary : ‖seriesDiscrepancy f c N * (N:ℂ)^(-s)‖ ≤ D*(N:ℝ)^(-s.re) := by
    rw [norm_mul, ←Complex.ofReal_natCast N, Complex.norm_cpow_eq_rpow_re_of_pos hNP,Complex.neg_re]
    exact mul_le_mul_of_nonneg_right (hb _ hNR) (Real.rpow_nonneg hNP.le _)
  have hsmall : ‖seriesDiscrepancy f c N * (N:ℂ)^(-s)‖ +
      ‖s*discrepancyTail (seriesDiscrepancy f c) N s‖ ≤ 2*(N:ℝ)^ε := by
    have ht : D*(N:ℝ)^(-s.re)/s.re ≤ 2*D*(N:ℝ)^(-s.re) := by
      apply (div_le_iff₀ hs0).mpr
      have hn := Real.rpow_nonneg hNP.le (-s.re)
      nlinarith [mul_nonneg hD hn,mul_nonneg (mul_nonneg hD hn) (sub_nonneg.mpr hhalf)]
    have he : (N:ℝ)*(N:ℝ)^(-s.re) ≤ (N:ℝ)^ε := by
      nth_rw 1 [←Real.rpow_one (N:ℝ)]
      rw [←Real.rpow_add hNP]
      apply Real.rpow_le_rpow_of_exponent_le hNR
      linarith
    calc
      _ ≤ D*(N:ℝ)^(-s.re) + ‖s‖*(2*D*(N:ℝ)^(-s.re)) := by
        nth_rw 2 [norm_mul]
        exact add_le_add hboundary (mul_le_mul_of_nonneg_left (htail.trans ht) (norm_nonneg s))
      _ ≤ 2*(N:ℝ)*(N:ℝ)^(-s.re) := by
        have hcoeff : D+2*‖s‖*D ≤ 2*(N:ℝ) := by nlinarith
        nlinarith [mul_nonneg (sub_nonneg.mpr hcoeff) (Real.rpow_nonneg hNP.le (-s.re))]
      _ ≤ _ := by nlinarith [he]
  have hi : ‖c*∫ t in (1:ℝ)..N, (t:ℂ)^(-s)‖ ≤ (N:ℝ)^ε/ε := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right hc (norm_nonneg _)).trans (by
      simpa using norm_intervalIntegral_cpow_le hε hNR hs)
  have hp : (N:ℝ)^ε ≤ (N:ℝ)^(2*ε) := Real.rpow_le_rpow_of_exponent_le hNR (by linarith)
  rw [regularSeries_cutoff hf0 hD (fun t ht => hb t ht.le) hN hs0]
  calc
    _ ≤ ‖∑ n ∈ Icc 1 N, f n*(n:ℂ)^(-s)‖ +
        (‖seriesDiscrepancy f c N * (N:ℂ)^(-s)‖ +
        ‖s*discrepancyTail (seriesDiscrepancy f c) N s‖) +
        ‖c*∫ t in (1:ℝ)..N, (t:ℂ)^(-s)‖ := by
      calc
        _ ≤ ‖(∑ n ∈ Icc 1 N, f n*(n:ℂ)^(-s)) - seriesDiscrepancy f c N * (N:ℂ)^(-s) +
             s*discrepancyTail (seriesDiscrepancy f c) N s‖ +
             ‖c*∫ t in (1:ℝ)..N, (t:ℂ)^(-s)‖ := norm_sub_le _ _
        _ ≤ (‖(∑ n ∈ Icc 1 N, f n*(n:ℂ)^(-s)) - seriesDiscrepancy f c N * (N:ℂ)^(-s)‖ +
             ‖s*discrepancyTail (seriesDiscrepancy f c) N s‖) +
             ‖c*∫ t in (1:ℝ)..N, (t:ℂ)^(-s)‖ := add_le_add (norm_add_le _ _) le_rfl
        _ ≤ _ := by
          have htri := norm_sub_le (∑ n ∈ Icc 1 N, f n*(n:ℂ)^(-s)) (seriesDiscrepancy f c N * (N:ℂ)^(-s))
          linarith
    _ ≤ ((∑' n : ℕ, (n:ℝ)^(-1-ε)))*(N:ℝ)^(2*ε) +
      2*(N:ℝ)^ε+(N:ℝ)^ε/ε := add_le_add (add_le_add (sum_cpow_norm_le hf hε hs hN) hsmall) hi
    _ ≤ ((∑' n : ℕ, (n:ℝ)^(-1-ε)))*(N:ℝ)^(2*ε) +
      2*(N:ℝ)^(2*ε)+(N:ℝ)^(2*ε)/ε := by
        linarith [div_le_div_of_nonneg_right hp hε.le]
    _ = _ := by ring

lemma regularSeries_norm_small_power {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1/2) :
    ∃ K : ℝ, 0 < K ∧ ∀ (f : ℕ → ℂ) (c : ℂ) (D : ℝ),
      f 0 = 0 → (∀ n, ‖f n‖ ≤ 1) → ‖c‖ ≤ 1 → 0 ≤ D →
      (∀ t, 1 ≤ t → ‖seriesDiscrepancy f c t‖ ≤ D) →
      ∀ s : ℂ, 1-ε ≤ s.re →
      ‖regularSeries f c s‖ ≤ K*((D+1)*(‖s‖+2))^(2*ε) := by
  let K₀ := (∑' n : ℕ, (n:ℝ)^(-1-ε))+2+1/ε
  have hK₀ : 0 < K₀ := by
    have ht : 0 ≤ ∑' n : ℕ, (n:ℝ)^(-1-ε) := tsum_nonneg (fun n => Real.rpow_nonneg n.cast_nonneg _)
    dsimp [K₀]
    positivity
  refine ⟨K₀*2^(2*ε), by positivity, ?_⟩
  intro f c D hf0 hf hc hD hb s hs
  let B := (D+1)*(‖s‖+2)
  have hB : 1 ≤ B := by dsimp [B]; nlinarith [norm_nonneg s]
  let N := ⌈B⌉₊
  have hBN : B ≤ (N:ℝ) := Nat.le_ceil B
  have hN : 1 ≤ N := by exact_mod_cast (hB.trans hBN)
  have hN2 : (N:ℝ) ≤ 2*B := by
    have := Nat.ceil_lt_add_one (zero_lt_one.trans_le hB).le
    change (N:ℝ) < B+1 at this
    linarith
  have hcut := regularSeries_norm_cutoff hf0 hf hc hD hb hε hε1 hN hs
    (show D*(1+‖s‖) ≤ (N:ℝ) from (by dsimp [B] at hBN; nlinarith [norm_nonneg s]))
  calc
    _ ≤ K₀*(N:ℝ)^(2*ε) := hcut
    _ ≤ K₀*(2*B)^(2*ε) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow N.cast_nonneg hN2 (by positivity)) hK₀.le
    _ = _ := by rw [Real.mul_rpow (by norm_num) (by linarith : 0 ≤ B)]; ring

def positiveCoefficients (f : ℕ → ℂ) (n : ℕ) : ℂ := if n = 0 then 0 else f n

lemma positiveCoefficients_zero (f : ℕ → ℂ) : positiveCoefficients f 0 = 0 := by simp [positiveCoefficients]

lemma positiveCoefficients_norm_le {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) (n : ℕ) :
    ‖positiveCoefficients f n‖ ≤ 1 := by
  by_cases hn : n=0 <;> simp [positiveCoefficients,hn,hf]

lemma sum_positiveCoefficients (f : ℕ → ℂ) (N : ℕ) :
    ∑ n ∈ Icc 1 N, positiveCoefficients f n = ∑ n ∈ Icc 1 N, f n := by
  apply sum_congr rfl
  intro n hn
  simp [positiveCoefficients,show n ≠ 0 from Nat.ne_of_gt (mem_Icc.mp hn).1]

lemma LSeries_positiveCoefficients (f : ℕ → ℂ) (s : ℂ) :
    LSeries (positiveCoefficients f) s = LSeries f s := by
  apply LSeries_congr
  intro n hn
  simp [positiveCoefficients,hn]

lemma discrepancy_character_bound {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (t : ℝ) :
    ‖seriesDiscrepancy (positiveCoefficients (fun n => χ (n : ZMod q))) 0 t‖ ≤ q+1 := by
  simpa [seriesDiscrepancy,sum_positiveCoefficients] using char_sum_Icc_norm_le hχ ⌊t⌋₊

lemma discrepancy_constant_bound {t : ℝ} (ht : 1 ≤ t) :
    ‖seriesDiscrepancy (positiveCoefficients (fun _ => 1)) 1 t‖ ≤ 1 := by
  simp only [seriesDiscrepancy,sum_positiveCoefficients,Finset.sum_const,nsmul_eq_mul,
    mul_one,Nat.card_Icc,Nat.add_sub_cancel,one_mul]
  rw [←Complex.ofReal_natCast,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
  have ht0 := (show (0:ℝ) ≤ t by linarith)
  rw [abs_of_nonpos (sub_nonpos.mpr (Nat.floor_le ht0))]
  have := Nat.lt_floor_add_one t
  linarith

lemma regularSeries_character_eq {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    regularSeries (positiveCoefficients (fun n => χ (n : ZMod q))) 0 s = χ.LFunction s := by
  let f := positiveCoefficients (fun n => χ (n : ZMod q))
  have hfrac : AnalyticOnNhd ℂ (regularSeries f 0) {s : ℂ | 0 < s.re} := by
    apply DifferentiableOn.analyticOnNhd ?_ (show IsOpen {z : ℂ | 0 < z.re} from isOpen_lt continuous_const Complex.continuous_re)
    intro s hs
    exact (regularSeries_differentiableAt (by positivity : (0:ℝ) ≤ q+1)
      (fun t _ => discrepancy_character_bound hχ t) hs).differentiableWithinAt
  have hL : AnalyticOnNhd ℂ χ.LFunction {s : ℂ | 0 < s.re} :=
    fun s _ => (DirichletCharacter.differentiable_LFunction hχ).analyticAt s
  have he : regularSeries f 0 =ᶠ[𝓝 (2:ℂ)] χ.LFunction := by
    filter_upwards [(continuous_re.tendsto (2:ℂ)).eventually (lt_mem_nhds (by norm_num : (1:ℝ) < (2:ℂ).re))] with z hz
    rw [regularSeries_eq_LSeries_sub (positiveCoefficients_norm_le (fun n => χ.norm_le_one _))
      (by positivity : (0:ℝ) ≤ q+1) (fun t _ => discrepancy_character_bound hχ t) hz]
    simp only [zero_div,sub_zero]
    rw [LSeries_positiveCoefficients,DirichletCharacter.LFunction_eq_LSeries χ hz]
  exact hfrac.eqOn_of_preconnected_of_eventuallyEq hL (convex_halfSpace_re_gt 0).isPreconnected
    (show (2:ℂ) ∈ {s:ℂ | 0<s.re} by norm_num) he hs

lemma LFunction_norm_small_power {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1/2) :
    ∃ K : ℝ, 0 < K ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ s : ℂ, 1-ε ≤ s.re →
      ‖χ.LFunction s‖ ≤ K*((q+2)*(‖s‖+2))^(2*ε) := by
  obtain ⟨K,hK,h⟩ := regularSeries_norm_small_power hε hε1
  refine ⟨K,hK,fun q _ χ hχ s hs => ?_⟩
  have he := h _ 0 (q+1) (positiveCoefficients_zero _) (positiveCoefficients_norm_le (fun n => χ.norm_le_one _))
    (by simp) (by positivity) (fun t _ => discrepancy_character_bound hχ t) s hs
  rw [regularSeries_character_eq hχ (by linarith)] at he
  convert he using 1
  congr 3
  ring

lemma regularSeries_deriv_norm_small_power {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1/2) :
    ∃ K : ℝ, 0 < K ∧ ∀ (f : ℕ → ℂ) (c : ℂ) (D : ℝ),
      f 0 = 0 → (∀ n, ‖f n‖ ≤ 1) → ‖c‖ ≤ 1 → 0 ≤ D →
      (∀ t, 1 ≤ t → ‖seriesDiscrepancy f c t‖ ≤ D) →
      ∀ s : ℂ, 1-ε/2 ≤ s.re →
      ‖deriv (regularSeries f c) s‖ ≤ K*((D+1)*(‖s‖+2))^(2*ε) := by
  obtain ⟨K,hK,h⟩ := regularSeries_norm_small_power hε hε1
  refine ⟨K*2^(2*ε)/(ε/2),by positivity,?_⟩
  intro f c D hf0 hf hc hD hb s hs
  have hε2 : 0 < ε/2 := by positivity
  have hre (z:ℂ) (hz : dist z s ≤ ε/2) : 1-ε ≤ z.re := by
    have hd := Complex.re_le_norm (s-z)
    rw [Complex.sub_re,←dist_eq_norm,dist_comm] at hd
    linarith
  have hd : DiffContOnCl ℂ (regularSeries f c) (Metric.ball s (ε/2)) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball _ hε2.ne']
    intro z hz
    exact (regularSeries_differentiableAt hD (fun t ht => hb t ht.le) (by
      have := hre z (Metric.mem_closedBall.mp hz)
      linarith)).differentiableWithinAt
  have hbnd (z:ℂ) (hz : z ∈ Metric.sphere s (ε/2)) :
      ‖regularSeries f c z‖ ≤ K*2^(2*ε)*((D+1)*(‖s‖+2))^(2*ε) := by
    have hdist := Metric.mem_sphere.mp hz
    have hzR := hre z hdist.le
    have hnorm : ‖z‖+2 ≤ 2*(‖s‖+2) := by
      have : ‖z‖ ≤ dist z s + ‖s‖ := by simpa [dist_eq_norm] using norm_add_le (z-s) s
      rw [hdist] at this
      nlinarith [norm_nonneg s]
    calc
      _ ≤ K*((D+1)*(‖z‖+2))^(2*ε) := h f c D hf0 hf hc hD hb z hzR
      _ ≤ K*(2*((D+1)*(‖s‖+2)))^(2*ε) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by positivity) (by nlinarith) (by positivity)) hK.le
      _ = _ := by rw [Real.mul_rpow (by positivity) (by positivity)]; ring
  have hder := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hε2 hd hbnd
  convert hder using 1
  ring

end LargePrimeGaps
end OAI

-- Source module: TaylorBounds
namespace OAI
namespace LargePrimeGaps
open Filter
open Set Filter MeasureTheory
open scoped Topology ContDiff
open Asymptotics
open scoped Classical
open scoped ContDiff
open Topology
open scoped Convolution ContDiff Pointwise
open scoped ComplexConjugate
open Filter Topology
open Complex Filter Topology
open Complex Filter Topology Set MeasureTheory Asymptotics
open Finset
open Complex Filter Topology Finset
lemma power_series_tail_bound {a : ℕ → ℝ} {M r z : ℝ} (_hM : 0 ≤ M)
    (hr : 0 < r) (hz : 0 ≤ z) (hzr : z < r)
    (hb : ∀ n, |a n| ≤ M/r^n) (N : ℕ) :
    |∑' n : ℕ, a (n+N)*z^(n+N)| ≤ M*(z/r)^N/(1-z/r) := by
  have hρ : 0 ≤ z/r := div_nonneg hz hr.le
  have hρ1 : z/r < 1 := (div_lt_one hr).mpr hzr
  have hg := (summable_geometric_of_lt_one hρ hρ1).mul_left (M*(z/r)^N)
  have hbound (n : ℕ) : ‖a (n+N)*z^(n+N)‖ ≤ (M*(z/r)^N)*(z/r)^n := by
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (pow_nonneg hz _)]
    calc
      _ ≤ (M/r^(n+N))*z^(n+N) := mul_le_mul_of_nonneg_right (hb _) (pow_nonneg hz _)
      _ = M*(z/r)^(n+N) := by rw [div_pow]; ring
      _ = _ := by rw [pow_add]; ring
  have hn := hg.of_nonneg_of_le (fun n => norm_nonneg _) hbound
  calc
    _ = ‖∑' n : ℕ, a (n+N)*z^(n+N)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∑' n : ℕ, ‖a (n+N)*z^(n+N)‖ := norm_tsum_le_tsum_norm hn
    _ ≤ ∑' n : ℕ, (M*(z/r)^N)*(z/r)^n := hn.tsum_le_tsum hbound hg
    _ = _ := by rw [tsum_mul_left,tsum_geometric_of_lt_one hρ hρ1]; rfl

lemma residue_lower_bound_of_taylor {a : ℕ → ℝ} {R M r z : ℝ} {N : ℕ}
    (hM : 0 ≤ M) (hr : 0 < r) (hz : 1 < z) (hzr : z < r)
    (hb : ∀ n, |a n| ≤ M/r^n) (ha0 : 1-R ≤ a 0)
    (ha : ∀ n, -R ≤ a n) (hN : 1 ≤ N)
    (hvalue : (∑' n : ℕ, a n*z^n) ≤ R/(z-1))
    (htail : M*(z/r)^N/(1-z/r) ≤ 1/2) :
    (z-1)/2 ≤ R*z^N := by
  have heach : ∀ n, (if n=0 then 1 else (0:ℝ)) - R*z^n ≤ a n*z^n := by
    intro n
    by_cases hn : n=0
    · simpa [hn] using ha0
    · simp only [hn,↓reduceIte,zero_sub]
      nlinarith [mul_le_mul_of_nonneg_right (ha n) (pow_nonneg (zero_lt_one.trans hz).le n)]
  have hsum := Finset.sum_le_sum (s := range N) (fun n _ => heach n)
  have hzero : (∑ n ∈ range N, if n=0 then 1 else (0:ℝ)) = 1 := by
    simp [show 0 < N by omega]
  rw [sum_sub_distrib,hzero,←mul_sum] at hsum
  have htail' := power_series_tail_bound hM hr (zero_lt_one.trans hz).le hzr hb N
  have ht : -(1/2:ℝ) ≤ ∑' n : ℕ, a (n+N)*z^(n+N) := by
    have := (abs_le.mp (htail'.trans htail)).1
    linarith
  have hs : Summable (fun n : ℕ => a n*z^n) := by
    have hρ : 0 ≤ z/r := by positivity
    have hρ1 : z/r < 1 := (div_lt_one hr).mpr hzr
    apply ((summable_geometric_of_lt_one hρ hρ1).mul_left M).of_norm_bounded
    intro n
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (pow_nonneg (zero_lt_one.trans hz).le _)]
    calc
      _ ≤ (M/r^n)*z^n := mul_le_mul_of_nonneg_right (hb _) (pow_nonneg (zero_lt_one.trans hz).le _)
      _ = M*(z/r)^n := by rw [div_mul_eq_mul_div,div_pow]; ring
  have hdecomp := hs.sum_add_tsum_nat_add N
  have hm : 1/2 ≤ R/(z-1)+R*(∑ n ∈ range N, z^n) := by linarith
  have hgeom := geom_sum_mul z N
  have hv := (le_div_iff₀ (sub_pos.mpr hz)).mp
    (show (1/2:ℝ) ≤ (R+R*(∑ n ∈ range N, z^n)*(z-1))/(z-1) from by
      rw [add_div,mul_div_cancel_right₀ _ (sub_pos.mpr hz).ne']
      exact hm)
  have hid : R+R*(∑ n ∈ range N, z^n)*(z-1) = R*z^N := by
    rw [mul_assoc R, hgeom]
    ring
  rw [hid] at hv
  linarith

noncomputable def signedTaylorCoeff (H : ℂ → ℂ) (n : ℕ) : ℝ :=
  (((-1:ℂ)^n)*(n.factorial:ℂ)⁻¹*iteratedDeriv n H 2).re

lemma signedTaylorCoeff_hasSum {H : ℂ → ℂ} {r z : ℝ}
    (hf : DifferentiableOn ℂ H (Metric.ball 2 r)) (hz : |z| < r) :
    HasSum (fun n => signedTaylorCoeff H n*z^n) (H ((2-z:ℝ):ℂ)).re := by
  have hmem : ((2-z:ℝ):ℂ) ∈ Metric.ball (2:ℂ) r := by
    rw [Metric.mem_ball,dist_eq_norm]
    have he : ((2-z:ℝ):ℂ)-(2:ℂ) = -(z:ℂ) := by push_cast; ring
    simpa [he,Complex.norm_real,Real.norm_eq_abs] using hz
  have hs := (Complex.hasSum_taylorSeries_on_ball hf hmem).map Complex.reCLM Complex.continuous_re
  change HasSum (fun n => ((n.factorial:ℂ)⁻¹ *
    ((((2-z:ℝ):ℂ)-2)^n * iteratedDeriv n H 2)).re) (H ((2-z:ℝ):ℂ)).re at hs
  convert hs using 1
  funext n
  dsimp [signedTaylorCoeff]
  have he : ((2-z:ℝ):ℂ)-(2:ℂ) = -(z:ℂ) := by push_cast; ring
  rw [he, show (-(z:ℂ))^n = (-1:ℂ)^n * (z:ℂ)^n by rw [←mul_pow]; congr 1; ring]
  have hmul : (n.factorial:ℂ)⁻¹*((-1:ℂ)^n*(z:ℂ)^n*iteratedDeriv n H 2) =
      ((-1:ℂ)^n*(n.factorial:ℂ)⁻¹*iteratedDeriv n H 2)*(z:ℂ)^n := by ring
  rw [hmul]
  simp only [←Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    mul_zero,sub_zero]

lemma signedTaylorCoeff_norm_bound {H : ℂ → ℂ} {r M : ℝ} (hr : 0 < r)
    (hf : DiffContOnCl ℂ H (Metric.ball 2 r))
    (hb : ∀ s ∈ Metric.sphere 2 r, ‖H s‖ ≤ M) (n : ℕ) :
    |signedTaylorCoeff H n| ≤ M/r^n := by
  have hder := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hr hf hb
  have hfact : (n.factorial:ℝ) ≠ 0 := by positivity
  calc
    _ ≤ ‖(-1:ℂ)^n*(n.factorial:ℂ)⁻¹*iteratedDeriv n H 2‖ := Complex.abs_re_le_norm _
    _ = (n.factorial:ℝ)⁻¹*‖iteratedDeriv n H 2‖ := by simp [norm_pow]
    _ ≤ (n.factorial:ℝ)⁻¹*((n.factorial:ℝ)*M/r^n) := by gcongr
    _ = _ := by field_simp

lemma signedTaylorCoeff_pole (R : ℝ) (n : ℕ) :
    signedTaylorCoeff (fun s : ℂ => (R:ℂ)/(s-1)) n = R := by
  unfold signedTaylorCoeff
  simp only [div_eq_mul_inv,iteratedDeriv_const_mul_field]
  have hi : iteratedDeriv n (fun s : ℂ => (s-1)⁻¹) 2 = (-1:ℂ)^n*n.factorial := by
    rw [iteratedDeriv_eq_iterate]
    simpa only [one_mul,one_pow, show (2:ℂ)-1=1 by norm_num, one_zpow,mul_one] using
      congrFun (iter_deriv_inv_linear_sub n (1:ℂ) 1) 2
  rw [hi]
  have hf : (n.factorial:ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hp : (-1:ℂ)^n*(-1:ℂ)^n = 1 := by rw [←mul_pow]; simp
  have he : (-1:ℂ)^n*(n.factorial:ℂ)⁻¹*((R:ℂ)*((-1:ℂ)^n*n.factorial)) = R := by
    calc
      _ = ((-1:ℂ)^n*(-1:ℂ)^n)*(R:ℂ)*((n.factorial:ℂ)⁻¹*n.factorial) := by ring
      _ = _ := by rw [hp,inv_mul_cancel₀ hf]; ring
  rw [he,Complex.ofReal_re]

lemma signedTaylorCoeff_sub {F G : ℂ → ℂ} (hF : AnalyticAt ℂ F 2)
    (hG : AnalyticAt ℂ G 2) (n : ℕ) :
    signedTaylorCoeff (fun s => F s-G s) n = signedTaylorCoeff F n-signedTaylorCoeff G n := by
  unfold signedTaylorCoeff
  have hd := iteratedDeriv_sub (n:=n) hF.contDiffAt hG.contDiffAt
  change iteratedDeriv n (fun s => F s-G s) 2 = _ at hd
  rw [hd,mul_sub,Complex.sub_re]

open scoped ComplexOrder in
lemma signedTaylorCoeff_LSeries_nonneg {a : ℕ → ℂ} (ha : ∀ n, 0 ≤ a n)
    (hc : LSeries.abscissaOfAbsConv a < (2:ℝ)) (n : ℕ) :
    0 ≤ signedTaylorCoeff (LSeries a) n := by
  have h := LSeries.iteratedDeriv_alternating ha hc n
  have hf : (0:ℝ) ≤ (n.factorial:ℝ)⁻¹ := by positivity
  have hr := (Complex.nonneg_iff.mp h).1
  unfold signedTaylorCoeff
  have he : (-1:ℂ)^n*(n.factorial:ℂ)⁻¹*iteratedDeriv n (LSeries a) 2 =
      (n.factorial:ℂ)⁻¹*((-1:ℂ)^n*iteratedDeriv n (LSeries a) 2) := by ring
  rw [he]
  simpa using mul_nonneg hf hr

open scoped ComplexOrder in
lemma LSeries_two_re_ge_one {a : ℕ → ℂ} (ha : ∀ n, 0 ≤ a n)
    (ha1 : 1 ≤ a 1) (hc : LSeries.abscissaOfAbsConv a < (2:ℝ)) :
    1 ≤ (LSeries a 2).re := by
  have hs : LSeriesSummable a 2 := LSeriesSummable_of_abscissaOfAbsConv_lt_re (by simpa using hc)
  have hl := hs.le_tsum 1 (fun n _ => LSeries.term_nonneg (ha n) 2)
  have hterm : LSeries.term a 2 1 = a 1 := by simp
  rw [hterm] at hl
  exact (Complex.le_def.mp (ha1.trans hl)).1

open scoped ComplexOrder in
set_option maxHeartbeats 800000 in
lemma signedTaylorCoeff_regular_nonneg {H : ℂ → ℂ} {a : ℕ → ℂ} {R : ℝ}
    (ha : ∀ n, 0 ≤ a n) (ha1 : 1 ≤ a 1)
    (hc : LSeries.abscissaOfAbsConv a < (2:ℝ))
    (he : H =ᶠ[𝓝 (2:ℂ)] fun s => LSeries a s-(R:ℂ)/(s-1)) :
    1-R ≤ (H 2).re ∧ ∀ n, -R ≤ signedTaylorCoeff H n := by
  have hL : AnalyticAt ℂ (LSeries a) 2 := LSeries_analyticOnNhd a 2 (by simpa using hc)
  have hP : AnalyticAt ℂ (fun s : ℂ => (R:ℂ)/(s-1)) 2 :=
    analyticAt_const.div (analyticAt_id.sub analyticAt_const) (by norm_num)
  constructor
  · rw [he.self_of_nhds]
    have h := LSeries_two_re_ge_one ha ha1 hc
    simp only [show (2:ℂ)-1=1 by norm_num,div_one,Complex.sub_re,Complex.ofReal_re]
    linarith
  · intro n
    unfold signedTaylorCoeff
    rw [he.iteratedDeriv_eq]
    change -R ≤ signedTaylorCoeff (fun s => LSeries a s-(R:ℂ)/(s-1)) n
    rw [signedTaylorCoeff_sub hL hP,signedTaylorCoeff_pole]
    linarith [signedTaylorCoeff_LSeries_nonneg ha hc n]

lemma residue_polynomial_lower {a : ℕ → ℝ} {R A Q z ε : ℝ}
    (hA : 0 ≤ A) (hQ : 2 ≤ Q) (hQA : 12*A ≤ Q)
    (hz : 1 < z) (hz1 : z ≤ 5/4) (hzε : 60*(z-1) ≤ ε)
    (hb : ∀ n, |a n| ≤ (A*Q^4)/(3/2)^n)
    (ha0 : 1-R ≤ a 0) (ha : ∀ n, -R ≤ a n)
    (hv : (∑' n : ℕ, a n*z^n) ≤ R/(z-1)) :
    ((z-1)/(2*z))*Q^(-ε) ≤ R := by
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  have hlogQ : 0 < Real.log Q := Real.log_pos (by linarith)
  have hz0 : 0 < z := by linarith
  have hlogz : 0 < Real.log z := Real.log_pos hz
  let N : ℕ := ⌈60*Real.log Q⌉₊
  have hNlo : 60*Real.log Q ≤ (N:ℝ) := Nat.le_ceil _
  have hNhi : (N:ℝ) < 60*Real.log Q+1 := Nat.ceil_lt_add_one (by positivity)
  have hN : 1 ≤ N := by
    have : 0 < (N:ℝ) := lt_of_lt_of_le (by positivity) hNlo
    exact_mod_cast (show 1 ≤ N from Nat.one_le_iff_ne_zero.mpr (by exact_mod_cast this.ne'))
  have hρ : 0 ≤ z/(3/2) := by positivity
  have hρ1 : z/(3/2) ≤ 5/6 := by linarith
  have hlogρ : Real.log (5/6:ℝ) ≤ -(1/6:ℝ) := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 5/6)
    linarith
  have hdecay : (z/(3/2))^N ≤ Q^(-10:ℝ) := by
    calc
      _ ≤ (5/6:ℝ)^N := pow_le_pow_left₀ hρ hρ1 N
      _ = Real.exp (Real.log (5/6:ℝ)*(N:ℝ)) := by
        rw [←Real.rpow_natCast,Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 5/6)]
      _ ≤ Real.exp (Real.log Q*(-10)) := by
        apply Real.exp_le_exp.mpr
        have hN0 : (0:ℝ) ≤ N := Nat.cast_nonneg N
        nlinarith [mul_le_mul_of_nonneg_right hlogρ hN0]
      _ = _ := (Real.rpow_def_of_pos hQ0 _).symm
  have htail : (A*Q^4)*(z/(3/2))^N/(1-z/(3/2)) ≤ 1/2 := by
    have hden : 0 < 1-z/(3/2) := by linarith
    have hpow : Q^4*Q^(-10:ℝ) ≤ Q⁻¹ := by
      calc
        _ = Q^(-6:ℝ) := by
          rw [←Real.rpow_natCast,←Real.rpow_add hQ0]
          norm_num
        _ ≤ Q^(-1:ℝ) := Real.rpow_le_rpow_of_exponent_le hQ1 (by norm_num)
        _ = Q⁻¹ := Real.rpow_neg_one Q
    have hp : (A*Q^4)*(z/(3/2))^N ≤ A/Q := by
      calc
        _ ≤ (A*Q^4)*Q^(-10:ℝ) := mul_le_mul_of_nonneg_left hdecay (by positivity)
        _ ≤ A*Q⁻¹ := by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hpow hA
        _ = _ := by rw [div_eq_mul_inv]
    have hAQ : A/Q ≤ 1/12 := (div_le_iff₀ hQ0).mpr (by linarith)
    apply (div_le_iff₀ hden).mpr
    nlinarith
  have hres := residue_lower_bound_of_taylor (by positivity : (0:ℝ) ≤ A*Q^4)
    (by norm_num : (0:ℝ) < 3/2) hz (by linarith : z < 3/2) hb ha0 ha hN hv htail
  have hzpow : z^N ≤ z*Q^ε := by
    have hlogz' : 60*Real.log z ≤ ε := by
      have := Real.log_le_sub_one_of_pos hz0
      linarith
    calc
      _ = Real.exp (Real.log z*(N:ℝ)) := by rw [←Real.rpow_natCast,Real.rpow_def_of_pos hz0]
      _ ≤ Real.exp (Real.log z+(Real.log Q)*ε) := by
        apply Real.exp_le_exp.mpr
        have h1 := mul_le_mul_of_nonneg_left hNhi.le hlogz.le
        have h2 := mul_le_mul_of_nonneg_left hlogz' hlogQ.le
        nlinarith
      _ = _ := by rw [Real.exp_add,Real.exp_log hz0,Real.rpow_def_of_pos hQ0]
  have hR : 0 ≤ R := by
    by_contra! h
    have := mul_neg_of_neg_of_pos h (pow_pos hz0 N)
    linarith
  have hres' : (z-1)/2 ≤ R*(z*Q^ε) := hres.trans (mul_le_mul_of_nonneg_left hzpow hR)
  rw [Real.rpow_neg hQ0.le,←div_eq_mul_inv]
  apply (div_le_iff₀ (Real.rpow_pos_of_pos hQ0 ε)).mpr
  apply (div_le_iff₀ (by positivity : (0:ℝ) < 2*z)).mpr
  nlinarith

open Complex Filter Topology Finset Set MeasureTheory
noncomputable def zetaRegular : ℂ → ℂ :=
  regularSeries (positiveCoefficients (fun _ => 1)) 1

lemma zetaRegular_differentiableAt {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ zetaRegular s :=
  regularSeries_differentiableAt zero_le_one (fun _ ht => discrepancy_constant_bound ht.le) hs

lemma zetaRegular_eq_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    zetaRegular s = riemannZeta s-1/(s-1) := by
  rw [zetaRegular,regularSeries_eq_LSeries_sub (positiveCoefficients_norm_le (by simp))
    zero_le_one (fun _ ht => discrepancy_constant_bound ht.le) hs,LSeries_positiveCoefficients]
  rw [show (fun _ : ℕ => (1:ℂ)) = 1 from rfl,LSeries_one_eq_riemannZeta hs]

lemma poleRemovedZeta_eq {s : ℂ} (hs : 0 < s.re) :
    DirichletCharacter.LFunctionTrivChar₁ 1 s = (s-1)*zetaRegular s+1 := by
  have hF : AnalyticOnNhd ℂ (DirichletCharacter.LFunctionTrivChar₁ 1) {s : ℂ | 0 < s.re} :=
    fun z _ => (DirichletCharacter.differentiable_LFunctionTrivChar₁ 1).analyticAt z
  have hG : AnalyticOnNhd ℂ (fun s : ℂ => (s-1)*zetaRegular s+1) {s : ℂ | 0 < s.re} := by
    apply DifferentiableOn.analyticOnNhd ?_ (show IsOpen {z : ℂ | 0 < z.re} from isOpen_lt continuous_const Complex.continuous_re)
    intro z hz
    exact (((differentiableAt_id.sub_const 1).mul (zetaRegular_differentiableAt hz)).add_const 1).differentiableWithinAt
  have he : DirichletCharacter.LFunctionTrivChar₁ 1 =ᶠ[𝓝 (2:ℂ)]
      fun s : ℂ => (s-1)*zetaRegular s+1 := by
    filter_upwards [(continuous_re.tendsto (2:ℂ)).eventually
      (lt_mem_nhds (by norm_num : (1:ℝ) < (2:ℂ).re))] with z hz
    have hz1 : z ≠ 1 := by intro h; simp [h] at hz
    rw [DirichletCharacter.LFunctionTrivChar₁,Function.update_of_ne hz1,
      DirichletCharacter.LFunctionTrivChar,DirichletCharacter.LFunction_modOne_eq,
      zetaRegular_eq_of_one_lt_re hz]
    field_simp
    ring
  exact hF.eqOn_of_preconnected_of_eventuallyEq hG (convex_halfSpace_re_gt 0).isPreconnected
    (show (2:ℂ) ∈ {s : ℂ | 0 < s.re} by norm_num) he hs

lemma zetaRegular_eq {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    zetaRegular s = riemannZeta s-1/(s-1) := by
  have h := poleRemovedZeta_eq hs
  rw [DirichletCharacter.LFunctionTrivChar₁,Function.update_of_ne hs1,
    DirichletCharacter.LFunctionTrivChar,DirichletCharacter.LFunction_modOne_eq] at h
  have hn : s-1 ≠ 0 := sub_ne_zero.mpr hs1
  apply (mul_left_cancel₀ hn)
  rw [mul_sub,mul_div_cancel₀ _ hn]
  linear_combination -h

lemma regularSeries_norm_simple {f : ℕ → ℂ} {c : ℂ} {D : ℝ} (hD : 0 ≤ D)
    (hb : ∀ t, 1 < t → ‖seriesDiscrepancy f c t‖ ≤ D) {s : ℂ} (hs : 0 < s.re) :
    ‖regularSeries f c s‖ ≤ ‖c‖+‖s‖*D/s.re := by
  have h := discrepancyTail_norm_le zero_lt_one hD (measurable_seriesDiscrepancy f c) hb hs
  simp only [Real.one_rpow,mul_one] at h
  calc
    _ ≤ ‖c‖+‖s*discrepancyTail (seriesDiscrepancy f c) 1 s‖ := norm_add_le _ _
    _ ≤ ‖c‖+‖s‖*(D/s.re) := by rw [norm_mul]; gcongr
    _ = _ := by ring

lemma closedBall_two_re_norm {s : ℂ} (hs : s ∈ Metric.closedBall 2 (7/4:ℝ)) :
    (1/4:ℝ) ≤ s.re ∧ ‖s‖ ≤ 4 := by
  have hd := Metric.mem_closedBall.mp hs
  have hr := Complex.re_le_norm ((2:ℂ)-s)
  rw [Complex.sub_re,←dist_eq_norm,dist_comm] at hr
  have hn : ‖s‖ ≤ dist s 2+‖(2:ℂ)‖ := by simpa [dist_eq_norm] using norm_add_le (s-2) (2:ℂ)
  norm_num at hr hn
  constructor <;> linarith

lemma zetaRegular_norm_le_seventeen {s : ℂ} (hs : s ∈ Metric.closedBall 2 (7/4:ℝ)) :
    ‖zetaRegular s‖ ≤ 17 := by
  obtain ⟨hre,hnorm⟩ := closedBall_two_re_norm hs
  have hp : 0 < s.re := by linarith
  have h := regularSeries_norm_simple zero_le_one (fun _ ht => discrepancy_constant_bound ht.le) hp
  change ‖zetaRegular s‖ ≤ _ at h
  norm_num at h
  have hq : ‖s‖/s.re ≤ 16 := (div_le_iff₀ hp).mpr (by linarith)
  linarith

lemma LFunction_norm_polynomial {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) {s : ℂ} (hs : s ∈ Metric.closedBall 2 (7/4:ℝ)) :
    ‖χ.LFunction s‖ ≤ 16*((q:ℝ)+1) := by
  obtain ⟨hre,hnorm⟩ := closedBall_two_re_norm hs
  have hp : 0 < s.re := by linarith
  have hb := regularSeries_norm_simple (by positivity : (0:ℝ) ≤ q+1)
    (fun t _ => discrepancy_character_bound hχ t) hp
  rw [regularSeries_character_eq hχ hp] at hb
  simp only [norm_zero,zero_add] at hb
  apply hb.trans
  apply (div_le_iff₀ hp).mpr
  nlinarith [Nat.cast_nonneg (α:=ℝ) q]

noncomputable def regularizedZetaProduct (P : ℂ → ℂ) (s : ℂ) : ℂ :=
  zetaRegular s*P s+dslope P 1 s

lemma regularizedZetaProduct_differentiableOn {P : ℂ → ℂ}
    (hP : DifferentiableOn ℂ P {s : ℂ | 0 < s.re}) :
    DifferentiableOn ℂ (regularizedZetaProduct P) {s : ℂ | 0 < s.re} := by
  have hs : {s : ℂ | 0 < s.re} ∈ 𝓝 (1:ℂ) :=
    (show IsOpen {z : ℂ | 0 < z.re} from isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  have hd := (Complex.differentiableOn_dslope hs).mpr hP
  have hz : DifferentiableOn ℂ zetaRegular {s : ℂ | 0 < s.re} :=
    fun s hs => (zetaRegular_differentiableAt hs).differentiableWithinAt
  exact (hz.mul hP).add hd

lemma regularizedZetaProduct_eq {P : ℂ → ℂ} {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    regularizedZetaProduct P s = riemannZeta s*P s-P 1/(s-1) := by
  rw [regularizedZetaProduct,zetaRegular_eq hs hs1,dslope_of_ne P hs1,slope_def_field]
  ring

lemma regularizedZetaProduct_bound {P : ℂ → ℂ} {B : ℝ}
    (hP : DifferentiableOn ℂ P {s : ℂ | 0 < s.re}) (_hB : 0 ≤ B)
    (hb : ∀ s ∈ Metric.closedBall (2:ℂ) (7/4:ℝ), ‖P s‖ ≤ B) :
    DiffContOnCl ℂ (regularizedZetaProduct P) (Metric.ball 2 (3/2:ℝ)) ∧
      ∀ s ∈ Metric.closedBall (2:ℂ) (3/2:ℝ), ‖regularizedZetaProduct P s‖ ≤ 21*B := by
  have hsRe (s : ℂ) (hs : s ∈ Metric.closedBall 2 (7/4:ℝ)) : 0 < s.re := by
    have := (closedBall_two_re_norm hs).1
    linarith
  have hder (s : ℂ) (hs : s ∈ Metric.closedBall 2 (3/2:ℝ)) : ‖deriv P s‖ ≤ 4*B := by
    have hsub : Metric.closedBall s (1/4:ℝ) ⊆ Metric.closedBall (2:ℂ) (7/4:ℝ) := by
      intro z hz
      have hdist := dist_triangle z s (2:ℂ)
      have hz' := Metric.mem_closedBall.mp hz
      have hs' := Metric.mem_closedBall.mp hs
      apply Metric.mem_closedBall.mpr
      linarith
    have hdiff : DiffContOnCl ℂ P (Metric.ball s (1/4:ℝ)) := by
      apply DifferentiableOn.diffContOnCl
      rw [closure_ball _ (by norm_num : (1/4:ℝ) ≠ 0)]
      exact hP.mono (fun z hz => hsRe z (hsub hz))
    have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by norm_num : (0:ℝ) < 1/4)
      hdiff (fun z hz => hb z (hsub (Metric.sphere_subset_closedBall hz)))
    convert h using 1; ring
  have hone : (1:ℂ) ∈ Metric.closedBall (2:ℂ) (3/2:ℝ) := by
    norm_num [Metric.mem_closedBall,dist_eq_norm]
  have hdslope (s : ℂ) (hs : s ∈ Metric.closedBall 2 (3/2:ℝ)) : ‖dslope P 1 s‖ ≤ 4*B := by
    by_cases hs1 : s = 1
    · subst s
      simpa only [dslope_same] using hder 1 hone
    · rw [dslope_of_ne P hs1,slope_def_field,norm_div]
      have hd := (convex_closedBall (2:ℂ) (3/2:ℝ)).norm_image_sub_le_of_norm_deriv_le
        (fun z hz => (hP z (hsRe z (Metric.closedBall_subset_closedBall (by norm_num) hz))).differentiableAt
          ((show IsOpen {z : ℂ | 0 < z.re} from isOpen_lt continuous_const Complex.continuous_re).mem_nhds
            (hsRe z (Metric.closedBall_subset_closedBall (by norm_num) hz)))) hder hone hs
      exact (div_le_iff₀ (norm_pos_iff.mpr (sub_ne_zero.mpr hs1))).mpr hd
  constructor
  · apply DifferentiableOn.diffContOnCl
    rw [closure_ball _ (by norm_num : (3/2:ℝ) ≠ 0)]
    exact (regularizedZetaProduct_differentiableOn hP).mono
      (fun z hz => hsRe z (Metric.closedBall_subset_closedBall (by norm_num) hz))
  · intro s hs
    have hs' := Metric.closedBall_subset_closedBall (by norm_num : (3/2:ℝ) ≤ 7/4) hs
    calc
      _ ≤ ‖zetaRegular s*P s‖+‖dslope P 1 s‖ := norm_add_le _ _
      _ ≤ 17*B+4*B := by rw [norm_mul]; gcongr; exact zetaRegular_norm_le_seventeen hs'; exact hb s hs'; exact hdslope s hs
      _ = _ := by ring

open Complex Finset ArithmeticFunction
open scoped ComplexOrder
def PrimePowerEq (p : ℕ) (f g : ArithmeticFunction ℂ) : Prop :=
  ∀ k : ℕ, f (p^k) = g (p^k)

lemma PrimePowerEq.refl (p : ℕ) (f : ArithmeticFunction ℂ) : PrimePowerEq p f f := fun _ => rfl

lemma PrimePowerEq.mul {p : ℕ} (hp : p.Prime) {f f' g g' : ArithmeticFunction ℂ}
    (hf : PrimePowerEq p f f') (hg : PrimePowerEq p g g') : PrimePowerEq p (f*g) (f'*g') := by
  intro k
  simp only [ArithmeticFunction.mul_apply]
  apply Finset.sum_congr rfl
  intro x hx
  obtain ⟨i,hi,hxi⟩ := (Nat.dvd_prime_pow hp).mp (Nat.mem_divisors.mp
    (Nat.fst_mem_divisors_of_mem_antidiagonal hx)).1
  obtain ⟨j,hj,hxj⟩ := (Nat.dvd_prime_pow hp).mp (Nat.mem_divisors.mp
    (Nat.snd_mem_divisors_of_mem_antidiagonal hx)).1
  rw [hxi,hxj,hf,hg]

lemma primePower_zeta {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (ArithmeticFunction.zeta : ArithmeticFunction ℂ) (p^k) = 1 := by
  simp [hp.ne_zero]

lemma primePower_one {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (1 : ArithmeticFunction ℂ) (p^k) = (0:ℂ)^k := by
  cases k with
  | zero => simp
  | succ k =>
    have hn : p^(k+1) ≠ 1 := by
      have h : 1 < p^(k+1) := one_lt_pow₀ hp.one_lt (by omega)
      omega
    simp [hp.ne_one]

lemma primePower_character {q p : ℕ} (χ : DirichletCharacter ℂ q) (hp : p.Prime) (k : ℕ) :
    toArithmeticFunction (χ ·) (p^k) = χ (p : ZMod q)^k := by
  simp [toArithmeticFunction,hp.ne_zero]

lemma arithmetic_convolution_nonneg {f g : ArithmeticFunction ℂ}
    (hf : ∀ n, 0 ≤ f n) (hg : ∀ n, 0 ≤ g n) (n : ℕ) : 0 ≤ (f*g) n := by
  rw [ArithmeticFunction.mul_apply]
  exact Finset.sum_nonneg (fun x _ => mul_nonneg (hf x.1) (hg x.2))

noncomputable def biquadraticCoefficients {q r : ℕ}
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r) : ArithmeticFunction ℂ :=
  ArithmeticFunction.zeta * toArithmeticFunction (χ ·) * toArithmeticFunction (ψ ·) *
    (toArithmeticFunction (χ ·)).pmul (toArithmeticFunction (ψ ·))

lemma biquadraticCoefficients_multiplicative {q r : ℕ}
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r) :
    (biquadraticCoefficients χ ψ).IsMultiplicative := by
  exact ((isMultiplicative_zeta.natCast.mul (DirichletCharacter.isMultiplicative_toArithmeticFunction χ)).mul
    (DirichletCharacter.isMultiplicative_toArithmeticFunction ψ)).mul
    ((DirichletCharacter.isMultiplicative_toArithmeticFunction χ).pmul (DirichletCharacter.isMultiplicative_toArithmeticFunction ψ))

lemma biquadraticCoefficients_comm {q r : ℕ}
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r) :
    biquadraticCoefficients χ ψ = biquadraticCoefficients ψ χ := by
  unfold biquadraticCoefficients
  rw [ArithmeticFunction.pmul_comm]
  ring

lemma biquadratic_prime_zero {q r p : ℕ}
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r) (hp : p.Prime)
    (hχ : χ (p : ZMod q) = 0) :
    PrimePowerEq p (biquadraticCoefficients χ ψ) ψ.zetaMul := by
  have hf : PrimePowerEq p (toArithmeticFunction (χ ·)) 1 := by
    intro k
    rw [primePower_character χ hp, hχ,primePower_one hp]
  have hh : PrimePowerEq p ((toArithmeticFunction (χ ·)).pmul (toArithmeticFunction (ψ ·))) 1 := by
    intro k
    rw [ArithmeticFunction.pmul_apply,primePower_character χ hp,primePower_character ψ hp,
      hχ,←mul_pow,zero_mul,primePower_one hp]
  have h := ((PrimePowerEq.refl p (ArithmeticFunction.zeta : ArithmeticFunction ℂ)).mul hp hf).mul hp
    (PrimePowerEq.refl p (toArithmeticFunction (ψ ·))) |>.mul hp hh
  simpa only [mul_one,biquadraticCoefficients,DirichletCharacter.zetaMul] using h

lemma biquadratic_prime_one {q r p : ℕ}
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r) (hp : p.Prime)
    (hχ : χ (p : ZMod q) = 1) :
    PrimePowerEq p (biquadraticCoefficients χ ψ) (ψ.zetaMul*ψ.zetaMul) := by
  have hf : PrimePowerEq p (toArithmeticFunction (χ ·)) ArithmeticFunction.zeta := by
    intro k
    rw [primePower_character χ hp,hχ,one_pow,primePower_zeta hp]
  have hh : PrimePowerEq p ((toArithmeticFunction (χ ·)).pmul (toArithmeticFunction (ψ ·)))
      (toArithmeticFunction (ψ ·)) := by
    intro k
    rw [ArithmeticFunction.pmul_apply,primePower_character χ hp,hχ,one_pow,one_mul]
  have h := ((PrimePowerEq.refl p (ArithmeticFunction.zeta : ArithmeticFunction ℂ)).mul hp hf).mul hp
    (PrimePowerEq.refl p (toArithmeticFunction (ψ ·))) |>.mul hp hh
  have he : (ArithmeticFunction.zeta : ArithmeticFunction ℂ)*ArithmeticFunction.zeta*
      toArithmeticFunction (ψ ·)*toArithmeticFunction (ψ ·) = ψ.zetaMul*ψ.zetaMul := by
    unfold DirichletCharacter.zetaMul
    ring
  simpa only [he,biquadraticCoefficients] using h

lemma biquadratic_prime_neg_one {q r p : ℕ}
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r) (hp : p.Prime)
    (hχ : χ (p : ZMod q) = -1) (hψ : ψ (p : ZMod r) = -1) :
    PrimePowerEq p (biquadraticCoefficients χ ψ) (χ.zetaMul*χ.zetaMul) := by
  have hg : PrimePowerEq p (toArithmeticFunction (ψ ·)) (toArithmeticFunction (χ ·)) := by
    intro k
    rw [primePower_character ψ hp,primePower_character χ hp,hχ,hψ]
  have hh : PrimePowerEq p ((toArithmeticFunction (χ ·)).pmul (toArithmeticFunction (ψ ·)))
      ArithmeticFunction.zeta := by
    intro k
    rw [ArithmeticFunction.pmul_apply,primePower_character χ hp,primePower_character ψ hp,
      hχ,hψ,←mul_pow,neg_mul_neg,one_mul,one_pow,primePower_zeta hp]
  have h := ((PrimePowerEq.refl p (ArithmeticFunction.zeta : ArithmeticFunction ℂ)).mul hp
    (PrimePowerEq.refl p (toArithmeticFunction (χ ·)))).mul hp hg |>.mul hp hh
  have he : (ArithmeticFunction.zeta : ArithmeticFunction ℂ)*toArithmeticFunction (χ ·)*
      toArithmeticFunction (χ ·)*ArithmeticFunction.zeta = χ.zetaMul*χ.zetaMul := by
    unfold DirichletCharacter.zetaMul
    ring
  simpa only [he,biquadraticCoefficients] using h

lemma biquadraticCoefficients_nonneg {q r : ℕ} {χ : DirichletCharacter ℂ q}
    {ψ : DirichletCharacter ℂ r} (hχ : χ^2=1) (hψ : ψ^2=1) (n : ℕ) :
    0 ≤ biquadraticCoefficients χ ψ n := by
  have hp (p : ℕ) (hp : p.Prime) (k : ℕ) : 0 ≤ biquadraticCoefficients χ ψ (p^k) := by
    rcases MulChar.isQuadratic_iff_sq_eq_one.mpr hχ (p:ZMod q) with h0|h1|hm
    · rw [biquadratic_prime_zero χ ψ hp h0 k]
      exact DirichletCharacter.zetaMul_nonneg hψ _
    · rw [biquadratic_prime_one χ ψ hp h1 k]
      exact arithmetic_convolution_nonneg (DirichletCharacter.zetaMul_nonneg hψ)
        (DirichletCharacter.zetaMul_nonneg hψ) _
    · rcases MulChar.isQuadratic_iff_sq_eq_one.mpr hψ (p:ZMod r) with h0|h1|hm'
      · rw [biquadraticCoefficients_comm χ ψ,biquadratic_prime_zero ψ χ hp h0 k]
        exact DirichletCharacter.zetaMul_nonneg hχ _
      · rw [biquadraticCoefficients_comm χ ψ,biquadratic_prime_one ψ χ hp h1 k]
        exact arithmetic_convolution_nonneg (DirichletCharacter.zetaMul_nonneg hχ)
          (DirichletCharacter.zetaMul_nonneg hχ) _
      · rw [biquadratic_prime_neg_one χ ψ hp hm hm' k]
        exact arithmetic_convolution_nonneg (DirichletCharacter.zetaMul_nonneg hχ)
          (DirichletCharacter.zetaMul_nonneg hχ) _
  rcases eq_or_ne n 0 with rfl|hn
  · simp
  · simpa only [(biquadraticCoefficients_multiplicative χ ψ).multiplicative_factorization _ hn,
      Finsupp.prod, Nat.support_factorization] using
      Finset.prod_nonneg (fun p hp' => hp p (Nat.prime_of_mem_primeFactors hp') _)

end LargePrimeGaps
end OAI

-- Source module: SiegelBounds
namespace OAI
namespace LargePrimeGaps
section
open Complex Filter Topology Set MeasureTheory Finset ArithmeticFunction
lemma quadratic_character_im {q : ℕ} {χ : DirichletCharacter ℂ q} (hχ : χ^2=1)
    (a : ZMod q) : (χ a).im = 0 := by
  rcases MulChar.isQuadratic_iff_sq_eq_one.mpr hχ a with h|h|h <;> simp [h]

lemma regularSeries_im_zero {f : ℕ → ℂ} {c : ℂ} {D : ℝ}
    (hf : ∀ n, (f n).im=0) (hc : c.im=0) (hD : 0 ≤ D)
    (hb : ∀ t, 1<t → ‖seriesDiscrepancy f c t‖ ≤ D) {x : ℝ} (hx : 0<x) :
    (regularSeries f c x).im=0 := by
  have hi := discrepancyTail_integrable zero_lt_one hD (measurable_seriesDiscrepancy f c) hb
    (show 0<(x:ℂ).re from hx)
  have he : (discrepancyTail (seriesDiscrepancy f c) 1 x).im=0 := by
    unfold discrepancyTail
    change RCLike.im (∫ t in Ioi (1:ℝ), seriesDiscrepancy f c t*(t:ℂ)^(-((x:ℂ)+1)))=0
    rw [←integral_im hi]
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hp : ((t:ℂ)^(-((x:ℂ)+1))).im=0 := by
      rw [show -((x:ℂ)+1)= (-(x+1):ℝ) by push_cast; rfl,
        ←Complex.ofReal_cpow (by exact (zero_lt_one.trans ht).le : 0≤t)]
      rfl
    change (seriesDiscrepancy f c t * (t:ℂ)^(-((x:ℂ)+1))).im=0
    rw [Complex.mul_im,hp,mul_zero,zero_add]
    have hz : (seriesDiscrepancy f c t).im=0 := by simp [seriesDiscrepancy,Complex.mul_im,hc,hf]
    rw [hz,zero_mul]
  simp [regularSeries,Complex.mul_im,hc,he]

lemma quadratic_LFunction_im {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ≠1) (hχ2 : χ^2=1) {x : ℝ} (hx : 0<x) : (χ.LFunction x).im=0 := by
  rw [←regularSeries_character_eq hχ hx]
  apply regularSeries_im_zero _ (by simp) (by positivity : (0:ℝ)≤q+1)
    (fun t _ => discrepancy_character_bound hχ t) hx
  intro n
  simp only [positiveCoefficients]
  split_ifs <;> simp [quadratic_character_im hχ2]

lemma LSeries_character_summable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1<s.re) :
    LSeriesSummable (toArithmeticFunction (fun n : ℕ => χ (n : ZMod q))) s := by
  apply (LSeriesSummable_congr _ (fun h => (χ.apply_eq_toArithmeticFunction_apply h).symm)).mpr
  exact ZMod.LSeriesSummable_of_one_lt_re χ hs

lemma LSeries_character_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1<s.re) :
    LSeries (toArithmeticFunction (fun n : ℕ => χ (n : ZMod q))) s = χ.LFunction s := by
  rw [χ.LFunction_eq_LSeries hs]
  exact (LSeries_congr χ.apply_eq_toArithmeticFunction_apply s).symm

lemma LSeries_zeta_complex_eq {s : ℂ} (hs : 1<s.re) :
    LSeries (ArithmeticFunction.zeta : ArithmeticFunction ℂ) s=riemannZeta s := by
  rw [←LSeries_one_eq_riemannZeta hs]
  apply LSeries_congr
  intro n hn
  simp [hn]

lemma LSeries_zetaMul_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1<s.re) : LSeries χ.zetaMul s=riemannZeta s*χ.LFunction s := by
  have hz : LSeriesSummable (ArithmeticFunction.zeta : ArithmeticFunction ℂ) s := by
    apply LSeriesSummable_of_bounded_of_one_lt_re (m:=1) _ hs
    intro n hn
    simp [hn]
  rw [DirichletCharacter.zetaMul,ArithmeticFunction.LSeries_mul' hz
    (LSeries_character_summable χ hs),LSeries_character_eq χ hs,LSeries_zeta_complex_eq hs]

open scoped ComplexOrder in
lemma quadratic_LFunction_re_pos_of_one_lt {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ2 : χ^2=1) {x : ℝ} (hx : 1<x) :
    0<(χ.LFunction x).re := by
  have hp := LSeries.positive (DirichletCharacter.zetaMul_nonneg hχ2)
    (χ.isMultiplicative_zetaMul.map_one ▸ zero_lt_one)
    (lt_of_le_of_lt (LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
      (fun s hs => χ.LSeriesSummable_zetaMul hs)) (show (1:EReal)<x by exact_mod_cast hx))
  rw [LSeries_zetaMul_eq χ hx] at hp
  have hr := (Complex.pos_iff.mp hp).1
  rw [Complex.mul_re,riemannZeta_im_eq_zero_of_one_lt hx,zero_mul,sub_zero] at hr
  exact (mul_pos_iff.mp hr).resolve_right (fun h => (riemannZeta_re_pos_of_one_lt hx).not_ge h.1.le) |>.2

lemma quadratic_LFunction_re_pos_one {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ≠1) (hχ2 : χ^2=1) : 0<(χ.LFunction 1).re := by
  have hc : Continuous (fun x : ℝ => (χ.LFunction x).re) :=
    Complex.continuous_re.comp ((DirichletCharacter.differentiable_LFunction hχ).continuous.comp
      Complex.continuous_ofReal)
  have hn : 0≤(χ.LFunction 1).re := by
    apply ge_of_tendsto (hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds :
      Tendsto (fun x : ℝ => (χ.LFunction x).re) (𝓝[>] 1) (𝓝 ((χ.LFunction 1).re)))
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (quadratic_LFunction_re_pos_of_one_lt hχ2 hx).le
  refine lt_of_le_of_ne hn ?_
  intro he
  apply DirichletCharacter.LFunction_apply_one_ne_zero hχ
  apply Complex.ext
  · simpa using he.symm
  · simpa using quadratic_LFunction_im hχ hχ2 (x:=1) zero_lt_one

lemma quadratic_LFunction_re_pos_of_no_root {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ≠1) (hχ2 : χ^2=1)
    {β : ℝ} (hβ : 0<β) (hβ1 : β≤1)
    (hz : ∀ x ∈ Set.Icc β 1, χ.LFunction x≠0) : 0<(χ.LFunction β).re := by
  by_contra! hn
  have hc : Continuous (fun x : ℝ => (χ.LFunction x).re) :=
    Complex.continuous_re.comp ((DirichletCharacter.differentiable_LFunction hχ).continuous.comp
      Complex.continuous_ofReal)
  obtain ⟨x,hx,hxe⟩ := intermediate_value_Icc hβ1 hc.continuousOn
    (show (0:ℝ) ∈ Set.Icc ((χ.LFunction β).re) ((χ.LFunction 1).re) from
      ⟨hn,(quadratic_LFunction_re_pos_one hχ hχ2).le⟩)
  apply hz x hx
  apply Complex.ext
  · simpa using hxe
  · simpa using quadratic_LFunction_im hχ hχ2 (hβ.trans_le hx.1)

end
section
open Complex Finset ArithmeticFunction
noncomputable def productCharacter {q r : ℕ} (χ : DirichletCharacter ℂ q)
    (ψ : DirichletCharacter ℂ r) : DirichletCharacter ℂ (q*r) :=
  χ.changeLevel (dvd_mul_right q r) * ψ.changeLevel (dvd_mul_left r q)

lemma changeLevel_natCast {q m : ℕ} (χ : DirichletCharacter ℂ q) (hqm : q∣m)
    {n : ℕ} (hn : n.Coprime m) :
    χ.changeLevel hqm (n : ZMod m)=χ (n : ZMod q) := by
  have h := χ.changeLevel_eq_cast_of_dvd hqm (ZMod.unitOfCoprime n hn)
  simp only [ZMod.coe_unitOfCoprime] at h
  rw [ZMod.cast_natCast hqm] at h
  exact h

lemma productCharacter_apply {q r n : ℕ} (χ : DirichletCharacter ℂ q)
    (ψ : DirichletCharacter ℂ r) : productCharacter χ ψ (n : ZMod (q*r))=
      χ (n : ZMod q)*ψ (n : ZMod r) := by
  by_cases hn : n.Coprime (q*r)
  · simp only [productCharacter,MulChar.mul_apply,changeLevel_natCast _ _ hn]
  · rw [MulChar.map_nonunit _ (by rwa [ZMod.isUnit_iff_coprime])]
    by_cases hq : n.Coprime q
    · have hr : ¬n.Coprime r := fun hr => hn (hq.mul_right hr)
      rw [ψ.map_nonunit (by rwa [ZMod.isUnit_iff_coprime]),mul_zero]
    · rw [χ.map_nonunit (by rwa [ZMod.isUnit_iff_coprime]),zero_mul]

lemma productCharacter_quadratic {q r : ℕ} {χ : DirichletCharacter ℂ q}
    {ψ : DirichletCharacter ℂ r} (hχ : χ^2=1) (hψ : ψ^2=1) :
    (productCharacter χ ψ)^2=1 := by
  simp [productCharacter,mul_pow,←map_pow,hχ,hψ]

lemma productCharacter_ne_one_of_levels_ne {q r : ℕ} [NeZero q] [NeZero r]
    {χ : DirichletCharacter ℂ q} {ψ : DirichletCharacter ℂ r}
    (hχ : χ.IsPrimitive) (hψ : ψ.IsPrimitive) (hψ2 : ψ^2=1) (hqr : q≠r) :
    productCharacter χ ψ≠1 := by
  intro h
  have h2 : (ψ.changeLevel (dvd_mul_left r q))^2=1 := by rw [←map_pow,hψ2,map_one]
  have he : χ.changeLevel (dvd_mul_right q r) = ψ.changeLevel (dvd_mul_left r q) := by
    calc
      _ = (χ.changeLevel (dvd_mul_right q r)*ψ.changeLevel (dvd_mul_left r q))*
          ψ.changeLevel (dvd_mul_left r q) := by rw [mul_assoc,←pow_two,h2,mul_one]
      _ = _ := by rw [show χ.changeLevel (dvd_mul_right q r)*ψ.changeLevel (dvd_mul_left r q)=1 from h,one_mul]
  have hc := congrArg DirichletCharacter.conductor he
  rw [DirichletCharacter.conductor_changeLevel,DirichletCharacter.conductor_changeLevel,
    hχ,hψ] at hc
  exact hqr hc

lemma productCharacter_toArithmeticFunction {q r : ℕ} (χ : DirichletCharacter ℂ q)
    (ψ : DirichletCharacter ℂ r) :
    toArithmeticFunction (productCharacter χ ψ ·)=
      (toArithmeticFunction (χ ·)).pmul (toArithmeticFunction (ψ ·)) := by
  ext n
  by_cases hn : n=0
  · simp [hn]
  · rw [ArithmeticFunction.pmul_apply]
    simp [toArithmeticFunction,hn,productCharacter_apply]

end
section
open Complex Filter Topology Set MeasureTheory Finset
open scoped ComplexOrder in
lemma zeta_product_residue_lower {P : ℂ → ℂ} {a : ℕ → ℂ} {A B Q β ε : ℝ}
    (hP : DifferentiableOn ℂ P {s : ℂ | 0<s.re})
    (hB : 0≤B) (hb : ∀ s ∈ Metric.closedBall (2:ℂ) (7/4:ℝ), ‖P s‖≤B)
    (hA : 0≤A) (hQ : 2≤Q) (hQA : 12*A≤Q) (hBQ : 21*B≤A*Q^4)
    (hβ : 3/4≤β) (hβ1 : β<1) (hβε : 60*(1-β)≤ε)
    (ha : ∀ n, 0≤a n) (ha1 : 1≤a 1) (haC : LSeries.abscissaOfAbsConv a≤1)
    (haP : ∀ s : ℂ, 1<s.re → LSeries a s=riemannZeta s*P s)
    (hvalue : (riemannZeta β*P β).re≤0) (hreal : (P 1).im=0) :
    ((1-β)/(2*(2-β)))*Q^(-ε)≤(P 1).re := by
  let H := regularizedZetaProduct P
  have hR : P 1=((P 1).re:ℂ) := by apply Complex.ext <;> simp [hreal]
  obtain ⟨hf,hbound⟩ := regularizedZetaProduct_bound hP hB hb
  have he : H =ᶠ[𝓝 (2:ℂ)] fun s => LSeries a s-((P 1).re:ℂ)/(s-1) := by
    filter_upwards [(continuous_re.tendsto (2:ℂ)).eventually
      (lt_mem_nhds (by norm_num : (1:ℝ)<(2:ℂ).re))] with s hs
    have hs1 : s≠1 := by intro h; simp [h] at hs
    rw [show H s=regularizedZetaProduct P s from rfl,regularizedZetaProduct_eq (by linarith) hs1,
      ←haP s hs,hR]
    simp only [Complex.ofReal_re]
  have hac : LSeries.abscissaOfAbsConv a<(2:ℝ) := haC.trans_lt (by exact_mod_cast (show (1:ℝ)<2 by norm_num))
  obtain ⟨ha0,han⟩ := signedTaylorCoeff_regular_nonneg ha ha1 hac he
  have hz : 1<2-β := by linarith
  have hz0 : 0<2-β := by linarith
  have hzr : 2-β<(3/2:ℝ) := by linarith
  have hv : (∑' n : ℕ, signedTaylorCoeff H n*(2-β)^n)≤(P 1).re/((2-β)-1) := by
    rw [(signedTaylorCoeff_hasSum hf.differentiableOn (by rwa [abs_of_pos hz0])).tsum_eq]
    have hβ0 : 0<β := by linarith
    have hβne : (β:ℂ)≠1 := by intro h; have := congrArg Complex.re h; simp at this; linarith
    rw [show (2-(2-β):ℝ)=β by ring]
    change (regularizedZetaProduct P β).re≤_
    rw [regularizedZetaProduct_eq hβ0 hβne,Complex.sub_re,hR,
      ←Complex.ofReal_one,←Complex.ofReal_sub,←Complex.ofReal_div,Complex.ofReal_re]
    have hid : (P 1).re/(β-1) = -(P 1).re/((2-β)-1) := by
      rw [show β-1 = -((2-β)-1) by ring,div_neg,neg_div]
    simp only [Complex.ofReal_one,Complex.ofReal_re]
    rw [hid,neg_div,sub_neg_eq_add]
    exact add_le_of_nonpos_left hvalue
  have hn (n : ℕ) : |signedTaylorCoeff H n|≤(A*Q^4)/(3/2)^n := by
    apply (signedTaylorCoeff_norm_bound (by norm_num : (0:ℝ)<3/2) hf
      (fun s hs => (hbound s (Metric.sphere_subset_closedBall hs)).trans hBQ) n)
  have hr := residue_polynomial_lower (ε:=ε) hA hQ hQA hz (by linarith) (by linarith) hn
    (by simpa [signedTaylorCoeff] using ha0) han hv
  convert hr using 1
  congr 2
  ring

lemma zeta_re_neg_near_one {β : ℝ} (hβ : 99/100≤β) (hβ1 : β<1) :
    (riemannZeta β).re<0 := by
  have hβ0 : 0<β := by linarith
  have hβne : (β:ℂ)≠1 := by intro h; have := congrArg Complex.re h; simp at this; linarith
  have hmem : (β:ℂ) ∈ Metric.closedBall 2 (7/4:ℝ) := by
    rw [Metric.mem_closedBall,dist_eq_norm,←Complex.ofReal_ofNat,←Complex.ofReal_sub,
      Complex.norm_real,Real.norm_eq_abs,abs_of_neg (by linarith : β-2<0)]
    linarith
  have hb := (Complex.re_le_norm (zetaRegular β)).trans (zetaRegular_norm_le_seventeen hmem)
  rw [zetaRegular_eq hβ0 hβne,Complex.sub_re,←Complex.ofReal_one,
    ←Complex.ofReal_sub,←Complex.ofReal_div,Complex.ofReal_re] at hb
  have hd : 1/(β-1)≤-100 := (div_le_iff_of_neg (by linarith : β-1<0)).mpr (by linarith)
  linarith

end
open Complex Filter Topology Set MeasureTheory Finset ArithmeticFunction
lemma LSeries_zeta_complex_summable {s : ℂ} (hs : 1<s.re) :
    LSeriesSummable (ArithmeticFunction.zeta : ArithmeticFunction ℂ) s := by
  apply LSeriesSummable_of_bounded_of_one_lt_re (m:=1) _ hs
  intro n hn
  simp [hn]

lemma biquadraticCoefficients_summable {q r : ℕ} [NeZero q] [NeZero r]
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r) {s : ℂ} (hs : 1<s.re) :
    LSeriesSummable (biquadraticCoefficients χ ψ) s := by
  rw [biquadraticCoefficients,←productCharacter_toArithmeticFunction]
  exact ArithmeticFunction.LSeriesSummable_mul
    (ArithmeticFunction.LSeriesSummable_mul
      (ArithmeticFunction.LSeriesSummable_mul (LSeries_zeta_complex_summable hs) (LSeries_character_summable χ hs))
      (LSeries_character_summable ψ hs)) (LSeries_character_summable (productCharacter χ ψ) hs)

lemma LSeries_biquadratic_eq {q r : ℕ} [NeZero q] [NeZero r]
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r) {s : ℂ} (hs : 1<s.re) :
    LSeries (biquadraticCoefficients χ ψ) s=
      riemannZeta s*(χ.LFunction s*ψ.LFunction s*(productCharacter χ ψ).LFunction s) := by
  have hz := LSeries_zeta_complex_summable hs
  have hχ := LSeries_character_summable χ hs
  have hψ := LSeries_character_summable ψ hs
  have hp := LSeries_character_summable (productCharacter χ ψ) hs
  rw [biquadraticCoefficients,←productCharacter_toArithmeticFunction,
    ArithmeticFunction.LSeries_mul' (ArithmeticFunction.LSeriesSummable_mul (ArithmeticFunction.LSeriesSummable_mul hz hχ) hψ) hp,
    ArithmeticFunction.LSeries_mul' (ArithmeticFunction.LSeriesSummable_mul hz hχ) hψ,
    ArithmeticFunction.LSeries_mul' hz hχ,LSeries_zeta_complex_eq hs,
    LSeries_character_eq χ hs,LSeries_character_eq ψ hs,
    LSeries_character_eq (productCharacter χ ψ) hs]
  ring

lemma quadratic_residue_lower_of_no_root {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ≠1) (hχ2 : χ^2=1)
    {β ε : ℝ} (hβ : 99/100≤β) (hβ1 : β<1) (hβε : 60*(1-β)≤ε)
    (hq : (4032:ℝ)≤q+1) (hz : ∀ x ∈ Set.Icc β 1, χ.LFunction x≠0) :
    ((1-β)/(2*(2-β)))*((q:ℝ)+1)^(-ε)≤‖χ.LFunction 1‖ := by
  have hQ : (2:ℝ)≤q+1 := by linarith
  have hpow : (q:ℝ)+1≤((q:ℝ)+1)^4 := le_self_pow₀ (by linarith) (by norm_num)
  have hv : (riemannZeta β*χ.LFunction β).re≤0 := by
    rw [Complex.mul_re,quadratic_LFunction_im hχ hχ2 (by linarith),mul_zero,sub_zero]
    exact mul_nonpos_of_nonpos_of_nonneg (zeta_re_neg_near_one hβ hβ1).le
      (quadratic_LFunction_re_pos_of_no_root hχ hχ2 (by linarith) hβ1.le hz).le
  apply le_trans _ (Complex.re_le_norm _)
  apply zeta_product_residue_lower (a:=χ.zetaMul) (A:=336) (B:=16*((q:ℝ)+1))
    (DirichletCharacter.differentiable_LFunction hχ).differentiableOn (by positivity)
    (fun s hs => LFunction_norm_polynomial hχ hs) (by norm_num) hQ
    (by norm_num; exact hq) (by nlinarith) (by linarith) hβ1 hβε
    (DirichletCharacter.zetaMul_nonneg hχ2)
    (by simp only [χ.isMultiplicative_zetaMul.map_one,le_refl])
    (LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable (fun s hs => χ.LSeriesSummable_zetaMul hs))
    (fun s hs => LSeries_zetaMul_eq χ hs) hv
    (by simpa using quadratic_LFunction_im hχ hχ2 (x:=1) zero_lt_one)

lemma biquadratic_norm_bound {q r : ℕ} [NeZero q] [NeZero r]
    {χ : DirichletCharacter ℂ q} {ψ : DirichletCharacter ℂ r}
    (hχ : χ≠1) (hψ : ψ≠1) (hp : productCharacter χ ψ≠1)
    {s : ℂ} (hs : s ∈ Metric.closedBall 2 (7/4:ℝ)) :
    ‖χ.LFunction s*ψ.LFunction s*(productCharacter χ ψ).LFunction s‖≤
      16^3*((q:ℝ)+1)^2*((r:ℝ)+1)^2 := by
  have hq0 : (0:ℝ)≤q := Nat.cast_nonneg q
  have hr0 : (0:ℝ)≤r := Nat.cast_nonneg r
  have hp' := LFunction_norm_polynomial hp hs
  simp only [Nat.cast_mul] at hp'
  calc
    _ ≤ (16*((q:ℝ)+1))*(16*((r:ℝ)+1))*(16*((q:ℝ)*r+1)) := by
      simp only [norm_mul]
      gcongr
      · exact LFunction_norm_polynomial hχ hs
      · exact LFunction_norm_polynomial hψ hs
    _ ≤ _ := by nlinarith [mul_nonneg hq0 hr0]

lemma biquadratic_residue_lower_of_root {q r : ℕ} [NeZero q] [NeZero r]
    {χ : DirichletCharacter ℂ q} {ψ : DirichletCharacter ℂ r}
    (hχ : χ≠1) (hχ2 : χ^2=1) (hψ : ψ≠1) (hψ2 : ψ^2=1)
    (hp : productCharacter ψ χ≠1) {β ε : ℝ}
    (hβ : 3/4≤β) (hβ1 : β<1) (hβε : 60*(1-β)≤ε)
    (hq : (12*(21*16^3*((r:ℝ)+1)^2))≤q+1) (hq1 : (2:ℝ)≤q+1)
    (hz : ψ.LFunction β=0) :
    ((1-β)/(2*(2-β)))*((q:ℝ)+1)^(-ε)≤
      ‖ψ.LFunction 1‖*‖χ.LFunction 1‖*‖(productCharacter ψ χ).LFunction 1‖ := by
  let P := fun s => ψ.LFunction s*χ.LFunction s*(productCharacter ψ χ).LFunction s
  have hd : Differentiable ℂ P :=
    ((DirichletCharacter.differentiable_LFunction hψ).mul
      (DirichletCharacter.differentiable_LFunction hχ)).mul
      (DirichletCharacter.differentiable_LFunction hp)
  have hpow : ((q:ℝ)+1)^2≤((q:ℝ)+1)^4 :=
    pow_le_pow_right₀ (by linarith) (by norm_num)
  have hb : ∀ s ∈ Metric.closedBall (2:ℂ) (7/4:ℝ),
      ‖P s‖≤16^3*((r:ℝ)+1)^2*((q:ℝ)+1)^2 := fun s hs => biquadratic_norm_bound hψ hχ hp hs
  have hiψ : (ψ.LFunction 1).im=0 := by simpa using quadratic_LFunction_im hψ hψ2 (x:=1) zero_lt_one
  have hiχ : (χ.LFunction 1).im=0 := by simpa using quadratic_LFunction_im hχ hχ2 (x:=1) zero_lt_one
  have hip : ((productCharacter ψ χ).LFunction 1).im=0 := by
    simpa using quadratic_LFunction_im hp (productCharacter_quadratic hψ2 hχ2) (x:=1) zero_lt_one
  have hreal : (P 1).im=0 := by simp [P,Complex.mul_im,hiψ,hiχ,hip]
  have hR := zeta_product_residue_lower (P:=P) (a:=biquadraticCoefficients ψ χ)
    (A:=21*16^3*((r:ℝ)+1)^2) (B:=16^3*((r:ℝ)+1)^2*((q:ℝ)+1)^2)
    hd.differentiableOn (by positivity) hb (by positivity) hq1 hq
    (by nlinarith [mul_le_mul_of_nonneg_left hpow (by positivity : (0:ℝ)≤21*16^3*((r:ℝ)+1)^2)])
    hβ hβ1 hβε (biquadraticCoefficients_nonneg hψ2 hχ2)
    (by simp only [(biquadraticCoefficients_multiplicative ψ χ).map_one,le_refl])
    (LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
      (fun s hs => biquadraticCoefficients_summable ψ χ hs))
    (fun s hs => LSeries_biquadratic_eq ψ χ hs) (by simp [P,hz]) hreal
  have := hR.trans (Complex.re_le_norm (P 1))
  simpa only [P,norm_mul] using this

lemma quadratic_siegel_eventual {ε : ℝ} (hε : 0<ε) (hε1 : ε≤1) :
    ∃ c Q₀ : ℝ, 0<c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → χ≠1 → χ^2=1 → Q₀≤(q:ℝ)+1 → c*((q:ℝ)+1)^(-ε)≤‖χ.LFunction 1‖ := by
  classical
  let β₀ : ℝ := 1-ε/240
  have hβ₀ : 99/100≤β₀ := by dsimp [β₀]; linarith
  have hβ₀1 : β₀<1 := by dsimp [β₀]; linarith
  by_cases hex : ∃ r : ℕ, ∃ ψ : DirichletCharacter ℂ (r+1),
      ψ.IsPrimitive ∧ ψ≠1 ∧ ψ^2=1 ∧ ∃ β ∈ Set.Icc β₀ 1, ψ.LFunction β=0
  · obtain ⟨r,ψ,hψprim,hψ,hψ2,β,hβI,hzero⟩ := hex
    have hβ1 : β<1 := lt_of_le_of_ne hβI.2 (by
      intro he
      apply DirichletCharacter.LFunction_apply_one_ne_zero hψ
      simpa [he] using hzero)
    have hβ : 99/100≤β := hβ₀.trans hβI.1
    have hβε : 60*(1-β)≤ε/2 := by dsimp [β₀] at hβI; linarith [hβI.1]
    obtain ⟨K,hK,hgrowth⟩ := LFunction_norm_small_power (by linarith : 0<ε/4)
      (by linarith : ε/4≤1/2)
    let D : ℝ := 3*((r:ℝ)+3)
    let U : ℝ := ‖ψ.LFunction 1‖*K*D^(ε/2)
    have hD : 0<D := by dsimp [D]; positivity
    have hU : 0<U := by
      exact mul_pos (mul_pos (norm_pos_iff.mpr (DirichletCharacter.LFunction_apply_one_ne_zero hψ)) hK)
        (Real.rpow_pos_of_pos hD _)
    let c : ℝ := (1-β)/(2*(2-β))/U
    have hc : 0<c := div_pos (div_pos (by linarith) (by linarith)) hU
    refine ⟨c,max (12*(21*16^3*(((r+1:ℕ):ℝ)+1)^2)) ((r:ℝ)+3),hc,?_⟩
    intro q _ χ hχprim hχ hχ2 hq
    have hq1 : (2:ℝ)≤q+1 := by have := (le_max_right _ _).trans hq; have : (0:ℝ)≤r := Nat.cast_nonneg r; linarith
    have hqr : r+1≠q := by
      have hr := (le_max_right _ _).trans hq
      intro he
      rw [←he] at hr
      push_cast at hr
      linarith
    have hp : productCharacter ψ χ≠1 :=
      productCharacter_ne_one_of_levels_ne hψprim hχprim hχ2 hqr
    have hl := biquadratic_residue_lower_of_root hχ hχ2 hψ hψ2 hp
      (by linarith) hβ1 hβε ((le_max_left _ _).trans hq) hq1 hzero
    have hb := hgrowth ((r+1)*q) (productCharacter ψ χ) hp 1 (by simp; linarith)
    have hQ0 : 0<(q:ℝ)+1 := by positivity
    have he : 2*(ε/4)=ε/2 := by ring
    rw [he] at hb
    have hbase : (((r+1)*q:ℕ):ℝ)+2≤((r:ℝ)+3)*((q:ℝ)+1) := by push_cast; nlinarith [Nat.cast_nonneg (α:=ℝ) q,Nat.cast_nonneg (α:=ℝ) r]
    have hb' : ‖(productCharacter ψ χ).LFunction 1‖≤K*D^(ε/2)*((q:ℝ)+1)^(ε/2) := by
      apply hb.trans
      simp only [norm_one]
      calc
        K*(((((r+1)*q:ℕ):ℝ)+2)*(1+2))^(ε/2) ≤ K*(D*((q:ℝ)+1))^(ε/2) := by
          apply mul_le_mul_of_nonneg_left _ hK.le
          apply Real.rpow_le_rpow (by positivity) _ (by linarith)
          dsimp [D]
          nlinarith
        _ = _ := by rw [Real.mul_rpow hD.le hQ0.le]; ring
    have hupper : ‖ψ.LFunction 1‖*‖χ.LFunction 1‖*‖(productCharacter ψ χ).LFunction 1‖≤
        U*((q:ℝ)+1)^(ε/2)*‖χ.LFunction 1‖ := by
      calc
        _ ≤ ‖ψ.LFunction 1‖*‖χ.LFunction 1‖*(K*D^(ε/2)*((q:ℝ)+1)^(ε/2)) := by gcongr
        _ = _ := by dsimp [U]; ring
    have hlow := hl.trans hupper
    have hQp : 0<((q:ℝ)+1)^(ε/2) := Real.rpow_pos_of_pos hQ0 _
    have hexp : ((q:ℝ)+1)^(-ε)*((q:ℝ)+1)^(ε/2)=((q:ℝ)+1)^(-(ε/2)) := by
      rw [←Real.rpow_add hQ0]; congr 1; ring
    have hfinal : U*(c*((q:ℝ)+1)^(-ε)*((q:ℝ)+1)^(ε/2)) ≤
        U*(‖χ.LFunction 1‖*((q:ℝ)+1)^(ε/2)) := by
      calc
        U*(c*((q:ℝ)+1)^(-ε)*((q:ℝ)+1)^(ε/2)) =
            ((1-β)/(2*(2-β)))*((q:ℝ)+1)^(-(ε/2)) := by
          rw [mul_assoc c,hexp]
          dsimp [c]
          field_simp
        _ ≤ U*(‖χ.LFunction 1‖*((q:ℝ)+1)^(ε/2)) := by simpa only [mul_assoc,mul_left_comm,mul_comm] using hlow
    exact (mul_le_mul_iff_left₀ hQp).mp ((mul_le_mul_iff_right₀ hU).mp hfinal)
  · refine ⟨(1-β₀)/(2*(2-β₀)),4032,div_pos (by linarith) (by linarith),?_⟩
    intro q hq χ hχprim hχ hχ2 hqbig
    apply quadratic_residue_lower_of_no_root hχ hχ2 hβ₀ hβ₀1
      (by dsimp [β₀]; linarith) hqbig
    intro x hx hz
    apply hex
    cases q with
    | zero => exact (NeZero.ne 0 rfl).elim
    | succ q => exact ⟨q,χ,hχprim,hχ,hχ2,x,hx,hz⟩

lemma finite_positive_lower {ι : Type*} (S : Finset ι) (f : ι → ℝ)
    (hf : ∀ i∈S,0<f i) : ∃ c : ℝ, 0<c ∧ ∀ i∈S,c≤f i := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1,zero_lt_one,by simp⟩
  | @insert a S ha ih =>
    obtain ⟨c,hc,hcb⟩ := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    refine ⟨min c (f a),lt_min hc (hf a (Finset.mem_insert_self _ _)),?_⟩
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl|hi
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (hcb i hi)

lemma LFunction_one_finite_lower (N : ℕ) :
    ∃ c : ℝ, 0<c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      q≤N → χ≠1 → c≤‖χ.LFunction 1‖ := by
  classical
  induction N with
  | zero => exact ⟨1,zero_lt_one,fun q _ χ hq _ => (NeZero.ne q (Nat.eq_zero_of_le_zero hq)).elim⟩
  | succ N ih =>
    obtain ⟨c,hc,hcb⟩ := ih
    obtain ⟨d,hd,hdb⟩ := finite_positive_lower
      ((Finset.univ : Finset (DirichletCharacter ℂ (N+1))).filter (·≠1))
      (fun χ => ‖χ.LFunction 1‖) (fun χ hχ =>
        norm_pos_iff.mpr (DirichletCharacter.LFunction_apply_one_ne_zero (Finset.mem_filter.mp hχ).2))
    refine ⟨min c d,lt_min hc hd,?_⟩
    intro q _ χ hq hχ
    rcases Nat.le_succ_iff_eq_or_le.mp hq with rfl|hq
    · exact (min_le_right _ _).trans (hdb χ (by simp [hχ]))
    · exact (min_le_left _ _).trans (hcb q χ hq hχ)

theorem quadratic_siegel {ε : ℝ} (hε : 0<ε) (hε1 : ε≤1) :
    ∃ c : ℝ, 0<c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → χ≠1 → χ^2=1 → c*((q:ℝ)+1)^(-ε)≤‖χ.LFunction 1‖ := by
  obtain ⟨c,Q₀,hc,hcb⟩ := quadratic_siegel_eventual hε hε1
  obtain ⟨d,hd,hdb⟩ := LFunction_one_finite_lower ⌈Q₀⌉₊
  refine ⟨min c d,lt_min hc hd,?_⟩
  intro q _ χ hχp hχ hχ2
  by_cases hq : Q₀≤(q:ℝ)+1
  · exact (mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.rpow_nonneg (by positivity) _)).trans
      (hcb q χ hχp hχ hχ2 hq)
  · have hqn : q≤⌈Q₀⌉₊ := by
      have := Nat.le_ceil Q₀
      have : (q:ℝ)≤(⌈Q₀⌉₊:ℝ) := by linarith
      exact_mod_cast this
    have hp : ((q:ℝ)+1)^(-ε)≤1 := Real.rpow_le_one_of_one_le_of_nonpos (by have := Nat.cast_nonneg (α:=ℝ) q; linarith) (by linarith)
    exact (mul_le_of_le_one_right (le_of_lt (lt_min hc hd)) hp).trans
      ((min_le_right _ _).trans (hdb q χ hqn hχ))

end LargePrimeGaps
end OAI

-- Source module: ZeroFreeBounds
namespace OAI
namespace LargePrimeGaps
section
open Complex Filter Topology Set MeasureTheory Finset
lemma periodic_sum_norm_le_mul {f : ℕ → ℂ} {q : ℕ} {D : ℝ} (hq : 0<q) (hD : 0≤D)
    (hp : ∀ n,f (q+n)=f n) (hz : ∑ n∈range q,f n=0)
    (hb : ∀ n,‖f n‖≤D) (N : ℕ) : ‖∑ n∈range N,f n‖≤q*D := by
  induction N using Nat.strong_induction_on with
  | ind N ih =>
    by_cases hN : N<q
    · calc
        _ ≤ ∑ n∈range N,‖f n‖ := norm_sum_le _ _
        _ ≤ ∑ _n∈range N,D := sum_le_sum (fun n _ => hb n)
        _ = N*D := by simp
        _ ≤ q*D := mul_le_mul_of_nonneg_right (by exact_mod_cast hN.le) hD
    · have he : q+(N-q)=N := Nat.add_sub_of_le (not_lt.mp hN)
      rw [←he,sum_range_add,hz,zero_add]
      simp_rw [hp]
      exact ih _ (Nat.sub_lt (lt_of_lt_of_le hq (not_lt.mp hN)) hq)

noncomputable def characterMean {q : ℕ} (χ : DirichletCharacter ℂ q) : ℂ :=
  (∑ n∈range q,χ (n : ZMod q))/(q:ℂ)

lemma characterMean_norm_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    ‖characterMean χ‖≤1 := by
  rw [characterMean,norm_div,Complex.norm_natCast]
  apply (div_le_one (by exact_mod_cast NeZero.pos q : (0:ℝ)<q)).mpr
  calc
    _ ≤ ∑ n∈range q,‖χ (n : ZMod q)‖ := norm_sum_le _ _
    _ ≤ ∑ _n∈range q,(1:ℝ) := sum_le_sum (fun n _ => χ.norm_le_one _)
    _ = q := by simp

lemma characterMean_eq_zero {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ≠1) :
    characterMean χ=0 := by simp [characterMean,char_sum_range_zero hχ]

lemma discrepancy_characterMean_bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {t : ℝ} (ht : 1≤t) :
    ‖seriesDiscrepancy (positiveCoefficients (fun n => χ (n : ZMod q))) (characterMean χ) t‖≤2*q+3 := by
  let c := characterMean χ
  have hc : ‖c‖≤1 := characterMean_norm_le χ
  have hb (n : ℕ) : ‖χ (n : ZMod q)-c‖≤2 := (norm_sub_le _ _).trans (by linarith [χ.norm_le_one (n : ZMod q)])
  have hz : ∑ n∈range q,(χ (n : ZMod q)-c)=0 := by
    rw [sum_sub_distrib,sum_const,card_range,nsmul_eq_mul]
    dsimp [c,characterMean]
    have hq : (q:ℂ)≠0 := by exact_mod_cast NeZero.ne q
    field_simp
    ring
  have hr := periodic_sum_norm_le_mul (NeZero.pos q) (by norm_num : (0:ℝ)≤2)
    (f:=fun n => χ (n : ZMod q)-c) (by intro n; simp) hz hb (⌊t⌋₊+1)
  have he : ∑ n∈range (⌊t⌋₊+1),(χ (n : ZMod q)-c) =
      χ (0 : ZMod q)-c+ ∑ n∈Icc 1 ⌊t⌋₊,(χ (n : ZMod q)-c) := by
    rw [Nat.range_succ_eq_Icc_zero,←Finset.insert_Icc_add_one_left_eq_Icc (Nat.zero_le ⌊t⌋₊)]
    simp
    ring
  have ht0 : 0≤t := by linarith
  have hfloor : ‖(⌊t⌋₊:ℂ)-(t:ℂ)‖≤1 := by
    rw [←Complex.ofReal_natCast,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonpos (sub_nonpos.mpr (Nat.floor_le ht0))]
    have := Nat.lt_floor_add_one t
    linarith
  have heq : seriesDiscrepancy (positiveCoefficients (fun n => χ (n : ZMod q))) c t =
      (∑ n∈range (⌊t⌋₊+1),(χ (n : ZMod q)-c))-(χ 0-c)+c*((⌊t⌋₊:ℂ)-(t:ℂ)) := by
    rw [he]
    simp only [seriesDiscrepancy,sum_positiveCoefficients,sum_sub_distrib,sum_const,Nat.card_Icc,
      Nat.add_sub_cancel,nsmul_eq_mul]
    ring
  rw [heq]
  calc
    _ ≤ ‖∑ n∈range (⌊t⌋₊+1),(χ (n : ZMod q)-c)‖+‖χ 0-c‖+‖c*((⌊t⌋₊:ℂ)-(t:ℂ))‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ (q:ℝ)*2+2+1 := by
      gcongr
      · simpa using hb 0
      · rw [norm_mul]; exact (mul_le_mul hc hfloor (norm_nonneg _) zero_le_one).trans_eq (by ring)
    _ = _ := by ring

lemma LFunction_regularSeries_characterMean {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1<s.re) :
    χ.LFunction s = regularSeries (positiveCoefficients (fun n => χ (n : ZMod q))) (characterMean χ) s+
      characterMean χ/(s-1) := by
  rw [regularSeries_eq_LSeries_sub (positiveCoefficients_norm_le (fun n => χ.norm_le_one _))
    (by positivity : (0:ℝ)≤2*q+3) (fun t ht => discrepancy_characterMean_bound χ ht.le) hs,
    sub_add_cancel,LSeries_positiveCoefficients,←χ.LFunction_eq_LSeries hs]

lemma LFunction_deriv_norm_small_power {ε : ℝ} (hε : 0<ε) (hε1 : ε≤1/2) :
    ∃ K : ℝ,0<K ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),χ≠1 →
      ∀ s : ℂ,1-ε/2 ≤ s.re → ‖deriv χ.LFunction s‖≤K*((q+2)*(‖s‖+2))^(2*ε) := by
  obtain ⟨K,hK,h⟩ := regularSeries_deriv_norm_small_power hε hε1
  refine ⟨K,hK,?_⟩
  intro q _ χ hχ s hs
  have he : regularSeries (positiveCoefficients (fun n => χ (n : ZMod q))) 0 =ᶠ[𝓝 s] χ.LFunction := by
    filter_upwards [(continuous_re.tendsto s).eventually (lt_mem_nhds (by linarith : 0<s.re))] with z hz
    exact regularSeries_character_eq hχ hz
  rw [←he.deriv_eq]
  have hb := h _ 0 (q+1) (positiveCoefficients_zero _) (positiveCoefficients_norm_le (fun n => χ.norm_le_one _))
    (by simp) (by positivity) (fun t _ => discrepancy_character_bound hχ t) s hs
  convert hb using 1
  congr 3
  ring

noncomputable def characterRegular {q : ℕ} (χ : DirichletCharacter ℂ q) : ℂ → ℂ :=
  regularSeries (positiveCoefficients (fun n => χ (n : ZMod q))) (characterMean χ)

lemma character_line_bounds {ε : ℝ} (hε : 0<ε) (hε1 : ε≤1/2) :
    ∃ K : ℝ,1≤K ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ),
      (∀ s : ℂ,1 ≤ s.re → ‖s‖+2≤4*(|t|+2) →
        ‖characterRegular χ s‖≤K*((q+2)*(|t|+2))^(2*ε)) ∧
      (χ≠1 → ∀ s : ℂ,1 ≤ s.re → ‖s‖+2≤4*(|t|+2) →
        ‖deriv χ.LFunction s‖≤K*((q+2)*(|t|+2))^(2*ε)) := by
  obtain ⟨K₀,hK₀,h₀⟩ := regularSeries_norm_small_power hε hε1
  obtain ⟨K₁,hK₁,h₁⟩ := LFunction_deriv_norm_small_power hε hε1
  let K := 1+K₀*8^(2*ε)+K₁*4^(2*ε)
  have hp₀ : 0≤K₀*8^(2*ε) := by positivity
  have hp₁ : 0≤K₁*4^(2*ε) := by positivity
  have hK : 1≤K := by dsimp [K]; linarith
  refine ⟨K,hK,?_⟩
  intro q _ χ t
  have hq : (0:ℝ)≤q := Nat.cast_nonneg q
  have ht : 0≤|t| := abs_nonneg t
  have hp : 0≤((q:ℝ)+2)*(|t|+2) := by positivity
  have he : 0≤2*ε := by positivity
  constructor
  · intro s hs hn
    have hb := h₀ _ (characterMean χ) (2*q+3) (positiveCoefficients_zero _)
      (positiveCoefficients_norm_le (fun n => χ.norm_le_one _)) (characterMean_norm_le χ)
      (by positivity) (fun t ht => discrepancy_characterMean_bound χ ht) s (by linarith)
    change ‖characterRegular χ s‖≤_ at hb
    have hb' : (2*q+3+1)*(‖s‖+2)≤8*(((q:ℝ)+2)*(|t|+2)) := by
      nlinarith [mul_nonneg (show (0:ℝ)≤2*q+4 by positivity) (sub_nonneg.mpr hn)]
    calc
      _ ≤ K₀*((2*q+3+1)*(‖s‖+2))^(2*ε) := hb
      _ ≤ K₀*(8*(((q:ℝ)+2)*(|t|+2)))^(2*ε) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hb' he) hK₀.le
      _ = (K₀*8^(2*ε))*(((q:ℝ)+2)*(|t|+2))^(2*ε) := by rw [Real.mul_rpow (by norm_num) hp]; ring
      _ ≤ _ := by gcongr; dsimp [K]; linarith
  · intro hχ s hs hn
    have hb := h₁ q χ hχ s (by linarith)
    have hb' : (q+2)*(‖s‖+2)≤4*(((q:ℝ)+2)*(|t|+2)) := by
      nlinarith [mul_nonneg (show (0:ℝ)≤q+2 by positivity) (sub_nonneg.mpr hn)]
    calc
      _ ≤ K₁*((q+2)*(‖s‖+2))^(2*ε) := hb
      _ ≤ K₁*(4*(((q:ℝ)+2)*(|t|+2)))^(2*ε) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hb' he) hK₁.le
      _ = (K₁*4^(2*ε))*(((q:ℝ)+2)*(|t|+2))^(2*ε) := by rw [Real.mul_rpow (by norm_num) hp]; ring
      _ ≤ _ := by gcongr; dsimp [K]; linarith

lemma line_growth_lipschitz {f : ℂ → ℂ} {t D : ℝ} (hf : Differentiable ℂ f)
    (hb : ∀ s : ℂ,1 ≤ s.re → ‖s‖+2≤4*(|t|+2) → ‖deriv f s‖≤D)
    {z w : ℂ} (hz : 1 ≤ z.re) (hw : 1 ≤ w.re)
    (hzn : ‖z‖+2≤4*(|t|+2)) (hwn : ‖w‖+2≤4*(|t|+2)) :
    ‖f z-f w‖≤D*‖z-w‖ := by
  let S := {s : ℂ | 1 ≤ s.re} ∩ Metric.closedBall 0 (4*(|t|+2)-2)
  have hS : Convex ℝ S := (convex_halfSpace_re_ge 1).inter (convex_closedBall 0 _)
  apply Convex.norm_image_sub_le_of_norm_deriv_le (s:=S) (fun z _ => hf z) ?_ hS
      ⟨hw,by simp [Metric.mem_closedBall,dist_zero_right]; linarith⟩
      ⟨hz,by simp [Metric.mem_closedBall,dist_zero_right]; linarith⟩
  intro s hs
  exact hb s hs.1 (by have := hs.2; simp only [Metric.mem_closedBall,dist_zero_right] at this; linarith)

end
lemma three_four_one_lower {a D E : ℝ} (ha : 0≤a) (hD : 1≤D) (hE : 1≤E)
    (h : ∀ δ : ℝ,0<δ → δ≤1 → 1≤(2*D/δ)^3*(a+D*δ)^4*E) :
    1/(256*D^6*E)≤a := by
  have hD0 : 0<D := by linarith
  have hE0 : 0<E := by linarith
  let δ := 1/(256*D^7*E)
  have hδ : 0<δ := by dsimp [δ]; positivity
  have hδ1 : δ≤1 := by
    have hp : (1:ℝ)≤D^7 := one_le_pow₀ hD
    have hp' : (1:ℝ)≤D^7*E := one_le_mul_of_one_le_of_one_le hp hE
    dsimp [δ]
    apply (div_le_one (by positivity)).mpr
    linarith
  have he : 1/(256*D^6*E)=D*δ := by dsimp [δ]; field_simp
  rw [he]
  by_contra! han
  have hb : a+D*δ≤2*D*δ := by linarith
  have hh := h δ hδ hδ1
  have hu : (2*D/δ)^3*(a+D*δ)^4*E≤(2*D/δ)^3*(2*D*δ)^4*E := by gcongr
  have hv : (2*D/δ)^3*(2*D*δ)^4*E=1/2 := by dsimp [δ]; field_simp; norm_num
  rw [hv] at hu
  linarith

open Complex Filter Topology Finset
lemma line_sample_norm {δ t u : ℝ} (hδ : 0≤δ) (hδ1 : δ≤1) (hu : |u|≤2*|t|) :
    ‖(1:ℂ)+δ+I*u‖+2≤4*(|t|+2) := by
  have h := Complex.norm_le_abs_re_add_abs_im ((1:ℂ)+δ+I*u)
  simp only [Complex.add_re,Complex.one_re,Complex.ofReal_re,Complex.mul_re,Complex.I_re,
    Complex.I_im,Complex.ofReal_im,mul_zero,zero_mul,sub_self,add_zero,Complex.add_im,
    Complex.one_im,Complex.mul_im,one_mul,zero_add] at h
  rw [abs_of_nonneg (by linarith : (0:ℝ)≤1+δ)] at h
  linarith [abs_nonneg t]

lemma LFunction_norm_le_regular_add_pole {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1<s.re) :
    ‖χ.LFunction s‖≤‖characterRegular χ s‖+1/‖s-1‖ := by
  rw [LFunction_regularSeries_characterMean χ hs]
  apply (norm_add_le _ _).trans
  dsimp [characterRegular]
  apply add_le_add le_rfl
  rw [norm_div]
  exact div_le_div_of_nonneg_right (characterMean_norm_le χ) (norm_nonneg _)

lemma characterRegular_eq_nonprincipal {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ≠1) {s : ℂ} (hs : 0<s.re) : characterRegular χ s=χ.LFunction s := by
  rw [characterRegular,characterMean_eq_zero hχ,regularSeries_character_eq hχ hs]

lemma nonprincipal_line_lower_aux {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ≠1) {t c K P : ℝ} (hc : 0<c) (_hc1 : c≤1) (hK : 1≤K) (hP : 1≤P)
    (hr : ∀ ψ : DirichletCharacter ℂ q,∀ s : ℂ,1 ≤ s.re → ‖s‖+2≤4*(|t|+2) →
      ‖characterRegular ψ s‖≤K*P)
    (hd : ∀ s : ℂ,1 ≤ s.re → ‖s‖+2≤4*(|t|+2) → ‖deriv χ.LFunction s‖≤K*P)
    (hsi : χ^2=1 → c/P≤‖χ.LFunction 1‖) :
    min (c/2) (1/(256*K^6*(K+K/c)))/P^8≤‖χ.LFunction (1+I*t)‖ := by
  have hK0 : 0<K := by linarith
  have hP0 : 0<P := by linarith
  have hhc : 0<K+K/c := by positivity
  have hKP : 1≤K*P := one_le_mul_of_one_le_of_one_le hK hP
  have hn0 : ‖(1:ℂ)+I*t‖+2≤4*(|t|+2) := by
    simpa using line_sample_norm (t:=t) (u:=t) (δ:=0) le_rfl zero_le_one (by linarith [abs_nonneg t])
  have hn1 : ‖(1:ℂ)‖+2≤4*(|t|+2) := by norm_num; linarith [abs_nonneg t]
  by_cases hsmall : χ^2=1 ∧ |t|≤c/(2*K*P^2)
  · have hdiff := line_growth_lipschitz (DirichletCharacter.differentiable_LFunction hχ) hd
      (z:=1) (w:=1+I*t) (by simp) (by simp) hn1 hn0
    have hnorm : ‖(1:ℂ)-(1+I*t)‖=|t| := by
      rw [show (1:ℂ)-(1+I*t)=-(I*t) by ring,norm_neg,norm_mul,Complex.norm_I,one_mul,
        Complex.norm_real,Real.norm_eq_abs]
    rw [hnorm] at hdiff
    have hdiff' : ‖χ.LFunction 1-χ.LFunction (1+I*t)‖≤c/(2*P) := by
      calc
        _ ≤ K*P*|t| := hdiff
        _ ≤ K*P*(c/(2*K*P^2)) := mul_le_mul_of_nonneg_left hsmall.2 (by positivity)
        _ = _ := by field_simp
    have hval : c/(2*P)≤‖χ.LFunction (1+I*t)‖ := by
      have htri := norm_add_le (χ.LFunction 1-χ.LFunction (1+I*t)) (χ.LFunction (1+I*t))
      rw [sub_add_cancel] at htri
      have he : c/P=2*(c/(2*P)) := by ring
      have hsi' := hsi hsmall.1
      rw [he] at hsi'
      linarith
    have hP8 : P≤P^8 := by simpa using pow_le_pow_right₀ hP (show (1:ℕ)≤8 by norm_num)
    calc
      _ ≤ (c/2)/P^8 := div_le_div_of_nonneg_right (min_le_left _ _) (by positivity)
      _ ≤ (c/2)/P := div_le_div_of_nonneg_left (by positivity) hP0 hP8
      _ = c/(2*P) := by ring
      _ ≤ _ := hval
  · have hLo : 1/(256*(K*P)^6*((K+K/c)*P^2))≤‖χ.LFunction (1+I*t)‖ := by
      apply three_four_one_lower (norm_nonneg _) hKP
        (one_le_mul_of_one_le_of_one_le (by linarith [div_pos hK0 hc]) (one_le_pow₀ hP))
      intro δ hδ hδ1
      have hrδ : ((1:ℂ)+δ+I*t).re=1+δ := by simp
      have hrδ2 : ((1:ℂ)+δ+2*I*t).re=1+δ := by simp
      have hnδ := line_sample_norm hδ.le hδ1 (t:=t) (u:=t) (by linarith [abs_nonneg t])
      have hnδ2 : ‖(1:ℂ)+δ+2*I*t‖+2≤4*(|t|+2) := by
        simpa only [show I*((2*t:ℝ):ℂ)=2*I*t by push_cast; ring] using
          line_sample_norm hδ.le hδ1 (t:=t) (u:=2*t) (by rw [abs_mul]; norm_num)
      have hL0 : ‖DirichletCharacter.LFunctionTrivChar q (1+δ)‖≤2*(K*P)/δ := by
        have hn : ‖(1:ℂ)+δ‖+2≤4*(|t|+2) := by
          simpa using line_sample_norm hδ.le hδ1 (t:=t) (u:=0) (by simp)
        have hreg := hr (1:DirichletCharacter ℂ q) (1+δ) (by simp; linarith) hn
        have hp := LFunction_norm_le_regular_add_pole (1:DirichletCharacter ℂ q)
          (s:=1+δ) (by simp; linarith)
        have hden : ‖(1:ℂ)+δ-1‖=δ := by simp [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hδ]
        rw [hden] at hp
        change ‖DirichletCharacter.LFunction (1:DirichletCharacter ℂ q) (1+δ)‖≤_
        apply (hp.trans (add_le_add hreg le_rfl)).trans
        apply (le_div_iff₀ hδ).mpr
        have hd : (K*P)*δ≤K*P := mul_le_of_le_one_right (by positivity) hδ1
        field_simp
        nlinarith
      have hLχ : ‖χ.LFunction (1+δ+I*t)‖≤‖χ.LFunction (1+I*t)‖+(K*P)*δ := by
        have hl := line_growth_lipschitz (DirichletCharacter.differentiable_LFunction hχ) hd
          (z:=1+δ+I*t) (w:=1+I*t) (by simp; linarith) (by simp) hnδ hn0
        have hden : ‖(1:ℂ)+δ+I*t-(1+I*t)‖=δ := by
          rw [show (1:ℂ)+δ+I*t-(1+I*t)=(δ:ℂ) by ring,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hδ]
        rw [hden] at hl
        have ht := norm_add_le (χ.LFunction (1+δ+I*t)-χ.LFunction (1+I*t)) (χ.LFunction (1+I*t))
        rw [sub_add_cancel] at ht
        linarith
      have hL2 : ‖(χ^2).LFunction (1+δ+2*I*t)‖≤(K+K/c)*P^2 := by
        by_cases hχ2 : χ^2=1
        · have ht : c/(2*K*P^2)< |t| := lt_of_not_ge (fun ht => hsmall ⟨hχ2,ht⟩)
          have ht0 : 0< |t| := (by positivity : 0<c/(2*K*P^2)).trans ht
          have hp := LFunction_norm_le_regular_add_pole (χ^2) (s:=1+δ+2*I*t) (by rw [hrδ2]; linarith)
          have hn : 2*|t|≤‖(1:ℂ)+δ+2*I*t-1‖ := by
            have h := Complex.abs_im_le_norm ((1:ℂ)+δ+2*I*t-1)
            simpa [abs_mul] using h
          have hfrac : 1/‖(1:ℂ)+δ+2*I*t-1‖≤K*P^2/c := by
            apply (div_le_div_of_nonneg_left zero_le_one (by positivity : 0<2*|t|) hn).trans
            apply (div_le_iff₀ (by positivity : 0<2*|t|)).mpr
            have ht' := (div_lt_iff₀ (by positivity : 0<2*K*P^2)).mp ht
            rw [div_mul_eq_mul_div]
            apply (le_div_iff₀ hc).mpr
            nlinarith
          have hreg := hr (χ^2) (1+δ+2*I*t) (by rw [hrδ2]; linarith) hnδ2
          have hP2 : P≤P^2 := by nlinarith
          have h := hp.trans (add_le_add hreg hfrac)
          apply h.trans
          calc
            K*P+K*P^2/c ≤ K*P^2+K*P^2/c := add_le_add (mul_le_mul_of_nonneg_left hP2 hK0.le) le_rfl
            _ = _ := by ring
        · have hreg := hr (χ^2) (1+δ+2*I*t) (by rw [hrδ2]; linarith) hnδ2
          rw [characterRegular_eq_nonprincipal hχ2 (by rw [hrδ2]; linarith)] at hreg
          have hP2 : P≤P^2 := by nlinarith
          exact hreg.trans (by nlinarith [mul_le_mul_of_nonneg_left hP2 hK0.le,div_pos hK0 hc])
      have hprod := χ.norm_LFunction_product_ge_one hδ t
      simp only [norm_mul,norm_pow] at hprod
      exact hprod.trans (by gcongr)
    calc
      _ ≤ (1/(256*K^6*(K+K/c)))/P^8 := div_le_div_of_nonneg_right (min_le_right _ _) (by positivity)
      _ = 1/(256*(K*P)^6*((K+K/c)*P^2)) := by field_simp
      _ ≤ _ := hLo

lemma nonprincipal_line_lower {ε : ℝ} (hε : 0<ε) (hε1 : ε≤1) :
    ∃ c : ℝ,0<c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → χ≠1 → ∀ t : ℝ,
        c*(((q:ℝ)+2)*(|t|+2))^(-ε)≤‖χ.LFunction (1+I*t)‖ := by
  obtain ⟨K,hK,hgrowth⟩ := character_line_bounds (by linarith : 0<ε/16) (by linarith : ε/16≤1/2)
  obtain ⟨c₀,hc₀,hsiegel⟩ := quadratic_siegel (by linarith : 0<ε/8) (by linarith : ε/8≤1)
  let c := min c₀ 1
  have hc : 0<c := lt_min hc₀ zero_lt_one
  have hc1 : c≤1 := min_le_right _ _
  let d := min (c/2) (1/(256*K^6*(K+K/c)))
  have hK0 : 0<K := by linarith
  have hd : 0<d := by dsimp [d]; positivity
  refine ⟨d,hd,?_⟩
  intro q _ χ hχp hχ t
  let X : ℝ := ((q:ℝ)+2)*(|t|+2)
  let P : ℝ := X^(ε/8)
  have hX : 1≤X := by dsimp [X]; nlinarith [Nat.cast_nonneg (α:=ℝ) q,abs_nonneg t]
  have hX0 : 0<X := by linarith
  have hP : 1≤P := Real.one_le_rpow hX (by positivity)
  have he : 2*(ε/16)=ε/8 := by ring
  have hsi : χ^2=1 → c/P≤‖χ.LFunction 1‖ := by
    intro hχ2
    have hq : (q:ℝ)+1≤X := by dsimp [X]; nlinarith [Nat.cast_nonneg (α:=ℝ) q,abs_nonneg t]
    calc
      c/P = c*X^(-(ε/8)) := by rw [Real.rpow_neg hX0.le]; rfl
      _ ≤ c₀*((q:ℝ)+1)^(-(ε/8)) := by
        apply mul_le_mul (min_le_left _ _) (Real.rpow_le_rpow_of_nonpos (by positivity) hq (by linarith))
          (Real.rpow_nonneg hX0.le _) hc₀.le
      _ ≤ _ := hsiegel q χ hχp hχ hχ2
  have hh := nonprincipal_line_lower_aux hχ hc hc1 hK hP
    (fun ψ s hs hn => by simpa only [he] using (hgrowth q ψ t).1 s hs hn)
    (fun s hs hn => by simpa only [he] using (hgrowth q χ t).2 hχ s hs hn) hsi
  have hP8 : P^8=X^ε := by
    dsimp [P]
    rw [←Real.rpow_mul_natCast hX0.le]
    congr 1
    norm_num
  change d/P^8≤_ at hh
  rw [hP8] at hh
  change d*X^(-ε)≤_
  simpa only [Real.rpow_neg hX0.le,div_eq_mul_inv] using hh

lemma character_interior_lower {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {t K P δ : ℝ} (hK : 1≤K) (hP : 1≤P) (hδ : 0<δ) (hδ1 : δ≤1)
    (hr : ∀ ψ : DirichletCharacter ℂ q,∀ s : ℂ,1 ≤ s.re → ‖s‖+2≤4*(|t|+2) →
      ‖characterRegular ψ s‖≤K*P) :
    δ/(2*K*P)≤‖χ.LFunction (1+δ+I*t)‖ := by
  have hKP : 1≤K*P := one_le_mul_of_one_le_of_one_le hK hP
  have hKP0 : 0<K*P := by linarith
  have hb (ψ : DirichletCharacter ℂ q) (u : ℝ) (hu : |u|≤2*|t|) :
      ‖ψ.LFunction (1+δ+I*u)‖≤2*K*P/δ := by
    have hp := LFunction_norm_le_regular_add_pole ψ (s:=1+δ+I*u) (by simp; linarith)
    have hn : δ≤‖(1:ℂ)+δ+I*u-1‖ := by
      simpa using Complex.re_le_norm ((1:ℂ)+δ+I*u-1)
    have hreg := hr ψ (1+δ+I*u) (by simp; linarith) (line_sample_norm hδ.le hδ1 hu)
    have hfrac := div_le_div_of_nonneg_left zero_le_one hδ hn
    apply (hp.trans (add_le_add hreg hfrac)).trans
    apply (le_div_iff₀ hδ).mpr
    have hd := mul_le_of_le_one_right hKP0.le hδ1
    have he : (K*P+1/δ)*δ=K*P*δ+1 := by field_simp
    rw [he]
    nlinarith
  have h0 : ‖DirichletCharacter.LFunctionTrivChar q (1+δ)‖≤2*K*P/δ := by
    simpa using hb (1:DirichletCharacter ℂ q) 0 (by simp)
  have h2 : ‖(χ^2).LFunction (1+δ+2*I*t)‖≤2*K*P/δ := by
    simpa only [show I*((2*t:ℝ):ℂ)=2*I*t by push_cast; ring] using hb (χ^2) (2*t) (by rw [abs_mul]; norm_num)
  have hh := χ.norm_LFunction_product_ge_one hδ t
  simp only [norm_mul,norm_pow] at hh
  have hu : 1≤(2*K*P/δ)^3*‖χ.LFunction (1+δ+I*t)‖^4*(2*K*P/δ) := hh.trans (by gcongr)
  have hp : (1:ℝ)^4≤((2*K*P/δ)*‖χ.LFunction (1+δ+I*t)‖)^4 := by convert hu using 1 <;> ring
  have hv := le_of_pow_le_pow_left₀ (by norm_num : (4:ℕ)≠0) (by positivity) hp
  apply (div_le_iff₀ (by positivity : 0<2*K*P)).mpr
  have he : (2*K*P/δ)*‖χ.LFunction (1+δ+I*t)‖=(‖χ.LFunction (1+δ+I*t)‖*(2*K*P))/δ := by ring
  rw [he] at hv
  simpa only [one_mul] using (le_div_iff₀ hδ).mp hv

lemma nonprincipal_strip_lower_aux {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ≠1) {t c K P δ : ℝ} (hc : 0<c) (hK : 1≤K) (hP : 1≤P)
    (hδ : 0≤δ) (hδ1 : δ≤1)
    (hr : ∀ ψ : DirichletCharacter ℂ q,∀ s : ℂ,1 ≤ s.re → ‖s‖+2≤4*(|t|+2) →
      ‖characterRegular ψ s‖≤K*P)
    (hd : ∀ s : ℂ,1 ≤ s.re → ‖s‖+2≤4*(|t|+2) → ‖deriv χ.LFunction s‖≤K*P)
    (hl : c/P≤‖χ.LFunction (1+I*t)‖) :
    (c/(4*K^2))/P^3≤‖χ.LFunction (1+δ+I*t)‖ := by
  have hK0 : 0<K := by linarith
  have hP0 : 0<P := by linarith
  by_cases hnear : δ≤c/(2*K*P^2)
  · have hn0 : ‖(1:ℂ)+I*t‖+2≤4*(|t|+2) := by
      simpa using line_sample_norm (t:=t) (u:=t) (δ:=0) le_rfl zero_le_one (by linarith [abs_nonneg t])
    have hnδ := line_sample_norm hδ hδ1 (t:=t) (u:=t) (by linarith [abs_nonneg t])
    have hdif := line_growth_lipschitz (DirichletCharacter.differentiable_LFunction hχ) hd
      (z:=1+I*t) (w:=1+δ+I*t) (by simp) (by simp; linarith) hn0 hnδ
    have hnorm : ‖(1:ℂ)+I*t-(1+δ+I*t)‖=δ := by
      rw [show (1:ℂ)+I*t-(1+δ+I*t)=-(δ:ℂ) by ring,norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hδ]
    rw [hnorm] at hdif
    have hdb : ‖χ.LFunction (1+I*t)-χ.LFunction (1+δ+I*t)‖≤c/(2*P) := by
      apply hdif.trans
      calc
        K*P*δ ≤ K*P*(c/(2*K*P^2)) := mul_le_mul_of_nonneg_left hnear (by positivity)
        _ = _ := by field_simp
    have htri := norm_add_le (χ.LFunction (1+I*t)-χ.LFunction (1+δ+I*t)) (χ.LFunction (1+δ+I*t))
    rw [sub_add_cancel] at htri
    have hva : c/(2*P)≤‖χ.LFunction (1+δ+I*t)‖ := by
      have he : c/P=2*(c/(2*P)) := by ring
      rw [he] at hl
      linarith
    apply le_trans ?_ hva
    rw [div_div]
    apply div_le_div_of_nonneg_left hc.le (by positivity)
    have hP3 : P≤P^3 := by simpa using pow_le_pow_right₀ hP (show (1:ℕ)≤3 by norm_num)
    have hK2 : 1≤K^2 := one_le_pow₀ hK
    nlinarith [mul_le_mul_of_nonneg_left hP3 (show (0:ℝ)≤4*K^2 by positivity)]
  · have hδ0 : 0<δ := (by positivity : 0<c/(2*K*P^2)).trans (lt_of_not_ge hnear)
    apply le_trans ?_ (character_interior_lower χ hK hP hδ0 hδ1 hr)
    calc
      (c/(4*K^2))/P^3 = (c/(2*K*P^2))/(2*K*P) := by field_simp; norm_num
      _ ≤ δ/(2*K*P) := div_le_div_of_nonneg_right (le_of_not_ge hnear) (by positivity)

lemma nonprincipal_strip_lower {ε : ℝ} (hε : 0<ε) (hε1 : ε≤1) :
    ∃ c : ℝ,0<c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → χ≠1 → ∀ σ t : ℝ, 1≤σ → σ≤2 →
        c*(((q:ℝ)+2)*(|t|+2))^(-ε)≤‖χ.LFunction (σ+I*t)‖ := by
  obtain ⟨K,hK,hg⟩ := character_line_bounds (by linarith : 0<ε/6) (by linarith : ε/6≤1/2)
  obtain ⟨c,hc,hl⟩ := nonprincipal_line_lower (by linarith : 0<ε/3) (by linarith : ε/3≤1)
  have hK0 : 0<K := by linarith
  refine ⟨c/(4*K^2),by positivity,?_⟩
  intro q _ χ hχp hχ σ t hσ hσ2
  let X : ℝ := ((q:ℝ)+2)*(|t|+2)
  let P : ℝ := X^(ε/3)
  have hX : 1≤X := by dsimp [X]; nlinarith [Nat.cast_nonneg (α:=ℝ) q,abs_nonneg t]
  have hX0 : 0<X := by linarith
  have hP : 1≤P := Real.one_le_rpow hX (by positivity)
  have he : 2*(ε/6)=ε/3 := by ring
  have hl' : c/P≤‖χ.LFunction (1+I*t)‖ := by
    have hh := hl q χ hχp hχ t
    change c*X^(-(ε/3))≤_ at hh
    change c/X^(ε/3)≤_
    simpa only [Real.rpow_neg hX0.le,div_eq_mul_inv] using hh
  have hb := nonprincipal_strip_lower_aux hχ hc hK hP (δ:=σ-1) (by linarith) (by linarith)
    (fun ψ s hs hn => by simpa only [he] using (hg q ψ t).1 s hs hn)
    (fun s hs hn => by simpa only [he] using (hg q χ t).2 hχ s hs hn) hl'
  have hP3 : P^3=X^ε := by dsimp [P]; rw [←Real.rpow_mul_natCast hX0.le]; congr 1; norm_num
  rw [hP3] at hb
  have hs : (1:ℂ)+((σ-1:ℝ):ℂ)+I*t=(σ:ℂ)+I*t := by push_cast; ring
  rw [hs] at hb
  change (c/(4*K^2))*X^(-ε)≤_
  simpa only [Real.rpow_neg hX0.le,div_eq_mul_inv] using hb

end LargePrimeGaps
end OAI

-- Source module: PrincipalGrowth
namespace OAI
namespace LargePrimeGaps
open Complex Filter Topology
lemma zetaRegular_bounds {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1/2) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ s : ℂ, 1-ε/2 ≤ s.re →
      ‖zetaRegular s‖ ≤ K*(‖s‖+2)^(2*ε) ∧
      ‖deriv zetaRegular s‖ ≤ K*(‖s‖+2)^(2*ε) := by
  obtain ⟨K₀,hK₀,h₀⟩ := regularSeries_norm_small_power hε hε1
  obtain ⟨K₁,hK₁,h₁⟩ := regularSeries_deriv_norm_small_power hε hε1
  let K := 1+(K₀+K₁)*2^(2*ε)
  have hK : 1 ≤ K := by dsimp [K]; linarith [show 0 < (K₀+K₁)*2^(2*ε) by positivity]
  refine ⟨K,hK,?_⟩
  intro s hs
  have hb₀ := h₀ _ 1 1 (positiveCoefficients_zero _) (positiveCoefficients_norm_le (by simp))
    (by simp) zero_le_one (fun t ht => discrepancy_constant_bound ht) s (by linarith)
  have hb₁ := h₁ _ 1 1 (positiveCoefficients_zero _) (positiveCoefficients_norm_le (by simp))
    (by simp) zero_le_one (fun t ht => discrepancy_constant_bound ht) s hs
  change ‖zetaRegular s‖ ≤ _ at hb₀
  change ‖deriv zetaRegular s‖ ≤ _ at hb₁
  norm_num only [one_add_one_eq_two] at hb₀ hb₁
  rw [Real.mul_rpow (by norm_num) (by positivity)] at hb₀ hb₁
  constructor
  · apply hb₀.trans
    have hc : K₀*2^(2*ε) ≤ K := by dsimp [K]; nlinarith [Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<2) (2*ε)]
    calc
      _ = (K₀*2^(2*ε))*(‖s‖+2)^(2*ε) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hc (by positivity)
  · apply hb₁.trans
    have hc : K₁*2^(2*ε) ≤ K := by dsimp [K]; nlinarith [Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<2) (2*ε)]
    calc
      _ = (K₁*2^(2*ε))*(‖s‖+2)^(2*ε) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hc (by positivity)

lemma zeta_deriv_eq_regular {s : ℂ} (hs : 0 < s.re) (hs1 : s≠1) :
    deriv riemannZeta s = deriv zetaRegular s-1/(s-1)^2 := by
  have he : riemannZeta =ᶠ[𝓝 s] fun z => zetaRegular z+1/(z-1) := by
    filter_upwards [(continuous_re.tendsto s).eventually (lt_mem_nhds hs),
      eventually_ne_nhds hs1] with z hz hz1
    rw [zetaRegular_eq hz hz1,sub_add_cancel]
  rw [he.deriv_eq]
  have hd := (hasDerivAt_const s (1:ℂ)).div ((hasDerivAt_id s).sub_const 1) (sub_ne_zero.mpr hs1)
  have hh := (zetaRegular_differentiableAt hs).hasDerivAt.add hd
  simpa only [Pi.add_def, Pi.div_def, id_eq, zero_mul, one_mul, zero_sub, neg_div, sub_eq_add_neg, zero_add] using hh.deriv

lemma horizontal_growth_lipschitz {f : ℂ → ℂ} {t D : ℝ}
    (hf : ∀ s : ℂ, 1 ≤ s.re → s.im=t → DifferentiableAt ℂ f s)
    (hb : ∀ s : ℂ, 1 ≤ s.re → s.im=t → ‖s‖+2 ≤ 4*(|t|+2) → ‖deriv f s‖ ≤ D)
    {z w : ℂ} (hz : 1 ≤ z.re) (hw : 1 ≤ w.re) (hzt : z.im=t) (hwt : w.im=t)
    (hzn : ‖z‖+2 ≤ 4*(|t|+2)) (hwn : ‖w‖+2 ≤ 4*(|t|+2)) :
    ‖f z-f w‖ ≤ D*‖z-w‖ := by
  let S := ({s : ℂ | 1 ≤ s.re} ∩ {s : ℂ | s.im=t}) ∩ Metric.closedBall 0 (4*(|t|+2)-2)
  have hi : Convex ℝ {s : ℂ | s.im=t} := convex_hyperplane (.mk Complex.add_im Complex.smul_im) t
  have hS : Convex ℝ S := ((convex_halfSpace_re_ge 1).inter hi).inter (convex_closedBall 0 _)
  apply Convex.norm_image_sub_le_of_norm_deriv_le (s:=S) (fun z hz => hf z hz.1.1 hz.1.2) ?_ hS
    ⟨⟨hw,hwt⟩,by simp [Metric.mem_closedBall,dist_zero_right]; linarith⟩
    ⟨⟨hz,hzt⟩,by simp [Metric.mem_closedBall,dist_zero_right]; linarith⟩
  intro s hs
  exact hb s hs.1.1 hs.1.2 (by have := hs.2; simp only [Metric.mem_closedBall,dist_zero_right] at this; linarith)

lemma zeta_high_line_bounds {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1/2) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ t : ℝ, 1 ≤ |t| →
      (∀ ψ : DirichletCharacter ℂ 1, ∀ s : ℂ, 1 ≤ s.re → ‖s‖+2 ≤ 4*(|t|+2) →
        ‖characterRegular ψ s‖ ≤ K*(|t|+2)^(2*ε)) ∧
      (∀ s : ℂ, 1 ≤ s.re → s.im=t → ‖s‖+2 ≤ 4*(|t|+2) →
        ‖deriv riemannZeta s‖ ≤ K*(|t|+2)^(2*ε)) := by
  obtain ⟨K₀,hK₀,h₀⟩ := character_line_bounds hε hε1
  obtain ⟨K₁,hK₁,h₁⟩ := zetaRegular_bounds hε hε1
  let K := K₀*3^(2*ε)+K₁*4^(2*ε)+1
  have hK₀' : 0 < K₀ := by linarith
  have hK₁' : 0 < K₁ := by linarith
  have hK : 1 ≤ K := by dsimp [K]; linarith [show 0 < K₀*3^(2*ε) by positivity, show 0 < K₁*4^(2*ε) by positivity]
  refine ⟨K,hK,?_⟩
  intro t ht
  have hP : 1 ≤ (|t|+2)^(2*ε) := Real.one_le_rpow (by linarith [abs_nonneg t]) (by positivity)
  constructor
  · intro ψ s hs hn
    have hb := (h₀ 1 ψ t).1 s hs hn
    norm_num only [Nat.cast_one,show (1:ℝ)+2=3 by norm_num] at hb
    rw [Real.mul_rpow (by norm_num) (by positivity)] at hb
    apply hb.trans
    have hc : K₀*3^(2*ε) ≤ K := by dsimp [K]; linarith [show 0 < K₁*4^(2*ε) by positivity]
    convert mul_le_mul_of_nonneg_right hc (by positivity : 0 ≤ (|t|+2)^(2*ε)) using 1
    ring
  · intro s hs him hn
    have hs1 : s≠1 := by intro h; simp [h] at him; rw [←him] at ht; norm_num at ht
    have hd := (h₁ s (by linarith)).2
    have hden : 1 ≤ ‖s-1‖ := by
      have h := Complex.abs_im_le_norm (s-1)
      simp only [Complex.sub_im,Complex.one_im,sub_zero,him] at h
      exact ht.trans h
    have hfrac : ‖(1:ℂ)/(s-1)^2‖ ≤ 1 := by
      simp only [norm_div,norm_one,norm_pow]
      exact div_le_one_of_le₀ (one_le_pow₀ hden) (by positivity)
    rw [zeta_deriv_eq_regular (by linarith) hs1]
    apply (norm_sub_le _ _).trans
    have hnorm := Real.rpow_le_rpow (by positivity : 0 ≤ ‖s‖+2) hn (by positivity : 0 ≤ 2*ε)
    rw [Real.mul_rpow (by norm_num) (by positivity)] at hnorm
    have hc : K₁*4^(2*ε)+1 ≤ K := by dsimp [K]; linarith [show 0 < K₀*3^(2*ε) by positivity]
    calc
      _ ≤ K₁*(‖s‖+2)^(2*ε)+1 := add_le_add hd hfrac
      _ ≤ (K₁*4^(2*ε))*(|t|+2)^(2*ε)+(|t|+2)^(2*ε) := by nlinarith
      _ = (K₁*4^(2*ε)+1)*(|t|+2)^(2*ε) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hc (by positivity)

lemma zeta_high_line_lower_aux {t K P : ℝ} (ht : 1 ≤ |t|) (hK : 1 ≤ K) (hP : 1 ≤ P)
    (hr : ∀ ψ : DirichletCharacter ℂ 1, ∀ s : ℂ, 1 ≤ s.re → ‖s‖+2 ≤ 4*(|t|+2) →
      ‖characterRegular ψ s‖ ≤ K*P)
    (hd : ∀ s : ℂ, 1 ≤ s.re → s.im=t → ‖s‖+2 ≤ 4*(|t|+2) → ‖deriv riemannZeta s‖ ≤ K*P) :
    (1/(512*K^7))/P^7 ≤ ‖riemannZeta (1+I*t)‖ := by
  have hK0 : 0 < K := by linarith
  have hP0 : 0 < P := by linarith
  have hKP : 1 ≤ K*P := one_le_mul_of_one_le_of_one_le hK hP
  have hh : 1/(256*(K*P)^6*(2*K*P)) ≤ ‖riemannZeta (1+I*t)‖ := by
    apply three_four_one_lower (norm_nonneg _) hKP (by linarith)
    intro δ hδ hδ1
    have hn0 : ‖(1:ℂ)+I*t‖+2 ≤ 4*(|t|+2) := by
      simpa using line_sample_norm (t:=t) (u:=t) (δ:=0) le_rfl zero_le_one (by linarith [abs_nonneg t])
    have hnδ := line_sample_norm hδ.le hδ1 (t:=t) (u:=t) (by linarith [abs_nonneg t])
    have hL0 : ‖DirichletCharacter.LFunctionTrivChar 1 (1+δ)‖ ≤ 2*(K*P)/δ := by
      have hn : ‖(1:ℂ)+δ‖+2 ≤ 4*(|t|+2) := by
        simpa using line_sample_norm hδ.le hδ1 (t:=t) (u:=0) (by simp)
      have hreg := hr 1 (1+δ) (by simp; linarith) hn
      have hp := LFunction_norm_le_regular_add_pole (1:DirichletCharacter ℂ 1)
        (s:=1+δ) (by simp; linarith)
      have hden : ‖(1:ℂ)+δ-1‖=δ := by simp [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hδ]
      rw [hden] at hp
      change ‖DirichletCharacter.LFunction (1:DirichletCharacter ℂ 1) (1+δ)‖ ≤ _
      apply (hp.trans (add_le_add hreg le_rfl)).trans
      apply (le_div_iff₀ hδ).mpr
      have hd := mul_le_of_le_one_right (by positivity : 0 ≤ K*P) hδ1
      field_simp
      nlinarith
    have hL1 : ‖riemannZeta (1+δ+I*t)‖ ≤ ‖riemannZeta (1+I*t)‖+(K*P)*δ := by
      have hf (s : ℂ) (_hs : 1 ≤ s.re) (him : s.im=t) : DifferentiableAt ℂ riemannZeta s := by
        apply differentiableAt_riemannZeta
        intro hs
        simp [hs] at him
        rw [←him] at ht
        norm_num at ht
      have hl := horizontal_growth_lipschitz hf hd (z:=1+δ+I*t) (w:=1+I*t)
        (by simp; linarith) (by simp) (by simp) (by simp) hnδ hn0
      have hden : ‖(1:ℂ)+δ+I*t-(1+I*t)‖=δ := by
        rw [show (1:ℂ)+δ+I*t-(1+I*t)=(δ:ℂ) by ring,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hδ]
      rw [hden] at hl
      have hh := norm_add_le (riemannZeta (1+δ+I*t)-riemannZeta (1+I*t)) (riemannZeta (1+I*t))
      rw [sub_add_cancel] at hh
      linarith
    have hL2 : ‖riemannZeta (1+δ+2*I*t)‖ ≤ 2*K*P := by
      have hn : ‖(1:ℂ)+δ+2*I*t‖+2 ≤ 4*(|t|+2) := by
        simpa only [show I*((2*t:ℝ):ℂ)=2*I*t by push_cast; ring] using
          line_sample_norm hδ.le hδ1 (t:=t) (u:=2*t) (by rw [abs_mul]; norm_num)
      have hp := LFunction_norm_le_regular_add_pole (1:DirichletCharacter ℂ 1)
        (s:=1+δ+2*I*t) (by simp; linarith)
      rw [DirichletCharacter.LFunction_modOne_eq] at hp
      have hreg := hr 1 (1+δ+2*I*t) (by simp; linarith) hn
      have hden : 1 ≤ ‖(1:ℂ)+δ+2*I*t-1‖ := by
        have hb := Complex.abs_im_le_norm ((1:ℂ)+δ+2*I*t-1)
        simp [abs_mul] at hb
        linarith
      have hfrac : 1/‖(1:ℂ)+δ+2*I*t-1‖ ≤ 1 := div_le_one_of_le₀ hden (norm_nonneg _)
      linarith
    have hprod := (1:DirichletCharacter ℂ 1).norm_LFunction_product_ge_one hδ t
    simp only [one_pow,DirichletCharacter.LFunction_modOne_eq,norm_mul,norm_pow] at hprod
    have hL0' : ‖riemannZeta (1+δ)‖ ≤ 2*(K*P)/δ := by
      simpa only [DirichletCharacter.LFunctionTrivChar,DirichletCharacter.LFunction_modOne_eq] using hL0
    exact hprod.trans (by gcongr)
  convert hh using 1
  field_simp
  ring

lemma zeta_high_line_lower {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ, 1 ≤ |t| →
      c*(|t|+2)^(-ε) ≤ ‖riemannZeta (1+I*t)‖ := by
  obtain ⟨K,hK,hg⟩ := zeta_high_line_bounds (by linarith : 0 < ε/14) (by linarith : ε/14 ≤ 1/2)
  have hK0 : 0 < K := by linarith
  refine ⟨1/(512*K^7),by positivity,?_⟩
  intro t ht
  let P : ℝ := (|t|+2)^(ε/7)
  have hP : 1 ≤ P := Real.one_le_rpow (by linarith [abs_nonneg t]) (by positivity)
  have he : 2*(ε/14)=ε/7 := by ring
  have hh := zeta_high_line_lower_aux ht hK hP
    (fun ψ s hs hn => by simpa only [he] using (hg t ht).1 ψ s hs hn)
    (fun s hs him hn => by simpa only [he] using (hg t ht).2 s hs him hn)
  have hP7 : P^7=(|t|+2)^ε := by
    dsimp [P]
    rw [←Real.rpow_mul_natCast (by positivity : 0 ≤ |t|+2)]
    congr 1
    norm_num
  rw [hP7] at hh
  simpa only [Real.rpow_neg (by positivity : 0 ≤ |t|+2),div_eq_mul_inv] using hh

lemma zeta_high_strip_lower_aux {t c K P δ : ℝ} (ht : 1 ≤ |t|) (hc : 0<c) (hK : 1≤K) (hP : 1≤P)
    (hδ : 0≤δ) (hδ1 : δ≤1)
    (hr : ∀ ψ : DirichletCharacter ℂ 1,∀ s : ℂ,1 ≤ s.re → ‖s‖+2≤4*(|t|+2) →
      ‖characterRegular ψ s‖≤K*P)
    (hd : ∀ s : ℂ,1 ≤ s.re → s.im=t → ‖s‖+2≤4*(|t|+2) → ‖deriv riemannZeta s‖≤K*P)
    (hl : c/P≤‖riemannZeta (1+I*t)‖) :
    (c/(4*K^2))/P^3≤‖riemannZeta (1+δ+I*t)‖ := by
  have hK0 : 0<K := by linarith
  have hP0 : 0<P := by linarith
  by_cases hnear : δ≤c/(2*K*P^2)
  · have hn0 : ‖(1:ℂ)+I*t‖+2≤4*(|t|+2) := by
      simpa using line_sample_norm (t:=t) (u:=t) (δ:=0) le_rfl zero_le_one (by linarith [abs_nonneg t])
    have hnδ := line_sample_norm hδ hδ1 (t:=t) (u:=t) (by linarith [abs_nonneg t])
    have hf (s : ℂ) (_hs : 1 ≤ s.re) (him : s.im=t) : DifferentiableAt ℂ riemannZeta s := by
      apply differentiableAt_riemannZeta
      intro hs
      simp [hs] at him
      rw [←him] at ht
      norm_num at ht
    have hdif := horizontal_growth_lipschitz hf hd
      (z:=1+I*t) (w:=1+δ+I*t) (by simp) (by simp; linarith) (by simp) (by simp) hn0 hnδ
    have hnorm : ‖(1:ℂ)+I*t-(1+δ+I*t)‖=δ := by
      rw [show (1:ℂ)+I*t-(1+δ+I*t)=-(δ:ℂ) by ring,norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hδ]
    rw [hnorm] at hdif
    have hdb : ‖riemannZeta (1+I*t)-riemannZeta (1+δ+I*t)‖≤c/(2*P) := by
      apply hdif.trans
      calc
        K*P*δ ≤ K*P*(c/(2*K*P^2)) := mul_le_mul_of_nonneg_left hnear (by positivity)
        _ = _ := by field_simp
    have htri := norm_add_le (riemannZeta (1+I*t)-riemannZeta (1+δ+I*t)) (riemannZeta (1+δ+I*t))
    rw [sub_add_cancel] at htri
    have hva : c/(2*P)≤‖riemannZeta (1+δ+I*t)‖ := by
      have he : c/P=2*(c/(2*P)) := by ring
      rw [he] at hl
      linarith
    apply le_trans ?_ hva
    rw [div_div]
    apply div_le_div_of_nonneg_left hc.le (by positivity)
    have hP3 : P≤P^3 := by simpa using pow_le_pow_right₀ hP (show (1:ℕ)≤3 by norm_num)
    have hK2 : 1≤K^2 := one_le_pow₀ hK
    nlinarith [mul_le_mul_of_nonneg_left hP3 (show (0:ℝ)≤4*K^2 by positivity)]
  · have hδ0 : 0<δ := (by positivity : 0<c/(2*K*P^2)).trans (lt_of_not_ge hnear)
    have hInt := character_interior_lower (1:DirichletCharacter ℂ 1) hK hP hδ0 hδ1 hr
    rw [DirichletCharacter.LFunction_modOne_eq] at hInt
    apply le_trans ?_ hInt
    calc
      (c/(4*K^2))/P^3 = (c/(2*K*P^2))/(2*K*P) := by field_simp; norm_num
      _ ≤ δ/(2*K*P) := div_le_div_of_nonneg_right (le_of_not_ge hnear) (by positivity)

lemma zeta_high_strip_lower {ε : ℝ} (hε : 0<ε) (hε1 : ε≤1) :
    ∃ c : ℝ,0<c ∧ ∀ σ t : ℝ, 1≤σ → σ≤2 → 1 ≤ |t| →
        c*(|t|+2)^(-ε)≤‖riemannZeta (σ+I*t)‖ := by
  obtain ⟨K,hK,hg⟩ := zeta_high_line_bounds (by linarith : 0<ε/6) (by linarith : ε/6≤1/2)
  obtain ⟨c,hc,hl⟩ := zeta_high_line_lower (by linarith : 0<ε/3) (by linarith : ε/3≤1)
  have hK0 : 0<K := by linarith
  refine ⟨c/(4*K^2),by positivity,?_⟩
  intro σ t hσ hσ2 ht
  let X : ℝ := (|t|+2)
  let P : ℝ := X^(ε/3)
  have hX : 1≤X := by dsimp [X]; linarith [abs_nonneg t]
  have hX0 : 0<X := by linarith
  have hP : 1≤P := Real.one_le_rpow hX (by positivity)
  have he : 2*(ε/6)=ε/3 := by ring
  have hl' : c/P≤‖riemannZeta (1+I*t)‖ := by
    have hh := hl t ht
    change c*X^(-(ε/3))≤_ at hh
    change c/X^(ε/3)≤_
    simpa only [Real.rpow_neg hX0.le,div_eq_mul_inv] using hh
  have hb := zeta_high_strip_lower_aux ht hc hK hP (δ:=σ-1) (by linarith) (by linarith)
    (fun ψ s hs hn => by simpa only [he] using (hg t ht).1 ψ s hs hn)
    (fun s hs him hn => by simpa only [he] using (hg t ht).2 s hs him hn) hl'
  have hP3 : P^3=X^ε := by dsimp [P]; rw [←Real.rpow_mul_natCast hX0.le]; congr 1; norm_num
  rw [hP3] at hb
  have hs : (1:ℂ)+((σ-1:ℝ):ℂ)+I*t=(σ:ℂ)+I*t := by push_cast; ring
  rw [hs] at hb
  change (c/(4*K^2))*X^(-ε)≤_
  simpa only [Real.rpow_neg hX0.le,div_eq_mul_inv] using hb

lemma principal_deriv_eq_regular {s : ℂ} (hs : 0 < s.re) :
    deriv (poleRemovedL (1:DirichletCharacter ℂ 1)) s = zetaRegular s+(s-1)*deriv zetaRegular s := by
  have he : poleRemovedL (1:DirichletCharacter ℂ 1) =ᶠ[𝓝 s] (fun z => (z-1)*zetaRegular z+1) := by
    filter_upwards [(continuous_re.tendsto s).eventually (lt_mem_nhds hs)] with z hz
    simpa only [poleRemovedL,ite_true] using poleRemovedZeta_eq hz
  have hh := (((hasDerivAt_id s).sub_const 1).mul (zetaRegular_differentiableAt hs).hasDerivAt).add_const 1
  rw [he.deriv_eq]
  simpa only [id_eq,one_mul,Pi.mul_apply] using hh.deriv

lemma principal_deriv_growth {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ s : ℂ, 1-ε/4 ≤ s.re →
      ‖deriv (poleRemovedL (1:DirichletCharacter ℂ 1)) s‖ ≤ K*(‖s‖+2)*(‖s‖+2)^ε := by
  obtain ⟨K,hK,hb⟩ := zetaRegular_bounds (by linarith : 0 < ε/2) (by linarith : ε/2 ≤ 1/2)
  have hK0 : 0 < K := by linarith
  refine ⟨K,hK0,?_⟩
  intro s hs
  obtain ⟨hl,hd⟩ := hb s (by linarith)
  rw [show 2*(ε/2)=ε by ring] at hl hd
  rw [principal_deriv_eq_regular (by linarith)]
  have hn : ‖s-1‖ ≤ ‖s‖+1 := by simpa using norm_sub_le s 1
  calc
    _ ≤ ‖zetaRegular s‖+‖s-1‖*‖deriv zetaRegular s‖ := by
      apply (norm_add_le _ _).trans_eq
      rw [norm_mul]
    _ ≤ K*(‖s‖+2)^ε+(‖s‖+1)*(K*(‖s‖+2)^ε) := by gcongr
    _ = _ := by ring

lemma principal_strip_lower {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ σ t : ℝ, 1 ≤ σ → σ ≤ 2 →
      c*(|t|+2)/((|t|+2)^ε) ≤ ‖poleRemovedL (1:DirichletCharacter ℂ 1) (σ+I*t)‖ := by
  obtain ⟨c₀,hc₀,hl⟩ := zeta_high_strip_lower hε hε1
  let F := poleRemovedL (1:DirichletCharacter ℂ 1)
  let S : Set ℂ := (fun p : ℝ×ℝ => (p.1:ℂ)+I*p.2) '' (Set.Icc 1 2 ×ˢ Set.Icc (-1) 1)
  have hS : IsCompact S := (isCompact_Icc.prod isCompact_Icc).image (by fun_prop)
  have hmem (z : ℂ) : z∈S ↔ 1 ≤ z.re ∧ z.re ≤ 2 ∧ |z.im| ≤ 1 := by
    constructor
    · rintro ⟨⟨u,v⟩,⟨hu,hv⟩,rfl⟩
      simpa [abs_le,and_assoc] using And.intro hu hv
    · rintro ⟨h₁,h₂,h₃⟩
      refine ⟨(z.re,z.im),⟨⟨h₁,h₂⟩,abs_le.mp h₃⟩,?_⟩
      simpa only [mul_comm] using Complex.re_add_im z
  have hc : ContinuousOn (fun z => (F z)⁻¹) S := by
    intro z hz
    exact (((poleRemovedL_differentiable 1).continuous.continuousAt).inv₀
      (poleRemovedL_ne_zero 1 ((hmem z).mp hz).1)).continuousWithinAt
  obtain ⟨M,hM⟩ := hS.exists_bound_of_continuousOn hc
  let D := max M 1
  have hD : 0 < D := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  let c := min (c₀/3) (1/(3*D))
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨c,hc,?_⟩
  intro σ t hσ hσ2
  let z : ℂ := (σ:ℂ)+I*t
  have hz : 1 ≤ z.re := by simpa [z] using hσ
  have hT : 1 ≤ |t|+2 := by linarith [abs_nonneg t]
  have hP : 1 ≤ (|t|+2)^ε := Real.one_le_rpow hT hε.le
  by_cases ht : 1 ≤ |t|
  · have hz1 : z≠1 := by intro hh; have hi := congrArg Complex.im hh; simp [z] at hi; simp [hi] at ht; norm_num at ht
    have he : F z=(z-1)*riemannZeta z := by
      simp only [F,poleRemovedL,ite_true,DirichletCharacter.LFunctionTrivChar₁,Function.update_of_ne hz1,
        DirichletCharacter.LFunctionTrivChar,DirichletCharacter.LFunction_modOne_eq]
    have hnorm : (|t|+2)/3 ≤ ‖z-1‖ := by
      have hi := Complex.abs_im_le_norm (z-1)
      simp [z] at hi
      linarith
    have hlow := hl σ t hσ hσ2 ht
    rw [Real.rpow_neg (by positivity : 0 ≤ |t|+2),←div_eq_mul_inv] at hlow
    change c*(|t|+2)/( |t|+2)^ε ≤ ‖F z‖
    rw [he,norm_mul]
    calc
      _ ≤ (c₀/3)*(|t|+2)/(|t|+2)^ε := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)) (by positivity)
      _ = ((|t|+2)/3)*(c₀/(|t|+2)^ε) := by ring
      _ ≤ _ := mul_le_mul hnorm hlow (by positivity) (norm_nonneg _)
  · have ht1 : |t| ≤ 1 := le_of_not_ge ht
    have hzS : z∈S := (hmem z).mpr ⟨hz,by simpa [z] using hσ2,by simpa [z] using ht1⟩
    have hb := (hM z hzS).trans (le_max_left M 1)
    have hn : 0 < ‖F z‖ := norm_pos_iff.mpr (poleRemovedL_ne_zero 1 hz)
    rw [norm_inv,inv_eq_one_div] at hb
    have hlow : 1/D ≤ ‖F z‖ := by
      apply (div_le_iff₀ hD).mpr
      have hh := (div_le_iff₀ hn).mp hb
      nlinarith
    change c*(|t|+2)/(|t|+2)^ε ≤ ‖F z‖
    apply le_trans ?_ hlow
    calc
      _ ≤ c*(|t|+2) := div_le_self (by positivity) hP
      _ ≤ (1/(3*D))*3 := mul_le_mul (min_le_right _ _) (by linarith) (by positivity) (by positivity)
      _ = 1/D := by ring

end LargePrimeGaps
end OAI

-- Source module: RieszBounds
namespace OAI
namespace LargePrimeGaps
open Complex Filter Topology
noncomputable def logRiesz (f : ℂ → ℂ) (s : ℂ) : ℂ := (-deriv f s / f s)/(s*(s+1))

lemma near_line_denominator {z w : ℂ} {r : ℝ} (hz : 1 ≤  z.re) (hr : r ≤ 1/4)
    (hw : w∈Metric.closedBall z r) :
    w≠0 ∧ w+1≠0 ∧ (|z.im|+2)^2 ≤ 16*‖w‖*‖w+1‖ := by
  have hd : ‖w-z‖ ≤ r := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hw
  have hre := Complex.re_le_norm (z-w)
  rw [Complex.sub_re,norm_sub_rev] at hre
  have hwre : 3/4 ≤ w.re := by linarith
  have hw0 : w≠0 := by intro h; simp [h] at hwre; norm_num at hwre
  have hw1 : w+1≠0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hna : 3/4 ≤ ‖w‖ := hwre.trans (Complex.re_le_norm w)
  have hnb : 3/4 ≤ ‖w+1‖ := by
    have h := Complex.re_le_norm (w+1)
    simp only [Complex.add_re,Complex.one_re] at h
    linarith
  have ha : |z.im| ≤ ‖w‖+r := by
    have ht := norm_add_le (z-w) w
    rw [sub_add_cancel,norm_sub_rev] at ht
    linarith [Complex.abs_im_le_norm z]
  have hb : |z.im| ≤ ‖w+1‖+r := by
    have ht := norm_add_le (z-w) (w+1)
    rw [show z-w+(w+1)=z+1 by ring,norm_sub_rev] at ht
    have hi := Complex.abs_im_le_norm (z+1)
    simp only [Complex.add_im,Complex.one_im,add_zero] at hi
    linarith
  have ha' : |z.im|+2 ≤ 4*‖w‖ := by linarith
  have hb' : |z.im|+2 ≤ 4*‖w+1‖ := by linarith
  refine ⟨hw0,hw1,?_⟩
  have hp := mul_le_mul ha' hb' (by positivity : 0 ≤ |z.im|+2) (by positivity : 0 ≤ 4*‖w‖)
  nlinarith

lemma logRiesz_local {f : ℂ → ℂ} {z : ℂ} {r m M : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1/4) (hm : 0 < m) (hM : 0 ≤ M) (hz : 1 ≤  z.re)
    (hf : ∀ w∈Metric.closedBall z r,AnalyticAt ℂ f w)
    (hb : ∀ w∈Metric.closedBall z r,‖deriv f w‖ ≤ M)
    (hl : m ≤ ‖f z‖) (hMr : M*r ≤ m/2) :
    (∀ w∈Metric.closedBall z r,f w≠0) ∧
      DiffContOnCl ℂ (logRiesz f) (Metric.ball z r) ∧
      ∀ w∈Metric.closedBall z r,‖logRiesz f w‖ ≤ (32*M/m)/(|z.im|+2)^2 := by
  have hmem : z∈Metric.closedBall z r := Metric.mem_closedBall_self hr.le
  have hlo (w : ℂ) (hw : w∈Metric.closedBall z r) : m/2 ≤ ‖f w‖ := by
    have hd := Convex.norm_image_sub_le_of_norm_deriv_le
      (fun w hw => (hf w hw).differentiableAt) hb (convex_closedBall z r) hw hmem
    have hdist : ‖z-w‖ ≤ r := by simpa only [Metric.mem_closedBall,dist_eq_norm,norm_sub_rev] using hw
    have hd' := hd.trans (mul_le_mul_of_nonneg_left hdist hM)
    have ht := norm_add_le (f z-f w) (f w)
    rw [sub_add_cancel] at ht
    linarith
  have hne (w : ℂ) (hw : w∈Metric.closedBall z r) : f w≠0 := by
    exact norm_pos_iff.mp ((by positivity : 0 < m/2).trans_le (hlo w hw))
  refine ⟨hne,?_,?_⟩
  · apply DifferentiableOn.diffContOnCl
    rw [closure_ball _ hr.ne']
    intro w hw
    obtain ⟨hw0,hw1,_⟩ := near_line_denominator hz hr1 hw
    exact (((hf w hw).deriv.neg.div (hf w hw) (hne w hw)).div
      (analyticAt_id.mul (analyticAt_id.add analyticAt_const)) (mul_ne_zero hw0 hw1)).differentiableWithinAt
  · intro w hw
    obtain ⟨hw0,hw1,hden⟩ := near_line_denominator hz hr1 hw
    have hnorm : 0 < ‖w‖*‖w+1‖ := mul_pos (norm_pos_iff.mpr hw0) (norm_pos_iff.mpr hw1)
    have hb₀ : ‖deriv f w‖/‖f w‖ ≤ 2*M/m := by
      apply (div_le_div₀ hM (hb w hw) (by positivity : 0 < m/2) (hlo w hw)).trans_eq
      ring
    have hb₁ : 1/(‖w‖*‖w+1‖) ≤ 16/(|z.im|+2)^2 := by
      apply (div_le_div_iff₀ hnorm (by positivity)).mpr
      nlinarith
    simp only [logRiesz,norm_div,norm_neg,norm_mul]
    calc
      _ = (‖deriv f w‖/‖f w‖)*(1/(‖w‖*‖w+1‖)) := by ring
      _  ≤  (2*M/m)*(16/(|z.im|+2)^2) := mul_le_mul hb₀ hb₁ (by positivity) (by positivity)
      _ = _ := by ring

lemma logRiesz_iteratedDeriv_bound {f : ℂ → ℂ} {z : ℂ} {r m M : ℝ}
    (n : ℕ) (hr : 0 < r) (hr1 : r ≤ 1/4) (hm : 0 < m) (hM : 0 ≤ M) (hz : 1 ≤  z.re)
    (hf : ∀ w∈Metric.closedBall z r,AnalyticAt ℂ f w)
    (hb : ∀ w∈Metric.closedBall z r,‖deriv f w‖ ≤ M)
    (hl : m ≤ ‖f z‖) (hMr : M*r ≤ m/2) :
    ‖iteratedDeriv n (logRiesz f) z‖ ≤ (n.factorial:ℝ)*((32*M/m)/(|z.im|+2)^2)/r^n := by
  have hh := logRiesz_local hr hr1 hm hM hz hf hb hl hMr
  exact Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hr hh.2.1
    (fun w hw => hh.2.2 w (Metric.sphere_subset_closedBall hw))

lemma logRiesz_power_bound {f : ℂ → ℂ} {z : ℂ} {P W c K d : ℝ} (n : ℕ)
    (hP : 1 ≤ P) (hW : 0 < W) (hc : 0 < c) (hK : 0 < K) (hd : 0 < d)
    (hd1 : d ≤ 1/4) (hKd : K*d ≤ c/2) (hz : 1 ≤ z.re)
    (hf : ∀ w∈Metric.closedBall z (d/P^2), AnalyticAt ℂ f w)
    (hb : ∀ w∈Metric.closedBall z (d/P^2), ‖deriv f w‖ ≤ K*W*P)
    (hl : c*W/P ≤ ‖f z‖) :
    ‖iteratedDeriv n (logRiesz f) z‖ ≤
      ((n.factorial:ℝ)*(32*K/c)/d^n)*P^(2*n+2)/(|z.im|+2)^2 := by
  have hP0 : 0 < P := by linarith
  have hr1 : d/P^2 ≤ 1/4 := by
    apply (div_le_self hd.le (one_le_pow₀ hP)).trans hd1
  have hMr : (K*W*P)*(d/P^2) ≤ (c*W/P)/2 := by
    calc
      _ = (K*d)*W/P := by field_simp
      _ ≤ (c/2)*W/P := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hKd hW.le) hP0.le
      _ = _ := by ring
  have hh := logRiesz_iteratedDeriv_bound n (by positivity : 0 < d/P^2) hr1
    (by positivity : 0 < c*W/P) (by positivity : 0 ≤ K*W*P) hz hf hb hl hMr
  apply hh.trans_eq
  rw [div_pow,pow_add,pow_mul]
  field_simp

lemma near_strip_geometry {σ t d P η : ℝ} (hσ : 1 ≤ σ) (hσ2 : σ ≤ 2)
    (hP : 1 ≤ P) (hd : 0 ≤ d) (hd1 : d ≤ 1/4) (hdη : d ≤ η/4)
    {w : ℂ} (hw : w∈Metric.closedBall ((σ:ℂ)+I*t) (d/P^2)) :
    1-η/4 ≤ w.re ∧ ‖w‖+2 ≤ 3*(|t|+2) := by
  have hr : d/P^2 ≤ d := div_le_self hd (one_le_pow₀ hP)
  have hdist : ‖w-((σ:ℂ)+I*t)‖ ≤ d/P^2 := by
    simpa only [Metric.mem_closedBall,dist_eq_norm] using hw
  have hre := Complex.re_le_norm (((σ:ℂ)+I*t)-w)
  simp only [Complex.sub_re,Complex.add_re,Complex.ofReal_re,Complex.mul_re,
    Complex.I_re,Complex.I_im,Complex.ofReal_im,mul_zero,zero_mul,sub_self,add_zero,norm_sub_rev] at hre
  have hnorm := norm_add_le (w-((σ:ℂ)+I*t)) ((σ:ℂ)+I*t)
  rw [sub_add_cancel] at hnorm
  have hnz := Complex.norm_le_abs_re_add_abs_im ((σ:ℂ)+I*t)
  simp only [Complex.add_re,Complex.add_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,zero_mul,mul_zero,
    one_mul,sub_self,zero_add,add_zero,abs_of_nonneg (by linarith : 0 ≤ σ)] at hnz
  constructor <;> linarith [abs_nonneg t]

lemma nonprincipal_logRiesz_bound (n : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → χ≠1 → ∀ σ t : ℝ, 1 ≤ σ → σ ≤ 2 →
        ‖iteratedDeriv n (logRiesz χ.LFunction) (σ+I*t)‖ ≤
          D*((q:ℝ)+2)^(1/2:ℝ)*(|t|+2)^(-(3/2:ℝ)) := by
  let ε : ℝ := 1/(4*(n+1:ℕ))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hε1 : ε ≤ 1 := by
    dsimp [ε]
    apply (div_le_one (by positivity : 0 < 4*((n+1:ℕ):ℝ))).mpr
    have hn : (1:ℝ) ≤ (n+1:ℕ) := by exact_mod_cast (Nat.succ_pos n)
    linarith
  obtain ⟨c,hc,hl⟩ := nonprincipal_strip_lower hε hε1
  obtain ⟨K₀,hK₀,hb⟩ := LFunction_deriv_norm_small_power (by linarith : 0 < ε/2) (by linarith : ε/2 ≤ 1/2)
  let K := K₀*3^ε
  have hK : 0 < K := by dsimp [K]; positivity
  let d := min (min (1/4) (ε/4)) (c/(2*K))
  have hd : 0 < d := by dsimp [d]; positivity
  have hd1 : d ≤ 1/4 := (min_le_left _ _).trans (min_le_left _ _)
  have hdε : d ≤ ε/4 := (min_le_left _ _).trans (min_le_right _ _)
  have hKd : K*d ≤ c/2 := by
    have h := min_le_right (min (1/4) (ε/4)) (c/(2*K))
    change d ≤ c/(2*K) at h
    have hh := mul_le_mul_of_nonneg_left h hK.le
    have he : K*(c/(2*K))=c/2 := by field_simp
    rwa [he] at hh
  let D := (n.factorial:ℝ)*(32*K/c)/d^n
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨D,hD,?_⟩
  intro q _ χ hχp hχ σ t hσ hσ2
  let X : ℝ := ((q:ℝ)+2)*(|t|+2)
  let P : ℝ := X^ε
  have hX : 1 ≤ X := by dsimp [X]; nlinarith [Nat.cast_nonneg (α:=ℝ) q,abs_nonneg t]
  have hX0 : 0 < X := by linarith
  have hP : 1 ≤ P := Real.one_le_rpow hX hε.le
  have hlow : c*1/P ≤ ‖χ.LFunction (σ+I*t)‖ := by
    have h := hl q χ hχp hχ σ t hσ hσ2
    change c*X^(-ε) ≤ _ at h
    simpa only [mul_one,Real.rpow_neg hX0.le,div_eq_mul_inv] using h
  have hbound : ∀ w∈Metric.closedBall ((σ:ℂ)+I*t) (d/P^2), ‖deriv χ.LFunction w‖ ≤ K*1*P := by
    intro w hw
    obtain ⟨hre,hnorm⟩ := near_strip_geometry hσ hσ2 hP hd.le hd1 hdε hw
    have h := hb q χ hχ w (by linarith)
    rw [show 2*(ε/2)=ε by ring] at h
    have hn : ((q:ℝ)+2)*(‖w‖+2) ≤ 3*X := by
      dsimp [X]
      nlinarith [mul_nonneg (show (0:ℝ) ≤ q+2 by positivity) (sub_nonneg.mpr hnorm)]
    calc
      _ ≤ K₀*((q+2)*(‖w‖+2))^ε := h
      _ ≤ K₀*(3*X)^ε := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hn hε.le) hK₀.le
      _ = K*1*P := by rw [Real.mul_rpow (by norm_num) hX0.le]; dsimp [K,P]; ring
  have hh := logRiesz_power_bound n hP zero_lt_one hc hK hd hd1 hKd (by simpa using hσ)
    (fun w _ => (DirichletCharacter.differentiable_LFunction hχ).analyticAt w) hbound hlow
  have he : ε*(2*n+2:ℕ)=1/2 := by
    dsimp [ε]
    push_cast
    field_simp
    ring
  have hpow : P^(2*n+2)=X^(1/2:ℝ) := by
    dsimp [P]
    rw [←Real.rpow_mul_natCast hX0.le,he]
  simp only [Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.I_re,Complex.I_im,
    zero_mul,one_mul,zero_add] at hh
  change ‖iteratedDeriv n (logRiesz χ.LFunction) (σ+I*t)‖ ≤ D*P^(2*n+2)/(|t|+2)^2 at hh
  rw [hpow] at hh
  apply hh.trans_eq
  dsimp [X]
  rw [Real.mul_rpow (by positivity) (by positivity),Real.rpow_neg (by positivity : 0 ≤ |t|+2)]
  have ht : (|t|+2)^(1/2:ℝ)*(|t|+2)^(3/2:ℝ)=(|t|+2)^2 := by
    rw [←Real.rpow_add (by positivity),show (1/2:ℝ)+3/2=2 by norm_num]
    norm_num
  field_simp
  rw [←ht]

end LargePrimeGaps
end OAI

-- Source module: MellinSmoothing
namespace OAI
namespace LargePrimeGaps
open Complex Real Set MeasureTheory Filter Topology
noncomputable def rieszKernel : ℝ → ℂ := (Ioc 0 1).indicator (fun t => 1-(t:ℂ))

lemma hasMellin_rieszKernel {s : ℂ} (hs : 0<s.re) :
    HasMellin rieszKernel s (1/(s*(s+1))) := by
  have h₀ := hasMellin_one_Ioc hs
  have h₁ := hasMellin_cpow_Ioc 1 (by simp; linarith : 0<s.re+(1:ℂ).re)
  have hh := hasMellin_sub h₀.1 h₁.1
  rw [h₀.2,h₁.2] at hh
  have he : (fun t : ℝ => (Ioc 0 1).indicator (fun _ : ℝ => (1:ℂ)) t-
      (Ioc 0 1).indicator (fun t : ℝ => (t:ℂ)^(1:ℂ)) t)=rieszKernel := by
    ext t
    by_cases ht : t∈Ioc (0:ℝ) 1 <;> simp [rieszKernel,ht]
  rw [he] at hh
  have hs0 : s≠0 := by intro h; simp [h] at hs
  have hs1 : s+1≠0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
  have heval : 1/s-1/(s+1)=1/(s*(s+1)) := by field_simp; ring
  rwa [heval] at hh

lemma rieszKernel_eq_max {x : ℝ} (hx : 0<x) : rieszKernel x=(max (1-x) 0:ℝ) := by
  by_cases hx1 : x≤1
  · simp [rieszKernel,Set.mem_Ioc,hx,hx1]
  · simp [rieszKernel,Set.mem_Ioc,hx,hx1,max_eq_right (by linarith : 1-x≤(0:ℝ))]

lemma rieszKernel_continuousAt {x : ℝ} (hx : 0<x) : ContinuousAt rieszKernel x := by
  have he : rieszKernel =ᶠ[𝓝 x] (fun x : ℝ => ((max (1-x) 0:ℝ):ℂ)) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact rieszKernel_eq_max hy
  exact (show ContinuousAt (fun x : ℝ => ((max (1-x) 0:ℝ):ℂ)) x by fun_prop).congr he.symm

lemma rieszDenominator_bound {s : ℂ} (hs : 1≤ s.re) :
    ‖1/(s*(s+1))‖≤2/(1+s.im^2) := by
  have ha : 1≤‖s‖ := hs.trans (Complex.re_le_norm s)
  have hb : 1≤‖s+1‖ := by have h := Complex.re_le_norm (s+1); simp at h; linarith
  have hai : |s.im|≤‖s‖ := Complex.abs_im_le_norm s
  have hbi : |s.im|≤‖s+1‖ := by simpa using Complex.abs_im_le_norm (s+1)
  have hp : 1≤‖s‖*‖s+1‖ := one_le_mul_of_one_le_of_one_le ha hb
  have hpi : s.im^2≤‖s‖*‖s+1‖ := by
    simpa only [←sq, sq_abs] using mul_le_mul hai hbi (abs_nonneg _) (norm_nonneg _)
  rw [norm_div,norm_one,norm_mul]
  apply (div_le_div_iff₀ (by positivity : 0<‖s‖*‖s+1‖) (by positivity : 0<1+s.im^2)).mpr
  nlinarith

set_option maxHeartbeats 800000 in
lemma rieszDenominator_verticalIntegrable {σ : ℝ} (hσ : 1≤σ) :
    VerticalIntegrable (fun s : ℂ => 1/(s*(s+1))) σ := by
  have hne (t : ℝ) : (σ:ℂ)+(t:ℂ)*I≠0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hne1 (t : ℝ) : (σ:ℂ)+(t:ℂ)*I+1≠0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hm : Continuous (fun t : ℝ => 1/(((σ:ℂ)+t*I)*((σ:ℂ)+t*I+1))) := by
    apply Continuous.div continuous_const (by fun_prop)
    intro t
    exact mul_ne_zero (hne t) (hne1 t)
  apply (integrable_inv_one_add_sq.const_mul 2).mono' hm.aestronglyMeasurable
  filter_upwards [] with t
  have hb := rieszDenominator_bound (s:=(σ:ℂ)+t*I) (by simpa using hσ)
  simpa only [Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.I_re,mul_zero,
    Complex.ofReal_re,Complex.I_im,mul_one,add_zero,zero_add,div_eq_mul_inv] using hb

lemma rieszKernel_mellinInv {σ x : ℝ} (hσ : 1≤σ) (hx : 0<x) :
    mellinInv σ (fun s : ℂ => 1/(s*(s+1))) x=rieszKernel x := by
  have hσ0 : (0:ℝ)<σ := by linarith
  have hm (t : ℝ) : mellin rieszKernel (σ+t*I)=1/((σ+t*I)*(σ+t*I+1)) :=
    (hasMellin_rieszKernel (by simpa using hσ0)).2
  have hF : VerticalIntegrable (mellin rieszKernel) σ := by
    unfold VerticalIntegrable
    simp_rw [hm]
    exact rieszDenominator_verticalIntegrable hσ
  rw [←mellinInv_mellin_eq σ rieszKernel hx (hasMellin_rieszKernel (by simpa using hσ0)).1 hF
    (rieszKernel_continuousAt hx)]
  simp only [mellinInv,hm]

open Complex Filter Topology
lemma principal_logRiesz_bound (n : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ σ t : ℝ, 1 ≤ σ → σ ≤ 2 →
        ‖iteratedDeriv n (logRiesz (poleRemovedL (1:DirichletCharacter ℂ 1))) (σ+I*t)‖ ≤
          D*(|t|+2)^(-(3/2:ℝ)) := by
  let ε : ℝ := 1/(4*(n+1:ℕ))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hε1 : ε ≤ 1 := by
    dsimp [ε]
    apply (div_le_one (by positivity : 0 < 4*((n+1:ℕ):ℝ))).mpr
    have hn : (1:ℝ) ≤ (n+1:ℕ) := by exact_mod_cast (Nat.succ_pos n)
    linarith
  obtain ⟨c,hc,hl⟩ := principal_strip_lower hε hε1
  obtain ⟨K₀,hK₀,hb⟩ := principal_deriv_growth hε hε1
  let K := 3*K₀*3^ε
  have hK : 0 < K := by dsimp [K]; positivity
  let d := min (min (1/4) (ε/4)) (c/(2*K))
  have hd : 0 < d := by dsimp [d]; positivity
  have hd1 : d ≤ 1/4 := (min_le_left _ _).trans (min_le_left _ _)
  have hdε : d ≤ ε/4 := (min_le_left _ _).trans (min_le_right _ _)
  have hKd : K*d ≤ c/2 := by
    have h := min_le_right (min (1/4) (ε/4)) (c/(2*K))
    change d ≤ c/(2*K) at h
    have hh := mul_le_mul_of_nonneg_left h hK.le
    have he : K*(c/(2*K))=c/2 := by field_simp
    rwa [he] at hh
  let D := (n.factorial:ℝ)*(32*K/c)/d^n
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨D,hD,?_⟩
  intro σ t hσ hσ2
  let X : ℝ := (|t|+2)
  let P : ℝ := X^ε
  have hX : 1 ≤ X := by dsimp [X]; linarith [abs_nonneg t]
  have hX0 : 0 < X := by linarith
  have hP : 1 ≤ P := Real.one_le_rpow hX hε.le
  have hlow : c*(|t|+2)/P ≤ ‖poleRemovedL (1:DirichletCharacter ℂ 1) (σ+I*t)‖ := hl σ t hσ hσ2
  have hbound : ∀ w∈Metric.closedBall ((σ:ℂ)+I*t) (d/P^2),
      ‖deriv (poleRemovedL (1:DirichletCharacter ℂ 1)) w‖ ≤ K*(|t|+2)*P := by
    intro w hw
    obtain ⟨hre,hnorm⟩ := near_strip_geometry hσ hσ2 hP hd.le hd1 hdε hw
    have h := hb w hre
    calc
      _ ≤ K₀*(‖w‖+2)*(‖w‖+2)^ε := h
      _ ≤ K₀*(3*X)*(3*X)^ε := by gcongr
      _ = K*(|t|+2)*P := by rw [Real.mul_rpow (by norm_num) hX0.le]; dsimp [K,P,X]; ring
  have hh := logRiesz_power_bound n hP (by positivity : 0 < |t|+2) hc hK hd hd1 hKd (by simpa using hσ)
    (fun w _ => (poleRemovedL_differentiable (1:DirichletCharacter ℂ 1)).analyticAt w) hbound hlow
  have he : ε*(2*n+2:ℕ)=1/2 := by
    dsimp [ε]
    push_cast
    field_simp
    ring
  have hpow : P^(2*n+2)=X^(1/2:ℝ) := by
    dsimp [P]
    rw [←Real.rpow_mul_natCast hX0.le,he]
  simp only [Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.I_re,Complex.I_im,
    zero_mul,one_mul,zero_add] at hh
  change ‖iteratedDeriv n (logRiesz (poleRemovedL (1:DirichletCharacter ℂ 1))) (σ+I*t)‖ ≤ D*P^(2*n+2)/(|t|+2)^2 at hh
  rw [hpow] at hh
  apply hh.trans_eq
  dsimp [X]
  rw [Real.rpow_neg (by positivity : 0 ≤ |t|+2)]
  have ht : (|t|+2)^(1/2:ℝ)*(|t|+2)^(3/2:ℝ)=(|t|+2)^2 := by
    rw [←Real.rpow_add (by positivity),show (1/2:ℝ)+3/2=2 by norm_num]
    norm_num
  field_simp
  rw [←ht]

lemma primitive_logRiesz_bound (n : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → ∀ σ t : ℝ, 1 ≤ σ → σ ≤ 2 →
        ‖iteratedDeriv n (logRiesz (poleRemovedL χ)) (σ+I*t)‖ ≤
          D*((q:ℝ)+2)^(1/2:ℝ)*(|t|+2)^(-(3/2:ℝ)) := by
  obtain ⟨D₀,hD₀,h₀⟩ := nonprincipal_logRiesz_bound n
  obtain ⟨D₁,hD₁,h₁⟩ := principal_logRiesz_bound n
  refine ⟨max D₀ D₁,lt_of_lt_of_le hD₀ (le_max_left _ _),?_⟩
  intro q _ χ hχp σ t hσ hσ2
  have hq : 1 ≤ ((q:ℝ)+2)^(1/2:ℝ) := Real.one_le_rpow (by linarith [Nat.cast_nonneg (α:=ℝ) q]) (by norm_num)
  by_cases hχ : χ=1
  · subst χ
    have hq1 : q=1 := by simpa [DirichletCharacter.IsPrimitive,DirichletCharacter.conductor_one] using hχp.symm
    subst q
    have hq' : 1 ≤ ((1:ℝ)+2)^(1/2:ℝ) := by simpa only [Nat.cast_one] using hq
    have hb := h₁ σ t hσ hσ2
    apply hb.trans
    have hc : D₁ ≤ max D₀ D₁*((1:ℝ)+2)^(1/2:ℝ) := by
      calc
        D₁ ≤ max D₀ D₁ := le_max_right _ _
        _ ≤ _ := le_mul_of_one_le_right (le_trans hD₀.le (le_max_left _ _)) hq'
    simpa only [Nat.cast_one] using mul_le_mul_of_nonneg_right hc (by positivity : 0 ≤ (|t|+2)^(-(3/2:ℝ)))
  · have hb := h₀ q χ hχp hχ σ t hσ hσ2
    simp only [poleRemovedL,hχ,ite_false]
    apply hb.trans
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)) (by positivity)

lemma logRiesz_poleRemoved_analyticAt {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 ≤ s.re) : AnalyticAt ℂ (logRiesz (poleRemovedL χ)) s := by
  have h₀ : s≠0 := by intro h; simp [h] at hs; norm_num at hs
  have h₁ : s+1≠0 := by
    intro h
    have hh := congrArg Complex.re h
    simp at hh
    linarith
  exact (primeLogDerivativeRegular_analyticAt χ (poleRemovedL_ne_zero χ hs)).div
    (analyticAt_id.mul (analyticAt_id.add analyticAt_const)) (mul_ne_zero h₀ h₁)

open Complex Filter Topology MeasureTheory
open scoped FourierTransform
lemma analyticAt_iteratedDeriv_local {f : ℂ → ℂ} {z : ℂ} (h : AnalyticAt ℂ f z) (n : ℕ) :
    AnalyticAt ℂ (iteratedDeriv n f) z := by
  induction n with
  | zero => simpa using h
  | succ n ih => rw [iteratedDeriv_succ]; exact ih.deriv

lemma vertical_contDiff {f : ℂ → ℂ} {z a : ℂ}
    (hf : ∀ t : ℝ, AnalyticAt ℂ f (z+a*t)) :
    ContDiff ℝ ⊤ (fun t : ℝ => f (z+a*t)) := by
  rw [contDiff_iff_contDiffAt]
  intro t
  have hr : ContDiffAt ℝ ⊤ (fun t : ℝ => (t:ℂ)) t := Complex.ofRealCLM.contDiff.contDiffAt
  exact ((hf t).contDiffAt.restrict_scalars ℝ).comp t
    (contDiffAt_const.add (contDiffAt_const.mul hr))

lemma vertical_iteratedDeriv {f : ℂ → ℂ} {z a : ℂ}
    (hf : ∀ t : ℝ, AnalyticAt ℂ f (z+a*t)) (n : ℕ) :
    iteratedDeriv n (fun t : ℝ => f (z+a*t)) =
      fun t : ℝ => a^n * iteratedDeriv n f (z+a*t) := by
  induction n with
  | zero => ext t; simp
  | succ n ih =>
    rw [iteratedDeriv_succ,ih]
    funext t
    have ha : HasDerivAt (fun t : ℝ => z+a*t) a t := by
      convert (((hasDerivAt_id (t:ℂ)).const_mul a).const_add z).comp_ofReal using 1 <;> simp
    have hd := ((analyticAt_iteratedDeriv_local (hf t) n).differentiableAt.hasDerivAt.comp t ha).const_mul (a^n)
    rw [iteratedDeriv_succ]
    simpa only [Function.comp_def,pow_succ,mul_assoc,mul_comm,mul_left_comm] using hd.deriv

noncomputable def decayMajorant (t : ℝ) : ℝ := (1+|t|)^(-(3/2:ℝ))

lemma decayMajorant_integrable : Integrable decayMajorant := by
  change Integrable (fun t : ℝ => (1+|t|)^(-(3/2:ℝ)))
  simpa only [Real.norm_eq_abs] using
    (integrable_one_add_norm (E:=ℝ) (by norm_num : (Module.finrank ℝ ℝ:ℝ) < 3/2))

lemma integrable_of_decay_bound {g : ℝ → ℂ} {M : ℝ} (hg : Continuous g)
    (hb : ∀ t, ‖g t‖ ≤ M*decayMajorant t) : Integrable g := by
  exact (decayMajorant_integrable.const_mul M).mono' hg.aestronglyMeasurable (Filter.Eventually.of_forall hb)

lemma integral_norm_le_of_decay_bound {g : ℝ → ℂ} {M : ℝ} (hg : Continuous g)
    (hb : ∀ t, ‖g t‖ ≤ M*decayMajorant t) :
    ∫ t, ‖g t‖ ≤ M*(∫ t, decayMajorant t) := by
  rw [←integral_const_mul]
  exact integral_mono (integrable_of_decay_bound hg hb).norm
    (decayMajorant_integrable.const_mul M) hb

lemma fourierInv_decay {g : ℝ → ℂ} (hg : ContDiff ℝ ⊤ g)
    (hi : ∀ n : ℕ, Integrable (iteratedDeriv n g)) (n : ℕ) {M u : ℝ}
    (hb : (∫ t, ‖iteratedDeriv n g t‖) ≤ M) (hu : 0 < |u|) :
    ‖𝓕⁻ g u‖ ≤ M/|u|^n := by
  have he := congrFun (Real.fourier_iteratedDeriv (N:=⊤) (hg.of_le le_top) (fun n _ => hi n) (n:=n) (by simp)) (-u)
  have hn := VectorFourier.norm_fourierIntegral_le_integral_norm Real.fourierChar volume
    (innerₗ ℝ) (iteratedDeriv n g) (-u)
  change ‖𝓕 (iteratedDeriv n g) (-u)‖ ≤ _ at hn
  have hn' := hn.trans hb
  rw [he,norm_smul,norm_pow] at hn'
  have hc : ‖(2:ℂ)*Real.pi*I*(-u)‖=2*Real.pi*|u| := by
    simp [Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  simp only [Complex.ofReal_neg] at hn'
  rw [hc] at hn'
  rw [Real.fourierInv_eq_fourier_neg]
  apply (le_div_iff₀ (pow_pos hu n)).mpr
  have hπ : (1:ℝ) ≤ 2*Real.pi := by linarith [Real.pi_gt_three]
  have hpow : |u|^n ≤ (2*Real.pi*|u|)^n := by
    gcongr
    exact le_mul_of_one_le_left hu.le hπ
  nlinarith [mul_le_mul_of_nonneg_right hpow (norm_nonneg (𝓕 g (-u)))]

open Complex Real Set MeasureTheory Filter Topology
lemma mellinInv_const_mul (σ : ℝ) (f : ℂ → ℂ) (a : ℂ) (x : ℝ) :
    mellinInv σ (fun s => a*f s) x=a*mellinInv σ f x := by
  simp [mellinInv,smul_eq_mul,Complex.real_smul,mul_left_comm,integral_const_mul,mul_assoc]

lemma mellinInv_term_riesz {σ y : ℝ} (hσ : 1≤σ) (hy : 0<y)
    (a : ℕ → ℂ) (n : ℕ) :
    mellinInv σ (fun s => LSeries.term a s n/(s*(s+1))) y=
      if n=0 then 0 else a n*rieszKernel ((n:ℝ)*y) := by
  by_cases hn : n=0
  · simp [hn,mellinInv]
  rw [ite_eq_right hn]
  have hi := rieszKernel_mellinInv hσ (mul_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)) hy)
  rw [←hi]
  simp only [mellinInv,LSeries.term_of_ne_zero hn,smul_eq_mul,Complex.real_smul]
  rw [mul_left_comm (a n) ((1/(2*π):ℝ):ℂ)]
  congr 1
  rw [←integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with t
  rw [Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg n) hy.le]
  simp only [Complex.ofReal_natCast,Complex.cpow_neg]
  ring

lemma riesz_inverse_integrand_norm {σ y : ℝ} (hy : 0<y) (a : ℕ → ℂ) (n : ℕ) (t : ℝ) :
    ‖(y:ℂ)^(-((σ:ℂ)+t*I))*(LSeries.term a ((σ:ℂ)+t*I) n/(((σ:ℂ)+t*I)*((σ:ℂ)+t*I+1)))‖=
      (y^(-σ)*‖LSeries.term a (σ:ℂ) n‖)*‖1/(((σ:ℂ)+t*I)*((σ:ℂ)+t*I+1))‖ := by
  simp only [norm_mul,norm_div,norm_one,Complex.norm_cpow_eq_rpow_re_of_pos hy,
    Complex.neg_re,Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,
    Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_self,add_zero,LSeries.norm_term_eq]
  ring

lemma riesz_inverse_integrand_summable {σ y : ℝ} (hσ : 1≤σ) (hy : 0<y)
    (a : ℕ → ℂ) (ha : LSeriesSummable a (σ:ℂ)) :
    (∀ n : ℕ, Integrable (fun t : ℝ => (y:ℂ)^(-((σ:ℂ)+t*I))*
        (LSeries.term a ((σ:ℂ)+t*I) n/(((σ:ℂ)+t*I)*((σ:ℂ)+t*I+1))))) ∧
    Summable (fun n : ℕ => ∫ t : ℝ, ‖(y:ℂ)^(-((σ:ℂ)+t*I))*
        (LSeries.term a ((σ:ℂ)+t*I) n/(((σ:ℂ)+t*I)*((σ:ℂ)+t*I+1)))‖) := by
  have hc (n : ℕ) : Continuous (fun t : ℝ => (y:ℂ)^(-((σ:ℂ)+t*I))*
      (LSeries.term a ((σ:ℂ)+t*I) n/(((σ:ℂ)+t*I)*((σ:ℂ)+t*I+1)))) := by
    have hz (t : ℝ) : (σ:ℂ)+t*I≠0 := by
      intro hh; have := congrArg Complex.re hh; simp at this; linarith
    have hz1 (t : ℝ) : (σ:ℂ)+t*I+1≠0 := by
      intro hh; have := congrArg Complex.re hh; simp at this; linarith
    have hd : Continuous (fun t : ℝ => ((σ:ℂ)+t*I)*((σ:ℂ)+t*I+1)) := by fun_prop
    have he : Continuous (fun t : ℝ => -((σ:ℂ)+t*I)) := by fun_prop
    apply (he.const_cpow (.inl (Complex.ofReal_ne_zero.mpr hy.ne'))).mul
    apply Continuous.div _ hd (fun t => mul_ne_zero (hz t) (hz1 t))
    by_cases hn : n=0
    · simpa [hn] using (continuous_const : Continuous (fun _t : ℝ => (0:ℂ)))
    · simp only [LSeries.term_of_ne_zero hn]
      apply continuous_const.div
      · exact (show Continuous (fun t : ℝ => (σ:ℂ)+t*I) by fun_prop).const_cpow
          (.inl (Nat.cast_ne_zero.mpr hn))
      · intro t; exact Complex.cpow_ne_zero_iff.mpr (.inl (Nat.cast_ne_zero.mpr hn))
  have hnorm (n : ℕ) : Integrable (fun t : ℝ => ‖(y:ℂ)^(-((σ:ℂ)+t*I))*
      (LSeries.term a ((σ:ℂ)+t*I) n/(((σ:ℂ)+t*I)*((σ:ℂ)+t*I+1)))‖) := by
    simp_rw [riesz_inverse_integrand_norm hy]
    exact (rieszDenominator_verticalIntegrable hσ).norm.const_mul _
  refine ⟨fun n => (integrable_norm_iff (hc n).aestronglyMeasurable).mp (hnorm n), ?_⟩
  simp_rw [riesz_inverse_integrand_norm hy,integral_const_mul]
  exact (ha.norm.mul_left (y^(-σ))).mul_right _

lemma mellinInv_LSeries_riesz {σ y : ℝ} (hσ : 1≤σ) (hy : 0<y)
    (a : ℕ → ℂ) (ha : LSeriesSummable a (σ:ℂ)) :
    mellinInv σ (fun s => LSeries a s/(s*(s+1))) y=
      ∑' n : ℕ, if n=0 then 0 else a n*rieszKernel ((n:ℝ)*y) := by
  obtain ⟨hi,hs⟩ := riesz_inverse_integrand_summable hσ hy a ha
  have he := integral_tsum_of_summable_integral_norm hi hs
  simp only [mellinInv,smul_eq_mul,Complex.real_smul]
  simp only [LSeries,←tsum_div_const,←tsum_mul_left]
  rw [←he,←tsum_mul_left]
  apply tsum_congr
  intro n
  exact mellinInv_term_riesz hσ hy a n

noncomputable def rieszSum (a : ℕ → ℂ) (x : ℝ) : ℂ :=
  ∑ n∈Finset.Ioc 0 ⌊x⌋₊, a n*(1-(n:ℂ)/(x:ℂ))

lemma rieszKernel_tsum_eq {x : ℝ} (hx : 0<x) (a : ℕ → ℂ) :
    (∑' n : ℕ, if n=0 then 0 else a n*rieszKernel ((n:ℝ)*(1/x)))=rieszSum a x := by
  classical
  rw [tsum_eq_sum (s:=Finset.Ioc 0 ⌊x⌋₊)]
  · apply Finset.sum_congr rfl
    intro n hn
    obtain ⟨hn0,hnx⟩ := Finset.mem_Ioc.mp hn
    have hn0' : (0:ℝ)<n := by exact_mod_cast hn0
    have hnx' : (n:ℝ)≤x := (Nat.le_floor_iff hx.le).mp hnx
    have hm0 : 0<(n:ℝ)*(1/x) := mul_pos hn0' (one_div_pos.mpr hx)
    have hm1 : (n:ℝ)*(1/x)≤1 := by rw [mul_one_div]; exact (div_le_one hx).mpr hnx'
    rw [ite_eq_right (by omega : n≠0),rieszKernel,
      Set.indicator_of_mem (show (n:ℝ)*(1/x)∈Ioc (0:ℝ) 1 from ⟨hm0,hm1⟩)]
    push_cast
    ring
  · intro n hn
    by_cases hn0 : n=0
    · simp [hn0]
    have hnx : x<(n:ℝ) := by
      have hnot : ¬n≤⌊x⌋₊ := by intro h; exact hn (Finset.mem_Ioc.mpr ⟨Nat.pos_of_ne_zero hn0,h⟩)
      exact lt_of_not_ge (fun h => hnot ((Nat.le_floor_iff hx.le).mpr h))
    have hm1 : ¬(n:ℝ)*(1/x)≤1 := by rw [mul_one_div]; exact not_le.mpr ((lt_div_iff₀ hx).mpr (by simpa using hnx))
    rw [ite_eq_right hn0,rieszKernel,
      Set.indicator_of_notMem (show (n:ℝ)*(1/x)∉Ioc (0:ℝ) 1 from fun h => hm1 h.2),mul_zero]

lemma rieszSum_mellinInv {σ x : ℝ} (hσ : 1≤σ) (hx : 0<x)
    (a : ℕ → ℂ) (ha : LSeriesSummable a (σ:ℂ)) :
    mellinInv σ (fun s => LSeries a s/(s*(s+1))) (1/x)=rieszSum a x := by
  rw [mellinInv_LSeries_riesz hσ (one_div_pos.mpr hx) a ha,rieszKernel_tsum_eq hx]

open Complex Real Set MeasureTheory Filter Topology
noncomputable def poleRieszKernel (y : ℝ) : ℂ :=
  (1/2:ℂ)*((y:ℂ)^(-1:ℂ)*rieszKernel y-rieszKernel y)

lemma hasMellin_poleRieszKernel {s : ℂ} (hs : 1<s.re) :
    HasMellin poleRieszKernel s (1/((s-1)*s*(s+1))) := by
  have h₀ := hasMellin_rieszKernel (s:=s) (by linarith)
  have h₁ := hasMellin_rieszKernel (s:=s+(-1)) (by simp; linarith)
  have hshift : MellinConvergent (fun t : ℝ => (t:ℂ)^(-1:ℂ) • rieszKernel t) s :=
    MellinConvergent.cpow_smul.mpr h₁.1
  have hm := mellin_cpow_smul rieszKernel s (-1)
  have hh := hasMellin_sub hshift h₀.1
  rw [hm,h₁.2,h₀.2] at hh
  have hhalf := hasMellin_const_smul hh.1 (1/2:ℂ)
  rw [hh.2] at hhalf
  have he : (1/2:ℂ) • (1/((s+-1)*(s+-1+1))-1/(s*(s+1)))=
      1/((s-1)*s*(s+1)) := by
    have hs0 : s≠0 := by intro h; simp [h] at hs; norm_num at hs
    have hs1 : s-1≠0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
    have hs2 : s+1≠0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
    rw [show s+-1+1=s by ring,←sub_eq_add_neg]
    simp only [smul_eq_mul]
    field_simp [hs0,hs1,hs2]
    ring
  rw [he] at hhalf
  change HasMellin (fun t : ℝ => (1/2:ℂ)*((t:ℂ)^(-1:ℂ)*rieszKernel t-rieszKernel t)) s _
  simpa only [smul_eq_mul] using hhalf

lemma poleRieszKernel_continuousAt {y : ℝ} (hy : 0<y) :
    ContinuousAt poleRieszKernel y := by
  apply continuousAt_const.mul
  apply ContinuousAt.sub _ (rieszKernel_continuousAt hy)
  apply ContinuousAt.mul _ (rieszKernel_continuousAt hy)
  simp only [Complex.cpow_neg_one]
  have hr : ContinuousAt (fun t : ℝ => (t:ℂ)) y := Complex.continuous_ofReal.continuousAt
  exact hr.inv₀ (Complex.ofReal_ne_zero.mpr hy.ne')

set_option maxHeartbeats 3000000 in
lemma poleRiesz_verticalIntegrable {σ : ℝ} (hσ : 1<σ) :
    VerticalIntegrable (fun s : ℂ => 1/((s-1)*s*(s+1))) σ := by
  have hn (t : ℝ) : ((σ:ℂ)+t*I-1)*((σ:ℂ)+t*I)*((σ:ℂ)+t*I+1)≠0 := by
    apply mul_ne_zero
    · apply mul_ne_zero
      · intro h; have := congrArg Complex.re h; simp at this; linarith
      · intro h; have := congrArg Complex.re h; simp at this; linarith
    · intro h; have := congrArg Complex.re h; simp at this; linarith
  have hc : Continuous (fun t : ℝ => 1/(((σ:ℂ)+t*I-1)*((σ:ℂ)+t*I)*((σ:ℂ)+t*I+1))) :=
    continuous_const.div (by fun_prop) hn
  have hbase : Integrable (fun t : ℝ => ‖1/(((σ:ℂ)+t*I)*((σ:ℂ)+t*I+1))‖) :=
    (rieszDenominator_verticalIntegrable hσ.le).norm
  change Integrable (fun t : ℝ => 1/(((σ:ℂ)+t*I-1)*((σ:ℂ)+t*I)*((σ:ℂ)+t*I+1)))
  apply (hbase.const_mul (1/(σ-1))).mono' hc.aestronglyMeasurable
  filter_upwards [] with t
  rw [norm_div,norm_one,norm_mul,norm_mul]
  have hl : σ-1 ≤ ‖(σ:ℂ)+t*I-1‖ := by simpa using Complex.re_le_norm ((σ:ℂ)+t*I-1)
  have hn0 : 0<‖(σ:ℂ)+t*I-1‖ := lt_of_lt_of_le (by linarith) hl
  have hh : 1/‖(σ:ℂ)+t*I-1‖ ≤ 1/(σ-1) := one_div_le_one_div_of_le (by linarith) hl
  simpa only [norm_div,norm_one,norm_mul,div_eq_mul_inv,mul_inv_rev,norm_inv,mul_assoc,mul_comm,mul_left_comm,one_mul,mul_one]
    using mul_le_mul_of_nonneg_right hh (norm_nonneg (1/(((σ:ℂ)+t*I)*((σ:ℂ)+t*I+1))))

lemma poleRiesz_mellinInv {σ y : ℝ} (hσ : 1<σ) (hy : 0<y) :
    mellinInv σ (fun s : ℂ => 1/((s-1)*s*(s+1))) y=poleRieszKernel y := by
  have hm (t : ℝ) : mellin poleRieszKernel (σ+t*I)=1/((σ+t*I-1)*(σ+t*I)*(σ+t*I+1)) :=
    (hasMellin_poleRieszKernel (by simpa using hσ)).2
  have hf : VerticalIntegrable (mellin poleRieszKernel) σ := by
    unfold VerticalIntegrable
    simp_rw [hm]
    exact poleRiesz_verticalIntegrable hσ
  rw [←mellinInv_mellin_eq σ poleRieszKernel hy
    (hasMellin_poleRieszKernel (by simpa using hσ)).1 hf (poleRieszKernel_continuousAt hy)]
  simp only [mellinInv,hm]

lemma poleRieszKernel_inv {x : ℝ} (hx : 1≤x) :
    poleRieszKernel (1/x)=((x/2-1+1/(2*x):ℝ):ℂ) := by
  have hx0 : 0<x := by linarith
  have hy : 0<1/x := one_div_pos.mpr hx0
  have hy1 : 1/x≤1 := (div_le_one hx0).mpr hx
  rw [poleRieszKernel,rieszKernel_eq_max hy,max_eq_left (by linarith : 0≤1-1/x)]
  simp only [Complex.cpow_neg_one,Complex.ofReal_div,Complex.ofReal_one,inv_div,div_one,
    Complex.ofReal_sub,Complex.ofReal_add,Complex.ofReal_mul,Complex.ofReal_ofNat]
  have hn : (x:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hx0.ne'
  field_simp
  ring

lemma mellinInv_integrable {σ y : ℝ} (hy : 0<y) {f : ℂ → ℂ}
    (hf : VerticalIntegrable f σ) :
    Integrable (fun t : ℝ => (y:ℂ)^(-((σ:ℂ)+t*I))*f ((σ:ℂ)+t*I)) := by
  have he : Continuous (fun t : ℝ => -((σ:ℂ)+t*I)) := by fun_prop
  have hc := he.const_cpow (.inl (Complex.ofReal_ne_zero.mpr hy.ne'))
  apply (hf.norm.const_mul (y^(-σ))).mono' (hc.aestronglyMeasurable.mul hf.aestronglyMeasurable)
  filter_upwards [] with t
  change ‖(y:ℂ)^(-((σ:ℂ)+t*I))*f ((σ:ℂ)+t*I)‖ ≤ y^(-σ)*‖f ((σ:ℂ)+t*I)‖
  simp only [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hy,Complex.neg_re,
    Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
    mul_zero,zero_mul,sub_self,add_zero,le_refl]

lemma mellinInv_add_of_verticalIntegrable {σ y : ℝ} (hy : 0<y) {f g : ℂ → ℂ}
    (hf : VerticalIntegrable f σ) (hg : VerticalIntegrable g σ) :
    mellinInv σ (fun s => f s+g s) y=mellinInv σ f y+mellinInv σ g y := by
  simp only [mellinInv,smul_eq_mul,Complex.real_smul,mul_add]
  rw [integral_add (mellinInv_integrable hy hf) (mellinInv_integrable hy hg),mul_add]

open Complex Real Set MeasureTheory Filter Topology
open scoped FourierTransform
end LargePrimeGaps
end OAI

-- Source module: RieszDecay
namespace OAI
namespace LargePrimeGaps
open Complex Filter Topology
open Complex Filter Topology MeasureTheory
open Complex Real Set MeasureTheory Filter Topology
open scoped FourierTransform
noncomputable def logRieszVertical {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (σ t : ℝ) : ℂ := logRiesz (poleRemovedL χ) (σ+2*π*t*I)

lemma logRieszVertical_contDiff {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {σ : ℝ} (hσ : 1≤σ) : ContDiff ℝ ⊤ (logRieszVertical χ σ) := by
  have h : ∀ t : ℝ, AnalyticAt ℂ (logRiesz (poleRemovedL χ)) ((σ:ℂ)+(2*π*I)*(t:ℂ)) := by
    intro t
    apply logRiesz_poleRemoved_analyticAt
    simpa using hσ
  convert vertical_contDiff h using 1
  ext t
  dsimp [logRieszVertical]
  congr 1
  ring

lemma logRieszVertical_iteratedDeriv {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {σ : ℝ} (hσ : 1≤σ) (n : ℕ) (t : ℝ) :
    iteratedDeriv n (logRieszVertical χ σ) t=
      ((2:ℂ)*π*I)^n*iteratedDeriv n (logRiesz (poleRemovedL χ)) (σ+2*π*t*I) := by
  have h : ∀ t : ℝ, AnalyticAt ℂ (logRiesz (poleRemovedL χ)) ((σ:ℂ)+(2*π*I)*(t:ℂ)) := by
    intro t
    apply logRiesz_poleRemoved_analyticAt
    simpa using hσ
  have he : logRieszVertical χ σ=(fun t : ℝ => logRiesz (poleRemovedL χ) ((σ:ℂ)+(2*π*I)*(t:ℂ))) := by
    ext t
    dsimp [logRieszVertical]
    congr 1
    ring
  simpa only [he,mul_assoc,mul_comm,mul_left_comm] using congrFun (vertical_iteratedDeriv h n) t

lemma logRieszVertical_bound (n : ℕ) :
    ∃ D : ℝ, 0<D ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
      ∀ σ t : ℝ, 1≤σ → σ≤2 →
        ‖iteratedDeriv n (logRieszVertical χ σ) t‖ ≤
          (D*((q:ℝ)+2)^(1/2:ℝ))*decayMajorant t := by
  obtain ⟨D,hD,hb⟩ := primitive_logRiesz_bound n
  refine ⟨(2*π)^n*D,by positivity,?_⟩
  intro q _ χ hp σ t hσ hσ2
  have he : (σ:ℂ)+2*π*t*I=(σ:ℂ)+I*((2*π*t:ℝ):ℂ) := by push_cast; ring
  rw [logRieszVertical_iteratedDeriv χ hσ,norm_mul,norm_pow,he]
  have hc : ‖(2:ℂ)*π*I‖=2*π := by simp [abs_of_pos pi_pos]
  rw [hc]
  have ht : (|2*π*t|+2)^(-(3/2:ℝ)) ≤ decayMajorant t := by
    dsimp [decayMajorant]
    apply Real.rpow_le_rpow_of_nonpos (by positivity)
    · rw [abs_mul,abs_mul,abs_of_pos pi_pos]
      norm_num
      nlinarith [abs_nonneg t,pi_gt_three]
    · norm_num
  calc
    _ ≤ (2*π)^n*(D*((q:ℝ)+2)^(1/2:ℝ)*(|2*π*t|+2)^(-(3/2:ℝ))) :=
      mul_le_mul_of_nonneg_left (hb q χ hp σ (2*π*t) hσ hσ2) (by positivity)
    _ ≤ (2*π)^n*(D*((q:ℝ)+2)^(1/2:ℝ)*decayMajorant t) := by gcongr
    _ = _ := by ring

lemma logRieszVertical_integrable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hp : χ.IsPrimitive) {σ : ℝ} (hσ : 1≤σ) (hσ2 : σ≤2) (n : ℕ) :
    Integrable (iteratedDeriv n (logRieszVertical χ σ)) := by
  obtain ⟨D,hD,hb⟩ := logRieszVertical_bound n
  exact integrable_of_decay_bound
    ((logRieszVertical_contDiff χ hσ).continuous_iteratedDeriv n (by simp))
    (hb q χ hp σ · hσ hσ2)

lemma logRiesz_mellinInv_bound (n : ℕ) :
    ∃ D : ℝ, 0<D ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
      ∀ σ x : ℝ, 1≤σ → σ≤2 → 1<x →
        ‖mellinInv σ (logRiesz (poleRemovedL χ)) (1/x)‖ ≤
          D*((q:ℝ)+2)^(1/2:ℝ)*x^σ/(Real.log x)^n := by
  obtain ⟨D,hD,hb⟩ := logRieszVertical_bound n
  let J : ℝ := ∫ t, decayMajorant t
  refine ⟨D*(|J|+1),by dsimp [J]; positivity,?_⟩
  intro q _ χ hp σ x hσ hσ2 hx
  have hx0 : 0<x := by linarith
  have hlog : 0<Real.log x := Real.log_pos hx
  have hi := logRieszVertical_integrable χ hp hσ hσ2
  have hg := logRieszVertical_contDiff χ hσ
  have hb' : (∫ t, ‖iteratedDeriv n (logRieszVertical χ σ) t‖) ≤ D*((q:ℝ)+2)^(1/2:ℝ)*J :=
    integral_norm_le_of_decay_bound (hg.continuous_iteratedDeriv n (by simp)) (hb q χ hp σ · hσ hσ2)
  have hf := fourierInv_decay hg hi n hb' (u:=Real.log x) (by rwa [abs_of_pos hlog])
  rw [mellinInv_eq_fourierInv σ _ (one_div_pos.mpr hx0),norm_smul,
    Complex.norm_cpow_eq_rpow_re_of_pos (one_div_pos.mpr hx0)]
  have he : -(Real.log (1/x))=Real.log x := by simp
  rw [he]
  change (1/x)^(-σ)*‖𝓕⁻ (logRieszVertical χ σ) (Real.log x)‖ ≤ _
  rw [one_div,Real.inv_rpow hx0.le,←Real.rpow_neg hx0.le,neg_neg]
  have hJ : J ≤ |J|+1 := by linarith [le_abs_self J]
  have hfac : 0≤ D*((q:ℝ)+2)^(1/2:ℝ) := by positivity
  calc
    _ ≤ x^σ*(D*((q:ℝ)+2)^(1/2:ℝ)*J/|Real.log x|^n) := mul_le_mul_of_nonneg_left hf (by positivity)
    _ ≤ x^σ*(D*((q:ℝ)+2)^(1/2:ℝ)*(|J|+1)/(Real.log x)^n) := by
      rw [abs_of_pos hlog]
      gcongr
    _ = _ := by ring

open Complex Real Set MeasureTheory Filter Topology
noncomputable def primeCoefficients {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ℕ) : ℂ :=
  χ (n:ZMod q)*(ArithmeticFunction.vonMangoldt n:ℂ)

noncomputable def characterMain {q : ℕ} (χ : DirichletCharacter ℂ q) : ℂ := by
  classical
  exact if χ=1 then 1 else 0

lemma characterMain_norm_le {q : ℕ} (χ : DirichletCharacter ℂ q) : ‖characterMain χ‖≤1 := by
  unfold characterMain
  split_ifs <;> norm_num

lemma primeCoefficients_summable {q : ℕ} (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1<s.re) :
    LSeriesSummable (primeCoefficients χ) s := DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ hs

lemma primeCoefficients_norm_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (n : ℕ) :
    ‖primeCoefficients χ n‖≤Real.log n := by
  rw [primeCoefficients,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  exact (mul_le_of_le_one_left ArithmeticFunction.vonMangoldt_nonneg (χ.norm_le_one _)).trans
    ArithmeticFunction.vonMangoldt_le_log

lemma primeRiesz_identity {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1<s.re) :
    LSeries (primeCoefficients χ) s/(s*(s+1))=
      logRiesz (poleRemovedL χ) s+characterMain χ*(1/((s-1)*s*(s+1))) := by
  have he := primeLogDerivativeRegular_eq χ hs
  change primeLogDerivativeRegular χ s=LSeries (primeCoefficients χ) s-_ at he
  have hlog : logRiesz (poleRemovedL χ) s=primeLogDerivativeRegular χ s/(s*(s+1)) := rfl
  have hs0 : s≠0 := by intro h; simp [h] at hs; norm_num at hs
  have hs1 : s-1≠0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
  have hs2 : s+1≠0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
  rw [hlog,he,characterMain]
  split_ifs <;> field_simp <;> ring

lemma logRiesz_verticalIntegrable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hp : χ.IsPrimitive) {σ : ℝ} (hσ : 1≤σ) (hσ2 : σ≤2) :
    VerticalIntegrable (logRiesz (poleRemovedL χ)) σ := by
  have hπ : (2*π:ℝ)≠0 := by positivity
  have hi := (logRieszVertical_integrable χ hp hσ hσ2 0).comp_mul_left' (inv_ne_zero hπ)
  simp only [iteratedDeriv_zero] at hi
  have he : (fun t : ℝ => logRieszVertical χ σ ((2*π)⁻¹*t))=
      (fun t : ℝ => logRiesz (poleRemovedL χ) (σ+t*I)) := by
    ext t
    dsimp [logRieszVertical]
    congr 1
    push_cast
    field_simp
  rwa [he] at hi

set_option maxHeartbeats 800000 in
lemma primeRiesz_mellinInv {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hp : χ.IsPrimitive) {σ x : ℝ} (hσ : 1<σ) (hσ2 : σ≤2) (hx : 0<x) :
    mellinInv σ (logRiesz (poleRemovedL χ)) (1/x)=
      rieszSum (primeCoefficients χ) x-characterMain χ*poleRieszKernel (1/x) := by
  have he : rieszSum (primeCoefficients χ) x=
      mellinInv σ (logRiesz (poleRemovedL χ)) (1/x)+characterMain χ*poleRieszKernel (1/x) := by
    rw [←rieszSum_mellinInv hσ.le hx _ (primeCoefficients_summable χ (by simpa using hσ))]
    calc
      _ = mellinInv σ (fun s => logRiesz (poleRemovedL χ) s+
          characterMain χ*(1/((s-1)*s*(s+1)))) (1/x) := by
        unfold mellinInv
        congr 1
        apply integral_congr_ae
        filter_upwards [] with t
        rw [primeRiesz_identity χ (by simpa using hσ)]
      _ = mellinInv σ (logRiesz (poleRemovedL χ)) (1/x)+
          mellinInv σ (fun s => characterMain χ*(1/((s-1)*s*(s+1)))) (1/x) :=
        mellinInv_add_of_verticalIntegrable (one_div_pos.mpr hx)
          (logRiesz_verticalIntegrable χ hp hσ.le hσ2) ((poleRiesz_verticalIntegrable hσ).const_mul _)
      _ = _ := by rw [mellinInv_const_mul,poleRiesz_mellinInv hσ (one_div_pos.mpr hx)]
  linear_combination -he

lemma primeRiesz_error_bound (n : ℕ) :
    ∃ D : ℝ, 0<D ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
      ∀ σ x : ℝ, 1<σ → σ≤2 → 1<x →
        ‖rieszSum (primeCoefficients χ) x-characterMain χ*(x:ℂ)/2‖ ≤
          D*((q:ℝ)+2)^(1/2:ℝ)*x^σ/(Real.log x)^n+1 := by
  obtain ⟨D,hD,hb⟩ := logRiesz_mellinInv_bound n
  refine ⟨D,hD,?_⟩
  intro q _ χ hp σ x hσ hσ2 hx
  have he := primeRiesz_mellinInv χ hp hσ hσ2 (by linarith : 0<x)
  rw [poleRieszKernel_inv hx.le] at he
  have he' : rieszSum (primeCoefficients χ) x-characterMain χ*(x:ℂ)/2=
      mellinInv σ (logRiesz (poleRemovedL χ)) (1/x)+characterMain χ*((-1+1/(2*x):ℝ):ℂ) := by
    push_cast at he ⊢
    linear_combination -he
  rw [he']
  apply (norm_add_le _ _).trans
  apply add_le_add (hb q χ hp σ x hσ.le hσ2 hx)
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
  have ht : |-1+1/(2*x)|≤1 := by
    rw [abs_le]
    have hx0 : 0<x := by linarith
    have ht0 : 0≤1/(2*x) := by positivity
    have ht1 : 1/(2*x)≤1 := (div_le_one (by positivity)).mpr (by linarith)
    constructor <;> linarith
  exact (mul_le_mul (characterMain_norm_le χ) ht (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)

open Complex Real Set MeasureTheory Filter Topology
noncomputable def weightedPrefix (a : ℕ → ℂ) (x : ℝ) : ℂ :=
  ∑ n∈Finset.Ioc 0 ⌊x⌋₊, ((x-(n:ℝ):ℝ):ℂ)*a n

lemma weightedPrefix_difference {x h : ℝ} (hh : 0≤h) (a : ℕ → ℂ) :
    weightedPrefix a (x+h)-weightedPrefix a x=
      (h:ℂ)*(∑ n∈Finset.Ioc 0 ⌊x⌋₊, a n)+
      ∑ n∈Finset.Ioc ⌊x⌋₊ ⌊x+h⌋₊, ((x+h-(n:ℝ):ℝ):ℂ)*a n := by
  classical
  have hfloor : ⌊x⌋₊≤⌊x+h⌋₊ := Nat.floor_mono (by linarith)
  have he : Finset.Ioc 0 ⌊x+h⌋₊=Finset.Ioc 0 ⌊x⌋₊ ∪ Finset.Ioc ⌊x⌋₊ ⌊x+h⌋₊ := by
    ext n
    simp only [Finset.mem_Ioc,Finset.mem_union]
    omega
  have hd : Disjoint (Finset.Ioc 0 ⌊x⌋₊) (Finset.Ioc ⌊x⌋₊ ⌊x+h⌋₊) := by
    rw [Finset.disjoint_left]
    intro n h₁ h₂
    simp only [Finset.mem_Ioc] at h₁ h₂
    omega
  unfold weightedPrefix
  rw [he,Finset.sum_union hd]
  have hs : (∑ n∈Finset.Ioc 0 ⌊x⌋₊, ((x+h-(n:ℝ):ℝ):ℂ)*a n)=
      (h:ℂ)*(∑ n∈Finset.Ioc 0 ⌊x⌋₊, a n)+
      ∑ n∈Finset.Ioc 0 ⌊x⌋₊, ((x-(n:ℝ):ℝ):ℂ)*a n := by
    rw [Finset.mul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n _
    push_cast
    ring
  rw [hs]
  ring

lemma weightedPrefix_tail_bound {x h L : ℝ} (hx : 0≤x) (hh : 0≤h) (hL : 0≤L)
    (a : ℕ → ℂ) (ha : ∀ n∈Finset.Ioc ⌊x⌋₊ ⌊x+h⌋₊, ‖a n‖≤L) :
    ‖∑ n∈Finset.Ioc ⌊x⌋₊ ⌊x+h⌋₊, ((x+h-(n:ℝ):ℝ):ℂ)*a n‖ ≤ (h+1)*(h*L) := by
  have hfloor : ⌊x⌋₊≤⌊x+h⌋₊ := Nat.floor_mono (by linarith)
  have hn (n : ℕ) (hn : n∈Finset.Ioc ⌊x⌋₊ ⌊x+h⌋₊) :
      0≤x+h-(n:ℝ) ∧ x+h-(n:ℝ)≤h := by
    obtain ⟨h₁,h₂⟩ := Finset.mem_Ioc.mp hn
    have hlo : x<(n:ℝ) := by
      have hn' : (⌊x⌋₊:ℝ)+1≤n := by exact_mod_cast h₁
      linarith [Nat.lt_floor_add_one x]
    have hup : (n:ℝ)≤x+h := (Nat.le_floor_iff (by linarith)).mp h₂
    constructor <;> linarith
  have hc : ((Finset.Ioc ⌊x⌋₊ ⌊x+h⌋₊).card:ℝ) ≤ h+1 := by
    rw [Nat.card_Ioc,Nat.cast_sub hfloor]
    have hlo := Nat.lt_floor_add_one x
    have hup := Nat.floor_le (by linarith : 0≤x+h)
    linarith
  calc
    _ ≤ ∑ n∈Finset.Ioc ⌊x⌋₊ ⌊x+h⌋₊, ‖((x+h-(n:ℝ):ℝ):ℂ)*a n‖ := norm_sum_le _ _
    _ ≤ ∑ _n∈Finset.Ioc ⌊x⌋₊ ⌊x+h⌋₊, h*L := by
      apply Finset.sum_le_sum
      intro n hn'
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hn n hn').1]
      exact mul_le_mul (hn n hn').2 (ha n hn') (norm_nonneg _) hh
    _ = ((Finset.Ioc ⌊x⌋₊ ⌊x+h⌋₊).card:ℝ)*(h*L) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hc (mul_nonneg hh hL)

lemma prefix_unsmoothing {x h L : ℝ} (hx : 0≤x) (hh : 0<h) (hL : 0≤L)
    (a : ℕ → ℂ) (δ : ℂ) (ha : ∀ n∈Finset.Ioc ⌊x⌋₊ ⌊x+h⌋₊, ‖a n‖≤L) :
    ‖(∑ n∈Finset.Ioc 0 ⌊x⌋₊, a n)-δ*(x:ℂ)‖ ≤
      (‖weightedPrefix a (x+h)-δ*((x+h:ℝ):ℂ)^2/2‖+
        ‖weightedPrefix a x-δ*(x:ℂ)^2/2‖)/h+(h+1)*L+‖δ‖*h/2 := by
  let T := ∑ n∈Finset.Ioc ⌊x⌋₊ ⌊x+h⌋₊, ((x+h-(n:ℝ):ℝ):ℂ)*a n
  let E (y : ℝ) := weightedPrefix a y-δ*(y:ℂ)^2/2
  have he : (h:ℂ)*((∑ n∈Finset.Ioc 0 ⌊x⌋₊, a n)-δ*(x:ℂ))=
      (E (x+h)-E x)-T+δ*(h:ℂ)^2/2 := by
    have hd := weightedPrefix_difference (x:=x) hh.le a
    change weightedPrefix a (x+h)-weightedPrefix a x = _+T at hd
    dsimp [E]
    push_cast
    linear_combination -hd
  have hn : h*‖(∑ n∈Finset.Ioc 0 ⌊x⌋₊, a n)-δ*(x:ℂ)‖ ≤
      (‖E (x+h)‖+‖E x‖)+((h+1)*(h*L))+‖δ‖*h^2/2 := by
    calc
      _ = ‖(h:ℂ)*((∑ n∈Finset.Ioc 0 ⌊x⌋₊, a n)-δ*(x:ℂ))‖ := by
        rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hh]
      _ = ‖(E (x+h)-E x)-T+δ*(h:ℂ)^2/2‖ := congrArg norm he
      _ ≤ ‖E (x+h)-E x‖+‖T‖+‖δ*(h:ℂ)^2/2‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
      _ ≤ (‖E (x+h)‖+‖E x‖)+((h+1)*(h*L))+‖δ‖*h^2/2 := by
        have hT : ‖T‖≤(h+1)*(h*L) := weightedPrefix_tail_bound hx hh.le hL a ha
        have hδ : ‖δ*(h:ℂ)^2/2‖=‖δ‖*h^2/2 := by
          simp [norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hh]
        rw [hδ]
        exact add_le_add (add_le_add (norm_sub_le _ _) hT) le_rfl
  have hd : h*((‖E (x+h)‖+‖E x‖)/h+(h+1)*L+‖δ‖*h/2)=
      (‖E (x+h)‖+‖E x‖)+((h+1)*(h*L))+‖δ‖*h^2/2 := by field_simp
  dsimp [E] at hn hd
  apply (mul_le_mul_iff_left₀ hh).mp
  rw [mul_comm _ h, mul_comm _ h, hd]
  exact hn

open Complex Real Set MeasureTheory Filter Topology
lemma weightedPrefix_eq_mul_rieszSum (a : ℕ → ℂ) {x : ℝ} (hx : 0<x) :
    weightedPrefix a x=(x:ℂ)*rieszSum a x := by
  unfold weightedPrefix rieszSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hx0 : (x:ℂ)≠0 := by exact_mod_cast hx.ne'
  push_cast
  field_simp

lemma rpow_one_add_inv_log {x : ℝ} (hx : 1<x) :
    x^(1+1/Real.log x)=Real.exp 1*x := by
  have hx0 : 0<x := by linarith
  have hlog : Real.log x≠0 := (Real.log_pos hx).ne'
  rw [Real.rpow_add hx0,Real.rpow_one,Real.rpow_def_of_pos hx0]
  rw [mul_one_div_cancel hlog]
  ring

lemma primeWeighted_error_bound (a : ℝ) :
    ∃ D : ℝ, 0<D ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
      ∀ x : ℝ, 1<x → 1≤Real.log x →
        ‖weightedPrefix (primeCoefficients χ) x-characterMain χ*(x:ℂ)^2/2‖ ≤
          D*((q:ℝ)+2)^(1/2:ℝ)*x^2*(Real.log x)^(-a)+x := by
  obtain ⟨D,hD,hb⟩ := primeRiesz_error_bound ⌈a⌉₊
  refine ⟨D*Real.exp 1,by positivity,?_⟩
  intro q _ χ hp x hx hL
  have hx0 : 0<x := by linarith
  have hlog : 0<Real.log x := Real.log_pos hx
  have hσ : 1<1+1/Real.log x := by linarith [one_div_pos.mpr hlog]
  have hσ2 : 1+1/Real.log x≤2 := by
    have : 1/Real.log x≤1 := (div_le_one hlog).mpr hL
    linarith
  have he : weightedPrefix (primeCoefficients χ) x-characterMain χ*(x:ℂ)^2/2=
      (x:ℂ)*(rieszSum (primeCoefficients χ) x-characterMain χ*(x:ℂ)/2) := by
    rw [weightedPrefix_eq_mul_rieszSum _ hx0]
    ring
  rw [he,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hx0]
  calc
    _ ≤ x*(D*((q:ℝ)+2)^(1/2:ℝ)*x^(1+1/Real.log x)/(Real.log x)^⌈a⌉₊+1) :=
      mul_le_mul_of_nonneg_left (hb q χ hp _ x hσ hσ2 hx) hx0.le
    _ = D*Real.exp 1*((q:ℝ)+2)^(1/2:ℝ)*x^2*(Real.log x)^(-(⌈a⌉₊:ℝ))+x := by
      rw [rpow_one_add_inv_log hx,Real.rpow_neg hlog.le,Real.rpow_natCast]
      ring
    _ ≤ _ := by
      have hn : a≤(⌈a⌉₊:ℝ) := Nat.le_ceil a
      gcongr

end LargePrimeGaps
end OAI

-- Source module: Main
namespace OAI
namespace LargePrimeGaps
open Complex Filter Topology
open Complex Filter Topology MeasureTheory
open scoped FourierTransform
open Complex Real Set MeasureTheory Filter Topology
lemma primeCharacterError_log_bound (A B : ℝ) (hA : 0<A) (hB : 0<B) :
    ∃ M : ℝ, 0<M ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
      ∀ x : ℝ, 2≤x → 1≤Real.log x → (Real.log x)^(2*A+2)≤x →
        (q:ℝ)≤(Real.log x)^B →
        ‖primeCharacterError x χ‖≤M*x*(Real.log x)^(-A) := by
  obtain ⟨D,hD,hb⟩ := primeWeighted_error_bound (B+2*A+2)
  refine ⟨15*D+8,by positivity,?_⟩
  intro q _ χ hp x hx hL hpower hq
  let L := Real.log x
  let K := A+2
  let a := B+2*A+2
  let Q := ((q:ℝ)+2)^(1/2:ℝ)
  let h := x/L^K
  have hx0 : 0<x := by linarith
  have hx1 : 1<x := by linarith
  have hL0 : 0<L := lt_of_lt_of_le zero_lt_one hL
  have hK : 0<K := by dsimp [K]; linarith
  have ha : 0<a := by dsimp [a]; linarith
  have hpK : 0<L^K := Real.rpow_pos_of_pos hL0 _
  have hh0 : 0<h := div_pos hx0 hpK
  have hK1 : 1≤L^K := Real.one_le_rpow hL hK.le
  have hhx : h≤x := (div_le_self hx0.le hK1)
  have hKh : L^K≤x := by
    apply (Real.rpow_le_rpow_of_exponent_le hL (show K≤2*A+2 by dsimp [K]; linarith)).trans
    exact hpower
  have hh1 : 1≤h := (le_div_iff₀ hpK).mpr (by simpa using hKh)
  have hyx : x≤x+h := by linarith
  have hy : 1<x+h := by linarith
  have hy2 : x+h≤2*x := by linarith
  have hLy : L≤Real.log (x+h) := Real.log_le_log hx0 hyx
  have hLy1 : 1≤Real.log (x+h) := hL.trans hLy
  have hLy2 : Real.log (x+h)≤2*L := by
    calc
      _ ≤ Real.log (x^2) := Real.log_le_log (by linarith) (by nlinarith)
      _ = _ := by rw [Real.log_pow]; rfl
  have hQ0 : 0≤Q := by dsimp [Q]; positivity
  have hQ : Q≤3*L^B := by
    have hq2 : 1≤(q:ℝ)+2 := by have := Nat.cast_nonneg (α:=ℝ) q; linarith
    have hqpow : Q≤(q:ℝ)+2 := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hq2 (show (1/2:ℝ)≤1 by norm_num)
    have hLB : 1≤L^B := Real.one_le_rpow hL hB.le
    linarith
  let E (y : ℝ) := ‖weightedPrefix (primeCoefficients χ) y-characterMain χ*(y:ℂ)^2/2‖
  have hEx : E x≤D*Q*x^2*L^(-a)+x := hb q χ hp x hx1 hL
  have hEy : E (x+h)≤4*D*Q*x^2*L^(-a)+2*x := by
    calc
      _ ≤ D*Q*(x+h)^2*(Real.log (x+h))^(-a)+(x+h) := hb q χ hp (x+h) hy hLy1
      _ ≤ D*Q*(2*x)^2*L^(-a)+2*x := by
        apply add_le_add _ hy2
        apply mul_le_mul _ (Real.rpow_le_rpow_of_nonpos hL0 hLy (neg_nonpos.mpr ha.le)) (by positivity) (by positivity)
        gcongr
      _ = _ := by ring
  have hcoeff (n : ℕ) (hn : n∈Finset.Ioc ⌊x⌋₊ ⌊x+h⌋₊) :
      ‖primeCoefficients χ n‖≤2*L := by
    have hn0 : 0<(n:ℝ) := by exact_mod_cast (show 0<n by have := (Finset.mem_Ioc.mp hn).1; omega)
    have hnx : (n:ℝ)≤x+h := (Nat.le_floor_iff (by linarith : 0≤x+h)).mp (Finset.mem_Ioc.mp hn).2
    exact (primeCoefficients_norm_le χ n).trans ((Real.log_le_log hn0 hnx).trans hLy2)
  have heq : primeCharacterError x χ=
      (∑ n∈Finset.Ioc 0 ⌊x⌋₊, primeCoefficients χ n)-characterMain χ*(x:ℂ) := by
    classical
    simp only [primeCharacterError,primeCharacterPrefix,primeCoefficients,characterMain]
    split_ifs <;> simp
  rw [heq]
  have hu := prefix_unsmoothing hx0.le hh0 (show 0≤2*L by positivity)
    (primeCoefficients χ) (characterMain χ) hcoeff
  change _≤(E (x+h)+E x)/h+(h+1)*(2*L)+‖characterMain χ‖*h/2 at hu
  have hδ : ‖characterMain χ‖*h/2≤h := by
    have := mul_le_mul_of_nonneg_right (characterMain_norm_le χ) hh0.le
    linarith
  have htail : (h+1)*(2*L)≤4*h*L := by nlinarith
  have herr : (E (x+h)+E x)/h ≤ 15*D*x*L^(-A)+3*x*L^(-A) := by
    calc
      _ ≤ (5*D*Q*x^2*L^(-a)+3*x)/h := by
        apply div_le_div_of_nonneg_right _ hh0.le
        linarith
      _ ≤ (5*D*(3*L^B)*x^2*L^(-a)+3*x)/h := by gcongr
      _ = (15*D*L^B*x^2*L^(-a)+3*x)/h := by ring
      _ = 15*D*x*L^(-A)+3*L^K := by
        dsimp [h]
        rw [div_eq_mul_inv,inv_div]
        have hr : L^B*L^(-a)*L^K=L^(-A) := by
          rw [←Real.rpow_add hL0,←Real.rpow_add hL0]
          congr 1
          dsimp [a,K]
          ring
        field_simp
        linear_combination 15*D*x*hr
      _ ≤ _ := by
        have ht : L^K≤x*L^(-A) := by
          calc
            _ = L^(2*A+2)*L^(-A) := by rw [←Real.rpow_add hL0]; congr 1; dsimp [K]; ring
            _ ≤ _ := mul_le_mul_of_nonneg_right hpower (by positivity)
        nlinarith [ht]
  have hsmall : h≤x*L^(-A) := by
    dsimp [h]
    rw [div_eq_mul_inv,←Real.rpow_neg hL0.le]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hL (show -K≤-A by dsimp [K]; linarith)) hx0.le
  have htail' : 4*h*L≤4*x*L^(-A) := by
    calc
      _ = 4*x*L^(1-K) := by
        dsimp [h]
        rw [div_eq_mul_inv,Real.rpow_sub hL0,Real.rpow_one]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hL (show 1-K≤-A by dsimp [K]; linarith)) (by positivity)
  calc
    _ ≤ (E (x+h)+E x)/h+(h+1)*(2*L)+‖characterMain χ‖*h/2 := hu
    _ ≤ (15*D*x*L^(-A)+3*x*L^(-A))+4*x*L^(-A)+x*L^(-A) := by
      exact add_le_add (add_le_add herr (htail.trans htail')) (hδ.trans hsmall)
    _ = _ := by ring

theorem siegelWalfisz : SiegelWalfisz := by
  intro A B hA hB
  obtain ⟨M,hM,hb⟩ := primeCharacterError_log_bound A B hA hB
  have hevent : ∀ᶠ x : ℝ in atTop, 2≤x ∧ 1≤Real.log x ∧ (Real.log x)^(2*A+2)≤x := by
    filter_upwards [eventually_ge_atTop (2:ℝ),eventually_ge_atTop (Real.exp 1),
      eventually_log_rpow_le_rpow (2*A+2) (by norm_num : (0:ℝ)<1)] with x hx hex hp
    refine ⟨hx,?_,by simpa only [Real.rpow_one] using hp⟩
    rw [←Real.log_exp (1:ℝ)]
    exact Real.log_le_log (Real.exp_pos _) hex
  obtain ⟨x₀,hx₀⟩ := eventually_atTop.mp hevent
  refine ⟨M,hM,max x₀ 2,by have := le_max_right x₀ (2:ℝ); linarith,?_⟩
  intro x hx d hd hdlog χ hχ
  let : NeZero d := ⟨ne_of_gt hd⟩
  obtain ⟨hx2,hlog,hpower⟩ := hx₀ x ((le_max_left _ _).trans hx)
  exact hb d χ hχ x hx2 hlog hpower hdlog

end LargePrimeGaps
end OAI


-- Source module: OrthantIntegrals
namespace OAI
namespace LargePrimeGaps
open Filter
open Set Filter MeasureTheory
open scoped Topology ContDiff
noncomputable def residueSlice (f : ℕ → ℝ) (L U q c : ℕ) : ℝ :=
  ∑ n ∈ (Finset.Ioc L U).filter (fun n => n % q = c), f n

noncomputable def residuePrefix (f : ℕ → ℝ) (Y q c : ℕ) : ℝ :=
  residueSlice f 0 Y q c

end LargePrimeGaps
end OAI

-- Source module: CharacterErrors
namespace OAI
namespace LargePrimeGaps
open Filter
open Set Filter MeasureTheory
open scoped Topology ContDiff
open Asymptotics
open scoped Classical
open scoped ContDiff
open Topology
open scoped Convolution ContDiff Pointwise
theorem character_prefix_orthogonality (x : ℝ) {q c : ℕ} (hq : 0<q)
    (hc : c<q) (hcop : Nat.Coprime c q) :
    ∑ χ : DirichletCharacter ℂ q, χ (c:ZMod q)⁻¹*primeCharacterPrefix x χ=
      (q.totient:ℂ)*(residuePrefix ArithmeticFunction.vonMangoldt ⌊x⌋₊ q c:ℂ) := by
  classical
  have : NeZero q := ⟨ne_of_gt hq⟩
  have hu : IsUnit (c:ZMod q) := (ZMod.isUnit_iff_coprime c q).mpr hcop
  have he (n : ℕ) : (c:ZMod q)=(n:ZMod q) ↔ n % q = c := by
    rw [ZMod.natCast_eq_natCast_iff',Nat.mod_eq_of_lt hc]
    exact eq_comm
  unfold primeCharacterPrefix
  simp_rw [Finset.mul_sum,←mul_assoc]
  rw [Finset.sum_comm]
  simp_rw [←Finset.sum_mul,DirichletCharacter.sum_char_inv_mul_char_eq ℂ hu,he]
  simp only [residuePrefix,residueSlice,Complex.ofReal_sum,Finset.sum_filter,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  split_ifs <;> simp

theorem character_error_orthogonality (x : ℝ) {q c : ℕ} (hq : 0<q)
    (hc : c<q) (hcop : Nat.Coprime c q) :
    ∑ χ : DirichletCharacter ℂ q, χ (c:ZMod q)⁻¹*primeCharacterError x χ=
      (q.totient:ℂ)*((residuePrefix ArithmeticFunction.vonMangoldt ⌊x⌋₊ q c-x/q.totient:ℝ):ℂ) := by
  classical
  have : NeZero q := ⟨ne_of_gt hq⟩
  have hu : IsUnit (c:ZMod q) := (ZMod.isUnit_iff_coprime c q).mpr hcop
  have huinv : IsUnit (c:ZMod q)⁻¹ := by
    obtain ⟨u,hu⟩ := hu
    rw [←hu,ZMod.inv_coe_unit]
    exact (u⁻¹).isUnit
  have ht : (q.totient:ℂ)≠0 := by exact_mod_cast ne_of_gt (Nat.totient_pos.mpr hq)
  simp only [primeCharacterError,mul_sub,Finset.sum_sub_distrib]
  rw [character_prefix_orthogonality x hq hc hcop]
  simp only [mul_ite,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,↓reduceIte,MulChar.one_apply huinv,one_mul]
  push_cast
  field_simp

theorem endpointClassError_le_character_sum (x : ℝ) {q c : ℕ} (hq : 0<q)
    (hc : c<q) (hcop : Nat.Coprime c q) :
    |residuePrefix ArithmeticFunction.vonMangoldt ⌊x⌋₊ q c-x/q.totient|≤
      (∑ χ : DirichletCharacter ℂ q, ‖primeCharacterError x χ‖)/(q.totient:ℝ) := by
  have hphi : (0:ℝ)<q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  apply (le_div_iff₀ hphi).mpr
  have hh := character_error_orthogonality x hq hc hcop
  calc
    _ = ‖(q.totient:ℂ)*((residuePrefix ArithmeticFunction.vonMangoldt ⌊x⌋₊ q c-x/q.totient:ℝ):ℂ)‖ := by
      rw [norm_mul,Complex.norm_natCast,Complex.norm_real,Real.norm_eq_abs,mul_comm]
    _ = ‖∑ χ : DirichletCharacter ℂ q, χ (c:ZMod q)⁻¹*primeCharacterError x χ‖ := congrArg norm hh.symm
    _ ≤ ∑ χ : DirichletCharacter ℂ q, ‖χ (c:ZMod q)⁻¹*primeCharacterError x χ‖ := norm_sum_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro χ _
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one _)

theorem vonMangoldt_noncoprime_sum_le (X : ℕ) {q : ℕ} (hq : 0<q) :
    (∑ n∈(Finset.Ioc 0 X).filter (fun n => ¬Nat.Coprime n q),
      ArithmeticFunction.vonMangoldt n)≤(Nat.log 2 X:ℝ)*Real.log q := by
  classical
  let S := (Finset.Ioc 0 X).filter (fun n => ¬Nat.Coprime n q ∧ ArithmeticFunction.vonMangoldt n≠0)
  have he : (∑ n∈(Finset.Ioc 0 X).filter (fun n => ¬Nat.Coprime n q),
      ArithmeticFunction.vonMangoldt n)=∑ n∈S,ArithmeticFunction.vonMangoldt n := by
    simp only [S,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n _
    by_cases hcop : Nat.Coprime n q <;> by_cases hn : ArithmeticFunction.vonMangoldt n=0 <;> simp [hcop,hn]
  rw [he]
  have hsub : S⊆(q^(Nat.log 2 X)).divisors := by
    intro n hn
    obtain ⟨hnI,hnq,hnv⟩ := Finset.mem_filter.mp hn
    obtain ⟨p,k,hp,_hk,hpkn⟩ := ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hnv
    have hp' : p.Prime := Nat.prime_iff.mpr hp
    have hdp : p∣q := by
      by_contra hd
      have hc := (hp'.coprime_iff_not_dvd).mpr hd
      exact hnq (hpkn ▸ hc.pow_left k)
    have hkX : k≤Nat.log 2 X := by
      apply Nat.le_log_of_pow_le (by norm_num : 1<2)
      calc
        2^k≤p^k := Nat.pow_le_pow_left hp'.two_le k
        _ = n := hpkn
        _ ≤ X := (Finset.mem_Ioc.mp hnI).2
    apply Nat.mem_divisors.mpr
    refine ⟨?_,pow_ne_zero _ (ne_of_gt hq)⟩
    rw [←hpkn]
    exact (pow_dvd_pow_of_dvd hdp k).trans (pow_dvd_pow q hkX)
  calc
    _ ≤ ∑ n∈(q^(Nat.log 2 X)).divisors,ArithmeticFunction.vonMangoldt n :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg)
    _ = Real.log ((q^(Nat.log 2 X):ℕ):ℝ) := ArithmeticFunction.vonMangoldt_sum
    _ = _ := by rw [Nat.cast_pow,Real.log_pow]

theorem primitiveCharacter_eq_one_iff {q : ℕ} (hq : 0<q) (χ : DirichletCharacter ℂ q) :
    χ.primitiveCharacter=1 ↔ χ=1 := by
  have : NeZero q := ⟨ne_of_gt hq⟩
  constructor
  · intro h
    rw [←DirichletCharacter.changeLevel_primitiveCharacter χ,h,DirichletCharacter.changeLevel_one]
  · rintro rfl
    exact DirichletCharacter.primitiveCharacter_one

theorem primeCharacterPrefix_primitive_difference (x : ℝ) {q : ℕ} (hq : 0<q)
    (χ : DirichletCharacter ℂ q) :
    ‖primeCharacterPrefix x χ-primeCharacterPrefix x χ.primitiveCharacter‖≤
      (Nat.log 2 ⌊x⌋₊:ℝ)*Real.log q := by
  have hsame (n : ℕ) (hn : Nat.Coprime n q) :
      χ.primitiveCharacter (n:ZMod χ.conductor)=χ (n:ZMod q) := by
    simpa only [Int.cast_natCast] using χ.primitiveCharacter_apply_of_isCoprime hn.isCoprime
  have hzero (n : ℕ) (hn : ¬Nat.Coprime n q) : χ (n:ZMod q)=0 :=
    χ.map_nonunit (fun h => hn ((ZMod.isUnit_iff_coprime n q).mp h))
  calc
    _ = ‖∑ n∈Finset.Ioc 0 ⌊x⌋₊,(χ (n:ZMod q)-χ.primitiveCharacter (n:ZMod χ.conductor))*
        (ArithmeticFunction.vonMangoldt n:ℂ)‖ := by
      congr 1
      simp only [primeCharacterPrefix,sub_mul,Finset.sum_sub_distrib]
    _ ≤ ∑ n∈Finset.Ioc 0 ⌊x⌋₊,‖(χ (n:ZMod q)-χ.primitiveCharacter (n:ZMod χ.conductor))*
        (ArithmeticFunction.vonMangoldt n:ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ n∈(Finset.Ioc 0 ⌊x⌋₊).filter (fun n => ¬Nat.Coprime n q),ArithmeticFunction.vonMangoldt n := by
      rw [Finset.sum_filter]
      apply Finset.sum_le_sum
      intro n _
      by_cases hn : Nat.Coprime n q
      · simp [hn,hsame n hn]
      · simp only [ite_eq_left hn,hzero n hn,zero_sub,norm_mul,norm_neg,Complex.norm_real,Real.norm_eq_abs,
          abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
        exact mul_le_of_le_one_left ArithmeticFunction.vonMangoldt_nonneg
          (χ.primitiveCharacter.norm_le_one _)
    _ ≤ _ := vonMangoldt_noncoprime_sum_le _ hq

theorem primeCharacterError_primitive_difference (x : ℝ) {q : ℕ} (hq : 0<q)
    (χ : DirichletCharacter ℂ q) :
    ‖primeCharacterError x χ-primeCharacterError x χ.primitiveCharacter‖≤
      (Nat.log 2 ⌊x⌋₊:ℝ)*Real.log q := by
  have he : primeCharacterError x χ-primeCharacterError x χ.primitiveCharacter=
      primeCharacterPrefix x χ-primeCharacterPrefix x χ.primitiveCharacter := by
    simp only [primeCharacterError,primitiveCharacter_eq_one_iff hq χ]
    ring
  rw [he]
  exact primeCharacterPrefix_primitive_difference x hq χ

theorem primeCharacterError_le_primitive (x : ℝ) {q : ℕ} (hq : 0<q)
    (χ : DirichletCharacter ℂ q) :
    ‖primeCharacterError x χ‖≤‖primeCharacterError x χ.primitiveCharacter‖+
      (Nat.log 2 ⌊x⌋₊:ℝ)*Real.log q := by
  have hn := norm_add_le (primeCharacterError x χ.primitiveCharacter)
    (primeCharacterError x χ-primeCharacterError x χ.primitiveCharacter)
  rw [add_sub_cancel] at hn
  exact hn.trans (add_le_add_right (primeCharacterError_primitive_difference x hq χ) _)

end LargePrimeGaps
end OAI

end

open Finset Filter MeasureTheory
open scoped Topology

namespace GoldbachMajorArc

noncomputable section

def primeWeight (k : ℕ) : ℝ := if k.Prime then Real.log (k : ℝ) else 0

def phase (x : ℝ) : ℂ := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

def primeSum (n : ℕ) (t : ℝ) : ℂ :=
  ∑ k ∈ range (n + 1), (primeWeight k : ℂ) * phase ((k : ℝ) * t)

def integrand (n : ℕ) (t : ℝ) : ℂ := (primeSum n t) ^ 2 * phase (-(n : ℝ) * t)

def cutoff (n : ℕ) : ℕ := (Nat.log 2 (n + 2)) ^ 2

def arcs (n : ℕ) : Set ℝ := {t | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ cutoff n ∧ a ≤ q ∧
  Nat.Coprime a q ∧ |t - (a : ℝ) / (q : ℝ)| ≤ (cutoff n : ℝ) / ((q : ℝ) * (n : ℝ))}

private theorem phase_add (x y : ℝ) : phase (x + y) = phase x * phase y := by
  unfold phase
  rw [← Complex.exp_add]
  push_cast
  congr 1
  ring

private theorem continuous_integrand (n : ℕ) : Continuous (integrand n) := by
  unfold integrand primeSum phase
  fun_prop

private theorem primeWeight_nonneg (k : ℕ) : 0 ≤ primeWeight k := by
  unfold primeWeight
  split_ifs with h
  · exact Real.log_nonneg (by exact_mod_cast h.one_le)
  · exact le_rfl

private theorem sum_primeWeight (n : ℕ) :
    ∑ k ∈ range (n + 1), primeWeight k = Chebyshev.theta n := by
  rw [Chebyshev.theta_eq_sum_primesLE_log, Nat.primesLE_eq_filter_range, sum_filter]
  rfl

/-- The geometric sum in the rational-frequency approximation, with the same endpoints as the prime sum. -/
def kernel (n : ℕ) (β : ℝ) : ℂ := ∑ k ∈ range (n + 1), phase ((k : ℝ) * β)

def unitMean (q a : ℕ) : ℂ :=
  (∑ r ∈ (range q).filter (fun r => Nat.Coprime r q), phase ((r : ℝ) * ((a : ℝ) / q))) /
    (q.totient : ℂ)

def centerErrorTerm (r : ℝ) (A : ℂ) (k : ℕ) : ℂ :=
  (primeWeight k : ℂ) * phase ((k : ℝ) * r) - A

/-- The largest initial segment discrepancy at the center, through the last term k = n. -/
def prefixError (n : ℕ) (r : ℝ) (A : ℂ) : ℝ :=
  (range (n + 2)).sup' ⟨0, by simp⟩ (fun m => ‖∑ k ∈ range m, centerErrorTerm r A k‖)

private theorem prefix_le {m n : ℕ} (hm : m ≤ n + 1) (r : ℝ) (A : ℂ) :
    ‖∑ k ∈ range m, centerErrorTerm r A k‖ ≤ prefixError n r A :=
  Finset.le_sup' (fun m => ‖∑ k ∈ range m, centerErrorTerm r A k‖) (mem_range.mpr (by omega))

private theorem norm_phase (x : ℝ) : ‖phase x‖ = 1 := Complex.norm_exp_ofReal_mul_I _

private theorem phase_step (k : ℕ) (β : ℝ) :
    ‖phase (((k + 1 : ℕ) : ℝ) * β) - phase ((k : ℝ) * β)‖ ≤ 2 * Real.pi * |β| := by
  have shift : ((k + 1 : ℕ) : ℝ) * β = k * β + β := by push_cast; ring
  rw [shift, phase_add, ← mul_sub_one, norm_mul, norm_phase, one_mul]
  unfold phase
  rw [mul_comm _ Complex.I]
  calc
    _ ≤ ‖2 * Real.pi * β‖ := Real.norm_exp_I_mul_ofReal_sub_one_le
    _ = _ := by rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * Real.pi)]

/-- Abel summation transports the finite initial segment discrepancies at r to a nearby frequency. -/
theorem shifted_sum_error (n : ℕ) (r β : ℝ) (A : ℂ) :
    ‖primeSum n (r + β) - A * kernel n β‖ ≤
      prefixError n r A * (1 + 2 * Real.pi * (n : ℝ) * |β|) := by
  let g := centerErrorTerm r A
  let v := fun k : ℕ => phase ((k : ℝ) * β)
  let D := prefixError n r A
  have hD : 0 ≤ D := (norm_nonneg _).trans (prefix_le (m := 0) (n := n) (by omega) r A)
  have expand : primeSum n (r + β) - A * kernel n β = ∑ k ∈ range (n + 1), v k * g k := by
    unfold primeSum kernel
    rw [mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun k _ => ?_
    rw [mul_add, phase_add]
    dsimp [v, g, centerErrorTerm]
    ring
  have habel := Finset.sum_range_by_parts (M := ℂ) v g (n + 1)
  simp only [Nat.add_sub_cancel, smul_eq_mul] at habel
  have hfirst : ‖v n * ∑ k ∈ range (n + 1), g k‖ ≤ D := by
    rw [norm_mul, show ‖v n‖ = 1 from norm_phase _, one_mul]
    exact prefix_le le_rfl r A
  have htail : ‖∑ i ∈ range n, (v (i + 1) - v i) * ∑ k ∈ range (i + 1), g k‖ ≤
      (n : ℝ) * (2 * Real.pi * |β| * D) := by
    calc
      _ ≤ ∑ i ∈ range n, ‖(v (i + 1) - v i) * ∑ k ∈ range (i + 1), g k‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _i ∈ range n, 2 * Real.pi * |β| * D := by
        refine sum_le_sum fun i hi => ?_
        rw [norm_mul]
        exact mul_le_mul (phase_step i β) (prefix_le (by have := mem_range.mp hi; omega) r A)
          (norm_nonneg _) (by positivity)
      _ = _ := by simp
  rw [expand, habel]
  calc
    _ ≤ _ := norm_sub_le _ _
    _ ≤ D + n * (2 * Real.pi * |β| * D) := add_le_add hfirst htail
    _ = _ := by dsimp [D]; ring

/-- On each published arc the amplification factor for the center error is at most
1 + 2πQ/q, with the declared width Q/(qn). -/
theorem rational_arc_error {n q a : ℕ} (hn : 0 < n) (hq : 0 < q) {β : ℝ}
    (hβ : |β| ≤ (cutoff n : ℝ) / ((q : ℝ) * n)) :
    ‖primeSum n ((a : ℝ) / q + β) - unitMean q a * kernel n β‖ ≤
      prefixError n ((a : ℝ) / q) (unitMean q a) * (1 + 2 * Real.pi * ((cutoff n : ℝ) / q)) := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hq' : 0 < (q : ℝ) := by exact_mod_cast hq
  have hscale : (n : ℝ) * |β| ≤ (cutoff n : ℝ) / q := by
    apply (le_div_iff₀ hq').mpr
    calc
      _ = |β| * ((q : ℝ) * n) := by ring
      _ ≤ _ := (le_div_iff₀ (mul_pos hq' hn')).mp hβ
  have hD : 0 ≤ prefixError n ((a : ℝ) / q) (unitMean q a) :=
    (norm_nonneg _).trans (prefix_le (m := 0) (n := n) (by omega) _ _)
  refine (shifted_sum_error n ((a : ℝ) / q) β (unitMean q a)).trans ?_
  apply mul_le_mul_of_nonneg_left _ hD
  apply add_le_add_right
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left hscale (by positivity)

private theorem phase_nat (k : ℕ) : phase (k : ℝ) = 1 := by
  unfold phase
  convert Complex.exp_nat_mul_two_pi_mul_I k using 2
  push_cast
  ring

private theorem phase_modulo {q : ℕ} (hq : 0 < q) (k a : ℕ) :
    phase ((k : ℝ) * ((a : ℝ) / q)) = phase (((k % q : ℕ) : ℝ) * ((a : ℝ) / q)) := by
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hk : (k : ℝ) = ((k % q : ℕ) : ℝ) + q * ((k / q : ℕ) : ℝ) := by
    exact_mod_cast (Nat.mod_add_div k q).symm
  have harg : (k : ℝ) * ((a : ℝ) / q) =
      ((k % q : ℕ) : ℝ) * ((a : ℝ) / q) + (((k / q * a : ℕ) : ℝ)) := by
    push_cast
    nth_rw 1 [hk]
    field_simp
  rw [harg, phase_add, phase_nat, mul_one]

/-- Logarithmic prime weight in one residue class for the initial segment 0 ≤ k < m. -/
def classMass (m q b : ℕ) : ℝ := ∑ k ∈ (range m).filter (fun k => k % q = b), primeWeight k

def classError (m q b : ℕ) : ℝ :=
  classMass m q b - if b.Coprime q then (m : ℝ) / q.totient else 0

/-- Exact expansion of the initial segment discrepancy at a rational center in progression errors. -/
theorem center_prefix_eq {q : ℕ} (hq : 0 < q) (a m : ℕ) :
    ∑ k ∈ range m, centerErrorTerm ((a : ℝ) / q) (unitMean q a) k =
      ∑ b ∈ range q, (classError m q b : ℂ) * phase ((b : ℝ) * ((a : ℝ) / q)) := by
  let e := fun k : ℕ => phase ((k : ℝ) * ((a : ℝ) / q))
  have masses : (∑ k ∈ range m, (primeWeight k : ℂ) * e k) =
      ∑ b ∈ range q, (classMass m q b : ℂ) * e b := by
    symm
    calc
      _ = ∑ b ∈ range q, ∑ k ∈ (range m).filter (fun k => k % q = b),
          (primeWeight k : ℂ) * e k := by
        refine sum_congr rfl fun b _ => ?_
        rw [classMass, Complex.ofReal_sum, sum_mul]
        refine sum_congr rfl fun k hk => ?_
        have he : e k = e b := by
          dsimp [e]
          rw [phase_modulo hq k a, (mem_filter.mp hk).2]
        rw [he]
      _ = _ := sum_fiberwise_of_maps_to (fun k _ => mem_range.mpr (Nat.mod_lt k hq)) _
  have model : (m : ℂ) * unitMean q a =
      ∑ b ∈ range q, (↑(if b.Coprime q then (m : ℝ) / q.totient else 0) : ℂ) * e b := by
    calc
      _ = ((m : ℂ) / q.totient) * ∑ b ∈ (range q).filter (fun b => b.Coprime q), e b := by
        unfold unitMean
        dsimp [e]
        ring
      _ = _ := by
        rw [mul_sum, sum_filter]
        refine sum_congr rfl fun b _ => ?_
        by_cases h : b.Coprime q
        · rw [ite_eq_left h, ite_eq_left h, Complex.ofReal_div, Complex.ofReal_natCast, Complex.ofReal_natCast]
        · rw [ite_eq_right h, ite_eq_right h, Complex.ofReal_zero, zero_mul]
  change (∑ k ∈ range m, ((primeWeight k : ℂ) * e k - unitMean q a)) = _
  rw [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul, masses, model, ← sum_sub_distrib]
  refine sum_congr rfl fun b _ => ?_
  rw [← sub_mul, classError, Complex.ofReal_sub]

/-- A useful bound even without a uniform prime number theorem in progressions. -/
theorem center_prefix_bound {q : ℕ} (hq : 0 < q) (a m : ℕ) :
    ‖∑ k ∈ range m, centerErrorTerm ((a : ℝ) / q) (unitMean q a) k‖ ≤
      ∑ b ∈ range q, |classError m q b| := by
  rw [center_prefix_eq hq]
  refine (norm_sum_le _ _).trans ?_
  apply sum_le_sum
  intro b _
  rw [norm_mul, norm_phase, mul_one, Complex.norm_real, Real.norm_eq_abs]

/-- The model and the actual complex integrand have the same unit twist.
This bounds their pointwise difference everywhere on each declared arc. -/
theorem squared_arc_error {n q a : ℕ} (hn : 0 < n) (hq : 0 < q) {β : ℝ}
    (hβ : |β| ≤ (cutoff n : ℝ) / ((q : ℝ) * n)) :
    let r : ℝ := (a : ℝ) / q
    let A := unitMean q a
    ‖integrand n (r + β) - (A * kernel n β) ^ 2 * phase (-(n : ℝ) * (r + β))‖ ≤
      prefixError n r A * (1 + 2 * Real.pi * ((cutoff n : ℝ) / q)) *
        (Chebyshev.theta n + ‖A‖ * (n + 1 : ℕ)) := by
  intro r A
  have hsum : ‖primeSum n (r + β)‖ ≤ Chebyshev.theta n := by
    rw [primeSum, ← sum_primeWeight]
    refine (norm_sum_le _ _).trans (sum_le_sum fun k _ => ?_)
    rw [norm_mul, norm_phase, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (primeWeight_nonneg k)]
  have hkernel : ‖kernel n β‖ ≤ (n + 1 : ℕ) := by
    unfold kernel
    refine (norm_sum_le _ _).trans ?_
    simp [norm_phase]
  have hplus : ‖primeSum n (r + β) + A * kernel n β‖ ≤ Chebyshev.theta n + ‖A‖ * (n + 1 : ℕ) := by
    refine (norm_add_le _ _).trans (add_le_add hsum ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left hkernel (norm_nonneg _)
  unfold integrand
  rw [← sub_mul, norm_mul, norm_phase, mul_one,
    show (primeSum n (r + β)) ^ 2 - (A * kernel n β) ^ 2 =
      (primeSum n (r + β) - A * kernel n β) * (primeSum n (r + β) + A * kernel n β) by ring,
    norm_mul]
  exact mul_le_mul (rational_arc_error (a := a) hn hq hβ) hplus (norm_nonneg _)
    ((norm_nonneg _).trans (rational_arc_error (a := a) hn hq hβ))

end

end GoldbachMajorArc

namespace GoldbachMajorArc

open Finset Filter MeasureTheory
open OAI.LargePrimeGaps

noncomputable section

/-- The character form of Siegel–Walfisz gives a uniform bound for a reduced class.
The second term pays for replacing the character by its primitive character. -/
theorem progression_error (A B : ℝ) (hA : 0 < A) (hB : 0 < B) :
    ∃ M : ℝ, 0 < M ∧ ∃ x₀ : ℝ, 1 < x₀ ∧
      ∀ x : ℝ, x₀ ≤ x → ∀ q b : ℕ, 0 < q → (q : ℝ) ≤ (Real.log x) ^ B →
        b < q → b.Coprime q →
        |residuePrefix ArithmeticFunction.vonMangoldt ⌊x⌋₊ q b - x / q.totient| ≤
          M * x * (Real.log x) ^ (-A) + (Nat.log 2 ⌊x⌋₊ : ℝ) * Real.log q := by
  obtain ⟨M, hM, x₀, hx₀, hχ⟩ := siegelWalfisz A B hA hB
  refine ⟨M, hM, x₀, hx₀, ?_⟩
  intro x hx q b hq hqlog hb hcop
  let : NeZero q := ⟨hq.ne'⟩
  have hchar (χ : DirichletCharacter ℂ q) :
      ‖primeCharacterError x χ‖ ≤
        M * x * (Real.log x) ^ (-A) + (Nat.log 2 ⌊x⌋₊ : ℝ) * Real.log q := by
    have hcond : (χ.conductor : ℝ) ≤ q := by
      exact_mod_cast Nat.le_of_dvd hq χ.conductor_dvd_level
    exact (primeCharacterError_le_primitive x hq χ).trans (add_le_add
      (hχ x hx χ.conductor (Nat.pos_of_ne_zero χ.conductor_ne_zero) (hcond.trans hqlog) χ.primitiveCharacter
        χ.primitiveCharacter_isPrimitive) (le_refl _))
  have hcard : Fintype.card (DirichletCharacter ℂ q) = q.totient := by
    simpa only [Nat.card_eq_fintype_card] using
      DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  apply (endpointClassError_le_character_sum x hq hb hcop).trans
  apply (div_le_iff₀ hφ).mpr
  calc
    _ ≤ ∑ _χ : DirichletCharacter ℂ q,
        (M * x * (Real.log x) ^ (-A) + (Nat.log 2 ⌊x⌋₊ : ℝ) * Real.log q) :=
      sum_le_sum fun χ _ => hchar χ
    _ = _ := by rw [sum_const, card_univ, hcard, nsmul_eq_mul, mul_comm]

private theorem primeWeight_le_mangoldt (k : ℕ) :
    primeWeight k ≤ ArithmeticFunction.vonMangoldt k := by
  by_cases hk : k.Prime
  · simp [primeWeight, hk, ArithmeticFunction.vonMangoldt_apply_prime hk]
  · simp [primeWeight, hk]

private theorem classMass_succ (N q b : ℕ) :
    classMass (N + 1) q b =
      ∑ k ∈ (Ioc 0 N).filter (fun k => k % q = b), primeWeight k := by
  rw [classMass, Nat.range_succ_eq_Icc_zero, sum_filter, sum_filter, ← add_sum_Ioc_eq_sum_Icc]
  · simp [primeWeight]
  · exact Nat.zero_le _

/-- Restriction to one class can discard no more prime-power mass than ψ(N) − θ(N). -/
theorem prime_power_correction (N q b : ℕ) :
    |classMass (N + 1) q b - residuePrefix ArithmeticFunction.vonMangoldt N q b| ≤
      Chebyshev.psi N - Chebyshev.theta N := by
  rw [classMass_succ, residuePrefix, residueSlice, abs_sub_comm, ← sum_sub_distrib,
    abs_of_nonneg (sum_nonneg fun k _ => sub_nonneg.mpr (primeWeight_le_mangoldt k))]
  have htotal : (∑ k ∈ Ioc 0 N, (ArithmeticFunction.vonMangoldt k - primeWeight k)) =
      Chebyshev.psi N - Chebyshev.theta N := by
    simp only [sum_sub_distrib, Chebyshev.psi, Chebyshev.theta, Nat.floor_natCast, sum_filter,
      primeWeight]
  rw [← htotal]
  apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
  exact fun k _ _ => sub_nonneg.mpr (primeWeight_le_mangoldt k)

/-- Siegel–Walfisz for the actual logarithmic prime weights, uniformly in reduced residue
classes. The additive terms account for nonprimitive characters and proper prime powers. -/
theorem prime_progression_error (A B : ℝ) (hA : 0 < A) (hB : 0 < B) :
    ∃ M : ℝ, 0 < M ∧ ∃ x₀ : ℝ, 1 < x₀ ∧
      ∀ N q b : ℕ, x₀ ≤ N → 0 < q → (q : ℝ) ≤ (Real.log N) ^ B →
        b < q → b.Coprime q →
        |classMass (N + 1) q b - (N : ℝ) / q.totient| ≤
          M * N * (Real.log N) ^ (-A) + (Nat.log 2 N : ℝ) * Real.log q +
            2 * Real.sqrt N * Real.log N := by
  obtain ⟨M, hM, x₀, hx₀, h⟩ := progression_error A B hA hB
  refine ⟨M, hM, x₀, hx₀, ?_⟩
  intro N q b hN hq hlog hb hcop
  have he := h (N : ℝ) hN q b hq hlog hb hcop
  simp only [Nat.floor_natCast] at he
  have hpow := (prime_power_correction N q b).trans (Chebyshev.psi_sub_theta_le (hx₀.le.trans hN))
  exact (abs_sub_le _ (residuePrefix ArithmeticFunction.vonMangoldt N q b) _).trans
    ((add_le_add hpow he).trans_eq (add_comm _ _))

private theorem classMass_nonunit (N q b : ℕ) (hq : 0 < q) (hb : ¬ b.Coprime q) :
    classMass (N + 1) q b ≤ (Nat.log 2 N : ℝ) * Real.log q := by
  rw [classMass_succ]
  have hs : (Ioc 0 N).filter (fun k => k % q = b) ⊆
      (Ioc 0 N).filter (fun k => ¬ k.Coprime q) := by
    intro k hk
    obtain ⟨hkN, hkb⟩ := mem_filter.mp hk
    refine mem_filter.mpr ⟨hkN, fun h => hb ?_⟩
    rw [← hkb, Nat.coprime_iff_gcd_eq_one, ← Nat.gcd_rec, Nat.gcd_comm]
    exact h.gcd_eq_one
  calc
    _ ≤ ∑ k ∈ (Ioc 0 N).filter (fun k => k % q = b), ArithmeticFunction.vonMangoldt k :=
      sum_le_sum fun k _ => primeWeight_le_mangoldt k
    _ ≤ ∑ k ∈ (Ioc 0 N).filter (fun k => ¬ k.Coprime q), ArithmeticFunction.vonMangoldt k :=
      sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg)
    _ ≤ _ := vonMangoldt_noncoprime_sum_le N hq

/-- A single error budget for every residue, with the initial segment length and the q-dependent
constant exactly as in the expansion of the prime exponential sum. -/
theorem all_class_error (A B : ℝ) (hA : 0 < A) (hB : 0 < B) :
    ∃ M : ℝ, 0 < M ∧ ∃ x₀ : ℝ, 1 < x₀ ∧
      ∀ N q b : ℕ, x₀ ≤ N → 0 < q → (q : ℝ) ≤ (Real.log N) ^ B → b < q →
        |classError (N + 1) q b| ≤
          M * N * (Real.log N) ^ (-A) + (Nat.log 2 N : ℝ) * Real.log q +
            2 * Real.sqrt N * Real.log N + 1 := by
  obtain ⟨M, hM, x₀, hx₀, h⟩ := prime_progression_error A B hA hB
  refine ⟨M, hM, x₀, hx₀, ?_⟩
  intro N q b hN hq hlog hb
  have hN' : (1 : ℝ) ≤ N := hx₀.le.trans hN
  have hL : 0 ≤ Real.log N := Real.log_nonneg hN'
  by_cases hcop : b.Coprime q
  · rw [classError, ite_eq_left hcop]
    have hφ : (1 : ℝ) ≤ q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
    have hlast : |(N : ℝ) / q.totient - ((N + 1 : ℕ) : ℝ) / q.totient| ≤ 1 := by
      rw [show (N : ℝ) / q.totient - ((N + 1 : ℕ) : ℝ) / q.totient = -(1 / (q.totient : ℝ)) by
        push_cast; ring, abs_neg, abs_of_nonneg (by positivity)]
      exact (div_le_one (by linarith)).mpr hφ
    exact (abs_sub_le _ ((N : ℝ) / q.totient) _).trans (add_le_add (h N q b hN hq hlog hb hcop) hlast)
  · rw [classError, ite_eq_right hcop, sub_zero, abs_of_nonneg (by
      unfold classMass
      apply sum_nonneg
      intro k _
      unfold primeWeight
      split_ifs with h
      · exact Real.log_nonneg (by exact_mod_cast h.one_le)
      · exact le_rfl)]
    have hmain : 0 ≤ M * N * (Real.log N) ^ (-A) := by positivity
    have hpower : 0 ≤ 2 * Real.sqrt N * Real.log N := by positivity
    linarith [classMass_nonunit N q b hq hcop]

end

end GoldbachMajorArc

namespace GoldbachMajorArc

open Finset Filter
open scoped Topology

noncomputable section

private theorem nat_log_two_le {u : ℕ} (hu : 1 ≤ u) :
    (Nat.log 2 u : ℝ) ≤ 2 * Real.log u := by
  have hL : 0 ≤ Real.log u := Real.log_nonneg (by exact_mod_cast hu)
  have h₂ := Real.log_two_gt_d9
  have h := Real.natLog_le_logb u 2
  simp only [Nat.cast_ofNat, Real.logb] at h
  refine h.trans ((div_le_iff₀ (by linarith : 0 < Real.log 2)).mpr ?_)
  nlinarith only [mul_nonneg hL (show 0 ≤ 2 * Real.log 2 - 1 by linarith)]

theorem cutoff_le_log_sq {n : ℕ} (hn : 2 ≤ n) :
    (cutoff n : ℝ) ≤ 16 * (Real.log n) ^ 2 := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : 0 < (n : ℝ) := by linarith
  have harg : (n : ℝ) + 2 ≤ (n : ℝ) ^ 2 := by nlinarith
  have hl := Real.log_le_log (by positivity : 0 < (n : ℝ) + 2) harg
  rw [Real.log_pow] at hl
  norm_num1 at hl
  have hnat := nat_log_two_le (u := n + 2) (by omega)
  push_cast at hnat
  have h : (Nat.log 2 (n + 2) : ℝ) ≤ 4 * Real.log n := by linarith
  have hsq := pow_le_pow_left₀ (Nat.cast_nonneg (Nat.log 2 (n + 2)) (α := ℝ)) h 2
  change (((Nat.log 2 (n + 2)) ^ 2 : ℕ) : ℝ) ≤ _
  push_cast
  nlinarith only [hsq]

private theorem class_error_trivial (u q b : ℕ) (hq : 0 < q) :
    |classError (u + 1) q b| ≤ (Real.log 4 + 1) * ((u : ℝ) + 1) := by
  have hw (k : ℕ) : 0 ≤ primeWeight k := by
    unfold primeWeight
    split_ifs with h
    · exact Real.log_nonneg (by exact_mod_cast h.one_le)
    · exact le_rfl
  have hmass : classMass (u + 1) q b ≤ Real.log 4 * u := by
    unfold classMass
    calc
      _ ≤ ∑ k ∈ range (u + 1), primeWeight k :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun k _ _ => hw k)
      _ = Chebyshev.theta u := by
        rw [Chebyshev.theta_eq_sum_primesLE_log, Nat.primesLE_eq_filter_range, sum_filter]; rfl
      _ ≤ _ := Chebyshev.theta_le_log4_mul_x (by positivity)
  have hφ : (1 : ℝ) ≤ q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  have hfrac : ((u + 1 : ℕ) : ℝ) / q.totient ≤ (u : ℝ) + 1 := by
    push_cast
    exact div_le_self (by positivity) hφ
  push_cast at hfrac
  have hm : 0 ≤ classMass (u + 1) q b := sum_nonneg (fun k _ => hw k)
  have hlog : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  unfold classError
  split_ifs
  · apply abs_le.mpr
    constructor <;> push_cast <;> nlinarith [show 0 ≤ ((u : ℝ) + 1) / q.totient by positivity,
      mul_nonneg hlog (Nat.cast_nonneg (α := ℝ) u)]
  · rw [sub_zero, abs_of_nonneg hm]
    linarith [Nat.cast_nonneg (α := ℝ) u]

/-- Upper bound for one class, uniform over every initial segment through n and every declared
denominator. The last term covers prefixes below √n. -/
def errorEnvelope (M : ℝ) (n : ℕ) : ℝ :=
  M * 2 ^ 16 * n / (Real.log n) ^ 16 + 32 * (Real.log n) ^ 3 +
    2 * Real.sqrt n * Real.log n + 1 + (Real.log 4 + 1) * (Real.sqrt n + 1)

theorem uniform_prefix_error :
    ∃ M : ℝ, 0 < M ∧ ∀ᶠ n : ℕ in atTop, ∀ q a : ℕ, 0 < q → q ≤ cutoff n →
      prefixError n ((a : ℝ) / q) (unitMean q a) ≤ q * errorEnvelope M n := by
  obtain ⟨M, hM, x₀, hx₀, hAP⟩ := all_class_error 16 4 (by norm_num) (by norm_num)
  refine ⟨M, hM, ?_⟩
  have hlim := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hroot := Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop (2 : ℕ), hlim.eventually_ge_atTop 16,
    hroot.eventually_ge_atTop x₀] with n hn hL hrootN
  change (16 : ℝ) ≤ Real.log n at hL
  change x₀ ≤ Real.sqrt n at hrootN
  intro q a hq hQ
  have hnL : 0 < Real.log n := by linarith
  have hQ' : (q : ℝ) ≤ 16 * (Real.log n) ^ 2 :=
    (show (q : ℝ) ≤ cutoff n by exact_mod_cast hQ).trans (cutoff_le_log_sq hn)
  have hconst : 0 < Real.log 4 + 1 := by positivity
  have henv : 0 ≤ errorEnvelope M n := by unfold errorEnvelope; positivity
  unfold prefixError
  apply Finset.sup'_le
  intro m hm
  refine (center_prefix_bound hq a m).trans ?_
  calc
    _ ≤ ∑ _b ∈ range q, errorEnvelope M n := by
      apply sum_le_sum
      intro b hb
      cases m with
      | zero => simpa [classError, classMass] using henv
      | succ u =>
        have hun : u ≤ n := by have := mem_range.mp hm; omega
        have hun' : (u : ℝ) ≤ n := by exact_mod_cast hun
        by_cases hs : (u : ℝ) < Real.sqrt n
        · refine (class_error_trivial u q b hq).trans ?_
          have hsmall := mul_le_mul_of_nonneg_left (add_le_add hs.le (le_refl (1 : ℝ))) hconst.le
          unfold errorEnvelope
          linarith [show 0 ≤ M * 2 ^ 16 * n / (Real.log n) ^ 16 by positivity,
            show 0 ≤ 32 * (Real.log n) ^ 3 by positivity, show 0 ≤ 2 * Real.sqrt n * Real.log n by positivity]
        · have hsu := le_of_not_gt hs
          have hux : x₀ ≤ (u : ℝ) := hrootN.trans hsu
          have hu1 : (1 : ℝ) < u := hx₀.trans_le hux
          have huL := Real.log_pos hu1
          have hhalf := Real.log_le_log (by linarith : 0 < Real.sqrt n) hsu
          rw [Real.log_sqrt (Nat.cast_nonneg n)] at hhalf
          have hupper := Real.log_le_log (by linarith : 0 < (u : ℝ)) hun'
          have hu8 : 8 ≤ Real.log u := by linarith
          have hl2 := pow_le_pow_left₀ hnL.le (show Real.log n ≤ 2 * Real.log u by linarith) 2
          have h4 : (q : ℝ) ≤ (Real.log u) ^ (4 : ℕ) := by
            nlinarith only [hQ', hl2, mul_nonneg (sq_nonneg (Real.log u))
              (show 0 ≤ (Real.log u) ^ 2 - 64 by nlinarith)]
          have hraw := hAP u q b hux hq (by simpa using h4) (mem_range.mp hb)
          have hrpow : (Real.log u) ^ (-(16 : ℝ)) = 1 / (Real.log u) ^ (16 : ℕ) := by
            rw [Real.rpow_neg huL.le]; norm_num [one_div]
          rw [hrpow, ← div_eq_mul_one_div] at hraw
          have hpow := pow_le_pow_left₀ hnL.le (show Real.log n ≤ 2 * Real.log u by linarith) 16
          rw [mul_pow] at hpow
          have hmain : M * (u : ℝ) / (Real.log u) ^ 16 ≤ M * 2 ^ 16 * n / (Real.log n) ^ 16 := by
            apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
            calc
              _ ≤ (M * n) * (2 ^ 16 * (Real.log u) ^ 16) :=
                mul_le_mul (mul_le_mul_of_nonneg_left hun' hM.le) hpow (by positivity) (by positivity)
              _ = _ := by ring
          have hNat := (nat_log_two_le (u := u) (by exact_mod_cast hu1.le)).trans
            (mul_le_mul_of_nonneg_left hupper (by norm_num : (0 : ℝ) ≤ 2))
          have hlogq : Real.log q ≤ 16 * (Real.log n) ^ 2 :=
            (Real.log_le_self (Nat.cast_nonneg q)).trans hQ'
          have hlogq0 : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
          have herr := mul_le_mul hNat hlogq hlogq0 (by positivity)
          have hsqrt := mul_le_mul (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hun') (by norm_num : (0 : ℝ) ≤ 2))
            hupper huL.le (by positivity)
          unfold errorEnvelope
          nlinarith only [hraw, hmain, herr, hsqrt,
            mul_nonneg hconst.le (show 0 ≤ Real.sqrt n + 1 by positivity)]
    _ = _ := by simp

private theorem log_power_over_power (k : ℕ) {s : ℝ} (hs : 0 < s) :
    Tendsto (fun n : ℕ => (Real.log n) ^ k / (n : ℝ) ^ s) atTop (𝓝 0) := by
  simpa only [Function.comp_def, Real.rpow_natCast] using
    ((isLittleO_log_rpow_rpow_atTop (k : ℝ) hs).tendsto_div_nhds_zero.comp
      (tendsto_natCast_atTop_atTop (R := ℝ)))

/-- The errors for a single residue class save more than ten powers of the logarithm,
even after taking the maximum over prefixes and the growing range of moduli. -/
theorem envelope_saving (M : ℝ) :
    Tendsto (fun n : ℕ => (Real.log n) ^ 10 * errorEnvelope M n / n) atTop (𝓝 0) := by
  have hlog := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hmain : Tendsto (fun n : ℕ => M * 2 ^ 16 / (Real.log n) ^ 6) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((tendsto_pow_atTop (α := ℝ) (by decide : 6 ≠ 0)).comp hlog)
  have hself (k : ℕ) : Tendsto (fun n : ℕ => (Real.log n) ^ k / (n : ℝ)) atTop (𝓝 0) := by
    simpa only [Real.rpow_one] using log_power_over_power k (show (0:ℝ) < 1 by norm_num)
  have hsqrt (k : ℕ) : Tendsto (fun n : ℕ => (Real.log n) ^ k / Real.sqrt n) atTop (𝓝 0) := by
    simpa only [Real.sqrt_eq_rpow] using log_power_over_power k (show (0:ℝ) < 1 / 2 by norm_num)
  have hsum := (((hmain.add ((hself 13).const_mul 32)).add ((hsqrt 11).const_mul 2)).add
    (hself 10)).add (((hsqrt 10).add (hself 10)).const_mul (Real.log 4 + 1))
  simp only [mul_zero, add_zero] at hsum
  apply hsum.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
  have hn' : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hL := (Real.log_pos hn').ne'
  have hv := (Real.sqrt_pos.mpr (zero_lt_one.trans hn')).ne'
  have alg (L v : ℝ) (hL : L ≠ 0) (hv : v ≠ 0) :
      M * 2 ^ 16 / L ^ 6 + 32 * (L ^ 13 / v ^ 2) + 2 * (L ^ 11 / v) + L ^ 10 / v ^ 2 +
        (Real.log 4 + 1) * (L ^ 10 / v + L ^ 10 / v ^ 2) =
      L ^ 10 * (M * 2 ^ 16 * v ^ 2 / L ^ 16 + 32 * L ^ 3 + 2 * v * L + 1 +
        (Real.log 4 + 1) * (v + 1)) / v ^ 2 := by
    field_simp
  have h := alg (Real.log n) (Real.sqrt n) hL hv
  rw [Real.sq_sqrt (Nat.cast_nonneg n)] at h
  simpa [errorEnvelope] using h

end
end GoldbachMajorArc

namespace GoldbachMajorArc

open Finset Filter MeasureTheory
open scoped ComplexConjugate

noncomputable section

private theorem conj_phase (x : ℝ) : conj (phase x) = phase (-x) := by
  unfold phase
  rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
  congr 1
  push_cast
  ring

/-- Centering the square of the geometric sum makes its phase cancel exactly. -/
theorem kernel_square_twist (n : ℕ) (β : ℝ) :
    kernel n β ^ 2 * phase (-(n : ℝ) * β) = ((‖kernel n β‖ ^ 2 : ℝ) : ℂ) := by
  have hsym : kernel n β * phase (-(n : ℝ) * β) = conj (kernel n β) := by
    unfold kernel
    rw [sum_mul, map_sum]
    calc
      _ = ∑ k ∈ range (n + 1), conj (phase (((n - k : ℕ) : ℝ) * β)) := by
        refine sum_congr rfl fun k hk => ?_
        rw [conj_phase, ← phase_add, Nat.cast_sub (Nat.lt_succ_iff.mp (mem_range.mp hk))]
        congr 1
        ring
      _ = _ := by
        simpa only [Nat.add_sub_cancel] using
          (Finset.sum_range_reflect (fun k => conj (phase ((k : ℝ) * β))) (n + 1))
  calc
    _ = kernel n β * (kernel n β * phase (-(n : ℝ) * β)) := by ring
    _ = _ := by rw [hsym, Complex.mul_conj, Complex.normSq_eq_norm_sq]

def kernelMass (n : ℕ) (b : ℝ) : ℝ := ∫ β in -b..b, ‖kernel n β‖ ^ 2

private theorem continuous_kernel (n : ℕ) : Continuous (kernel n) := by
  unfold kernel phase
  fun_prop

theorem kernelMass_mono {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (n : ℕ) :
    kernelMass n u ≤ kernelMass n v :=
  intervalIntegral.integral_mono_interval (neg_le_neg huv) (by linarith) huv
    (Eventually.of_forall fun _ => sq_nonneg _) (((continuous_kernel n).norm.pow 2).intervalIntegrable _ _)

private theorem kernel_on_zero_arc {n : ℕ} (hn : 0 < n) {t : ℝ}
    (ht : t ∈ Set.Icc 0 (1 / (6 * (n : ℝ)))) : (n : ℝ) / 2 ≤ ‖kernel n t‖ := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hnt := (le_div_iff₀ (show 0 < 6 * (n : ℝ) by positivity)).mp ht.2
  have hc (k : ℕ) (hk : k ∈ range (n + 1)) :
      1 / 2 ≤ (phase ((k : ℝ) * t)).re := by
    rw [phase, Complex.exp_ofReal_mul_I_re, ← Real.cos_pi_div_three]
    apply Real.cos_le_cos_of_nonneg_of_le_pi
    · exact mul_nonneg (by positivity) (mul_nonneg (Nat.cast_nonneg _) ht.1)
    · linarith [Real.pi_pos]
    have hk' : (k : ℝ) ≤ n := by exact_mod_cast Nat.lt_succ_iff.mp (mem_range.mp hk)
    have hkt := mul_le_mul_of_nonneg_right hk' ht.1
    nlinarith only [mul_le_mul_of_nonneg_left hnt Real.pi_pos.le,
      mul_le_mul_of_nonneg_left hkt Real.pi_pos.le]
  calc
    _ ≤ ∑ _k ∈ range (n + 1), (1 / 2 : ℝ) := by simp; linarith
    _ ≤ ∑ k ∈ range (n + 1), (phase ((k : ℝ) * t)).re := sum_le_sum hc
    _ = (kernel n t).re := by rw [kernel, Complex.re_sum]
    _ ≤ _ := Complex.re_le_norm _

/-- Each width at least 1/(6n) captures a positive linear amount of the model's mass. -/
theorem kernelMass_floor {n : ℕ} (hn : 0 < n) {b : ℝ} (hb : 1 / (6 * (n : ℝ)) ≤ b) :
    (n : ℝ) / 24 ≤ kernelMass n b := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  let u : ℝ := 1 / (6 * (n : ℝ))
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hb0 : 0 ≤ b := hu.trans hb
  have hc := (continuous_kernel n).norm.pow 2
  calc
    _ = ∫ _t in (0 : ℝ)..u, ((n : ℝ) / 2) ^ 2 := by
      rw [intervalIntegral.integral_const]
      simp only [sub_zero, smul_eq_mul, u]
      field_simp
      ring
    _ ≤ ∫ t in (0 : ℝ)..u, ‖kernel n t‖ ^ 2 :=
      intervalIntegral.integral_mono_on hu (by simp) (hc.intervalIntegrable _ _) fun _ ht =>
        pow_le_pow_left₀ (by positivity) (kernel_on_zero_arc hn ht) 2
    _ ≤ _ := intervalIntegral.integral_mono_interval (neg_nonpos.mpr hb0) hu hb
      (Eventually.of_forall fun _ => sq_nonneg _) (hc.intervalIntegrable _ _)

end
end GoldbachMajorArc

namespace GoldbachMajorArc

open Finset Filter MeasureTheory
open scoped Topology

noncomputable section

def width (n q : ℕ) : ℝ := (cutoff n : ℝ) / ((q : ℝ) * n)

def modelError (n q a : ℕ) (β : ℝ) : ℝ :=
  let r : ℝ := (a : ℝ) / q
  ‖integrand n (r + β) - (unitMean q a * kernel n β) ^ 2 * phase (-(n : ℝ) * (r + β))‖

/-- Sum of absolute errors on the uncut intervals; summing all numerators also bounds
the errors on the reduced fractions and on their portions inside [0,1]. -/
def totalArcError (n : ℕ) : ℝ :=
  ∑ q ∈ Icc 1 (cutoff n), ∑ a ∈ range (q + 1),
    ∫ β in -(width n q)..(width n q), modelError n q a β

private theorem unitMean_norm (q a : ℕ) (hq : 0 < q) : ‖unitMean q a‖ ≤ 1 := by
  let U := (range q).filter (fun r => r.Coprime q)
  have hcard : U.card = q.totient := by
    rw [Nat.totient_eq_card_coprime]
    have h : U = (range q).filter (fun r => q.Coprime r) := by ext k; simp [U, Nat.coprime_comm]
    rw [h]
  have hφ : 0 < (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
  unfold unitMean
  rw [norm_div, Complex.norm_natCast, div_le_one hφ]
  refine (norm_sum_le _ _).trans ?_
  change ∑ r ∈ U, ‖phase ((r : ℝ) * ((a : ℝ) / q))‖ ≤ _
  simp only [phase, Complex.norm_exp_ofReal_mul_I, sum_const, nsmul_eq_mul, mul_one, hcard, le_refl]

private theorem integral_error_bound {n q : ℕ} (hn : 1 ≤ n) (hq : 0 < q) (hQ : q ≤ cutoff n)
    (a : ℕ) {E : ℝ} (hE : 0 ≤ E)
    (hp : prefixError n ((a : ℝ) / q) (unitMean q a) ≤ q * E) :
    (∫ β in -(width n q)..(width n q), modelError n q a β) ≤
      2 * (cutoff n : ℝ) ^ 2 * E * ((1 + 2 * Real.pi) * (Real.log 4 + 2)) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hQ' : (q : ℝ) ≤ cutoff n := by exact_mod_cast hQ
  have npos : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn'
  have qpos : (0 : ℝ) < q := lt_of_lt_of_le zero_lt_one hq'
  let B := E * ((1 + 2 * Real.pi) * (cutoff n : ℝ)) * ((Real.log 4 + 2) * (n : ℝ))
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have wpos : 0 ≤ width n q := by unfold width; positivity
  have hlength : width n q ≤ (cutoff n : ℝ) / n := by
    unfold width
    apply div_le_div_of_nonneg_left (by positivity) npos
    simpa only [one_mul] using (mul_le_mul_of_nonneg_right hq' npos.le)
  have hpoint {β : ℝ} (hβ : β ∈ Set.Icc (-(width n q)) (width n q)) :
      modelError n q a β ≤ B := by
    have hp' := squared_arc_error (a := a) hn hq (abs_le.mpr hβ)
    have hscale :
        prefixError n ((a : ℝ) / q) (unitMean q a) * (1 + 2 * Real.pi * ((cutoff n : ℝ) / q)) ≤
        E * ((1 + 2 * Real.pi) * (cutoff n : ℝ)) := by
      calc
        _ ≤ ((q : ℝ) * E) * (1 + 2 * Real.pi * ((cutoff n : ℝ) / q)) :=
          mul_le_mul_of_nonneg_right hp (by positivity)
        _ = E * ((q : ℝ) + 2 * Real.pi * cutoff n) := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left (by nlinarith only [hQ']) hE
    have hU := unitMean_norm q a hq
    have hcap : Chebyshev.theta n + ‖unitMean q a‖ * (n + 1 : ℕ) ≤ (Real.log 4 + 2) * (n : ℝ) := by
      have hcard := mul_le_mul_of_nonneg_right hU (show 0 ≤ (n : ℝ) + 1 by positivity)
      push_cast
      nlinarith only [Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg n), hcard, hn']
    exact hp'.trans (mul_le_mul hscale hcap (by positivity) (by positivity))
  have hc : Continuous (modelError n q a) := by
    unfold modelError integrand primeSum kernel phase
    fun_prop
  calc
    _ ≤ ∫ _β in -(width n q)..(width n q), B :=
      intervalIntegral.integral_mono_on (by linarith) (hc.intervalIntegrable _ _)
        (by simp) (fun β hβ => hpoint hβ)
    _ = (2 * width n q) * B := by rw [intervalIntegral.integral_const, smul_eq_mul]; ring
    _ ≤ (2 * ((cutoff n : ℝ) / n)) * B :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlength (by norm_num)) hB
    _ = _ := by dsimp [B]; field_simp

private theorem totalArcError_nonneg (n : ℕ) : 0 ≤ totalArcError n := by
  refine sum_nonneg fun q _ => sum_nonneg fun a _ => ?_
  have hw : 0 ≤ width n q := by unfold width; positivity
  exact intervalIntegral.integral_nonneg (by linarith) fun _ _ => norm_nonneg _

/-- The aggregate integral error made by the rational models is o(n) for the exact
logarithmic cutoff, with their denominators, widths and both endpoints retained. -/
theorem totalArcError_sublinear : Tendsto (fun n : ℕ => totalArcError n / n) atTop (𝓝 0) := by
  obtain ⟨M, hM, hpre⟩ := uniform_prefix_error
  let C : ℝ := 4 * ((1 + 2 * Real.pi) * (Real.log 4 + 2))
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hlimit := (envelope_saving M).const_mul (C * 16 ^ 4)
  simp only [mul_zero] at hlimit
  apply squeeze_zero' (Eventually.of_forall fun n => div_nonneg (totalArcError_nonneg n) (Nat.cast_nonneg n)) _ hlimit
  have hl := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hpre, eventually_ge_atTop (2 : ℕ), hl.eventually_ge_atTop 1] with n hp hn hL
  change (1 : ℝ) ≤ Real.log n at hL
  have hn1 : 1 ≤ n := by omega
  have hQ1 : 1 ≤ cutoff n := Nat.one_le_iff_ne_zero.mpr
    (pow_ne_zero 2 (Nat.log_pos (by decide : 1 < 2) (by omega : 2 ≤ n + 2)).ne')
  have hQ' : (1 : ℝ) ≤ cutoff n := by exact_mod_cast hQ1
  have hE : 0 ≤ errorEnvelope M n := by unfold errorEnvelope; positivity
  let B : ℝ := 2 * (cutoff n : ℝ) ^ 2 * errorEnvelope M n * ((1 + 2 * Real.pi) * (Real.log 4 + 2))
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have htot : totalArcError n ≤ C * (cutoff n : ℝ) ^ 4 * errorEnvelope M n := by
    unfold totalArcError
    calc
      _ ≤ ∑ _q ∈ Icc 1 (cutoff n), (((cutoff n : ℝ) + 1) * B) := by
        refine sum_le_sum fun q hq => ?_
        have hq' := mem_Icc.mp hq
        calc
          _ ≤ ∑ _a ∈ range (q + 1), B := sum_le_sum fun a _ =>
            integral_error_bound hn1 hq'.1 hq'.2 a hE (hp q a hq'.1 hq'.2)
          _ = ((q : ℝ) + 1) * B := by simp
          _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.add_le_add_right hq'.2 1) hB
      _ = (cutoff n : ℝ) * (((cutoff n : ℝ) + 1) * B) := by simp [Nat.card_Icc]
      _ ≤ (cutoff n : ℝ) * ((2 * (cutoff n : ℝ)) * B) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by linarith) hB) (Nat.cast_nonneg _)
      _ = _ := by dsimp [B, C]; ring
  have hpow := pow_le_pow_left₀ (Nat.cast_nonneg (α := ℝ) (cutoff n)) (cutoff_le_log_sq hn) 4
  have hlpow : (Real.log n) ^ 8 ≤ (Real.log n) ^ 10 :=
    pow_le_pow_right₀ hL (by decide)
  have hcomp : (cutoff n : ℝ) ^ 4 ≤ 16 ^ 4 * (Real.log n) ^ 10 := by
    calc
      _ ≤ _ := hpow
      _ = 16 ^ 4 * (Real.log n) ^ 8 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hlpow (by norm_num)
  calc
    _ ≤ (C * (cutoff n : ℝ) ^ 4 * errorEnvelope M n) / n :=
      div_le_div_of_nonneg_right htot (Nat.cast_nonneg _)
    _ ≤ (C * (16 ^ 4 * (Real.log n) ^ 10) * errorEnvelope M n) / n :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcomp hC) hE) (Nat.cast_nonneg _)
    _ = _ := by ring

end
end GoldbachMajorArc

/- The finite CRT and prime-power calculations below adapt goldbach-proofs PRs #207 (XianWu18) and #203 (wzhxzkk), Apache-2.0. -/
namespace GoldbachMajorArc.RamanujanCRT
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

end GoldbachMajorArc.RamanujanCRT
namespace GoldbachMajorArc.RamanujanPower
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

end GoldbachMajorArc.RamanujanPower

namespace GoldbachMajorArc

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

theorem ram_unit (q h : ℕ) (hc : h.Coprime q) : ram q h = ram q 1 := by
  induction q using Nat.recOnPrimeCoprime with
  | zero => simp [ram]
  | prime_pow p j hp =>
    cases j with
    | zero => simp [ram_one]
    | succ k =>
      have hc' := (Nat.coprime_pow_right_iff (Nat.succ_pos k) h p).mp hc
      rw [ram_unit_power hp k h hc', ram_unit_power hp k 1 (by simp)]
  | coprime q r hq hr hqr iq ir =>
    obtain ⟨h₁,h₂⟩ := Nat.coprime_mul_iff_right.mp hc
    rw [ram_mul (by omega) (by omega) hqr, ram_mul (by omega) (by omega) hqr, iq h₁, ir h₂]

theorem unitMean_eq_ram {q a : ℕ} (h : a.Coprime q) :
    unitMean q a = ram q 1 / (q.totient : ℂ) := by
  calc
    _ = ram q a / (q.totient : ℂ) := by
      apply congrArg (fun z : ℂ => z / (q.totient : ℂ))
      apply sum_congr rfl
      intro k _
      exact congrArg phase (by ring)
    _ = _ := congrArg (fun z : ℂ => z / (q.totient : ℂ)) (ram_unit q a h)

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

theorem sum_centers_eq_coefficient (q n : ℕ) :
    (∑ a ∈ (range q).filter (fun a => a.Coprime q),
      (unitMean q a) ^ 2 * phase (-(n : ℝ) * ((a : ℝ) / q))) = coefficient q n := by
  unfold coefficient ram
  rw [map_sum, mul_sum]
  refine sum_congr rfl fun a ha => ?_
  rw [unitMean_eq_ram (mem_filter.mp ha).2]
  congr 1
  unfold phase
  rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
  congr 1
  push_cast
  ring

end
end GoldbachMajorArc

namespace GoldbachMajorArc

open Finset
noncomputable section

def badFactor (p : ℕ) : ℝ := 1 / ((p : ℝ) - 1) ^ 2

private theorem badFactor_nonneg (p : ℕ) : 0 ≤ badFactor p := by unfold badFactor; positivity

private theorem tail_telescope (m : ℕ) :
    ∏ p ∈ range (m + 5), (if 5 ≤ p then 1 + badFactor p else 1) ≤
      4 * ((m : ℝ) + 3) / (3 * ((m : ℝ) + 4)) := by
  induction m with
  | zero =>
    have h : ∏ p ∈ range (0 + 5), (if 5 ≤ p then 1 + badFactor p else 1) = 1 :=
      prod_eq_one fun p hp => ite_eq_right (Nat.not_le.mpr (mem_range.mp hp))
    norm_num [h]
  | succ m ih =>
    rw [show m.succ + 5 = (m + 5) + 1 by omega, prod_range_succ, ite_eq_left (show 5 ≤ m + 5 by omega)]
    apply (mul_le_mul_of_nonneg_right ih (by linarith [badFactor_nonneg (m + 5)])).trans
    unfold badFactor
    push_cast
    have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
    have h₁ : 0 < (m : ℝ) + 4 := by linarith
    have h₂ : 0 < (m : ℝ) + 1 + 4 := by linarith
    rw [show (m : ℝ) + 5 - 1 = m + 4 by ring]
    field_simp
    nlinarith only [hm]

private theorem product_tail_le {s : Finset ℕ} (hs : ∀ p ∈ s, 5 ≤ p) :
    ∏ p ∈ s, (1 + badFactor p) ≤ 4 / 3 := by
  let m := s.sup id
  have hsub : s ⊆ range (m + 5) := by
    intro p hp
    have h : p ≤ m := Finset.le_sup (f := id) hp
    exact mem_range.mpr (by omega)
  calc
    _ = ∏ p ∈ s, (if 5 ≤ p then 1 + badFactor p else 1) :=
      prod_congr rfl fun p hp => (ite_eq_left (hs p hp)).symm
    _ ≤ ∏ p ∈ range (m + 5), (if 5 ≤ p then 1 + badFactor p else 1) := by
      refine prod_le_prod_of_subset_of_one_le₀ hsub ?_ ?_
      · intro i _
        split_ifs <;> linarith [badFactor_nonneg i]
      · intro i _ _
        split_ifs <;> linarith [badFactor_nonneg i]
    _ ≤ _ := tail_telescope m
    _ ≤ 4 / 3 := by
      apply (div_le_div_iff₀ (by positivity) (by norm_num)).mpr
      linarith

/-- Every finite set of odd primes has absolute Euler excess at most 2/3.
Separate p = 3 and telescope the comparison product starting at p = 5. -/
theorem product_bad_factors {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime ∧ 2 < p) :
    ∏ p ∈ s, (1 + badFactor p) ≤ 5 / 3 := by
  have hrest : ∀ p ∈ s.erase 3, 5 ≤ p := by
    intro p hp
    obtain ⟨hne, hmem⟩ := mem_erase.mp hp
    obtain ⟨hprime, hpos⟩ := hs p hmem
    have hfour : p ≠ 4 := by rintro rfl; exact (by decide : ¬ Nat.Prime 4) hprime
    omega
  have hsub : s ⊆ insert 3 (s.erase 3) := by intro p hp; by_cases p = 3 <;> simp_all
  calc
    _ ≤ ∏ p ∈ insert 3 (s.erase 3), (1 + badFactor p) :=
      prod_le_prod_of_subset_of_one_le₀ hsub (fun p _ => by linarith [badFactor_nonneg p])
        (fun p _ _ => by linarith [badFactor_nonneg p])
    _ = (5 / 4) * ∏ p ∈ s.erase 3, (1 + badFactor p) := by
      rw [prod_insert (notMem_erase _ _)]
      congr 1
      norm_num [badFactor]
    _ ≤ (5 / 4) * (4 / 3) := mul_le_mul_of_nonneg_left (product_tail_le hrest) (by norm_num)
    _ = _ := by norm_num

/-- Summing the signed factors at primes away from an even target leaves at least
a third of the mass at d. The function W may already include a denominator cutoff. -/
theorem negative_factors_lower {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime ∧ 2 < p)
    (W : ℕ → ℝ) (hnonneg : ∀ k, 0 ≤ W k) (hmono : ∀ i j, 0 < i → i ≤ j → W j ≤ W i)
    {d : ℕ} (hd : 0 < d) :
    W d / 3 ≤ ∑ t ∈ s.powerset, (∏ p ∈ t, -badFactor p) * W (d * ∏ p ∈ t, p) := by
  let P := s.powerset.erase ∅
  have hempty : ∅ ∈ s.powerset := mem_powerset.mpr (empty_subset _)
  have hrest : (∑ t ∈ P, ∏ p ∈ t, badFactor p) + 1 ≤ 5 / 3 := by
    have h := prod_one_add (f := badFactor) s
    rw [← sum_erase_add _ _ hempty] at h
    simp only [prod_empty] at h
    rw [← h]
    exact product_bad_factors hs
  have hterm (t : Finset ℕ) (ht : t ∈ P) :
      -(W d * ∏ p ∈ t, badFactor p) ≤ (∏ p ∈ t, -badFactor p) * W (d * ∏ p ∈ t, p) := by
    have ht' : t ⊆ s := mem_powerset.mp (mem_erase.mp ht).2
    have hprod : 0 < ∏ p ∈ t, p := prod_pos fun p hp => (hs p (ht' hp)).1.pos
    have hle := hmono d (d * ∏ p ∈ t, p) hd (Nat.le_mul_of_pos_right d hprod)
    apply (abs_le.mp ?_).1
    rw [abs_mul, abs_of_nonneg (hnonneg _), Finset.abs_prod]
    simp_rw [abs_neg, abs_of_nonneg (badFactor_nonneg _)]
    rw [mul_comm (W d)]
    exact mul_le_mul_of_nonneg_left hle (prod_nonneg fun _ _ => badFactor_nonneg _)
  have low := sum_le_sum hterm
  simp only [sum_neg_distrib, ← mul_sum] at low
  have cap := mul_le_mul_of_nonneg_left (show (∑ t ∈ P, ∏ p ∈ t, badFactor p) ≤ 2 / 3 by linarith) (hnonneg d)
  rw [← sum_erase_add _ _ hempty]
  simp only [prod_empty, mul_one, one_mul]
  dsimp only [P] at low cap
  linarith

end
end GoldbachMajorArc

namespace GoldbachMajorArc

open Finset
noncomputable section

private theorem coefficient_not_squarefree {q : ℕ} (n : ℕ) (hq : 0 < q)
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

private theorem coefficient_prime_product (n : ℕ) (s : Finset ℕ)
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

private theorem reindex_denominators (Q n : ℕ) (W : ℕ → ℝ) (hcut : ∀ q, Q < q → W q = 0) :
    (∑ q ∈ Icc 1 Q, (coefficient q n).re * W q) =
    ∑ t ∈ ((range (Q + 1)).filter Nat.Prime).powerset, (∏ p ∈ t, localCoefficient p n) * W (∏ p ∈ t, p) := by
  classical
  let P := (range (Q + 1)).filter Nat.Prime
  have hprime {t : Finset ℕ} (ht : t ∈ P.powerset) : ∀ p ∈ t, p.Prime :=
    fun p hp => (mem_filter.mp (mem_powerset.mp ht hp)).2
  symm
  apply sum_bij_ne_zero (fun t _ _ => ∏ p ∈ t, p)
  · intro t ht hnz
    exact mem_Icc.mpr ⟨prod_pos fun p hp => (hprime ht p hp).pos, le_of_not_gt fun h => hnz (by rw [hcut _ h, mul_zero])⟩
  · intro s hs _ t ht _ he
    exact (Nat.primeFactors_prod (hprime hs)).symm.trans ((congrArg Nat.primeFactors he).trans (Nat.primeFactors_prod (hprime ht)))
  · intro q hq hnz
    have hq' := mem_Icc.mp hq
    have hsq : Squarefree q := by
      by_contra hh
      exact hnz (by rw [coefficient_not_squarefree n hq'.1 hh]; simp)
    have hprod := Nat.prod_primeFactors_of_squarefree hsq
    have hsub : q.primeFactors ∈ P.powerset := by
      apply mem_powerset.mpr
      intro p hp
      exact mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le ((Nat.le_of_mem_primeFactors hp).trans hq'.2)),
        Nat.prime_of_mem_primeFactors hp⟩
    have hc := coefficient_prime_product n q.primeFactors (hprime hsub)
    rw [hprod] at hc
    exact ⟨q.primeFactors, hsub, fun hh => hnz (by rw [hprod] at hh; simpa only [hc, Complex.ofReal_re] using hh), hprod⟩
  · intro t ht _
    rw [coefficient_prime_product n t (hprime ht), Complex.ofReal_re]

private theorem signed_powerset_floor (n : ℕ) (W : ℕ → ℝ) (hnonneg : ∀ k, 0 ≤ W k)
    (hmono : ∀ i j, 0 < i → i ≤ j → W j ≤ W i)
    (B G : Finset ℕ) (hB : ∀ p ∈ B, (p.Prime ∧ 2 < p) ∧ ¬ p ∣ n)
    (hG : ∀ p ∈ G, p.Prime ∧ p ∣ n) (d : ℕ) (hd : 0 < d) :
    W d / 3 ≤ ∑ t ∈ (G ∪ B).powerset,
      (∏ p ∈ t, localCoefficient p n) * W (d * ∏ p ∈ t, p) := by
  classical
  induction G using Finset.induction_on generalizing d with
  | empty =>
    rw [empty_union]
    apply (negative_factors_lower (fun p hp => (hB p hp).1) W hnonneg hmono hd).trans
    apply le_of_eq
    apply sum_congr rfl
    intro t ht
    congr 1
    apply prod_congr rfl
    intro p hp
    simp [localCoefficient, badFactor, (hB p (mem_powerset.mp ht hp)).2]
  | @insert p G hp ih =>
    have hp' := hG p (mem_insert_self _ _)
    have hG' : ∀ r ∈ G, r.Prime ∧ r ∣ n := fun r hr => hG _ (mem_insert_of_mem hr)
    have hpB : p ∉ B := fun h => (hB p h).2 hp'.2
    have hpGB : p ∉ G ∪ B := by simp [hp, hpB]
    have hsign : 0 ≤ localCoefficient p n := by
      have h : (1 : ℝ) < p := by exact_mod_cast hp'.1.one_lt
      simp [localCoefficient, hp'.2, le_of_lt h]
    rw [insert_union, sum_powerset_insert hpGB]
    have hsecond : 0 ≤ ∑ t ∈ (G ∪ B).powerset, (∏ r ∈ insert p t, localCoefficient r n) *
        W (d * ∏ r ∈ insert p t, r) := by
      calc
        0 ≤ localCoefficient p n * (∑ t ∈ (G ∪ B).powerset, (∏ r ∈ t, localCoefficient r n) *
            W (d * p * ∏ r ∈ t, r)) :=
          mul_nonneg hsign ((div_nonneg (hnonneg _) (by norm_num)).trans (ih hG' _ (Nat.mul_pos hd hp'.1.pos)))
        _ = _ := by
          rw [mul_sum]
          apply sum_congr rfl
          intro t ht
          have hpt : p ∉ t := fun h => hpGB (mem_powerset.mp ht h)
          rw [prod_insert hpt, prod_insert hpt, ← mul_assoc d, mul_assoc (localCoefficient p n)]
    linarith [ih hG' d hd]

/-- The even-target arithmetic main term retains at least one third of the q = 1
mass under every nonnegative decreasing weight supported on the denominator cutoff. -/
theorem arithmetic_floor {Q n : ℕ} (hn : Even n) (W : ℕ → ℝ) (hnonneg : ∀ k, 0 ≤ W k)
    (hmono : ∀ i j, 0 < i → i ≤ j → W j ≤ W i) (hcut : ∀ q, Q < q → W q = 0) :
    W 1 / 3 ≤ ∑ q ∈ Icc 1 Q, (coefficient q n).re * W q := by
  classical
  let P := (range (Q+1)).filter Nat.Prime
  let G := P.filter (fun p => p ∣ n)
  let B := P.filter (fun p => ¬ p ∣ n)
  have hGB : G ∪ B = P := by ext p; simp [G, B]; tauto
  have hB (p : ℕ) (hp : p ∈ B) : (p.Prime ∧ 2 < p) ∧ ¬ p ∣ n := by
    have hp' := (mem_filter.mp hp)
    have hpr := (mem_filter.mp hp'.1).2
    have hne : p ≠ 2 := fun e => hp'.2 (e ▸ even_iff_two_dvd.mp hn)
    exact ⟨⟨hpr, lt_of_le_of_ne hpr.two_le (Ne.symm hne)⟩, hp'.2⟩
  have hG (p : ℕ) (hp : p ∈ G) : p.Prime ∧ p ∣ n :=
    ⟨(mem_filter.mp (mem_filter.mp hp).1).2,(mem_filter.mp hp).2⟩
  have h := signed_powerset_floor n W hnonneg hmono B G hB hG 1 zero_lt_one
  rw [hGB] at h
  rw [reindex_denominators Q n W hcut]
  simpa only [one_mul] using h

end
end GoldbachMajorArc

namespace GoldbachMajorArc

open Finset Filter MeasureTheory
open scoped Topology
noncomputable section

def numerators (q : ℕ) := (range (q+1)).filter (fun a => a.Coprime q)
def center (q a : ℕ) : ℝ := (a : ℝ) / q
def window (n q a : ℕ) : Set ℝ := Set.Icc (center q a - width n q) (center q a + width n q)
def leftEnd (n q a : ℕ) : ℝ := max (center q a - width n q) 0 - center q a
def rightEnd (n q a : ℕ) : ℝ := min (center q a + width n q) 1 - center q a

theorem cutoff_positive (n : ℕ) : 1 ≤ cutoff n :=
  Nat.one_le_iff_ne_zero.mpr (pow_ne_zero 2 (Nat.log_pos (by decide : 1 < 2) (by omega : 2 ≤ n+2)).ne')

theorem cutoff_separated : ∀ᶠ n : ℕ in atTop, 2 * (cutoff n)^2 < n := by
  have h : Tendsto (fun n : ℕ => (Real.log n)^4 / (n : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.rpow_natCast, Real.rpow_ofNat, Real.rpow_one] using
      ((isLittleO_log_rpow_rpow_atTop (4 : ℝ) (by norm_num : (0:ℝ) < 1)).tendsto_div_nhds_zero.comp
        (tendsto_natCast_atTop_atTop (R := ℝ)))
  filter_upwards [eventually_ge_atTop (2 : ℕ), h.eventually_lt_const (by norm_num : (0:ℝ) < 1/512)] with n hn hl
  have hn' : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hl' := (div_lt_iff₀ hn').mp hl
  have hb := pow_le_pow_left₀ (Nat.cast_nonneg (α := ℝ) (cutoff n)) (cutoff_le_log_sq hn) 2
  have h' : 2 * (cutoff n : ℝ)^2 < n := by nlinarith only [hb, hl']
  exact_mod_cast h'

theorem width_nonneg (n q : ℕ) : 0 ≤ width n q := by unfold width; positivity

theorem mem_window (n q a : ℕ) (t : ℝ) : t ∈ window n q a ↔ |t - center q a| ≤ width n q := by
  change _ ∧ _ ↔ _
  rw [abs_le]
  constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith

/-- Separation of reduced rational arcs, using the spacing argument of wzhxzkk,
goldbach-proofs PR 153 (93d33090fdfc93fb272dde08cb463f3bff3c64ce). -/
private theorem cross_eq_of_overlap {n q r a b : ℕ} {t : ℝ} (hn : 2 * (cutoff n)^2 < n)
    (hq : q ∈ Icc 1 (cutoff n)) (hr : r ∈ Icc 1 (cutoff n))
    (ha : t ∈ window n q a) (hb : t ∈ window n r b) : a*r=b*q := by
  obtain ⟨hq₁,hqQ⟩ := mem_Icc.mp hq
  obtain ⟨hr₁,hrQ⟩ := mem_Icc.mp hr
  have hqr : 0 < (q : ℝ) := by exact_mod_cast hq₁
  have hrr : 0 < (r : ℝ) := by exact_mod_cast hr₁
  have hnr : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  let Q := cutoff n
  have hsmall : Q * r + Q * q < n := by nlinarith only [hn, Nat.mul_le_mul_left Q hrQ, Nat.mul_le_mul_left Q hqQ]
  have hradii : (Q : ℝ) / (q*n) + Q/(r*n) < 1/(q*r) := calc
    _ = ((Q : ℝ)*r+Q*q)/(q*r*n) := by field_simp
    _ < (n : ℝ)/(q*r*n) := (div_lt_div_iff_of_pos_right (by positivity)).mpr (by exact_mod_cast hsmall)
    _ = _ := by field_simp
  by_contra hne
  have hsep : 1 / ((q : ℝ)*r) ≤ |(a : ℝ)/q - b/r| := by
    rw [show (a:ℝ)/q - b/r = (a*r-b*q)/(q*r) by field_simp, abs_div, abs_of_pos (mul_pos hqr hrr)]
    apply (div_le_div_iff_of_pos_right (mul_pos hqr hrr)).mpr
    rcases lt_or_gt_of_ne hne with hab | hba
    · have hgap : (a:ℝ)*r + 1 ≤ b*q := by exact_mod_cast Nat.succ_le_of_lt hab
      linarith [neg_le_abs ((a:ℝ)*r - b*q)]
    · have hgap : (b:ℝ)*q + 1 ≤ a*r := by exact_mod_cast Nat.succ_le_of_lt hba
      linarith [le_abs_self ((a:ℝ)*r - b*q)]
  have ht := abs_sub_le ((a:ℝ)/q) t ((b:ℝ)/r)
  rw [abs_sub_comm ((a:ℝ)/q) t] at ht
  have h₁ := (mem_window n q a t).mp ha
  have h₂ := (mem_window n r b t).mp hb
  change |t-(a:ℝ)/q| ≤ (Q:ℝ)/(q*n) at h₁
  change |t-(b:ℝ)/r| ≤ (Q:ℝ)/(r*n) at h₂
  linarith

private theorem center_unique {n q r a b : ℕ} {t : ℝ} (hn : 2*(cutoff n)^2<n)
    (hq : q ∈ Icc 1 (cutoff n)) (hr : r ∈ Icc 1 (cutoff n))
    (ha : a ∈ numerators q) (hb : b ∈ numerators r)
    (hta : t ∈ window n q a) (htb : t ∈ window n r b) : q=r ∧ a=b := by
  have he := cross_eq_of_overlap hn hq hr hta htb
  have hc := (mem_filter.mp ha).2
  have hc' := (mem_filter.mp hb).2
  have hqr : q ∣ r := hc.symm.dvd_of_dvd_mul_left (he ▸ dvd_mul_left q b)
  have hrq : r ∣ q := hc'.symm.dvd_of_dvd_mul_left (he.symm ▸ dvd_mul_left r a)
  obtain rfl := Nat.dvd_antisymm hqr hrq
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_right (mem_Icc.mp hq).1 he⟩

theorem arc_indicator_sum {n : ℕ} (hn : 2*(cutoff n)^2<n) (t : ℝ) :
    (arcs n).indicator (integrand n) t =
    ∑ q ∈ Icc 1 (cutoff n), ∑ a ∈ numerators q, (window n q a).indicator (integrand n) t := by
  classical
  by_cases ht : t ∈ arcs n
  · rw [Set.indicator_of_mem ht]
    obtain ⟨q,a,hq₁,hqQ,ha,hc,habs⟩ := ht
    have hq := mem_Icc.mpr ⟨hq₁,hqQ⟩
    have ha' : a ∈ numerators q := mem_filter.mpr ⟨mem_range.mpr (by omega),hc⟩
    have hw := (mem_window n q a t).mpr habs
    symm
    calc
      _ = ∑ b ∈ numerators q, (window n q b).indicator (integrand n) t := by
        apply sum_eq_single_of_mem q hq
        intro r hr hrq
        exact sum_eq_zero fun b hb => Set.indicator_of_notMem (fun ht' => hrq (center_unique hn hr hq hb ha' ht' hw).1) _
      _ = (window n q a).indicator (integrand n) t := by
        exact sum_eq_single_of_mem a ha' fun b hb hba =>
          Set.indicator_of_notMem (fun ht' => hba (center_unique hn hq hq hb ha' ht' hw).2) _
      _ = _ := Set.indicator_of_mem hw _
  · rw [Set.indicator_of_notMem ht]
    symm
    apply sum_eq_zero
    intro q hq
    apply sum_eq_zero
    intro a ha
    exact Set.indicator_of_notMem (fun hw => ht ⟨q,a,(mem_Icc.mp hq).1,(mem_Icc.mp hq).2,
      Nat.le_of_lt_succ (mem_range.mp (mem_filter.mp ha).1),(mem_filter.mp ha).2,(mem_window n q a t).mp hw⟩) _

theorem center_in_unit {q a : ℕ} (hq : 0<q) (ha : a≤q) :
    0 ≤ center q a ∧ center q a ≤ 1 := by
  have hq' : (0:ℝ)<q := by exact_mod_cast hq
  exact ⟨by unfold center; positivity, (div_le_one hq').mpr (by exact_mod_cast ha)⟩

theorem clipped_order {n q a : ℕ} (hq : 0<q) (ha : a≤q) :
    -width n q ≤ leftEnd n q a ∧ leftEnd n q a ≤ rightEnd n q a ∧ rightEnd n q a ≤ width n q := by
  obtain ⟨h₁,h₂⟩ := center_in_unit hq ha
  have hw := width_nonneg n q
  unfold leftEnd rightEnd
  constructor
  · linarith [le_max_left (center q a-width n q) 0]
  constructor
  · apply sub_le_sub_right
    exact max_le (le_min (by linarith) (by linarith)) (le_min (by linarith) zero_le_one)
  · linarith [min_le_left (center q a+width n q) 1]

theorem indicator_clipped {n q a : ℕ} (hq : 0<q) (ha : a≤q) (F : ℝ→ℂ) :
    (∫ t in (0:ℝ)..1, (window n q a).indicator F t) =
    ∫ β in leftEnd n q a..rightEnd n q a, F (center q a+β) := by
  rw [intervalIntegral.integral_comp_add_left]
  have h := (clipped_order (n := n) hq ha).2.1
  unfold leftEnd rightEnd at h ⊢
  simp only [add_sub_cancel]
  rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc,
    window, integral_indicator measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc,
    Set.Icc_inter_Icc, intervalIntegral.integral_of_le (by linarith : max (center q a-width n q) 0 ≤ min (center q a+width n q) 1),
    ← integral_Icc_eq_integral_Ioc]

def majorContribution (n : ℕ) : ℂ := ∫ t in (0:ℝ)..1, (arcs n).indicator (integrand n) t
def actualPiece (n q a : ℕ) : ℂ := ∫ β in leftEnd n q a..rightEnd n q a, integrand n (center q a+β)

theorem major_split {n : ℕ} (hn : 2*(cutoff n)^2<n) : majorContribution n =
    ∑ q ∈ Icc 1 (cutoff n), ∑ a ∈ numerators q, actualPiece n q a := by
  have hcont := continuous_integrand n
  have hInt (q a : ℕ) : IntervalIntegrable ((window n q a).indicator (integrand n)) volume 0 1 :=
    ⟨(hcont.intervalIntegrable 0 1).1.indicator measurableSet_Icc,
      (hcont.intervalIntegrable 0 1).2.indicator measurableSet_Icc⟩
  unfold majorContribution
  simp_rw [arc_indicator_sum hn]
  rw [intervalIntegral.integral_finsetSum]
  · apply sum_congr rfl
    intro q hq
    rw [intervalIntegral.integral_finsetSum (fun a _ => hInt q a)]
    exact sum_congr rfl fun a ha => indicator_clipped (mem_Icc.mp hq).1
      (Nat.le_of_lt_succ (mem_range.mp (mem_filter.mp ha).1)) _
  · intro q _
    exact ⟨integrable_finsetSum _ (fun a _ => (hInt q a).1),
      integrable_finsetSum _ (fun a _ => (hInt q a).2)⟩

end
end GoldbachMajorArc

namespace GoldbachMajorArc

open Finset Filter MeasureTheory
noncomputable section

def modelPoint (n q a : ℕ) (β : ℝ) : ℂ :=
  (unitMean q a * kernel n β)^2 * phase (-(n:ℝ) * (center q a + β))

def modelPiece (n q a : ℕ) : ℂ :=
  (unitMean q a ^ 2 * phase (-(n:ℝ)*center q a)) *
    ((∫ β in leftEnd n q a..rightEnd n q a, ‖kernel n β‖^2 : ℝ) : ℂ)

theorem model_piece_eq (n q a : ℕ) :
    (∫ β in leftEnd n q a..rightEnd n q a, modelPoint n q a β) = modelPiece n q a := by
  have h (β : ℝ) : modelPoint n q a β =
      (unitMean q a ^2 * phase (-(n:ℝ)*center q a)) * ((‖kernel n β‖^2 : ℝ) : ℂ) := by
    rw [modelPoint, ← kernel_square_twist, mul_add, phase_add]
    ring
  simp_rw [h]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal]
  rfl

private theorem error_cont (n q a : ℕ) :
    Continuous (fun β => integrand n (center q a+β) - modelPoint n q a β) := by
  unfold integrand modelPoint primeSum kernel phase
  fun_prop

theorem piece_error_le {n q a : ℕ} (hq : 0<q) (ha : a≤q) :
    ‖actualPiece n q a - modelPiece n q a‖ ≤ ∫ β in -(width n q)..width n q, modelError n q a β := by
  have hi : Continuous (fun β => integrand n (center q a+β)) := by unfold integrand primeSum phase; fun_prop
  have hm : Continuous (modelPoint n q a) := by unfold modelPoint kernel phase; fun_prop
  have ⟨hl,hord,hr⟩ := clipped_order (n := n) hq ha
  rw [actualPiece, ← model_piece_eq, ← intervalIntegral.integral_sub (hi.intervalIntegrable _ _) (hm.intervalIntegrable _ _)]
  apply (intervalIntegral.norm_integral_le_integral_norm hord).trans
  exact intervalIntegral.integral_mono_interval hl hord hr (Eventually.of_forall fun _ => norm_nonneg _)
    ((error_cont n q a).norm.intervalIntegrable _ _)

theorem width_le_unit {n q : ℕ} (hn : 2*(cutoff n)^2<n) (hq : 0<q) :
    width n q ≤ 1/(q:ℝ) := by
  have hn' : (0:ℝ)<n := by exact_mod_cast (by omega : 0<n)
  have hq' : (0:ℝ)<q := by exact_mod_cast hq
  have hQn : cutoff n ≤ n := by nlinarith [cutoff_positive n]
  calc
    width n q = ((cutoff n:ℝ)/n)/q := by unfold width; ring
    _ ≤ _ := div_le_div_of_nonneg_right ((div_le_one hn').mpr (by exact_mod_cast hQn)) hq'.le

private theorem interior_order {q a : ℕ} (hq : 1<q) (ha : a ∈ numerators q) : 0<a ∧ a<q := by
  obtain ⟨h,hc⟩ := mem_filter.mp ha
  have hle : a≤q := Nat.le_of_lt_succ (mem_range.mp h)
  have ha0 : a ≠ 0 := by rintro rfl; simp [Nat.Coprime] at hc; omega
  have hne : a ≠ q := by rintro rfl; simp [Nat.Coprime] at hc; omega
  omega

private theorem uncut {n q a : ℕ} (hn : 2*(cutoff n)^2<n) (hq : 1<q) (ha : a∈numerators q) :
    leftEnd n q a = -(width n q) ∧ rightEnd n q a = width n q := by
  obtain ⟨ha₁,haq⟩ := interior_order hq ha
  have hq' : (0:ℝ)<q := by exact_mod_cast (by omega : 0<q)
  have hw := width_le_unit hn (by omega : 0<q)
  have hc₁ : 1/(q:ℝ) ≤ center q a :=
    div_le_div_of_nonneg_right (by exact_mod_cast ha₁) hq'.le
  have hc₂ : center q a + 1/q ≤ 1 := by
    rw [center, ← add_div, div_le_one hq']
    exact_mod_cast (Nat.succ_le_of_lt haq)
  unfold leftEnd rightEnd
  rw [max_eq_left (by linarith), min_eq_left (by linarith)]
  constructor <;> ring

private theorem denom_one_phase (n : ℕ) : phase (-(n:ℝ)) = 1 := by
  unfold phase
  convert Complex.exp_int_mul_two_pi_mul_I (-(n:ℤ)) using 2
  push_cast
  ring

/-- The two boundary half intervals together give the full kernel mass for q = 1. -/
private theorem endpoint_models {n : ℕ} (hn : 2*(cutoff n)^2<n) :
    (∑ a ∈ numerators 1, modelPiece n 1 a) = (kernelMass n (width n 1) : ℂ) := by
  let w := width n 1
  have hw : 0≤w := width_nonneg _ _
  have hw1 : w≤1 := by simpa [w] using width_le_unit hn (by decide : 0<1)
  have h0 : leftEnd n 1 0 = 0 ∧ rightEnd n 1 0 = w := by
    change max (0/(1:ℝ)-w) 0 - 0/1 = 0 ∧ min (0/1+w) 1 - 0/1 = w
    simp [hw,hw1]
  have h1 : leftEnd n 1 1 = -w ∧ rightEnd n 1 1 = 0 := by
    change max (1/(1:ℝ)-w) 0 - 1/1 = -w ∧ min (1/1+w) 1 - 1/1 = 0
    rw [one_div_one, max_eq_left (by linarith), min_eq_right (by linarith)]
    constructor <;> ring
  have hu (a : ℕ) : unitMean 1 a=1 := by rw [unitMean_eq_ram (by simp), ram_one]; simp
  have hker : Continuous (fun β => ‖kernel n β‖^2) := (continuous_kernel n).norm.pow 2
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (hker.intervalIntegrable (μ := volume) (-w) 0) (hker.intervalIntegrable 0 w)
  have hnSet : numerators 1 = {0,1} := by decide
  rw [hnSet]
  simp only [sum_insert (by decide : (0:ℕ) ∉ {1}),sum_singleton,modelPiece,h0.1,h0.2,h1.1,h1.2,hu,
    center, Nat.cast_zero,Nat.cast_one,div_one,mul_zero,mul_one,one_pow,one_mul,denom_one_phase]
  have hz : phase 0=1 := by simp [phase]
  rw [hz,one_mul,add_comm,← Complex.ofReal_add,hadd]
  rfl

theorem model_by_denominator {n q : ℕ} (hn : 2*(cutoff n)^2<n) (hq : 0<q) :
    (∑ a ∈ numerators q, modelPiece n q a) = coefficient q n * (kernelMass n (width n q):ℂ) := by
  rcases eq_or_lt_of_le (show 1 ≤ q by omega) with h | h
  · subst q
    rw [coefficient_one,one_mul]
    exact endpoint_models hn
  · have hs : numerators q = (range q).filter (fun a => a.Coprime q) := by
      ext a
      constructor
      · intro ha
        exact mem_filter.mpr ⟨mem_range.mpr (interior_order h ha).2, (mem_filter.mp ha).2⟩
      · intro ha
        exact mem_filter.mpr ⟨mem_range.mpr (by have := mem_range.mp (mem_filter.mp ha).1; omega),(mem_filter.mp ha).2⟩
    rw [← sum_centers_eq_coefficient, ← hs, sum_mul]
    apply sum_congr rfl
    intro a ha
    obtain ⟨hl,hr⟩ := uncut hn h ha
    simp only [modelPiece,hl,hr,kernelMass,center]

end
end GoldbachMajorArc

namespace GoldbachMajorArc

open Finset Filter MeasureTheory
open scoped Topology
noncomputable section

def modeledContribution (n : ℕ) : ℂ :=
  ∑ q ∈ Icc 1 (cutoff n), coefficient q n * (kernelMass n (width n q) : ℂ)

/-- The original indicator integral differs from the finite arithmetic model by at most
the sum of the absolute errors on all the full rational arcs. -/
theorem major_error {n : ℕ} (hn : 2*(cutoff n)^2<n) :
    ‖majorContribution n - modeledContribution n‖ ≤ totalArcError n := by
  have hmodels : modeledContribution n =
      ∑ q ∈ Icc 1 (cutoff n), ∑ a ∈ numerators q, modelPiece n q a :=
    sum_congr rfl fun q hq => (model_by_denominator hn (mem_Icc.mp hq).1).symm
  rw [major_split hn, hmodels, ← sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  unfold totalArcError
  apply sum_le_sum
  intro q hq
  rw [← sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ a ∈ numerators q, ∫ β in -(width n q)..width n q, modelError n q a β :=
      sum_le_sum fun a ha => piece_error_le (mem_Icc.mp hq).1 (Nat.le_of_lt_succ (mem_range.mp (mem_filter.mp ha).1))
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun a _ _ =>
      intervalIntegral.integral_nonneg (by linarith [width_nonneg n q]) fun _ _ => norm_nonneg _

private def truncatedMass (n q : ℕ) : ℝ :=
  if q ≤ cutoff n then kernelMass n (width n q) else 0

private theorem truncated_nonneg (n q : ℕ) : 0 ≤ truncatedMass n q := by
  unfold truncatedMass
  split_ifs
  · exact intervalIntegral.integral_nonneg (by linarith [width_nonneg n q]) fun _ _ => sq_nonneg _
  · exact le_rfl

private theorem truncated_mono {n : ℕ} (hn : 0 < n) (i j : ℕ) (hi : 0 < i) (hij : i ≤ j) :
    truncatedMass n j ≤ truncatedMass n i := by
  by_cases hj : j≤cutoff n
  · simp only [truncatedMass, ite_eq_left hj, ite_eq_left (hij.trans hj)]
    apply kernelMass_mono (width_nonneg _ _)
    have hnr : (0:ℝ) < n := by exact_mod_cast hn
    have hir : (0:ℝ) < i := by exact_mod_cast hi
    unfold width
    exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) (mul_pos hir hnr)
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hij) hnr.le)
  · rw [truncatedMass, ite_eq_right hj]
    exact truncated_nonneg n i

theorem model_linear_floor {n : ℕ} (hn : 0 < n) (heven : Even n) :
    (n : ℝ)/72 ≤ (modeledContribution n).re := by
  have har := arithmetic_floor (Q := cutoff n) heven (truncatedMass n) (truncated_nonneg n)
    (truncated_mono hn) (fun q hq => by simp [truncatedMass, not_le.mpr hq])
  have hr : (modeledContribution n).re = ∑ q ∈ Icc 1 (cutoff n), (coefficient q n).re * truncatedMass n q := by
    rw [modeledContribution, Complex.re_sum]
    refine sum_congr rfl fun q hq => ?_
    simp [truncatedMass, (mem_Icc.mp hq).2, Complex.mul_re]
  have hQ : (1:ℝ) ≤ cutoff n := by exact_mod_cast cutoff_positive n
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hwidth : 1/(6*(n:ℝ)) ≤ width n 1 := by
    rw [width, Nat.cast_one, one_mul]
    apply (div_le_div_iff₀ (by positivity) hn').mpr
    nlinarith only [hn', mul_nonneg (sub_nonneg.mpr hQ) hn'.le]
  have hmass := kernelMass_floor hn hwidth
  rw [truncatedMass, ite_eq_left (cutoff_positive n)] at har
  rw [hr]
  linarith

/-- A quantitative constant for the registry statement. -/
theorem major_linear_floor :
    ∃ (c : ℝ) (N : ℕ), 0<c ∧ ∀ n : ℕ, N≤n → Even n → c*(n:ℝ) ≤ (majorContribution n).re := by
  have hsmall := totalArcError_sublinear.eventually_lt_const (by norm_num : (0:ℝ) < 1/144)
  obtain ⟨N,hN⟩ := eventually_atTop.mp (cutoff_separated.and hsmall)
  refine ⟨1/144,N,by norm_num,?_⟩
  intro n hn he
  obtain ⟨hsep,herr⟩ := hN n hn
  have hpos : 0 < n := by omega
  have hpos' : (0:ℝ) < n := by exact_mod_cast hpos
  have he' := (div_lt_iff₀ hpos').mp herr
  have hp := model_linear_floor hpos he
  have hd := Complex.re_le_norm (modeledContribution n - majorContribution n)
  rw [Complex.sub_re, norm_sub_rev] at hd
  linarith [major_error hsep]

end
end GoldbachMajorArc


open MeasureTheory intervalIntegral
open scoped Interval

private noncomputable def phase (x : ℝ) : ℂ := Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I)
private noncomputable def polysum (n : ℕ) (x : ℝ) : ℂ := ∑ k ∈ Finset.Icc 1 n, phase (k*x)
private noncomputable def target (t : ℝ) := phase (t/2)*(Real.sinc (Real.pi*t):ℂ)

private theorem phaseNorm (x : ℝ) : ‖phase x‖=1 := Complex.norm_exp_ofReal_mul_I _
private theorem phaseAdd (x y : ℝ) : phase (x+y)=phase x*phase y := by
  simp only [phase, mul_add, Complex.ofReal_add,add_mul,Complex.exp_add]
private theorem phaseLip (x y : ℝ) : ‖phase x-phase y‖ ≤ 2*Real.pi*|x-y| := by
  have h : phase x-phase y = (phase (x-y)-1)*phase y := by
    rw [sub_mul, ← phaseAdd, sub_add_cancel,one_mul]
  rw [h,norm_mul,phaseNorm,mul_one]
  unfold phase
  rw [mul_comm _ Complex.I, Complex.norm_exp_I_mul_ofReal_sub_one,Real.norm_eq_abs,abs_mul]
  rw [show 2*Real.pi*(x-y)/2=Real.pi*(x-y) by ring]
  have hb : |Real.sin (Real.pi*(x-y))| ≤ |Real.pi*(x-y)| := Real.abs_sin_le_abs
  rw [abs_mul,abs_of_pos Real.pi_pos] at hb
  norm_num
  linarith

private theorem continuousPhase : Continuous phase := by unfold phase; fun_prop
private theorem continuousPoly (n : ℕ) : Continuous (polysum n) := by unfold polysum phase; fun_prop
private theorem continuousTarget : Continuous target := by unfold target phase; fun_prop
private theorem targetNorm (t : ℝ) : ‖target t‖ ≤ 1 := by
  simpa [target,norm_mul,phaseNorm,Complex.norm_real,Real.norm_eq_abs] using Real.abs_sinc_le_one (Real.pi*t)

private theorem kernelInt (t : ℝ) : (∫ x in (0:ℝ)..1, phase (x*t)) = target t := by
  by_cases ht : t=0
  · subst t; simp [phase,target]
  let a := Real.pi*t
  have ha : a ≠ 0 := mul_ne_zero Real.pi_ne_zero ht
  let w := fun z : ℝ => Complex.exp ((z:ℂ)*Complex.I)
  have fac (x : ℝ) : phase (x*t) = phase (t/2)*w ((2*a)*x-a) := by
    simp only [phase,w,← Complex.exp_add]
    congr 1
    dsimp [a]; push_cast; ring
  simp_rw [fac]
  rw [intervalIntegral.integral_const_mul]
  have h := intervalIntegral.integral_comp_mul_add (a:=(0:ℝ)) (b:=1) w
    (show 2*a ≠ 0 by positivity) (-a)
  simp only [mul_zero,zero_add,mul_one,show 2*a + -a = a by ring] at h
  change _ * (∫ x in (0:ℝ)..1, w (2*a*x + -a)) = _
  rw [h]
  change phase (t/2)* ((2*a)⁻¹ • (∫ z in -a..a, Complex.exp ((z:ℂ)*Complex.I))) = _
  rw [integral_exp_mul_I_eq_sinc,Complex.real_smul]
  change phase (t/2) * _ = phase (t/2) * (Real.sinc a : ℂ)
  congr 1
  push_cast
  field_simp [show (a:ℂ)≠0 by exact_mod_cast ha]

private theorem rangePoly (n : ℕ) (y : ℝ) :
    polysum n y = ∑ k ∈ Finset.range n, phase (((k:ℝ)+1)*y) := by
  unfold polysum
  rw [← Finset.Ico_succ_right_eq_Icc,Finset.sum_Ico_eq_sum_range]
  simp [Nat.add_comm]

private theorem cell (u : ℝ) (j : ℕ) :
    ‖phase (((j:ℝ)+1)*u) - ∫ x in (j:ℝ)..((j:ℝ)+1), phase (x*u)‖ ≤ Real.pi*|u| := by
  let b : ℝ := j+1
  let a : ℝ := j
  let g := fun x : ℝ => phase (x*u)
  have hab : a≤b := by dsimp [a,b]; linarith
  have hg : Continuous g := continuousPhase.comp (continuous_id.mul continuous_const)
  have he : (∫ _x in a..b, g b) = g b := by simp [intervalIntegral.integral_const,a,b]
  change ‖g b - ∫ x in a..b, g x‖ ≤ _
  rw [← he, ← intervalIntegral.integral_sub (continuous_const.intervalIntegrable _ _) (hg.intervalIntegrable _ _)]
  let C := 2*Real.pi*|u|
  calc
    _ ≤ ∫ x in a..b, C*(b-x) := by
      apply intervalIntegral.norm_integral_le_of_norm_le hab (Filter.Eventually.of_forall ?_)
        ((show Continuous (fun x : ℝ => C*(b-x)) by fun_prop).intervalIntegrable _ _)
      intro x hx
      calc ‖g b-g x‖ ≤ 2*Real.pi*|b*u-x*u| := phaseLip _ _
           _ = _ := by rw [← sub_mul,abs_mul,abs_of_nonneg (sub_nonneg.mpr hx.2)]; ring
    _ = _ := by
      rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_sub (f:=fun _ : ℝ => b) (g:=fun x : ℝ => x) (continuous_const.intervalIntegrable _ _) (continuous_id.intervalIntegrable _ _),
        integral_id,intervalIntegral.integral_const]
      dsimp [a,b,C]; ring

private theorem approx (n : ℕ) (hn : 0<n) (t : ℝ) :
    ‖polysum n (t/n)/(n:ℂ) - target t‖ ≤ Real.pi*|t|/n := by
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  have hnC : (n:ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  let u := t/n
  let g := fun x : ℝ => phase (x*u)
  have hg : Continuous g := continuousPhase.comp (continuous_id.mul continuous_const)
  have tel := intervalIntegral.sum_integral_adjacent_intervals (a:=fun k : ℕ => (k:ℝ)) (n:=n)
    (fun k _ => hg.intervalIntegrable (μ:=volume) (a:=(k:ℝ)) (b:=((k+1:ℕ):ℝ)))
  have integ : (∫ x in (0:ℝ)..n, g x) = (n:ℂ)*target t := by
    have sm := intervalIntegral.integral_comp_div (a:=(0:ℝ)) (b:=(n:ℝ)) (fun x : ℝ => phase (x*t)) hnR.ne'
    simp only [zero_div,div_self hnR.ne',kernelInt,Complex.real_smul,Complex.ofReal_natCast] at sm
    convert sm using 1
    apply intervalIntegral.integral_congr; intro x _
    unfold g u; congr 1; ring
  have C : ‖polysum n u - (n:ℂ)*target t‖ ≤ (n:ℝ)*(Real.pi*|u|) := by
    rw [rangePoly,← integ]
    simp only [Nat.cast_zero,Nat.cast_add,Nat.cast_one] at tel
    rw [← tel, ← Finset.sum_sub_distrib]
    exact (norm_sum_le _ _).trans ((Finset.sum_le_sum (fun k _ => cell u k)).trans_eq (by simp))
  change ‖polysum n u/(n:ℂ)-target t‖ ≤ _
  rw [show polysum n u/(n:ℂ)-target t=(polysum n u-(n:ℂ)*target t)/(n:ℂ) by field_simp, norm_div,Complex.norm_natCast]
  rw [div_le_div_iff_of_pos_right hnR]
  apply C.trans_eq
  dsimp [u]; rw [abs_div,abs_of_pos hnR]; field_simp

private theorem avgNorm (n : ℕ) (hn : 0<n) (t : ℝ) : ‖polysum n (t/n)/(n:ℂ)‖ ≤ 1 := by
  rw [norm_div,Complex.norm_natCast, div_le_one (by exact_mod_cast hn)]
  unfold polysum
  exact (norm_sum_le _ _).trans (by simp [phaseNorm,Nat.card_Icc])

private theorem targetSq (t : ℝ) : (target t)^2 * phase (-t) = ((Real.sinc (Real.pi*t))^2 : ℝ) := by
  have h : phase (t/2)*phase (t/2)*phase (-t)=1 := by
    rw [← phaseAdd, ← phaseAdd,show t/2+t/2 + -t = 0 by ring]
    simp [phase]
  dsimp [target]; push_cast
  linear_combination (Real.sinc (Real.pi*t):ℂ)^2*h

private theorem scaled {𝕜 : Type*} [RCLike 𝕜] (v : ℝ → 𝕜) (d h : ℝ) (hd : d≠0) :
    (∫ x in -h..h, v (x/d)/(d:𝕜)^2) = (∫ x in -(h/d)..h/d, v x)/(d:𝕜) := by
  rw [intervalIntegral.integral_div,intervalIntegral.integral_comp_div v hd, neg_div, RCLike.real_smul_eq_coe_mul]
  have hn : (d:𝕜)≠0 := by exact_mod_cast hd
  field_simp

private theorem intBound {𝕜 : Type*} [RCLike 𝕜] {a b : ℝ → 𝕜} (ha : Continuous a) (hb : Continuous b)
    (h C : ℝ) (hh : 0 ≤ h) (hC : 0 ≤ C)
    (hab : ∀ x, ‖a x-b x‖ ≤ C*|x|) :
    ‖(∫ x in -h..h, a x)-(∫ x in -h..h, b x)‖ ≤ 2*C*h^2 := by
  rw [← intervalIntegral.integral_sub (ha.intervalIntegrable _ _) (hb.intervalIntegrable _ _)]
  have step := intervalIntegral.norm_integral_le_of_norm_le_const (a := -h) (b := h) (C := C*h)
    (f := fun x => a x-b x) (fun x hx => (hab x).trans (mul_le_mul_of_nonneg_left (by
      rw [Set.uIoc_of_le (by linarith : -h≤h)] at hx
      exact abs_le.mpr ⟨hx.1.le,hx.2⟩) hC))
  exact step.trans_eq (by rw [abs_of_nonneg (by linarith : 0 ≤ h- -h)]; ring)

theorem kernel_rescale : let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let _J := fun (h : ℝ) (f : ℝ → ℂ) => intervalIntegral f (-h) h MeasureTheory.volume; let Jr := fun (h : ℝ) (f : ℝ → ℝ) => intervalIntegral f (-h) h MeasureTheory.volume; let V := fun (n : ℕ) (β : ℝ) => ∑ k ∈ Finset.Icc 1 n, E ((k:ℝ)*β); ∀ (n : ℕ) (h : ℝ), 0<n → 0≤h → (let f := fun t : ℝ => V n (t/n)/(n:ℂ); (∀ t : ℝ, ‖f t - E (t/2)*(Real.sinc (Real.pi*t):ℂ)‖ ≤ 2*Real.pi*|t|/(n:ℝ)) ∧ |((_J (h/n) (fun β => (V n β)^2*E (-(n:ℝ)*β))).re/(n:ℝ)) - Jr h (fun t => Real.sinc (Real.pi*t)^2)| ≤ 4*Real.pi*h^2/(n:ℝ) ∧ |Jr (h/n) (fun β => ‖V n β‖^2)/(n:ℝ) - Jr h (fun t => Real.sinc (Real.pi*t)^2)| ≤ 4*Real.pi*h^2/(n:ℝ)) := by
  dsimp only
  intro n h hn hh
  have hr : 0 < (n:ℝ) := by exact_mod_cast hn
  let F := fun t : ℝ => polysum n (t/n)/(n:ℂ)
  let sqF := fun t : ℝ => (F t)^2*phase (-t)
  let sqG := fun t : ℝ => (((Real.sinc (Real.pi*t))^2:ℝ):ℂ)
  let M := fun t : ℝ => ‖F t‖^2
  let J := fun t : ℝ => (Real.sinc (Real.pi*t))^2
  have cF : Continuous F := (continuousPoly n |>.comp (continuous_id.div_const _)).div_const _
  have cSq : Continuous sqF := (cF.pow 2).mul (continuousPhase.comp continuous_neg)
  have cJ : Continuous J := by dsimp [J]; fun_prop
  have cG : Continuous sqG := Complex.continuous_ofReal.comp cJ
  have cM : Continuous M := cF.norm.pow 2
  have hp t : ‖F t - target t‖ ≤ Real.pi*|t|/n := approx n hn t
  have hF t : ‖F t‖ ≤ 1 := avgNorm n hn t
  have c : 0 ≤ 2*Real.pi/(n:ℝ) := by positivity
  have pointC t : ‖sqF t-sqG t‖ ≤ 2*Real.pi/n*|t| := by
    change ‖F t^2 * phase (-t) - ((J t : ℝ):ℂ)‖ ≤ _
    rw [show ((J t : ℝ):ℂ) = target t^2*phase (-t) from (targetSq _).symm,
        ← sub_mul,norm_mul,phaseNorm,mul_one, sq_sub_sq,norm_mul]
    have hs : ‖F t + target t‖ ≤ 2 := (norm_add_le _ _).trans (by linarith [hF t,targetNorm t])
    calc _ ≤ 2*(Real.pi*|t|/n) := by nlinarith [mul_le_mul hs (hp t) (norm_nonneg (F t-target t)) (by norm_num : (0:ℝ)≤2)]
         _ = _ := by ring
  have pointR t : ‖M t-J t‖ ≤ 2*Real.pi/n*|t| := by
    have ht : ‖target t‖^2 = J t := by simp [target,J,norm_mul,phaseNorm,Complex.norm_real, Real.norm_eq_abs,sq_abs]
    change ‖‖F t‖^2-J t‖ ≤ _
    rw [← ht,sq_sub_sq,Real.norm_eq_abs,abs_mul,abs_of_nonneg (by positivity : 0≤‖F t‖+‖target t‖)]
    have hd := (abs_norm_sub_norm_le (F t) (target t)).trans (hp t)
    have hs : ‖F t‖+‖target t‖ ≤ 2 := by linarith [hF t,targetNorm t]
    calc _ ≤ 2*(Real.pi*|t|/n) := by nlinarith [mul_le_mul hs hd (abs_nonneg (‖F t‖-‖target t‖)) (by norm_num : (0:ℝ)≤2)]
         _ = _ := by ring
  have sc : (∫ t in -h..h, sqF t) = (∫ β in -(h/n)..h/n, polysum n β^2*phase (-(n:ℝ)*β))/(n:ℂ) := by
    convert scaled (fun β : ℝ => polysum n β^2*phase (-(n:ℝ)*β)) (n:ℝ) h hr.ne' using 1
    apply intervalIntegral.integral_congr
    intro t _
    have he : -(n:ℝ)*(t/n) = -t := by field_simp
    change (polysum n (t/n)/(n:ℂ))^2 * phase (-t) = (polysum n (t/n)^2 * phase (-(n:ℝ)*(t/n))) / (((n:ℝ):ℂ)^2)
    rw [he,Complex.ofReal_natCast,div_pow]
    ring
  have sr : (∫ t in -h..h, M t) = (∫ β in -(h/n)..h/n, ‖polysum n β‖^2)/(n:ℝ) := by
    convert scaled (fun β : ℝ => ‖polysum n β‖^2) (n:ℝ) h hr.ne' using 1
    apply intervalIntegral.integral_congr; intro t _
    simp [M,F,norm_div,Complex.norm_natCast,div_pow]
  have hG : (∫ t in -h..h, sqG t) = ((∫ t in -h..h, J t):ℝ) := intervalIntegral.integral_ofReal
  refine ⟨fun t => (hp t).trans (by have := abs_nonneg t; gcongr <;> linarith [Real.pi_pos]),?_,?_⟩
  · have hc := intBound cSq cG h (2*Real.pi/n) hh c pointC
    have hl := (Complex.abs_re_le_norm _).trans hc
    rw [sc,hG,Complex.sub_re,Complex.ofReal_re] at hl
    have hre (z : ℂ) : (z/(n:ℂ)).re = z.re/n := by exact Complex.div_ofReal_re z (n:ℝ)
    rw [hre] at hl
    exact hl.trans_eq (by ring)
  · have hl := intBound cM cJ h (2*Real.pi/n) hh c pointR
    rw [sr,Real.norm_eq_abs] at hl
    exact hl.trans_eq (by ring)

-- ===== Ramanujan divisor formula (from Conjectures/Goldbach/FiniteMajorSignedErrorDivisorFold) =====
namespace RamFold
open Finset

noncomputable def phase (x : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

def units (q : ℕ) := (range q).filter (fun a => Nat.Coprime a q)

private theorem complete_phase_sum (m a : ℕ) (hm : 0 < m) :
    ∑ b ∈ range m, phase ((a : ℝ) * (b : ℝ) / m) =
      if m ∣ a then (m : ℂ) else 0 := by
  let z : ℂ := Complex.exp (2 * Real.pi * Complex.I * a / m)
  have hz : z = 1 ↔ m ∣ a :=
    Complex.exp_two_pi_mul_I_mul_div_eq_one_iff hm.ne'
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hpow (b : ℕ) : phase ((a : ℝ) * (b : ℝ) / m) = z ^ b := by
    rw [← Complex.exp_nat_mul]
    unfold phase
    push_cast
    congr 1
    field_simp
  simp_rw [hpow]
  by_cases h : m ∣ a
  · simp [h, hz.mpr h]
  · simp only [h, ite_false]
    have hzm : z ^ m = 1 := by
      rw [← Complex.exp_nat_mul]
      have harg : (m : ℂ) * (2 * Real.pi * Complex.I * a / m) =
          a * (2 * Real.pi * Complex.I) := by
        field_simp
      rw [harg]
      exact Complex.exp_nat_mul_two_pi_mul_I a
    have hsum := geom_sum_mul z m
    rw [hzm, sub_self] at hsum
    exact (mul_eq_zero.mp hsum).resolve_right
      (sub_ne_zero.mpr (fun hz1 => h (hz.mp hz1)))

private theorem coprime_indicator (q b : ℕ) (hq : 0 < q) :
    (∑ d ∈ q.divisors, if d ∣ b then (ArithmeticFunction.moebius d : ℂ) else 0) =
      if Nat.Coprime b q then 1 else 0 := by
  have hg : Nat.gcd b q ≠ 0 := (Nat.gcd_pos_of_pos_right b hq).ne'
  have hs : q.divisors.filter (fun d => d ∣ b) = (Nat.gcd b q).divisors := by
    ext d
    simp [Nat.mem_divisors, hq.ne', hg, Nat.dvd_gcd_iff, and_comm]
  rw [← sum_filter, hs]
  have h := DFunLike.congr_fun
    (ArithmeticFunction.coe_zeta_mul_coe_moebius (R := ℂ)) (Nat.gcd b q)
  simpa only [ArithmeticFunction.coe_zeta_mul_apply, ArithmeticFunction.one_apply,
    ArithmeticFunction.intCoe_apply, Nat.Coprime] using h

private theorem multiples_phase_sum (q a d : ℕ) (hq : 0 < q) (hd : d ∣ q) :
    ∑ b ∈ (range q).filter (fun b => d ∣ b), phase ((a : ℝ) * (b : ℝ) / q) =
      if q / d ∣ a then ((q / d : ℕ) : ℂ) else 0 := by
  obtain ⟨m, rfl⟩ := hd
  have hd : 0 < d := Nat.pos_of_mul_pos_right hq
  have hm : 0 < m := Nat.pos_of_mul_pos_left hq
  rw [Nat.mul_div_cancel_left _ hd, ← complete_phase_sum m a hm]
  symm
  apply sum_nbij' (d * ·) (· / d)
  · intro j hj
    exact mem_filter.mpr
      ⟨mem_range.mpr (Nat.mul_lt_mul_of_pos_left (mem_range.mp hj) hd),
        dvd_mul_right d j⟩
  · intro k hk
    apply mem_range.mpr
    exact (Nat.div_lt_iff_lt_mul hd).mpr
      (by simpa [Nat.mul_comm] using mem_range.mp (mem_filter.mp hk).1)
  · intro j _
    exact Nat.mul_div_cancel_left j hd
  · intro k hk
    exact Nat.mul_div_cancel' (mem_filter.mp hk).2
  · intro j _
    unfold phase
    push_cast
    congr 1
    have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
    have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
    field_simp

private theorem ramanujan_sum (q a : ℕ) (hq : 0 < q) :
    ∑ b ∈ units q, phase ((a : ℝ) * (b : ℝ) / q) =
      ∑ d ∈ q.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℂ) *
        (if q / d ∣ a then ((q / d : ℕ) : ℂ) else 0) := by
  calc
    _ = ∑ b ∈ range q,
        (∑ d ∈ q.divisors,
          if d ∣ b then (ArithmeticFunction.moebius d : ℂ) else 0) *
          phase ((a : ℝ) * (b : ℝ) / q) := by
      simp only [coprime_indicator q _ hq, units, sum_filter]
      apply sum_congr rfl
      intro b _
      by_cases h : Nat.Coprime b q <;> simp [h]
    _ = ∑ d ∈ q.divisors, ∑ b ∈ range q,
        (if d ∣ b then (ArithmeticFunction.moebius d : ℂ) else 0) *
          phase ((a : ℝ) * (b : ℝ) / q) := by
      simp only [sum_mul]
      rw [sum_comm]
    _ = _ := by
      apply sum_congr rfl
      intro d hd
      rw [← multiples_phase_sum q a d hq (Nat.dvd_of_mem_divisors hd),
        mul_sum, sum_filter]
      apply sum_congr rfl
      intro b _
      by_cases h : d ∣ b <;> simp [h]

theorem ramanujan_divisor_formula (q a : ℕ) (hq : 0 < q) :
    ∑ b ∈ units q, phase ((a : ℝ) * (b : ℝ) / q) =
      ∑ d ∈ q.divisors,
        if d ∣ a then
          (d : ℂ) * ((ArithmeticFunction.moebius (q / d) : ℤ) : ℂ)
        else 0 := by
  rw [ramanujan_sum q a hq]
  let f : ℕ → ℂ := fun d =>
    if d ∣ a then (d : ℂ) * ((ArithmeticFunction.moebius (q / d) : ℤ) : ℂ) else 0
  calc
    (∑ d ∈ q.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℂ) *
        (if q / d ∣ a then ((q / d : ℕ) : ℂ) else 0)) =
        ∑ d ∈ q.divisors, f (q / d) := by
      apply sum_congr rfl
      intro d hd
      have hcomp : q / (q / d) = d :=
        Nat.div_div_self (Nat.dvd_of_mem_divisors hd) hq.ne'
      unfold f
      rw [hcomp]
      by_cases ha : q / d ∣ a <;> simp [ha]
      ring
    _ = ∑ d ∈ q.divisors, f d := Nat.sum_div_divisors q f
    _ = ∑ d ∈ q.divisors,
        if d ∣ a then
          (d : ℂ) * ((ArithmeticFunction.moebius (q / d) : ℤ) : ℂ)
        else 0 := rfl

end RamFold

namespace Glue
open Finset Filter MeasureTheory
open scoped Topology ComplexConjugate
noncomputable section

open GoldbachMajorArc

/-- The statement's prime weight. -/
def waux (k : ℕ) : ℝ := if Nat.Prime k then Real.log (k:ℝ) else 0

theorem waux_nonneg (k : ℕ) : 0 ≤ waux k := by
  unfold waux
  split_ifs with h
  · exact Real.log_nonneg (by exact_mod_cast h.one_le)
  · exact le_rfl

def lowaux (n k : ℕ) : ℝ := if k^3 ≤ n then waux k else 0

def highaux (n k : ℕ) : ℝ := waux k - lowaux n k

def Saux (n : ℕ) (w : ℕ → ℝ) (t : ℝ) : ℂ :=
  Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*GoldbachMajorArc.phase ((k:ℝ)*t))

def Iaux (n:ℕ) (a b:ℕ→ℝ) : ℂ :=
  intervalIntegral (fun t => (arcs n)ᶜ.indicator (fun u => Saux n a u*Saux n b u*GoldbachMajorArc.phase (-(n:ℝ)*u)) t)
    (0:ℝ) 1 MeasureTheory.volume

def majArc (n : ℕ) (a : ℕ → ℝ) : ℂ :=
  intervalIntegral (fun t => (arcs n).indicator (fun u => Saux n a u*Saux n a u*GoldbachMajorArc.phase (-(n:ℝ)*u)) t)
    (0:ℝ) 1 MeasureTheory.volume

def majHigh (n : ℕ) : ℂ := majArc n (highaux n)

def Raux (n : ℕ) : ℝ := Finset.sum (Finset.HasAntidiagonal.antidiagonal n) (fun x => waux x.1*waux x.2)

def Rhighaux (n : ℕ) : ℝ := Finset.sum (Finset.range (n+1)) (fun k => highaux n k * highaux n (n-k))

def caux (q n : ℕ) : ℝ :=
  Finset.sum q.divisors (fun d => (if d ∣ n then (d:ℝ) else 0)*(ArithmeticFunction.moebius (q/d):ℝ))

def Jaux (z : ℝ) : ℝ :=
  intervalIntegral (fun t : ℝ => (Real.sinc (Real.pi*t))^2) (-z) z MeasureTheory.volume

def Maux (n : ℕ) : ℝ :=
  (n:ℝ)*Finset.sum (Finset.Icc 1 (cutoff n))
    (fun q => caux q n*((ArithmeticFunction.moebius q:ℝ)/q.totient)^2*Jaux ((cutoff n:ℝ)/q))

def Vaux (n : ℕ) (β : ℝ) : ℂ := ∑ k ∈ Finset.Icc 1 n, GoldbachMajorArc.phase ((k:ℝ)*β)

def KVaux (n : ℕ) (b : ℝ) : ℝ := ∫ β in -b..b, ‖Vaux n β‖^2

/-! ### Basic measurability and continuity -/

theorem arcs_measurable (n : ℕ) : MeasurableSet (arcs n) := by
  have h := ConvSum.measurable_rational_arcs (cutoff n) n
  exact h

theorem continuous_Saux (n : ℕ) (w : ℕ → ℝ) : Continuous (Saux n w) := by
  unfold Saux GoldbachMajorArc.phase
  fun_prop

theorem phase_norm (x : ℝ) : ‖GoldbachMajorArc.phase x‖ = 1 := by
  unfold GoldbachMajorArc.phase
  exact Complex.norm_exp_ofReal_mul_I _

/-! ### The minor arc integral as a convolution minus the major arc part -/

theorem Iaux_eq (n : ℕ) (a : ℕ → ℝ) :
    Iaux n a a = ((∑ k ∈ Finset.range (n+1), a k * a (n-k) : ℝ) : ℂ) - majArc n a := by
  have hA : MeasurableSet (arcs n) := arcs_measurable n
  have hcont : Continuous (fun u => Saux n a u * Saux n a u * GoldbachMajorArc.phase (-(n:ℝ)*u)) := by
    have h1 : Continuous (Saux n a) := continuous_Saux n a
    exact ((h1.mul h1).mul (by unfold GoldbachMajorArc.phase; fun_prop))
  have hint : IntervalIntegrable (fun u => Saux n a u * Saux n a u * GoldbachMajorArc.phase (-(n:ℝ)*u))
      MeasureTheory.volume 0 1 := hcont.intervalIntegrable 0 1
  have hsplit := ConvSum.indicator_integral_split (f := fun u => Saux n a u * Saux n a u * GoldbachMajorArc.phase (-(n:ℝ)*u))
    hA hint
  have hsplit' : (∫ t in (0:ℝ)..1, (arcs n)ᶜ.indicator (fun u => Saux n a u * Saux n a u * GoldbachMajorArc.phase (-(n:ℝ)*u)) t)
      + (∫ t in (0:ℝ)..1, (arcs n).indicator (fun u => Saux n a u * Saux n a u * GoldbachMajorArc.phase (-(n:ℝ)*u)) t)
      = (∫ t in (0:ℝ)..1, Saux n a t * Saux n a t * GoldbachMajorArc.phase (-(n:ℝ)*t)) := by
    rw [add_comm]
    exact hsplit
  have hconv : (∫ t in (0:ℝ)..1, Saux n a t * Saux n a t * GoldbachMajorArc.phase (-(n:ℝ)*t))
      = ((∑ k ∈ Finset.range (n+1), a k * a (n-k) : ℝ) : ℂ) := by
    have h := ConvSum.coefficient a n
    have hs : (fun t => Saux n a t * Saux n a t * GoldbachMajorArc.phase (-(n:ℝ)*t))
        = (fun t => (∑ k ∈ Finset.range (n + 1), (a k : ℂ) * ConvSum.E ((k : ℝ) * t)) ^ 2 *
          ConvSum.E (-(n:ℝ) * t)) := by
      funext t
      simp only [Saux, ConvSum.E, GoldbachMajorArc.phase, sq]
    rw [hs, h]
  unfold Iaux majArc
  rw [eq_sub_iff_add_eq, hsplit', hconv]

theorem Iaux_re (n : ℕ) :
    (Iaux n (highaux n) (highaux n)).re = Rhighaux n - (majHigh n).re := by
  rw [Iaux_eq]
  simp [Rhighaux, majHigh, Complex.sub_re, Complex.ofReal_re]

/-! ### The two convolutions -/

theorem Raux_eq (n : ℕ) : Raux n = ∑ k ∈ Finset.range (n+1), waux k * waux (n-k) := by
  classical
  unfold Raux
  rw [Finset.Nat.antidiagonal_eq_map, Finset.sum_map]
  rfl

theorem highaux_nonneg (n k : ℕ) : 0 ≤ highaux n k := by
  unfold highaux lowaux
  split_ifs with h
  · simp
  · simpa using waux_nonneg k

theorem highaux_le (n k : ℕ) : highaux n k ≤ waux k := by
  unfold highaux lowaux
  split_ifs with h
  · simpa using waux_nonneg k
  · simp

theorem Rhighaux_le_Raux (n : ℕ) : Rhighaux n ≤ Raux n := by
  rw [Raux_eq]
  unfold Rhighaux
  apply Finset.sum_le_sum
  intro k _
  exact mul_le_mul (highaux_le n k) (highaux_le n (n-k)) (highaux_nonneg n (n-k))
    (waux_nonneg k)

/-! ### Bounding the removed small primes -/

theorem waux_le_log (n k : ℕ) (hk : k ≤ n) (hn : 1 ≤ n) : waux k ≤ Real.log (n:ℝ) := by
  unfold waux
  split_ifs with h
  · have h0 : (0:ℝ) < (k:ℝ) := by exact_mod_cast h.pos
    have h2 : (k:ℝ) ≤ (n:ℝ) := by exact_mod_cast hk
    exact Real.log_le_log h0 h2
  · have : (0:ℝ) ≤ Real.log (n:ℝ) := Real.log_nonneg (by exact_mod_cast hn)
    exact this

theorem small_card (n : ℕ) :
    (((Finset.range (n+1)).filter (fun k => k^3 ≤ n)).card : ℝ) ≤ Real.sqrt (n:ℝ) + 1 := by
  have hn0 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
  have hsub : (Finset.range (n+1)).filter (fun k => k^3 ≤ n)
      ⊆ Finset.range (⌊Real.sqrt (n:ℝ)⌋₊ + 1) := by
    intro k hk
    have hk3 : k^3 ≤ n := (Finset.mem_filter.mp hk).2
    have hk1 : k ≤ n := by
      have hself : k ≤ k^3 := by
        cases k with
        | zero => exact le_rfl
        | succ m => exact Nat.le_self_pow (by norm_num) _
      omega
    have hsq : (k:ℝ)^2 ≤ (n:ℝ) := by
      have h1 : (k:ℝ)^3 ≤ (n:ℝ) := by exact_mod_cast hk3
      have h2 : (k:ℝ)^2 ≤ (k:ℝ)^3 := by
        rcases Nat.eq_zero_or_pos k with rfl | hk0
        · norm_num
        · have hk1' : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk0
          calc (k:ℝ)^2 = (k:ℝ)^2 * 1 := by ring
            _ ≤ (k:ℝ)^2 * (k:ℝ) := mul_le_mul_of_nonneg_left hk1' (sq_nonneg _)
            _ = (k:ℝ)^3 := by ring
      linarith
    have hksqrt : (k:ℝ) ≤ Real.sqrt (n:ℝ) := by
      have h := Real.sqrt_le_sqrt hsq
      rwa [Real.sqrt_sq (Nat.cast_nonneg k)] at h
    have hfloor : k ≤ ⌊Real.sqrt (n:ℝ)⌋₊ := Nat.le_floor hksqrt
    exact Finset.mem_range.mpr (by omega)
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_range] at hcard
  have hfloor : ((⌊Real.sqrt (n:ℝ)⌋₊ : ℕ) : ℝ) ≤ Real.sqrt (n:ℝ) :=
    Nat.floor_le (Real.sqrt_nonneg (n:ℝ))
  calc (((Finset.range (n+1)).filter (fun k => k^3 ≤ n)).card : ℝ)
      ≤ ((⌊Real.sqrt (n:ℝ)⌋₊ + 1 : ℕ) : ℝ) := by exact_mod_cast hcard
    _ = ((⌊Real.sqrt (n:ℝ)⌋₊ : ℕ) : ℝ) + 1 := by push_cast; ring
    _ ≤ Real.sqrt (n:ℝ) + 1 := by linarith

theorem RminusRhigh (n : ℕ) (hn : 1 ≤ n) :
    Raux n - Rhighaux n ≤ 2 * ((Real.sqrt (n:ℝ) + 1) * (Real.log (n:ℝ))^2) := by
  have hlog : 0 ≤ Real.log (n:ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  have hstep1 : Raux n - Rhighaux n
      ≤ (∑ k ∈ Finset.range (n+1),
          ((if k^3 ≤ n then waux k * waux (n-k) else 0) +
           (if (n-k)^3 ≤ n then waux k * waux (n-k) else 0))) := by
    rw [Raux_eq]
    unfold Rhighaux
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro k hk
    have hw : 0 ≤ waux k * waux (n-k) := mul_nonneg (waux_nonneg k) (waux_nonneg (n-k))
    have hA : highaux n k = if k^3 ≤ n then 0 else waux k := by
      unfold highaux lowaux
      split_ifs <;> simp
    have hB : highaux n (n-k) = if (n-k)^3 ≤ n then 0 else waux (n-k) := by
      unfold highaux lowaux
      split_ifs <;> simp
    rw [hA, hB]
    by_cases h1 : k^3 ≤ n <;> by_cases h2 : (n-k)^3 ≤ n <;>
      simp [h1, h2] <;> linarith [hw]
  have hstep2 : (∑ k ∈ Finset.range (n+1),
        (if k^3 ≤ n then waux k * waux (n-k) else 0)) ≤
      (Real.sqrt (n:ℝ) + 1) * (Real.log (n:ℝ))^2 := by
    have hbound : ∀ k ∈ Finset.range (n+1), k^3 ≤ n →
        waux k * waux (n-k) ≤ (Real.log (n:ℝ))^2 := by
      intro k hk hk3
      have hkn : k ≤ n := by have := Finset.mem_range.mp hk; omega
      have h1 : waux k * waux (n-k) ≤ Real.log (n:ℝ) * Real.log (n:ℝ) :=
        mul_le_mul (waux_le_log n k hkn hn) (waux_le_log n (n-k) (by omega) hn)
          (waux_nonneg (n-k)) hlog
      calc waux k * waux (n-k) ≤ Real.log (n:ℝ) * Real.log (n:ℝ) := h1
        _ = (Real.log (n:ℝ))^2 := by ring
    have : (∑ k ∈ (Finset.range (n+1)).filter (fun k => k^3 ≤ n),
        waux k * waux (n-k)) ≤ (((Finset.range (n+1)).filter (fun k => k^3 ≤ n)).card : ℝ)
          * (Real.log (n:ℝ))^2 := by
      calc _ ≤ ∑ _k ∈ (Finset.range (n+1)).filter (fun k => k^3 ≤ n), (Real.log (n:ℝ))^2 :=
            Finset.sum_le_sum (fun k hk => hbound k (Finset.mem_filter.mp hk).1
              (Finset.mem_filter.mp hk).2)
        _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
    have hrw : (∑ k ∈ Finset.range (n+1), (if k^3 ≤ n then waux k * waux (n-k) else 0))
        = ∑ k ∈ (Finset.range (n+1)).filter (fun k => k^3 ≤ n), waux k * waux (n-k) :=
      (Finset.sum_filter _ _).symm
    rw [hrw]
    have hcard := small_card n
    nlinarith [this]
  have hstep3 : (∑ k ∈ Finset.range (n+1),
        (if (n-k)^3 ≤ n then waux k * waux (n-k) else 0)) ≤
      (Real.sqrt (n:ℝ) + 1) * (Real.log (n:ℝ))^2 := by
    have hrw : (∑ k ∈ Finset.range (n+1), (if (n-k)^3 ≤ n then waux k * waux (n-k) else 0))
        = ∑ k ∈ (Finset.range (n+1)).filter (fun k => (n-k)^3 ≤ n), waux k * waux (n-k) :=
      (Finset.sum_filter _ _).symm
    rw [hrw]
    have hbound : ∀ k ∈ (Finset.range (n+1)).filter (fun k => (n-k)^3 ≤ n),
        waux k * waux (n-k) ≤ (Real.log (n:ℝ))^2 := by
      intro k hk
      have hk' := Finset.mem_filter.mp hk
      have hkn : k ≤ n := by have := Finset.mem_range.mp hk'.1; omega
      have h1 : waux k * waux (n-k) ≤ Real.log (n:ℝ) * Real.log (n:ℝ) :=
        mul_le_mul (waux_le_log n k hkn hn) (waux_le_log n (n-k) (by omega) hn)
          (waux_nonneg (n-k)) hlog
      calc waux k * waux (n-k) ≤ Real.log (n:ℝ) * Real.log (n:ℝ) := h1
        _ = (Real.log (n:ℝ))^2 := by ring
    have hcard' : (((Finset.range (n+1)).filter (fun k => (n-k)^3 ≤ n)).card : ℝ)
        ≤ Real.sqrt (n:ℝ) + 1 := by
      have hsub : (Finset.range (n+1)).filter (fun k => (n-k)^3 ≤ n)
          ⊆ ((Finset.range (n+1)).filter (fun j => j^3 ≤ n)).image (fun j => n - j) := by
        intro k hk
        have hk' := Finset.mem_filter.mp hk
        have hkn : k ≤ n := by have := Finset.mem_range.mp hk'.1; omega
        refine Finset.mem_image.mpr ⟨n - k, Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr (by omega), hk'.2⟩, ?_⟩
        omega
      have hc := Finset.card_le_card hsub
      have hi := Finset.card_image_le (s := (Finset.range (n+1)).filter (fun j => j^3 ≤ n))
        (f := fun j => n - j)
      have hcard := small_card n
      calc (((Finset.range (n+1)).filter (fun k => (n-k)^3 ≤ n)).card : ℝ)
          ≤ ((((Finset.range (n+1)).filter (fun j => j^3 ≤ n)).image (fun j => n - j)).card : ℝ) := by
            exact_mod_cast hc
        _ ≤ (((Finset.range (n+1)).filter (fun j => j^3 ≤ n)).card : ℝ) := by exact_mod_cast hi
        _ ≤ Real.sqrt (n:ℝ) + 1 := hcard
    calc _ ≤ ∑ _k ∈ (Finset.range (n+1)).filter (fun k => (n-k)^3 ≤ n), (Real.log (n:ℝ))^2 :=
          Finset.sum_le_sum hbound
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (Real.sqrt (n:ℝ) + 1) * (Real.log (n:ℝ))^2 := by
          have hlog2 : 0 ≤ (Real.log (n:ℝ))^2 := sq_nonneg _
          nlinarith [hcard']
  have hsplit_sum : (∑ k ∈ Finset.range (n+1),
        ((if k^3 ≤ n then waux k * waux (n-k) else 0) +
         (if (n-k)^3 ≤ n then waux k * waux (n-k) else 0)))
      = (∑ k ∈ Finset.range (n+1), (if k^3 ≤ n then waux k * waux (n-k) else 0))
        + (∑ k ∈ Finset.range (n+1), (if (n-k)^3 ≤ n then waux k * waux (n-k) else 0)) :=
    Finset.sum_add_distrib
  rw [hsplit_sum] at hstep1
  linarith [hstep1, hstep2, hstep3]

/-! ### The Ramanujan coefficient matches the divisor sum -/

theorem ram_divisor (q h : ℕ) (hq : 0 < q) : ram q h = ((caux q h : ℝ) : ℂ) := by
  have h1 : (∑ b ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), GoldbachMajorArc.phase ((h:ℝ)*(b:ℝ)/q))
      = ∑ d ∈ q.divisors, if d ∣ h then (d:ℂ)*((ArithmeticFunction.moebius (q/d):ℤ):ℂ) else 0 := by
    have := RamFold.ramanujan_divisor_formula q h hq
    simpa only [RamFold.units, RamFold.phase, GoldbachMajorArc.phase] using this
  unfold ram
  rw [h1]
  unfold caux
  push_cast
  apply Finset.sum_congr rfl
  intro d _
  by_cases hd : d ∣ h
  · simp only [hd, if_true]
    push_cast
    ring
  · simp [hd]

theorem caux_one (q : ℕ) (hq : 0 < q) : caux q 1 = (ArithmeticFunction.moebius q : ℝ) := by
  unfold caux
  have hone : (1:ℕ) ∈ q.divisors := Nat.one_mem_divisors.mpr hq.ne'
  have hz : ∀ d ∈ q.divisors, d ≠ 1 →
      (if d ∣ (1:ℕ) then (d:ℝ) else 0)*(ArithmeticFunction.moebius (q/d):ℝ) = 0 := by
    intro d _ hne
    have : ¬ (d ∣ (1:ℕ)) := fun h => hne (Nat.dvd_one.mp h)
    simp [this]
  rw [Finset.sum_eq_single 1 hz (fun h => absurd hone h)]
  simp

theorem coefficient_re (q n : ℕ) (hq : 0 < q) :
    (coefficient q n).re = caux q n * ((ArithmeticFunction.moebius q:ℝ)/q.totient)^2 := by
  have h1 : ram q 1 = ((ArithmeticFunction.moebius q:ℝ):ℂ) := by
    rw [ram_divisor q 1 hq, caux_one q hq]
  have h2 : ram q n = ((caux q n:ℝ):ℂ) := ram_divisor q n hq
  have hφ : ((q.totient:ℕ):ℂ) = ((q.totient:ℝ):ℂ) := by norm_cast
  have hrw : coefficient q n
      = ((((ArithmeticFunction.moebius q:ℝ)/(q.totient:ℝ))^2 * caux q n : ℝ) : ℂ) := by
    unfold coefficient
    rw [h1, h2, hφ, Complex.conj_ofReal, ← Complex.ofReal_div, ← Complex.ofReal_pow,
      ← Complex.ofReal_mul]
  rw [hrw, Complex.ofReal_re]
  ring

/-! ### Elementary coefficient bounds -/

theorem caux_bound (q n : ℕ) (hq : 0 < q) : |caux q n| ≤ (q:ℝ)^2 := by
  have hcard : q.divisors.card ≤ q := by
    have hsub : q.divisors ⊆ Finset.Icc 1 q := by
      intro d hd
      have hd' := Nat.mem_divisors.mp hd
      exact Finset.mem_Icc.mpr ⟨Nat.pos_of_dvd_of_pos hd'.1 hq, Nat.le_of_dvd hq hd'.1⟩
    have := Finset.card_le_card hsub
    rwa [Nat.card_Icc] at this
  have hterm : ∀ d ∈ q.divisors,
      |(if d ∣ n then (d:ℝ) else 0)*(ArithmeticFunction.moebius (q/d):ℝ)| ≤ (q:ℝ) := by
    intro d hd
    have hd' := Nat.mem_divisors.mp hd
    have hdq : d ≤ q := Nat.le_of_dvd hq hd'.1
    have h1 : |(if d ∣ n then (d:ℝ) else 0)| ≤ (q:ℝ) := by
      by_cases h : d ∣ n
      · simp only [h, if_true]
        rw [abs_of_nonneg (by exact_mod_cast (Nat.zero_le d) : (0:ℝ) ≤ (d:ℝ))]
        exact_mod_cast hdq
      · simp only [h, if_false, abs_zero]
        exact Nat.cast_nonneg q
    have h2 : |(ArithmeticFunction.moebius (q/d):ℝ)| ≤ 1 := by
      have hμ := ArithmeticFunction.abs_moebius_le_one (n := q/d)
      rw [abs_le] at hμ ⊢
      exact ⟨by exact_mod_cast hμ.1, by exact_mod_cast hμ.2⟩
    calc _ = |(if d ∣ n then (d:ℝ) else 0)| * |(ArithmeticFunction.moebius (q/d):ℝ)| := abs_mul _ _
      _ ≤ (q:ℝ) * 1 := by
          apply mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = (q:ℝ) := by ring
  unfold caux
  calc |∑ d ∈ q.divisors, _| ≤ ∑ d ∈ q.divisors, |(if d ∣ n then (d:ℝ) else 0)*(ArithmeticFunction.moebius (q/d):ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ q.divisors, (q:ℝ) := Finset.sum_le_sum hterm
    _ = (q.divisors.card : ℝ) * (q:ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (q:ℝ)*(q:ℝ) := by
        have : (q.divisors.card : ℝ) ≤ (q:ℝ) := by exact_mod_cast hcard
        nlinarith [this, Nat.cast_nonneg (α := ℝ) q]
    _ = (q:ℝ)^2 := by ring

theorem coeff_sq_le_one (q : ℕ) (hq : 0 < q) :
    ((ArithmeticFunction.moebius q:ℝ)/q.totient)^2 ≤ 1 := by
  have hφ : (1:ℝ) ≤ (q.totient:ℝ) := by
    have := Nat.totient_pos.mpr hq
    exact_mod_cast (show 1 ≤ q.totient by omega)
  have hμ : |(ArithmeticFunction.moebius q:ℝ)| ≤ 1 := by
    have h := ArithmeticFunction.abs_moebius_le_one (n := q)
    rw [abs_le] at h ⊢
    exact ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩
  have hφpos : (0:ℝ) < (q.totient:ℝ) := by
    have h := Nat.totient_pos.mpr hq
    exact_mod_cast h
  have h1 : |(ArithmeticFunction.moebius q:ℝ)/q.totient| ≤ 1 := by
    have hμ' := abs_le.mp hμ
    rw [abs_le]
    constructor
    · rw [le_div_iff₀ hφpos]
      nlinarith [hμ'.1, hμ'.2, hφ]
    · rw [div_le_iff₀ hφpos]
      nlinarith [hμ'.1, hμ'.2, hφ]
  have hx := abs_le.mp h1
  nlinarith [hx.1, hx.2]

/-! ### The discrete kernel against the continuous sinc model -/

theorem kernel_eq_Vaux (n : ℕ) (β : ℝ) : kernel n β = 1 + Vaux n β := by
  have hset : Finset.range (n+1) = insert 0 (Finset.Icc 1 n) := by
    ext k
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  unfold kernel Vaux
  rw [hset, Finset.sum_insert (by simp)]
  simp [GoldbachMajorArc.phase]

theorem Vaux_norm_le (n : ℕ) (β : ℝ) : ‖Vaux n β‖ ≤ (n:ℝ) := by
  unfold Vaux
  calc ‖∑ k ∈ Finset.Icc 1 n, GoldbachMajorArc.phase ((k:ℝ)*β)‖ ≤ ∑ k ∈ Finset.Icc 1 n, ‖GoldbachMajorArc.phase ((k:ℝ)*β)‖ :=
        norm_sum_le _ _
    _ = ((Finset.Icc 1 n).card : ℝ) := by
        simp only [phase_norm, Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ (n:ℝ) := by
        rw [Nat.card_Icc]
        have h : n + 1 - 1 = n := by omega
        rw [h]

theorem kernelMass_sub_KV (n : ℕ) (b : ℝ) (hb : 0 ≤ b) :
    |kernelMass n b - KVaux n b| ≤ (2*(n:ℝ)+1) * (2*b) := by
  have hpt : ∀ β, ‖(‖kernel n β‖^2 : ℝ) - ‖Vaux n β‖^2‖ ≤ 2*(n:ℝ)+1 := by
    intro β
    rw [kernel_eq_Vaux]
    have hV := Vaux_norm_le n β
    have h1 : ‖(1:ℂ) + Vaux n β‖ ≤ 1 + (n:ℝ) := by
      calc _ ≤ ‖(1:ℂ)‖ + ‖Vaux n β‖ := norm_add_le _ _
        _ ≤ 1 + (n:ℝ) := by rw [norm_one]; linarith
    have h2 : |‖(1:ℂ) + Vaux n β‖ - ‖Vaux n β‖| ≤ 1 := by
      calc _ ≤ ‖(1:ℂ) + Vaux n β - Vaux n β‖ := abs_norm_sub_norm_le _ _
        _ = 1 := by simp
    have h3 : (0:ℝ) ≤ ‖(1:ℂ) + Vaux n β‖ := norm_nonneg _
    have h4 : (0:ℝ) ≤ ‖Vaux n β‖ := norm_nonneg _
    have h5 : ‖(1:ℂ) + Vaux n β‖ - ‖Vaux n β‖ ≤ 1 := (abs_le.mp h2).2
    have h6 : -(1:ℝ) ≤ ‖(1:ℂ) + Vaux n β‖ - ‖Vaux n β‖ := (abs_le.mp h2).1
    rw [sq_sub_sq, Real.norm_eq_abs, abs_mul, abs_of_nonneg (by linarith)]
    nlinarith [h1, hV, h5, h6]
  have hc1 : Continuous (fun β => ‖kernel n β‖^2) := by
    unfold kernel GoldbachMajorArc.phase; fun_prop
  have hc2 : Continuous (fun β => ‖Vaux n β‖^2) := by
    unfold Vaux GoldbachMajorArc.phase; fun_prop
  have hdiff : Continuous (fun β => (‖kernel n β‖^2 : ℝ) - ‖Vaux n β‖^2) := hc1.sub hc2
  unfold kernelMass KVaux
  rw [← intervalIntegral.integral_sub (hc1.intervalIntegrable _ _) (hc2.intervalIntegrable _ _)]
  calc ‖∫ β in -b..b, ((‖kernel n β‖^2 : ℝ) - ‖Vaux n β‖^2)‖
      ≤ ∫ β in -b..b, ‖(‖kernel n β‖^2 : ℝ) - ‖Vaux n β‖^2‖ :=
        intervalIntegral.norm_integral_le_integral_norm (by linarith)
    _ ≤ ∫ β in -b..b, (2*(n:ℝ)+1) := by
        apply intervalIntegral.integral_mono_on (by linarith)
        · exact hdiff.norm.intervalIntegrable _ _
        · exact continuous_const.intervalIntegrable _ _
        · intro β _; exact hpt β
    _ = (2*(n:ℝ)+1) * (2*b) := by
        rw [intervalIntegral.integral_const]
        norm_num
        ring

theorem kernelMass_model (n q : ℕ) (hn : 0 < n) (hq : 0 < q) :
    |kernelMass n (width n q) - (n:ℝ)*Jaux ((cutoff n:ℝ)/q)|
      ≤ 4*Real.pi*((cutoff n:ℝ)/q)^2 + (2*(n:ℝ)+1)*(2*width n q) := by
  have hnR : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have hqR : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  have hres := kernel_rescale n ((cutoff n:ℝ)/q) hn (by positivity)
  have h3 : |(∫ β in -(((cutoff n:ℝ)/q)/n)..(((cutoff n:ℝ)/q)/n), ‖Vaux n β‖^2)/(n:ℝ)
      - Jaux ((cutoff n:ℝ)/q)| ≤ 4*Real.pi*((cutoff n:ℝ)/q)^2/(n:ℝ) := by
    have h := hres
    dsimp only at h
    simpa only [Vaux, Jaux, GoldbachMajorArc.phase] using h.2.2
  have hwidth : ((cutoff n:ℝ)/q)/n = width n q := by
    unfold width
    field_simp <;> ring
  rw [hwidth] at h3
  have hKV : |KVaux n (width n q) - (n:ℝ)*Jaux ((cutoff n:ℝ)/q)|
      ≤ 4*Real.pi*((cutoff n:ℝ)/q)^2 := by
    have h1 : |KVaux n (width n q) - (n:ℝ)*Jaux ((cutoff n:ℝ)/q)|
        = (n:ℝ) * |KVaux n (width n q)/(n:ℝ) - Jaux ((cutoff n:ℝ)/q)| := by
      have hkey : KVaux n (width n q) - (n:ℝ)*Jaux ((cutoff n:ℝ)/q)
          = (n:ℝ) * (KVaux n (width n q)/(n:ℝ) - Jaux ((cutoff n:ℝ)/q)) := by
        field_simp
      rw [hkey, abs_mul, abs_of_pos hnR]
    rw [h1]
    have h3' : |KVaux n (width n q)/(n:ℝ) - Jaux ((cutoff n:ℝ)/q)|
        ≤ 4*Real.pi*((cutoff n:ℝ)/q)^2/(n:ℝ) := by
      unfold KVaux
      exact h3
    have h2 := mul_le_mul_of_nonneg_left h3' hnR.le
    calc _ ≤ (n:ℝ) * (4*Real.pi*((cutoff n:ℝ)/q)^2/(n:ℝ)) := h2
      _ = 4*Real.pi*((cutoff n:ℝ)/q)^2 := by field_simp
  have hkern := kernelMass_sub_KV n (width n q) (by unfold width; positivity)
  calc |kernelMass n (width n q) - (n:ℝ)*Jaux ((cutoff n:ℝ)/q)|
      ≤ |kernelMass n (width n q) - KVaux n (width n q)|
          + |KVaux n (width n q) - (n:ℝ)*Jaux ((cutoff n:ℝ)/q)| := abs_sub_le _ _ _
    _ ≤ _ := by linarith

/-! ### The finite major-arc model against the statement's model -/

theorem model_gap (n : ℕ) (hn : 0 < n) :
    |(modeledContribution n).re - Maux n| ≤ (4*Real.pi+6)*(cutoff n:ℝ)^3 := by
  have hre : (modeledContribution n).re
      = ∑ q ∈ Finset.Icc 1 (cutoff n),
          caux q n * ((ArithmeticFunction.moebius q:ℝ)/q.totient)^2 * kernelMass n (width n q) := by
    unfold modeledContribution
    rw [Complex.re_sum]
    apply Finset.sum_congr rfl
    intro q hq
    have hq1 : 0 < q := (Finset.mem_Icc.mp hq).1
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, coefficient_re q n hq1]
    ring
  have hM : Maux n = ∑ q ∈ Finset.Icc 1 (cutoff n),
      (n:ℝ) * (caux q n * ((ArithmeticFunction.moebius q:ℝ)/q.totient)^2 * Jaux ((cutoff n:ℝ)/q)) := by
    unfold Maux
    rw [Finset.mul_sum]
  have hterm : ∀ q ∈ Finset.Icc 1 (cutoff n),
      |caux q n * ((ArithmeticFunction.moebius q:ℝ)/q.totient)^2 * kernelMass n (width n q)
        - (n:ℝ) * (caux q n * ((ArithmeticFunction.moebius q:ℝ)/q.totient)^2 * Jaux ((cutoff n:ℝ)/q))|
        ≤ (4*Real.pi+6)*(cutoff n:ℝ)^2 := by
    intro q hq
    have hq1 : 0 < q := (Finset.mem_Icc.mp hq).1
    have hq2 : q ≤ cutoff n := (Finset.mem_Icc.mp hq).2
    have hqR : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq1
    have hnR : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
    have hQ0 : (0:ℝ) ≤ (cutoff n:ℝ) := Nat.cast_nonneg _
    have hQq : (q:ℝ) ≤ (cutoff n:ℝ) := by exact_mod_cast hq2
    have hk := kernelMass_model n q hn hq1
    have hc := caux_bound q n hq1
    have hcs := coeff_sq_le_one q hq1
    have hcs0 : (0:ℝ) ≤ ((ArithmeticFunction.moebius q:ℝ)/q.totient)^2 := sq_nonneg _
    have hw : width n q = (cutoff n:ℝ)/((q:ℝ)*(n:ℝ)) := rfl
    have hmain : |caux q n * ((ArithmeticFunction.moebius q:ℝ)/q.totient)^2 * kernelMass n (width n q)
        - (n:ℝ) * (caux q n * ((ArithmeticFunction.moebius q:ℝ)/q.totient)^2 * Jaux ((cutoff n:ℝ)/q))|
        = |caux q n| * ((ArithmeticFunction.moebius q:ℝ)/q.totient)^2
          * |kernelMass n (width n q) - (n:ℝ)*Jaux ((cutoff n:ℝ)/q)| := by
      rw [show caux q n * ((ArithmeticFunction.moebius q:ℝ)/q.totient)^2 * kernelMass n (width n q)
            - (n:ℝ) * (caux q n * ((ArithmeticFunction.moebius q:ℝ)/q.totient)^2 * Jaux ((cutoff n:ℝ)/q))
          = (caux q n * ((ArithmeticFunction.moebius q:ℝ)/q.totient)^2) *
            (kernelMass n (width n q) - (n:ℝ)*Jaux ((cutoff n:ℝ)/q)) by ring,
        abs_mul, abs_mul, abs_of_nonneg hcs0]
    rw [hmain]
    have hstep1 : |caux q n| * ((ArithmeticFunction.moebius q:ℝ)/q.totient)^2
        ≤ (q:ℝ)^2 := by
      calc _ ≤ |caux q n| * 1 := by
            exact mul_le_mul_of_nonneg_left hcs (abs_nonneg _)
        _ ≤ (q:ℝ)^2 * 1 := by
            exact mul_le_mul_of_nonneg_right hc (by norm_num)
        _ = (q:ℝ)^2 := by ring
    have hstep2 : |caux q n| * ((ArithmeticFunction.moebius q:ℝ)/q.totient)^2
        * |kernelMass n (width n q) - (n:ℝ)*Jaux ((cutoff n:ℝ)/q)|
        ≤ (q:ℝ)^2 * (4*Real.pi*((cutoff n:ℝ)/q)^2 + (2*(n:ℝ)+1)*(2*width n q)) := by
      calc _ ≤ (q:ℝ)^2 * |kernelMass n (width n q) - (n:ℝ)*Jaux ((cutoff n:ℝ)/q)| := by
            exact mul_le_mul_of_nonneg_right hstep1 (abs_nonneg _)
        _ ≤ (q:ℝ)^2 * (4*Real.pi*((cutoff n:ℝ)/q)^2 + (2*(n:ℝ)+1)*(2*width n q)) := by
            exact mul_le_mul_of_nonneg_left hk (by positivity)
    have hq2pos : (0:ℝ) < (q:ℝ)^2 := by positivity
    have hA : (q:ℝ)^2 * (4*Real.pi*((cutoff n:ℝ)/q)^2) = 4*Real.pi*(cutoff n:ℝ)^2 := by
      field_simp <;> ring
    have hB : (q:ℝ)^2 * ((2*(n:ℝ)+1)*(2*width n q))
        = 2*(q:ℝ)*((2*(n:ℝ)+1)/(n:ℝ))*(cutoff n:ℝ) := by
      rw [hw]
      field_simp <;> ring
    have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    have h2n1 : (2*(n:ℝ)+1)/(n:ℝ) ≤ 3 := by
      rw [div_le_iff₀ hnR]
      linarith
    have hpos3 : (0:ℝ) ≤ 2*(q:ℝ)*(cutoff n:ℝ) := by positivity
    calc _ ≤ (q:ℝ)^2 * (4*Real.pi*((cutoff n:ℝ)/q)^2 + (2*(n:ℝ)+1)*(2*width n q)) := hstep2
      _ = 4*Real.pi*(cutoff n:ℝ)^2 + 2*(q:ℝ)*((2*(n:ℝ)+1)/(n:ℝ))*(cutoff n:ℝ) := by
          rw [mul_add, hA, hB]
      _ ≤ 4*Real.pi*(cutoff n:ℝ)^2 + 2*(cutoff n:ℝ)*3*(cutoff n:ℝ) := by
          have h1 : 2*(q:ℝ)*((2*(n:ℝ)+1)/(n:ℝ))*(cutoff n:ℝ)
              ≤ 2*(cutoff n:ℝ)*((2*(n:ℝ)+1)/(n:ℝ))*(cutoff n:ℝ) := by
            have : (0:ℝ) ≤ 2*((2*(n:ℝ)+1)/(n:ℝ))*(cutoff n:ℝ) := by positivity
            nlinarith [this, hQq]
          have h2 : 2*(cutoff n:ℝ)*((2*(n:ℝ)+1)/(n:ℝ))*(cutoff n:ℝ)
              ≤ 2*(cutoff n:ℝ)*3*(cutoff n:ℝ) := by
            have : (0:ℝ) ≤ 2*(cutoff n:ℝ)*(cutoff n:ℝ) := by positivity
            nlinarith [this, h2n1]
          linarith
      _ = (4*Real.pi+6)*(cutoff n:ℝ)^2 := by ring
  rw [hre, hM, ← Finset.sum_sub_distrib]
  calc |∑ q ∈ Finset.Icc 1 (cutoff n),
        (caux q n * ((ArithmeticFunction.moebius q:ℝ)/q.totient)^2 * kernelMass n (width n q)
          - (n:ℝ) * (caux q n * ((ArithmeticFunction.moebius q:ℝ)/q.totient)^2 * Jaux ((cutoff n:ℝ)/q)))|
      ≤ ∑ q ∈ Finset.Icc 1 (cutoff n),
        |caux q n * ((ArithmeticFunction.moebius q:ℝ)/q.totient)^2 * kernelMass n (width n q)
          - (n:ℝ) * (caux q n * ((ArithmeticFunction.moebius q:ℝ)/q.totient)^2 * Jaux ((cutoff n:ℝ)/q))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _q ∈ Finset.Icc 1 (cutoff n), (4*Real.pi+6)*(cutoff n:ℝ)^2 := Finset.sum_le_sum hterm
    _ = ((Finset.Icc 1 (cutoff n)).card : ℝ) * ((4*Real.pi+6)*(cutoff n:ℝ)^2) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (cutoff n:ℝ) * ((4*Real.pi+6)*(cutoff n:ℝ)^2) := by
        have hcard : ((Finset.Icc 1 (cutoff n)).card : ℝ) ≤ (cutoff n:ℝ) := by
          rw [Nat.card_Icc]
          have h : cutoff n + 1 - 1 = cutoff n := by omega
          rw [h]
        exact mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = (4*Real.pi+6)*(cutoff n:ℝ)^3 := by ring
/-! ### Sup norms of the exponential sums -/

theorem Saux_norm_le (n : ℕ) (a : ℕ → ℝ) (t : ℝ) :
    ‖Saux n a t‖ ≤ ∑ k ∈ Finset.range (n+1), |a k| := by
  unfold Saux
  calc ‖∑ k ∈ Finset.range (n+1), (a k:ℂ)*GoldbachMajorArc.phase ((k:ℝ)*t)‖
      ≤ ∑ k ∈ Finset.range (n+1), ‖(a k:ℂ)*GoldbachMajorArc.phase ((k:ℝ)*t)‖ := norm_sum_le _ _
    _ = ∑ k ∈ Finset.range (n+1), |a k| := by
        apply Finset.sum_congr rfl
        intro k _
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, phase_norm, mul_one]

theorem Saux_waux_bound (n : ℕ) (hn : 1 ≤ n) (t : ℝ) :
    ‖Saux n waux t‖ ≤ ((n:ℝ)+1) * Real.log (n:ℝ) := by
  refine (Saux_norm_le n waux t).trans ?_
  have h : ∀ k ∈ Finset.range (n+1), |waux k| ≤ Real.log (n:ℝ) := by
    intro k hk
    have hkn : k ≤ n := by have := Finset.mem_range.mp hk; omega
    rw [abs_of_nonneg (waux_nonneg k)]
    exact waux_le_log n k hkn hn
  calc ∑ k ∈ Finset.range (n+1), |waux k| ≤ ∑ _k ∈ Finset.range (n+1), Real.log (n:ℝ) :=
        Finset.sum_le_sum h
    _ = ((Finset.range (n+1)).card : ℝ) * Real.log (n:ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = ((n:ℝ)+1) * Real.log (n:ℝ) := by rw [Finset.card_range]; push_cast; ring

theorem Saux_low_bound (n : ℕ) (hn : 1 ≤ n) (t : ℝ) :
    ‖Saux n (lowaux n) t‖ ≤ (Real.sqrt (n:ℝ) + 1) * Real.log (n:ℝ) := by
  refine (Saux_norm_le n (lowaux n) t).trans ?_
  have hsum : (∑ k ∈ Finset.range (n+1), |lowaux n k|)
      = ∑ k ∈ (Finset.range (n+1)).filter (fun k => k^3 ≤ n), waux k := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro k _
    unfold lowaux
    split_ifs with h
    · exact abs_of_nonneg (waux_nonneg k)
    · simp
  rw [hsum]
  have h : ∀ k ∈ (Finset.range (n+1)).filter (fun k => k^3 ≤ n), waux k ≤ Real.log (n:ℝ) := by
    intro k hk
    have hk' := Finset.mem_filter.mp hk
    have hkn : k ≤ n := by have := Finset.mem_range.mp hk'.1; omega
    exact waux_le_log n k hkn hn
  have hcard := small_card n
  have hlog : 0 ≤ Real.log (n:ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  calc _ ≤ ∑ _k ∈ (Finset.range (n+1)).filter (fun k => k^3 ≤ n), Real.log (n:ℝ) :=
        Finset.sum_le_sum h
    _ = (((Finset.range (n+1)).filter (fun k => k^3 ≤ n)).card : ℝ) * Real.log (n:ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (Real.sqrt (n:ℝ)+1) * Real.log (n:ℝ) := by nlinarith

theorem Saux_high_bound (n : ℕ) (hn : 1 ≤ n) (t : ℝ) :
    ‖Saux n (highaux n) t‖ ≤ ((n:ℝ)+1) * Real.log (n:ℝ) := by
  refine (Saux_norm_le n (highaux n) t).trans ?_
  have h : ∀ k ∈ Finset.range (n+1), |highaux n k| ≤ |waux k| := by
    intro k _
    rw [abs_of_nonneg (highaux_nonneg n k), abs_of_nonneg (waux_nonneg k)]
    exact highaux_le n k
  have h2 : ∀ k ∈ Finset.range (n+1), |waux k| ≤ Real.log (n:ℝ) := by
    intro k hk
    have hkn : k ≤ n := by have := Finset.mem_range.mp hk; omega
    rw [abs_of_nonneg (waux_nonneg k)]
    exact waux_le_log n k hkn hn
  calc ∑ k ∈ Finset.range (n+1), |highaux n k| ≤ ∑ k ∈ Finset.range (n+1), |waux k| :=
        Finset.sum_le_sum h
    _ ≤ ∑ _k ∈ Finset.range (n+1), Real.log (n:ℝ) := Finset.sum_le_sum h2
    _ = ((Finset.range (n+1)).card : ℝ) * Real.log (n:ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = ((n:ℝ)+1) * Real.log (n:ℝ) := by rw [Finset.card_range]; push_cast; ring

theorem Saux_add (n : ℕ) (a b : ℕ → ℝ) (t : ℝ) :
    Saux n a t + Saux n b t = Saux n (fun k => a k + b k) t := by
  unfold Saux
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  push_cast
  ring

theorem waux_split (n k : ℕ) : highaux n k + lowaux n k = waux k := by
  unfold highaux
  ring

theorem Saux_waux_eq (n : ℕ) (t : ℝ) :
    Saux n waux t = Saux n (highaux n) t + Saux n (lowaux n) t := by
  have hsplit : (fun k => highaux n k + lowaux n k) = waux := by
    funext k
    exact waux_split n k
  rw [Saux_add, hsplit]

theorem Saux_waux_primeSum (n : ℕ) (t : ℝ) :
    Saux n waux t = GoldbachMajorArc.primeSum n t := by
  unfold Saux waux GoldbachMajorArc.primeSum GoldbachMajorArc.primeWeight
  rfl

theorem diff_bound (n : ℕ) (hn : 1 ≤ n) (t : ℝ) :
    ‖Saux n (highaux n) t * Saux n (highaux n) t * GoldbachMajorArc.phase (-(n:ℝ)*t)
      - GoldbachMajorArc.integrand n t‖
      ≤ 8 * (Real.sqrt (n:ℝ) * (n:ℝ)) * (Real.log (n:ℝ))^2 := by
  have hs := Saux_waux_eq n t
  have hSh := Saux_high_bound n hn t
  have hSf := Saux_waux_bound n hn t
  have hSl := Saux_low_bound n hn t
  have hph : ‖GoldbachMajorArc.phase (-(n:ℝ)*t)‖ = 1 := phase_norm _
  have hid : GoldbachMajorArc.integrand n t
      = Saux n waux t * Saux n waux t * GoldbachMajorArc.phase (-(n:ℝ)*t) := by
    unfold GoldbachMajorArc.integrand
    rw [Saux_waux_primeSum]
    ring
  rw [hid, show Saux n (highaux n) t * Saux n (highaux n) t * GoldbachMajorArc.phase (-(n:ℝ)*t)
      - Saux n waux t * Saux n waux t * GoldbachMajorArc.phase (-(n:ℝ)*t)
      = ((Saux n (highaux n) t - Saux n waux t) * (Saux n (highaux n) t + Saux n waux t))
        * GoldbachMajorArc.phase (-(n:ℝ)*t) by ring,
    norm_mul, hph, mul_one, norm_mul]
  have h1 : ‖Saux n (highaux n) t - Saux n waux t‖ = ‖Saux n (lowaux n) t‖ := by
    rw [hs]
    rw [show Saux n (highaux n) t - (Saux n (highaux n) t + Saux n (lowaux n) t)
        = -(Saux n (lowaux n) t) by ring, norm_neg]
  rw [h1]
  have h2 : ‖Saux n (highaux n) t + Saux n waux t‖ ≤ 2 * (((n:ℝ)+1) * Real.log (n:ℝ)) := by
    calc _ ≤ ‖Saux n (highaux n) t‖ + ‖Saux n waux t‖ := norm_add_le _ _
      _ ≤ _ := by linarith
  have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hsqrt1 : 1 ≤ Real.sqrt (n:ℝ) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hn1
  have hL0 : 0 ≤ Real.log (n:ℝ) := Real.log_nonneg hn1
  calc ‖Saux n (lowaux n) t‖ * ‖Saux n (highaux n) t + Saux n waux t‖
      ≤ ((Real.sqrt (n:ℝ)+1) * Real.log (n:ℝ)) * (2*(((n:ℝ)+1) * Real.log (n:ℝ))) := by
        exact mul_le_mul hSl h2 (norm_nonneg _) (mul_nonneg (by positivity) hL0)
    _ = 2 * ((Real.sqrt (n:ℝ)+1) * ((n:ℝ)+1)) * (Real.log (n:ℝ))^2 := by ring
    _ ≤ 2 * ((2*Real.sqrt (n:ℝ)) * (2*(n:ℝ))) * (Real.log (n:ℝ))^2 := by
        have hA : (Real.sqrt (n:ℝ)+1) * ((n:ℝ)+1) ≤ (2*Real.sqrt (n:ℝ)) * (2*(n:ℝ)) := by
          nlinarith [mul_nonneg (sub_nonneg.mpr hsqrt1) (sub_nonneg.mpr hn1),
            Real.sqrt_nonneg (n:ℝ), Real.mul_self_sqrt (Nat.cast_nonneg n)]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hA (by norm_num)) (sq_nonneg _)
    _ = 8 * (Real.sqrt (n:ℝ) * (n:ℝ)) * (Real.log (n:ℝ))^2 := by ring

/-! ### The measure of the major arcs -/

theorem indicator_ii {f : ℝ → ℂ} {s : Set ℝ} (hs : MeasurableSet s) (hf : Continuous f)
    (a b : ℝ) : IntervalIntegrable (s.indicator f) volume a b :=
  ⟨(hf.intervalIntegrable a b).1.indicator hs, (hf.intervalIntegrable a b).2.indicator hs⟩

theorem indicator_ii_real {f : ℝ → ℝ} {s : Set ℝ} (hs : MeasurableSet s) (hf : Continuous f)
    (a b : ℝ) : IntervalIntegrable (s.indicator f) volume a b :=
  ⟨(hf.intervalIntegrable a b).1.indicator hs, (hf.intervalIntegrable a b).2.indicator hs⟩

theorem arcs_sum_bound (n : ℕ) (hn : 0 < n) :
    (∑ q ∈ Finset.Icc 1 (cutoff n), ∑ a ∈ Finset.range (q+1), 2*width n q)
      ≤ 4*(cutoff n:ℝ)^2/(n:ℝ) := by
  have hn' : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have hstep : ∀ q ∈ Finset.Icc 1 (cutoff n),
      (∑ a ∈ Finset.range (q+1), 2*width n q) ≤ 4*(cutoff n:ℝ)/(n:ℝ) := by
    intro q hq
    have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
    have hqpos : (0:ℝ) < (q:ℝ) := by exact_mod_cast (by omega : 0 < q)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hcard : (((q+1):ℕ):ℝ) = (q:ℝ)+1 := by push_cast; ring
    rw [hcard]
    have hq1' : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq1
    have hb : ((q:ℝ)+1)/(q:ℝ) ≤ 2 := by
      rw [div_le_iff₀ hqpos]
      linarith
    have hrw : ((q:ℝ)+1) * (2*width n q)
        = (2*(cutoff n:ℝ)/(n:ℝ)) * (((q:ℝ)+1)/(q:ℝ)) := by
      unfold width
      field_simp <;> ring
    rw [hrw]
    calc _ ≤ (2*(cutoff n:ℝ)/(n:ℝ)) * 2 :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ = 4*(cutoff n:ℝ)/(n:ℝ) := by ring
  calc ∑ q ∈ Finset.Icc 1 (cutoff n), ∑ a ∈ Finset.range (q+1), 2*width n q
      ≤ ∑ q ∈ Finset.Icc 1 (cutoff n), (4*(cutoff n:ℝ)/(n:ℝ)) :=
        Finset.sum_le_sum hstep
    _ = ((Finset.Icc 1 (cutoff n)).card : ℝ) * (4*(cutoff n:ℝ)/(n:ℝ)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (cutoff n:ℝ) * (4*(cutoff n:ℝ)/(n:ℝ)) := by
        have hcard : ((Finset.Icc 1 (cutoff n)).card : ℝ) ≤ (cutoff n:ℝ) := by
          rw [Nat.card_Icc]
          have h : cutoff n + 1 - 1 = cutoff n := by omega
          rw [h]
        exact mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = 4*(cutoff n:ℝ)^2/(n:ℝ) := by ring

private theorem ofReal_sum_aux (s : Finset ℕ) (f : ℕ → ℝ) (hf : ∀ i, 0 ≤ f i) :
    ∑ i ∈ s, ENNReal.ofReal (f i) = ENNReal.ofReal (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha,
        ENNReal.ofReal_add (hf a) (Finset.sum_nonneg fun i _ => hf i), ih]

theorem arcs_volume (n : ℕ) (hn : 0 < n) :
    volume (Set.Icc 0 1 ∩ arcs n) ≤ ENNReal.ofReal (4*(cutoff n:ℝ)^2/(n:ℝ)) := by
  have hsub : Set.Icc 0 1 ∩ arcs n ⊆
      ⋃ q ∈ Finset.Icc 1 (cutoff n), ⋃ a ∈ Finset.range (q+1), window n q a := by
    intro t ht
    obtain ⟨q, a, hq1, hqQ, ha, hc, habs⟩ := ht.2
    refine Set.mem_iUnion.mpr ⟨q, ?_⟩
    refine Set.mem_iUnion.mpr ⟨Finset.mem_Icc.mpr ⟨hq1, hqQ⟩, ?_⟩
    refine Set.mem_iUnion.mpr ⟨a, ?_⟩
    refine Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩
    exact (mem_window n q a t).mpr habs
  have h1 : volume (Set.Icc 0 1 ∩ arcs n)
      ≤ ∑ q ∈ Finset.Icc 1 (cutoff n), ∑ a ∈ Finset.range (q+1), volume (window n q a) := by
    refine (measure_mono hsub).trans ?_
    refine (measure_biUnion_finset_le (Finset.Icc 1 (cutoff n)) _).trans ?_
    apply Finset.sum_le_sum
    intro q hq
    exact measure_biUnion_finset_le (Finset.range (q+1)) (fun a => window n q a)
  have h2 : ∀ q ∈ Finset.Icc 1 (cutoff n), ∀ a ∈ Finset.range (q+1),
      volume (window n q a) = ENNReal.ofReal (2*width n q) := by
    intro q hq a ha
    unfold window
    rw [Real.volume_Icc]
    congr 1
    ring
  have hinner : ∀ q ∈ Finset.Icc 1 (cutoff n),
      (∑ a ∈ Finset.range (q+1), volume (window n q a))
        = ENNReal.ofReal (∑ a ∈ Finset.range (q+1), 2*width n q) := by
    intro q hq
    rw [Finset.sum_congr rfl (h2 q hq)]
    exact ofReal_sum_aux _ _ (fun a => mul_nonneg (by norm_num) (width_nonneg n q))
  have h3 : (∑ q ∈ Finset.Icc 1 (cutoff n), ∑ a ∈ Finset.range (q+1), volume (window n q a))
      = ENNReal.ofReal (∑ q ∈ Finset.Icc 1 (cutoff n), ∑ a ∈ Finset.range (q+1), 2*width n q) := by
    calc (∑ q ∈ Finset.Icc 1 (cutoff n), ∑ a ∈ Finset.range (q+1), volume (window n q a))
        = ∑ q ∈ Finset.Icc 1 (cutoff n),
            ENNReal.ofReal (∑ a ∈ Finset.range (q+1), 2*width n q) :=
          Finset.sum_congr rfl hinner
      _ = ENNReal.ofReal (∑ q ∈ Finset.Icc 1 (cutoff n), ∑ a ∈ Finset.range (q+1), 2*width n q) :=
          ofReal_sum_aux _ _
            (fun q => Finset.sum_nonneg fun a _ => mul_nonneg (by norm_num) (width_nonneg n q))
  rw [h3] at h1
  exact h1.trans (ENNReal.ofReal_le_ofReal (arcs_sum_bound n hn))

theorem arcs_measure (n : ℕ) (hn : 0 < n) :
    (volume (Set.Icc 0 1 ∩ arcs n)).toReal ≤ 4*(cutoff n:ℝ)^2/(n:ℝ) := by
  have h := arcs_volume n hn
  have hfin : ENNReal.ofReal (4*(cutoff n:ℝ)^2/(n:ℝ)) ≠ ⊤ := ENNReal.ofReal_ne_top
  have := ENNReal.toReal_mono hfin h
  rwa [ENNReal.toReal_ofReal (by positivity)] at this

/-! ### The high-prime major arc against the full-prime major arc -/

theorem majHigh_sub_major (n : ℕ) (hn : 1 ≤ n) :
    ‖majHigh n - majorContribution n‖
      ≤ 32 * (Real.sqrt (n:ℝ)) * (Real.log (n:ℝ))^2 * (cutoff n:ℝ)^2 := by
  have hmeas := arcs_measurable n
  have hC0 : 0 ≤ 8 * (Real.sqrt (n:ℝ) * (n:ℝ)) * (Real.log (n:ℝ))^2 := by positivity
  have hc1 : Continuous (Saux n (highaux n)) := continuous_Saux n (highaux n)
  have hc2 : Continuous (GoldbachMajorArc.integrand n) := by
    unfold GoldbachMajorArc.integrand GoldbachMajorArc.primeSum GoldbachMajorArc.phase
    fun_prop
  have hcp : Continuous (fun u : ℝ => GoldbachMajorArc.phase (-(n:ℝ)*u)) := by
    unfold GoldbachMajorArc.phase
    fun_prop
  have hfull : Continuous (fun u => Saux n (highaux n) u * Saux n (highaux n) u
      * GoldbachMajorArc.phase (-(n:ℝ)*u)) := (hc1.mul hc1).mul hcp
  have hD : Continuous (fun u => Saux n (highaux n) u * Saux n (highaux n) u
      * GoldbachMajorArc.phase (-(n:ℝ)*u) - GoldbachMajorArc.integrand n u) := hfull.sub hc2
  have hrew : majHigh n - majorContribution n
      = ∫ t in (0:ℝ)..1, (arcs n).indicator (fun u => Saux n (highaux n) u * Saux n (highaux n) u
        * GoldbachMajorArc.phase (-(n:ℝ)*u) - GoldbachMajorArc.integrand n u) t := by
    unfold majHigh majArc majorContribution
    rw [← intervalIntegral.integral_sub (indicator_ii hmeas hfull 0 1) (indicator_ii hmeas hc2 0 1)]
    apply intervalIntegral.integral_congr
    intro t _
    by_cases ht : t ∈ arcs n <;> simp [ht]
  rw [hrew]
  calc ‖∫ t in (0:ℝ)..1, (arcs n).indicator (fun u => Saux n (highaux n) u
        * Saux n (highaux n) u * GoldbachMajorArc.phase (-(n:ℝ)*u)
        - GoldbachMajorArc.integrand n u) t‖
      ≤ ∫ t in (0:ℝ)..1, ‖(arcs n).indicator (fun u => Saux n (highaux n) u
        * Saux n (highaux n) u * GoldbachMajorArc.phase (-(n:ℝ)*u)
        - GoldbachMajorArc.integrand n u) t‖ :=
        intervalIntegral.norm_integral_le_integral_norm zero_le_one
    _ ≤ ∫ t in (0:ℝ)..1, (arcs n).indicator
        (fun _ : ℝ => 8 * (Real.sqrt (n:ℝ) * (n:ℝ)) * (Real.log (n:ℝ))^2) t := by
        apply intervalIntegral.integral_mono_on zero_le_one
        · exact ⟨((hD.intervalIntegrable 0 1).1.indicator hmeas).norm,
            ((hD.intervalIntegrable 0 1).2.indicator hmeas).norm⟩
        · exact indicator_ii_real hmeas continuous_const 0 1
        · intro t _
          by_cases ht : t ∈ arcs n
          · simp only [Set.indicator_of_mem ht]
            exact diff_bound n hn t
          · simp [Set.indicator_of_notMem ht]
    _ = (volume (Set.Icc 0 1 ∩ arcs n)).toReal
        * (8 * (Real.sqrt (n:ℝ) * (n:ℝ)) * (Real.log (n:ℝ))^2) := by
        rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc,
          setIntegral_indicator hmeas, setIntegral_const]
        simp [Measure.real, smul_eq_mul]
    _ ≤ (4*(cutoff n:ℝ)^2/(n:ℝ)) * (8 * (Real.sqrt (n:ℝ) * (n:ℝ)) * (Real.log (n:ℝ))^2) := by
        exact mul_le_mul_of_nonneg_right (arcs_measure n (by omega)) hC0
    _ = 32 * (Real.sqrt (n:ℝ)) * (Real.log (n:ℝ))^2 * (cutoff n:ℝ)^2 := by
        have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast (by omega : 0 < n).ne'
        field_simp <;> ring

/-! ### Growth of the error terms -/

theorem log_pow_div_rpow (k : ℕ) (s : ℝ) (hs : 0 < s) :
    Tendsto (fun n : ℕ => (Real.log (n:ℝ))^k / (n:ℝ)^s) atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_rpow_atTop (k:ℝ) hs).tendsto_div_nhds_zero.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  simpa only [Function.comp_def, Real.rpow_natCast] using h

theorem log_pow_div (k : ℕ) : Tendsto (fun n : ℕ => (Real.log (n:ℝ))^k / (n:ℝ)) atTop (𝓝 0) := by
  have h := log_pow_div_rpow k 1 (by norm_num)
  simpa only [Real.rpow_one] using h

theorem log_pow_div_sqrt (k : ℕ) :
    Tendsto (fun n : ℕ => (Real.log (n:ℝ))^k / Real.sqrt (n:ℝ)) atTop (𝓝 0) := by
  have h := log_pow_div_rpow k ((1:ℝ)/2) (by norm_num)
  have h2 : (fun n : ℕ => (Real.log (n:ℝ))^k / (n:ℝ)^((1:ℝ)/2))
      = (fun n : ℕ => (Real.log (n:ℝ))^k / Real.sqrt (n:ℝ)) := by
    funext n
    rw [Real.sqrt_eq_rpow]
  rwa [h2] at h

theorem gap_bound (n : ℕ) (hn : 1 ≤ n) (hsep : 2*(cutoff n)^2 < n) :
    |(majHigh n).re - Maux n|
      ≤ totalArcError n + (4*Real.pi+6)*(cutoff n:ℝ)^3
        + 32*(Real.sqrt (n:ℝ))*(Real.log (n:ℝ))^2*(cutoff n:ℝ)^2 := by
  have h1 := majHigh_sub_major n hn
  have h2 := major_error hsep
  have h3 := model_gap n (by omega)
  have h4 : |(majHigh n).re - (majorContribution n).re| ≤ ‖majHigh n - majorContribution n‖ := by
    rw [← Complex.sub_re]
    exact Complex.abs_re_le_norm _
  have h5 : |(majorContribution n).re - (modeledContribution n).re|
      ≤ ‖majorContribution n - modeledContribution n‖ := by
    rw [← Complex.sub_re]
    exact Complex.abs_re_le_norm _
  calc |(majHigh n).re - Maux n|
      ≤ |(majHigh n).re - (majorContribution n).re|
          + |(majorContribution n).re - (modeledContribution n).re|
          + |(modeledContribution n).re - Maux n| := by
        have hA := abs_sub_le ((majHigh n).re) ((majorContribution n).re) (Maux n)
        have hB := abs_sub_le ((majorContribution n).re) ((modeledContribution n).re) (Maux n)
        linarith [abs_nonneg ((majHigh n).re - (majorContribution n).re)]
    _ ≤ _ := by linarith

theorem gap_eventually (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, 2*(cutoff n)^2 < n ∧ |(majHigh n).re - Maux n| ≤ δ*(n:ℝ) := by
  have hsep := cutoff_separated
  have h1 := totalArcError_sublinear.eventually_lt_const (by linarith : (0:ℝ) < δ/3)
  have h2 := (log_pow_div 6).eventually_lt_const
    (by positivity : (0:ℝ) < δ/(3*(4*Real.pi+6)*4096))
  have h3 := (log_pow_div_sqrt 6).eventually_lt_const (by positivity : (0:ℝ) < δ/(3*8192))
  have h4 : ∀ᶠ n : ℕ in atTop, 2 ≤ n := eventually_ge_atTop 2
  filter_upwards [hsep, h1, h2, h3, h4] with n hsepn h1n h2n h3n h4n
  refine ⟨hsepn, ?_⟩
  have hn0 : (0:ℝ) < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hL0 : 0 ≤ Real.log (n:ℝ) := Real.log_nonneg hn1
  have hQ := cutoff_le_log_sq h4n
  have hQ0 : (0:ℝ) ≤ (cutoff n:ℝ) := Nat.cast_nonneg _
  have hp3 := pow_le_pow_left₀ hQ0 hQ 3
  have hp2 := pow_le_pow_left₀ hQ0 hQ 2
  have hQ3 : (cutoff n:ℝ)^3 ≤ 4096 * (Real.log (n:ℝ))^6 := by nlinarith [hp3]
  have hQ2 : (cutoff n:ℝ)^2 ≤ 256 * (Real.log (n:ℝ))^4 := by nlinarith [hp2]
  have hs0 : 0 < Real.sqrt (n:ℝ) := Real.sqrt_pos.2 hn0
  have hE1 : totalArcError n ≤ (δ/3)*n := by
    have := (div_lt_iff₀ hn0).mp h1n
    linarith
  have hE2 : (4*Real.pi+6)*(cutoff n:ℝ)^3 ≤ (δ/3)*n := by
    have hK : 0 < 4*Real.pi+6 := by positivity
    have hL6 : (Real.log (n:ℝ))^6 ≤ (δ/(3*(4*Real.pi+6)*4096)) * n := by
      have := (div_lt_iff₀ hn0).mp h2n
      linarith
    have hA1 : (4*Real.pi+6)*(cutoff n:ℝ)^3
        ≤ (4*Real.pi+6)*(4096*(Real.log (n:ℝ))^6) :=
      mul_le_mul_of_nonneg_left hQ3 hK.le
    have hA2 : (4*Real.pi+6)*(4096*(Real.log (n:ℝ))^6)
        ≤ (4*Real.pi+6)*(4096*((δ/(3*(4*Real.pi+6)*4096)) * n)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hL6 (by norm_num)) hK.le
    calc (4*Real.pi+6)*(cutoff n:ℝ)^3 ≤ (4*Real.pi+6)*(4096*(Real.log (n:ℝ))^6) := hA1
      _ ≤ (4*Real.pi+6)*(4096*((δ/(3*(4*Real.pi+6)*4096)) * n)) := hA2
      _ = (δ/3)*n := by field_simp [hK.ne'] <;> ring
  have hE3 : 32*(Real.sqrt (n:ℝ))*(Real.log (n:ℝ))^2*(cutoff n:ℝ)^2 ≤ (δ/3)*n := by
    have hL6 : (Real.log (n:ℝ))^6 ≤ (δ/(3*8192)) * Real.sqrt (n:ℝ) := by
      have := (div_lt_iff₀ hs0).mp h3n
      linarith
    have hsq := Real.mul_self_sqrt (Nat.cast_nonneg n)
    have hB1 : (0:ℝ) ≤ 32*(Real.sqrt (n:ℝ))*(Real.log (n:ℝ))^2 := by positivity
    have hstep : 32*(Real.sqrt (n:ℝ))*(Real.log (n:ℝ))^2*(cutoff n:ℝ)^2
        ≤ 32*(Real.sqrt (n:ℝ))*(Real.log (n:ℝ))^2*(256*(Real.log (n:ℝ))^4) := by
      nlinarith [hQ2, hB1]
    have hstep' : 32*(Real.sqrt (n:ℝ))*(Real.log (n:ℝ))^2*(cutoff n:ℝ)^2
        ≤ 8192*(Real.sqrt (n:ℝ))*(Real.log (n:ℝ))^6 := by
      calc _ ≤ 32*(Real.sqrt (n:ℝ))*(Real.log (n:ℝ))^2*(256*(Real.log (n:ℝ))^4) := hstep
        _ = 8192*(Real.sqrt (n:ℝ))*(Real.log (n:ℝ))^6 := by ring
    have hB2 : (0:ℝ) ≤ 8192*(Real.sqrt (n:ℝ)) := by positivity
    have hstep2 : 8192*(Real.sqrt (n:ℝ))*(Real.log (n:ℝ))^6
        ≤ 8192*(Real.sqrt (n:ℝ))*((δ/(3*8192)) * Real.sqrt (n:ℝ)) := by
      nlinarith [hL6, hB2]
    calc 32*(Real.sqrt (n:ℝ))*(Real.log (n:ℝ))^2*(cutoff n:ℝ)^2
        ≤ 8192*(Real.sqrt (n:ℝ))*(Real.log (n:ℝ))^6 := hstep'
      _ ≤ 8192*(Real.sqrt (n:ℝ))*((δ/(3*8192)) * Real.sqrt (n:ℝ)) := hstep2
      _ = (δ/3)*(n:ℝ) := by
          calc 8192*(Real.sqrt (n:ℝ))*((δ/(3*8192)) * Real.sqrt (n:ℝ))
              = (δ/3) * (Real.sqrt (n:ℝ) * Real.sqrt (n:ℝ)) := by ring
            _ = (δ/3)*(n:ℝ) := by rw [hsq]
  have := gap_bound n (by omega) hsepn
  linarith

theorem smallR_eventually (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, Raux n - Rhighaux n ≤ δ*(n:ℝ) := by
  have h := (log_pow_div_sqrt 2).eventually_lt_const (by linarith : (0:ℝ) < δ/4)
  have h1 : ∀ᶠ n : ℕ in atTop, 1 ≤ n := eventually_ge_atTop 1
  filter_upwards [h, h1] with n hn hn1
  have hR := RminusRhigh n hn1
  have hn0 : (0:ℝ) < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hs0 : 0 < Real.sqrt (n:ℝ) := Real.sqrt_pos.2 hn0
  have hsq := Real.mul_self_sqrt (Nat.cast_nonneg n)
  have hL : (Real.log (n:ℝ))^2 ≤ (δ/4) * Real.sqrt (n:ℝ) := by
    have := (div_lt_iff₀ hs0).mp hn
    linarith
  have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn1
  have hsqrt1 : 1 ≤ Real.sqrt (n:ℝ) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hn1
  nlinarith [hR, hL, hsq, hs0.le, hsqrt1]

/-! ### The equivalence -/

theorem fwd (h : ∀ e:ℝ, 0<e → ∃ N:ℕ, ∀ n ≥ N, Even n →
      -(e*(n:ℝ)) ≤ (Iaux n (highaux n) (highaux n)).re)
    (ε : ℝ) (hε : 0 < ε) : ∃ N:ℕ, ∀ n ≥ N, Even n → Maux n ≤ Raux n + ε*(n:ℝ) := by
  obtain ⟨N₀, hN₀⟩ := h (ε/4) (by linarith)
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.1 (gap_eventually (ε/4) (by linarith))
  refine ⟨max N₀ N₁, ?_⟩
  intro n hn heven
  have hn0 : N₀ ≤ n := le_of_max_le_left hn
  have hn1 : N₁ ≤ n := le_of_max_le_right hn
  obtain ⟨hsep, hgap⟩ := hN₁ n hn1
  have hL := hN₀ n hn0 heven
  rw [Iaux_re] at hL
  have hR := Rhighaux_le_Raux n
  have hM : Maux n ≤ (majHigh n).re + |(majHigh n).re - Maux n| := by
    have := neg_le_abs ((majHigh n).re - Maux n)
    linarith
  have hpos : (0:ℝ) ≤ (ε/2)*(n:ℝ) :=
    mul_nonneg (by linarith : (0:ℝ) ≤ ε/2) (Nat.cast_nonneg n)
  linarith

theorem bwd (h : ∀ ε:ℝ, 0<ε → ∃ N:ℕ, ∀ n≥N, Even n → Maux n ≤ Raux n + ε*(n:ℝ))
    (e : ℝ) (he : 0 < e) : ∃ N:ℕ, ∀ n≥N, Even n →
      -(e*(n:ℝ)) ≤ (Iaux n (highaux n) (highaux n)).re := by
  obtain ⟨N₀, hN₀⟩ := h (e/3) (by linarith)
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.1 (gap_eventually (e/3) (by linarith))
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.1 (smallR_eventually (e/3) (by linarith))
  refine ⟨max (max N₀ N₁) N₂, ?_⟩
  intro n hn heven
  have hn0 : N₀ ≤ n := le_of_max_le_left (le_of_max_le_left hn)
  have hn1 : N₁ ≤ n := le_of_max_le_right (le_of_max_le_left hn)
  have hn2 : N₂ ≤ n := le_of_max_le_right hn
  obtain ⟨hsep, hgap⟩ := hN₁ n hn1
  have hM := hN₀ n hn0 heven
  have hsmall := hN₂ n hn2
  rw [Iaux_re]
  have hG : (majHigh n).re ≤ Maux n + |(majHigh n).re - Maux n| := by
    have := le_abs_self ((majHigh n).re - Maux n)
    linarith
  linarith

theorem equivalence :
    (∀ e:ℝ, 0<e → ∃ N:ℕ, ∀ n ≥ N, Even n →
      -(e*(n:ℝ)) ≤ (Iaux n (highaux n) (highaux n)).re) ↔
    (∀ ε:ℝ, 0<ε → ∃ N:ℕ, ∀ n≥N, Even n → Maux n ≤ Raux n + ε*(n:ℝ)) :=
  ⟨fun h ε hε => fwd h ε hε, fun h e he => bwd h e he⟩

end
end Glue
end MovingBulk.Original

/- Project proof adapted from Estermann, revision 919c3e44522724be404d6ddb33022e34e996b687 (Apache-2.0). Original attributions preserved. -/

namespace MovingBulk.Frozen

/-! The short blocks use a central prime interval that moves with the target block. Its Fourier
sum is the difference of two prime sums. At each rational arc its model Dirichlet kernel
has a translated phase, and its two interval endpoints obey common major and minor estimates.
The on-block correlation estimate follows from finite Fourier orthogonality and Bessel.
The analytic background below incorporates the credited major-arc and Vaughan developments. -/
section

/-!
# Major-arc estimates for the prime logarithmic sum

The general finite estimates below are from DFQDZZ, goldbach-proofs PR #316,
revision e4ab24712555ae8c2c926adf19d368a9fb392c35 (Apache-2.0).

The analytic material in the namespaces OAI.LargePrimeGaps is selected and adapted
from OpenAI's openai/math, lean/OAI/NumberTheory/PrimeGaps, at revision
f5702854040e97fa7675c21ba37a9608f5f92dd3, licensed under Apache 2.0 (see LICENSE).
It is specialized to the declarations required for the small-modulus estimate and
ported from toolchain 4.34.1 to the version locked by this repository.
-/

section

-- Source module: CharacterErrors
namespace OAI
namespace LargePrimeGaps
open Filter
open Set Filter MeasureTheory
open scoped Topology ContDiff
open Asymptotics
open scoped Classical
open scoped ContDiff
open Topology
open scoped Convolution ContDiff Pointwise
noncomputable def primeCharacterPrefix (x : ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ n∈Finset.Ioc 0 ⌊x⌋₊, χ (n:ZMod q)*(ArithmeticFunction.vonMangoldt n:ℂ)

noncomputable def primeCharacterError (x : ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) : ℂ :=
  primeCharacterPrefix x χ-if χ=1 then (x:ℂ) else 0

end LargePrimeGaps
end OAI

-- Source module: ConductorBounds
namespace OAI
namespace LargePrimeGaps
open Filter
open Set Filter MeasureTheory
open scoped Topology ContDiff
open Asymptotics
open scoped Classical
open scoped ContDiff
open Topology
open scoped Convolution ContDiff Pointwise
open scoped ComplexConjugate
open Filter Topology
def SiegelWalfisz : Prop :=
  ∀ A B : ℝ, 0 < A → 0 < B → ∃ M : ℝ, 0 < M ∧ ∃ x₀ : ℝ, 1 < x₀ ∧
    ∀ x : ℝ, x₀ ≤ x → ∀ d : ℕ, 0 < d → (d:ℝ) ≤ (Real.log x)^B →
      ∀ χ : DirichletCharacter ℂ d, χ.IsPrimitive →
        ‖primeCharacterError x χ‖ ≤ M*x*(Real.log x)^(-A)

theorem eventually_log_rpow_le_rpow (a : ℝ) {s : ℝ} (hs : 0 < s) :
    ∀ᶠ x : ℝ in atTop, (Real.log x)^a ≤ x^s := by
  filter_upwards [(isLittleO_log_rpow_rpow_atTop a hs).bound (by norm_num : (0:ℝ)<1),
    eventually_ge_atTop (1:ℝ)] with x h hx
  simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Real.log_nonneg hx) _),
    abs_of_nonneg (Real.rpow_nonneg (by linarith : 0≤x) _),one_mul] using h

end LargePrimeGaps
end OAI

-- Source module: LogParameters
namespace OAI
namespace LargePrimeGaps
open Filter
open Set Filter MeasureTheory
open scoped Topology ContDiff
open Asymptotics
open scoped Classical
open scoped ContDiff
open Topology
open scoped Convolution ContDiff Pointwise
open scoped ComplexConjugate
open Filter Topology
open Complex Filter Topology
noncomputable def poleRemovedL {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) : ℂ → ℂ :=
  if χ = 1 then DirichletCharacter.LFunctionTrivChar₁ q else χ.LFunction

noncomputable def primeLogDerivativeRegular {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  -deriv (poleRemovedL χ) s / poleRemovedL χ s

theorem poleRemovedL_differentiable {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) : Differentiable ℂ (poleRemovedL χ) := by
  unfold poleRemovedL
  split_ifs with hχ
  · exact DirichletCharacter.differentiable_LFunctionTrivChar₁ q
  · exact DirichletCharacter.differentiable_LFunction hχ

theorem poleRemovedL_ne_zero {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 ≤ s.re) :
    poleRemovedL χ s ≠ 0 := by
  unfold poleRemovedL
  split_ifs with hχ
  · rcases eq_or_ne s 1 with rfl | hs1
    · exact DirichletCharacter.LFunctionTrivChar₁_apply_one_ne_zero q
    · rw [DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hs1]
      refine mul_ne_zero (sub_ne_zero.mpr hs1) ?_
      exact DirichletCharacter.LFunction_ne_zero_of_one_le_re 1 (.inr hs1) hs
  · exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (.inl hχ) hs

theorem primeLogDerivativeRegular_analyticAt {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : poleRemovedL χ s ≠ 0) :
    AnalyticAt ℂ (primeLogDerivativeRegular χ) s := by
  have h := (poleRemovedL_differentiable χ).analyticAt s
  exact h.deriv.neg.div h hs

theorem primeLogDerivativeRegular_eq {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    primeLogDerivativeRegular χ s =
      LSeries (fun n : ℕ => χ (n : ZMod q) * (ArithmeticFunction.vonMangoldt n : ℂ)) s -
        (if χ = 1 then 1 / (s - 1) else 0) := by
  have hs1 : s ≠ 1 := by intro h; simp [h] at hs
  have hL := DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hs
  change LSeries (fun n : ℕ => χ (n : ZMod q) * (ArithmeticFunction.vonMangoldt n : ℂ)) s =
    -deriv (LSeries (fun n : ℕ => χ (n : ZMod q))) s /
      LSeries (fun n : ℕ => χ (n : ZMod q)) s at hL
  rw [hL, ← DirichletCharacter.LFunction_eq_LSeries χ hs,
    ← DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ hs]
  by_cases hχ : χ = 1
  · subst χ
    have hn := DirichletCharacter.LFunction_ne_zero_of_one_le_re
      (1 : DirichletCharacter ℂ q) (.inr hs1) hs.le
    simp only [primeLogDerivativeRegular, poleRemovedL, ↓reduceIte]
    rw [DirichletCharacter.deriv_LFunctionTrivChar₁_apply_of_ne_one q hs1,
      DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hs1]
    change -((s-1)*deriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)) s +
      DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) s) /
      ((s-1)*DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) s) = _
    field_simp
    ring
  · simp [primeLogDerivativeRegular, poleRemovedL, hχ]

end LargePrimeGaps
end OAI

-- Source module: DirichletGrowth
namespace OAI
namespace LargePrimeGaps
open Filter
open Set Filter MeasureTheory
open scoped Topology ContDiff
open Asymptotics
open scoped Classical
open scoped ContDiff
open Topology
open scoped Convolution ContDiff Pointwise
open scoped ComplexConjugate
open Filter Topology
open Complex Filter Topology
open Complex Filter Topology Set MeasureTheory Asymptotics
noncomputable def discrepancyTail (A : ℝ → ℂ) (u : ℝ) (s : ℂ) : ℂ :=
  ∫ t in Ioi u, A t * (t:ℂ)^(-(s+1))

lemma discrepancyTail_integrable {A : ℝ → ℂ} {u D : ℝ} (hu : 0 < u) (hD : 0 ≤ D)
    (hA : Measurable A) (hbound : ∀ t, u < t → ‖A t‖ ≤ D) {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun t => A t * (t:ℂ)^(-(s+1))) (Ioi u) := by
  have hp : (-(s+1)).re < -1 := by simp only [neg_re,add_re,one_re]; linarith
  have hi := (integrableOn_Ioi_norm_cpow_of_lt hp hu).const_mul D
  have hm := (integrableOn_Ioi_cpow_of_lt hp hu).aestronglyMeasurable
  refine hi.mono (hA.aestronglyMeasurable.restrict.mul hm) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hD (norm_nonneg _))]
  exact mul_le_mul_of_nonneg_right (hbound t ht) (norm_nonneg _)

lemma discrepancyTail_norm_le {A : ℝ → ℂ} {u D : ℝ} (hu : 0 < u) (_hD : 0 ≤ D)
    (_hA : Measurable A) (hbound : ∀ t, u < t → ‖A t‖ ≤ D) {s : ℂ} (hs : 0 < s.re) :
    ‖discrepancyTail A u s‖ ≤ D * u^(-s.re)/s.re := by
  have hi := (integrableOn_Ioi_rpow_of_lt (by linarith : -s.re-1 < -1) hu).const_mul D
  calc
    _ ≤ ∫ t in Ioi u, D*t^(-s.re-1) := by
      apply norm_integral_le_of_norm_le hi
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [norm_mul, norm_cpow_eq_rpow_re_of_pos (hu.trans ht)]
      simp only [neg_re,add_re,one_re,neg_add_rev]
      have he : -1 + -s.re = -s.re-1 := by ring
      rw [he]
      exact mul_le_mul_of_nonneg_right (hbound t ht) (Real.rpow_nonneg (hu.trans ht).le _)
    _ = _ := by
      rw [integral_const_mul,integral_Ioi_rpow_of_lt (by linarith : -s.re-1 < -1) hu]
      ring_nf

lemma discrepancyTail_eq_mellin {A : ℝ → ℂ} {u : ℝ} (hu : 0 ≤ u) (s : ℂ) :
    discrepancyTail A u s = mellin ((Ioi u).indicator A) (-s) := by
  rw [mellin]
  simp_rw [←Set.indicator_smul]
  rw [integral_indicator measurableSet_Ioi,Measure.restrict_restrict measurableSet_Ioi]
  have he : Ioi u ∩ Ioi 0 = Ioi u := Set.inter_eq_left.mpr (fun t ht => hu.trans_lt ht)
  rw [he]
  unfold discrepancyTail
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  simp only [smul_eq_mul]
  rw [mul_comm]
  congr 2
  ring

lemma discrepancyTail_differentiableAt {A : ℝ → ℂ} {u D : ℝ} (hu : 0 < u) (hD : 0 ≤ D)
    (hA : Measurable A) (hbound : ∀ t, u < t → ‖A t‖ ≤ D) {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (discrepancyTail A u) s := by
  let B := (Ioi u).indicator A
  have hm : Measurable B := hA.indicator measurableSet_Ioi
  have hb : ∀ t, ‖B t‖ ≤ D := by
    intro t
    by_cases ht : u < t
    · simpa [B,ht] using hbound t ht
    · simpa [B,ht] using hD
  have hloc : LocallyIntegrableOn B (Ioi 0) :=
    ((locallyIntegrable_const D).mono hm.aestronglyMeasurable
      (.of_forall (fun t => (hb t).trans (le_abs_self D)))).locallyIntegrableOn _
  have htop : B =O[atTop] (fun t : ℝ => t^(-(0:ℝ))) := by
    refine isBigO_iff.mpr ⟨D,Eventually.of_forall ?_⟩
    intro t
    simpa using hb t
  have hbot : B =O[𝓝[>] 0] (fun t : ℝ => t^(-(-s.re-1))) := by
    refine isBigO_iff.mpr ⟨0,?_⟩
    filter_upwards [nhdsWithin_le_nhds (gt_mem_nhds hu)] with t ht
    simp [B,not_lt.mpr ht.le]
  have hd := mellin_differentiableAt_of_isBigO_rpow hloc htop
    (by simpa using hs : (-s).re < 0) hbot (by simp : -s.re-1 < (-s).re)
  have he : discrepancyTail A u = fun z => mellin B (-z) := funext (discrepancyTail_eq_mellin hu.le)
  rw [he]
  exact hd.comp s differentiableAt_id.neg

open Finset
lemma periodic_sum_norm_le {f : ℕ → ℂ} {q : ℕ} (hq : 0 < q)
    (hp : ∀ n, f (q+n) = f n) (hz : ∑ n ∈ range q, f n = 0)
    (hb : ∀ n, ‖f n‖ ≤ 1) (N : ℕ) : ‖∑ n ∈ range N, f n‖ ≤ q := by
  induction N using Nat.strong_induction_on with
  | ind N ih =>
    by_cases hN : N < q
    · calc
        _ ≤ ∑ n ∈ range N, ‖f n‖ := norm_sum_le _ _
        _ ≤ ∑ _n ∈ range N, (1:ℝ) := sum_le_sum (fun n _ => hb n)
        _ = N := by simp
        _ ≤ q := by exact_mod_cast hN.le
    · have he : q+(N-q) = N := Nat.add_sub_of_le (not_lt.mp hN)
      rw [←he, sum_range_add, hz, zero_add]
      simp_rw [hp]
      exact ih _ (Nat.sub_lt (lt_of_lt_of_le hq (not_lt.mp hN)) hq)

lemma char_sum_range_zero {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) : ∑ n ∈ range q, χ (n : ZMod q) = 0 := by
  rw [←Fin.sum_univ_eq_sum_range]
  have he := (ZMod.finEquiv q).toEquiv.sum_comp χ
  cases q with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ q =>
    have hz := he.trans (MulChar.sum_eq_zero_of_ne_one hχ)
    change (∑ i : Fin (q+1), χ i) = 0 at hz
    calc
      _ = ∑ i : Fin (q+1), χ (i : Fin (q+1)) := by
        apply Finset.sum_congr rfl
        intro i hi
        congr 1
        exact Fin.cast_val_eq_self i
      _ = 0 := hz

lemma char_sum_Icc_norm_le {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (N : ℕ) : ‖∑ n ∈ Icc 1 N, χ (n : ZMod q)‖ ≤ q+1 := by
  have hr := periodic_sum_norm_le (NeZero.pos q)
    (f := fun n => χ (n : ZMod q)) (by intro n; simp)
    (char_sum_range_zero hχ) (fun n => χ.norm_le_one _) (N+1)
  have he : ∑ n ∈ range (N+1), χ (n : ZMod q) =
      χ (0 : ZMod q) + ∑ n ∈ Icc 1 N, χ (n : ZMod q) := by
    rw [Nat.range_succ_eq_Icc_zero, ←Finset.insert_Icc_add_one_left_eq_Icc (Nat.zero_le N)]
    simp
  rw [he] at hr
  calc
    _ = ‖(χ (0 : ZMod q) + ∑ n ∈ Icc 1 N, χ (n : ZMod q)) - χ 0‖ := by congr 1; ring
    _ ≤ ‖χ (0 : ZMod q) + ∑ n ∈ Icc 1 N, χ (n : ZMod q)‖ + ‖χ 0‖ := norm_sub_le _ _
    _ ≤ q+1 := add_le_add hr (χ.norm_le_one _)

noncomputable def seriesDiscrepancy (f : ℕ → ℂ) (c : ℂ) (t : ℝ) : ℂ :=
  (∑ n ∈ Icc 1 ⌊t⌋₊, f n) - c*t

lemma measurable_seriesDiscrepancy (f : ℕ → ℂ) (c : ℂ) :
    Measurable (seriesDiscrepancy f c) := by
  exact ((measurable_of_countable (fun N : ℕ => ∑ n ∈ Icc 1 N, f n)).comp
    Nat.measurable_floor).sub (measurable_const.mul Complex.continuous_ofReal.measurable)

noncomputable def regularSeries (f : ℕ → ℂ) (c : ℂ) (s : ℂ) : ℂ :=
  c+s*discrepancyTail (seriesDiscrepancy f c) 1 s

lemma regularSeries_differentiableAt {f : ℕ → ℂ} {c : ℂ} {D : ℝ} (hD : 0 ≤ D)
    (hb : ∀ t, 1 < t → ‖seriesDiscrepancy f c t‖ ≤ D) {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (regularSeries f c) s := by
  exact (differentiableAt_const c).add (differentiableAt_id.mul
    (discrepancyTail_differentiableAt zero_lt_one hD (measurable_seriesDiscrepancy f c) hb hs))

lemma regularSeries_eq_LSeries_sub {f : ℕ → ℂ} {c : ℂ} {D : ℝ}
    (hf : ∀ n, ‖f n‖ ≤ 1) (hD : 0 ≤ D)
    (hb : ∀ t, 1 < t → ‖seriesDiscrepancy f c t‖ ≤ D) {s : ℂ} (hs : 1 < s.re) :
    regularSeries f c s = LSeries f s - c/(s-1) := by
  have hO : (fun n => ∑ k ∈ Icc 1 n, ‖f k‖) =O[atTop] (fun n => (n:ℝ)^(1:ℝ)) := by
    refine isBigO_iff.mpr ⟨1, .of_forall (fun n => ?_)⟩
    simp only [Real.rpow_one, one_mul, Real.norm_eq_abs]
    rw [abs_of_nonneg (sum_nonneg (fun _ _ => norm_nonneg _))]
    calc
      _ ≤ ∑ _k ∈ Icc 1 n, (1:ℝ) := sum_le_sum (fun n _ => hf n)
      _ ≤ |(n:ℝ)| := by simp
  rw [LSeries_eq_mul_integral' f zero_le_one hs hO]
  have hiA := discrepancyTail_integrable zero_lt_one hD (measurable_seriesDiscrepancy f c) hb
    (zero_lt_one.trans hs)
  have hi := integrableOn_Ioi_cpow_of_lt (by simpa using neg_lt_neg hs : (-s).re < -1) zero_lt_one
  have he (t : ℝ) (ht : 1 < t) :
      (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * (t:ℂ)^(-(s+1)) =
      seriesDiscrepancy f c t * (t:ℂ)^(-(s+1)) + c*(t:ℂ)^(-s) := by
    have ht0 : (t:ℂ) ≠ 0 := by exact_mod_cast (zero_lt_one.trans ht).ne'
    have ht1 : (t:ℂ)*(t:ℂ)^(-(s+1)) = (t:ℂ)^(-s) := by
      nth_rw 1 [←Complex.cpow_one (t:ℂ)]
      rw [←Complex.cpow_add _ _ ht0]
      congr 1
      ring
    dsimp [seriesDiscrepancy]
    rw [sub_mul, mul_assoc c, ht1]
    ring
  have hs0 : s-1 ≠ 0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
  have hv : ∫ t in Ioi (1:ℝ), (t:ℂ)^(-s) = 1/(s-1) := by
    rw [integral_Ioi_cpow_of_lt (by simpa using neg_lt_neg hs : (-s).re < -1) zero_lt_one]
    simp only [ofReal_one, one_cpow]
    have he : -s+1 = -(s-1) := by ring
    rw [he, neg_div_neg_eq]
  have hint : (∫ t in Ioi (1:ℝ), (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * (t:ℂ)^(-(s+1))) =
      ∫ t in Ioi (1:ℝ), seriesDiscrepancy f c t * (t:ℂ)^(-(s+1)) + c*(t:ℂ)^(-s) :=
    setIntegral_congr_fun measurableSet_Ioi (fun {t} ht => he t ht)
  rw [hint,
    integral_add hiA (hi.const_mul c), integral_const_mul, hv]
  dsimp [regularSeries,discrepancyTail]
  field_simp [hs0]
  ring

lemma sum_Icc_zero_eq {f : ℕ → ℂ} (hf : f 0 = 0) (N : ℕ) :
    ∑ k ∈ Icc 0 N, f k = ∑ k ∈ Icc 1 N, f k := by
  rw [←Finset.insert_Icc_add_one_left_eq_Icc (Nat.zero_le N)]
  simp [hf]

lemma weighted_sum_abel {f : ℕ → ℂ} (hf : f 0 = 0) {N : ℕ} (hN : 1 ≤ N)
    {s : ℂ} (hs : 0 < s.re) :
    ∑ n ∈ Icc 1 N, f n * (n:ℂ)^(-s) =
      (∑ n ∈ Icc 1 N, f n)*(N:ℂ)^(-s) +
        s*∫ t in (1:ℝ)..N, (∑ n ∈ Icc 1 ⌊t⌋₊, f n)*(t:ℂ)^(-(s+1)) := by
  have hNR : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hs0 : s ≠ 0 := Complex.ne_zero_of_re_pos hs
  have hd (t:ℝ) (ht : t ∈ Set.Icc 1 (N:ℝ)) :
      HasDerivAt (fun t : ℝ => (t:ℂ)^(-s)) ((-s)*(t:ℂ)^(-(s+1))) t := by
    rw [show -(s+1) = -s-1 by ring]
    exact hasDerivAt_ofReal_cpow_const ((zero_lt_one.trans_le ht.1).ne') (neg_ne_zero.mpr hs0)
  have hcont : ContinuousOn (fun t : ℝ => (-s)*(t:ℂ)^(-(s+1))) (Set.Icc 1 (N:ℝ)) := by
    intro t ht
    exact (continuousAt_const.mul (Complex.continuousAt_ofReal_cpow_const _ _
      (.inr (zero_lt_one.trans_le ht.1).ne'))).continuousWithinAt
  have hi : IntegrableOn (deriv (fun t:ℝ => (t:ℂ)^(-s))) (Set.Icc 1 (N:ℝ)) :=
    hcont.integrableOn_Icc.congr_fun (fun t ht => (hd t ht).deriv.symm) measurableSet_Icc
  have ha := sum_mul_eq_sub_sub_integral_mul' f hN (fun t ht => (hd t (by simpa using ht)).differentiableAt) (by simpa using hi)
  have he : (insert 1 (Finset.Ioc 1 N) : Finset ℕ) = Finset.Icc 1 N := by
    ext k
    simp only [Finset.mem_insert,Finset.mem_Ioc,Finset.mem_Icc]
    omega
  have hint : (∫ t in Set.Ioc (1:ℝ) (N:ℝ),
      deriv (fun t:ℝ => (t:ℂ)^(-s)) t * ∑ k ∈ Icc 0 ⌊t⌋₊, f k) =
      (-s)*∫ t in (1:ℝ)..N, (∑ k ∈ Icc 1 ⌊t⌋₊, f k)*(t:ℂ)^(-(s+1)) := by
    rw [intervalIntegral.integral_of_le hNR, ←integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    dsimp only
    rw [(hd t ⟨ht.1.le,ht.2⟩).deriv,sum_Icc_zero_eq hf]
    ring
  simp only [Nat.cast_one, Complex.ofReal_natCast, Complex.ofReal_one] at ha
  rw [hint] at ha
  simp only [one_cpow,one_mul,sum_Icc_zero_eq hf,Finset.Icc_self,sum_singleton] at ha
  conv_lhs => rw [←he,sum_insert (by simp)]
  simp only [Nat.cast_one,one_cpow,mul_one]
  simp_rw [mul_comm (f _) ((_:ℂ)^(-s))]
  rw [ha]
  ring

lemma cpow_sub_eq_mul_intervalIntegral {N : ℝ} (hN : 1 ≤ N) (s : ℂ) :
    (N:ℂ)^(1-s)-1 = (1-s)*∫ t in (1:ℝ)..N, (t:ℂ)^(-s) := by
  by_cases hs : s = 1
  · subst s
    simp
  · have hn : (0:ℝ) ∉ Set.uIcc 1 N := by rw [Set.uIcc_of_le hN]; simp
    rw [integral_cpow (.inr ⟨by simpa using hs,hn⟩)]
    simp only [Complex.ofReal_one,one_cpow]
    have he : -s+1 = 1-s := by ring
    rw [he]
    field_simp

lemma regularSeries_cutoff {f : ℕ → ℂ} {c : ℂ} {D : ℝ} (hf : f 0 = 0)
    (hD : 0 ≤ D) (hb : ∀ t, 1 < t → ‖seriesDiscrepancy f c t‖ ≤ D)
    {N : ℕ} (hN : 1 ≤ N) {s : ℂ} (hs : 0 < s.re) :
    regularSeries f c s = (∑ n ∈ Icc 1 N, f n*(n:ℂ)^(-s)) -
      seriesDiscrepancy f c N * (N:ℂ)^(-s) +
      s*discrepancyTail (seriesDiscrepancy f c) N s -
      c*∫ t in (1:ℝ)..N, (t:ℂ)^(-s) := by
  have hNR : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hn0 : (N:ℂ) ≠ 0 := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN).ne'
  have hi := discrepancyTail_integrable zero_lt_one hD (measurable_seriesDiscrepancy f c) hb hs
  have htail := intervalIntegral.integral_Ioi_sub_Ioi hi hNR
  have hp : ∀ t ∈ Set.Icc (1:ℝ) (N:ℝ),
      (t:ℂ)*(t:ℂ)^(-(s+1)) = (t:ℂ)^(-s) := by
    intro t ht
    have ht0 : (t:ℂ) ≠ 0 := by exact_mod_cast (zero_lt_one.trans_le ht.1).ne'
    nth_rw 1 [←Complex.cpow_one (t:ℂ)]
    rw [←Complex.cpow_add _ _ ht0]
    congr 1
    ring
  have hip : IntervalIntegrable (fun t:ℝ => (t:ℂ)^(-s)) volume 1 N :=
    intervalIntegral.intervalIntegrable_cpow (.inr (by rw [Set.uIcc_of_le hNR]; simp))
  have hiA : IntervalIntegrable (fun t:ℝ => seriesDiscrepancy f c t*(t:ℂ)^(-(s+1))) volume 1 N :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hNR).mpr (hi.mono_set Set.Ioc_subset_Ioi_self)
  have hint : (∫ t in (1:ℝ)..N, (∑ n ∈ Icc 1 ⌊t⌋₊, f n)*(t:ℂ)^(-(s+1))) =
      (∫ t in (1:ℝ)..N, seriesDiscrepancy f c t*(t:ℂ)^(-(s+1))) +
        c*∫ t in (1:ℝ)..N, (t:ℂ)^(-s) := by
    rw [←intervalIntegral.integral_const_mul, ←intervalIntegral.integral_add hiA (hip.const_mul c)]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hNR] at ht
    dsimp [seriesDiscrepancy]
    rw [sub_mul,mul_assoc c,hp t ht]
    ring
  have hab := weighted_sum_abel hf hN hs
  rw [hint, ←htail] at hab
  have hpow : (N:ℂ)*(N:ℂ)^(-s) = (N:ℂ)^(1-s) := by
    nth_rw 1 [←Complex.cpow_one (N:ℂ)]
    rw [←Complex.cpow_add _ _ hn0]
    congr 1
  have hc := cpow_sub_eq_mul_intervalIntegral hNR s
  simp only [Complex.ofReal_natCast] at hc
  dsimp [regularSeries,discrepancyTail]
  rw [hab]
  simp only [seriesDiscrepancy,Nat.floor_natCast,Complex.ofReal_natCast]
  rw [sub_mul,mul_assoc c,hpow,sub_eq_iff_eq_add.mp hc]
  ring

lemma sum_cpow_norm_le {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) {ε : ℝ} (hε : 0 < ε)
    {s : ℂ} (hs : 1-ε ≤ s.re) {N : ℕ} (_hN : 1 ≤ N) :
    ‖∑ n ∈ Icc 1 N, f n*(n:ℂ)^(-s)‖ ≤
      (∑' n : ℕ, (n:ℝ)^(-1-ε)) * (N:ℝ)^(2*ε) := by
  have hsumm : Summable (fun n : ℕ => (n:ℝ)^(-1-ε)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  calc
    _ ≤ ∑ n ∈ Icc 1 N, ‖f n*(n:ℂ)^(-s)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Icc 1 N, (n:ℝ)^(-1-ε)*(N:ℝ)^(2*ε) := by
      apply sum_le_sum
      intro n hn
      have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (mem_Icc.mp hn).1
      have hnN : (n:ℝ) ≤ N := by exact_mod_cast (mem_Icc.mp hn).2
      have hn0 := zero_lt_one.trans_le hn1
      rw [norm_mul]
      have hn0C : (n:ℂ) = ((n:ℝ):ℂ) := by simp
      rw [hn0C,Complex.norm_cpow_eq_rpow_re_of_pos hn0,Complex.neg_re]
      calc
        _ ≤ (n:ℝ)^(-s.re) := by
          simpa using mul_le_mul_of_nonneg_right (hf n) (Real.rpow_nonneg hn0.le (-s.re))
        _ ≤ (n:ℝ)^(-1+ε) := Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
        _ = (n:ℝ)^(-1-ε)*(n:ℝ)^(2*ε) := by rw [←Real.rpow_add hn0]; congr 1; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hn0.le hnN (by positivity))
          (Real.rpow_nonneg hn0.le _)
    _ = (∑ n ∈ Icc 1 N, (n:ℝ)^(-1-ε))*(N:ℝ)^(2*ε) := by rw [sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (hsumm.sum_le_tsum _ (fun n _ => Real.rpow_nonneg n.cast_nonneg _))
      (Real.rpow_nonneg N.cast_nonneg _)

lemma norm_intervalIntegral_cpow_le {ε N : ℝ} (hε : 0 < ε) (hN : 1 ≤ N)
    {s : ℂ} (hs : 1-ε ≤ s.re) :
    ‖∫ t in (1:ℝ)..N, (t:ℂ)^(-s)‖ ≤ N^ε/ε := by
  have hn : (0:ℝ) ∉ Set.uIcc 1 N := by rw [Set.uIcc_of_le hN]; simp
  calc
    _ ≤ ∫ t in (1:ℝ)..N, t^(-1+ε) := by
      apply intervalIntegral.norm_integral_le_of_norm_le hN
        (.of_forall (fun t ht => ?_)) (intervalIntegral.intervalIntegrable_rpow (.inr hn))
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans ht.1),Complex.neg_re]
      exact Real.rpow_le_rpow_of_exponent_le ht.1.le (by linarith)
    _ = (N^ε-1)/ε := by
      rw [integral_rpow (.inl (by linarith : -1 < -1+ε))]
      have he : -1+ε+1 = ε := by ring
      simp [he]
    _ ≤ _ := div_le_div_of_nonneg_right (by linarith) hε.le

lemma regularSeries_norm_cutoff {f : ℕ → ℂ} {c : ℂ} {D ε : ℝ}
    (hf0 : f 0 = 0) (hf : ∀ n, ‖f n‖ ≤ 1) (hc : ‖c‖ ≤ 1) (hD : 0 ≤ D)
    (hb : ∀ t, 1 ≤ t → ‖seriesDiscrepancy f c t‖ ≤ D)
    (hε : 0 < ε) (hε1 : ε ≤ 1/2) {N : ℕ} (hN : 1 ≤ N) {s : ℂ}
    (hs : 1-ε ≤ s.re) (hNs : D*(1+‖s‖) ≤ N) :
    ‖regularSeries f c s‖ ≤ ((∑' n : ℕ, (n:ℝ)^(-1-ε))+2+1/ε)*(N:ℝ)^(2*ε) := by
  have hNR : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hNP := zero_lt_one.trans_le hNR
  have hs0 : 0 < s.re := by linarith
  have hhalf : 1/2 ≤ s.re := by linarith
  have htail := discrepancyTail_norm_le hNP hD (measurable_seriesDiscrepancy f c)
    (fun t ht => hb t (hNR.trans ht.le)) hs0
  have hboundary : ‖seriesDiscrepancy f c N * (N:ℂ)^(-s)‖ ≤ D*(N:ℝ)^(-s.re) := by
    rw [norm_mul, ←Complex.ofReal_natCast N, Complex.norm_cpow_eq_rpow_re_of_pos hNP,Complex.neg_re]
    exact mul_le_mul_of_nonneg_right (hb _ hNR) (Real.rpow_nonneg hNP.le _)
  have hsmall : ‖seriesDiscrepancy f c N * (N:ℂ)^(-s)‖ +
      ‖s*discrepancyTail (seriesDiscrepancy f c) N s‖ ≤ 2*(N:ℝ)^ε := by
    have ht : D*(N:ℝ)^(-s.re)/s.re ≤ 2*D*(N:ℝ)^(-s.re) := by
      apply (div_le_iff₀ hs0).mpr
      have hn := Real.rpow_nonneg hNP.le (-s.re)
      nlinarith [mul_nonneg hD hn,mul_nonneg (mul_nonneg hD hn) (sub_nonneg.mpr hhalf)]
    have he : (N:ℝ)*(N:ℝ)^(-s.re) ≤ (N:ℝ)^ε := by
      nth_rw 1 [←Real.rpow_one (N:ℝ)]
      rw [←Real.rpow_add hNP]
      apply Real.rpow_le_rpow_of_exponent_le hNR
      linarith
    calc
      _ ≤ D*(N:ℝ)^(-s.re) + ‖s‖*(2*D*(N:ℝ)^(-s.re)) := by
        nth_rw 2 [norm_mul]
        exact add_le_add hboundary (mul_le_mul_of_nonneg_left (htail.trans ht) (norm_nonneg s))
      _ ≤ 2*(N:ℝ)*(N:ℝ)^(-s.re) := by
        have hcoeff : D+2*‖s‖*D ≤ 2*(N:ℝ) := by nlinarith
        nlinarith [mul_nonneg (sub_nonneg.mpr hcoeff) (Real.rpow_nonneg hNP.le (-s.re))]
      _ ≤ _ := by nlinarith [he]
  have hi : ‖c*∫ t in (1:ℝ)..N, (t:ℂ)^(-s)‖ ≤ (N:ℝ)^ε/ε := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right hc (norm_nonneg _)).trans (by
      simpa using norm_intervalIntegral_cpow_le hε hNR hs)
  have hp : (N:ℝ)^ε ≤ (N:ℝ)^(2*ε) := Real.rpow_le_rpow_of_exponent_le hNR (by linarith)
  rw [regularSeries_cutoff hf0 hD (fun t ht => hb t ht.le) hN hs0]
  calc
    _ ≤ ‖∑ n ∈ Icc 1 N, f n*(n:ℂ)^(-s)‖ +
        (‖seriesDiscrepancy f c N * (N:ℂ)^(-s)‖ +
        ‖s*discrepancyTail (seriesDiscrepancy f c) N s‖) +
        ‖c*∫ t in (1:ℝ)..N, (t:ℂ)^(-s)‖ := by
      calc
        _ ≤ ‖(∑ n ∈ Icc 1 N, f n*(n:ℂ)^(-s)) - seriesDiscrepancy f c N * (N:ℂ)^(-s) +
             s*discrepancyTail (seriesDiscrepancy f c) N s‖ +
             ‖c*∫ t in (1:ℝ)..N, (t:ℂ)^(-s)‖ := norm_sub_le _ _
        _ ≤ (‖(∑ n ∈ Icc 1 N, f n*(n:ℂ)^(-s)) - seriesDiscrepancy f c N * (N:ℂ)^(-s)‖ +
             ‖s*discrepancyTail (seriesDiscrepancy f c) N s‖) +
             ‖c*∫ t in (1:ℝ)..N, (t:ℂ)^(-s)‖ := add_le_add (norm_add_le _ _) le_rfl
        _ ≤ _ := by
          have htri := norm_sub_le (∑ n ∈ Icc 1 N, f n*(n:ℂ)^(-s)) (seriesDiscrepancy f c N * (N:ℂ)^(-s))
          linarith
    _ ≤ ((∑' n : ℕ, (n:ℝ)^(-1-ε)))*(N:ℝ)^(2*ε) +
      2*(N:ℝ)^ε+(N:ℝ)^ε/ε := add_le_add (add_le_add (sum_cpow_norm_le hf hε hs hN) hsmall) hi
    _ ≤ ((∑' n : ℕ, (n:ℝ)^(-1-ε)))*(N:ℝ)^(2*ε) +
      2*(N:ℝ)^(2*ε)+(N:ℝ)^(2*ε)/ε := by
        linarith [div_le_div_of_nonneg_right hp hε.le]
    _ = _ := by ring

lemma regularSeries_norm_small_power {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1/2) :
    ∃ K : ℝ, 0 < K ∧ ∀ (f : ℕ → ℂ) (c : ℂ) (D : ℝ),
      f 0 = 0 → (∀ n, ‖f n‖ ≤ 1) → ‖c‖ ≤ 1 → 0 ≤ D →
      (∀ t, 1 ≤ t → ‖seriesDiscrepancy f c t‖ ≤ D) →
      ∀ s : ℂ, 1-ε ≤ s.re →
      ‖regularSeries f c s‖ ≤ K*((D+1)*(‖s‖+2))^(2*ε) := by
  let K₀ := (∑' n : ℕ, (n:ℝ)^(-1-ε))+2+1/ε
  have hK₀ : 0 < K₀ := by
    have ht : 0 ≤ ∑' n : ℕ, (n:ℝ)^(-1-ε) := tsum_nonneg (fun n => Real.rpow_nonneg n.cast_nonneg _)
    dsimp [K₀]
    positivity
  refine ⟨K₀*2^(2*ε), by positivity, ?_⟩
  intro f c D hf0 hf hc hD hb s hs
  let B := (D+1)*(‖s‖+2)
  have hB : 1 ≤ B := by dsimp [B]; nlinarith [norm_nonneg s]
  let N := ⌈B⌉₊
  have hBN : B ≤ (N:ℝ) := Nat.le_ceil B
  have hN : 1 ≤ N := by exact_mod_cast (hB.trans hBN)
  have hN2 : (N:ℝ) ≤ 2*B := by
    have := Nat.ceil_lt_add_one (zero_lt_one.trans_le hB).le
    change (N:ℝ) < B+1 at this
    linarith
  have hcut := regularSeries_norm_cutoff hf0 hf hc hD hb hε hε1 hN hs
    (show D*(1+‖s‖) ≤ (N:ℝ) from (by dsimp [B] at hBN; nlinarith [norm_nonneg s]))
  calc
    _ ≤ K₀*(N:ℝ)^(2*ε) := hcut
    _ ≤ K₀*(2*B)^(2*ε) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow N.cast_nonneg hN2 (by positivity)) hK₀.le
    _ = _ := by rw [Real.mul_rpow (by norm_num) (by linarith : 0 ≤ B)]; ring

def positiveCoefficients (f : ℕ → ℂ) (n : ℕ) : ℂ := if n = 0 then 0 else f n

lemma positiveCoefficients_zero (f : ℕ → ℂ) : positiveCoefficients f 0 = 0 := by simp [positiveCoefficients]

lemma positiveCoefficients_norm_le {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) (n : ℕ) :
    ‖positiveCoefficients f n‖ ≤ 1 := by
  by_cases hn : n=0 <;> simp [positiveCoefficients,hn,hf]

lemma sum_positiveCoefficients (f : ℕ → ℂ) (N : ℕ) :
    ∑ n ∈ Icc 1 N, positiveCoefficients f n = ∑ n ∈ Icc 1 N, f n := by
  apply sum_congr rfl
  intro n hn
  simp [positiveCoefficients,show n ≠ 0 from Nat.ne_of_gt (mem_Icc.mp hn).1]

lemma LSeries_positiveCoefficients (f : ℕ → ℂ) (s : ℂ) :
    LSeries (positiveCoefficients f) s = LSeries f s := by
  apply LSeries_congr
  intro n hn
  simp [positiveCoefficients,hn]

lemma discrepancy_character_bound {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (t : ℝ) :
    ‖seriesDiscrepancy (positiveCoefficients (fun n => χ (n : ZMod q))) 0 t‖ ≤ q+1 := by
  simpa [seriesDiscrepancy,sum_positiveCoefficients] using char_sum_Icc_norm_le hχ ⌊t⌋₊

lemma discrepancy_constant_bound {t : ℝ} (ht : 1 ≤ t) :
    ‖seriesDiscrepancy (positiveCoefficients (fun _ => 1)) 1 t‖ ≤ 1 := by
  simp only [seriesDiscrepancy,sum_positiveCoefficients,Finset.sum_const,nsmul_eq_mul,
    mul_one,Nat.card_Icc,Nat.add_sub_cancel,one_mul]
  rw [←Complex.ofReal_natCast,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
  have ht0 := (show (0:ℝ) ≤ t by linarith)
  rw [abs_of_nonpos (sub_nonpos.mpr (Nat.floor_le ht0))]
  have := Nat.lt_floor_add_one t
  linarith

lemma regularSeries_character_eq {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    regularSeries (positiveCoefficients (fun n => χ (n : ZMod q))) 0 s = χ.LFunction s := by
  let f := positiveCoefficients (fun n => χ (n : ZMod q))
  have hfrac : AnalyticOnNhd ℂ (regularSeries f 0) {s : ℂ | 0 < s.re} := by
    apply DifferentiableOn.analyticOnNhd ?_ (show IsOpen {z : ℂ | 0 < z.re} from isOpen_lt continuous_const Complex.continuous_re)
    intro s hs
    exact (regularSeries_differentiableAt (by positivity : (0:ℝ) ≤ q+1)
      (fun t _ => discrepancy_character_bound hχ t) hs).differentiableWithinAt
  have hL : AnalyticOnNhd ℂ χ.LFunction {s : ℂ | 0 < s.re} :=
    fun s _ => (DirichletCharacter.differentiable_LFunction hχ).analyticAt s
  have he : regularSeries f 0 =ᶠ[𝓝 (2:ℂ)] χ.LFunction := by
    filter_upwards [(continuous_re.tendsto (2:ℂ)).eventually (lt_mem_nhds (by norm_num : (1:ℝ) < (2:ℂ).re))] with z hz
    rw [regularSeries_eq_LSeries_sub (positiveCoefficients_norm_le (fun n => χ.norm_le_one _))
      (by positivity : (0:ℝ) ≤ q+1) (fun t _ => discrepancy_character_bound hχ t) hz]
    simp only [zero_div,sub_zero]
    rw [LSeries_positiveCoefficients,DirichletCharacter.LFunction_eq_LSeries χ hz]
  exact hfrac.eqOn_of_preconnected_of_eventuallyEq hL (convex_halfSpace_re_gt 0).isPreconnected
    (show (2:ℂ) ∈ {s:ℂ | 0<s.re} by norm_num) he hs

lemma LFunction_norm_small_power {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1/2) :
    ∃ K : ℝ, 0 < K ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ s : ℂ, 1-ε ≤ s.re →
      ‖χ.LFunction s‖ ≤ K*((q+2)*(‖s‖+2))^(2*ε) := by
  obtain ⟨K,hK,h⟩ := regularSeries_norm_small_power hε hε1
  refine ⟨K,hK,fun q _ χ hχ s hs => ?_⟩
  have he := h _ 0 (q+1) (positiveCoefficients_zero _) (positiveCoefficients_norm_le (fun n => χ.norm_le_one _))
    (by simp) (by positivity) (fun t _ => discrepancy_character_bound hχ t) s hs
  rw [regularSeries_character_eq hχ (by linarith)] at he
  convert he using 1
  congr 3
  ring

lemma regularSeries_deriv_norm_small_power {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1/2) :
    ∃ K : ℝ, 0 < K ∧ ∀ (f : ℕ → ℂ) (c : ℂ) (D : ℝ),
      f 0 = 0 → (∀ n, ‖f n‖ ≤ 1) → ‖c‖ ≤ 1 → 0 ≤ D →
      (∀ t, 1 ≤ t → ‖seriesDiscrepancy f c t‖ ≤ D) →
      ∀ s : ℂ, 1-ε/2 ≤ s.re →
      ‖deriv (regularSeries f c) s‖ ≤ K*((D+1)*(‖s‖+2))^(2*ε) := by
  obtain ⟨K,hK,h⟩ := regularSeries_norm_small_power hε hε1
  refine ⟨K*2^(2*ε)/(ε/2),by positivity,?_⟩
  intro f c D hf0 hf hc hD hb s hs
  have hε2 : 0 < ε/2 := by positivity
  have hre (z:ℂ) (hz : dist z s ≤ ε/2) : 1-ε ≤ z.re := by
    have hd := Complex.re_le_norm (s-z)
    rw [Complex.sub_re,←dist_eq_norm,dist_comm] at hd
    linarith
  have hd : DiffContOnCl ℂ (regularSeries f c) (Metric.ball s (ε/2)) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball _ hε2.ne']
    intro z hz
    exact (regularSeries_differentiableAt hD (fun t ht => hb t ht.le) (by
      have := hre z (Metric.mem_closedBall.mp hz)
      linarith)).differentiableWithinAt
  have hbnd (z:ℂ) (hz : z ∈ Metric.sphere s (ε/2)) :
      ‖regularSeries f c z‖ ≤ K*2^(2*ε)*((D+1)*(‖s‖+2))^(2*ε) := by
    have hdist := Metric.mem_sphere.mp hz
    have hzR := hre z hdist.le
    have hnorm : ‖z‖+2 ≤ 2*(‖s‖+2) := by
      have : ‖z‖ ≤ dist z s + ‖s‖ := by simpa [dist_eq_norm] using norm_add_le (z-s) s
      rw [hdist] at this
      nlinarith [norm_nonneg s]
    calc
      _ ≤ K*((D+1)*(‖z‖+2))^(2*ε) := h f c D hf0 hf hc hD hb z hzR
      _ ≤ K*(2*((D+1)*(‖s‖+2)))^(2*ε) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by positivity) (by nlinarith) (by positivity)) hK.le
      _ = _ := by rw [Real.mul_rpow (by positivity) (by positivity)]; ring
  have hder := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hε2 hd hbnd
  convert hder using 1
  ring

end LargePrimeGaps
end OAI

-- Source module: TaylorBounds
namespace OAI
namespace LargePrimeGaps
open Filter
open Set Filter MeasureTheory
open scoped Topology ContDiff
open Asymptotics
open scoped Classical
open scoped ContDiff
open Topology
open scoped Convolution ContDiff Pointwise
open scoped ComplexConjugate
open Filter Topology
open Complex Filter Topology
open Complex Filter Topology Set MeasureTheory Asymptotics
open Finset
open Complex Filter Topology Finset
lemma power_series_tail_bound {a : ℕ → ℝ} {M r z : ℝ} (_hM : 0 ≤ M)
    (hr : 0 < r) (hz : 0 ≤ z) (hzr : z < r)
    (hb : ∀ n, |a n| ≤ M/r^n) (N : ℕ) :
    |∑' n : ℕ, a (n+N)*z^(n+N)| ≤ M*(z/r)^N/(1-z/r) := by
  have hρ : 0 ≤ z/r := div_nonneg hz hr.le
  have hρ1 : z/r < 1 := (div_lt_one hr).mpr hzr
  have hg := (summable_geometric_of_lt_one hρ hρ1).mul_left (M*(z/r)^N)
  have hbound (n : ℕ) : ‖a (n+N)*z^(n+N)‖ ≤ (M*(z/r)^N)*(z/r)^n := by
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (pow_nonneg hz _)]
    calc
      _ ≤ (M/r^(n+N))*z^(n+N) := mul_le_mul_of_nonneg_right (hb _) (pow_nonneg hz _)
      _ = M*(z/r)^(n+N) := by rw [div_pow]; ring
      _ = _ := by rw [pow_add]; ring
  have hn := hg.of_nonneg_of_le (fun n => norm_nonneg _) hbound
  calc
    _ = ‖∑' n : ℕ, a (n+N)*z^(n+N)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∑' n : ℕ, ‖a (n+N)*z^(n+N)‖ := norm_tsum_le_tsum_norm hn
    _ ≤ ∑' n : ℕ, (M*(z/r)^N)*(z/r)^n := hn.tsum_le_tsum hbound hg
    _ = _ := by rw [tsum_mul_left,tsum_geometric_of_lt_one hρ hρ1]; rfl

lemma residue_lower_bound_of_taylor {a : ℕ → ℝ} {R M r z : ℝ} {N : ℕ}
    (hM : 0 ≤ M) (hr : 0 < r) (hz : 1 < z) (hzr : z < r)
    (hb : ∀ n, |a n| ≤ M/r^n) (ha0 : 1-R ≤ a 0)
    (ha : ∀ n, -R ≤ a n) (hN : 1 ≤ N)
    (hvalue : (∑' n : ℕ, a n*z^n) ≤ R/(z-1))
    (htail : M*(z/r)^N/(1-z/r) ≤ 1/2) :
    (z-1)/2 ≤ R*z^N := by
  have heach : ∀ n, (if n=0 then 1 else (0:ℝ)) - R*z^n ≤ a n*z^n := by
    intro n
    by_cases hn : n=0
    · simpa [hn] using ha0
    · simp only [hn,↓reduceIte,zero_sub]
      nlinarith [mul_le_mul_of_nonneg_right (ha n) (pow_nonneg (zero_lt_one.trans hz).le n)]
  have hsum := Finset.sum_le_sum (s := range N) (fun n _ => heach n)
  have hzero : (∑ n ∈ range N, if n=0 then 1 else (0:ℝ)) = 1 := by
    simp [show 0 < N by omega]
  rw [sum_sub_distrib,hzero,←mul_sum] at hsum
  have htail' := power_series_tail_bound hM hr (zero_lt_one.trans hz).le hzr hb N
  have ht : -(1/2:ℝ) ≤ ∑' n : ℕ, a (n+N)*z^(n+N) := by
    have := (abs_le.mp (htail'.trans htail)).1
    linarith
  have hs : Summable (fun n : ℕ => a n*z^n) := by
    have hρ : 0 ≤ z/r := by positivity
    have hρ1 : z/r < 1 := (div_lt_one hr).mpr hzr
    apply ((summable_geometric_of_lt_one hρ hρ1).mul_left M).of_norm_bounded
    intro n
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (pow_nonneg (zero_lt_one.trans hz).le _)]
    calc
      _ ≤ (M/r^n)*z^n := mul_le_mul_of_nonneg_right (hb _) (pow_nonneg (zero_lt_one.trans hz).le _)
      _ = M*(z/r)^n := by rw [div_mul_eq_mul_div,div_pow]; ring
  have hdecomp := hs.sum_add_tsum_nat_add N
  have hm : 1/2 ≤ R/(z-1)+R*(∑ n ∈ range N, z^n) := by linarith
  have hgeom := geom_sum_mul z N
  have hv := (le_div_iff₀ (sub_pos.mpr hz)).mp
    (show (1/2:ℝ) ≤ (R+R*(∑ n ∈ range N, z^n)*(z-1))/(z-1) from by
      rw [add_div,mul_div_cancel_right₀ _ (sub_pos.mpr hz).ne']
      exact hm)
  have hid : R+R*(∑ n ∈ range N, z^n)*(z-1) = R*z^N := by
    rw [mul_assoc R, hgeom]
    ring
  rw [hid] at hv
  linarith

noncomputable def signedTaylorCoeff (H : ℂ → ℂ) (n : ℕ) : ℝ :=
  (((-1:ℂ)^n)*(n.factorial:ℂ)⁻¹*iteratedDeriv n H 2).re

lemma signedTaylorCoeff_hasSum {H : ℂ → ℂ} {r z : ℝ}
    (hf : DifferentiableOn ℂ H (Metric.ball 2 r)) (hz : |z| < r) :
    HasSum (fun n => signedTaylorCoeff H n*z^n) (H ((2-z:ℝ):ℂ)).re := by
  have hmem : ((2-z:ℝ):ℂ) ∈ Metric.ball (2:ℂ) r := by
    rw [Metric.mem_ball,dist_eq_norm]
    have he : ((2-z:ℝ):ℂ)-(2:ℂ) = -(z:ℂ) := by push_cast; ring
    simpa [he,Complex.norm_real,Real.norm_eq_abs] using hz
  have hs := (Complex.hasSum_taylorSeries_on_ball hf hmem).map Complex.reCLM Complex.continuous_re
  change HasSum (fun n => ((n.factorial:ℂ)⁻¹ *
    ((((2-z:ℝ):ℂ)-2)^n * iteratedDeriv n H 2)).re) (H ((2-z:ℝ):ℂ)).re at hs
  convert hs using 1
  funext n
  dsimp [signedTaylorCoeff]
  have he : ((2-z:ℝ):ℂ)-(2:ℂ) = -(z:ℂ) := by push_cast; ring
  rw [he, show (-(z:ℂ))^n = (-1:ℂ)^n * (z:ℂ)^n by rw [←mul_pow]; congr 1; ring]
  have hmul : (n.factorial:ℂ)⁻¹*((-1:ℂ)^n*(z:ℂ)^n*iteratedDeriv n H 2) =
      ((-1:ℂ)^n*(n.factorial:ℂ)⁻¹*iteratedDeriv n H 2)*(z:ℂ)^n := by ring
  rw [hmul]
  simp only [←Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    mul_zero,sub_zero]

lemma signedTaylorCoeff_norm_bound {H : ℂ → ℂ} {r M : ℝ} (hr : 0 < r)
    (hf : DiffContOnCl ℂ H (Metric.ball 2 r))
    (hb : ∀ s ∈ Metric.sphere 2 r, ‖H s‖ ≤ M) (n : ℕ) :
    |signedTaylorCoeff H n| ≤ M/r^n := by
  have hder := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hr hf hb
  have hfact : (n.factorial:ℝ) ≠ 0 := by positivity
  calc
    _ ≤ ‖(-1:ℂ)^n*(n.factorial:ℂ)⁻¹*iteratedDeriv n H 2‖ := Complex.abs_re_le_norm _
    _ = (n.factorial:ℝ)⁻¹*‖iteratedDeriv n H 2‖ := by simp [norm_pow]
    _ ≤ (n.factorial:ℝ)⁻¹*((n.factorial:ℝ)*M/r^n) := by gcongr
    _ = _ := by field_simp

lemma signedTaylorCoeff_pole (R : ℝ) (n : ℕ) :
    signedTaylorCoeff (fun s : ℂ => (R:ℂ)/(s-1)) n = R := by
  unfold signedTaylorCoeff
  simp only [div_eq_mul_inv,iteratedDeriv_const_mul_field]
  have hi : iteratedDeriv n (fun s : ℂ => (s-1)⁻¹) 2 = (-1:ℂ)^n*n.factorial := by
    rw [iteratedDeriv_eq_iterate]
    simpa only [one_mul,one_pow, show (2:ℂ)-1=1 by norm_num, one_zpow,mul_one] using
      congrFun (iter_deriv_inv_linear_sub n (1:ℂ) 1) 2
  rw [hi]
  have hf : (n.factorial:ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hp : (-1:ℂ)^n*(-1:ℂ)^n = 1 := by rw [←mul_pow]; simp
  have he : (-1:ℂ)^n*(n.factorial:ℂ)⁻¹*((R:ℂ)*((-1:ℂ)^n*n.factorial)) = R := by
    calc
      _ = ((-1:ℂ)^n*(-1:ℂ)^n)*(R:ℂ)*((n.factorial:ℂ)⁻¹*n.factorial) := by ring
      _ = _ := by rw [hp,inv_mul_cancel₀ hf]; ring
  rw [he,Complex.ofReal_re]

lemma signedTaylorCoeff_sub {F G : ℂ → ℂ} (hF : AnalyticAt ℂ F 2)
    (hG : AnalyticAt ℂ G 2) (n : ℕ) :
    signedTaylorCoeff (fun s => F s-G s) n = signedTaylorCoeff F n-signedTaylorCoeff G n := by
  unfold signedTaylorCoeff
  have hd := iteratedDeriv_sub (n:=n) hF.contDiffAt hG.contDiffAt
  change iteratedDeriv n (fun s => F s-G s) 2 = _ at hd
  rw [hd,mul_sub,Complex.sub_re]

open scoped ComplexOrder in
lemma signedTaylorCoeff_LSeries_nonneg {a : ℕ → ℂ} (ha : ∀ n, 0 ≤ a n)
    (hc : LSeries.abscissaOfAbsConv a < (2:ℝ)) (n : ℕ) :
    0 ≤ signedTaylorCoeff (LSeries a) n := by
  have h := LSeries.iteratedDeriv_alternating ha hc n
  have hf : (0:ℝ) ≤ (n.factorial:ℝ)⁻¹ := by positivity
  have hr := (Complex.nonneg_iff.mp h).1
  unfold signedTaylorCoeff
  have he : (-1:ℂ)^n*(n.factorial:ℂ)⁻¹*iteratedDeriv n (LSeries a) 2 =
      (n.factorial:ℂ)⁻¹*((-1:ℂ)^n*iteratedDeriv n (LSeries a) 2) := by ring
  rw [he]
  simpa using mul_nonneg hf hr

open scoped ComplexOrder in
lemma LSeries_two_re_ge_one {a : ℕ → ℂ} (ha : ∀ n, 0 ≤ a n)
    (ha1 : 1 ≤ a 1) (hc : LSeries.abscissaOfAbsConv a < (2:ℝ)) :
    1 ≤ (LSeries a 2).re := by
  have hs : LSeriesSummable a 2 := LSeriesSummable_of_abscissaOfAbsConv_lt_re (by simpa using hc)
  have hl := hs.le_tsum 1 (fun n _ => LSeries.term_nonneg (ha n) 2)
  have hterm : LSeries.term a 2 1 = a 1 := by simp
  rw [hterm] at hl
  exact (Complex.le_def.mp (ha1.trans hl)).1

open scoped ComplexOrder in
set_option maxHeartbeats 800000 in
lemma signedTaylorCoeff_regular_nonneg {H : ℂ → ℂ} {a : ℕ → ℂ} {R : ℝ}
    (ha : ∀ n, 0 ≤ a n) (ha1 : 1 ≤ a 1)
    (hc : LSeries.abscissaOfAbsConv a < (2:ℝ))
    (he : H =ᶠ[𝓝 (2:ℂ)] fun s => LSeries a s-(R:ℂ)/(s-1)) :
    1-R ≤ (H 2).re ∧ ∀ n, -R ≤ signedTaylorCoeff H n := by
  have hL : AnalyticAt ℂ (LSeries a) 2 := LSeries_analyticOnNhd a 2 (by simpa using hc)
  have hP : AnalyticAt ℂ (fun s : ℂ => (R:ℂ)/(s-1)) 2 :=
    analyticAt_const.div (analyticAt_id.sub analyticAt_const) (by norm_num)
  constructor
  · rw [he.self_of_nhds]
    have h := LSeries_two_re_ge_one ha ha1 hc
    simp only [show (2:ℂ)-1=1 by norm_num,div_one,Complex.sub_re,Complex.ofReal_re]
    linarith
  · intro n
    unfold signedTaylorCoeff
    rw [he.iteratedDeriv_eq]
    change -R ≤ signedTaylorCoeff (fun s => LSeries a s-(R:ℂ)/(s-1)) n
    rw [signedTaylorCoeff_sub hL hP,signedTaylorCoeff_pole]
    linarith [signedTaylorCoeff_LSeries_nonneg ha hc n]

lemma residue_polynomial_lower {a : ℕ → ℝ} {R A Q z ε : ℝ}
    (hA : 0 ≤ A) (hQ : 2 ≤ Q) (hQA : 12*A ≤ Q)
    (hz : 1 < z) (hz1 : z ≤ 5/4) (hzε : 60*(z-1) ≤ ε)
    (hb : ∀ n, |a n| ≤ (A*Q^4)/(3/2)^n)
    (ha0 : 1-R ≤ a 0) (ha : ∀ n, -R ≤ a n)
    (hv : (∑' n : ℕ, a n*z^n) ≤ R/(z-1)) :
    ((z-1)/(2*z))*Q^(-ε) ≤ R := by
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  have hlogQ : 0 < Real.log Q := Real.log_pos (by linarith)
  have hz0 : 0 < z := by linarith
  have hlogz : 0 < Real.log z := Real.log_pos hz
  let N : ℕ := ⌈60*Real.log Q⌉₊
  have hNlo : 60*Real.log Q ≤ (N:ℝ) := Nat.le_ceil _
  have hNhi : (N:ℝ) < 60*Real.log Q+1 := Nat.ceil_lt_add_one (by positivity)
  have hN : 1 ≤ N := by
    have : 0 < (N:ℝ) := lt_of_lt_of_le (by positivity) hNlo
    exact_mod_cast (show 1 ≤ N from Nat.one_le_iff_ne_zero.mpr (by exact_mod_cast this.ne'))
  have hρ : 0 ≤ z/(3/2) := by positivity
  have hρ1 : z/(3/2) ≤ 5/6 := by linarith
  have hlogρ : Real.log (5/6:ℝ) ≤ -(1/6:ℝ) := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 5/6)
    linarith
  have hdecay : (z/(3/2))^N ≤ Q^(-10:ℝ) := by
    calc
      _ ≤ (5/6:ℝ)^N := pow_le_pow_left₀ hρ hρ1 N
      _ = Real.exp (Real.log (5/6:ℝ)*(N:ℝ)) := by
        rw [←Real.rpow_natCast,Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 5/6)]
      _ ≤ Real.exp (Real.log Q*(-10)) := by
        apply Real.exp_le_exp.mpr
        have hN0 : (0:ℝ) ≤ N := Nat.cast_nonneg N
        nlinarith [mul_le_mul_of_nonneg_right hlogρ hN0]
      _ = _ := (Real.rpow_def_of_pos hQ0 _).symm
  have htail : (A*Q^4)*(z/(3/2))^N/(1-z/(3/2)) ≤ 1/2 := by
    have hden : 0 < 1-z/(3/2) := by linarith
    have hpow : Q^4*Q^(-10:ℝ) ≤ Q⁻¹ := by
      calc
        _ = Q^(-6:ℝ) := by
          rw [←Real.rpow_natCast,←Real.rpow_add hQ0]
          norm_num
        _ ≤ Q^(-1:ℝ) := Real.rpow_le_rpow_of_exponent_le hQ1 (by norm_num)
        _ = Q⁻¹ := Real.rpow_neg_one Q
    have hp : (A*Q^4)*(z/(3/2))^N ≤ A/Q := by
      calc
        _ ≤ (A*Q^4)*Q^(-10:ℝ) := mul_le_mul_of_nonneg_left hdecay (by positivity)
        _ ≤ A*Q⁻¹ := by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hpow hA
        _ = _ := by rw [div_eq_mul_inv]
    have hAQ : A/Q ≤ 1/12 := (div_le_iff₀ hQ0).mpr (by linarith)
    apply (div_le_iff₀ hden).mpr
    nlinarith
  have hres := residue_lower_bound_of_taylor (by positivity : (0:ℝ) ≤ A*Q^4)
    (by norm_num : (0:ℝ) < 3/2) hz (by linarith : z < 3/2) hb ha0 ha hN hv htail
  have hzpow : z^N ≤ z*Q^ε := by
    have hlogz' : 60*Real.log z ≤ ε := by
      have := Real.log_le_sub_one_of_pos hz0
      linarith
    calc
      _ = Real.exp (Real.log z*(N:ℝ)) := by rw [←Real.rpow_natCast,Real.rpow_def_of_pos hz0]
      _ ≤ Real.exp (Real.log z+(Real.log Q)*ε) := by
        apply Real.exp_le_exp.mpr
        have h1 := mul_le_mul_of_nonneg_left hNhi.le hlogz.le
        have h2 := mul_le_mul_of_nonneg_left hlogz' hlogQ.le
        nlinarith
      _ = _ := by rw [Real.exp_add,Real.exp_log hz0,Real.rpow_def_of_pos hQ0]
  have hR : 0 ≤ R := by
    by_contra! h
    have := mul_neg_of_neg_of_pos h (pow_pos hz0 N)
    linarith
  have hres' : (z-1)/2 ≤ R*(z*Q^ε) := hres.trans (mul_le_mul_of_nonneg_left hzpow hR)
  rw [Real.rpow_neg hQ0.le,←div_eq_mul_inv]
  apply (div_le_iff₀ (Real.rpow_pos_of_pos hQ0 ε)).mpr
  apply (div_le_iff₀ (by positivity : (0:ℝ) < 2*z)).mpr
  nlinarith

open Complex Filter Topology Finset Set MeasureTheory
noncomputable def zetaRegular : ℂ → ℂ :=
  regularSeries (positiveCoefficients (fun _ => 1)) 1

lemma zetaRegular_differentiableAt {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ zetaRegular s :=
  regularSeries_differentiableAt zero_le_one (fun _ ht => discrepancy_constant_bound ht.le) hs

lemma zetaRegular_eq_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    zetaRegular s = riemannZeta s-1/(s-1) := by
  rw [zetaRegular,regularSeries_eq_LSeries_sub (positiveCoefficients_norm_le (by simp))
    zero_le_one (fun _ ht => discrepancy_constant_bound ht.le) hs,LSeries_positiveCoefficients]
  rw [show (fun _ : ℕ => (1:ℂ)) = 1 from rfl,LSeries_one_eq_riemannZeta hs]

lemma poleRemovedZeta_eq {s : ℂ} (hs : 0 < s.re) :
    DirichletCharacter.LFunctionTrivChar₁ 1 s = (s-1)*zetaRegular s+1 := by
  have hF : AnalyticOnNhd ℂ (DirichletCharacter.LFunctionTrivChar₁ 1) {s : ℂ | 0 < s.re} :=
    fun z _ => (DirichletCharacter.differentiable_LFunctionTrivChar₁ 1).analyticAt z
  have hG : AnalyticOnNhd ℂ (fun s : ℂ => (s-1)*zetaRegular s+1) {s : ℂ | 0 < s.re} := by
    apply DifferentiableOn.analyticOnNhd ?_ (show IsOpen {z : ℂ | 0 < z.re} from isOpen_lt continuous_const Complex.continuous_re)
    intro z hz
    exact (((differentiableAt_id.sub_const 1).mul (zetaRegular_differentiableAt hz)).add_const 1).differentiableWithinAt
  have he : DirichletCharacter.LFunctionTrivChar₁ 1 =ᶠ[𝓝 (2:ℂ)]
      fun s : ℂ => (s-1)*zetaRegular s+1 := by
    filter_upwards [(continuous_re.tendsto (2:ℂ)).eventually
      (lt_mem_nhds (by norm_num : (1:ℝ) < (2:ℂ).re))] with z hz
    have hz1 : z ≠ 1 := by intro h; simp [h] at hz
    rw [DirichletCharacter.LFunctionTrivChar₁,Function.update_of_ne hz1,
      DirichletCharacter.LFunctionTrivChar,DirichletCharacter.LFunction_modOne_eq,
      zetaRegular_eq_of_one_lt_re hz]
    field_simp
    ring
  exact hF.eqOn_of_preconnected_of_eventuallyEq hG (convex_halfSpace_re_gt 0).isPreconnected
    (show (2:ℂ) ∈ {s : ℂ | 0 < s.re} by norm_num) he hs

lemma zetaRegular_eq {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    zetaRegular s = riemannZeta s-1/(s-1) := by
  have h := poleRemovedZeta_eq hs
  rw [DirichletCharacter.LFunctionTrivChar₁,Function.update_of_ne hs1,
    DirichletCharacter.LFunctionTrivChar,DirichletCharacter.LFunction_modOne_eq] at h
  have hn : s-1 ≠ 0 := sub_ne_zero.mpr hs1
  apply (mul_left_cancel₀ hn)
  rw [mul_sub,mul_div_cancel₀ _ hn]
  linear_combination -h

lemma regularSeries_norm_simple {f : ℕ → ℂ} {c : ℂ} {D : ℝ} (hD : 0 ≤ D)
    (hb : ∀ t, 1 < t → ‖seriesDiscrepancy f c t‖ ≤ D) {s : ℂ} (hs : 0 < s.re) :
    ‖regularSeries f c s‖ ≤ ‖c‖+‖s‖*D/s.re := by
  have h := discrepancyTail_norm_le zero_lt_one hD (measurable_seriesDiscrepancy f c) hb hs
  simp only [Real.one_rpow,mul_one] at h
  calc
    _ ≤ ‖c‖+‖s*discrepancyTail (seriesDiscrepancy f c) 1 s‖ := norm_add_le _ _
    _ ≤ ‖c‖+‖s‖*(D/s.re) := by rw [norm_mul]; gcongr
    _ = _ := by ring

lemma closedBall_two_re_norm {s : ℂ} (hs : s ∈ Metric.closedBall 2 (7/4:ℝ)) :
    (1/4:ℝ) ≤ s.re ∧ ‖s‖ ≤ 4 := by
  have hd := Metric.mem_closedBall.mp hs
  have hr := Complex.re_le_norm ((2:ℂ)-s)
  rw [Complex.sub_re,←dist_eq_norm,dist_comm] at hr
  have hn : ‖s‖ ≤ dist s 2+‖(2:ℂ)‖ := by simpa [dist_eq_norm] using norm_add_le (s-2) (2:ℂ)
  norm_num at hr hn
  constructor <;> linarith

lemma zetaRegular_norm_le_seventeen {s : ℂ} (hs : s ∈ Metric.closedBall 2 (7/4:ℝ)) :
    ‖zetaRegular s‖ ≤ 17 := by
  obtain ⟨hre,hnorm⟩ := closedBall_two_re_norm hs
  have hp : 0 < s.re := by linarith
  have h := regularSeries_norm_simple zero_le_one (fun _ ht => discrepancy_constant_bound ht.le) hp
  change ‖zetaRegular s‖ ≤ _ at h
  norm_num at h
  have hq : ‖s‖/s.re ≤ 16 := (div_le_iff₀ hp).mpr (by linarith)
  linarith

lemma LFunction_norm_polynomial {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) {s : ℂ} (hs : s ∈ Metric.closedBall 2 (7/4:ℝ)) :
    ‖χ.LFunction s‖ ≤ 16*((q:ℝ)+1) := by
  obtain ⟨hre,hnorm⟩ := closedBall_two_re_norm hs
  have hp : 0 < s.re := by linarith
  have hb := regularSeries_norm_simple (by positivity : (0:ℝ) ≤ q+1)
    (fun t _ => discrepancy_character_bound hχ t) hp
  rw [regularSeries_character_eq hχ hp] at hb
  simp only [norm_zero,zero_add] at hb
  apply hb.trans
  apply (div_le_iff₀ hp).mpr
  nlinarith [Nat.cast_nonneg (α:=ℝ) q]

noncomputable def regularizedZetaProduct (P : ℂ → ℂ) (s : ℂ) : ℂ :=
  zetaRegular s*P s+dslope P 1 s

lemma regularizedZetaProduct_differentiableOn {P : ℂ → ℂ}
    (hP : DifferentiableOn ℂ P {s : ℂ | 0 < s.re}) :
    DifferentiableOn ℂ (regularizedZetaProduct P) {s : ℂ | 0 < s.re} := by
  have hs : {s : ℂ | 0 < s.re} ∈ 𝓝 (1:ℂ) :=
    (show IsOpen {z : ℂ | 0 < z.re} from isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  have hd := (Complex.differentiableOn_dslope hs).mpr hP
  have hz : DifferentiableOn ℂ zetaRegular {s : ℂ | 0 < s.re} :=
    fun s hs => (zetaRegular_differentiableAt hs).differentiableWithinAt
  exact (hz.mul hP).add hd

lemma regularizedZetaProduct_eq {P : ℂ → ℂ} {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    regularizedZetaProduct P s = riemannZeta s*P s-P 1/(s-1) := by
  rw [regularizedZetaProduct,zetaRegular_eq hs hs1,dslope_of_ne P hs1,slope_def_field]
  ring

lemma regularizedZetaProduct_bound {P : ℂ → ℂ} {B : ℝ}
    (hP : DifferentiableOn ℂ P {s : ℂ | 0 < s.re}) (_hB : 0 ≤ B)
    (hb : ∀ s ∈ Metric.closedBall (2:ℂ) (7/4:ℝ), ‖P s‖ ≤ B) :
    DiffContOnCl ℂ (regularizedZetaProduct P) (Metric.ball 2 (3/2:ℝ)) ∧
      ∀ s ∈ Metric.closedBall (2:ℂ) (3/2:ℝ), ‖regularizedZetaProduct P s‖ ≤ 21*B := by
  have hsRe (s : ℂ) (hs : s ∈ Metric.closedBall 2 (7/4:ℝ)) : 0 < s.re := by
    have := (closedBall_two_re_norm hs).1
    linarith
  have hder (s : ℂ) (hs : s ∈ Metric.closedBall 2 (3/2:ℝ)) : ‖deriv P s‖ ≤ 4*B := by
    have hsub : Metric.closedBall s (1/4:ℝ) ⊆ Metric.closedBall (2:ℂ) (7/4:ℝ) := by
      intro z hz
      have hdist := dist_triangle z s (2:ℂ)
      have hz' := Metric.mem_closedBall.mp hz
      have hs' := Metric.mem_closedBall.mp hs
      apply Metric.mem_closedBall.mpr
      linarith
    have hdiff : DiffContOnCl ℂ P (Metric.ball s (1/4:ℝ)) := by
      apply DifferentiableOn.diffContOnCl
      rw [closure_ball _ (by norm_num : (1/4:ℝ) ≠ 0)]
      exact hP.mono (fun z hz => hsRe z (hsub hz))
    have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by norm_num : (0:ℝ) < 1/4)
      hdiff (fun z hz => hb z (hsub (Metric.sphere_subset_closedBall hz)))
    convert h using 1; ring
  have hone : (1:ℂ) ∈ Metric.closedBall (2:ℂ) (3/2:ℝ) := by
    norm_num [Metric.mem_closedBall,dist_eq_norm]
  have hdslope (s : ℂ) (hs : s ∈ Metric.closedBall 2 (3/2:ℝ)) : ‖dslope P 1 s‖ ≤ 4*B := by
    by_cases hs1 : s = 1
    · subst s
      simpa only [dslope_same] using hder 1 hone
    · rw [dslope_of_ne P hs1,slope_def_field,norm_div]
      have hd := (convex_closedBall (2:ℂ) (3/2:ℝ)).norm_image_sub_le_of_norm_deriv_le
        (fun z hz => (hP z (hsRe z (Metric.closedBall_subset_closedBall (by norm_num) hz))).differentiableAt
          ((show IsOpen {z : ℂ | 0 < z.re} from isOpen_lt continuous_const Complex.continuous_re).mem_nhds
            (hsRe z (Metric.closedBall_subset_closedBall (by norm_num) hz)))) hder hone hs
      exact (div_le_iff₀ (norm_pos_iff.mpr (sub_ne_zero.mpr hs1))).mpr hd
  constructor
  · apply DifferentiableOn.diffContOnCl
    rw [closure_ball _ (by norm_num : (3/2:ℝ) ≠ 0)]
    exact (regularizedZetaProduct_differentiableOn hP).mono
      (fun z hz => hsRe z (Metric.closedBall_subset_closedBall (by norm_num) hz))
  · intro s hs
    have hs' := Metric.closedBall_subset_closedBall (by norm_num : (3/2:ℝ) ≤ 7/4) hs
    calc
      _ ≤ ‖zetaRegular s*P s‖+‖dslope P 1 s‖ := norm_add_le _ _
      _ ≤ 17*B+4*B := by rw [norm_mul]; gcongr; exact zetaRegular_norm_le_seventeen hs'; exact hb s hs'; exact hdslope s hs
      _ = _ := by ring

open Complex Finset ArithmeticFunction
open scoped ComplexOrder
def PrimePowerEq (p : ℕ) (f g : ArithmeticFunction ℂ) : Prop :=
  ∀ k : ℕ, f (p^k) = g (p^k)

lemma PrimePowerEq.refl (p : ℕ) (f : ArithmeticFunction ℂ) : PrimePowerEq p f f := fun _ => rfl

lemma PrimePowerEq.mul {p : ℕ} (hp : p.Prime) {f f' g g' : ArithmeticFunction ℂ}
    (hf : PrimePowerEq p f f') (hg : PrimePowerEq p g g') : PrimePowerEq p (f*g) (f'*g') := by
  intro k
  simp only [ArithmeticFunction.mul_apply]
  apply Finset.sum_congr rfl
  intro x hx
  obtain ⟨i,hi,hxi⟩ := (Nat.dvd_prime_pow hp).mp (Nat.mem_divisors.mp
    (Nat.fst_mem_divisors_of_mem_antidiagonal hx)).1
  obtain ⟨j,hj,hxj⟩ := (Nat.dvd_prime_pow hp).mp (Nat.mem_divisors.mp
    (Nat.snd_mem_divisors_of_mem_antidiagonal hx)).1
  rw [hxi,hxj,hf,hg]

lemma primePower_zeta {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (ArithmeticFunction.zeta : ArithmeticFunction ℂ) (p^k) = 1 := by
  simp [hp.ne_zero]

lemma primePower_one {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (1 : ArithmeticFunction ℂ) (p^k) = (0:ℂ)^k := by
  cases k with
  | zero => simp
  | succ k =>
    have hn : p^(k+1) ≠ 1 := by
      have h : 1 < p^(k+1) := one_lt_pow₀ hp.one_lt (by omega)
      omega
    simp [hp.ne_one]

lemma primePower_character {q p : ℕ} (χ : DirichletCharacter ℂ q) (hp : p.Prime) (k : ℕ) :
    toArithmeticFunction (χ ·) (p^k) = χ (p : ZMod q)^k := by
  simp [toArithmeticFunction,hp.ne_zero]

lemma arithmetic_convolution_nonneg {f g : ArithmeticFunction ℂ}
    (hf : ∀ n, 0 ≤ f n) (hg : ∀ n, 0 ≤ g n) (n : ℕ) : 0 ≤ (f*g) n := by
  rw [ArithmeticFunction.mul_apply]
  exact Finset.sum_nonneg (fun x _ => mul_nonneg (hf x.1) (hg x.2))

noncomputable def biquadraticCoefficients {q r : ℕ}
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r) : ArithmeticFunction ℂ :=
  ArithmeticFunction.zeta * toArithmeticFunction (χ ·) * toArithmeticFunction (ψ ·) *
    (toArithmeticFunction (χ ·)).pmul (toArithmeticFunction (ψ ·))

lemma biquadraticCoefficients_multiplicative {q r : ℕ}
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r) :
    (biquadraticCoefficients χ ψ).IsMultiplicative := by
  exact ((isMultiplicative_zeta.natCast.mul (DirichletCharacter.isMultiplicative_toArithmeticFunction χ)).mul
    (DirichletCharacter.isMultiplicative_toArithmeticFunction ψ)).mul
    ((DirichletCharacter.isMultiplicative_toArithmeticFunction χ).pmul (DirichletCharacter.isMultiplicative_toArithmeticFunction ψ))

lemma biquadraticCoefficients_comm {q r : ℕ}
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r) :
    biquadraticCoefficients χ ψ = biquadraticCoefficients ψ χ := by
  unfold biquadraticCoefficients
  rw [ArithmeticFunction.pmul_comm]
  ring

lemma biquadratic_prime_zero {q r p : ℕ}
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r) (hp : p.Prime)
    (hχ : χ (p : ZMod q) = 0) :
    PrimePowerEq p (biquadraticCoefficients χ ψ) ψ.zetaMul := by
  have hf : PrimePowerEq p (toArithmeticFunction (χ ·)) 1 := by
    intro k
    rw [primePower_character χ hp, hχ,primePower_one hp]
  have hh : PrimePowerEq p ((toArithmeticFunction (χ ·)).pmul (toArithmeticFunction (ψ ·))) 1 := by
    intro k
    rw [ArithmeticFunction.pmul_apply,primePower_character χ hp,primePower_character ψ hp,
      hχ,←mul_pow,zero_mul,primePower_one hp]
  have h := ((PrimePowerEq.refl p (ArithmeticFunction.zeta : ArithmeticFunction ℂ)).mul hp hf).mul hp
    (PrimePowerEq.refl p (toArithmeticFunction (ψ ·))) |>.mul hp hh
  simpa only [mul_one,biquadraticCoefficients,DirichletCharacter.zetaMul] using h

lemma biquadratic_prime_one {q r p : ℕ}
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r) (hp : p.Prime)
    (hχ : χ (p : ZMod q) = 1) :
    PrimePowerEq p (biquadraticCoefficients χ ψ) (ψ.zetaMul*ψ.zetaMul) := by
  have hf : PrimePowerEq p (toArithmeticFunction (χ ·)) ArithmeticFunction.zeta := by
    intro k
    rw [primePower_character χ hp,hχ,one_pow,primePower_zeta hp]
  have hh : PrimePowerEq p ((toArithmeticFunction (χ ·)).pmul (toArithmeticFunction (ψ ·)))
      (toArithmeticFunction (ψ ·)) := by
    intro k
    rw [ArithmeticFunction.pmul_apply,primePower_character χ hp,hχ,one_pow,one_mul]
  have h := ((PrimePowerEq.refl p (ArithmeticFunction.zeta : ArithmeticFunction ℂ)).mul hp hf).mul hp
    (PrimePowerEq.refl p (toArithmeticFunction (ψ ·))) |>.mul hp hh
  have he : (ArithmeticFunction.zeta : ArithmeticFunction ℂ)*ArithmeticFunction.zeta*
      toArithmeticFunction (ψ ·)*toArithmeticFunction (ψ ·) = ψ.zetaMul*ψ.zetaMul := by
    unfold DirichletCharacter.zetaMul
    ring
  simpa only [he,biquadraticCoefficients] using h

lemma biquadratic_prime_neg_one {q r p : ℕ}
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r) (hp : p.Prime)
    (hχ : χ (p : ZMod q) = -1) (hψ : ψ (p : ZMod r) = -1) :
    PrimePowerEq p (biquadraticCoefficients χ ψ) (χ.zetaMul*χ.zetaMul) := by
  have hg : PrimePowerEq p (toArithmeticFunction (ψ ·)) (toArithmeticFunction (χ ·)) := by
    intro k
    rw [primePower_character ψ hp,primePower_character χ hp,hχ,hψ]
  have hh : PrimePowerEq p ((toArithmeticFunction (χ ·)).pmul (toArithmeticFunction (ψ ·)))
      ArithmeticFunction.zeta := by
    intro k
    rw [ArithmeticFunction.pmul_apply,primePower_character χ hp,primePower_character ψ hp,
      hχ,hψ,←mul_pow,neg_mul_neg,one_mul,one_pow,primePower_zeta hp]
  have h := ((PrimePowerEq.refl p (ArithmeticFunction.zeta : ArithmeticFunction ℂ)).mul hp
    (PrimePowerEq.refl p (toArithmeticFunction (χ ·)))).mul hp hg |>.mul hp hh
  have he : (ArithmeticFunction.zeta : ArithmeticFunction ℂ)*toArithmeticFunction (χ ·)*
      toArithmeticFunction (χ ·)*ArithmeticFunction.zeta = χ.zetaMul*χ.zetaMul := by
    unfold DirichletCharacter.zetaMul
    ring
  simpa only [he,biquadraticCoefficients] using h

lemma biquadraticCoefficients_nonneg {q r : ℕ} {χ : DirichletCharacter ℂ q}
    {ψ : DirichletCharacter ℂ r} (hχ : χ^2=1) (hψ : ψ^2=1) (n : ℕ) :
    0 ≤ biquadraticCoefficients χ ψ n := by
  have hp (p : ℕ) (hp : p.Prime) (k : ℕ) : 0 ≤ biquadraticCoefficients χ ψ (p^k) := by
    rcases MulChar.isQuadratic_iff_sq_eq_one.mpr hχ (p:ZMod q) with h0|h1|hm
    · rw [biquadratic_prime_zero χ ψ hp h0 k]
      exact DirichletCharacter.zetaMul_nonneg hψ _
    · rw [biquadratic_prime_one χ ψ hp h1 k]
      exact arithmetic_convolution_nonneg (DirichletCharacter.zetaMul_nonneg hψ)
        (DirichletCharacter.zetaMul_nonneg hψ) _
    · rcases MulChar.isQuadratic_iff_sq_eq_one.mpr hψ (p:ZMod r) with h0|h1|hm'
      · rw [biquadraticCoefficients_comm χ ψ,biquadratic_prime_zero ψ χ hp h0 k]
        exact DirichletCharacter.zetaMul_nonneg hχ _
      · rw [biquadraticCoefficients_comm χ ψ,biquadratic_prime_one ψ χ hp h1 k]
        exact arithmetic_convolution_nonneg (DirichletCharacter.zetaMul_nonneg hχ)
          (DirichletCharacter.zetaMul_nonneg hχ) _
      · rw [biquadratic_prime_neg_one χ ψ hp hm hm' k]
        exact arithmetic_convolution_nonneg (DirichletCharacter.zetaMul_nonneg hχ)
          (DirichletCharacter.zetaMul_nonneg hχ) _
  rcases eq_or_ne n 0 with rfl|hn
  · simp
  · simpa only [(biquadraticCoefficients_multiplicative χ ψ).multiplicative_factorization _ hn,
      Finsupp.prod, Nat.support_factorization] using
      Finset.prod_nonneg (fun p hp' => hp p (Nat.prime_of_mem_primeFactors hp') _)

end LargePrimeGaps
end OAI

-- Source module: SiegelBounds
namespace OAI
namespace LargePrimeGaps
section
open Complex Filter Topology Set MeasureTheory Finset ArithmeticFunction
lemma quadratic_character_im {q : ℕ} {χ : DirichletCharacter ℂ q} (hχ : χ^2=1)
    (a : ZMod q) : (χ a).im = 0 := by
  rcases MulChar.isQuadratic_iff_sq_eq_one.mpr hχ a with h|h|h <;> simp [h]

lemma regularSeries_im_zero {f : ℕ → ℂ} {c : ℂ} {D : ℝ}
    (hf : ∀ n, (f n).im=0) (hc : c.im=0) (hD : 0 ≤ D)
    (hb : ∀ t, 1<t → ‖seriesDiscrepancy f c t‖ ≤ D) {x : ℝ} (hx : 0<x) :
    (regularSeries f c x).im=0 := by
  have hi := discrepancyTail_integrable zero_lt_one hD (measurable_seriesDiscrepancy f c) hb
    (show 0<(x:ℂ).re from hx)
  have he : (discrepancyTail (seriesDiscrepancy f c) 1 x).im=0 := by
    unfold discrepancyTail
    change RCLike.im (∫ t in Ioi (1:ℝ), seriesDiscrepancy f c t*(t:ℂ)^(-((x:ℂ)+1)))=0
    rw [←integral_im hi]
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hp : ((t:ℂ)^(-((x:ℂ)+1))).im=0 := by
      rw [show -((x:ℂ)+1)= (-(x+1):ℝ) by push_cast; rfl,
        ←Complex.ofReal_cpow (by exact (zero_lt_one.trans ht).le : 0≤t)]
      rfl
    change (seriesDiscrepancy f c t * (t:ℂ)^(-((x:ℂ)+1))).im=0
    rw [Complex.mul_im,hp,mul_zero,zero_add]
    have hz : (seriesDiscrepancy f c t).im=0 := by simp [seriesDiscrepancy,Complex.mul_im,hc,hf]
    rw [hz,zero_mul]
  simp [regularSeries,Complex.mul_im,hc,he]

lemma quadratic_LFunction_im {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ≠1) (hχ2 : χ^2=1) {x : ℝ} (hx : 0<x) : (χ.LFunction x).im=0 := by
  rw [←regularSeries_character_eq hχ hx]
  apply regularSeries_im_zero _ (by simp) (by positivity : (0:ℝ)≤q+1)
    (fun t _ => discrepancy_character_bound hχ t) hx
  intro n
  simp only [positiveCoefficients]
  split_ifs <;> simp [quadratic_character_im hχ2]

lemma LSeries_character_summable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1<s.re) :
    LSeriesSummable (toArithmeticFunction (fun n : ℕ => χ (n : ZMod q))) s := by
  apply (LSeriesSummable_congr _ (fun h => (χ.apply_eq_toArithmeticFunction_apply h).symm)).mpr
  exact ZMod.LSeriesSummable_of_one_lt_re χ hs

lemma LSeries_character_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1<s.re) :
    LSeries (toArithmeticFunction (fun n : ℕ => χ (n : ZMod q))) s = χ.LFunction s := by
  rw [χ.LFunction_eq_LSeries hs]
  exact (LSeries_congr χ.apply_eq_toArithmeticFunction_apply s).symm

lemma LSeries_zeta_complex_eq {s : ℂ} (hs : 1<s.re) :
    LSeries (ArithmeticFunction.zeta : ArithmeticFunction ℂ) s=riemannZeta s := by
  rw [←LSeries_one_eq_riemannZeta hs]
  apply LSeries_congr
  intro n hn
  simp [hn]

lemma LSeries_zetaMul_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1<s.re) : LSeries χ.zetaMul s=riemannZeta s*χ.LFunction s := by
  have hz : LSeriesSummable (ArithmeticFunction.zeta : ArithmeticFunction ℂ) s := by
    apply LSeriesSummable_of_bounded_of_one_lt_re (m:=1) _ hs
    intro n hn
    simp [hn]
  rw [DirichletCharacter.zetaMul,ArithmeticFunction.LSeries_mul' hz
    (LSeries_character_summable χ hs),LSeries_character_eq χ hs,LSeries_zeta_complex_eq hs]

open scoped ComplexOrder in
lemma quadratic_LFunction_re_pos_of_one_lt {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ2 : χ^2=1) {x : ℝ} (hx : 1<x) :
    0<(χ.LFunction x).re := by
  have hp := LSeries.positive (DirichletCharacter.zetaMul_nonneg hχ2)
    (χ.isMultiplicative_zetaMul.map_one ▸ zero_lt_one)
    (lt_of_le_of_lt (LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
      (fun s hs => χ.LSeriesSummable_zetaMul hs)) (show (1:EReal)<x by exact_mod_cast hx))
  rw [LSeries_zetaMul_eq χ hx] at hp
  have hr := (Complex.pos_iff.mp hp).1
  rw [Complex.mul_re,riemannZeta_im_eq_zero_of_one_lt hx,zero_mul,sub_zero] at hr
  exact (mul_pos_iff.mp hr).resolve_right (fun h => (riemannZeta_re_pos_of_one_lt hx).not_ge h.1.le) |>.2

lemma quadratic_LFunction_re_pos_one {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ≠1) (hχ2 : χ^2=1) : 0<(χ.LFunction 1).re := by
  have hc : Continuous (fun x : ℝ => (χ.LFunction x).re) :=
    Complex.continuous_re.comp ((DirichletCharacter.differentiable_LFunction hχ).continuous.comp
      Complex.continuous_ofReal)
  have hn : 0≤(χ.LFunction 1).re := by
    apply ge_of_tendsto (hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds :
      Tendsto (fun x : ℝ => (χ.LFunction x).re) (𝓝[>] 1) (𝓝 ((χ.LFunction 1).re)))
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (quadratic_LFunction_re_pos_of_one_lt hχ2 hx).le
  refine lt_of_le_of_ne hn ?_
  intro he
  apply DirichletCharacter.LFunction_apply_one_ne_zero hχ
  apply Complex.ext
  · simpa using he.symm
  · simpa using quadratic_LFunction_im hχ hχ2 (x:=1) zero_lt_one

lemma quadratic_LFunction_re_pos_of_no_root {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ≠1) (hχ2 : χ^2=1)
    {β : ℝ} (hβ : 0<β) (hβ1 : β≤1)
    (hz : ∀ x ∈ Set.Icc β 1, χ.LFunction x≠0) : 0<(χ.LFunction β).re := by
  by_contra! hn
  have hc : Continuous (fun x : ℝ => (χ.LFunction x).re) :=
    Complex.continuous_re.comp ((DirichletCharacter.differentiable_LFunction hχ).continuous.comp
      Complex.continuous_ofReal)
  obtain ⟨x,hx,hxe⟩ := intermediate_value_Icc hβ1 hc.continuousOn
    (show (0:ℝ) ∈ Set.Icc ((χ.LFunction β).re) ((χ.LFunction 1).re) from
      ⟨hn,(quadratic_LFunction_re_pos_one hχ hχ2).le⟩)
  apply hz x hx
  apply Complex.ext
  · simpa using hxe
  · simpa using quadratic_LFunction_im hχ hχ2 (hβ.trans_le hx.1)

end
section
open Complex Finset ArithmeticFunction
noncomputable def productCharacter {q r : ℕ} (χ : DirichletCharacter ℂ q)
    (ψ : DirichletCharacter ℂ r) : DirichletCharacter ℂ (q*r) :=
  χ.changeLevel (dvd_mul_right q r) * ψ.changeLevel (dvd_mul_left r q)

lemma changeLevel_natCast {q m : ℕ} (χ : DirichletCharacter ℂ q) (hqm : q∣m)
    {n : ℕ} (hn : n.Coprime m) :
    χ.changeLevel hqm (n : ZMod m)=χ (n : ZMod q) := by
  have h := χ.changeLevel_eq_cast_of_dvd hqm (ZMod.unitOfCoprime n hn)
  simp only [ZMod.coe_unitOfCoprime] at h
  rw [ZMod.cast_natCast hqm] at h
  exact h

lemma productCharacter_apply {q r n : ℕ} (χ : DirichletCharacter ℂ q)
    (ψ : DirichletCharacter ℂ r) : productCharacter χ ψ (n : ZMod (q*r))=
      χ (n : ZMod q)*ψ (n : ZMod r) := by
  by_cases hn : n.Coprime (q*r)
  · simp only [productCharacter,MulChar.mul_apply,changeLevel_natCast _ _ hn]
  · rw [MulChar.map_nonunit _ (by rwa [ZMod.isUnit_iff_coprime])]
    by_cases hq : n.Coprime q
    · have hr : ¬n.Coprime r := fun hr => hn (hq.mul_right hr)
      rw [ψ.map_nonunit (by rwa [ZMod.isUnit_iff_coprime]),mul_zero]
    · rw [χ.map_nonunit (by rwa [ZMod.isUnit_iff_coprime]),zero_mul]

lemma productCharacter_quadratic {q r : ℕ} {χ : DirichletCharacter ℂ q}
    {ψ : DirichletCharacter ℂ r} (hχ : χ^2=1) (hψ : ψ^2=1) :
    (productCharacter χ ψ)^2=1 := by
  simp [productCharacter,mul_pow,←map_pow,hχ,hψ]

lemma productCharacter_ne_one_of_levels_ne {q r : ℕ} [NeZero q] [NeZero r]
    {χ : DirichletCharacter ℂ q} {ψ : DirichletCharacter ℂ r}
    (hχ : χ.IsPrimitive) (hψ : ψ.IsPrimitive) (hψ2 : ψ^2=1) (hqr : q≠r) :
    productCharacter χ ψ≠1 := by
  intro h
  have h2 : (ψ.changeLevel (dvd_mul_left r q))^2=1 := by rw [←map_pow,hψ2,map_one]
  have he : χ.changeLevel (dvd_mul_right q r) = ψ.changeLevel (dvd_mul_left r q) := by
    calc
      _ = (χ.changeLevel (dvd_mul_right q r)*ψ.changeLevel (dvd_mul_left r q))*
          ψ.changeLevel (dvd_mul_left r q) := by rw [mul_assoc,←pow_two,h2,mul_one]
      _ = _ := by rw [show χ.changeLevel (dvd_mul_right q r)*ψ.changeLevel (dvd_mul_left r q)=1 from h,one_mul]
  have hc := congrArg DirichletCharacter.conductor he
  rw [DirichletCharacter.conductor_changeLevel,DirichletCharacter.conductor_changeLevel,
    hχ,hψ] at hc
  exact hqr hc

lemma productCharacter_toArithmeticFunction {q r : ℕ} (χ : DirichletCharacter ℂ q)
    (ψ : DirichletCharacter ℂ r) :
    toArithmeticFunction (productCharacter χ ψ ·)=
      (toArithmeticFunction (χ ·)).pmul (toArithmeticFunction (ψ ·)) := by
  ext n
  by_cases hn : n=0
  · simp [hn]
  · rw [ArithmeticFunction.pmul_apply]
    simp [toArithmeticFunction,hn,productCharacter_apply]

end
section
open Complex Filter Topology Set MeasureTheory Finset
open scoped ComplexOrder in
lemma zeta_product_residue_lower {P : ℂ → ℂ} {a : ℕ → ℂ} {A B Q β ε : ℝ}
    (hP : DifferentiableOn ℂ P {s : ℂ | 0<s.re})
    (hB : 0≤B) (hb : ∀ s ∈ Metric.closedBall (2:ℂ) (7/4:ℝ), ‖P s‖≤B)
    (hA : 0≤A) (hQ : 2≤Q) (hQA : 12*A≤Q) (hBQ : 21*B≤A*Q^4)
    (hβ : 3/4≤β) (hβ1 : β<1) (hβε : 60*(1-β)≤ε)
    (ha : ∀ n, 0≤a n) (ha1 : 1≤a 1) (haC : LSeries.abscissaOfAbsConv a≤1)
    (haP : ∀ s : ℂ, 1<s.re → LSeries a s=riemannZeta s*P s)
    (hvalue : (riemannZeta β*P β).re≤0) (hreal : (P 1).im=0) :
    ((1-β)/(2*(2-β)))*Q^(-ε)≤(P 1).re := by
  let H := regularizedZetaProduct P
  have hR : P 1=((P 1).re:ℂ) := by apply Complex.ext <;> simp [hreal]
  obtain ⟨hf,hbound⟩ := regularizedZetaProduct_bound hP hB hb
  have he : H =ᶠ[𝓝 (2:ℂ)] fun s => LSeries a s-((P 1).re:ℂ)/(s-1) := by
    filter_upwards [(continuous_re.tendsto (2:ℂ)).eventually
      (lt_mem_nhds (by norm_num : (1:ℝ)<(2:ℂ).re))] with s hs
    have hs1 : s≠1 := by intro h; simp [h] at hs
    rw [show H s=regularizedZetaProduct P s from rfl,regularizedZetaProduct_eq (by linarith) hs1,
      ←haP s hs,hR]
    simp only [Complex.ofReal_re]
  have hac : LSeries.abscissaOfAbsConv a<(2:ℝ) := haC.trans_lt (by exact_mod_cast (show (1:ℝ)<2 by norm_num))
  obtain ⟨ha0,han⟩ := signedTaylorCoeff_regular_nonneg ha ha1 hac he
  have hz : 1<2-β := by linarith
  have hz0 : 0<2-β := by linarith
  have hzr : 2-β<(3/2:ℝ) := by linarith
  have hv : (∑' n : ℕ, signedTaylorCoeff H n*(2-β)^n)≤(P 1).re/((2-β)-1) := by
    rw [(signedTaylorCoeff_hasSum hf.differentiableOn (by rwa [abs_of_pos hz0])).tsum_eq]
    have hβ0 : 0<β := by linarith
    have hβne : (β:ℂ)≠1 := by intro h; have := congrArg Complex.re h; simp at this; linarith
    rw [show (2-(2-β):ℝ)=β by ring]
    change (regularizedZetaProduct P β).re≤_
    rw [regularizedZetaProduct_eq hβ0 hβne,Complex.sub_re,hR,
      ←Complex.ofReal_one,←Complex.ofReal_sub,←Complex.ofReal_div,Complex.ofReal_re]
    have hid : (P 1).re/(β-1) = -(P 1).re/((2-β)-1) := by
      rw [show β-1 = -((2-β)-1) by ring,div_neg,neg_div]
    simp only [Complex.ofReal_one,Complex.ofReal_re]
    rw [hid,neg_div,sub_neg_eq_add]
    exact add_le_of_nonpos_left hvalue
  have hn (n : ℕ) : |signedTaylorCoeff H n|≤(A*Q^4)/(3/2)^n := by
    apply (signedTaylorCoeff_norm_bound (by norm_num : (0:ℝ)<3/2) hf
      (fun s hs => (hbound s (Metric.sphere_subset_closedBall hs)).trans hBQ) n)
  have hr := residue_polynomial_lower (ε:=ε) hA hQ hQA hz (by linarith) (by linarith) hn
    (by simpa [signedTaylorCoeff] using ha0) han hv
  convert hr using 1
  congr 2
  ring

lemma zeta_re_neg_near_one {β : ℝ} (hβ : 99/100≤β) (hβ1 : β<1) :
    (riemannZeta β).re<0 := by
  have hβ0 : 0<β := by linarith
  have hβne : (β:ℂ)≠1 := by intro h; have := congrArg Complex.re h; simp at this; linarith
  have hmem : (β:ℂ) ∈ Metric.closedBall 2 (7/4:ℝ) := by
    rw [Metric.mem_closedBall,dist_eq_norm,←Complex.ofReal_ofNat,←Complex.ofReal_sub,
      Complex.norm_real,Real.norm_eq_abs,abs_of_neg (by linarith : β-2<0)]
    linarith
  have hb := (Complex.re_le_norm (zetaRegular β)).trans (zetaRegular_norm_le_seventeen hmem)
  rw [zetaRegular_eq hβ0 hβne,Complex.sub_re,←Complex.ofReal_one,
    ←Complex.ofReal_sub,←Complex.ofReal_div,Complex.ofReal_re] at hb
  have hd : 1/(β-1)≤-100 := (div_le_iff_of_neg (by linarith : β-1<0)).mpr (by linarith)
  linarith

end
open Complex Filter Topology Set MeasureTheory Finset ArithmeticFunction
lemma LSeries_zeta_complex_summable {s : ℂ} (hs : 1<s.re) :
    LSeriesSummable (ArithmeticFunction.zeta : ArithmeticFunction ℂ) s := by
  apply LSeriesSummable_of_bounded_of_one_lt_re (m:=1) _ hs
  intro n hn
  simp [hn]

lemma biquadraticCoefficients_summable {q r : ℕ} [NeZero q] [NeZero r]
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r) {s : ℂ} (hs : 1<s.re) :
    LSeriesSummable (biquadraticCoefficients χ ψ) s := by
  rw [biquadraticCoefficients,←productCharacter_toArithmeticFunction]
  exact ArithmeticFunction.LSeriesSummable_mul
    (ArithmeticFunction.LSeriesSummable_mul
      (ArithmeticFunction.LSeriesSummable_mul (LSeries_zeta_complex_summable hs) (LSeries_character_summable χ hs))
      (LSeries_character_summable ψ hs)) (LSeries_character_summable (productCharacter χ ψ) hs)

lemma LSeries_biquadratic_eq {q r : ℕ} [NeZero q] [NeZero r]
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r) {s : ℂ} (hs : 1<s.re) :
    LSeries (biquadraticCoefficients χ ψ) s=
      riemannZeta s*(χ.LFunction s*ψ.LFunction s*(productCharacter χ ψ).LFunction s) := by
  have hz := LSeries_zeta_complex_summable hs
  have hχ := LSeries_character_summable χ hs
  have hψ := LSeries_character_summable ψ hs
  have hp := LSeries_character_summable (productCharacter χ ψ) hs
  rw [biquadraticCoefficients,←productCharacter_toArithmeticFunction,
    ArithmeticFunction.LSeries_mul' (ArithmeticFunction.LSeriesSummable_mul (ArithmeticFunction.LSeriesSummable_mul hz hχ) hψ) hp,
    ArithmeticFunction.LSeries_mul' (ArithmeticFunction.LSeriesSummable_mul hz hχ) hψ,
    ArithmeticFunction.LSeries_mul' hz hχ,LSeries_zeta_complex_eq hs,
    LSeries_character_eq χ hs,LSeries_character_eq ψ hs,
    LSeries_character_eq (productCharacter χ ψ) hs]
  ring

lemma quadratic_residue_lower_of_no_root {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ≠1) (hχ2 : χ^2=1)
    {β ε : ℝ} (hβ : 99/100≤β) (hβ1 : β<1) (hβε : 60*(1-β)≤ε)
    (hq : (4032:ℝ)≤q+1) (hz : ∀ x ∈ Set.Icc β 1, χ.LFunction x≠0) :
    ((1-β)/(2*(2-β)))*((q:ℝ)+1)^(-ε)≤‖χ.LFunction 1‖ := by
  have hQ : (2:ℝ)≤q+1 := by linarith
  have hpow : (q:ℝ)+1≤((q:ℝ)+1)^4 := le_self_pow₀ (by linarith) (by norm_num)
  have hv : (riemannZeta β*χ.LFunction β).re≤0 := by
    rw [Complex.mul_re,quadratic_LFunction_im hχ hχ2 (by linarith),mul_zero,sub_zero]
    exact mul_nonpos_of_nonpos_of_nonneg (zeta_re_neg_near_one hβ hβ1).le
      (quadratic_LFunction_re_pos_of_no_root hχ hχ2 (by linarith) hβ1.le hz).le
  apply le_trans _ (Complex.re_le_norm _)
  apply zeta_product_residue_lower (a:=χ.zetaMul) (A:=336) (B:=16*((q:ℝ)+1))
    (DirichletCharacter.differentiable_LFunction hχ).differentiableOn (by positivity)
    (fun s hs => LFunction_norm_polynomial hχ hs) (by norm_num) hQ
    (by norm_num; exact hq) (by nlinarith) (by linarith) hβ1 hβε
    (DirichletCharacter.zetaMul_nonneg hχ2)
    (by simp only [χ.isMultiplicative_zetaMul.map_one,le_refl])
    (LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable (fun s hs => χ.LSeriesSummable_zetaMul hs))
    (fun s hs => LSeries_zetaMul_eq χ hs) hv
    (by simpa using quadratic_LFunction_im hχ hχ2 (x:=1) zero_lt_one)

lemma biquadratic_norm_bound {q r : ℕ} [NeZero q] [NeZero r]
    {χ : DirichletCharacter ℂ q} {ψ : DirichletCharacter ℂ r}
    (hχ : χ≠1) (hψ : ψ≠1) (hp : productCharacter χ ψ≠1)
    {s : ℂ} (hs : s ∈ Metric.closedBall 2 (7/4:ℝ)) :
    ‖χ.LFunction s*ψ.LFunction s*(productCharacter χ ψ).LFunction s‖≤
      16^3*((q:ℝ)+1)^2*((r:ℝ)+1)^2 := by
  have hq0 : (0:ℝ)≤q := Nat.cast_nonneg q
  have hr0 : (0:ℝ)≤r := Nat.cast_nonneg r
  have hp' := LFunction_norm_polynomial hp hs
  simp only [Nat.cast_mul] at hp'
  calc
    _ ≤ (16*((q:ℝ)+1))*(16*((r:ℝ)+1))*(16*((q:ℝ)*r+1)) := by
      simp only [norm_mul]
      gcongr
      · exact LFunction_norm_polynomial hχ hs
      · exact LFunction_norm_polynomial hψ hs
    _ ≤ _ := by nlinarith [mul_nonneg hq0 hr0]

lemma biquadratic_residue_lower_of_root {q r : ℕ} [NeZero q] [NeZero r]
    {χ : DirichletCharacter ℂ q} {ψ : DirichletCharacter ℂ r}
    (hχ : χ≠1) (hχ2 : χ^2=1) (hψ : ψ≠1) (hψ2 : ψ^2=1)
    (hp : productCharacter ψ χ≠1) {β ε : ℝ}
    (hβ : 3/4≤β) (hβ1 : β<1) (hβε : 60*(1-β)≤ε)
    (hq : (12*(21*16^3*((r:ℝ)+1)^2))≤q+1) (hq1 : (2:ℝ)≤q+1)
    (hz : ψ.LFunction β=0) :
    ((1-β)/(2*(2-β)))*((q:ℝ)+1)^(-ε)≤
      ‖ψ.LFunction 1‖*‖χ.LFunction 1‖*‖(productCharacter ψ χ).LFunction 1‖ := by
  let P := fun s => ψ.LFunction s*χ.LFunction s*(productCharacter ψ χ).LFunction s
  have hd : Differentiable ℂ P :=
    ((DirichletCharacter.differentiable_LFunction hψ).mul
      (DirichletCharacter.differentiable_LFunction hχ)).mul
      (DirichletCharacter.differentiable_LFunction hp)
  have hpow : ((q:ℝ)+1)^2≤((q:ℝ)+1)^4 :=
    pow_le_pow_right₀ (by linarith) (by norm_num)
  have hb : ∀ s ∈ Metric.closedBall (2:ℂ) (7/4:ℝ),
      ‖P s‖≤16^3*((r:ℝ)+1)^2*((q:ℝ)+1)^2 := fun s hs => biquadratic_norm_bound hψ hχ hp hs
  have hiψ : (ψ.LFunction 1).im=0 := by simpa using quadratic_LFunction_im hψ hψ2 (x:=1) zero_lt_one
  have hiχ : (χ.LFunction 1).im=0 := by simpa using quadratic_LFunction_im hχ hχ2 (x:=1) zero_lt_one
  have hip : ((productCharacter ψ χ).LFunction 1).im=0 := by
    simpa using quadratic_LFunction_im hp (productCharacter_quadratic hψ2 hχ2) (x:=1) zero_lt_one
  have hreal : (P 1).im=0 := by simp [P,Complex.mul_im,hiψ,hiχ,hip]
  have hR := zeta_product_residue_lower (P:=P) (a:=biquadraticCoefficients ψ χ)
    (A:=21*16^3*((r:ℝ)+1)^2) (B:=16^3*((r:ℝ)+1)^2*((q:ℝ)+1)^2)
    hd.differentiableOn (by positivity) hb (by positivity) hq1 hq
    (by nlinarith [mul_le_mul_of_nonneg_left hpow (by positivity : (0:ℝ)≤21*16^3*((r:ℝ)+1)^2)])
    hβ hβ1 hβε (biquadraticCoefficients_nonneg hψ2 hχ2)
    (by simp only [(biquadraticCoefficients_multiplicative ψ χ).map_one,le_refl])
    (LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
      (fun s hs => biquadraticCoefficients_summable ψ χ hs))
    (fun s hs => LSeries_biquadratic_eq ψ χ hs) (by simp [P,hz]) hreal
  have := hR.trans (Complex.re_le_norm (P 1))
  simpa only [P,norm_mul] using this

lemma quadratic_siegel_eventual {ε : ℝ} (hε : 0<ε) (hε1 : ε≤1) :
    ∃ c Q₀ : ℝ, 0<c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → χ≠1 → χ^2=1 → Q₀≤(q:ℝ)+1 → c*((q:ℝ)+1)^(-ε)≤‖χ.LFunction 1‖ := by
  classical
  let β₀ : ℝ := 1-ε/240
  have hβ₀ : 99/100≤β₀ := by dsimp [β₀]; linarith
  have hβ₀1 : β₀<1 := by dsimp [β₀]; linarith
  by_cases hex : ∃ r : ℕ, ∃ ψ : DirichletCharacter ℂ (r+1),
      ψ.IsPrimitive ∧ ψ≠1 ∧ ψ^2=1 ∧ ∃ β ∈ Set.Icc β₀ 1, ψ.LFunction β=0
  · obtain ⟨r,ψ,hψprim,hψ,hψ2,β,hβI,hzero⟩ := hex
    have hβ1 : β<1 := lt_of_le_of_ne hβI.2 (by
      intro he
      apply DirichletCharacter.LFunction_apply_one_ne_zero hψ
      simpa [he] using hzero)
    have hβ : 99/100≤β := hβ₀.trans hβI.1
    have hβε : 60*(1-β)≤ε/2 := by dsimp [β₀] at hβI; linarith [hβI.1]
    obtain ⟨K,hK,hgrowth⟩ := LFunction_norm_small_power (by linarith : 0<ε/4)
      (by linarith : ε/4≤1/2)
    let D : ℝ := 3*((r:ℝ)+3)
    let U : ℝ := ‖ψ.LFunction 1‖*K*D^(ε/2)
    have hD : 0<D := by dsimp [D]; positivity
    have hU : 0<U := by
      exact mul_pos (mul_pos (norm_pos_iff.mpr (DirichletCharacter.LFunction_apply_one_ne_zero hψ)) hK)
        (Real.rpow_pos_of_pos hD _)
    let c : ℝ := (1-β)/(2*(2-β))/U
    have hc : 0<c := div_pos (div_pos (by linarith) (by linarith)) hU
    refine ⟨c,max (12*(21*16^3*(((r+1:ℕ):ℝ)+1)^2)) ((r:ℝ)+3),hc,?_⟩
    intro q _ χ hχprim hχ hχ2 hq
    have hq1 : (2:ℝ)≤q+1 := by have := (le_max_right _ _).trans hq; have : (0:ℝ)≤r := Nat.cast_nonneg r; linarith
    have hqr : r+1≠q := by
      have hr := (le_max_right _ _).trans hq
      intro he
      rw [←he] at hr
      push_cast at hr
      linarith
    have hp : productCharacter ψ χ≠1 :=
      productCharacter_ne_one_of_levels_ne hψprim hχprim hχ2 hqr
    have hl := biquadratic_residue_lower_of_root hχ hχ2 hψ hψ2 hp
      (by linarith) hβ1 hβε ((le_max_left _ _).trans hq) hq1 hzero
    have hb := hgrowth ((r+1)*q) (productCharacter ψ χ) hp 1 (by simp; linarith)
    have hQ0 : 0<(q:ℝ)+1 := by positivity
    have he : 2*(ε/4)=ε/2 := by ring
    rw [he] at hb
    have hbase : (((r+1)*q:ℕ):ℝ)+2≤((r:ℝ)+3)*((q:ℝ)+1) := by push_cast; nlinarith [Nat.cast_nonneg (α:=ℝ) q,Nat.cast_nonneg (α:=ℝ) r]
    have hb' : ‖(productCharacter ψ χ).LFunction 1‖≤K*D^(ε/2)*((q:ℝ)+1)^(ε/2) := by
      apply hb.trans
      simp only [norm_one]
      calc
        K*(((((r+1)*q:ℕ):ℝ)+2)*(1+2))^(ε/2) ≤ K*(D*((q:ℝ)+1))^(ε/2) := by
          apply mul_le_mul_of_nonneg_left _ hK.le
          apply Real.rpow_le_rpow (by positivity) _ (by linarith)
          dsimp [D]
          nlinarith
        _ = _ := by rw [Real.mul_rpow hD.le hQ0.le]; ring
    have hupper : ‖ψ.LFunction 1‖*‖χ.LFunction 1‖*‖(productCharacter ψ χ).LFunction 1‖≤
        U*((q:ℝ)+1)^(ε/2)*‖χ.LFunction 1‖ := by
      calc
        _ ≤ ‖ψ.LFunction 1‖*‖χ.LFunction 1‖*(K*D^(ε/2)*((q:ℝ)+1)^(ε/2)) := by gcongr
        _ = _ := by dsimp [U]; ring
    have hlow := hl.trans hupper
    have hQp : 0<((q:ℝ)+1)^(ε/2) := Real.rpow_pos_of_pos hQ0 _
    have hexp : ((q:ℝ)+1)^(-ε)*((q:ℝ)+1)^(ε/2)=((q:ℝ)+1)^(-(ε/2)) := by
      rw [←Real.rpow_add hQ0]; congr 1; ring
    have hfinal : U*(c*((q:ℝ)+1)^(-ε)*((q:ℝ)+1)^(ε/2)) ≤
        U*(‖χ.LFunction 1‖*((q:ℝ)+1)^(ε/2)) := by
      calc
        U*(c*((q:ℝ)+1)^(-ε)*((q:ℝ)+1)^(ε/2)) =
            ((1-β)/(2*(2-β)))*((q:ℝ)+1)^(-(ε/2)) := by
          rw [mul_assoc c,hexp]
          dsimp [c]
          field_simp
        _ ≤ U*(‖χ.LFunction 1‖*((q:ℝ)+1)^(ε/2)) := by simpa only [mul_assoc,mul_left_comm,mul_comm] using hlow
    exact (mul_le_mul_iff_left₀ hQp).mp ((mul_le_mul_iff_right₀ hU).mp hfinal)
  · refine ⟨(1-β₀)/(2*(2-β₀)),4032,div_pos (by linarith) (by linarith),?_⟩
    intro q hq χ hχprim hχ hχ2 hqbig
    apply quadratic_residue_lower_of_no_root hχ hχ2 hβ₀ hβ₀1
      (by dsimp [β₀]; linarith) hqbig
    intro x hx hz
    apply hex
    cases q with
    | zero => exact (NeZero.ne 0 rfl).elim
    | succ q => exact ⟨q,χ,hχprim,hχ,hχ2,x,hx,hz⟩

lemma finite_positive_lower {ι : Type*} (S : Finset ι) (f : ι → ℝ)
    (hf : ∀ i∈S,0<f i) : ∃ c : ℝ, 0<c ∧ ∀ i∈S,c≤f i := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1,zero_lt_one,by simp⟩
  | @insert a S ha ih =>
    obtain ⟨c,hc,hcb⟩ := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    refine ⟨min c (f a),lt_min hc (hf a (Finset.mem_insert_self _ _)),?_⟩
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl|hi
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (hcb i hi)

lemma LFunction_one_finite_lower (N : ℕ) :
    ∃ c : ℝ, 0<c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      q≤N → χ≠1 → c≤‖χ.LFunction 1‖ := by
  classical
  induction N with
  | zero => exact ⟨1,zero_lt_one,fun q _ χ hq _ => (NeZero.ne q (Nat.eq_zero_of_le_zero hq)).elim⟩
  | succ N ih =>
    obtain ⟨c,hc,hcb⟩ := ih
    obtain ⟨d,hd,hdb⟩ := finite_positive_lower
      ((Finset.univ : Finset (DirichletCharacter ℂ (N+1))).filter (·≠1))
      (fun χ => ‖χ.LFunction 1‖) (fun χ hχ =>
        norm_pos_iff.mpr (DirichletCharacter.LFunction_apply_one_ne_zero (Finset.mem_filter.mp hχ).2))
    refine ⟨min c d,lt_min hc hd,?_⟩
    intro q _ χ hq hχ
    rcases Nat.le_succ_iff_eq_or_le.mp hq with rfl|hq
    · exact (min_le_right _ _).trans (hdb χ (by simp [hχ]))
    · exact (min_le_left _ _).trans (hcb q χ hq hχ)

theorem quadratic_siegel {ε : ℝ} (hε : 0<ε) (hε1 : ε≤1) :
    ∃ c : ℝ, 0<c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → χ≠1 → χ^2=1 → c*((q:ℝ)+1)^(-ε)≤‖χ.LFunction 1‖ := by
  obtain ⟨c,Q₀,hc,hcb⟩ := quadratic_siegel_eventual hε hε1
  obtain ⟨d,hd,hdb⟩ := LFunction_one_finite_lower ⌈Q₀⌉₊
  refine ⟨min c d,lt_min hc hd,?_⟩
  intro q _ χ hχp hχ hχ2
  by_cases hq : Q₀≤(q:ℝ)+1
  · exact (mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.rpow_nonneg (by positivity) _)).trans
      (hcb q χ hχp hχ hχ2 hq)
  · have hqn : q≤⌈Q₀⌉₊ := by
      have := Nat.le_ceil Q₀
      have : (q:ℝ)≤(⌈Q₀⌉₊:ℝ) := by linarith
      exact_mod_cast this
    have hp : ((q:ℝ)+1)^(-ε)≤1 := Real.rpow_le_one_of_one_le_of_nonpos (by have := Nat.cast_nonneg (α:=ℝ) q; linarith) (by linarith)
    exact (mul_le_of_le_one_right (le_of_lt (lt_min hc hd)) hp).trans
      ((min_le_right _ _).trans (hdb q χ hqn hχ))

end LargePrimeGaps
end OAI

-- Source module: ZeroFreeBounds
namespace OAI
namespace LargePrimeGaps
section
open Complex Filter Topology Set MeasureTheory Finset
lemma periodic_sum_norm_le_mul {f : ℕ → ℂ} {q : ℕ} {D : ℝ} (hq : 0<q) (hD : 0≤D)
    (hp : ∀ n,f (q+n)=f n) (hz : ∑ n∈range q,f n=0)
    (hb : ∀ n,‖f n‖≤D) (N : ℕ) : ‖∑ n∈range N,f n‖≤q*D := by
  induction N using Nat.strong_induction_on with
  | ind N ih =>
    by_cases hN : N<q
    · calc
        _ ≤ ∑ n∈range N,‖f n‖ := norm_sum_le _ _
        _ ≤ ∑ _n∈range N,D := sum_le_sum (fun n _ => hb n)
        _ = N*D := by simp
        _ ≤ q*D := mul_le_mul_of_nonneg_right (by exact_mod_cast hN.le) hD
    · have he : q+(N-q)=N := Nat.add_sub_of_le (not_lt.mp hN)
      rw [←he,sum_range_add,hz,zero_add]
      simp_rw [hp]
      exact ih _ (Nat.sub_lt (lt_of_lt_of_le hq (not_lt.mp hN)) hq)

noncomputable def characterMean {q : ℕ} (χ : DirichletCharacter ℂ q) : ℂ :=
  (∑ n∈range q,χ (n : ZMod q))/(q:ℂ)

lemma characterMean_norm_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    ‖characterMean χ‖≤1 := by
  rw [characterMean,norm_div,Complex.norm_natCast]
  apply (div_le_one (by exact_mod_cast NeZero.pos q : (0:ℝ)<q)).mpr
  calc
    _ ≤ ∑ n∈range q,‖χ (n : ZMod q)‖ := norm_sum_le _ _
    _ ≤ ∑ _n∈range q,(1:ℝ) := sum_le_sum (fun n _ => χ.norm_le_one _)
    _ = q := by simp

lemma characterMean_eq_zero {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ≠1) :
    characterMean χ=0 := by simp [characterMean,char_sum_range_zero hχ]

lemma discrepancy_characterMean_bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {t : ℝ} (ht : 1≤t) :
    ‖seriesDiscrepancy (positiveCoefficients (fun n => χ (n : ZMod q))) (characterMean χ) t‖≤2*q+3 := by
  let c := characterMean χ
  have hc : ‖c‖≤1 := characterMean_norm_le χ
  have hb (n : ℕ) : ‖χ (n : ZMod q)-c‖≤2 := (norm_sub_le _ _).trans (by linarith [χ.norm_le_one (n : ZMod q)])
  have hz : ∑ n∈range q,(χ (n : ZMod q)-c)=0 := by
    rw [sum_sub_distrib,sum_const,card_range,nsmul_eq_mul]
    dsimp [c,characterMean]
    have hq : (q:ℂ)≠0 := by exact_mod_cast NeZero.ne q
    field_simp
    ring
  have hr := periodic_sum_norm_le_mul (NeZero.pos q) (by norm_num : (0:ℝ)≤2)
    (f:=fun n => χ (n : ZMod q)-c) (by intro n; simp) hz hb (⌊t⌋₊+1)
  have he : ∑ n∈range (⌊t⌋₊+1),(χ (n : ZMod q)-c) =
      χ (0 : ZMod q)-c+ ∑ n∈Icc 1 ⌊t⌋₊,(χ (n : ZMod q)-c) := by
    rw [Nat.range_succ_eq_Icc_zero,←Finset.insert_Icc_add_one_left_eq_Icc (Nat.zero_le ⌊t⌋₊)]
    simp
    ring
  have ht0 : 0≤t := by linarith
  have hfloor : ‖(⌊t⌋₊:ℂ)-(t:ℂ)‖≤1 := by
    rw [←Complex.ofReal_natCast,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonpos (sub_nonpos.mpr (Nat.floor_le ht0))]
    have := Nat.lt_floor_add_one t
    linarith
  have heq : seriesDiscrepancy (positiveCoefficients (fun n => χ (n : ZMod q))) c t =
      (∑ n∈range (⌊t⌋₊+1),(χ (n : ZMod q)-c))-(χ 0-c)+c*((⌊t⌋₊:ℂ)-(t:ℂ)) := by
    rw [he]
    simp only [seriesDiscrepancy,sum_positiveCoefficients,sum_sub_distrib,sum_const,Nat.card_Icc,
      Nat.add_sub_cancel,nsmul_eq_mul]
    ring
  rw [heq]
  calc
    _ ≤ ‖∑ n∈range (⌊t⌋₊+1),(χ (n : ZMod q)-c)‖+‖χ 0-c‖+‖c*((⌊t⌋₊:ℂ)-(t:ℂ))‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ (q:ℝ)*2+2+1 := by
      gcongr
      · simpa using hb 0
      · rw [norm_mul]; exact (mul_le_mul hc hfloor (norm_nonneg _) zero_le_one).trans_eq (by ring)
    _ = _ := by ring

lemma LFunction_regularSeries_characterMean {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1<s.re) :
    χ.LFunction s = regularSeries (positiveCoefficients (fun n => χ (n : ZMod q))) (characterMean χ) s+
      characterMean χ/(s-1) := by
  rw [regularSeries_eq_LSeries_sub (positiveCoefficients_norm_le (fun n => χ.norm_le_one _))
    (by positivity : (0:ℝ)≤2*q+3) (fun t ht => discrepancy_characterMean_bound χ ht.le) hs,
    sub_add_cancel,LSeries_positiveCoefficients,←χ.LFunction_eq_LSeries hs]

lemma LFunction_deriv_norm_small_power {ε : ℝ} (hε : 0<ε) (hε1 : ε≤1/2) :
    ∃ K : ℝ,0<K ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),χ≠1 →
      ∀ s : ℂ,1-ε/2 ≤ s.re → ‖deriv χ.LFunction s‖≤K*((q+2)*(‖s‖+2))^(2*ε) := by
  obtain ⟨K,hK,h⟩ := regularSeries_deriv_norm_small_power hε hε1
  refine ⟨K,hK,?_⟩
  intro q _ χ hχ s hs
  have he : regularSeries (positiveCoefficients (fun n => χ (n : ZMod q))) 0 =ᶠ[𝓝 s] χ.LFunction := by
    filter_upwards [(continuous_re.tendsto s).eventually (lt_mem_nhds (by linarith : 0<s.re))] with z hz
    exact regularSeries_character_eq hχ hz
  rw [←he.deriv_eq]
  have hb := h _ 0 (q+1) (positiveCoefficients_zero _) (positiveCoefficients_norm_le (fun n => χ.norm_le_one _))
    (by simp) (by positivity) (fun t _ => discrepancy_character_bound hχ t) s hs
  convert hb using 1
  congr 3
  ring

noncomputable def characterRegular {q : ℕ} (χ : DirichletCharacter ℂ q) : ℂ → ℂ :=
  regularSeries (positiveCoefficients (fun n => χ (n : ZMod q))) (characterMean χ)

lemma character_line_bounds {ε : ℝ} (hε : 0<ε) (hε1 : ε≤1/2) :
    ∃ K : ℝ,1≤K ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ),
      (∀ s : ℂ,1 ≤ s.re → ‖s‖+2≤4*(|t|+2) →
        ‖characterRegular χ s‖≤K*((q+2)*(|t|+2))^(2*ε)) ∧
      (χ≠1 → ∀ s : ℂ,1 ≤ s.re → ‖s‖+2≤4*(|t|+2) →
        ‖deriv χ.LFunction s‖≤K*((q+2)*(|t|+2))^(2*ε)) := by
  obtain ⟨K₀,hK₀,h₀⟩ := regularSeries_norm_small_power hε hε1
  obtain ⟨K₁,hK₁,h₁⟩ := LFunction_deriv_norm_small_power hε hε1
  let K := 1+K₀*8^(2*ε)+K₁*4^(2*ε)
  have hp₀ : 0≤K₀*8^(2*ε) := by positivity
  have hp₁ : 0≤K₁*4^(2*ε) := by positivity
  have hK : 1≤K := by dsimp [K]; linarith
  refine ⟨K,hK,?_⟩
  intro q _ χ t
  have hq : (0:ℝ)≤q := Nat.cast_nonneg q
  have ht : 0≤|t| := abs_nonneg t
  have hp : 0≤((q:ℝ)+2)*(|t|+2) := by positivity
  have he : 0≤2*ε := by positivity
  constructor
  · intro s hs hn
    have hb := h₀ _ (characterMean χ) (2*q+3) (positiveCoefficients_zero _)
      (positiveCoefficients_norm_le (fun n => χ.norm_le_one _)) (characterMean_norm_le χ)
      (by positivity) (fun t ht => discrepancy_characterMean_bound χ ht) s (by linarith)
    change ‖characterRegular χ s‖≤_ at hb
    have hb' : (2*q+3+1)*(‖s‖+2)≤8*(((q:ℝ)+2)*(|t|+2)) := by
      nlinarith [mul_nonneg (show (0:ℝ)≤2*q+4 by positivity) (sub_nonneg.mpr hn)]
    calc
      _ ≤ K₀*((2*q+3+1)*(‖s‖+2))^(2*ε) := hb
      _ ≤ K₀*(8*(((q:ℝ)+2)*(|t|+2)))^(2*ε) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hb' he) hK₀.le
      _ = (K₀*8^(2*ε))*(((q:ℝ)+2)*(|t|+2))^(2*ε) := by rw [Real.mul_rpow (by norm_num) hp]; ring
      _ ≤ _ := by gcongr; dsimp [K]; linarith
  · intro hχ s hs hn
    have hb := h₁ q χ hχ s (by linarith)
    have hb' : (q+2)*(‖s‖+2)≤4*(((q:ℝ)+2)*(|t|+2)) := by
      nlinarith [mul_nonneg (show (0:ℝ)≤q+2 by positivity) (sub_nonneg.mpr hn)]
    calc
      _ ≤ K₁*((q+2)*(‖s‖+2))^(2*ε) := hb
      _ ≤ K₁*(4*(((q:ℝ)+2)*(|t|+2)))^(2*ε) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hb' he) hK₁.le
      _ = (K₁*4^(2*ε))*(((q:ℝ)+2)*(|t|+2))^(2*ε) := by rw [Real.mul_rpow (by norm_num) hp]; ring
      _ ≤ _ := by gcongr; dsimp [K]; linarith

lemma line_growth_lipschitz {f : ℂ → ℂ} {t D : ℝ} (hf : Differentiable ℂ f)
    (hb : ∀ s : ℂ,1 ≤ s.re → ‖s‖+2≤4*(|t|+2) → ‖deriv f s‖≤D)
    {z w : ℂ} (hz : 1 ≤ z.re) (hw : 1 ≤ w.re)
    (hzn : ‖z‖+2≤4*(|t|+2)) (hwn : ‖w‖+2≤4*(|t|+2)) :
    ‖f z-f w‖≤D*‖z-w‖ := by
  let S := {s : ℂ | 1 ≤ s.re} ∩ Metric.closedBall 0 (4*(|t|+2)-2)
  have hS : Convex ℝ S := (convex_halfSpace_re_ge 1).inter (convex_closedBall 0 _)
  apply Convex.norm_image_sub_le_of_norm_deriv_le (s:=S) (fun z _ => hf z) ?_ hS
      ⟨hw,by simp [Metric.mem_closedBall,dist_zero_right]; linarith⟩
      ⟨hz,by simp [Metric.mem_closedBall,dist_zero_right]; linarith⟩
  intro s hs
  exact hb s hs.1 (by have := hs.2; simp only [Metric.mem_closedBall,dist_zero_right] at this; linarith)

end
lemma three_four_one_lower {a D E : ℝ} (ha : 0≤a) (hD : 1≤D) (hE : 1≤E)
    (h : ∀ δ : ℝ,0<δ → δ≤1 → 1≤(2*D/δ)^3*(a+D*δ)^4*E) :
    1/(256*D^6*E)≤a := by
  have hD0 : 0<D := by linarith
  have hE0 : 0<E := by linarith
  let δ := 1/(256*D^7*E)
  have hδ : 0<δ := by dsimp [δ]; positivity
  have hδ1 : δ≤1 := by
    have hp : (1:ℝ)≤D^7 := one_le_pow₀ hD
    have hp' : (1:ℝ)≤D^7*E := one_le_mul_of_one_le_of_one_le hp hE
    dsimp [δ]
    apply (div_le_one (by positivity)).mpr
    linarith
  have he : 1/(256*D^6*E)=D*δ := by dsimp [δ]; field_simp
  rw [he]
  by_contra! han
  have hb : a+D*δ≤2*D*δ := by linarith
  have hh := h δ hδ hδ1
  have hu : (2*D/δ)^3*(a+D*δ)^4*E≤(2*D/δ)^3*(2*D*δ)^4*E := by gcongr
  have hv : (2*D/δ)^3*(2*D*δ)^4*E=1/2 := by dsimp [δ]; field_simp; norm_num
  rw [hv] at hu
  linarith

open Complex Filter Topology Finset
lemma line_sample_norm {δ t u : ℝ} (hδ : 0≤δ) (hδ1 : δ≤1) (hu : |u|≤2*|t|) :
    ‖(1:ℂ)+δ+I*u‖+2≤4*(|t|+2) := by
  have h := Complex.norm_le_abs_re_add_abs_im ((1:ℂ)+δ+I*u)
  simp only [Complex.add_re,Complex.one_re,Complex.ofReal_re,Complex.mul_re,Complex.I_re,
    Complex.I_im,Complex.ofReal_im,mul_zero,zero_mul,sub_self,add_zero,Complex.add_im,
    Complex.one_im,Complex.mul_im,one_mul,zero_add] at h
  rw [abs_of_nonneg (by linarith : (0:ℝ)≤1+δ)] at h
  linarith [abs_nonneg t]

lemma LFunction_norm_le_regular_add_pole {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1<s.re) :
    ‖χ.LFunction s‖≤‖characterRegular χ s‖+1/‖s-1‖ := by
  rw [LFunction_regularSeries_characterMean χ hs]
  apply (norm_add_le _ _).trans
  dsimp [characterRegular]
  apply add_le_add le_rfl
  rw [norm_div]
  exact div_le_div_of_nonneg_right (characterMean_norm_le χ) (norm_nonneg _)

lemma characterRegular_eq_nonprincipal {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ≠1) {s : ℂ} (hs : 0<s.re) : characterRegular χ s=χ.LFunction s := by
  rw [characterRegular,characterMean_eq_zero hχ,regularSeries_character_eq hχ hs]

lemma nonprincipal_line_lower_aux {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ≠1) {t c K P : ℝ} (hc : 0<c) (_hc1 : c≤1) (hK : 1≤K) (hP : 1≤P)
    (hr : ∀ ψ : DirichletCharacter ℂ q,∀ s : ℂ,1 ≤ s.re → ‖s‖+2≤4*(|t|+2) →
      ‖characterRegular ψ s‖≤K*P)
    (hd : ∀ s : ℂ,1 ≤ s.re → ‖s‖+2≤4*(|t|+2) → ‖deriv χ.LFunction s‖≤K*P)
    (hsi : χ^2=1 → c/P≤‖χ.LFunction 1‖) :
    min (c/2) (1/(256*K^6*(K+K/c)))/P^8≤‖χ.LFunction (1+I*t)‖ := by
  have hK0 : 0<K := by linarith
  have hP0 : 0<P := by linarith
  have hhc : 0<K+K/c := by positivity
  have hKP : 1≤K*P := one_le_mul_of_one_le_of_one_le hK hP
  have hn0 : ‖(1:ℂ)+I*t‖+2≤4*(|t|+2) := by
    simpa using line_sample_norm (t:=t) (u:=t) (δ:=0) le_rfl zero_le_one (by linarith [abs_nonneg t])
  have hn1 : ‖(1:ℂ)‖+2≤4*(|t|+2) := by norm_num; linarith [abs_nonneg t]
  by_cases hsmall : χ^2=1 ∧ |t|≤c/(2*K*P^2)
  · have hdiff := line_growth_lipschitz (DirichletCharacter.differentiable_LFunction hχ) hd
      (z:=1) (w:=1+I*t) (by simp) (by simp) hn1 hn0
    have hnorm : ‖(1:ℂ)-(1+I*t)‖=|t| := by
      rw [show (1:ℂ)-(1+I*t)=-(I*t) by ring,norm_neg,norm_mul,Complex.norm_I,one_mul,
        Complex.norm_real,Real.norm_eq_abs]
    rw [hnorm] at hdiff
    have hdiff' : ‖χ.LFunction 1-χ.LFunction (1+I*t)‖≤c/(2*P) := by
      calc
        _ ≤ K*P*|t| := hdiff
        _ ≤ K*P*(c/(2*K*P^2)) := mul_le_mul_of_nonneg_left hsmall.2 (by positivity)
        _ = _ := by field_simp
    have hval : c/(2*P)≤‖χ.LFunction (1+I*t)‖ := by
      have htri := norm_add_le (χ.LFunction 1-χ.LFunction (1+I*t)) (χ.LFunction (1+I*t))
      rw [sub_add_cancel] at htri
      have he : c/P=2*(c/(2*P)) := by ring
      have hsi' := hsi hsmall.1
      rw [he] at hsi'
      linarith
    have hP8 : P≤P^8 := by simpa using pow_le_pow_right₀ hP (show (1:ℕ)≤8 by norm_num)
    calc
      _ ≤ (c/2)/P^8 := div_le_div_of_nonneg_right (min_le_left _ _) (by positivity)
      _ ≤ (c/2)/P := div_le_div_of_nonneg_left (by positivity) hP0 hP8
      _ = c/(2*P) := by ring
      _ ≤ _ := hval
  · have hLo : 1/(256*(K*P)^6*((K+K/c)*P^2))≤‖χ.LFunction (1+I*t)‖ := by
      apply three_four_one_lower (norm_nonneg _) hKP
        (one_le_mul_of_one_le_of_one_le (by linarith [div_pos hK0 hc]) (one_le_pow₀ hP))
      intro δ hδ hδ1
      have hrδ : ((1:ℂ)+δ+I*t).re=1+δ := by simp
      have hrδ2 : ((1:ℂ)+δ+2*I*t).re=1+δ := by simp
      have hnδ := line_sample_norm hδ.le hδ1 (t:=t) (u:=t) (by linarith [abs_nonneg t])
      have hnδ2 : ‖(1:ℂ)+δ+2*I*t‖+2≤4*(|t|+2) := by
        simpa only [show I*((2*t:ℝ):ℂ)=2*I*t by push_cast; ring] using
          line_sample_norm hδ.le hδ1 (t:=t) (u:=2*t) (by rw [abs_mul]; norm_num)
      have hL0 : ‖DirichletCharacter.LFunctionTrivChar q (1+δ)‖≤2*(K*P)/δ := by
        have hn : ‖(1:ℂ)+δ‖+2≤4*(|t|+2) := by
          simpa using line_sample_norm hδ.le hδ1 (t:=t) (u:=0) (by simp)
        have hreg := hr (1:DirichletCharacter ℂ q) (1+δ) (by simp; linarith) hn
        have hp := LFunction_norm_le_regular_add_pole (1:DirichletCharacter ℂ q)
          (s:=1+δ) (by simp; linarith)
        have hden : ‖(1:ℂ)+δ-1‖=δ := by simp [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hδ]
        rw [hden] at hp
        change ‖DirichletCharacter.LFunction (1:DirichletCharacter ℂ q) (1+δ)‖≤_
        apply (hp.trans (add_le_add hreg le_rfl)).trans
        apply (le_div_iff₀ hδ).mpr
        have hd : (K*P)*δ≤K*P := mul_le_of_le_one_right (by positivity) hδ1
        field_simp
        nlinarith
      have hLχ : ‖χ.LFunction (1+δ+I*t)‖≤‖χ.LFunction (1+I*t)‖+(K*P)*δ := by
        have hl := line_growth_lipschitz (DirichletCharacter.differentiable_LFunction hχ) hd
          (z:=1+δ+I*t) (w:=1+I*t) (by simp; linarith) (by simp) hnδ hn0
        have hden : ‖(1:ℂ)+δ+I*t-(1+I*t)‖=δ := by
          rw [show (1:ℂ)+δ+I*t-(1+I*t)=(δ:ℂ) by ring,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hδ]
        rw [hden] at hl
        have ht := norm_add_le (χ.LFunction (1+δ+I*t)-χ.LFunction (1+I*t)) (χ.LFunction (1+I*t))
        rw [sub_add_cancel] at ht
        linarith
      have hL2 : ‖(χ^2).LFunction (1+δ+2*I*t)‖≤(K+K/c)*P^2 := by
        by_cases hχ2 : χ^2=1
        · have ht : c/(2*K*P^2)< |t| := lt_of_not_ge (fun ht => hsmall ⟨hχ2,ht⟩)
          have ht0 : 0< |t| := (by positivity : 0<c/(2*K*P^2)).trans ht
          have hp := LFunction_norm_le_regular_add_pole (χ^2) (s:=1+δ+2*I*t) (by rw [hrδ2]; linarith)
          have hn : 2*|t|≤‖(1:ℂ)+δ+2*I*t-1‖ := by
            have h := Complex.abs_im_le_norm ((1:ℂ)+δ+2*I*t-1)
            simpa [abs_mul] using h
          have hfrac : 1/‖(1:ℂ)+δ+2*I*t-1‖≤K*P^2/c := by
            apply (div_le_div_of_nonneg_left zero_le_one (by positivity : 0<2*|t|) hn).trans
            apply (div_le_iff₀ (by positivity : 0<2*|t|)).mpr
            have ht' := (div_lt_iff₀ (by positivity : 0<2*K*P^2)).mp ht
            rw [div_mul_eq_mul_div]
            apply (le_div_iff₀ hc).mpr
            nlinarith
          have hreg := hr (χ^2) (1+δ+2*I*t) (by rw [hrδ2]; linarith) hnδ2
          have hP2 : P≤P^2 := by nlinarith
          have h := hp.trans (add_le_add hreg hfrac)
          apply h.trans
          calc
            K*P+K*P^2/c ≤ K*P^2+K*P^2/c := add_le_add (mul_le_mul_of_nonneg_left hP2 hK0.le) le_rfl
            _ = _ := by ring
        · have hreg := hr (χ^2) (1+δ+2*I*t) (by rw [hrδ2]; linarith) hnδ2
          rw [characterRegular_eq_nonprincipal hχ2 (by rw [hrδ2]; linarith)] at hreg
          have hP2 : P≤P^2 := by nlinarith
          exact hreg.trans (by nlinarith [mul_le_mul_of_nonneg_left hP2 hK0.le,div_pos hK0 hc])
      have hprod := χ.norm_LFunction_product_ge_one hδ t
      simp only [norm_mul,norm_pow] at hprod
      exact hprod.trans (by gcongr)
    calc
      _ ≤ (1/(256*K^6*(K+K/c)))/P^8 := div_le_div_of_nonneg_right (min_le_right _ _) (by positivity)
      _ = 1/(256*(K*P)^6*((K+K/c)*P^2)) := by field_simp
      _ ≤ _ := hLo

lemma nonprincipal_line_lower {ε : ℝ} (hε : 0<ε) (hε1 : ε≤1) :
    ∃ c : ℝ,0<c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → χ≠1 → ∀ t : ℝ,
        c*(((q:ℝ)+2)*(|t|+2))^(-ε)≤‖χ.LFunction (1+I*t)‖ := by
  obtain ⟨K,hK,hgrowth⟩ := character_line_bounds (by linarith : 0<ε/16) (by linarith : ε/16≤1/2)
  obtain ⟨c₀,hc₀,hsiegel⟩ := quadratic_siegel (by linarith : 0<ε/8) (by linarith : ε/8≤1)
  let c := min c₀ 1
  have hc : 0<c := lt_min hc₀ zero_lt_one
  have hc1 : c≤1 := min_le_right _ _
  let d := min (c/2) (1/(256*K^6*(K+K/c)))
  have hK0 : 0<K := by linarith
  have hd : 0<d := by dsimp [d]; positivity
  refine ⟨d,hd,?_⟩
  intro q _ χ hχp hχ t
  let X : ℝ := ((q:ℝ)+2)*(|t|+2)
  let P : ℝ := X^(ε/8)
  have hX : 1≤X := by dsimp [X]; nlinarith [Nat.cast_nonneg (α:=ℝ) q,abs_nonneg t]
  have hX0 : 0<X := by linarith
  have hP : 1≤P := Real.one_le_rpow hX (by positivity)
  have he : 2*(ε/16)=ε/8 := by ring
  have hsi : χ^2=1 → c/P≤‖χ.LFunction 1‖ := by
    intro hχ2
    have hq : (q:ℝ)+1≤X := by dsimp [X]; nlinarith [Nat.cast_nonneg (α:=ℝ) q,abs_nonneg t]
    calc
      c/P = c*X^(-(ε/8)) := by rw [Real.rpow_neg hX0.le]; rfl
      _ ≤ c₀*((q:ℝ)+1)^(-(ε/8)) := by
        apply mul_le_mul (min_le_left _ _) (Real.rpow_le_rpow_of_nonpos (by positivity) hq (by linarith))
          (Real.rpow_nonneg hX0.le _) hc₀.le
      _ ≤ _ := hsiegel q χ hχp hχ hχ2
  have hh := nonprincipal_line_lower_aux hχ hc hc1 hK hP
    (fun ψ s hs hn => by simpa only [he] using (hgrowth q ψ t).1 s hs hn)
    (fun s hs hn => by simpa only [he] using (hgrowth q χ t).2 hχ s hs hn) hsi
  have hP8 : P^8=X^ε := by
    dsimp [P]
    rw [←Real.rpow_mul_natCast hX0.le]
    congr 1
    norm_num
  change d/P^8≤_ at hh
  rw [hP8] at hh
  change d*X^(-ε)≤_
  simpa only [Real.rpow_neg hX0.le,div_eq_mul_inv] using hh

lemma character_interior_lower {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {t K P δ : ℝ} (hK : 1≤K) (hP : 1≤P) (hδ : 0<δ) (hδ1 : δ≤1)
    (hr : ∀ ψ : DirichletCharacter ℂ q,∀ s : ℂ,1 ≤ s.re → ‖s‖+2≤4*(|t|+2) →
      ‖characterRegular ψ s‖≤K*P) :
    δ/(2*K*P)≤‖χ.LFunction (1+δ+I*t)‖ := by
  have hKP : 1≤K*P := one_le_mul_of_one_le_of_one_le hK hP
  have hKP0 : 0<K*P := by linarith
  have hb (ψ : DirichletCharacter ℂ q) (u : ℝ) (hu : |u|≤2*|t|) :
      ‖ψ.LFunction (1+δ+I*u)‖≤2*K*P/δ := by
    have hp := LFunction_norm_le_regular_add_pole ψ (s:=1+δ+I*u) (by simp; linarith)
    have hn : δ≤‖(1:ℂ)+δ+I*u-1‖ := by
      simpa using Complex.re_le_norm ((1:ℂ)+δ+I*u-1)
    have hreg := hr ψ (1+δ+I*u) (by simp; linarith) (line_sample_norm hδ.le hδ1 hu)
    have hfrac := div_le_div_of_nonneg_left zero_le_one hδ hn
    apply (hp.trans (add_le_add hreg hfrac)).trans
    apply (le_div_iff₀ hδ).mpr
    have hd := mul_le_of_le_one_right hKP0.le hδ1
    have he : (K*P+1/δ)*δ=K*P*δ+1 := by field_simp
    rw [he]
    nlinarith
  have h0 : ‖DirichletCharacter.LFunctionTrivChar q (1+δ)‖≤2*K*P/δ := by
    simpa using hb (1:DirichletCharacter ℂ q) 0 (by simp)
  have h2 : ‖(χ^2).LFunction (1+δ+2*I*t)‖≤2*K*P/δ := by
    simpa only [show I*((2*t:ℝ):ℂ)=2*I*t by push_cast; ring] using hb (χ^2) (2*t) (by rw [abs_mul]; norm_num)
  have hh := χ.norm_LFunction_product_ge_one hδ t
  simp only [norm_mul,norm_pow] at hh
  have hu : 1≤(2*K*P/δ)^3*‖χ.LFunction (1+δ+I*t)‖^4*(2*K*P/δ) := hh.trans (by gcongr)
  have hp : (1:ℝ)^4≤((2*K*P/δ)*‖χ.LFunction (1+δ+I*t)‖)^4 := by convert hu using 1 <;> ring
  have hv := le_of_pow_le_pow_left₀ (by norm_num : (4:ℕ)≠0) (by positivity) hp
  apply (div_le_iff₀ (by positivity : 0<2*K*P)).mpr
  have he : (2*K*P/δ)*‖χ.LFunction (1+δ+I*t)‖=(‖χ.LFunction (1+δ+I*t)‖*(2*K*P))/δ := by ring
  rw [he] at hv
  simpa only [one_mul] using (le_div_iff₀ hδ).mp hv

lemma nonprincipal_strip_lower_aux {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ≠1) {t c K P δ : ℝ} (hc : 0<c) (hK : 1≤K) (hP : 1≤P)
    (hδ : 0≤δ) (hδ1 : δ≤1)
    (hr : ∀ ψ : DirichletCharacter ℂ q,∀ s : ℂ,1 ≤ s.re → ‖s‖+2≤4*(|t|+2) →
      ‖characterRegular ψ s‖≤K*P)
    (hd : ∀ s : ℂ,1 ≤ s.re → ‖s‖+2≤4*(|t|+2) → ‖deriv χ.LFunction s‖≤K*P)
    (hl : c/P≤‖χ.LFunction (1+I*t)‖) :
    (c/(4*K^2))/P^3≤‖χ.LFunction (1+δ+I*t)‖ := by
  have hK0 : 0<K := by linarith
  have hP0 : 0<P := by linarith
  by_cases hnear : δ≤c/(2*K*P^2)
  · have hn0 : ‖(1:ℂ)+I*t‖+2≤4*(|t|+2) := by
      simpa using line_sample_norm (t:=t) (u:=t) (δ:=0) le_rfl zero_le_one (by linarith [abs_nonneg t])
    have hnδ := line_sample_norm hδ hδ1 (t:=t) (u:=t) (by linarith [abs_nonneg t])
    have hdif := line_growth_lipschitz (DirichletCharacter.differentiable_LFunction hχ) hd
      (z:=1+I*t) (w:=1+δ+I*t) (by simp) (by simp; linarith) hn0 hnδ
    have hnorm : ‖(1:ℂ)+I*t-(1+δ+I*t)‖=δ := by
      rw [show (1:ℂ)+I*t-(1+δ+I*t)=-(δ:ℂ) by ring,norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hδ]
    rw [hnorm] at hdif
    have hdb : ‖χ.LFunction (1+I*t)-χ.LFunction (1+δ+I*t)‖≤c/(2*P) := by
      apply hdif.trans
      calc
        K*P*δ ≤ K*P*(c/(2*K*P^2)) := mul_le_mul_of_nonneg_left hnear (by positivity)
        _ = _ := by field_simp
    have htri := norm_add_le (χ.LFunction (1+I*t)-χ.LFunction (1+δ+I*t)) (χ.LFunction (1+δ+I*t))
    rw [sub_add_cancel] at htri
    have hva : c/(2*P)≤‖χ.LFunction (1+δ+I*t)‖ := by
      have he : c/P=2*(c/(2*P)) := by ring
      rw [he] at hl
      linarith
    apply le_trans ?_ hva
    rw [div_div]
    apply div_le_div_of_nonneg_left hc.le (by positivity)
    have hP3 : P≤P^3 := by simpa using pow_le_pow_right₀ hP (show (1:ℕ)≤3 by norm_num)
    have hK2 : 1≤K^2 := one_le_pow₀ hK
    nlinarith [mul_le_mul_of_nonneg_left hP3 (show (0:ℝ)≤4*K^2 by positivity)]
  · have hδ0 : 0<δ := (by positivity : 0<c/(2*K*P^2)).trans (lt_of_not_ge hnear)
    apply le_trans ?_ (character_interior_lower χ hK hP hδ0 hδ1 hr)
    calc
      (c/(4*K^2))/P^3 = (c/(2*K*P^2))/(2*K*P) := by field_simp; norm_num
      _ ≤ δ/(2*K*P) := div_le_div_of_nonneg_right (le_of_not_ge hnear) (by positivity)

lemma nonprincipal_strip_lower {ε : ℝ} (hε : 0<ε) (hε1 : ε≤1) :
    ∃ c : ℝ,0<c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → χ≠1 → ∀ σ t : ℝ, 1≤σ → σ≤2 →
        c*(((q:ℝ)+2)*(|t|+2))^(-ε)≤‖χ.LFunction (σ+I*t)‖ := by
  obtain ⟨K,hK,hg⟩ := character_line_bounds (by linarith : 0<ε/6) (by linarith : ε/6≤1/2)
  obtain ⟨c,hc,hl⟩ := nonprincipal_line_lower (by linarith : 0<ε/3) (by linarith : ε/3≤1)
  have hK0 : 0<K := by linarith
  refine ⟨c/(4*K^2),by positivity,?_⟩
  intro q _ χ hχp hχ σ t hσ hσ2
  let X : ℝ := ((q:ℝ)+2)*(|t|+2)
  let P : ℝ := X^(ε/3)
  have hX : 1≤X := by dsimp [X]; nlinarith [Nat.cast_nonneg (α:=ℝ) q,abs_nonneg t]
  have hX0 : 0<X := by linarith
  have hP : 1≤P := Real.one_le_rpow hX (by positivity)
  have he : 2*(ε/6)=ε/3 := by ring
  have hl' : c/P≤‖χ.LFunction (1+I*t)‖ := by
    have hh := hl q χ hχp hχ t
    change c*X^(-(ε/3))≤_ at hh
    change c/X^(ε/3)≤_
    simpa only [Real.rpow_neg hX0.le,div_eq_mul_inv] using hh
  have hb := nonprincipal_strip_lower_aux hχ hc hK hP (δ:=σ-1) (by linarith) (by linarith)
    (fun ψ s hs hn => by simpa only [he] using (hg q ψ t).1 s hs hn)
    (fun s hs hn => by simpa only [he] using (hg q χ t).2 hχ s hs hn) hl'
  have hP3 : P^3=X^ε := by dsimp [P]; rw [←Real.rpow_mul_natCast hX0.le]; congr 1; norm_num
  rw [hP3] at hb
  have hs : (1:ℂ)+((σ-1:ℝ):ℂ)+I*t=(σ:ℂ)+I*t := by push_cast; ring
  rw [hs] at hb
  change (c/(4*K^2))*X^(-ε)≤_
  simpa only [Real.rpow_neg hX0.le,div_eq_mul_inv] using hb

end LargePrimeGaps
end OAI

-- Source module: PrincipalGrowth
namespace OAI
namespace LargePrimeGaps
open Complex Filter Topology
lemma zetaRegular_bounds {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1/2) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ s : ℂ, 1-ε/2 ≤ s.re →
      ‖zetaRegular s‖ ≤ K*(‖s‖+2)^(2*ε) ∧
      ‖deriv zetaRegular s‖ ≤ K*(‖s‖+2)^(2*ε) := by
  obtain ⟨K₀,hK₀,h₀⟩ := regularSeries_norm_small_power hε hε1
  obtain ⟨K₁,hK₁,h₁⟩ := regularSeries_deriv_norm_small_power hε hε1
  let K := 1+(K₀+K₁)*2^(2*ε)
  have hK : 1 ≤ K := by dsimp [K]; linarith [show 0 < (K₀+K₁)*2^(2*ε) by positivity]
  refine ⟨K,hK,?_⟩
  intro s hs
  have hb₀ := h₀ _ 1 1 (positiveCoefficients_zero _) (positiveCoefficients_norm_le (by simp))
    (by simp) zero_le_one (fun t ht => discrepancy_constant_bound ht) s (by linarith)
  have hb₁ := h₁ _ 1 1 (positiveCoefficients_zero _) (positiveCoefficients_norm_le (by simp))
    (by simp) zero_le_one (fun t ht => discrepancy_constant_bound ht) s hs
  change ‖zetaRegular s‖ ≤ _ at hb₀
  change ‖deriv zetaRegular s‖ ≤ _ at hb₁
  norm_num only [one_add_one_eq_two] at hb₀ hb₁
  rw [Real.mul_rpow (by norm_num) (by positivity)] at hb₀ hb₁
  constructor
  · apply hb₀.trans
    have hc : K₀*2^(2*ε) ≤ K := by dsimp [K]; nlinarith [Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<2) (2*ε)]
    calc
      _ = (K₀*2^(2*ε))*(‖s‖+2)^(2*ε) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hc (by positivity)
  · apply hb₁.trans
    have hc : K₁*2^(2*ε) ≤ K := by dsimp [K]; nlinarith [Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<2) (2*ε)]
    calc
      _ = (K₁*2^(2*ε))*(‖s‖+2)^(2*ε) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hc (by positivity)

lemma zeta_deriv_eq_regular {s : ℂ} (hs : 0 < s.re) (hs1 : s≠1) :
    deriv riemannZeta s = deriv zetaRegular s-1/(s-1)^2 := by
  have he : riemannZeta =ᶠ[𝓝 s] fun z => zetaRegular z+1/(z-1) := by
    filter_upwards [(continuous_re.tendsto s).eventually (lt_mem_nhds hs),
      eventually_ne_nhds hs1] with z hz hz1
    rw [zetaRegular_eq hz hz1,sub_add_cancel]
  rw [he.deriv_eq]
  have hd := (hasDerivAt_const s (1:ℂ)).div ((hasDerivAt_id s).sub_const 1) (sub_ne_zero.mpr hs1)
  have hh := (zetaRegular_differentiableAt hs).hasDerivAt.add hd
  simpa only [Pi.add_def, Pi.div_def, id_eq, zero_mul, one_mul, zero_sub, neg_div, sub_eq_add_neg, zero_add] using hh.deriv

lemma horizontal_growth_lipschitz {f : ℂ → ℂ} {t D : ℝ}
    (hf : ∀ s : ℂ, 1 ≤ s.re → s.im=t → DifferentiableAt ℂ f s)
    (hb : ∀ s : ℂ, 1 ≤ s.re → s.im=t → ‖s‖+2 ≤ 4*(|t|+2) → ‖deriv f s‖ ≤ D)
    {z w : ℂ} (hz : 1 ≤ z.re) (hw : 1 ≤ w.re) (hzt : z.im=t) (hwt : w.im=t)
    (hzn : ‖z‖+2 ≤ 4*(|t|+2)) (hwn : ‖w‖+2 ≤ 4*(|t|+2)) :
    ‖f z-f w‖ ≤ D*‖z-w‖ := by
  let S := ({s : ℂ | 1 ≤ s.re} ∩ {s : ℂ | s.im=t}) ∩ Metric.closedBall 0 (4*(|t|+2)-2)
  have hi : Convex ℝ {s : ℂ | s.im=t} := convex_hyperplane (.mk Complex.add_im Complex.smul_im) t
  have hS : Convex ℝ S := ((convex_halfSpace_re_ge 1).inter hi).inter (convex_closedBall 0 _)
  apply Convex.norm_image_sub_le_of_norm_deriv_le (s:=S) (fun z hz => hf z hz.1.1 hz.1.2) ?_ hS
    ⟨⟨hw,hwt⟩,by simp [Metric.mem_closedBall,dist_zero_right]; linarith⟩
    ⟨⟨hz,hzt⟩,by simp [Metric.mem_closedBall,dist_zero_right]; linarith⟩
  intro s hs
  exact hb s hs.1.1 hs.1.2 (by have := hs.2; simp only [Metric.mem_closedBall,dist_zero_right] at this; linarith)

lemma zeta_high_line_bounds {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1/2) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ t : ℝ, 1 ≤ |t| →
      (∀ ψ : DirichletCharacter ℂ 1, ∀ s : ℂ, 1 ≤ s.re → ‖s‖+2 ≤ 4*(|t|+2) →
        ‖characterRegular ψ s‖ ≤ K*(|t|+2)^(2*ε)) ∧
      (∀ s : ℂ, 1 ≤ s.re → s.im=t → ‖s‖+2 ≤ 4*(|t|+2) →
        ‖deriv riemannZeta s‖ ≤ K*(|t|+2)^(2*ε)) := by
  obtain ⟨K₀,hK₀,h₀⟩ := character_line_bounds hε hε1
  obtain ⟨K₁,hK₁,h₁⟩ := zetaRegular_bounds hε hε1
  let K := K₀*3^(2*ε)+K₁*4^(2*ε)+1
  have hK₀' : 0 < K₀ := by linarith
  have hK₁' : 0 < K₁ := by linarith
  have hK : 1 ≤ K := by dsimp [K]; linarith [show 0 < K₀*3^(2*ε) by positivity, show 0 < K₁*4^(2*ε) by positivity]
  refine ⟨K,hK,?_⟩
  intro t ht
  have hP : 1 ≤ (|t|+2)^(2*ε) := Real.one_le_rpow (by linarith [abs_nonneg t]) (by positivity)
  constructor
  · intro ψ s hs hn
    have hb := (h₀ 1 ψ t).1 s hs hn
    norm_num only [Nat.cast_one,show (1:ℝ)+2=3 by norm_num] at hb
    rw [Real.mul_rpow (by norm_num) (by positivity)] at hb
    apply hb.trans
    have hc : K₀*3^(2*ε) ≤ K := by dsimp [K]; linarith [show 0 < K₁*4^(2*ε) by positivity]
    convert mul_le_mul_of_nonneg_right hc (by positivity : 0 ≤ (|t|+2)^(2*ε)) using 1
    ring
  · intro s hs him hn
    have hs1 : s≠1 := by intro h; simp [h] at him; rw [←him] at ht; norm_num at ht
    have hd := (h₁ s (by linarith)).2
    have hden : 1 ≤ ‖s-1‖ := by
      have h := Complex.abs_im_le_norm (s-1)
      simp only [Complex.sub_im,Complex.one_im,sub_zero,him] at h
      exact ht.trans h
    have hfrac : ‖(1:ℂ)/(s-1)^2‖ ≤ 1 := by
      simp only [norm_div,norm_one,norm_pow]
      exact div_le_one_of_le₀ (one_le_pow₀ hden) (by positivity)
    rw [zeta_deriv_eq_regular (by linarith) hs1]
    apply (norm_sub_le _ _).trans
    have hnorm := Real.rpow_le_rpow (by positivity : 0 ≤ ‖s‖+2) hn (by positivity : 0 ≤ 2*ε)
    rw [Real.mul_rpow (by norm_num) (by positivity)] at hnorm
    have hc : K₁*4^(2*ε)+1 ≤ K := by dsimp [K]; linarith [show 0 < K₀*3^(2*ε) by positivity]
    calc
      _ ≤ K₁*(‖s‖+2)^(2*ε)+1 := add_le_add hd hfrac
      _ ≤ (K₁*4^(2*ε))*(|t|+2)^(2*ε)+(|t|+2)^(2*ε) := by nlinarith
      _ = (K₁*4^(2*ε)+1)*(|t|+2)^(2*ε) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hc (by positivity)

lemma zeta_high_line_lower_aux {t K P : ℝ} (ht : 1 ≤ |t|) (hK : 1 ≤ K) (hP : 1 ≤ P)
    (hr : ∀ ψ : DirichletCharacter ℂ 1, ∀ s : ℂ, 1 ≤ s.re → ‖s‖+2 ≤ 4*(|t|+2) →
      ‖characterRegular ψ s‖ ≤ K*P)
    (hd : ∀ s : ℂ, 1 ≤ s.re → s.im=t → ‖s‖+2 ≤ 4*(|t|+2) → ‖deriv riemannZeta s‖ ≤ K*P) :
    (1/(512*K^7))/P^7 ≤ ‖riemannZeta (1+I*t)‖ := by
  have hK0 : 0 < K := by linarith
  have hP0 : 0 < P := by linarith
  have hKP : 1 ≤ K*P := one_le_mul_of_one_le_of_one_le hK hP
  have hh : 1/(256*(K*P)^6*(2*K*P)) ≤ ‖riemannZeta (1+I*t)‖ := by
    apply three_four_one_lower (norm_nonneg _) hKP (by linarith)
    intro δ hδ hδ1
    have hn0 : ‖(1:ℂ)+I*t‖+2 ≤ 4*(|t|+2) := by
      simpa using line_sample_norm (t:=t) (u:=t) (δ:=0) le_rfl zero_le_one (by linarith [abs_nonneg t])
    have hnδ := line_sample_norm hδ.le hδ1 (t:=t) (u:=t) (by linarith [abs_nonneg t])
    have hL0 : ‖DirichletCharacter.LFunctionTrivChar 1 (1+δ)‖ ≤ 2*(K*P)/δ := by
      have hn : ‖(1:ℂ)+δ‖+2 ≤ 4*(|t|+2) := by
        simpa using line_sample_norm hδ.le hδ1 (t:=t) (u:=0) (by simp)
      have hreg := hr 1 (1+δ) (by simp; linarith) hn
      have hp := LFunction_norm_le_regular_add_pole (1:DirichletCharacter ℂ 1)
        (s:=1+δ) (by simp; linarith)
      have hden : ‖(1:ℂ)+δ-1‖=δ := by simp [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hδ]
      rw [hden] at hp
      change ‖DirichletCharacter.LFunction (1:DirichletCharacter ℂ 1) (1+δ)‖ ≤ _
      apply (hp.trans (add_le_add hreg le_rfl)).trans
      apply (le_div_iff₀ hδ).mpr
      have hd := mul_le_of_le_one_right (by positivity : 0 ≤ K*P) hδ1
      field_simp
      nlinarith
    have hL1 : ‖riemannZeta (1+δ+I*t)‖ ≤ ‖riemannZeta (1+I*t)‖+(K*P)*δ := by
      have hf (s : ℂ) (_hs : 1 ≤ s.re) (him : s.im=t) : DifferentiableAt ℂ riemannZeta s := by
        apply differentiableAt_riemannZeta
        intro hs
        simp [hs] at him
        rw [←him] at ht
        norm_num at ht
      have hl := horizontal_growth_lipschitz hf hd (z:=1+δ+I*t) (w:=1+I*t)
        (by simp; linarith) (by simp) (by simp) (by simp) hnδ hn0
      have hden : ‖(1:ℂ)+δ+I*t-(1+I*t)‖=δ := by
        rw [show (1:ℂ)+δ+I*t-(1+I*t)=(δ:ℂ) by ring,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hδ]
      rw [hden] at hl
      have hh := norm_add_le (riemannZeta (1+δ+I*t)-riemannZeta (1+I*t)) (riemannZeta (1+I*t))
      rw [sub_add_cancel] at hh
      linarith
    have hL2 : ‖riemannZeta (1+δ+2*I*t)‖ ≤ 2*K*P := by
      have hn : ‖(1:ℂ)+δ+2*I*t‖+2 ≤ 4*(|t|+2) := by
        simpa only [show I*((2*t:ℝ):ℂ)=2*I*t by push_cast; ring] using
          line_sample_norm hδ.le hδ1 (t:=t) (u:=2*t) (by rw [abs_mul]; norm_num)
      have hp := LFunction_norm_le_regular_add_pole (1:DirichletCharacter ℂ 1)
        (s:=1+δ+2*I*t) (by simp; linarith)
      rw [DirichletCharacter.LFunction_modOne_eq] at hp
      have hreg := hr 1 (1+δ+2*I*t) (by simp; linarith) hn
      have hden : 1 ≤ ‖(1:ℂ)+δ+2*I*t-1‖ := by
        have hb := Complex.abs_im_le_norm ((1:ℂ)+δ+2*I*t-1)
        simp [abs_mul] at hb
        linarith
      have hfrac : 1/‖(1:ℂ)+δ+2*I*t-1‖ ≤ 1 := div_le_one_of_le₀ hden (norm_nonneg _)
      linarith
    have hprod := (1:DirichletCharacter ℂ 1).norm_LFunction_product_ge_one hδ t
    simp only [one_pow,DirichletCharacter.LFunction_modOne_eq,norm_mul,norm_pow] at hprod
    have hL0' : ‖riemannZeta (1+δ)‖ ≤ 2*(K*P)/δ := by
      simpa only [DirichletCharacter.LFunctionTrivChar,DirichletCharacter.LFunction_modOne_eq] using hL0
    exact hprod.trans (by gcongr)
  convert hh using 1
  field_simp
  ring

lemma zeta_high_line_lower {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ, 1 ≤ |t| →
      c*(|t|+2)^(-ε) ≤ ‖riemannZeta (1+I*t)‖ := by
  obtain ⟨K,hK,hg⟩ := zeta_high_line_bounds (by linarith : 0 < ε/14) (by linarith : ε/14 ≤ 1/2)
  have hK0 : 0 < K := by linarith
  refine ⟨1/(512*K^7),by positivity,?_⟩
  intro t ht
  let P : ℝ := (|t|+2)^(ε/7)
  have hP : 1 ≤ P := Real.one_le_rpow (by linarith [abs_nonneg t]) (by positivity)
  have he : 2*(ε/14)=ε/7 := by ring
  have hh := zeta_high_line_lower_aux ht hK hP
    (fun ψ s hs hn => by simpa only [he] using (hg t ht).1 ψ s hs hn)
    (fun s hs him hn => by simpa only [he] using (hg t ht).2 s hs him hn)
  have hP7 : P^7=(|t|+2)^ε := by
    dsimp [P]
    rw [←Real.rpow_mul_natCast (by positivity : 0 ≤ |t|+2)]
    congr 1
    norm_num
  rw [hP7] at hh
  simpa only [Real.rpow_neg (by positivity : 0 ≤ |t|+2),div_eq_mul_inv] using hh

lemma zeta_high_strip_lower_aux {t c K P δ : ℝ} (ht : 1 ≤ |t|) (hc : 0<c) (hK : 1≤K) (hP : 1≤P)
    (hδ : 0≤δ) (hδ1 : δ≤1)
    (hr : ∀ ψ : DirichletCharacter ℂ 1,∀ s : ℂ,1 ≤ s.re → ‖s‖+2≤4*(|t|+2) →
      ‖characterRegular ψ s‖≤K*P)
    (hd : ∀ s : ℂ,1 ≤ s.re → s.im=t → ‖s‖+2≤4*(|t|+2) → ‖deriv riemannZeta s‖≤K*P)
    (hl : c/P≤‖riemannZeta (1+I*t)‖) :
    (c/(4*K^2))/P^3≤‖riemannZeta (1+δ+I*t)‖ := by
  have hK0 : 0<K := by linarith
  have hP0 : 0<P := by linarith
  by_cases hnear : δ≤c/(2*K*P^2)
  · have hn0 : ‖(1:ℂ)+I*t‖+2≤4*(|t|+2) := by
      simpa using line_sample_norm (t:=t) (u:=t) (δ:=0) le_rfl zero_le_one (by linarith [abs_nonneg t])
    have hnδ := line_sample_norm hδ hδ1 (t:=t) (u:=t) (by linarith [abs_nonneg t])
    have hf (s : ℂ) (_hs : 1 ≤ s.re) (him : s.im=t) : DifferentiableAt ℂ riemannZeta s := by
      apply differentiableAt_riemannZeta
      intro hs
      simp [hs] at him
      rw [←him] at ht
      norm_num at ht
    have hdif := horizontal_growth_lipschitz hf hd
      (z:=1+I*t) (w:=1+δ+I*t) (by simp) (by simp; linarith) (by simp) (by simp) hn0 hnδ
    have hnorm : ‖(1:ℂ)+I*t-(1+δ+I*t)‖=δ := by
      rw [show (1:ℂ)+I*t-(1+δ+I*t)=-(δ:ℂ) by ring,norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hδ]
    rw [hnorm] at hdif
    have hdb : ‖riemannZeta (1+I*t)-riemannZeta (1+δ+I*t)‖≤c/(2*P) := by
      apply hdif.trans
      calc
        K*P*δ ≤ K*P*(c/(2*K*P^2)) := mul_le_mul_of_nonneg_left hnear (by positivity)
        _ = _ := by field_simp
    have htri := norm_add_le (riemannZeta (1+I*t)-riemannZeta (1+δ+I*t)) (riemannZeta (1+δ+I*t))
    rw [sub_add_cancel] at htri
    have hva : c/(2*P)≤‖riemannZeta (1+δ+I*t)‖ := by
      have he : c/P=2*(c/(2*P)) := by ring
      rw [he] at hl
      linarith
    apply le_trans ?_ hva
    rw [div_div]
    apply div_le_div_of_nonneg_left hc.le (by positivity)
    have hP3 : P≤P^3 := by simpa using pow_le_pow_right₀ hP (show (1:ℕ)≤3 by norm_num)
    have hK2 : 1≤K^2 := one_le_pow₀ hK
    nlinarith [mul_le_mul_of_nonneg_left hP3 (show (0:ℝ)≤4*K^2 by positivity)]
  · have hδ0 : 0<δ := (by positivity : 0<c/(2*K*P^2)).trans (lt_of_not_ge hnear)
    have hInt := character_interior_lower (1:DirichletCharacter ℂ 1) hK hP hδ0 hδ1 hr
    rw [DirichletCharacter.LFunction_modOne_eq] at hInt
    apply le_trans ?_ hInt
    calc
      (c/(4*K^2))/P^3 = (c/(2*K*P^2))/(2*K*P) := by field_simp; norm_num
      _ ≤ δ/(2*K*P) := div_le_div_of_nonneg_right (le_of_not_ge hnear) (by positivity)

lemma zeta_high_strip_lower {ε : ℝ} (hε : 0<ε) (hε1 : ε≤1) :
    ∃ c : ℝ,0<c ∧ ∀ σ t : ℝ, 1≤σ → σ≤2 → 1 ≤ |t| →
        c*(|t|+2)^(-ε)≤‖riemannZeta (σ+I*t)‖ := by
  obtain ⟨K,hK,hg⟩ := zeta_high_line_bounds (by linarith : 0<ε/6) (by linarith : ε/6≤1/2)
  obtain ⟨c,hc,hl⟩ := zeta_high_line_lower (by linarith : 0<ε/3) (by linarith : ε/3≤1)
  have hK0 : 0<K := by linarith
  refine ⟨c/(4*K^2),by positivity,?_⟩
  intro σ t hσ hσ2 ht
  let X : ℝ := (|t|+2)
  let P : ℝ := X^(ε/3)
  have hX : 1≤X := by dsimp [X]; linarith [abs_nonneg t]
  have hX0 : 0<X := by linarith
  have hP : 1≤P := Real.one_le_rpow hX (by positivity)
  have he : 2*(ε/6)=ε/3 := by ring
  have hl' : c/P≤‖riemannZeta (1+I*t)‖ := by
    have hh := hl t ht
    change c*X^(-(ε/3))≤_ at hh
    change c/X^(ε/3)≤_
    simpa only [Real.rpow_neg hX0.le,div_eq_mul_inv] using hh
  have hb := zeta_high_strip_lower_aux ht hc hK hP (δ:=σ-1) (by linarith) (by linarith)
    (fun ψ s hs hn => by simpa only [he] using (hg t ht).1 ψ s hs hn)
    (fun s hs him hn => by simpa only [he] using (hg t ht).2 s hs him hn) hl'
  have hP3 : P^3=X^ε := by dsimp [P]; rw [←Real.rpow_mul_natCast hX0.le]; congr 1; norm_num
  rw [hP3] at hb
  have hs : (1:ℂ)+((σ-1:ℝ):ℂ)+I*t=(σ:ℂ)+I*t := by push_cast; ring
  rw [hs] at hb
  change (c/(4*K^2))*X^(-ε)≤_
  simpa only [Real.rpow_neg hX0.le,div_eq_mul_inv] using hb

lemma principal_deriv_eq_regular {s : ℂ} (hs : 0 < s.re) :
    deriv (poleRemovedL (1:DirichletCharacter ℂ 1)) s = zetaRegular s+(s-1)*deriv zetaRegular s := by
  have he : poleRemovedL (1:DirichletCharacter ℂ 1) =ᶠ[𝓝 s] (fun z => (z-1)*zetaRegular z+1) := by
    filter_upwards [(continuous_re.tendsto s).eventually (lt_mem_nhds hs)] with z hz
    simpa only [poleRemovedL,ite_true] using poleRemovedZeta_eq hz
  have hh := (((hasDerivAt_id s).sub_const 1).mul (zetaRegular_differentiableAt hs).hasDerivAt).add_const 1
  rw [he.deriv_eq]
  simpa only [id_eq,one_mul,Pi.mul_apply] using hh.deriv

lemma principal_deriv_growth {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ s : ℂ, 1-ε/4 ≤ s.re →
      ‖deriv (poleRemovedL (1:DirichletCharacter ℂ 1)) s‖ ≤ K*(‖s‖+2)*(‖s‖+2)^ε := by
  obtain ⟨K,hK,hb⟩ := zetaRegular_bounds (by linarith : 0 < ε/2) (by linarith : ε/2 ≤ 1/2)
  have hK0 : 0 < K := by linarith
  refine ⟨K,hK0,?_⟩
  intro s hs
  obtain ⟨hl,hd⟩ := hb s (by linarith)
  rw [show 2*(ε/2)=ε by ring] at hl hd
  rw [principal_deriv_eq_regular (by linarith)]
  have hn : ‖s-1‖ ≤ ‖s‖+1 := by simpa using norm_sub_le s 1
  calc
    _ ≤ ‖zetaRegular s‖+‖s-1‖*‖deriv zetaRegular s‖ := by
      apply (norm_add_le _ _).trans_eq
      rw [norm_mul]
    _ ≤ K*(‖s‖+2)^ε+(‖s‖+1)*(K*(‖s‖+2)^ε) := by gcongr
    _ = _ := by ring

lemma principal_strip_lower {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ σ t : ℝ, 1 ≤ σ → σ ≤ 2 →
      c*(|t|+2)/((|t|+2)^ε) ≤ ‖poleRemovedL (1:DirichletCharacter ℂ 1) (σ+I*t)‖ := by
  obtain ⟨c₀,hc₀,hl⟩ := zeta_high_strip_lower hε hε1
  let F := poleRemovedL (1:DirichletCharacter ℂ 1)
  let S : Set ℂ := (fun p : ℝ×ℝ => (p.1:ℂ)+I*p.2) '' (Set.Icc 1 2 ×ˢ Set.Icc (-1) 1)
  have hS : IsCompact S := (isCompact_Icc.prod isCompact_Icc).image (by fun_prop)
  have hmem (z : ℂ) : z∈S ↔ 1 ≤ z.re ∧ z.re ≤ 2 ∧ |z.im| ≤ 1 := by
    constructor
    · rintro ⟨⟨u,v⟩,⟨hu,hv⟩,rfl⟩
      simpa [abs_le,and_assoc] using And.intro hu hv
    · rintro ⟨h₁,h₂,h₃⟩
      refine ⟨(z.re,z.im),⟨⟨h₁,h₂⟩,abs_le.mp h₃⟩,?_⟩
      simpa only [mul_comm] using Complex.re_add_im z
  have hc : ContinuousOn (fun z => (F z)⁻¹) S := by
    intro z hz
    exact (((poleRemovedL_differentiable 1).continuous.continuousAt).inv₀
      (poleRemovedL_ne_zero 1 ((hmem z).mp hz).1)).continuousWithinAt
  obtain ⟨M,hM⟩ := hS.exists_bound_of_continuousOn hc
  let D := max M 1
  have hD : 0 < D := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  let c := min (c₀/3) (1/(3*D))
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨c,hc,?_⟩
  intro σ t hσ hσ2
  let z : ℂ := (σ:ℂ)+I*t
  have hz : 1 ≤ z.re := by simpa [z] using hσ
  have hT : 1 ≤ |t|+2 := by linarith [abs_nonneg t]
  have hP : 1 ≤ (|t|+2)^ε := Real.one_le_rpow hT hε.le
  by_cases ht : 1 ≤ |t|
  · have hz1 : z≠1 := by intro hh; have hi := congrArg Complex.im hh; simp [z] at hi; simp [hi] at ht; norm_num at ht
    have he : F z=(z-1)*riemannZeta z := by
      simp only [F,poleRemovedL,ite_true,DirichletCharacter.LFunctionTrivChar₁,Function.update_of_ne hz1,
        DirichletCharacter.LFunctionTrivChar,DirichletCharacter.LFunction_modOne_eq]
    have hnorm : (|t|+2)/3 ≤ ‖z-1‖ := by
      have hi := Complex.abs_im_le_norm (z-1)
      simp [z] at hi
      linarith
    have hlow := hl σ t hσ hσ2 ht
    rw [Real.rpow_neg (by positivity : 0 ≤ |t|+2),←div_eq_mul_inv] at hlow
    change c*(|t|+2)/( |t|+2)^ε ≤ ‖F z‖
    rw [he,norm_mul]
    calc
      _ ≤ (c₀/3)*(|t|+2)/(|t|+2)^ε := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)) (by positivity)
      _ = ((|t|+2)/3)*(c₀/(|t|+2)^ε) := by ring
      _ ≤ _ := mul_le_mul hnorm hlow (by positivity) (norm_nonneg _)
  · have ht1 : |t| ≤ 1 := le_of_not_ge ht
    have hzS : z∈S := (hmem z).mpr ⟨hz,by simpa [z] using hσ2,by simpa [z] using ht1⟩
    have hb := (hM z hzS).trans (le_max_left M 1)
    have hn : 0 < ‖F z‖ := norm_pos_iff.mpr (poleRemovedL_ne_zero 1 hz)
    rw [norm_inv,inv_eq_one_div] at hb
    have hlow : 1/D ≤ ‖F z‖ := by
      apply (div_le_iff₀ hD).mpr
      have hh := (div_le_iff₀ hn).mp hb
      nlinarith
    change c*(|t|+2)/(|t|+2)^ε ≤ ‖F z‖
    apply le_trans ?_ hlow
    calc
      _ ≤ c*(|t|+2) := div_le_self (by positivity) hP
      _ ≤ (1/(3*D))*3 := mul_le_mul (min_le_right _ _) (by linarith) (by positivity) (by positivity)
      _ = 1/D := by ring

end LargePrimeGaps
end OAI

-- Source module: RieszBounds
namespace OAI
namespace LargePrimeGaps
open Complex Filter Topology
noncomputable def logRiesz (f : ℂ → ℂ) (s : ℂ) : ℂ := (-deriv f s / f s)/(s*(s+1))

lemma near_line_denominator {z w : ℂ} {r : ℝ} (hz : 1 ≤  z.re) (hr : r ≤ 1/4)
    (hw : w∈Metric.closedBall z r) :
    w≠0 ∧ w+1≠0 ∧ (|z.im|+2)^2 ≤ 16*‖w‖*‖w+1‖ := by
  have hd : ‖w-z‖ ≤ r := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hw
  have hre := Complex.re_le_norm (z-w)
  rw [Complex.sub_re,norm_sub_rev] at hre
  have hwre : 3/4 ≤ w.re := by linarith
  have hw0 : w≠0 := by intro h; simp [h] at hwre; norm_num at hwre
  have hw1 : w+1≠0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hna : 3/4 ≤ ‖w‖ := hwre.trans (Complex.re_le_norm w)
  have hnb : 3/4 ≤ ‖w+1‖ := by
    have h := Complex.re_le_norm (w+1)
    simp only [Complex.add_re,Complex.one_re] at h
    linarith
  have ha : |z.im| ≤ ‖w‖+r := by
    have ht := norm_add_le (z-w) w
    rw [sub_add_cancel,norm_sub_rev] at ht
    linarith [Complex.abs_im_le_norm z]
  have hb : |z.im| ≤ ‖w+1‖+r := by
    have ht := norm_add_le (z-w) (w+1)
    rw [show z-w+(w+1)=z+1 by ring,norm_sub_rev] at ht
    have hi := Complex.abs_im_le_norm (z+1)
    simp only [Complex.add_im,Complex.one_im,add_zero] at hi
    linarith
  have ha' : |z.im|+2 ≤ 4*‖w‖ := by linarith
  have hb' : |z.im|+2 ≤ 4*‖w+1‖ := by linarith
  refine ⟨hw0,hw1,?_⟩
  have hp := mul_le_mul ha' hb' (by positivity : 0 ≤ |z.im|+2) (by positivity : 0 ≤ 4*‖w‖)
  nlinarith

lemma logRiesz_local {f : ℂ → ℂ} {z : ℂ} {r m M : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1/4) (hm : 0 < m) (hM : 0 ≤ M) (hz : 1 ≤  z.re)
    (hf : ∀ w∈Metric.closedBall z r,AnalyticAt ℂ f w)
    (hb : ∀ w∈Metric.closedBall z r,‖deriv f w‖ ≤ M)
    (hl : m ≤ ‖f z‖) (hMr : M*r ≤ m/2) :
    (∀ w∈Metric.closedBall z r,f w≠0) ∧
      DiffContOnCl ℂ (logRiesz f) (Metric.ball z r) ∧
      ∀ w∈Metric.closedBall z r,‖logRiesz f w‖ ≤ (32*M/m)/(|z.im|+2)^2 := by
  have hmem : z∈Metric.closedBall z r := Metric.mem_closedBall_self hr.le
  have hlo (w : ℂ) (hw : w∈Metric.closedBall z r) : m/2 ≤ ‖f w‖ := by
    have hd := Convex.norm_image_sub_le_of_norm_deriv_le
      (fun w hw => (hf w hw).differentiableAt) hb (convex_closedBall z r) hw hmem
    have hdist : ‖z-w‖ ≤ r := by simpa only [Metric.mem_closedBall,dist_eq_norm,norm_sub_rev] using hw
    have hd' := hd.trans (mul_le_mul_of_nonneg_left hdist hM)
    have ht := norm_add_le (f z-f w) (f w)
    rw [sub_add_cancel] at ht
    linarith
  have hne (w : ℂ) (hw : w∈Metric.closedBall z r) : f w≠0 := by
    exact norm_pos_iff.mp ((by positivity : 0 < m/2).trans_le (hlo w hw))
  refine ⟨hne,?_,?_⟩
  · apply DifferentiableOn.diffContOnCl
    rw [closure_ball _ hr.ne']
    intro w hw
    obtain ⟨hw0,hw1,_⟩ := near_line_denominator hz hr1 hw
    exact (((hf w hw).deriv.neg.div (hf w hw) (hne w hw)).div
      (analyticAt_id.mul (analyticAt_id.add analyticAt_const)) (mul_ne_zero hw0 hw1)).differentiableWithinAt
  · intro w hw
    obtain ⟨hw0,hw1,hden⟩ := near_line_denominator hz hr1 hw
    have hnorm : 0 < ‖w‖*‖w+1‖ := mul_pos (norm_pos_iff.mpr hw0) (norm_pos_iff.mpr hw1)
    have hb₀ : ‖deriv f w‖/‖f w‖ ≤ 2*M/m := by
      apply (div_le_div₀ hM (hb w hw) (by positivity : 0 < m/2) (hlo w hw)).trans_eq
      ring
    have hb₁ : 1/(‖w‖*‖w+1‖) ≤ 16/(|z.im|+2)^2 := by
      apply (div_le_div_iff₀ hnorm (by positivity)).mpr
      nlinarith
    simp only [logRiesz,norm_div,norm_neg,norm_mul]
    calc
      _ = (‖deriv f w‖/‖f w‖)*(1/(‖w‖*‖w+1‖)) := by ring
      _  ≤  (2*M/m)*(16/(|z.im|+2)^2) := mul_le_mul hb₀ hb₁ (by positivity) (by positivity)
      _ = _ := by ring

lemma logRiesz_iteratedDeriv_bound {f : ℂ → ℂ} {z : ℂ} {r m M : ℝ}
    (n : ℕ) (hr : 0 < r) (hr1 : r ≤ 1/4) (hm : 0 < m) (hM : 0 ≤ M) (hz : 1 ≤  z.re)
    (hf : ∀ w∈Metric.closedBall z r,AnalyticAt ℂ f w)
    (hb : ∀ w∈Metric.closedBall z r,‖deriv f w‖ ≤ M)
    (hl : m ≤ ‖f z‖) (hMr : M*r ≤ m/2) :
    ‖iteratedDeriv n (logRiesz f) z‖ ≤ (n.factorial:ℝ)*((32*M/m)/(|z.im|+2)^2)/r^n := by
  have hh := logRiesz_local hr hr1 hm hM hz hf hb hl hMr
  exact Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hr hh.2.1
    (fun w hw => hh.2.2 w (Metric.sphere_subset_closedBall hw))

lemma logRiesz_power_bound {f : ℂ → ℂ} {z : ℂ} {P W c K d : ℝ} (n : ℕ)
    (hP : 1 ≤ P) (hW : 0 < W) (hc : 0 < c) (hK : 0 < K) (hd : 0 < d)
    (hd1 : d ≤ 1/4) (hKd : K*d ≤ c/2) (hz : 1 ≤ z.re)
    (hf : ∀ w∈Metric.closedBall z (d/P^2), AnalyticAt ℂ f w)
    (hb : ∀ w∈Metric.closedBall z (d/P^2), ‖deriv f w‖ ≤ K*W*P)
    (hl : c*W/P ≤ ‖f z‖) :
    ‖iteratedDeriv n (logRiesz f) z‖ ≤
      ((n.factorial:ℝ)*(32*K/c)/d^n)*P^(2*n+2)/(|z.im|+2)^2 := by
  have hP0 : 0 < P := by linarith
  have hr1 : d/P^2 ≤ 1/4 := by
    apply (div_le_self hd.le (one_le_pow₀ hP)).trans hd1
  have hMr : (K*W*P)*(d/P^2) ≤ (c*W/P)/2 := by
    calc
      _ = (K*d)*W/P := by field_simp
      _ ≤ (c/2)*W/P := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hKd hW.le) hP0.le
      _ = _ := by ring
  have hh := logRiesz_iteratedDeriv_bound n (by positivity : 0 < d/P^2) hr1
    (by positivity : 0 < c*W/P) (by positivity : 0 ≤ K*W*P) hz hf hb hl hMr
  apply hh.trans_eq
  rw [div_pow,pow_add,pow_mul]
  field_simp

lemma near_strip_geometry {σ t d P η : ℝ} (hσ : 1 ≤ σ) (hσ2 : σ ≤ 2)
    (hP : 1 ≤ P) (hd : 0 ≤ d) (hd1 : d ≤ 1/4) (hdη : d ≤ η/4)
    {w : ℂ} (hw : w∈Metric.closedBall ((σ:ℂ)+I*t) (d/P^2)) :
    1-η/4 ≤ w.re ∧ ‖w‖+2 ≤ 3*(|t|+2) := by
  have hr : d/P^2 ≤ d := div_le_self hd (one_le_pow₀ hP)
  have hdist : ‖w-((σ:ℂ)+I*t)‖ ≤ d/P^2 := by
    simpa only [Metric.mem_closedBall,dist_eq_norm] using hw
  have hre := Complex.re_le_norm (((σ:ℂ)+I*t)-w)
  simp only [Complex.sub_re,Complex.add_re,Complex.ofReal_re,Complex.mul_re,
    Complex.I_re,Complex.I_im,Complex.ofReal_im,mul_zero,zero_mul,sub_self,add_zero,norm_sub_rev] at hre
  have hnorm := norm_add_le (w-((σ:ℂ)+I*t)) ((σ:ℂ)+I*t)
  rw [sub_add_cancel] at hnorm
  have hnz := Complex.norm_le_abs_re_add_abs_im ((σ:ℂ)+I*t)
  simp only [Complex.add_re,Complex.add_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,zero_mul,mul_zero,
    one_mul,sub_self,zero_add,add_zero,abs_of_nonneg (by linarith : 0 ≤ σ)] at hnz
  constructor <;> linarith [abs_nonneg t]

lemma nonprincipal_logRiesz_bound (n : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → χ≠1 → ∀ σ t : ℝ, 1 ≤ σ → σ ≤ 2 →
        ‖iteratedDeriv n (logRiesz χ.LFunction) (σ+I*t)‖ ≤
          D*((q:ℝ)+2)^(1/2:ℝ)*(|t|+2)^(-(3/2:ℝ)) := by
  let ε : ℝ := 1/(4*(n+1:ℕ))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hε1 : ε ≤ 1 := by
    dsimp [ε]
    apply (div_le_one (by positivity : 0 < 4*((n+1:ℕ):ℝ))).mpr
    have hn : (1:ℝ) ≤ (n+1:ℕ) := by exact_mod_cast (Nat.succ_pos n)
    linarith
  obtain ⟨c,hc,hl⟩ := nonprincipal_strip_lower hε hε1
  obtain ⟨K₀,hK₀,hb⟩ := LFunction_deriv_norm_small_power (by linarith : 0 < ε/2) (by linarith : ε/2 ≤ 1/2)
  let K := K₀*3^ε
  have hK : 0 < K := by dsimp [K]; positivity
  let d := min (min (1/4) (ε/4)) (c/(2*K))
  have hd : 0 < d := by dsimp [d]; positivity
  have hd1 : d ≤ 1/4 := (min_le_left _ _).trans (min_le_left _ _)
  have hdε : d ≤ ε/4 := (min_le_left _ _).trans (min_le_right _ _)
  have hKd : K*d ≤ c/2 := by
    have h := min_le_right (min (1/4) (ε/4)) (c/(2*K))
    change d ≤ c/(2*K) at h
    have hh := mul_le_mul_of_nonneg_left h hK.le
    have he : K*(c/(2*K))=c/2 := by field_simp
    rwa [he] at hh
  let D := (n.factorial:ℝ)*(32*K/c)/d^n
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨D,hD,?_⟩
  intro q _ χ hχp hχ σ t hσ hσ2
  let X : ℝ := ((q:ℝ)+2)*(|t|+2)
  let P : ℝ := X^ε
  have hX : 1 ≤ X := by dsimp [X]; nlinarith [Nat.cast_nonneg (α:=ℝ) q,abs_nonneg t]
  have hX0 : 0 < X := by linarith
  have hP : 1 ≤ P := Real.one_le_rpow hX hε.le
  have hlow : c*1/P ≤ ‖χ.LFunction (σ+I*t)‖ := by
    have h := hl q χ hχp hχ σ t hσ hσ2
    change c*X^(-ε) ≤ _ at h
    simpa only [mul_one,Real.rpow_neg hX0.le,div_eq_mul_inv] using h
  have hbound : ∀ w∈Metric.closedBall ((σ:ℂ)+I*t) (d/P^2), ‖deriv χ.LFunction w‖ ≤ K*1*P := by
    intro w hw
    obtain ⟨hre,hnorm⟩ := near_strip_geometry hσ hσ2 hP hd.le hd1 hdε hw
    have h := hb q χ hχ w (by linarith)
    rw [show 2*(ε/2)=ε by ring] at h
    have hn : ((q:ℝ)+2)*(‖w‖+2) ≤ 3*X := by
      dsimp [X]
      nlinarith [mul_nonneg (show (0:ℝ) ≤ q+2 by positivity) (sub_nonneg.mpr hnorm)]
    calc
      _ ≤ K₀*((q+2)*(‖w‖+2))^ε := h
      _ ≤ K₀*(3*X)^ε := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hn hε.le) hK₀.le
      _ = K*1*P := by rw [Real.mul_rpow (by norm_num) hX0.le]; dsimp [K,P]; ring
  have hh := logRiesz_power_bound n hP zero_lt_one hc hK hd hd1 hKd (by simpa using hσ)
    (fun w _ => (DirichletCharacter.differentiable_LFunction hχ).analyticAt w) hbound hlow
  have he : ε*(2*n+2:ℕ)=1/2 := by
    dsimp [ε]
    push_cast
    field_simp
    ring
  have hpow : P^(2*n+2)=X^(1/2:ℝ) := by
    dsimp [P]
    rw [←Real.rpow_mul_natCast hX0.le,he]
  simp only [Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.I_re,Complex.I_im,
    zero_mul,one_mul,zero_add] at hh
  change ‖iteratedDeriv n (logRiesz χ.LFunction) (σ+I*t)‖ ≤ D*P^(2*n+2)/(|t|+2)^2 at hh
  rw [hpow] at hh
  apply hh.trans_eq
  dsimp [X]
  rw [Real.mul_rpow (by positivity) (by positivity),Real.rpow_neg (by positivity : 0 ≤ |t|+2)]
  have ht : (|t|+2)^(1/2:ℝ)*(|t|+2)^(3/2:ℝ)=(|t|+2)^2 := by
    rw [←Real.rpow_add (by positivity),show (1/2:ℝ)+3/2=2 by norm_num]
    norm_num
  field_simp
  rw [←ht]

end LargePrimeGaps
end OAI

-- Source module: MellinSmoothing
namespace OAI
namespace LargePrimeGaps
open Complex Real Set MeasureTheory Filter Topology
noncomputable def rieszKernel : ℝ → ℂ := (Ioc 0 1).indicator (fun t => 1-(t:ℂ))

lemma hasMellin_rieszKernel {s : ℂ} (hs : 0<s.re) :
    HasMellin rieszKernel s (1/(s*(s+1))) := by
  have h₀ := hasMellin_one_Ioc hs
  have h₁ := hasMellin_cpow_Ioc 1 (by simp; linarith : 0<s.re+(1:ℂ).re)
  have hh := hasMellin_sub h₀.1 h₁.1
  rw [h₀.2,h₁.2] at hh
  have he : (fun t : ℝ => (Ioc 0 1).indicator (fun _ : ℝ => (1:ℂ)) t-
      (Ioc 0 1).indicator (fun t : ℝ => (t:ℂ)^(1:ℂ)) t)=rieszKernel := by
    ext t
    by_cases ht : t∈Ioc (0:ℝ) 1 <;> simp [rieszKernel,ht]
  rw [he] at hh
  have hs0 : s≠0 := by intro h; simp [h] at hs
  have hs1 : s+1≠0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
  have heval : 1/s-1/(s+1)=1/(s*(s+1)) := by field_simp; ring
  rwa [heval] at hh

lemma rieszKernel_eq_max {x : ℝ} (hx : 0<x) : rieszKernel x=(max (1-x) 0:ℝ) := by
  by_cases hx1 : x≤1
  · simp [rieszKernel,Set.mem_Ioc,hx,hx1]
  · simp [rieszKernel,Set.mem_Ioc,hx,hx1,max_eq_right (by linarith : 1-x≤(0:ℝ))]

lemma rieszKernel_continuousAt {x : ℝ} (hx : 0<x) : ContinuousAt rieszKernel x := by
  have he : rieszKernel =ᶠ[𝓝 x] (fun x : ℝ => ((max (1-x) 0:ℝ):ℂ)) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact rieszKernel_eq_max hy
  exact (show ContinuousAt (fun x : ℝ => ((max (1-x) 0:ℝ):ℂ)) x by fun_prop).congr he.symm

lemma rieszDenominator_bound {s : ℂ} (hs : 1≤ s.re) :
    ‖1/(s*(s+1))‖≤2/(1+s.im^2) := by
  have ha : 1≤‖s‖ := hs.trans (Complex.re_le_norm s)
  have hb : 1≤‖s+1‖ := by have h := Complex.re_le_norm (s+1); simp at h; linarith
  have hai : |s.im|≤‖s‖ := Complex.abs_im_le_norm s
  have hbi : |s.im|≤‖s+1‖ := by simpa using Complex.abs_im_le_norm (s+1)
  have hp : 1≤‖s‖*‖s+1‖ := one_le_mul_of_one_le_of_one_le ha hb
  have hpi : s.im^2≤‖s‖*‖s+1‖ := by
    simpa only [←sq, sq_abs] using mul_le_mul hai hbi (abs_nonneg _) (norm_nonneg _)
  rw [norm_div,norm_one,norm_mul]
  apply (div_le_div_iff₀ (by positivity : 0<‖s‖*‖s+1‖) (by positivity : 0<1+s.im^2)).mpr
  nlinarith

set_option maxHeartbeats 800000 in
lemma rieszDenominator_verticalIntegrable {σ : ℝ} (hσ : 1≤σ) :
    VerticalIntegrable (fun s : ℂ => 1/(s*(s+1))) σ := by
  have hne (t : ℝ) : (σ:ℂ)+(t:ℂ)*I≠0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hne1 (t : ℝ) : (σ:ℂ)+(t:ℂ)*I+1≠0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hm : Continuous (fun t : ℝ => 1/(((σ:ℂ)+t*I)*((σ:ℂ)+t*I+1))) := by
    apply Continuous.div continuous_const (by fun_prop)
    intro t
    exact mul_ne_zero (hne t) (hne1 t)
  apply (integrable_inv_one_add_sq.const_mul 2).mono' hm.aestronglyMeasurable
  filter_upwards [] with t
  have hb := rieszDenominator_bound (s:=(σ:ℂ)+t*I) (by simpa using hσ)
  simpa only [Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.I_re,mul_zero,
    Complex.ofReal_re,Complex.I_im,mul_one,add_zero,zero_add,div_eq_mul_inv] using hb

lemma rieszKernel_mellinInv {σ x : ℝ} (hσ : 1≤σ) (hx : 0<x) :
    mellinInv σ (fun s : ℂ => 1/(s*(s+1))) x=rieszKernel x := by
  have hσ0 : (0:ℝ)<σ := by linarith
  have hm (t : ℝ) : mellin rieszKernel (σ+t*I)=1/((σ+t*I)*(σ+t*I+1)) :=
    (hasMellin_rieszKernel (by simpa using hσ0)).2
  have hF : VerticalIntegrable (mellin rieszKernel) σ := by
    unfold VerticalIntegrable
    simp_rw [hm]
    exact rieszDenominator_verticalIntegrable hσ
  rw [←mellinInv_mellin_eq σ rieszKernel hx (hasMellin_rieszKernel (by simpa using hσ0)).1 hF
    (rieszKernel_continuousAt hx)]
  simp only [mellinInv,hm]

open Complex Filter Topology
lemma principal_logRiesz_bound (n : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ σ t : ℝ, 1 ≤ σ → σ ≤ 2 →
        ‖iteratedDeriv n (logRiesz (poleRemovedL (1:DirichletCharacter ℂ 1))) (σ+I*t)‖ ≤
          D*(|t|+2)^(-(3/2:ℝ)) := by
  let ε : ℝ := 1/(4*(n+1:ℕ))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hε1 : ε ≤ 1 := by
    dsimp [ε]
    apply (div_le_one (by positivity : 0 < 4*((n+1:ℕ):ℝ))).mpr
    have hn : (1:ℝ) ≤ (n+1:ℕ) := by exact_mod_cast (Nat.succ_pos n)
    linarith
  obtain ⟨c,hc,hl⟩ := principal_strip_lower hε hε1
  obtain ⟨K₀,hK₀,hb⟩ := principal_deriv_growth hε hε1
  let K := 3*K₀*3^ε
  have hK : 0 < K := by dsimp [K]; positivity
  let d := min (min (1/4) (ε/4)) (c/(2*K))
  have hd : 0 < d := by dsimp [d]; positivity
  have hd1 : d ≤ 1/4 := (min_le_left _ _).trans (min_le_left _ _)
  have hdε : d ≤ ε/4 := (min_le_left _ _).trans (min_le_right _ _)
  have hKd : K*d ≤ c/2 := by
    have h := min_le_right (min (1/4) (ε/4)) (c/(2*K))
    change d ≤ c/(2*K) at h
    have hh := mul_le_mul_of_nonneg_left h hK.le
    have he : K*(c/(2*K))=c/2 := by field_simp
    rwa [he] at hh
  let D := (n.factorial:ℝ)*(32*K/c)/d^n
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨D,hD,?_⟩
  intro σ t hσ hσ2
  let X : ℝ := (|t|+2)
  let P : ℝ := X^ε
  have hX : 1 ≤ X := by dsimp [X]; linarith [abs_nonneg t]
  have hX0 : 0 < X := by linarith
  have hP : 1 ≤ P := Real.one_le_rpow hX hε.le
  have hlow : c*(|t|+2)/P ≤ ‖poleRemovedL (1:DirichletCharacter ℂ 1) (σ+I*t)‖ := hl σ t hσ hσ2
  have hbound : ∀ w∈Metric.closedBall ((σ:ℂ)+I*t) (d/P^2),
      ‖deriv (poleRemovedL (1:DirichletCharacter ℂ 1)) w‖ ≤ K*(|t|+2)*P := by
    intro w hw
    obtain ⟨hre,hnorm⟩ := near_strip_geometry hσ hσ2 hP hd.le hd1 hdε hw
    have h := hb w hre
    calc
      _ ≤ K₀*(‖w‖+2)*(‖w‖+2)^ε := h
      _ ≤ K₀*(3*X)*(3*X)^ε := by gcongr
      _ = K*(|t|+2)*P := by rw [Real.mul_rpow (by norm_num) hX0.le]; dsimp [K,P,X]; ring
  have hh := logRiesz_power_bound n hP (by positivity : 0 < |t|+2) hc hK hd hd1 hKd (by simpa using hσ)
    (fun w _ => (poleRemovedL_differentiable (1:DirichletCharacter ℂ 1)).analyticAt w) hbound hlow
  have he : ε*(2*n+2:ℕ)=1/2 := by
    dsimp [ε]
    push_cast
    field_simp
    ring
  have hpow : P^(2*n+2)=X^(1/2:ℝ) := by
    dsimp [P]
    rw [←Real.rpow_mul_natCast hX0.le,he]
  simp only [Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.I_re,Complex.I_im,
    zero_mul,one_mul,zero_add] at hh
  change ‖iteratedDeriv n (logRiesz (poleRemovedL (1:DirichletCharacter ℂ 1))) (σ+I*t)‖ ≤ D*P^(2*n+2)/(|t|+2)^2 at hh
  rw [hpow] at hh
  apply hh.trans_eq
  dsimp [X]
  rw [Real.rpow_neg (by positivity : 0 ≤ |t|+2)]
  have ht : (|t|+2)^(1/2:ℝ)*(|t|+2)^(3/2:ℝ)=(|t|+2)^2 := by
    rw [←Real.rpow_add (by positivity),show (1/2:ℝ)+3/2=2 by norm_num]
    norm_num
  field_simp
  rw [←ht]

lemma primitive_logRiesz_bound (n : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → ∀ σ t : ℝ, 1 ≤ σ → σ ≤ 2 →
        ‖iteratedDeriv n (logRiesz (poleRemovedL χ)) (σ+I*t)‖ ≤
          D*((q:ℝ)+2)^(1/2:ℝ)*(|t|+2)^(-(3/2:ℝ)) := by
  obtain ⟨D₀,hD₀,h₀⟩ := nonprincipal_logRiesz_bound n
  obtain ⟨D₁,hD₁,h₁⟩ := principal_logRiesz_bound n
  refine ⟨max D₀ D₁,lt_of_lt_of_le hD₀ (le_max_left _ _),?_⟩
  intro q _ χ hχp σ t hσ hσ2
  have hq : 1 ≤ ((q:ℝ)+2)^(1/2:ℝ) := Real.one_le_rpow (by linarith [Nat.cast_nonneg (α:=ℝ) q]) (by norm_num)
  by_cases hχ : χ=1
  · subst χ
    have hq1 : q=1 := by simpa [DirichletCharacter.IsPrimitive,DirichletCharacter.conductor_one] using hχp.symm
    subst q
    have hq' : 1 ≤ ((1:ℝ)+2)^(1/2:ℝ) := by simpa only [Nat.cast_one] using hq
    have hb := h₁ σ t hσ hσ2
    apply hb.trans
    have hc : D₁ ≤ max D₀ D₁*((1:ℝ)+2)^(1/2:ℝ) := by
      calc
        D₁ ≤ max D₀ D₁ := le_max_right _ _
        _ ≤ _ := le_mul_of_one_le_right (le_trans hD₀.le (le_max_left _ _)) hq'
    simpa only [Nat.cast_one] using mul_le_mul_of_nonneg_right hc (by positivity : 0 ≤ (|t|+2)^(-(3/2:ℝ)))
  · have hb := h₀ q χ hχp hχ σ t hσ hσ2
    simp only [poleRemovedL,hχ,ite_false]
    apply hb.trans
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)) (by positivity)

lemma logRiesz_poleRemoved_analyticAt {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 ≤ s.re) : AnalyticAt ℂ (logRiesz (poleRemovedL χ)) s := by
  have h₀ : s≠0 := by intro h; simp [h] at hs; norm_num at hs
  have h₁ : s+1≠0 := by
    intro h
    have hh := congrArg Complex.re h
    simp at hh
    linarith
  exact (primeLogDerivativeRegular_analyticAt χ (poleRemovedL_ne_zero χ hs)).div
    (analyticAt_id.mul (analyticAt_id.add analyticAt_const)) (mul_ne_zero h₀ h₁)

open Complex Filter Topology MeasureTheory
open scoped FourierTransform
lemma analyticAt_iteratedDeriv_local {f : ℂ → ℂ} {z : ℂ} (h : AnalyticAt ℂ f z) (n : ℕ) :
    AnalyticAt ℂ (iteratedDeriv n f) z := by
  induction n with
  | zero => simpa using h
  | succ n ih => rw [iteratedDeriv_succ]; exact ih.deriv

lemma vertical_contDiff {f : ℂ → ℂ} {z a : ℂ}
    (hf : ∀ t : ℝ, AnalyticAt ℂ f (z+a*t)) :
    ContDiff ℝ ⊤ (fun t : ℝ => f (z+a*t)) := by
  rw [contDiff_iff_contDiffAt]
  intro t
  have hr : ContDiffAt ℝ ⊤ (fun t : ℝ => (t:ℂ)) t := Complex.ofRealCLM.contDiff.contDiffAt
  exact ((hf t).contDiffAt.restrict_scalars ℝ).comp t
    (contDiffAt_const.add (contDiffAt_const.mul hr))

lemma vertical_iteratedDeriv {f : ℂ → ℂ} {z a : ℂ}
    (hf : ∀ t : ℝ, AnalyticAt ℂ f (z+a*t)) (n : ℕ) :
    iteratedDeriv n (fun t : ℝ => f (z+a*t)) =
      fun t : ℝ => a^n * iteratedDeriv n f (z+a*t) := by
  induction n with
  | zero => ext t; simp
  | succ n ih =>
    rw [iteratedDeriv_succ,ih]
    funext t
    have ha : HasDerivAt (fun t : ℝ => z+a*t) a t := by
      convert (((hasDerivAt_id (t:ℂ)).const_mul a).const_add z).comp_ofReal using 1 <;> simp
    have hd := ((analyticAt_iteratedDeriv_local (hf t) n).differentiableAt.hasDerivAt.comp t ha).const_mul (a^n)
    rw [iteratedDeriv_succ]
    simpa only [Function.comp_def,pow_succ,mul_assoc,mul_comm,mul_left_comm] using hd.deriv

noncomputable def decayMajorant (t : ℝ) : ℝ := (1+|t|)^(-(3/2:ℝ))

lemma decayMajorant_integrable : Integrable decayMajorant := by
  change Integrable (fun t : ℝ => (1+|t|)^(-(3/2:ℝ)))
  simpa only [Real.norm_eq_abs] using
    (integrable_one_add_norm (E:=ℝ) (by norm_num : (Module.finrank ℝ ℝ:ℝ) < 3/2))

lemma integrable_of_decay_bound {g : ℝ → ℂ} {M : ℝ} (hg : Continuous g)
    (hb : ∀ t, ‖g t‖ ≤ M*decayMajorant t) : Integrable g := by
  exact (decayMajorant_integrable.const_mul M).mono' hg.aestronglyMeasurable (Filter.Eventually.of_forall hb)

lemma integral_norm_le_of_decay_bound {g : ℝ → ℂ} {M : ℝ} (hg : Continuous g)
    (hb : ∀ t, ‖g t‖ ≤ M*decayMajorant t) :
    ∫ t, ‖g t‖ ≤ M*(∫ t, decayMajorant t) := by
  rw [←integral_const_mul]
  exact integral_mono (integrable_of_decay_bound hg hb).norm
    (decayMajorant_integrable.const_mul M) hb

lemma fourierInv_decay {g : ℝ → ℂ} (hg : ContDiff ℝ ⊤ g)
    (hi : ∀ n : ℕ, Integrable (iteratedDeriv n g)) (n : ℕ) {M u : ℝ}
    (hb : (∫ t, ‖iteratedDeriv n g t‖) ≤ M) (hu : 0 < |u|) :
    ‖𝓕⁻ g u‖ ≤ M/|u|^n := by
  have he := congrFun (Real.fourier_iteratedDeriv (N:=⊤) (hg.of_le le_top) (fun n _ => hi n) (n:=n) (by simp)) (-u)
  have hn := VectorFourier.norm_fourierIntegral_le_integral_norm Real.fourierChar volume
    (innerₗ ℝ) (iteratedDeriv n g) (-u)
  change ‖𝓕 (iteratedDeriv n g) (-u)‖ ≤ _ at hn
  have hn' := hn.trans hb
  rw [he,norm_smul,norm_pow] at hn'
  have hc : ‖(2:ℂ)*Real.pi*I*(-u)‖=2*Real.pi*|u| := by
    simp [Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  simp only [Complex.ofReal_neg] at hn'
  rw [hc] at hn'
  rw [Real.fourierInv_eq_fourier_neg]
  apply (le_div_iff₀ (pow_pos hu n)).mpr
  have hπ : (1:ℝ) ≤ 2*Real.pi := by linarith [Real.pi_gt_three]
  have hpow : |u|^n ≤ (2*Real.pi*|u|)^n := by
    gcongr
    exact le_mul_of_one_le_left hu.le hπ
  nlinarith [mul_le_mul_of_nonneg_right hpow (norm_nonneg (𝓕 g (-u)))]

open Complex Real Set MeasureTheory Filter Topology
lemma mellinInv_const_mul (σ : ℝ) (f : ℂ → ℂ) (a : ℂ) (x : ℝ) :
    mellinInv σ (fun s => a*f s) x=a*mellinInv σ f x := by
  simp [mellinInv,smul_eq_mul,Complex.real_smul,mul_left_comm,integral_const_mul,mul_assoc]

lemma mellinInv_term_riesz {σ y : ℝ} (hσ : 1≤σ) (hy : 0<y)
    (a : ℕ → ℂ) (n : ℕ) :
    mellinInv σ (fun s => LSeries.term a s n/(s*(s+1))) y=
      if n=0 then 0 else a n*rieszKernel ((n:ℝ)*y) := by
  by_cases hn : n=0
  · simp [hn,mellinInv]
  rw [ite_eq_right hn]
  have hi := rieszKernel_mellinInv hσ (mul_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)) hy)
  rw [←hi]
  simp only [mellinInv,LSeries.term_of_ne_zero hn,smul_eq_mul,Complex.real_smul]
  rw [mul_left_comm (a n) ((1/(2*π):ℝ):ℂ)]
  congr 1
  rw [←integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with t
  rw [Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg n) hy.le]
  simp only [Complex.ofReal_natCast,Complex.cpow_neg]
  ring

lemma riesz_inverse_integrand_norm {σ y : ℝ} (hy : 0<y) (a : ℕ → ℂ) (n : ℕ) (t : ℝ) :
    ‖(y:ℂ)^(-((σ:ℂ)+t*I))*(LSeries.term a ((σ:ℂ)+t*I) n/(((σ:ℂ)+t*I)*((σ:ℂ)+t*I+1)))‖=
      (y^(-σ)*‖LSeries.term a (σ:ℂ) n‖)*‖1/(((σ:ℂ)+t*I)*((σ:ℂ)+t*I+1))‖ := by
  simp only [norm_mul,norm_div,norm_one,Complex.norm_cpow_eq_rpow_re_of_pos hy,
    Complex.neg_re,Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,
    Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_self,add_zero,LSeries.norm_term_eq]
  ring

lemma riesz_inverse_integrand_summable {σ y : ℝ} (hσ : 1≤σ) (hy : 0<y)
    (a : ℕ → ℂ) (ha : LSeriesSummable a (σ:ℂ)) :
    (∀ n : ℕ, Integrable (fun t : ℝ => (y:ℂ)^(-((σ:ℂ)+t*I))*
        (LSeries.term a ((σ:ℂ)+t*I) n/(((σ:ℂ)+t*I)*((σ:ℂ)+t*I+1))))) ∧
    Summable (fun n : ℕ => ∫ t : ℝ, ‖(y:ℂ)^(-((σ:ℂ)+t*I))*
        (LSeries.term a ((σ:ℂ)+t*I) n/(((σ:ℂ)+t*I)*((σ:ℂ)+t*I+1)))‖) := by
  have hc (n : ℕ) : Continuous (fun t : ℝ => (y:ℂ)^(-((σ:ℂ)+t*I))*
      (LSeries.term a ((σ:ℂ)+t*I) n/(((σ:ℂ)+t*I)*((σ:ℂ)+t*I+1)))) := by
    have hz (t : ℝ) : (σ:ℂ)+t*I≠0 := by
      intro hh; have := congrArg Complex.re hh; simp at this; linarith
    have hz1 (t : ℝ) : (σ:ℂ)+t*I+1≠0 := by
      intro hh; have := congrArg Complex.re hh; simp at this; linarith
    have hd : Continuous (fun t : ℝ => ((σ:ℂ)+t*I)*((σ:ℂ)+t*I+1)) := by fun_prop
    have he : Continuous (fun t : ℝ => -((σ:ℂ)+t*I)) := by fun_prop
    apply (he.const_cpow (.inl (Complex.ofReal_ne_zero.mpr hy.ne'))).mul
    apply Continuous.div _ hd (fun t => mul_ne_zero (hz t) (hz1 t))
    by_cases hn : n=0
    · simpa [hn] using (continuous_const : Continuous (fun _t : ℝ => (0:ℂ)))
    · simp only [LSeries.term_of_ne_zero hn]
      apply continuous_const.div
      · exact (show Continuous (fun t : ℝ => (σ:ℂ)+t*I) by fun_prop).const_cpow
          (.inl (Nat.cast_ne_zero.mpr hn))
      · intro t; exact Complex.cpow_ne_zero_iff.mpr (.inl (Nat.cast_ne_zero.mpr hn))
  have hnorm (n : ℕ) : Integrable (fun t : ℝ => ‖(y:ℂ)^(-((σ:ℂ)+t*I))*
      (LSeries.term a ((σ:ℂ)+t*I) n/(((σ:ℂ)+t*I)*((σ:ℂ)+t*I+1)))‖) := by
    simp_rw [riesz_inverse_integrand_norm hy]
    exact (rieszDenominator_verticalIntegrable hσ).norm.const_mul _
  refine ⟨fun n => (integrable_norm_iff (hc n).aestronglyMeasurable).mp (hnorm n), ?_⟩
  simp_rw [riesz_inverse_integrand_norm hy,integral_const_mul]
  exact (ha.norm.mul_left (y^(-σ))).mul_right _

lemma mellinInv_LSeries_riesz {σ y : ℝ} (hσ : 1≤σ) (hy : 0<y)
    (a : ℕ → ℂ) (ha : LSeriesSummable a (σ:ℂ)) :
    mellinInv σ (fun s => LSeries a s/(s*(s+1))) y=
      ∑' n : ℕ, if n=0 then 0 else a n*rieszKernel ((n:ℝ)*y) := by
  obtain ⟨hi,hs⟩ := riesz_inverse_integrand_summable hσ hy a ha
  have he := integral_tsum_of_summable_integral_norm hi hs
  simp only [mellinInv,smul_eq_mul,Complex.real_smul]
  simp only [LSeries,←tsum_div_const,←tsum_mul_left]
  rw [←he,←tsum_mul_left]
  apply tsum_congr
  intro n
  exact mellinInv_term_riesz hσ hy a n

noncomputable def rieszSum (a : ℕ → ℂ) (x : ℝ) : ℂ :=
  ∑ n∈Finset.Ioc 0 ⌊x⌋₊, a n*(1-(n:ℂ)/(x:ℂ))

lemma rieszKernel_tsum_eq {x : ℝ} (hx : 0<x) (a : ℕ → ℂ) :
    (∑' n : ℕ, if n=0 then 0 else a n*rieszKernel ((n:ℝ)*(1/x)))=rieszSum a x := by
  classical
  rw [tsum_eq_sum (s:=Finset.Ioc 0 ⌊x⌋₊)]
  · apply Finset.sum_congr rfl
    intro n hn
    obtain ⟨hn0,hnx⟩ := Finset.mem_Ioc.mp hn
    have hn0' : (0:ℝ)<n := by exact_mod_cast hn0
    have hnx' : (n:ℝ)≤x := (Nat.le_floor_iff hx.le).mp hnx
    have hm0 : 0<(n:ℝ)*(1/x) := mul_pos hn0' (one_div_pos.mpr hx)
    have hm1 : (n:ℝ)*(1/x)≤1 := by rw [mul_one_div]; exact (div_le_one hx).mpr hnx'
    rw [ite_eq_right (by omega : n≠0),rieszKernel,
      Set.indicator_of_mem (show (n:ℝ)*(1/x)∈Ioc (0:ℝ) 1 from ⟨hm0,hm1⟩)]
    push_cast
    ring
  · intro n hn
    by_cases hn0 : n=0
    · simp [hn0]
    have hnx : x<(n:ℝ) := by
      have hnot : ¬n≤⌊x⌋₊ := by intro h; exact hn (Finset.mem_Ioc.mpr ⟨Nat.pos_of_ne_zero hn0,h⟩)
      exact lt_of_not_ge (fun h => hnot ((Nat.le_floor_iff hx.le).mpr h))
    have hm1 : ¬(n:ℝ)*(1/x)≤1 := by rw [mul_one_div]; exact not_le.mpr ((lt_div_iff₀ hx).mpr (by simpa using hnx))
    rw [ite_eq_right hn0,rieszKernel,
      Set.indicator_of_notMem (show (n:ℝ)*(1/x)∉Ioc (0:ℝ) 1 from fun h => hm1 h.2),mul_zero]

lemma rieszSum_mellinInv {σ x : ℝ} (hσ : 1≤σ) (hx : 0<x)
    (a : ℕ → ℂ) (ha : LSeriesSummable a (σ:ℂ)) :
    mellinInv σ (fun s => LSeries a s/(s*(s+1))) (1/x)=rieszSum a x := by
  rw [mellinInv_LSeries_riesz hσ (one_div_pos.mpr hx) a ha,rieszKernel_tsum_eq hx]

open Complex Real Set MeasureTheory Filter Topology
noncomputable def poleRieszKernel (y : ℝ) : ℂ :=
  (1/2:ℂ)*((y:ℂ)^(-1:ℂ)*rieszKernel y-rieszKernel y)

lemma hasMellin_poleRieszKernel {s : ℂ} (hs : 1<s.re) :
    HasMellin poleRieszKernel s (1/((s-1)*s*(s+1))) := by
  have h₀ := hasMellin_rieszKernel (s:=s) (by linarith)
  have h₁ := hasMellin_rieszKernel (s:=s+(-1)) (by simp; linarith)
  have hshift : MellinConvergent (fun t : ℝ => (t:ℂ)^(-1:ℂ) • rieszKernel t) s :=
    MellinConvergent.cpow_smul.mpr h₁.1
  have hm := mellin_cpow_smul rieszKernel s (-1)
  have hh := hasMellin_sub hshift h₀.1
  rw [hm,h₁.2,h₀.2] at hh
  have hhalf := hasMellin_const_smul hh.1 (1/2:ℂ)
  rw [hh.2] at hhalf
  have he : (1/2:ℂ) • (1/((s+-1)*(s+-1+1))-1/(s*(s+1)))=
      1/((s-1)*s*(s+1)) := by
    have hs0 : s≠0 := by intro h; simp [h] at hs; norm_num at hs
    have hs1 : s-1≠0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
    have hs2 : s+1≠0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
    rw [show s+-1+1=s by ring,←sub_eq_add_neg]
    simp only [smul_eq_mul]
    field_simp [hs0,hs1,hs2]
    ring
  rw [he] at hhalf
  change HasMellin (fun t : ℝ => (1/2:ℂ)*((t:ℂ)^(-1:ℂ)*rieszKernel t-rieszKernel t)) s _
  simpa only [smul_eq_mul] using hhalf

lemma poleRieszKernel_continuousAt {y : ℝ} (hy : 0<y) :
    ContinuousAt poleRieszKernel y := by
  apply continuousAt_const.mul
  apply ContinuousAt.sub _ (rieszKernel_continuousAt hy)
  apply ContinuousAt.mul _ (rieszKernel_continuousAt hy)
  simp only [Complex.cpow_neg_one]
  have hr : ContinuousAt (fun t : ℝ => (t:ℂ)) y := Complex.continuous_ofReal.continuousAt
  exact hr.inv₀ (Complex.ofReal_ne_zero.mpr hy.ne')

set_option maxHeartbeats 3000000 in
lemma poleRiesz_verticalIntegrable {σ : ℝ} (hσ : 1<σ) :
    VerticalIntegrable (fun s : ℂ => 1/((s-1)*s*(s+1))) σ := by
  have hn (t : ℝ) : ((σ:ℂ)+t*I-1)*((σ:ℂ)+t*I)*((σ:ℂ)+t*I+1)≠0 := by
    apply mul_ne_zero
    · apply mul_ne_zero
      · intro h; have := congrArg Complex.re h; simp at this; linarith
      · intro h; have := congrArg Complex.re h; simp at this; linarith
    · intro h; have := congrArg Complex.re h; simp at this; linarith
  have hc : Continuous (fun t : ℝ => 1/(((σ:ℂ)+t*I-1)*((σ:ℂ)+t*I)*((σ:ℂ)+t*I+1))) :=
    continuous_const.div (by fun_prop) hn
  have hbase : Integrable (fun t : ℝ => ‖1/(((σ:ℂ)+t*I)*((σ:ℂ)+t*I+1))‖) :=
    (rieszDenominator_verticalIntegrable hσ.le).norm
  change Integrable (fun t : ℝ => 1/(((σ:ℂ)+t*I-1)*((σ:ℂ)+t*I)*((σ:ℂ)+t*I+1)))
  apply (hbase.const_mul (1/(σ-1))).mono' hc.aestronglyMeasurable
  filter_upwards [] with t
  rw [norm_div,norm_one,norm_mul,norm_mul]
  have hl : σ-1 ≤ ‖(σ:ℂ)+t*I-1‖ := by simpa using Complex.re_le_norm ((σ:ℂ)+t*I-1)
  have hn0 : 0<‖(σ:ℂ)+t*I-1‖ := lt_of_lt_of_le (by linarith) hl
  have hh : 1/‖(σ:ℂ)+t*I-1‖ ≤ 1/(σ-1) := one_div_le_one_div_of_le (by linarith) hl
  simpa only [norm_div,norm_one,norm_mul,div_eq_mul_inv,mul_inv_rev,norm_inv,mul_assoc,mul_comm,mul_left_comm,one_mul,mul_one]
    using mul_le_mul_of_nonneg_right hh (norm_nonneg (1/(((σ:ℂ)+t*I)*((σ:ℂ)+t*I+1))))

lemma poleRiesz_mellinInv {σ y : ℝ} (hσ : 1<σ) (hy : 0<y) :
    mellinInv σ (fun s : ℂ => 1/((s-1)*s*(s+1))) y=poleRieszKernel y := by
  have hm (t : ℝ) : mellin poleRieszKernel (σ+t*I)=1/((σ+t*I-1)*(σ+t*I)*(σ+t*I+1)) :=
    (hasMellin_poleRieszKernel (by simpa using hσ)).2
  have hf : VerticalIntegrable (mellin poleRieszKernel) σ := by
    unfold VerticalIntegrable
    simp_rw [hm]
    exact poleRiesz_verticalIntegrable hσ
  rw [←mellinInv_mellin_eq σ poleRieszKernel hy
    (hasMellin_poleRieszKernel (by simpa using hσ)).1 hf (poleRieszKernel_continuousAt hy)]
  simp only [mellinInv,hm]

lemma poleRieszKernel_inv {x : ℝ} (hx : 1≤x) :
    poleRieszKernel (1/x)=((x/2-1+1/(2*x):ℝ):ℂ) := by
  have hx0 : 0<x := by linarith
  have hy : 0<1/x := one_div_pos.mpr hx0
  have hy1 : 1/x≤1 := (div_le_one hx0).mpr hx
  rw [poleRieszKernel,rieszKernel_eq_max hy,max_eq_left (by linarith : 0≤1-1/x)]
  simp only [Complex.cpow_neg_one,Complex.ofReal_div,Complex.ofReal_one,inv_div,div_one,
    Complex.ofReal_sub,Complex.ofReal_add,Complex.ofReal_mul,Complex.ofReal_ofNat]
  have hn : (x:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hx0.ne'
  field_simp
  ring

lemma mellinInv_integrable {σ y : ℝ} (hy : 0<y) {f : ℂ → ℂ}
    (hf : VerticalIntegrable f σ) :
    Integrable (fun t : ℝ => (y:ℂ)^(-((σ:ℂ)+t*I))*f ((σ:ℂ)+t*I)) := by
  have he : Continuous (fun t : ℝ => -((σ:ℂ)+t*I)) := by fun_prop
  have hc := he.const_cpow (.inl (Complex.ofReal_ne_zero.mpr hy.ne'))
  apply (hf.norm.const_mul (y^(-σ))).mono' (hc.aestronglyMeasurable.mul hf.aestronglyMeasurable)
  filter_upwards [] with t
  change ‖(y:ℂ)^(-((σ:ℂ)+t*I))*f ((σ:ℂ)+t*I)‖ ≤ y^(-σ)*‖f ((σ:ℂ)+t*I)‖
  simp only [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hy,Complex.neg_re,
    Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
    mul_zero,zero_mul,sub_self,add_zero,le_refl]

lemma mellinInv_add_of_verticalIntegrable {σ y : ℝ} (hy : 0<y) {f g : ℂ → ℂ}
    (hf : VerticalIntegrable f σ) (hg : VerticalIntegrable g σ) :
    mellinInv σ (fun s => f s+g s) y=mellinInv σ f y+mellinInv σ g y := by
  simp only [mellinInv,smul_eq_mul,Complex.real_smul,mul_add]
  rw [integral_add (mellinInv_integrable hy hf) (mellinInv_integrable hy hg),mul_add]

open Complex Real Set MeasureTheory Filter Topology
open scoped FourierTransform
end LargePrimeGaps
end OAI

-- Source module: RieszDecay
namespace OAI
namespace LargePrimeGaps
open Complex Filter Topology
open Complex Filter Topology MeasureTheory
open Complex Real Set MeasureTheory Filter Topology
open scoped FourierTransform
noncomputable def logRieszVertical {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (σ t : ℝ) : ℂ := logRiesz (poleRemovedL χ) (σ+2*π*t*I)

lemma logRieszVertical_contDiff {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {σ : ℝ} (hσ : 1≤σ) : ContDiff ℝ ⊤ (logRieszVertical χ σ) := by
  have h : ∀ t : ℝ, AnalyticAt ℂ (logRiesz (poleRemovedL χ)) ((σ:ℂ)+(2*π*I)*(t:ℂ)) := by
    intro t
    apply logRiesz_poleRemoved_analyticAt
    simpa using hσ
  convert vertical_contDiff h using 1
  ext t
  dsimp [logRieszVertical]
  congr 1
  ring

lemma logRieszVertical_iteratedDeriv {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {σ : ℝ} (hσ : 1≤σ) (n : ℕ) (t : ℝ) :
    iteratedDeriv n (logRieszVertical χ σ) t=
      ((2:ℂ)*π*I)^n*iteratedDeriv n (logRiesz (poleRemovedL χ)) (σ+2*π*t*I) := by
  have h : ∀ t : ℝ, AnalyticAt ℂ (logRiesz (poleRemovedL χ)) ((σ:ℂ)+(2*π*I)*(t:ℂ)) := by
    intro t
    apply logRiesz_poleRemoved_analyticAt
    simpa using hσ
  have he : logRieszVertical χ σ=(fun t : ℝ => logRiesz (poleRemovedL χ) ((σ:ℂ)+(2*π*I)*(t:ℂ))) := by
    ext t
    dsimp [logRieszVertical]
    congr 1
    ring
  simpa only [he,mul_assoc,mul_comm,mul_left_comm] using congrFun (vertical_iteratedDeriv h n) t

lemma logRieszVertical_bound (n : ℕ) :
    ∃ D : ℝ, 0<D ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
      ∀ σ t : ℝ, 1≤σ → σ≤2 →
        ‖iteratedDeriv n (logRieszVertical χ σ) t‖ ≤
          (D*((q:ℝ)+2)^(1/2:ℝ))*decayMajorant t := by
  obtain ⟨D,hD,hb⟩ := primitive_logRiesz_bound n
  refine ⟨(2*π)^n*D,by positivity,?_⟩
  intro q _ χ hp σ t hσ hσ2
  have he : (σ:ℂ)+2*π*t*I=(σ:ℂ)+I*((2*π*t:ℝ):ℂ) := by push_cast; ring
  rw [logRieszVertical_iteratedDeriv χ hσ,norm_mul,norm_pow,he]
  have hc : ‖(2:ℂ)*π*I‖=2*π := by simp [abs_of_pos pi_pos]
  rw [hc]
  have ht : (|2*π*t|+2)^(-(3/2:ℝ)) ≤ decayMajorant t := by
    dsimp [decayMajorant]
    apply Real.rpow_le_rpow_of_nonpos (by positivity)
    · rw [abs_mul,abs_mul,abs_of_pos pi_pos]
      norm_num
      nlinarith [abs_nonneg t,pi_gt_three]
    · norm_num
  calc
    _ ≤ (2*π)^n*(D*((q:ℝ)+2)^(1/2:ℝ)*(|2*π*t|+2)^(-(3/2:ℝ))) :=
      mul_le_mul_of_nonneg_left (hb q χ hp σ (2*π*t) hσ hσ2) (by positivity)
    _ ≤ (2*π)^n*(D*((q:ℝ)+2)^(1/2:ℝ)*decayMajorant t) := by gcongr
    _ = _ := by ring

lemma logRieszVertical_integrable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hp : χ.IsPrimitive) {σ : ℝ} (hσ : 1≤σ) (hσ2 : σ≤2) (n : ℕ) :
    Integrable (iteratedDeriv n (logRieszVertical χ σ)) := by
  obtain ⟨D,hD,hb⟩ := logRieszVertical_bound n
  exact integrable_of_decay_bound
    ((logRieszVertical_contDiff χ hσ).continuous_iteratedDeriv n (by simp))
    (hb q χ hp σ · hσ hσ2)

lemma logRiesz_mellinInv_bound (n : ℕ) :
    ∃ D : ℝ, 0<D ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
      ∀ σ x : ℝ, 1≤σ → σ≤2 → 1<x →
        ‖mellinInv σ (logRiesz (poleRemovedL χ)) (1/x)‖ ≤
          D*((q:ℝ)+2)^(1/2:ℝ)*x^σ/(Real.log x)^n := by
  obtain ⟨D,hD,hb⟩ := logRieszVertical_bound n
  let J : ℝ := ∫ t, decayMajorant t
  refine ⟨D*(|J|+1),by dsimp [J]; positivity,?_⟩
  intro q _ χ hp σ x hσ hσ2 hx
  have hx0 : 0<x := by linarith
  have hlog : 0<Real.log x := Real.log_pos hx
  have hi := logRieszVertical_integrable χ hp hσ hσ2
  have hg := logRieszVertical_contDiff χ hσ
  have hb' : (∫ t, ‖iteratedDeriv n (logRieszVertical χ σ) t‖) ≤ D*((q:ℝ)+2)^(1/2:ℝ)*J :=
    integral_norm_le_of_decay_bound (hg.continuous_iteratedDeriv n (by simp)) (hb q χ hp σ · hσ hσ2)
  have hf := fourierInv_decay hg hi n hb' (u:=Real.log x) (by rwa [abs_of_pos hlog])
  rw [mellinInv_eq_fourierInv σ _ (one_div_pos.mpr hx0),norm_smul,
    Complex.norm_cpow_eq_rpow_re_of_pos (one_div_pos.mpr hx0)]
  have he : -(Real.log (1/x))=Real.log x := by simp
  rw [he]
  change (1/x)^(-σ)*‖𝓕⁻ (logRieszVertical χ σ) (Real.log x)‖ ≤ _
  rw [one_div,Real.inv_rpow hx0.le,←Real.rpow_neg hx0.le,neg_neg]
  have hJ : J ≤ |J|+1 := by linarith [le_abs_self J]
  have hfac : 0≤ D*((q:ℝ)+2)^(1/2:ℝ) := by positivity
  calc
    _ ≤ x^σ*(D*((q:ℝ)+2)^(1/2:ℝ)*J/|Real.log x|^n) := mul_le_mul_of_nonneg_left hf (by positivity)
    _ ≤ x^σ*(D*((q:ℝ)+2)^(1/2:ℝ)*(|J|+1)/(Real.log x)^n) := by
      rw [abs_of_pos hlog]
      gcongr
    _ = _ := by ring

open Complex Real Set MeasureTheory Filter Topology
noncomputable def primeCoefficients {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ℕ) : ℂ :=
  χ (n:ZMod q)*(ArithmeticFunction.vonMangoldt n:ℂ)

noncomputable def characterMain {q : ℕ} (χ : DirichletCharacter ℂ q) : ℂ := by
  classical
  exact if χ=1 then 1 else 0

lemma characterMain_norm_le {q : ℕ} (χ : DirichletCharacter ℂ q) : ‖characterMain χ‖≤1 := by
  unfold characterMain
  split_ifs <;> norm_num

lemma primeCoefficients_summable {q : ℕ} (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1<s.re) :
    LSeriesSummable (primeCoefficients χ) s := DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ hs

lemma primeCoefficients_norm_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (n : ℕ) :
    ‖primeCoefficients χ n‖≤Real.log n := by
  rw [primeCoefficients,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  exact (mul_le_of_le_one_left ArithmeticFunction.vonMangoldt_nonneg (χ.norm_le_one _)).trans
    ArithmeticFunction.vonMangoldt_le_log

lemma primeRiesz_identity {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1<s.re) :
    LSeries (primeCoefficients χ) s/(s*(s+1))=
      logRiesz (poleRemovedL χ) s+characterMain χ*(1/((s-1)*s*(s+1))) := by
  have he := primeLogDerivativeRegular_eq χ hs
  change primeLogDerivativeRegular χ s=LSeries (primeCoefficients χ) s-_ at he
  have hlog : logRiesz (poleRemovedL χ) s=primeLogDerivativeRegular χ s/(s*(s+1)) := rfl
  have hs0 : s≠0 := by intro h; simp [h] at hs; norm_num at hs
  have hs1 : s-1≠0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
  have hs2 : s+1≠0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
  rw [hlog,he,characterMain]
  split_ifs <;> field_simp <;> ring

lemma logRiesz_verticalIntegrable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hp : χ.IsPrimitive) {σ : ℝ} (hσ : 1≤σ) (hσ2 : σ≤2) :
    VerticalIntegrable (logRiesz (poleRemovedL χ)) σ := by
  have hπ : (2*π:ℝ)≠0 := by positivity
  have hi := (logRieszVertical_integrable χ hp hσ hσ2 0).comp_mul_left' (inv_ne_zero hπ)
  simp only [iteratedDeriv_zero] at hi
  have he : (fun t : ℝ => logRieszVertical χ σ ((2*π)⁻¹*t))=
      (fun t : ℝ => logRiesz (poleRemovedL χ) (σ+t*I)) := by
    ext t
    dsimp [logRieszVertical]
    congr 1
    push_cast
    field_simp
  rwa [he] at hi

set_option maxHeartbeats 800000 in
lemma primeRiesz_mellinInv {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hp : χ.IsPrimitive) {σ x : ℝ} (hσ : 1<σ) (hσ2 : σ≤2) (hx : 0<x) :
    mellinInv σ (logRiesz (poleRemovedL χ)) (1/x)=
      rieszSum (primeCoefficients χ) x-characterMain χ*poleRieszKernel (1/x) := by
  have he : rieszSum (primeCoefficients χ) x=
      mellinInv σ (logRiesz (poleRemovedL χ)) (1/x)+characterMain χ*poleRieszKernel (1/x) := by
    rw [←rieszSum_mellinInv hσ.le hx _ (primeCoefficients_summable χ (by simpa using hσ))]
    calc
      _ = mellinInv σ (fun s => logRiesz (poleRemovedL χ) s+
          characterMain χ*(1/((s-1)*s*(s+1)))) (1/x) := by
        unfold mellinInv
        congr 1
        apply integral_congr_ae
        filter_upwards [] with t
        rw [primeRiesz_identity χ (by simpa using hσ)]
      _ = mellinInv σ (logRiesz (poleRemovedL χ)) (1/x)+
          mellinInv σ (fun s => characterMain χ*(1/((s-1)*s*(s+1)))) (1/x) :=
        mellinInv_add_of_verticalIntegrable (one_div_pos.mpr hx)
          (logRiesz_verticalIntegrable χ hp hσ.le hσ2) ((poleRiesz_verticalIntegrable hσ).const_mul _)
      _ = _ := by rw [mellinInv_const_mul,poleRiesz_mellinInv hσ (one_div_pos.mpr hx)]
  linear_combination -he

lemma primeRiesz_error_bound (n : ℕ) :
    ∃ D : ℝ, 0<D ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
      ∀ σ x : ℝ, 1<σ → σ≤2 → 1<x →
        ‖rieszSum (primeCoefficients χ) x-characterMain χ*(x:ℂ)/2‖ ≤
          D*((q:ℝ)+2)^(1/2:ℝ)*x^σ/(Real.log x)^n+1 := by
  obtain ⟨D,hD,hb⟩ := logRiesz_mellinInv_bound n
  refine ⟨D,hD,?_⟩
  intro q _ χ hp σ x hσ hσ2 hx
  have he := primeRiesz_mellinInv χ hp hσ hσ2 (by linarith : 0<x)
  rw [poleRieszKernel_inv hx.le] at he
  have he' : rieszSum (primeCoefficients χ) x-characterMain χ*(x:ℂ)/2=
      mellinInv σ (logRiesz (poleRemovedL χ)) (1/x)+characterMain χ*((-1+1/(2*x):ℝ):ℂ) := by
    push_cast at he ⊢
    linear_combination -he
  rw [he']
  apply (norm_add_le _ _).trans
  apply add_le_add (hb q χ hp σ x hσ.le hσ2 hx)
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
  have ht : |-1+1/(2*x)|≤1 := by
    rw [abs_le]
    have hx0 : 0<x := by linarith
    have ht0 : 0≤1/(2*x) := by positivity
    have ht1 : 1/(2*x)≤1 := (div_le_one (by positivity)).mpr (by linarith)
    constructor <;> linarith
  exact (mul_le_mul (characterMain_norm_le χ) ht (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)

open Complex Real Set MeasureTheory Filter Topology
noncomputable def weightedPrefix (a : ℕ → ℂ) (x : ℝ) : ℂ :=
  ∑ n∈Finset.Ioc 0 ⌊x⌋₊, ((x-(n:ℝ):ℝ):ℂ)*a n

lemma weightedPrefix_difference {x h : ℝ} (hh : 0≤h) (a : ℕ → ℂ) :
    weightedPrefix a (x+h)-weightedPrefix a x=
      (h:ℂ)*(∑ n∈Finset.Ioc 0 ⌊x⌋₊, a n)+
      ∑ n∈Finset.Ioc ⌊x⌋₊ ⌊x+h⌋₊, ((x+h-(n:ℝ):ℝ):ℂ)*a n := by
  classical
  have hfloor : ⌊x⌋₊≤⌊x+h⌋₊ := Nat.floor_mono (by linarith)
  have he : Finset.Ioc 0 ⌊x+h⌋₊=Finset.Ioc 0 ⌊x⌋₊ ∪ Finset.Ioc ⌊x⌋₊ ⌊x+h⌋₊ := by
    ext n
    simp only [Finset.mem_Ioc,Finset.mem_union]
    omega
  have hd : Disjoint (Finset.Ioc 0 ⌊x⌋₊) (Finset.Ioc ⌊x⌋₊ ⌊x+h⌋₊) := by
    rw [Finset.disjoint_left]
    intro n h₁ h₂
    simp only [Finset.mem_Ioc] at h₁ h₂
    omega
  unfold weightedPrefix
  rw [he,Finset.sum_union hd]
  have hs : (∑ n∈Finset.Ioc 0 ⌊x⌋₊, ((x+h-(n:ℝ):ℝ):ℂ)*a n)=
      (h:ℂ)*(∑ n∈Finset.Ioc 0 ⌊x⌋₊, a n)+
      ∑ n∈Finset.Ioc 0 ⌊x⌋₊, ((x-(n:ℝ):ℝ):ℂ)*a n := by
    rw [Finset.mul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n _
    push_cast
    ring
  rw [hs]
  ring

lemma weightedPrefix_tail_bound {x h L : ℝ} (hx : 0≤x) (hh : 0≤h) (hL : 0≤L)
    (a : ℕ → ℂ) (ha : ∀ n∈Finset.Ioc ⌊x⌋₊ ⌊x+h⌋₊, ‖a n‖≤L) :
    ‖∑ n∈Finset.Ioc ⌊x⌋₊ ⌊x+h⌋₊, ((x+h-(n:ℝ):ℝ):ℂ)*a n‖ ≤ (h+1)*(h*L) := by
  have hfloor : ⌊x⌋₊≤⌊x+h⌋₊ := Nat.floor_mono (by linarith)
  have hn (n : ℕ) (hn : n∈Finset.Ioc ⌊x⌋₊ ⌊x+h⌋₊) :
      0≤x+h-(n:ℝ) ∧ x+h-(n:ℝ)≤h := by
    obtain ⟨h₁,h₂⟩ := Finset.mem_Ioc.mp hn
    have hlo : x<(n:ℝ) := by
      have hn' : (⌊x⌋₊:ℝ)+1≤n := by exact_mod_cast h₁
      linarith [Nat.lt_floor_add_one x]
    have hup : (n:ℝ)≤x+h := (Nat.le_floor_iff (by linarith)).mp h₂
    constructor <;> linarith
  have hc : ((Finset.Ioc ⌊x⌋₊ ⌊x+h⌋₊).card:ℝ) ≤ h+1 := by
    rw [Nat.card_Ioc,Nat.cast_sub hfloor]
    have hlo := Nat.lt_floor_add_one x
    have hup := Nat.floor_le (by linarith : 0≤x+h)
    linarith
  calc
    _ ≤ ∑ n∈Finset.Ioc ⌊x⌋₊ ⌊x+h⌋₊, ‖((x+h-(n:ℝ):ℝ):ℂ)*a n‖ := norm_sum_le _ _
    _ ≤ ∑ _n∈Finset.Ioc ⌊x⌋₊ ⌊x+h⌋₊, h*L := by
      apply Finset.sum_le_sum
      intro n hn'
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hn n hn').1]
      exact mul_le_mul (hn n hn').2 (ha n hn') (norm_nonneg _) hh
    _ = ((Finset.Ioc ⌊x⌋₊ ⌊x+h⌋₊).card:ℝ)*(h*L) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hc (mul_nonneg hh hL)

lemma prefix_unsmoothing {x h L : ℝ} (hx : 0≤x) (hh : 0<h) (hL : 0≤L)
    (a : ℕ → ℂ) (δ : ℂ) (ha : ∀ n∈Finset.Ioc ⌊x⌋₊ ⌊x+h⌋₊, ‖a n‖≤L) :
    ‖(∑ n∈Finset.Ioc 0 ⌊x⌋₊, a n)-δ*(x:ℂ)‖ ≤
      (‖weightedPrefix a (x+h)-δ*((x+h:ℝ):ℂ)^2/2‖+
        ‖weightedPrefix a x-δ*(x:ℂ)^2/2‖)/h+(h+1)*L+‖δ‖*h/2 := by
  let T := ∑ n∈Finset.Ioc ⌊x⌋₊ ⌊x+h⌋₊, ((x+h-(n:ℝ):ℝ):ℂ)*a n
  let E (y : ℝ) := weightedPrefix a y-δ*(y:ℂ)^2/2
  have he : (h:ℂ)*((∑ n∈Finset.Ioc 0 ⌊x⌋₊, a n)-δ*(x:ℂ))=
      (E (x+h)-E x)-T+δ*(h:ℂ)^2/2 := by
    have hd := weightedPrefix_difference (x:=x) hh.le a
    change weightedPrefix a (x+h)-weightedPrefix a x = _+T at hd
    dsimp [E]
    push_cast
    linear_combination -hd
  have hn : h*‖(∑ n∈Finset.Ioc 0 ⌊x⌋₊, a n)-δ*(x:ℂ)‖ ≤
      (‖E (x+h)‖+‖E x‖)+((h+1)*(h*L))+‖δ‖*h^2/2 := by
    calc
      _ = ‖(h:ℂ)*((∑ n∈Finset.Ioc 0 ⌊x⌋₊, a n)-δ*(x:ℂ))‖ := by
        rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hh]
      _ = ‖(E (x+h)-E x)-T+δ*(h:ℂ)^2/2‖ := congrArg norm he
      _ ≤ ‖E (x+h)-E x‖+‖T‖+‖δ*(h:ℂ)^2/2‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
      _ ≤ (‖E (x+h)‖+‖E x‖)+((h+1)*(h*L))+‖δ‖*h^2/2 := by
        have hT : ‖T‖≤(h+1)*(h*L) := weightedPrefix_tail_bound hx hh.le hL a ha
        have hδ : ‖δ*(h:ℂ)^2/2‖=‖δ‖*h^2/2 := by
          simp [norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hh]
        rw [hδ]
        exact add_le_add (add_le_add (norm_sub_le _ _) hT) le_rfl
  have hd : h*((‖E (x+h)‖+‖E x‖)/h+(h+1)*L+‖δ‖*h/2)=
      (‖E (x+h)‖+‖E x‖)+((h+1)*(h*L))+‖δ‖*h^2/2 := by field_simp
  dsimp [E] at hn hd
  apply (mul_le_mul_iff_left₀ hh).mp
  rw [mul_comm _ h, mul_comm _ h, hd]
  exact hn

open Complex Real Set MeasureTheory Filter Topology
lemma weightedPrefix_eq_mul_rieszSum (a : ℕ → ℂ) {x : ℝ} (hx : 0<x) :
    weightedPrefix a x=(x:ℂ)*rieszSum a x := by
  unfold weightedPrefix rieszSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hx0 : (x:ℂ)≠0 := by exact_mod_cast hx.ne'
  push_cast
  field_simp

lemma rpow_one_add_inv_log {x : ℝ} (hx : 1<x) :
    x^(1+1/Real.log x)=Real.exp 1*x := by
  have hx0 : 0<x := by linarith
  have hlog : Real.log x≠0 := (Real.log_pos hx).ne'
  rw [Real.rpow_add hx0,Real.rpow_one,Real.rpow_def_of_pos hx0]
  rw [mul_one_div_cancel hlog]
  ring

lemma primeWeighted_error_bound (a : ℝ) :
    ∃ D : ℝ, 0<D ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
      ∀ x : ℝ, 1<x → 1≤Real.log x →
        ‖weightedPrefix (primeCoefficients χ) x-characterMain χ*(x:ℂ)^2/2‖ ≤
          D*((q:ℝ)+2)^(1/2:ℝ)*x^2*(Real.log x)^(-a)+x := by
  obtain ⟨D,hD,hb⟩ := primeRiesz_error_bound ⌈a⌉₊
  refine ⟨D*Real.exp 1,by positivity,?_⟩
  intro q _ χ hp x hx hL
  have hx0 : 0<x := by linarith
  have hlog : 0<Real.log x := Real.log_pos hx
  have hσ : 1<1+1/Real.log x := by linarith [one_div_pos.mpr hlog]
  have hσ2 : 1+1/Real.log x≤2 := by
    have : 1/Real.log x≤1 := (div_le_one hlog).mpr hL
    linarith
  have he : weightedPrefix (primeCoefficients χ) x-characterMain χ*(x:ℂ)^2/2=
      (x:ℂ)*(rieszSum (primeCoefficients χ) x-characterMain χ*(x:ℂ)/2) := by
    rw [weightedPrefix_eq_mul_rieszSum _ hx0]
    ring
  rw [he,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hx0]
  calc
    _ ≤ x*(D*((q:ℝ)+2)^(1/2:ℝ)*x^(1+1/Real.log x)/(Real.log x)^⌈a⌉₊+1) :=
      mul_le_mul_of_nonneg_left (hb q χ hp _ x hσ hσ2 hx) hx0.le
    _ = D*Real.exp 1*((q:ℝ)+2)^(1/2:ℝ)*x^2*(Real.log x)^(-(⌈a⌉₊:ℝ))+x := by
      rw [rpow_one_add_inv_log hx,Real.rpow_neg hlog.le,Real.rpow_natCast]
      ring
    _ ≤ _ := by
      have hn : a≤(⌈a⌉₊:ℝ) := Nat.le_ceil a
      gcongr

end LargePrimeGaps
end OAI

-- Source module: Main
namespace OAI
namespace LargePrimeGaps
open Complex Filter Topology
open Complex Filter Topology MeasureTheory
open scoped FourierTransform
open Complex Real Set MeasureTheory Filter Topology
lemma primeCharacterError_log_bound (A B : ℝ) (hA : 0<A) (hB : 0<B) :
    ∃ M : ℝ, 0<M ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
      ∀ x : ℝ, 2≤x → 1≤Real.log x → (Real.log x)^(2*A+2)≤x →
        (q:ℝ)≤(Real.log x)^B →
        ‖primeCharacterError x χ‖≤M*x*(Real.log x)^(-A) := by
  obtain ⟨D,hD,hb⟩ := primeWeighted_error_bound (B+2*A+2)
  refine ⟨15*D+8,by positivity,?_⟩
  intro q _ χ hp x hx hL hpower hq
  let L := Real.log x
  let K := A+2
  let a := B+2*A+2
  let Q := ((q:ℝ)+2)^(1/2:ℝ)
  let h := x/L^K
  have hx0 : 0<x := by linarith
  have hx1 : 1<x := by linarith
  have hL0 : 0<L := lt_of_lt_of_le zero_lt_one hL
  have hK : 0<K := by dsimp [K]; linarith
  have ha : 0<a := by dsimp [a]; linarith
  have hpK : 0<L^K := Real.rpow_pos_of_pos hL0 _
  have hh0 : 0<h := div_pos hx0 hpK
  have hK1 : 1≤L^K := Real.one_le_rpow hL hK.le
  have hhx : h≤x := (div_le_self hx0.le hK1)
  have hKh : L^K≤x := by
    apply (Real.rpow_le_rpow_of_exponent_le hL (show K≤2*A+2 by dsimp [K]; linarith)).trans
    exact hpower
  have hh1 : 1≤h := (le_div_iff₀ hpK).mpr (by simpa using hKh)
  have hyx : x≤x+h := by linarith
  have hy : 1<x+h := by linarith
  have hy2 : x+h≤2*x := by linarith
  have hLy : L≤Real.log (x+h) := Real.log_le_log hx0 hyx
  have hLy1 : 1≤Real.log (x+h) := hL.trans hLy
  have hLy2 : Real.log (x+h)≤2*L := by
    calc
      _ ≤ Real.log (x^2) := Real.log_le_log (by linarith) (by nlinarith)
      _ = _ := by rw [Real.log_pow]; rfl
  have hQ0 : 0≤Q := by dsimp [Q]; positivity
  have hQ : Q≤3*L^B := by
    have hq2 : 1≤(q:ℝ)+2 := by have := Nat.cast_nonneg (α:=ℝ) q; linarith
    have hqpow : Q≤(q:ℝ)+2 := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hq2 (show (1/2:ℝ)≤1 by norm_num)
    have hLB : 1≤L^B := Real.one_le_rpow hL hB.le
    linarith
  let E (y : ℝ) := ‖weightedPrefix (primeCoefficients χ) y-characterMain χ*(y:ℂ)^2/2‖
  have hEx : E x≤D*Q*x^2*L^(-a)+x := hb q χ hp x hx1 hL
  have hEy : E (x+h)≤4*D*Q*x^2*L^(-a)+2*x := by
    calc
      _ ≤ D*Q*(x+h)^2*(Real.log (x+h))^(-a)+(x+h) := hb q χ hp (x+h) hy hLy1
      _ ≤ D*Q*(2*x)^2*L^(-a)+2*x := by
        apply add_le_add _ hy2
        apply mul_le_mul _ (Real.rpow_le_rpow_of_nonpos hL0 hLy (neg_nonpos.mpr ha.le)) (by positivity) (by positivity)
        gcongr
      _ = _ := by ring
  have hcoeff (n : ℕ) (hn : n∈Finset.Ioc ⌊x⌋₊ ⌊x+h⌋₊) :
      ‖primeCoefficients χ n‖≤2*L := by
    have hn0 : 0<(n:ℝ) := by exact_mod_cast (show 0<n by have := (Finset.mem_Ioc.mp hn).1; omega)
    have hnx : (n:ℝ)≤x+h := (Nat.le_floor_iff (by linarith : 0≤x+h)).mp (Finset.mem_Ioc.mp hn).2
    exact (primeCoefficients_norm_le χ n).trans ((Real.log_le_log hn0 hnx).trans hLy2)
  have heq : primeCharacterError x χ=
      (∑ n∈Finset.Ioc 0 ⌊x⌋₊, primeCoefficients χ n)-characterMain χ*(x:ℂ) := by
    classical
    simp only [primeCharacterError,primeCharacterPrefix,primeCoefficients,characterMain]
    split_ifs <;> simp
  rw [heq]
  have hu := prefix_unsmoothing hx0.le hh0 (show 0≤2*L by positivity)
    (primeCoefficients χ) (characterMain χ) hcoeff
  change _≤(E (x+h)+E x)/h+(h+1)*(2*L)+‖characterMain χ‖*h/2 at hu
  have hδ : ‖characterMain χ‖*h/2≤h := by
    have := mul_le_mul_of_nonneg_right (characterMain_norm_le χ) hh0.le
    linarith
  have htail : (h+1)*(2*L)≤4*h*L := by nlinarith
  have herr : (E (x+h)+E x)/h ≤ 15*D*x*L^(-A)+3*x*L^(-A) := by
    calc
      _ ≤ (5*D*Q*x^2*L^(-a)+3*x)/h := by
        apply div_le_div_of_nonneg_right _ hh0.le
        linarith
      _ ≤ (5*D*(3*L^B)*x^2*L^(-a)+3*x)/h := by gcongr
      _ = (15*D*L^B*x^2*L^(-a)+3*x)/h := by ring
      _ = 15*D*x*L^(-A)+3*L^K := by
        dsimp [h]
        rw [div_eq_mul_inv,inv_div]
        have hr : L^B*L^(-a)*L^K=L^(-A) := by
          rw [←Real.rpow_add hL0,←Real.rpow_add hL0]
          congr 1
          dsimp [a,K]
          ring
        field_simp
        linear_combination 15*D*x*hr
      _ ≤ _ := by
        have ht : L^K≤x*L^(-A) := by
          calc
            _ = L^(2*A+2)*L^(-A) := by rw [←Real.rpow_add hL0]; congr 1; dsimp [K]; ring
            _ ≤ _ := mul_le_mul_of_nonneg_right hpower (by positivity)
        nlinarith [ht]
  have hsmall : h≤x*L^(-A) := by
    dsimp [h]
    rw [div_eq_mul_inv,←Real.rpow_neg hL0.le]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hL (show -K≤-A by dsimp [K]; linarith)) hx0.le
  have htail' : 4*h*L≤4*x*L^(-A) := by
    calc
      _ = 4*x*L^(1-K) := by
        dsimp [h]
        rw [div_eq_mul_inv,Real.rpow_sub hL0,Real.rpow_one]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hL (show 1-K≤-A by dsimp [K]; linarith)) (by positivity)
  calc
    _ ≤ (E (x+h)+E x)/h+(h+1)*(2*L)+‖characterMain χ‖*h/2 := hu
    _ ≤ (15*D*x*L^(-A)+3*x*L^(-A))+4*x*L^(-A)+x*L^(-A) := by
      exact add_le_add (add_le_add herr (htail.trans htail')) (hδ.trans hsmall)
    _ = _ := by ring

theorem siegelWalfisz : SiegelWalfisz := by
  intro A B hA hB
  obtain ⟨M,hM,hb⟩ := primeCharacterError_log_bound A B hA hB
  have hevent : ∀ᶠ x : ℝ in atTop, 2≤x ∧ 1≤Real.log x ∧ (Real.log x)^(2*A+2)≤x := by
    filter_upwards [eventually_ge_atTop (2:ℝ),eventually_ge_atTop (Real.exp 1),
      eventually_log_rpow_le_rpow (2*A+2) (by norm_num : (0:ℝ)<1)] with x hx hex hp
    refine ⟨hx,?_,by simpa only [Real.rpow_one] using hp⟩
    rw [←Real.log_exp (1:ℝ)]
    exact Real.log_le_log (Real.exp_pos _) hex
  obtain ⟨x₀,hx₀⟩ := eventually_atTop.mp hevent
  refine ⟨M,hM,max x₀ 2,by have := le_max_right x₀ (2:ℝ); linarith,?_⟩
  intro x hx d hd hdlog χ hχ
  let : NeZero d := ⟨ne_of_gt hd⟩
  obtain ⟨hx2,hlog,hpower⟩ := hx₀ x ((le_max_left _ _).trans hx)
  exact hb d χ hχ x hx2 hlog hpower hdlog

end LargePrimeGaps
end OAI


-- Source module: OrthantIntegrals
namespace OAI
namespace LargePrimeGaps
open Filter
open Set Filter MeasureTheory
open scoped Topology ContDiff
noncomputable def residueSlice (f : ℕ → ℝ) (L U q c : ℕ) : ℝ :=
  ∑ n ∈ (Finset.Ioc L U).filter (fun n => n % q = c), f n

noncomputable def residuePrefix (f : ℕ → ℝ) (Y q c : ℕ) : ℝ :=
  residueSlice f 0 Y q c

end LargePrimeGaps
end OAI

-- Source module: CharacterErrors
namespace OAI
namespace LargePrimeGaps
open Filter
open Set Filter MeasureTheory
open scoped Topology ContDiff
open Asymptotics
open scoped Classical
open scoped ContDiff
open Topology
open scoped Convolution ContDiff Pointwise
theorem character_prefix_orthogonality (x : ℝ) {q c : ℕ} (hq : 0<q)
    (hc : c<q) (hcop : Nat.Coprime c q) :
    ∑ χ : DirichletCharacter ℂ q, χ (c:ZMod q)⁻¹*primeCharacterPrefix x χ=
      (q.totient:ℂ)*(residuePrefix ArithmeticFunction.vonMangoldt ⌊x⌋₊ q c:ℂ) := by
  classical
  have : NeZero q := ⟨ne_of_gt hq⟩
  have hu : IsUnit (c:ZMod q) := (ZMod.isUnit_iff_coprime c q).mpr hcop
  have he (n : ℕ) : (c:ZMod q)=(n:ZMod q) ↔ n % q = c := by
    rw [ZMod.natCast_eq_natCast_iff',Nat.mod_eq_of_lt hc]
    exact eq_comm
  unfold primeCharacterPrefix
  simp_rw [Finset.mul_sum,←mul_assoc]
  rw [Finset.sum_comm]
  simp_rw [←Finset.sum_mul,DirichletCharacter.sum_char_inv_mul_char_eq ℂ hu,he]
  simp only [residuePrefix,residueSlice,Complex.ofReal_sum,Finset.sum_filter,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  split_ifs <;> simp

theorem character_error_orthogonality (x : ℝ) {q c : ℕ} (hq : 0<q)
    (hc : c<q) (hcop : Nat.Coprime c q) :
    ∑ χ : DirichletCharacter ℂ q, χ (c:ZMod q)⁻¹*primeCharacterError x χ=
      (q.totient:ℂ)*((residuePrefix ArithmeticFunction.vonMangoldt ⌊x⌋₊ q c-x/q.totient:ℝ):ℂ) := by
  classical
  have : NeZero q := ⟨ne_of_gt hq⟩
  have hu : IsUnit (c:ZMod q) := (ZMod.isUnit_iff_coprime c q).mpr hcop
  have huinv : IsUnit (c:ZMod q)⁻¹ := by
    obtain ⟨u,hu⟩ := hu
    rw [←hu,ZMod.inv_coe_unit]
    exact (u⁻¹).isUnit
  have ht : (q.totient:ℂ)≠0 := by exact_mod_cast ne_of_gt (Nat.totient_pos.mpr hq)
  simp only [primeCharacterError,mul_sub,Finset.sum_sub_distrib]
  rw [character_prefix_orthogonality x hq hc hcop]
  simp only [mul_ite,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,↓reduceIte,MulChar.one_apply huinv,one_mul]
  push_cast
  field_simp

theorem endpointClassError_le_character_sum (x : ℝ) {q c : ℕ} (hq : 0<q)
    (hc : c<q) (hcop : Nat.Coprime c q) :
    |residuePrefix ArithmeticFunction.vonMangoldt ⌊x⌋₊ q c-x/q.totient|≤
      (∑ χ : DirichletCharacter ℂ q, ‖primeCharacterError x χ‖)/(q.totient:ℝ) := by
  have hphi : (0:ℝ)<q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  apply (le_div_iff₀ hphi).mpr
  have hh := character_error_orthogonality x hq hc hcop
  calc
    _ = ‖(q.totient:ℂ)*((residuePrefix ArithmeticFunction.vonMangoldt ⌊x⌋₊ q c-x/q.totient:ℝ):ℂ)‖ := by
      rw [norm_mul,Complex.norm_natCast,Complex.norm_real,Real.norm_eq_abs,mul_comm]
    _ = ‖∑ χ : DirichletCharacter ℂ q, χ (c:ZMod q)⁻¹*primeCharacterError x χ‖ := congrArg norm hh.symm
    _ ≤ ∑ χ : DirichletCharacter ℂ q, ‖χ (c:ZMod q)⁻¹*primeCharacterError x χ‖ := norm_sum_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro χ _
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one _)

theorem vonMangoldt_noncoprime_sum_le (X : ℕ) {q : ℕ} (hq : 0<q) :
    (∑ n∈(Finset.Ioc 0 X).filter (fun n => ¬Nat.Coprime n q),
      ArithmeticFunction.vonMangoldt n)≤(Nat.log 2 X:ℝ)*Real.log q := by
  classical
  let S := (Finset.Ioc 0 X).filter (fun n => ¬Nat.Coprime n q ∧ ArithmeticFunction.vonMangoldt n≠0)
  have he : (∑ n∈(Finset.Ioc 0 X).filter (fun n => ¬Nat.Coprime n q),
      ArithmeticFunction.vonMangoldt n)=∑ n∈S,ArithmeticFunction.vonMangoldt n := by
    simp only [S,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n _
    by_cases hcop : Nat.Coprime n q <;> by_cases hn : ArithmeticFunction.vonMangoldt n=0 <;> simp [hcop,hn]
  rw [he]
  have hsub : S⊆(q^(Nat.log 2 X)).divisors := by
    intro n hn
    obtain ⟨hnI,hnq,hnv⟩ := Finset.mem_filter.mp hn
    obtain ⟨p,k,hp,_hk,hpkn⟩ := ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hnv
    have hp' : p.Prime := Nat.prime_iff.mpr hp
    have hdp : p∣q := by
      by_contra hd
      have hc := (hp'.coprime_iff_not_dvd).mpr hd
      exact hnq (hpkn ▸ hc.pow_left k)
    have hkX : k≤Nat.log 2 X := by
      apply Nat.le_log_of_pow_le (by norm_num : 1<2)
      calc
        2^k≤p^k := Nat.pow_le_pow_left hp'.two_le k
        _ = n := hpkn
        _ ≤ X := (Finset.mem_Ioc.mp hnI).2
    apply Nat.mem_divisors.mpr
    refine ⟨?_,pow_ne_zero _ (ne_of_gt hq)⟩
    rw [←hpkn]
    exact (pow_dvd_pow_of_dvd hdp k).trans (pow_dvd_pow q hkX)
  calc
    _ ≤ ∑ n∈(q^(Nat.log 2 X)).divisors,ArithmeticFunction.vonMangoldt n :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg)
    _ = Real.log ((q^(Nat.log 2 X):ℕ):ℝ) := ArithmeticFunction.vonMangoldt_sum
    _ = _ := by rw [Nat.cast_pow,Real.log_pow]

theorem primitiveCharacter_eq_one_iff {q : ℕ} (hq : 0<q) (χ : DirichletCharacter ℂ q) :
    χ.primitiveCharacter=1 ↔ χ=1 := by
  have : NeZero q := ⟨ne_of_gt hq⟩
  constructor
  · intro h
    rw [←DirichletCharacter.changeLevel_primitiveCharacter χ,h,DirichletCharacter.changeLevel_one]
  · rintro rfl
    exact DirichletCharacter.primitiveCharacter_one

theorem primeCharacterPrefix_primitive_difference (x : ℝ) {q : ℕ} (hq : 0<q)
    (χ : DirichletCharacter ℂ q) :
    ‖primeCharacterPrefix x χ-primeCharacterPrefix x χ.primitiveCharacter‖≤
      (Nat.log 2 ⌊x⌋₊:ℝ)*Real.log q := by
  have hsame (n : ℕ) (hn : Nat.Coprime n q) :
      χ.primitiveCharacter (n:ZMod χ.conductor)=χ (n:ZMod q) := by
    simpa only [Int.cast_natCast] using χ.primitiveCharacter_apply_of_isCoprime hn.isCoprime
  have hzero (n : ℕ) (hn : ¬Nat.Coprime n q) : χ (n:ZMod q)=0 :=
    χ.map_nonunit (fun h => hn ((ZMod.isUnit_iff_coprime n q).mp h))
  calc
    _ = ‖∑ n∈Finset.Ioc 0 ⌊x⌋₊,(χ (n:ZMod q)-χ.primitiveCharacter (n:ZMod χ.conductor))*
        (ArithmeticFunction.vonMangoldt n:ℂ)‖ := by
      congr 1
      simp only [primeCharacterPrefix,sub_mul,Finset.sum_sub_distrib]
    _ ≤ ∑ n∈Finset.Ioc 0 ⌊x⌋₊,‖(χ (n:ZMod q)-χ.primitiveCharacter (n:ZMod χ.conductor))*
        (ArithmeticFunction.vonMangoldt n:ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ n∈(Finset.Ioc 0 ⌊x⌋₊).filter (fun n => ¬Nat.Coprime n q),ArithmeticFunction.vonMangoldt n := by
      rw [Finset.sum_filter]
      apply Finset.sum_le_sum
      intro n _
      by_cases hn : Nat.Coprime n q
      · simp [hn,hsame n hn]
      · simp only [ite_eq_left hn,hzero n hn,zero_sub,norm_mul,norm_neg,Complex.norm_real,Real.norm_eq_abs,
          abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
        exact mul_le_of_le_one_left ArithmeticFunction.vonMangoldt_nonneg
          (χ.primitiveCharacter.norm_le_one _)
    _ ≤ _ := vonMangoldt_noncoprime_sum_le _ hq

theorem primeCharacterError_primitive_difference (x : ℝ) {q : ℕ} (hq : 0<q)
    (χ : DirichletCharacter ℂ q) :
    ‖primeCharacterError x χ-primeCharacterError x χ.primitiveCharacter‖≤
      (Nat.log 2 ⌊x⌋₊:ℝ)*Real.log q := by
  have he : primeCharacterError x χ-primeCharacterError x χ.primitiveCharacter=
      primeCharacterPrefix x χ-primeCharacterPrefix x χ.primitiveCharacter := by
    simp only [primeCharacterError,primitiveCharacter_eq_one_iff hq χ]
    ring
  rw [he]
  exact primeCharacterPrefix_primitive_difference x hq χ

theorem primeCharacterError_le_primitive (x : ℝ) {q : ℕ} (hq : 0<q)
    (χ : DirichletCharacter ℂ q) :
    ‖primeCharacterError x χ‖≤‖primeCharacterError x χ.primitiveCharacter‖+
      (Nat.log 2 ⌊x⌋₊:ℝ)*Real.log q := by
  have hn := norm_add_le (primeCharacterError x χ.primitiveCharacter)
    (primeCharacterError x χ-primeCharacterError x χ.primitiveCharacter)
  rw [add_sub_cancel] at hn
  exact hn.trans (add_le_add_right (primeCharacterError_primitive_difference x hq χ) _)

end LargePrimeGaps
end OAI

end

open Finset Filter MeasureTheory
open scoped Topology

namespace GoldbachMajorArc

noncomputable section

def primeWeight (k : ℕ) : ℝ := if k.Prime then Real.log (k : ℝ) else 0

def phase (x : ℝ) : ℂ := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

def primeSum (n : ℕ) (t : ℝ) : ℂ :=
  ∑ k ∈ range (n + 1), (primeWeight k : ℂ) * phase ((k : ℝ) * t)

private theorem phase_add (x y : ℝ) : phase (x + y) = phase x * phase y := by
  unfold phase
  rw [← Complex.exp_add]
  push_cast
  congr 1
  ring

/-- The geometric sum in the rational-frequency approximation, with the same endpoints as the prime sum. -/
def kernel (n : ℕ) (β : ℝ) : ℂ := ∑ k ∈ range (n + 1), phase ((k : ℝ) * β)

def unitMean (q a : ℕ) : ℂ :=
  (∑ r ∈ (range q).filter (fun r => Nat.Coprime r q), phase ((r : ℝ) * ((a : ℝ) / q))) /
    (q.totient : ℂ)

def centerErrorTerm (r : ℝ) (A : ℂ) (k : ℕ) : ℂ :=
  (primeWeight k : ℂ) * phase ((k : ℝ) * r) - A

/-- The largest initial segment discrepancy at the center, through the last term k = n. -/
def prefixError (n : ℕ) (r : ℝ) (A : ℂ) : ℝ :=
  (range (n + 2)).sup' ⟨0, by simp⟩ (fun m => ‖∑ k ∈ range m, centerErrorTerm r A k‖)

private theorem prefix_le {m n : ℕ} (hm : m ≤ n + 1) (r : ℝ) (A : ℂ) :
    ‖∑ k ∈ range m, centerErrorTerm r A k‖ ≤ prefixError n r A :=
  Finset.le_sup' (fun m => ‖∑ k ∈ range m, centerErrorTerm r A k‖) (mem_range.mpr (by omega))

private theorem norm_phase (x : ℝ) : ‖phase x‖ = 1 := Complex.norm_exp_ofReal_mul_I _

private theorem phase_step (k : ℕ) (β : ℝ) :
    ‖phase (((k + 1 : ℕ) : ℝ) * β) - phase ((k : ℝ) * β)‖ ≤ 2 * Real.pi * |β| := by
  have shift : ((k + 1 : ℕ) : ℝ) * β = k * β + β := by push_cast; ring
  rw [shift, phase_add, ← mul_sub_one, norm_mul, norm_phase, one_mul]
  unfold phase
  rw [mul_comm _ Complex.I]
  calc
    _ ≤ ‖2 * Real.pi * β‖ := Real.norm_exp_I_mul_ofReal_sub_one_le
    _ = _ := by rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * Real.pi)]

/-- Abel summation transports the finite initial segment discrepancies at r to a nearby frequency. -/
theorem shifted_sum_error (n : ℕ) (r β : ℝ) (A : ℂ) :
    ‖primeSum n (r + β) - A * kernel n β‖ ≤
      prefixError n r A * (1 + 2 * Real.pi * (n : ℝ) * |β|) := by
  let g := centerErrorTerm r A
  let v := fun k : ℕ => phase ((k : ℝ) * β)
  let D := prefixError n r A
  have hD : 0 ≤ D := (norm_nonneg _).trans (prefix_le (m := 0) (n := n) (by omega) r A)
  have expand : primeSum n (r + β) - A * kernel n β = ∑ k ∈ range (n + 1), v k * g k := by
    unfold primeSum kernel
    rw [mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun k _ => ?_
    rw [mul_add, phase_add]
    dsimp [v, g, centerErrorTerm]
    ring
  have habel := Finset.sum_range_by_parts (M := ℂ) v g (n + 1)
  simp only [Nat.add_sub_cancel, smul_eq_mul] at habel
  have hfirst : ‖v n * ∑ k ∈ range (n + 1), g k‖ ≤ D := by
    rw [norm_mul, show ‖v n‖ = 1 from norm_phase _, one_mul]
    exact prefix_le le_rfl r A
  have htail : ‖∑ i ∈ range n, (v (i + 1) - v i) * ∑ k ∈ range (i + 1), g k‖ ≤
      (n : ℝ) * (2 * Real.pi * |β| * D) := by
    calc
      _ ≤ ∑ i ∈ range n, ‖(v (i + 1) - v i) * ∑ k ∈ range (i + 1), g k‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _i ∈ range n, 2 * Real.pi * |β| * D := by
        refine sum_le_sum fun i hi => ?_
        rw [norm_mul]
        exact mul_le_mul (phase_step i β) (prefix_le (by have := mem_range.mp hi; omega) r A)
          (norm_nonneg _) (by positivity)
      _ = _ := by simp
  rw [expand, habel]
  calc
    _ ≤ _ := norm_sub_le _ _
    _ ≤ D + n * (2 * Real.pi * |β| * D) := add_le_add hfirst htail
    _ = _ := by dsimp [D]; ring

private theorem phase_nat (k : ℕ) : phase (k : ℝ) = 1 := by
  unfold phase
  convert Complex.exp_nat_mul_two_pi_mul_I k using 2
  push_cast
  ring

private theorem phase_modulo {q : ℕ} (hq : 0 < q) (k a : ℕ) :
    phase ((k : ℝ) * ((a : ℝ) / q)) = phase (((k % q : ℕ) : ℝ) * ((a : ℝ) / q)) := by
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hk : (k : ℝ) = ((k % q : ℕ) : ℝ) + q * ((k / q : ℕ) : ℝ) := by
    exact_mod_cast (Nat.mod_add_div k q).symm
  have harg : (k : ℝ) * ((a : ℝ) / q) =
      ((k % q : ℕ) : ℝ) * ((a : ℝ) / q) + (((k / q * a : ℕ) : ℝ)) := by
    push_cast
    nth_rw 1 [hk]
    field_simp
  rw [harg, phase_add, phase_nat, mul_one]

/-- Logarithmic prime weight in one residue class for the initial segment 0 ≤ k < m. -/
def classMass (m q b : ℕ) : ℝ := ∑ k ∈ (range m).filter (fun k => k % q = b), primeWeight k

def classError (m q b : ℕ) : ℝ :=
  classMass m q b - if b.Coprime q then (m : ℝ) / q.totient else 0

/-- Exact expansion of the initial segment discrepancy at a rational center in progression errors. -/
theorem center_prefix_eq {q : ℕ} (hq : 0 < q) (a m : ℕ) :
    ∑ k ∈ range m, centerErrorTerm ((a : ℝ) / q) (unitMean q a) k =
      ∑ b ∈ range q, (classError m q b : ℂ) * phase ((b : ℝ) * ((a : ℝ) / q)) := by
  let e := fun k : ℕ => phase ((k : ℝ) * ((a : ℝ) / q))
  have masses : (∑ k ∈ range m, (primeWeight k : ℂ) * e k) =
      ∑ b ∈ range q, (classMass m q b : ℂ) * e b := by
    symm
    calc
      _ = ∑ b ∈ range q, ∑ k ∈ (range m).filter (fun k => k % q = b),
          (primeWeight k : ℂ) * e k := by
        refine sum_congr rfl fun b _ => ?_
        rw [classMass, Complex.ofReal_sum, sum_mul]
        refine sum_congr rfl fun k hk => ?_
        have he : e k = e b := by
          dsimp [e]
          rw [phase_modulo hq k a, (mem_filter.mp hk).2]
        rw [he]
      _ = _ := sum_fiberwise_of_maps_to (fun k _ => mem_range.mpr (Nat.mod_lt k hq)) _
  have model : (m : ℂ) * unitMean q a =
      ∑ b ∈ range q, (↑(if b.Coprime q then (m : ℝ) / q.totient else 0) : ℂ) * e b := by
    calc
      _ = ((m : ℂ) / q.totient) * ∑ b ∈ (range q).filter (fun b => b.Coprime q), e b := by
        unfold unitMean
        dsimp [e]
        ring
      _ = _ := by
        rw [mul_sum, sum_filter]
        refine sum_congr rfl fun b _ => ?_
        by_cases h : b.Coprime q
        · rw [ite_eq_left h, ite_eq_left h, Complex.ofReal_div, Complex.ofReal_natCast, Complex.ofReal_natCast]
        · rw [ite_eq_right h, ite_eq_right h, Complex.ofReal_zero, zero_mul]
  change (∑ k ∈ range m, ((primeWeight k : ℂ) * e k - unitMean q a)) = _
  rw [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul, masses, model, ← sum_sub_distrib]
  refine sum_congr rfl fun b _ => ?_
  rw [← sub_mul, classError, Complex.ofReal_sub]

/-- A useful bound even without a uniform prime number theorem in progressions. -/
theorem center_prefix_bound {q : ℕ} (hq : 0 < q) (a m : ℕ) :
    ‖∑ k ∈ range m, centerErrorTerm ((a : ℝ) / q) (unitMean q a) k‖ ≤
      ∑ b ∈ range q, |classError m q b| := by
  rw [center_prefix_eq hq]
  refine (norm_sum_le _ _).trans ?_
  apply sum_le_sum
  intro b _
  rw [norm_mul, norm_phase, mul_one, Complex.norm_real, Real.norm_eq_abs]

end

end GoldbachMajorArc

namespace GoldbachMajorArc

open Finset Filter MeasureTheory
open OAI.LargePrimeGaps

noncomputable section

/-- The character form of Siegel–Walfisz gives a uniform bound for a reduced class.
The second term pays for replacing the character by its primitive character. -/
theorem progression_error (A B : ℝ) (hA : 0 < A) (hB : 0 < B) :
    ∃ M : ℝ, 0 < M ∧ ∃ x₀ : ℝ, 1 < x₀ ∧
      ∀ x : ℝ, x₀ ≤ x → ∀ q b : ℕ, 0 < q → (q : ℝ) ≤ (Real.log x) ^ B →
        b < q → b.Coprime q →
        |residuePrefix ArithmeticFunction.vonMangoldt ⌊x⌋₊ q b - x / q.totient| ≤
          M * x * (Real.log x) ^ (-A) + (Nat.log 2 ⌊x⌋₊ : ℝ) * Real.log q := by
  obtain ⟨M, hM, x₀, hx₀, hχ⟩ := siegelWalfisz A B hA hB
  refine ⟨M, hM, x₀, hx₀, ?_⟩
  intro x hx q b hq hqlog hb hcop
  let : NeZero q := ⟨hq.ne'⟩
  have hchar (χ : DirichletCharacter ℂ q) :
      ‖primeCharacterError x χ‖ ≤
        M * x * (Real.log x) ^ (-A) + (Nat.log 2 ⌊x⌋₊ : ℝ) * Real.log q := by
    have hcond : (χ.conductor : ℝ) ≤ q := by
      exact_mod_cast Nat.le_of_dvd hq χ.conductor_dvd_level
    exact (primeCharacterError_le_primitive x hq χ).trans (add_le_add
      (hχ x hx χ.conductor (Nat.pos_of_ne_zero χ.conductor_ne_zero) (hcond.trans hqlog) χ.primitiveCharacter
        χ.primitiveCharacter_isPrimitive) (le_refl _))
  have hcard : Fintype.card (DirichletCharacter ℂ q) = q.totient := by
    simpa only [Nat.card_eq_fintype_card] using
      DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  apply (endpointClassError_le_character_sum x hq hb hcop).trans
  apply (div_le_iff₀ hφ).mpr
  calc
    _ ≤ ∑ _χ : DirichletCharacter ℂ q,
        (M * x * (Real.log x) ^ (-A) + (Nat.log 2 ⌊x⌋₊ : ℝ) * Real.log q) :=
      sum_le_sum fun χ _ => hchar χ
    _ = _ := by rw [sum_const, card_univ, hcard, nsmul_eq_mul, mul_comm]

private theorem primeWeight_le_mangoldt (k : ℕ) :
    primeWeight k ≤ ArithmeticFunction.vonMangoldt k := by
  by_cases hk : k.Prime
  · simp [primeWeight, hk, ArithmeticFunction.vonMangoldt_apply_prime hk]
  · simp [primeWeight, hk]

private theorem classMass_succ (N q b : ℕ) :
    classMass (N + 1) q b =
      ∑ k ∈ (Ioc 0 N).filter (fun k => k % q = b), primeWeight k := by
  rw [classMass, Nat.range_succ_eq_Icc_zero, sum_filter, sum_filter, ← add_sum_Ioc_eq_sum_Icc]
  · simp [primeWeight]
  · exact Nat.zero_le _

/-- Restriction to one class can discard no more prime-power mass than ψ(N) − θ(N). -/
theorem prime_power_correction (N q b : ℕ) :
    |classMass (N + 1) q b - residuePrefix ArithmeticFunction.vonMangoldt N q b| ≤
      Chebyshev.psi N - Chebyshev.theta N := by
  rw [classMass_succ, residuePrefix, residueSlice, abs_sub_comm, ← sum_sub_distrib,
    abs_of_nonneg (sum_nonneg fun k _ => sub_nonneg.mpr (primeWeight_le_mangoldt k))]
  have htotal : (∑ k ∈ Ioc 0 N, (ArithmeticFunction.vonMangoldt k - primeWeight k)) =
      Chebyshev.psi N - Chebyshev.theta N := by
    simp only [sum_sub_distrib, Chebyshev.psi, Chebyshev.theta, Nat.floor_natCast, sum_filter,
      primeWeight]
  rw [← htotal]
  apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
  exact fun k _ _ => sub_nonneg.mpr (primeWeight_le_mangoldt k)

/-- Siegel–Walfisz for the actual logarithmic prime weights, uniformly in reduced residue
classes. The additive terms account for nonprimitive characters and proper prime powers. -/
theorem prime_progression_error (A B : ℝ) (hA : 0 < A) (hB : 0 < B) :
    ∃ M : ℝ, 0 < M ∧ ∃ x₀ : ℝ, 1 < x₀ ∧
      ∀ N q b : ℕ, x₀ ≤ N → 0 < q → (q : ℝ) ≤ (Real.log N) ^ B →
        b < q → b.Coprime q →
        |classMass (N + 1) q b - (N : ℝ) / q.totient| ≤
          M * N * (Real.log N) ^ (-A) + (Nat.log 2 N : ℝ) * Real.log q +
            2 * Real.sqrt N * Real.log N := by
  obtain ⟨M, hM, x₀, hx₀, h⟩ := progression_error A B hA hB
  refine ⟨M, hM, x₀, hx₀, ?_⟩
  intro N q b hN hq hlog hb hcop
  have he := h (N : ℝ) hN q b hq hlog hb hcop
  simp only [Nat.floor_natCast] at he
  have hpow := (prime_power_correction N q b).trans (Chebyshev.psi_sub_theta_le (hx₀.le.trans hN))
  exact (abs_sub_le _ (residuePrefix ArithmeticFunction.vonMangoldt N q b) _).trans
    ((add_le_add hpow he).trans_eq (add_comm _ _))

private theorem classMass_nonunit (N q b : ℕ) (hq : 0 < q) (hb : ¬ b.Coprime q) :
    classMass (N + 1) q b ≤ (Nat.log 2 N : ℝ) * Real.log q := by
  rw [classMass_succ]
  have hs : (Ioc 0 N).filter (fun k => k % q = b) ⊆
      (Ioc 0 N).filter (fun k => ¬ k.Coprime q) := by
    intro k hk
    obtain ⟨hkN, hkb⟩ := mem_filter.mp hk
    refine mem_filter.mpr ⟨hkN, fun h => hb ?_⟩
    rw [← hkb, Nat.coprime_iff_gcd_eq_one, ← Nat.gcd_rec, Nat.gcd_comm]
    exact h.gcd_eq_one
  calc
    _ ≤ ∑ k ∈ (Ioc 0 N).filter (fun k => k % q = b), ArithmeticFunction.vonMangoldt k :=
      sum_le_sum fun k _ => primeWeight_le_mangoldt k
    _ ≤ ∑ k ∈ (Ioc 0 N).filter (fun k => ¬ k.Coprime q), ArithmeticFunction.vonMangoldt k :=
      sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg)
    _ ≤ _ := vonMangoldt_noncoprime_sum_le N hq

/-- A single error budget for every residue, with the initial segment length and the q-dependent
constant exactly as in the expansion of the prime exponential sum. -/
theorem all_class_error (A B : ℝ) (hA : 0 < A) (hB : 0 < B) :
    ∃ M : ℝ, 0 < M ∧ ∃ x₀ : ℝ, 1 < x₀ ∧
      ∀ N q b : ℕ, x₀ ≤ N → 0 < q → (q : ℝ) ≤ (Real.log N) ^ B → b < q →
        |classError (N + 1) q b| ≤
          M * N * (Real.log N) ^ (-A) + (Nat.log 2 N : ℝ) * Real.log q +
            2 * Real.sqrt N * Real.log N + 1 := by
  obtain ⟨M, hM, x₀, hx₀, h⟩ := prime_progression_error A B hA hB
  refine ⟨M, hM, x₀, hx₀, ?_⟩
  intro N q b hN hq hlog hb
  have hN' : (1 : ℝ) ≤ N := hx₀.le.trans hN
  have hL : 0 ≤ Real.log N := Real.log_nonneg hN'
  by_cases hcop : b.Coprime q
  · rw [classError, ite_eq_left hcop]
    have hφ : (1 : ℝ) ≤ q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
    have hlast : |(N : ℝ) / q.totient - ((N + 1 : ℕ) : ℝ) / q.totient| ≤ 1 := by
      rw [show (N : ℝ) / q.totient - ((N + 1 : ℕ) : ℝ) / q.totient = -(1 / (q.totient : ℝ)) by
        push_cast; ring, abs_neg, abs_of_nonneg (by positivity)]
      exact (div_le_one (by linarith)).mpr hφ
    exact (abs_sub_le _ ((N : ℝ) / q.totient) _).trans (add_le_add (h N q b hN hq hlog hb hcop) hlast)
  · rw [classError, ite_eq_right hcop, sub_zero, abs_of_nonneg (by
      unfold classMass
      apply sum_nonneg
      intro k _
      unfold primeWeight
      split_ifs with h
      · exact Real.log_nonneg (by exact_mod_cast h.one_le)
      · exact le_rfl)]
    have hmain : 0 ≤ M * N * (Real.log N) ^ (-A) := by positivity
    have hpower : 0 ≤ 2 * Real.sqrt N * Real.log N := by positivity
    linarith [classMass_nonunit N q b hq hcop]

end

end GoldbachMajorArc

namespace GoldbachMajorArc

open Finset Filter MeasureTheory
open scoped ComplexConjugate

noncomputable section

def kernelMass (n : ℕ) (b : ℝ) : ℝ := ∫ β in -b..b, ‖kernel n β‖ ^ 2

private theorem continuous_kernel (n : ℕ) : Continuous (kernel n) := by
  unfold kernel phase
  fun_prop

theorem kernelMass_mono {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (n : ℕ) :
    kernelMass n u ≤ kernelMass n v :=
  intervalIntegral.integral_mono_interval (neg_le_neg huv) (by linarith) huv
    (Eventually.of_forall fun _ => sq_nonneg _) (((continuous_kernel n).norm.pow 2).intervalIntegrable _ _)

private theorem kernel_on_zero_arc {n : ℕ} (hn : 0 < n) {t : ℝ}
    (ht : t ∈ Set.Icc 0 (1 / (6 * (n : ℝ)))) : (n : ℝ) / 2 ≤ ‖kernel n t‖ := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hnt := (le_div_iff₀ (show 0 < 6 * (n : ℝ) by positivity)).mp ht.2
  have hc (k : ℕ) (hk : k ∈ range (n + 1)) :
      1 / 2 ≤ (phase ((k : ℝ) * t)).re := by
    rw [phase, Complex.exp_ofReal_mul_I_re, ← Real.cos_pi_div_three]
    apply Real.cos_le_cos_of_nonneg_of_le_pi
    · exact mul_nonneg (by positivity) (mul_nonneg (Nat.cast_nonneg _) ht.1)
    · linarith [Real.pi_pos]
    have hk' : (k : ℝ) ≤ n := by exact_mod_cast Nat.lt_succ_iff.mp (mem_range.mp hk)
    have hkt := mul_le_mul_of_nonneg_right hk' ht.1
    nlinarith only [mul_le_mul_of_nonneg_left hnt Real.pi_pos.le,
      mul_le_mul_of_nonneg_left hkt Real.pi_pos.le]
  calc
    _ ≤ ∑ _k ∈ range (n + 1), (1 / 2 : ℝ) := by simp; linarith
    _ ≤ ∑ k ∈ range (n + 1), (phase ((k : ℝ) * t)).re := sum_le_sum hc
    _ = (kernel n t).re := by rw [kernel, Complex.re_sum]
    _ ≤ _ := Complex.re_le_norm _

/-- Each width at least 1/(6n) captures a positive linear amount of the model's mass. -/
theorem kernelMass_floor {n : ℕ} (hn : 0 < n) {b : ℝ} (hb : 1 / (6 * (n : ℝ)) ≤ b) :
    (n : ℝ) / 24 ≤ kernelMass n b := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  let u : ℝ := 1 / (6 * (n : ℝ))
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hb0 : 0 ≤ b := hu.trans hb
  have hc := (continuous_kernel n).norm.pow 2
  calc
    _ = ∫ _t in (0 : ℝ)..u, ((n : ℝ) / 2) ^ 2 := by
      rw [intervalIntegral.integral_const]
      simp only [sub_zero, smul_eq_mul, u]
      field_simp
      ring
    _ ≤ ∫ t in (0 : ℝ)..u, ‖kernel n t‖ ^ 2 :=
      intervalIntegral.integral_mono_on hu (by simp) (hc.intervalIntegrable _ _) fun _ ht =>
        pow_le_pow_left₀ (by positivity) (kernel_on_zero_arc hn ht) 2
    _ ≤ _ := intervalIntegral.integral_mono_interval (neg_nonpos.mpr hb0) hu hb
      (Eventually.of_forall fun _ => sq_nonneg _) (hc.intervalIntegrable _ _)

end
end GoldbachMajorArc

/- The finite CRT and prime-power calculations below adapt goldbach-proofs PRs #207 (XianWu18) and #203 (wzhxzkk), Apache-2.0. -/
namespace GoldbachMajorArc.RamanujanCRT
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

end GoldbachMajorArc.RamanujanCRT
namespace GoldbachMajorArc.RamanujanPower
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

end GoldbachMajorArc.RamanujanPower

namespace GoldbachMajorArc

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

theorem ram_unit (q h : ℕ) (hc : h.Coprime q) : ram q h = ram q 1 := by
  induction q using Nat.recOnPrimeCoprime with
  | zero => simp [ram]
  | prime_pow p j hp =>
    cases j with
    | zero => simp [ram_one]
    | succ k =>
      have hc' := (Nat.coprime_pow_right_iff (Nat.succ_pos k) h p).mp hc
      rw [ram_unit_power hp k h hc', ram_unit_power hp k 1 (by simp)]
  | coprime q r hq hr hqr iq ir =>
    obtain ⟨h₁,h₂⟩ := Nat.coprime_mul_iff_right.mp hc
    rw [ram_mul (by omega) (by omega) hqr, ram_mul (by omega) (by omega) hqr, iq h₁, ir h₂]

theorem unitMean_eq_ram {q a : ℕ} (h : a.Coprime q) :
    unitMean q a = ram q 1 / (q.totient : ℂ) := by
  calc
    _ = ram q a / (q.totient : ℂ) := by
      apply congrArg (fun z : ℂ => z / (q.totient : ℂ))
      apply sum_congr rfl
      intro k _
      exact congrArg phase (by ring)
    _ = _ := congrArg (fun z : ℂ => z / (q.totient : ℂ)) (ram_unit q a h)

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

theorem sum_centers_eq_coefficient (q n : ℕ) :
    (∑ a ∈ (range q).filter (fun a => a.Coprime q),
      (unitMean q a) ^ 2 * phase (-(n : ℝ) * ((a : ℝ) / q))) = coefficient q n := by
  unfold coefficient ram
  rw [map_sum, mul_sum]
  refine sum_congr rfl fun a ha => ?_
  rw [unitMean_eq_ram (mem_filter.mp ha).2]
  congr 1
  unfold phase
  rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
  congr 1
  push_cast
  ring

end
end GoldbachMajorArc

namespace GoldbachMajorArc

open Finset
noncomputable section

def badFactor (p : ℕ) : ℝ := 1 / ((p : ℝ) - 1) ^ 2

private theorem badFactor_nonneg (p : ℕ) : 0 ≤ badFactor p := by unfold badFactor; positivity

private theorem tail_telescope (m : ℕ) :
    ∏ p ∈ range (m + 5), (if 5 ≤ p then 1 + badFactor p else 1) ≤
      4 * ((m : ℝ) + 3) / (3 * ((m : ℝ) + 4)) := by
  induction m with
  | zero =>
    have h : ∏ p ∈ range (0 + 5), (if 5 ≤ p then 1 + badFactor p else 1) = 1 :=
      prod_eq_one fun p hp => ite_eq_right (Nat.not_le.mpr (mem_range.mp hp))
    norm_num [h]
  | succ m ih =>
    rw [show m.succ + 5 = (m + 5) + 1 by omega, prod_range_succ, ite_eq_left (show 5 ≤ m + 5 by omega)]
    apply (mul_le_mul_of_nonneg_right ih (by linarith [badFactor_nonneg (m + 5)])).trans
    unfold badFactor
    push_cast
    have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
    have h₁ : 0 < (m : ℝ) + 4 := by linarith
    have h₂ : 0 < (m : ℝ) + 1 + 4 := by linarith
    rw [show (m : ℝ) + 5 - 1 = m + 4 by ring]
    field_simp
    nlinarith only [hm]

private theorem product_tail_le {s : Finset ℕ} (hs : ∀ p ∈ s, 5 ≤ p) :
    ∏ p ∈ s, (1 + badFactor p) ≤ 4 / 3 := by
  let m := s.sup id
  have hsub : s ⊆ range (m + 5) := by
    intro p hp
    have h : p ≤ m := Finset.le_sup (f := id) hp
    exact mem_range.mpr (by omega)
  calc
    _ = ∏ p ∈ s, (if 5 ≤ p then 1 + badFactor p else 1) :=
      prod_congr rfl fun p hp => (ite_eq_left (hs p hp)).symm
    _ ≤ ∏ p ∈ range (m + 5), (if 5 ≤ p then 1 + badFactor p else 1) := by
      refine prod_le_prod_of_subset_of_one_le₀ hsub ?_ ?_
      · intro i _
        split_ifs <;> linarith [badFactor_nonneg i]
      · intro i _ _
        split_ifs <;> linarith [badFactor_nonneg i]
    _ ≤ _ := tail_telescope m
    _ ≤ 4 / 3 := by
      apply (div_le_div_iff₀ (by positivity) (by norm_num)).mpr
      linarith

/-- Every finite set of odd primes has absolute Euler excess at most 2/3.
Separate p = 3 and telescope the comparison product starting at p = 5. -/
theorem product_bad_factors {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime ∧ 2 < p) :
    ∏ p ∈ s, (1 + badFactor p) ≤ 5 / 3 := by
  have hrest : ∀ p ∈ s.erase 3, 5 ≤ p := by
    intro p hp
    obtain ⟨hne, hmem⟩ := mem_erase.mp hp
    obtain ⟨hprime, hpos⟩ := hs p hmem
    have hfour : p ≠ 4 := by rintro rfl; exact (by decide : ¬ Nat.Prime 4) hprime
    omega
  have hsub : s ⊆ insert 3 (s.erase 3) := by intro p hp; by_cases p = 3 <;> simp_all
  calc
    _ ≤ ∏ p ∈ insert 3 (s.erase 3), (1 + badFactor p) :=
      prod_le_prod_of_subset_of_one_le₀ hsub (fun p _ => by linarith [badFactor_nonneg p])
        (fun p _ _ => by linarith [badFactor_nonneg p])
    _ = (5 / 4) * ∏ p ∈ s.erase 3, (1 + badFactor p) := by
      rw [prod_insert (notMem_erase _ _)]
      congr 1
      norm_num [badFactor]
    _ ≤ (5 / 4) * (4 / 3) := mul_le_mul_of_nonneg_left (product_tail_le hrest) (by norm_num)
    _ = _ := by norm_num

/-- Summing the signed factors at primes away from an even target leaves at least
a third of the mass at d. The function W may already include a denominator cutoff. -/
theorem negative_factors_lower {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime ∧ 2 < p)
    (W : ℕ → ℝ) (hnonneg : ∀ k, 0 ≤ W k) (hmono : ∀ i j, 0 < i → i ≤ j → W j ≤ W i)
    {d : ℕ} (hd : 0 < d) :
    W d / 3 ≤ ∑ t ∈ s.powerset, (∏ p ∈ t, -badFactor p) * W (d * ∏ p ∈ t, p) := by
  let P := s.powerset.erase ∅
  have hempty : ∅ ∈ s.powerset := mem_powerset.mpr (empty_subset _)
  have hrest : (∑ t ∈ P, ∏ p ∈ t, badFactor p) + 1 ≤ 5 / 3 := by
    have h := prod_one_add (f := badFactor) s
    rw [← sum_erase_add _ _ hempty] at h
    simp only [prod_empty] at h
    rw [← h]
    exact product_bad_factors hs
  have hterm (t : Finset ℕ) (ht : t ∈ P) :
      -(W d * ∏ p ∈ t, badFactor p) ≤ (∏ p ∈ t, -badFactor p) * W (d * ∏ p ∈ t, p) := by
    have ht' : t ⊆ s := mem_powerset.mp (mem_erase.mp ht).2
    have hprod : 0 < ∏ p ∈ t, p := prod_pos fun p hp => (hs p (ht' hp)).1.pos
    have hle := hmono d (d * ∏ p ∈ t, p) hd (Nat.le_mul_of_pos_right d hprod)
    apply (abs_le.mp ?_).1
    rw [abs_mul, abs_of_nonneg (hnonneg _), Finset.abs_prod]
    simp_rw [abs_neg, abs_of_nonneg (badFactor_nonneg _)]
    rw [mul_comm (W d)]
    exact mul_le_mul_of_nonneg_left hle (prod_nonneg fun _ _ => badFactor_nonneg _)
  have low := sum_le_sum hterm
  simp only [sum_neg_distrib, ← mul_sum] at low
  have cap := mul_le_mul_of_nonneg_left (show (∑ t ∈ P, ∏ p ∈ t, badFactor p) ≤ 2 / 3 by linarith) (hnonneg d)
  rw [← sum_erase_add _ _ hempty]
  simp only [prod_empty, mul_one, one_mul]
  dsimp only [P] at low cap
  linarith

end
end GoldbachMajorArc

namespace GoldbachMajorArc

open Finset
noncomputable section

private theorem coefficient_not_squarefree {q : ℕ} (n : ℕ) (hq : 0 < q)
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

private theorem coefficient_prime_product (n : ℕ) (s : Finset ℕ)
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

private theorem reindex_denominators (Q n : ℕ) (W : ℕ → ℝ) (hcut : ∀ q, Q < q → W q = 0) :
    (∑ q ∈ Icc 1 Q, (coefficient q n).re * W q) =
    ∑ t ∈ ((range (Q + 1)).filter Nat.Prime).powerset, (∏ p ∈ t, localCoefficient p n) * W (∏ p ∈ t, p) := by
  classical
  let P := (range (Q + 1)).filter Nat.Prime
  have hprime {t : Finset ℕ} (ht : t ∈ P.powerset) : ∀ p ∈ t, p.Prime :=
    fun p hp => (mem_filter.mp (mem_powerset.mp ht hp)).2
  symm
  apply sum_bij_ne_zero (fun t _ _ => ∏ p ∈ t, p)
  · intro t ht hnz
    exact mem_Icc.mpr ⟨prod_pos fun p hp => (hprime ht p hp).pos, le_of_not_gt fun h => hnz (by rw [hcut _ h, mul_zero])⟩
  · intro s hs _ t ht _ he
    exact (Nat.primeFactors_prod (hprime hs)).symm.trans ((congrArg Nat.primeFactors he).trans (Nat.primeFactors_prod (hprime ht)))
  · intro q hq hnz
    have hq' := mem_Icc.mp hq
    have hsq : Squarefree q := by
      by_contra hh
      exact hnz (by rw [coefficient_not_squarefree n hq'.1 hh]; simp)
    have hprod := Nat.prod_primeFactors_of_squarefree hsq
    have hsub : q.primeFactors ∈ P.powerset := by
      apply mem_powerset.mpr
      intro p hp
      exact mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le ((Nat.le_of_mem_primeFactors hp).trans hq'.2)),
        Nat.prime_of_mem_primeFactors hp⟩
    have hc := coefficient_prime_product n q.primeFactors (hprime hsub)
    rw [hprod] at hc
    exact ⟨q.primeFactors, hsub, fun hh => hnz (by rw [hprod] at hh; simpa only [hc, Complex.ofReal_re] using hh), hprod⟩
  · intro t ht _
    rw [coefficient_prime_product n t (hprime ht), Complex.ofReal_re]

private theorem signed_powerset_floor (n : ℕ) (W : ℕ → ℝ) (hnonneg : ∀ k, 0 ≤ W k)
    (hmono : ∀ i j, 0 < i → i ≤ j → W j ≤ W i)
    (B G : Finset ℕ) (hB : ∀ p ∈ B, (p.Prime ∧ 2 < p) ∧ ¬ p ∣ n)
    (hG : ∀ p ∈ G, p.Prime ∧ p ∣ n) (d : ℕ) (hd : 0 < d) :
    W d / 3 ≤ ∑ t ∈ (G ∪ B).powerset,
      (∏ p ∈ t, localCoefficient p n) * W (d * ∏ p ∈ t, p) := by
  classical
  induction G using Finset.induction_on generalizing d with
  | empty =>
    rw [empty_union]
    apply (negative_factors_lower (fun p hp => (hB p hp).1) W hnonneg hmono hd).trans
    apply le_of_eq
    apply sum_congr rfl
    intro t ht
    congr 1
    apply prod_congr rfl
    intro p hp
    simp [localCoefficient, badFactor, (hB p (mem_powerset.mp ht hp)).2]
  | @insert p G hp ih =>
    have hp' := hG p (mem_insert_self _ _)
    have hG' : ∀ r ∈ G, r.Prime ∧ r ∣ n := fun r hr => hG _ (mem_insert_of_mem hr)
    have hpB : p ∉ B := fun h => (hB p h).2 hp'.2
    have hpGB : p ∉ G ∪ B := by simp [hp, hpB]
    have hsign : 0 ≤ localCoefficient p n := by
      have h : (1 : ℝ) < p := by exact_mod_cast hp'.1.one_lt
      simp [localCoefficient, hp'.2, le_of_lt h]
    rw [insert_union, sum_powerset_insert hpGB]
    have hsecond : 0 ≤ ∑ t ∈ (G ∪ B).powerset, (∏ r ∈ insert p t, localCoefficient r n) *
        W (d * ∏ r ∈ insert p t, r) := by
      calc
        0 ≤ localCoefficient p n * (∑ t ∈ (G ∪ B).powerset, (∏ r ∈ t, localCoefficient r n) *
            W (d * p * ∏ r ∈ t, r)) :=
          mul_nonneg hsign ((div_nonneg (hnonneg _) (by norm_num)).trans (ih hG' _ (Nat.mul_pos hd hp'.1.pos)))
        _ = _ := by
          rw [mul_sum]
          apply sum_congr rfl
          intro t ht
          have hpt : p ∉ t := fun h => hpGB (mem_powerset.mp ht h)
          rw [prod_insert hpt, prod_insert hpt, ← mul_assoc d, mul_assoc (localCoefficient p n)]
    linarith [ih hG' d hd]

/-- The even-target arithmetic main term retains at least one third of the q = 1
mass under every nonnegative decreasing weight supported on the denominator cutoff. -/
theorem arithmetic_floor {Q n : ℕ} (hn : Even n) (W : ℕ → ℝ) (hnonneg : ∀ k, 0 ≤ W k)
    (hmono : ∀ i j, 0 < i → i ≤ j → W j ≤ W i) (hcut : ∀ q, Q < q → W q = 0) :
    W 1 / 3 ≤ ∑ q ∈ Icc 1 Q, (coefficient q n).re * W q := by
  classical
  let P := (range (Q+1)).filter Nat.Prime
  let G := P.filter (fun p => p ∣ n)
  let B := P.filter (fun p => ¬ p ∣ n)
  have hGB : G ∪ B = P := by ext p; simp [G, B]; tauto
  have hB (p : ℕ) (hp : p ∈ B) : (p.Prime ∧ 2 < p) ∧ ¬ p ∣ n := by
    have hp' := (mem_filter.mp hp)
    have hpr := (mem_filter.mp hp'.1).2
    have hne : p ≠ 2 := fun e => hp'.2 (e ▸ even_iff_two_dvd.mp hn)
    exact ⟨⟨hpr, lt_of_le_of_ne hpr.two_le (Ne.symm hne)⟩, hp'.2⟩
  have hG (p : ℕ) (hp : p ∈ G) : p.Prime ∧ p ∣ n :=
    ⟨(mem_filter.mp (mem_filter.mp hp).1).2,(mem_filter.mp hp).2⟩
  have h := signed_powerset_floor n W hnonneg hmono B G hB hG 1 zero_lt_one
  rw [hGB] at h
  rw [reindex_denominators Q n W hcut]
  simpa only [one_mul] using h

end
end GoldbachMajorArc


/-! Bounds for the aggregate size of the Ramanujan coefficients of DFQDZZ's PR #316.
The bound is uniform in the frequency, including when the frequency has many prime divisors. -/
namespace GoldbachMajorArc
open Finset
noncomputable section

private def parityFactor (q : ℕ) : ℝ := if Even q then 2 else 1

private lemma parityFactor_coprime {u v : ℕ} (hc : u.Coprime v) :
    parityFactor (u*v) = parityFactor u * parityFactor v := by
  have hboth (hu : Even u) (hv : Even v) : False := by
    have hd := Nat.dvd_gcd (even_iff_two_dvd.mp hu) (even_iff_two_dvd.mp hv)
    rw [hc.gcd_eq_one] at hd; omega
  by_cases hu : Even u
  · have hv : ¬ Even v := hboth hu
    simp [parityFactor, hu, hv]
  · by_cases hv : Even v <;> simp [parityFactor, Nat.even_mul, hu, hv]

private lemma coeffPrime_size (n p : ℕ) (hp : p.Prime) :
    (p : ℝ) * ‖coefficient p n‖^2 ≤ parityFactor p := by
  have hp2 : 2 ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hp0 : 0 < (p : ℝ) - 1 := by linarith
  have h1 : ‖coefficient p n‖ ≤ 1 / ((p : ℝ) - 1) := by
    rw [coefficient_prime hp, Complex.norm_real, Real.norm_eq_abs]
    unfold localCoefficient
    split_ifs with hd
    · rw [abs_of_nonneg (by positivity)]
    · rw [abs_neg, abs_of_nonneg (by positivity)]
      apply one_div_le_one_div_of_le hp0; nlinarith
  have h2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) h1 2) (Nat.cast_nonneg p)
  apply h2.trans
  by_cases htwo : p = 2
  · subst p; norm_num [parityFactor]
  have hp3 : 3 ≤ (p : ℝ) := by exact_mod_cast (show 3 ≤ p by have := hp.two_le; omega)
  have hodd : ¬Even p := Nat.not_even_iff_odd.mpr (hp.odd_of_ne_two htwo)
  rw [parityFactor, ite_eq_right hodd, div_pow, one_pow, ← mul_div_assoc, mul_one]
  apply (div_le_iff₀ (by positivity)).mpr; nlinarith [sq_nonneg ((p : ℝ)-3)]

/-- Even squarefree moduli can lose a factor of two at the prime 2. -/
theorem coefficient_frequency_energy (q n : ℕ) : (q : ℝ) * ‖coefficient q n‖^2 ≤ parityFactor q := by
  induction q using Nat.recOnPosPrimePosCoprime with
  | zero => simp [parityFactor]
  | one => simp [coefficient_one, parityFactor]
  | prime_pow p k hp hk =>
    cases k with
    | zero => omega
    | succ k =>
      cases k with
      | zero => simpa using coeffPrime_size n p hp
      | succ j => simp only [show j+1+1 = j+2 by omega, coefficient_higher_power hp, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero]; unfold parityFactor; split <;> norm_num
  | coprime u v hu hv huv iu iv =>
    rw [coefficient_mul (by omega) (by omega) huv, Nat.cast_mul, norm_mul, mul_pow, parityFactor_coprime huv]
    calc _ = ((u:ℝ) * ‖coefficient u n‖^2) * ((v:ℝ) * ‖coefficient v n‖^2) := by ring
         _ ≤ parityFactor u * parityFactor v := mul_le_mul iu iv (by positivity) (by unfold parityFactor; split <;> norm_num)

/-- Summing the absolute coefficient values costs only a square root of the cutoff. -/
theorem sum_norm_coefficient_le_sqrt (Q n : ℕ) :
    ∑ q ∈ Finset.Icc 1 Q, ‖coefficient q n‖ ≤ 4 * Real.sqrt Q := by
  have hs (q : ℕ) : ‖coefficient (q+1) n‖ ≤
      4 * (Real.sqrt (q+1 : ℕ) - Real.sqrt q) := by
    let X := Real.sqrt (q+1 : ℕ)
    let Y := Real.sqrt q
    have hX : 0 < X := Real.sqrt_pos.mpr (by positivity)
    have hY : 0 ≤ Y := Real.sqrt_nonneg _
    have hXY : Y ≤ X := Real.sqrt_le_sqrt (by exact_mod_cast (Nat.le_succ q))
    have hX2 : X^2 = (q : ℝ) + 1 := by dsimp only [X]; push_cast; exact Real.sq_sqrt (by positivity)
    have hY2 : Y^2 = (q : ℝ) := Real.sq_sqrt (by positivity)
    have hh : (q+1 : ℝ) * ‖coefficient (q+1) n‖^2 ≤ 2 := by
      exact_mod_cast (coefficient_frequency_energy (q+1) n).trans (show parityFactor (q+1) ≤ 2 by unfold parityFactor; split <;> norm_num)
    have hb : ‖coefficient (q+1) n‖ * X ≤ 2 := by
      have : (‖coefficient (q+1) n‖ * X)^2 ≤ 2 := by rw [mul_pow, hX2, mul_comm]; exact hh
      nlinarith
    have hprod : (X-Y)*(X+Y) = 1 := by nlinarith [hX2,hY2]
    apply (le_of_mul_le_mul_right (a := X+Y) _ (by linarith : 0 < X+Y))
    change ‖coefficient (q+1) n‖ * (X+Y) ≤ 4 * (X-Y)*(X+Y)
    nlinarith [mul_le_mul_of_nonneg_left hXY (norm_nonneg (coefficient (q+1) n))]
  induction Q with
  | zero => simp
  | succ Q ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ Q+1)]
    linarith [hs Q]

end
end GoldbachMajorArc

/-! A change-of-frequency bound for the major-arc Dirichlet kernel. The centered-square
identity uses the reflection argument from DFQDZZ, goldbach-proofs PR #316 (Apache 2.0), and the
mode integral uses the argument from TranswarpDrive's PR #158. Taking the difference of
the two exact Fourier coefficients bounds the loss on any subinterval of one period. -/
namespace GoldbachEstermannKernel
noncomputable section
open Finset MeasureTheory
open scoped ComplexConjugate

def phase (x : ℝ) : ℂ := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)
def kernel (M : ℕ) (t : ℝ) := ∑ k ∈ range (M + 1), phase ((k : ℝ) * t)
def twisted (M n : ℕ) (t : ℝ) := kernel M t ^ 2 * phase (-(n : ℝ) * t)

private lemma phase_add (x y : ℝ) : phase (x + y) = phase x * phase y := by
  unfold phase; rw [← Complex.exp_add]; congr 1; push_cast; ring

private lemma norm_phase (x : ℝ) : ‖phase x‖ = 1 := Complex.norm_exp_ofReal_mul_I _

private lemma phase_int (j : ℤ) : phase (j : ℝ) = 1 := by
  unfold phase
  convert Complex.exp_int_mul_two_pi_mul_I j using 2
  push_cast; ring

private lemma centered_mode (j : ℤ) :
    (∫ t in (-(1/2) : ℝ)..1/2, phase ((j : ℝ) * t)) = if j = 0 then 1 else 0 := by
  have hp : Function.Periodic (fun t : ℝ => phase ((j : ℝ) * t)) 1 := by
    intro t; simp only [mul_add, mul_one, phase_add, phase_int, mul_one]
  have hshift := hp.intervalIntegral_add_eq (-(1/2)) 0
  norm_num only [show (-(1/2) : ℝ) + 1 = 1/2 by norm_num, zero_add] at hshift
  rw [hshift]
  by_cases hj : j = 0
  · subst j; simp [phase]
  let c : ℂ := (j : ℂ) * (2 * Real.pi * Complex.I)
  have he (t : ℝ) : phase ((j : ℝ) * t) = Complex.exp (c * (t : ℂ)) := by
    unfold phase c; congr 1; push_cast; ring
  have hc : c ≠ 0 := mul_ne_zero (by exact_mod_cast hj)
    (mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero)
  simp_rw [he]; rw [integral_exp_mul_complex hc]; simp [hj, c, Complex.exp_int_mul_two_pi_mul_I]

/-- The coefficient of the square of a length M+1 kernel at every n up to M. -/
theorem full_coefficient (M n : ℕ) (hn : n ≤ M) :
    (∫ t in (-(1/2) : ℝ)..1/2, twisted M n t) = (n : ℂ) + 1 := by
  let I := range (M+1)
  let f (k j : ℕ) (t : ℝ) := phase (((k : ℤ) + (j : ℤ) - n : ℤ) * (t : ℝ))
  have hcont (k j : ℕ) : Continuous (f k j) := by dsimp [f, phase]; fun_prop
  have hex (t : ℝ) : twisted M n t = ∑ k ∈ I, ∑ j ∈ I, f k j t := by
    dsimp [twisted, kernel, I]
    simp only [sq, Finset.sum_mul, Finset.mul_sum]
    refine sum_congr rfl fun k _ => sum_congr rfl fun j _ => ?_
    dsimp [f]; push_cast; rw [← phase_add, ← phase_add]; congr 1; ring
  have hrow (k : ℕ) : (∫ t in (-(1/2) : ℝ)..1/2, ∑ j ∈ I, f k j t) = if k ≤ n then 1 else 0 := by
    rw [intervalIntegral.integral_finsetSum (fun j _ => (hcont k j).intervalIntegrable _ _)]
    simp only [f, centered_mode]
    by_cases hk : k ≤ n
    · rw [ite_eq_left hk, sum_eq_single_of_mem (n-k) (show n-k ∈ I by apply mem_range.mpr; omega)]
      · simp [show (k : ℤ) + ↑(n-k) - ↑n = 0 by omega]
      · intro j _ hdiff; simp [show (k : ℤ) + ↑j - ↑n ≠ 0 by omega]
    · rw [ite_eq_right hk]; apply sum_eq_zero; intro j _; simp [show (k : ℤ) + ↑j - ↑n ≠ 0 by omega]
  simp_rw [hex]
  rw [intervalIntegral.integral_finsetSum (fun k _ => (continuous_finsetSum I fun j _ => hcont k j).intervalIntegrable _ _)]
  simp_rw [hrow]
  rw [← Finset.sum_filter]
  have hset : I.filter (fun k => k ≤ n) = range (n+1) := by ext k; simp [I]; omega
  simp [hset]

private lemma centered (M : ℕ) (t : ℝ) : twisted M M t = ((‖kernel M t‖^2 : ℝ) : ℂ) := by
  have hc (x : ℝ) : conj (phase x) = phase (-x) := by
    unfold phase; rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
    congr 1; push_cast; ring
  have hsym : kernel M t * phase (-(M : ℝ) * t) = conj (kernel M t) := by
    unfold kernel; rw [sum_mul, map_sum]
    calc
      _ = ∑ k ∈ range (M+1), conj (phase (((M-k : ℕ) : ℝ)*t)) := by
        apply sum_congr rfl
        intro k hk
        rw [hc, ← phase_add, Nat.cast_sub (Nat.lt_succ_iff.mp (mem_range.mp hk))]; congr 1; ring
      _ = _ := by simpa only [Nat.add_sub_cancel] using
                    (Finset.sum_range_reflect (fun k => conj (phase ((k : ℝ)*t))) (M+1))
  calc
    _ = kernel M t * (kernel M t * phase (-(M : ℝ) * t)) := by dsimp [twisted]; ring
    _ = _ := by rw [hsym, Complex.mul_conj, Complex.normSq_eq_norm_sq]

private lemma cont (M n : ℕ) : Continuous (twisted M n) := by unfold twisted kernel phase; fun_prop

set_option maxHeartbeats 1200000 in
/-- On any subinterval of the centered period, changing the target M to n costs at most M−n. -/
theorem loss_on_interval (M n : ℕ) (hn : n ≤ M) {a b : ℝ} (ha : -(1/2) ≤ a)
    (hab : a ≤ b) (hb : b ≤ 1/2) :
    0 ≤ (∫ t in a..b, ‖kernel M t‖ ^ 2) - (∫ t in a..b, (twisted M n t).re) ∧
      (∫ t in a..b, ‖kernel M t‖ ^ 2) - (∫ t in a..b, (twisted M n t).re) ≤ (M : ℝ) - n := by
  let loss (t : ℝ) := (twisted M M t).re - (twisted M n t).re
  have hnn (t : ℝ) : 0 ≤ loss t := by
    dsimp only [loss]; rw [centered, Complex.ofReal_re]; apply sub_nonneg.mpr
    apply (Complex.re_le_norm _).trans_eq
    simp [twisted, norm_pow, norm_phase]
  have hreal (j : ℕ) : Continuous (fun t => (twisted M j t).re) := Complex.continuous_re.comp (cont M j)
  have hcont : Continuous loss := (hreal M).sub (hreal n)
  have hex (c d : ℝ) : (∫ t in c..d, loss t) =
      (∫ t in c..d, (twisted M M t).re) - (∫ t in c..d, (twisted M n t).re) :=
    intervalIntegral.integral_sub ((hreal M).intervalIntegrable c d) ((hreal n).intervalIntegrable c d)
  have hre (j : ℕ) : (∫ t in (-(1/2) : ℝ)..1/2, (twisted M j t).re) =
      (∫ t in (-(1/2) : ℝ)..1/2, twisted M j t).re :=
    intervalIntegral.intervalIntegral_re (𝕜 := ℂ) ((cont M j).intervalIntegrable _ _)
  have hwhole : (∫ t in (-(1/2) : ℝ)..1/2, loss t) = (M : ℝ) - n := by
    rw [hex, hre, hre, full_coefficient M M le_rfl, full_coefficient M n hn]; simp
  have hlocal := hex a b
  simp only [centered, Complex.ofReal_re] at hlocal
  rw [← hlocal]
  exact ⟨intervalIntegral.integral_nonneg hab (fun t _ => hnn t),
    (intervalIntegral.integral_mono_interval ha hab hb (Filter.Eventually.of_forall hnn)
      (hcont.intervalIntegrable ..)).trans_eq hwhole⟩

end
end GoldbachEstermannKernel

namespace GoldbachMajorArc
noncomputable section
open Finset MeasureTheory

/-- Common rational arc radii for a block of frequencies near M. -/
def blockWidth (M Q q : ℕ) : ℝ := (Q : ℝ) / ((q : ℝ) * M)

def blockModel (M Q n : ℕ) : ℝ :=
  ∑ q ∈ Icc 1 Q, (coefficient q n).re *
    ∫ t in -(blockWidth M Q q)..blockWidth M Q q, (GoldbachEstermannKernel.twisted M n t).re

/-- The spectrum length, cutoff and arc widths are uniform in the target n. -/
theorem block_model_floor (M Q n : ℕ) (hM : 0 < M) (hQ : 1 ≤ Q)
    (hdis : 2*Q ≤ M) (hn : n ≤ M) (heven : Even n) :
    (M : ℝ) / 72 - 4 * Real.sqrt Q * ((M : ℝ) - n) ≤ blockModel M Q n := by
  let W (q : ℕ) := if q ≤ Q then kernelMass M (blockWidth M Q q) else 0
  have hMr : 0 < (M : ℝ) := by exact_mod_cast hM
  have hQr : 1 ≤ (Q : ℝ) := by exact_mod_cast hQ
  have hwr (q : ℕ) : 0 ≤ blockWidth M Q q := by unfold blockWidth; positivity
  have hn' : 0 ≤ (M : ℝ) - n := sub_nonneg.mpr (by exact_mod_cast hn)
  have hnon (q : ℕ) : 0 ≤ W q := by
    dsimp only [W]; split_ifs
    · apply intervalIntegral.integral_nonneg (by linarith [hwr q]); intro t _; exact sq_nonneg _
    · rfl
  have hmono (i j : ℕ) (hi : 0 < i) (hij : i ≤ j) : W j ≤ W i := by
    by_cases hj : j ≤ Q
    · simp only [W, ite_eq_left hj, ite_eq_left (hij.trans hj)]
      apply kernelMass_mono (hwr j)
      apply div_le_div_of_nonneg_left (Nat.cast_nonneg _) (mul_pos (by exact_mod_cast hi) hMr)
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hij) hMr.le
    · simp only [W, ite_eq_right hj]; exact hnon i
  have hsum := arithmetic_floor (Q := Q) heven W hnon hmono (by intro q hq; simp [W, not_le.mpr hq])
  have h1 : 1 / (6*(M : ℝ)) ≤ blockWidth M Q 1 := by
    unfold blockWidth; simp only [Nat.cast_one, one_mul]
    rw [div_le_div_iff₀ (by positivity) hMr]; nlinarith [mul_le_mul_of_nonneg_right hQr hMr.le]
  have hmodel : (M : ℝ) / 72 ≤ ∑ q ∈ Icc 1 Q, (coefficient q n).re * W q := by
    rw [show W 1 = kernelMass M (blockWidth M Q 1) by simp [W, hQ]] at hsum
    linarith [kernelMass_floor hM h1]
  have hdiff (q : ℕ) (hq : q ∈ Icc 1 Q) :
      (coefficient q n).re * W q - (coefficient q n).re *
        (∫ t in -(blockWidth M Q q)..blockWidth M Q q, (GoldbachEstermannKernel.twisted M n t).re) ≤
      ‖coefficient q n‖ * ((M : ℝ) - n) := by
    have hle : blockWidth M Q q ≤ 1/2 := by
      have hq' : (1 : ℝ) ≤ q := by exact_mod_cast (mem_Icc.mp hq).1
      have hdis' : 2 * (Q : ℝ) ≤ M := by exact_mod_cast hdis
      unfold blockWidth
      apply (div_le_iff₀ (mul_pos (by linarith) hMr)).mpr
      nlinarith [mul_le_mul_of_nonneg_right hq' hMr.le]
    obtain ⟨hpos,hloss⟩ := GoldbachEstermannKernel.loss_on_interval M n hn
      (neg_le_neg hle) (by linarith [hwr q] : -(blockWidth M Q q) ≤ blockWidth M Q q) hle
    rw [← mul_sub, show W q = kernelMass M (blockWidth M Q q) by simp [W, (mem_Icc.mp hq).2]]
    exact mul_le_mul (Complex.re_le_norm _) hloss hpos (norm_nonneg _)
  have htot := Finset.sum_le_sum hdiff
  rw [sum_sub_distrib, ← sum_mul] at htot
  have hcoef := mul_le_mul_of_nonneg_right (sum_norm_coefficient_le_sqrt Q n) hn'
  unfold blockModel
  linarith

theorem coefficient_im_zero {q : ℕ} (n : ℕ) (hq : 0 < q) : (coefficient q n).im = 0 := by
  induction q using Nat.recOnPosPrimePosCoprime with
  | zero => omega
  | one => simp [coefficient_one]
  | prime_pow p k hp hk =>
    cases k with
    | zero => omega
    | succ k =>
      cases k with
      | zero => simp [coefficient_prime hp]
      | succ j => rw [coefficient_higher_power hp]; rfl
  | coprime u v hu hv huv iu iv =>
    simp [coefficient_mul (by omega : 0 < u) (by omega : 0 < v) huv,
      Complex.mul_im, iu (by omega), iv (by omega)]

/-- Reassemble the unscaled complex coefficient and pass real parts through its integral. -/
theorem block_model_complex_re (M Q n : ℕ) :
    (∑ q ∈ Icc 1 Q, coefficient q n *
      ∫ t in -(blockWidth M Q q)..blockWidth M Q q, GoldbachEstermannKernel.twisted M n t).re =
    blockModel M Q n := by
  rw [Complex.re_sum]
  unfold blockModel
  apply sum_congr rfl
  intro q hq
  have hc : Continuous (GoldbachEstermannKernel.twisted M n) := by
    unfold GoldbachEstermannKernel.twisted GoldbachEstermannKernel.kernel GoldbachEstermannKernel.phase
    fun_prop
  rw [Complex.mul_re, coefficient_im_zero n (by have := (mem_Icc.mp hq).1; omega),
    zero_mul, sub_zero]
  exact congrArg ((coefficient q n).re * ·)
    (intervalIntegral.intervalIntegral_re (𝕜 := ℂ) (hc.intervalIntegrable _ _)).symm

end
end GoldbachMajorArc



/-!
Uniform square-model errors on full major arcs for any fixed logarithmic exponent.
The starting finite inequalities and Siegel--Walfisz application are from DFQDZZ's
goldbach-proofs PR #316 at e4ab24712555ae8c2c926adf19d368a9fb392c35 (Apache-2.0).
Its Siegel--Walfisz proof is adapted from OpenAI/math, as recorded in the attribution above.
The arbitrary cutoff exponent, arbitrary target twist and log-power savings below
are the new generalizations.
-/
namespace GoldbachMajorArc.Polylog
open Finset Filter MeasureTheory
open scoped Topology
noncomputable section

def cutoff (B n : ℕ) : ℕ := (Nat.log 2 (n + 2)) ^ B

private theorem nat_log_two_le {u : ℕ} (hu : 1 ≤ u) :
    (Nat.log 2 u : ℝ) ≤ 2 * Real.log u := by
  have hL : 0 ≤ Real.log u := Real.log_nonneg (by exact_mod_cast hu)
  have h₂ := Real.log_two_gt_d9
  have h := Real.natLog_le_logb u 2
  simp only [Nat.cast_ofNat, Real.logb] at h
  refine h.trans ((div_le_iff₀ (by linarith : 0 < Real.log 2)).mpr ?_)
  nlinarith only [mul_nonneg hL (show 0 ≤ 2 * Real.log 2 - 1 by linarith)]
theorem cutoff_le_log (B : ℕ) {n : ℕ} (hn : 2 ≤ n) :
    (cutoff B n : ℝ) ≤ (4 * Real.log n) ^ B := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : 0 < (n : ℝ) := by linarith
  have harg : (n : ℝ) + 2 ≤ (n : ℝ) ^ 2 := by nlinarith
  have hl := Real.log_le_log (by positivity : 0 < (n : ℝ) + 2) harg
  rw [Real.log_pow] at hl
  norm_num1 at hl
  have hnat := nat_log_two_le (u := n + 2) (by omega)
  push_cast at hnat
  have h : (Nat.log 2 (n + 2) : ℝ) ≤ 4 * Real.log n := by linarith
  simpa only [cutoff, Nat.cast_pow] using
    pow_le_pow_left₀ (Nat.cast_nonneg (Nat.log 2 (n + 2)) (α := ℝ)) h B

private theorem class_error_trivial (u q b : ℕ) (hq : 0 < q) :
    |classError (u + 1) q b| ≤ (Real.log 4 + 1) * ((u : ℝ) + 1) := by
  have hw (k : ℕ) : 0 ≤ primeWeight k := by
    unfold primeWeight
    split_ifs with h
    · exact Real.log_nonneg (by exact_mod_cast h.one_le)
    · exact le_rfl
  have hmass : classMass (u + 1) q b ≤ Real.log 4 * u := by
    unfold classMass
    calc
      _ ≤ ∑ k ∈ range (u + 1), primeWeight k :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun k _ _ => hw k)
      _ = Chebyshev.theta u := by
        rw [Chebyshev.theta_eq_sum_primesLE_log, Nat.primesLE_eq_filter_range, sum_filter]; rfl
      _ ≤ _ := Chebyshev.theta_le_log4_mul_x (by positivity)
  have hφ : (1 : ℝ) ≤ q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  have hfrac : ((u + 1 : ℕ) : ℝ) / q.totient ≤ (u : ℝ) + 1 := by
    push_cast
    exact div_le_self (by positivity) hφ
  push_cast at hfrac
  have hm : 0 ≤ classMass (u + 1) q b := sum_nonneg (fun k _ => hw k)
  have hlog : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  unfold classError
  split_ifs
  · apply abs_le.mpr
    constructor <;> push_cast <;> nlinarith [show 0 ≤ ((u : ℝ) + 1) / q.totient by positivity,
      mul_nonneg hlog (Nat.cast_nonneg (α := ℝ) u)]
  · rw [sub_zero, abs_of_nonneg hm]
    linarith [Nat.cast_nonneg (α := ℝ) u]

def errorEnvelope (B K : ℕ) (M : ℝ) (n : ℕ) : ℝ :=
  M * 2 ^ (K+1) * n / (Real.log n) ^ (K+1) + (2 * 4 ^ B) * (Real.log n) ^ (B+1) +
    2 * Real.sqrt n * Real.log n + 1 + (Real.log 4 + 1) * (Real.sqrt n + 1)

theorem uniform_prefix_error (B K : ℕ) (hB : 0 < B) :
    ∃ M : ℝ, 0 < M ∧ ∀ᶠ n : ℕ in atTop, ∀ q a : ℕ, 0 < q → q ≤ cutoff B n →
      prefixError n ((a : ℝ) / q) (unitMean q a) ≤ q * errorEnvelope B K M n := by
  obtain ⟨M, hM, x₀, hx₀, hAP⟩ := all_class_error ((K+1 : ℕ) : ℝ) ((2*B : ℕ) : ℝ) (by positivity) (by positivity)
  refine ⟨M, hM, ?_⟩
  have hlim := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hroot := Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop (2 : ℕ), hlim.eventually_ge_atTop 16,
    hroot.eventually_ge_atTop x₀] with n hn hL hrootN
  change (16 : ℝ) ≤ Real.log n at hL
  change x₀ ≤ Real.sqrt n at hrootN
  intro q a hq hQ
  have hnL : 0 < Real.log n := by linarith
  have hQ' : (q : ℝ) ≤ (4 * Real.log n) ^ B :=
    (show (q : ℝ) ≤ cutoff B n by exact_mod_cast hQ).trans (cutoff_le_log B hn)
  have hconst : 0 < Real.log 4 + 1 := by positivity
  have henv : 0 ≤ errorEnvelope B K M n := by unfold errorEnvelope; positivity
  unfold prefixError
  apply Finset.sup'_le
  intro m hm
  refine (center_prefix_bound hq a m).trans ?_
  calc
    _ ≤ ∑ _b ∈ range q, errorEnvelope B K M n := by
      apply sum_le_sum
      intro b hb
      cases m with
      | zero => simpa [classError, classMass] using henv
      | succ u =>
        have hun : u ≤ n := by have := mem_range.mp hm; omega
        have hun' : (u : ℝ) ≤ n := by exact_mod_cast hun
        by_cases hs : (u : ℝ) < Real.sqrt n
        · refine (class_error_trivial u q b hq).trans ?_
          have hsmall := mul_le_mul_of_nonneg_left (add_le_add hs.le (le_refl (1 : ℝ))) hconst.le
          unfold errorEnvelope
          linarith [show 0 ≤ M * 2 ^ (K+1) * n / (Real.log n) ^ (K+1) by positivity,
            show 0 ≤ (2 * 4 ^ B) * (Real.log n) ^ (B+1) by positivity, show 0 ≤ 2 * Real.sqrt n * Real.log n by positivity]
        · have hsu := le_of_not_gt hs
          have hux : x₀ ≤ (u : ℝ) := hrootN.trans hsu
          have hu1 : (1 : ℝ) < u := hx₀.trans_le hux
          have huL := Real.log_pos hu1
          have hhalf := Real.log_le_log (by linarith : 0 < Real.sqrt n) hsu
          rw [Real.log_sqrt (Nat.cast_nonneg n)] at hhalf
          have hupper := Real.log_le_log (by linarith : 0 < (u : ℝ)) hun'
          have hu8 : 8 ≤ Real.log u := by linarith
          have hbase : 4 * Real.log n ≤ (Real.log u) ^ 2 := by
            nlinarith only [hhalf, hu8, mul_nonneg huL.le (sub_nonneg.mpr hu8)]
          have hmod : (q : ℝ) ≤ (Real.log u) ^ (2*B : ℕ) := by
            rw [pow_mul]
            exact hQ'.trans (pow_le_pow_left₀ (by positivity) hbase B)
          have hraw := hAP u q b hux hq (by simpa only [Real.rpow_natCast] using hmod) (mem_range.mp hb)
          have hrpow : (Real.log u) ^ (-((K+1 : ℕ) : ℝ)) = 1 / (Real.log u) ^ (K+1) := by
            rw [Real.rpow_neg huL.le, Real.rpow_natCast, one_div]
          rw [hrpow, ← div_eq_mul_one_div] at hraw
          have hpow := pow_le_pow_left₀ hnL.le (show Real.log n ≤ 2 * Real.log u by linarith) (K+1)
          rw [mul_pow] at hpow
          have hmain : M * (u : ℝ) / (Real.log u) ^ (K+1) ≤ M * 2 ^ (K+1) * n / (Real.log n) ^ (K+1) := by
            apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
            calc
              _ ≤ (M * n) * (2 ^ (K+1) * (Real.log u) ^ (K+1)) :=
                mul_le_mul (mul_le_mul_of_nonneg_left hun' hM.le) hpow (by positivity) (by positivity)
              _ = _ := by ring
          have hNat := (nat_log_two_le (u := u) (by exact_mod_cast hu1.le)).trans
            (mul_le_mul_of_nonneg_left hupper (by norm_num : (0 : ℝ) ≤ 2))
          have hlogq : Real.log q ≤ (4 * Real.log n) ^ B :=
            (Real.log_le_self (Nat.cast_nonneg q)).trans hQ'
          have hlogq0 : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
          have herr := mul_le_mul hNat hlogq hlogq0 (by positivity)
          have hsqrt := mul_le_mul (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hun') (by norm_num : (0 : ℝ) ≤ 2))
            hupper huL.le (by positivity)
          have herr' : (Nat.log 2 u : ℝ) * Real.log q ≤ (2 * 4 ^ B) * (Real.log n) ^ (B+1) := by
            refine herr.trans_eq ?_
            rw [mul_pow, pow_succ]
            ring
          unfold errorEnvelope
          linarith only [hraw, hmain, herr', hsqrt,
            mul_nonneg hconst.le (show 0 ≤ Real.sqrt n + 1 by positivity)]
    _ = _ := by simp

private theorem log_power_over_power (k : ℕ) {s : ℝ} (hs : 0 < s) :
    Tendsto (fun n : ℕ => (Real.log n) ^ k / (n : ℝ) ^ s) atTop (𝓝 0) := by
  simpa only [Function.comp_def, Real.rpow_natCast] using
    ((isLittleO_log_rpow_rpow_atTop (k : ℝ) hs).tendsto_div_nhds_zero.comp
      (tendsto_natCast_atTop_atTop (R := ℝ)))

theorem envelope_saving (B K : ℕ) (M : ℝ) :
    Tendsto (fun n : ℕ => (Real.log n) ^ K * errorEnvelope B K M n / n) atTop (𝓝 0) := by
  have hlog := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hmain : Tendsto (fun n : ℕ => M * 2 ^ (K+1) / Real.log n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlog
  have hself (k : ℕ) : Tendsto (fun n : ℕ => (Real.log n) ^ k / (n : ℝ)) atTop (𝓝 0) := by
    simpa only [Real.rpow_one] using log_power_over_power k (show (0:ℝ) < 1 by norm_num)
  have hsqrt (k : ℕ) : Tendsto (fun n : ℕ => (Real.log n) ^ k / Real.sqrt n) atTop (𝓝 0) := by
    simpa only [Real.sqrt_eq_rpow] using log_power_over_power k (show (0:ℝ) < 1 / 2 by norm_num)

  have hsum := (((hmain.add ((hself (K+(B+1))).const_mul (2 * 4 ^ B))).add
    ((hsqrt (K+1)).const_mul 2)).add (hself K)).add
    (((hsqrt K).add (hself K)).const_mul (Real.log 4 + 1))
  simp only [mul_zero, add_zero] at hsum
  apply hsum.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
  have hn' : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hL := (Real.log_pos hn').ne'
  have hv := (Real.sqrt_pos.mpr (zero_lt_one.trans hn')).ne'
  have alg (L v : ℝ) (hL : L ≠ 0) (hv : v ≠ 0) :
      M * 2 ^ (K+1) / L + (2 * 4 ^ B) * (L ^ (K+(B+1)) / v ^ 2) +
        2 * (L ^ (K+1) / v) + L ^ K / v ^ 2 + (Real.log 4 + 1) * (L ^ K / v + L ^ K / v ^ 2) =
      L ^ K * (M * 2 ^ (K+1) * v ^ 2 / L ^ (K+1) + (2 * 4 ^ B) * L ^ (B+1) +
        2 * v * L + 1 + (Real.log 4 + 1) * (v + 1)) / v ^ 2 := by
    simp only [pow_add, pow_one]
    field_simp
  have h := alg (Real.log n) (Real.sqrt n) hL hv
  rw [Real.sq_sqrt (Nat.cast_nonneg n)] at h
  simpa [errorEnvelope] using h

end
end GoldbachMajorArc.Polylog

namespace GoldbachMajorArc.Polylog
open Finset Filter MeasureTheory
open scoped Topology
noncomputable section

def width (Q n q : ℕ) : ℝ := (Q : ℝ) / ((q : ℝ) * n)

/-- Absolute square-model error at frequency m, centered at a/q. -/
def modelError (n q a : ℕ) (m β : ℝ) : ℝ :=
  let t := (a : ℝ) / q + β
  ‖(primeSum n t)^2 * phase (-m*t) - (unitMean q a * kernel n β)^2 * phase (-m*t)‖

theorem modelError_eq (n q a : ℕ) (m β : ℝ) :
    modelError n q a m β =
      ‖(primeSum n ((a : ℝ) / q + β))^2 - (unitMean q a * kernel n β)^2‖ := by
  unfold modelError
  dsimp only
  rw [← sub_mul, norm_mul, show ∀ x, ‖phase x‖ = 1 from fun _ => Complex.norm_exp_ofReal_mul_I _, mul_one]

def totalArcError (Q n : ℕ) (m : ℝ) : ℝ :=
  ∑ q ∈ Icc 1 Q, ∑ a ∈ range (q + 1),
    ∫ β in -(width Q n q)..(width Q n q), modelError n q a m β

theorem totalArcError_frequency_independent (Q n : ℕ) (m m' : ℝ) :
    totalArcError Q n m = totalArcError Q n m' := by
  simp only [totalArcError, modelError_eq]
private theorem primeWeight_nonneg (k : ℕ) : 0 ≤ primeWeight k := by
  unfold primeWeight
  split_ifs with h
  · exact Real.log_nonneg (by exact_mod_cast h.one_le)
  · exact le_rfl

private theorem sum_primeWeight (n : ℕ) :
    ∑ k ∈ range (n + 1), primeWeight k = Chebyshev.theta n := by
  rw [Chebyshev.theta_eq_sum_primesLE_log, Nat.primesLE_eq_filter_range, sum_filter]
  rfl
private theorem prefix_le {m n : ℕ} (hm : m ≤ n + 1) (r : ℝ) (A : ℂ) :
    ‖∑ k ∈ range m, centerErrorTerm r A k‖ ≤ prefixError n r A :=
  Finset.le_sup' (fun m => ‖∑ k ∈ range m, centerErrorTerm r A k‖) (mem_range.mpr (by omega))

private theorem norm_phase (x : ℝ) : ‖phase x‖ = 1 := Complex.norm_exp_ofReal_mul_I _
theorem rational_arc_error {Q n q a : ℕ} (hn : 0 < n) (hq : 0 < q) {β : ℝ}
    (hβ : |β| ≤ (Q : ℝ) / ((q : ℝ) * n)) :
    ‖primeSum n ((a : ℝ) / q + β) - unitMean q a * kernel n β‖ ≤
      prefixError n ((a : ℝ) / q) (unitMean q a) * (1 + 2 * Real.pi * ((Q : ℝ) / q)) := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hq' : 0 < (q : ℝ) := by exact_mod_cast hq
  have hscale : (n : ℝ) * |β| ≤ (Q : ℝ) / q := by
    apply (le_div_iff₀ hq').mpr
    calc
      _ = |β| * ((q : ℝ) * n) := by ring
      _ ≤ _ := (le_div_iff₀ (mul_pos hq' hn')).mp hβ
  have hD : 0 ≤ prefixError n ((a : ℝ) / q) (unitMean q a) :=
    (norm_nonneg _).trans (prefix_le (m := 0) (n := n) (by omega) _ _)
  refine (shifted_sum_error n ((a : ℝ) / q) β (unitMean q a)).trans ?_
  apply mul_le_mul_of_nonneg_left _ hD
  apply add_le_add_right
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left hscale (by positivity)
theorem squared_arc_error {Q n q a : ℕ} (m : ℝ) (hn : 0 < n) (hq : 0 < q) {β : ℝ}
    (hβ : |β| ≤ (Q : ℝ) / ((q : ℝ) * n)) :
    let r : ℝ := (a : ℝ) / q
    let A := unitMean q a
    modelError n q a m β ≤
      prefixError n r A * (1 + 2 * Real.pi * ((Q : ℝ) / q)) *
        (Chebyshev.theta n + ‖A‖ * (n + 1 : ℕ)) := by
  intro r A
  have hsum : ‖primeSum n (r + β)‖ ≤ Chebyshev.theta n := by
    rw [primeSum, ← sum_primeWeight]
    refine (norm_sum_le _ _).trans (sum_le_sum fun k _ => ?_)
    rw [norm_mul, norm_phase, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (primeWeight_nonneg k)]
  have hkernel : ‖kernel n β‖ ≤ (n + 1 : ℕ) := by
    unfold kernel
    refine (norm_sum_le _ _).trans ?_
    simp [norm_phase]
  have hplus : ‖primeSum n (r + β) + A * kernel n β‖ ≤ Chebyshev.theta n + ‖A‖ * (n + 1 : ℕ) := by
    refine (norm_add_le _ _).trans (add_le_add hsum ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left hkernel (norm_nonneg _)
  rw [modelError_eq,
    show (primeSum n (r + β)) ^ 2 - (A * kernel n β) ^ 2 =
      (primeSum n (r + β) - A * kernel n β) * (primeSum n (r + β) + A * kernel n β) by ring,
    norm_mul]
  exact mul_le_mul (rational_arc_error (a := a) hn hq hβ) hplus (norm_nonneg _)
    ((norm_nonneg _).trans (rational_arc_error (a := a) hn hq hβ))
private theorem unitMean_norm (q a : ℕ) (hq : 0 < q) : ‖unitMean q a‖ ≤ 1 := by
  let U := (range q).filter (fun r => r.Coprime q)
  have hcard : U.card = q.totient := by
    rw [Nat.totient_eq_card_coprime]
    have h : U = (range q).filter (fun r => q.Coprime r) := by ext k; simp [U, Nat.coprime_comm]
    rw [h]
  have hφ : 0 < (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
  unfold unitMean
  rw [norm_div, Complex.norm_natCast, div_le_one hφ]
  refine (norm_sum_le _ _).trans ?_
  change ∑ r ∈ U, ‖phase ((r : ℝ) * ((a : ℝ) / q))‖ ≤ _
  simp only [phase, Complex.norm_exp_ofReal_mul_I, sum_const, nsmul_eq_mul, mul_one, hcard, le_refl]
private theorem integral_error_bound {Q n q : ℕ} (m : ℝ) (hn : 1 ≤ n) (hq : 0 < q) (hQ : q ≤ Q)
    (a : ℕ) {E : ℝ} (hE : 0 ≤ E)
    (hp : prefixError n ((a : ℝ) / q) (unitMean q a) ≤ q * E) :
    (∫ β in -(width Q n q)..(width Q n q), modelError n q a m β) ≤
      2 * (Q : ℝ) ^ 2 * E * ((1 + 2 * Real.pi) * (Real.log 4 + 2)) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hQ' : (q : ℝ) ≤ Q := by exact_mod_cast hQ
  have npos : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn'
  have qpos : (0 : ℝ) < q := lt_of_lt_of_le zero_lt_one hq'
  let B := E * ((1 + 2 * Real.pi) * (Q : ℝ)) * ((Real.log 4 + 2) * (n : ℝ))
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have wpos : 0 ≤ width Q n q := by unfold width; positivity
  have hlength : width Q n q ≤ (Q : ℝ) / n := by
    unfold width
    apply div_le_div_of_nonneg_left (by positivity) npos
    simpa only [one_mul] using (mul_le_mul_of_nonneg_right hq' npos.le)
  have hpoint {β : ℝ} (hβ : β ∈ Set.Icc (-(width Q n q)) (width Q n q)) :
      modelError n q a m β ≤ B := by
    have hp' := squared_arc_error (a := a) m hn hq (abs_le.mpr hβ)
    have hscale :
        prefixError n ((a : ℝ) / q) (unitMean q a) * (1 + 2 * Real.pi * ((Q : ℝ) / q)) ≤
        E * ((1 + 2 * Real.pi) * (Q : ℝ)) := by
      calc
        _ ≤ ((q : ℝ) * E) * (1 + 2 * Real.pi * ((Q : ℝ) / q)) :=
          mul_le_mul_of_nonneg_right hp (by positivity)
        _ = E * ((q : ℝ) + 2 * Real.pi * Q) := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left (by nlinarith only [hQ']) hE
    have hU := unitMean_norm q a hq
    have hcap : Chebyshev.theta n + ‖unitMean q a‖ * (n + 1 : ℕ) ≤ (Real.log 4 + 2) * (n : ℝ) := by
      have hcard := mul_le_mul_of_nonneg_right hU (show 0 ≤ (n : ℝ) + 1 by positivity)
      push_cast
      nlinarith only [Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg n), hcard, hn']
    exact hp'.trans (mul_le_mul hscale hcap (by positivity) (by positivity))
  have hc : Continuous (modelError n q a m) := by
    unfold modelError primeSum kernel phase
    fun_prop
  calc
    _ ≤ ∫ _β in -(width Q n q)..(width Q n q), B :=
      intervalIntegral.integral_mono_on (by linarith) (hc.intervalIntegrable _ _)
        (by simp) (fun β hβ => hpoint hβ)
    _ = (2 * width Q n q) * B := by rw [intervalIntegral.integral_const, smul_eq_mul]; ring
    _ ≤ (2 * ((Q : ℝ) / n)) * B :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlength (by norm_num)) hB
    _ = _ := by dsimp [B]; field_simp

private theorem totalArcError_nonneg (Q n : ℕ) (m : ℝ) : 0 ≤ totalArcError Q n m := by
  refine sum_nonneg fun q _ => sum_nonneg fun a _ => ?_
  have hw : 0 ≤ width Q n q := by unfold width; positivity
  exact intervalIntegral.integral_nonneg (by linarith) fun _ _ => norm_nonneg _

/-- Finite absolute error estimate, with arbitrary cutoff and twist. -/
theorem totalArcError_le {Q n : ℕ} (hn1 : 1 ≤ n) (hQ1 : 1 ≤ Q) (m : ℝ)
    {E : ℝ} (hE : 0 ≤ E) (hp : ∀ q a : ℕ, 0 < q → q ≤ Q →
      prefixError n ((a : ℝ) / q) (unitMean q a) ≤ q * E) :
    totalArcError Q n m ≤
      (4 * ((1 + 2 * Real.pi) * (Real.log 4 + 2))) * (Q : ℝ)^4 * E := by
  have hQ' : (1 : ℝ) ≤ Q := by exact_mod_cast hQ1
  let C : ℝ := 4 * ((1 + 2 * Real.pi) * (Real.log 4 + 2))
  let B : ℝ := 2 * (Q : ℝ) ^ 2 * E * ((1 + 2 * Real.pi) * (Real.log 4 + 2))
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have htot : totalArcError Q n m ≤ C * (Q : ℝ) ^ 4 * E := by
    unfold totalArcError
    calc
      _ ≤ ∑ _q ∈ Icc 1 Q, (((Q : ℝ) + 1) * B) := by
        refine sum_le_sum fun q hq => ?_
        have hq' := mem_Icc.mp hq
        calc
          _ ≤ ∑ _a ∈ range (q + 1), B := sum_le_sum fun a _ =>
            integral_error_bound m hn1 hq'.1 hq'.2 a hE (hp q a hq'.1 hq'.2)
          _ = ((q : ℝ) + 1) * B := by simp
          _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.add_le_add_right hq'.2 1) hB
      _ = (Q : ℝ) * (((Q : ℝ) + 1) * B) := by simp [Nat.card_Icc]
      _ ≤ (Q : ℝ) * ((2 * (Q : ℝ)) * B) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by linarith) hB) (Nat.cast_nonneg _)
      _ = _ := by dsimp [B, C]; ring
  exact htot

/-- The sum of the absolute errors on all full arcs is o(n/log(n)^S), for every
fixed natural S and every positive exponent B in Q=(log₂(n+2))^B. The target
frequency may vary arbitrarily with n. -/
theorem totalArcError_log_saving (B S : ℕ) (hB : 0 < B) (freq : ℕ → ℝ) :
    Tendsto (fun n : ℕ => (Real.log n)^S * totalArcError (cutoff B n) n (freq n) / n)
      atTop (𝓝 0) := by
  obtain ⟨M, hM, hpre⟩ := uniform_prefix_error B (S+B*4) hB
  let C : ℝ := 4 * ((1 + 2 * Real.pi) * (Real.log 4 + 2))
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hlimit := (envelope_saving B (S+B*4) M).const_mul (C * (4^B)^4)
  simp only [mul_zero] at hlimit
  apply squeeze_zero' (Eventually.of_forall fun n => div_nonneg (mul_nonneg
    (pow_nonneg (Real.log_natCast_nonneg n) _) (totalArcError_nonneg _ _ _)) (Nat.cast_nonneg n)) _ hlimit
  filter_upwards [hpre, eventually_ge_atTop (2 : ℕ)] with n hp hn
  have hn1 : 1 ≤ n := by omega
  have hQ1 : 1 ≤ cutoff B n := Nat.one_le_iff_ne_zero.mpr
    (pow_ne_zero B (Nat.log_pos (by decide : 1 < 2) (by omega : 2 ≤ n + 2)).ne')
  have hL : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  have hE : 0 ≤ errorEnvelope B (S+B*4) M n := by unfold errorEnvelope; positivity
  have htot := totalArcError_le hn1 hQ1 (freq n) hE hp
  have hpow := pow_le_pow_left₀ (Nat.cast_nonneg (α := ℝ) (cutoff B n)) (cutoff_le_log B hn) 4
  have hcomp : (cutoff B n : ℝ)^4 ≤ (4^B)^4 * (Real.log n)^(B*4) := by
    simpa only [mul_pow, pow_mul] using hpow
  calc
    _ ≤ (Real.log n)^S * (C * (cutoff B n : ℝ)^4 * errorEnvelope B (S+B*4) M n) / n :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left htot (pow_nonneg hL _)) (Nat.cast_nonneg n)
    _ ≤ (Real.log n)^S * (C * ((4^B)^4 * (Real.log n)^(B*4)) * errorEnvelope B (S+B*4) M n) / n :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcomp hC) hE) (pow_nonneg hL _)) (Nat.cast_nonneg n)
    _ = _ := by simp only [pow_add]; ring

theorem totalArcError_sublinear (B : ℕ) (hB : 0 < B) (freq : ℕ → ℝ) :
    Tendsto (fun n : ℕ => totalArcError (cutoff B n) n (freq n) / n) atTop (𝓝 0) := by
  simpa only [pow_zero, one_mul] using totalArcError_log_saving B 0 hB freq

/-- With one threshold uniform in the target frequency. -/
theorem eventually_totalArcError_lt (B S : ℕ) (hB : 0 < B) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ m : ℝ, (Real.log n)^S * totalArcError (cutoff B n) n m < ε * n := by
  have h := (tendsto_order.1 (totalArcError_log_saving B S hB (fun _ => 0))).2 ε hε
  filter_upwards [h, eventually_ge_atTop (1 : ℕ)] with n hn hnpos m
  rw [totalArcError_frequency_independent _ _ m 0]
  exact (div_lt_iff₀ (show (0 : ℝ) < n by exact_mod_cast hnpos)).mp hn

end
end GoldbachMajorArc.Polylog

end

section

/-!
The Vaughan estimate and its supporting development are adapted from OpenAI,
openai/math, revision 3344da59991ed94f9ba711217b29c1d760badfa6,
lean/OAI/NumberTheory/EgyptianFractions (Apache License 2.0).
This version selects the declarations supporting the final estimate and adapts them
to version 4.36.0 of the proof assistant and its pinned Mathlib. Section comments identify upstream files.
https://github.com/openai/math/tree/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/NumberTheory/EgyptianFractions
-/

-- Upstream module OAI.NumberTheory.EgyptianFractions.VaughanDyadic

namespace OAI
/-!
# Exact dyadic decomposition of a truncated hyperbola

The long--long convolution is partitioned into genuine dyadic row intervals.
Each column interval is shortened to `N / 2^j`, retaining the exact `mn ≤ N`
cutoff. This is a finite reindexing, with no analytic cancellation hypothesis.
-/

noncomputable section
open scoped BigOperators
open Finset

namespace Problem337.VaughanDyadic

/-- Rows above the lower cutoff, inside one half-open power-of-two interval. -/
def shell (U N j : ℕ) : Finset ℕ :=
  (Ioc U N).filter fun m => 2 ^ j ≤ m ∧ m < 2 ^ (j + 1)

lemma mem_shell {U N j m : ℕ} :
    m ∈ shell U N j ↔ U < m ∧ m ≤ N ∧ 2 ^ j ≤ m ∧ m < 2 ^ (j + 1) := by
  simp only [shell, mem_filter, mem_Ioc]
  tauto

lemma shell_eq_log_fiber (U N j : ℕ) :
    shell U N j = (Ioc U N).filter (fun m => Nat.log 2 m = j) := by
  ext m
  simp only [shell, mem_filter]
  apply and_congr_right
  intro hm
  exact (Nat.log_eq_iff (Or.inr ⟨by decide, (lt_of_le_of_lt (Nat.zero_le U)
    (mem_Ioc.mp hm).1).ne'⟩)).symm

/-- The shell is a single consecutive interval, so its phase correlations remain geometric. -/
lemma shell_eq_Icc (U N j : ℕ) :
    shell U N j = Icc (max (U + 1) (2 ^ j)) (min N (2 ^ (j + 1) - 1)) := by
  ext m
  rw [mem_shell]
  simp only [mem_Icc, max_le_iff, le_min_iff]
  have hp : 0 < 2 ^ (j + 1) := by positivity
  omega

/-- Exact partition, valid also when the original interval is empty. -/
theorem sum_eq_sum_shells {E : Type*} [AddCommMonoid E]
    (U N : ℕ) (f : ℕ → E) :
    (∑ m ∈ Ioc U N, f m) =
      ∑ j ∈ range (Nat.log 2 N + 1), ∑ m ∈ shell U N j, f m := by
  simp_rw [shell_eq_log_fiber]
  apply (sum_fiberwise_of_maps_to ?_ f).symm
  intro m hm
  exact mem_range.mpr (Nat.lt_succ_of_le (Nat.log_mono_right (mem_Ioc.mp hm).2))

lemma inner_sum_eq_common_cutoff {E : Type*} [AddCommMonoid E]
    (N U V j m : ℕ) (hm : m ∈ shell U N j) (f : ℕ → E) :
    (∑ n ∈ Ioc V (N / m), f n) =
      ∑ n ∈ Ioc V (N / 2 ^ j), if m * n ≤ N then f n else 0 := by
  have hmem := mem_shell.mp hm
  have hm0 : 0 < m := lt_of_le_of_lt (Nat.zero_le U) hmem.1
  have hpow : 0 < 2 ^ j := by positivity
  have hdiv : N / m ≤ N / 2 ^ j := Nat.div_le_div_left hmem.2.2.1 hpow
  have hsets : Ioc V (N / m) =
      (Ioc V (N / 2 ^ j)).filter (fun n => m * n ≤ N) := by
    ext n
    simp only [mem_Ioc, mem_filter]
    constructor
    · rintro ⟨hV, hn⟩
      exact ⟨⟨hV, hn.trans hdiv⟩,
        by simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hm0).mp hn⟩
    · rintro ⟨⟨hV, _⟩, hn⟩
      exact ⟨hV, (Nat.le_div_iff_mul_le hm0).mpr (by simpa [Nat.mul_comm] using hn)⟩
  rw [hsets, sum_filter]

/-- The actual dyadic block, not a rectangular surrogate without the cutoff. -/
def block {E : Type*} [AddCommMonoid E] (N U V j : ℕ) (F : ℕ → ℕ → E) : E :=
  ∑ m ∈ shell U N j, ∑ n ∈ Ioc V (N / 2 ^ j),
    if m * n ≤ N then F m n else 0

/-- Exact long--long hyperbola decomposition into common-column dyadic blocks. -/
theorem sum_hyperbola_eq_sum_blocks {E : Type*} [AddCommMonoid E]
    (N U V : ℕ) (F : ℕ → ℕ → E) :
    (∑ m ∈ Ioc U N, ∑ n ∈ Ioc V (N / m), F m n) =
      ∑ j ∈ range (Nat.log 2 N + 1), block N U V j F := by
  rw [sum_eq_sum_shells]
  apply sum_congr rfl
  intro j hj
  unfold block
  apply sum_congr rfl
  intro m hm
  exact inner_sum_eq_common_cutoff N U V j m hm (F m)

/-- Product-finset form of the same exact decomposition. -/
theorem sum_filtered_product_eq_sum_blocks {E : Type*} [AddCommMonoid E]
    (N U V : ℕ) (F : ℕ → ℕ → E) :
    (∑ d ∈ (Ioc U N ×ˢ Ioc V N).filter (fun d => d.1 * d.2 ≤ N), F d.1 d.2) =
      ∑ j ∈ range (Nat.log 2 N + 1), block N U V j F := by
  rw [← sum_hyperbola_eq_sum_blocks, sum_filter, sum_product]
  apply sum_congr rfl
  intro m hm
  have hm0 : 0 < m := lt_of_le_of_lt (Nat.zero_le U) (mem_Ioc.mp hm).1
  rw [← sum_filter]
  have he : (Ioc V N).filter (fun n => m * n ≤ N) = Ioc V (N / m) := by
    ext n
    simp only [mem_filter, mem_Ioc]
    constructor
    · rintro ⟨⟨hV, _⟩, hmn⟩
      exact ⟨hV, (Nat.le_div_iff_mul_le hm0).mpr (by simpa [Nat.mul_comm] using hmn)⟩
    · rintro ⟨hV, hn⟩
      exact ⟨⟨hV, hn.trans (Nat.div_le_self N m)⟩,
        by simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hm0).mp hn⟩
  rw [he]

/-- Triangle inequality with the actual dyadic block norms. -/
theorem norm_hyperbola_le_sum_block_norms {E : Type*} [SeminormedAddCommGroup E]
    (N U V : ℕ) (F : ℕ → ℕ → E) :
    ‖∑ m ∈ Ioc U N, ∑ n ∈ Ioc V (N / m), F m n‖ ≤
      ∑ j ∈ range (Nat.log 2 N + 1), ‖block N U V j F‖ := by
  rw [sum_hyperbola_eq_sum_blocks]
  exact norm_sum_le _ _

/-- Any genuine uniform block estimate pays only the number of dyadic blocks. -/
theorem norm_hyperbola_le_block_count {E : Type*} [SeminormedAddCommGroup E]
    (N U V : ℕ) (F : ℕ → ℕ → E) (B : ℝ)
    (hB : ∀ j < Nat.log 2 N + 1, ‖block N U V j F‖ ≤ B) :
    ‖∑ m ∈ Ioc U N, ∑ n ∈ Ioc V (N / m), F m n‖ ≤
      (Nat.log 2 N + 1 : ℕ) * B := by
  calc
    _ ≤ ∑ j ∈ range (Nat.log 2 N + 1), ‖block N U V j F‖ :=
      norm_hyperbola_le_sum_block_norms N U V F
    _ ≤ ∑ j ∈ range (Nat.log 2 N + 1), B :=
      sum_le_sum fun j hj => hB j (mem_range.mp hj)
    _ = _ := by simp

/-- Real-log normalization of the finite dyadic block count. -/
theorem norm_hyperbola_le_log_budget {E : Type*} [SeminormedAddCommGroup E]
    (N U V : ℕ) (F : ℕ → ℕ → E) (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ j < Nat.log 2 N + 1, ‖block N U V j F‖ ≤ B) :
    ‖∑ m ∈ Ioc U N, ∑ n ∈ Ioc V (N / m), F m n‖ ≤
      (1 + Real.log N / Real.log 2) * B := by
  refine (norm_hyperbola_le_block_count N U V F B hB).trans ?_
  apply mul_le_mul_of_nonneg_right _ hB0
  have h := Real.natLog_le_logb N 2
  simp only [Real.logb, Nat.cast_ofNat] at h
  push_cast
  linarith

end Problem337.VaughanDyadic

end

end OAI

-- Upstream module OAI.NumberTheory.EgyptianFractions.VaughanIdentity

namespace OAI
/-!
# Vaughan's identity with finite cutoffs

This file supplies an unconditional algebraic input to the analytic three-prime
route. Multiplication of arithmetic functions below is Dirichlet convolution.
No estimate for exponential sums over primes is assumed or asserted here.
-/

noncomputable section

open scoped BigOperators ArithmeticFunction ArithmeticFunction.Moebius
  ArithmeticFunction.zeta

namespace Problem337.Vaughan

/-- The part of an arithmetic function supported on integers at most `U`. -/
def shortPart {R : Type*} [Zero R] (U : ℕ) (f : ArithmeticFunction R) :
    ArithmeticFunction R :=
  ⟨fun n => if n ≤ U then f n else 0, by simp⟩

/-- The complementary part, supported on integers strictly above `U`. -/
def longPart {R : Type*} [Zero R] (U : ℕ) (f : ArithmeticFunction R) :
    ArithmeticFunction R :=
  ⟨fun n => if U < n then f n else 0, by simp⟩

@[simp] lemma shortPart_apply {R : Type*} [Zero R]
    (U : ℕ) (f : ArithmeticFunction R) (n : ℕ) :
    shortPart U f n = if n ≤ U then f n else 0 := rfl

@[simp] lemma longPart_apply {R : Type*} [Zero R]
    (U : ℕ) (f : ArithmeticFunction R) (n : ℕ) :
    longPart U f n = if U < n then f n else 0 := rfl

lemma shortPart_add_longPart {R : Type*} [AddMonoid R]
    (U : ℕ) (f : ArithmeticFunction R) : shortPart U f + longPart U f = f := by
  ext n
  by_cases hn : n ≤ U <;> simp [hn, Nat.not_lt.mpr, Nat.lt_of_not_ge]

lemma longPart_eq_sub_shortPart {R : Type*} [AddCommGroup R]
    (U : ℕ) (f : ArithmeticFunction R) : longPart U f = f - shortPart U f := by
  have h := shortPart_add_longPart U f
  exact eq_sub_iff_add_eq.mpr (by simpa only [add_comm] using h)

/-- Vaughan's four-term identity, valid also at zero and for zero cutoffs.
The first convolution is Type I; the second has a coefficient supported on
`[1,U*V]`; the last is the long-long Type II convolution. -/
theorem vonMangoldt_identity (U V : ℕ) :
    ArithmeticFunction.vonMangoldt =
      shortPart V ArithmeticFunction.vonMangoldt +
      shortPart U (μ : ArithmeticFunction ℝ) * ArithmeticFunction.log -
      (shortPart U (μ : ArithmeticFunction ℝ) *
        shortPart V ArithmeticFunction.vonMangoldt) * (ζ : ArithmeticFunction ℝ) +
      (longPart U (μ : ArithmeticFunction ℝ) * (ζ : ArithmeticFunction ℝ)) *
        longPart V ArithmeticFunction.vonMangoldt := by
  rw [longPart_eq_sub_shortPart, longPart_eq_sub_shortPart]
  have hμ : (μ : ArithmeticFunction ℝ) * (ζ : ArithmeticFunction ℝ) = 1 :=
    ArithmeticFunction.coe_moebius_mul_coe_zeta
  have hΛ : (ζ : ArithmeticFunction ℝ) * ArithmeticFunction.vonMangoldt =
      ArithmeticFunction.log := ArithmeticFunction.zeta_mul_vonMangoldt
  calc
    ArithmeticFunction.vonMangoldt =
        ((μ : ArithmeticFunction ℝ) * (ζ : ArithmeticFunction ℝ)) *
          ArithmeticFunction.vonMangoldt := by rw [hμ, one_mul]
    _ = _ := by
      rw [← hΛ]
      have hshort : ((μ : ArithmeticFunction ℝ) * (ζ : ArithmeticFunction ℝ)) *
          shortPart V ArithmeticFunction.vonMangoldt =
          shortPart V ArithmeticFunction.vonMangoldt := by rw [hμ, one_mul]
      linear_combination hshort

/-- A convolution of two short parts has the expected product support. -/
lemma shortPart_mul_eq_zero_of_lt {R : Type*} [Semiring R]
    (U V n : ℕ) (f g : ArithmeticFunction R) (hn : U * V < n) :
    (shortPart U f * shortPart V g) n = 0 := by
  rw [ArithmeticFunction.mul_apply]
  apply Finset.sum_eq_zero
  intro ab hab
  have habn := (Nat.mem_divisorsAntidiagonal.mp hab).1
  by_cases ha : ab.1 ≤ U
  · have hb : ¬ ab.2 ≤ V := by
      intro hb
      have hm := Nat.mul_le_mul ha hb
      rw [habn] at hm
      omega
    simp [ha, hb]
  · simp [ha]

/-- Convolving a long part cannot create a smaller positive index. -/
lemma longPart_mul_eq_zero_of_le {R : Type*} [Semiring R]
    (U n : ℕ) (f g : ArithmeticFunction R) (hn : n ≤ U) :
    (longPart U f * g) n = 0 := by
  rw [ArithmeticFunction.mul_apply]
  apply Finset.sum_eq_zero
  intro ab hab
  obtain ⟨hprod, hn0⟩ := Nat.mem_divisorsAntidiagonal.mp hab
  have ha : ab.1 ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) ⟨ab.2, hprod.symm⟩
  have hnot : ¬ U < ab.1 := by omega
  simp [hnot]

lemma abs_shortPart_le (U : ℕ) (f : ArithmeticFunction ℝ) (n : ℕ) :
    |shortPart U f n| ≤ |f n| := by
  by_cases hn : n ≤ U <;> simp [hn, abs_nonneg]

lemma abs_longPart_le (U : ℕ) (f : ArithmeticFunction ℝ) (n : ℕ) :
    |longPart U f n| ≤ |f n| := by
  by_cases hn : U < n <;> simp [hn, abs_nonneg]

lemma abs_real_moebius_le_one (n : ℕ) :
    |(μ : ArithmeticFunction ℝ) n| ≤ 1 := by
  change |((ArithmeticFunction.moebius n : ℤ) : ℝ)| ≤ 1
  exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := n))

/-- The short convolution coefficient appearing in Type I sums. -/
def typeICoefficient (U V : ℕ) : ArithmeticFunction ℝ :=
  shortPart U (μ : ArithmeticFunction ℝ) * shortPart V ArithmeticFunction.vonMangoldt

/-- The coefficient appearing in the long-long Type II sum. -/
def typeIICoefficient (U : ℕ) : ArithmeticFunction ℝ :=
  longPart U (μ : ArithmeticFunction ℝ) * (ζ : ArithmeticFunction ℝ)

lemma typeICoefficient_eq_zero (U V n : ℕ) (hn : U * V < n) :
    typeICoefficient U V n = 0 := shortPart_mul_eq_zero_of_lt U V n _ _ hn

lemma typeIICoefficient_eq_zero (U n : ℕ) (hn : n ≤ U) :
    typeIICoefficient U n = 0 := longPart_mul_eq_zero_of_le U n _ _ hn

/-- The Type I coefficient costs only a logarithm, not a divisor function. -/
lemma abs_typeICoefficient_le_log (U V n : ℕ) :
    |typeICoefficient U V n| ≤ Real.log n := by
  unfold typeICoefficient
  rw [ArithmeticFunction.mul_apply]
  calc
    _ ≤ ∑ ab ∈ n.divisorsAntidiagonal,
        |shortPart U (μ : ArithmeticFunction ℝ) ab.1 *
          shortPart V ArithmeticFunction.vonMangoldt ab.2| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ ab ∈ n.divisorsAntidiagonal, ArithmeticFunction.vonMangoldt ab.2 := by
      apply Finset.sum_le_sum
      intro ab hab
      rw [abs_mul]
      have hμ := (abs_shortPart_le U (μ : ArithmeticFunction ℝ) ab.1).trans
        (abs_real_moebius_le_one ab.1)
      have hΛ := abs_shortPart_le V ArithmeticFunction.vonMangoldt ab.2
      rw [abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg] at hΛ
      calc
        _ ≤ 1 * ArithmeticFunction.vonMangoldt ab.2 :=
          mul_le_mul hμ hΛ (abs_nonneg _) zero_le_one
        _ = _ := one_mul _
    _ = Real.log n := by
      rw [Nat.sum_divisorsAntidiagonal' (fun _ b => ArithmeticFunction.vonMangoldt b)]
      exact ArithmeticFunction.vonMangoldt_sum

/-- A uniform elementary coefficient bound for the Type II sum. -/
lemma abs_typeIICoefficient_le_divisors_card (U n : ℕ) :
    |typeIICoefficient U n| ≤ (n.divisors.card : ℝ) := by
  rw [typeIICoefficient, ArithmeticFunction.coe_mul_zeta_apply]
  calc
    _ ≤ ∑ d ∈ n.divisors, |longPart U (μ : ArithmeticFunction ℝ) d| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ n.divisors, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      exact (abs_longPart_le U (μ : ArithmeticFunction ℝ) d).trans
        (abs_real_moebius_le_one d)
    _ = _ := by simp

end Problem337.Vaughan

end

end OAI

-- Upstream module OAI.NumberTheory.EgyptianFractions.VaughanHyperbola

namespace OAI
/-!
# Finite hyperbola reindexing for Vaughan sums

An exact finite change of variables from `n = a*b` to pairs of positive
integers below a hyperbola. The arbitrary weight version is suitable for
both rational additive characters and real-frequency exponential sums.
-/

noncomputable section
open scoped BigOperators

namespace Problem337.Vaughan

/-- Positive lattice points below the multiplicative hyperbola `a*b ≤ N`. -/
def hyperbola (N : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 N).product (Finset.Icc 1 N)).filter (fun ab => ab.1 * ab.2 ≤ N)

@[simp] lemma mem_hyperbola {N a b : ℕ} :
    (a, b) ∈ hyperbola N ↔ 1 ≤ a ∧ 1 ≤ b ∧ a * b ≤ N := by
  change ((a, b) ∈ ((Finset.Icc 1 N).product (Finset.Icc 1 N)).filter
    (fun ab => ab.1 * ab.2 ≤ N)) ↔ _
  rw [Finset.mem_filter]
  have hm : (a, b) ∈ (Finset.Icc 1 N).product (Finset.Icc 1 N) ↔
      a ∈ Finset.Icc 1 N ∧ b ∈ Finset.Icc 1 N := Finset.mem_product
  rw [hm]
  simp only [Finset.mem_Icc]
  constructor
  · rintro ⟨⟨⟨ha, _⟩, ⟨hb, _⟩⟩, hp⟩
    exact ⟨ha, hb, hp⟩
  · rintro ⟨ha, hb, hp⟩
    have haN : a ≤ N := (Nat.le_mul_of_pos_right a (by omega : 0 < b)).trans hp
    have hbN : b ≤ N := (Nat.le_mul_of_pos_left b (by omega : 0 < a)).trans hp
    exact ⟨⟨⟨ha, haN⟩, ⟨hb, hbN⟩⟩, hp⟩

/-- The divisor-antidiagonal fibers partition the positive hyperbola exactly.
The summand may also depend on the product index `n`. -/
theorem sum_divisor_fibers {A : Type*} [AddCommMonoid A]
    (N : ℕ) (F : ℕ → ℕ → ℕ → A) :
    (∑ n ∈ Finset.Icc 1 N, ∑ ab ∈ n.divisorsAntidiagonal, F n ab.1 ab.2) =
      ∑ ab ∈ hyperbola N, F (ab.1 * ab.2) ab.1 ab.2 := by
  rw [Finset.sum_sigma']
  apply Finset.sum_nbij'
    (fun x : Sigma (fun _n : ℕ => ℕ × ℕ) => x.2)
    (fun ab : ℕ × ℕ => (⟨ab.1 * ab.2, ab⟩ : Sigma (fun _n : ℕ => ℕ × ℕ)))
  · rintro ⟨n, a, b⟩ hx
    obtain ⟨hn, hab⟩ := Finset.mem_sigma.mp hx
    obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hn
    obtain ⟨hprod, hn0⟩ := Nat.mem_divisorsAntidiagonal.mp hab
    apply mem_hyperbola.mpr
    change a * b = n at hprod
    change n ≠ 0 at hn0
    have hab0 : a * b ≠ 0 := by rw [hprod]; exact hn0
    exact ⟨Nat.pos_of_ne_zero (left_ne_zero_of_mul hab0),
      Nat.pos_of_ne_zero (right_ne_zero_of_mul hab0), by rw [hprod]; exact hnN⟩
  · rintro ⟨a, b⟩ hab
    obtain ⟨ha, hb, hp⟩ := mem_hyperbola.mp hab
    apply Finset.mem_sigma.mpr
    constructor
    · exact Finset.mem_Icc.mpr ⟨Nat.mul_pos ha hb, hp⟩
    · exact Nat.mem_divisorsAntidiagonal.mpr ⟨rfl, Nat.ne_of_gt (Nat.mul_pos ha hb)⟩
  · rintro ⟨n, a, b⟩ hx
    have hprod := (Nat.mem_divisorsAntidiagonal.mp (Finset.mem_sigma.mp hx).2).1
    change (⟨a * b, (a, b)⟩ : Sigma (fun _n : ℕ => ℕ × ℕ)) = ⟨n, (a, b)⟩
    rw [hprod]
  · intro ab hab
    rfl
  · rintro ⟨n, a, b⟩ hx
    have hprod := (Nat.mem_divisorsAntidiagonal.mp (Finset.mem_sigma.mp hx).2).1
    change F n a b = F (a * b) a b
    rw [hprod]

/-- The hyperbola sum as ordinary nested integer intervals. The inner endpoint
is the natural-number quotient `N / a`; the outer interval excludes zero. -/
theorem sum_hyperbola_eq_nested {A : Type*} [AddCommMonoid A]
    (N : ℕ) (F : ℕ → ℕ → A) :
    (∑ ab ∈ hyperbola N, F ab.1 ab.2) =
      ∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 (N / a), F a b := by
  rw [Finset.sum_sigma']
  apply Finset.sum_nbij'
    (fun ab : ℕ × ℕ => (⟨ab.1, ab.2⟩ : Sigma (fun _a : ℕ => ℕ)))
    (fun x : Sigma (fun _a : ℕ => ℕ) => (x.1, x.2))
  · rintro ⟨a, b⟩ hab
    obtain ⟨ha, hb, hp⟩ := mem_hyperbola.mp hab
    apply Finset.mem_sigma.mpr
    constructor
    · exact Finset.mem_Icc.mpr ⟨ha,
        (Nat.le_mul_of_pos_right a (by omega : 0 < b)).trans hp⟩
    · apply Finset.mem_Icc.mpr
      exact ⟨hb, (Nat.le_div_iff_mul_le (by omega : 0 < a)).mpr (by simpa [mul_comm] using hp)⟩
  · rintro ⟨a, b⟩ hx
    obtain ⟨ha, hb⟩ := Finset.mem_sigma.mp hx
    obtain ⟨ha1, haN⟩ := Finset.mem_Icc.mp ha
    obtain ⟨hb1, hbN⟩ := Finset.mem_Icc.mp hb
    change 1 ≤ a at ha1
    change 1 ≤ b at hb1
    change b ≤ N / a at hbN
    apply mem_hyperbola.mpr
    refine ⟨ha1, hb1, ?_⟩
    have hp := (Nat.le_div_iff_mul_le (by omega : 0 < a)).mp hbN
    simpa [mul_comm] using hp
  · intro ab hab
    rfl
  · intro x hx
    rfl
  · intro ab hab
    rfl

/-- Real arithmetic coefficients with complex weights, the combination used
for the von-Mangoldt exponential sum. -/
theorem sum_real_convolution_hyperbola
    (N : ℕ) (f g : ArithmeticFunction ℝ) (w : ℕ → ℂ) :
    (∑ n ∈ Finset.Icc 1 N, ((f * g) n : ℂ) * w n) =
      ∑ ab ∈ hyperbola N, ((f ab.1 * g ab.2 : ℝ) : ℂ) * w (ab.1 * ab.2) := by
  simp_rw [ArithmeticFunction.mul_apply, Complex.ofReal_sum, Finset.sum_mul]
  exact sum_divisor_fibers N (fun n a b => ((f a * g b : ℝ) : ℂ) * w n)

/-- The traditional nested-interval form of the finite convolution identity. -/
theorem sum_real_convolution_eq_nested
    (N : ℕ) (f g : ArithmeticFunction ℝ) (w : ℕ → ℂ) :
    (∑ n ∈ Finset.Icc 1 N, ((f * g) n : ℂ) * w n) =
      ∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 (N / a),
        ((f a * g b : ℝ) : ℂ) * w (a * b) := by
  rw [sum_real_convolution_hyperbola]
  exact sum_hyperbola_eq_nested (A := ℂ) N
    (fun a b => ((f a * g b : ℝ) : ℂ) * w (a * b))

end Problem337.Vaughan

end

end OAI

-- Upstream module OAI.NumberTheory.EgyptianFractions.VaughanWeighted

namespace OAI
noncomputable section
open scoped BigOperators ArithmeticFunction ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace Problem337.Vaughan

/-- Finite complex weighted sum of a real arithmetic function. -/
def weightedSum (s : Finset ℕ) (w : ℕ → ℂ) (f : ArithmeticFunction ℝ) : ℂ :=
  ∑ n ∈ s, (f n : ℂ) * w n

@[simp] theorem weightedSum_add (s : Finset ℕ) (w : ℕ → ℂ)
    (f g : ArithmeticFunction ℝ) :
    weightedSum s w (f + g) = weightedSum s w f + weightedSum s w g := by
  simp [weightedSum, add_mul, Finset.sum_add_distrib]

@[simp] theorem weightedSum_sub (s : Finset ℕ) (w : ℕ → ℂ)
    (f g : ArithmeticFunction ℝ) :
    weightedSum s w (f - g) = weightedSum s w f - weightedSum s w g := by
  simp [sub_eq_add_neg, weightedSum, add_mul, Finset.sum_add_distrib]

/-- Exact complex weighted Vaughan decomposition, using the canonical cutoff API. -/
theorem weighted_identity (s : Finset ℕ) (w : ℕ → ℂ) (U V : ℕ) :
    weightedSum s w Λ = weightedSum s w (shortPart V Λ) +
      weightedSum s w (shortPart U (μ : ArithmeticFunction ℝ) * ArithmeticFunction.log) -
      weightedSum s w (typeICoefficient U V * ζ) +
      weightedSum s w (typeIICoefficient U * longPart V Λ) := by
  have h := congrArg (weightedSum s w) (vonMangoldt_identity U V)
  simpa only [weightedSum_add, weightedSum_sub, typeICoefficient, typeIICoefficient] using h

lemma positive_interval (N : ℕ) : Finset.Icc 1 N = Finset.Ioc 0 N := by
  ext n
  simp only [Finset.mem_Icc, Finset.mem_Ioc]
  omega

/-- A convolution sum with its outer coefficient factored out. -/
theorem weightedSum_mul (N : ℕ) (w : ℕ → ℂ) (f g : ArithmeticFunction ℝ) :
    weightedSum (Finset.Ioc 0 N) w (f * g) =
      ∑ a ∈ Finset.Ioc 0 N, (f a : ℂ) *
        ∑ b ∈ Finset.Ioc 0 (N / a), (g b : ℂ) * w (a * b) := by
  simpa only [weightedSum, positive_interval, Finset.mul_sum, Complex.ofReal_mul,
    mul_assoc] using sum_real_convolution_eq_nested N f g w

/-- A compactly supported coefficient restricts the outer interval exactly. -/
theorem weightedSum_mul_of_support (N A : ℕ) (w : ℕ → ℂ)
    (f g : ArithmeticFunction ℝ) (hf : ∀ a, A < a → f a = 0) :
    weightedSum (Finset.Ioc 0 N) w (f * g) =
      ∑ a ∈ Finset.Ioc 0 (min A N), (f a : ℂ) *
        ∑ b ∈ Finset.Ioc 0 (N / a), (g b : ℂ) * w (a * b) := by
  rw [weightedSum_mul]
  symm
  apply Finset.sum_subset
  · intro a ha
    obtain ⟨ha0, haAN⟩ := Finset.mem_Ioc.mp ha
    exact Finset.mem_Ioc.mpr ⟨ha0, (le_min_iff.mp haAN).2⟩
  · intro a ha hnot
    have hA : A < a := by
      simp only [Finset.mem_Ioc] at ha hnot
      omega
    simp [hf a hA]

/-- Exact first Type I sum with its actual short cutoff. -/
theorem first_typeI_eq_sum (N U : ℕ) (w : ℕ → ℂ) :
    weightedSum (Finset.Ioc 0 N) w
        (shortPart U (μ : ArithmeticFunction ℝ) * ArithmeticFunction.log) =
      ∑ a ∈ Finset.Ioc 0 (min U N), ((μ a : ℝ) : ℂ) *
        ∑ b ∈ Finset.Ioc 0 (N / a), (Real.log b : ℂ) * w (a * b) := by
  rw [weightedSum_mul_of_support N U w _ _ (by
    intro a ha
    simp [not_le.mpr ha])]
  apply Finset.sum_congr rfl
  intro a ha
  have haU := (le_min_iff.mp (Finset.mem_Ioc.mp ha).2).1
  simp [haU]

/-- Exact second Type I sum, supported up to the product cutoff. -/
theorem second_typeI_eq_sum (N U V : ℕ) (w : ℕ → ℂ) :
    weightedSum (Finset.Ioc 0 N) w (typeICoefficient U V * ζ) =
      ∑ a ∈ Finset.Ioc 0 (min (U * V) N), (typeICoefficient U V a : ℂ) *
        ∑ b ∈ Finset.Ioc 0 (N / a), w (a * b) := by
  rw [weightedSum_mul_of_support N (U * V) w _ _ (typeICoefficient_eq_zero U V)]
  apply Finset.sum_congr rfl
  intro a ha
  congr 1
  apply Finset.sum_congr rfl
  intro b hb
  simp [ArithmeticFunction.zeta_apply_ne (Nat.ne_of_gt (Finset.mem_Ioc.mp hb).1)]

end Problem337.Vaughan

end

end OAI

-- Upstream module OAI.NumberTheory.EgyptianFractions.FirstDerivativeSum

namespace OAI
open scoped BigOperators

namespace Problem337

/-- A finite integration-by-parts identity with endpoint terms exposed. -/
theorem weighted_difference_sum (a b : ℕ → ℂ) (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1), b j * (a (j + 1) - a j)) =
      b n * a (n + 1) - b 0 * a 0 -
        ∑ j ∈ Finset.range n, (b (j + 1) - b j) * a (j + 1) := by
  induction n with
  | zero => simp; ring
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    ring

end Problem337

end OAI

-- Upstream module OAI.NumberTheory.EgyptianFractions.ThreePrimePartialSummation

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337.ThreePrimeAnalysis

/-- Finite Abel summation controlled by initial sums and total variation. -/
theorem weighted_sum_norm_le_partial_sum_bound
    (a b : ℕ → ℂ) (n : ℕ) (B : ℝ)
    (hprefix : ∀ k ≤ n + 1, ‖∑ j ∈ Finset.range k, a j‖ ≤ B) :
    ‖∑ j ∈ Finset.range (n + 1), b j * a j‖ ≤
      B * (‖b n‖ + ∑ j ∈ Finset.range n, ‖b (j + 1) - b j‖) := by
  let A : ℕ → ℂ := fun k => ∑ j ∈ Finset.range k, a j
  have hdiff (j : ℕ) : A (j + 1) - A j = a j := by
    simp [A, Finset.sum_range_succ]
  have hid := Problem337.weighted_difference_sum A b n
  simp only [hdiff, A, Finset.range_zero, Finset.sum_empty, mul_zero, sub_zero] at hid
  rw [hid]
  calc
    _ ≤ ‖b n * ∑ j ∈ Finset.range (n + 1), a j‖ +
        ‖∑ j ∈ Finset.range n, (b (j + 1) - b j) *
          ∑ i ∈ Finset.range (j + 1), a i‖ := norm_sub_le _ _
    _ ≤ ‖b n‖ * B + ∑ j ∈ Finset.range n, ‖b (j + 1) - b j‖ * B := by
      apply add_le_add
      · rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hprefix (n + 1) le_rfl) (norm_nonneg _)
      · apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro j hj
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hprefix (j + 1) (by
          have := Finset.mem_range.mp hj
          omega)) (norm_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; ring

end Problem337.ThreePrimeAnalysis

end

end OAI

-- Upstream module OAI.NumberTheory.EgyptianFractions.VaughanTypeI

namespace OAI
noncomputable section
open scoped BigOperators ArithmeticFunction ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace Problem337.Vaughan

/-- Indexing positive initial intervals by a zero-based range. -/
lemma sum_Ioc_zero_eq_sum_range_succ {R : Type*} [AddCommMonoid R]
    (f : ℕ → R) (N : ℕ) :
    (∑ j ∈ Finset.Ioc 0 N, f j) = ∑ j ∈ Finset.range N, f (j + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_Ioc_succ_top (Nat.zero_le N), Finset.sum_range_succ, ih]

/-- Adding a logarithmic weight costs at most twice the endpoint logarithm.
The initial-sum bound remains explicit; no cancellation estimate is assumed silently. -/
theorem log_weighted_sum_norm_le (w : ℕ → ℂ) (N : ℕ) (B : ℝ)
    (hprefix : ∀ k ≤ N, ‖∑ j ∈ Finset.Ioc 0 k, w j‖ ≤ B) :
    ‖∑ j ∈ Finset.Ioc 0 N, (Real.log j : ℂ) * w j‖ ≤
      2 * B * Real.log N := by
  cases N with
  | zero => simp
  | succ n =>
    have hlog (j : ℕ) : 0 ≤ Real.log (j + 1 : ℕ) :=
      Real.log_nonneg (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le j))
    have hmono (j : ℕ) : Real.log (j + 1 : ℕ) ≤ Real.log (j + 1 + 1 : ℕ) := by
      apply Real.log_le_log
      · positivity
      · exact_mod_cast Nat.le_succ (j + 1)
    have hvar : (∑ j ∈ Finset.range n,
        ‖(Real.log (j + 1 + 1 : ℕ) : ℂ) - (Real.log (j + 1 : ℕ) : ℂ)‖) =
        Real.log (n + 1 : ℕ) := by
      calc
        _ = ∑ j ∈ Finset.range n,
            (Real.log (j + 1 + 1 : ℕ) - Real.log (j + 1 : ℕ)) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (sub_nonneg.mpr (hmono j))]
        _ = _ := by
          simpa using Finset.sum_range_sub (fun j => Real.log (j + 1 : ℕ)) n
    have h := ThreePrimeAnalysis.weighted_sum_norm_le_partial_sum_bound
      (fun j => w (j + 1)) (fun j => (Real.log (j + 1 : ℕ) : ℂ)) n B (by
        intro k hk
        simpa only [sum_Ioc_zero_eq_sum_range_succ] using hprefix k hk)
    rw [hvar, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hlog n)] at h
    rw [sum_Ioc_zero_eq_sum_range_succ]
    convert h using 1
    ring

/-- Type I logarithmic bilinear estimate for coefficients bounded by one. -/
theorem norm_log_bilinear_sum_le (w : ℕ → ℂ) (N A : ℕ) (c B : ℕ → ℝ)
    (hA : A ≤ N)
    (hc : ∀ a ∈ Finset.Ioc 0 A, |c a| ≤ 1)
    (hprefix : ∀ a ∈ Finset.Ioc 0 A, ∀ k ≤ N / a,
      ‖∑ b ∈ Finset.Ioc 0 k, w (a * b)‖ ≤ B a) :
    ‖∑ a ∈ Finset.Ioc 0 A, (c a : ℂ) *
        ∑ b ∈ Finset.Ioc 0 (N / a), (Real.log b : ℂ) * w (a * b)‖ ≤
      2 * Real.log N * ∑ a ∈ Finset.Ioc 0 A, B a := by
  calc
    _ ≤ ∑ a ∈ Finset.Ioc 0 A,
        ‖(c a : ℂ) * ∑ b ∈ Finset.Ioc 0 (N / a),
          (Real.log b : ℂ) * w (a * b)‖ := norm_sum_le _ _
    _ ≤ ∑ a ∈ Finset.Ioc 0 A, 2 * Real.log N * B a := by
      apply Finset.sum_le_sum
      intro a ha
      obtain ⟨ha0, haA⟩ := Finset.mem_Ioc.mp ha
      have haN := haA.trans hA
      have hq : 1 ≤ N / a := (Nat.le_div_iff_mul_le ha0).mpr (by simpa using haN)
      have hB : 0 ≤ B a := by simpa using hprefix a ha 0 (Nat.zero_le _)
      have hlog : Real.log (N / a : ℕ) ≤ Real.log N := by
        apply Real.log_le_log
        · exact_mod_cast (Nat.zero_lt_of_lt hq)
        · exact_mod_cast Nat.div_le_self N a
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      calc
        _ ≤ 1 * ‖∑ b ∈ Finset.Ioc 0 (N / a),
            (Real.log b : ℂ) * w (a * b)‖ :=
          mul_le_mul_of_nonneg_right (hc a ha) (norm_nonneg _)
        _ ≤ 2 * B a * Real.log (N / a : ℕ) := by
          simpa using log_weighted_sum_norm_le (fun b => w (a * b)) (N / a) (B a)
            (hprefix a ha)
        _ ≤ 2 * Real.log N * B a := by
          nlinarith [mul_le_mul_of_nonneg_left hlog (show 0 ≤ 2 * B a by positivity)]
    _ = _ := by rw [Finset.mul_sum]

/-- Type I bilinear estimate for coefficients with the logarithmic majorant. -/
theorem norm_bilinear_sum_le_log (w : ℕ → ℂ) (N A : ℕ) (c B : ℕ → ℝ)
    (hA : A ≤ N)
    (hc : ∀ a ∈ Finset.Ioc 0 A, |c a| ≤ Real.log a)
    (hinner : ∀ a ∈ Finset.Ioc 0 A,
      ‖∑ b ∈ Finset.Ioc 0 (N / a), w (a * b)‖ ≤ B a) :
    ‖∑ a ∈ Finset.Ioc 0 A, (c a : ℂ) *
        ∑ b ∈ Finset.Ioc 0 (N / a), w (a * b)‖ ≤
      Real.log N * ∑ a ∈ Finset.Ioc 0 A, B a := by
  calc
    _ ≤ ∑ a ∈ Finset.Ioc 0 A,
        ‖(c a : ℂ) * ∑ b ∈ Finset.Ioc 0 (N / a), w (a * b)‖ := norm_sum_le _ _
    _ ≤ ∑ a ∈ Finset.Ioc 0 A, Real.log N * B a := by
      apply Finset.sum_le_sum
      intro a ha
      obtain ⟨ha0, haA⟩ := Finset.mem_Ioc.mp ha
      have hB : 0 ≤ B a := (norm_nonneg _).trans (hinner a ha)
      have hlog : Real.log a ≤ Real.log N := Real.log_le_log
        (by exact_mod_cast ha0) (by exact_mod_cast haA.trans hA)
      have hlogN : 0 ≤ Real.log N := (abs_nonneg _).trans ((hc a ha).trans hlog)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul ((hc a ha).trans hlog) (hinner a ha) (norm_nonneg _) hlogN
    _ = _ := by rw [Finset.mul_sum]

/-- The first Vaughan Type I term in its finite bilinear form. -/
theorem first_typeI_sum_bound (w : ℕ → ℂ) (N U : ℕ) (B : ℕ → ℝ)
    (hprefix : ∀ a ∈ Finset.Ioc 0 (min U N), ∀ k ≤ N / a,
      ‖∑ b ∈ Finset.Ioc 0 k, w (a * b)‖ ≤ B a) :
    ‖∑ a ∈ Finset.Ioc 0 (min U N), ((μ a : ℝ) : ℂ) *
        ∑ b ∈ Finset.Ioc 0 (N / a), (Real.log b : ℂ) * w (a * b)‖ ≤
      2 * Real.log N * ∑ a ∈ Finset.Ioc 0 (min U N), B a := by
  apply norm_log_bilinear_sum_le w N (min U N) (fun a => (μ a : ℝ)) B
    (min_le_right _ _) _ hprefix
  intro a ha
  exact abs_real_moebius_le_one a

/-- The second Vaughan Type I term in its finite bilinear form. -/
theorem second_typeI_sum_bound (w : ℕ → ℂ) (N U V : ℕ) (B : ℕ → ℝ)
    (hinner : ∀ a ∈ Finset.Ioc 0 (min (U * V) N),
      ‖∑ b ∈ Finset.Ioc 0 (N / a), w (a * b)‖ ≤ B a) :
    ‖∑ a ∈ Finset.Ioc 0 (min (U * V) N), (typeICoefficient U V a : ℂ) *
        ∑ b ∈ Finset.Ioc 0 (N / a), w (a * b)‖ ≤
      Real.log N * ∑ a ∈ Finset.Ioc 0 (min (U * V) N), B a := by
  exact norm_bilinear_sum_le_log w N (min (U * V) N) (typeICoefficient U V) B
    (min_le_right _ _) (fun a _ => abs_typeICoefficient_le_log U V a) hinner

/-- First Type I estimate directly for the actual Vaughan convolution. -/
theorem first_typeI_bound (w : ℕ → ℂ) (N U : ℕ) (B : ℕ → ℝ)
    (hprefix : ∀ a ∈ Finset.Ioc 0 (min U N), ∀ k ≤ N / a,
      ‖∑ b ∈ Finset.Ioc 0 k, w (a * b)‖ ≤ B a) :
    ‖weightedSum (Finset.Ioc 0 N) w
        (shortPart U (μ : ArithmeticFunction ℝ) * ArithmeticFunction.log)‖ ≤
      2 * Real.log N * ∑ a ∈ Finset.Ioc 0 (min U N), B a := by
  rw [first_typeI_eq_sum]
  exact first_typeI_sum_bound w N U B hprefix

/-- Second Type I estimate directly for the actual Vaughan convolution. -/
theorem second_typeI_bound (w : ℕ → ℂ) (N U V : ℕ) (B : ℕ → ℝ)
    (hinner : ∀ a ∈ Finset.Ioc 0 (min (U * V) N),
      ‖∑ b ∈ Finset.Ioc 0 (N / a), w (a * b)‖ ≤ B a) :
    ‖weightedSum (Finset.Ioc 0 N) w (typeICoefficient U V * ζ)‖ ≤
      Real.log N * ∑ a ∈ Finset.Ioc 0 (min (U * V) N), B a := by
  rw [second_typeI_eq_sum]
  exact second_typeI_sum_bound w N U V B hinner

end Problem337.Vaughan

end

end OAI

-- Upstream module OAI.NumberTheory.EgyptianFractions.VaughanDecomposition

namespace OAI
noncomputable section
open scoped BigOperators ArithmeticFunction ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace Problem337.Vaughan

/-- Taking a short part restricts a finite weighted sum to the smaller interval. -/
theorem weightedSum_shortPart (N V : ℕ) (w : ℕ → ℂ) (f : ArithmeticFunction ℝ) :
    weightedSum (Finset.Ioc 0 N) w (shortPart V f) =
      weightedSum (Finset.Ioc 0 (min V N)) w f := by
  unfold weightedSum
  calc
    _ = ∑ n ∈ Finset.Ioc 0 (min V N), (shortPart V f n : ℂ) * w n := by
      symm
      apply Finset.sum_subset
      · intro n hn
        obtain ⟨hn0, hnVN⟩ := Finset.mem_Ioc.mp hn
        exact Finset.mem_Ioc.mpr ⟨hn0, (le_min_iff.mp hnVN).2⟩
      · intro n hn hnot
        have hV : ¬ n ≤ V := by
          simp only [Finset.mem_Ioc] at hn hnot
          omega
        simp [hV]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n hn
      simp [(le_min_iff.mp (Finset.mem_Ioc.mp hn).2).1]

/-- The initial von Mangoldt segment has the elementary `V log V` bound. -/
theorem norm_short_vonMangoldt_sum_le (N V : ℕ) (w : ℕ → ℂ)
    (hw : ∀ n ∈ Finset.Ioc 0 N, ‖w n‖ ≤ 1) :
    ‖weightedSum (Finset.Ioc 0 N) w (shortPart V Λ)‖ ≤
      (V : ℝ) * Real.log V := by
  rw [weightedSum_shortPart]
  unfold weightedSum
  calc
    _ ≤ ∑ n ∈ Finset.Ioc 0 (min V N), ‖(Λ n : ℂ) * w n‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.Ioc 0 (min V N), Real.log V := by
      apply Finset.sum_le_sum
      intro n hn
      obtain ⟨hn0, hnVN⟩ := Finset.mem_Ioc.mp hn
      obtain ⟨hnV, hnN⟩ := le_min_iff.mp hnVN
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      calc
        Λ n * ‖w n‖ ≤ Λ n * 1 := mul_le_mul_of_nonneg_left
          (hw n (Finset.mem_Ioc.mpr ⟨hn0, hnN⟩)) ArithmeticFunction.vonMangoldt_nonneg
        _ ≤ Real.log n := by simpa using (ArithmeticFunction.vonMangoldt_le_log (n := n))
        _ ≤ Real.log V := Real.log_le_log (by exact_mod_cast hn0) (by exact_mod_cast hnV)
    _ = (min V N : ℕ) * Real.log V := by simp
    _ ≤ (V : ℝ) * Real.log V := mul_le_mul_of_nonneg_right
      (by exact_mod_cast min_le_left V N) (Real.log_natCast_nonneg V)

/-- The actual Type II term is a hyperbola with both short factors removed. -/
theorem typeII_eq_hyperbola (N U V : ℕ) (w : ℕ → ℂ) :
    weightedSum (Finset.Ioc 0 N) w (typeIICoefficient U * longPart V Λ) =
      ∑ d ∈ (hyperbola N).filter (fun d => U < d.1 ∧ V < d.2),
        (typeIICoefficient U d.1 : ℂ) * (Λ d.2 : ℂ) * w (d.1 * d.2) := by
  unfold weightedSum
  rw [← positive_interval N, sum_real_convolution_hyperbola, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hU : U < d.1
  · by_cases hV : V < d.2 <;> simp [hU, hV]
  · simp [hU, typeIICoefficient_eq_zero U d.1 (not_lt.mp hU)]

end Problem337.Vaughan

end

end OAI

-- Upstream module OAI.NumberTheory.EgyptianFractions.DivisorSquareMean

namespace OAI
/-!
# An elementary mean-square bound for the divisor function

The pointwise majorant `tau^2 ≤ zeta^4` and the elementary harmonic-sum
bound supply the coefficient energy used in finite Type-II estimates.
-/

noncomputable section

open scoped BigOperators ArithmeticFunction.zeta
open Finset ArithmeticFunction

namespace Problem337.DivisorSquareMean

lemma square_le_sigma_convolution_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (k + 1) ^ 2 ≤ (sigma 0 * sigma 0) (p ^ k) := by
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal (fun a b => sigma 0 a * sigma 0 b),
    Nat.sum_divisors_prime_pow hp]
  calc
    (k + 1) ^ 2 = ∑ i ∈ range (k + 1), (k + 1) := by simp [pow_two]
    _ ≤ ∑ i ∈ range (k + 1), sigma 0 (p ^ i) * sigma 0 (p ^ k / p ^ i) := by
      apply sum_le_sum
      intro i hi
      have hik : i ≤ k := by simpa using hi
      rw [Nat.pow_div hik hp.pos,
        sigma_zero_apply_prime_pow hp, sigma_zero_apply_prime_pow hp]
      have hsub : i + (k - i) = k := Nat.add_sub_of_le hik
      nlinarith

theorem card_divisors_sq_le_convolution (n : ℕ) :
    n.divisors.card ^ 2 ≤ (sigma 0 * sigma 0) n := by
  by_cases hn : n = 0
  · simp [hn]
  have hf : IsMultiplicative (sigma 0 * sigma 0) :=
    isMultiplicative_sigma.mul isMultiplicative_sigma
  rw [Nat.card_divisors hn, ← prod_pow,
    hf.multiplicative_factorization (sigma 0 * sigma 0) hn]
  change (∏ p ∈ n.primeFactors, (n.factorization p + 1) ^ 2) ≤
    ∏ p ∈ n.factorization.support, (sigma 0 * sigma 0) (p ^ n.factorization p)
  rw [Nat.support_factorization]
  exact prod_le_prod fun p hp =>
    square_le_sigma_convolution_prime_pow (Nat.prime_of_mem_primeFactors hp) _

theorem card_divisors_sq_le_zeta_four (n : ℕ) :
    n.divisors.card ^ 2 ≤ (ζ ^ 4) n := by
  have hs : sigma 0 = ζ * ζ := by
    rw [← zeta_mul_pow_eq_sigma, pow_zero_eq_zeta]
  convert card_divisors_sq_le_convolution n using 1
  rw [hs]
  congr 1
  ring

lemma real_harmonic_eq_sum (N : ℕ) :
    (harmonic N : ℝ) = ∑ n ∈ Ioc 0 N, (n : ℝ)⁻¹ := by
  have hset : Ioc 0 N = Icc 1 N := by
    ext n
    simp only [mem_Ioc, mem_Icc]
    omega
  simp [hset, harmonic_eq_sum_Icc]

lemma real_harmonic_nonneg (N : ℕ) : 0 ≤ (harmonic N : ℝ) := by
  rw [real_harmonic_eq_sum]
  positivity

lemma real_harmonic_mono {M N : ℕ} (h : M ≤ N) :
    (harmonic M : ℝ) ≤ (harmonic N : ℝ) := by
  rw [real_harmonic_eq_sum, real_harmonic_eq_sum]
  exact sum_le_sum_of_subset_of_nonneg (Ioc_subset_Ioc_right h)
    (fun _ _ _ => by positivity)

/-- The summatory `(k+1)`-fold divisor function costs at most `k` harmonic factors. -/
theorem sum_zeta_pow_le_harmonic (k N : ℕ) :
    (∑ n ∈ Ioc 0 N, (ζ ^ (k + 1)) n : ℕ) ≤
      (N : ℝ) * (harmonic N : ℝ) ^ k := by
  induction k generalizing N with
  | zero =>
    rw [Nat.zero_add, pow_one, sum_Ioc_zeta, pow_zero, mul_one]
  | succ k ih =>
    rw [show k + 1 + 1 = (k + 1) + 1 by omega, pow_succ',
      sum_Ioc_mul_eq_sum_sum]
    simp only [Nat.cast_sum, Nat.cast_mul]
    calc
      ∑ n ∈ Ioc 0 N, (ζ n : ℝ) *
          (∑ m ∈ Ioc 0 (N / n), ((ζ ^ (k + 1)) m : ℝ))
        ≤ ∑ n ∈ Ioc 0 N, ((N : ℝ) / n) * (harmonic N : ℝ) ^ k := by
          apply sum_le_sum
          intro n hn
          have hn0 : n ≠ 0 := (mem_Ioc.mp hn).1.ne'
          rw [zeta_apply_ne hn0, Nat.cast_one, one_mul]
          have hi := ih (N / n)
          simp only [Nat.cast_sum] at hi
          exact hi.trans (mul_le_mul Nat.cast_div_le
            (pow_le_pow_left₀ (real_harmonic_nonneg _) (real_harmonic_mono (Nat.div_le_self N n)) k)
            (pow_nonneg (real_harmonic_nonneg _) _) (by positivity))
      _ = (N : ℝ) * (harmonic N : ℝ) ^ (k + 1) := by
        simp_rw [div_eq_mul_inv, mul_assoc]
        rw [← mul_sum, ← sum_mul, ← real_harmonic_eq_sum, pow_succ]
        ring

/-- Sharp elementary harmonic form of the divisor mean-square bound. -/
theorem sum_card_divisors_sq_le_harmonic (N : ℕ) :
    (∑ n ∈ Ioc 0 N, (n.divisors.card : ℝ) ^ 2) ≤
      (N : ℝ) * (harmonic N : ℝ) ^ 3 := by
  calc
    (∑ n ∈ Ioc 0 N, (n.divisors.card : ℝ) ^ 2)
      ≤ (∑ n ∈ Ioc 0 N, (ζ ^ 4) n : ℕ) := by
        rw [Nat.cast_sum]
        apply sum_le_sum
        intro n hn
        have h : ((n.divisors.card ^ 2 : ℕ) : ℝ) ≤ (((ζ ^ 4) n : ℕ) : ℝ) :=
          Nat.cast_le.mpr (card_divisors_sq_le_zeta_four n)
        simpa only [Nat.cast_pow] using h
    _ ≤ (N : ℝ) * (harmonic N : ℝ) ^ 3 := by
      have h := sum_zeta_pow_le_harmonic 3 N
      simp only [show (3 : ℕ) + 1 = 4 from rfl] at h
      exact h

/-- The classical elementary `N (1 + log N)^3` divisor mean square, including `N = 0`. -/
theorem sum_card_divisors_sq_le_log (N : ℕ) :
    (∑ n ∈ Ioc 0 N, (n.divisors.card : ℝ) ^ 2) ≤
      (N : ℝ) * (1 + Real.log N) ^ 3 := by
  exact (sum_card_divisors_sq_le_harmonic N).trans
    (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (real_harmonic_nonneg N) (harmonic_le_one_add_log N) 3)
      (Nat.cast_nonneg N))

/-- A finite subinterval/subset version, allowing a uniform coefficient multiplier. -/
theorem sum_norm_sq_le_log_of_subset {E : Type*} [SeminormedAddCommGroup E]
    (b : ℕ → E) (T : Finset ℕ) (N : ℕ) (B : ℝ)
    (hT : T ⊆ Ioc 0 N)
    (hb : ∀ n ∈ T, ‖b n‖ ≤ B * (n.divisors.card : ℝ)) :
    (∑ n ∈ T, ‖b n‖ ^ 2) ≤ B ^ 2 * ((N : ℝ) * (1 + Real.log N) ^ 3) := by
  calc
    (∑ n ∈ T, ‖b n‖ ^ 2)
      ≤ ∑ n ∈ T, (B * (n.divisors.card : ℝ)) ^ 2 :=
        sum_le_sum fun n hn => pow_le_pow_left₀ (norm_nonneg _) (hb n hn) 2
    _ = B ^ 2 * ∑ n ∈ T, (n.divisors.card : ℝ) ^ 2 := by
      simp_rw [mul_pow]
      rw [mul_sum]
    _ ≤ B ^ 2 * ∑ n ∈ Ioc 0 N, (n.divisors.card : ℝ) ^ 2 := by
      exact mul_le_mul_of_nonneg_left
        (sum_le_sum_of_subset_of_nonneg hT (fun _ _ _ => sq_nonneg _)) (sq_nonneg B)
    _ ≤ B ^ 2 * ((N : ℝ) * (1 + Real.log N) ^ 3) :=
      mul_le_mul_of_nonneg_left (sum_card_divisors_sq_le_log N) (sq_nonneg B)

end Problem337.DivisorSquareMean

end

end OAI

-- Upstream module OAI.NumberTheory.EgyptianFractions.VaughanDyadicDecomposition

namespace OAI
noncomputable section
open scoped BigOperators ArithmeticFunction ArithmeticFunction.Moebius ArithmeticFunction.zeta
open Finset

namespace Problem337.Vaughan

lemma long_hyperbola_eq_filtered_product (N U V : ℕ) :
    (hyperbola N).filter (fun d => U < d.1 ∧ V < d.2) =
      (Ioc U N ×ˢ Ioc V N).filter (fun d => d.1 * d.2 ≤ N) := by
  ext d
  rcases d with ⟨a, b⟩
  simp only [mem_filter, mem_hyperbola, mem_product, mem_Ioc]
  constructor
  · rintro ⟨⟨ha, hb, hp⟩, hU, hV⟩
    exact ⟨⟨⟨hU, (Nat.le_mul_of_pos_right a hb).trans hp⟩,
      ⟨hV, (Nat.le_mul_of_pos_left b ha).trans hp⟩⟩, hp⟩
  · rintro ⟨⟨⟨hU, ha⟩, ⟨hV, hb⟩⟩, hp⟩
    exact ⟨⟨by omega, by omega, hp⟩, hU, hV⟩

/-- The dyadic block with the actual arithmetic coefficients in Vaughan's identity. -/
def typeIIBlock (N U V j : ℕ) (w : ℕ → ℂ) : ℂ :=
  VaughanDyadic.block N U V j
    (fun m n => (typeIICoefficient U m : ℂ) * (Λ n : ℂ) * w (m * n))

/-- No arithmetic coefficient or hyperbolic cutoff is lost in dyadic decomposition. -/
theorem typeII_eq_sum_dyadic_blocks (N U V : ℕ) (w : ℕ → ℂ) :
    weightedSum (Ioc 0 N) w (typeIICoefficient U * longPart V Λ) =
      ∑ j ∈ range (Nat.log 2 N + 1), typeIIBlock N U V j w := by
  rw [typeII_eq_hyperbola, long_hyperbola_eq_filtered_product]
  exact VaughanDyadic.sum_filtered_product_eq_sum_blocks (E := ℂ) N U V
    (fun m n => (typeIICoefficient U m : ℂ) * (Λ n : ℂ) * w (m * n))

/-- A genuine uniform block bound has only a logarithmic decomposition cost. -/
theorem norm_typeII_le_dyadic_log_budget (N U V : ℕ) (w : ℕ → ℂ)
    (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ j < Nat.log 2 N + 1, ‖typeIIBlock N U V j w‖ ≤ B) :
    ‖weightedSum (Ioc 0 N) w (typeIICoefficient U * longPart V Λ)‖ ≤
      (1 + Real.log N / Real.log 2) * B := by
  let F : ℕ → ℕ → ℂ :=
    fun m n => (typeIICoefficient U m : ℂ) * (Λ n : ℂ) * w (m * n)
  have he : weightedSum (Ioc 0 N) w (typeIICoefficient U * longPart V Λ) =
      ∑ m ∈ Ioc U N, ∑ n ∈ Ioc V (N / m), F m n := by
    rw [typeII_eq_sum_dyadic_blocks, VaughanDyadic.sum_hyperbola_eq_sum_blocks]
    rfl
  rw [he]
  exact VaughanDyadic.norm_hyperbola_le_log_budget N U V F B hB0 hB

/-- Sharp unconditional row energy for the actual Type II coefficient in a dyadic shell. -/
theorem typeII_shell_energy_le (N U j : ℕ) :
    (∑ m ∈ VaughanDyadic.shell U N j, ‖(typeIICoefficient U m : ℂ)‖ ^ 2) ≤
      (2 ^ (j + 1) : ℕ) * (1 + Real.log (2 ^ (j + 1) : ℕ)) ^ 3 := by
  have hT : VaughanDyadic.shell U N j ⊆ Ioc 0 (2 ^ (j + 1)) := by
    intro m hm
    have h := VaughanDyadic.mem_shell.mp hm
    exact mem_Ioc.mpr ⟨lt_of_le_of_lt (Nat.zero_le U) h.1, h.2.2.2.le⟩
  have h := DivisorSquareMean.sum_norm_sq_le_log_of_subset
    (fun m => (typeIICoefficient U m : ℂ)) (VaughanDyadic.shell U N j)
    (2 ^ (j + 1)) 1 hT (by
      intro m hm
      simpa only [Complex.norm_real, Real.norm_eq_abs, one_mul] using
        abs_typeIICoefficient_le_divisors_card U m)
  simpa only [one_pow, one_mul] using h

end Problem337.Vaughan

end

end OAI

-- Upstream module OAI.NumberTheory.EgyptianFractions.HyperbolaCorrelation

namespace OAI
noncomputable section
open scoped BigOperators
open ComplexConjugate

namespace Problem337.HyperbolaCorrelation

/-- The common support of two columns cut off by a product bound. -/
theorem product_support_iff (X m n₁ n₂ : ℕ) (hn : 0 < max n₁ n₂) :
    (m * n₁ ≤ X ∧ m * n₂ ≤ X) ↔ m ≤ X / max n₁ n₂ := by
  rw [Nat.le_div_iff_mul_le hn, mul_max, max_le_iff]

/-- Intersecting two hyperbolic columns leaves an ordinary integer interval.
Empty intervals and a zero value of one of the two column indices are allowed. -/
theorem filter_common_support (X L U n₁ n₂ : ℕ) (hn : 0 < max n₁ n₂) :
    (Finset.Icc L U).filter (fun m => m * n₁ ≤ X ∧ m * n₂ ≤ X) =
      Finset.Icc L (min U (X / max n₁ n₂)) := by
  ext m
  simp only [Finset.mem_filter, Finset.mem_Icc, product_support_iff X m n₁ n₂ hn,
    le_min_iff]
  tauto

/-- Exact correlation identity for arbitrary complex hyperbolic columns. -/
theorem cutoff_correlation (X L U n₁ n₂ : ℕ) (hn : 0 < max n₁ n₂)
    (f g : ℕ → ℂ) :
    (∑ m ∈ Finset.Icc L U,
      (if m * n₁ ≤ X then f m else 0) *
        conj (if m * n₂ ≤ X then g m else 0)) =
      ∑ m ∈ Finset.Icc L (min U (X / max n₁ n₂)), f m * conj (g m) := by
  rw [← filter_common_support X L U n₁ n₂ hn, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro m hm
  by_cases h₁ : m * n₁ ≤ X <;> by_cases h₂ : m * n₂ ≤ X <;> simp [h₁, h₂]

/-- The standard real-frequency complex phase. -/
def phase (x : ℝ) : ℂ := Complex.exp ((2 * Real.pi * x : ℝ) * Complex.I)

@[simp] theorem norm_phase (x : ℝ) : ‖phase x‖ = 1 := by
  simp [phase, Complex.norm_exp]

theorem phase_sub (x y : ℝ) : phase (x - y) = phase x * conj (phase y) := by
  simp only [phase, ← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  push_cast
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  ring

/-- A column of a bilinear exponential sum with its actual hyperbolic support. -/
def column (α : ℝ) (X n m : ℕ) : ℂ :=
  if m * n ≤ X then phase (α * (m : ℝ) * (n : ℝ)) else 0

/-- The off-diagonal correlation is a geometric exponential sum on one interval,
not a sum over an arbitrary subset. Differences are taken in `ℝ`, so negative
frequencies are retained rather than truncated by natural subtraction. -/
theorem column_correlation (α : ℝ) (X L U n₁ n₂ : ℕ)
    (hn : 0 < max n₁ n₂) :
    (∑ m ∈ Finset.Icc L U, column α X n₁ m * conj (column α X n₂ m)) =
      ∑ m ∈ Finset.Icc L (min U (X / max n₁ n₂)),
        phase (α * (m : ℝ) * ((n₁ : ℝ) - (n₂ : ℝ))) := by
  unfold column
  rw [cutoff_correlation X L U n₁ n₂ hn]
  apply Finset.sum_congr rfl
  intro m hm
  rw [← phase_sub]
  congr 1
  ring

end Problem337.HyperbolaCorrelation

end

end OAI

-- Upstream module OAI.NumberTheory.EgyptianFractions.VaughanBilinear

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337.VaughanBilinear

/-- The exact correlation expansion of a weighted finite bilinear energy.
No distinctness or unit-modulus assumption on the phase is needed. -/
theorem energy_identity {α β : Type*} (s : Finset α) (t : Finset β)
    (b : β → ℂ) (z : α → β → ℂ) :
    ((∑ m ∈ s, ‖∑ n ∈ t, b n * z m n‖ ^ 2 : ℝ) : ℂ) =
      ∑ n ∈ t, ∑ k ∈ t, b n * (starRingEnd ℂ) (b k) *
        ∑ m ∈ s, z m n * (starRingEnd ℂ) (z m k) := by
  classical
  have hpoint (m : α) :
      (‖∑ n ∈ t, b n * z m n‖ ^ 2 : ℂ) =
        ∑ n ∈ t, ∑ k ∈ t,
          b n * (starRingEnd ℂ) (b k) *
            (z m n * (starRingEnd ℂ) (z m k)) := by
    rw [← Complex.mul_conj']
    simp only [map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro n hn
    apply Finset.sum_congr rfl
    intro k hk
    ring
  push_cast
  simp_rw [hpoint]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mul_sum]

/-- Bounding a bilinear energy by absolute correlations retains the
arithmetic cancellation in the first variable. -/
theorem energy_le_correlations {α β : Type*} (s : Finset α) (t : Finset β)
    (b : β → ℂ) (z : α → β → ℂ) :
    (∑ m ∈ s, ‖∑ n ∈ t, b n * z m n‖ ^ 2) ≤
      ∑ n ∈ t, ∑ k ∈ t, ‖b n‖ * ‖b k‖ *
        ‖∑ m ∈ s, z m n * (starRingEnd ℂ) (z m k)‖ := by
  have h := congrArg Complex.re (energy_identity s t b z)
  simp only [Complex.ofReal_re, Complex.re_sum] at h
  rw [h]
  apply Finset.sum_le_sum
  intro n hn
  apply Finset.sum_le_sum
  intro k hk
  calc
    _ ≤ ‖b n * (starRingEnd ℂ) (b k) *
        ∑ m ∈ s, z m n * (starRingEnd ℂ) (z m k)‖ := Complex.re_le_norm _
    _ = _ := by simp only [norm_mul, Complex.norm_conj]

/-- Finite Type-II Cauchy--Schwarz, with the full correlation sum explicit.
This is an unconditional algebraic bound, not a minor-arc hypothesis. -/
theorem norm_bilinear_sq_le {α β : Type*} (s : Finset α) (t : Finset β)
    (a : α → ℂ) (b : β → ℂ) (z : α → β → ℂ) :
    ‖∑ m ∈ s, a m * ∑ n ∈ t, b n * z m n‖ ^ 2 ≤
      (∑ m ∈ s, ‖a m‖ ^ 2) *
        (∑ n ∈ t, ∑ k ∈ t, ‖b n‖ * ‖b k‖ *
          ‖∑ m ∈ s, z m n * (starRingEnd ℂ) (z m k)‖) := by
  calc
    _ ≤ (∑ m ∈ s, ‖a m‖ * ‖∑ n ∈ t, b n * z m n‖) ^ 2 := by
      apply pow_le_pow_left₀ (norm_nonneg _)
      simpa only [norm_mul] using
        norm_sum_le s (fun m => a m * ∑ n ∈ t, b n * z m n)
    _ ≤ (∑ m ∈ s, ‖a m‖ ^ 2) *
        ∑ m ∈ s, ‖∑ n ∈ t, b n * z m n‖ ^ 2 :=
      Finset.sum_mul_sq_le_sq_mul_sq s _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (energy_le_correlations s t b z)
      (Finset.sum_nonneg fun _ _ => sq_nonneg _)

/-- The standard real additive phase, with the `2π` convention. -/
def phase (x : ℝ) : ℂ := Real.fourierChar x

@[simp] theorem norm_phase (x : ℝ) : ‖phase x‖ = 1 := Circle.norm_coe _

theorem phase_mul_conj (x y : ℝ) :
    phase x * (starRingEnd ℂ) (phase y) = phase (x - y) := by
  unfold phase
  rw [Circle.starRingEnd_addChar, ← Circle.coe_mul, ← AddChar.map_add_eq_mul]
  congr 2

theorem phase_nat_mul (x : ℝ) (n : ℕ) : phase (x * n) = phase x ^ n := by
  unfold phase
  rw [mul_comm, ← nsmul_eq_mul, AddChar.map_nsmul_eq_pow, Circle.coe_pow]

/-- An exact geometric cancellation bound in a form valid even at resonance. -/
theorem phase_sum_mul_bound (x : ℝ) (M : ℕ) :
    ‖∑ m ∈ Finset.range M, phase (x * m)‖ * ‖1 - phase x‖ ≤ 2 := by
  simp_rw [phase_nat_mul]
  rw [← norm_mul, geom_sum_mul_neg]
  calc
    ‖1 - phase x ^ M‖ ≤ ‖(1 : ℂ)‖ + ‖phase x ^ M‖ := norm_sub_le _ _
    _ = 2 := by simp; norm_num

/-- The usual geometric sum bound away from resonance. -/
theorem phase_sum_le_min (x : ℝ) (M : ℕ) (hx : phase x ≠ 1) :
    ‖∑ m ∈ Finset.range M, phase (x * m)‖ ≤
      min (M : ℝ) (2 / ‖1 - phase x‖) := by
  apply le_min
  · calc
      _ ≤ ∑ m ∈ Finset.range M, ‖phase (x * m)‖ := norm_sum_le _ _
      _ = M := by simp
  · have hpos : 0 < ‖1 - phase x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hx.symm)
    exact (le_div_iff₀ hpos).mpr (phase_sum_mul_bound x M)

/-- A total geometric majorant. Resonant frequencies use the trivial bound;
the definition never interprets division by zero as cancellation. -/
def geometricBound (M : ℕ) (x : ℝ) : ℝ :=
  if phase x = 1 then M else min (M : ℝ) (2 / ‖1 - phase x‖)

theorem phase_sum_le_geometricBound (x : ℝ) (M : ℕ) :
    ‖∑ m ∈ Finset.range M, phase (x * m)‖ ≤ geometricBound M x := by
  unfold geometricBound
  split_ifs with hx
  · simp_rw [phase_nat_mul, hx]
    simp
  · exact phase_sum_le_min x M hx

/-- A finite real Schur bound, proved by symmetrizing `2xy ≤ x²+y²`.
The coefficients need not be nonnegative. -/
theorem symmetric_weighted_sum_le {β : Type*} (t : Finset β)
    (f : β → ℝ) (K : β → β → ℝ)
    (hK : ∀ n ∈ t, ∀ k ∈ t, 0 ≤ K n k)
    (hsym : ∀ n ∈ t, ∀ k ∈ t, K n k = K k n) :
    (∑ n ∈ t, ∑ k ∈ t, f n * f k * K n k) ≤
      ∑ n ∈ t, f n ^ 2 * ∑ k ∈ t, K n k := by
  have hfirst : (∑ n ∈ t, ∑ k ∈ t, f n ^ 2 * K n k) =
      ∑ n ∈ t, f n ^ 2 * ∑ k ∈ t, K n k := by
    simp only [Finset.mul_sum]
  have hsecond : (∑ n ∈ t, ∑ k ∈ t, f k ^ 2 * K n k) =
      ∑ n ∈ t, f n ^ 2 * ∑ k ∈ t, K n k := by
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    apply Finset.sum_congr rfl
    intro k hk
    rw [hsym k hk n hn]
  calc
    _ ≤ ∑ n ∈ t, ∑ k ∈ t,
        (f n ^ 2 * K n k + f k ^ 2 * K n k) / 2 := by
      apply Finset.sum_le_sum
      intro n hn
      apply Finset.sum_le_sum
      intro k hk
      nlinarith [mul_nonneg (sq_nonneg (f n - f k)) (hK n hn k hk)]
    _ = ((∑ n ∈ t, ∑ k ∈ t, f n ^ 2 * K n k) +
        (∑ n ∈ t, ∑ k ∈ t, f k ^ 2 * K n k)) / 2 := by
      simp only [add_div, Finset.sum_div, Finset.sum_add_distrib]
    _ = _ := by rw [hfirst, hsecond]; ring

/-- Reversing a correlation conjugates it, hence preserves its norm. -/
theorem correlation_norm_symm {α β : Type*} (s : Finset α)
    (z : α → β → ℂ) (n k : β) :
    ‖∑ m ∈ s, z m n * (starRingEnd ℂ) (z m k)‖ =
      ‖∑ m ∈ s, z m k * (starRingEnd ℂ) (z m n)‖ := by
  have hc : (∑ m ∈ s, z m n * (starRingEnd ℂ) (z m k)) =
      (starRingEnd ℂ) (∑ m ∈ s, z m k * (starRingEnd ℂ) (z m n)) := by
    simp only [map_sum, map_mul, starRingEnd_self_apply]
    apply Finset.sum_congr rfl
    intro m hm
    ring
  rw [hc, Complex.norm_conj]

/-- Type-II energy bound using an absolute correlation row bound. Unlike the
bounded-coefficient version, this retains both coefficient squared sums and
therefore applies directly to divisor-coefficient second-moment estimates. -/
theorem norm_bilinear_sq_le_energy {α β : Type*} (s : Finset α) (t : Finset β)
    (a : α → ℂ) (b : β → ℂ) (z : α → β → ℂ) (C : ℝ)
    (hrow : ∀ n ∈ t,
      (∑ k ∈ t, ‖∑ m ∈ s, z m n * (starRingEnd ℂ) (z m k)‖) ≤ C) :
    ‖∑ m ∈ s, a m * ∑ n ∈ t, b n * z m n‖ ^ 2 ≤
      (∑ m ∈ s, ‖a m‖ ^ 2) * C * (∑ n ∈ t, ‖b n‖ ^ 2) := by
  have hweight := symmetric_weighted_sum_le t (fun n => ‖b n‖)
    (fun n k => ‖∑ m ∈ s, z m n * (starRingEnd ℂ) (z m k)‖)
    (fun _ _ _ _ => norm_nonneg _)
    (fun n _ k _ => correlation_norm_symm s z n k)
  have hbound :
      (∑ n ∈ t, ∑ k ∈ t, ‖b n‖ * ‖b k‖ *
        ‖∑ m ∈ s, z m n * (starRingEnd ℂ) (z m k)‖) ≤
      C * ∑ n ∈ t, ‖b n‖ ^ 2 := by
    refine hweight.trans ?_
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n hn
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hrow n hn) (sq_nonneg ‖b n‖)
  calc
    _ ≤ _ := norm_bilinear_sq_le s t a b z
    _ ≤ (∑ m ∈ s, ‖a m‖ ^ 2) * (C * ∑ n ∈ t, ‖b n‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hbound (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    _ = _ := by ring

end Problem337.VaughanBilinear

end

end OAI

-- Upstream module OAI.NumberTheory.EgyptianFractions.HyperbolaTypeII

namespace OAI
noncomputable section
open scoped BigOperators
open ComplexConjugate

namespace Problem337.HyperbolaCorrelation

lemma phase_eq_vaughan (x : ℝ) : phase x = VaughanBilinear.phase x := rfl

lemma phase_add (x y : ℝ) : phase (x + y) = phase x * phase y := by
  simp only [phase, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Translation of an integer interval does not affect its geometric-sum bound. -/
theorem phase_sum_Icc_le (x : ℝ) (L U : ℕ) :
    ‖∑ m ∈ Finset.Icc L U, phase (x * (m : ℝ))‖ ≤
      VaughanBilinear.geometricBound (U + 1 - L) x := by
  have hI : Finset.Icc L U = Finset.Ico L (U + 1) := by
    ext m
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [hI, Finset.sum_Ico_eq_sum_range]
  have hsum : (∑ m ∈ Finset.range (U + 1 - L), phase (x * ((L + m : ℕ) : ℝ))) =
      phase (x * L) * ∑ m ∈ Finset.range (U + 1 - L), phase (x * (m : ℝ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    rw [Nat.cast_add, mul_add, phase_add]
  rw [hsum, norm_mul, norm_phase, one_mul]
  exact VaughanBilinear.phase_sum_le_geometricBound x (U + 1 - L)

lemma geometricBound_mono {M N : ℕ} (hMN : M ≤ N) (x : ℝ) :
    VaughanBilinear.geometricBound M x ≤ VaughanBilinear.geometricBound N x := by
  unfold VaughanBilinear.geometricBound
  split_ifs
  · exact_mod_cast hMN
  · exact min_le_min_right _ (by exact_mod_cast hMN)

/-- A hyperbolic correlation admits the same geometric majorant as a full
interval of rows. The moving endpoint introduces no additional loss. -/
theorem column_correlation_le (α : ℝ) (X L U n₁ n₂ : ℕ)
    (hn : 0 < max n₁ n₂) :
    ‖∑ m ∈ Finset.Icc L U, column α X n₁ m * conj (column α X n₂ m)‖ ≤
      VaughanBilinear.geometricBound (U + 1 - L) (α * ((n₁ : ℝ) - (n₂ : ℝ))) := by
  rw [column_correlation α X L U n₁ n₂ hn]
  have heq : (fun m : ℕ => phase (α * (m : ℝ) * ((n₁ : ℝ) - (n₂ : ℝ)))) =
      (fun m : ℕ => phase ((α * ((n₁ : ℝ) - (n₂ : ℝ))) * (m : ℝ))) := by
    funext m
    congr 1
    ring
  simp_rw [heq]
  exact (phase_sum_Icc_le _ L (min U (X / max n₁ n₂))).trans
    (geometricBound_mono (by omega) _)

end Problem337.HyperbolaCorrelation

end

end OAI

-- Upstream module OAI.NumberTheory.EgyptianFractions.GeometricCharacterBound

namespace OAI
noncomputable section

open scoped BigOperators

namespace Problem337

/-- Geometric cancellation on the complex unit circle. -/
theorem norm_geometric_sum_le_two_div {z : ℂ} (hz : ‖z‖ = 1) (hne : z ≠ 1)
    (N : ℕ) : ‖∑ j ∈ Finset.range N, z ^ j‖ ≤ 2 / ‖z - 1‖ := by
  rw [geom_sum_eq hne, norm_div]
  apply div_le_div_of_nonneg_right _ (norm_nonneg _)
  calc
    ‖z ^ N - 1‖ ≤ ‖z ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by norm_num [norm_pow, hz]

/-- The elementary peak bound for a geometric kernel. -/
theorem norm_geometric_sum_le_card {z : ℂ} (hz : ‖z‖ = 1) (N : ℕ) :
    ‖∑ j ∈ Finset.range N, z ^ j‖ ≤ (N : ℝ) := by
  calc
    ‖∑ j ∈ Finset.range N, z ^ j‖ ≤ ∑ j ∈ Finset.range N, ‖z ^ j‖ := norm_sum_le _ _
    _ = (N : ℝ) := by simp [norm_pow, hz]

/-- The chord distance for a phase of period one. -/
theorem norm_exp_phase_sub_one (x : ℝ) :
    ‖Complex.exp (Complex.I * (2 * Real.pi * x : ℝ)) - 1‖ =
      2 * |Real.sin (Real.pi * x)| := by
  rw [Complex.norm_exp_I_mul_ofReal_sub_one]
  have heq : 2 * Real.pi * x / 2 = Real.pi * x := by ring
  rw [heq, Real.norm_eq_abs, abs_mul]
  norm_num

/-- Geometric cancellation expressed directly in terms of the phase sine. -/
theorem norm_geometric_phase_sum_le {x : ℝ} (hx : Real.sin (Real.pi * x) ≠ 0)
    (N : ℕ) :
    ‖∑ j ∈ Finset.range N, (Complex.exp (Complex.I * (2 * Real.pi * x : ℝ))) ^ j‖ ≤
      1 / |Real.sin (Real.pi * x)| := by
  have habs : 0 < |Real.sin (Real.pi * x)| := abs_pos.2 hx
  have hne : Complex.exp (Complex.I * (2 * Real.pi * x : ℝ)) ≠ 1 := by
    intro h
    have hn := norm_exp_phase_sub_one x
    rw [h, sub_self, norm_zero] at hn
    linarith
  have hbound := norm_geometric_sum_le_two_div
    (Complex.norm_exp_I_mul_ofReal (2 * Real.pi * x)) hne N
  rw [norm_exp_phase_sub_one] at hbound
  convert hbound using 1
  field_simp

/-- Uniform lower bound for the sine away from both ends of a period. -/
theorem sin_pi_mul_lower_on_middle {δ x : ℝ} (hδ : 0 < δ)
    (hleft : δ ≤ x) (hright : x ≤ 1 - δ) :
    2 * δ ≤ Real.sin (Real.pi * x) := by
  have hx0 : 0 ≤ x := le_trans hδ.le hleft
  have hx1 : 0 ≤ 1 - x := by linarith
  by_cases hx : x ≤ 1 / 2
  · have hs := Real.mul_le_sin (x := Real.pi * x)
      (mul_nonneg Real.pi_pos.le hx0) (by nlinarith [Real.pi_pos])
    have heq : 2 / Real.pi * (Real.pi * x) = 2 * x := by field_simp
    rw [heq] at hs
    linarith
  · have hs := Real.mul_le_sin (x := Real.pi * (1 - x))
      (mul_nonneg Real.pi_pos.le hx1)
      (by nlinarith [Real.pi_pos])
    have heq : 2 / Real.pi * (Real.pi * (1 - x)) = 2 * (1 - x) := by field_simp
    rw [heq, show Real.pi * (1 - x) = Real.pi - Real.pi * x by ring,
      Real.sin_pi_sub] at hs
    linarith

end Problem337

end

end OAI

-- Upstream module OAI.NumberTheory.EgyptianFractions.RationalPhaseSpacing

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337.RationalPhaseSpacing

/-- A reduced rational approximation with error at most `q⁻²` separates
frequencies whose index difference has absolute value at most `q/2`.
The estimate is uniform over every possible nearest integer. -/
theorem separation_of_rational_approximation
    (α : ℝ) (a : ℤ) (q : ℕ) (hq : 0 < q)
    (hcop : IsCoprime a (q : ℤ))
    (happrox : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (h : ℤ) (hne : h ≠ 0) (hsmall : 2 * |h| ≤ (q : ℤ)) (k : ℤ) :
    1 / (2 * (q : ℝ)) ≤ |α * (h : ℝ) - k| := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hhpos : (0 : ℤ) < |h| := abs_pos.mpr hne
  have hnotdvd : ¬ (q : ℤ) ∣ h := by
    intro hd
    have hle := Int.le_of_dvd hhpos ((dvd_abs (q : ℤ) h).mpr hd)
    omega
  have hnonzero : a * h - k * (q : ℤ) ≠ 0 := by
    intro hz
    apply hnotdvd
    apply hcop.symm.dvd_of_dvd_mul_left
    refine ⟨k, ?_⟩
    linear_combination hz
  have hinteger : (1 : ℝ) ≤ |(a : ℝ) * h - (k : ℝ) * q| := by
    exact_mod_cast Int.one_le_abs hnonzero
  have hsmallR : (2 : ℝ) * |(h : ℝ)| ≤ q := by exact_mod_cast hsmall
  have herr : (q : ℝ) * |α - (a : ℝ) / q| * |(h : ℝ)| ≤ 1 / 2 := by
    have hb := (le_div_iff₀ (sq_pos_of_pos hqR)).mp happrox
    have hc := mul_le_mul_of_nonneg_left hsmallR
      (mul_nonneg hqR.le (abs_nonneg (α - (a : ℝ) / q)))
    nlinarith
  have hid : (a : ℝ) * h - (k : ℝ) * q =
      (q : ℝ) * (α * h - k) - (q : ℝ) * (α - (a : ℝ) / q) * h := by
    field_simp
    ring
  have htri : |(a : ℝ) * h - (k : ℝ) * q| ≤
      (q : ℝ) * |α * h - k| + (q : ℝ) * |α - (a : ℝ) / q| * |(h : ℝ)| := by
    rw [hid]
    calc
      _ ≤ |(q : ℝ) * (α * h - k)| + |(q : ℝ) * (α - (a : ℝ) / q) * h| :=
        abs_sub _ _
      _ = _ := by simp only [abs_mul, abs_of_pos hqR]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * q)).mpr
  nlinarith

/-- Fractional parts at two nearby distinct integer indices are separated
under the same reduced rational approximation. -/
theorem fract_separation
    (α : ℝ) (a : ℤ) (q : ℕ) (hq : 0 < q)
    (hcop : IsCoprime a (q : ℤ))
    (happrox : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (m n : ℤ) (hne : m ≠ n) (hsmall : 2 * |m - n| ≤ (q : ℤ)) :
    1 / (2 * (q : ℝ)) ≤ |Int.fract (α * m) - Int.fract (α * n)| := by
  have hs := separation_of_rational_approximation α a q hq hcop happrox
    (m - n) (sub_ne_zero.mpr hne) hsmall (⌊α * m⌋ - ⌊α * n⌋)
  simpa only [Int.fract, Int.cast_sub, mul_sub, sub_sub_sub_comm] using hs

/-- A canonical finite bin index for the phase of an integer. -/
def phaseBin (q : ℕ) (α : ℝ) (n : ℤ) : ℕ :=
  ⌊2 * (q : ℝ) * Int.fract (α * n)⌋₊

theorem phaseBin_lt (q : ℕ) (hq : 0 < q) (α : ℝ) (n : ℤ) :
    phaseBin q α n < 2 * q := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  apply (Nat.floor_lt (mul_nonneg (by positivity) (Int.fract_nonneg (α * (n : ℝ))))).mpr
  push_cast
  nlinarith [Int.fract_lt_one (α * n)]

/-- Bin encoding preserves the multiplicity of indices in every short block:
no two indices have the same bin. -/
theorem phaseBin_injOn
    (α : ℝ) (a : ℤ) (q : ℕ) (hq : 0 < q)
    (hcop : IsCoprime a (q : ℤ))
    (happrox : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (A : Finset ℤ) (hspan : ∀ m ∈ A, ∀ n ∈ A, 2 * |m - n| ≤ (q : ℤ)) :
    Set.InjOn (phaseBin q α) A := by
  intro m hm n hn heq
  by_contra hne
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hs := fract_separation α a q hq hcop happrox m n hne (hspan m hm n hn)
  have hmlo := Nat.floor_le (show 0 ≤ 2 * (q : ℝ) * Int.fract (α * m) from mul_nonneg (by positivity) (Int.fract_nonneg _))
  have hnlo := Nat.floor_le (show 0 ≤ 2 * (q : ℝ) * Int.fract (α * n) from mul_nonneg (by positivity) (Int.fract_nonneg _))
  have hmhi := Nat.lt_floor_add_one (2 * (q : ℝ) * Int.fract (α * m))
  have hnhi := Nat.lt_floor_add_one (2 * (q : ℝ) * Int.fract (α * n))
  change phaseBin q α m = phaseBin q α n at heq
  change (phaseBin q α m : ℝ) ≤ _ at hmlo
  change (phaseBin q α n : ℝ) ≤ _ at hnlo
  change _ < (phaseBin q α m : ℝ) + 1 at hmhi
  change _ < (phaseBin q α n : ℝ) + 1 at hnhi
  rw [heq] at hmlo hmhi
  have hlt : |Int.fract (α * m) - Int.fract (α * n)| < 1 / (2 * (q : ℝ)) := by
    apply abs_sub_lt_iff.mpr
    constructor
    · apply (lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * q)).mpr
      nlinarith
    · apply (lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * q)).mpr
      nlinarith
  exact (not_lt_of_ge hs) hlt

/-- A reciprocal truncated at `Y`, with its correct value at the singular
point. The special value is needed for geometric exponential sums. -/
def truncatedInv (Y x : ℝ) : ℝ := if x = 0 then Y else min Y (1 / x)

theorem truncatedInv_nonneg {Y x : ℝ} (hY : 0 ≤ Y) (hx : 0 ≤ x) :
    0 ≤ truncatedInv Y x := by
  unfold truncatedInv
  split_ifs
  · exact hY
  · exact le_min hY (one_div_nonneg.mpr hx)

theorem truncatedInv_le_cap (Y x : ℝ) : truncatedInv Y x ≤ Y := by
  unfold truncatedInv
  split_ifs
  · exact le_rfl
  · exact min_le_left _ _

/-- Bin majorant for the one-sided reciprocal distance. -/
def binWeight (H : ℕ) (Y : ℝ) (j : ℕ) : ℝ :=
  if j = 0 then Y else (H : ℝ) / j

theorem binWeight_nonneg {H j : ℕ} {Y : ℝ} (hY : 0 ≤ Y) :
    0 ≤ binWeight H Y j := by
  unfold binWeight
  split_ifs
  · exact hY
  · positivity

theorem truncatedInv_fract_le_binWeight (q : ℕ) (hq : 0 < q)
    (Y α : ℝ) (n : ℤ) :
    truncatedInv Y (Int.fract (α * n)) ≤ binWeight (2 * q) Y (phaseBin q α n) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  by_cases hj : phaseBin q α n = 0
  · simpa [binWeight, hj] using truncatedInv_le_cap Y (Int.fract (α * n))
  · have hjpos : (0 : ℝ) < phaseBin q α n := by exact_mod_cast Nat.pos_of_ne_zero hj
    have hlo := Nat.floor_le (show 0 ≤ 2 * (q : ℝ) * Int.fract (α * n)
      from mul_nonneg (by positivity) (Int.fract_nonneg _))
    change (phaseBin q α n : ℝ) ≤ _ at hlo
    have hxpos : 0 < Int.fract (α * n) := by nlinarith [Int.fract_nonneg (α * (n : ℝ))]
    rw [binWeight, ite_eq_right hj, truncatedInv, ite_eq_right (ne_of_gt hxpos)]
    apply (min_le_right _ _).trans
    apply (div_le_div_iff₀ hxpos hjpos).mpr
    push_cast
    simpa using hlo

/-- Summing the bin majorants costs one singular term and a harmonic sum. -/
theorem sum_binWeight_le (H : ℕ) (hH : 0 < H) (Y : ℝ) :
    (∑ j ∈ Finset.range H, binWeight H Y j) ≤
      Y + (H : ℝ) * (1 + Real.log (H : ℝ)) := by
  have hterm (j : ℕ) : binWeight H Y j =
      (if j = 0 then Y else 0) + (H : ℝ) * (1 / (j : ℝ)) := by
    by_cases hj : j = 0
    · simp [binWeight, hj]
    · simp [binWeight, hj, div_eq_mul_inv]
  have hsum : (∑ j ∈ Finset.range H, binWeight H Y j) =
      Y + (H : ℝ) * ∑ j ∈ Finset.range H, (1 / (j : ℝ)) := by
    simp_rw [hterm]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    simp [hH]
  have hrecip : (∑ j ∈ Finset.range H, (1 / (j : ℝ))) ≤ (harmonic H : ℝ) := by
    calc
      _ ≤ ∑ j ∈ Finset.range (H + 1), (1 / (j : ℝ)) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
        intro j _ _
        positivity
      _ = (harmonic H : ℝ) := by
        rw [Finset.sum_range_succ']
        simp [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div]
  rw [hsum]
  apply add_le_add le_rfl
  exact mul_le_mul_of_nonneg_left (hrecip.trans (harmonic_le_one_add_log H)) (Nat.cast_nonneg H)

/-- A reduced rational approximation controls the sum of truncated one-sided
reciprocal distances on every short block. No cancellation hypothesis is used. -/
theorem sum_truncatedInv_fract_le
    (α : ℝ) (a : ℤ) (q : ℕ) (hq : 0 < q)
    (hcop : IsCoprime a (q : ℤ))
    (happrox : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (A : Finset ℤ) (hspan : ∀ m ∈ A, ∀ n ∈ A, 2 * |m - n| ≤ (q : ℤ))
    (Y : ℝ) (hY : 0 ≤ Y) :
    (∑ n ∈ A, truncatedInv Y (Int.fract (α * n))) ≤
      Y + (2 * (q : ℝ)) * (1 + Real.log (2 * (q : ℝ))) := by
  classical
  have hinj := phaseBin_injOn α a q hq hcop happrox A hspan
  calc
    _ ≤ ∑ n ∈ A, binWeight (2 * q) Y (phaseBin q α n) := by
      exact Finset.sum_le_sum (fun n _ => truncatedInv_fract_le_binWeight q hq Y α n)
    _ = ∑ j ∈ A.image (phaseBin q α), binWeight (2 * q) Y j := by
      rw [Finset.sum_image]
      exact fun m hm n hn heq => hinj hm hn heq
    _ ≤ ∑ j ∈ Finset.range (2 * q), binWeight (2 * q) Y j := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro j hj
        obtain ⟨n, _, rfl⟩ := Finset.mem_image.mp hj
        exact Finset.mem_range.mpr (phaseBin_lt q hq α n)
      · intro j _ _
        exact binWeight_nonneg hY
    _ ≤ _ := by simpa only [Nat.cast_mul, Nat.cast_ofNat] using sum_binWeight_le (2 * q) (by omega) Y

/-- Distance of a real phase to the nearest integer, expressed without a
choice of nearest integer. -/
def intDistance (x : ℝ) : ℝ := min (Int.fract x) (1 - Int.fract x)

@[simp] theorem intDistance_eq_abs_sub_round (x : ℝ) :
    intDistance x = |x - round x| := (abs_sub_round_eq_min x).symm

theorem intDistance_nonneg (x : ℝ) : 0 ≤ intDistance x :=
  le_min (Int.fract_nonneg x) (sub_nonneg.mpr (Int.fract_lt_one x).le)

/-- Two one-sided reciprocal majorants control the nearest-integer one,
including integer phases where the truncation must equal `Y`. -/
theorem truncatedInv_intDistance_le {Y : ℝ} (hY : 0 ≤ Y) (x : ℝ) :
    truncatedInv Y (intDistance x) ≤
      truncatedInv Y (Int.fract x) + truncatedInv Y (Int.fract (-x)) := by
  have hsecond : truncatedInv Y (1 - Int.fract x) ≤ truncatedInv Y (Int.fract (-x)) := by
    by_cases hx : Int.fract x = 0
    · have hneg := Int.fract_neg_eq_zero.mpr hx
      rw [hneg]
      simpa [truncatedInv] using truncatedInv_le_cap Y (1 - Int.fract x)
    · rw [Int.fract_neg hx]
  unfold intDistance
  rcases le_total (Int.fract x) (1 - Int.fract x) with h | h
  · rw [min_eq_left h]
    exact le_add_of_nonneg_right (truncatedInv_nonneg hY (Int.fract_nonneg _))
  · rw [min_eq_right h]
    exact hsecond.trans (le_add_of_nonneg_left (truncatedInv_nonneg hY (Int.fract_nonneg _)))

/-- The classical truncated reciprocal-distance estimate on one short block,
with an explicit constant and correct treatment of integer phases. -/
theorem sum_truncatedInv_intDistance_le
    (α : ℝ) (a : ℤ) (q : ℕ) (hq : 0 < q)
    (hcop : IsCoprime a (q : ℤ))
    (happrox : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (A : Finset ℤ) (hspan : ∀ m ∈ A, ∀ n ∈ A, 2 * |m - n| ≤ (q : ℤ))
    (Y : ℝ) (hY : 0 ≤ Y) :
    (∑ n ∈ A, truncatedInv Y (intDistance (α * n))) ≤
      2 * Y + 4 * (q : ℝ) * (1 + Real.log (2 * (q : ℝ))) := by
  have hnegative : |(-α) - ((-a : ℤ) : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2 := by
    simpa only [Int.cast_neg, neg_div, neg_sub_neg, abs_sub_comm] using happrox
  have hp := sum_truncatedInv_fract_le α a q hq hcop happrox A hspan Y hY
  have hn := sum_truncatedInv_fract_le (-α) (-a) q hq hcop.neg_left hnegative A hspan Y hY
  have hs : (∑ n ∈ A, truncatedInv Y (intDistance (α * n))) ≤
      (∑ n ∈ A, truncatedInv Y (Int.fract (α * n))) +
        ∑ n ∈ A, truncatedInv Y (Int.fract ((-α) * n)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro n _
    simpa only [neg_mul] using truncatedInv_intDistance_le hY (α * n)
  linarith

/-- Any interval of `floor(q/2)+1` consecutive integers is a short block. -/
theorem short_interval_span (q : ℕ) (L : ℤ) :
    ∀ m ∈ Finset.Ico L (L + (q / 2 : ℕ) + 1),
      ∀ n ∈ Finset.Ico L (L + (q / 2 : ℕ) + 1),
        2 * |m - n| ≤ (q : ℤ) := by
  intro m hm n hn
  have hm' := Finset.mem_Ico.mp hm
  have hn' := Finset.mem_Ico.mp hn
  have hh : 2 * (q / 2 : ℕ) ≤ q := by omega
  have hh' : (2 : ℤ) * (q / 2 : ℕ) ≤ q := by exact_mod_cast hh
  have habs : |m - n| ≤ (q / 2 : ℕ) := by
    apply abs_le.mpr
    constructor <;> omega
  omega

/-- Interval form of the short-block estimate used in Type I/II decompositions. -/
theorem sum_truncatedInv_intDistance_short_interval_le
    (α : ℝ) (a : ℤ) (q : ℕ) (hq : 0 < q)
    (hcop : IsCoprime a (q : ℤ))
    (happrox : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (L : ℤ) (Y : ℝ) (hY : 0 ≤ Y) :
    (∑ n ∈ Finset.Ico L (L + (q / 2 : ℕ) + 1), truncatedInv Y (intDistance (α * n))) ≤
      2 * Y + 4 * (q : ℝ) * (1 + Real.log (2 * (q : ℝ))) :=
  sum_truncatedInv_intDistance_le α a q hq hcop happrox _ (short_interval_span q L) Y hY

theorem sum_int_Ico_add (f : ℤ → ℝ) (L M R : ℤ)
    (hLM : L ≤ M) (hMR : M ≤ R) :
    (∑ n ∈ Finset.Ico L M, f n) + (∑ n ∈ Finset.Ico M R, f n) =
      ∑ n ∈ Finset.Ico L R, f n := by
  have hdisj : Disjoint (Finset.Ico L M) (Finset.Ico M R) := by
    apply Finset.disjoint_left.mpr
    intro n hn hn'
    have h := Finset.mem_Ico.mp hn
    have h' := Finset.mem_Ico.mp hn'
    omega
  have hunion : Finset.Ico L M ∪ Finset.Ico M R = Finset.Ico L R := by
    ext n
    simp only [Finset.mem_union, Finset.mem_Ico]
    omega
  rw [← Finset.sum_union hdisj, hunion]

/-- Aggregate an estimate on consecutive blocks, with no periodicity premise. -/
theorem sum_int_Ico_le_blocks (f : ℤ → ℝ) (B : ℕ) (hB : 0 < B) (C : ℝ)
    (hblock : ∀ L : ℤ, (∑ n ∈ Finset.Ico L (L + B), f n) ≤ C)
    (L : ℤ) (k : ℕ) :
    (∑ n ∈ Finset.Ico L (L + (k : ℤ) * B), f n) ≤ (k : ℝ) * C := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hBz : (0 : ℤ) < B := by exact_mod_cast hB
    have hleft : L ≤ L + (k : ℤ) * B := le_add_of_nonneg_right (by positivity)
    have hright : L + (k : ℤ) * B ≤ L + (k : ℤ) * B + B := by omega
    have hend : L + ((k + 1 : ℕ) : ℤ) * B = L + (k : ℤ) * B + B := by
      push_cast
      ring
    rw [hend, ← sum_int_Ico_add f L (L + (k : ℤ) * B)
      (L + (k : ℤ) * B + B) hleft hright]
    calc
      _ ≤ (k : ℝ) * C + C := add_le_add ih (hblock (L + (k : ℤ) * B))
      _ = ((k + 1 : ℕ) : ℝ) * C := by push_cast; ring

/-- Full interval version, with the exact number of short blocks. -/
theorem sum_truncatedInv_intDistance_interval_le_blocks
    (α : ℝ) (a : ℤ) (q : ℕ) (hq : 0 < q)
    (hcop : IsCoprime a (q : ℤ))
    (happrox : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (L : ℤ) (N : ℕ) (Y : ℝ) (hY : 0 ≤ Y) :
    (∑ n ∈ Finset.Ico L (L + N), truncatedInv Y (intDistance (α * n))) ≤
      ((N / (q / 2 + 1) + 1 : ℕ) : ℝ) *
        (2 * Y + 4 * (q : ℝ) * (1 + Real.log (2 * (q : ℝ)))) := by
  let B : ℕ := q / 2 + 1
  have hB : 0 < B := by dsimp [B]; omega
  have hcover : N ≤ (N / B + 1) * B := by
    simpa only [Nat.mul_comm] using (Nat.lt_mul_div_succ N hB).le
  have hcoverZ : (N : ℤ) ≤ ((N / B + 1 : ℕ) : ℤ) * B := by exact_mod_cast hcover
  have hs := sum_int_Ico_le_blocks
    (fun n : ℤ => truncatedInv Y (intDistance (α * n))) B hB
    (2 * Y + 4 * (q : ℝ) * (1 + Real.log (2 * (q : ℝ))))
    (fun l => by
      simpa [B, Nat.cast_add, Nat.cast_one, add_assoc] using
        sum_truncatedInv_intDistance_short_interval_le α a q hq hcop happrox l Y hY)
    L (N / B + 1)
  apply le_trans ?_ hs
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.Ico_subset_Ico le_rfl (by omega)
  · intro n _ _
    exact truncatedInv_nonneg hY (intDistance_nonneg _)

/-- Standard convenient full-interval form of the rational approximation
reciprocal-distance estimate. It applies equally to negative interval origins. -/
theorem sum_truncatedInv_intDistance_interval_le
    (α : ℝ) (a : ℤ) (q : ℕ) (hq : 0 < q)
    (hcop : IsCoprime a (q : ℤ))
    (happrox : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (L : ℤ) (N : ℕ) (Y : ℝ) (hY : 0 ≤ Y) :
    (∑ n ∈ Finset.Ico L (L + N), truncatedInv Y (intDistance (α * n))) ≤
      (2 * (N : ℝ) / q + 1) *
        (2 * Y + 4 * (q : ℝ) * (1 + Real.log (2 * (q : ℝ)))) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hh : q ≤ 2 * (q / 2 + 1) := by omega
  have hhR : (q : ℝ) ≤ 2 * ((q / 2 + 1 : ℕ) : ℝ) := by exact_mod_cast hh
  have hdivR : ((N / (q / 2 + 1) : ℕ) : ℝ) * ((q / 2 + 1 : ℕ) : ℝ) ≤ N := by
    exact_mod_cast Nat.div_mul_le_self N (q / 2 + 1)
  have hcount : ((N / (q / 2 + 1) + 1 : ℕ) : ℝ) ≤ 2 * (N : ℝ) / q + 1 := by
    push_cast
    apply add_le_add _ le_rfl
    apply (le_div_iff₀ hqR).mpr
    nlinarith [mul_le_mul_of_nonneg_left hhR (Nat.cast_nonneg (N / (q / 2 + 1)) :
      (0 : ℝ) ≤ (N / (q / 2 + 1) : ℕ))]
  have hlog : 0 ≤ Real.log (2 * (q : ℝ)) := by
    apply Real.log_nonneg
    have hqone : (1 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  exact (sum_truncatedInv_intDistance_interval_le_blocks α a q hq hcop happrox L N Y hY).trans
    (mul_le_mul_of_nonneg_right hcount (by positivity))

end Problem337.RationalPhaseSpacing

end

end OAI

-- Upstream module OAI.NumberTheory.EgyptianFractions.VaughanNearRational

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337.VaughanBilinear

theorem phase_int (n : ℤ) : phase n = 1 := by
  rw [phase, Real.fourierChar_apply]
  have he : (↑(2 * Real.pi * (n : ℝ)) : ℂ) * Complex.I =
      (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [he, Complex.exp_int_mul_two_pi_mul_I]

theorem phase_fract (x : ℝ) : phase (Int.fract x) = phase x := by
  rw [Int.fract, ← phase_mul_conj, phase_int]
  simp

theorem phase_eq_geometric_phase (x : ℝ) :
    phase x = Complex.exp (Complex.I * (2 * Real.pi * x : ℝ)) := by
  rw [phase, Real.fourierChar_apply]
  congr 1
  ring

/-- The explicit geometric majorant itself is bounded by the truncated
reciprocal distance. This also allows variable inner interval lengths. -/
theorem geometricBound_le_truncatedInv (M : ℕ) (x : ℝ) :
    geometricBound M x ≤
      RationalPhaseSpacing.truncatedInv M (RationalPhaseSpacing.intDistance x) := by
  by_cases hd : RationalPhaseSpacing.intDistance x = 0
  · rw [RationalPhaseSpacing.truncatedInv, ite_eq_left hd]
    unfold geometricBound
    split_ifs
    · exact le_rfl
    · exact min_le_left _ _
  have hdpos : 0 < RationalPhaseSpacing.intDistance x :=
    lt_of_le_of_ne (RationalPhaseSpacing.intDistance_nonneg x) (Ne.symm hd)
  have hlow : RationalPhaseSpacing.intDistance x ≤ Int.fract x := min_le_left _ _
  have hhigh : Int.fract x ≤ 1 - RationalPhaseSpacing.intDistance x := by
    have h := min_le_right (Int.fract x) (1 - Int.fract x)
    change RationalPhaseSpacing.intDistance x ≤ 1 - Int.fract x at h
    linarith
  have hs := sin_pi_mul_lower_on_middle hdpos hlow hhigh
  have hchord : 2 * RationalPhaseSpacing.intDistance x ≤ ‖1 - phase x‖ := by
    rw [norm_sub_rev, ← phase_fract x, phase_eq_geometric_phase, norm_exp_phase_sub_one]
    have habs := le_abs_self (Real.sin (Real.pi * Int.fract x))
    nlinarith
  have hnorm : 0 < ‖1 - phase x‖ := by linarith
  have hx : phase x ≠ 1 := by
    intro hx
    simp [hx] at hnorm
  rw [geometricBound, ite_eq_right hx, RationalPhaseSpacing.truncatedInv, ite_eq_right hd]
  apply min_le_min_left
  apply (div_le_div_iff₀ hnorm hdpos).mpr
  simpa using hchord

/-- A uniform harmonic row bound for indexed integer frequencies. The map
into the interval must be injective, but need not exhaust the interval. -/
theorem sum_geometricBound_difference_le {β : Type*}
    (θ : ℝ) (a : ℤ) (q : ℕ) (hq : 0 < q)
    (hcop : IsCoprime a (q : ℤ))
    (happrox : |θ - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (M : ℕ) (t : Finset β) (f : β → ℤ) (L : ℤ) (N : ℕ)
    (hf : ∀ k ∈ t, f k ∈ Finset.Ico L (L + N))
    (hinj : Set.InjOn f t) (n : ℤ) :
    (∑ k ∈ t, geometricBound M (θ * ((n - f k : ℤ) : ℝ))) ≤
      (2 * (N : ℝ) / q + 1) *
        (2 * (M : ℝ) + 4 * (q : ℝ) * (1 + Real.log (2 * (q : ℝ)))) := by
  classical
  let A := t.image (fun k => n - f k)
  let L' : ℤ := n - L - N + 1
  have hA : A ⊆ Finset.Ico L' (L' + N) := by
    intro j hj
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hj
    have hk' := Finset.mem_Ico.mp (hf k hk)
    apply Finset.mem_Ico.mpr
    dsimp [L']
    omega
  calc
    _ ≤ ∑ k ∈ t, RationalPhaseSpacing.truncatedInv M
        (RationalPhaseSpacing.intDistance (θ * ((n - f k : ℤ) : ℝ))) :=
      Finset.sum_le_sum (fun k _ => geometricBound_le_truncatedInv M _)
    _ = ∑ j ∈ A, RationalPhaseSpacing.truncatedInv M
        (RationalPhaseSpacing.intDistance (θ * j)) := by
      rw [Finset.sum_image]
      intro k hk i hi heq
      apply hinj hk hi
      dsimp at heq
      omega
    _ ≤ ∑ j ∈ Finset.Ico L' (L' + N), RationalPhaseSpacing.truncatedInv M
        (RationalPhaseSpacing.intDistance (θ * j)) :=
      Finset.sum_le_sum_of_subset_of_nonneg hA (fun _ _ _ =>
        RationalPhaseSpacing.truncatedInv_nonneg (Nat.cast_nonneg M)
          (RationalPhaseSpacing.intDistance_nonneg _))
    _ ≤ _ := RationalPhaseSpacing.sum_truncatedInv_intDistance_interval_le
      θ a q hq hcop happrox L' N M (Nat.cast_nonneg M)

end Problem337.VaughanBilinear

end

end OAI

-- Upstream module OAI.NumberTheory.EgyptianFractions.VaughanHyperbolicNearRational

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337.VaughanBilinear

/-- A full Type-II estimate for the actual hyperbolic region `m*n ≤ X`.
The rational approximation is the only analytic input: support intersection,
geometric cancellation, harmonic spacing, and coefficient-energy estimates
are all supplied by checked lemmas. Empty row and column intervals are allowed. -/
theorem near_rational_hyperbolic_bilinear_sq_le
    (θ : ℝ) (a : ℤ) (q : ℕ) (hq : 0 < q)
    (hcop : IsCoprime a (q : ℤ))
    (happrox : |θ - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (X L U V N : ℕ) (t : Finset ℕ)
    (ht : t ⊆ Finset.Ico V (V + N)) (hpos : ∀ n ∈ t, 0 < n)
    (c b : ℕ → ℂ) :
    ‖∑ m ∈ Finset.Icc L U, c m * ∑ n ∈ t,
      b n * HyperbolaCorrelation.column θ X n m‖ ^ 2 ≤
      (∑ m ∈ Finset.Icc L U, ‖c m‖ ^ 2) *
        ((2 * (N : ℝ) / q + 1) *
          (2 * ((U + 1 - L : ℕ) : ℝ) +
            4 * (q : ℝ) * (1 + Real.log (2 * (q : ℝ))))) *
              (∑ n ∈ t, ‖b n‖ ^ 2) := by
  apply norm_bilinear_sq_le_energy
  intro n hn
  calc
    _ ≤ ∑ k ∈ t, geometricBound (U + 1 - L) (θ * ((n : ℝ) - k)) := by
      apply Finset.sum_le_sum
      intro k hk
      exact HyperbolaCorrelation.column_correlation_le θ X L U n k
        ((hpos n hn).trans_le (le_max_left _ _))
    _ ≤ _ := by
      simpa only [Int.cast_sub, Int.cast_natCast] using
        (sum_geometricBound_difference_le θ a q hq hcop happrox
          (U + 1 - L) t (fun k : ℕ => (k : ℤ)) (V : ℤ) N
          (by
            intro k hk
            obtain ⟨hl, hu⟩ := Finset.mem_Ico.mp (ht hk)
            apply Finset.mem_Ico.mpr
            constructor <;> exact_mod_cast (by assumption))
          (by
            intro i hi j hj hij
            dsimp at hij
            exact_mod_cast hij)
          (n : ℤ))

end Problem337.VaughanBilinear

end

end OAI

-- Upstream module OAI.NumberTheory.EgyptianFractions.VaughanDyadicEstimate

namespace OAI
noncomputable section
open scoped BigOperators ArithmeticFunction
open Finset

namespace Problem337.Vaughan

lemma typeIIBlock_eq_bilinear (θ : ℝ) (N U V j : ℕ) :
    typeIIBlock N U V j (fun k => VaughanBilinear.phase (θ * k)) =
      ∑ m ∈ Icc (max (U + 1) (2 ^ j)) (min N (2 ^ (j + 1) - 1)),
        (typeIICoefficient U m : ℂ) *
          ∑ n ∈ Ioc V (N / 2 ^ j), (Λ n : ℂ) *
            HyperbolaCorrelation.column θ N n m := by
  unfold typeIIBlock VaughanDyadic.block
  rw [VaughanDyadic.shell_eq_Icc]
  apply sum_congr rfl
  intro m hm
  rw [mul_sum]
  apply sum_congr rfl
  intro n hn
  unfold HyperbolaCorrelation.column
  by_cases h : m * n ≤ N
  · simp only [ite_eq_left h, HyperbolaCorrelation.phase_eq_vaughan]
    rw [mul_assoc]
    congr 2
    congr 1
    push_cast
    ring
  · simp [h]

lemma dyadic_row_length_le (N U j : ℕ) :
    min N (2 ^ (j + 1) - 1) + 1 - max (U + 1) (2 ^ j) ≤ 2 ^ j := by
  have htop : min N (2 ^ (j + 1) - 1) ≤ 2 ^ (j + 1) - 1 := min_le_right _ _
  have hlow : 2 ^ j ≤ max (U + 1) (2 ^ j) := le_max_right _ _
  have hp : 0 < 2 ^ j := by positivity
  rw [pow_succ] at htop
  omega

/-- The elementary bounded-weight column energy, used only as a normalization
inside the actual Type II block estimate. -/
lemma mangoldt_column_energy_le (V T : ℕ) :
    (∑ n ∈ Ioc V T, ‖(Λ n : ℂ)‖ ^ 2) ≤ (T : ℝ) * (Real.log T) ^ 2 := by
  calc
    _ ≤ ∑ n ∈ Ioc V T, (Real.log T) ^ 2 := by
      apply sum_le_sum
      intro n hn
      have h := mem_Ioc.mp hn
      have hn0 : 0 < n := lt_of_le_of_lt (Nat.zero_le V) h.1
      apply pow_le_pow_left₀ (norm_nonneg _)
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      exact ArithmeticFunction.vonMangoldt_le_log.trans
        (Real.log_le_log (by exact_mod_cast hn0) (by exact_mod_cast h.2))
    _ = ((T - V : ℕ) : ℝ) * (Real.log T) ^ 2 := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le T V) (sq_nonneg _)

/-- A genuine rational-approximation estimate for one actual Vaughan block.
All coefficient energies and correlations have been evaluated explicitly. -/
theorem typeIIBlock_sq_le_raw
    (θ : ℝ) (a : ℤ) (q : ℕ) (hq : 0 < q)
    (hcop : IsCoprime a (q : ℤ))
    (happrox : |θ - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (N U V j : ℕ) :
    ‖typeIIBlock N U V j (fun k => VaughanBilinear.phase (θ * k))‖ ^ 2 ≤
      ((2 ^ (j + 1) : ℕ) * (1 + Real.log (2 ^ (j + 1) : ℕ)) ^ 3) *
        ((2 * ((N / 2 ^ j : ℕ) : ℝ) / q + 1) *
          (2 * ((2 ^ j : ℕ) : ℝ) + 4 * (q : ℝ) * (1 + Real.log (2 * (q : ℝ))))) *
            (((N / 2 ^ j : ℕ) : ℝ) * (Real.log (N / 2 ^ j : ℕ)) ^ 2) := by
  have hlog : 0 ≤ 1 + Real.log (2 * (q : ℝ)) := by
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
    have h := Real.log_nonneg (show (1 : ℝ) ≤ 2 * q by linarith)
    linarith
  have h := VaughanBilinear.near_rational_hyperbolic_bilinear_sq_le θ a q hq hcop happrox
    N (max (U + 1) (2 ^ j)) (min N (2 ^ (j + 1) - 1)) (V + 1) (N / 2 ^ j)
    (Ioc V (N / 2 ^ j)) (by
      intro n hn
      have hn' := mem_Ioc.mp hn
      exact mem_Ico.mpr ⟨by omega, by omega⟩)
    (fun n hn => lt_of_le_of_lt (Nat.zero_le V) (mem_Ioc.mp hn).1)
    (fun m => (typeIICoefficient U m : ℂ)) (fun n => (Λ n : ℂ))
  rw [← typeIIBlock_eq_bilinear, ← VaughanDyadic.shell_eq_Icc] at h
  refine h.trans ?_
  have hA := typeII_shell_energy_le N U j
  have hB := mangoldt_column_energy_le V (N / 2 ^ j)
  have hlength : ((min N (2 ^ (j + 1) - 1) + 1 - max (U + 1) (2 ^ j) : ℕ) : ℝ) ≤
      ((2 ^ j : ℕ) : ℝ) := by exact_mod_cast dyadic_row_length_le N U j
  gcongr

end Problem337.Vaughan

end

end OAI

-- Upstream module OAI.NumberTheory.EgyptianFractions.TypeIIBlockScalar

namespace OAI
namespace Problem337.TypeIIBlockScalar

/-- The scalar aggregation for one dyadic Vaughan Type-II block. All analytic
information is explicit in the three elementary size bounds. -/
theorem block_bound (X M T Q U V H : ℝ)
    (hX : 0 ≤ X) (hM : 0 ≤ M) (hT : 0 ≤ T)
    (hQ : 0 < Q) (hU : 0 < U) (hV : 0 < V) (hH : 1 ≤ H)
    (hMT : M * T ≤ X) (hTU : T ≤ 2 * X / U) (hMV : M ≤ X / V) :
    (2 * M * H ^ 3) * ((2 * T / Q + 1) * (2 * M + 4 * Q * H)) *
        (T * H ^ 2) ≤
      32 * X * H ^ 6 * (X / Q + X / U + X / V + Q) := by
  have hH0 : 0 ≤ H := by linarith
  have hXQ : 0 ≤ X / Q := div_nonneg hX hQ.le
  have hXU : 0 ≤ X / U := div_nonneg hX hU.le
  have hXV : 0 ≤ X / V := div_nonneg hX hV.le
  have hMTQ : M * T / Q ≤ X / Q := div_le_div_of_nonneg_right hMT hQ.le
  have hTH : T * H ≤ (2 * X / U) * H := mul_le_mul_of_nonneg_right hTU hH0
  have hQH : X / Q ≤ H * (X / Q) := by nlinarith [mul_le_mul_of_nonneg_right hH hXQ]
  have hVH : X / V ≤ H * (X / V) := by nlinarith [mul_le_mul_of_nonneg_right hH hXV]
  have hinner : (2 * T / Q + 1) * (2 * M + 4 * Q * H) ≤
      16 * H * (X / Q + X / U + X / V + Q) := by
    have heq : (2 * T / Q + 1) * (2 * M + 4 * Q * H) =
        4 * (M * T / Q) + 8 * T * H + 2 * M + 4 * Q * H := by
      field_simp
      ring
    rw [heq]
    have hTH' : T * H ≤ 2 * (X / U) * H := by convert hTH using 1; ring
    nlinarith [mul_nonneg hH0 hXQ, mul_nonneg hH0 hXV, mul_nonneg hH0 hQ.le]
  have hfactor : 2 * (M * T) * H ^ 5 ≤ 2 * X * H ^ 5 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hMT (by norm_num)) (by positivity)
  have hinner0 : 0 ≤ (2 * T / Q + 1) * (2 * M + 4 * Q * H) := by positivity
  calc
    _ = (2 * (M * T) * H ^ 5) * ((2 * T / Q + 1) * (2 * M + 4 * Q * H)) := by ring
    _ ≤ (2 * X * H ^ 5) * (16 * H * (X / Q + X / U + X / V + Q)) :=
      mul_le_mul hfactor hinner hinner0 (by positivity)
    _ = _ := by ring

end Problem337.TypeIIBlockScalar

end OAI

-- Upstream module OAI.NumberTheory.EgyptianFractions.HyperbolaDyadicBridge

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337.VaughanDyadic

/-- Empty high shells contribute nothing to the long--long hyperbola. -/
theorem block_eq_zero_of_large_base {E : Type*} [AddCommMonoid E]
    (N U V j : ℕ) (F : ℕ → ℕ → E) (hN : N < 2 ^ j * (V + 1)) :
    block N U V j F = 0 := by
  unfold block
  apply Finset.sum_eq_zero
  intro m hm
  apply Finset.sum_eq_zero
  intro n hn
  have hm2 := (mem_shell.mp hm).2.2.1
  have hnV : V + 1 ≤ n := (Finset.mem_Ioc.mp hn).1
  have hmn : N < m * n := hN.trans_le (Nat.mul_le_mul hm2 hnV)
  simp [not_le.mpr hmn]

/-- Every nonzero block has row scale at most the hyperbolic long-column cap. -/
theorem base_le_div_of_block_ne_zero {E : Type*} [AddCommMonoid E]
    (N U V j : ℕ) (F : ℕ → ℕ → E) (hblock : block N U V j F ≠ 0) :
    2 ^ j ≤ N / (V + 1) := by
  apply (Nat.le_div_iff_mul_le (Nat.succ_pos V)).mpr
  by_contra h
  exact hblock (block_eq_zero_of_large_base N U V j F (Nat.lt_of_not_ge h))

end Problem337.VaughanDyadic

end

end OAI

-- Upstream module OAI.NumberTheory.EgyptianFractions.VaughanDyadicUniform

namespace OAI
noncomputable section
open scoped BigOperators ArithmeticFunction
open Finset

namespace Problem337.Vaughan

def typeIILogScale (N : ℕ) : ℝ := 1 + Real.log (2 * (N : ℝ))

lemma one_le_typeIILogScale (N : ℕ) : 1 ≤ typeIILogScale N := by
  have h := Real.log_natCast_nonneg (2 * N)
  simp only [Nat.cast_mul, Nat.cast_ofNat] at h
  unfold typeIILogScale
  linarith

lemma log_nat_le_typeIILogScale (N T : ℕ) (hT : T ≤ N) :
    Real.log T ≤ typeIILogScale N := by
  by_cases h0 : T = 0
  · simp only [h0, Nat.cast_zero, Real.log_zero]
    exact zero_le_one.trans (one_le_typeIILogScale N)
  have ht : (0 : ℝ) < T := by exact_mod_cast Nat.pos_of_ne_zero h0
  have htn : (T : ℝ) ≤ 2 * (N : ℝ) := by
    have h := (Nat.cast_le (α := ℝ)).mpr hT
    nlinarith [Nat.cast_nonneg N (α := ℝ)]
  have hlog := Real.log_le_log ht htn
  unfold typeIILogScale
  linarith

/-- Uniform logarithmic normalization of the coefficient block estimate. -/
theorem typeIIBlock_sq_le_normalized
    (θ : ℝ) (a : ℤ) (q : ℕ) (hq : 0 < q)
    (hcop : IsCoprime a (q : ℤ))
    (happrox : |θ - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (N U V j : ℕ) (hqN : q ≤ N) (hM : 2 ^ j ≤ N) :
    ‖typeIIBlock N U V j (fun k => VaughanBilinear.phase (θ * k))‖ ^ 2 ≤
      (2 * ((2 ^ j : ℕ) : ℝ) * (typeIILogScale N) ^ 3) *
        ((2 * ((N / 2 ^ j : ℕ) : ℝ) / q + 1) *
          (2 * ((2 ^ j : ℕ) : ℝ) + 4 * (q : ℝ) * typeIILogScale N)) *
            (((N / 2 ^ j : ℕ) : ℝ) * (typeIILogScale N) ^ 2) := by
  have hH0 : 0 ≤ typeIILogScale N := zero_le_one.trans (one_le_typeIILogScale N)
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hMR : (0 : ℝ) < ((2 ^ j : ℕ) : ℝ) := by positivity
  have hqlog : 1 + Real.log (2 * (q : ℝ)) ≤ typeIILogScale N := by
    unfold typeIILogScale
    apply add_le_add le_rfl
    exact Real.log_le_log (by positivity) (by exact_mod_cast Nat.mul_le_mul_left 2 hqN)
  have hMlog : 1 + Real.log (2 ^ (j + 1) : ℕ) ≤ typeIILogScale N := by
    unfold typeIILogScale
    apply add_le_add le_rfl
    apply Real.log_le_log (by positivity)
    rw [pow_succ, Nat.cast_mul, Nat.cast_ofNat]
    have hMRN : ((2 ^ j : ℕ) : ℝ) ≤ N := by exact_mod_cast hM
    nlinarith
  have hTlog := log_nat_le_typeIILogScale N (N / 2 ^ j) (Nat.div_le_self _ _)
  have hraw := typeIIBlock_sq_le_raw θ a q hq hcop happrox N U V j
  refine hraw.trans ?_
  have hqlog0 : 0 ≤ 1 + Real.log (2 * (q : ℝ)) := by
    have h := Real.log_natCast_nonneg (2 * q)
    simp only [Nat.cast_mul, Nat.cast_ofNat] at h
    linarith
  have hMlog0 : 0 ≤ 1 + Real.log (2 ^ (j + 1) : ℕ) := by
    linarith [Real.log_natCast_nonneg (2 ^ (j + 1))]
  have hTlog0 := Real.log_natCast_nonneg (N / 2 ^ j)
  have he : ((2 ^ (j + 1) : ℕ) : ℝ) = 2 * ((2 ^ j : ℕ) : ℝ) := by
    rw [pow_succ, Nat.cast_mul, Nat.cast_ofNat]
    ring
  rw [he] at hMlog hMlog0 ⊢
  gcongr

/-- Uniform actual Type II block bound, with no cancellation or energy premise. -/
theorem typeIIBlock_sq_le_uniform
    (θ : ℝ) (a : ℤ) (q : ℕ) (hq : 0 < q)
    (hcop : IsCoprime a (q : ℤ))
    (happrox : |θ - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (N U V j : ℕ) (hqN : q ≤ N) (hU : 0 < U) (hV : 0 < V) :
    ‖typeIIBlock N U V j (fun k => VaughanBilinear.phase (θ * k))‖ ^ 2 ≤
      32 * (N : ℝ) * (typeIILogScale N) ^ 6 *
        ((N : ℝ) / q + (N : ℝ) / U + (N : ℝ) / V + q) := by
  have hH : 0 ≤ typeIILogScale N := zero_le_one.trans (one_le_typeIILogScale N)
  by_cases hb : typeIIBlock N U V j (fun k => VaughanBilinear.phase (θ * k)) = 0
  · rw [hb, norm_zero, zero_pow (by decide : 2 ≠ 0)]
    positivity
  have hs : (VaughanDyadic.shell U N j).Nonempty := by
    by_contra he
    have he' : VaughanDyadic.shell U N j = ∅ := not_nonempty_iff_eq_empty.mp he
    apply hb
    simp [typeIIBlock, VaughanDyadic.block, he']
  obtain ⟨m, hm⟩ := hs
  have hm' := VaughanDyadic.mem_shell.mp hm
  have hM : 2 ^ j ≤ N := hm'.2.2.1.trans hm'.2.1
  have hbase := VaughanDyadic.base_le_div_of_block_ne_zero N U V j
    (fun m n => (typeIICoefficient U m : ℂ) * (Λ n : ℂ) *
      VaughanBilinear.phase (θ * (m * n : ℕ))) hb
  have hMT : (((2 ^ j : ℕ) : ℝ) * ((N / 2 ^ j : ℕ) : ℝ)) ≤ N := by
    exact_mod_cast Nat.mul_div_le N (2 ^ j)
  have hU2M : (U : ℝ) ≤ 2 * ((2 ^ j : ℕ) : ℝ) := by
    have hnat : U ≤ 2 * 2 ^ j := by
      have hu := hm'.1
      have hmhi := hm'.2.2.2
      rw [pow_succ] at hmhi
      omega
    exact_mod_cast hnat
  have hTU : ((N / 2 ^ j : ℕ) : ℝ) ≤ 2 * (N : ℝ) / U := by
    apply (le_div_iff₀ (by exact_mod_cast hU : (0 : ℝ) < U)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hU2M
      (Nat.cast_nonneg (N / 2 ^ j) : (0 : ℝ) ≤ (N / 2 ^ j : ℕ))]
  have hMV : ((2 ^ j : ℕ) : ℝ) ≤ (N : ℝ) / V := by
    apply (le_div_iff₀ (by exact_mod_cast hV : (0 : ℝ) < V)).mpr
    have hn : 2 ^ j * V ≤ N :=
      (Nat.mul_le_mul_left (2 ^ j) (Nat.le_succ V)).trans
        ((Nat.le_div_iff_mul_le (Nat.succ_pos V)).mp hbase)
    exact_mod_cast hn
  exact (typeIIBlock_sq_le_normalized θ a q hq hcop happrox N U V j hqN hM).trans
    (TypeIIBlockScalar.block_bound N (2 ^ j : ℕ) (N / 2 ^ j : ℕ) q U V (typeIILogScale N)
      (Nat.cast_nonneg N) (by positivity) (Nat.cast_nonneg _)
      (by exact_mod_cast hq) (by exact_mod_cast hU) (by exact_mod_cast hV)
      (one_le_typeIILogScale N) hMT hTU hMV)

end Problem337.Vaughan

end

end OAI

-- Upstream module OAI.NumberTheory.EgyptianFractions.VaughanCutoff

namespace OAI
noncomputable section
open Filter

namespace Problem337.Vaughan

/-- The conventional balanced natural cutoff for Vaughan's identity. -/
def optimizedCutoff (X : ℝ) : ℕ := ⌊X ^ (2 / 5 : ℝ)⌋₊

theorem optimizedCutoff_le (X : ℝ) (hX : 0 ≤ X) :
    (optimizedCutoff X : ℝ) ≤ X ^ (2 / 5 : ℝ) :=
  Nat.floor_le (Real.rpow_nonneg hX _)

theorem optimizedCutoff_lower (X : ℝ) (hX : 2 ≤ X ^ (2 / 5 : ℝ)) :
    X ^ (2 / 5 : ℝ) / 2 ≤ (optimizedCutoff X : ℝ) := by
  have hfloor := Nat.lt_floor_add_one (X ^ (2 / 5 : ℝ))
  unfold optimizedCutoff
  linarith

theorem optimizedCutoff_pos (X : ℝ) (hX : 2 ≤ X ^ (2 / 5 : ℝ)) :
    0 < optimizedCutoff X := by
  have h : 2 ≤ optimizedCutoff X := Nat.le_floor hX
  omega

theorem optimizedCutoff_sq_le (X : ℝ) (hX : 0 ≤ X) :
    (optimizedCutoff X : ℝ) ^ 2 ≤ X ^ (4 / 5 : ℝ) := by
  have hpow : (X ^ (2 / 5 : ℝ)) ^ 2 = X ^ (4 / 5 : ℝ) := by
    have h := Real.rpow_mul hX (2 / 5 : ℝ) (2 : ℝ)
    norm_num at h
    exact h.symm
  rw [← hpow]
  exact pow_le_pow_left₀ (Nat.cast_nonneg _) (optimizedCutoff_le X hX) 2

theorem optimizedCutoff_le_four_fifths (X : ℝ) (hX : 1 ≤ X) :
    (optimizedCutoff X : ℝ) ≤ X ^ (4 / 5 : ℝ) :=
  (optimizedCutoff_le X (by linarith)).trans
    (Real.rpow_le_rpow_of_exponent_le hX (by norm_num))

/-- The reciprocal square-root loss from a long-variable cutoff has precisely
the required four-fifths power, with a harmless explicit constant. -/
theorem div_sqrt_optimizedCutoff_le (X : ℝ) (hX : 0 < X)
    (hpow : 2 ≤ X ^ (2 / 5 : ℝ)) :
    X / Real.sqrt (optimizedCutoff X : ℝ) ≤ 2 * X ^ (4 / 5 : ℝ) := by
  have hsq : (X ^ (1 / 5 : ℝ)) ^ 2 = X ^ (2 / 5 : ℝ) := by
    have h := Real.rpow_mul hX.le (1 / 5 : ℝ) (2 : ℝ)
    norm_num at h
    exact h.symm
  have hcut := optimizedCutoff_lower X hpow
  have hs : X ^ (1 / 5 : ℝ) / 2 ≤ Real.sqrt (optimizedCutoff X : ℝ) := by
    apply (Real.le_sqrt (by positivity) (Nat.cast_nonneg _)).mpr
    nlinarith [sq_nonneg (X ^ (1 / 5 : ℝ))]
  have hpos : 0 < Real.sqrt (optimizedCutoff X : ℝ) :=
    Real.sqrt_pos.mpr (by exact_mod_cast optimizedCutoff_pos X hpow)
  apply (div_le_iff₀ hpos).mpr
  have hprod : X ^ (4 / 5 : ℝ) * X ^ (1 / 5 : ℝ) = X := by
    rw [← Real.rpow_add hX]
    norm_num
  calc
    X = X ^ (4 / 5 : ℝ) * X ^ (1 / 5 : ℝ) := hprod.symm
    _ = (2 * X ^ (4 / 5 : ℝ)) * (X ^ (1 / 5 : ℝ) / 2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hs (by positivity)

/-- A concrete scalar optimization of the cutoff-dependent error terms. -/
theorem optimizedCutoff_error_le (X : ℝ) (hX : 1 ≤ X)
    (hpow : 2 ≤ X ^ (2 / 5 : ℝ)) :
    (optimizedCutoff X : ℝ) + (optimizedCutoff X : ℝ) ^ 2 +
        X / Real.sqrt (optimizedCutoff X : ℝ) ≤ 4 * X ^ (4 / 5 : ℝ) := by
  have h1 := optimizedCutoff_le_four_fifths X hX
  have h2 := optimizedCutoff_sq_le X (by linarith)
  have h3 := div_sqrt_optimizedCutoff_le X (by linarith) hpow
  linarith

/-- The short initial segment is also absorbed by the four-fifths budget. -/
theorem optimizedCutoff_log_le (X : ℝ) (hX : 1 ≤ X)
    (hpow : 2 ≤ X ^ (2 / 5 : ℝ)) :
    (optimizedCutoff X : ℝ) * Real.log (optimizedCutoff X : ℝ) ≤
      X ^ (4 / 5 : ℝ) * Real.log X := by
  have hUX : (optimizedCutoff X : ℝ) ≤ X := by
    calc
      _ ≤ X ^ (2 / 5 : ℝ) := optimizedCutoff_le X (by linarith)
      _ ≤ X ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hX (by norm_num)
      _ = X := Real.rpow_one X
  have hlog : Real.log (optimizedCutoff X : ℝ) ≤ Real.log X :=
    Real.log_le_log (by exact_mod_cast optimizedCutoff_pos X hpow) hUX
  have hlogX : 0 ≤ Real.log X := Real.log_nonneg hX
  exact (mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg _)).trans
    (mul_le_mul_of_nonneg_right (optimizedCutoff_le_four_fifths X hX) hlogX)

/-- Scalar normalization to the usual three-term Vaughan envelope. The
Diophantine denominator only needs the ordinary range `1 ≤ q ≤ X`. -/
theorem optimizedCutoff_standard_envelope (X q : ℝ) (hX : 1 ≤ X)
    (hq : 1 ≤ q) (hqX : q ≤ X) (hpow : 2 ≤ X ^ (2 / 5 : ℝ)) :
    X / q + ((optimizedCutoff X : ℝ) + (optimizedCutoff X : ℝ) ^ 2 +
        X / Real.sqrt (optimizedCutoff X : ℝ)) + q ≤
      4 * (X / Real.sqrt q + X ^ (4 / 5 : ℝ) + Real.sqrt (X * q)) := by
  have hX0 : 0 ≤ X := by linarith
  have hq0 : 0 ≤ q := by linarith
  have hsqpos : 0 < Real.sqrt q := Real.sqrt_pos.mpr (by linarith)
  have hsqq : Real.sqrt q ≤ q := Real.sqrt_le_self_iff.mpr (Or.inr hq)
  have hdiv : X / q ≤ X / Real.sqrt q :=
    div_le_div_of_nonneg_left hX0 hsqpos hsqq
  have hqsqrt : q ≤ Real.sqrt (X * q) := by
    apply (Real.le_sqrt hq0 (mul_nonneg hX0 hq0)).mpr
    nlinarith [mul_le_mul_of_nonneg_right hqX hq0]
  have herr := optimizedCutoff_error_le X hX hpow
  have hnonneg : 0 ≤ X / Real.sqrt q := div_nonneg hX0 hsqpos.le
  nlinarith [Real.sqrt_nonneg (X * q)]

/-- Optimization of the square-root expression arising from a Type II block.
Both long-variable cutoffs are the same balanced natural cutoff. -/
theorem sqrt_optimizedCutoff_envelope_le (X q : ℝ) (hX : 1 ≤ X)
    (hq : 0 < q) (hpow : 2 ≤ X ^ (2 / 5 : ℝ)) :
    Real.sqrt (X * (X / q + X / (optimizedCutoff X : ℝ) +
        X / (optimizedCutoff X : ℝ) + q)) ≤
      3 * (X / Real.sqrt q + X ^ (4 / 5 : ℝ) + Real.sqrt (X * q)) := by
  have hX0 : 0 ≤ X := by linarith
  have hU0 : 0 < (optimizedCutoff X : ℝ) := by
    exact_mod_cast optimizedCutoff_pos X hpow
  have hA : 0 ≤ X / Real.sqrt q := by positivity
  have hB : 0 ≤ X ^ (4 / 5 : ℝ) := by positivity
  have hC : 0 ≤ Real.sqrt (X * q) := Real.sqrt_nonneg _
  have hqeq : X * (X / q) = (X / Real.sqrt q) ^ 2 := by
    rw [div_pow, Real.sq_sqrt hq.le]
    ring
  have hUeq : X * (X / (optimizedCutoff X : ℝ)) =
      (X / Real.sqrt (optimizedCutoff X : ℝ)) ^ 2 := by
    rw [div_pow, Real.sq_sqrt hU0.le]
    ring
  have hUbound := pow_le_pow_left₀ (show 0 ≤ X / Real.sqrt (optimizedCutoff X : ℝ) by
    positivity) (div_sqrt_optimizedCutoff_le X (by linarith) hpow) 2
  have hCeq := Real.sq_sqrt (mul_nonneg hX0 hq.le)
  apply (Real.sqrt_le_left (by positivity)).mpr
  rw [mul_add, mul_add, mul_add, hqeq, hUeq]
  nlinarith [mul_nonneg hA hB, mul_nonneg hA hC, mul_nonneg hB hC,
    sq_nonneg (X / Real.sqrt q), sq_nonneg (X ^ (4 / 5 : ℝ)),
    sq_nonneg (Real.sqrt (X * q))]

/-- The precise squared Type II block budget transfers to the standard
Vaughan envelope after choosing both cutoffs as `optimizedCutoff X`. -/
theorem optimizedCutoff_squared_budget (X q C R : ℝ) (hX : 1 ≤ X)
    (hq : 0 < q) (hC : 0 ≤ C) (hpow : 2 ≤ X ^ (2 / 5 : ℝ))
    (hbound : R ^ 2 ≤ C * X * (1 + Real.log (2 * X)) ^ 6 *
      (X / q + X / (optimizedCutoff X : ℝ) + X / (optimizedCutoff X : ℝ) + q)) :
    R ≤ 3 * Real.sqrt C * (1 + Real.log (2 * X)) ^ 3 *
      (X / Real.sqrt q + X ^ (4 / 5 : ℝ) + Real.sqrt (X * q)) := by
  let L : ℝ := 1 + Real.log (2 * X)
  let E : ℝ := X / Real.sqrt q + X ^ (4 / 5 : ℝ) + Real.sqrt (X * q)
  have hX0 : 0 ≤ X := by linarith
  have hL : 0 ≤ L := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 2 * X by linarith)
    dsimp [L]
    linarith
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hD : X * (X / q + X / (optimizedCutoff X : ℝ) +
      X / (optimizedCutoff X : ℝ) + q) ≤ (3 * E) ^ 2 :=
    (Real.sqrt_le_left (by positivity)).mp (sqrt_optimizedCutoff_envelope_le X q hX hq hpow)
  change R ≤ 3 * Real.sqrt C * L ^ 3 * E
  apply le_of_sq_le_sq _ (by positivity)
  calc
    R ^ 2 ≤ C * X * L ^ 6 *
        (X / q + X / (optimizedCutoff X : ℝ) + X / (optimizedCutoff X : ℝ) + q) := hbound
    _ = (C * L ^ 6) * (X *
        (X / q + X / (optimizedCutoff X : ℝ) + X / (optimizedCutoff X : ℝ) + q)) := by ring
    _ ≤ (C * L ^ 6) * (3 * E) ^ 2 := mul_le_mul_of_nonneg_left hD (by positivity)
    _ = (3 * Real.sqrt C * L ^ 3 * E) ^ 2 := by
      have hs := Real.sq_sqrt hC
      calc
        _ = (3 * E) ^ 2 * L ^ 6 * (Real.sqrt C) ^ 2 := by rw [hs]; ring
        _ = _ := by ring

end Problem337.Vaughan

end

end OAI

-- Upstream module OAI.NumberTheory.EgyptianFractions.VaughanOptimized

namespace OAI
noncomputable section
open scoped BigOperators ArithmeticFunction

namespace Problem337.Vaughan

/-- The standard three-term envelope for a reduced rational approximation. -/
def approximationEnvelope (X q : ℝ) : ℝ :=
  X / Real.sqrt q + X ^ (4 / 5 : ℝ) + Real.sqrt (X * q)

lemma approximationEnvelope_nonneg (X q : ℝ) (hX : 0 ≤ X) :
    0 ≤ approximationEnvelope X q := by
  unfold approximationEnvelope
  positivity

lemma dyadic_log_le_three_scale (N : ℕ) :
    1 + Real.log N / Real.log 2 ≤ 3 * typeIILogScale N := by
  have hlog := Real.log_natCast_nonneg N
  have htwo : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hdiv : Real.log N / Real.log 2 ≤ 2 * Real.log N := by
    apply (div_le_iff₀ (by linarith : 0 < Real.log 2)).mpr
    nlinarith [mul_le_mul_of_nonneg_right htwo hlog]
  have hN := log_nat_le_typeIILogScale N N le_rfl
  have hH := one_le_typeIILogScale N
  linarith

/-- Balanced cutoffs turn each actual Type II block into the standard envelope. -/
theorem optimized_typeIIBlock_bound
    (θ : ℝ) (a : ℤ) (q : ℕ) (hq : 0 < q)
    (hcop : IsCoprime a (q : ℤ))
    (happrox : |θ - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (N j : ℕ) (hqN : q ≤ N)
    (hpow : 2 ≤ (N : ℝ) ^ (2 / 5 : ℝ)) :
    ‖typeIIBlock N (optimizedCutoff N) (optimizedCutoff N) j
      (fun k => VaughanBilinear.phase (θ * k))‖ ≤
      18 * (typeIILogScale N) ^ 3 * approximationEnvelope N q := by
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast hq.trans_le hqN
  have hU := optimizedCutoff_pos N hpow
  have hs := typeIIBlock_sq_le_uniform θ a q hq hcop happrox N
    (optimizedCutoff N) (optimizedCutoff N) j hqN hU hU
  have hb := optimizedCutoff_squared_budget N q 32
    ‖typeIIBlock N (optimizedCutoff N) (optimizedCutoff N) j
      (fun k => VaughanBilinear.phase (θ * k))‖
    hN (by exact_mod_cast hq) (by norm_num) hpow hs
  have hsqrt : Real.sqrt (32 : ℝ) ≤ 6 :=
    (Real.sqrt_le_left (by norm_num)).mpr (by norm_num)
  change _ ≤ 3 * Real.sqrt 32 * (typeIILogScale N) ^ 3 * approximationEnvelope N q at hb
  refine hb.trans ?_
  have hH : 0 ≤ typeIILogScale N := zero_le_one.trans (one_le_typeIILogScale N)
  have hE := approximationEnvelope_nonneg N q (Nat.cast_nonneg N)
  gcongr
  norm_num at *
  linarith

/-- Summing the genuine dyadic blocks costs one further logarithm, not a
power of the summation length. All cancellation hypotheses are discharged. -/
theorem optimized_typeII_bound
    (θ : ℝ) (a : ℤ) (q : ℕ) (hq : 0 < q)
    (hcop : IsCoprime a (q : ℤ))
    (happrox : |θ - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (N : ℕ) (hqN : q ≤ N)
    (hpow : 2 ≤ (N : ℝ) ^ (2 / 5 : ℝ)) :
    ‖weightedSum (Finset.Ioc 0 N) (fun k => VaughanBilinear.phase (θ * k))
      (typeIICoefficient (optimizedCutoff N) * longPart (optimizedCutoff N) Λ)‖ ≤
      54 * (typeIILogScale N) ^ 4 * approximationEnvelope N q := by
  have hH : 0 ≤ typeIILogScale N := zero_le_one.trans (one_le_typeIILogScale N)
  have hE := approximationEnvelope_nonneg N q (Nat.cast_nonneg N)
  have hb := norm_typeII_le_dyadic_log_budget N (optimizedCutoff N) (optimizedCutoff N)
    (fun k => VaughanBilinear.phase (θ * k))
    (18 * (typeIILogScale N) ^ 3 * approximationEnvelope N q) (by positivity)
    (fun j _ => optimized_typeIIBlock_bound θ a q hq hcop happrox N j hqN hpow)
  refine hb.trans ?_
  calc
    _ ≤ (3 * typeIILogScale N) *
        (18 * (typeIILogScale N) ^ 3 * approximationEnvelope N q) :=
      mul_le_mul_of_nonneg_right (dyadic_log_le_three_scale N) (by positivity)
    _ = _ := by ring

end Problem337.Vaughan

end

end OAI

-- Upstream module OAI.NumberTheory.EgyptianFractions.RationalPhaseHyperbola

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337.RationalPhaseSpacing

/-- Monotonicity in the cap, valid also at integer phases. -/
theorem truncatedInv_mono_cap {Y Z : ℝ} (hYZ : Y ≤ Z) (x : ℝ) :
    truncatedInv Y x ≤ truncatedInv Z x := by
  unfold truncatedInv
  split_ifs
  · exact hYZ
  · exact min_le_min hYZ le_rfl

/-- Positive indices in the first half-block cannot approach an integer more
closely than `1/(2q)`. This removes the artificial singular term in Type I. -/
theorem intDistance_lower_bound
    (α : ℝ) (a : ℤ) (q : ℕ) (hq : 0 < q)
    (hcop : IsCoprime a (q : ℤ))
    (happrox : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (n : ℤ) (hn : n ≠ 0) (hsmall : 2 * |n| ≤ (q : ℤ)) :
    1 / (2 * (q : ℝ)) ≤ intDistance (α * n) := by
  simpa only [intDistance_eq_abs_sub_round] using
    separation_of_rational_approximation α a q hq hcop happrox n hn hsmall (round (α * n))

/-- First-block harmonic estimate with arbitrary, even varying, caps. The
bound is independent of those caps because zero frequency is excluded. -/
theorem sum_truncatedInv_first_block_le
    (α : ℝ) (a : ℤ) (q : ℕ) (hq : 0 < q)
    (hcop : IsCoprime a (q : ℤ))
    (happrox : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (cap : ℤ → ℝ) :
    (∑ n ∈ Finset.Ico 1 ((q / 2 + 1 : ℕ) : ℤ),
      truncatedInv (cap n) (intDistance (α * n))) ≤
      8 * (q : ℝ) * (1 + Real.log (2 * (q : ℝ))) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hhalf : (2 : ℤ) * (q / 2 : ℕ) ≤ q := by exact_mod_cast (show 2 * (q / 2) ≤ q by omega)
  have hspan : ∀ m ∈ Finset.Ico 1 ((q / 2 + 1 : ℕ) : ℤ),
      ∀ n ∈ Finset.Ico 1 ((q / 2 + 1 : ℕ) : ℤ), 2 * |m - n| ≤ (q : ℤ) := by
    intro m hm n hn
    apply short_interval_span q 0 m _ n _
    · have hh := Finset.mem_Ico.mp hm
      apply Finset.mem_Ico.mpr
      push_cast at hh ⊢
      omega
    · have hh := Finset.mem_Ico.mp hn
      apply Finset.mem_Ico.mpr
      push_cast at hh ⊢
      omega
  have hpoint : ∀ n ∈ Finset.Ico 1 ((q / 2 + 1 : ℕ) : ℤ),
      truncatedInv (cap n) (intDistance (α * n)) ≤
        truncatedInv (2 * (q : ℝ)) (intDistance (α * n)) := by
    intro n hn
    have hn' := Finset.mem_Ico.mp hn
    have hnp : 0 < n := by omega
    have hsmall : 2 * |n| ≤ (q : ℤ) := by
      rw [abs_of_pos hnp]
      push_cast at hn'
      omega
    have hd := intDistance_lower_bound α a q hq hcop happrox n (by omega) hsmall
    have hdp : 0 < intDistance (α * n) := (by positivity : (0 : ℝ) < 1 / (2 * q)).trans_le hd
    have hinv : 1 / intDistance (α * n) ≤ 2 * (q : ℝ) := by
      apply (div_le_iff₀ hdp).mpr
      have hh := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * q)).mp hd
      nlinarith
    simp only [truncatedInv, ite_eq_right (ne_of_gt hdp), min_eq_right hinv]
    exact min_le_right _ _
  have hs := sum_truncatedInv_intDistance_le α a q hq hcop happrox
    (Finset.Ico 1 ((q / 2 + 1 : ℕ) : ℤ)) hspan (2 * (q : ℝ)) (by positivity)
  have hlog : 0 ≤ Real.log (2 * (q : ℝ)) := by
    apply Real.log_nonneg
    have hqone : (1 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  exact (Finset.sum_le_sum hpoint).trans (hs.trans (by nlinarith))

/-- On later blocks the hyperbolic cap `X/n` is bounded by the cap at the
left endpoint. This is the actual ingredient that removes an `O(X)` error. -/
theorem sum_truncatedInv_hyperbolic_block_le
    (α : ℝ) (a : ℤ) (q : ℕ) (hq : 0 < q)
    (hcop : IsCoprime a (q : ℤ))
    (happrox : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (L : ℤ) (hL : 0 < L) (X : ℝ) (hX : 0 ≤ X) :
    (∑ n ∈ Finset.Ico L (L + (q / 2 + 1 : ℕ)),
      truncatedInv (X / (n : ℝ)) (intDistance (α * n))) ≤
      2 * X / (L : ℝ) + 4 * (q : ℝ) * (1 + Real.log (2 * (q : ℝ))) := by
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hs := sum_truncatedInv_intDistance_short_interval_le α a q hq hcop happrox
    L (X / (L : ℝ)) (by positivity)
  have hpoint : ∀ n ∈ Finset.Ico L (L + (q / 2 + 1 : ℕ)),
      truncatedInv (X / (n : ℝ)) (intDistance (α * n)) ≤
        truncatedInv (X / (L : ℝ)) (intDistance (α * n)) := by
    intro n hn
    apply truncatedInv_mono_cap
    apply div_le_div_of_nonneg_left hX hLr
    exact_mod_cast (Finset.mem_Ico.mp hn).1
  apply (Finset.sum_le_sum hpoint).trans
  simpa only [Nat.cast_add, Nat.cast_one, add_assoc, mul_div_assoc] using hs

/-- Prefix aggregation with hyperbolic caps. The first block has no singular
term; the remaining singular terms sum harmonically rather than linearly. -/
theorem sum_truncatedInv_hyperbolic_prefix_blocks_le
    (α : ℝ) (a : ℤ) (q : ℕ) (hq : 0 < q)
    (hcop : IsCoprime a (q : ℤ))
    (happrox : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (X : ℝ) (hX : 0 ≤ X) (k : ℕ) :
    (∑ n ∈ Finset.Ico 1 ((k : ℤ) * (q / 2 + 1 : ℕ) + (q / 2 + 1 : ℕ)),
      truncatedInv (X / (n : ℝ)) (intDistance (α * n))) ≤
      ((k : ℝ) + 2) * (4 * (q : ℝ) * (1 + Real.log (2 * (q : ℝ)))) +
        (2 * X / ((q / 2 + 1 : ℕ) : ℝ)) * (harmonic k : ℝ) := by
  let B : ℕ := q / 2 + 1
  let C : ℝ := 4 * (q : ℝ) * (1 + Real.log (2 * (q : ℝ)))
  change (∑ n ∈ Finset.Ico 1 ((k : ℤ) * B + B),
      truncatedInv (X / (n : ℝ)) (intDistance (α * n))) ≤
      ((k : ℝ) + 2) * C + (2 * X / (B : ℝ)) * (harmonic k : ℝ)
  have hB : 0 < B := by dsimp [B]; omega
  have hBz : (0 : ℤ) < B := by exact_mod_cast hB
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  induction k with
  | zero =>
    have hs := sum_truncatedInv_first_block_le α a q hq hcop happrox (fun n => X / (n : ℝ))
    convert hs using 1 <;> simp [B, C]
    ring
  | succ k ih =>
    have hmiddle : 0 < (k : ℤ) * B + B := by positivity
    have hleft : (1 : ℤ) ≤ (k : ℤ) * B + B := by omega
    have hright : (k : ℤ) * B + B ≤ (k : ℤ) * B + B + B := by omega
    have hend : ((k + 1 : ℕ) : ℤ) * B + B = (k : ℤ) * B + B + B := by
      push_cast
      ring
    rw [hend, ← sum_int_Ico_add _ 1 ((k : ℤ) * B + B)
      ((k : ℤ) * B + B + B) hleft hright]
    have hblock := sum_truncatedInv_hyperbolic_block_le α a q hq hcop happrox
      ((k : ℤ) * B + B) hmiddle X hX
    have hrecip : 2 * X / ((k : ℝ) * B + B) =
        (2 * X / (B : ℝ)) * (1 / ((k : ℝ) + 1)) := by
      have hkpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      have hfactor : (k : ℝ) * B + B = (B : ℝ) * ((k : ℝ) + 1) := by ring
      rw [hfactor]
      field_simp
    have hblock' : (∑ n ∈ Finset.Ico ((k : ℤ) * B + B) ((k : ℤ) * B + B + B),
        truncatedInv (X / (n : ℝ)) (intDistance (α * n))) ≤
        (2 * X / (B : ℝ)) * (1 / ((k : ℝ) + 1)) + C := by
      change (∑ n ∈ Finset.Ico ((k : ℤ) * B + B) ((k : ℤ) * B + B + B),
          truncatedInv (X / (n : ℝ)) (intDistance (α * n))) ≤
          2 * X / (((k : ℤ) * B + B : ℤ) : ℝ) + C at hblock
      push_cast at hblock
      simpa only [hrecip] using hblock
    have hharm : (harmonic (k + 1) : ℝ) = (harmonic k : ℝ) + 1 / ((k : ℝ) + 1) := by
      rw [harmonic_succ]
      push_cast
      simp only [one_div]
    apply (add_le_add ih hblock').trans
    rw [hharm]
    push_cast
    ring_nf
    exact le_rfl

/-- A uniform hyperbolic reciprocal-distance bound. This is the scalar
Type-I estimate: the potentially large cap contributes `X/q`, not `X`. -/
theorem sum_truncatedInv_hyperbolic_le
    (α : ℝ) (a : ℤ) (q : ℕ) (hq : 0 < q)
    (hcop : IsCoprime a (q : ℤ))
    (happrox : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (X : ℝ) (hX : 0 ≤ X) (M : ℕ) :
    (∑ n ∈ Finset.Icc 1 (M : ℤ),
      truncatedInv (X / (n : ℝ)) (intDistance (α * n))) ≤
      8 * ((M : ℝ) + q) * (1 + Real.log (2 * (q : ℝ))) +
        (4 * X / (q : ℝ)) * (1 + Real.log ((M : ℝ) + 1)) := by
  let B : ℕ := q / 2 + 1
  let k : ℕ := M / B
  let C : ℝ := 4 * (q : ℝ) * (1 + Real.log (2 * (q : ℝ)))
  have hB : 0 < B := by dsimp [B]; omega
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hcover : (M : ℤ) < (k : ℤ) * B + B := by
    exact_mod_cast (Nat.lt_div_mul_add (a := M) hB)
  have hsub : Finset.Icc 1 (M : ℤ) ⊆ Finset.Ico 1 ((k : ℤ) * B + B) := by
    intro n hn
    have hh := Finset.mem_Icc.mp hn
    exact Finset.mem_Ico.mpr ⟨hh.1, hh.2.trans_lt hcover⟩
  have hsum := sum_truncatedInv_hyperbolic_prefix_blocks_le α a q hq hcop happrox X hX k
  have hsum' : (∑ n ∈ Finset.Icc 1 (M : ℤ),
      truncatedInv (X / (n : ℝ)) (intDistance (α * n))) ≤
        ((k : ℝ) + 2) * C + (2 * X / (B : ℝ)) * (harmonic k : ℝ) := by
    apply le_trans ?_ hsum
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro n hn _
    apply truncatedInv_nonneg
    · have hnpos : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Ico.mp hn).1
      positivity
    · exact intDistance_nonneg _
  have hqB : (q : ℝ) ≤ 2 * (B : ℝ) := by
    exact_mod_cast (show q ≤ 2 * B by dsimp [B]; omega)
  have hkB : (k : ℝ) * B ≤ M := by exact_mod_cast Nat.div_mul_le_self M B
  have hkq : (k : ℝ) * q ≤ 2 * (M : ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_left hqB (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hlogq : 0 ≤ 1 + Real.log (2 * (q : ℝ)) := by
    have hqone : (1 : ℝ) ≤ q := by exact_mod_cast hq
    have hh := Real.log_nonneg (show 1 ≤ 2 * (q : ℝ) by linarith)
    linarith
  have hCbound : ((k : ℝ) + 2) * C ≤
      8 * ((M : ℝ) + q) * (1 + Real.log (2 * (q : ℝ))) := by
    have hh := mul_le_mul_of_nonneg_right hkq hlogq
    dsimp [C]
    nlinarith
  have hA : 2 * X / (B : ℝ) ≤ 4 * X / (q : ℝ) := by
    apply (div_le_div_iff₀ hBr hqR).mpr
    nlinarith [mul_le_mul_of_nonneg_left hqB hX]
  have hharm : (harmonic k : ℝ) ≤ 1 + Real.log ((M : ℝ) + 1) := by
    have hkle : k ≤ M + 1 := (Nat.div_le_self M B).trans (by omega)
    have hmono : (harmonic k : ℝ) ≤ (harmonic (M + 1) : ℝ) := by
      simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hkle)
      intro n _ _
      positivity
    exact hmono.trans (by simpa only [Nat.cast_add, Nat.cast_one] using harmonic_le_one_add_log (M + 1))
  have hharm0 : (0 : ℝ) ≤ harmonic k := by
    simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    positivity
  exact hsum'.trans (add_le_add hCbound (mul_le_mul hA hharm hharm0 (by positivity)))

end Problem337.RationalPhaseSpacing

end

end OAI

-- Upstream module OAI.NumberTheory.EgyptianFractions.RealPhaseEnvelope

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337.RealPhase

/-- Distance to the nearest integer. The tie convention of `round` does not
affect this distance. -/
def integerDistance (x : ℝ) : ℝ := |x - round x|

lemma integerDistance_nonneg (x : ℝ) : 0 ≤ integerDistance x := abs_nonneg _

lemma abs_sin_fract (x : ℝ) :
    |Real.sin (Real.pi * Int.fract x)| = |Real.sin (Real.pi * x)| := by
  have he : Real.pi * Int.fract x = Real.pi * x - (⌊x⌋ : ℝ) * Real.pi := by
    simp only [Int.fract]
    ring
  rw [he, Real.sin_sub_int_mul_pi, abs_mul, abs_zpow]
  simp

/-- Jordan's sine inequality in the nearest-integer convention used by
Diophantine approximation and minor-arc spacing. -/
theorem two_integerDistance_le_abs_sin (x : ℝ) :
    2 * integerDistance x ≤ |Real.sin (Real.pi * x)| := by
  have hd : integerDistance x = min (Int.fract x) (1 - Int.fract x) :=
    abs_sub_round_eq_min x
  by_cases hzero : integerDistance x = 0
  · simp [hzero]
  have hp : 0 < integerDistance x :=
    lt_of_le_of_ne (integerDistance_nonneg x) (Ne.symm hzero)
  have hl : integerDistance x ≤ Int.fract x := by rw [hd]; exact min_le_left _ _
  have hr : Int.fract x ≤ 1 - integerDistance x := by
    have h := min_le_right (Int.fract x) (1 - Int.fract x)
    rw [← hd] at h
    linarith
  calc
    2 * integerDistance x ≤ Real.sin (Real.pi * Int.fract x) :=
      sin_pi_mul_lower_on_middle hp hl hr
    _ ≤ |Real.sin (Real.pi * Int.fract x)| := le_abs_self _
    _ = _ := abs_sin_fract x

/-- Period-one complex phase, with the same normalization as the standard
cyclic character and the circle-method Fourier sum. -/
def phase (x : ℝ) : ℂ := Complex.exp (Complex.I * (2 * Real.pi * x : ℝ))

lemma norm_phase (x : ℝ) : ‖phase x‖ = 1 :=
  Complex.norm_exp_I_mul_ofReal _

lemma phase_add (x y : ℝ) : phase (x + y) = phase x * phase y := by
  unfold phase
  rw [show Complex.I * (2 * Real.pi * (x + y) : ℝ) =
      Complex.I * (2 * Real.pi * x : ℝ) + Complex.I * (2 * Real.pi * y : ℝ) by
    push_cast; ring]
  exact Complex.exp_add _ _

lemma phase_nat_mul (x : ℝ) (n : ℕ) : phase ((n : ℝ) * x) = phase x ^ n := by
  unfold phase
  rw [show Complex.I * (2 * Real.pi * ((n : ℝ) * x) : ℝ) =
      (n : ℂ) * (Complex.I * (2 * Real.pi * x : ℝ)) by push_cast; ring]
  exact Complex.exp_nat_mul _ _

/-- A capped geometric envelope with the integer frequencies accounted for
explicitly, rather than assigning an invalid reciprocal at distance zero. -/
def envelope (N : ℕ) (x : ℝ) : ℝ :=
  if integerDistance x = 0 then N else min (N : ℝ) (1 / (2 * integerDistance x))

theorem norm_sum_phase_le_envelope (x : ℝ) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, phase ((n : ℝ) * x)‖ ≤ envelope N x := by
  simp_rw [phase_nat_mul]
  have hcap := norm_geometric_sum_le_card (norm_phase x) N
  by_cases hx : integerDistance x = 0
  · simpa [envelope, hx] using hcap
  simp only [envelope, ite_eq_right hx]
  refine le_min hcap ?_
  have hd : 0 < integerDistance x :=
    lt_of_le_of_ne (integerDistance_nonneg x) (Ne.symm hx)
  have hs := two_integerDistance_le_abs_sin x
  have hspos : 0 < |Real.sin (Real.pi * x)| := by linarith
  calc
    _ ≤ 1 / |Real.sin (Real.pi * x)| :=
      norm_geometric_phase_sum_le (abs_pos.mp hspos) N
    _ ≤ 1 / (2 * integerDistance x) :=
      one_div_le_one_div_of_le (by positivity) hs

/-- Translating the integer interval and adding a constant phase preserve
the norm, so the same envelope handles every interval location. -/
theorem norm_sum_shift_phase_eq (x β t : ℝ) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, phase (x * (t + n) + β)‖ =
      ‖∑ n ∈ Finset.range N, phase ((n : ℝ) * x)‖ := by
  have he : ∀ n : ℕ, phase (x * (t + n) + β) =
      phase (x * t + β) * phase ((n : ℝ) * x) := by
    intro n
    rw [← phase_add]
    congr 1
    ring
  simp_rw [he]
  rw [← Finset.mul_sum, norm_mul, norm_phase, one_mul]

theorem norm_sum_shift_phase_le_envelope (x β t : ℝ) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, phase (x * (t + n) + β)‖ ≤ envelope N x := by
  rw [norm_sum_shift_phase_eq]
  exact norm_sum_phase_le_envelope x N

end Problem337.RealPhase

end

end OAI

-- Upstream module OAI.NumberTheory.EgyptianFractions.RealTypeI

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337.RealTypeI

open RationalPhaseSpacing

lemma geometric_envelope_le_truncated_real (t : ℝ) (M : ℕ) (cap : ℝ)
    (hM : (M : ℝ) ≤ cap) :
    RealPhase.envelope M t ≤ truncatedInv cap (intDistance t) := by
  have heq : RealPhase.integerDistance t = intDistance t := abs_sub_round_eq_min t
  unfold RealPhase.envelope
  rw [heq]
  unfold truncatedInv
  split_ifs with hzero
  · exact hM
  · have hd : 0 < intDistance t :=
      lt_of_le_of_ne (intDistance_nonneg _) (Ne.symm hzero)
    exact min_le_min hM (one_div_le_one_div_of_le hd (by linarith))

/-- The explicit scalar cost of a hyperbolic Type I sum. -/
def hyperbolicCost (X : ℝ) (M q : ℕ) : ℝ :=
  8 * ((M : ℝ) + q) * (1 + Real.log (2 * (q : ℝ))) +
    (4 * X / (q : ℝ)) * (1 + Real.log ((M : ℝ) + 1))

end Problem337.RealTypeI

end

end OAI

-- Upstream module OAI.NumberTheory.EgyptianFractions.VaughanRealTypeIHyperbolic

namespace OAI
/-!
# Actual near-rational estimates for the two Vaughan Type I terms

The initial-sum estimate uses the sharper canonical harmonic hyperbola bound
for its scalar aggregation.
The variable hyperbolic lengths are retained throughout.  In particular the
right hand side has size `N / q + A + q`, up to logarithmic factors, rather
than the much larger fixed-cap estimate obtained by replacing every `N / d`
with `N`.
-/

noncomputable section
open scoped BigOperators ArithmeticFunction ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace Problem337.VaughanHyperbolic

open Vaughan

open RationalPhaseSpacing

/-- Every truncated hyperbolic inner sum has the required variable-cap envelope.
This includes the zero-frequency case and does not require a nonresonance
assumption. -/
theorem norm_phase_Ioc_mul_le_variable (α : ℝ) (N d k : ℕ) (hk : k ≤ N / d) :
    ‖∑ b ∈ Finset.Ioc 0 k, RealPhase.phase (α * (d * b : ℕ))‖ ≤
      truncatedInv ((N : ℝ) / d) (intDistance (α * d)) := by
  have heq : (∑ b ∈ Finset.Ioc 0 k, RealPhase.phase (α * (d * b : ℕ))) =
      ∑ j ∈ Finset.range k, RealPhase.phase ((α * d) * (1 + j) + 0) := by
    rw [sum_Ioc_zero_eq_sum_range_succ]
    apply Finset.sum_congr rfl
    intro j hj
    congr 1
    push_cast
    ring
  rw [heq]
  exact (RealPhase.norm_sum_shift_phase_le_envelope (α * d) 0 1 k).trans
    (RealTypeI.geometric_envelope_le_truncated_real (α * d) k ((N : ℝ) / d)
      ((by exact_mod_cast hk : (k : ℝ) ≤ (N / d : ℕ)).trans Nat.cast_div_le))

/-- The positive-initial-interval convention used by Vaughan's identity. -/
theorem sum_variable_reciprocal_Ioc_le
    (α : ℝ) (a : ℤ) (q : ℕ) (hq : 0 < q)
    (hcop : IsCoprime a (q : ℤ))
    (happrox : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (N A : ℕ) :
    (∑ d ∈ Finset.Ioc 0 A,
      truncatedInv ((N : ℝ) / d) (intDistance (α * d))) ≤
      RealTypeI.hyperbolicCost (N : ℝ) A q := by
  have hcast : (∑ d ∈ Finset.Ioc 0 A,
      truncatedInv ((N : ℝ) / d) (intDistance (α * d))) =
      ∑ d ∈ Finset.Icc 1 (A : ℤ),
        truncatedInv ((N : ℝ) / d) (intDistance (α * d)) := by
    apply Finset.sum_nbij' (fun d : ℕ => (d : ℤ)) Int.toNat
    · intro d hd
      obtain ⟨hd0, hdA⟩ := Finset.mem_Ioc.mp hd
      exact Finset.mem_Icc.mpr ⟨by exact_mod_cast hd0, by exact_mod_cast hdA⟩
    · intro d hd
      obtain ⟨hd1, hdA⟩ := Finset.mem_Icc.mp hd
      apply Finset.mem_Ioc.mpr
      omega
    · intro d hd
      exact Int.toNat_natCast d
    · intro d hd
      exact Int.toNat_of_nonneg (by have := (Finset.mem_Icc.mp hd).1; omega)
    · intro d hd
      simp
  rw [hcast]
  exact sum_truncatedInv_hyperbolic_le α a q hq hcop happrox N (Nat.cast_nonneg N) A

/-- The first actual Vaughan convolution, with its logarithmic inner weight,
is bounded using only a reduced rational approximation to the frequency. -/
theorem first_typeI_real_phase_bound
    (α : ℝ) (a : ℤ) (q : ℕ) (hq : 0 < q)
    (hcop : IsCoprime a (q : ℤ))
    (happrox : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (N U : ℕ) :
    ‖weightedSum (Finset.Ioc 0 N) (fun n => RealPhase.phase (α * n))
        (shortPart U (μ : ArithmeticFunction ℝ) * ArithmeticFunction.log)‖ ≤
      2 * Real.log N * RealTypeI.hyperbolicCost (N : ℝ) (min U N) q := by
  apply (first_typeI_bound (fun n => RealPhase.phase (α * n)) N U
    (fun d => truncatedInv ((N : ℝ) / d) (intDistance (α * d)))
    (fun d _ k hk => norm_phase_Ioc_mul_le_variable α N d k hk)).trans
  exact mul_le_mul_of_nonneg_left
    (sum_variable_reciprocal_Ioc_le α a q hq hcop happrox N (min U N))
    (by positivity)

/-- The second actual Vaughan convolution has one logarithmic coefficient
factor and the same variable-length reciprocal budget. -/
theorem second_typeI_real_phase_bound
    (α : ℝ) (a : ℤ) (q : ℕ) (hq : 0 < q)
    (hcop : IsCoprime a (q : ℤ))
    (happrox : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (N U V : ℕ) :
    ‖weightedSum (Finset.Ioc 0 N) (fun n => RealPhase.phase (α * n))
        (typeICoefficient U V * ζ)‖ ≤
      Real.log N * RealTypeI.hyperbolicCost (N : ℝ) (min (U * V) N) q := by
  apply (second_typeI_bound (fun n => RealPhase.phase (α * n)) N U V
    (fun d => truncatedInv ((N : ℝ) / d) (intDistance (α * d)))
    (fun d _ => norm_phase_Ioc_mul_le_variable α N d (N / d) le_rfl)).trans
  exact mul_le_mul_of_nonneg_left
    (sum_variable_reciprocal_Ioc_le α a q hq hcop happrox N (min (U * V) N))
    (Real.log_natCast_nonneg N)

end Problem337.VaughanHyperbolic

end

end OAI

-- Upstream module OAI.NumberTheory.EgyptianFractions.VaughanTypeINormalized

namespace OAI
noncomputable section
open scoped BigOperators ArithmeticFunction ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace Problem337.VaughanHyperbolic

/-- A common logarithmic majorant for both actual Type I costs. -/
theorem hyperbolicCost_min_le (N A q : ℕ) (hN : 1 ≤ N) (hq : 0 < q)
    (hqN : q ≤ N) :
    RealTypeI.hyperbolicCost N (min A N) q ≤
      8 * ((N : ℝ) / q + A + q) * (1 + Real.log (2 * (N : ℝ))) := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hqr : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hqNr : (q : ℝ) ≤ N := by exact_mod_cast hqN
  have hminA : ((min A N : ℕ) : ℝ) ≤ A := by exact_mod_cast min_le_left A N
  have hminN : ((min A N : ℕ) : ℝ) ≤ N := by exact_mod_cast min_le_right A N
  have hlogq : 0 ≤ 1 + Real.log (2 * (q : ℝ)) := by
    have := Real.log_nonneg (show 1 ≤ 2 * (q : ℝ) by linarith)
    linarith
  have hH : 0 ≤ 1 + Real.log (2 * (N : ℝ)) := by
    have := Real.log_nonneg (show 1 ≤ 2 * (N : ℝ) by linarith)
    linarith
  have hlogqN : 1 + Real.log (2 * (q : ℝ)) ≤
      1 + Real.log (2 * (N : ℝ)) := by
    gcongr
  have hlogmin : 1 + Real.log (((min A N : ℕ) : ℝ) + 1) ≤
      1 + Real.log (2 * (N : ℝ)) := by
    exact add_le_add le_rfl (Real.log_le_log (by positivity) (by linarith))
  unfold RealTypeI.hyperbolicCost
  calc
    _ ≤ 8 * ((A : ℝ) + q) * (1 + Real.log (2 * (N : ℝ))) +
        (4 * (N : ℝ) / q) * (1 + Real.log (2 * (N : ℝ))) := by
      apply add_le_add
      · exact mul_le_mul (by gcongr) hlogqN hlogq (by positivity)
      · exact mul_le_mul_of_nonneg_left hlogmin (by positivity)
    _ ≤ _ := by
      have hd : 0 ≤ (N : ℝ) / q := by positivity
      simp only [mul_div_assoc]
      nlinarith [mul_nonneg hd hH]

private lemma log_le_common (N : ℕ) (hN : 1 ≤ N) :
    Real.log N ≤ 1 + Real.log (2 * (N : ℝ)) := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have h := Real.log_le_log (show 0 < (N : ℝ) by linarith)
    (show (N : ℝ) ≤ 2 * N by linarith)
  linarith

/-- Uniform Type I bound in the parameters of the optimized Vaughan cutoff. -/
theorem first_typeI_normalized_bound
    (α : ℝ) (a : ℤ) (q : ℕ) (hq : 0 < q)
    (hcop : IsCoprime a (q : ℤ))
    (happrox : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (N U : ℕ) (hN : 1 ≤ N) (hqN : q ≤ N) :
    ‖Vaughan.weightedSum (Finset.Ioc 0 N) (fun n => RealPhase.phase (α * n))
        (Vaughan.shortPart U (μ : ArithmeticFunction ℝ) * ArithmeticFunction.log)‖ ≤
      16 * (1 + Real.log (2 * (N : ℝ))) ^ 2 * ((N : ℝ) / q + U + q) := by
  have hH : 0 ≤ 1 + Real.log (2 * (N : ℝ)) :=
    (Real.log_natCast_nonneg N).trans (log_le_common N hN)
  calc
    _ ≤ 2 * Real.log N * RealTypeI.hyperbolicCost N (min U N) q :=
      first_typeI_real_phase_bound α a q hq hcop happrox N U
    _ ≤ 2 * Real.log N *
        (8 * ((N : ℝ) / q + U + q) * (1 + Real.log (2 * (N : ℝ)))) :=
      mul_le_mul_of_nonneg_left (hyperbolicCost_min_le N U q hN hq hqN) (by positivity)
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_right (log_le_common N hN)
        (show 0 ≤ 16 * ((N : ℝ) / q + U + q) *
          (1 + Real.log (2 * (N : ℝ))) by positivity)
      nlinarith

/-- Uniform second Type I bound with the full product support retained. -/
theorem second_typeI_normalized_bound
    (α : ℝ) (a : ℤ) (q : ℕ) (hq : 0 < q)
    (hcop : IsCoprime a (q : ℤ))
    (happrox : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (N U V : ℕ) (hN : 1 ≤ N) (hqN : q ≤ N) :
    ‖Vaughan.weightedSum (Finset.Ioc 0 N) (fun n => RealPhase.phase (α * n))
        (Vaughan.typeICoefficient U V * ζ)‖ ≤
      8 * (1 + Real.log (2 * (N : ℝ))) ^ 2 * ((N : ℝ) / q + U * V + q) := by
  have hH : 0 ≤ 1 + Real.log (2 * (N : ℝ)) :=
    (Real.log_natCast_nonneg N).trans (log_le_common N hN)
  calc
    _ ≤ Real.log N * RealTypeI.hyperbolicCost N (min (U * V) N) q :=
      second_typeI_real_phase_bound α a q hq hcop happrox N U V
    _ ≤ Real.log N *
        (8 * ((N : ℝ) / q + (U * V : ℕ) + q) * (1 + Real.log (2 * (N : ℝ)))) :=
      mul_le_mul_of_nonneg_left (hyperbolicCost_min_le N (U * V) q hN hq hqN)
        (Real.log_natCast_nonneg N)
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_right (log_le_common N hN)
        (show 0 ≤ 8 * ((N : ℝ) / q + U * V + q) *
          (1 + Real.log (2 * (N : ℝ))) by positivity)
      push_cast
      nlinarith

end Problem337.VaughanHyperbolic

end

end OAI

-- Upstream module OAI.NumberTheory.EgyptianFractions.VaughanEstimate

namespace OAI
noncomputable section
open scoped BigOperators ArithmeticFunction ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace Problem337.Vaughan

lemma realPhase_eq_bilinear_phase (x : ℝ) :
    RealPhase.phase x = VaughanBilinear.phase x :=
  (VaughanBilinear.phase_eq_geometric_phase x).symm

lemma optimized_typeI_scales (X q : ℝ) (hX : 1 ≤ X) (hq : 1 ≤ q)
    (hqX : q ≤ X) (hpow : 2 ≤ X ^ (2 / 5 : ℝ)) :
    X / q + (optimizedCutoff X : ℝ) + q ≤ 4 * approximationEnvelope X q ∧
    X / q + (optimizedCutoff X : ℝ) ^ 2 + q ≤ 4 * approximationEnvelope X q := by
  have hs := optimizedCutoff_standard_envelope X q hX hq hqX hpow
  have hdiv : 0 ≤ X / Real.sqrt (optimizedCutoff X : ℝ) := by positivity
  change _ ≤ 4 * approximationEnvelope X q at hs
  constructor <;> nlinarith [Nat.cast_nonneg (optimizedCutoff X) (α := ℝ),
    sq_nonneg (optimizedCutoff X : ℝ)]

/-- An explicit classical Vaughan estimate for the actual von Mangoldt
exponential sum. The only analytic input is a reduced rational approximation;
all Type I and Type II cancellation estimates have been proved above. -/
theorem vonMangoldt_sum_bound
    (θ : ℝ) (a : ℤ) (q : ℕ) (hq : 0 < q)
    (hcop : IsCoprime a (q : ℤ))
    (happrox : |θ - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (N : ℕ) (hqN : q ≤ N)
    (hpow : 2 ≤ (N : ℝ) ^ (2 / 5 : ℝ)) :
    ‖weightedSum (Finset.Ioc 0 N) (fun k => VaughanBilinear.phase (θ * k)) Λ‖ ≤
      200 * (typeIILogScale N) ^ 4 * approximationEnvelope N q := by
  let U := optimizedCutoff (N : ℝ)
  let w : ℕ → ℂ := fun k => VaughanBilinear.phase (θ * k)
  let H := typeIILogScale N
  let E := approximationEnvelope (N : ℝ) q
  have hN : 1 ≤ N := hq.trans_le hqN
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hqr : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hqNr : (q : ℝ) ≤ N := by exact_mod_cast hqN
  have hH : 1 ≤ H := one_le_typeIILogScale N
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  have hE : 0 ≤ E := approximationEnvelope_nonneg N q (Nat.cast_nonneg N)
  have hH14 : H ≤ H ^ 4 := by
    simpa using (pow_le_pow_right₀ hH (show 1 ≤ 4 by omega))
  have hH24 : H ^ 2 ≤ H ^ 4 := pow_le_pow_right₀ hH (by omega)
  have hcost := optimized_typeI_scales N q hNr hqr hqNr hpow
  have hfirst := VaughanHyperbolic.first_typeI_normalized_bound θ a q hq hcop happrox
    N U hN hqN
  have hsecond := VaughanHyperbolic.second_typeI_normalized_bound θ a q hq hcop happrox
    N U U hN hqN
  simp only [realPhase_eq_bilinear_phase] at hfirst hsecond
  have h1 : ‖weightedSum (Finset.Ioc 0 N) w
      (shortPart U (μ : ArithmeticFunction ℝ) * ArithmeticFunction.log)‖ ≤ 64 * H ^ 4 * E := by
    calc
      _ ≤ 16 * H ^ 2 * ((N : ℝ) / q + U + q) := hfirst
      _ ≤ 16 * H ^ 2 * (4 * E) := mul_le_mul_of_nonneg_left hcost.1 (by positivity)
      _ ≤ 64 * H ^ 4 * E := by nlinarith [mul_le_mul_of_nonneg_right hH24 hE]
  have h2 : ‖weightedSum (Finset.Ioc 0 N) w (typeICoefficient U U * ζ)‖ ≤
      32 * H ^ 4 * E := by
    calc
      _ ≤ 8 * H ^ 2 * ((N : ℝ) / q + (U : ℝ) ^ 2 + q) := by
        simpa only [H, typeIILogScale, w, pow_two] using hsecond
      _ ≤ 8 * H ^ 2 * (4 * E) := mul_le_mul_of_nonneg_left hcost.2 (by positivity)
      _ ≤ 32 * H ^ 4 * E := by nlinarith [mul_le_mul_of_nonneg_right hH24 hE]
  have h0 : ‖weightedSum (Finset.Ioc 0 N) w (shortPart U Λ)‖ ≤ H ^ 4 * E := by
    have hlog : Real.log N ≤ H ^ 4 := (log_nat_le_typeIILogScale N N le_rfl).trans hH14
    have hpower : (N : ℝ) ^ (4 / 5 : ℝ) ≤ E := by
      dsimp [E, approximationEnvelope]
      have hd : 0 ≤ (N : ℝ) / Real.sqrt q := by positivity
      linarith [Real.sqrt_nonneg ((N : ℝ) * q)]
    calc
      _ ≤ (U : ℝ) * Real.log U := norm_short_vonMangoldt_sum_le N U w (by
        intro n hn
        simp [w])
      _ ≤ (N : ℝ) ^ (4 / 5 : ℝ) * Real.log N := optimizedCutoff_log_le N hNr hpow
      _ ≤ E * H ^ 4 := mul_le_mul hpower hlog (Real.log_natCast_nonneg N) hE
      _ = _ := by ring
  have hII : ‖weightedSum (Finset.Ioc 0 N) w (typeIICoefficient U * longPart U Λ)‖ ≤
      54 * H ^ 4 * E := optimized_typeII_bound θ a q hq hcop happrox N hqN hpow
  change ‖weightedSum (Finset.Ioc 0 N) w Λ‖ ≤ 200 * H ^ 4 * E
  rw [weighted_identity (Finset.Ioc 0 N) w U U]
  calc
    _ ≤ (‖weightedSum (Finset.Ioc 0 N) w (shortPart U Λ)‖ +
        ‖weightedSum (Finset.Ioc 0 N) w
          (shortPart U (μ : ArithmeticFunction ℝ) * ArithmeticFunction.log)‖) +
        ‖weightedSum (Finset.Ioc 0 N) w (typeICoefficient U U * ζ)‖ +
        ‖weightedSum (Finset.Ioc 0 N) w (typeIICoefficient U * longPart U Λ)‖ := by
      apply (norm_add_le _ _).trans
      apply add_le_add _ le_rfl
      apply (norm_sub_le _ _).trans
      exact add_le_add (norm_add_le _ _) le_rfl
    _ ≤ _ := by nlinarith [mul_nonneg (pow_nonneg hH0 4) hE]

/-- The ordinary logarithmic form of the classical Vaughan estimate. -/
theorem vonMangoldt_sum_log_bound
    (θ : ℝ) (a : ℤ) (q : ℕ) (hq : 0 < q)
    (hcop : IsCoprime a (q : ℤ))
    (happrox : |θ - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (N : ℕ) (hqN : q ≤ N)
    (hpow : 2 ≤ (N : ℝ) ^ (2 / 5 : ℝ)) (hlog : 1 ≤ Real.log N) :
    ‖weightedSum (Finset.Ioc 0 N) (fun k => VaughanBilinear.phase (θ * k)) Λ‖ ≤
      16200 * (Real.log N) ^ 4 * approximationEnvelope N q := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hq.trans_le hqN
  have hH : typeIILogScale N ≤ 3 * Real.log N := by
    unfold typeIILogScale
    rw [Real.log_mul (by norm_num) hNr.ne']
    linarith [Real.log_two_lt_d9]
  have hH0 : 0 ≤ typeIILogScale N := zero_le_one.trans (one_le_typeIILogScale N)
  have hE := approximationEnvelope_nonneg N q (Nat.cast_nonneg N)
  refine (vonMangoldt_sum_bound θ a q hq hcop happrox N hqN hpow).trans ?_
  calc
    _ ≤ 200 * (3 * Real.log N) ^ 4 * approximationEnvelope N q := by gcongr
    _ = _ := by ring

open Filter in
/-- The estimate holds uniformly in every reduced approximation once the
summation length is large, with an absolute explicit constant. -/
theorem eventually_vonMangoldt_sum_log_bound :
    ∀ᶠ N : ℕ in atTop, ∀ (θ : ℝ) (a : ℤ) (q : ℕ), 0 < q →
      IsCoprime a (q : ℤ) → |θ - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2 → q ≤ N →
      ‖weightedSum (Finset.Ioc 0 N) (fun k => VaughanBilinear.phase (θ * k)) Λ‖ ≤
        16200 * (Real.log N) ^ 4 * approximationEnvelope N q := by
  have hlog : ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log (N : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (1 : ℝ))
  have hpow : ∀ᶠ N : ℕ in atTop, 2 ≤ (N : ℝ) ^ (2 / 5 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 5)).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop (2 : ℝ))
  filter_upwards [hlog, hpow] with N hlog hpow
  intro θ a q hq hcop happrox hqN
  exact vonMangoldt_sum_log_bound θ a q hq hcop happrox N hqN hpow hlog

end Problem337.Vaughan

end

end OAI

open Filter

/-- The dyadic logarithm dominates the natural logarithm at this cutoff. -/
private theorem log_le_dyadic {n : ℕ} (hn : 8 ≤ n) :
    Real.log n ≤ (Nat.log 2 (n + 2) : ℝ) := by
  let k := Nat.log 2 (n+2)
  have hk : 3 ≤ k := Nat.le_log_of_pow_le (by decide) (by norm_num; omega)
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hpow : n < 2 ^ (k+1) := by have := Nat.lt_pow_succ_log_self (by decide : 1 < 2) (n+2); dsimp [k]; omega
  have hl := Real.log_le_log hnpos (by exact_mod_cast hpow.le : (n:ℝ) ≤ 2^(k+1))
  rw [Real.log_pow] at hl
  push_cast at hl
  have hlog : Real.log 2 ≤ 3/4 := by linarith [Real.log_two_lt_d9]
  have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
  change _ ≤ (k:ℝ)
  calc _ ≤ ((k:ℝ)+1)*Real.log 2 := hl
       _ ≤ (k+1)*(3/4:ℝ) := by gcongr
       _ ≤ k := by linarith

/-- The cutoff absorbs the logarithmic loss in Vaughan's estimate. -/
private theorem cutoff_sqrt_lower {A : ℝ} {n : ℕ} (hn : 8 ≤ n) (hL : 1 ≤ Real.log n) :
    (Real.log n) ^ (A+8) ≤ Real.sqrt (((Nat.log 2 (n+2))^(2*⌈A⌉₊+16) : ℕ) : ℝ) := by
  let k := Nat.log 2 (n+2)
  have h := log_le_dyadic hn
  have e : 2*⌈A⌉₊+16 = (⌈A⌉₊+8)*2 := by omega
  rw [e, pow_mul, Nat.cast_pow, Real.sqrt_sq (by positivity)]
  calc (Real.log n)^(A+8) ≤ (Real.log n)^((⌈A⌉₊:ℝ)+8) :=
        Real.rpow_le_rpow_of_exponent_le hL (by linarith [Nat.le_ceil A])
       _ = (Real.log n)^(⌈A⌉₊+8 : ℕ) := by norm_cast
       _ ≤ _ := by push_cast; gcongr

/-- For small and large rational denominators the two endpoint terms in the
classical Vaughan estimate are simultaneously controlled by the same cutoff. -/
private theorem vaughan_denominator_terms {x q P T : ℝ} (hx : 0 < x) (hT : 0 < T)
    (hP : 0 < P) (hTsize : T ≤ Real.sqrt P) (hlow : P ≤ q) (hhigh : q ≤ x/P) :
    x / Real.sqrt q ≤ x/T ∧ Real.sqrt (x*q) ≤ x/T := by
  have hq := hP.trans_le hlow
  have hT2 : T^2 ≤ P := (Real.le_sqrt (by positivity) hP.le).mp hTsize
  constructor
  · exact div_le_div_of_nonneg_left hx.le hT (hTsize.trans (Real.sqrt_le_sqrt hlow))
  · apply (Real.sqrt_le_iff).mpr
    refine ⟨by positivity, ?_⟩
    rw [div_pow, le_div_iff₀ (by positivity)]
    have hprod := (le_div_iff₀ hP).mp hhigh
    nlinarith only [mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hT2 hq.le) hx.le,
      mul_le_mul_of_nonneg_left hprod hx.le]

private theorem minor_approximant (Q n : ℕ) (t : ℝ) (hQ : 1 ≤ Q) (hQn : Q ≤ n)
    (ht : t ∈ Set.Icc (0:ℝ) 1)
    (hminor : t ∉ {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Q ∧ a ≤ q ∧ a.Coprime q ∧
      |t - a/(q:ℝ)| ≤ (Q:ℝ)/(q*n)}) :
    ∃ q a : ℕ, Q < q ∧ q ≤ n / Q ∧ a ≤ q ∧ a.Coprime q ∧
      |t - a/(q:ℝ)| ≤ 1 / ((q:ℝ)*((n/Q : ℕ)+1 : ℝ)) := by
  let B := n / Q
  have hB : 0 < B := Nat.div_pos hQn hQ
  obtain ⟨s,hs,hd⟩ := Real.exists_rat_abs_sub_le_and_den_le t hB
  have hdpos : (0 : ℝ) < s.den := Nat.cast_pos.mpr s.pos
  have hBpos : (0 : ℝ) < B := Nat.cast_pos.mpr hB
  have hQB : (0 : ℝ) < Q := Nat.cast_pos.mpr hQ
  have hnp : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  rw [Rat.cast_def, mul_comm ((B : ℝ) + 1) (s.den : ℝ)] at hs
  have hclose : |t * s.den - s.num| < 1 := by
    have h := (mul_le_mul_of_nonneg_right hs hdpos.le)
    rw [← abs_of_pos hdpos, ← abs_mul, abs_of_pos hdpos] at h
    rw [sub_mul, div_mul_cancel₀ _ hdpos.ne'] at h
    refine h.trans_lt ?_
    rw [div_mul_eq_mul_div, one_mul, div_lt_one (by positivity)]
    nlinarith
  obtain ⟨hl,hu⟩ := abs_lt.mp hclose
  have ht0 : 0 ≤ t * s.den := mul_nonneg ht.1 hdpos.le
  have ht1 : t * s.den ≤ s.den := by simpa using mul_le_mul_of_nonneg_right ht.2 hdpos.le
  have hnlo : (-1 : ℤ) < s.num := by exact_mod_cast (show (-1 : ℝ) < s.num by linarith)
  have hnhi : s.num < (s.den : ℤ) + 1 := by exact_mod_cast (show (s.num : ℝ) < s.den + 1 by linarith)
  have hcast : (s.num.natAbs : ℤ) = s.num := by rw [Int.natCast_natAbs, abs_of_nonneg (by omega)]
  have hcast' : (s.num.natAbs : ℝ) = s.num := by
    calc (s.num.natAbs : ℝ) = ((s.num.natAbs : ℤ) : ℝ) := by simp
         _ = _ := congrArg (fun z : ℤ => (z : ℝ)) hcast
  have hle : s.num.natAbs ≤ s.den := by exact_mod_cast (show (s.num.natAbs : ℤ) ≤ s.den by omega)
  rw [← hcast'] at hs
  refine ⟨s.den, s.num.natAbs, ?_, hd, hle, s.reduced, hs⟩
  by_contra! hsmall
  apply hminor
  refine ⟨s.den, s.num.natAbs, s.pos, hsmall, hle, s.reduced, hs.trans ?_⟩
  have hbound : (n : ℝ) < Q * ((B : ℝ) + 1) := by exact_mod_cast Nat.lt_mul_div_succ n hQ
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith only [mul_le_mul_of_nonneg_left hbound.le hdpos.le]

/-- For fixed B even the enlarged logarithmic cutoff is eventually smaller than n. -/
private theorem cutoff_eventually_le (B : ℕ) : ∀ᶠ n : ℕ in atTop, (Nat.log 2 (n+2))^B ≤ n := by
  have asy := (isLittleO_log_rpow_rpow_atTop (B : ℝ) (by norm_num : (0:ℝ) < 1)).comp_tendsto
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have hbound := asy.bound (show 0 < (4:ℝ)⁻¹^B by positivity)
  filter_upwards [hbound,eventually_ge_atTop (2:ℕ)] with n hn hn2
  have hnpos : 0 < (n:ℝ) := Nat.cast_pos.mpr (by omega)
  have hN : 2 ≤ (n:ℝ) := by exact_mod_cast hn2
  have hlog := Real.log_nonneg (by linarith : 1 ≤ (n:ℝ))
  have hlog' : 0 ≤ Real.log (n+2:ℝ) := Real.log_nonneg (by linarith)
  have hnat := Real.natLog_le_logb (n+2) 2
  simp only [Nat.cast_ofNat, Nat.cast_add, Real.logb] at hnat
  have h₂ := Real.log_two_gt_d9
  have hlog2 : 0 < Real.log 2 := by linarith
  have hh := (le_div_iff₀ hlog2).mp hnat
  have harg := Real.log_le_log (by positivity : 0 < (n : ℝ)+2) (show (n:ℝ)+2 ≤ (n:ℝ)^2 by nlinarith)
  rw [Real.log_pow] at harg
  have hcut : (Nat.log 2 (n + 2) : ℝ) ≤ 4 * Real.log n := by
    norm_num1 at harg
    nlinarith only [mul_nonneg (Nat.cast_nonneg (Nat.log 2 (n+2)) : (0:ℝ) ≤ _) (show 0 ≤ Real.log 2 - 1/2 by linarith), hh, harg]
  change ‖(Real.log (n:ℝ))^(B:ℝ)‖ ≤ _ * ‖(n:ℝ)^(1:ℝ)‖ at hn
  simp only [Real.rpow_natCast,Real.rpow_one,Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hlog B),abs_of_nonneg hnpos.le] at hn
  have hpow := pow_le_pow_left₀ (Nat.cast_nonneg (α:=ℝ) _) hcut B
  rw [mul_pow] at hpow
  have hpos : 0 < (4:ℝ)^B := by positivity
  rw [inv_pow,inv_mul_eq_div] at hn
  have hlast : (Nat.log 2 (n+2) : ℝ)^B ≤ (n:ℝ) :=
    hpow.trans (by simpa only [mul_comm] using (le_div_iff₀ hpos).mp hn)
  exact_mod_cast hlast

/-- Absorb the numerical constant and the prime-power error while retaining half of
    the target on each side of the transfer. -/
private theorem log_budgets (A : ℝ) : ∀ᶠ n : ℕ in atTop,
    1 ≤ Real.log n ∧ 100000 ≤ (Real.log n)^4 ∧
    (Real.log n)^(A+8) ≤ (n:ℝ)^(1/5:ℝ) ∧
    (Real.log n)^(A+1) ≤ (1/4:ℝ)*Real.sqrt n := by
  have ht := tendsto_natCast_atTop_atTop (R:=ℝ)
  have h1 := ((isLittleO_log_rpow_rpow_atTop (A+8) (by norm_num : (0:ℝ)<1/5)).comp_tendsto ht).bound one_pos
  have h2 := ((isLittleO_log_rpow_rpow_atTop (A+1) (by norm_num : (0:ℝ)<1/2)).comp_tendsto ht).bound (by norm_num : (0:ℝ)<1/4)
  filter_upwards [(Real.tendsto_log_atTop.comp ht).eventually_ge_atTop 20, h1, h2] with n hn hh hhh
  change 20 ≤ Real.log n at hn
  have h0 : 0 ≤ Real.log n := by linarith
  have hpow : (20:ℝ)^4 ≤ (Real.log n)^4 := pow_le_pow_left₀ (by norm_num) hn _
  refine ⟨by linarith, by norm_num at hpow; linarith, ?_, ?_⟩
  · simpa only [Function.comp_apply, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg h0 _), abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _), one_mul] using hh
  · rw [Real.sqrt_eq_rpow]; simpa only [Function.comp_apply,Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg h0 _), abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)] using hhh

private theorem envelope_budget {x q P L A : ℝ} (hx : 0 < x) (hL : 1 ≤ L) (hP : 0 < P)
    (hlow : P ≤ q) (hhigh : q ≤ x/P) (hsqrt : L^(A+8) ≤ Real.sqrt P)
    (hxsmall : L^(A+8) ≤ x^(1/5:ℝ)) (habsorb : 100000 ≤ L^4) :
    16200 * L^4 * (x / Real.sqrt q + x^(4/5:ℝ) + Real.sqrt (x*q)) ≤ (1/2:ℝ)*x*L^(-A) := by
  have hLp : 0 < L := by linarith
  have hT : 0 < L^(A+8) := Real.rpow_pos_of_pos hLp _
  obtain ⟨h1,h3⟩ := vaughan_denominator_terms hx hT hP hsqrt hlow hhigh
  have h2 : x^(4/5:ℝ) ≤ x / L^(A+8) := by
    apply (le_div_iff₀ hT).mpr
    calc x^(4/5:ℝ)*L^(A+8) ≤ x^(4/5:ℝ)*x^(1/5:ℝ) := by gcongr
         _ = x := by rw [← Real.rpow_add hx]; norm_num
  have hsum := add_le_add (add_le_add h1 h2) h3
  have fact : L^(A+8) = L^A * L^4 * L^4 := by
    rw [Real.rpow_add hLp]; norm_num; ring
  rw [Real.rpow_neg hLp.le]
  calc _ ≤ 16200*L^4*(3*(x/L^(A+8))) := by gcongr; linarith only [hsum]
       _ ≤ (1/2:ℝ)*x*(L^A)⁻¹ := by
         rw [fact]
         have hp := Real.rpow_pos_of_pos hLp A
         field_simp
         linarith only [habsorb]

private theorem residual_budget {x L A : ℝ} (hx : 0 < x) (hL : 0 < L)
    (hlog : L^(A+1) ≤ (1/4:ℝ)*Real.sqrt x) :
    2*Real.sqrt x*L ≤ (1/2:ℝ)*x*L^(-A) := by
  rw [Real.rpow_neg hL.le, ← div_eq_mul_inv]
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hL _)).mpr
  rw [Real.rpow_add_one hL.ne'] at hlog
  nlinarith only [mul_le_mul_of_nonneg_left hlog (Real.sqrt_nonneg x), Real.sq_sqrt hx.le]

private theorem mangoldt_pointwise_bridge (n : ℕ) (hn : 1 ≤ n) (t : ℝ) :
    let w := fun k : ℕ => if k.Prime then Real.log (k : ℝ) else 0
    let e := fun x : ℝ => Complex.exp (((2*Real.pi*x : ℝ):ℂ)*Complex.I)
    ‖∑ k ∈ Finset.range (n+1), ((ArithmeticFunction.vonMangoldt k - w k : ℝ):ℂ) * e ((k:ℝ)*t)‖ ≤
      2 * Real.sqrt n * Real.log n := by
  intro w e
  have hnon (k : ℕ) : 0 ≤ ArithmeticFunction.vonMangoldt k - w k := by
    by_cases hk : k.Prime <;> simp [w,hk,ArithmeticFunction.vonMangoldt_apply_prime]
  calc
    _ ≤ ∑ k ∈ Finset.range (n+1), ‖((ArithmeticFunction.vonMangoldt k - w k : ℝ):ℂ) * e ((k:ℝ)*t)‖ := norm_sum_le _ _
    _ = ∑ k ∈ Finset.range (n+1), (ArithmeticFunction.vonMangoldt k - w k) := by
      simp only [norm_mul,e,Complex.norm_exp_ofReal_mul_I,mul_one,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hnon _)]
    _ = Chebyshev.psi n - Chebyshev.theta n := by
      rw [Nat.range_succ_eq_Icc_zero, ← Finset.add_sum_Ioc_eq_sum_Icc (Nat.zero_le n)]
      simp [Chebyshev.psi,Chebyshev.theta,w,Finset.sum_filter,Finset.sum_sub_distrib]
    _ ≤ _ := Chebyshev.psi_sub_theta_le (by exact_mod_cast hn)

theorem GoldbachEstermann.uniformMinorSum :
    let w (k : ℕ) := if Nat.Prime k then Real.log (k : ℝ) else 0; let E (x : ℝ) := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I); let S (n : ℕ) (u : ℕ → ℝ) (t : ℝ) := ∑ k ∈ Finset.range (n + 1), (u k : ℂ) * E ((k : ℝ) * t); let Qpow (B n : ℕ) := (Nat.log 2 (n + 2)) ^ B; let arcsPoly (B n : ℕ) := {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Qpow B n ∧ a ≤ q ∧ Nat.Coprime a q ∧ |t - (a : ℝ) / q| ≤ (Qpow B n : ℝ) / ((q : ℝ) * n)}; ∀ A : ℝ, 0 < A → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ t ∈ Set.Icc (0 : ℝ) 1, t ∉ arcsPoly (2 * ⌈A⌉₊ + 16) n → ‖S n ArithmeticFunction.vonMangoldt t‖ ≤ (n : ℝ) * (Real.log (n : ℝ)) ^ (-A) ∧ ‖S n w t‖ ≤ (n : ℝ) * (Real.log (n : ℝ)) ^ (-A) := by
  intro w E S Qpow arcsPoly A hA
  let B := 2 * ⌈A⌉₊ + 16
  apply eventually_atTop.mp
  filter_upwards [eventually_ge_atTop (8 : ℕ), cutoff_eventually_le B, log_budgets A,
    OAI.Problem337.Vaughan.eventually_vonMangoldt_sum_log_bound] with n hn hcut hlogs hv
  intro t ht hminor
  let P := Qpow B n
  let L := Real.log n
  have hnpos : (0:ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hk : 1 ≤ Nat.log 2 (n+2) := Nat.le_log_of_pow_le (by decide) (by simp)
  have hP : 0 < P := pow_pos hk _
  have hPr : (0:ℝ) < P := Nat.cast_pos.mpr hP
  obtain ⟨q,a,hPq,hqB,_ha,hcop,happrox⟩ := minor_approximant P n t hP hcut ht hminor
  have hqp : 0 < q := by omega
  have hqr : (0:ℝ) < q := Nat.cast_pos.mpr hqp
  have hqN : q ≤ n := hqB.trans (Nat.div_le_self _ _)
  have hqsec : |t - (a:ℝ)/q| ≤ 1/(q:ℝ)^2 := by
    apply happrox.trans
    apply one_div_le_one_div_of_le (by positivity)
    rw [sq]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.le_succ_of_le hqB) hqr.le
  have hvq := hv t (a:ℤ) q hqp hcop.isCoprime (by simpa using hqsec) hqN
  have hsum : S n ArithmeticFunction.vonMangoldt t = OAI.Problem337.Vaughan.weightedSum
      (Finset.Ioc 0 n) (fun k => OAI.Problem337.VaughanBilinear.phase (t*k)) ArithmeticFunction.vonMangoldt := by
    dsimp [S,E,OAI.Problem337.Vaughan.weightedSum,OAI.Problem337.VaughanBilinear.phase]
    rw [Nat.range_succ_eq_Icc_zero, ← Finset.add_sum_Ioc_eq_sum_Icc (Nat.zero_le n)]
    simp only [ArithmeticFunction.map_zero,Complex.ofReal_zero,zero_mul,zero_add, Real.fourierChar_apply]
    apply Finset.sum_congr rfl
    intro k _; rw [mul_comm t (k:ℝ)]
  obtain ⟨hL,habs,hsmall,hres⟩ := hlogs
  have hhigh : (q:ℝ) ≤ (n:ℝ)/P := (le_div_iff₀ hPr).mpr (by exact_mod_cast (Nat.le_div_iff_mul_le hP).mp hqB)
  have hbound : ‖S n ArithmeticFunction.vonMangoldt t‖ ≤ (1/2:ℝ)*n*L^(-A) := by
    rw [hsum]; refine hvq.trans ?_
    exact envelope_budget hnpos hL hPr (by exact_mod_cast hPq.le) hhigh (cutoff_sqrt_lower hn hL) hsmall habs
  have hb : 2*Real.sqrt n*L ≤ (1/2:ℝ)*n*L^(-A) := residual_budget hnpos (by linarith) hres
  have herr : ‖S n ArithmeticFunction.vonMangoldt t - S n w t‖ ≤ 2*Real.sqrt n*L := by
    simpa only [S, ← Finset.sum_sub_distrib, ← sub_mul, ← Complex.ofReal_sub] using
      mangoldt_pointwise_bridge n (by omega) t
  have hnon : 0 ≤ (n:ℝ) * L^(-A) := mul_nonneg hnpos.le (Real.rpow_nonneg (by linarith) _)
  constructor
  · change _ ≤ (n:ℝ)*L^(-A); linarith only [hbound,hnon]
  · change _ ≤ (n:ℝ)*L^(-A)
    have htriangle := norm_sub_le (S n ArithmeticFunction.vonMangoldt t) (S n ArithmeticFunction.vonMangoldt t - S n w t)
    rw [sub_sub_cancel] at htriangle
    linarith only [htriangle,hbound,herr,hb]

end

section

/- The arc separation and clipping arguments follow DFQDZZ's goldbach-proofs PR 316
and wzhxzkk's PR 153, licensed under Apache-2.0. Here the denominator cutoff,
the integrated function, and the centered model are independent parameters. -/
namespace GoldbachBlockGeometry
noncomputable section
open Finset Filter MeasureTheory

def width (Q n q : ℕ) : ℝ := (Q:ℝ)/((q:ℝ)*n)
def arcs (Q n : ℕ) : Set ℝ := {t | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Q ∧ a ≤ q ∧ a.Coprime q ∧
  |t-(a:ℝ)/q| ≤ width Q n q}
def numerators (q : ℕ) := (range (q+1)).filter (fun a => a.Coprime q)
def center (q a : ℕ) : ℝ := (a : ℝ) / q
def window (Q n q a : ℕ) : Set ℝ := Set.Icc (center q a - width Q n q) (center q a + width Q n q)
def leftEnd (Q n q a : ℕ) : ℝ := max (center q a - width Q n q) 0 - center q a
def rightEnd (Q n q a : ℕ) : ℝ := min (center q a + width Q n q) 1 - center q a


variable {Q : ℕ}

theorem width_nonneg (n q : ℕ) : 0 ≤ width Q n q := by unfold width; positivity

theorem mem_window (n q a : ℕ) (t : ℝ) : t ∈ window Q n q a ↔ |t - center q a| ≤ width Q n q := by
  change _ ∧ _ ↔ _
  rw [abs_le]
  constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith

/-- Separation of reduced rational arcs, using the spacing argument of wzhxzkk,
goldbach-proofs PR 153 (93d33090fdfc93fb272dde08cb463f3bff3c64ce). -/
private theorem cross_eq_of_overlap {n q r a b : ℕ} {t : ℝ} (hn : 2 * Q^2 < n)
    (hq : q ∈ Icc 1 Q) (hr : r ∈ Icc 1 Q)
    (ha : t ∈ window Q n q a) (hb : t ∈ window Q n r b) : a*r=b*q := by
  obtain ⟨hq₁,hqQ⟩ := mem_Icc.mp hq
  obtain ⟨hr₁,hrQ⟩ := mem_Icc.mp hr
  have hqr : 0 < (q : ℝ) := by exact_mod_cast hq₁
  have hrr : 0 < (r : ℝ) := by exact_mod_cast hr₁
  have hnr : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hsmall : Q * r + Q * q < n := by nlinarith only [hn, Nat.mul_le_mul_left Q hrQ, Nat.mul_le_mul_left Q hqQ]
  have hradii : (Q : ℝ) / (q*n) + Q/(r*n) < 1/(q*r) := calc
    _ = ((Q : ℝ)*r+Q*q)/(q*r*n) := by field_simp
    _ < (n : ℝ)/(q*r*n) := (div_lt_div_iff_of_pos_right (by positivity)).mpr (by exact_mod_cast hsmall)
    _ = _ := by field_simp
  by_contra hne
  have hsep : 1 / ((q : ℝ)*r) ≤ |(a : ℝ)/q - b/r| := by
    rw [show (a:ℝ)/q - b/r = (a*r-b*q)/(q*r) by field_simp, abs_div, abs_of_pos (mul_pos hqr hrr)]
    apply (div_le_div_iff_of_pos_right (mul_pos hqr hrr)).mpr
    rcases lt_or_gt_of_ne hne with hab | hba
    · have hgap : (a:ℝ)*r + 1 ≤ b*q := by exact_mod_cast Nat.succ_le_of_lt hab
      linarith [neg_le_abs ((a:ℝ)*r - b*q)]
    · have hgap : (b:ℝ)*q + 1 ≤ a*r := by exact_mod_cast Nat.succ_le_of_lt hba
      linarith [le_abs_self ((a:ℝ)*r - b*q)]
  have ht := abs_sub_le ((a:ℝ)/q) t ((b:ℝ)/r)
  rw [abs_sub_comm ((a:ℝ)/q) t] at ht
  have h₁ := (mem_window (Q := Q) n q a t).mp ha
  have h₂ := (mem_window (Q := Q) n r b t).mp hb
  change |t-(a:ℝ)/q| ≤ (Q:ℝ)/(q*n) at h₁
  change |t-(b:ℝ)/r| ≤ (Q:ℝ)/(r*n) at h₂
  linarith

private theorem center_unique {n q r a b : ℕ} {t : ℝ} (hn : 2*Q^2<n)
    (hq : q ∈ Icc 1 Q) (hr : r ∈ Icc 1 Q)
    (ha : a ∈ numerators q) (hb : b ∈ numerators r)
    (hta : t ∈ window Q n q a) (htb : t ∈ window Q n r b) : q=r ∧ a=b := by
  have he := cross_eq_of_overlap hn hq hr hta htb
  have hc := (mem_filter.mp ha).2
  have hc' := (mem_filter.mp hb).2
  have hqr : q ∣ r := hc.symm.dvd_of_dvd_mul_left (he ▸ dvd_mul_left q b)
  have hrq : r ∣ q := hc'.symm.dvd_of_dvd_mul_left (he.symm ▸ dvd_mul_left r a)
  obtain rfl := Nat.dvd_antisymm hqr hrq
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_right (mem_Icc.mp hq).1 he⟩

theorem arc_indicator_sum (F : ℝ → ℂ) {n : ℕ} (hn : 2*Q^2<n) (t : ℝ) :
    (arcs Q n).indicator F t =
    ∑ q ∈ Icc 1 Q, ∑ a ∈ numerators q, (window Q n q a).indicator F t := by
  classical
  by_cases ht : t ∈ arcs Q n
  · rw [Set.indicator_of_mem ht]
    obtain ⟨q,a,hq₁,hqQ,ha,hc,habs⟩ := ht
    have hq := mem_Icc.mpr ⟨hq₁,hqQ⟩
    have ha' : a ∈ numerators q := mem_filter.mpr ⟨mem_range.mpr (by omega),hc⟩
    have hw := (mem_window (Q := Q) n q a t).mpr habs
    symm
    calc
      _ = ∑ b ∈ numerators q, (window Q n q b).indicator F t := by
        apply sum_eq_single_of_mem q hq
        intro r hr hrq
        exact sum_eq_zero fun b hb => Set.indicator_of_notMem (fun ht' => hrq (center_unique hn hr hq hb ha' ht' hw).1) _
      _ = (window Q n q a).indicator F t := by
        exact sum_eq_single_of_mem a ha' fun b hb hba =>
          Set.indicator_of_notMem (fun ht' => hba (center_unique hn hq hq hb ha' ht' hw).2) _
      _ = _ := Set.indicator_of_mem hw _
  · rw [Set.indicator_of_notMem ht]
    symm
    apply sum_eq_zero
    intro q hq
    apply sum_eq_zero
    intro a ha
    exact Set.indicator_of_notMem (fun hw => ht ⟨q,a,(mem_Icc.mp hq).1,(mem_Icc.mp hq).2,
      Nat.le_of_lt_succ (mem_range.mp (mem_filter.mp ha).1),(mem_filter.mp ha).2,(mem_window (Q := Q) n q a t).mp hw⟩) _

theorem center_in_unit {q a : ℕ} (hq : 0<q) (ha : a≤q) :
    0 ≤ center q a ∧ center q a ≤ 1 := by
  have hq' : (0:ℝ)<q := by exact_mod_cast hq
  exact ⟨by unfold center; positivity, (div_le_one hq').mpr (by exact_mod_cast ha)⟩

theorem clipped_order {n q a : ℕ} (hq : 0<q) (ha : a≤q) :
    -width Q n q ≤ leftEnd Q n q a ∧ leftEnd Q n q a ≤ rightEnd Q n q a ∧ rightEnd Q n q a ≤ width Q n q := by
  obtain ⟨h₁,h₂⟩ := center_in_unit hq ha
  have hw := width_nonneg (Q := Q) n q
  unfold leftEnd rightEnd
  constructor
  · linarith [le_max_left (center q a-width Q n q) 0]
  constructor
  · apply sub_le_sub_right
    exact max_le (le_min (by linarith) (by linarith)) (le_min (by linarith) zero_le_one)
  · linarith [min_le_left (center q a+width Q n q) 1]

theorem indicator_clipped {n q a : ℕ} (hq : 0<q) (ha : a≤q) (F : ℝ→ℂ) :
    (∫ t in (0:ℝ)..1, (window Q n q a).indicator F t) =
    ∫ β in leftEnd Q n q a..rightEnd Q n q a, F (center q a+β) := by
  rw [intervalIntegral.integral_comp_add_left]
  have h := (clipped_order (Q := Q) (n := n) hq ha).2.1
  unfold leftEnd rightEnd at h ⊢
  simp only [add_sub_cancel]
  rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc,
    window, integral_indicator measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc,
    Set.Icc_inter_Icc, intervalIntegral.integral_of_le (by linarith : max (center q a-width Q n q) 0 ≤ min (center q a+width Q n q) 1),
    ← integral_Icc_eq_integral_Ioc]

def majorContribution (Q n : ℕ) (F : ℝ → ℂ) : ℂ := ∫ t in (0:ℝ)..1, (arcs Q n).indicator F t
def actualPiece (Q n q a : ℕ) (F : ℝ → ℂ) : ℂ := ∫ β in leftEnd Q n q a..rightEnd Q n q a, F (center q a+β)

theorem major_split (F : ℝ → ℂ) (hcont : Continuous F) {n : ℕ} (hn : 2*Q^2<n) : majorContribution Q n F =
    ∑ q ∈ Icc 1 Q, ∑ a ∈ numerators q, actualPiece Q n q a F := by
  have hInt (q a : ℕ) : IntervalIntegrable ((window Q n q a).indicator F) volume 0 1 :=
    ⟨(hcont.intervalIntegrable 0 1).1.indicator measurableSet_Icc,
      (hcont.intervalIntegrable 0 1).2.indicator measurableSet_Icc⟩
  unfold majorContribution
  simp_rw [arc_indicator_sum F hn]
  rw [intervalIntegral.integral_finsetSum]
  · apply sum_congr rfl
    intro q hq
    rw [intervalIntegral.integral_finsetSum (fun a _ => hInt q a)]
    exact sum_congr rfl fun a ha => indicator_clipped (mem_Icc.mp hq).1
      (Nat.le_of_lt_succ (mem_range.mp (mem_filter.mp ha).1)) _
  · intro q _
    exact ⟨integrable_finsetSum _ (fun a _ => (hInt q a).1),
      integrable_finsetSum _ (fun a _ => (hInt q a).2)⟩


theorem width_le_unit {n q : ℕ} (hn : 2*Q^2<n) (hq : 0<q) :
    width Q n q ≤ 1/(q:ℝ) := by
  have hn' : (0:ℝ)<n := by exact_mod_cast (by omega : 0<n)
  have hq' : (0:ℝ)<q := by exact_mod_cast hq
  have hQn : Q ≤ n := by nlinarith [Nat.le_self_pow (by decide : 2 ≠ 0) Q]
  calc
    width Q n q = ((Q:ℝ)/n)/q := by unfold width; ring
    _ ≤ _ := div_le_div_of_nonneg_right ((div_le_one hn').mpr (by exact_mod_cast hQn)) hq'.le

private theorem interior_order {q a : ℕ} (hq : 1<q) (ha : a ∈ numerators q) : 0<a ∧ a<q := by
  obtain ⟨h,hc⟩ := mem_filter.mp ha
  have hle : a≤q := Nat.le_of_lt_succ (mem_range.mp h)
  have ha0 : a ≠ 0 := by rintro rfl; simp [Nat.Coprime] at hc; omega
  have hne : a ≠ q := by rintro rfl; simp [Nat.Coprime] at hc; omega
  omega

private theorem uncut {n q a : ℕ} (hn : 2*Q^2<n) (hq : 1<q) (ha : a∈numerators q) :
    leftEnd Q n q a = -(width Q n q) ∧ rightEnd Q n q a = width Q n q := by
  obtain ⟨ha₁,haq⟩ := interior_order hq ha
  have hq' : (0:ℝ)<q := by exact_mod_cast (by omega : 0<q)
  have hw := width_le_unit hn (by omega : 0<q)
  have hc₁ : 1/(q:ℝ) ≤ center q a :=
    div_le_div_of_nonneg_right (by exact_mod_cast ha₁) hq'.le
  have hc₂ : center q a + 1/q ≤ 1 := by
    rw [center, ← add_div, div_le_one hq']
    exact_mod_cast (Nat.succ_le_of_lt haq)
  unfold leftEnd rightEnd
  rw [max_eq_left (by linarith), min_eq_left (by linarith)]
  constructor <;> ring


def modelPiece (Q n q a : ℕ) (C : ℕ → ℕ → ℂ) (K : ℝ → ℂ) : ℂ :=
  C q a * ∫ β in leftEnd Q n q a..rightEnd Q n q a, K β

private theorem endpoint_models (K : ℝ → ℂ) (hK : Continuous K) (C : ℕ → ℕ → ℂ) (hC : C 1 0 = C 1 1)
    {n : ℕ} (hn : 2*Q^2<n) :
    (∑ a ∈ numerators 1, modelPiece Q n 1 a C K) =
      C 1 0 * ∫ β in -(width Q n 1)..width Q n 1, K β := by
  let w := width Q n 1
  have hw : 0≤w := width_nonneg _ _
  have hw1 : w≤1 := by simpa [w] using width_le_unit hn (by decide : 0<1)
  have h0 : leftEnd Q n 1 0 = 0 ∧ rightEnd Q n 1 0 = w := by
    change max (0/(1:ℝ)-w) 0 - 0/1 = 0 ∧ min (0/1+w) 1 - 0/1 = w
    simp [hw,hw1]
  have h1 : leftEnd Q n 1 1 = -w ∧ rightEnd Q n 1 1 = 0 := by
    change max (1/(1:ℝ)-w) 0 - 1/1 = -w ∧ min (1/1+w) 1 - 1/1 = 0
    rw [one_div_one, max_eq_left (by linarith), min_eq_right (by linarith)]
    constructor <;> ring
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (hK.intervalIntegrable (μ := volume) (-w) 0) (hK.intervalIntegrable 0 w)
  rw [show numerators 1 = {0,1} by decide]
  simp only [sum_insert (by decide : (0:ℕ) ∉ {1}),sum_singleton,modelPiece,h0.1,h0.2,h1.1,h1.2]
  rw [← hC, ← mul_add, add_comm, hadd]

private theorem model_by_denominator (C : ℕ → ℕ → ℂ) (K : ℝ → ℂ)
    (hK : Continuous K) (hC : C 1 0 = C 1 1) {n q : ℕ} (hn : 2*Q^2<n) (hq : 0<q) :
    (∑ a ∈ numerators q, modelPiece Q n q a C K) =
      (∑ a ∈ (range q).filter (fun a => a.Coprime q), C q a) *
      ∫ β in -(width Q n q)..width Q n q, K β := by
  rcases eq_or_lt_of_le (show 1 ≤ q by omega) with h | h
  · subst q
    have hone : (range 1).filter (fun a => a.Coprime 1) = {0} := by decide
    rw [hone,sum_singleton]
    exact endpoint_models K hK C hC hn
  · have hs : numerators q = (range q).filter (fun a => a.Coprime q) := by
      ext a
      constructor
      · intro ha
        exact mem_filter.mpr ⟨mem_range.mpr (interior_order h ha).2, (mem_filter.mp ha).2⟩
      · intro ha
        exact mem_filter.mpr ⟨mem_range.mpr (by have := mem_range.mp (mem_filter.mp ha).1; omega),(mem_filter.mp ha).2⟩
    rw [← hs, sum_mul]
    apply sum_congr rfl
    intro a ha
    obtain ⟨hl,hr⟩ := uncut hn h ha
    simp only [modelPiece,hl,hr]

theorem major_error (F K : ℝ → ℂ) (hF : Continuous F) (hK : Continuous K)
    (C : ℕ → ℕ → ℂ) (hC : C 1 0 = C 1 1) {n : ℕ} (hn : 2*Q^2<n) :
    ‖majorContribution Q n F - ∑ q ∈ Icc 1 Q,
      (∑ a ∈ (range q).filter (fun a => a.Coprime q), C q a) *
      ∫ β in -(width Q n q)..width Q n q, K β‖ ≤
    ∑ q ∈ Icc 1 Q, ∑ a ∈ range (q+1), ∫ β in -(width Q n q)..width Q n q,
      ‖F (center q a+β) - C q a*K β‖ := by
  rw [major_split F hF hn]
  have hmodel (q : ℕ) (hq : q ∈ Icc 1 Q) := model_by_denominator C K hK hC hn (mem_Icc.mp hq).1
  rw [← sum_congr rfl hmodel, ← sum_sub_distrib]
  refine (norm_sum_le _ _).trans (sum_le_sum fun q hq => ?_)
  rw [← sum_sub_distrib]
  refine (norm_sum_le _ _).trans ((sum_le_sum fun a ha => ?_).trans
    (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun a _ _ =>
      intervalIntegral.integral_nonneg (by linarith [width_nonneg (Q := Q) n q]) fun _ _ => norm_nonneg _)))
  have hi : Continuous (fun β => F (center q a+β)) := hF.comp (continuous_const.add continuous_id)
  have hm : Continuous (fun β => C q a*K β) := continuous_const.mul hK
  have ⟨hl,ho,hr⟩ := clipped_order (Q := Q) (n := n) (mem_Icc.mp hq).1
    (Nat.le_of_lt_succ (mem_range.mp (mem_filter.mp ha).1))
  rw [actualPiece,modelPiece,←intervalIntegral.integral_const_mul,←intervalIntegral.integral_sub
    (hi.intervalIntegrable _ _) (hm.intervalIntegrable _ _)]
  exact (intervalIntegral.norm_integral_le_integral_norm ho).trans
    (intervalIntegral.integral_mono_interval hl ho hr (Eventually.of_forall fun _ => norm_nonneg _)
      ((hi.sub hm).norm.intervalIntegrable _ _))

end
end GoldbachBlockGeometry

end

namespace GoldbachEstermann
open MeasureTheory
theorem measurable_block_arcs (Q n : ℕ) :
    MeasurableSet {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Q ∧ a ≤ q ∧ Nat.Coprime a q ∧
      |t - (a : ℝ) / (q : ℝ)| ≤ (Q : ℝ) / ((q : ℝ) * (n : ℝ))} := by
  simp only [Set.ofPred_exists]
  apply MeasurableSet.iUnion
  intro q
  apply MeasurableSet.iUnion
  intro a
  by_cases h : 1 ≤ q ∧ q ≤ Q ∧ a ≤ q ∧ Nat.Coprime a q
  · obtain ⟨h₁, h₂, h₃, h₄⟩ := h
    have hmeas : MeasurableSet {t : ℝ | |t - (a : ℝ) / (q : ℝ)| ≤ (Q : ℝ) / (q * n)} :=
      measurableSet_le (show Continuous (fun t : ℝ => |t - (a : ℝ) / (q : ℝ)|) by fun_prop).measurable
        measurable_const
    convert hmeas using 1
    ext t
    exact ⟨fun h => h.2.2.2.2, fun h => ⟨h₁, h₂, h₃, h₄, h⟩⟩
  · convert MeasurableSet.empty (α := ℝ) using 1
    ext t
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨h₁, h₂, h₃, h₄, _⟩
    exact h ⟨h₁, h₂, h₃, h₄⟩


end GoldbachEstermann

section
open Finset

namespace GoldbachEstermann

/-- Cover the dyadic range by adjacent windows ending at a common grid of right endpoints. -/
theorem dyadic_short_block_count (P : ℕ → Prop) [DecidablePred P] {X H : ℕ}
    (hh : 0 < H) (hHX : H ≤ X) (W : ℝ)
    (hbound : ∀ M : ℕ, X ≤ M → M ≤ 3*X →
      (((Ico (M-H) M).filter P).card : ℝ) ≤ W) :
    (((Ico X (2*X)).filter P).card : ℝ) ≤ (X/H+1 : ℕ)*W := by
  classical
  let I := range (X/H+1)
  let M (j : ℕ) := X+(j+1)*H
  let window (j : ℕ) := (Ico (M j-H) (M j)).filter P
  have hsub : (Ico X (2*X)).filter P ⊆ I.biUnion window := by
    intro n hn
    obtain ⟨hn,hp⟩ := mem_filter.mp hn
    obtain ⟨hnX,h2X⟩ := mem_Ico.mp hn
    let j := (n-X)/H
    have hleft : j*H ≤ n-X := Nat.div_mul_le_self _ _
    have hright : n-X < (j+1)*H := (Nat.div_lt_iff_lt_mul hh).mp (Nat.lt_succ_self j)
    refine mem_biUnion.mpr ⟨j,mem_range.mpr ?_,mem_filter.mpr ⟨mem_Ico.mpr ⟨?_,?_⟩,hp⟩⟩
    · exact Nat.lt_succ_of_le (Nat.div_le_div_right (by omega))
    · dsimp only [M]; rw [Nat.add_mul,Nat.one_mul]; omega
    · dsimp only [M]; omega
  have hbound' (j : ℕ) (hj : j ∈ I) : ((window j).card : ℝ) ≤ W := by
    have hj' : j ≤ X/H := Nat.le_of_lt_succ (mem_range.mp hj)
    have hlen : j*H ≤ X := (Nat.le_div_iff_mul_le hh).mp hj'
    apply hbound
    · simp [M]
    · dsimp only [M]; rw [Nat.add_mul,Nat.one_mul]; omega
  have hs : (((Ico X (2*X)).filter P).card : ℝ) ≤ ∑ j ∈ I, ((window j).card : ℝ) := by
    exact_mod_cast (card_le_card hsub).trans (card_biUnion_le ..)
  refine hs.trans ((sum_le_sum hbound').trans_eq ?_)
  simp [I]

end GoldbachEstermann
end

section
namespace GoldbachMajorArc
open Finset MeasureTheory
noncomputable section
def anchoredModel (M Q n m : ℕ) : ℝ :=
  ∑ q ∈ Icc 1 Q, (coefficient q n).re *
    ∫ t in -(blockWidth M Q q)..blockWidth M Q q, (GoldbachEstermannKernel.twisted M m t).re

/-- The spectrum length, cutoff and arc widths are uniform in the target n. -/
theorem anchoredModel_floor (M Q n m : ℕ) (hM : 0 < M) (hQ : 1 ≤ Q)
    (hdis : 2*Q ≤ M) (hmode : m ≤ M) (heven : Even n) :
    (M : ℝ) / 72 - 4 * Real.sqrt Q * ((M : ℝ) - m) ≤ anchoredModel M Q n m := by
  let W (q : ℕ) := if q ≤ Q then kernelMass M (blockWidth M Q q) else 0
  have hMr : 0 < (M : ℝ) := by exact_mod_cast hM
  have hQr : 1 ≤ (Q : ℝ) := by exact_mod_cast hQ
  have hwr (q : ℕ) : 0 ≤ blockWidth M Q q := by unfold blockWidth; positivity
  have hn' : 0 ≤ (M : ℝ) - m := sub_nonneg.mpr (by exact_mod_cast hmode)
  have hnon (q : ℕ) : 0 ≤ W q := by
    dsimp only [W]; split_ifs
    · apply intervalIntegral.integral_nonneg (by linarith [hwr q]); intro t _; exact sq_nonneg _
    · rfl
  have hmono (i j : ℕ) (hi : 0 < i) (hij : i ≤ j) : W j ≤ W i := by
    by_cases hj : j ≤ Q
    · simp only [W, ite_eq_left hj, ite_eq_left (hij.trans hj)]
      apply kernelMass_mono (hwr j)
      apply div_le_div_of_nonneg_left (Nat.cast_nonneg _) (mul_pos (by exact_mod_cast hi) hMr)
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hij) hMr.le
    · simp only [W, ite_eq_right hj]; exact hnon i
  have hsum := arithmetic_floor (Q := Q) heven W hnon hmono (by intro q hq; simp [W, not_le.mpr hq])
  have h1 : 1 / (6*(M : ℝ)) ≤ blockWidth M Q 1 := by
    unfold blockWidth; simp only [Nat.cast_one, one_mul]
    rw [div_le_div_iff₀ (by positivity) hMr]; nlinarith [mul_le_mul_of_nonneg_right hQr hMr.le]
  have hmodel : (M : ℝ) / 72 ≤ ∑ q ∈ Icc 1 Q, (coefficient q n).re * W q := by
    rw [show W 1 = kernelMass M (blockWidth M Q 1) by simp [W, hQ]] at hsum
    linarith [kernelMass_floor hM h1]
  have hdiff (q : ℕ) (hq : q ∈ Icc 1 Q) :
      (coefficient q n).re * W q - (coefficient q n).re *
        (∫ t in -(blockWidth M Q q)..blockWidth M Q q, (GoldbachEstermannKernel.twisted M m t).re) ≤
      ‖coefficient q n‖ * ((M : ℝ) - m) := by
    have hle : blockWidth M Q q ≤ 1/2 := by
      have hq' : (1 : ℝ) ≤ q := by exact_mod_cast (mem_Icc.mp hq).1
      have hdis' : 2 * (Q : ℝ) ≤ M := by exact_mod_cast hdis
      unfold blockWidth
      apply (div_le_iff₀ (mul_pos (by linarith) hMr)).mpr
      nlinarith [mul_le_mul_of_nonneg_right hq' hMr.le]
    obtain ⟨hpos,hloss⟩ := GoldbachEstermannKernel.loss_on_interval M m hmode
      (neg_le_neg hle) (by linarith [hwr q] : -(blockWidth M Q q) ≤ blockWidth M Q q) hle
    rw [← mul_sub, show W q = kernelMass M (blockWidth M Q q) by simp [W, (mem_Icc.mp hq).2]]
    exact mul_le_mul (Complex.re_le_norm _) hloss hpos (norm_nonneg _)
  have htot := Finset.sum_le_sum hdiff
  rw [sum_sub_distrib, ← sum_mul] at htot
  have hcoef := mul_le_mul_of_nonneg_right (sum_norm_coefficient_le_sqrt Q n) hn'
  unfold anchoredModel
  linarith

theorem anchoredModel_real (M Q n m : ℕ) :
    (∑ q ∈ Icc 1 Q, coefficient q n *
      ∫ t in -(blockWidth M Q q)..blockWidth M Q q, GoldbachEstermannKernel.twisted M m t).re =
    anchoredModel M Q n m := by
  rw [Complex.re_sum]
  unfold anchoredModel
  apply sum_congr rfl
  intro q hq
  have hc : Continuous (GoldbachEstermannKernel.twisted M m) := by
    unfold GoldbachEstermannKernel.twisted GoldbachEstermannKernel.kernel GoldbachEstermannKernel.phase
    fun_prop
  rw [Complex.mul_re, coefficient_im_zero n (by have := (mem_Icc.mp hq).1; omega),
    zero_mul, sub_zero]
  exact congrArg ((coefficient q n).re * ·)
    (intervalIntegral.intervalIntegral_re (𝕜 := ℂ) (hc.intervalIntegrable _ _)).symm

end
end GoldbachMajorArc
end

section
open Finset Filter MeasureTheory
namespace BulkCircle
open GoldbachMajorArc
noncomputable section

def S (L D : ℕ) (t : ℝ) : ℂ := primeSum (L+D+1) t - primeSum L t
def U (L D : ℕ) (t : ℝ) : ℂ := kernel (L+D+1) t - kernel L t
def integrand (L D n : ℕ) (t : ℝ) := S L D t ^ 2 * phase (-(n:ℝ)*t)

theorem phase_add (a b : ℝ) : phase (a+b)=phase a*phase b := by
  unfold phase; rw [←Complex.exp_add]; congr 1; push_cast; ring

theorem norm_phase (a : ℝ) : ‖phase a‖=1 := Complex.norm_exp_ofReal_mul_I _

theorem shifted_kernel (L D : ℕ) (t : ℝ) : U L D t = phase (((L:ℝ)+1)*t)*kernel D t := by
  unfold U kernel
  rw [show L+D+1+1 = (L+1)+(D+1) by omega, sum_range_add, add_sub_cancel_left, mul_sum]
  refine sum_congr rfl fun k _ => ?_
  push_cast
  rw [add_mul,phase_add]

theorem remove_phase (q a L D n m : ℕ) (hn : n=m+2*(L+1)) (t : ℝ) :
    ‖integrand L D n (GoldbachBlockGeometry.center q a+t) -
      (unitMean q a ^2*phase (-(n:ℝ)*GoldbachBlockGeometry.center q a)) *
        GoldbachEstermannKernel.twisted D m t‖ =
      ‖S L D (GoldbachBlockGeometry.center q a+t)^2 -
        (unitMean q a*U L D t)^2‖ := by
  let r := GoldbachBlockGeometry.center q a
  have hR : (n:ℝ) = (m:ℝ)+2*((L:ℝ)+1) := by exact_mod_cast hn
  have he : phase (((L:ℝ)+1)*t)^2 * phase (-(n:ℝ)*(r+t)) =
      phase (-(n:ℝ)*r) * phase (-(m:ℝ)*t) := by
    rw [pow_two, ←phase_add, ←phase_add, ←phase_add]; congr 1; rw [hR]; ring
  have hmodel : (unitMean q a*U L D t)^2 * phase (-(n:ℝ)*(r+t)) =
    (unitMean q a^2*phase (-(n:ℝ)*r))*GoldbachEstermannKernel.twisted D m t := by
    rw [shifted_kernel, mul_pow, mul_pow]
    change (_ * (_*_))*_ = (_*_)*((kernel D t)^2 * phase (-(m:ℝ)*t))
    calc
      _ = unitMean q a^2 * kernel D t^2 * (phase (((L:ℝ)+1)*t)^2 * phase (-(n:ℝ)*(r+t))) := by ring
      _ = _ := by rw [he]; ring
  unfold integrand
  change ‖S L D (r+t)^2 * phase (-(n:ℝ)*(r+t)) - _‖ = _
  rw [←hmodel,←sub_mul,norm_mul,norm_phase,mul_one]

theorem pref_mono {u x : ℕ} (hu : u ≤ x) (r : ℝ) (A : ℂ) : prefixError u r A ≤ prefixError x r A := by
  unfold prefixError
  apply Finset.sup'_le
  intro k hk
  exact Finset.le_sup' (fun m => ‖∑ j ∈ range m, centerErrorTerm r A j‖) (Finset.mem_range.mpr (by have := Finset.mem_range.mp hk; omega))

theorem point_approx {x Q q a u D : ℕ} {β E : ℝ} (hx : x ≤ 64*D) (hu : 0<u) (hux : u≤x)
    (hq : 0<q) (hqQ : q≤Q) (hβ : |β| ≤ blockWidth D Q q) (hE0 : 0≤E)
    (hE : prefixError x ((a:ℝ)/q) (unitMean q a) ≤ q*E) :
      ‖primeSum u ((a:ℝ)/q+β) - unitMean q a*kernel u β‖ ≤ 500*(Q:ℝ)*E := by
  have hD : 0 < (D:ℝ) := by exact_mod_cast (show 0<D by omega)
  have hqR : 0 < (q:ℝ) := by exact_mod_cast hq
  have huR : 0 < (u:ℝ) := by exact_mod_cast hu
  have hQ : (0:ℝ)≤Q := by positivity
  have huD : (u:ℝ) ≤ 64*D := by exact_mod_cast (show u≤64*D by omega)
  have hβ' : |β| ≤ ((64*Q:ℕ):ℝ)/((q:ℝ)*u) := by
    apply hβ.trans
    unfold blockWidth
    rw [div_le_div_iff₀ (mul_pos hqR hD) (mul_pos hqR huR), Nat.cast_mul, Nat.cast_ofNat]
    linarith only [mul_le_mul_of_nonneg_left huD (mul_nonneg hQ hqR.le)]
  have hr := Polylog.rational_arc_error (a:=a) hu hq hβ'
  calc
    _ ≤ ((q:ℝ)*E)*(1+2*Real.pi*(((64*Q:ℕ):ℝ)/q)) :=
      hr.trans (mul_le_mul_of_nonneg_right ((pref_mono hux _ _).trans hE) (by positivity))
    _ = E*((q:ℝ)+128*Real.pi*Q) := by push_cast; field_simp; ring
    _ ≤ _ := by
      have hq' : (q:ℝ) ≤ Q := by exact_mod_cast hqQ
      have hpi := mul_le_mul_of_nonneg_right (le_of_lt Real.pi_lt_d2) hQ
      calc
        _ ≤ E*(500*Q) := mul_le_mul_of_nonneg_left (by linarith) hE0
        _ = _ := by ring

theorem unitMean_norm (q a : ℕ) (hq : 0 < q) : ‖unitMean q a‖ ≤ 1 := by
  let U := (range q).filter (fun r => r.Coprime q)
  have hcard : U.card = q.totient := by
    rw [Nat.totient_eq_card_coprime]
    have h : U = (range q).filter (fun r => q.Coprime r) := by ext k; simp [U, Nat.coprime_comm]
    rw [h]
  have hφ : 0 < (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
  unfold unitMean
  rw [norm_div, Complex.norm_natCast, div_le_one hφ]
  refine (norm_sum_le _ _).trans ?_
  change ∑ r ∈ U, ‖phase ((r : ℝ) * ((a : ℝ) / q))‖ ≤ _
  simp only [phase, Complex.norm_exp_ofReal_mul_I, sum_const, nsmul_eq_mul, mul_one, hcard, le_refl]

end
end BulkCircle
end

section
open Finset Filter MeasureTheory
namespace BulkCircle
open GoldbachMajorArc
noncomputable section

theorem pw_pos (k : ℕ) : 0 ≤ primeWeight k := by
  unfold primeWeight; split <;> rename_i h
  · exact Real.log_nonneg (by exact_mod_cast h.one_le)
  · rfl

theorem norm_primeSum_le (k : ℕ) (t : ℝ) : ‖primeSum k t‖ ≤ 2*(k:ℝ) := by
  have hsum : ∑ j ∈ range (k+1), primeWeight j = Chebyshev.theta k := by
    rw [Chebyshev.theta_eq_sum_primesLE_log, Nat.primesLE_eq_filter_range, sum_filter]; rfl
  calc
    _ ≤ ∑ j ∈ range (k+1), primeWeight j := (norm_sum_le _ _).trans (sum_le_sum (fun j _ => by
      rw [norm_mul, norm_phase, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (pw_pos j)]))
    _ ≤ _ := by
      rw [hsum]
      have h4 : Real.log (4:ℝ) ≤ 2 := by rw [show (4:ℝ)=2^2 by norm_num, Real.log_pow]; norm_num; linarith [Real.log_two_lt_d9]
      exact (Chebyshev.theta_le_log4_mul_x (by positivity)).trans (mul_le_mul_of_nonneg_right h4 (by positivity))

theorem norm_kernel_le (k : ℕ) (t : ℝ) : ‖kernel k t‖ ≤ (k:ℝ)+1 := by
  unfold kernel; apply (norm_sum_le _ _).trans; simp [norm_phase]

theorem point_squared {x Q q a L D : ℕ} {β E : ℝ} (hx : x≤64*D) (hL : 0<L) (hux : L+D+1≤x)
    (hq : 0<q) (hqQ : q≤Q) (hβ : |β| ≤ blockWidth D Q q) (hE0 : 0≤E)
    (hE : prefixError x ((a:ℝ)/q) (unitMean q a) ≤ q*E) :
    ‖S L D ((a:ℝ)/q+β)^2-(unitMean q a*U L D β)^2‖ ≤ 8000*(x:ℝ)*Q*E := by
  let r := (a:ℝ)/q+β
  let A := unitMean q a
  have small : ‖S L D r-A*U L D β‖ ≤ 1000*(Q:ℝ)*E := by
    have he : S L D r-A*U L D β = (primeSum (L+D+1) r-A*kernel (L+D+1) β) - (primeSum L r-A*kernel L β) := by unfold S U; ring
    rw [he]
    apply (norm_sub_le ..).trans
    have h1 := point_approx (a:=a) hx (by omega : 0<L+D+1) hux hq hqQ hβ hE0 hE
    have h2 := point_approx (a:=a) hx hL (by omega : L≤x) hq hqQ hβ hE0 hE
    change ‖primeSum (L+D+1) r-A*kernel (L+D+1) β‖ ≤ _ at h1
    change ‖primeSum L r-A*kernel L β‖ ≤ _ at h2
    linarith
  have wide : ‖S L D r+A*U L D β‖ ≤ 8*(x:ℝ) := by
    apply (norm_add_le ..).trans
    have hxU : ((L+D+1:ℕ):ℝ) ≤ x := by exact_mod_cast hux
    have hxL : (L:ℝ)≤x := by exact_mod_cast (show L≤x by omega)
    have hS : ‖S L D r‖ ≤ 4*(x:ℝ) := (norm_sub_le ..).trans
      (by linarith only [norm_primeSum_le (L+D+1) r,norm_primeSum_le L r,hxU,hxL])
    have hU : ‖U L D β‖ ≤ 4*(x:ℝ) := (norm_sub_le ..).trans
      (by linarith only [norm_kernel_le (L+D+1) β,norm_kernel_le L β,hxU,hxL,show (1:ℝ)≤x by exact_mod_cast (show 1≤x by omega)])
    rw [norm_mul]
    have hmodel := mul_le_of_le_one_left (norm_nonneg (U L D β)) (unitMean_norm q a hq)
    change ‖A‖*‖U L D β‖ ≤ _ at hmodel
    linarith only [hS,hU,hmodel]
  change ‖(S L D r)^2-(A*U L D β)^2‖ ≤ _
  rw [sq_sub_sq, mul_comm (S L D r + A * U L D β), norm_mul]
  calc
    _ ≤ (1000*(Q:ℝ)*E)*(8*(x:ℝ)) := mul_le_mul small wide (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem total_squared {x Q L D : ℕ} (hx : x≤64*D) (hL : 0<L) (hux : L+D+1≤x) (hQ : 1≤Q)
    {E : ℝ} (hE0 : 0≤E) (hE : ∀ q a : ℕ, 0<q → q≤Q → prefixError x ((a:ℝ)/q) (unitMean q a) ≤ q*E) :
    (∑ q ∈ Icc 1 Q, ∑ a ∈ range (q+1), ∫ β in -(blockWidth D Q q)..blockWidth D Q q,
      ‖S L D ((a:ℝ)/q+β)^2-(unitMean q a*U L D β)^2‖) ≤ 2048000*(Q:ℝ)^4*E := by
  let B := 1024000*(Q:ℝ)^2*E
  have hQr : (1:ℝ)≤Q := by exact_mod_cast hQ
  have hb : 0≤B := by dsimp [B]; positivity
  have hD : 0<(D:ℝ) := by exact_mod_cast (show 0<D by omega)
  have hxr : (x:ℝ)≤64*D := by exact_mod_cast hx
  have hf (q a : ℕ) : Continuous (fun β => ‖S L D ((a:ℝ)/q+β)^2-(unitMean q a*U L D β)^2‖) := by
    unfold S U primeSum kernel phase; fun_prop
  have each (q a : ℕ) (hq : 0<q) (hqq : q≤Q) :
      (∫ β in -(blockWidth D Q q)..blockWidth D Q q, ‖S L D ((a:ℝ)/q+β)^2-(unitMean q a*U L D β)^2‖) ≤ B := by
    let W := blockWidth D Q q
    let K := 8000*(x:ℝ)*Q*E
    have hw : 0≤W := by unfold W blockWidth; positivity
    have hsmall : W ≤ (Q:ℝ)/D := by
      apply div_le_div_of_nonneg_left (by positivity) hD
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (by exact_mod_cast hq : (1:ℝ) ≤ q) hD.le
    calc
      _ ≤ ∫ _ in -W..W, K := intervalIntegral.integral_mono_on (by linarith only [hw])
        ((hf q a).intervalIntegrable ..) intervalIntegrable_const
        (fun β hβ => point_squared hx hL hux hq hqq (abs_le.mpr hβ) hE0 (hE q a hq hqq))
      _ = 2*W*K := by rw [intervalIntegral.integral_const, smul_eq_mul]; ring
      _ ≤ 2*((Q:ℝ)/D)*K := mul_le_mul_of_nonneg_right (by linarith only [hsmall]) (by dsimp [K]; positivity)
      _ ≤ B := by
        dsimp [K, B]
        field_simp
        linarith only [mul_le_mul_of_nonneg_right hxr hE0]
  calc
    _ ≤ ∑ _q ∈ Icc 1 Q, ((Q:ℝ)+1)*B := by
      apply sum_le_sum; intro q hq
      obtain ⟨hl,hr⟩ := mem_Icc.mp hq
      calc
        _ ≤ ∑ _a ∈ range (q+1), B := sum_le_sum (fun a _ => each q a hl hr)
        _ = ((q:ℝ)+1)*B := by simp
        _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast (show q+1≤Q+1 by omega)) hb
    _ = (Q:ℝ)*(((Q:ℝ)+1)*B) := by simp
    _ ≤ (Q:ℝ)*((2*(Q:ℝ))*B) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by linarith) hb) (by positivity)
    _ = _ := by dsimp [B]; ring

end
end BulkCircle
end

section
open Finset Filter MeasureTheory
namespace BulkCircle
open GoldbachMajorArc
open scoped Topology
noncomputable section

theorem major_error {x Q L D n m : ℕ} (hx : x≤64*D) (hL : 0<L) (hux : L+D+1≤x)
    (hn : n=m+2*(L+1)) (hsep : 2*Q^2<D) (hQ : 1≤Q) {E : ℝ} (hE0 : 0≤E)
    (hE : ∀ q a : ℕ, 0<q → q≤Q → prefixError x ((a:ℝ)/q) (unitMean q a) ≤ q*E) :
    anchoredModel D Q n m - (GoldbachBlockGeometry.majorContribution Q D (integrand L D n)).re ≤ 2048000*(Q:ℝ)^4*E := by
  let C (q a : ℕ) := unitMean q a ^ 2 * phase (-(n:ℝ)*GoldbachBlockGeometry.center q a)
  let K := GoldbachEstermannKernel.twisted D m
  have hC : C 1 0 = C 1 1 := by
    have hu (a : ℕ) : unitMean 1 a = 1 := by rw [unitMean_eq_ram (by simp),ram_one]; simp
    have hz : phase 0 = 1 := by simp [phase]
    have hint : phase (-(n:ℝ)) = 1 := by
      unfold phase; convert Complex.exp_int_mul_two_pi_mul_I (-(n:ℤ)) using 2
      push_cast; ring
    simp [C,hu,GoldbachBlockGeometry.center,hz,hint]
  have hF : Continuous (integrand L D n) := by unfold integrand S primeSum phase; fun_prop
  have hK : Continuous K := by
    unfold K GoldbachEstermannKernel.twisted GoldbachEstermannKernel.kernel GoldbachEstermannKernel.phase
    fun_prop
  have h := GoldbachBlockGeometry.major_error (integrand L D n) K hF hK C hC hsep
  have hcoef (q : ℕ) : (∑ a ∈ (range q).filter (fun a => a.Coprime q), C q a) = coefficient q n :=
    sum_centers_eq_coefficient q n
  simp_rw [hcoef] at h
  let model := ∑ q ∈ Icc 1 Q, coefficient q n *
    ∫ β in -(blockWidth D Q q)..blockWidth D Q q, GoldbachEstermannKernel.twisted D m β
  have ht (q a : ℕ) (t : ℝ) : ‖integrand L D n (GoldbachBlockGeometry.center q a + t)-C q a*K t‖ =
      ‖S L D ((a:ℝ)/q+t)^2-(unitMean q a*U L D t)^2‖ := remove_phase q a L D n m hn t
  simp_rw [ht] at h
  have hr := Complex.re_le_norm (model - GoldbachBlockGeometry.majorContribution Q D (integrand L D n))
  rw [Complex.sub_re,norm_sub_rev] at hr
  rw [←anchoredModel_real D Q n m]
  change model.re-_ ≤ _
  exact hr.trans (h.trans (total_squared hx hL hux hQ hE0 hE))

theorem eventually_major (B : ℕ) (hB : 0<B) :
    ∀ᶠ x : ℕ in atTop, ∀ L D n m : ℕ, x≤64*D → 0<L → L+D+1≤x →
      n=m+2*(L+1) → Even n → m≤D →
      let Q := Polylog.cutoff B x
      2*Q^2<D → 4*Real.sqrt Q*((D:ℝ)-m) ≤ (D:ℝ)/288 →
      (D:ℝ)/288 ≤ (GoldbachBlockGeometry.majorContribution Q D (integrand L D n)).re := by
  obtain ⟨M,hM,hpre⟩ := Polylog.uniform_prefix_error B (B*4) hB
  let C : ℝ := 2048000*(4^B)^4
  have hlim := (Polylog.envelope_saving B (B*4) M).const_mul C
  simp only [mul_zero] at hlim
  filter_upwards [hpre,hlim.eventually_lt_const (by norm_num : (0:ℝ)<1/(64*288)),eventually_ge_atTop (2:ℕ)] with x hpre herr hx2
  intro L D n m hx hL hux hn he hm Q hsep hshort
  have hQr : 1≤Q := pow_pos (Nat.log_pos (by decide : 1<2) (by omega : 2≤x+2)) _
  have hD : 0<D := by omega
  let env := Polylog.errorEnvelope B (B*4) M x
  have hE : 0 ≤ env := by unfold env Polylog.errorEnvelope; positivity
  have hact := major_error hx hL hux hn hsep hQr hE hpre
  have hmodel := anchoredModel_floor D Q n m hD hQr
    (by nlinarith only [hsep,Nat.le_self_pow (by decide : 2 ≠ 0) Q]) hm he
  have hpow := pow_le_pow_left₀ (Nat.cast_nonneg (α:=ℝ) Q) (Polylog.cutoff_le_log B hx2) 4
  have hcomp : (Q:ℝ)^4 ≤ (4^B)^4*(Real.log x)^(B*4) := by
    simpa only [mul_pow,pow_mul] using hpow
  have hxr : 0 < (x:ℝ) := by exact_mod_cast (show 0<x by omega)
  change C*(((Real.log x)^(B*4)*env)/(x:ℝ)) < _ at herr
  rw [←mul_div_assoc, div_lt_iff₀ hxr] at herr
  dsimp [C] at herr
  have hxd : (x:ℝ)≤64*D := by exact_mod_cast hx
  nlinarith only [hact,hmodel,hshort,herr,hxd,mul_le_mul_of_nonneg_right hcomp hE]

end
end BulkCircle
end

section
/- The finite Parseval proof below is adapted from Clrs17’s L-goldbach-continuous-parseval,
   PR #138, commit 5ab2bcbb94ec2a8224686cc2cf35f1736f882a64 (Apache-2.0).
   https://github.com/CGandGameEngineLearner/goldbach-proofs/pull/138
   The application after the finite Parseval helper is new. -/

open scoped BigOperators ComplexConjugate

private noncomputable def parsevalPhase (t : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I)

namespace WindowBessel

private theorem finiteParseval :
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); ∀ n w, intervalIntegral (fun t => ‖S n w t‖^2) (0:ℝ) 1 MeasureTheory.volume = Finset.sum (Finset.range (n+1)) (fun k => (w k)^2) := by
  dsimp only
  intro n w
  let T := Finset.range (n + 1)
  let S : ℝ → ℂ := fun t => ∑ k ∈ T, (w k : ℂ) * parsevalPhase ((k : ℝ) * t)
  let z : ℝ → ℂ := fun t => ∑ k ∈ T, ∑ j ∈ T,
    ((w k : ℂ) * (w j : ℂ)) * parsevalPhase (((j : ℝ) - (k : ℝ)) * t)
  change intervalIntegral (fun t => ‖S t‖ ^ 2) (0 : ℝ) 1 MeasureTheory.volume = _
  have hphase_mul : ∀ x y : ℝ, parsevalPhase (x + y) = parsevalPhase x * parsevalPhase y := by
    intro x y
    unfold parsevalPhase
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hphase_cont : Continuous parsevalPhase := by
    unfold parsevalPhase
    fun_prop
  have hphase_exp : ∀ m : ℤ, Complex.exp (2 * (Real.pi : ℂ) * (m : ℂ) * Complex.I) = 1 := by
    intro m
    have h : 2 * (Real.pi : ℂ) * (m : ℂ) * Complex.I =
        (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by ring
    rw [h, Complex.exp_int_mul_two_pi_mul_I]
  have hphase_one : ∀ m : ℤ, parsevalPhase (m : ℝ) = 1 := by
    intro m
    unfold parsevalPhase
    have h : (((2 * Real.pi * (m : ℝ) : ℝ) : ℂ) * Complex.I) =
        2 * (Real.pi : ℂ) * (m : ℂ) * Complex.I := by
      push_cast
      ring
    rw [h, hphase_exp m]
  have hphase_conj : ∀ x : ℝ, conj (parsevalPhase x) = parsevalPhase (-x) := by
    intro x
    unfold parsevalPhase
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  have horth : ∀ m : ℤ, intervalIntegral (fun t : ℝ => parsevalPhase ((m : ℝ) * t))
      (0 : ℝ) 1 MeasureTheory.volume = if m = 0 then 1 else 0 := by
    intro m
    have hrewrite : intervalIntegral (fun t : ℝ => parsevalPhase ((m : ℝ) * t))
        (0 : ℝ) 1 MeasureTheory.volume =
        ∫ t in (0 : ℝ)..1, Complex.exp ((((2 * Real.pi * (m : ℝ) : ℝ) : ℂ) * Complex.I) * (t : ℂ)) := by
      refine intervalIntegral.integral_congr (fun t _ => ?_)
      unfold parsevalPhase
      congr 1
      push_cast
      ring
    rw [hrewrite]
    by_cases hm : m = 0
    · subst hm
      simp
    · have hmr : (m : ℝ) ≠ 0 := by
        intro hzero
        exact hm (by exact_mod_cast hzero)
      have h1 : (2 * Real.pi * (m : ℝ)) ≠ 0 :=
        mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) hmr
      have hc : (((2 * Real.pi * (m : ℝ) : ℝ) : ℂ) * Complex.I) ≠ 0 := by
        have h2 : ((2 * Real.pi * (m : ℝ) : ℝ) : ℂ) ≠ 0 := by
          simpa [Complex.ofReal_eq_zero] using h1
        exact mul_ne_zero h2 Complex.I_ne_zero
      have hval : Complex.exp ((((2 * Real.pi * (m : ℝ) : ℝ) : ℂ)) * Complex.I) = 1 := by
        have hone := hphase_one m
        simpa only [parsevalPhase] using hone
      rw [integral_exp_mul_complex hc]
      simp [hphase_exp m, hm]
  have hint_single : ∀ (c : ℂ) (a : ℝ),
      IntervalIntegrable (fun t : ℝ => c * parsevalPhase (a * t)) MeasureTheory.volume (0 : ℝ) 1 := by
    intro c a
    exact (continuous_const.mul (hphase_cont.comp (by fun_prop))).intervalIntegrable (0 : ℝ) 1
  have hpoint : ∀ t : ℝ, (Complex.normSq (S t) : ℂ) = z t := by
    intro t
    rw [Complex.normSq_eq_conj_mul_self]
    dsimp only [S, z]
    rw [map_sum, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro j hj
    simp only [map_mul, Complex.conj_ofReal, hphase_conj]
    have hmul : parsevalPhase (-((k : ℝ) * t)) * parsevalPhase ((j : ℝ) * t) =
        parsevalPhase (((j : ℝ) - (k : ℝ)) * t) := by
      rw [← hphase_mul]
      congr 1
      ring
    calc
      ((w k : ℂ) * parsevalPhase (-((k : ℝ) * t))) *
          ((w j : ℂ) * parsevalPhase ((j : ℝ) * t)) =
          ((w k : ℂ) * (w j : ℂ)) *
            (parsevalPhase (-((k : ℝ) * t)) * parsevalPhase ((j : ℝ) * t)) := by ring
      _ = ((w k : ℂ) * (w j : ℂ)) * parsevalPhase (((j : ℝ) - (k : ℝ)) * t) := by
        rw [hmul]
  have hint_z : IntervalIntegrable z MeasureTheory.volume (0 : ℝ) 1 := by
    dsimp only [z]
    exact (continuous_finsetSum _ (fun k _ => continuous_finsetSum _
      (fun j _ => continuous_const.mul (hphase_cont.comp (by fun_prop))))).intervalIntegrable (0 : ℝ) 1
  have hmain : intervalIntegral z (0 : ℝ) 1 MeasureTheory.volume =
      ((∑ k ∈ T, (w k) ^ 2 : ℝ) : ℂ) := by
    dsimp only [z]
    have houter (k : ℕ) (hk : k ∈ T) : IntervalIntegrable (fun t : ℝ => ∑ j ∈ T,
        ((w k : ℂ) * (w j : ℂ)) * parsevalPhase (((j : ℝ) - (k : ℝ)) * t))
        MeasureTheory.volume (0 : ℝ) 1 := by
      exact (continuous_finsetSum _ (fun j _ => continuous_const.mul
        (hphase_cont.comp (by fun_prop)))).intervalIntegrable (0 : ℝ) 1
    rw [intervalIntegral.integral_finsetSum houter]
    have hstep : ∀ k ∈ T, intervalIntegral (fun t : ℝ => ∑ j ∈ T,
        ((w k : ℂ) * (w j : ℂ)) * parsevalPhase (((j : ℝ) - (k : ℝ)) * t))
        (0 : ℝ) 1 MeasureTheory.volume = ∑ j ∈ T,
        ((w k : ℂ) * (w j : ℂ)) * (if ((j : ℤ) - (k : ℤ)) = 0 then 1 else 0) := by
      intro k hk
      rw [intervalIntegral.integral_finsetSum (fun j _ =>
        hint_single ((w k : ℂ) * (w j : ℂ)) (((j : ℝ) - (k : ℝ))))]
      apply Finset.sum_congr rfl
      intro j hj
      rw [intervalIntegral.integral_const_mul]
      congr 1
      have hm : ((j : ℝ) - (k : ℝ)) = (((j : ℤ) - (k : ℤ) : ℤ) : ℝ) := by
        push_cast
        ring
      simp_rw [hm]
      rw [horth]
    calc
      (∑ k ∈ T, intervalIntegral (fun t : ℝ => ∑ j ∈ T,
          ((w k : ℂ) * (w j : ℂ)) * parsevalPhase (((j : ℝ) - (k : ℝ)) * t))
          (0 : ℝ) 1 MeasureTheory.volume) =
          ∑ k ∈ T, ∑ j ∈ T, ((w k : ℂ) * (w j : ℂ)) *
            (if ((j : ℤ) - (k : ℤ)) = 0 then 1 else 0) := Finset.sum_congr rfl hstep
      _ = ((∑ k ∈ T, (w k) ^ 2 : ℝ) : ℂ) := by
        push_cast
        simp only [sub_eq_zero, Int.ofNat_inj]
        apply Finset.sum_congr rfl
        intro k hk
        simp [hk, pow_two]
  have hre : intervalIntegral (fun t => (z t).re) (0 : ℝ) 1 MeasureTheory.volume =
      (intervalIntegral z (0 : ℝ) 1 MeasureTheory.volume).re := by
    rw [intervalIntegral.intervalIntegral_eq_integral_uIoc,
      intervalIntegral.intervalIntegral_eq_integral_uIoc]
    simp only [show (0 : ℝ) ≤ 1 by norm_num, ite_true, one_smul]
    exact integral_re hint_z.def'
  calc
    intervalIntegral (fun t => ‖S t‖ ^ 2) (0 : ℝ) 1 MeasureTheory.volume =
        intervalIntegral (fun t => (z t).re) (0 : ℝ) 1 MeasureTheory.volume := by
      apply intervalIntegral.integral_congr
      intro t ht
      have hp := congrArg Complex.re (hpoint t)
      simpa only [Complex.ofReal_re, Complex.normSq_eq_norm_sq] using hp
    _ = (intervalIntegral z (0 : ℝ) 1 MeasureTheory.volume).re := hre
    _ = ∑ k ∈ T, (w k) ^ 2 := by rw [hmain]; exact Complex.ofReal_re _



end WindowBessel

/- The summation over integer frequencies uses Mathlib’s interval Parseval theorem
   hasSum_sq_fourierCoeffOn (Analysis/Fourier/AddCircle). -/

open MeasureTheory Filter

namespace WindowBessel

private theorem maskedBessel :
    let E (x : ℝ) := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I); let S (X : ℕ) (u : ℕ → ℝ) (t : ℝ) := ∑ k ∈ Finset.range (X+1), (u k : ℂ) * E ((k : ℝ)*t); ∀ (X M : ℕ) (u : ℕ → ℝ) (A : Set ℝ), MeasurableSet A → (∑ m ∈ Finset.range M, ‖intervalIntegral (A.indicator (fun t => (S X u t)^2 * E (-(m : ℝ)*t))) (0 : ℝ) 1 MeasureTheory.volume‖^2) ≤ intervalIntegral (A.indicator (fun t => ‖S X u t‖^4)) (0 : ℝ) 1 MeasureTheory.volume := by
  intro E S X M u A hA
  let f := A.indicator (fun t => (S X u t)^2)
  let μ := volume.restrict (Set.Ioc (0:ℝ) 1)
  have hc : Continuous (fun t => (S X u t)^2) := by dsimp [S,E]; fun_prop
  have hmem : MemLp f 2 μ := by
    apply MemLp.indicator hA.nullMeasurableSet
    apply (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).2
    exact ((hc.norm.pow 2).intervalIntegrable (μ := volume) 0 1).1
  have hcoeff (m : ℕ) : fourierCoeffOn zero_lt_one f (m:ℤ) =
      ∫ t in (0:ℝ)..1, A.indicator (fun t => (S X u t)^2 * E (-(m:ℝ)*t)) t := by
    rw [fourierCoeffOn_eq_integral, sub_zero, one_div_one, one_smul]
    apply intervalIntegral.integral_congr
    intro t _
    by_cases h : t ∈ A
    · simp only [f, Set.indicator_of_mem h, smul_eq_mul, fourier_coe_apply]
      rw [mul_comm]
      congr 2
      dsimp [E]
      push_cast
      ring
    · simp [f,h]
  let s : Finset ℤ := (Finset.range M).map ⟨Int.ofNat, fun _ _ h => Int.ofNat_inj.mp h⟩
  have hParse := hasSum_sq_fourierCoeffOn zero_lt_one hmem
  have hbound := sum_le_hasSum s (fun i _ => sq_nonneg ‖fourierCoeffOn zero_lt_one f i‖) hParse
  have hpoint (t : ℝ) : ‖f t‖^2 = A.indicator (fun t => ‖S X u t‖ ^ 4) t := by
    by_cases ht : t ∈ A
    · simp only [f,Set.indicator_of_mem ht,norm_pow]; ring
    · simp [f, ht]
  simp only [s, Finset.sum_map, sub_zero, inv_one, one_smul, hpoint] at hbound
  change (∑ m ∈ Finset.range M, ‖fourierCoeffOn zero_lt_one f (m : ℤ)‖^2) ≤ _ at hbound
  simp_rw [hcoeff] at hbound
  exact hbound

end WindowBessel

open MeasureTheory Filter

namespace WindowBessel

theorem minorFourthMoment :
    let E (x : ℝ) := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I); let S (X : ℕ) (u : ℕ → ℝ) (t : ℝ) := ∑ k ∈ Finset.range (X+1), (u k : ℂ) * E ((k : ℝ)*t); ∀ (X M : ℕ) (u : ℕ → ℝ) (A : Set ℝ) (U : ℝ), MeasurableSet A → 0 ≤ U → (∀ t ∈ Set.Icc (0 : ℝ) 1, t ∉ A → ‖S X u t‖ ≤ U) → (∑ m ∈ Finset.range M, ‖intervalIntegral (Aᶜ.indicator (fun t => (S X u t)^2 * E (-(m : ℝ)*t))) (0 : ℝ) 1 MeasureTheory.volume‖^2) ≤ U^2 * ∑ k ∈ Finset.range (X+1), (u k)^2 := by
  intro E S X M u A U hA hU hsup
  have hc : Continuous (S X u) := by dsimp [S,E]; fun_prop
  have hfour : IntervalIntegrable (Aᶜ.indicator (fun t => ‖S X u t‖^4)) volume 0 1 :=
    ⟨((hc.norm.pow 4).intervalIntegrable _ _).1.indicator hA.compl,
      ((hc.norm.pow 4).intervalIntegrable _ _).2.indicator hA.compl⟩
  calc
    _ ≤ ∫ t in (0:ℝ)..1, Aᶜ.indicator (fun t => ‖S X u t‖^4) t :=
      maskedBessel X M u Aᶜ hA.compl
    _ ≤ ∫ t in (0:ℝ)..1, U^2 * ‖S X u t‖^2 := by
      apply intervalIntegral.integral_mono_on zero_le_one hfour
        ((continuous_const.mul (hc.norm.pow 2)).intervalIntegrable _ _)
      intro t ht
      by_cases h : t ∈ Aᶜ
      · rw [Set.indicator_of_mem h]
        calc
          ‖S X u t‖ ^ 4 = ‖S X u t‖ ^ 2 * ‖S X u t‖ ^ 2 := by ring
          _ ≤ U^2 * ‖S X u t‖^2 := by gcongr; exact hsup t ht h
      · rw [Set.indicator_of_notMem h]
        exact mul_nonneg (sq_nonneg U) (sq_nonneg _)
    _ = _ := by rw [intervalIntegral.integral_const_mul, finiteParseval X u]

end WindowBessel

/- The Fourier coefficient, arc measurability and indicator-splitting lemmas are adapted
from TranswarpDrive, goldbach-proofs PR #158 (Apache-2.0), commit
d03fe72a521e7e8e5e06447bc0bae3a1d34465d8. The unrestricted frequency below detects an exceptional integer. -/

open MeasureTheory

namespace WindowBessel.ExceptionalCoefficients

private noncomputable def E (x : ℝ) : ℂ := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

private lemma phase_add (u v : ℝ) : E (u + v) = E u * E v := by
  unfold E
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private lemma fourier_mode (m : ℤ) :
    (∫ t in (0 : ℝ)..1, E ((m : ℝ) * t)) = if m = 0 then 1 else 0 := by
  by_cases hm : m = 0
  · subst m
    simp [E]
  let c : ℂ := (m : ℂ) * (2 * Real.pi * Complex.I)
  have he (t : ℝ) : E ((m : ℝ) * t) = Complex.exp (c * (t : ℂ)) := by
    unfold E c
    congr 1
    push_cast
    ring
  have hc : c ≠ 0 := by
    dsimp [c]
    exact mul_ne_zero (by exact_mod_cast hm)
      (mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero)
  simp_rw [he]
  rw [integral_exp_mul_complex hc]
  simp [hm, c, Complex.exp_int_mul_two_pi_mul_I]

theorem zero_from_pairs (w : ℕ → ℝ) (n Y : ℕ) (hn : ∀ k j : ℕ, k+j=n → w k*w j=0) :
    (∫ t in (0 : ℝ)..1, (∑ k ∈ Finset.range (Y+1), (w k : ℂ)*E ((k : ℝ)*t))^2 * E (-(n:ℝ)*t)) = 0 := by
  let I := Finset.range (Y+1)
  let term := fun (k j : ℕ) (t : ℝ) =>
    ((w k : ℂ) * (w j : ℂ)) * E (((((k : ℤ) + j - n) : ℤ) : ℝ) * t)
  have hcont (k j : ℕ) : Continuous (term k j) := by dsimp [term, E]; fun_prop
  have hpoint (t : ℝ) : (∑ k ∈ I, (w k : ℂ) * E ((k : ℝ) * t)) ^ 2 * E (-(n : ℝ) * t) =
      ∑ k ∈ I, ∑ j ∈ I, term k j t := by
    simp only [sq, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun j _ => ?_))
    dsimp [term]
    push_cast
    rw [show ((k : ℝ) + j - n) * t = ((k : ℝ) * t + j * t) + -(n : ℝ) * t by ring,
      phase_add, phase_add]
    ring
  change (∫ t in (0:ℝ)..1, (∑ k ∈ I, (w k : ℂ) * E ((k : ℝ) * t))^2 * E (-(n:ℝ)*t)) = _
  simp_rw [hpoint]
  rw [intervalIntegral.integral_finsetSum (fun k _ =>
    (continuous_finsetSum I (fun j _ => hcont k j)).intervalIntegrable _ _)]
  apply Finset.sum_eq_zero
  intro k _
  rw [intervalIntegral.integral_finsetSum (fun j _ => (hcont k j).intervalIntegrable _ _)]
  apply Finset.sum_eq_zero
  intro j _
  simp only [term, intervalIntegral.integral_const_mul, fourier_mode]
  by_cases heq : (k : ℤ)+j-n = 0
  · have hz : w k*w j=0 := hn k j (by omega)
    simp only [heq, if_true, mul_one]
    exact_mod_cast hz
  · simp [heq]

/-- Split any interval-integrable complex coefficient at an arbitrary measurable set. -/
theorem indicator_integral_split {f : ℝ → ℂ} {s : Set ℝ} (hs : MeasurableSet s)
    {a b : ℝ} (hf : IntervalIntegrable f volume a b) :
    intervalIntegral (s.indicator f) a b volume +
      intervalIntegral (sᶜ.indicator f) a b volume = intervalIntegral f a b volume := by
  have hi {u : Set ℝ} (hu : MeasurableSet u) :
      IntervalIntegrable (u.indicator f) volume a b :=
    ⟨hf.1.indicator hu, hf.2.indicator hu⟩
  rw [← intervalIntegral.integral_add (hi hs) (hi hs.compl)]
  apply congrArg (fun g : ℝ → ℂ => intervalIntegral g a b volume)
  funext t
  by_cases ht : t ∈ s <;> simp [ht]


end WindowBessel.ExceptionalCoefficients
end

section
open Finset Filter MeasureTheory
namespace BulkCircle
open GoldbachMajorArc
noncomputable section

def target (x : ℕ) := (range (2*x+1)).filter (fun n => Even n ∧ 13*x≤12*n ∧ 4*n≤5*x)
def band (x : ℕ) := (range (x+1)).filter (fun k => x≤2*k ∧ 3*k≤2*x)
def rep (x n : ℕ) := ∑ p ∈ (band x).filter (fun p => n-p ∈ band x ∧ p≤n), primeWeight p*primeWeight (n-p)
def ww (L D k : ℕ) := if L<k ∧ k≤L+D+1 then primeWeight k else 0
def holes (x : ℕ) := (target x).filter (fun n => rep x n=0)

theorem pw_nonneg (k : ℕ) : 0≤primeWeight k := by
  unfold primeWeight; split <;> rename_i h
  · exact Real.log_nonneg (by exact_mod_cast h.one_le)
  · rfl

theorem as_mask (x L D : ℕ) (hx : L+D+1≤x) (t : ℝ) :
    S L D t = ∑ k ∈ range (x+1), (ww L D k:ℂ)*phase ((k:ℝ)*t) := by
  let A := range (L+D+1+1)
  let B := range (L+1)
  have hsub : B⊆A := range_subset_range.mpr (by omega)
  have hset : A \ B = (range (x+1)).filter (fun k => L<k ∧ k≤L+D+1) := by
    ext k; simp [A,B]; omega
  unfold S primeSum
  rw [←sum_sdiff_eq_sub hsub, hset, sum_filter]
  apply sum_congr rfl; intro k _
  by_cases h : L<k ∧ k≤L+D+1 <;> simp [ww,h]

theorem zero_pairs {L D x n : ℕ} (win : ∀ k : ℕ, L<k → k≤L+D+1 → k∈band x)
    (hrep : rep x n=0) (i j : ℕ) (hij : i+j=n) : ww L D i * ww L D j=0 := by
  by_cases hi : L < i ∧ i≤L+D+1
  · by_cases hj : L < j ∧ j≤L+D+1
    · rw [ww,if_pos hi,ww,if_pos hj]
      have hn : n-i=j := by omega
      have hmem : i∈(band x).filter (fun p => n-p ∈ band x ∧ p≤n) := mem_filter.mpr
        ⟨win _ hi.1 hi.2,hn ▸ win _ hj.1 hj.2,by omega⟩
      have h := Finset.single_le_sum (f := fun p => primeWeight p*primeWeight (n-p))
        (fun p _ => mul_nonneg (pw_nonneg p) (pw_nonneg _)) hmem
      change primeWeight i * primeWeight (n-i) ≤ rep x n at h
      rw [hn,hrep] at h
      exact le_antisymm h (mul_nonneg (pw_nonneg _) (pw_nonneg _))
    · simp [ww,hj]
  · simp [ww,hi]

theorem mask_energy (x L D : ℕ) : (∑ k ∈ range (x+1), (ww L D k)^2) ≤ ((x:ℝ)+1)*(Real.log x)^2 := by
  calc
    _ ≤ ∑ _k ∈ range (x+1), (Real.log x)^2 := by
      refine sum_le_sum fun k hk => ?_
      by_cases h : L<k ∧ k≤L+D+1 ∧ k.Prime
      · have hkx : (k:ℝ) ≤ x := by exact_mod_cast Nat.le_of_lt_succ (mem_range.mp hk)
        rw [ww,if_pos ⟨h.1,h.2.1⟩, primeWeight, if_pos h.2.2]
        apply pow_le_pow_left₀ (Real.log_nonneg (by exact_mod_cast h.2.2.one_le))
        exact Real.log_le_log (by exact_mod_cast h.2.2.pos) hkx
      · by_cases h1 : L<k ∧ k≤L+D+1
        · have hn : ¬ k.Prime := fun hp => h ⟨h1.1,h1.2,hp⟩
          simp [ww,primeWeight,h1,hn,sq_nonneg]
        · simp [ww,h1,sq_nonneg]
    _ = _ := by simp

theorem masked_count {x L D M H : ℕ} {T : ℝ} {A : Set ℝ}
    (hux : L+D+1≤x) (win : ∀ k : ℕ, L<k → k≤L+D+1 → k∈band x)
    (hA : MeasurableSet A) (hT : 0≤T)
    (hmajor : ∀ n∈(Ico (M-H) M) ∩ holes x, (D:ℝ)/288 ≤ (∫ t in (0:ℝ)..1, A.indicator (integrand L D n) t).re)
    (hminor : ∀ t∈Set.Icc (0:ℝ) 1, t∉A → ‖S L D t‖ ≤ T) :
    (((Ico (M-H) M) ∩ holes x).card:ℝ)*((D:ℝ)/288)^2 ≤ T^2 * (((x:ℝ)+1)*(Real.log x)^2) := by
  let Tset := (Ico (M-H) M) ∩ holes x
  let minor (n : ℕ) := ∫ t in (0:ℝ)..1, Aᶜ.indicator (integrand L D n) t
  have hsub : Tset ⊆ range M := fun n hn => mem_range.mpr (mem_Ico.mp (mem_inter.mp hn).1).2
  have hf (n : ℕ) (hn : n∈Tset) : ((D:ℝ)/288)^2 ≤ ‖minor n‖^2 := by
    have hn0 : rep x n=0 := (mem_filter.mp (mem_inter.mp hn).2).2
    have full := WindowBessel.ExceptionalCoefficients.zero_from_pairs (ww L D) n x (zero_pairs win hn0)
    have hfull : (∫ t in (0:ℝ)..1, integrand L D n t)=0 := by
      unfold integrand
      simp_rw [as_mask _ _ _ hux]
      exact full
    have hcont : Continuous (integrand L D n) := by unfold integrand S primeSum phase; fun_prop
    have hsplit := (WindowBessel.ExceptionalCoefficients.indicator_integral_split hA (hcont.intervalIntegrable 0 1)).trans hfull
    have hRe := congrArg Complex.re hsplit
    rw [Complex.add_re, Complex.zero_re] at hRe
    change _ + (minor n).re=0 at hRe
    apply pow_le_pow_left₀ (by positivity)
    linarith only [hmajor n hn, hRe, (abs_le.mp (Complex.abs_re_le_norm (minor n))).1]
  have hmoment : (∑ n ∈ range M, ‖minor n‖^2) ≤ T^2 * ∑ k ∈ range (x+1), (ww L D k)^2 := by
    unfold minor integrand
    simp_rw [as_mask _ _ _ hux] at hminor ⊢
    exact WindowBessel.minorFourthMoment x M (ww L D) A T hA hT hminor
  calc
    _ = ∑ _n ∈ Tset, ((D:ℝ)/288)^2 := by simp [Tset]
    _ ≤ ∑ n ∈ Tset, ‖minor n‖^2 := sum_le_sum hf
    _ ≤ _ := (sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)).trans
      (hmoment.trans (mul_le_mul_of_nonneg_left (mask_energy x L D) (sq_nonneg _)))

end
end BulkCircle
end

section
open Finset Filter MeasureTheory
open scoped Topology BigOperators
namespace BulkCircle
open GoldbachMajorArc
noncomputable section

theorem holes_card_le (x : ℕ) : (holes x).card ≤ 2*x+1 := by
  calc (holes x).card ≤ (target x).card := card_le_card (filter_subset _ _)
    _ ≤ (range (2*x+1)).card := card_le_card (filter_subset _ _)
    _ = 2*x+1 := card_range _

/-! ### Generalised exponent tail -/

def cut (e x : ℕ) : ℕ := Polylog.cutoff (2*e+36) x
def root (e x : ℕ) : ℕ := Polylog.cutoff (e+18) x
def length (x : ℕ) : ℕ := x/32
def block (e x : ℕ) : ℕ := x/(1000000*root e x)
def start (x M : ℕ) : ℕ := (M-length x+1)/2-1

theorem cut_sq (e x : ℕ) : cut e x=(root e x)^2 := by
  unfold cut root Polylog.cutoff
  rw [← pow_mul, show (e+18)*2 = 2*e+36 by ring]

theorem rpos (e x : ℕ) : 1 ≤ root e x :=
  pow_pos (Nat.log_pos (by decide : 1<2) (by omega : 2≤x+2)) _

set_option maxRecDepth 20000 in
theorem eventually_grid (e : ℕ) :
    ∀ᶠ x : ℕ in atTop, 1000000000*(root e x)^4 ≤ x := by
  have hlim : Tendsto (fun x : ℕ => (Real.log x)^(4*(e+18))/(x:ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.rpow_natCast, Real.rpow_one] using
      ((isLittleO_log_rpow_rpow_atTop ((4*(e+18):ℕ):ℝ) (by norm_num : (0:ℝ)<1)).tendsto_div_nhds_zero.comp
        (tendsto_natCast_atTop_atTop (R := ℝ)))
  have ht := hlim.const_mul (1000000000*(4:ℝ)^(4*(e+18)))
  simp only [mul_zero] at ht
  filter_upwards [ht.eventually_lt_const zero_lt_one, eventually_ge_atTop (2:ℕ)] with x h hx
  have hxR : (0:ℝ)<x := by exact_mod_cast (show 0<x by omega)
  change 1000000000*4^(4*(e+18))*((Real.log x)^(4*(e+18))/x)<1 at h
  rw [←mul_div_assoc,div_lt_one hxR] at h
  have hp := pow_le_pow_left₀ (Nat.cast_nonneg (α:=ℝ) (root e x)) (Polylog.cutoff_le_log (e+18) hx) 4
  have same : (((4:ℝ)*Real.log x)^(e+18))^4 = (4:ℝ)^(4*(e+18)) * (Real.log x)^(4*(e+18)) := by
    rw [← pow_mul, mul_pow, show (e+18)*4 = 4*(e+18) by ring]
  rw [same] at hp
  exact_mod_cast (show (1000000000:ℝ)*(root e x:ℝ)^4 ≤ x by linarith only [hp,h])

theorem grid_bounds (e x : ℕ) (hx : 1000000000*(root e x)^4 ≤ x) :
    0<block e x ∧ block e x≤x ∧ 100*block e x≤x ∧
    x/block e x+1 ≤ 3000000*root e x ∧ x≤64*length x ∧
    2*(cut e x)^2<length x ∧
    4*Real.sqrt (cut e x)*((block e x:ℝ)+1) ≤ (length x:ℝ)/288 := by
  let r := root e x
  have hr : 1≤r := rpos e x
  have hr4 : r ≤ r^4 := Nat.le_self_pow (by decide) r
  have hlarge : 1000000000*r ≤ x := (Nat.mul_le_mul_left _ hr4).trans hx
  let den := 1000000*r
  have hden : 0<den := by dsimp [den]; omega
  have hdenbig : 100≤den := by dsimp [den]; omega
  have hH : 1≤block e x := (Nat.le_div_iff_mul_le hden).mpr (by dsimp [den]; omega)
  have hdprod : block e x*den≤x := Nat.div_mul_le_self x den
  have hsmall : 100*block e x≤x := by
    rw [Nat.mul_comm]; exact (Nat.mul_le_mul_left _ hdenbig).trans hdprod
  have hcount : x/block e x+1 ≤ 3*den := by
    have lt := (Nat.div_lt_iff_lt_mul hden).mp (Nat.lt_succ_self (block e x))
    have hH2 : block e x+1 ≤ 2*block e x := by omega
    have hh := Nat.mul_le_mul_right den hH2
    have bound : x < (2*den)*block e x := by
      rw [show 2*den*block e x=2*block e x*den by ring]; exact lt_of_lt_of_le lt hh
    have := (Nat.div_lt_iff_lt_mul hH).mpr bound
    omega
  have hsize : x≤64*length x := by dsimp [length]; omega
  have hsep : 2*(cut e x)^2 < length x := by
    rw [cut_sq, ←pow_mul]; norm_num
    dsimp [length]
    have : 0<(root e x)^4 := pow_pos (rpos e x) _
    omega
  refine ⟨hH,Nat.div_le_self _ _,hsmall,?_,hsize,hsep,?_⟩
  · dsimp [den] at hcount
    omega
  rw [cut_sq,Nat.cast_pow,Real.sqrt_sq (Nat.cast_nonneg _)]
  change 4*(r:ℝ)*((block e x:ℝ)+1) ≤ (length x:ℝ)/288
  have mulb : 1000000*((r:ℝ)*(block e x:ℝ)) ≤ x := by
    exact_mod_cast (show 1000000*(r*block e x)≤x by convert hdprod using 1 <;> dsimp [den] <;> ring)
  have big : 1000000000*(r:ℝ) ≤ x := by exact_mod_cast hlarge
  have ds : (x:ℝ)≤64*length x := by exact_mod_cast hsize
  linarith only [mulb,big,ds]

theorem window_geometry {e x M : ℕ} (hx : 100≤x) (hsmall : 100*block e x≤x)
    (hJ : ((Ico (M-block e x) M) ∩ holes x).Nonempty) :
    0<start x M ∧ start x M+length x+1≤x ∧ x≤4*start x M ∧
    (∀ k : ℕ, start x M<k → k ≤ start x M+length x+1 → k∈band x) ∧
    ∀ n∈(Ico (M-block e x) M) ∩ holes x, ∃ m : ℕ, n=m+2*(start x M+1) ∧
      m≤length x ∧ length x-m≤block e x+1 := by
  obtain ⟨v,hv⟩ := hJ
  obtain ⟨hi,hh⟩ := mem_inter.mp hv
  have hvI := mem_Ico.mp hi
  have hvT := mem_filter.mp (mem_filter.mp hh).1
  dsimp [start,length] at *
  refine ⟨by omega,by omega,by omega,?_,?_⟩
  · intro k h1 h2
    simp only [band,mem_filter,mem_range]; omega
  · intro n hn
    have hIn := mem_Ico.mp (mem_inter.mp hn).1
    refine ⟨n-2*((M-x/32+1)/2-1+1),?_,?_,?_⟩ <;> omega

set_option maxHeartbeats 500000 in
theorem minor_window (e : ℕ) :
  ∀ᶠ x : ℕ in atTop, ∀ L D : ℕ, x≤4*L → 0<D → D≤L → L+D+1≤x →
    ∀ t∈Set.Icc (0:ℝ) 1, t∉GoldbachBlockGeometry.arcs (Polylog.cutoff (2*e+36) x) D →
      ‖S L D t‖ ≤ (2:ℝ)^(e+11)*x/(Real.log x)^(e+10) := by
  obtain ⟨N,hN⟩ := GoldbachEstermann.uniformMinorSum ((e+10:ℕ):ℝ) (by positivity)
  have he : 2*⌈((e+10:ℕ):ℝ)⌉₊+16 = 2*e+36 := by rw [Nat.ceil_natCast]; ring
  rw [he] at hN
  filter_upwards [eventually_ge_atTop (4*N+20)] with x hx
  intro L D hxL hD hDL hLx t ht hminor
  have hxpos : 0 < (x:ℝ) := by exact_mod_cast (show 0<x by omega)
  have hlog : 0 < Real.log x := Real.log_pos (by exact_mod_cast (show 1<x by omega))
  have single (u : ℕ) (hLu : L≤u) (hux : u≤x) :
      ‖primeSum u t‖ ≤ (2:ℝ)^(e+10)*x/(Real.log x)^(e+10) := by
    have hu4 : 4≤u := by omega
    have hu0 : 0 < (u:ℝ) := by exact_mod_cast (show 0<u by omega)
    have hl : 0 < Real.log u := Real.log_pos (by exact_mod_cast (show 1<u by omega))
    have hsq : x≤u^2 := by nlinarith only [hxL,hLu,hu4, Nat.mul_le_mul_left u hu4]
    have hlog2 : Real.log x ≤ 2*Real.log u := by
      have := Real.log_le_log hxpos (show (x:ℝ) ≤ (u:ℝ)^2 by exact_mod_cast hsq)
      simpa only [Real.log_pow,Nat.cast_ofNat] using this
    have hcap : Polylog.cutoff (2*e+36) u ≤ Polylog.cutoff (2*e+36) x :=
      Nat.pow_le_pow_left (Nat.log_mono_right (by omega)) _
    have hoff : t ∉ GoldbachBlockGeometry.arcs (Polylog.cutoff (2*e+36) u) u := by
      rintro ⟨q,a,hq,hqu,har,hcop,hβ⟩
      apply hminor
      refine ⟨q,a,hq,hqu.trans hcap,har,hcop,hβ.trans ?_⟩
      change ((Polylog.cutoff (2*e+36) u):ℝ)/((q:ℝ)*u) ≤ ((Polylog.cutoff (2*e+36) x):ℝ)/((q:ℝ)*D)
      have hDr : (0:ℝ)<D := by exact_mod_cast hD
      have hqr : (0:ℝ)<q := by exact_mod_cast hq
      apply div_le_div₀ (by positivity) (by exact_mod_cast hcap) (by positivity) (by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact_mod_cast (hDL.trans hLu))
    have hh := (hN u (by omega) t ht hoff).2
    change ‖primeSum u t‖ ≤ (u:ℝ)*(Real.log u)^(-((e+10:ℕ):ℝ)) at hh
    rw [Real.rpow_neg hl.le, show (Real.log u)^((e+10:ℕ):ℝ) = (Real.log u)^(e+10) from Real.rpow_natCast _ _, ←div_eq_mul_inv] at hh
    apply hh.trans
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hp := pow_le_pow_left₀ hlog.le hlog2 (e+10)
    rw [mul_pow] at hp
    calc
      _ ≤ (x:ℝ)*((2:ℝ)^(e+10)*(Real.log u)^(e+10)) := mul_le_mul (by exact_mod_cast hux) hp (by positivity) hxpos.le
      _ = _ := by ring
  have h1 := single (L+D+1) (by omega) hLx
  have h2 := single L (by omega) (by omega)
  refine (norm_sub_le ..).trans ((add_le_add h1 h2).trans_eq ?_)
  have key : (2:ℝ)^(e+11) = (2:ℝ)^(e+10) + (2:ℝ)^(e+10) := by
    rw [show e+11 = (e+10)+1 by ring, pow_succ]; ring
  rw [key]; ring

private theorem count_algebra (e : ℕ) (x d l c y : ℝ) (hx : 1≤x) (hl : 0<l)
    (hy : 0≤y) (hd : x≤64*d)
    (h : y*(d/288)^2 ≤ (c*x/l^(e+10))^2*((x+1)*l^2)) :
    y ≤ (2*18432^2*c^2)*x/l^(2*e+18) := by
  have hx0 : 0<x := by linarith
  have hd' : 0≤d := by linarith
  have hp : y*(x/18432)^2 ≤ (c*x/l^(e+10))^2*((x+1)*l^2) :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith : x/18432 ≤ d/288) 2) hy).trans h
  rw [le_div_iff₀ (by positivity)]
  have hmax := mul_le_mul_of_nonneg_right (by linarith : x+1≤2*x) (by positivity : 0 ≤ (18432:ℝ)^2*c^2)
  have hL : (l^(e+10))^2 = l^(2*e+18)*l^2 := by
    rw [← pow_mul, ← pow_add]; congr 1; ring
  field_simp at hp
  rw [hL] at hp
  have hpos : (0:ℝ) < l^2 := by positivity
  have h6 : y*l^(2*e+18) ≤ 18432^2*c^2*(x+1) := by
    have h5 : y*l^(2*e+18)*l^2 ≤ 18432^2*c^2*(x+1)*l^2 := by
      calc y*l^(2*e+18)*l^2 = y*(l^(2*e+18)*l^2) := by ring
        _ ≤ 18432^2*c^2*(x+1)*l^2 := hp
    exact le_of_mul_le_mul_right h5 hpos
  linarith only [h6, hmax]

def boundC (e : ℕ) : ℝ := 2*18432^2*((2:ℝ)^(e+11))^2

theorem fixed_block (e : ℕ) :
    ∀ᶠ x : ℕ in atTop, ∀ M : ℕ,
      ((((Ico (M-block e x) M) ∩ holes x).card:ℝ)) ≤ boundC e*x/(Real.log x)^(2*e+18) := by
  filter_upwards [eventually_grid e, eventually_major (2*e+36) (by omega), minor_window e,
    eventually_ge_atTop (100:ℕ)] with x hgrid hmaj hmin hx100
  intro M
  let T := (Ico (M-block e x) M) ∩ holes x
  by_cases hT : T.Nonempty
  · obtain ⟨hH,hHx,hsmall,hnum,hxD,hsep,hshort⟩ := grid_bounds e x hgrid
    let L := start x M
    let D := length x
    let Q := cut e x
    obtain ⟨hl,hux,hxL,win,freq⟩ := window_geometry hx100 hsmall hT
    have hD : 0<D := by omega
    have hDL : D≤L := by dsimp [D,length,L] at *; omega
    have hxR : (1:ℝ)≤x := by exact_mod_cast (show 1≤x by omega)
    have hlog : 0<Real.log x := Real.log_pos (by exact_mod_cast (show 1<x by omega))
    let A := GoldbachBlockGeometry.arcs Q D
    have hmajor (n : ℕ) (hn : n∈T) :
        (D:ℝ)/288 ≤ (∫ t in (0:ℝ)..1, A.indicator (integrand L D n) t).re := by
      obtain ⟨m,heq,hmd,hdm⟩ := freq n hn
      have he := (mem_filter.mp (mem_filter.mp (mem_inter.mp hn).2).1).2.1
      have hmd' : (D:ℝ) ≤ (block e x:ℝ)+1+m := by
        exact_mod_cast (show D ≤ block e x+1+m by omega)
      apply hmaj L D n m hxD hl hux heq he hmd hsep
      exact (mul_le_mul_of_nonneg_left (by linarith only [hmd'] : (D:ℝ)-m≤block e x+1) (by positivity)).trans hshort
    have hm := masked_count (A:=A) hux win (GoldbachEstermann.measurable_block_arcs _ _)
      (by positivity : 0≤(2:ℝ)^(e+11)*x/(Real.log x)^(e+10)) hmajor (hmin L D hxL hD hDL hux)
    exact count_algebra e x D _ _ _ hxR hlog (Nat.cast_nonneg _) (by exact_mod_cast hxD) hm
  · have he := Finset.not_nonempty_iff_eq_empty.mp hT
    change (T.card:ℝ) ≤ _
    rw [he]; simp only [card_empty,Nat.cast_zero]
    have hlog : 0<Real.log x := Real.log_pos (by exact_mod_cast (show 1<x by omega))
    refine div_nonneg (mul_nonneg (by unfold boundC; positivity) (Nat.cast_nonneg _)) ?_
    exact pow_nonneg hlog.le _

theorem band_bound (e : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℕ in atTop,
    ((holes x).card : ℝ) * (Real.log x)^e ≤ C * x := by
  refine ⟨3000000*4^(e+18)*boundC e, by unfold boundC; positivity, ?_⟩
  filter_upwards [fixed_block e, eventually_grid e, eventually_ge_atTop (100:ℕ)] with x hm hg hx100
  obtain ⟨hH,hHx,_,hnum,_,_,_⟩ := grid_bounds e x hg
  have hI : (Ico x (2*x)).filter (fun n => n∈holes x) = holes x := by
    ext n
    constructor
    · intro hn; exact (mem_filter.mp hn).2
    · intro hn; have hg := (mem_filter.mp (mem_filter.mp hn).1).2
      exact mem_filter.mpr ⟨mem_Ico.mpr ⟨by omega, by omega⟩,hn⟩
  have short (M : ℕ) : (Ico (M-block e x) M).filter (fun n => n∈holes x) = (Ico (M-block e x) M) ∩ holes x := by
    ext n; simp
  have bound := GoldbachEstermann.dyadic_short_block_count (fun n => n∈holes x) hH hHx
    (boundC e*x/(Real.log x)^(2*e+18)) (fun M _ _ => by rw [short]; exact hm M)
  rw [hI] at bound
  have hlog : 0 < Real.log x := Real.log_pos (by exact_mod_cast (show 1<x by omega))
  have hfactor : ((x/block e x+1:ℕ):ℝ) ≤ (3000000*4^(e+18))*(Real.log x)^(e+18) := by
    have hnum' : ((x/block e x+1:ℕ):ℝ) ≤ 3000000*(root e x:ℝ) := by exact_mod_cast hnum
    have hc := Polylog.cutoff_le_log (e+18) (by omega : 2≤x)
    rw [mul_pow] at hc
    dsimp [root] at hnum'
    linarith only [hc, hnum']
  have hsplit : (Real.log x)^(2*e+18) = (Real.log x)^e * (Real.log x)^(e+18) := by
    rw [← pow_add]; congr 1; ring
  have key : ((holes x).card:ℝ) * (Real.log x)^e * (Real.log x)^(e+18) ≤
      (3000000*4^(e+18)*boundC e) * x * (Real.log x)^(e+18) := by
    calc ((holes x).card:ℝ) * (Real.log x)^e * (Real.log x)^(e+18)
        = ((holes x).card:ℝ) * (Real.log x)^(2*e+18) := by rw [hsplit]; ring
      _ ≤ (((x/block e x+1:ℕ):ℝ) * (boundC e*x/(Real.log x)^(2*e+18))) * (Real.log x)^(2*e+18) :=
          mul_le_mul_of_nonneg_right bound (pow_nonneg hlog.le _)
      _ = ((x/block e x+1:ℕ):ℝ) * (boundC e*x) := by
          have hne : (Real.log x)^(2*e+18) ≠ 0 := pow_ne_zero _ (ne_of_gt hlog)
          field_simp <;> ring
      _ ≤ ((3000000*4^(e+18))*(Real.log x)^(e+18)) * (boundC e * x) := by
          exact mul_le_mul_of_nonneg_right hfactor (by unfold boundC; positivity)
      _ = (3000000*4^(e+18)*boundC e) * x * (Real.log x)^(e+18) := by ring
  have hpos : (0:ℝ) < (Real.log x)^(e+18) := pow_pos hlog _
  exact le_of_mul_le_mul_right key hpos

end
end BulkCircle
end

section
open Finset Filter MeasureTheory
open scoped Topology BigOperators
namespace Cover
open BulkCircle

open BulkCircle

def myreps (n : ℕ) := (Finset.range (n + 1)).filter (fun p => Nat.Prime p ∧ Nat.Prime (n - p))
def exc (X : ℕ) := (Finset.range (X + 1)).filter (fun n => 4 ≤ n ∧ Even n ∧ (myreps n).card = 0)

theorem exc_mem_holes {x n : ℕ} (hn : n ∈ target x) (hrep : (myreps n).card = 0) :
    n ∈ holes x := by
  refine mem_filter.mpr ⟨hn, ?_⟩
  unfold rep
  apply sum_eq_zero
  intro p hp
  obtain ⟨hpb, hnpb, hpn⟩ := mem_filter.mp hp
  have hpempty : myreps n = ∅ := card_eq_zero.mp hrep
  by_cases h1 : Nat.Prime p
  · by_cases h2 : Nat.Prime (n - p)
    · exfalso
      have hmem : p ∈ myreps n := mem_filter.mpr ⟨mem_range.mpr (by omega), h1, h2⟩
      rw [hpempty] at hmem
      simp at hmem
    · simp [GoldbachMajorArc.primeWeight, h2]
  · simp [GoldbachMajorArc.primeWeight, h1]

def xseq (X : ℕ) : ℕ → ℕ
  | 0 => X
  | j+1 => 13 * xseq X j / 15 + 1

theorem xseq_zero (X : ℕ) : xseq X 0 = X := rfl
theorem xseq_succ (X j : ℕ) : xseq X (j+1) = 13 * xseq X j / 15 + 1 := rfl

theorem xseq_step (X j : ℕ) : 13 * xseq X j + 1 ≤ 15 * xseq X (j+1) := by
  rw [xseq_succ]
  have h := Nat.div_add_mod (13 * xseq X j) 15
  have h2 := Nat.mod_lt (13 * xseq X j) (by norm_num : (0:ℕ) < 15)
  omega

theorem xseq_pos (X : ℕ) (hX : 1 ≤ X) : ∀ j, 1 ≤ xseq X j := by
  intro j
  induction j with
  | zero => exact hX
  | succ j ih => rw [xseq_succ]; omega

theorem xseq_ratio (X j : ℕ) (h : 15 ≤ xseq X j) :
    ((xseq X (j+1) : ℕ) : ℝ) ≤ (14/15) * ((xseq X j : ℕ) : ℝ) := by
  have h1 : 15 * xseq X (j+1) ≤ 14 * xseq X j := by
    rw [xseq_succ]
    have := Nat.div_mul_le_self (13 * xseq X j) 15
    omega
  have h2 : (15:ℝ) * ((xseq X (j+1):ℕ):ℝ) ≤ 14 * ((xseq X j:ℕ):ℝ) := by exact_mod_cast h1
  linarith

theorem xseq_shift (X : ℕ) : ∀ j, xseq X (j+1) = xseq (xseq X 1) j := by
  intro j
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [xseq_succ X (j+1), ih, xseq_succ (xseq X 1) j]

theorem xseq_exists : ∀ X : ℕ, ∃ j, xseq X j < 200 := by
  have h : ∀ X : ℕ, (∀ m, m < X → ∃ j, xseq m j < 200) → ∃ j, xseq X j < 200 := by
    intro X ih
    by_cases hX : X < 200
    · exact ⟨0, hX⟩
    · have h1 : xseq X 1 < X := by
        rw [xseq_succ, xseq_zero]
        have := Nat.div_mul_le_self (13*X) 15
        omega
      obtain ⟨j, hj⟩ := ih (xseq X 1) h1
      exact ⟨j+1, by rw [xseq_shift]; exact hj⟩
  exact fun X => Nat.strong_induction_on X h

theorem xseq_exists' (X T : ℕ) (hT : 200 ≤ T) : ∃ j, xseq X j < T := by
  obtain ⟨j, hj⟩ := xseq_exists X
  exact ⟨j, by omega⟩

def KT (X T : ℕ) (hT : 200 ≤ T) : ℕ := Nat.find (xseq_exists' X T hT)
theorem KT_spec (X T : ℕ) (hT : 200 ≤ T) : xseq X (KT X T hT) < T := Nat.find_spec (xseq_exists' X T hT)
theorem KT_min (X T : ℕ) (hT : 200 ≤ T) {j : ℕ} (hj : j < KT X T hT) : T ≤ xseq X j :=
  le_of_not_gt (Nat.find_min (xseq_exists' X T hT) hj)

theorem geo_sum_range {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (f : ℕ → ℝ) (hf : ∀ j, 0 ≤ f j) :
    ∀ (a L : ℕ), (∀ j, a ≤ j → j < a + L → f (j+1) ≤ r * f j) →
      (∑ j ∈ range L, f (a+j)) * (1 - r) ≤ f a := by
  intro a L
  induction L with
  | zero => intro _; simpa using hf a
  | succ L ih =>
    intro hstep
    have hshift : ∑ j ∈ range L, f (a+j+1) ≤ r * ∑ j ∈ range L, f (a+j) := by
      calc ∑ j ∈ range L, f (a+j+1) ≤ ∑ j ∈ range L, r * f (a+j) := by
            apply sum_le_sum; intro j hj
            have hjL : j < L := mem_range.mp hj
            exact hstep (a+j) (by omega) (by omega)
        _ = r * ∑ j ∈ range L, f (a+j) := by rw [Finset.mul_sum]
    have hIH : (∑ j ∈ range L, f (a+j)) * (1-r) ≤ f a := by
      apply ih; intro j hj1 hj2; exact hstep j hj1 (by omega)
    have hsplit : ∑ j ∈ range (L+1), f (a+j) = (∑ j ∈ range L, f (a+j+1)) + f a := by
      have h := sum_range_succ' (fun j => f (a+j)) L
      have h1 : ∑ j ∈ range L, f (a+(j+1)) = ∑ j ∈ range L, f (a+j+1) := by
        apply sum_congr rfl; intro j _
        rw [show a + (j+1) = a+j+1 by omega]
      have h2 : f (a+0) = f a := by rw [show a+0 = a by omega]
      rw [h, h1, h2]
    rw [hsplit]
    have hpos : (0:ℝ) ≤ 1 - r := by linarith
    have hmul : ((∑ j ∈ range L, f (a+j+1)) + f a) * (1-r) ≤
        (r * ∑ j ∈ range L, f (a+j) + f a) * (1-r) :=
      mul_le_mul_of_nonneg_right (add_le_add hshift (le_refl (f a))) hpos
    refine hmul.trans ?_
    have heq : (r * ∑ j ∈ range L, f (a+j) + f a) * (1-r) =
        r * ((∑ j ∈ range L, f (a+j))*(1-r)) + f a*(1-r) := by ring
    rw [heq]
    have h5 : r * ((∑ j ∈ range L, f (a+j))*(1-r)) ≤ r * f a :=
      mul_le_mul_of_nonneg_left hIH hr
    linarith

theorem cover_aux (X n : ℕ) (hhi : 4 * n ≤ 5 * X) :
    ∀ K : ℕ, 13 * xseq X K ≤ 12 * n → ∃ j ≤ K, 13 * xseq X j ≤ 12 * n ∧ 4 * n ≤ 5 * xseq X j := by
  intro K
  induction K with
  | zero =>
    intro hK
    exact ⟨0, le_rfl, hK, by rw [xseq_zero]; exact hhi⟩
  | succ K ih =>
    intro hK
    by_cases h : 4 * n ≤ 5 * xseq X (K+1)
    · exact ⟨K+1, le_rfl, hK, h⟩
    · have h5 : 5 * xseq X (K+1) ≤ 4*n - 1 := by omega
      have h13 : 13 * xseq X K ≤ 12 * n := by
        have hs := xseq_step X K
        omega
      obtain ⟨j, hj, h1, h2⟩ := ih h13
      exact ⟨j, le_trans hj (Nat.le_succ K), h1, h2⟩

theorem cover (X T n : ℕ) (hT : 200 ≤ T) (heven : Even n) (hhi : 4 * n ≤ 5 * X)
    (hlo : 13 * xseq X (KT X T hT) ≤ 12 * n) :
    ∃ j ≤ KT X T hT, n ∈ target (xseq X j) := by
  obtain ⟨j, hj, h1, h2⟩ := cover_aux X n hhi (KT X T hT) hlo
  refine ⟨j, hj, ?_⟩
  show n ∈ (range (2*xseq X j+1)).filter (fun m => Even m ∧ 13*xseq X j ≤ 12*m ∧ 4*m ≤ 5*xseq X j)
  exact mem_filter.mpr ⟨mem_range.mpr (by omega), heven, h1, h2⟩


theorem exc_subset (X T : ℕ) (hT : 200 ≤ T) :
    exc X ⊆ (exc X ∩ range (2*T+1)) ∪ (range (KT X T hT + 1)).biUnion (fun j => holes (xseq X j)) := by
  intro n hn
  have hn' := mem_filter.mp hn
  have hnX : n < X + 1 := mem_range.mp hn'.1
  have hev : Even n := hn'.2.2.1
  have hrep : (myreps n).card = 0 := hn'.2.2.2
  by_cases h : 13 * xseq X (KT X T hT) ≤ 12 * n
  · refine mem_union.mpr (Or.inr ?_)
    obtain ⟨j, hj, hmem⟩ := cover X T n hT hev (by omega) h
    exact mem_biUnion.mpr ⟨j, mem_range.mpr (by omega), exc_mem_holes hmem hrep⟩
  · refine mem_union.mpr (Or.inl ?_)
    refine mem_inter.mpr ⟨hn, mem_range.mpr ?_⟩
    have hK := KT_spec X T hT
    omega

theorem exc_card_le (X T : ℕ) (hT : 200 ≤ T) :
    ((exc X).card:ℝ) ≤ ((2*T+1:ℕ):ℝ) + ∑ j ∈ range (KT X T hT + 1), ((holes (xseq X j)).card:ℝ) := by
  have hsub := exc_subset X T hT
  have h1 : (exc X).card ≤ (exc X ∩ range (2*T+1)).card +
      ((range (KT X T hT+1)).biUnion (fun j => holes (xseq X j))).card :=
    (card_le_card hsub).trans (card_union_le _ _)
  have h2 : (exc X ∩ range (2*T+1)).card ≤ 2*T+1 :=
    (card_le_card (fun a ha => (mem_inter.mp ha).2)).trans (by rw [card_range])
  have h3 : ((range (KT X T hT+1)).biUnion (fun j => holes (xseq X j))).card ≤
      ∑ j ∈ range (KT X T hT+1), (holes (xseq X j)).card := card_biUnion_le
  have h4 := h1.trans (add_le_add h2 h3)
  exact_mod_cast h4

noncomputable def thr (X : ℕ) : ℕ := ⌊((X:ℕ):ℝ)^((1:ℝ)/4)⌋₊

set_option maxHeartbeats 1600000 in
theorem exc_polylog (A : ℝ) (hA : 0 < A) : ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
    ((exc X).card:ℝ) ≤ ((X:ℕ):ℝ) * (Real.log ((X:ℕ):ℝ))^(-A) := by
  set e := ⌈A⌉₊ + 2 with he
  obtain ⟨C, hC, hband⟩ := BulkCircle.band_bound e
  obtain ⟨N, hN⟩ := eventually_atTop.mp hband
  have heA : A ≤ (e:ℝ) := by
    have h1 := Nat.le_ceil A
    have h2 : ((⌈A⌉₊:ℕ):ℝ) ≤ (e:ℝ) := by rw [he]; exact_mod_cast Nat.le_add_right _ 2
    linarith
  have hAe : A - (e:ℝ) ≤ -2 := by
    have h1 := Nat.le_ceil A
    have h2 : (e:ℝ) = ((⌈A⌉₊:ℕ):ℝ) + 2 := by rw [he]; push_cast; ring
    linarith
  have htend4 : Tendsto (fun X : ℕ => ((X:ℕ):ℝ)^((1:ℝ)/4)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ) < (1:ℝ)/4)).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hF1 : ∀ᶠ X : ℕ in atTop, (N:ℝ)+1 ≤ ((X:ℕ):ℝ)^((1:ℝ)/4) := htend4.eventually_ge_atTop _
  have hF2 : ∀ᶠ X : ℕ in atTop, (201:ℝ) ≤ ((X:ℕ):ℝ)^((1:ℝ)/4) := htend4.eventually_ge_atTop _
  have hF3 : ∀ᶠ X : ℕ in atTop, max (20*Real.log 2 + 1) 20 ≤ Real.log ((X:ℕ):ℝ) :=
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop _
  have hF4 : ∀ᶠ X : ℕ in atTop, (Real.log ((X:ℕ):ℝ))^A ≤ ((X:ℕ):ℝ)^((1:ℝ)/4) := by
    have h := (isLittleO_log_rpow_rpow_atTop A (by norm_num : (0:ℝ) < (1:ℝ)/4)).tendsto_div_nhds_zero
    have h2 := h.comp (tendsto_natCast_atTop_atTop (R := ℝ))
    have h3 := h2.eventually_lt_const zero_lt_one
    simp only [Function.comp_def] at h3
    filter_upwards [h3, eventually_ge_atTop (2:ℕ)] with X hX hX2
    have hxpos : (0:ℝ) < ((X:ℕ):ℝ) := by exact_mod_cast (show 0<X by omega)
    have hq : (0:ℝ) < ((X:ℕ):ℝ)^((1:ℝ)/4) := Real.rpow_pos_of_pos hxpos _
    rw [div_lt_one hq] at hX
    exact le_of_lt hX
  have hF5 : ∀ᶠ X : ℕ in atTop, (Real.log ((X:ℕ):ℝ))^((A:ℝ)-(e:ℝ)) ≤ 1/(30*C*5^e) := by
    have hb : (0:ℝ) < 1/(30*C*5^e) := by positivity
    have h : Tendsto (fun X : ℕ => (Real.log ((X:ℕ):ℝ))^((A:ℝ)-(e:ℝ))) atTop (𝓝 0) := by
      have h1 : Tendsto (fun x : ℝ => (Real.log x)^((A:ℝ)-(e:ℝ))) atTop (𝓝 0) := by
        have h4 : (A:ℝ)-(e:ℝ) = -((e:ℝ)-A) := by ring
        rw [h4]
        exact (tendsto_rpow_neg_atTop (by linarith : (0:ℝ) < (e:ℝ)-A)).comp Real.tendsto_log_atTop
      exact h1.comp (tendsto_natCast_atTop_atTop (R := ℝ))
    filter_upwards [h.eventually (Iio_mem_nhds hb)] with X hX
    exact le_of_lt hX
  have hF6 : ∀ᶠ X : ℕ in atTop, 12*5^e ≤ ((X:ℕ):ℝ)^((1:ℝ)/2) := by
    have h := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop ((12*5^e)^2)
    filter_upwards [h] with X hX
    have h5e : (0:ℝ) ≤ 12*5^e := by positivity
    have h1 : Real.sqrt ((12*5^e)^2) ≤ Real.sqrt ((X:ℕ):ℝ) := Real.sqrt_le_sqrt hX
    rw [Real.sqrt_sq h5e, Real.sqrt_eq_rpow] at h1
    exact h1
  have hmain : ∀ᶠ X : ℕ in atTop, ((exc X).card:ℝ) ≤ ((X:ℕ):ℝ) * (Real.log ((X:ℕ):ℝ))^(-A) := by
    filter_upwards [hF1, hF2, hF3, hF4, hF5, hF6, eventually_ge_atTop (1:ℕ)] with X hN1 h201 hlogX hlA h5 hsq hX1
    have hxpos : (0:ℝ) < ((X:ℕ):ℝ) := by exact_mod_cast (show 0 < X by omega)
    have hx1 : (1:ℝ) ≤ ((X:ℕ):ℝ) := by exact_mod_cast hX1
    have hq : (0:ℝ) < ((X:ℕ):ℝ)^((1:ℝ)/4) := Real.rpow_pos_of_pos hxpos _
    have hthrlt : ((X:ℕ):ℝ)^((1:ℝ)/4) < ((thr X:ℕ):ℝ) + 1 := Nat.lt_floor_add_one _
    have hthrge : (200:ℝ) ≤ ((thr X:ℕ):ℝ) := by linarith
    have hT200 : 200 ≤ thr X := by
      have h : (200:ℕ) ≤ thr X := by exact_mod_cast hthrge
      exact h
    have hNle : N ≤ thr X := by
      have h : (N:ℕ) < thr X := by
        have : (N:ℝ) < ((thr X:ℕ):ℝ) := by linarith
        exact_mod_cast this
      omega
    have hthr1 : 1 ≤ thr X := by omega
    have hthrR1 : (1:ℝ) ≤ ((thr X:ℕ):ℝ) := by exact_mod_cast hthr1
    have hthrR0 : (0:ℝ) < ((thr X:ℕ):ℝ) := by linarith
    have hthrle : ((thr X:ℕ):ℝ) ≤ ((X:ℕ):ℝ)^((1:ℝ)/4) := Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    have hthrX : thr X ≤ X := by
      have h2 : ((X:ℕ):ℝ)^((1:ℝ)/4) ≤ ((X:ℕ):ℝ) := by
        have := Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num : (1:ℝ)/4 ≤ 1)
        simpa using this
      exact_mod_cast (hthrle.trans h2)
    have hl20 : (20:ℝ) ≤ Real.log ((X:ℕ):ℝ) := le_trans (le_max_right _ _) hlogX
    have hlbig : 20*Real.log 2 + 1 ≤ Real.log ((X:ℕ):ℝ) := le_trans (le_max_left _ _) hlogX
    have hlpos : (0:ℝ) < Real.log ((X:ℕ):ℝ) := by linarith
    have hl1 : (1:ℝ) ≤ Real.log ((X:ℕ):ℝ) := by linarith
    have hlogT : (1/5) * Real.log ((X:ℕ):ℝ) ≤ Real.log ((thr X:ℕ):ℝ) := by
      have hhalf : ((X:ℕ):ℝ)^((1:ℝ)/4)/2 < ((thr X:ℕ):ℝ) := by linarith
      have h1 : Real.log (((X:ℕ):ℝ)^((1:ℝ)/4)/2) ≤ Real.log ((thr X:ℕ):ℝ) :=
        Real.log_le_log (by positivity) (le_of_lt hhalf)
      have h2 : Real.log (((X:ℕ):ℝ)^((1:ℝ)/4)/2) = (1/4)*Real.log ((X:ℕ):ℝ) - Real.log 2 := by
        rw [Real.log_div (by positivity) (by norm_num), Real.log_rpow hxpos]
      rw [h2] at h1
      linarith
    have hlT1 : (1:ℝ) ≤ Real.log ((thr X:ℕ):ℝ) := by linarith
    have hlT0 : (0:ℝ) ≤ Real.log ((thr X:ℕ):ℝ) := le_trans (by norm_num) hlT1
    have hLl : (Real.log ((thr X:ℕ):ℝ))^e ≤ (Real.log ((X:ℕ):ℝ))^e := by
      apply pow_le_pow_left₀ hlT0 ?_ e
      exact Real.log_le_log hthrR0 (by exact_mod_cast hthrX)
    have hLe : (Real.log ((X:ℕ):ℝ))^e ≤ 5^e * (Real.log ((thr X:ℕ):ℝ))^e := by
      have h1 : Real.log ((X:ℕ):ℝ)/5 ≤ Real.log ((thr X:ℕ):ℝ) := by linarith
      have h2 : (Real.log ((X:ℕ):ℝ)/5)^e ≤ (Real.log ((thr X:ℕ):ℝ))^e :=
        pow_le_pow_left₀ (by positivity) h1 e
      have h3 : (Real.log ((X:ℕ):ℝ)/5)^e = (Real.log ((X:ℕ):ℝ))^e/5^e := by rw [div_pow]
      have h4 : (0:ℝ) < 5^e := by positivity
      rw [h3, div_le_iff₀ h4] at h2
      calc (Real.log ((X:ℕ):ℝ))^e ≤ (Real.log ((thr X:ℕ):ℝ))^e * 5^e := h2
        _ = 5^e * (Real.log ((thr X:ℕ):ℝ))^e := by ring
    have hgeo : ∑ j ∈ range (KT X (thr X) hT200), ((xseq X j:ℕ):ℝ) ≤ 15 * ((X:ℕ):ℝ) := by
      have h := geo_sum_range (r := (14:ℝ)/15) (by norm_num) (by norm_num)
        (fun j => ((xseq X j:ℕ):ℝ)) (fun j => Nat.cast_nonneg _) 0 (KT X (thr X) hT200)
        (fun j hj1 hj2 => by
          have hjK : j < KT X (thr X) hT200 := by omega
          exact xseq_ratio X j (by have := KT_min X (thr X) hT200 hjK; omega))
      have h2 : (1:ℝ) - 14/15 = 1/15 := by norm_num
      rw [h2] at h
      simp only [Nat.zero_add, xseq_zero] at h
      linarith
    have hsum1 : (∑ j ∈ range (KT X (thr X) hT200), ((holes (xseq X j)).card:ℝ)) *
        (Real.log ((thr X:ℕ):ℝ))^e ≤ 15*C*((X:ℕ):ℝ) := by
      have h1 : ∀ j ∈ range (KT X (thr X) hT200),
          ((holes (xseq X j)).card:ℝ) * (Real.log ((thr X:ℕ):ℝ))^e ≤ C * ((xseq X j:ℕ):ℝ) := by
        intro j hj
        have hjK : j < KT X (thr X) hT200 := mem_range.mp hj
        have hxj : thr X ≤ xseq X j := KT_min X (thr X) hT200 hjK
        have hNle' : N ≤ xseq X j := le_trans hNle hxj
        have hlogmono : Real.log ((thr X:ℕ):ℝ) ≤ Real.log ((xseq X j:ℕ):ℝ) :=
          Real.log_le_log hthrR0 (by exact_mod_cast hxj)
        have hband1 := hN (xseq X j) hNle'
        calc ((holes (xseq X j)).card:ℝ) * (Real.log ((thr X:ℕ):ℝ))^e
            ≤ ((holes (xseq X j)).card:ℝ) * (Real.log ((xseq X j:ℕ):ℝ))^e := by
              exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlT0 hlogmono e) (Nat.cast_nonneg _)
          _ ≤ C * ((xseq X j:ℕ):ℝ) := hband1
      calc (∑ j ∈ range (KT X (thr X) hT200), ((holes (xseq X j)).card:ℝ)) * (Real.log ((thr X:ℕ):ℝ))^e
          = ∑ j ∈ range (KT X (thr X) hT200), (((holes (xseq X j)).card:ℝ) * (Real.log ((thr X:ℕ):ℝ))^e) := by
            rw [Finset.sum_mul]
        _ ≤ ∑ j ∈ range (KT X (thr X) hT200), (C * ((xseq X j:ℕ):ℝ)) := Finset.sum_le_sum h1
        _ = C * ∑ j ∈ range (KT X (thr X) hT200), ((xseq X j:ℕ):ℝ) := by rw [Finset.mul_sum]
        _ ≤ C * (15*((X:ℕ):ℝ)) := mul_le_mul_of_nonneg_left hgeo hC.le
        _ = 15*C*((X:ℕ):ℝ) := by ring
    have hlast : ((holes (xseq X (KT X (thr X) hT200))).card:ℝ) ≤ 3 * ((thr X:ℕ):ℝ) := by
      have h1 := holes_card_le (xseq X (KT X (thr X) hT200))
      have h2 := KT_spec X (thr X) hT200
      have hc1 : ((holes (xseq X (KT X (thr X) hT200))).card:ℝ) ≤
          2*((xseq X (KT X (thr X) hT200):ℕ):ℝ)+1 := by exact_mod_cast h1
      have hc2 : ((xseq X (KT X (thr X) hT200):ℕ):ℝ) + 1 ≤ ((thr X:ℕ):ℝ) := by
        exact_mod_cast (show xseq X (KT X (thr X) hT200) + 1 ≤ thr X by omega)
      linarith
    have hEc : ((exc X).card:ℝ) ≤ ((2*(thr X)+1:ℕ):ℝ) +
        ∑ j ∈ range (KT X (thr X) hT200 + 1), ((holes (xseq X j)).card:ℝ) := exc_card_le X (thr X) hT200
    have hsplit : ∑ j ∈ range (KT X (thr X) hT200 + 1), ((holes (xseq X j)).card:ℝ) =
        (∑ j ∈ range (KT X (thr X) hT200), ((holes (xseq X j)).card:ℝ)) +
        ((holes (xseq X (KT X (thr X) hT200))).card:ℝ) := by rw [sum_range_succ]
    have hEc2 : ((exc X).card:ℝ) ≤ ((2*(thr X)+1:ℕ):ℝ) +
        (∑ j ∈ range (KT X (thr X) hT200), ((holes (xseq X j)).card:ℝ)) +
        ((holes (xseq X (KT X (thr X) hT200))).card:ℝ) := by
      rw [hsplit] at hEc; linarith
    have hposL : (0:ℝ) ≤ (Real.log ((thr X:ℕ):ℝ))^e := pow_nonneg hlT0 _
    have hE : ((exc X).card:ℝ) * (Real.log ((thr X:ℕ):ℝ))^e ≤
        (5*((thr X:ℕ):ℝ)+1) * (Real.log ((thr X:ℕ):ℝ))^e + 15*C*((X:ℕ):ℝ) := by
      calc ((exc X).card:ℝ) * (Real.log ((thr X:ℕ):ℝ))^e
          ≤ (((2*(thr X)+1:ℕ):ℝ) + (∑ j ∈ range (KT X (thr X) hT200), ((holes (xseq X j)).card:ℝ)) +
              ((holes (xseq X (KT X (thr X) hT200))).card:ℝ)) * (Real.log ((thr X:ℕ):ℝ))^e :=
            mul_le_mul_of_nonneg_right hEc2 hposL
        _ = ((2*(thr X)+1:ℕ):ℝ)*(Real.log ((thr X:ℕ):ℝ))^e +
              (∑ j ∈ range (KT X (thr X) hT200), ((holes (xseq X j)).card:ℝ))*(Real.log ((thr X:ℕ):ℝ))^e +
              ((holes (xseq X (KT X (thr X) hT200))).card:ℝ)*(Real.log ((thr X:ℕ):ℝ))^e := by ring
        _ ≤ ((2*(thr X)+1:ℕ):ℝ)*(Real.log ((thr X:ℕ):ℝ))^e + 15*C*((X:ℕ):ℝ) +
              3*((thr X:ℕ):ℝ)*(Real.log ((thr X:ℕ):ℝ))^e := by
            have hh := add_le_add hsum1 (mul_le_mul_of_nonneg_right hlast hposL)
            linarith
        _ = (5*((thr X:ℕ):ℝ)+1) * (Real.log ((thr X:ℕ):ℝ))^e + 15*C*((X:ℕ):ℝ) := by
            have hcast : ((2*(thr X)+1:ℕ):ℝ) = 2*((thr X:ℕ):ℝ) + 1 := by push_cast; ring
            rw [hcast]; ring
    have hLe' : (Real.log ((X:ℕ):ℝ))^(e:ℝ) ≤ 5^e * (Real.log ((thr X:ℕ):ℝ))^e := by
      rw [Real.rpow_natCast]; exact hLe
    have hrpow : (Real.log ((X:ℕ):ℝ))^((A:ℝ)-(e:ℝ)) * (Real.log ((X:ℕ):ℝ))^(e:ℝ) =
        (Real.log ((X:ℕ):ℝ))^A := by
      rw [← Real.rpow_add hlpos]
      congr 1
      ring
    have hrn : (0:ℝ) ≤ (Real.log ((X:ℕ):ℝ))^((A:ℝ)-(e:ℝ)) := Real.rpow_nonneg hlpos.le _
    have hre : (0:ℝ) ≤ (Real.log ((X:ℕ):ℝ))^(e:ℝ) := Real.rpow_nonneg hlpos.le _
    have h5e0 : (0:ℝ) ≤ 5^e := by positivity
    have step1 : ((exc X).card:ℝ) * (Real.log ((X:ℕ):ℝ))^A ≤
        5^e * (Real.log ((X:ℕ):ℝ))^((A:ℝ)-(e:ℝ)) * (((exc X).card:ℝ) * (Real.log ((thr X:ℕ):ℝ))^e) := by
      calc ((exc X).card:ℝ) * (Real.log ((X:ℕ):ℝ))^A
          = ((exc X).card:ℝ) * ((Real.log ((X:ℕ):ℝ))^((A:ℝ)-(e:ℝ)) * (Real.log ((X:ℕ):ℝ))^(e:ℝ)) := by
            rw [hrpow]
        _ ≤ ((exc X).card:ℝ) * ((Real.log ((X:ℕ):ℝ))^((A:ℝ)-(e:ℝ)) *
              (5^e * (Real.log ((thr X:ℕ):ℝ))^e)) := by
            apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
            exact mul_le_mul_of_nonneg_left hLe' hrn
        _ = 5^e * (Real.log ((X:ℕ):ℝ))^((A:ℝ)-(e:ℝ)) * (((exc X).card:ℝ) * (Real.log ((thr X:ℕ):ℝ))^e) := by ring
    have hcoef : (0:ℝ) ≤ 5^e * (Real.log ((X:ℕ):ℝ))^((A:ℝ)-(e:ℝ)) := mul_nonneg h5e0 hrn
    have step2 : 5^e * (Real.log ((X:ℕ):ℝ))^((A:ℝ)-(e:ℝ)) * (((exc X).card:ℝ) * (Real.log ((thr X:ℕ):ℝ))^e) ≤
        5^e * (Real.log ((X:ℕ):ℝ))^((A:ℝ)-(e:ℝ)) *
          ((5*((thr X:ℕ):ℝ)+1) * (Real.log ((thr X:ℕ):ℝ))^e + 15*C*((X:ℕ):ℝ)) :=
      mul_le_mul_of_nonneg_left hE hcoef
    have t2 : 5^e * (Real.log ((X:ℕ):ℝ))^((A:ℝ)-(e:ℝ)) * (15*C*((X:ℕ):ℝ)) ≤ ((X:ℕ):ℝ)/2 := by
      have h2 : 5^e * (Real.log ((X:ℕ):ℝ))^((A:ℝ)-(e:ℝ)) * (15*C*((X:ℕ):ℝ)) ≤
          5^e * (1/(30*C*5^e)) * (15*C*((X:ℕ):ℝ)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left h5 h5e0
      refine h2.trans (le_of_eq ?_)
      have hC0 : C ≠ 0 := ne_of_gt hC
      have h5ne : (5:ℝ)^e ≠ 0 := by positivity
      field_simp <;> ring
    have t1 : 5^e * (Real.log ((X:ℕ):ℝ))^((A:ℝ)-(e:ℝ)) *
        ((5*((thr X:ℕ):ℝ)+1) * (Real.log ((thr X:ℕ):ℝ))^e) ≤ ((X:ℕ):ℝ)/2 := by
      have h1 : (Real.log ((X:ℕ):ℝ))^((A:ℝ)-(e:ℝ)) * (Real.log ((thr X:ℕ):ℝ))^e ≤
          (Real.log ((X:ℕ):ℝ))^A := by
        calc (Real.log ((X:ℕ):ℝ))^((A:ℝ)-(e:ℝ)) * (Real.log ((thr X:ℕ):ℝ))^e
            ≤ (Real.log ((X:ℕ):ℝ))^((A:ℝ)-(e:ℝ)) * (Real.log ((X:ℕ):ℝ))^e := by
              exact mul_le_mul_of_nonneg_left hLl hrn
          _ ≤ (Real.log ((X:ℕ):ℝ))^((A:ℝ)-(e:ℝ)) * (Real.log ((X:ℕ):ℝ))^(e:ℝ) := by
              exact mul_le_mul_of_nonneg_left (by rw [Real.rpow_natCast]) hrn
          _ = (Real.log ((X:ℕ):ℝ))^A := hrpow
      have h2 : 5^e * (Real.log ((X:ℕ):ℝ))^((A:ℝ)-(e:ℝ)) *
          ((5*((thr X:ℕ):ℝ)+1) * (Real.log ((thr X:ℕ):ℝ))^e) =
          5^e * (5*((thr X:ℕ):ℝ)+1) * ((Real.log ((X:ℕ):ℝ))^((A:ℝ)-(e:ℝ)) * (Real.log ((thr X:ℕ):ℝ))^e) := by ring
      have hx4 : (1:ℝ) ≤ ((X:ℕ):ℝ)^((1:ℝ)/4) := by
        have := Real.rpow_le_rpow (by norm_num : (0:ℝ) ≤ 1) hx1 (by norm_num : (0:ℝ) ≤ (1:ℝ)/4)
        simpa using this
      have ha : 5*((thr X:ℕ):ℝ)+1 ≤ 6*((X:ℕ):ℝ)^((1:ℝ)/4) := by linarith
      have hpos1 : (0:ℝ) ≤ 5^e * (6*((X:ℕ):ℝ)^((1:ℝ)/4)) := by positivity
      have hq2 : (0:ℝ) ≤ ((X:ℕ):ℝ)^((1:ℝ)/4) := le_of_lt hq
      rw [h2]
      calc 5^e * (5*((thr X:ℕ):ℝ)+1) * ((Real.log ((X:ℕ):ℝ))^((A:ℝ)-(e:ℝ)) * (Real.log ((thr X:ℕ):ℝ))^e)
          ≤ 5^e * (5*((thr X:ℕ):ℝ)+1) * (Real.log ((X:ℕ):ℝ))^A := by
            exact mul_le_mul_of_nonneg_left h1 (mul_nonneg h5e0 (by linarith))
        _ ≤ 5^e * (6*((X:ℕ):ℝ)^((1:ℝ)/4)) * (Real.log ((X:ℕ):ℝ))^A :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ha h5e0) (Real.rpow_nonneg hlpos.le _)
        _ ≤ 5^e * (6*((X:ℕ):ℝ)^((1:ℝ)/4)) * ((X:ℕ):ℝ)^((1:ℝ)/4) :=
            mul_le_mul_of_nonneg_left hlA hpos1
        _ = 6*5^e*((X:ℕ):ℝ)^((1:ℝ)/2) := by
            have hh : ((X:ℕ):ℝ)^((1:ℝ)/4)*((X:ℕ):ℝ)^((1:ℝ)/4) = ((X:ℕ):ℝ)^((1:ℝ)/2) := by
              rw [← Real.rpow_add hxpos, show (1:ℝ)/4 + 1/4 = 1/2 by norm_num]
            rw [show 5^e * (6*((X:ℕ):ℝ)^((1:ℝ)/4)) * ((X:ℕ):ℝ)^((1:ℝ)/4)
                  = 6*5^e*(((X:ℕ):ℝ)^((1:ℝ)/4)*((X:ℕ):ℝ)^((1:ℝ)/4)) by ring, hh]
        _ ≤ ((X:ℕ):ℝ)/2 := by
            have hhalf : ((X:ℕ):ℝ)^((1:ℝ)/2)*((X:ℕ):ℝ)^((1:ℝ)/2) = ((X:ℕ):ℝ) := by
              rw [← Real.rpow_add hxpos, show (1:ℝ)/2 + 1/2 = 1 by norm_num, Real.rpow_one]
            have hkey : 6*5^e*((X:ℕ):ℝ)^((1:ℝ)/2)*2 ≤ ((X:ℕ):ℝ) := by
              calc 6*5^e*((X:ℕ):ℝ)^((1:ℝ)/2)*2 = 12*5^e*((X:ℕ):ℝ)^((1:ℝ)/2) := by ring
                _ ≤ ((X:ℕ):ℝ)^((1:ℝ)/2)*((X:ℕ):ℝ)^((1:ℝ)/2) :=
                    mul_le_mul_of_nonneg_right hsq (Real.rpow_nonneg hxpos.le _)
                _ = ((X:ℕ):ℝ) := hhalf
            linarith
    have step3 : 5^e * (Real.log ((X:ℕ):ℝ))^((A:ℝ)-(e:ℝ)) *
        ((5*((thr X:ℕ):ℝ)+1) * (Real.log ((thr X:ℕ):ℝ))^e + 15*C*((X:ℕ):ℝ)) ≤ ((X:ℕ):ℝ) := by
      calc 5^e * (Real.log ((X:ℕ):ℝ))^((A:ℝ)-(e:ℝ)) *
          ((5*((thr X:ℕ):ℝ)+1) * (Real.log ((thr X:ℕ):ℝ))^e + 15*C*((X:ℕ):ℝ))
          = 5^e * (Real.log ((X:ℕ):ℝ))^((A:ℝ)-(e:ℝ)) *
              ((5*((thr X:ℕ):ℝ)+1) * (Real.log ((thr X:ℕ):ℝ))^e) +
            5^e * (Real.log ((X:ℕ):ℝ))^((A:ℝ)-(e:ℝ)) * (15*C*((X:ℕ):ℝ)) := by ring
        _ ≤ ((X:ℕ):ℝ)/2 + ((X:ℕ):ℝ)/2 := add_le_add t1 t2
        _ = ((X:ℕ):ℝ) := by ring
    have hfinal : ((exc X).card:ℝ) * (Real.log ((X:ℕ):ℝ))^A ≤ ((X:ℕ):ℝ) :=
      step1.trans (step2.trans step3)
    have hdiv : ((exc X).card:ℝ) ≤ ((X:ℕ):ℝ) / (Real.log ((X:ℕ):ℝ))^A :=
      (le_div_iff₀ (by positivity)).mpr hfinal
    have hrw : ((X:ℕ):ℝ) / (Real.log ((X:ℕ):ℝ))^A = ((X:ℕ):ℝ) * (Real.log ((X:ℕ):ℝ))^(-A) := by
      rw [div_eq_mul_inv, ← Real.rpow_neg hlpos.le]
    rw [hrw] at hdiv
    exact hdiv
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp hmain
  exact ⟨X₀, hX₀⟩

theorem density_zero : Tendsto (fun X : ℕ => ((exc X).card:ℝ)/((X:ℕ):ℝ)) atTop (nhds 0) := by
  obtain ⟨X₀, hX₀⟩ := exc_polylog 1 (by norm_num)
  have hlog : Tendsto (fun X : ℕ => (Real.log ((X:ℕ):ℝ))^(-(1:ℝ))) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (by norm_num)).comp
      (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ)))
  refine squeeze_zero' ?_ ?_ hlog
  · filter_upwards [eventually_ge_atTop X₀] with X hX
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · filter_upwards [eventually_ge_atTop (max X₀ 1)] with X hX
    have h1 : ((exc X).card:ℝ) ≤ ((X:ℕ):ℝ) * (Real.log ((X:ℕ):ℝ))^(-(1:ℝ)) :=
      hX₀ X (le_trans (le_max_left _ _) hX)
    have hxpos : (0:ℝ) < ((X:ℕ):ℝ) := by
      have : 1 ≤ X := le_trans (le_max_right _ _) hX
      exact_mod_cast (show 0 < X by omega)
    rw [div_le_iff₀ hxpos]
    calc ((exc X).card:ℝ) ≤ ((X:ℕ):ℝ) * (Real.log ((X:ℕ):ℝ))^(-(1:ℝ)) := h1
      _ = (Real.log ((X:ℕ):ℝ))^(-(1:ℝ)) * ((X:ℕ):ℝ) := by ring

end Cover
end
end MovingBulk.Frozen

namespace MovingBulk
noncomputable section
open Finset Filter MeasureTheory
open scoped Topology

def R (n : ℕ) : ℝ := Original.Glue.Raux n
def signed (n : ℕ) : ℝ :=
  (Original.Glue.Iaux n (Original.Glue.highaux n) (Original.Glue.highaux n)).re
def cutoff (n : ℕ) := Original.GoldbachMajorArc.cutoff n
def bigCut (n : ℕ) := Frozen.GoldbachMajorArc.Polylog.cutoff 20 n
def major (N D m : ℕ) : ℂ := Frozen.GoldbachBlockGeometry.majorContribution D N
  (fun t => (Frozen.GoldbachMajorArc.primeSum N t)^2 *
    Frozen.GoldbachMajorArc.phase (-(m:ℝ)*t))
def Z (N D m : ℕ) : ℂ :=
  ∑ q ∈ Icc 1 D, Frozen.GoldbachMajorArc.coefficient q m *
    (∫ t in -(Frozen.GoldbachBlockGeometry.width D N q)..Frozen.GoldbachBlockGeometry.width D N q,
      Frozen.GoldbachEstermannKernel.twisted N m t)

theorem coeff_re_arithmetic (q m : ℕ) (hq : 0<q) :
    (Frozen.GoldbachMajorArc.coefficient q m).re = Original.Glue.caux q m *
      ((ArithmeticFunction.moebius q:ℝ)/q.totient)^2 :=
  Original.Glue.coefficient_re q m hq

theorem Z_diagonal (n : ℕ) :
    Z n (cutoff n) n = Original.GoldbachMajorArc.modeledContribution n := by
  unfold Z Original.GoldbachMajorArc.modeledContribution
  refine sum_congr rfl fun q hq => congrArg ((Original.GoldbachMajorArc.coefficient q n) * ·) ?_
  change (∫ t in -(Original.GoldbachMajorArc.width n q)..Original.GoldbachMajorArc.width n q,
    (Original.GoldbachMajorArc.kernel n t)^2 * Original.GoldbachMajorArc.phase (-(n:ℝ)*t)) =
    ((Original.GoldbachMajorArc.kernelMass n (Original.GoldbachMajorArc.width n q):ℝ):ℂ)
  simp_rw [Original.GoldbachMajorArc.kernel_square_twist]
  rw [intervalIntegral.integral_ofReal] <;> rfl

/- Uniform removal of the distinction between the discrete kernel and the sinc
model in BulkCountEquivalence, using the quantitative error proved there. -/
private theorem diagonal_sinc_error (δ : ℝ) (hd : 0<δ) :
    ∀ᶠ n : ℕ in atTop, |(Z n (cutoff n) n).re - Original.Glue.Maux n| ≤ δ*n := by
  have hsmall := (Original.Glue.log_pow_div 6).eventually_lt_const
    (by positivity : (0:ℝ) < δ/((4*Real.pi+6)*4096))
  filter_upwards [hsmall, eventually_ge_atTop (2:ℕ)] with n hn h2
  have hn' : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hK : 0 < 4*Real.pi+6 := by positivity
  have hq := Original.GoldbachMajorArc.cutoff_le_log_sq h2
  have hQ3 : (Original.GoldbachMajorArc.cutoff n:ℝ)^3 ≤ 4096*(Real.log (n:ℝ))^6 := by
    have hp := pow_le_pow_left₀ (Nat.cast_nonneg (α:=ℝ) (Original.GoldbachMajorArc.cutoff n)) hq 3
    nlinarith only [hp]
  have hlog := (div_lt_iff₀ hn').mp hn
  rw [Z_diagonal]
  calc
    _ ≤ _ := Original.Glue.model_gap n (by omega)
    _ ≤ (4*Real.pi+6)*(4096*(Real.log (n:ℝ))^6) :=
      mul_le_mul_of_nonneg_left hQ3 hK.le
    _ ≤ (4*Real.pi+6)*(4096*(δ/((4*Real.pi+6)*4096)*n)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlog.le (by norm_num)) hK.le
    _ = _ := by field_simp [hK.ne'] <;> ring

theorem moving_error (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop, |signed n - (R n - (Z n (cutoff n) n).re)| ≤ ε*n := by
  have hsmall : 0 < ε/3 := by positivity
  filter_upwards [Original.Glue.gap_eventually _ hsmall, Original.Glue.smallR_eventually _ hsmall,
    diagonal_sinc_error _ hsmall] with n hg hr hz
  have hc := Original.Glue.Rhighaux_le_Raux n
  have h1 := abs_le.mp hg.2
  have h2 := abs_le.mp hz
  unfold signed R
  rw [Original.Glue.Iaux_re, abs_le]
  constructor <;> linarith only [h1.1,h1.2,h2.1,h2.2,hr,hc,
    mul_nonneg hsmall.le (Nat.cast_nonneg (α:=ℝ) n)]

end
end MovingBulk

namespace MovingBulk
noncomputable section
open Finset Filter MeasureTheory
open Frozen.GoldbachMajorArc
open scoped Topology

private theorem phase_add_fixed (x y : ℝ) : phase (x+y) = phase x * phase y := by
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem major_error_bound (N D m : ℕ) (hsep : 2*D^2<N) :
    ‖major N D m - Z N D m‖ ≤ Polylog.totalArcError D N (m:ℝ) := by
  let F := fun t : ℝ => (primeSum N t)^2 * phase (-(m:ℝ)*t)
  let C := fun q a : ℕ => (unitMean q a)^2 * phase (-(m:ℝ)*((a:ℝ)/q))
  let K := Frozen.GoldbachEstermannKernel.twisted N m
  have hC : C 1 0 = C 1 1 := by
    have hu (a : ℕ) : unitMean 1 a=1 := by rw [unitMean_eq_ram (by simp),ram_one]; simp
    have hz : phase 0=1 := by simp [phase]
    have hint : phase (-(m:ℝ))=1 := by
      unfold phase
      convert Complex.exp_int_mul_two_pi_mul_I (-(m:ℤ)) using 2
      push_cast
      ring
    simp [C,hu,hz,hint]
  have hF : Continuous F := by unfold F primeSum phase; fun_prop
  have hK : Continuous K := by
    unfold K Frozen.GoldbachEstermannKernel.twisted Frozen.GoldbachEstermannKernel.kernel
      Frozen.GoldbachEstermannKernel.phase
    fun_prop
  have h := Frozen.GoldbachBlockGeometry.major_error F K hF hK C hC hsep
  have hco (q : ℕ) :
      (∑ a ∈ (range q).filter (fun a => a.Coprime q), C q a) = coefficient q m :=
    sum_centers_eq_coefficient q m
  simp_rw [hco] at h
  have herr (q a : ℕ) (t : ℝ) :
      ‖F (Frozen.GoldbachBlockGeometry.center q a + t) - C q a * K t‖ =
        Polylog.modelError N q a m t := by
    change ‖(primeSum N ((a:ℝ)/q+t))^2 * phase (-(m:ℝ)*((a:ℝ)/q+t)) -
        ((unitMean q a)^2 * phase (-(m:ℝ)*((a:ℝ)/q))) *
          ((kernel N t)^2 * phase (-(m:ℝ)*t))‖ =
      ‖(primeSum N ((a:ℝ)/q+t))^2 * phase (-(m:ℝ)*((a:ℝ)/q+t)) -
        (unitMean q a * kernel N t)^2 * phase (-(m:ℝ)*((a:ℝ)/q+t))‖
    rw [mul_add, phase_add_fixed]
    congr 1
    ring
  simp_rw [herr] at h
  exact h

theorem big_separated : ∀ᶠ n : ℕ in atTop, 2*(bigCut n)^2 < n := by
  have h := (Original.Glue.log_pow_div 40).eventually_lt_const
    (by norm_num : (0:ℝ) < 1/(2*4^40))
  filter_upwards [h,eventually_ge_atTop (2:ℕ)] with n hn hn2
  have hn0 : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have h' := (div_lt_iff₀ hn0).mp hn
  have hq : (bigCut n:ℝ) ≤ (4*Real.log n)^20 := Polylog.cutoff_le_log 20 hn2
  have hpow := pow_le_pow_left₀ (Nat.cast_nonneg (α:=ℝ) (bigCut n)) hq 2
  have hr : (2:ℝ)*(bigCut n:ℝ)^2 < n := by
    calc
      _ ≤ 2*((4*Real.log n)^20)^2 := mul_le_mul_of_nonneg_left hpow (by norm_num)
      _ = (2*4^40)*(Real.log n)^40 := by ring
      _ < _ := by linarith only [h']
  exact_mod_cast hr

theorem fixed_major_error (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop, ∀ m : ℕ, ‖major N (bigCut N) m - Z N (bigCut N) m‖ ≤ ε*N := by
  have hh := Polylog.eventually_totalArcError_lt 20 0 (by decide) hε
  filter_upwards [hh,big_separated] with N hN hs m
  refine (major_error_bound N (bigCut N) m hs).trans ?_
  simpa only [bigCut,pow_zero,one_mul] using (hN (m:ℝ)).le

end
end MovingBulk

namespace MovingBulk
noncomputable section
open Finset Filter MeasureTheory
open scoped Topology

def minor (N D m : ℕ) : ℂ :=
  ∫ t in (0:ℝ)..1, (Frozen.GoldbachBlockGeometry.arcs D N)ᶜ.indicator
    (fun u => (Frozen.GoldbachMajorArc.primeSum N u)^2 *
      Frozen.GoldbachMajorArc.phase (-(m:ℝ)*u)) t

private theorem weight_square_sum (N : ℕ) :
    (∑ k ∈ range (N+1), (Frozen.GoldbachMajorArc.primeWeight k)^2) ≤
      ((N:ℝ)+1)*(Real.log N)^2 := by
  calc
    _ ≤ ∑ _k ∈ range (N+1), (Real.log N)^2 := by
      apply sum_le_sum
      intro k hk
      by_cases hp : k.Prime
      · rw [Frozen.GoldbachMajorArc.primeWeight, if_pos hp]
        exact pow_le_pow_left₀ (Real.log_natCast_nonneg k)
          (Real.log_le_log (by exact_mod_cast hp.pos)
            (by exact_mod_cast Nat.le_of_lt_succ (mem_range.mp hk))) 2
      · simp [Frozen.GoldbachMajorArc.primeWeight,hp,sq_nonneg]
    _ = _ := by simp

private theorem count_minor_scalar (n l δ ε c : ℝ) (hn : 1≤n) (hl : 1≤l)
    (hδ : 0<δ) (hε : 0<ε) (hlarge : 2/(ε*δ^2) ≤ l)
    (hb : c*(δ*n)^2 ≤ (n/l^2)^2*((n+1)*l^2)) : c ≤ ε*n := by
  have hn0 : 0<n := by linarith
  have hl0 : 0<l := by linarith
  have he : 0<ε*δ^2 := by positivity
  have hscale : 2 ≤ ε*δ^2*l^2 := by
    have h1 := (div_le_iff₀ he).mp hlarge
    have h2 : l ≤ l^2 := by nlinarith only [mul_nonneg hl0.le (sub_nonneg.mpr hl)]
    have h3 : 2 ≤ ε*δ^2*l := by simpa only [mul_comm l (ε*δ^2)] using h1
    exact h3.trans (mul_le_mul_of_nonneg_left h2 he.le)
  have hpos : 0 < (δ*n)^2*l^2 := by positivity
  apply (mul_le_mul_iff_left₀ hpos).mp
  calc
    c*((δ*n)^2*l^2) = (c*(δ*n)^2)*l^2 := by ring
    _ ≤ ((n/l^2)^2*((n+1)*l^2))*l^2 := mul_le_mul_of_nonneg_right hb (sq_nonneg l)
    _ = n^2*(n+1) := by field_simp [hl0.ne'] <;> ring
    _ ≤ n^2*(2*n) := mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg n)
    _ = n^3*2 := by ring
    _ ≤ n^3*(ε*δ^2*l^2) := mul_le_mul_of_nonneg_left hscale (by positivity)
    _ = ε*n*((δ*n)^2*l^2) := by ring

/-- A single prime sum and mask control every finite window of Fourier modes. -/
theorem minor_sparse (δ ε : ℝ) (hδ : 0<δ) (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop, ∀ M : ℕ,
      (((range M).filter (fun m =>
        δ*(N:ℝ) ≤ ‖minor N (Frozen.GoldbachMajorArc.Polylog.cutoff 20 N) m‖)).card : ℝ)
        ≤ ε*(N:ℝ) := by
  classical
  obtain ⟨N₀,hN₀⟩ := Frozen.GoldbachEstermann.uniformMinorSum (2:ℝ) (by norm_num)
  rw [show 2 * ⌈(2:ℝ)⌉₊ + 16 = 20 by norm_num] at hN₀
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [eventually_ge_atTop N₀, eventually_ge_atTop (1:ℕ),
    hlog.eventually_ge_atTop 1, hlog.eventually_ge_atTop (2/(ε*δ^2))] with N hN hN1 hL hbig
  change 1 ≤ Real.log (N:ℝ) at hL
  change 2/(ε*δ^2) ≤ Real.log (N:ℝ) at hbig
  intro M
  let D := Frozen.GoldbachMajorArc.Polylog.cutoff 20 N
  let U := (N:ℝ)/(Real.log N)^2
  let B := (range M).filter (fun m => δ*(N:ℝ) ≤ ‖minor N D m‖)
  have hsup (t : ℝ) (ht : t ∈ Set.Icc 0 1) (hoff : t ∉ Frozen.GoldbachBlockGeometry.arcs D N) :
      ‖Frozen.GoldbachMajorArc.primeSum N t‖ ≤ U := by
    have hx := (hN₀ N hN t ht hoff).2
    change ‖Frozen.GoldbachMajorArc.primeSum N t‖ ≤ (N:ℝ)*(Real.log N)^(-(2:ℝ)) at hx
    rw [Real.rpow_neg (by linarith : 0≤Real.log (N:ℝ)),
      show (Real.log N)^(2:ℝ) = (Real.log N)^2 from Real.rpow_natCast _ 2,
      ←div_eq_mul_inv] at hx
    exact hx
  have hmoment := Frozen.WindowBessel.minorFourthMoment N M Frozen.GoldbachMajorArc.primeWeight
    (Frozen.GoldbachBlockGeometry.arcs D N) U (Frozen.GoldbachEstermann.measurable_block_arcs D N)
    (by dsimp [U]; positivity) hsup
  change (∑ m ∈ range M, ‖minor N D m‖^2) ≤
    U^2*∑ k ∈ range (N+1), (Frozen.GoldbachMajorArc.primeWeight k)^2 at hmoment
  change (B.card:ℝ) ≤ ε*(N:ℝ)
  apply count_minor_scalar (N:ℝ) (Real.log N) δ ε (B.card:ℝ)
    (by exact_mod_cast hN1) hL hδ hε hbig
  calc
    (B.card:ℝ)*(δ*(N:ℝ))^2 = ∑ _m ∈ B, (δ*(N:ℝ))^2 := by simp
    _ ≤ ∑ m ∈ B, ‖minor N D m‖^2 := by
      apply sum_le_sum
      intro m hm
      exact pow_le_pow_left₀ (by positivity) (mem_filter.mp hm).2 2
    _ ≤ ∑ m ∈ range M, ‖minor N D m‖^2 :=
      sum_le_sum_of_subset_of_nonneg (filter_subset ..) (fun m _ _ => sq_nonneg _)
    _ ≤ _ := hmoment.trans (mul_le_mul_of_nonneg_left (weight_square_sum N) (sq_nonneg U))

end
end MovingBulk

namespace MovingBulk
noncomputable section
open Finset MeasureTheory Original.ConvSum

/- Finite Fourier orthogonality from BulkCountEquivalence, adapted to distinct
polynomial length and coefficient index. Frequencies above m cannot contribute. -/
private theorem full_weighted (w : ℕ → ℝ) (N m : ℕ) (hm : m≤N) :
    (∫ t in (0:ℝ)..1,
      (∑ k ∈ range (N+1), (w k:ℂ)*E ((k:ℝ)*t))^2 * E (-(m:ℝ)*t)) =
        ((∑ k ∈ range (m+1), w k*w (m-k) : ℝ):ℂ) := by
  let I := range (N+1)
  let term := fun (k j : ℕ) (t : ℝ) =>
    ((w k:ℂ)*(w j:ℂ))*E (((((k:ℤ)+j-m):ℤ):ℝ)*t)
  have hc (k j : ℕ) : Continuous (term k j) := by dsimp [term,E]; fun_prop
  have hp (t : ℝ) :
      (∑ k ∈ I, (w k:ℂ)*E ((k:ℝ)*t))^2 * E (-(m:ℝ)*t) =
        ∑ k∈I, ∑ j∈I, term k j t := by
    simp only [sq,sum_mul,mul_sum]
    refine sum_congr rfl fun k _ => sum_congr rfl fun j _ => ?_
    dsimp [term]
    push_cast
    rw [show ((k:ℝ)+j-m)*t = ((k:ℝ)*t+j*t) + -(m:ℝ)*t by ring, phase_add,phase_add]
    ring
  let row := fun k : ℕ => ∫ t in (0:ℝ)..1, ∑ j∈I, term k j t
  have hrow (k : ℕ) (hk : k ∈ range (m+1)) : row k = (w k:ℂ)*(w (m-k):ℂ) := by
    dsimp only [row]
    rw [intervalIntegral.integral_finsetSum (fun j _ => (hc k j).intervalIntegrable ..)]
    have hk' := mem_range.mp hk
    have hsub : m-k ∈ I := mem_range.mpr (by omega)
    simp only [term,intervalIntegral.integral_const_mul,fourier_mode]
    rw [sum_eq_single_of_mem (m-k) hsub]
    · simp [show (k:ℤ)+((m-k:ℕ):ℤ)-m = 0 by omega]
    · intro j _ hne
      simp [show (k:ℤ)+j-m ≠ 0 by omega]
  have hzero (k : ℕ) (hk : k ∉ range (m+1)) : row k = 0 := by
    have hkm : m<k := by have h := mt mem_range.mpr hk; omega
    dsimp only [row]
    rw [intervalIntegral.integral_finsetSum (fun j _ => (hc k j).intervalIntegrable ..)]
    apply sum_eq_zero
    intro j _
    simp [term,intervalIntegral.integral_const_mul,fourier_mode,
      show (k:ℤ)+j-m ≠ 0 by omega]
  change (∫ t in (0:ℝ)..1,
    (∑ k ∈ I, (w k:ℂ)*E ((k:ℝ)*t))^2 * E (-(m:ℝ)*t)) = _
  simp_rw [hp]
  rw [intervalIntegral.integral_finsetSum
    (fun k _ => (continuous_finsetSum I (fun j _ => hc k j)).intervalIntegrable ..)]
  calc
    _ = ∑ k ∈ range (m+1), row k := (sum_subset
      (range_subset_range.mpr (by omega : m+1≤N+1)) (fun k _ hk => hzero k hk)).symm
    _ = _ := by push_cast; exact sum_congr rfl hrow

theorem full_coefficient (N m : ℕ) (hm : m≤N) :
    (∫ t in (0:ℝ)..1, (Frozen.GoldbachMajorArc.primeSum N t)^2 *
      Frozen.GoldbachMajorArc.phase (-(m:ℝ)*t)) = (R m:ℂ) := by
  unfold R
  rw [Original.Glue.Raux_eq]
  exact full_weighted Original.Glue.waux N m hm

theorem major_add_minor (N D m : ℕ) (hm : m≤N) :
    major N D m + minor N D m = (R m:ℂ) := by
  have hc : Continuous (fun t : ℝ => (Frozen.GoldbachMajorArc.primeSum N t)^2 *
      Frozen.GoldbachMajorArc.phase (-(m:ℝ)*t)) := by
    unfold Frozen.GoldbachMajorArc.primeSum Frozen.GoldbachMajorArc.phase
    fun_prop
  have hs : MeasurableSet (Frozen.GoldbachBlockGeometry.arcs D N) :=
    Original.ConvSum.measurable_rational_arcs D N
  exact (Frozen.WindowBessel.ExceptionalCoefficients.indicator_integral_split
    hs (hc.intervalIntegrable 0 1)).trans (full_coefficient N m hm)

end
end MovingBulk

open scoped BigOperators
open Finset

namespace MovingDivisor

/-- Summing the absolute divisor formula over positive arguments costs at most
one copy of the interval length for each divisor of the modulus. -/
theorem mean_abs_divisor_sum (q N : ℕ) :
    (∑ m ∈ Finset.Icc 1 N,
      |∑ d ∈ q.divisors, if d ∣ m then (d : ℝ) * (ArithmeticFunction.moebius (q/d) : ℝ) else 0|)
    ≤ (N : ℝ) * (q.divisors.card : ℝ) := by
  classical
  have hmoeb (k : ℕ) : |(ArithmeticFunction.moebius k : ℝ)| ≤ 1 := by
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := k))
  have hI : Finset.Icc 1 N = Finset.Ioc 0 N := by
    ext m
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
  have hcount (d : ℕ) :
      (∑ m ∈ Finset.Icc 1 N, if d ∣ m then (d : ℝ) else 0) ≤ N := by
    calc
      _ = ∑ _m ∈ (Finset.Ioc 0 N).filter (fun m => d ∣ m), (d : ℝ) := by
        rw [hI, Finset.sum_filter]
      _ = ((N / d : ℕ) : ℝ) * d := by
        simp only [Finset.sum_const, Nat.Ioc_filter_dvd_card_eq_div, nsmul_eq_mul]
      _ ≤ N := by exact_mod_cast Nat.div_mul_le_self N d
  calc
    _ ≤ ∑ m ∈ Finset.Icc 1 N, ∑ d ∈ q.divisors,
          |if d ∣ m then (d : ℝ) * (ArithmeticFunction.moebius (q/d) : ℝ) else 0| := by
      exact Finset.sum_le_sum fun m _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ m ∈ Finset.Icc 1 N, ∑ d ∈ q.divisors, if d ∣ m then (d : ℝ) else 0 := by
      refine Finset.sum_le_sum fun m _ => Finset.sum_le_sum fun d _ => ?_
      by_cases h : d ∣ m
      · simp only [if_pos h, abs_mul, abs_of_nonneg (Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_left (hmoeb (q / d)) (Nat.cast_nonneg d : (0 : ℝ) ≤ d)
      · simp [h]
    _ = ∑ d ∈ q.divisors, ∑ m ∈ Finset.Icc 1 N, if d ∣ m then (d : ℝ) else 0 :=
      Finset.sum_comm
    _ ≤ ∑ _d ∈ q.divisors, (N : ℝ) := Finset.sum_le_sum fun d _ => hcount d
    _ = (N : ℝ) * (q.divisors.card : ℝ) := by simp [nsmul_eq_mul, mul_comm]

end MovingDivisor

-- The three local-factor bounds, the weighted Euler product, and the totient
-- ratio bound below are adapted from the Apache-2.0 project proof
-- lean/PEqualNP/Outside/L_goldbach_grh_goldbach_exception_density.lean.
-- These estimates occur in the unconditional portion of that file.
namespace MovingTotient
open Finset Filter
open scoped BigOperators Topology

noncomputable def localTerm (n p : ℕ) : ℝ :=
  if p ∣ n then 1/((p:ℝ)-1) else -1/((p:ℝ)-1)^2

def primesThrough (P : ℕ) : Finset ℕ := (range (P+1)).filter Nat.Prime

private theorem sqrt_times_atom_le {n p : ℕ} (hp : p.Prime) (h : ¬ p ∣ n) :
    Real.sqrt p * |localTerm n p| ≤ 4*(p:ℝ)^(-(3/2):ℝ) := by
  have hp₂ : 2 ≤ (p:ℝ) := by exact_mod_cast hp.two_le
  have hp₀ : 0 < (p:ℝ) := by linarith
  have hd : 0 < (p:ℝ)-1 := by linarith
  have he : (p:ℝ)^(-(3/2):ℝ) = Real.sqrt p/(p:ℝ)^2 := by
    rw [Real.sqrt_eq_rpow,← Real.rpow_two,← Real.rpow_sub hp₀]
    norm_num
  rw [he,localTerm,ite_eq_right h,abs_div,abs_neg,abs_one,abs_of_nonneg (sq_nonneg _)]
  rw [mul_one_div,mul_div_assoc']
  apply (div_le_div_iff₀ (sq_pos_of_pos hd) (sq_pos_of_pos hp₀)).2
  have hh : (p:ℝ)^2 ≤ 4*((p:ℝ)-1)^2 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hp₂) (by linarith : 0 ≤ 3*(p:ℝ)-2)]
  nlinarith only [mul_le_mul_of_nonneg_left hh (Real.sqrt_nonneg (p:ℝ))]

private theorem sqrt_times_atom_le_two {n p : ℕ} (hp : p.Prime) (h : p ∣ n) :
    Real.sqrt p * |localTerm n p| ≤ 2 := by
  have hp₂ : 2 ≤ (p:ℝ) := by exact_mod_cast hp.two_le
  have hd : 0 < (p:ℝ)-1 := by linarith
  have hh : Real.sqrt p ≤ (p:ℝ) := (Real.sqrt_le_left (by positivity)).2 (by nlinarith [sq_nonneg ((p:ℝ)-1)])
  rw [localTerm,ite_eq_left h,abs_of_nonneg (one_div_pos.mpr hd).le,mul_one_div]
  apply (div_le_iff₀ hd).2
  linarith

private theorem prime_divisor_product_le {n : ℕ} (hn : 0 < n) (S : Finset ℕ)
    (hS : ∀ p ∈ S, Nat.Prime p) {ε : ℝ} (he : 0 < ε) :
    (∏ p ∈ S, if p ∣ n then (p:ℝ)^ε else 1) ≤ (n:ℝ)^ε := by
  let D := S.filter (fun p => p ∣ n)
  have hD : D ⊆ n.primeFactors := by
    intro p hp
    have h := Finset.mem_filter.mp hp
    exact Nat.mem_primeFactors.mpr ⟨hS p h.1,h.2,hn.ne'⟩
  rw [← Finset.prod_filter]
  have hprod : ∀ U : Finset ℕ, (∏ p ∈ U, (p:ℝ)^ε) = ((∏ p ∈ U, p : ℕ):ℝ)^ε := by
    intro U
    induction U using Finset.induction_on with
    | empty => simp
    | insert a U ha ih =>
      rw [Finset.prod_insert ha,Finset.prod_insert ha,ih,Nat.cast_mul,Real.mul_rpow (by positivity) (by positivity)]
  rw [hprod]
  apply Real.rpow_le_rpow (by positivity) _ he.le
  exact_mod_cast Nat.le_of_dvd hn ((Finset.prod_dvd_prod_of_subset _ _ id hD).trans (Nat.prod_primeFactors_dvd n))

/-- Rankin's estimate for the absolute local factors, uniform in the prime cutoff. -/
theorem weighted_euler_bound {ε : ℝ} (he : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n P : ℕ), 0 < n →
      (∏ p ∈ primesThrough P, (1+Real.sqrt p*|localTerm n p|)) ≤ C*(n:ℝ)^ε := by
  have htop := (tendsto_rpow_atTop he).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  obtain ⟨K,hK⟩ := Filter.eventually_atTop.mp (htop.eventually_ge_atTop 3)
  let f := fun p : ℕ => 4*(p:ℝ)^(-(3/2):ℝ)
  have hf : Summable f := (Real.summable_nat_rpow.mpr (by norm_num : -(3/2:ℝ) < -1)).mul_left 4
  let A := ∑' p, f p
  refine ⟨Real.exp A*3^K,by positivity,?_⟩
  intro n P hn
  let S := primesThrough P
  have hS : ∀ p ∈ S, Nat.Prime p := fun p hp => (Finset.mem_filter.mp hp).2
  let b := fun p : ℕ => if p < K then (3:ℝ) else 1
  let c := fun p : ℕ => if p ∣ n then (p:ℝ)^ε else 1
  have fpos (p : ℕ) : 0 ≤ f p := by dsimp [f]; positivity
  have b₁ (p : ℕ) : 1 ≤ b p := by dsimp [b]; split_ifs <;> norm_num
  have hpbound (p : ℕ) (hp : p ∈ S) :
      1+Real.sqrt p * |localTerm n p| ≤ Real.exp (f p)*b p*c p := by
    have hexp : 1 ≤ Real.exp (f p) := Real.one_le_exp (fpos p)
    by_cases hd : p ∣ n
    · have hp₁ : 1 ≤ (p:ℝ) := by exact_mod_cast (hS p hp).one_le
      have hc : 1 ≤ c p := by simpa [c,hd] using Real.one_le_rpow hp₁ he.le
      have h₃ : 1+Real.sqrt p*|localTerm n p| ≤ 3 := by linarith [sqrt_times_atom_le_two (hS p hp) hd]
      apply h₃.trans
      by_cases hk : p < K
      · dsimp only [b]; rw [ite_eq_left hk]; nlinarith only [hexp,hc,mul_le_mul hexp hc (by norm_num) (Real.exp_pos _).le]
      · have := hK p (le_of_not_gt hk)
        simp only [b,ite_eq_right hk,mul_one,c,ite_eq_left hd] at *
        exact this.trans (le_mul_of_one_le_left (by positivity) hexp)
    · rw [show c p=1 by simp [c,hd],mul_one]
      exact ((add_le_add le_rfl (sqrt_times_atom_le (hS p hp) hd)).trans (by
        linarith only [Real.add_one_le_exp (f p)] : 1+f p ≤ Real.exp (f p))).trans
          (le_mul_of_one_le_right (Real.exp_pos _).le (b₁ p))
  have h₁ : ∏ p ∈ S, Real.exp (f p) ≤ Real.exp A := by
    rw [← Real.exp_sum]
    exact Real.exp_le_exp.mpr (hf.sum_le_tsum S (fun i _ => fpos i))
  have h₂ : ∏ p ∈ S, b p ≤ (3:ℝ)^K := by
    dsimp [b]
    rw [← Finset.prod_filter,Finset.prod_const]
    apply pow_le_pow_right₀ (by norm_num)
    simpa using Finset.card_le_card (show S.filter (fun p => p < K) ⊆ range K from
      fun p hp => Finset.mem_range.mpr (Finset.mem_filter.mp hp).2)
  have h₃ := prime_divisor_product_le hn S hS he
  calc
    _ ≤ ∏ p ∈ S, Real.exp (f p)*b p*c p := Finset.prod_le_prod₀ (fun p _ => by positivity) hpbound
    _ = _ := by rw [Finset.prod_mul_distrib,Finset.prod_mul_distrib]
    _ ≤ (Real.exp A*3^K)*(n:ℝ)^ε := by
      apply mul_le_mul (mul_le_mul h₁ h₂ (Finset.prod_nonneg fun p _ => (b₁ p).trans' zero_le_one)
        (Real.exp_pos _).le) h₃ _ (by positivity)
      apply Finset.prod_nonneg; intro p _; split_ifs <;> positivity

theorem totient_ratio_bound {ε : ℝ} (he : 0 < ε) :
    ∃ C : ℝ, 0<C ∧ ∀ q : ℕ, 0<q → (q:ℝ)/(q.totient:ℝ) ≤ C*(q:ℝ)^ε := by
  obtain ⟨C,hC,H⟩ := weighted_euler_bound he
  refine ⟨C,hC,?_⟩
  intro q hq
  have hφ : 0 < (q.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
  have hp (p : ℕ) (h : p ∈ q.primeFactors) : 2 ≤ (p:ℝ) := by
    exact_mod_cast (Nat.prime_of_mem_primeFactors h).two_le
  have hD : (∏ p ∈ q.primeFactors, ((p:ℝ)-1)) ≠ 0 :=
    (Finset.prod_pos fun p h => by linarith [hp p h]).ne'
  have hh : (q.totient:ℝ)*(∏ p ∈ q.primeFactors, (p:ℝ)) =
      (q:ℝ)*(∏ p ∈ q.primeFactors, ((p:ℝ)-1)) := by
    have ho := congrArg (fun a : ℕ => (a:ℝ)) (Nat.totient_mul_prod_primeFactors q)
    push_cast at ho
    convert ho using 2
    apply Finset.prod_congr rfl
    intro p h
    rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors h).one_le]; simp
  have hsub : q.primeFactors ⊆ primesThrough q := by
    intro p h
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_of_mem_primeFactors h)),
      Nat.prime_of_mem_primeFactors h⟩
  calc
    _ = ∏ p ∈ q.primeFactors, (p:ℝ)/((p:ℝ)-1) := by
      rw [Finset.prod_div_distrib]; field_simp; linarith only [hh]
    _ ≤ ∏ p ∈ q.primeFactors, (1+Real.sqrt p*|localTerm q p|) := by
      apply Finset.prod_le_prod₀ (fun p h => div_nonneg (Nat.cast_nonneg _) (by linarith [hp p h]))
      intro p h
      have hd : 0 < (p:ℝ)-1 := by linarith [hp p h]
      rw [localTerm,ite_eq_left (Nat.dvd_of_mem_primeFactors h),abs_of_pos (one_div_pos.mpr hd),mul_one_div]
      have hs : 1 ≤ Real.sqrt p := by simpa using Real.sqrt_le_sqrt (show (1:ℝ) ≤ p by linarith [hp p h])
      field_simp; linarith
    _ ≤ _ := (Finset.prod_le_prod_of_subset_of_one_le₀ hsub (fun p _ => by positivity)
      (fun p _ _ => le_add_of_nonneg_right (by positivity))).trans (H q q hq)


private theorem divisors_card_sqrt (q : ℕ) (hq : 0 < q) :
    q.divisors.card ≤ 2 * q.sqrt := by
  classical
  let S := q.divisors.filter fun d => d ≤ q.sqrt
  let T := q.divisors.filter fun d => ¬ d ≤ q.sqrt
  let U := Finset.Icc 1 q.sqrt
  have hs : S.card ≤ U.card := Finset.card_le_card (by
    intro d hd
    obtain ⟨hmem,hle⟩ := Finset.mem_filter.mp hd
    exact Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hmem,hle⟩)
  have ht : T.card ≤ U.card := by
    refine Finset.card_le_card_of_injOn (fun d => q/d) ?_ ?_
    · intro d hd
      obtain ⟨hm,hlarge⟩ := Finset.mem_filter.mp hd
      have hdvd := Nat.dvd_of_mem_divisors hm
      have hp := Nat.pos_of_mem_divisors hm
      have hdiv : 0 < q/d := Nat.div_pos (Nat.le_of_dvd hq hdvd) hp
      have heq : q = d*(q/d) := (Nat.mul_div_cancel' hdvd).symm
      exact Finset.mem_Icc.mpr ⟨hdiv, (Nat.le_sqrt_of_eq_mul heq).resolve_left hlarge⟩
    · intro a ha b hb hab
      have had := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp ha).1
      have hbd := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hb).1
      have hpos := Nat.div_pos (Nat.le_of_dvd hq had)
        (Nat.pos_of_mem_divisors (Finset.mem_filter.mp ha).1)
      apply Nat.eq_of_mul_eq_mul_left hpos
      calc
        q / a * a = q := Nat.div_mul_cancel had
        _ = q / b * b := (Nat.div_mul_cancel hbd).symm
        _ = q / a * b := by rw [hab]
  have hu : U.card = q.sqrt := by simp [U, Nat.card_Icc]
  have hpart : S.card + T.card = q.divisors.card :=
    Finset.card_filter_add_card_filter_not (s := q.divisors) (fun d => d ≤ q.sqrt)
  omega

theorem summable_divisors_div_totient_sq :
    Summable (fun q : ℕ => (q.divisors.card : ℝ) / (q.totient : ℝ)^2) := by
  obtain ⟨C,hC,H⟩ := totient_ratio_bound (ε := 1/8) (by norm_num)
  have hs : Summable fun q : ℕ => (2*C^2) * (q : ℝ)^(-5/4 : ℝ) :=
    (Real.summable_nat_rpow.mpr (by norm_num : (-5/4 : ℝ) < -1)).mul_left _
  apply Summable.of_nonneg_of_le (fun q => by positivity) _ hs
  intro q
  by_cases hz : q = 0
  · subst q
    simp [show (-5 / 4 : ℝ) ≠ 0 by norm_num]
  have hq := Nat.pos_of_ne_zero hz
  have x : 0 < (q : ℝ) := by exact_mod_cast hq
  have hphi : 0 < (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
  have ht : (q.divisors.card : ℝ) ≤ 2 * Real.sqrt q := by
    calc
      _ ≤ 2*(q.sqrt : ℝ) := by exact_mod_cast divisors_card_sqrt q hq
      _ ≤ 2*Real.sqrt q := mul_le_mul_of_nonneg_left Real.nat_sqrt_le_real_sqrt (by norm_num)
  have h₂ := pow_le_pow_left₀ (div_nonneg x.le hphi.le) (H q hq) 2
  have hp : Real.sqrt (q:ℝ) * ((q:ℝ)^(1/8:ℝ))^2 / (q:ℝ)^2 = (q:ℝ)^(-5/4:ℝ) := by
    rw [Real.sqrt_eq_rpow, pow_two ((q:ℝ)^(1/8:ℝ)), ← Real.rpow_add x,
      ← Real.rpow_add x, ← Real.rpow_two, ← Real.rpow_sub x]
    norm_num
  calc
    _ = (q.divisors.card : ℝ) * ((q:ℝ) / (q.totient:ℝ))^2 / (q:ℝ)^2 := by
      field_simp [x.ne',hphi.ne'] <;> ring
    _ ≤ (2*Real.sqrt q) * (C*(q:ℝ)^(1/8:ℝ))^2 / (q:ℝ)^2 :=
      div_le_div_of_nonneg_right (mul_le_mul ht h₂ (sq_nonneg _) (by positivity)) (sq_nonneg _)
    _ = (2*C^2) * (Real.sqrt q * ((q:ℝ)^(1/8:ℝ))^2 / (q:ℝ)^2) := by ring
    _ = _ := by rw [hp]

end MovingTotient

namespace MovingBulk
noncomputable section
open Finset Filter
open scoped Topology

def tail (H T m : ℕ) : ℝ :=
  ∑ q ∈ Ioc H T, |(Frozen.GoldbachMajorArc.coefficient q m).re|

theorem tail_nonneg (H T m : ℕ) : 0 ≤ tail H T m :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

private theorem coefficient_mean (q N : ℕ) (hq : 0 < q) :
    (∑ m ∈ Icc 1 N, |(Frozen.GoldbachMajorArc.coefficient q m).re|) ≤
      (N : ℝ) * ((q.divisors.card : ℝ) / (q.totient : ℝ)^2) := by
  have hmean : (∑ m ∈ Icc 1 N, |Original.Glue.caux q m|) ≤
      (N : ℝ) * (q.divisors.card : ℝ) := by
    simpa only [Original.Glue.caux, ite_mul, zero_mul] using
      MovingDivisor.mean_abs_divisor_sum q N
  have hmu : |(ArithmeticFunction.moebius q : ℝ)| ≤ 1 := by
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := q)
  have hsq : (ArithmeticFunction.moebius q : ℝ)^2 ≤ 1 := by
    have h := abs_le.mp hmu
    nlinarith [mul_nonneg (sub_nonneg.mpr h.2) (show 0 ≤ 1+(ArithmeticFunction.moebius q:ℝ) by linarith [h.1])]
  simp_rw [coeff_re_arithmetic q _ hq, abs_mul, abs_of_nonneg (sq_nonneg _)]
  rw [← sum_mul]
  calc
    _ ≤ ((N:ℝ) * (q.divisors.card:ℝ)) * ((ArithmeticFunction.moebius q:ℝ)/q.totient)^2 :=
      mul_le_mul_of_nonneg_right hmean (sq_nonneg _)
    _ ≤ ((N:ℝ) * (q.divisors.card:ℝ)) * (1 / (q.totient:ℝ)^2) := by
      rw [div_pow]
      exact mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right hsq (sq_nonneg _)) (by positivity)
    _ = _ := by ring

theorem uniform_tail (hs : Summable (fun q : ℕ => (q.divisors.card:ℝ) / (q.totient:ℝ)^2))
    (η : ℝ) (hη : 0 < η) :
    ∃ H : ℕ, ∀ T N : ℕ, (∑ m ∈ Icc 1 N, tail H T m) ≤ N * η := by
  classical
  obtain ⟨s, h⟩ := hs.vanishing (Iio_mem_nhds hη)
  refine ⟨s.sup id, fun T N => ?_⟩
  have hd : Disjoint (Ioc (s.sup id) T) s := by
    refine Finset.disjoint_left.mpr fun q hq hqs => ?_
    exact (not_lt_of_ge (Finset.le_sup (f := id) hqs)) (mem_Ioc.mp hq).1
  have hlt : (∑ q ∈ Ioc (s.sup id) T, (q.divisors.card:ℝ)/(q.totient:ℝ)^2) < η :=
    h _ hd
  unfold tail
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ q ∈ Ioc (s.sup id) T, (N:ℝ) * ((q.divisors.card:ℝ)/(q.totient:ℝ)^2) :=
      Finset.sum_le_sum fun q hq => coefficient_mean q N (lt_of_le_of_lt (Nat.zero_le _) (mem_Ioc.mp hq).1)
    _ ≤ _ := by rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left hlt.le (by positivity)

theorem tail_card (H N : ℕ) (s η : ℝ) (hs : 0<s)
    (havg : (∑ m ∈ Icc 1 N, tail H N m) ≤ N * η) :
    (((Icc 1 N).filter (fun m => s ≤ tail H N m)).card : ℝ) * s ≤ N * η := by
  classical
  let A := (Icc 1 N).filter (fun m => s ≤ tail H N m)
  calc
    _ = ∑ _m ∈ A, s := by simp [A, nsmul_eq_mul]
    _ ≤ ∑ m ∈ A, tail H N m :=
      sum_le_sum fun m hm => (mem_filter.mp hm).2
    _ ≤ ∑ m ∈ Icc 1 N, tail H N m :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun m _ _ => tail_nonneg _ _ _)
    _ ≤ _ := havg

end
end MovingBulk

namespace MovingBulk
noncomputable section
open Finset MeasureTheory
open Frozen.GoldbachEstermannKernel
open scoped Topology

def mass (N D m q : ℕ) : ℂ :=
  ∫ t in -(Frozen.GoldbachBlockGeometry.width D N q)..Frozen.GoldbachBlockGeometry.width D N q,
    twisted N m t

private theorem mass_width (N D q : ℕ) (hq : 0<q) (hD : 0<D) (hsep : 2*D^2<N) :
    0 < Frozen.GoldbachBlockGeometry.width D N q ∧ Frozen.GoldbachBlockGeometry.width D N q ≤ 1/2 := by
  have hn : 0<N := by omega
  have hn' : 0<(N:ℝ) := by exact_mod_cast hn
  have hq' : (1:ℝ) ≤ q := by exact_mod_cast hq
  have hD' : 0<(D:ℝ) := by exact_mod_cast hD
  have hdn : 2*D ≤ N := by
    have hsq : D ≤ D^2 := by simpa [sq] using Nat.mul_le_mul_left D hD
    omega
  have hdn' : 2*(D:ℝ) ≤ N := by exact_mod_cast hdn
  have hqn : (N:ℝ) ≤ q*(N:ℝ) := by simpa using mul_le_mul_of_nonneg_right hq' hn'.le
  unfold Frozen.GoldbachBlockGeometry.width
  constructor
  · positivity
  · apply (div_le_iff₀ (by positivity)).mpr
    linarith

private theorem twisted_continuous (N m : ℕ) : Continuous (twisted N m) := by
  unfold twisted kernel phase
  fun_prop

private theorem twisted_norm (N m : ℕ) (t : ℝ) : ‖twisted N m t‖ = ‖kernel N t‖^2 := by
  simp [twisted,phase,norm_pow,Complex.norm_exp_ofReal_mul_I]

theorem mass_norm (N D m q : ℕ) (hq : 0<q) (hD : 0<D) (hsep : 2*D^2<N) :
    ‖mass N D m q‖ ≤ (N:ℝ)+1 := by
  let w := Frozen.GoldbachBlockGeometry.width D N q
  obtain ⟨hw,hw'⟩ := mass_width N D q hq hD hsep
  change 0<w at hw
  change w≤1/2 at hw'
  have hker : Continuous (fun t => ‖kernel N t‖^2) := by unfold kernel phase; fun_prop
  have hcenter (t : ℝ) : twisted N N t = ((‖kernel N t‖^2 : ℝ):ℂ) :=
    Original.GoldbachMajorArc.kernel_square_twist N t
  have hfull := full_coefficient N N le_rfl
  simp_rw [hcenter] at hfull
  rw [intervalIntegral.integral_ofReal] at hfull
  change ‖∫ t in -w..w, twisted N m t‖ ≤ _
  calc
    _ ≤ ∫ t in -w..w, ‖twisted N m t‖ := intervalIntegral.norm_integral_le_integral_norm (by linarith)
    _ = ∫ t in -w..w, ‖kernel N t‖^2 := by simp_rw [twisted_norm]
    _ ≤ ∫ t in (-(1/2):ℝ)..1/2, ‖kernel N t‖^2 :=
      intervalIntegral.integral_mono_interval (by linarith) (by linarith) hw'
        (Filter.Eventually.of_forall fun t => sq_nonneg _) (hker.intervalIntegrable _ _)
    _ = (N:ℝ)+1 := by simpa using congrArg Complex.re hfull

private theorem twisted_tail_point (N m : ℕ) (t : ℝ) (ht : t≠0) (hhalf : |t|≤1/2) :
    ‖twisted N m t‖ ≤ t^(-2:ℤ) := by
  have hp := abs_pos.mpr ht
  have hs := Frozen.OAI.Problem337.sin_pi_mul_lower_on_middle hp (le_refl |t|)
    (by linarith : |t|≤1-|t|)
  have hs' : |t| ≤ |Real.sin (Real.pi*t)| := by
    by_cases h : 0≤t
    · rw [abs_of_nonneg h] at hs ⊢
      exact (by linarith : t ≤ Real.sin (Real.pi*t)).trans (le_abs_self _)
    · have ht' := lt_of_not_ge h
      rw [abs_of_neg ht',mul_neg,Real.sin_neg] at hs
      rw [abs_of_neg ht']
      exact (by linarith : -t ≤ -Real.sin (Real.pi*t)).trans (neg_le_abs _)
  have hgeom := Frozen.OAI.Problem337.norm_geometric_phase_sum_le
    (abs_pos.mp (hp.trans_le hs')) (N+1)
  have hphase (k : ℕ) : phase ((k:ℝ)*t) =
      Complex.exp (Complex.I*(2*Real.pi*t : ℝ))^k := by
    unfold phase
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hbound : ‖kernel N t‖ ≤ 1/|t| := by
    unfold kernel
    simp_rw [hphase]
    exact hgeom.trans (one_div_le_one_div_of_le hp hs')
  rw [twisted_norm]
  calc
    ‖kernel N t‖^2 ≤ (1/|t|)^2 := pow_le_pow_left₀ (norm_nonneg _) hbound 2
    _ = t^(-2:ℤ) := by norm_num [div_pow, sq_abs, one_div]

private theorem mass_tail_interval (N m : ℕ) {a b : ℝ} (hab : a≤b)
    (ha : -(1/2)≤a) (hb : b≤1/2) (hz : 0 ∉ Set.uIcc a b) :
    ‖∫ t in a..b, twisted N m t‖ ≤ a⁻¹-b⁻¹ := by
  calc
    _ ≤ ∫ t in a..b, ‖twisted N m t‖ := intervalIntegral.norm_integral_le_integral_norm hab
    _ ≤ ∫ t in a..b, t^(-2:ℤ) := by
      apply intervalIntegral.integral_mono_on hab ((twisted_continuous N m).norm.intervalIntegrable _ _)
        (intervalIntegral.intervalIntegrable_zpow (Or.inr hz))
      intro t ht
      have ht0 : t≠0 := by
        rintro rfl
        exact hz (by rwa [Set.uIcc_of_le hab])
      exact twisted_tail_point N m t ht0 (abs_le.mpr ⟨ha.trans ht.1,ht.2.trans hb⟩)
    _ = a⁻¹-b⁻¹ := by
      rw [integral_zpow (n:=(-2:ℤ)) (Or.inr ⟨by norm_num, hz⟩)]
      norm_num <;> ring

theorem mass_error (N D m q : ℕ) (hm : m≤N) (hq : 0<q) (hD : 0<D) (hsep : 2*D^2<N) :
    ‖mass N D m q - ((m:ℂ)+1)‖ ≤ 2*((q:ℝ)*N)/D := by
  let w := Frozen.GoldbachBlockGeometry.width D N q
  obtain ⟨hw,hw'⟩ := mass_width N D q hq hD hsep
  change 0<w at hw
  change w≤1/2 at hw'
  have hle : -(1/2:ℝ) ≤ -w := by linarith
  have hleft := mass_tail_interval N m hle le_rfl (by linarith : -w ≤ 1/2)
    (by rw [Set.uIcc_of_le hle]; intro h; linarith [h.2])
  have hright := mass_tail_interval N m hw' (by linarith : -(1/2)≤w) le_rfl
    (by rw [Set.uIcc_of_le hw']; intro h; linarith [h.1])
  let F := twisted N m
  have hcont := twisted_continuous N m
  have hsum : (∫ t in (-(1/2):ℝ)..-w, F t) + (∫ t in -w..w, F t) +
      (∫ t in w..1/2, F t) = (m:ℂ)+1 := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hcont.intervalIntegrable _ _)
      (hcont.intervalIntegrable _ _), intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)]
    exact full_coefficient N m hm
  have herr : mass N D m q - ((m:ℂ)+1) =
      -((∫ t in (-(1/2):ℝ)..-w, F t) + (∫ t in w..1/2, F t)) := by
    change (∫ t in -w..w, F t) - _ = _
    rw [← hsum]
    abel
  rw [herr,norm_neg]
  apply (norm_add_le _ _).trans
  calc
    _ ≤ (-(1/2:ℝ))⁻¹-(-w)⁻¹+(w⁻¹-(1/2:ℝ)⁻¹) := add_le_add hleft hright
    _ ≤ 2*w⁻¹ := by norm_num <;> linarith
    _ = _ := by dsimp [w,Frozen.GoldbachBlockGeometry.width]; rw [inv_div]; ring

end
end MovingBulk

namespace MovingBulk
noncomputable section
open Finset Frozen.GoldbachMajorArc

private theorem coeff_re_abs_cap (q m : ℕ) (hq : 0<q) : |(coefficient q m).re| ≤ 2 := by
  have he : (q:ℝ)*‖coefficient q m‖^2 ≤ (if Even q then 2 else 1) :=
    coefficient_frequency_energy q m
  have hp : (if Even q then (2:ℝ) else 1) ≤ 2 := by split <;> norm_num
  have hq' : (1:ℝ) ≤ q := by exact_mod_cast hq
  have hsq : ‖coefficient q m‖^2 ≤ 2 := by
    nlinarith only [he.trans hp,mul_nonneg (sub_nonneg.mpr hq') (sq_nonneg ‖coefficient q m‖)]
  exact (Complex.abs_re_le_norm _).trans (by nlinarith [norm_nonneg (coefficient q m)])

theorem model_trunc_error (N D m H T : ℕ) (hHD : H ≤ D) (hDT : D ≤ T) (hm : m ≤ N)
    (hD : 0 < D) (hsep : 2*D^2 < N) :
    |(Z N D m).re - ((m:ℝ)+1)*(∑ q ∈ Icc 1 H, (coefficient q m).re)| ≤
      (N:ℝ)*(4*(H:ℝ)^2)/(D:ℝ) + ((N:ℝ)+1)*tail H T m := by
  let u (q : ℕ) := (coefficient q m).re
  let v (q : ℕ) := (mass N D m q).re
  have real_sum : (Z N D m).re = ∑ q ∈ Icc 1 D, u q*v q := by
    unfold Z
    rw [Complex.re_sum]
    refine sum_congr rfl fun q hq => ?_
    change (coefficient q m * mass N D m q).re = u q*v q
    rw [Complex.mul_re,coefficient_im_zero m (mem_Icc.mp hq).1,zero_mul,sub_zero]
  have partition : Icc 1 D = Icc 1 H ∪ Ioc H D := by
    ext q
    simp only [mem_union,mem_Icc,mem_Ioc]
    omega
  have hdj : Disjoint (Icc 1 H) (Ioc H D) := disjoint_left.mpr fun q hq hq' =>
    (not_lt_of_ge (mem_Icc.mp hq).2) (mem_Ioc.mp hq').1
  have integral_error (q : ℕ) (hq : q ∈ Icc 1 H) :
      |v q-((m:ℝ)+1)| ≤ 2*((H:ℝ)*N)/(D:ℝ) := by
    have hq₀ := (mem_Icc.mp hq).1
    have hqH : (q:ℝ)≤H := by exact_mod_cast (mem_Icc.mp hq).2
    calc
      _ = |(mass N D m q - ((m:ℂ)+1)).re| := by simp [v]
      _ ≤ _ := Complex.abs_re_le_norm _
      _ ≤ _ := mass_error N D m q hm hq₀ hD hsep
      _ ≤ _ := by gcongr
  have low :
      |∑ q ∈ Icc 1 H, u q*(v q-((m:ℝ)+1))| ≤ (N:ℝ)*(4*(H:ℝ)^2)/(D:ℝ) := by
    calc
      _ ≤ ∑ q ∈ Icc 1 H, |u q*(v q-((m:ℝ)+1))| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _q ∈ Icc 1 H, 2*(2*((H:ℝ)*N)/(D:ℝ)) := by
        apply sum_le_sum
        intro q hq
        rw [abs_mul]
        exact mul_le_mul (coeff_re_abs_cap q m (mem_Icc.mp hq).1)
          (integral_error q hq) (abs_nonneg _) (by norm_num)
      _ = _ := by simp [Nat.card_Icc] <;> ring
  have high :
      |∑ q ∈ Ioc H D, u q*v q| ≤ ((N:ℝ)+1)*tail H T m := by
    calc
      _ ≤ ∑ q ∈ Ioc H D, |u q*v q| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ q ∈ Ioc H D, ((N:ℝ)+1)*|u q| := by
        apply sum_le_sum
        intro q hq
        have hq₀ : 0<q := by have := (mem_Ioc.mp hq).1; omega
        have hv : |v q| ≤ (N:ℝ)+1 :=
          (Complex.abs_re_le_norm _).trans (mass_norm N D m q hq₀ hD hsep)
        rw [abs_mul,mul_comm ((N:ℝ)+1)]
        exact mul_le_mul_of_nonneg_left hv (abs_nonneg _)
      _ = ((N:ℝ)+1) * (∑ q ∈ Ioc H D, |u q|) := (mul_sum ..).symm
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact sum_le_sum_of_subset_of_nonneg
          (fun q hq => mem_Ioc.mpr ⟨(mem_Ioc.mp hq).1, (mem_Ioc.mp hq).2.trans hDT⟩)
          (fun q _ _ => abs_nonneg _)
  have hsplit : (Z N D m).re - ((m:ℝ)+1)*(∑ q ∈ Icc 1 H, u q) =
      (∑ q ∈ Icc 1 H, u q*(v q-((m:ℝ)+1))) + ∑ q ∈ Ioc H D, u q*v q := by
    rw [real_sum,partition,sum_union hdj]
    simp_rw [mul_sub]
    rw [sum_sub_distrib, ←sum_mul]
    ring
  change |(Z N D m).re - ((m:ℝ)+1)*(∑ q ∈ Icc 1 H, u q)| ≤ _
  rw [hsplit]
  exact (abs_add_le _ _).trans (add_le_add low high)
end
end MovingBulk

namespace MovingBulk
noncomputable section
open Finset Filter
open scoped Topology

private theorem cutoffs_large (K : ℕ) :
    ∀ᶠ n : ℕ in atTop, K ≤ cutoff n ∧ K ≤ bigCut n := by
  filter_upwards [eventually_ge_atTop (2^K)] with n hn
  have hl : K ≤ Nat.log 2 (n+2) := Nat.le_log_of_pow_le (by decide) (by omega)
  have h1 : 1 ≤ Nat.log 2 (n+2) := Nat.le_log_of_pow_le (by decide) (by simp)
  exact ⟨hl.trans (le_self_pow h1 (by decide : 2 ≠ 0)),
    hl.trans (le_self_pow h1 (by decide : 20 ≠ 0))⟩

private theorem cut_budget (H : ℕ) (s : ℝ) (hs : 0 < s) :
    ∀ᶠ n : ℕ in atTop, ∀ D ∈ ({cutoff n, bigCut n} : Finset ℕ),
      H ≤ D ∧ 0 < D ∧ (n:ℝ)*(4*(H:ℝ)^2)/D ≤ s*n := by
  obtain ⟨K, hK⟩ := exists_nat_gt (4*(H:ℝ)^2 / s)
  filter_upwards [cutoffs_large (max 1 (max H K))] with n hn D hD
  have hb : max 1 (max H K) ≤ D := by
    simp only [mem_insert, mem_singleton] at hD
    rcases hD with rfl | rfl
    · exact hn.1
    · exact hn.2
  have hH : H ≤ D := (le_max_left H K).trans ((le_max_right ..).trans hb)
  have hkn : K ≤ D := (le_max_right H K).trans ((le_max_right ..).trans hb)
  have hD0 : 0<D := (le_max_left 1 _).trans hb
  have hkn' : (K:ℝ) ≤ D := by exact_mod_cast hkn
  have hsmall := (div_lt_iff₀ hs).mp hK
  refine ⟨hH, hD0, (div_le_iff₀ (by exact_mod_cast hD0 : (0:ℝ)<D)).2 ?_⟩
  calc
    _ ≤ (n:ℝ)*((D:ℝ)*s) := mul_le_mul_of_nonneg_left
      (hsmall.le.trans (mul_le_mul_of_nonneg_right hkn' hs.le)) (by positivity)
    _ = _ := by ring

private theorem signed_floor {N m H : ℕ} {s : ℝ}
    (hs : 0<s) (hm : m ≤ N) (h1 : 1 ≤ N)
    (hms : 2*(cutoff m)^2 < m) (hNs : 2*(bigCut N)^2 < N)
    (hmcut : H ≤ cutoff m ∧ 0 < cutoff m ∧
      (m:ℝ)*(4*(H:ℝ)^2)/cutoff m ≤ s*m)
    (hNcut : H ≤ bigCut N ∧ 0 < bigCut N ∧
      (N:ℝ)*(4*(H:ℝ)^2)/bigCut N ≤ s*N)
    (hmove : |signed m - (R m - (Z m (cutoff m) m).re)| ≤ s*m)
    (hfix : ‖major N (bigCut N) m - Z N (bigCut N) m‖ ≤ s*N)
    (hminor : ‖minor N (bigCut N) m‖ ≤ s*N)
    (htail : tail H N m ≤ s) : -(10*s*(N:ℝ)) ≤ signed m := by
  have hdm : cutoff m ≤ (cutoff m)^2 := le_self_pow hmcut.2.1 (by decide)
  have hdN : bigCut N ≤ (bigCut N)^2 := le_self_pow hNcut.2.1 (by decide)
  have hA := model_trunc_error m (cutoff m) m H N hmcut.1 (by omega : cutoff m ≤ N)
    le_rfl hmcut.2.1 hms
  have hB := model_trunc_error N (bigCut N) m H N hNcut.1 (by omega : bigCut N ≤ N)
    hm hNcut.2.1 hNs
  have hmr : (m:ℝ) ≤ N := by exact_mod_cast hm
  have hNr : (1:ℝ) ≤ N := by exact_mod_cast h1
  have hsm : s*(m:ℝ) ≤ s*N := mul_le_mul_of_nonneg_left hmr hs.le
  have ht (k : ℕ) (hk : k ≤ N) : ((k:ℝ)+1)*tail H N m ≤ 2*(s*N) := by
    have hkr : (k:ℝ) ≤ N := by exact_mod_cast hk
    calc
      _ ≤ ((k:ℝ)+1)*s := mul_le_mul_of_nonneg_left htail (by positivity)
      _ ≤ (2*(N:ℝ))*s := mul_le_mul_of_nonneg_right (by linarith) hs.le
      _ = _ := by ring
  have hreal := congrArg Complex.re (major_add_minor N (bigCut N) m hm)
  rw [Complex.add_re, Complex.ofReal_re] at hreal
  have hmaj := (Complex.re_le_norm (-(major N (bigCut N) m - Z N (bigCut N) m))).trans
    ((norm_neg _).le.trans hfix)
  rw [Complex.neg_re, Complex.sub_re] at hmaj
  have hmin := (Complex.re_le_norm (-minor N (bigCut N) m)).trans
    ((norm_neg _).le.trans hminor)
  rw [Complex.neg_re] at hmin
  linarith only [(abs_le.mp hA).2, (abs_le.mp hB).1, hmcut.2.2, hNcut.2.2,
    ht m hm, ht N le_rfl, (abs_le.mp hmove).1, hmaj, hmin, hreal, hsm,
    mul_nonneg hs.le (Nat.cast_nonneg (α:=ℝ) N)]

theorem signed_density (e : ℝ) (he : 0<e) :
    Tendsto (fun j : ℕ => (((Ico j (2*j)).filter (fun i => signed (2*i) < -(e*(2*i:ℕ)))).card : ℝ) / j)
      atTop (nhds (0:ℝ)) := by
  classical
  rw [Metric.tendsto_atTop]
  intro r hr
  let s := e/64
  let ξ := r/16
  have hs : 0<s := by dsimp [s]; positivity
  have hx : 0<ξ := by dsimp [ξ]; positivity
  obtain ⟨H, htail⟩ := uniform_tail MovingTotient.summable_divisors_div_totient_sq (ξ*s) (mul_pos hx hs)
  have hgood := (cut_budget H s hs).and ((moving_error s hs).and
    (Original.GoldbachMajorArc.cutoff_separated.and (big_separated.and
    ((fixed_major_error s hs).and (minor_sparse s ξ hs hx)))))
  obtain ⟨K, hK⟩ := eventually_atTop.1 hgood
  refine ⟨max 1 K, fun j hj => ?_⟩
  let N := 4*j
  have hj1 : 1 ≤ j := (le_max_left ..).trans hj
  have hjK : K ≤ j := (le_max_right ..).trans hj
  have hN : K ≤ N := by dsimp [N]; omega
  have hNj : (N:ℝ) = 4*(j:ℝ) := by dsimp [N]; push_cast; ring
  obtain ⟨hcutN, _, _, hsepN, hfixN, hminN⟩ := hK N hN
  let A := (range (N+1)).filter (fun m => s*(N:ℝ) ≤ ‖minor N (bigCut N) m‖)
  let B := (Icc 1 N).filter (fun m => s ≤ tail H N m)
  let bad := (Ico j (2*j)).filter (fun i => signed (2*i) < -(e*(2*i:ℕ)))
  have hA : (A.card : ℝ) ≤ ξ*N := hminN (N+1)
  have hB : (B.card : ℝ) ≤ ξ*N := by
    have h := tail_card H N s (ξ*s) hs (htail N N)
    apply (le_of_mul_le_mul_right ?_ hs : _)
    simpa only [mul_assoc, mul_left_comm, mul_comm, B] using h
  have hmap : Set.MapsTo (fun i : ℕ => 2*i) (bad : Set ℕ) ((A ∪ B : Finset ℕ) : Set ℕ) := by
    intro i hi
    obtain ⟨hij, hbad⟩ := mem_filter.mp (show i ∈ bad from hi)
    obtain ⟨hil, hiu⟩ := mem_Ico.mp hij
    have hm : 2*i ≤ N := by dsimp [N]; omega
    have hm1 : 1 ≤ 2*i := by omega
    by_contra hnot
    have hnot' : 2*i ∉ A ∪ B := hnot
    have ha : 2*i ∉ A := fun h => hnot' (mem_union_left _ h)
    have hb : 2*i ∉ B := fun h => hnot' (mem_union_right _ h)
    have hmi : ‖minor N (bigCut N) (2*i)‖ < s*N := lt_of_not_ge (fun h =>
      ha (mem_filter.mpr ⟨mem_range.mpr (by omega), h⟩))
    have hta : tail H N (2*i) < s := lt_of_not_ge (fun h =>
      hb (mem_filter.mpr ⟨mem_Icc.mpr ⟨hm1,hm⟩, h⟩))
    obtain ⟨hcm, hmov, hsm, _⟩ := hK (2*i) (by omega)
    have hf := signed_floor hs hm (by dsimp [N]; omega) hsm hsepN
      (hcm _ (by simp)) (hcutN _ (by simp)) hmov (hfixN _) hmi.le hta.le
    have : (j:ℝ) ≤ i := by exact_mod_cast hil
    have hei := mul_le_mul_of_nonneg_left this he.le
    dsimp only [s] at hf
    push_cast at hbad
    rw [hNj] at hf
    nlinarith only [hf,hbad,hei,mul_nonneg he.le (Nat.cast_nonneg (α:=ℝ) j)]
  have hn : bad.card ≤ A.card+B.card :=
    (card_le_card_of_injOn (fun i : ℕ => 2*i) hmap (fun a _ b _ hab => by dsimp at hab; omega)).trans
      (card_union_le ..)
  have hn' : (bad.card : ℝ) ≤ (A.card : ℝ) + (B.card : ℝ) := by exact_mod_cast hn
  change dist ((bad.card:ℝ)/j) 0 < r
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)]
  have hjpos : (0:ℝ)<j := by exact_mod_cast (show 0<j by omega)
  apply (div_lt_iff₀ hjpos).2
  rw [hNj] at hA hB
  dsimp only [ξ] at hA hB
  nlinarith only [hn',hA,hB,mul_pos hr hjpos]

end
end MovingBulk

theorem Conjectures.Goldbach.BulkSignedExceptionDensity :
    let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let low := fun (n k : ℕ) => if k^3≤n then w k else 0; let high := fun (n k : ℕ) => w k-low n k; let I := fun (n:ℕ) (a b:ℕ→ℝ) => intervalIntegral (fun t => (arcs n)ᶜ.indicator (fun u => S n a u*S n b u*E (-(n:ℝ)*u)) t) (0:ℝ) 1 MeasureTheory.volume; ∀ e : ℝ, 0 < e → Filter.Tendsto (fun j : ℕ => (((Finset.Ico j (2*j)).filter (fun i => (I (2*i) (high (2*i)) (high (2*i))).re < -(e*(2*i:ℕ)))).card : ℝ) / j) Filter.atTop (nhds (0:ℝ)) := by
  exact MovingBulk.signed_density
