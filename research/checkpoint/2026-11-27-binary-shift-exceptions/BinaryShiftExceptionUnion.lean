import Mathlib
import Conjectures.Goldbach.B13BilateralVaughanReduction
import Conjectures.Goldbach.EstermannAlmostAllPolylog
import Conjectures.Goldbach.MaskedPrimeCutoffLoss
import PEqualNP.Outside.L_goldbach_central_positive_density
import PEqualNP.Outside.L_goldbach_continuous_parseval
import PEqualNP.Outside.L_goldbach_frontier_no_siegel_zero
import PEqualNP.Outside.L_goldbach_frontier_uncond_deep_second_moment
import PEqualNP.Outside.L_goldbach_grh_goldbach_exception_density

-- Adapted from the Apache-2.0 proof of
-- Conjectures.Goldbach.DeepThreeQuartersExceptionalZeroCriterion
-- https://github.com/CGandGameEngineLearner/goldbach-proofs/pull/3316
-- Reuse the common analytic declarations from the verified real-zero-gap module.
-- The declarations below supply the explicit formula on the major arcs.

section

/-!
Rational-arc explicit formula with signed zero multiplicities. An average
over contour abscissae bounds the left edge using local zero counts and an
integrable product kernel. The major-arc width permits a real-part cutoff
of 5/8. Summing the oscillatory tails lowers the height cutoff on each
dyadic block. Finite character inversion recovers the prime sum.

The analytic growth, Jensen disk, logarithmic derivative and rectangle
residue estimates are adapted from DNZJSJ, goldbach-proofs PR #2486,
commit f3613cf846dfb3e7fe7d04fe6ce51c6ee25e7d4f (Apache-2.0).
The Mellin window and inversion use the same integer endpoints as the
conditional three-quarters proof. The right-half count, shared edge
selection and two-sided truncation estimate below do not use Dirichlet GRH.
The per-ordinate oscillatory bounds are from 34245621, PR #2511, at
cba708bd00210b8e17a7f7f9d5e48b74599f48c5. The rational-approximation and main-term estimates
are adapted from Esythium, PR #2512 at 9117b0e8465c7323ed09c4673b5ceac9a7ef8118.
-/

section
namespace GoldbachSmoothing

open Complex DirichletCharacter MeasureTheory
open scoped BigOperators

noncomputable section

def twistedCoefficient {q : ℕ} (χ : DirichletCharacter ℂ q) : ℕ → ℂ :=
  (fun n : ℕ => χ (n : ZMod q)) * (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ))

theorem twistedCoefficient_zero {q : ℕ} (χ : DirichletCharacter ℂ q) :
    twistedCoefficient χ 0 = 0 := by
  simp [twistedCoefficient]

theorem LSeries_twistedCoefficient_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 < s.re) :
    LSeries (twistedCoefficient χ) s = -logDeriv (LFunction χ) s := by
  rw [twistedCoefficient, χ.LSeries_twist_vonMangoldt_eq hs,
    ← χ.deriv_LFunction_eq_deriv_LSeries hs, ← χ.LFunction_eq_LSeries hs]
  simp only [logDeriv, Pi.div_apply, neg_div]
end
end GoldbachSmoothing
open scoped BigOperators Topology
open Asymptotics Complex Filter Finset MeasureTheory Set

noncomputable section

namespace Goldbach

/-- The same anchor bound after multiplication by the factor that cancels a pole at one. -/
theorem one_fourth_le_norm_mul_sub_one_LFunction_anchor {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (t : ℝ) :
    (1 / 4 : ℝ) ≤ ‖((⟨2, t⟩ : ℂ) - 1) * χ.LFunction (⟨2, t⟩ : ℂ)‖ := by
  have hFactor : (1 : ℝ) ≤ ‖(⟨2, t⟩ : ℂ) - 1‖ := by
    have h := Complex.re_le_norm ((⟨2, t⟩ : ℂ) - 1)
    change (2 : ℝ) - 1 ≤ _ at h
    linarith only [h]
  rw [norm_mul]
  exact (one_fourth_le_norm_LFunction_anchor χ t).trans
    (le_mul_of_one_le_left (norm_nonneg _) hFactor)

end Goldbach

namespace Goldbach

open Metric Set MeromorphicOn

/-- The zeros in the open critical strip at height at most one from `t`. -/
def criticalZeroSlice (f : ℂ → ℂ) (t : ℝ) : Set ℂ :=
  {z | 0 < z.re ∧ z.re < 1 ∧ |z.im - t| ≤ 1 ∧ f z = 0}

private theorem jensen_mem_inner {z : ℂ} {t : ℝ} (hre : z.re = 1 / 2)
    (him : |z.im - t| ≤ 1) : z ∈ closedBall (⟨2, t⟩ : ℂ) (29 / 16) := by
  rw [mem_closedBall, dist_eq_norm]
  apply (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 29 / 16)).mp
  have himSq : (z.im - t) ^ 2 ≤ 1 := by
    simpa only [sq_abs, one_pow] using
      (sq_le_sq₀ (abs_nonneg _) zero_le_one).mpr him
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, hre]
  nlinarith only [himSq]

private theorem jensen_re_of_mem_outer {z : ℂ} {t : ℝ}
    (hz : z ∈ closedBall (⟨2, t⟩ : ℂ) (15 / 8)) : 1 / 8 ≤ z.re := by
  rw [mem_closedBall, dist_eq_norm] at hz
  have hre := (Complex.abs_re_le_norm (z - (⟨2, t⟩ : ℂ))).trans hz
  simp only [Complex.sub_re] at hre
  linarith only [(abs_le.mp hre).1]

private theorem jensen_norm_of_mem_outer {z : ℂ} {t : ℝ}
    (hz : z ∈ closedBall (⟨2, t⟩ : ℂ) (15 / 8)) : 1 + ‖z‖ ≤ 3 * (2 + |t|) := by
  rw [mem_closedBall, dist_eq_norm] at hz
  let center : ℂ := ⟨2, t⟩
  have hcenter : ‖center‖ ≤ 2 + |t| := by
    simpa [center] using Complex.norm_le_abs_re_add_abs_im center
  have hnorm : ‖z‖ ≤ ‖z - center‖ + ‖center‖ := by
    simpa only [sub_add_cancel] using norm_add_le (z - center) center
  linarith only [hz, hcenter, hnorm, abs_nonneg t]

private theorem jensen_analytic_outer {f : ℂ → ℂ} {t : ℝ}
    (hAnalytic : AnalyticOnNhd ℂ f {z | 0 < z.re}) :
    AnalyticOnNhd ℂ f (closedBall (⟨2, t⟩ : ℂ) (15 / 8)) := by
  intro z hz
  exact hAnalytic z (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 8)
    (jensen_re_of_mem_outer hz))

/-- For a holomorphic function with fixed growth and anchor bounds, the total divisor mass
in the closed disk of radius `29 / 16` about `2 + it` grows at most logarithmically. -/
theorem jensen_diskDivisor_bound {A b : ℝ} (hA : 0 < A) (hb : 0 < b) :
    ∃ K : ℝ, 0 < K ∧ ∀ (q : ℕ) (f : ℂ → ℂ) (t : ℝ), 0 < q →
      AnalyticOnNhd ℂ f {z | 0 < z.re} →
      (∀ z : ℂ, 1 / 8 ≤ z.re → ‖f z‖ ≤ A * (q : ℝ) * (1 + ‖z‖) ^ 2) →
      b ≤ ‖f (⟨2, t⟩ : ℂ)‖ →
      ((∑ᶠ z : ℂ, divisor f (closedBall (⟨2, t⟩ : ℂ) (29 / 16)) z : ℤ) : ℝ) ≤
        K * Real.log (2 * (q : ℝ) * (2 + |t|)) := by
  classical
  let r : ℝ := 29 / 16
  let R : ℝ := 15 / 8
  have hr : 0 < r := by norm_num [r]
  have hR : 0 < R := by norm_num [R]
  have hrR : r < R := by norm_num [r, R]
  let B : ℝ := 1 + 9 * A
  let bMin : ℝ := min 1 b
  let D : ℝ := B / bMin
  let logRatio : ℝ := Real.log (R / r)
  let logFactor : ℝ := 2 + Real.log D / Real.log 2
  have hB : 1 ≤ B := by dsimp [B]; linarith only [hA]
  have hbMin : 0 < bMin := lt_min zero_lt_one hb
  have hD : 1 ≤ D := by
    apply (le_div_iff₀ hbMin).mpr
    simpa only [one_mul] using (min_le_left (1 : ℝ) b).trans hB
  have hlogD : 0 ≤ Real.log D := Real.log_nonneg hD
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogRatio : 0 < logRatio := Real.log_pos ((one_lt_div hr).mpr hrR)
  have hlogCoeff : 0 ≤ Real.log D / Real.log 2 := div_nonneg hlogD hlog2.le
  have hlogFactor : 0 < logFactor := by dsimp [logFactor]; linarith only [hlogCoeff]
  refine ⟨logFactor / logRatio, div_pos hlogFactor hlogRatio, ?_⟩
  intro q f t hq hAnalytic hGrowth hAnchor
  let c : ℂ := ⟨2, t⟩
  let v : ℝ := 2 + |t|
  let w : ℝ := 2 * (q : ℝ) * v
  let M : ℝ := B * w ^ 2
  have hq₁ : (1 : ℝ) ≤ q := by exact_mod_cast Nat.succ_le_of_lt hq
  have hq₀ : (0 : ℝ) ≤ q := by positivity
  have hv : 2 ≤ v := by dsimp [v]; linarith only [abs_nonneg t]
  have hw : 2 ≤ w := by
    have hq₂ : (1 : ℝ) ≤ 2 * (q : ℝ) := by linarith only [hq₁]
    exact hv.trans (le_mul_of_one_le_left (by linarith only [hv]) hq₂)
  have hw₀ : 0 < w := by linarith only [hw]
  have hM : 1 ≤ M := by
    have hWs : 1 ≤ w ^ 2 := by nlinarith only [hw, sq_nonneg (w - 2)]
    exact one_le_mul_of_one_le_of_one_le hB hWs
  have hAnchorMin : bMin ≤ ‖f c‖ := (min_le_right 1 b).trans hAnchor
  have hFpos : 0 < ‖f c‖ := hbMin.trans_le hAnchorMin
  have hFc : f c ≠ 0 := norm_pos_iff.mp hFpos
  have hOuter : AnalyticOnNhd ℂ f (closedBall c R) := by
    exact jensen_analytic_outer hAnalytic
  have hBound : ∀ z ∈ closedBall c R, ‖f z‖ ≤ M := by
    intro z hz
    have hnorm : 1 + ‖z‖ ≤ 3 * v := jensen_norm_of_mem_outer hz
    have hnormSq : (1 + ‖z‖) ^ 2 ≤ (3 * v) ^ 2 :=
      (sq_le_sq₀ (by positivity) (by linarith only [hv])).mpr hnorm
    have hqSq : (q : ℝ) ≤ (2 * (q : ℝ)) ^ 2 := by
      have hqSelf : (q : ℝ) ≤ (q : ℝ) * (q : ℝ) := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hq₁ hq₀
      nlinarith only [hqSelf, sq_nonneg (q : ℝ)]
    have hqvSq : (q : ℝ) * v ^ 2 ≤ w ^ 2 := calc
      _ ≤ (2 * (q : ℝ)) ^ 2 * v ^ 2 := mul_le_mul_of_nonneg_right hqSq (sq_nonneg v)
      _ = _ := by dsimp [w]; ring
    calc
      ‖f z‖ ≤ A * (q : ℝ) * (1 + ‖z‖) ^ 2 := hGrowth z (jensen_re_of_mem_outer hz)
      _ ≤ A * (q : ℝ) * (3 * v) ^ 2 := mul_le_mul_of_nonneg_left hnormSq (mul_nonneg hA.le hq₀)
      _ = 9 * A * ((q : ℝ) * v ^ 2) := by ring
      _ ≤ 9 * A * w ^ 2 := mul_le_mul_of_nonneg_left hqvSq (by positivity)
      _ ≤ M := mul_le_mul_of_nonneg_right (by dsimp [B]; linarith) (sq_nonneg w)
  have hJensen : ((∑ᶠ z : ℂ, divisor f (closedBall c |r|) z : ℤ) : ℝ) ≤
      Real.log (M / ‖f c‖) / logRatio := by
    have hOuterAbs : AnalyticOnNhd ℂ f (closedBall c |R|) := by simpa [abs_of_pos hR] using hOuter
    have hCircle : ∀ z ∈ sphere c |R|, ‖f z‖ ≤ M := by
      intro z hz
      apply hBound z
      simpa only [abs_of_pos hR] using sphere_subset_closedBall hz
    exact AnalyticOnNhd.sum_divisor_le (r := r) (R := R) (M := M)
      (by simpa only [abs_of_pos hr] using hr)
      (by simpa only [abs_of_pos hr, abs_of_pos hR] using hrR)
      hM hOuterAbs hFc hCircle
  have hLogW : Real.log 2 ≤ Real.log w := Real.log_le_log (by norm_num) hw
  have hLogBound : Real.log (M / ‖f c‖) ≤ logFactor * Real.log w := by
    have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
    have hDivBound : M / ‖f c‖ ≤ D * w ^ 2 := calc
      _ ≤ M / bMin := div_le_div_of_nonneg_left hMpos.le hbMin hAnchorMin
      _ = _ := by dsimp [M, D]; ring
    calc
      _ ≤ Real.log (D * w ^ 2) := Real.log_le_log (div_pos hMpos hFpos) hDivBound
      _ = 2 * Real.log w + Real.log D := by
        rw [Real.log_mul (by linarith only [hD]) (pow_ne_zero _ hw₀.ne'), Real.log_pow]
        norm_num [add_comm]
      _ = 2 * Real.log w + (Real.log D / Real.log 2) * Real.log 2 := by
        rw [div_mul_cancel₀ _ hlog2.ne']
      _ ≤ 2 * Real.log w + (Real.log D / Real.log 2) * Real.log w :=
        (add_le_add le_rfl (mul_le_mul_of_nonneg_left hLogW hlogCoeff))
      _ = _ := by dsimp [logFactor]; ring
  change ((∑ᶠ z : ℂ, divisor f (closedBall c r) z : ℤ) : ℝ) ≤
    (logFactor / logRatio) * Real.log w
  calc
    _ = ((∑ᶠ z : ℂ, divisor f (closedBall c |r|) z : ℤ) : ℝ) :=
      congrArg (fun U : Set ℂ ↦ ((∑ᶠ z : ℂ, divisor f U z : ℤ) : ℝ))
        (congrArg (closedBall c) (abs_of_pos hr).symm)
    _ ≤ Real.log (M / ‖f c‖) / logRatio := hJensen
    _ ≤ (logFactor * Real.log w) / logRatio :=
      div_le_div_of_nonneg_right hLogBound hlogRatio.le
    _ = _ := by ring

/-- A fixed polynomial growth bound and a positive anchor bound give a uniform logarithmic
bound on the number of critical-strip zeros, counted with multiplicity, in each height slice.
The zero-line hypothesis places the entire slice in the smaller Jensen disk. -/
theorem jensen_criticalZeroSlice_bound {A b : ℝ} (hA : 0 < A) (hb : 0 < b) :
    ∃ K : ℝ, 0 < K ∧ ∀ (q : ℕ) (f : ℂ → ℂ) (t : ℝ), 0 < q →
      AnalyticOnNhd ℂ f {z | 0 < z.re} →
      (∀ z : ℂ, 1 / 8 ≤ z.re → ‖f z‖ ≤ A * (q : ℝ) * (1 + ‖z‖) ^ 2) →
      b ≤ ‖f (⟨2, t⟩ : ℂ)‖ →
      (∀ z : ℂ, 0 < z.re → z.re < 1 → f z = 0 → z.re = 1 / 2) →
      (criticalZeroSlice f t).Finite ∧
        (∑ᶠ z : ℂ, (criticalZeroSlice f t).indicator
          (fun z ↦ (analyticOrderNatAt f z : ℝ)) z) ≤
          K * Real.log (2 * (q : ℝ) * (2 + |t|)) := by
  classical
  obtain ⟨K, hK, hDiskBound⟩ := jensen_diskDivisor_bound hA hb
  refine ⟨K, hK, ?_⟩
  intro q f t hq hAnalytic hGrowth hAnchor hLine
  let c : ℂ := ⟨2, t⟩
  let r : ℝ := 29 / 16
  let R : ℝ := 15 / 8
  have hFc : f c ≠ 0 := norm_pos_iff.mp (hb.trans_le hAnchor)
  have hCenter : c ∈ closedBall c R := mem_closedBall_self (by norm_num [R])
  have hOuter : AnalyticOnNhd ℂ f (closedBall c R) := jensen_analytic_outer hAnalytic
  have hInnerSubset : closedBall c r ⊆ closedBall c R :=
    closedBall_subset_closedBall (by norm_num [r, R])
  have hInner : AnalyticOnNhd ℂ f (closedBall c r) := hOuter.mono hInnerSubset
  have hOrderCenter : analyticOrderAt f c ≠ ⊤ := by
    rw [(hOuter c hCenter).analyticOrderAt_eq_zero.mpr hFc]
    exact ENat.zero_ne_top
  let countDivisor : ℂ → ℤ := fun z ↦ divisor f (closedBall c r) z
  let countSlice : ℂ → ℝ := (criticalZeroSlice f t).indicator
    (fun z ↦ (analyticOrderNatAt f z : ℝ))
  have hSliceOrder (z : ℂ) (hz : z ∈ criticalZeroSlice f t) :
      countDivisor z = (analyticOrderNatAt f z : ℤ) ∧ 0 < analyticOrderNatAt f z := by
    have hre := hLine z hz.1 hz.2.1 hz.2.2.2
    have hzInner : z ∈ closedBall c r := jensen_mem_inner hre hz.2.2.1
    have hzOuter : z ∈ closedBall c R := hInnerSubset hzInner
    have hOrder : analyticOrderAt f z ≠ ⊤ := hOuter.analyticOrderAt_ne_top_of_isPreconnected
      isPreconnected_closedBall hCenter hzOuter hOrderCenter
    constructor
    · change divisor f (closedBall c r) z = _
      rw [hInner.divisor_apply hzInner, ← Nat.cast_analyticOrderNatAt hOrder,
        ENat.map_natCast, WithTop.untop₀_coe]
    · apply Nat.pos_of_ne_zero
      intro hZero
      apply (hInner z hzInner).analyticOrderAt_ne_zero.mpr hz.2.2.2
      rw [← Nat.cast_analyticOrderNatAt hOrder, hZero, Nat.cast_zero]
  have hDivFinite : (Function.support countDivisor).Finite :=
    (divisor f (closedBall c r)).finiteSupport (isCompact_closedBall c r)
  have hSliceFinite : (criticalZeroSlice f t).Finite := by
    apply hDivFinite.subset
    intro z hz
    change countDivisor z ≠ 0
    rw [(hSliceOrder z hz).1]
    exact_mod_cast (hSliceOrder z hz).2.ne'
  refine ⟨hSliceFinite, ?_⟩
  have hSliceCountFinite : (Function.support countSlice).Finite := by
    apply hSliceFinite.subset
    intro z hz
    by_contra hNot
    exact hz (Set.indicator_of_notMem hNot _)
  let divisorOverReal : ℂ → ℝ := fun z ↦ (countDivisor z : ℝ)
  have hDivCountFinite : (Function.support divisorOverReal).Finite := by
    apply hDivFinite.subset
    intro z hz
    simpa [Function.mem_support, divisorOverReal] using hz
  change (∑ᶠ z : ℂ, countSlice z) ≤ K * Real.log (2 * (q : ℝ) * (2 + |t|))
  calc
    _ ≤ ∑ᶠ z : ℂ, divisorOverReal z := by
      apply finsum_le_finsum hSliceCountFinite hDivCountFinite
      intro z
      by_cases hz : z ∈ criticalZeroSlice f t
      · simp [countSlice, divisorOverReal, Set.indicator_of_mem hz, (hSliceOrder z hz).1]
      · rw [show countSlice z = 0 from Set.indicator_of_notMem hz _]
        have hNonnegative : (0 : ℤ) ≤ countDivisor z := hInner.divisor_nonneg z
        change (0 : ℝ) ≤ (countDivisor z : ℝ)
        exact_mod_cast hNonnegative
    _ = ((∑ᶠ z : ℂ, countDivisor z : ℤ) : ℝ) :=
      (map_finsum (Int.castRingHom ℝ) hDivFinite).symm
    _ ≤ _ := hDiskBound q f t hq hAnalytic hGrowth hAnchor

end Goldbach

namespace Goldbach

open Complex DirichletCharacter Set

abbrev GRH := ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ),
  0 < s.re → s.re < 1 → LFunction χ s = 0 → s.re = 1 / 2

noncomputable def regularizedL {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) : ℂ → ℂ := by
  classical
  exact if χ = 1 then LFunctionTrivChar₁ q else LFunction χ

noncomputable def principalFlag {q : ℕ} (χ : DirichletCharacter ℂ q) : ℂ := by
  classical
  exact if χ = 1 then 1 else 0

theorem re_lt_one_of_regularizedL_zero {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hz : regularizedL χ s = 0) : s.re < 1 := by
  by_contra! hs
  by_cases hχ : χ = 1
  · subst χ
    have hz' : LFunctionTrivChar₁ q s = 0 := by simpa [regularizedL] using hz
    by_cases hs1 : s = 1
    · exact LFunctionTrivChar₁_apply_one_ne_zero q (hs1 ▸ hz')
    · rw [LFunctionTrivChar₁, Function.update_of_ne hs1, mul_eq_zero] at hz'
      exact LFunction_ne_zero_of_one_le_re 1 (Or.inr hs1) hs
        (hz'.resolve_left (sub_ne_zero.mpr hs1))
  · exact LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) hs (by simpa [regularizedL, hχ] using hz)

theorem analytic_regularizedL {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    AnalyticOnNhd ℂ (regularizedL χ) univ := by
  intro s _
  by_cases hχ : χ = 1
  · simpa only [regularizedL, hχ, ite_true] using (differentiable_LFunctionTrivChar₁ q).analyticAt s
  · simpa only [regularizedL, hχ, ite_false] using (differentiable_LFunction hχ).analyticAt s

/-- Inducing a character to a larger modulus preserves the zeros and their
multiplicities in the positive half-plane away from the pole. -/
theorem regularizedL_changeLevel_zero_and_order {m q : ℕ} [NeZero m] [NeZero q]
    (hmq : m ∣ q) (χ : DirichletCharacter ℂ m) (s : ℂ) (hRe : 0 < s.re) (hs : s ≠ 1) :
    (regularizedL (changeLevel hmq χ) s = 0 ↔ regularizedL χ s = 0) ∧
      analyticOrderNatAt (regularizedL (changeLevel hmq χ)) s =
        analyticOrderNatAt (regularizedL χ) s := by
  let E := fun z : ℂ => ∏ p ∈ q.primeFactors, (1 - χ (p : ZMod m) * (p : ℂ) ^ (-z))
  have hE : E s ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro p hp
    have hprime := Nat.prime_of_mem_primeFactors hp
    have hpNorm : ‖(p : ℂ) ^ (-s)‖ < 1 := by
      rw [Complex.norm_natCast_cpow_of_pos hprime.pos, Complex.neg_re]
      exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hprime.one_lt) (neg_lt_zero.mpr hRe)
    have hnorm : ‖χ (p : ZMod m) * (p : ℂ)^(-s)‖ < 1 := by
      rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one _)).trans_lt hpNorm
    intro hzero
    rw [(sub_eq_zero.mp hzero).symm, norm_one] at hnorm
    exact (lt_irrefl 1) hnorm
  have hEAnalytic : AnalyticAt ℂ E s := by
    apply Differentiable.analyticAt
    refine Differentiable.fun_finsetProd (fun p hp => ?_)
    have hp₀ : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.prime_of_mem_primeFactors hp).ne_zero
    exact (differentiable_const (c := (1 : ℂ))).sub
      ((differentiable_neg.const_cpow (Or.inl hp₀)).const_mul (χ (p : ZMod m)))
  have hreg {k : ℕ} [NeZero k] (ψ : DirichletCharacter ℂ k) (z : ℂ) (hz : z ≠ 1) :
      regularizedL ψ z = (if ψ = 1 then z - 1 else 1) * LFunction ψ z := by
    by_cases hψ : ψ = 1
    · simp only [regularizedL, hψ, ite_true, LFunctionTrivChar₁, Function.update_of_ne hz]
    · simp [regularizedL, hψ]
  have hEq : regularizedL (changeLevel hmq χ) =ᶠ[𝓝 s] (regularizedL χ) * E := by
    filter_upwards [isOpen_ne.mem_nhds hs] with z hz
    rw [Pi.mul_apply, hreg _ _ hz, hreg _ _ hz, LFunction_changeLevel hmq χ (Or.inr hz)]
    simp only [changeLevel_eq_one_iff hmq]
    exact (mul_assoc ..).symm
  have hpoint : regularizedL (changeLevel hmq χ) s = regularizedL χ s * E s :=
    hEq.self_of_nhds
  refine ⟨by rw [hpoint, mul_eq_zero]; simp [hE],?_⟩
  have horder :
      analyticOrderAt (regularizedL (changeLevel hmq χ)) s = analyticOrderAt (regularizedL χ) s := by
    rw [analyticOrderAt_congr hEq, analyticOrderAt_mul (analytic_regularizedL χ s (mem_univ _)) hEAnalytic,
      hEAnalytic.analyticOrderAt_eq_zero.mpr hE, add_zero]
  exact congrArg ENat.toNat horder

theorem regularizedL_zero_line {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hGRH : GRH)
    {s : ℂ} (hs : 0 < s.re) (hz : regularizedL χ s = 0) : s.re = 1 / 2 := by
  by_cases hχ : χ = 1
  · subst χ
    have hzero : LFunctionTrivChar₁ q s = 0 := by simpa only [regularizedL, eq_self, ite_true] using hz
    by_cases hs1 : s = 1
    · subst s
      exact False.elim (LFunctionTrivChar₁_apply_one_ne_zero q hzero)
    rw [LFunctionTrivChar₁, Function.update_of_ne hs1, mul_eq_zero] at hzero
    have hL : LFunction (1 : DirichletCharacter ℂ q) s = 0 :=
      hzero.resolve_left (sub_ne_zero.mpr hs1)
    have hslt : s.re < 1 := lt_of_not_ge fun hge =>
      LFunction_ne_zero_of_one_le_re (1 : DirichletCharacter ℂ q) (Or.inr hs1) hge hL
    exact hGRH q 1 s hs hslt hL
  · have hL : LFunction χ s = 0 := by simpa only [regularizedL, hχ, ite_false] using hz
    have hslt : s.re < 1 := lt_of_not_ge fun hge =>
      LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) hge hL
    exact hGRH q χ s hs hslt hL

theorem norm_regularizedL_anchor {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ) :
    (1 / 4 : ℝ) ≤ ‖regularizedL χ (⟨2, t⟩ : ℂ)‖ := by
  by_cases hχ : χ = 1
  · subst χ
    have hs : (⟨2, t⟩ : ℂ) ≠ 1 := by
      intro h
      have he := congrArg Complex.re h
      norm_num at he
    simp only [regularizedL, eq_self, ite_true]
    rw [LFunctionTrivChar₁, Function.update_of_ne hs]
    exact one_fourth_le_norm_mul_sub_one_LFunction_anchor (1 : DirichletCharacter ℂ q) t
  · simpa only [regularizedL, hχ, ite_false] using one_fourth_le_norm_LFunction_anchor χ t

theorem uniform_dirichlet_zero_slice (hGRH : GRH) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ),
      (criticalZeroSlice (regularizedL χ) t).Finite ∧
        (∑ᶠ z : ℂ, (criticalZeroSlice (regularizedL χ) t).indicator
          (fun z => (analyticOrderNatAt (regularizedL χ) z : ℝ)) z) ≤
          C * Real.log (2 * (q : ℝ) * (2 + |t|)) := by
  obtain ⟨C, hC, hJensen⟩ :=
    jensen_criticalZeroSlice_bound (A := 25) (b := 1 / 4) (by norm_num) (by norm_num)
  refine ⟨C, hC, ?_⟩
  intro q _ χ t
  exact hJensen q (regularizedL χ) t (Nat.pos_of_ne_zero (NeZero.ne q))
    ((analytic_regularizedL χ).mono (subset_univ _))
    (fun s hs => by
      have hg := GoldbachGrhGrowth.norm_regularizedLFunction_le χ hs
      by_cases hχ : χ = 1
      · simpa only [regularizedL, hχ, ite_true] using hg
      · simpa only [regularizedL, hχ, ite_false] using hg)
    (norm_regularizedL_anchor χ t) (fun s hs _ hzero => regularizedL_zero_line χ hGRH hs hzero)

theorem logDeriv_regularizedL_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : s ≠ 1) (hL : LFunction χ s ≠ 0) :
    logDeriv (regularizedL χ) s = logDeriv (LFunction χ) s + principalFlag χ / (s - 1) := by
  by_cases hχ : χ = 1
  · subst χ
    simp only [regularizedL, principalFlag, eq_self, ite_true, logDeriv, Pi.div_apply]
    rw [deriv_LFunctionTrivChar₁_apply_of_ne_one q hs,
      LFunctionTrivChar₁, Function.update_of_ne hs]
    field_simp [sub_ne_zero.mpr hs, hL]
  · simp [regularizedL, principalFlag, hχ]

end Goldbach

open scoped BigOperators Topology
open Complex Filter Metric Set

noncomputable section

namespace Goldbach

open Complex Metric Set
open scoped BigOperators

/-- Uniform logarithmic derivative bound on the right of Re s = 9/20, at a point with a
given positive separation from the zeros of the regularized L-function. -/
theorem norm_logDeriv_regularizedL_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (t σ d : ℝ),
      9 / 20 ≤ σ → σ ≤ 2 → 0 < d →
      (∀ ρ : ℂ, 0 < ρ.re → regularizedL χ ρ = 0 → d ≤ ‖(⟨σ, t⟩ : ℂ) - ρ‖) →
      ‖logDeriv (regularizedL χ) (⟨σ, t⟩ : ℂ)‖ ≤
        C * Real.log (2 * (q : ℝ) * (2 + |t|)) * (1 + d⁻¹) := by
  let R : ℝ := 15 / 8
  let A : ℝ := 130200 / R
  let E : ℝ := (Real.log (12 / 11 : ℝ))⁻¹
  have hR : 0 < R := by norm_num [R]
  have hA : 0 < A := div_pos (by norm_num) hR
  have hE : 0 < E := inv_pos.mpr (Real.log_pos (by norm_num))
  refine ⟨13 * (A + E), mul_pos (by norm_num) (add_pos hA hE), ?_⟩
  intro q _ χ t σ d hσlo hσhi hd hSep
  let f := regularizedL χ
  let c : ℂ := ⟨2, t⟩
  let s : ℂ := ⟨σ, t⟩
  let K : ℝ := 2 + |t|
  let B : ℝ := 900 * (q : ℝ) * K ^ 2
  let L : ℝ := Real.log (2 * (q : ℝ) * K)
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.succ_le_of_lt q.pos_of_neZero
  have hq0 : 0 < (q : ℝ) := zero_lt_one.trans_le hq1
  have hK2 : 2 ≤ K := le_add_of_nonneg_right (abs_nonneg t)
  have hK1 : 1 ≤ K := by linarith
  have hK0 : 0 < K := zero_lt_one.trans_le hK1
  have hB0 : 0 < B := by
    dsimp only [B]
    positivity
  have hB2 : 2 ≤ B := by
    calc
      (2 : ℝ) ≤ 900 * 1 * 1 := by norm_num
      _ ≤ B := mul_le_mul (mul_le_mul_of_nonneg_left hq1 (by norm_num))
        (one_le_pow₀ hK1) zero_le_one (by positivity)
  have hReLower (w : ℂ) (hw : w ∈ closedBall c R) : (1 / 8 : ℝ) ≤ w.re := by
    have hDist := mem_closedBall_iff_norm.mp hw
    have hRe := abs_re_le_norm (w - c)
    rw [sub_re, show c.re = 2 from rfl] at hRe
    have hLower := neg_le_abs (w.re - 2)
    dsimp only [R] at hDist
    linarith
  have hcform : c = (2 : ℂ) + (t : ℂ) * I := by
    apply Complex.ext <;> simp [c, Complex.mul_re, Complex.mul_im]
  have hcnorm : ‖c‖ ≤ K := by
    rw [hcform]
    calc
      _ ≤ ‖(2 : ℂ)‖ + ‖(t : ℂ) * I‖ := norm_add_le _ _
      _ = _ := by simp [K, norm_real, Real.norm_eq_abs]
  have hAnchor : (1 / 4 : ℝ) ≤ ‖f c‖ := norm_regularizedL_anchor χ t
  have hf0 : f c ≠ 0 := norm_pos_iff.mp ((by norm_num : (0 : ℝ) < 1 / 4).trans_le hAnchor)
  have hf : AnalyticOnNhd ℂ f (closedBall c R) := (analytic_regularizedL χ).mono (subset_univ _)
  have hfB (w : ℂ) (hw : w ∈ closedBall c (24 / 25 * R)) : ‖f w‖ ≤ B * ‖f c‖ := by
    have hwBig := closedBall_subset_closedBall (show (24 / 25 : ℝ) * R ≤ R by norm_num [R]) hw
    have hDist := mem_closedBall_iff_norm.mp hwBig
    have hwNorm : 1 + ‖w‖ ≤ 3 * K := by
      dsimp only [R] at hDist
      linarith only [norm_le_norm_sub_add w c, hDist, hcnorm, hK2]
    have hGrowth : ‖f w‖ ≤ 25 * (q : ℝ) * (1 + ‖w‖) ^ 2 := by
      have hRaw := GoldbachGrhGrowth.norm_regularizedLFunction_le χ (hReLower w hwBig)
      by_cases hχ : χ = 1 <;> simpa [f, regularizedL, hχ] using hRaw
    calc
      _ ≤ 25 * (q : ℝ) * (1 + ‖w‖) ^ 2 := hGrowth
      _ ≤ 25 * (q : ℝ) * (3 * K) ^ 2 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hwNorm 2) (by positivity)
      _ = B * (1 / 4 : ℝ) := by
        dsimp only [B]
        ring
      _ ≤ B * ‖f c‖ := mul_le_mul_of_nonneg_left hAnchor hB0.le
  have hS : s ∈ closedBall c (83 / 100 * R) := by
    have hSub : s - c = ((σ - 2 : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [s, c]
    rw [mem_closedBall_iff_norm, hSub, norm_real, Real.norm_eq_abs,
      abs_of_nonpos (sub_nonpos.mpr hσhi)]
    dsimp only [R]
    linarith
  have hS0 : f s ≠ 0 := by
    intro hsz
    have hs : 0 < s.re := (by norm_num : (0 : ℝ) < 9 / 20).trans_le hσlo
    have h := hSep s hs hsz
    rw [sub_self, norm_zero] at h
    exact hd.not_ge h
  obtain ⟨Z, hZ, hMass, hApprox⟩ :=
    GoldbachGrhLogDerivative.logDeriv_partial_fraction_disk hR hf hf0 hB2 hfB
  have hTerms : ‖∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) / (s - ρ)‖ ≤
      (∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℝ)) * d⁻¹ := by
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun ρ hρ => ?_
    have hZmem : ρ ∈ (↑Z : Set ℂ) := hρ
    rw [hZ] at hZmem
    have hρLarge := closedBall_subset_closedBall (show (22 / 25 : ℝ) * R ≤ R by norm_num [R])
      hZmem.1
    have hρPos := (by norm_num : (0 : ℝ) < 1 / 8).trans_le (hReLower ρ hρLarge)
    have hρdist : d ≤ ‖s - ρ‖ := hSep ρ hρPos hZmem.2
    have hRecip : ‖s - ρ‖⁻¹ ≤ d⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le hd hρdist
    rw [norm_div, Complex.norm_natCast, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hRecip (Nat.cast_nonneg _)
  have hLFormula : L = Real.log 2 + Real.log (q : ℝ) + Real.log K := by
    dsimp only [L]
    rw [Real.log_mul (by positivity) hK0.ne', Real.log_mul (by norm_num) hq0.ne']
  have hBLFormula : Real.log B = Real.log 900 + Real.log (q : ℝ) + 2 * Real.log K := by
    dsimp only [B]
    rw [Real.log_mul (by positivity) (pow_ne_zero _ hK0.ne'),
      Real.log_mul (by norm_num) hq0.ne', Real.log_pow]
    norm_num
  have hLog900 : Real.log 900 ≤ 10 * Real.log 2 := by
    calc
      _ ≤ Real.log ((2 : ℝ) ^ (10 : ℕ)) := Real.log_le_log (by norm_num) (by norm_num)
      _ = _ := by
        rw [Real.log_pow]
        norm_num
  have hLPos : 0 < L := by
    rw [hLFormula]
    linarith only [Real.log_nonneg hq1, Real.log_nonneg hK1, Real.log_pos (by norm_num : (1 : ℝ) < 2)]
  have hScaleLog : Real.log B ≤ 13 * L := by
    rw [hBLFormula, hLFormula]
    linarith only [hLog900, Real.log_nonneg hq1, Real.log_nonneg hK1,
      Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]
  have hRecip0 : 0 ≤ d⁻¹ := inv_nonneg.mpr hd.le
  have hBudget : A + E * d⁻¹ ≤ (A + E) * (1 + d⁻¹) := by
    nlinarith only [hE.le, mul_nonneg hA.le hRecip0]
  have hMass' := mul_le_mul_of_nonneg_right hMass hRecip0
  change ‖logDeriv f s‖ ≤ 13 * (A + E) * L * (1 + d⁻¹)
  calc
    _ ≤ ‖logDeriv f s - ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) / (s - ρ)‖ +
        ‖∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) / (s - ρ)‖ := norm_le_norm_sub_add _ _
    _ ≤ A * Real.log B + (Real.log B / Real.log (12 / 11)) * d⁻¹ :=
      (add_le_add (hApprox s hS hS0) (hTerms.trans hMass'))
    _ = Real.log B * (A + E * d⁻¹) := by
      dsimp only [E]
      rw [div_eq_mul_inv]
      ring
    _ ≤ (13 * L) * (A + E * d⁻¹) := mul_le_mul_of_nonneg_right hScaleLog (by positivity)
    _ ≤ (13 * L) * ((A + E) * (1 + d⁻¹)) := mul_le_mul_of_nonneg_left hBudget (by positivity)
    _ = _ := by ring

end Goldbach

namespace Goldbach

/-- A unit interval contains a height separated by `1 / (2 * (1 + S.card))`
from all ordinates in a finite family. -/
theorem exists_goodHeight {α : Type*} (S : Finset α) (ordinate : α → ℝ) (T : ℝ) :
    ∃ u ∈ Set.Icc T (T + 1),
      ∀ a ∈ S, (1 : ℝ) / (2 * (1 + (S.card : ℝ))) ≤ |u - ordinate a| := by
  classical
  let den : ℝ := 1 + (S.card : ℝ)
  let gap : ℝ := 1 / (2 * den)
  let grid (j : Fin (S.card + 1)) : ℝ := T + (j.val : ℝ) / den
  have hDen : 0 < den := by dsimp [den]; positivity
  have hGrid (j : Fin (S.card + 1)) : grid j ∈ Set.Icc T (T + 1) := by
    have hj : (j.val : ℝ) ≤ S.card := by exact_mod_cast Nat.le_of_lt_succ j.isLt
    have hLower : 0 ≤ (j.val : ℝ) / den := div_nonneg (by positivity) hDen.le
    have hUpper : (j.val : ℝ) / den ≤ 1 := by
      apply (div_le_one hDen).mpr
      dsimp [den]
      linarith only [hj]
    exact ⟨by dsimp [grid]; linarith only [hLower], add_le_add le_rfl hUpper⟩
  have hGridGap {j k : Fin (S.card + 1)} (hjk : j ≠ k) :
      gap + gap ≤ |grid j - grid k| := by
    have hNat : j.val ≠ k.val := fun heq ↦ hjk (Fin.ext heq)
    have hInt : (j.val : ℤ) ≠ (k.val : ℤ) := by exact_mod_cast hNat
    have hAbsInt : (1 : ℤ) ≤ |(j.val : ℤ) - (k.val : ℤ)| :=
      Int.one_le_abs (sub_ne_zero.mpr hInt)
    have hAbs : (1 : ℝ) ≤ |(j.val : ℝ) - (k.val : ℝ)| := by exact_mod_cast hAbsInt
    have hGridSub : grid j - grid k = ((j.val : ℝ) - (k.val : ℝ)) / den := by
      dsimp [grid]
      ring
    calc
      gap + gap = 1 / den := by
        dsimp [gap]
        field_simp [hDen.ne']
        norm_num
      _ ≤ |(j.val : ℝ) - (k.val : ℝ)| / den := div_le_div_of_nonneg_right hAbs hDen.le
      _ = |grid j - grid k| := by rw [hGridSub, abs_div, abs_of_pos hDen]
  by_contra hNoGood
  have hBad (j : Fin (S.card + 1)) : ∃ a : S, |grid j - ordinate a| < gap := by
    by_contra hNoBad
    apply hNoGood
    refine ⟨grid j, hGrid j, ?_⟩
    intro a ha
    exact le_of_not_gt (fun h ↦ hNoBad ⟨⟨a, ha⟩, h⟩)
  let badAt (j : Fin (S.card + 1)) : S := (hBad j).choose
  have hBadAt (j : Fin (S.card + 1)) : |grid j - ordinate (badAt j)| < gap :=
    (hBad j).choose_spec
  have hInjective : Function.Injective badAt := by
    intro j k hEqual
    by_contra hDifferent
    have hPair : |grid j - ordinate (badAt j)| + |grid k - ordinate (badAt j)| < gap + gap :=
      (add_lt_add (hBadAt j) (by simpa only [hEqual] using hBadAt k))
    have hTri : |grid j - grid k| ≤
        |grid j - ordinate (badAt j)| + |grid k - ordinate (badAt j)| := by
      simpa only [abs_sub_comm (ordinate (badAt j)) (grid k)] using
        abs_sub_le (grid j) (ordinate (badAt j)) (grid k)
    exact not_lt_of_ge (hGridGap hDifferent) (hTri.trans_lt hPair)
  have hCard : S.card + 1 ≤ S.card := by
    simpa only [Fintype.card_fin, Fintype.card_coe] using
      Fintype.card_le_of_injective badAt hInjective
  omega
end Goldbach
namespace Goldbach

open Complex Set

noncomputable section

def logHeight (q : ℕ) (t : ℝ) : ℝ := Real.log (2 * (q : ℝ) * (2 + |t|))

def contourLog {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (z : ℂ) : ℂ :=
  -logDeriv (regularizedL χ) z + principalFlag χ / (z - 1)

def UniformDirichletLogDerivative (C : ℝ) : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (σ t d : ℝ),
    σ ∈ Icc (9 / 20 : ℝ) 2 → 0 < d →
    (∀ ρ : ℂ, 0 < ρ.re → regularizedL χ ρ = 0 → d ≤ ‖((σ : ℂ) + (t : ℂ) * I) - ρ‖) →
    ‖logDeriv (regularizedL χ) ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C * logHeight q t * (1 + d⁻¹)

theorem logHeight_ge_one (q : ℕ) [NeZero q] (t : ℝ) : 1 ≤ logHeight q t := by
  have hq : 1 ≤ (q : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne q))
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith
  have hlog4 : 1 ≤ Real.log 4 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    linarith
  have harg : (4 : ℝ) ≤ 2 * (q : ℝ) * (2 + |t|) := calc
    _ ≤ 2 * (1 : ℝ) * (2 + |t|) := by linarith [abs_nonneg t]
    _ ≤ _ := by gcongr
  exact hlog4.trans (Real.log_le_log (by norm_num) harg)

end
end Goldbach
namespace Goldbach

open Complex DirichletCharacter MeromorphicOn Set

/-- The regularized Dirichlet L-function is nonzero at one. -/
theorem regularizedL_ne_zero_at_one {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    regularizedL χ 1 ≠ 0 := by
  by_cases hχ : χ = 1
  · simpa only [regularizedL, hχ, ite_true] using LFunctionTrivChar₁_apply_one_ne_zero q
  · simpa only [regularizedL, hχ, ite_false] using LFunction_apply_one_ne_zero hχ

/-- The anchor gives finite order of the regularized L-function at every complex point. -/
theorem regularizedL_analyticOrder_ne_top {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (z : ℂ) : analyticOrderAt (regularizedL χ) z ≠ ⊤ := by
  let c : ℂ := ⟨2, 0⟩
  have hC : regularizedL χ c ≠ 0 := norm_pos_iff.mp
    ((by norm_num : (0 : ℝ) < 1 / 4).trans_le (norm_regularizedL_anchor χ 0))
  have hOrderC : analyticOrderAt (regularizedL χ) c ≠ ⊤ := by
    rw [((analytic_regularizedL χ) c (mem_univ c)).analyticOrderAt_eq_zero.mpr hC]
    exact ENat.zero_ne_top
  exact (analytic_regularizedL χ).analyticOrderAt_ne_top_of_isPreconnected
    isPreconnected_univ (mem_univ c) (mem_univ z) hOrderC

theorem regularizedL_analyticOrderNatAt_pos_iff {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (z : ℂ) :
    0 < analyticOrderNatAt (regularizedL χ) z ↔ regularizedL χ z = 0 := by
  constructor
  · intro h
    exact apply_eq_zero_of_analyticOrderNatAt_ne_zero h.ne'
  · intro h
    apply Nat.pos_of_ne_zero
    intro hzero
    apply ((analytic_regularizedL χ) z (mem_univ z)).analyticOrderAt_ne_zero.mpr h
    rw [← Nat.cast_analyticOrderNatAt (regularizedL_analyticOrder_ne_top χ z), hzero, Nat.cast_zero]

theorem regularizedL_divisor_apply {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {U : Set ℂ} {z : ℂ} (hz : z ∈ U) :
    divisor (regularizedL χ) U z = (analyticOrderNatAt (regularizedL χ) z : ℤ) := by
  rw [((analytic_regularizedL χ).mono (subset_univ U)).divisor_apply hz,
    ← Nat.cast_analyticOrderNatAt (regularizedL_analyticOrder_ne_top χ z),
    ENat.map_natCast, WithTop.untop₀_coe]
end Goldbach
open Complex Set MeasureTheory
open scoped BigOperators Interval

namespace Goldbach

/- For a reference statement, see PrimeNumberTheoremAnd's ResidueCalcOnRectangles.lean at
   2c476fa6441c607096d93c8fc7ac0a227a655dae, licensed under Apache 2.0.
   The argument below uses the complex logarithm on each side of the rectangle. -/

/-- Counterclockwise boundary integral for the rectangle with real sides a and b
and imaginary sides c and d. -/
noncomputable def rectBoundaryIntegral (f : ℂ → ℂ) (a b c d : ℝ) : ℂ :=
  (∫ x : ℝ in a..b, f (x + c * I)) - (∫ x : ℝ in a..b, f (x + d * I)) +
    I * (∫ y : ℝ in c..d, f (b + y * I)) - I * (∫ y : ℝ in c..d, f (a + y * I))

private lemma integral_div_affine (u v : ℂ) (a b : ℝ)
    (hpath : ∀ t ∈ [[a, b]], (t : ℂ) * v + u ∈ slitPlane) :
    (∫ t : ℝ in a..b, v / ((t : ℂ) * v + u)) =
      log ((b : ℂ) * v + u) - log ((a : ℂ) * v + u) := by
  have hint : IntervalIntegrable (fun t : ℝ => v / ((t : ℂ) * v + u)) volume a b :=
    (continuousOn_const.div (by fun_prop) fun t ht => slitPlane_ne_zero (hpath t ht)).intervalIntegrable
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun s : ℝ => log ((s : ℂ) * v + u)) (fun t ht => ?_) hint
  have hreal : HasDerivAt (fun s : ℝ => (s : ℂ)) (1 : ℂ) t := by
    have hf : (ofRealCLM : ℝ → ℂ) = (fun s : ℝ => (s : ℂ)) := rfl
    simpa only [hf, ofRealCLM_apply, ofReal_one] using (ofRealCLM.hasDerivAt (x := t))
  have haff : HasDerivAt (fun s : ℝ => (s : ℂ) * v + u) v t := by
    simpa only [one_mul] using (hreal.mul_const v).add_const u
  simpa only [Function.comp_def, smul_eq_mul, div_eq_mul_inv] using
    (hasDerivAt_log (hpath t ht)).scomp t haff

private lemma horizontal_inv (p : ℂ) (a b y : ℝ) (hy : y ≠ p.im) :
    (∫ x : ℝ in a..b, ((x : ℂ) + y * I - p)⁻¹) =
      log ((b : ℂ) + y * I - p) - log ((a : ℂ) + y * I - p) := by
  have hs (t : ℝ) : (t : ℂ) * 1 + ((y : ℂ) * I - p) ∈ slitPlane := by
    apply mem_slitPlane_iff.mpr
    right
    simpa [add_im, sub_im, mul_im] using sub_ne_zero.mpr hy
  simpa only [mul_one, one_div, add_sub_assoc] using
    integral_div_affine ((y : ℂ) * I - p) 1 a b (fun t _ => hs t)

private lemma vertical_inv_right (p : ℂ) (x a b : ℝ) (hx : p.re < x) :
    I * (∫ y : ℝ in a..b, ((x : ℂ) + y * I - p)⁻¹) =
      log ((x : ℂ) + b * I - p) - log ((x : ℂ) + a * I - p) := by
  have hs (t : ℝ) : (t : ℂ) * I + ((x : ℂ) - p) ∈ slitPlane := by
    apply mem_slitPlane_iff.mpr
    left
    simpa [add_re, sub_re, mul_re] using sub_pos.mpr hx
  rw [← intervalIntegral.integral_const_mul]
  simpa only [div_eq_mul_inv, ← add_sub_assoc, add_comm ((x : ℂ))] using
    integral_div_affine ((x : ℂ) - p) I a b (fun t _ => hs t)

private lemma vertical_inv_left (p : ℂ) (x a b : ℝ) (hx : x < p.re) :
    I * (∫ y : ℝ in a..b, ((x : ℂ) + y * I - p)⁻¹) =
      log (-((x : ℂ) + b * I - p)) - log (-((x : ℂ) + a * I - p)) := by
  have harg (t : ℝ) : (t : ℂ) * (-I) + (p - (x : ℂ)) = -((x : ℂ) + t * I - p) := by ring
  have hs (t : ℝ) : (t : ℂ) * (-I) + (p - (x : ℂ)) ∈ slitPlane := by
    apply mem_slitPlane_iff.mpr
    left
    simpa [add_re, sub_re, mul_re, neg_re, neg_im] using sub_pos.mpr hx
  rw [← intervalIntegral.integral_const_mul]
  have h := integral_div_affine (p - (x : ℂ)) (-I) a b (fun t _ => hs t)
  simp only [harg] at h
  simpa only [div_eq_mul_inv, inv_neg, neg_mul, mul_neg, neg_neg] using h

private lemma log_sub_log_neg_pos {z : ℂ} (hz : 0 < z.im) :
    log z - log (-z) = (Real.pi : ℂ) * I := by
  apply Complex.ext
  · simp [sub_re, log_re, mul_re]
  · simp [sub_im, log_im, mul_im, arg_neg_eq_arg_sub_pi_of_im_pos hz]

private lemma log_sub_log_neg_neg {z : ℂ} (hz : z.im < 0) :
    log z - log (-z) = -(Real.pi : ℂ) * I := by
  apply Complex.ext
  · simp [sub_re, log_re, mul_re, neg_re]
  · simp [sub_im, log_im, mul_im, arg_neg_eq_arg_add_pi_of_im_neg hz]

/-- The rectangle encloses p strictly, and the reciprocal has residue one there. -/
theorem rectBoundaryIntegral_inv_sub {a b c d : ℝ} {p : ℂ}
    (ha : a < p.re) (hb : p.re < b) (hc : c < p.im) (hd : p.im < d) :
    rectBoundaryIntegral (fun z => (z - p)⁻¹) a b c d = 2 * (Real.pi : ℂ) * I := by
  have htop : 0 < ((a : ℂ) + d * I - p).im := by
    simpa [add_im, sub_im, mul_im] using sub_pos.mpr hd
  have hbot : ((a : ℂ) + c * I - p).im < 0 := by
    simpa [add_im, sub_im, mul_im] using sub_neg.mpr hc
  unfold rectBoundaryIntegral
  rw [horizontal_inv p a b c hc.ne, horizontal_inv p a b d hd.ne',
    vertical_inv_right p b c d hb, vertical_inv_left p a c d ha]
  calc
    _ = (log ((a : ℂ) + d * I - p) - log (-((a : ℂ) + d * I - p))) -
        (log ((a : ℂ) + c * I - p) - log (-((a : ℂ) + c * I - p))) := by ring
    _ = _ := by rw [log_sub_log_neg_pos htop, log_sub_log_neg_neg hbot]; ring

private lemma integral_decompose {a b : ℝ} {f g : ℂ → ℂ}
    (S : Finset ℂ) (r : ℂ → ℂ) (γ : ℝ → ℂ) (hγ : Continuous γ)
    (hg : ContinuousOn (g ∘ γ) [[a, b]]) (haway : ∀ t ∈ [[a, b]], γ t ∉ S)
    (he : ∀ t ∈ [[a, b]], f (γ t) = g (γ t) + ∑ p ∈ S, r p / (γ t - p)) :
    (∫ t : ℝ in a..b, f (γ t)) =
      (∫ t : ℝ in a..b, g (γ t)) + ∑ p ∈ S, r p * (∫ t : ℝ in a..b, (γ t - p)⁻¹) := by
  have hterms (p : ℂ) (hp : p ∈ S) :
      ContinuousOn (fun t : ℝ => r p / (γ t - p)) [[a, b]] := by
    have hnum : ContinuousOn (fun _ : ℝ => r p) [[a, b]] := continuousOn_const
    have hdenom : ContinuousOn (fun t : ℝ => γ t - p) [[a, b]] :=
      (hγ.sub continuous_const).continuousOn
    exact hnum.div hdenom fun t ht => sub_ne_zero.mpr fun htp => haway t ht (htp.symm ▸ hp)
  have hsum : ContinuousOn (fun t : ℝ => ∑ p ∈ S, r p / (γ t - p)) [[a, b]] :=
    continuousOn_finsetSum S hterms
  calc
    _ = ∫ t : ℝ in a..b, g (γ t) + ∑ p ∈ S, r p / (γ t - p) :=
      intervalIntegral.integral_congr he
    _ = (∫ t : ℝ in a..b, g (γ t)) + ∑ p ∈ S, ∫ t : ℝ in a..b, r p / (γ t - p) := by
      have hgi : IntervalIntegrable (fun t : ℝ => g (γ t)) volume a b := hg.intervalIntegrable
      have hsi : IntervalIntegrable (fun t : ℝ => ∑ p ∈ S, r p / (γ t - p)) volume a b :=
        hsum.intervalIntegrable
      rw [intervalIntegral.integral_add hgi hsi]
      congr 1
      exact intervalIntegral.integral_finsetSum (fun p hp => (hterms p hp).intervalIntegrable)
    _ = _ := by simp_rw [div_eq_mul_inv, intervalIntegral.integral_const_mul]

private lemma rect_sum_combine (S : Finset ℂ) (r bot top right left : ℂ → ℂ) :
    (∑ p ∈ S, r p * bot p) - (∑ p ∈ S, r p * top p) +
      I * (∑ p ∈ S, r p * right p) - I * (∑ p ∈ S, r p * left p) =
    ∑ p ∈ S, r p * (bot p - top p + I * right p - I * left p) := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun p _ => by ring

/-- Boundary integration computes the sum of the residues at interior simple
poles if subtracting the principal parts leaves a continuous remainder that
is complex differentiable away from the poles. -/
theorem rectBoundaryIntegral_eq_sum_residues {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (f g : ℂ → ℂ) (S : Finset ℂ) (r : ℂ → ℂ)
    (hpoles : ∀ p ∈ S, a < p.re ∧ p.re < b ∧ c < p.im ∧ p.im < d)
    (hg : ContinuousOn g (Icc a b ×ℂ Icc c d))
    (hgd : ∀ z ∈ (Ioo a b ×ℂ Ioo c d) \ (S : Set ℂ), DifferentiableAt ℂ g z)
    (hfg : EqOn f (fun z => g z + ∑ p ∈ S, r p / (z - p))
      ((Icc a b ×ℂ Icc c d) \ (S : Set ℂ))) :
    rectBoundaryIntegral f a b c d = (2 * (Real.pi : ℂ) * I) * ∑ p ∈ S, r p := by
  have hgc : ContinuousOn g ([[a, b]] ×ℂ [[c, d]]) := by
    simpa only [uIcc_of_le hab, uIcc_of_le hcd] using hg
  have hgd' : ∀ z ∈ (Ioo (min a b) (max a b) ×ℂ Ioo (min c d) (max c d)) \ (S : Set ℂ),
      DifferentiableAt ℂ g z := by
    simpa only [min_eq_left hab, max_eq_right hab, min_eq_left hcd, max_eq_right hcd] using hgd
  have hzero : rectBoundaryIntegral g a b c d = 0 := by
    simpa only [rectBoundaryIntegral, smul_eq_mul] using
      Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable
        g (⟨a, c⟩ : ℂ) (⟨b, d⟩ : ℂ) (S : Set ℂ) S.finite_toSet.countable hgc hgd'
  have edge {u v : ℝ} (γ : ℝ → ℂ) (hγ : Continuous γ)
      (hmem : MapsTo γ [[u, v]] (Icc a b ×ℂ Icc c d))
      (haway : ∀ t ∈ [[u, v]], γ t ∉ S) :=
    integral_decompose S r γ hγ (hg.comp hγ.continuousOn hmem) haway
      (fun t ht => hfg ⟨hmem ht, haway t ht⟩)
  have horizontal (y : ℝ) (hy : y ∈ Icc c d) (hy' : ∀ p ∈ S, y ≠ p.im) :=
    edge (u := a) (v := b) (fun x : ℝ => x + y * I) (by fun_prop)
      (fun t ht => by
        rw [mem_reProdIm]
        constructor
        · simpa [add_re, mul_re, uIcc_of_le hab] using ht
        · simpa [add_im, mul_im] using hy)
      (fun t _ hp => (hy' _ hp) (by simp [add_im, mul_im]))
  have vertical (x : ℝ) (hx : x ∈ Icc a b) (hx' : ∀ p ∈ S, x ≠ p.re) :=
    edge (u := c) (v := d) (fun y : ℝ => x + y * I) (by fun_prop)
      (fun t ht => by
        rw [mem_reProdIm]
        constructor
        · simpa [add_re, mul_re] using hx
        · simpa [add_im, mul_im, uIcc_of_le hcd] using ht)
      (fun t _ hp => (hx' _ hp) (by simp [add_re, mul_re]))
  have hdecomp :
      rectBoundaryIntegral f a b c d =
        rectBoundaryIntegral g a b c d +
          ∑ p ∈ S, r p * rectBoundaryIntegral (fun z => (z - p)⁻¹) a b c d := by
    unfold rectBoundaryIntegral
    rw [horizontal c ⟨le_rfl, hcd⟩ (fun p hp => (hpoles p hp).2.2.1.ne),
        horizontal d ⟨hcd, le_rfl⟩ (fun p hp => (hpoles p hp).2.2.2.ne'),
        vertical b ⟨hab, le_rfl⟩ (fun p hp => (hpoles p hp).2.1.ne'),
        vertical a ⟨le_rfl, hab⟩ (fun p hp => (hpoles p hp).1.ne)]
    rw [← rect_sum_combine]
    ring
  rw [hdecomp, hzero, zero_add, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  obtain ⟨ha, hb, hc, hd⟩ := hpoles p hp
  rw [rectBoundaryIntegral_inv_sub ha hb hc hd]
  ring

end Goldbach

open Filter Set
open scoped BigOperators Topology

namespace Goldbach

private lemma analyticAt_logDeriv_of_ne_zero {F : ℂ → ℂ} {w : ℂ}
    (hF : AnalyticAt ℂ F w) (hFw : F w ≠ 0) : AnalyticAt ℂ (logDeriv F) w :=
  hF.deriv.div hF hFw

/-- The weighted logarithmic derivative at a finite-order zero has principal
part equal to its order times the weight at that zero, divided by the local
coordinate. The same formula applies at order zero. -/
theorem logDeriv_mul_local_polar_part {F K : ℂ → ℂ} {w : ℂ}
    (hF : AnalyticAt ℂ F w) (horder : analyticOrderAt F w ≠ ⊤)
    (hK : AnalyticAt ℂ K w) :
    ∃ G : ℂ → ℂ, AnalyticAt ℂ G w ∧
      (fun z => logDeriv F z * K z - (analyticOrderNatAt F w : ℂ) * K w / (z - w))
        =ᶠ[𝓝[≠] w] G := by
  obtain ⟨A, hA, hA0, hfactor⟩ := hF.analyticOrderAt_ne_top.mp horder
  let m := analyticOrderNatAt F w
  let D : ℂ → ℂ := fun z => z - w
  have hD : Differentiable ℂ D := by dsimp [D]; fun_prop
  have hlogD (z : ℂ) : logDeriv D z = 1 / (z - w) := by
    simp [D, logDeriv_apply]
  have hfac : F =ᶠ[𝓝 w] fun z => D z ^ m * A z := by
    simpa only [D, m, smul_eq_mul] using hfactor
  have hz_ne : ∀ᶠ z in 𝓝[≠] w, z ≠ w := by
    simpa using (eventually_mem_nhdsWithin (a := w) (s := {w}ᶜ))
  have hlog : logDeriv F =ᶠ[𝓝[≠] w] fun z => (m : ℂ) / (z - w) + logDeriv A z := by
    filter_upwards [(logDeriv_congr_nhds hfac).filter_mono nhdsWithin_le_nhds,
      hA.eventually_analyticAt.filter_mono nhdsWithin_le_nhds,
      (hA.continuousAt.eventually_ne hA0).filter_mono nhdsWithin_le_nhds, hz_ne]
      with z hdz hAz hAnz hzne
    have hDz : D z ≠ 0 := sub_ne_zero.mpr hzne
    rw [hdz, logDeriv_fun_mul (f := fun t => D t ^ m) (g := A) z (pow_ne_zero m hDz) hAnz
      (hD.differentiableAt.pow m) hAz.differentiableAt,
      logDeriv_fun_pow (f := D) hD.differentiableAt m, hlogD, mul_one_div]
  refine ⟨fun z => (m : ℂ) * dslope K w z + logDeriv A z * K z, ?_, ?_⟩
  · exact (analyticAt_const.mul (hK.dslope w)).add
      ((analyticAt_logDeriv_of_ne_zero hA hA0).mul hK)
  · filter_upwards [hlog, hz_ne] with z hz hzne
    have hds : dslope K w z = (K z - K w) / (z - w) := by
      apply (eq_div_iff (sub_ne_zero.mpr hzne)).mpr
      simpa only [smul_eq_mul, mul_comm] using sub_smul_dslope K w z
    change logDeriv F z * K z - (m : ℂ) * K w / (z - w) =
      (m : ℂ) * dslope K w z + logDeriv A z * K z
    rw [hz, hds]
    ring

private lemma analyticAt_principal_term (r p z : ℂ) (hz : z ≠ p) :
    AnalyticAt ℂ (fun t : ℂ => r / (t - p)) z := by
  have hnum : AnalyticAt ℂ (fun _ : ℂ => r) z := analyticAt_const
  have hdenom : AnalyticAt ℂ (fun t : ℂ => t - p) z := by fun_prop
  exact hnum.div hdenom (sub_ne_zero.mpr hz)

/-- Subtracting all principal parts of a weighted logarithmic derivative
leaves an analytic remainder. The equality is stated away from the finitely
many points where the principal parts have poles. -/
theorem logDeriv_mul_exists_analytic_remainder {F K : ℂ → ℂ} {U : Set ℂ}
    (S : Finset ℂ) (hSU : (S : Set ℂ) ⊆ U) (hF : AnalyticOnNhd ℂ F U)
    (hK : AnalyticOnNhd ℂ K U) (hzeros : ∀ z ∈ U, F z = 0 → z ∈ S)
    (horder : ∀ p ∈ S, analyticOrderAt F p ≠ ⊤) :
    ∃ G : ℂ → ℂ, AnalyticOnNhd ℂ G U ∧
      EqOn (fun z => logDeriv F z * K z)
        (fun z => G z + ∑ p ∈ S, (analyticOrderNatAt F p : ℂ) * K p / (z - p))
        (U \ (S : Set ℂ)) := by
  classical
  let r : ℂ → ℂ := fun p => (analyticOrderNatAt F p : ℂ) * K p
  have hlocal (p : ℂ) (hp : p ∈ S) :
      ∃ g : ℂ → ℂ, AnalyticAt ℂ g p ∧
        (fun z => logDeriv F z * K z - r p / (z - p)) =ᶠ[𝓝[≠] p] g :=
    logDeriv_mul_local_polar_part (hF p (hSU hp)) (horder p hp) (hK p (hSU hp))
  choose localPart hlocalA hlocalEq using hlocal
  let regular : ℂ → ℂ := fun z => logDeriv F z * K z - ∑ p ∈ S, r p / (z - p)
  let G : ℂ → ℂ := fun z =>
    if hz : z ∈ S then localPart z hz z - ∑ p ∈ S.erase z, r p / (z - p) else regular z
  refine ⟨G, ?_, ?_⟩
  · intro z hz
    by_cases hzS : z ∈ S
    · have havoid : ∀ᶠ t in 𝓝 z, t ∉ S.erase z :=
        (S.erase z).finite_toSet.isClosed.isOpen_compl.mem_nhds (by simp)
      have heq : ∀ᶠ t in 𝓝 z, t ≠ z →
          logDeriv F t * K t - r z / (t - z) = localPart z hzS t := by
        simpa using (eventually_nhdsWithin_iff.mp (hlocalEq z hzS))
      have hG : G =ᶠ[𝓝 z] fun t =>
          localPart z hzS t - ∑ p ∈ S.erase z, r p / (t - p) := by
        filter_upwards [havoid, heq] with t ht hEq
        by_cases htz : t = z
        · subst t
          simp only [G, dite_eq_left hzS]
        · have htS : t ∉ S := fun h => ht (Finset.mem_erase.mpr ⟨htz, h⟩)
          simp only [G, dite_eq_right htS, regular]
          rw [← Finset.sum_erase_add S (fun p => r p / (t - p)) hzS, ← hEq htz]
          ring
      have hA : AnalyticAt ℂ (fun t => ∑ p ∈ S.erase z, r p / (t - p)) z :=
        (S.erase z).analyticAt_fun_sum fun p hp =>
          analyticAt_principal_term (r p) p z (Finset.ne_of_mem_erase hp).symm
      exact ((hlocalA z hzS).sub hA).congr hG.symm
    · have havoid : ∀ᶠ t in 𝓝 z, t ∉ S :=
        S.finite_toSet.isClosed.isOpen_compl.mem_nhds hzS
      have hG : G =ᶠ[𝓝 z] regular := by
        filter_upwards [havoid] with t ht
        simp only [G, dite_eq_right ht]
      have hFz : F z ≠ 0 := fun hzF => hzS (hzeros z hz hzF)
      have hsum : AnalyticAt ℂ (fun t => ∑ p ∈ S, r p / (t - p)) z :=
        S.analyticAt_fun_sum fun p hp =>
          analyticAt_principal_term (r p) p z (fun h => hzS (h.symm ▸ hp))
      exact (((analyticAt_logDeriv_of_ne_zero (hF z hz) hFz).mul (hK z hz)).sub hsum).congr
        hG.symm
  · intro z hz
    have hzS : z ∉ S := hz.2
    change logDeriv F z * K z = G z + ∑ p ∈ S, r p / (z - p)
    simp only [G, dite_eq_right hzS, regular, sub_add_cancel]

end Goldbach

open Complex Filter Set MeasureTheory
open scoped BigOperators Interval Topology

namespace Goldbach

/-- Finite contour identity for the weighted logarithmic derivative with the
principal pole at one restored explicitly. -/
theorem rectBoundaryIntegral_neg_logDeriv_add_pole_mul
    {a b c d : ℝ} (F K : ℂ → ℂ) (S : Finset ℂ) (δ : ℂ)
    (ha : a < 1) (hb : 1 < b) (hc : c < 0) (hd : 0 < d)
    (hF : AnalyticOnNhd ℂ F (Icc a b ×ℂ Icc c d))
    (hK : AnalyticOnNhd ℂ K (Icc a b ×ℂ Icc c d))
    (hzeros : ∀ z ∈ Icc a b ×ℂ Icc c d, F z = 0 ↔ z ∈ S)
    (hinterior : ∀ p ∈ S, a < p.re ∧ p.re < b ∧ c < p.im ∧ p.im < d)
    (horder : ∀ p ∈ S, analyticOrderAt F p ≠ ⊤) (hF1 : F 1 ≠ 0) :
    rectBoundaryIntegral (fun z => (-logDeriv F z + δ / (z - 1)) * K z) a b c d =
      (2 * (Real.pi : ℂ) * I) * (δ * K 1 - ∑ p ∈ S, (analyticOrderNatAt F p : ℂ) * K p) := by
  classical
  let U := Icc a b ×ℂ Icc c d
  let T := insert (1 : ℂ) S
  let r : ℂ → ℂ := fun p => (analyticOrderNatAt F p : ℂ) * K p
  let coeff : ℂ → ℂ := fun p => if p = 1 then δ * K 1 else -r p
  have h1U : (1 : ℂ) ∈ U := by
    exact mem_reProdIm.mpr ⟨by simpa only [one_re] using Set.mem_Icc.mpr ⟨ha.le, hb.le⟩,
      by simpa only [one_im] using Set.mem_Icc.mpr ⟨hc.le, hd.le⟩⟩
  have h1S : (1 : ℂ) ∉ S := fun h => hF1 ((hzeros 1 h1U).mpr h)
  have hSU : (S : Set ℂ) ⊆ U := by
    intro p hp
    obtain ⟨hpa, hpb, hpc, hpd⟩ := hinterior p hp
    exact mem_reProdIm.mpr ⟨⟨hpa.le, hpb.le⟩, ⟨hpc.le, hpd.le⟩⟩
  have hT : ∀ p ∈ T, a < p.re ∧ p.re < b ∧ c < p.im ∧ p.im < d := by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · simpa only [one_re, one_im] using And.intro ha (And.intro hb (And.intro hc hd))
    · exact hinterior p hp
  have hcoeff1 : coeff 1 = δ * K 1 := ite_eq_left rfl
  have hcoeff (p : ℂ) (hp : p ∈ S) : coeff p = -r p := by
    have hp1 : p ≠ (1 : ℂ) := fun heq => h1S (heq ▸ hp)
    exact ite_eq_right hp1
  have hsum (z : ℂ) :
      (∑ p ∈ T, coeff p / (z - p)) =
        δ * K 1 / (z - 1) - ∑ p ∈ S, r p / (z - p) := by
    have hsumS : (∑ p ∈ S, coeff p / (z - p)) = -(∑ p ∈ S, r p / (z - p)) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun p hp => by rw [hcoeff p hp, neg_div]
    change (∑ p ∈ insert (1 : ℂ) S, coeff p / (z - p)) = _
    rw [Finset.sum_insert h1S, hcoeff1, hsumS]
    exact (sub_eq_add_neg _ _).symm
  have hsum_coeff : (∑ p ∈ T, coeff p) = δ * K 1 - ∑ p ∈ S, r p := by
    have hsumS : (∑ p ∈ S, coeff p) = -(∑ p ∈ S, r p) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl hcoeff
    change (∑ p ∈ insert (1 : ℂ) S, coeff p) = _
    rw [Finset.sum_insert h1S, hcoeff1, hsumS, sub_eq_add_neg]
  obtain ⟨G, hG, hG_eq⟩ := logDeriv_mul_exists_analytic_remainder S hSU hF hK
    (fun z hz => (hzeros z hz).mp) horder
  let J : ℂ → ℂ := fun z => -G z + δ * dslope K 1 z
  have hJ : AnalyticOnNhd ℂ J U := by
    intro z hz
    exact (hG z hz).neg.add (analyticAt_const.mul ((hK z hz).dslope 1))
  have hJ_diff : ∀ z ∈ (Ioo a b ×ℂ Ioo c d) \ (T : Set ℂ), DifferentiableAt ℂ J z := by
    intro z hz
    obtain ⟨hr, hi⟩ := mem_reProdIm.mp hz.1
    exact (hJ z (mem_reProdIm.mpr ⟨Ioo_subset_Icc_self hr, Ioo_subset_Icc_self hi⟩)).differentiableAt
  have hEq : EqOn (fun z => (-logDeriv F z + δ / (z - 1)) * K z)
      (fun z => J z + ∑ p ∈ T, coeff p / (z - p)) (U \ (T : Set ℂ)) := by
    intro z hz
    have hzT : z ∉ T := hz.2
    have hzS : z ∉ S := fun h => hzT (Finset.mem_insert_of_mem h)
    have hz1 : z ≠ (1 : ℂ) := fun h => hzT (Finset.mem_insert.mpr (Or.inl h))
    have hGK := hG_eq ⟨hz.1, hzS⟩
    change logDeriv F z * K z = G z + ∑ p ∈ S, r p / (z - p) at hGK
    have hds : dslope K 1 z = (K z - K 1) / (z - 1) := by
      apply (eq_div_iff (sub_ne_zero.mpr hz1)).mpr
      simpa only [smul_eq_mul, mul_comm] using sub_smul_dslope K 1 z
    change (-logDeriv F z + δ / (z - 1)) * K z =
      (-G z + δ * dslope K 1 z) + ∑ p ∈ T, coeff p / (z - p)
    rw [hsum, hds]
    calc
      _ = -(logDeriv F z * K z) + δ / (z - 1) * K z := by ring
      _ = _ := by rw [hGK]; ring
  rw [rectBoundaryIntegral_eq_sum_residues (ha.le.trans hb.le) (hc.le.trans hd.le)
    _ J T coeff hT hJ.continuousOn hJ_diff hEq, hsum_coeff]

/-- Solve a rectangular contour identity for its right vertical integral. -/
theorem right_vertical_integral_of_rect {f : ℂ → ℂ} {a b c d : ℝ} {R : ℂ}
    (h : rectBoundaryIntegral f a b c d = 2 * (Real.pi : ℂ) * I * R) :
    (∫ y : ℝ in c..d, f (b + y * I)) =
      (∫ y : ℝ in c..d, f (a + y * I)) + 2 * (Real.pi : ℂ) * R +
        I * ((∫ x : ℝ in a..b, f (x + c * I)) - ∫ x : ℝ in a..b, f (x + d * I)) := by
  unfold rectBoundaryIntegral at h
  set bottom := (∫ x : ℝ in a..b, f (x + c * I))
  set top := (∫ x : ℝ in a..b, f (x + d * I))
  set left := (∫ y : ℝ in c..d, f (a + y * I))
  set right := (∫ y : ℝ in c..d, f (b + y * I))
  calc
    right = left - I * (bottom - top + I * right - I * left) + I * (bottom - top) := by
      ring_nf
      simp only [I_sq]
      ring
    _ = _ := by
      rw [h]
      ring_nf
      simp only [I_sq]
      ring

end Goldbach
namespace Goldbach

open Complex Filter MeasureTheory Set
open scoped BigOperators Interval Topology

theorem uniform_dirichlet_log_control : ∃ C : ℝ, 0 < C ∧ UniformDirichletLogDerivative C := by
  obtain ⟨C, hC, h⟩ := norm_logDeriv_regularizedL_le
  refine ⟨C, hC, ?_⟩
  intro q _ χ σ t d hσ hd hdist
  have hpoint : (⟨σ, t⟩ : ℂ) = (σ : ℂ) + (t : ℂ) * I := by
    apply Complex.ext <;> simp
  rw [← hpoint] at hdist ⊢
  exact h q χ t σ d hσ.1 hσ.2 hd hdist
end Goldbach
end
end
end

section
open Set MeasureTheory

namespace GoldbachOscillation

/-- The multiplier R(y) = y/(L²+y²) stays finite as the phase slope crosses zero. -/
private noncomputable def D (L y : ℝ) := L^2+y^2
private noncomputable def R (L y : ℝ) := y / D L y
private noncomputable def R' (L y : ℝ) := (L^2-y^2) / (D L y)^2
private noncomputable def J (L y : ℝ) := Real.arctan (y/L) / L
private noncomputable def wave (y : ℝ) := Complex.exp ((y:ℂ)*Complex.I)

private theorem D_pos {L : ℝ} (hL : 0 < L) (y : ℝ) : 0 < D L y := by unfold D; positivity

private theorem R_deriv {L : ℝ} (hL : 0 < L) (y : ℝ) : HasDerivAt (R L) (R' L y) y := by
  have h := (hasDerivAt_id y).div ((hasDerivAt_const y (L^2)).add ((hasDerivAt_id y).pow 2))
    (D_pos hL y).ne'
  convert h using 1
  · rfl
  unfold R' D
  simp
  ring

private theorem J_deriv {L : ℝ} (hL : 0 < L) (y : ℝ) : HasDerivAt (J L) (1 / D L y) y := by
  have h := ((Real.hasDerivAt_arctan (y/L)).comp y ((hasDerivAt_id y).div_const L)).div_const L
  convert h using 1
  · rfl
  unfold D
  field_simp [hL.ne']

private theorem wave_deriv (y : ℝ) :
    HasDerivAt wave (wave y * Complex.I) y := by
  simpa [wave] using! (((hasDerivAt_id (y:ℂ)).mul_const Complex.I).cexp).comp_ofReal

private theorem wave_norm (y : ℝ) : ‖wave y‖ = 1 := Complex.norm_exp_ofReal_mul_I _

private theorem R_bound {L : ℝ} (hL : 0 < L) (y : ℝ) : |R L y| ≤ 1/L := by
  rw [R, abs_div, abs_of_pos (D_pos hL y)]
  apply (div_le_div_iff₀ (D_pos hL y) hL).mpr
  unfold D
  nlinarith only [sq_nonneg (L-|y|), sq_abs y, mul_nonneg hL.le (abs_nonneg y)]

private theorem R'_bound {L : ℝ} (hL : 0 < L) (y : ℝ) : |R' L y| ≤ 1 / D L y := by
  have hp := D_pos hL y
  rw [R', abs_div, abs_of_pos (sq_pos_of_pos hp)]
  have hab : |L^2-y^2| ≤ D L y := abs_le.mpr ⟨by dsimp [D]; nlinarith [sq_nonneg L],
    by dsimp [D]; nlinarith [sq_nonneg y]⟩
  apply (div_le_div_iff₀ (sq_pos_of_pos hp) hp).mpr
  nlinarith only [mul_le_mul_of_nonneg_right hab hp.le]

private theorem remainder {L : ℝ} (hL : 0 < L) (y : ℝ) :
    1-y*R L y = L^2 / D L y := by
  unfold R
  field_simp [(D_pos hL y).ne']
  unfold D
  ring

private noncomputable def mainTerm (w f : ℝ → ℝ) (x : ℝ) : ℂ := (w x:ℂ)*wave (f x)
private noncomputable def primitive (L : ℝ) (w f p : ℝ → ℝ) (x : ℝ) : ℂ :=
  -Complex.I*((w x * R L (p x) : ℝ):ℂ)*wave (f x)
private noncomputable def errorTerm (L : ℝ) (w dw f p dp : ℝ → ℝ) (x : ℝ) : ℂ :=
  wave (f x) * (((w x * (1-p x*R L (p x)) : ℝ):ℂ) +
    Complex.I * ((dw x*R L (p x)+w x*R' L (p x)*dp x : ℝ):ℂ))

private theorem primitive_deriv {L x : ℝ} (hL : 0 < L) {w dw f p dp : ℝ → ℝ}
    (hw : HasDerivAt w (dw x) x) (hf : HasDerivAt f (p x) x) (hp : HasDerivAt p (dp x) x) :
    HasDerivAt (primitive L w f p) (mainTerm w f x - errorTerm L w dw f p dp x) x := by
  have hr := (R_deriv hL (p x)).comp x hp
  have hd := (((hw.mul hr).ofReal_comp.const_mul (-Complex.I)).mul ((wave_deriv (f x)).scomp x hf))
  convert hd using 1
  · rfl
  dsimp [mainTerm, errorTerm]
  push_cast
  ring_nf
  simp [Complex.I_sq]

private theorem primitive_bound {L x : ℝ} (hL : 0 < L) (w f p : ℝ → ℝ)
    (hw : |w x| ≤ 1) : ‖primitive L w f p x‖ ≤ 1/L := by
  simp only [primitive, norm_mul, norm_neg, Complex.norm_I, one_mul, wave_norm,
    mul_one, Complex.norm_real, Real.norm_eq_abs]
  simpa using mul_le_mul hw (R_bound hL (p x)) (abs_nonneg _) zero_le_one

private theorem error_bound {L x : ℝ} (hL : 0 < L) (w dw f p dp : ℝ → ℝ)
    (hw : |w x| ≤ 1) (hdw : |dw x| ≤ 1) (hcurv : L^2 ≤ 4*dp x) :
    ‖errorTerm L w dw f p dp x‖ ≤ 1/L + 5 * (dp x / D L (p x)) := by
  have hd := D_pos hL (p x)
  have hp : 0 ≤ dp x := by nlinarith only [sq_nonneg L,hcurv]
  rw [errorTerm, norm_mul, wave_norm, one_mul]
  apply (norm_add_le ..).trans
  simp only [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
    remainder hL, abs_of_nonneg (div_nonneg (sq_nonneg L) hd.le)]
  have hfirst := mul_le_of_le_one_left (div_nonneg (sq_nonneg L) hd.le) hw
  have hsecond : |dw x*R L (p x)| ≤ 1/L := by
    rw [abs_mul]
    simpa using mul_le_mul hdw (R_bound hL _) (abs_nonneg _) zero_le_one
  have hthird : |w x*R' L (p x)*dp x| ≤ dp x/D L (p x) := by
    simp only [abs_mul, abs_of_nonneg hp]
    have hs : |w x| * |R' L (p x)| ≤ 1/D L (p x) := by
      simpa using mul_le_mul hw (R'_bound hL _) (abs_nonneg _) zero_le_one
    simpa [div_eq_mul_inv, mul_comm] using mul_le_mul_of_nonneg_right hs hp
  have hscale := div_le_div_of_nonneg_right hcurv hd.le
  rw [mul_div_assoc] at hscale
  have htriangle := abs_add_le (dw x*R L (p x)) (w x*R' L (p x)*dp x)
  linarith

/-- A regularized integration by parts works across a possible stationary point.
The arctangent controls the total variation of the multiplier. -/
private theorem regularized {a b L : ℝ} (hab : a ≤ b) (hlen : b-a ≤ 1) (hL : 0 < L)
    (w dw f p dp : ℝ → ℝ)
    (hw : ∀ x ∈ Icc a b, HasDerivAt w (dw x) x)
    (hf : ∀ x ∈ Icc a b, HasDerivAt f (p x) x)
    (hp : ∀ x ∈ Icc a b, HasDerivAt p (dp x) x)
    (hcw : ContinuousOn dw (Icc a b)) (hcp : ContinuousOn dp (Icc a b))
    (hw1 : ∀ x ∈ Icc a b, |w x| ≤ 1) (hdw1 : ∀ x ∈ Icc a b, |dw x| ≤ 1)
    (hcurv : ∀ x ∈ Icc a b, L^2 ≤ 4*dp x) :
    ‖∫ x in a..b, mainTerm w f x‖ ≤ (3+5*Real.pi)/L := by
  have cw := HasDerivAt.continuousOn hw
  have cf := HasDerivAt.continuousOn hf
  have cp := HasDerivAt.continuousOn hp
  have cR : Continuous (R L) := continuous_iff_continuousAt.mpr fun y => (R_deriv hL y).continuousAt
  have cD : Continuous (D L) := by unfold D; fun_prop
  have cR' : Continuous (R' L) := by
    unfold R'
    exact (continuous_const.sub (continuous_id.pow 2)).div (cD.pow 2) (fun y => (sq_pos_of_pos (D_pos hL y)).ne')
  have cWave : Continuous wave := continuous_iff_continuousAt.mpr fun y => (wave_deriv y).continuousAt
  have cwav := cWave.comp_continuousOn cf
  have cr := cR.comp_continuousOn cp
  have cr' := cR'.comp_continuousOn cp
  have mainC : ContinuousOn (mainTerm w f) (Icc a b) := by unfold mainTerm; fun_prop
  have errC : ContinuousOn (errorTerm L w dw f p dp) (Icc a b) := by unfold errorTerm; fun_prop
  have mainI := mainC.intervalIntegrable_of_Icc (μ := volume) hab
  have errI := errC.intervalIntegrable_of_Icc (μ := volume) hab
  have identity := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := primitive L w f p) (f' := fun x => mainTerm w f x - errorTerm L w dw f p dp x)
    (fun x hx => by rw [uIcc_of_le hab] at hx; exact primitive_deriv hL (hw x hx) (hf x hx) (hp x hx))
    (mainI.sub errI)
  rw [intervalIntegral.integral_sub mainI errI] at identity
  let density := fun x => dp x / D L (p x)
  have denC : ContinuousOn density (Icc a b) :=
    hcp.div (cD.comp_continuousOn cp) (fun x _ => (D_pos hL (p x)).ne')
  have di := denC.intervalIntegrable_of_Icc (μ := volume) hab
  have jd := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := J L ∘ p) (f' := density) (fun x hx => by
      rw [uIcc_of_le hab] at hx
      convert (J_deriv hL (p x)).comp x (hp x hx) using 1
      dsimp [density]; ring) di
  -- Integrating the positive density only costs the range of arctan, divided by L.
  have jbound : (∫ x in a..b, density x) ≤ Real.pi/L := by
    rw [jd]
    dsimp [J]
    rw [← sub_div]
    apply div_le_div_of_nonneg_right _ hL.le
    linarith only [Real.arctan_lt_pi_div_two (p b/L), Real.neg_pi_div_two_lt_arctan (p a/L)]
  have errBound := intervalIntegral.norm_integral_le_of_norm_le hab
    (g := fun x => 1/L + 5 * density x) (Filter.Eventually.of_forall fun x hx =>
      error_bound hL w dw f p dp (hw1 x ⟨hx.1.le,hx.2⟩) (hdw1 x ⟨hx.1.le,hx.2⟩) (hcurv x ⟨hx.1.le,hx.2⟩))
    (intervalIntegrable_const.add (di.const_mul 5))
  rw [intervalIntegral.integral_add intervalIntegrable_const (di.const_mul 5),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul, smul_eq_mul] at errBound
  have lhs : (∫ x in a..b, mainTerm w f x) =
      (primitive L w f p b - primitive L w f p a) + ∫ x in a..b, errorTerm L w dw f p dp x :=
    sub_eq_iff_eq_add.mp identity
  rw [lhs]
  apply (norm_add_le ..).trans
  have nd := norm_sub_le (primitive L w f p b) (primitive L w f p a)
  have ba := primitive_bound hL w f p (hw1 a (left_mem_Icc.mpr hab))
  have bb := primitive_bound hL w f p (hw1 b (right_mem_Icc.mpr hab))
  have length := mul_le_mul_of_nonneg_right hlen (one_div_nonneg.mpr hL.le)
  rw [add_div, mul_div_assoc]
  rw [show 3/L = 3*(1/L) by ring]
  linarith only [ba,bb,nd,errBound,length,jbound]

private noncomputable def kernel (σ β γ x : ℝ) : ℂ :=
  ((x^(σ-1):ℝ):ℂ) * wave (β*x + γ*Real.log x)

private theorem dyadic_minus {a b γ σ : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ 2)
    (hγ : 0 < γ) (hσ : 0 ≤ σ) (hσ' : σ ≤ 1) (β : ℝ) :
    ‖∫ x in a..b, kernel σ β (-γ) x‖ ≤ (3+5*Real.pi)/Real.sqrt γ := by
  let w := fun x : ℝ => x^(σ-1)
  let dw := fun x : ℝ => (σ-1)*x^(σ-1-1)
  let f := fun x : ℝ => β*x+(-γ)*Real.log x
  let p := fun x : ℝ => β-γ/x
  let dp := fun x : ℝ => γ/x^2
  have hx {x : ℝ} (h : x ∈ Icc a b) : 1 ≤ x := ha.trans h.1
  have hxp {x : ℝ} (h : x ∈ Icc a b) : 0 < x := zero_lt_one.trans_le (hx h)
  apply regularized hab (by linarith) (Real.sqrt_pos.mpr hγ) w dw f p dp
  · intro x h
    exact Real.hasDerivAt_rpow_const (Or.inl (hxp h).ne')
  · intro x h
    have h' := ((hasDerivAt_id x).const_mul β).add ((Real.hasDerivAt_log (hxp h).ne').const_mul (-γ))
    convert h' using 1
    · rfl
    dsimp [p]; ring
  · intro x h
    have h' := (hasDerivAt_const x β).sub ((hasDerivAt_const x γ).div (hasDerivAt_id x) (hxp h).ne')
    convert h' using 1
    · rfl
    dsimp [dp]; ring
  · unfold dw; fun_prop (disch := solve_by_elim [ne_of_gt, hxp])
  · change ContinuousOn (fun x : ℝ => γ/x^2) (Icc a b)
    fun_prop (disch := intro x hx; exact pow_ne_zero 2 (hxp hx).ne')
  · intro x h
    dsimp [w]
    rw [abs_of_nonneg (Real.rpow_nonneg (hxp h).le _)]
    exact Real.rpow_le_one_of_one_le_of_nonpos (hx h) (by linarith)
  · intro x h
    dsimp [dw]
    rw [abs_mul, abs_of_nonpos (sub_nonpos.mpr hσ'), abs_of_nonneg (Real.rpow_nonneg (hxp h).le _)]
    have h1 : -(σ-1) ≤ 1 := by linarith
    have h2 := Real.rpow_le_one_of_one_le_of_nonpos (hx h) (show σ-1-1 ≤ 0 by linarith)
    simpa using mul_le_mul h1 h2 (Real.rpow_nonneg (hxp h).le _) zero_le_one
  · intro x h
    rw [Real.sq_sqrt hγ.le]
    change γ ≤ 4*(γ/x^2)
    rw [← mul_div_assoc]
    apply (le_div_iff₀ (sq_pos_of_pos (hxp h))).mpr
    have h2 := pow_le_pow_left₀ (hxp h).le (h.2.trans hb) 2
    nlinarith only [mul_le_mul_of_nonneg_left h2 hγ.le]

open scoped ComplexConjugate

private theorem wave_add (u v : ℝ) : wave (u+v) = wave u * wave v := by
  unfold wave
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem conjugate_kernel (σ β γ x : ℝ) :
    conj (kernel σ (-β) (-γ) x) = kernel σ β γ x := by
  unfold kernel wave
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  congr 2
  simp
  ring

private theorem dyadic {a b γ σ : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ 2)
    (hγ : γ ≠ 0) (hσ : 0 ≤ σ) (hσ' : σ ≤ 1) (β : ℝ) :
    ‖∫ x in a..b, kernel σ β γ x‖ ≤ min 1 ((3+5*Real.pi)/Real.sqrt |γ|) := by
  apply le_min
  · have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b)
      (f := kernel σ β γ) (C := 1) (fun x hx => by
        rw [uIoc_of_le hab] at hx
        have h1 := ha.trans hx.1.le
        rw [kernel, norm_mul, wave_norm, mul_one, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Real.rpow_nonneg (zero_le_one.trans h1) _)]
        exact Real.rpow_le_one_of_one_le_of_nonpos h1 (by linarith))
    rw [abs_of_nonneg (sub_nonneg.mpr hab), one_mul] at h
    exact h.trans (by linarith)
  · rcases lt_or_gt_of_ne hγ with hn | hpos
    · simpa [abs_of_neg hn] using dyadic_minus ha hab hb (neg_pos.mpr hn) hσ hσ' β
    · have id : (∫ x in a..b, kernel σ β γ x) = conj (∫ x in a..b, kernel σ (-β) (-γ) x) := by
        rw [← intervalIntegral.intervalIntegral_conj]
        exact intervalIntegral.integral_congr fun x _ => (conjugate_kernel σ β γ x).symm
      rw [id, Complex.norm_conj, abs_of_pos hpos]
      exact dyadic_minus ha hab hb hpos hσ hσ' (-β)

private theorem rescale {Y x : ℝ} (hY : 0 < Y) (hx : 0 < x) (σ β γ : ℝ) :
    kernel σ β γ (Y*x) = (((Y^(σ-1):ℝ):ℂ)*wave (γ*Real.log Y)) * kernel σ (β*Y) γ x := by
  unfold kernel
  rw [Real.mul_rpow hY.le hx.le, Real.log_mul hY.ne' hx.ne',
    show β*(Y*x)+γ*(Real.log Y+Real.log x) = γ*Real.log Y + ((β*Y)*x+γ*Real.log x) by ring, wave_add]
  push_cast
  ring

/- Away from a stationary point, integrate with the reciprocal of βx+γ.
Its fixed-sign derivative gives a total variation bound from the endpoints. -/
set_option maxHeartbeats 600000 in
private theorem separated {a b σ γ β H : ℝ} (ha : 0 < a) (hab : a ≤ b) (hσ : 0 ≤ σ)
    (hH : 0 < H) (hsep : ∀ x ∈ Icc a b, H ≤ |β*x+γ|) :
    ‖∫ x in a..b, kernel σ β γ x‖ ≤ 5*b^σ/H := by
  let F := fun x : ℝ => β*x + γ*Real.log x
  let p := fun x : ℝ => β+γ/x
  let W := fun x : ℝ => x^σ
  let dW := fun x : ℝ => σ*x^(σ-1)
  let z := fun x : ℝ => 1/(β*x+γ)
  let dz := fun x : ℝ => -β/(β*x+γ)^2
  let B := fun x : ℝ => -Complex.I*((W x*z x : ℝ):ℂ)*wave (F x)
  let er := fun x : ℝ => Complex.I*((dW x*z x+W x*dz x : ℝ):ℂ)*wave (F x)
  have pos {x : ℝ} (hx : x ∈ Icc a b) : 0 < x := ha.trans_le hx.1
  have nz {x : ℝ} (hx : x ∈ Icc a b) : β*x+γ ≠ 0 := abs_pos.mp (hH.trans_le (hsep x hx))
  have zd (x : ℝ) (hx : x ∈ Icc a b) : HasDerivAt z (dz x) x := by
    have h := (hasDerivAt_const x (1:ℝ)).div (((hasDerivAt_id x).const_mul β).add_const γ) (nz hx)
    convert h using 1 <;> first | rfl | (dsimp [dz]; ring)
  have wd (x : ℝ) (hx : x ∈ Icc a b) : HasDerivAt W (dW x) x :=
    Real.hasDerivAt_rpow_const (Or.inl (pos hx).ne')
  have fd (x : ℝ) (hx : x ∈ Icc a b) : HasDerivAt F (p x) x := by
    have h := ((hasDerivAt_id x).const_mul β).add ((Real.hasDerivAt_log (pos hx).ne').const_mul γ)
    convert h using 1 <;> first | rfl | (dsimp [p]; ring)
  have hB (x : ℝ) (hx : x ∈ Icc a b) : HasDerivAt B (kernel σ β γ x - er x) x := by
    have hv := ((((wd x hx).mul (zd x hx)).ofReal_comp.const_mul (-Complex.I)).mul
      ((wave_deriv (F x)).scomp x (fd x hx)))
    have unit : W x*z x*p x = x^(σ-1) := by
      dsimp [W,z,p]
      rw [Real.rpow_sub_one (pos hx).ne']
      field_simp [(nz hx),(pos hx).ne']
    have hu : (W x:ℂ)*(z x:ℂ)*(p x:ℂ) = ((x^(σ-1):ℝ):ℂ) := by exact_mod_cast unit
    convert hv using 1
    · rfl
    change ((x^(σ-1):ℝ):ℂ)*wave (F x) - er x = _
    dsimp only [er, Pi.mul_apply, Function.comp_apply]
    push_cast
    rw [← hu]
    simp only [Complex.real_smul]
    linear_combination ((W x:ℂ)*(z x:ℂ)*(p x:ℂ)*wave (F x)) * Complex.I_sq
  have cw := HasDerivAt.continuousOn wd
  have cz := HasDerivAt.continuousOn zd
  have cf := HasDerivAt.continuousOn fd
  have cdw : ContinuousOn dW (Icc a b) := by unfold dW; fun_prop (disch := solve_by_elim [ne_of_gt,pos])
  have cdz : ContinuousOn dz (Icc a b) := by unfold dz; fun_prop (disch := intro x hx; exact pow_ne_zero _ (nz hx))
  have cwave : Continuous wave := continuous_iff_continuousAt.mpr fun y => (wave_deriv y).continuousAt
  have cwF := cwave.comp_continuousOn cf
  have ce : ContinuousOn er (Icc a b) := by unfold er; fun_prop
  have ck : ContinuousOn (kernel σ β γ) (Icc a b) := by
    change ContinuousOn (fun x : ℝ => ((x^(σ-1):ℝ):ℂ)*wave (F x)) _
    have hc : ContinuousOn (fun x : ℝ => x^(σ-1)) (Icc a b) :=
      continuousOn_id.rpow_const fun _ hx => Or.inl (pos hx).ne'
    exact (Complex.continuous_ofReal.comp_continuousOn hc).mul cwF
  have ei := ce.intervalIntegrable_of_Icc (μ := volume) hab
  have ki := ck.intervalIntegrable_of_Icc (μ := volume) hab
  have fi := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := B)
    (f' := fun x => kernel σ β γ x - er x)
    (fun x hx => hB x ((uIcc_of_le hab) ▸ hx)) (ki.sub ei)
  rw [intervalIntegral.integral_sub ki ei] at fi
  have zi := cdz.intervalIntegrable_of_Icc (μ := volume) hab
  have wi := cdw.intervalIntegrable_of_Icc (μ := volume) hab
  have wint := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := W) (f' := dW)
    (fun x hx => wd x ((uIcc_of_le hab) ▸ hx)) wi
  have zint := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := z) (f' := dz)
    (fun x hx => zd x ((uIcc_of_le hab) ▸ hx)) zi
  have zmax (x : ℝ) (hx : x ∈ Icc a b) : |z x| ≤ 1/H := by
    simp only [z, abs_div, abs_one]
    exact one_div_le_one_div_of_le hH (hsep x hx)
  have Wmax (x : ℝ) (hx : x ∈ Icc a b) : |W x| ≤ b^σ := by
    rw [abs_of_nonneg (Real.rpow_nonneg (pos hx).le _)]
    exact Real.rpow_le_rpow (pos hx).le hx.2 hσ
  have Bmax (x : ℝ) (hx : x ∈ Icc a b) : ‖B x‖ ≤ b^σ/H := by
    simp only [B, norm_mul, norm_neg, Complex.norm_I, wave_norm, one_mul, mul_one,
      Complex.norm_real, Real.norm_eq_abs]
    simpa [div_eq_mul_inv] using mul_le_mul (Wmax x hx) (zmax x hx) (abs_nonneg _) (Real.rpow_nonneg (ha.trans_le hab).le _)
  -- The sign of β determines the monotonicity of the reciprocal on this interval.
  have zvar : (∫ x in a..b, |dz x|) ≤ 2/H := by
    have sign {x : ℝ} : 0 ≤ (β*x+γ)^2 := sq_nonneg _
    have za := abs_le.mp (zmax a (left_mem_Icc.mpr hab))
    have zb := abs_le.mp (zmax b (right_mem_Icc.mpr hab))
    rcases le_total 0 β with hp | hn
    · have he : (∫ x in a..b, |dz x|) = -(z b-z a) := by
        rw [← zint, ← intervalIntegral.integral_neg]
        exact intervalIntegral.integral_congr fun x _ => abs_of_nonpos (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hp) sign)
      rw [he,show 2/H = 2*(1/H) by ring]; linarith
    · have he : (∫ x in a..b, |dz x|) = z b-z a := by
        rw [← zint]
        exact intervalIntegral.integral_congr fun x _ => abs_of_nonneg (div_nonneg (neg_nonneg.mpr hn) sign)
      rw [he,show 2/H = 2*(1/H) by ring]; linarith
  have eBound (x : ℝ) (hx : x ∈ Icc a b) : ‖er x‖ ≤ dW x*(1/H) + b^σ*|dz x| := by
    simp only [er, norm_mul, Complex.norm_I, one_mul, wave_norm, mul_one, Complex.norm_real, Real.norm_eq_abs]
    apply (abs_add_le ..).trans
    rw [abs_mul (dW x) (z x), abs_mul (W x) (dz x), abs_of_nonneg (show 0 ≤ dW x from mul_nonneg hσ (Real.rpow_nonneg (pos hx).le _))]
    exact add_le_add (mul_le_mul_of_nonneg_left (zmax x hx) (mul_nonneg hσ (Real.rpow_nonneg (pos hx).le _)))
      (mul_le_mul_of_nonneg_right (Wmax x hx) (abs_nonneg _))
  have ai := cdz.abs.intervalIntegrable_of_Icc (μ := volume) hab
  have eint := intervalIntegral.norm_integral_le_of_norm_le hab
    (Filter.Eventually.of_forall fun x hx => eBound x ⟨hx.1.le,hx.2⟩)
    ((wi.mul_const (1/H)).add (ai.const_mul (b^σ)))
  rw [intervalIntegral.integral_add (wi.mul_const (1/H)) (ai.const_mul (b^σ)),
    intervalIntegral.integral_mul_const (1/H) dW, intervalIntegral.integral_const_mul (b^σ) (fun x => |dz x|), wint] at eint
  rw [sub_eq_iff_eq_add.mp fi]
  apply (norm_add_le ..).trans
  have bd := norm_sub_le (B b) (B a)
  have bl := Bmax a (left_mem_Icc.mpr hab)
  have br := Bmax b (right_mem_Icc.mpr hab)
  have vb := mul_le_mul_of_nonneg_left zvar (Real.rpow_nonneg (ha.trans_le hab).le σ)
  have wa : 0 ≤ W a := Real.rpow_nonneg ha.le _
  have wb := mul_le_mul_of_nonneg_right (show W b-W a ≤ b^σ from sub_le_self _ wa) (one_div_nonneg.mpr hH.le)
  simp only [div_eq_mul_inv,one_mul] at bl br vb eint wb ⊢
  linarith only [bd,bl,br,vb,eint,wb]

/-- The bound holds through a stationary point and is uniform in the additive
frequency. The factor X^σ comes from scaling the dyadic interval. -/
private theorem uniform_bound :
    ∀ (X a b σ γ β : ℝ), 0 < X → X ≤ a → a ≤ b → b ≤ 2*X →
      0 ≤ σ → σ ≤ 1 → γ ≠ 0 →
      ‖∫ x in a..b, ((x^(σ-1):ℝ):ℂ) *
        Complex.exp (((β*x+γ*Real.log x:ℝ):ℂ)*Complex.I)‖ ≤
        X^σ * min 1 ((3+5*Real.pi)/Real.sqrt |γ|) := by
  intro X a b σ γ β hX ha hab hb hσ hσ' hγ
  let l := a/X
  let r := b/X
  have h1 : 1 ≤ l := (one_le_div hX).mpr ha
  have hlr : l ≤ r := div_le_div_of_nonneg_right hab hX.le
  have h2 : r ≤ 2 := (div_le_iff₀ hX).mpr hb
  let z : ℂ := ((X^(σ-1):ℝ):ℂ)*wave (γ*Real.log X)
  have hz : ‖z‖ = X^(σ-1) := by
    simp only [z, norm_mul, wave_norm, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hX.le _)]
  have eqn : (∫ x in l..r, kernel σ β γ (X*x)) = z * (∫ x in l..r, kernel σ (β*X) γ x) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hlr] at hx
    exact rescale hX (zero_lt_one.trans_le (h1.trans hx.1)) σ β γ
  have sub := intervalIntegral.integral_comp_mul_left (kernel σ β γ) (a := l) (b := r) hX.ne'
  have hx1 : X*l = a := by dsimp [l]; field_simp
  have hx2 : X*r = b := by dsimp [r]; field_simp
  rw [sub,hx1,hx2] at eqn
  have eqnorm := congrArg norm eqn
  simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hX), norm_mul, hz] at eqnorm
  have hxpow : X * X^(σ-1) = X^σ := by
    calc
      _ = X^(1:ℝ) * X^(σ-1) := by rw [Real.rpow_one]
      _ = X^(1+(σ-1)) := (Real.rpow_add hX _ _).symm
      _ = _ := by rw [show (1:ℝ)+(σ-1)=σ by ring]
  change ‖∫ x in a..b, kernel σ β γ x‖ ≤ _
  calc
    _ = X*(X^(σ-1) * ‖∫ x in l..r, kernel σ (β*X) γ x‖) := by
      rw [← eqnorm, ← mul_assoc, mul_inv_cancel₀ hX.ne', one_mul]
    _ ≤ X^σ * min 1 ((3+5*Real.pi)/Real.sqrt |γ|) := by
      rw [← mul_assoc, hxpow]
      exact mul_le_mul_of_nonneg_left (dyadic h1 hlr h2 hγ hσ hσ' (β*X)) (Real.rpow_nonneg hX.le _)



/-- A dyadic piece of the additively twisted zero kernel. The curvature bound is
uniform in the frequency, and a lower bound on the absolute phase slope gives
stronger decay when the interval misses the stationary point. -/
theorem per_ordinate :
    ∀ (X a b σ γ β : ℝ), 0 < X → X ≤ a → a ≤ b → b ≤ 2*X → 0 ≤ σ → σ ≤ 1 →
      let K := ∫ x in a..b, ((x^(σ-1):ℝ):ℂ) *
        Complex.exp (((β*x+γ*Real.log x:ℝ):ℂ)*Complex.I)
      ‖K‖ ≤ X^σ ∧
      (γ ≠ 0 → ‖K‖ ≤ X^σ * ((3+5*Real.pi)/Real.sqrt |γ|)) ∧
      ∀ H : ℝ, 0 < H → (∀ x ∈ Set.Icc a b, H ≤ |β*x+γ|) → ‖K‖ ≤ 5*b^σ/H := by
  intro X a b σ γ β hX ha hab hb hσ hσ' K
  refine ⟨?_, ?_, fun H hH hsep => separated (hX.trans_le ha) hab hσ hH hsep⟩
  · have h := intervalIntegral.norm_integral_le_of_norm_le_const (f := kernel σ β γ)
      (C := X^(σ-1)) (a := a) (b := b) (fun x hx => by
        rw [uIoc_of_le hab] at hx
        have hxx := ha.trans hx.1.le
        rw [kernel,norm_mul,wave_norm,mul_one,Complex.norm_real,Real.norm_eq_abs,
          abs_of_nonneg (Real.rpow_nonneg (hX.le.trans hxx) _)]
        exact Real.rpow_le_rpow_of_nonpos hX hxx (sub_nonpos.mpr hσ'))
    rw [abs_of_nonneg (sub_nonneg.mpr hab)] at h
    have hb' : b-a ≤ X := by linarith
    apply h.trans
    calc
      _ ≤ X^(σ-1)*X := mul_le_mul_of_nonneg_left hb' (Real.rpow_nonneg hX.le _)
      _ = _ := by rw [Real.rpow_sub_one hX.ne', div_mul_cancel₀ _ hX.ne']
  · intro hγ
    exact (uniform_bound X a b σ γ β hX ha hab hb hσ hσ' hγ).trans
      (mul_le_mul_of_nonneg_left (min_le_right ..) (Real.rpow_nonneg hX.le _))
end GoldbachOscillation
end

section
open Set Filter MeasureTheory Complex
open scoped Topology Interval

noncomputable section

namespace GoldbachTwistedMellin

/-- The trapezoid rises on [a,a+1] and falls on [b,b+1]. For integral
endpoints it agrees with the sharp interval (a,b] at every integer. -/
def taper (a b x : ℝ) : ℝ := max 0 (min (x-a) (min 1 (b+1-x)))

def phase (β x : ℝ) : ℂ := Complex.exp (((β*x:ℝ):ℂ)*Complex.I)

def test (a b β x : ℝ) : ℂ := (taper a b x:ℂ)*phase β x

def transform (a b β : ℝ) (s : ℂ) : ℂ := mellin (test a b β) s

theorem taper_left {a b x : ℝ} (h : x ≤ a) : taper a b x = 0 := by
  exact max_eq_left ((min_le_left ..).trans (sub_nonpos.mpr h))

theorem taper_right {a b x : ℝ} (h : b+1 ≤ x) : taper a b x = 0 := by
  exact max_eq_left ((min_le_right ..).trans ((min_le_right ..).trans (sub_nonpos.mpr h)))

theorem taper_rise {a b x : ℝ} (h : a+1 ≤ b) (hx : x ∈ Icc a (a+1)) :
    taper a b x = x-a := by
  rw [taper,min_eq_left (le_min (by linarith [hx.2]) (by linarith [hx.1,hx.2])),
    max_eq_right (sub_nonneg.mpr hx.1)]

theorem taper_flat {a b x : ℝ} (hx : x ∈ Icc (a+1) b) : taper a b x = 1 := by
  rw [taper,min_eq_left (show 1 ≤ b+1-x by linarith [hx.2]),
    min_eq_right (show 1 ≤ x-a by linarith [hx.1]),max_eq_right zero_le_one]

theorem taper_fall {a b x : ℝ} (h : a+1 ≤ b) (hx : x ∈ Icc b (b+1)) :
    taper a b x = b+1-x := by
  rw [taper,min_eq_right (show b+1-x ≤ 1 by linarith [hx.1]),
    min_eq_right (show b+1-x ≤ x-a by linarith [hx.1]),max_eq_right (sub_nonneg.mpr hx.2)]

theorem taper_nat (a b k : ℕ) :
    taper a b k = if k ∈ Finset.Ioc a b then 1 else 0 := by
  split_ifs with h
  · have hx := Finset.mem_Ioc.mp h
    apply taper_flat
    constructor
    · exact_mod_cast hx.1
    · exact_mod_cast hx.2
  · by_cases hk : k ≤ a
    · exact taper_left (by exact_mod_cast hk)
    · apply taper_right
      have hb : b+1 ≤ k := by simp only [Finset.mem_Ioc] at h; omega
      exact_mod_cast hb

theorem continuous_taper (a b : ℝ) : Continuous (taper a b) := by unfold taper; fun_prop

theorem phase_deriv (β x : ℝ) : HasDerivAt (phase β) (phase β x*((β:ℂ)*I)) x := by
  have d := ((((hasDerivAt_id (x:ℂ)).const_mul (β:ℂ)).mul_const I).cexp).comp_ofReal
  change HasDerivAt (fun y : ℝ => Complex.exp (((β*y:ℝ):ℂ)*I)) _ x
  simpa [phase,mul_assoc] using d

theorem continuous_phase (β : ℝ) : Continuous (phase β) :=
  continuous_iff_continuousAt.mpr fun x => (phase_deriv β x).continuousAt

@[simp] theorem norm_phase (β x : ℝ) : ‖phase β x‖ = 1 := by simp [phase,Complex.norm_exp]

theorem continuous_test (a b β : ℝ) : Continuous (test a b β) :=
  (continuous_ofReal.comp (continuous_taper a b)).mul (continuous_phase β)

theorem compact_test (a b β : ℝ) : HasCompactSupport (test a b β) := by
  apply HasCompactSupport.intro' (K := Icc a (b+1)) isCompact_Icc isClosed_Icc
  intro x hx
  rcases not_and_or.mp (show ¬(a ≤ x ∧ x ≤ b+1) from hx) with hl | hr
  · simp [test,taper_left (le_of_not_ge hl)]
  · simp [test,taper_right (le_of_not_ge hr)]

private theorem test_top (a b β p : ℝ) : test a b β =O[atTop] (fun x : ℝ => x^p) := by
  apply Asymptotics.IsBigO.of_bound (c := 0)
  filter_upwards [eventually_ge_atTop (b+1)] with x hx
  simp [test,taper_right hx]

private theorem test_bot {a : ℝ} (ha : 0 < a) (b β p : ℝ) :
    test a b β =O[𝓝[>] (0:ℝ)] (fun x : ℝ => x^p) := by
  apply Asymptotics.IsBigO.of_bound (c := 0)
  filter_upwards [(eventually_lt_nhds ha).filter_mono (nhdsWithin_le_nhds (s := Ioi (0:ℝ)))] with x hx
  simp [test,taper_left hx.le]

theorem analytic_transform {a : ℝ} (ha : 0 < a) (b β : ℝ) :
    Differentiable ℂ (transform a b β) := by
  intro s
  exact mellin_differentiableAt_of_isBigO_rpow (a := s.re+1) (b := s.re-1)
    ((continuous_test a b β).locallyIntegrable.locallyIntegrableOn _)
    (test_top ..) (by linarith) (test_bot ha ..) (by linarith)

/-- The integral against the trapezoid is a difference of unit averages of
any primitive. This identity is used for both stationary and nonstationary phases. -/
theorem window_primitive {a b : ℝ} (hab : a+1 ≤ b) (f P : ℝ → ℂ)
    (hc : ContinuousOn f (Icc a (b+1))) (hd : ∀ x ∈ Icc a (b+1), HasDerivAt P (f x) x) :
    (∫ x in a..b+1, (taper a b x:ℂ)*f x) =
      (∫ x in b..b+1, P x) - ∫ x in a..a+1, P x := by
  have ab : a ≤ b := by linarith
  have a1 : a ≤ a+1 := by linarith
  have b1 : b ≤ b+1 := by linarith
  have hP : ContinuousOn P (Icc a (b+1)) := fun x hx =>
    (hd x hx).continuousAt.continuousWithinAt
  have iW {l r : ℝ} (hl : a ≤ l) (hr : r ≤ b+1) (hlr : l ≤ r) :
      IntervalIntegrable (fun x => (taper a b x:ℂ)*f x) volume l r :=
    ((continuous_ofReal.comp (continuous_taper a b)).continuousOn.mul
      (hc.mono (Icc_subset_Icc hl hr))).intervalIntegrable_of_Icc hlr
  have ip {l r : ℝ} (hl : a ≤ l) (hr : r ≤ b+1) (hlr : l ≤ r)
      (u : ℝ → ℂ) (v : ℂ) (hu : ∀ x, HasDerivAt u v x) :
      (∫ x in l..r, u x*f x) = u r*P r-u l*P l-(∫ x in l..r, v*P x) := by
    apply intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    · exact (continuous_iff_continuousAt.mpr fun x => (hu x).continuousAt).continuousOn
    · rw [uIcc_of_le hlr]
      exact hP.mono (Icc_subset_Icc hl hr)
    · exact fun x _ => hu x
    · intro x hx
      rw [min_eq_left hlr,max_eq_right hlr] at hx
      exact hd x ⟨hl.trans hx.1.le,hx.2.le.trans hr⟩
    · exact intervalIntegrable_const
    · exact (hc.mono (Icc_subset_Icc hl hr)).intervalIntegrable_of_Icc hlr
  have rise : (∫ x in a..a+1, (taper a b x:ℂ)*f x) = P (a+1) - ∫ x in a..a+1, P x := by
    let u := fun x : ℝ => (x:ℂ)-a
    have hu (x : ℝ) : HasDerivAt u 1 x := by
      simpa [u] using ((hasDerivAt_id (x:ℂ)).sub_const (a:ℂ)).comp_ofReal
    rw [intervalIntegral.integral_congr (g := fun x => u x*f x) (fun x hx => by
      rw [uIcc_of_le a1] at hx
      simp only [u,taper_rise hab hx,ofReal_sub]),ip le_rfl (by linarith) a1 u 1 hu]
    simp [u]
  have mid : (∫ x in a+1..b, (taper a b x:ℂ)*f x) = P b-P (a+1) := by
    rw [intervalIntegral.integral_congr (g := fun x => f x) (fun x hx => by
      rw [uIcc_of_le hab] at hx
      simp [taper_flat hx])]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x hx => hd x ((Icc_subset_Icc a1 b1) ((uIcc_of_le hab) ▸ hx)))
      ((hc.mono (Icc_subset_Icc a1 b1)).intervalIntegrable_of_Icc hab)
  have fall : (∫ x in b..b+1, (taper a b x:ℂ)*f x) = -P b + ∫ x in b..b+1, P x := by
    let u := fun x : ℝ => (b:ℂ)+1-x
    have hu (x : ℝ) : HasDerivAt u (-1) x := by
      simpa [u] using ((hasDerivAt_id (x:ℂ)).const_sub ((b:ℂ)+1)).comp_ofReal
    rw [intervalIntegral.integral_congr (g := fun x => u x*f x) (fun x hx => by
      rw [uIcc_of_le b1] at hx
      simp only [u,taper_fall hab hx,ofReal_sub,ofReal_add,ofReal_one]),ip ab le_rfl b1 u (-1) hu]
    simp [u,intervalIntegral.integral_neg]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (iW le_rfl b1 ab) (iW ab le_rfl b1),
    ← intervalIntegral.integral_add_adjacent_intervals (iW le_rfl (by linarith) a1) (iW a1 b1 hab),
    rise,mid,fall]
  abel

def density (β : ℝ) (s : ℂ) (x : ℝ) : ℂ := phase β x*(x:ℂ)^(s-1)

theorem continuousAt_density (β : ℝ) (s : ℂ) {x : ℝ} (hx : 0 < x) :
    ContinuousAt (density β s) x :=
  (continuous_phase β).continuousAt.mul
    (differentiableAt_id.ofReal_cpow_const (s-1) hx.ne').continuousAt

theorem integral_density {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (β : ℝ) (s : ℂ) :
    IntervalIntegrable (density β s) volume a b :=
  (show ContinuousOn (density β s) (Icc a b) from fun _ hx =>
    (continuousAt_density β s (ha.trans_le hx.1)).continuousWithinAt).intervalIntegrable_of_Icc hab

theorem transform_eq_taper_integral {a b : ℝ} (ha : 0 < a) (hab : a+1 ≤ b) (β : ℝ) (s : ℂ) :
    transform a b β s = ∫ x in a..b+1, (taper a b x:ℂ)*density β s x := by
  rw [transform,mellin,intervalIntegral.integral_of_le (show a ≤ b+1 by linarith)]
  simp only [smul_eq_mul]
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (s := Ioc a (b+1)) (t := Ioi (0:ℝ)) measurableSet_Ioi
    (fun x hx => ha.trans hx.1) (fun x hx => by
      rcases le_or_gt x a with hl | hl
      · simp [test,taper_left hl]
      · have hr : b+1 ≤ x := le_of_not_ge fun h => hx.2 ⟨hl,h⟩
        simp [test,taper_right hr])]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro x _
  unfold test density
  ring

/-- The integer-exact trapezoid is the average of translated sharp intervals.
The identity keeps the oscillatory phase, not just its absolute value. -/
theorem transform_eq_average {a b : ℝ} (ha : 0 < a) (hab : a+1 ≤ b) (β : ℝ) (s : ℂ) :
    transform a b β s = ∫ u in (0:ℝ)..1, ∫ x in (a+u)..(b+u), density β s x := by
  let f := density β s
  let P (v : ℝ) := ∫ x in a..v, f x
  have ab : a ≤ b := by linarith
  have hd (x : ℝ) (hx : x ∈ Icc a (b+1)) : HasDerivAt P (f x) x := by
    apply intervalIntegral.integral_hasDerivAt_right (integral_density ha hx.1 β s)
    · exact ContinuousAt.stronglyMeasurableAtFilter (s := Ioi (0:ℝ)) isOpen_Ioi
        (fun y hy => continuousAt_density β s hy) x (ha.trans_le hx.1)
    · exact continuousAt_density β s (ha.trans_le hx.1)
  have hc : ContinuousOn f (Icc a (b+1)) := fun x hx =>
    (continuousAt_density β s (ha.trans_le hx.1)).continuousWithinAt
  have pc : ContinuousOn P (Icc a (b+1)) := fun x hx => (hd x hx).continuousAt.continuousWithinAt
  have shift (l : ℝ) (hl : a ≤ l) (hl' : l ≤ b) :
      IntervalIntegrable (fun u => P (l+u)) volume 0 1 := by
    have hmap : MapsTo (fun u : ℝ => l+u) (Icc 0 1) (Icc a (b+1)) :=
      fun u hu => ⟨by linarith [hu.1],by linarith [hu.2]⟩
    exact (pc.comp (continuous_const.add continuous_id).continuousOn hmap).intervalIntegrable_of_Icc zero_le_one
  rw [transform_eq_taper_integral ha hab,window_primitive hab f P hc hd]
  have he : (∫ u in (0:ℝ)..1, ∫ x in (a+u)..(b+u), f x) =
      ∫ u in (0:ℝ)..1, (P (b+u)-P (a+u)) := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le zero_le_one] at hu
    exact eq_sub_of_add_eq' (intervalIntegral.integral_add_adjacent_intervals
      (integral_density ha (by linarith [hu.1]: a ≤ a+u) β s)
      (integral_density (by linarith [hu.1] : 0 < a+u) (by linarith : a+u ≤ b+u) β s))
  change _ = ∫ u in (0:ℝ)..1, ∫ x in (a+u)..(b+u), f x
  rw [he,intervalIntegral.integral_sub (shift b ab le_rfl) (shift a le_rfl ab),
    intervalIntegral.integral_comp_add_left,intervalIntegral.integral_comp_add_left]
  simp

theorem density_eq {x : ℝ} (hx : 0 < x) (β : ℝ) (s : ℂ) :
    density β s x = ((x^(s.re-1):ℝ):ℂ)*
      Complex.exp (((β*x+s.im*Real.log x:ℝ):ℂ)*I) := by
  rw [density,phase,Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'),
    ← Complex.ofReal_log hx.le,Real.rpow_def_of_pos hx,Complex.ofReal_exp,
    ← Complex.exp_add,← Complex.exp_add]
  congr 1
  apply Complex.ext <;> simp
  ring

/-- Any uniform bound for sharp subinterval integrals bounds the transform
of the exact integer window with the same constant. -/
theorem norm_transform_le {X a b D : ℝ} (hX : 0 < X) (ha : X ≤ a) (hab : a+1 ≤ b)
    (hb : b+1 ≤ 2*X) (β : ℝ) (s : ℂ)
    (hd : ∀ l r : ℝ, X ≤ l → l ≤ r → r ≤ 2*X → ‖∫ x in l..r, density β s x‖ ≤ D) :
    ‖transform a b β s‖ ≤ D := by
  rw [transform_eq_average (hX.trans_le ha) hab]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1) (C := D)
    (f := fun u : ℝ => ∫ x in (a+u)..(b+u), density β s x) (fun u hu => by
      rw [uIoc_of_le zero_le_one] at hu
      exact hd _ _ (by linarith [hu.1]) (by linarith) (by linarith [hu.2]))
  simpa using h

theorem norm_window_modes {X a b : ℝ} (hX : 0 < X) (ha : X ≤ a) (hab : a+1 ≤ b)
    (hb : b+1 ≤ 2*X) (β : ℝ) (s : ℂ) (hσ : 0 ≤ s.re) (hσ' : s.re ≤ 1) :
    ‖transform a b β s‖ ≤ X^s.re ∧
      (s.im ≠ 0 → ‖transform a b β s‖ ≤ X^s.re*((3+5*Real.pi)/Real.sqrt |s.im|)) ∧
      (0 < |s.im| → 4*|β| * X ≤ |s.im| →
        ‖transform a b β s‖ ≤ 20*X^s.re/|s.im|) := by
  have bounds (l r : ℝ) (hl : X ≤ l) (hlr : l ≤ r) (hr : r ≤ 2*X) :
      let K := ∫ x in l..r, density β s x
      ‖K‖ ≤ X^s.re ∧ (s.im ≠ 0 → ‖K‖ ≤ X^s.re*((3+5*Real.pi)/Real.sqrt |s.im|)) ∧
        ∀ H : ℝ, 0 < H → (∀ x ∈ Icc l r, H ≤ |β*x+s.im|) → ‖K‖ ≤ 5*r^s.re/H := by
    have he := intervalIntegral.integral_congr (μ := volume) (f := density β s)
      (a := l) (b := r) (fun x hx => density_eq ((hX.trans_le hl).trans_le (((uIcc_of_le hlr) ▸ hx).1)) β s)
    dsimp only
    rw [he]
    exact GoldbachOscillation.per_ordinate X l r s.re s.im β hX hl hlr hr hσ hσ'
  refine ⟨norm_transform_le hX ha hab hb β s (fun l r hl hm hr => (bounds l r hl hm hr).1),?_,?_⟩
  · intro ht
    exact norm_transform_le hX ha hab hb β s (fun l r hl hm hr => (bounds l r hl hm hr).2.1 ht)
  · intro ht hcut
    apply norm_transform_le hX ha hab hb β s
    intro l r hl hlr hr
    have hsep (x : ℝ) (hx : x ∈ Icc l r) : |s.im|/2 ≤ |β*x+s.im| := by
      have h := abs_add_le (β*x+s.im) (-(β*x))
      rw [show β*x+s.im+ -(β*x) = s.im by ring,abs_neg,abs_mul,abs_of_nonneg (hX.le.trans (hl.trans hx.1))] at h
      have hj := mul_le_mul_of_nonneg_left (hx.2.trans hr) (abs_nonneg β)
      linarith only [h,hcut,hj]
    have hpow : r^s.re ≤ 2*X^s.re := calc
      _ ≤ (2*X)^s.re := Real.rpow_le_rpow (hX.le.trans (hl.trans hlr)) hr hσ
      _ = (2:ℝ)^s.re * X^s.re := Real.mul_rpow (by norm_num) hX.le
      _ ≤ _ := mul_le_mul_of_nonneg_right (by
        simpa using Real.rpow_le_rpow_of_exponent_le (show (1:ℝ) ≤ 2 by norm_num) hσ')
        (Real.rpow_nonneg hX.le _)
    apply ((bounds l r hl hlr hr).2.2 _ (half_pos ht) hsep).trans
    rw [div_div_eq_mul_div]
    exact (div_le_div_iff_of_pos_right ht).mpr (by linarith only [hpow])

end GoldbachTwistedMellin
end
end

section
open Set MeasureTheory Complex
open scoped Interval

noncomputable section
namespace GoldbachTwistedMellin

private def freq (β : ℝ) : ℂ := (β:ℂ)*I
private theorem norm_freq (β : ℝ) : ‖freq β‖ = |β| := by simp [freq,Real.norm_eq_abs]

theorem density_succ (β : ℝ) (s : ℂ) (x : ℝ) :
    density β (s+1) x = phase β x*(x:ℂ)^s := by simp [density]

private theorem pow_deriv {s : ℂ} (hs : 0 < s.re) (β : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (density β (s+1)) (s*density β s x+freq β*density β (s+1) x) x := by
  have sn : s ≠ 0 := fun h => by simp [h] at hs
  have he := (phase_deriv β x).mul (hasDerivAt_ofReal_cpow_const hx.ne' sn)
  rw [show density β (s+1) = fun y : ℝ => phase β y*(y:ℂ)^s from funext (density_succ β s)]
  convert he using 1
  unfold density freq
  ring

private theorem pow_ibp {l r : ℝ} (hl : 0 < l) (hlr : l ≤ r) (β : ℝ) {s : ℂ} (hs : 0 < s.re) :
    s*(∫ x in l..r, density β s x) = density β (s+1) r - density β (s+1) l -
      freq β*(∫ x in l..r, density β (s+1) x) := by
  have hder := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := density β (s+1)) (a := l) (b := r)
    (fun x hx => pow_deriv hs β (hl.trans_le (((uIcc_of_le hlr) ▸ hx).1)))
    (((integral_density hl hlr β s).const_mul s).add ((integral_density hl hlr β (s+1)).const_mul (freq β)))
  rw [intervalIntegral.integral_add ((integral_density hl hlr β s).const_mul s)
    ((integral_density hl hlr β (s+1)).const_mul (freq β)),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul] at hder
  exact eq_sub_of_add_eq hder

/-- Integration by parts for the whole piecewise linear window. The first
derivative contains two unit end intervals and the derivative of the twist. -/
theorem transform_recurrence {a b : ℝ} (ha : 0 < a) (hab : a+1 ≤ b) (β : ℝ) {s : ℂ} (hs : 0 < s.re) :
    s*transform a b β s = (∫ x in b..b+1, density β (s+1) x) -
      (∫ x in a..a+1, density β (s+1) x) - freq β*transform a b β (s+1) := by
  have hL : a ≤ b+1 := by linarith
  have cont (z : ℂ) : ContinuousOn (density β z) (Icc a (b+1)) :=
    fun x hx => (continuousAt_density β z (ha.trans_le hx.1)).continuousWithinAt
  have wcont (z : ℂ) : ContinuousOn (fun x => (taper a b x:ℂ)*density β z x) (Icc a (b+1)) :=
    (continuous_ofReal.comp (continuous_taper a b)).continuousOn.mul (cont z)
  have wp := window_primitive hab
    (fun x => s*density β s x+freq β*density β (s+1) x) (density β (s+1))
    (((cont s).const_mul _).add ((cont (s+1)).const_mul _))
    (fun x hx => pow_deriv hs β (ha.trans_le hx.1))
  have point (x : ℝ) : (taper a b x:ℂ)*(s*density β s x+freq β*density β (s+1) x) =
      s*((taper a b x:ℂ)*density β s x)+freq β*((taper a b x:ℂ)*density β (s+1) x) := by ring
  simp_rw [point] at wp
  rw [intervalIntegral.integral_add (((wcont s).intervalIntegrable_of_Icc hL).const_mul s)
    (((wcont (s+1)).intervalIntegrable_of_Icc hL).const_mul (freq β)),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
    ← transform_eq_taper_integral ha hab,← transform_eq_taper_integral ha hab] at wp
  exact eq_sub_of_add_eq wp

/-- The derivative of the smooth phase is bounded for |β|≤1. One integration
by parts gives a common first-order bound for the integrals in the recurrence. -/
private theorem endpoint_bound {X l r β : ℝ} (hX : 1 ≤ X) (hl : X ≤ l) (hlr : l ≤ r)
    (hr : r ≤ 2*X) (hβ : |β| ≤ 1) {s : ℂ} (hs : 0 < s.re) (hs' : s.re ≤ 2)
    (hn : 0 < ‖s+1‖) :
    ‖∫ x in l..r, density β (s+1) x‖ ≤ 32*X^4/‖s+1‖ := by
  have xl : 0 < l := zero_lt_one.trans_le (hX.trans hl)
  have bnd (x : ℝ) (hx : x ∈ Icc l r) : ‖density β ((s+1)+1) x‖ ≤ (2*X)^3 := by
    rw [density_succ,norm_mul,norm_phase,one_mul,norm_cpow_eq_rpow_re_of_pos (xl.trans_le hx.1)]
    rw [add_re,one_re]
    calc
      x^(s.re+1) ≤ (2*X)^(s.re+1) :=
        Real.rpow_le_rpow (xl.le.trans hx.1) (hx.2.trans hr) (by linarith)
      _ ≤ (2*X)^(3:ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      _ = _ := by norm_num
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := l) (b := r)
    (fun x hx => bnd x (by rw [uIoc_of_le hlr] at hx; exact ⟨hx.1.le,hx.2⟩))
  rw [abs_of_nonneg (sub_nonneg.mpr hlr)] at hb
  have e := pow_ibp xl hlr β (s := s+1) (by simp only [add_re,one_re]; linarith)
  have he := (norm_sub_le .. : ‖(density β ((s+1)+1) r - density β ((s+1)+1) l) -
      freq β*(∫ x in l..r, density β ((s+1)+1) x)‖ ≤ _)
  rw [← e,norm_mul,norm_mul,norm_freq] at he
  apply (le_div_iff₀ hn).mpr
  rw [mul_comm]
  have coeff := mul_le_of_le_one_left (norm_nonneg (∫ x in l..r, density β ((s+1)+1) x)) hβ
  have len : r-l ≤ 2*X := by linarith
  have hlen := mul_le_mul_of_nonneg_left len (by positivity : 0 ≤ (2*X)^3)
  have x3 : X^3 ≤ X^4 := by
    simpa only [pow_succ] using (le_mul_of_one_le_right (by positivity : 0 ≤ X^3) hX)
  linarith only [he,norm_sub_le (density β ((s+1)+1) r) (density β ((s+1)+1) l),
    bnd r (right_mem_Icc.mpr hlr),bnd l (left_mem_Icc.mpr hlr),coeff,hb,hlen,x3]

/-- Uniform quadratic decay throughout the contour strip, including the
unit-width transition regions. This bound is only used beyond polynomial height. -/
theorem norm_transform_tail {X a b β : ℝ} (hX : 1 ≤ X) (ha : X ≤ a) (hab : a+1 ≤ b)
    (hb : b+1 ≤ 2*X) (hβ : |β| ≤ 1) (s : ℂ) (hs : 0 < s.re) (hs' : s.re ≤ 2)
    (ht : 0 < |s.im|) : ‖transform a b β s‖ ≤ 96*X^4/|s.im|^2 := by
  have lt0 : 0 < X := zero_lt_one.trans_le hX
  have t1 : |s.im| ≤ ‖s+1‖ := by simpa using abs_im_le_norm (s+1)
  have t0 := abs_im_le_norm s
  have ext (l r : ℝ) (hl : X ≤ l) (hlr : l ≤ r) (hr : r ≤ 2*X) :=
    endpoint_bound hX hl hlr hr hβ hs hs' (ht.trans_le t1)
  have hB := ext b (b+1) (by linarith) (by linarith) hb
  have hA := ext a (a+1) ha (by linarith) (by linarith)
  have hG := norm_transform_le lt0 ha hab hb β (s+1) ext
  have he := transform_recurrence (lt0.trans_le ha) hab β hs
  have triangle := norm_sub_le ((∫ x in b..b+1, density β (s+1) x)-(∫ x in a..a+1, density β (s+1) x))
    (freq β*transform a b β (s+1))
  rw [← he,norm_mul,norm_mul,norm_freq] at triangle
  have part := norm_sub_le (∫ x in b..b+1, density β (s+1) x) (∫ x in a..a+1, density β (s+1) x)
  have coeff := mul_le_of_le_one_left (norm_nonneg (transform a b β (s+1))) hβ
  have total : ‖s‖ * ‖transform a b β s‖ ≤ 96*X^4/‖s+1‖ := by
    simp only [div_eq_mul_inv] at hA hB hG ⊢
    linarith only [triangle,part,coeff,hA,hB,hG]
  have htprod := (le_div_iff₀ (ht.trans_le t1)).mp total
  apply (le_div_iff₀ (sq_pos_of_pos ht)).mpr
  calc
    _ = |s.im| * ‖transform a b β s‖*|s.im| := by ring
    _ ≤ _ := (mul_le_mul (mul_le_mul_of_nonneg_right t0 (norm_nonneg _)) t1 ht.le (by positivity)).trans htprod

/-- Twice integrate by parts, retaining the unit lengths of the window
transitions and the upper bound on the major-arc twist. -/
theorem norm_transform_major_tail {X a b β : ℝ} (hX : 1 ≤ X) (ha : X ≤ a)
    (hab : a+1 ≤ b) (hb : b+1 ≤ 2*X) (hβ : |β| ≤ 1) (hβX : |β|^2*X ≤ 64)
    (s : ℂ) (hs : 0 < s.re) (hs' : s.re ≤ 1) (ht : 0 < |s.im|) :
    ‖transform a b β s‖ ≤ 600*X^2/|s.im|^2 := by
  have hXPos : 0 < X := zero_lt_one.trans_le hX
  have haPos := hXPos.trans_le ha
  have hs₁ : 0 < (s+1).re := by simp only [add_re, one_re]; linarith
  have hdensity (x : ℝ) (hx : x ∈ Icc X (2*X)) :
      ‖density β (s+1+1) x‖ ≤ 4*X^2 := by
    have hxPos := hXPos.trans_le hx.1
    rw [density_succ, norm_mul, norm_phase, one_mul, norm_cpow_eq_rpow_re_of_pos hxPos,
      add_re, one_re]
    calc
      _ ≤ x^(2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (hX.trans hx.1) (by linarith)
      _ = x^2 := by norm_num
      _ ≤ (2*X)^2 := pow_le_pow_left₀ hxPos.le hx.2 2
      _ = _ := by ring
  have hinterval (l r : ℝ) (hl : X ≤ l) (hlr : l ≤ r) (hr : r ≤ 2*X) :
      ‖∫ x in l..r, density β (s+1+1) x‖ ≤ (4*X^2)*(r-l) := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := l) (b := r) (C := 4*X^2) (fun x hx => hdensity x (by
        rw [uIoc_of_le hlr] at hx
        exact ⟨hl.trans hx.1.le,hx.2.trans hr⟩))
    simpa only [abs_of_nonneg (sub_nonneg.mpr hlr)] using h
  have hunit (l : ℝ) (hl : X ≤ l) (hr : l+1 ≤ 2*X) :
      ‖∫ x in l..(l+1), density β (s+1+1) x‖ ≤ 4*X^2 := by
    simpa using hinterval l (l+1) hl (by linarith) hr
  have hedge (l : ℝ) (hl : X ≤ l) (hr : l+1 ≤ 2*X) :
      ‖s+1‖ * ‖∫ x in l..(l+1), density β (s+1) x‖ ≤ 12*X^2 := by
    let v := density β (s+1+1)
    have he := pow_ibp (hXPos.trans_le hl) (by linarith : l ≤ l+1) β hs₁
    have hsub := norm_sub_le (v (l+1)-v l) (freq β*(∫ x in l..(l+1), v x))
    change ‖v (l+1) - v l - freq β*(∫ x in l..(l+1), v x)‖ ≤ _ at hsub
    rw [← he, norm_mul, norm_mul, norm_freq] at hsub
    have hv (x : ℝ) (hx : x ∈ Icc X (2*X)) := hdensity x hx
    linarith only [hsub,norm_sub_le (v (l+1)) (v l),
      hv l ⟨hl,by linarith⟩,hv (l+1) ⟨by linarith,hr⟩,hunit l hl hr,
      mul_le_of_le_one_left (norm_nonneg (∫ x in l..(l+1), v x)) hβ]
  have htransform := norm_transform_le hXPos ha hab hb β (s+1+1) (D := 8*X^3)
    (fun l r hl hlr hr => (hinterval l r hl hlr hr).trans (by
      nlinarith only [mul_le_mul_of_nonneg_left (show r-l ≤ 2*X by linarith)
        (show 0 ≤ (4:ℝ)*X^2 by positivity)]))
  have hb' : X ≤ b := by linarith
  have ha' : a+1 ≤ 2*X := by linarith
  have hsecond : ‖s+1‖ * ‖transform a b β (s+1)‖ ≤
      8*X^2 + |β| * (8*X^3) := by
    let v := density β (s+1+1)
    have h := norm_sub_le ((∫ x in b..(b+1), v x) - (∫ x in a..(a+1), v x))
      (freq β*transform a b β (s+1+1))
    rw [← transform_recurrence haPos hab β hs₁, norm_mul, norm_mul, norm_freq] at h
    linarith only [h,norm_sub_le (∫ x in b..(b+1), v x) (∫ x in a..(a+1), v x),
      hunit b hb' hb, hunit a ha ha', mul_le_mul_of_nonneg_left htransform (abs_nonneg β)]
  have hsecondWeighted : |β| * (‖s+1‖ * ‖transform a b β (s+1)‖) ≤ 520*X^2 := calc
    _ ≤ |β| * (8*X^2 + |β| * (8*X^3)) := mul_le_mul_of_nonneg_left hsecond (abs_nonneg β)
    _ = |β| * (8*X^2)+(|β|^2*X)*(8*X^2) := by ring
    _ ≤ _ := by
      linarith only [mul_le_of_le_one_left (show 0 ≤ (8:ℝ)*X^2 by positivity) hβ,
        mul_le_mul_of_nonneg_right hβX (show 0 ≤ (8:ℝ)*X^2 by positivity)]
  have htotal : ‖s+1‖ * (‖s‖ * ‖transform a b β s‖) ≤ 600*X^2 := by
    let v := density β (s+1)
    have h := norm_sub_le ((∫ x in b..(b+1), v x) - (∫ x in a..(a+1), v x))
      (freq β*transform a b β (s+1))
    rw [← transform_recurrence haPos hab β hs, norm_mul, norm_mul, norm_freq] at h
    have h' := mul_le_mul_of_nonneg_left h (norm_nonneg (s+1))
    have hsub := mul_le_mul_of_nonneg_left
      (norm_sub_le (∫ x in b..(b+1), v x) (∫ x in a..(a+1), v x)) (norm_nonneg (s+1))
    dsimp [v] at h' hsub
    nlinarith only [h',hsub,hedge b hb' hb,hedge a ha ha',hsecondWeighted,sq_nonneg X]
  apply (le_div_iff₀ (sq_pos_of_pos ht)).mpr
  calc
    _ = |s.im| * (|s.im| * ‖transform a b β s‖) := by ring
    _ ≤ _ := (mul_le_mul (by simpa using abs_im_le_norm (s+1))
      (mul_le_mul_of_nonneg_right (abs_im_le_norm s) (norm_nonneg _)) (by positivity) (norm_nonneg _)).trans htotal

end GoldbachTwistedMellin
end
end

section
open Set Filter MeasureTheory Complex
open scoped Topology Interval

noncomputable section
namespace GoldbachTwistedMellin

theorem integrable_transform {X a b β σ : ℝ} (hX : 1 ≤ X) (ha : X ≤ a) (hab : a+1 ≤ b)
    (hb : b+1 ≤ 2*X) (hβ : |β| ≤ 1) (hs : 0 < σ) (hs' : σ ≤ 2) :
    Integrable (fun t : ℝ => transform a b β ((σ:ℂ)+(t:ℂ)*I)) := by
  let g := fun t : ℝ => transform a b β ((σ:ℂ)+(t:ℂ)*I)
  have hc : Continuous g := (analytic_transform (zero_lt_one.trans_le (hX.trans ha)) b β).continuous.comp
    (continuous_const.add (continuous_ofReal.mul continuous_const))
  obtain ⟨M,hM⟩ := (isCompact_Icc (α := ℝ) (a := -1) (b := 1)).exists_bound_of_continuousOn hc.continuousOn
  let C := 2*(max 0 M+96*X^4)
  refine (integrable_inv_one_add_sq.const_mul C).mono' hc.aestronglyMeasurable ?_
  filter_upwards with t
  change ‖g t‖ ≤ C*(1+t^2)⁻¹
  rw [← div_eq_mul_inv]
  apply (le_div_iff₀ (by positivity)).mpr
  by_cases ht : |t| ≤ 1
  · have h := hM t (abs_le.mp ht)
    have ht2 : t^2 ≤ 1 := by
      have hprod := mul_nonneg (sub_nonneg.mpr ht) (show 0 ≤ 1+|t| by positivity)
      nlinarith only [hprod,sq_abs t]
    have hm : ‖g t‖*(1+t^2) ≤ (max 0 M)*2 :=
      mul_le_mul (h.trans (le_max_right ..)) (by linarith) (by positivity) (le_max_left ..)
    dsimp [C]
    nlinarith only [hm,show 0 ≤ X^4 by positivity]
  · have ht' : 0 < |t| := by linarith only [lt_of_not_ge ht]
    have hbound := norm_transform_tail hX ha hab hb hβ ((σ:ℂ)+(t:ℂ)*I)
      (by simpa using hs) (by simpa using hs') (by simpa using ht')
    have hn : ‖g t‖*|t|^2 ≤ 96*X^4 := (le_div_iff₀ (by positivity)).mp (by simpa [g] using hbound)
    have hsq : 1 ≤ |t|^2 := by nlinarith only [lt_of_not_ge ht,sq_nonneg (|t|-1)]
    have hmul := mul_le_mul_of_nonneg_left (by nlinarith only [hsq,sq_abs t] : 1+t^2 ≤ 2*|t|^2) (norm_nonneg (g t))
    dsimp [C]
    nlinarith only [hmul,hn,le_max_left 0 M]

theorem mellinInv_transform {X a b β σ y : ℝ} (hX : 1 ≤ X) (ha : X ≤ a) (hab : a+1 ≤ b)
    (hb : b+1 ≤ 2*X) (hβ : |β| ≤ 1) (hs : 0 < σ) (hs' : σ ≤ 2) (hy : 0 < y) :
    mellinInv σ (transform a b β) y = test a b β y := by
  have ha0 := zero_lt_one.trans_le (hX.trans ha)
  have hm : MellinConvergent (test a b β) (σ:ℂ) := by
    apply mellinConvergent_of_isBigO_rpow (a := σ+1) (b := σ-1)
      ((continuous_test a b β).locallyIntegrable.locallyIntegrableOn _)
    · apply Asymptotics.IsBigO.of_bound (c := 0)
      filter_upwards [eventually_ge_atTop (b+1)] with x hx
      simp [test,taper_right hx]
    · simp
    · apply Asymptotics.IsBigO.of_bound (c := 0)
      filter_upwards [(eventually_lt_nhds ha0).filter_mono (nhdsWithin_le_nhds (s := Ioi (0:ℝ)))] with x hx
      simp [test,taper_left hx.le]
    · simp
  exact mellinInv_mellin_eq σ _ hy hm (integrable_transform hX ha hab hb hβ hs hs') (continuous_test a b β).continuousAt

-- The Dirichlet-series interchange follows the smoothing proof of PR #2486.
private theorem term_norm_vertical (a : ℕ → ℂ) (σ t : ℝ) (n : ℕ) :
    ‖LSeries.term a ((σ : ℂ) + (t : ℂ) * I) n‖ = ‖LSeries.term a (σ : ℂ) n‖ := by
  by_cases hn : n = 0
  · subst n
    simp
  · simp only [LSeries.term_of_ne_zero hn, norm_div,
      norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn), add_re, ofReal_re, mul_I_re, ofReal_im,
      neg_zero, add_zero]

private theorem term_continuous_vertical (a : ℕ → ℂ) (σ : ℝ) (n : ℕ) :
    Continuous (fun t : ℝ => LSeries.term a ((σ : ℂ) + (t : ℂ) * I) n) := by
  by_cases hn : n = 0
  · subst n
    simpa only [LSeries.term_zero] using (continuous_const : Continuous fun _ : ℝ => (0 : ℂ))
  · have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    have hline : Continuous (fun t : ℝ => (σ : ℂ) + (t : ℂ) * I) :=
      continuous_const.add (continuous_ofReal.mul continuous_const)
    simp_rw [LSeries.term_of_ne_zero hn, cpow_def_of_ne_zero hnC]
    exact continuous_const.div (continuous_exp.comp (continuous_const.mul hline))
      (fun _ => exp_ne_zero _)


theorem integrable_series_transform (a : ℕ → ℂ) (K : ℂ → ℂ) {σ : ℝ}
    (hK : Integrable (fun t : ℝ => K ((σ:ℂ)+(t:ℂ)*I)))
    (hAbs : Summable fun n => ‖LSeries.term a (σ : ℂ) n‖) :
    Integrable (fun t : ℝ => LSeries a ((σ : ℂ) + (t : ℂ) * I) *
      K ((σ : ℂ) + (t : ℂ) * I)) := by
  let z (t : ℝ) : ℂ := (σ : ℂ) + (t : ℂ) * I
  have hc : Continuous (fun t : ℝ => LSeries a (z t)) := by
    exact continuous_tsum (term_continuous_vertical a σ) hAbs
      (fun n t => le_of_eq (term_norm_vertical a σ t n))
  refine (hK.norm.const_mul (∑' n, ‖LSeries.term a (σ : ℂ) n‖)).mono'
    (hc.aestronglyMeasurable.mul hK.aestronglyMeasurable) ?_
  filter_upwards with t
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  have hS : Summable (fun n => ‖LSeries.term a (z t) n‖) :=
    hAbs.congr (fun n => (term_norm_vertical a σ t n).symm)
  exact (norm_tsum_le_tsum_norm hS).trans_eq (tsum_congr (term_norm_vertical a σ t))

/-- Mellin inversion with an absolutely convergent Dirichlet series. -/
theorem series_transform_inversion (a : ℕ → ℂ) (ha0 : a 0 = 0) (f : ℝ → ℂ) (K : ℂ → ℂ) {σ : ℝ}
    (hK : Integrable (fun t : ℝ => K ((σ:ℂ)+(t:ℂ)*I)))
    (hInvK : ∀ y : ℝ, 0 < y → mellinInv σ K y = f y)
    (hAbs : Summable fun n => ‖LSeries.term a (σ : ℂ) n‖) :
    (∑' n, a n * f n) =
      (1 / (2 * Real.pi)) • (∫ t : ℝ,
        LSeries a ((σ : ℂ) + (t : ℂ) * I) * K ((σ : ℂ) + (t : ℂ) * I)) := by
  let z (t : ℝ) : ℂ := (σ : ℂ) + (t : ℂ) * I
  let F (n : ℕ) (t : ℝ) : ℂ := LSeries.term a (z t) n * K (z t)
  have hN (n : ℕ) (t : ℝ) : ‖F n t‖ =
      ‖LSeries.term a (σ : ℂ) n‖ * ‖K (z t)‖ := by
    dsimp only [F]
    rw [norm_mul, term_norm_vertical]
  have hF (n : ℕ) : Integrable (F n) := by
    refine (hK.norm.const_mul ‖LSeries.term a (σ : ℂ) n‖).mono' ?_ ?_
    · exact (term_continuous_vertical a σ n).aestronglyMeasurable.mul hK.aestronglyMeasurable
    · filter_upwards with t
      exact le_of_eq (hN n t)
  have hFsum : Summable fun n => ∫ t : ℝ, ‖F n t‖ := by
    simp_rw [hN, integral_const_mul]
    exact hAbs.mul_right _
  have hInv (n : ℕ) : a n * f n =
      (1 / (2 * Real.pi)) • (∫ t : ℝ, F n t) := by
    by_cases hn : n = 0
    · subst n
      simp [F, ha0]
    have hnR : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    rw [← hInvK n hnR]
    unfold mellinInv
    simp only [F, z, LSeries.term_def₀ ha0, ofReal_natCast, smul_eq_mul, mul_assoc]
    rw [integral_const_mul]
    simp only [Algebra.smul_def]
    ring
  calc
    _ = ∑' n, (1 / (2 * Real.pi)) • (∫ t : ℝ, F n t) := tsum_congr hInv
    _ = (1 / (2 * Real.pi)) • (∑' n, ∫ t : ℝ, F n t) := tsum_const_smul'' _
    _ = (1 / (2 * Real.pi)) • (∫ t : ℝ, ∑' n, F n t) :=
      congrArg ((1 / (2 * Real.pi)) • ·) (integral_tsum_of_summable_integral_norm hF hFsum)
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards with t
      simp only [F, z, LSeries, tsum_mul_right]


open GoldbachSmoothing DirichletCharacter

theorem character_sum_eq_vertical {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {a b : ℕ} {X β : ℝ} (hX : 1 ≤ X) (ha : X ≤ (a:ℝ)) (hab : (a:ℝ)+1 ≤ b)
    (hb : (b:ℝ)+1 ≤ 2*X) (hβ : |β| ≤ 1) :
    (∑ n ∈ Finset.Ioc a b, twistedCoefficient χ n * phase β n) =
      (1/(2*Real.pi)) • ∫ t : ℝ, (-logDeriv (LFunction χ) (2+(t:ℂ)*I)) *
        transform a b β (2+(t:ℂ)*I) := by
  have hAbs : Summable fun n => ‖LSeries.term (twistedCoefficient χ) (2:ℂ) n‖ :=
    summable_norm_iff.mpr (χ.LSeriesSummable_twist_vonMangoldt (by norm_num))
  have hEq (t : ℝ) : LSeries (twistedCoefficient χ) (2+(t:ℂ)*I) =
      -logDeriv (LFunction χ) (2+(t:ℂ)*I) := LSeries_twistedCoefficient_eq χ (by norm_num)
  have h := series_transform_inversion (twistedCoefficient χ) (twistedCoefficient_zero χ)
    (test a b β) (transform a b β) (σ := 2) (integrable_transform hX ha hab hb hβ (by norm_num) le_rfl)
    (fun _ hy => mellinInv_transform hX ha hab hb hβ (by norm_num) le_rfl hy) (by simpa using hAbs)
  simp only [ofReal_ofNat,hEq] at h
  rw [← h, tsum_eq_sum (s := Finset.Ioc a b)]
  · apply Finset.sum_congr rfl
    intro n hn
    simp [test,taper_nat,hn]
  · intro n hn
    simp [test,taper_nat,hn]

end GoldbachTwistedMellin
end
end

section
open Set Filter MeasureTheory Complex Goldbach DirichletCharacter
open scoped Topology Interval

noncomputable section
namespace GoldbachTwistedMellin

def line (σ t : ℝ) : ℂ := (σ:ℂ)+(t:ℂ)*I

@[simp] theorem re_line (σ t : ℝ) : (line σ t).re = σ := by simp [line]
@[simp] theorem im_line (σ t : ℝ) : (line σ t).im = t := by simp [line]

theorem continuous_line (σ : ℝ) : Continuous (line σ) :=
  continuous_const.add (continuous_ofReal.mul continuous_const)

theorem left_pole_dist {σ : ℝ} (hs : σ ≤ 3/4) (t : ℝ) : 1/4 ≤ ‖line σ t-1‖ := by
  have h := neg_le_abs (line σ t-1).re
  have h' := abs_re_le_norm (line σ t-1)
  simp only [sub_re,re_line,one_re] at h h'
  linarith

theorem horizontal_pole_dist {t : ℝ} (ht : 1 ≤ |t|) (σ : ℝ) : 1/4 ≤ ‖line σ t-1‖ := by
  have h := abs_im_le_norm (line σ t-1)
  simp only [sub_im,im_line,one_im,sub_zero] at h
  linarith

theorem contour_right (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ) :
    contourLog χ (line 2 t) = -logDeriv (LFunction χ) (line 2 t) := by
  have hn : line 2 t ≠ 1 := by intro h; have := congrArg Complex.re h; simp at this
  have hL := LFunction_ne_zero_of_one_le_re χ (Or.inr hn) (by simp)
  rw [contourLog,logDeriv_regularizedL_eq χ hn hL]
  ring

end GoldbachTwistedMellin
end
end

section
open Set Filter MeasureTheory Complex Goldbach DirichletCharacter MeromorphicOn
open scoped Topology Interval
noncomputable section
namespace GoldbachTwistedMellin

/-- Every zero on a compact rectangle has finite multiplicity and the set is finite.
The rectangle may cross the critical line. -/
theorem finite_box_zeros {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (a b c d : ℝ) :
    {z : ℂ | z ∈ Icc a b ×ℂ Icc c d ∧ regularizedL χ z = 0}.Finite := by
  let U := Icc a b ×ℂ Icc c d
  have hcompact : IsCompact U := isCompact_Icc.reProdIm isCompact_Icc
  apply ((divisor (regularizedL χ) U).finiteSupport hcompact).subset
  intro z hz
  change divisor (regularizedL χ) U z ≠ 0
  rw [regularizedL_divisor_apply χ hz.1]
  exact_mod_cast ((regularizedL_analyticOrderNatAt_pos_iff χ z).mpr hz.2).ne'

noncomputable def boxZeros {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (a b c d : ℝ) : Finset ℂ := (finite_box_zeros χ a b c d).toFinset

theorem mem_boxZeros {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (a b c d : ℝ) (z : ℂ) :
    z ∈ boxZeros χ a b c d ↔ z ∈ Icc a b ×ℂ Icc c d ∧ regularizedL χ z = 0 :=
  (finite_box_zeros χ a b c d).mem_toFinset

theorem regularizedL_ne_zero_right {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {z : ℂ} (hz : 1 < z.re) : regularizedL χ z ≠ 0 := by
  have hz1 : z ≠ 1 := by intro h; simp [h] at hz
  have hn := LFunction_ne_zero_of_one_le_re χ (Or.inr hz1) hz.le
  by_cases hχ : χ = 1
  · subst χ
    simpa only [regularizedL, ite_true, LFunctionTrivChar₁, Function.update_of_ne hz1] using
      mul_ne_zero (sub_ne_zero.mpr hz1) hn
  · simpa only [regularizedL, ite_eq_right hχ] using hn

/-- The same vertical side and symmetric truncation heights work for every
character of a fixed conductor parameter. The choices can be made in
arbitrarily short prescribed open intervals. -/
theorem common_box_sides (q : ℕ) [NeZero q] {u v B D : ℝ}
    (huv : u < v) (hB : 0 < B) (hBD : B < D) :
    ∃ σ ∈ Ioo u v, ∃ T ∈ Ioo B D, ∀ χ : DirichletCharacter ℂ q,
      ∀ z ∈ boxZeros χ σ 2 (-T) T, σ < z.re ∧ z.re < 2 ∧ -T < z.im ∧ z.im < T := by
  classical
  let allZeros : Finset ℂ := Finset.univ.biUnion fun χ : DirichletCharacter ℂ q => boxZeros χ u 2 (-D) D
  obtain ⟨σ,hσ,avoidR⟩ := (Ioo_infinite huv).exists_notMem_finset (allZeros.image Complex.re)
  obtain ⟨T,hT,avoidI⟩ := (Ioo_infinite hBD).exists_notMem_finset (allZeros.image fun z => |z.im|)
  refine ⟨σ,hσ,T,hT,?_⟩
  intro χ z hz
  have hz' := (mem_boxZeros χ σ 2 (-T) T z).mp hz
  have hb := mem_reProdIm.mp hz'.1
  have hzall : z ∈ allZeros := by
    refine Finset.mem_biUnion.mpr ⟨χ,Finset.mem_univ _,(mem_boxZeros χ u 2 (-D) D z).mpr ⟨?_,hz'.2⟩⟩
    exact mem_reProdIm.mpr ⟨⟨hσ.1.le.trans hb.1.1,hb.1.2⟩,⟨(neg_le_neg hT.2.le).trans hb.2.1,hb.2.2.trans hT.2.le⟩⟩
  have hT0 : 0 < T := hB.trans hT.1
  have hleft : σ ≠ z.re := fun h => avoidR (Finset.mem_image.mpr ⟨z,hzall,h.symm⟩)
  have habs : |z.im| ≠ T := fun h => avoidI (Finset.mem_image.mpr ⟨z,hzall,h⟩)
  refine ⟨lt_of_le_of_ne hb.1.1 hleft,lt_of_le_of_ne hb.1.2 ?_,lt_of_le_of_ne hb.2.1 ?_,lt_of_le_of_ne hb.2.2 ?_⟩
  · intro h
    exact regularizedL_ne_zero_right χ (by rw [h]; norm_num) hz'.2
  · intro h
    apply habs
    rw [← h,abs_neg,abs_of_pos hT0]
  · intro h
    exact habs (by rw [h,abs_of_pos hT0])

end GoldbachTwistedMellin
end
end

section
open Set Filter MeasureTheory Complex Goldbach DirichletCharacter GoldbachSmoothing
open scoped Topology Interval
noncomputable section
namespace GoldbachTwistedMellin

noncomputable def integrand {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (a b β : ℝ) (z : ℂ) : ℂ :=
  contourLog χ z * transform a b β z

/-- Signed, multiplicity-weighted residues of the additively twisted Mellin window. -/
noncomputable def zeroContribution {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (a b β σ T : ℝ) : ℂ :=
  ∑ z ∈ boxZeros χ σ 2 (-T) T, (analyticOrderNatAt (regularizedL χ) z : ℂ) * transform a b β z

noncomputable def contourRemainder {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (a b β σ T : ℝ) : ℂ :=
  let F := integrand χ a b β
  (1/(2*Real.pi)) • ((∫ t : ℝ in (-T)..T, F (line σ t)) +
    I * ((∫ x : ℝ in σ..2, F (line x (-T))) - ∫ x : ℝ in σ..2, F (line x T)))

noncomputable def truncationRemainder {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (a b β T : ℝ) : ℂ :=
  let F := integrand χ a b β
  (1/(2*Real.pi)) • ((∫ t : ℝ, F (line 2 t)) - ∫ t : ℝ in (-T)..T, F (line 2 t))

theorem exact_twisted_box {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {a b : ℕ} {X β σ T : ℝ} (hX : 1 ≤ X) (ha : X ≤ (a:ℝ)) (hab : (a:ℝ)+1 ≤ b)
    (hb : (b:ℝ)+1 ≤ 2*X) (hβ : |β| ≤ 1) (hs : σ < 1) (hT : 0 < T)
    (hinterior : ∀ z ∈ boxZeros χ σ 2 (-T) T, σ < z.re ∧ z.re < 2 ∧ -T < z.im ∧ z.im < T) :
    (∑ n ∈ Finset.Ioc a b, twistedCoefficient χ n * phase β n) =
      principalFlag χ * transform a b β 1 - zeroContribution χ a b β σ T +
        contourRemainder χ a b β σ T + truncationRemainder χ a b β T := by
  let K := transform a b β
  let S := boxZeros χ σ 2 (-T) T
  let F := integrand χ a b β
  let c : ℝ := 1/(2*Real.pi)
  have hK := analytic_transform (zero_lt_one.trans_le (hX.trans ha)) (b:ℝ) β
  have hr := rectBoundaryIntegral_neg_logDeriv_add_pole_mul (regularizedL χ) K S (principalFlag χ)
    hs (by norm_num : (1:ℝ) < 2) (neg_lt_zero.mpr hT) hT
    ((analytic_regularizedL χ).mono (subset_univ _)) (fun z _ => hK.analyticAt z)
    (fun z hz => by simp only [S,mem_boxZeros,and_iff_right hz]) hinterior
    (fun z _ => regularizedL_analyticOrder_ne_top χ z) (regularizedL_ne_zero_at_one χ)
  have vertical := right_vertical_integral_of_rect hr
  change (∫ y : ℝ in (-T)..T, F (line 2 y)) =
    (∫ y : ℝ in (-T)..T, F (line σ y)) +
      (2*(Real.pi:ℂ))*(principalFlag χ * K 1-zeroContribution χ a b β σ T) +
      I*((∫ x : ℝ in σ..2, F (line x (-T))) - ∫ x : ℝ in σ..2, F (line x T)) at vertical
  have inv := character_sum_eq_vertical χ hX ha hab hb hβ
  have rline (t : ℝ) : -logDeriv (LFunction χ) (2+(t:ℂ)*I) = contourLog χ (line 2 t) := by
    simpa [line] using (contour_right q χ t).symm
  simp_rw [rline] at inv
  change _ = c • ∫ t : ℝ, F (line 2 t) at inv
  have cancel (z : ℂ) : c • ((2*(Real.pi:ℂ))*z) = z := by
    rw [Complex.real_smul]
    simp [c,Complex.ofReal_mul,Real.pi_ne_zero,mul_assoc]
  have scaled := congrArg (fun z : ℂ => c • z) vertical
  simp only [smul_add,cancel] at scaled
  rw [inv]
  change _ = _ + c • (_ + _) + c • (_ - _)
  rw [smul_add,smul_sub,scaled]
  abel

end GoldbachTwistedMellin
end
end

section
open Set Filter MeasureTheory Complex Goldbach DirichletCharacter GoldbachSmoothing
open scoped Topology Interval
noncomputable section
namespace GoldbachTwistedMellin

/-- A single absolute convergent series bounds the logarithmic derivatives on
the right edge, for all characters and all imaginary heights. -/
theorem uniform_right_log_bound : ∃ A : ℝ, 0 < A ∧ ∀ (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (t : ℝ), ‖contourLog χ (line 2 t)‖ ≤ A := by
  let f : ℕ → ℂ := fun n => (ArithmeticFunction.vonMangoldt n : ℂ)
  have hsum : Summable fun n => ‖LSeries.term f (2:ℂ) n‖ :=
    summable_norm_iff.mpr (ArithmeticFunction.LSeriesSummable_vonMangoldt (by norm_num))
  let M := ∑' n, ‖LSeries.term f (2:ℂ) n‖
  have hM : 0 ≤ M := tsum_nonneg fun n => norm_nonneg _
  refine ⟨M+1,by positivity,?_⟩
  intro q _ χ t
  rw [contour_right, ← LSeries_twistedCoefficient_eq χ (by simp)]
  have h (n : ℕ) : ‖LSeries.term (twistedCoefficient χ) (line 2 t) n‖ ≤ ‖LSeries.term f (2:ℂ) n‖ := by
    have hs : ‖LSeries.term f (line 2 t) n‖ = ‖LSeries.term f (2:ℂ) n‖ := by simp [LSeries.norm_term_eq]
    rw [← hs]
    apply LSeries.norm_term_le
    change ‖χ (n:ZMod q)*(ArithmeticFunction.vonMangoldt n:ℂ)‖ ≤ ‖(ArithmeticFunction.vonMangoldt n:ℂ)‖
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one _)
  have ht := hsum.of_nonneg_of_le (fun _ => norm_nonneg _) h
  exact ((norm_tsum_le_tsum_norm ht).trans (ht.tsum_le_tsum h hsum)).trans (by dsimp [M]; linarith)

/-- Removing both infinite tails of a vertical integral loses at most 2M/T
when the pointwise norm beyond height T is at most M/t². -/
theorem tails_bound {f : ℝ → ℂ} (hi : Integrable f) {T M : ℝ} (hT : 0 < T) (_hM : 0 ≤ M)
    (hb : ∀ t : ℝ, T < |t| → ‖f t‖ ≤ M / t^2) :
    ‖(∫ t : ℝ, f t) - (∫ t : ℝ in (-T)..T, f t)‖ ≤ 2*M/T := by
  have ht : -T ≤ T := by linarith
  have hcut := intervalIntegral.integral_Iic_add_Ioi (b := T) (μ := volume) hi.integrableOn hi.integrableOn
  have hsplit : (∫ t in Iic T, f t) =
      (∫ t in Iic (-T), f t) + ∫ t in Ioc (-T) T, f t := by
    rw [← setIntegral_union (Iic_disjoint_Ioc (le_refl (-T))) measurableSet_Ioc hi.integrableOn hi.integrableOn,
      Iic_union_Ioc_eq_Iic ht]
  have htail (g : ℝ → ℂ) (hg : IntegrableOn g (Ioi T)) (hg' : ∀ t ∈ Ioi T, ‖g t‖ ≤ M/t^2) :
      ‖∫ t in Ioi T, g t‖ ≤ M/T := by
    have hr (t : ℝ) (h : t ∈ Ioi T) : t^(-2:ℝ) = (t^2)⁻¹ := by
      rw [Real.rpow_neg (hT.trans h).le,Real.rpow_two]
    have hm := (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2:ℝ) < -1) hT).const_mul M
    calc
      ‖∫ t in Ioi T, g t‖ ≤ ∫ t in Ioi T, ‖g t‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ t in Ioi T, M*t^(-2:ℝ) := by
        apply setIntegral_mono_on hg.norm hm measurableSet_Ioi
        intro t ht'
        simpa only [hr t ht',div_eq_mul_inv] using hg' t ht'
      _ = M/T := by
        rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num : (-2:ℝ) < -1) hT]
        norm_num [Real.rpow_neg hT.le,div_eq_mul_inv]
  have hpos := htail f hi.integrableOn (fun t ht' => hb t (by rwa [abs_of_pos (hT.trans ht')]))
  have hneg := htail (fun t => f (-t)) hi.comp_neg.integrableOn (fun t ht' => by
    simpa only [neg_sq] using hb (-t) (by rwa [abs_neg,abs_of_pos (hT.trans ht')]))
  rw [integral_comp_neg_Ioi] at hneg
  rw [← hcut, hsplit, intervalIntegral.integral_of_le ht]
  have cancel (l m r : ℂ) : l+m+r-m = l+r := by abel
  rw [cancel]
  exact (norm_add_le _ _).trans ((add_le_add hneg hpos).trans_eq (by ring))

end GoldbachTwistedMellin
end
end

section
open Set Filter MeasureTheory Complex Goldbach DirichletCharacter GoldbachSmoothing
open scoped Topology Interval
noncomputable section
namespace GoldbachTwistedMellin

theorem truncation_bound : ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (a b : ℕ) (X β T : ℝ), 1 ≤ X → X ≤ (a:ℝ) → (a:ℝ)+1 ≤ b → (b:ℝ)+1 ≤ 2*X →
      |β| ≤ 1 → 0 < T → ‖truncationRemainder χ a b β T‖ ≤ C*X^4/T := by
  obtain ⟨A,hA,logbound⟩ := uniform_right_log_bound
  let c : ℝ := 1/(2*Real.pi)
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨c*(2*A*96),by positivity,?_⟩
  intro q _ χ a b X β T hX ha hab hb hβ hT
  let F := integrand χ a b β
  have hr (t : ℝ) : LSeries (twistedCoefficient χ) (line 2 t) = contourLog χ (line 2 t) := by
    rw [contour_right]
    exact LSeries_twistedCoefficient_eq χ (by simp)
  have hAbs : Summable fun n => ‖LSeries.term (twistedCoefficient χ) (2:ℂ) n‖ :=
    summable_norm_iff.mpr (χ.LSeriesSummable_twist_vonMangoldt (by norm_num))
  have hi : Integrable fun t : ℝ => F (line 2 t) := by
    dsimp [F,integrand]
    simp_rw [← hr]
    exact integrable_series_transform (twistedCoefficient χ) (transform a b β) (σ := 2)
      (integrable_transform hX ha hab hb hβ (by norm_num) le_rfl) (by simpa using hAbs)
  have hbnd (t : ℝ) (ht : T < |t|) : ‖F (line 2 t)‖ ≤ (A*96*X^4)/t^2 := by
    have h := norm_transform_tail hX ha hab hb hβ (line 2 t) (by simp) (by simp) (by simpa using hT.trans ht)
    rw [im_line, sq_abs] at h
    change ‖contourLog χ (line 2 t) * _‖ ≤ _
    rw [norm_mul]
    exact (mul_le_mul (logbound q χ t) h (norm_nonneg _) hA.le).trans_eq (by ring)
  have ht := tails_bound hi hT (by positivity : 0 ≤ A*96*X^4) hbnd
  change ‖c • _‖ ≤ _
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos hc]
  exact (mul_le_mul_of_nonneg_left ht hc.le).trans_eq (by ring)

/-- A finite-height explicit formula for every character with a common modulus.
The sides are selected before the character, frequency or dyadic interval.
All zeros in the rectangle occur with their true analytic multiplicities. -/
theorem finite_twisted_explicit_formula :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (u v B D : ℝ), u < v → v < 1 → 0 < B → B < D →
      ∃ σ ∈ Ioo u v, ∃ T ∈ Ioo B D, ∀ (χ : DirichletCharacter ℂ q) (a b : ℕ) (X β : ℝ),
        1 ≤ X → X ≤ (a:ℝ) → (a:ℝ)+1 ≤ b → (b:ℝ)+1 ≤ 2*X → |β| ≤ 1 →
        ‖(∑ n ∈ Finset.Ioc a b, twistedCoefficient χ n * phase β n) -
          (principalFlag χ*transform a b β 1 - zeroContribution χ a b β σ T +
            contourRemainder χ a b β σ T)‖ ≤ C*X^4/T := by
  obtain ⟨C,hC,tail⟩ := truncation_bound
  refine ⟨C,hC,?_⟩
  intro q _ u v B D huv hv hB hBD
  obtain ⟨σ,hσ,T,hT,edges⟩ := common_box_sides q huv hB hBD
  refine ⟨σ,hσ,T,hT,?_⟩
  intro χ a b X β hX ha hab hb hβ
  rw [exact_twisted_box χ hX ha hab hb hβ (hσ.2.trans hv) (hB.trans hT.1) (edges χ),add_sub_cancel_left]
  exact tail q χ a b X β T hX ha hab hb hβ (hB.trans hT.1)

end GoldbachTwistedMellin
end
end

section
open Set Filter MeasureTheory Complex Goldbach DirichletCharacter MeromorphicOn Metric
open scoped Topology Interval
noncomputable section
namespace GoldbachTwistedMellin

/-- Every zero to the right of the critical line whose ordinate differs from t
by at most one lies in the same Jensen disk. -/
theorem mem_right_jensen_disk {z : ℂ} {t : ℝ}
    (hl : 1/2 ≤ z.re) (hr : z.re ≤ 2) (hi : |z.im-t| ≤ 1) :
    z ∈ closedBall (⟨2,t⟩:ℂ) (29/16) := by
  rw [mem_closedBall,dist_eq_norm]
  apply (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 29/16)).mp
  have hrabs : |z.re-2| ≤ 3/2 := abs_le.mpr ⟨by linarith,by linarith⟩
  have h1 := (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 3/2)).mpr hrabs
  have h2 := (sq_le_sq₀ (abs_nonneg _) zero_le_one).mpr hi
  rw [sq_abs] at h1 h2
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re,Complex.sub_im]
  nlinarith only [h1,h2]

/-- The unit-height bound counts multiplicities throughout the right half of
the critical strip. It requires no hypothesis on the real part of other zeros. -/
theorem unconditional_right_slice_count :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ) (Z : Finset ℂ),
      (∀ z ∈ Z, 1/2 ≤ z.re ∧ z.re ≤ 2 ∧ |z.im-t| ≤ 1) →
      (∑ z ∈ Z, (analyticOrderNatAt (regularizedL χ) z:ℝ)) ≤ C*logHeight q t := by
  classical
  obtain ⟨C,hC,jensen⟩ := jensen_diskDivisor_bound (A:=25) (b:=1/4) (by norm_num) (by norm_num)
  refine ⟨C,hC,?_⟩
  intro q _ χ t Z hZ
  let U := closedBall (⟨2,t⟩:ℂ) (29/16)
  let D := divisor (regularizedL χ) U
  have hfin := D.finiteSupport (isCompact_closedBall _ _)
  let W := Z ∪ hfin.toFinset
  have hsup : Function.support D ⊆ (W:Set ℂ) := fun _ hz => Finset.mem_union_right _ (hfin.mem_toFinset.mpr hz)
  have hbound := jensen q (regularizedL χ) t (NeZero.pos q)
    ((analytic_regularizedL χ).mono (subset_univ _))
    (fun s hs => by
      have hg := GoldbachGrhGrowth.norm_regularizedLFunction_le χ hs
      by_cases hχ : χ = 1
      · simpa only [regularizedL,hχ,ite_true] using hg
      · simpa only [regularizedL,hχ,ite_false] using hg) (norm_regularizedL_anchor χ t)
  have hmul (z : ℂ) (hz : z ∈ Z) : (analyticOrderNatAt (regularizedL χ) z : ℤ) = D z :=
    (regularizedL_divisor_apply χ (mem_right_jensen_disk (hZ z hz).1 (hZ z hz).2.1 (hZ z hz).2.2)).symm
  have hD : ∀ z, 0 ≤ D z := ((analytic_regularizedL χ).mono (subset_univ U)).divisor_nonneg
  have hsum : (∑ z ∈ Z,(analyticOrderNatAt (regularizedL χ) z:ℤ)) ≤ ∑ᶠ z, D z := by
    rw [finsum_eq_sum_of_support_subset _ hsup,Finset.sum_congr rfl hmul]
    exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left (fun z _ _ => hD z)
  exact (show (∑ z ∈ Z,(analyticOrderNatAt (regularizedL χ) z:ℝ)) ≤ ((∑ᶠ z, D z : ℤ):ℝ) by exact_mod_cast hsum).trans hbound

end GoldbachTwistedMellin
end
end

section
open Set Filter MeasureTheory Complex Goldbach DirichletCharacter
open scoped Topology Interval
noncomputable section
namespace GoldbachTwistedMellin

/-- The number of distinct right-hand zeros in a horizontal band is at most
the Jensen bound for their total multiplicity. -/
theorem right_box_card :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ),
      ((boxZeros χ (1/2) 2 (t-1) (t+1)).card:ℝ) ≤ C*logHeight q t := by
  obtain ⟨C,hC,count⟩ := unconditional_right_slice_count
  refine ⟨C,hC,?_⟩
  intro q _ χ t
  let Z := boxZeros χ (1/2) 2 (t-1) (t+1)
  have hz (z : ℂ) (h : z ∈ Z) := (mem_boxZeros χ _ _ _ _ z).mp h
  have bounds (z : ℂ) (h : z ∈ Z) : 1/2 ≤ z.re ∧ z.re ≤ 2 ∧ |z.im-t| ≤ 1 := by
    have b := mem_reProdIm.mp (hz z h).1
    exact ⟨b.1.1,b.1.2,abs_le.mpr ⟨by linarith [b.2.1],by linarith [b.2.2]⟩⟩
  have one (z : ℂ) (h : z ∈ Z) : (1:ℝ) ≤ analyticOrderNatAt (regularizedL χ) z := by
    exact_mod_cast (regularizedL_analyticOrderNatAt_pos_iff χ z).mpr (hz z h).2
  exact (show (Z.card:ℝ) ≤ ∑ z ∈ Z, (analyticOrderNatAt (regularizedL χ) z:ℝ) by
    simpa using Finset.sum_le_sum one).trans (count q χ t Z bounds)

/-- A height in each unit interval avoids the ordinates of zeros near both the
upper and lower edge. The width of the forbidden neighborhoods is inverse
logarithmic in the modulus and height. -/
theorem good_symmetric_height :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (B : ℝ), 2 ≤ B →
      ∃ T ∈ Icc B (B+1), ∀ z : ℂ, 1/2 ≤ z.re → regularizedL χ z = 0 →
        (C*logHeight q (B+1/2))⁻¹ ≤ abs (T - |z.im|) := by
  obtain ⟨C,hC,count⟩ := right_box_card
  refine ⟨4*(1+2*C),by positivity,?_⟩
  intro q _ χ B hB
  let t := B+1/2
  let P := boxZeros χ (1/2) 2 (t-1) (t+1)
  let N := boxZeros χ (1/2) 2 (-t-1) (-t+1)
  let S := P ∪ N
  let L := logHeight q t
  have hL : 1 ≤ L := logHeight_ge_one q t
  have hLn : logHeight q (-t) = L := by simp [L,logHeight]
  have hs : (S.card:ℝ) ≤ 2*C*L := by
    have hp := count q χ t
    have hn := count q χ (-t)
    rw [hLn] at hn
    have hu : (S.card:ℝ) ≤ (P.card:ℝ)+(N.card:ℝ) := by exact_mod_cast Finset.card_union_le P N
    dsimp only [P,N] at hu
    linarith [hp,hn]
  obtain ⟨v,hv,sep⟩ := exists_goodHeight S (fun z => 2*|z.im|) (2*B+1/2)
  let T := v/2
  have hT : B+1/4 ≤ T ∧ T ≤ B+3/4 := by dsimp [T]; constructor <;> linarith [hv.1,hv.2]
  let g := (4*(1+2*C)*L)⁻¹
  have hden : 4*(1+(S.card:ℝ)) ≤ 4*(1+2*C)*L := by linarith only [hs,hL]
  have hg : g ≤ 1/(4*(1+(S.card:ℝ))) := by
    rw [one_div];exact inv_anti₀ (by positivity) hden
  have hg' : g ≤ 1/4 := hg.trans ((one_div_le_one_div_of_le (by norm_num : (0:ℝ)<4) (by linarith [Nat.cast_nonneg (α:=ℝ) S.card] : (4:ℝ) ≤ 4*(1+(S.card:ℝ)))))
  refine ⟨T,⟨by linarith [hT.1],by linarith [hT.2]⟩,?_⟩
  intro z hz hzero
  change g ≤ _
  by_contra! hclose
  have hnear := abs_lt.mp (hclose.trans_le hg')
  have hr : z.re ≤ 2 := by by_contra! h; exact regularizedL_ne_zero_right χ (by linarith) hzero
  have hzS : z ∈ S := by
    by_cases hi : 0 ≤ z.im
    · rw [abs_of_nonneg hi] at hnear
      apply Finset.mem_union_left
      apply (mem_boxZeros χ _ _ _ _ z).mpr
      exact ⟨mem_reProdIm.mpr ⟨⟨hz,hr⟩,⟨by dsimp [t];linarith [hT.1,hnear.2],by dsimp [t];linarith [hT.2,hnear.1]⟩⟩,hzero⟩
    · rw [abs_of_neg (lt_of_not_ge hi)] at hnear
      apply Finset.mem_union_right
      apply (mem_boxZeros χ _ _ _ _ z).mpr
      exact ⟨mem_reProdIm.mpr ⟨⟨hz,hr⟩,⟨by dsimp [t];linarith [hT.2,hnear.1],by dsimp [t];linarith [hT.1,hnear.2]⟩⟩,hzero⟩
  have hsep := sep z hzS
  rw [show v-2*|z.im|=2*(T-|z.im|) by dsimp [T];ring,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)] at hsep
  have heq : 1/(2*(1+(S.card:ℝ))) = 2*(1/(4*(1+(S.card:ℝ)))) := by field_simp; ring
  linarith only [heq,hsep,hg,hclose]

end GoldbachTwistedMellin
end
end

section
open Set Filter MeasureTheory Complex Goldbach DirichletCharacter
open scoped Topology Interval
noncomputable section
namespace GoldbachTwistedMellin

theorem logHeight_mono_abs (q : ℕ) [NeZero q] {s t : ℝ} (h : |s| ≤ |t|) :
    logHeight q s ≤ logHeight q t := by
  have hq : (0:ℝ) < q := by exact_mod_cast NeZero.pos q
  apply Real.log_le_log (by positivity)
  exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)

/-- A uniform logarithmic-derivative bound holds on both horizontal edges. The
height can depend on the character; every point of each edge is covered. -/
theorem unconditional_horizontal_log {d : ℝ} (hd : 0 < d) :
    ∃ A : ℝ, 0 < A ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (B : ℝ), 2 ≤ B →
      ∃ T ∈ Icc B (B+1), (∀ z : ℂ, 1/2 ≤ z.re → regularizedL χ z = 0 → |z.im| ≠ T) ∧
        ∀ σ t : ℝ, 1/2+d ≤ σ → σ ≤ 2 → |t| = T →
        ‖contourLog χ (line σ t)‖ ≤ A*(logHeight q (B+1))^2 := by
  obtain ⟨C,hC,good⟩ := good_symmetric_height
  obtain ⟨K,hK,bound⟩ := uniform_dirichlet_log_control
  refine ⟨K*(1+d⁻¹+C)+4,by positivity,?_⟩
  intro q _ χ B hB
  obtain ⟨T,hT,avoid⟩ := good q χ B hB
  let L := logHeight q (B+1)
  have hL : 1 ≤ L := logHeight_ge_one q _
  have hc := logHeight_ge_one q (B+1/2)
  have hmid : logHeight q (B+1/2) ≤ L := by
    apply logHeight_mono_abs
    rw [abs_of_nonneg (by linarith : 0 ≤ B+1/2),abs_of_nonneg (by linarith : 0 ≤ B+1)]
    linarith
  let r := min d (C*logHeight q (B+1/2))⁻¹
  have hr : 0 < r := lt_min hd (by positivity)
  have hr' : r⁻¹ ≤ d⁻¹+C*L := by
    dsimp [r]
    rcases le_total d (C*logHeight q (B+1/2))⁻¹ with h|h
    · rw [min_eq_left h]; nlinarith only [hC,hL,mul_pos hC (by linarith : 0 < L)]
    · rw [min_eq_right h,inv_inv]; linarith only [mul_le_mul_of_nonneg_left hmid hC.le,inv_pos.mpr hd]
  refine ⟨T,hT,?_,?_⟩
  · intro z hz hz0 heq
    have gap := avoid z hz hz0
    rw [heq,sub_self,abs_zero] at gap
    exact (not_le_of_gt (by positivity)) gap
  intro σ t hσ hσ' ht
  have hdist (z : ℂ) (_hz : 0 < z.re) (hz0 : regularizedL χ z = 0) : r ≤ ‖line σ t - z‖ := by
    by_cases hz : 1/2 ≤ z.re
    · have h := avoid z hz hz0
      have h' := abs_norm_sub_norm_le t z.im
      simp only [Real.norm_eq_abs,ht] at h'
      exact ((min_le_right ..).trans (h.trans h')).trans (by simpa using abs_im_le_norm (line σ t-z))
    · exact (min_le_left ..).trans ((show d ≤ (line σ t-z).re by simp only [sub_re,re_line];linarith).trans (re_le_norm _))
  have raw := bound q χ σ t r ⟨by linarith,hσ'⟩ hr hdist
  have htlog : logHeight q t ≤ L := by apply logHeight_mono_abs;rw [ht,abs_of_nonneg (by linarith : 0≤B+1)];exact hT.2
  have hsep := horizontal_pole_dist (by rw [ht];linarith [hT.1] : 1 ≤ |t|) σ
  have hflag : ‖principalFlag χ‖ ≤ 1 := by by_cases h : χ = 1 <;> simp [principalFlag,h]
  have hpole : ‖principalFlag χ/(line σ t-1)‖ ≤ 4 := by
    rw [norm_div];apply (div_le_iff₀ (by linarith : 0 < ‖line σ t-1‖)).mpr;linarith
  rw [mul_right_comm K] at raw
  change ‖logDeriv (regularizedL χ) (line σ t)‖ ≤ K*(1+r⁻¹)*logHeight q t at raw
  have hfactor : 1+r⁻¹ ≤ (1+d⁻¹+C)*L := by
    nlinarith only [hr',hL,mul_le_mul_of_nonneg_left hL (inv_pos.mpr hd).le]
  have hm := mul_le_mul (mul_le_mul_of_nonneg_left hfactor hK.le) htlog
    (by linarith [logHeight_ge_one q t]) (by positivity)
  have hsq : 1 ≤ L^2 := one_le_pow₀ hL
  calc
    ‖contourLog χ (line σ t)‖ ≤ ‖logDeriv (regularizedL χ) (line σ t)‖ + ‖principalFlag χ/(line σ t-1)‖ := by
      simpa only [contourLog,norm_neg] using norm_add_le (-logDeriv (regularizedL χ) (line σ t)) (principalFlag χ/(line σ t-1))
    _ ≤ (K*(1+d⁻¹+C)+4)*L^2 := by nlinarith only [raw.trans hm,hpole,hsq]

end GoldbachTwistedMellin
end
end

section
open Set Filter MeasureTheory Complex Goldbach DirichletCharacter GoldbachSmoothing
open scoped Topology Interval
noncomputable section
namespace GoldbachTwistedMellin

noncomputable def leftVertical {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (a b β σ T : ℝ) : ℂ :=
  (1/(2*Real.pi)) • ∫ t : ℝ in (-T)..T, integrand χ a b β (line σ t)

/-- Along either horizontal side the window decays quadratically in height.
The loss from the logarithmic derivative is at most quadratic in log height. -/
theorem horizontal_edge_bound {d σ T B A X β : ℝ} {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {a b : ℕ} (hX : 1 ≤ X) (ha : X ≤ (a:ℝ)) (hab : (a:ℝ)+1 ≤ b)
    (hb : (b:ℝ)+1 ≤ 2*X) (hβ : |β| ≤ 1) (hd : 0 < d)
    (hs : 1/2+d ≤ σ) (hs' : σ < 1) (hT : 0 < T) (hA : 0 ≤ A)
    (hlog : ∀ x t : ℝ, 1/2+d ≤ x → x ≤ 2 → |t| = T →
      ‖contourLog χ (line x t)‖ ≤ A*(logHeight q (B+1))^2) {t : ℝ} (ht : |t| = T) :
    ‖∫ x : ℝ in σ..2, integrand χ a b β (line x t)‖ ≤
      (2*A*96)*X^4*(logHeight q (B+1))^2/T^2 := by
  let L := logHeight q (B+1)
  have hpos : 0 < σ := by linarith
  have pt (x : ℝ) (hx : x ∈ Ι σ 2) : ‖integrand χ a b β (line x t)‖ ≤ (A*L^2)*(96*X^4/T^2) := by
    rw [uIoc_of_le (by linarith)] at hx
    have hw := norm_transform_tail hX ha hab hb hβ (line x t) (by simp;linarith [hx.1])
      (by simpa using hx.2) (by simpa [ht] using hT)
    rw [im_line,ht] at hw
    rw [integrand,norm_mul]
    exact mul_le_mul (hlog x t (hs.trans hx.1.le) hx.2 ht) hw (norm_nonneg _) (by positivity)
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const pt
  have hlen : |2-σ| ≤ 2 := by rw [abs_of_nonneg (by linarith)];linarith
  exact hi.trans ((mul_le_mul_of_nonneg_left hlen (by positivity)).trans_eq (by dsimp [L];ring))


end GoldbachTwistedMellin
end
end

section
open Set Filter MeasureTheory Complex
open scoped Topology Interval

noncomputable section
namespace GoldbachTwistedMellin

def heightCut (X : ℝ) : ℝ := (2*X)^8
def logBudget (q : ℕ) (X : ℝ) : ℝ := 1+Goldbach.logHeight q (heightCut X)

theorem heightCut_ge {X : ℝ} (hX : 1 ≤ X) : 1+4*X ≤ heightCut X := by
  have hpow : X ≤ X^8 := by simpa using pow_le_pow_right₀ hX (show 1 ≤ 8 by decide)
  dsimp [heightCut]
  rw [mul_pow]
  norm_num
  linarith


end GoldbachTwistedMellin
end
end

section
open Set MeasureTheory
open scoped Interval Topology
noncomputable section
namespace GoldbachTwistedMellin

def rootKernel (x : ℝ) := |x|^(-(1/2):ℝ)

theorem rootKernel_nonneg (x : ℝ) : 0 ≤ rootKernel x := Real.rpow_nonneg (abs_nonneg _) _

theorem integrable_rootKernel (a b r : ℝ) : IntervalIntegrable (fun x => rootKernel (x-r)) volume a b := by
  have hpow (u v : ℝ) : IntervalIntegrable (fun x : ℝ => x^(-(1/2):ℝ)) volume u v :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hpos : IntervalIntegrable (fun x : ℝ => (x-r)^(-(1/2):ℝ)) volume a b :=
    by simpa using (hpow (a-r) (b-r)).comp_sub_right r
  have hneg : IntervalIntegrable (fun x : ℝ => (r-x)^(-(1/2):ℝ)) volume a b :=
    by simpa using (hpow (r-a) (r-b)).comp_sub_left r
  rw [intervalIntegrable_iff] at hpos hneg ⊢
  have h := Integrable.piecewise (μ:=volume.restrict (Ι a b)) (s:=Iio r) measurableSet_Iio.nullMeasurableSet
    (Integrable.integrableOn hneg) (Integrable.integrableOn hpos)
  apply h.congr
  filter_upwards with x
  by_cases hx : x < r
  · simp [Set.piecewise,hx,rootKernel,abs_of_neg (sub_neg.mpr hx),neg_sub]
  · simp [Set.piecewise,hx,rootKernel,abs_of_nonneg (sub_nonneg.mpr (le_of_not_gt hx))]

theorem integral_rootKernel_right {a b r : ℝ} (ha : r ≤ a) (hab : a ≤ b) :
    (∫ x in a..b, rootKernel (x-r)) = 2*(Real.sqrt (b-r)-Real.sqrt (a-r)) := by
  have h : (∫ x in a..b, rootKernel (x-r)) = ∫ x in a..b, (x-r)^(-(1/2):ℝ) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hab] at hx
    simp [rootKernel,abs_of_nonneg (sub_nonneg.mpr (ha.trans hx.1))]
  rw [h,intervalIntegral.integral_comp_sub_right (fun x : ℝ => x^(-(1/2):ℝ)) r,
    integral_rpow (Or.inl (by norm_num))]
  norm_num [← Real.sqrt_eq_rpow]
  ring

theorem integral_rootKernel_left {a b r : ℝ} (hb : b ≤ r) (hab : a ≤ b) :
    (∫ x in a..b, rootKernel (x-r)) = 2*(Real.sqrt (r-a)-Real.sqrt (r-b)) := by
  have h : (∫ x in a..b, rootKernel (x-r)) = ∫ x in a..b, (r-x)^(-(1/2):ℝ) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hab] at hx
    simp [rootKernel,abs_of_nonpos (sub_nonpos.mpr (hx.2.trans hb)),neg_sub]
  rw [h,intervalIntegral.integral_comp_sub_left (fun x : ℝ => x^(-(1/2):ℝ)) r,
    integral_rpow (Or.inl (by norm_num))]
  norm_num [← Real.sqrt_eq_rpow]
  ring

theorem integral_rootKernel_le {a b : ℝ} (hab : a ≤ b) (r : ℝ) :
    (∫ x in a..b, rootKernel (x-r)) ≤ 4*Real.sqrt (b-a) := by
  have diffBound (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
      Real.sqrt (x+y)-Real.sqrt x ≤ Real.sqrt y := by
    apply sub_le_iff_le_add.mpr
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mp
    nlinarith only [Real.sq_sqrt (add_nonneg hx hy),Real.sq_sqrt hx,Real.sq_sqrt hy,
      mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y)]
  rcases le_total r a with h|h
  · rw [integral_rootKernel_right h hab]
    have he : b-r = a-r+(b-a) := by ring
    rw [he]
    linarith [diffBound (a-r) (b-a) (by linarith) (by linarith),Real.sqrt_nonneg (b-a)]
  rcases le_total b r with h'|h'
  · rw [integral_rootKernel_left h' hab]
    have he : r-a = r-b+(b-a) := by ring
    rw [he]
    linarith [diffBound (r-b) (b-a) (by linarith) (by linarith),Real.sqrt_nonneg (b-a)]
  rw [← intervalIntegral.integral_add_adjacent_intervals (integrable_rootKernel a r r) (integrable_rootKernel r b r),
    integral_rootKernel_left (le_refl r) h,integral_rootKernel_right (le_refl r) h',sub_self,Real.sqrt_zero]
  linarith [Real.sqrt_le_sqrt (by linarith : r-a ≤ b-a),Real.sqrt_le_sqrt (by linarith : b-r ≤ b-a)]

end GoldbachTwistedMellin
end
end

section
open Set MeasureTheory
open scoped Interval Topology
noncomputable section
namespace GoldbachTwistedMellin

/-- A vertical side avoiding any prescribed finite set can be chosen with
controlled total square-root singularity at all real coordinates. -/
theorem exists_weighted_rootKernel_bound {ι : Type*} (S : Finset ι) (w y : ι → ℝ)
    (hw : ∀ i ∈ S, 0 ≤ w i) (bad : Finset ℝ) {a b : ℝ} (hab : a < b) :
    ∃ x ∈ Ioo a b, x ∉ bad ∧
      (∑ i ∈ S, w i*rootKernel (x-y i)) ≤ (4/Real.sqrt (b-a))*(∑ i ∈ S,w i) := by
  classical
  let I := Ioc a b
  let μ := volume.restrict I
  have len : 0 < b-a := sub_pos.mpr hab
  have hreal : μ.real univ = b-a := by
    simp [μ,I,Measure.real,Real.volume_Ioc,ENNReal.toReal_ofReal len.le]
  have hn : μ ≠ 0 := by
    intro h
    have hp : 0 < μ.real univ := hreal.symm ▸ len
    simp [h] at hp
  let : IsFiniteMeasure μ := ⟨by simp [μ,I,Real.volume_Ioc]⟩
  let g := fun x : ℝ => ∑ i ∈ S, w i*rootKernel (x-y i)
  have int (i : ι) : Integrable (fun x => w i*rootKernel (x-y i)) μ :=
    ((integrable_rootKernel a b (y i)).1.const_mul (w i))
  have hi : Integrable g μ := integrable_finsetSum S (fun i _ => int i)
  have avg : (⨍ x, g x ∂μ) ≤ (4/Real.sqrt (b-a))*(∑ i ∈ S,w i) := by
    rw [average_eq,hreal,smul_eq_mul]
    have hi' : (∫ x, g x ∂μ) ≤ 4*Real.sqrt (b-a)*(∑ i ∈ S,w i) := by
      unfold g
      rw [integral_finsetSum S (fun i _ => int i),Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i hi
      rw [integral_const_mul]
      have hbound := integral_rootKernel_le hab.le (y i)
      rw [intervalIntegral.integral_of_le hab.le] at hbound
      exact (mul_le_mul_of_nonneg_left hbound (hw i hi)).trans_eq (by ring)
    apply (mul_le_mul_of_nonneg_left hi' (inv_nonneg.mpr len.le)).trans_eq
    have hs := Real.sq_sqrt len.le
    have hp := Real.sqrt_pos.mpr len
    field_simp
    rw [hs]
  let N : Set ℝ := Iᶜ ∪ (↑(insert b bad) : Set ℝ)
  have hN : μ N = 0 := by
    apply measure_union_null
    · simp [μ,I,Measure.restrict_apply,measurableSet_Ioc.compl]
    · exact (insert b bad).measure_zero μ
  obtain ⟨x,hx,hgx⟩ := exists_notMem_null_le_average hn hi hN
  have h' : x ∈ I := by by_contra hh;exact hx (Or.inl hh)
  have hbad : x ∉ insert b bad := fun h => hx (Or.inr h)
  exact ⟨x,⟨h'.1,lt_of_le_of_ne h'.2 (fun h => hbad (Finset.mem_insert.mpr (.inl h)))⟩,
    fun h => hbad (Finset.mem_insert.mpr (.inr h)),hgx.trans avg⟩

end GoldbachTwistedMellin
end
end

section
open Set Filter MeasureTheory Complex Goldbach DirichletCharacter
open scoped Topology Interval
noncomputable section
namespace GoldbachTwistedMellin

theorem inv_distance_le_root_product (s z : ℂ) (hx : s.re ≠ z.re) (hy : s.im ≠ z.im) :
    ‖s-z‖⁻¹ ≤ rootKernel (s.re-z.re)*rootKernel (s.im-z.im) := by
  let x := |s.re-z.re|
  let y := |s.im-z.im|
  have hxp : 0 < x := abs_pos.mpr (sub_ne_zero.mpr hx)
  have hyp : 0 < y := abs_pos.mpr (sub_ne_zero.mpr hy)
  have h1 : x ≤ ‖s-z‖ := abs_re_le_norm _
  have h2 : y ≤ ‖s-z‖ := abs_im_le_norm _
  have hsq : Real.sqrt x*Real.sqrt y ≤ ‖s-z‖ := by
    rw [← Real.sqrt_mul hxp.le]
    exact (Real.sqrt_le_iff).mpr ⟨norm_nonneg _,by simpa only [pow_two] using mul_le_mul h1 h2 hyp.le (norm_nonneg _)⟩
  change _ ≤ x^(-(1/2):ℝ)*y^(-(1/2):ℝ)
  rw [Real.rpow_neg hxp.le,Real.rpow_neg hyp.le,←Real.sqrt_eq_rpow,←Real.sqrt_eq_rpow,← mul_inv]
  exact inv_anti₀ (mul_pos (Real.sqrt_pos.mpr hxp) (Real.sqrt_pos.mpr hyp)) hsq

/-- Only zeros within one vertical unit and to the right of one half may
contribute a singular term. A product of two locally integrable kernels
majorizes each such term at almost every height. -/
noncomputable def localZeroPotential (Z : Finset ℂ) (σ t : ℝ) : ℝ :=
  ∑ z ∈ Z, if |t-z.im| ≤ 1 then rootKernel (σ-z.re)*rootKernel (t-z.im) else 0

theorem localPotential_nonneg (Z : Finset ℂ) (σ t : ℝ) : 0 ≤ localZeroPotential Z σ t :=
  Finset.sum_nonneg fun z _ => by split <;> first | exact mul_nonneg (rootKernel_nonneg _) (rootKernel_nonneg _) | exact le_rfl

theorem localPotential_term {Z : Finset ℂ} {z : ℂ} (hz : z ∈ Z) (σ t : ℝ) (h : |t-z.im| ≤ 1) :
    rootKernel (σ-z.re)*rootKernel (t-z.im) ≤ localZeroPotential Z σ t := by
  classical
  let w := fun z : ℂ => if |t-z.im| ≤ 1 then rootKernel (σ-z.re)*rootKernel (t-z.im) else 0
  have hn (z : ℂ) (_ : z ∈ Z) : 0 ≤ w z := by dsimp [w];split <;> first | exact mul_nonneg (rootKernel_nonneg _) (rootKernel_nonneg _) | exact le_rfl
  simpa only [w,localZeroPotential,ite_eq_left h] using Finset.single_le_sum hn hz

theorem log_control_via_potential {d : ℝ} (hd : 0 < d) :
    ∃ A : ℝ, 0 < A ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (σ t T : ℝ),
      1/2+d ≤ σ → σ ≤ 3/4 → |t| ≤ T →
      let Z := boxZeros χ (1/2) 2 (-T-1) (T+1)
      (∀ z ∈ Z, σ ≠ z.re) → (∀ z ∈ Z, t ≠ z.im) →
      ‖contourLog χ (line σ t)‖ ≤ A*logHeight q t*(1+localZeroPotential Z σ t) := by
  obtain ⟨C,hC,bound⟩ := uniform_dirichlet_log_control
  refine ⟨C*(2+d⁻¹)+4,by positivity,?_⟩
  intro q _ χ σ t T hs hs' ht Z xr yi
  let P := localZeroPotential Z σ t
  have hP : 0 ≤ P := localPotential_nonneg _ _ _
  let D := 1+d⁻¹+P
  have hD : 0 < D := by dsimp [D];positivity
  have sep (z : ℂ) (_ : 0 < z.re) (hz : regularizedL χ z = 0) : D⁻¹ ≤ ‖line σ t-z‖ := by
    by_cases hreal : z.re < 1/2
    · have hsep : d ≤ ‖line σ t-z‖ := (show d ≤ (line σ t-z).re by simp only [sub_re,re_line];linarith).trans (re_le_norm _)
      exact (show D⁻¹ ≤ d by simpa using inv_anti₀ (inv_pos.mpr hd) (by dsimp [D];linarith : d⁻¹ ≤ D)).trans hsep
    by_cases him : |t-z.im| ≤ 1
    · have hZ : z ∈ Z := by
        apply (mem_boxZeros χ _ _ _ _ z).mpr
        have hright : z.re ≤ 2 := by by_contra! h;exact regularizedL_ne_zero_right χ (by linarith) hz
        have htt := abs_le.mp ht
        have hii := abs_le.mp him
        exact ⟨mem_reProdIm.mpr ⟨⟨le_of_not_gt hreal,hright⟩,⟨by linarith [htt.1,hii.2],by linarith [htt.2,hii.1]⟩⟩,hz⟩
      have hdis := inv_distance_le_root_product (line σ t) z (by simpa using xr z hZ) (by simpa using yi z hZ)
      simp only [re_line,im_line] at hdis
      have hle := hdis.trans (localPotential_term hZ σ t him)
      have hp : 0 < ‖line σ t-z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (fun he => xr z hZ (by simpa using congrArg Complex.re he)))
      exact (inv_le_comm₀ hD hp).mpr (by dsimp [D];linarith only [hle,inv_pos.mpr hd])
    · have hi : 1 ≤ ‖line σ t-z‖ := (le_of_not_ge him).trans (by simpa using abs_im_le_norm (line σ t-z))
      exact (show D⁻¹ ≤ 1 by simpa using inv_anti₀ zero_lt_one (by dsimp [D];linarith only [hP,inv_pos.mpr hd] : 1 ≤ D)).trans hi
  have raw := bound q χ σ t D⁻¹ ⟨by linarith,by linarith⟩ (inv_pos.mpr hD) sep
  rw [inv_inv] at raw
  have hL := logHeight_ge_one q t
  have hp := left_pole_dist hs' t
  have hf : ‖principalFlag χ‖ ≤ 1 := by by_cases h : χ=1 <;> simp [principalFlag,h]
  have hflag : ‖principalFlag χ/(line σ t-1)‖ ≤ 4 := by
    rw [norm_div];apply (div_le_iff₀ (by linarith : 0<‖line σ t-1‖)).mpr;linarith
  calc
    ‖contourLog χ (line σ t)‖ ≤ ‖logDeriv (regularizedL χ) (line σ t)‖ + ‖principalFlag χ/(line σ t-1)‖ := by
      simpa only [contourLog,norm_neg] using norm_add_le (-logDeriv (regularizedL χ) (line σ t)) (principalFlag χ/(line σ t-1))
    _ ≤ (C*(2+d⁻¹)+4)*logHeight q t*(1+P) := by
      change ‖logDeriv (regularizedL χ) (line σ t)‖ ≤ C*logHeight q t*(1+D) at raw
      have hfac : 1+D ≤ (2+d⁻¹)*(1+P) := by dsimp [D];nlinarith only [hP,mul_nonneg (inv_pos.mpr hd).le hP]
      have hh := mul_le_mul_of_nonneg_left hfac (mul_nonneg hC.le (by linarith : 0≤logHeight q t))
      nlinarith only [raw.trans hh,hflag,hL,mul_nonneg (by linarith : 0≤logHeight q t) hP]

end GoldbachTwistedMellin
end
end

section
open Set MeasureTheory
open scoped Interval Topology
noncomputable section
namespace GoldbachTwistedMellin

theorem exists_cluster_average {ι : Type*} (I : Finset ι) (Z : ι → Finset ℂ) (w : ι → ℝ)
    (hw : ∀ i ∈ I, 0 ≤ w i) (bad : Finset ℝ) {a b M : ℝ} (hab : a < b)
    (hM : ∀ i ∈ I, ((Z i).card:ℝ) ≤ M) :
    ∃ σ ∈ Ioo a b, σ ∉ bad ∧
      (∑ i ∈ I, w i*(1+4*∑ z ∈ Z i,rootKernel (σ-z.re))) ≤
        (1+16*M/Real.sqrt (b-a))*(∑ i ∈ I,w i) := by
  classical
  let S := I.sigma Z
  let weight := fun p : Σ _ : ι, ℂ => w p.1
  obtain ⟨x,hx,hbad,avg⟩ := exists_weighted_rootKernel_bound S weight (fun p => p.2.re)
    (fun p hp => hw p.1 (Finset.mem_sigma.mp hp).1) bad hab
  simp only [S,weight,Finset.sum_sigma] at avg
  refine ⟨x,hx,hbad,?_⟩
  have sumWeight : (∑ i ∈ I,∑ _ ∈ Z i,w i) ≤ M*∑ i ∈ I,w i := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i hi => by
      simpa only [Finset.sum_const,nsmul_eq_mul] using mul_le_mul_of_nonneg_right (hM i hi) (hw i hi)
  have hg := avg.trans (mul_le_mul_of_nonneg_left sumWeight (by positivity))
  have eq : (∑ i ∈ I,w i*(1+4*∑ z ∈ Z i,rootKernel (x-z.re))) =
      (∑ i ∈ I,w i)+4*(∑ i ∈ I,∑ z ∈ Z i,w i*rootKernel (x-z.re)) := by
    simp only [Finset.mul_sum,Finset.sum_add_distrib,mul_add,mul_one]
    simp only [mul_left_comm (w _)]
  rw [eq]
  calc
    _ ≤ (∑ i ∈ I,w i) + 4*((4/Real.sqrt (b-a))*(M*∑ i ∈ I,w i)) := by gcongr
    _ = (1+16*M/Real.sqrt (b-a))*(∑ i ∈ I,w i) := by ring

end GoldbachTwistedMellin
end
end

section
open Set Filter MeasureTheory Complex Goldbach DirichletCharacter
open scoped Topology Interval
noncomputable section
namespace GoldbachTwistedMellin

theorem potential_localize {Z S : Finset ℂ} (σ t : ℝ)
    (hs : ∀ z ∈ Z, |t-z.im| ≤ 1 → z ∈ S) :
    localZeroPotential Z σ t ≤ ∑ z ∈ S, rootKernel (σ-z.re)*rootKernel (t-z.im) := by
  classical
  rw [localZeroPotential,← Finset.sum_filter]
  exact Finset.sum_le_sum_of_subset_of_nonneg (fun z hz => hs z (Finset.mem_filter.mp hz).1 (Finset.mem_filter.mp hz).2)
    (fun z _ _ => mul_nonneg (rootKernel_nonneg _) (rootKernel_nonneg _))

theorem band_integral_majorant (S : Finset ℂ) (σ l H : ℝ) (hH : 0 ≤ H)
    (f : ℝ → ℝ) (hi : IntervalIntegrable f volume l (l+1))
    (hf : ∀ᵐ t ∂volume.restrict (Icc l (l+1)), f t ≤
      H*(1+∑ z ∈ S,rootKernel (σ-z.re)*rootKernel (t-z.im))) :
    (∫ t in l..l+1, f t) ≤ H*(1+4*∑ z ∈ S,rootKernel (σ-z.re)) := by
  let g (z : ℂ) (t : ℝ) := rootKernel (σ-z.re)*rootKernel (t-z.im)
  have ig (z : ℂ) : IntervalIntegrable (g z) volume l (l+1) :=
    (integrable_rootKernel l (l+1) z.im).const_mul _
  have isum : IntervalIntegrable (fun t => ∑ z ∈ S,g z t) volume l (l+1) :=
    ⟨integrable_finsetSum S (fun z _ => (ig z).1),integrable_finsetSum S (fun z _ => (ig z).2)⟩
  have hb := intervalIntegral.integral_mono_ae_restrict (by linarith : l ≤ l+1) hi
    ((intervalIntegrable_const.add isum).const_mul H) hf
  apply hb.trans
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_add intervalIntegrable_const isum,
    intervalIntegral.integral_const,intervalIntegral.integral_finsetSum (fun z _ => ig z),Finset.mul_sum]
  simp only [add_sub_cancel_left,one_smul]
  apply mul_le_mul_of_nonneg_left _ hH
  apply add_le_add_right
  apply Finset.sum_le_sum
  intro z hz
  rw [show (∫ t in l..l+1, g z t) = rootKernel (σ-z.re) * (∫ t in l..l+1,rootKernel (t-z.im)) from
    intervalIntegral.integral_const_mul ..]
  have hk := integral_rootKernel_le (by linarith : l ≤ l+1) z.im
  simp only [add_sub_cancel_left,Real.sqrt_one,mul_one] at hk
  exact (mul_le_mul_of_nonneg_left hk (rootKernel_nonneg _)).trans_eq (mul_comm ..)

theorem integrable_box_line {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {σ M : ℝ}
    (hs : 1/2 ≤ σ) (hs' : σ ≤ 3/4) {a b β : ℝ} (ha : 0 < a)
    (avoid : ∀ z ∈ boxZeros χ (1/2) 2 (-M-1) (M+1), σ ≠ z.re) :
    ContinuousOn (fun t : ℝ => integrand χ a b β (line σ t)) (Icc (-M) M) := by
  intro t ht
  let z := line σ t
  have hz : regularizedL χ z ≠ 0 := by
    intro hz
    have hm : z ∈ boxZeros χ (1/2) 2 (-M-1) (M+1) := by
      apply (mem_boxZeros χ _ _ _ _ z).mpr
      exact ⟨mem_reProdIm.mpr ⟨⟨by simpa [z] using hs,by dsimp [z];simp;linarith⟩,⟨by dsimp [z];simp;linarith [ht.1],by dsimp [z];simp;linarith [ht.2]⟩⟩,hz⟩
    exact avoid z hm (by simp [z])
  have hF := analytic_regularizedL χ z (mem_univ _)
  have hlog : AnalyticAt ℂ (logDeriv (regularizedL χ)) z := by
    simpa only [logDeriv,Pi.div_apply] using hF.deriv.div hF hz
  have hz1 : z-1 ≠ 0 := sub_ne_zero.mpr fun h => (by have he := congrArg Complex.re h; simp [z] at he;linarith)
  have hden : AnalyticAt ℂ (fun w : ℂ => w-1) z := analyticAt_id.sub analyticAt_const
  have hflag : AnalyticAt ℂ (fun _ : ℂ => principalFlag χ) z := analyticAt_const
  have hc : AnalyticAt ℂ (contourLog χ) z := hlog.neg.add (hflag.div hden hz1)
  have hi : AnalyticAt ℂ (integrand χ a b β) z := hc.mul ((analytic_transform ha b β).analyticAt z)
  exact (ContinuousAt.comp (f := line σ) (g := integrand χ a b β) (x := t) hi.continuousAt
    (continuous_line σ).continuousAt).continuousWithinAt

end GoldbachTwistedMellin
end
end

section
open Set Filter MeasureTheory Complex Goldbach DirichletCharacter
open scoped Topology Interval
noncomputable section
namespace GoldbachTwistedMellin

/-- The three-unit interval contains all zeros within vertical distance one
of a point of the integration interval [l,l+1]. -/
noncomputable def bandZeros {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (l : ℝ) :=
  boxZeros χ (1/2) 2 (l-1) (l+2)

theorem bandZeros_card :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (l M : ℝ),
      |l| ≤ M → ((bandZeros χ l).card:ℝ) ≤ C*logHeight q (M+2) := by
  obtain ⟨C,hC,bound⟩ := right_box_card
  refine ⟨2*C,by positivity,?_⟩
  intro q _ χ l M hm
  let P := boxZeros χ (1/2) 2 (l-1) (l+1)
  let N := boxZeros χ (1/2) 2 ((l+1)-1) ((l+1)+1)
  have hsub : bandZeros χ l ⊆ P ∪ N := by
    intro z hz
    obtain ⟨hb,hz0⟩ := (mem_boxZeros χ _ _ _ _ z).mp hz
    have h := mem_reProdIm.mp hb
    by_cases h' : z.im ≤ l+1
    · exact Finset.mem_union_left _ ((mem_boxZeros χ _ _ _ _ z).mpr ⟨mem_reProdIm.mpr ⟨h.1,h.2.1,h'⟩,hz0⟩)
    · exact Finset.mem_union_right _ ((mem_boxZeros χ _ _ _ _ z).mpr ⟨mem_reProdIm.mpr ⟨h.1,by linarith,by linarith [h.2.2]⟩,hz0⟩)
  have hn : (0:ℝ) ≤ M := (abs_nonneg _).trans hm
  have hp := (bound q χ l).trans (mul_le_mul_of_nonneg_left
    (logHeight_mono_abs q (by rw [abs_of_nonneg (by linarith : 0 ≤ M+2)];linarith : |l| ≤ |M+2|)) hC.le)
  have hh : |l+1| ≤ |M+2| := by
    rw [abs_of_nonneg (by linarith : 0 ≤ M+2)]
    linarith [abs_add_le l 1,abs_one (α:=ℝ)]
  have hN := (bound q χ (l+1)).trans (mul_le_mul_of_nonneg_left (logHeight_mono_abs q hh) hC.le)
  exact (show ((bandZeros χ l).card:ℝ) ≤ (P.card:ℝ)+(N.card:ℝ) by
    exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_union_le P N)).trans ((add_le_add hp hN).trans_eq (by ring))

theorem near_zero_in_band {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (l t M : ℝ)
    (ht : t ∈ Icc l (l+1)) {z : ℂ} (hz : z ∈ boxZeros χ (1/2) 2 (-M-1) (M+1))
    (h : |t-z.im|≤1) : z ∈ bandZeros χ l := by
  obtain ⟨hb,hz0⟩ := (mem_boxZeros χ _ _ _ _ z).mp hz
  have hi := abs_le.mp h
  exact (mem_boxZeros χ _ _ _ _ z).mpr ⟨mem_reProdIm.mpr ⟨(mem_reProdIm.mp hb).1,
    by linarith [ht.1,hi.2],by linarith [ht.2,hi.1]⟩,hz0⟩

end GoldbachTwistedMellin
end
end

section
open Set MeasureTheory Finset
open scoped Interval Topology
noncomputable section
namespace GoldbachTwistedMellin

def grid (M : ℕ) : Finset (Bool × ℕ) := Finset.univ ×ˢ Finset.range M

def gridStart (p : Bool × ℕ) : ℝ := if p.1 then (p.2:ℝ) else -((p.2:ℝ)+1)

theorem grid_geometry {M : ℕ} {p : Bool × ℕ} (hp : p ∈ grid M) :
    |gridStart p| ≤ M ∧ ∀ t ∈ Icc (gridStart p) (gridStart p+1), (p.2:ℝ) ≤ |t| ∧ |t| ≤ M := by
  have hj := Finset.mem_range.mp (Finset.mem_product.mp hp).2
  have hle : (p.2:ℝ)+1 ≤ M := by exact_mod_cast hj
  have hn : (0:ℝ) ≤ p.2 := by positivity
  cases he : p.1 <;> simp only [gridStart,he,Bool.false_eq_true,ite_false,ite_true,abs_neg,
    abs_of_nonneg hn,abs_of_nonneg (by linarith : 0≤(p.2:ℝ)+1)]
  · refine ⟨hle,?_⟩; intro t ht
    rw [abs_of_nonpos (by linarith [ht.2])]
    constructor <;> linarith [ht.1,ht.2]
  · refine ⟨by linarith,?_⟩;intro t ht
    rw [abs_of_nonneg (by linarith [ht.1])]
    exact ⟨ht.1,ht.2.trans hle⟩

theorem sum_grid_weight (M : ℕ) (w : ℕ → ℝ) :
    (∑ p ∈ grid M, w p.2) = 2*∑ j ∈ Finset.range M,w j := by
  simp [grid,Finset.sum_product,two_mul]

theorem sum_grid_integrals {M : ℕ} (f : ℝ → ℝ)
    (hi : ∀ p ∈ grid M, IntervalIntegrable f volume (gridStart p) (gridStart p+1)) :
    (∫ t in -(M:ℝ)..(M:ℝ), f t) = ∑ p ∈ grid M, ∫ t in gridStart p..gridStart p+1, f t := by
  have ip (j : ℕ) (hj : j < M) : IntervalIntegrable f volume (j:ℝ) ((j+1:ℕ):ℝ) := by
    simpa [gridStart,Nat.cast_add] using hi (true,j) (by simp [grid,hj])
  have im (j : ℕ) (hj : j < M) : IntervalIntegrable f volume (-(j:ℝ)) (-((j+1:ℕ):ℝ)) := by
    have h := (hi (false,j) (by simp [grid,hj])).symm
    simpa [gridStart,Nat.cast_add,neg_add_rev] using h
  have hp := intervalIntegral.sum_integral_adjacent_intervals (a:=fun k : ℕ => (k:ℝ)) ip
  have hm := intervalIntegral.sum_integral_adjacent_intervals (a:=fun k : ℕ => -(k:ℝ)) im
  have hip := IntervalIntegrable.trans_iterate ip
  have him := IntervalIntegrable.trans_iterate im
  simp only [Nat.cast_zero,neg_zero] at hp hm hip him
  have hneg := congrArg Neg.neg hm
  rw [← Finset.sum_neg_distrib,←intervalIntegral.integral_symm] at hneg
  simp_rw [← intervalIntegral.integral_symm] at hneg
  rw [← intervalIntegral.integral_add_adjacent_intervals him.symm hip,←hneg,←hp]
  simp [grid,gridStart,Finset.sum_product,Nat.cast_add,neg_add_rev,add_comm]

end GoldbachTwistedMellin
end
end

section
open Set Filter MeasureTheory Complex Finset
open scoped Topology
noncomputable section
namespace GoldbachTwistedMellin

/-- Average the dyadic window over unit height intervals using the oscillatory
estimates of the earlier zero-integral proof. -/

noncomputable def profile (J j : ℕ) : ℝ :=
  if j = 0 then 1 else if j ≤ J then (3+5*Real.pi)/Real.sqrt j else 20/j

theorem profile_nonneg (J j : ℕ) : 0 ≤ profile J j := by
  unfold profile
  split_ifs <;> positivity

private theorem sqrt_step (j : ℕ) :
    1 / Real.sqrt (j+1:ℝ) ≤ 2*(Real.sqrt (j+1:ℝ)-Real.sqrt j) := by
  have hp : 0 < Real.sqrt (j+1:ℝ) := by positivity
  have hle := Real.sqrt_le_sqrt (show (j:ℝ) ≤ j+1 by linarith)
  have hs1 := Real.sq_sqrt (show 0 ≤ (j+1:ℝ) by positivity)
  have hs0 := Real.sq_sqrt (show 0 ≤ (j:ℝ) by positivity)
  apply (div_le_iff₀ hp).mpr
  nlinarith only [sq_nonneg (Real.sqrt (j+1:ℝ)-Real.sqrt j), hs1, hs0]

theorem profile_sum (J N : ℕ) :
    (∑ j ∈ Finset.range (N+1), profile J j) ≤
      1+2*(3+5*Real.pi)*Real.sqrt J + 20*(1+Real.log (N+1:ℝ)) := by
  have bound (n : ℕ) :
      (∑ j ∈ Finset.range (n+1), profile J j) ≤
        1+2*(3+5*Real.pi)*Real.sqrt (min n J) + 20*(harmonic n:ℝ) := by
    induction n with
    | zero => simp [profile, harmonic]
    | succ n ih =>
      rw [Finset.sum_range_succ]
      rw [show profile J (n+1) = (if n+1 ≤ J then (3+5*Real.pi)/Real.sqrt (n+1:ℝ) else 20/(n+1:ℝ)) by simp [profile]]
      rw [harmonic_succ]
      push_cast
      split_ifs with h
      · rw [min_eq_left (show (n:ℝ)+1 ≤ J by exact_mod_cast h)]
        rw [min_eq_left (show (n:ℝ) ≤ J by exact_mod_cast Nat.le_trans (Nat.le_succ n) h)] at ih
        have hs := mul_le_mul_of_nonneg_left (sqrt_step n) (show 0 ≤ 3+5*Real.pi by positivity)
        have hr : 0 ≤ ((n:ℝ)+1)⁻¹ := by positivity
        simp only [div_eq_mul_inv, one_mul] at hs ⊢
        linarith only [ih,hs,hr]
      · have hn : J ≤ n := by omega
        rw [min_eq_right (show (J:ℝ) ≤ n by exact_mod_cast hn)] at ih
        rw [min_eq_right (show (J:ℝ) ≤ n+1 by exact_mod_cast hn.trans (Nat.le_succ _))]
        simp only [div_eq_mul_inv]
        linarith only [ih]
  have hs := Real.sqrt_le_sqrt (show min (N:ℝ) J ≤ J by exact min_le_right _ _)
  have hs' := mul_le_mul_of_nonneg_left hs (show 0 ≤ 2*(3+5*Real.pi) by positivity)
  have hn := harmonic_le_one_add_log (N+1)
  have hh : (harmonic N : ℝ) ≤ harmonic (N+1) := by
    rw [harmonic_succ]
    push_cast
    have h : 0 ≤ ((N:ℝ)+1)⁻¹ := by positivity
    linarith
  push_cast at hn
  linarith only [bound N,hs',hn,hh]

theorem window_bin_bound {X a b β V σ t : ℝ} (hX : 1 ≤ X) (ha : X ≤ a) (hab : a+1 ≤ b)
    (hb : b+1 ≤ 2*X) (hs : 0 ≤ σ) (hs' : σ ≤ 1) (hV : σ ≤ V) {j J : ℕ}
    (ht : (j:ℝ) ≤ |t|) (hJ : 4 * |β| * X ≤ (J:ℝ)) :
    ‖transform a b β (line σ t)‖ ≤ X^V * profile J j := by
  obtain ⟨triv,curv,far⟩ := norm_window_modes (zero_lt_one.trans_le hX) ha hab hb β (line σ t)
    (by simpa using hs) (by simpa using hs')
  simp only [re_line,im_line] at triv curv far
  have hpow := Real.rpow_le_rpow_of_exponent_le hX hV
  apply le_trans _ (mul_le_mul_of_nonneg_right hpow (profile_nonneg J j))
  by_cases h0 : j=0
  · simpa [profile,h0] using triv
  have hj : 0 < (j:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero h0
  have htpos := hj.trans_le ht
  by_cases hjJ : j ≤ J
  · rw [profile,ite_eq_right h0,ite_eq_left hjJ]
    apply (curv (abs_pos.mp htpos)).trans
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left (by positivity) (Real.sqrt_pos.mpr hj)
      (Real.sqrt_le_sqrt ht)) (Real.rpow_nonneg (by linarith) _)
  · rw [profile,ite_eq_right h0,ite_eq_right hjJ]
    have hfar := far htpos (hJ.trans ((by exact_mod_cast (Nat.le_of_not_ge hjJ) : (J:ℝ) ≤ j).trans ht))
    exact hfar.trans ((div_le_div_of_nonneg_left (by positivity) hj ht).trans_eq (by ring))

end GoldbachTwistedMellin
end
end

section
open Set Filter MeasureTheory Complex Goldbach DirichletCharacter
open scoped Topology Interval
noncomputable section
namespace GoldbachTwistedMellin

theorem local_band_norm {d A X a b β V σ M l : ℝ} {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (j J : ℕ) (hd : 0 < d) (hA : 0 ≤ A)
    (hX : 1 ≤ X) (ha : X ≤ a) (hab : a+1 ≤ b) (hb : b+1 ≤ 2*X)
    (hs : 1/2+d ≤ σ) (hs' : σ ≤ 3/4) (hV : σ ≤ V) (hJ : 4 * |β| * X ≤ (J:ℝ))
    (hgrid : ∀ t ∈ Icc l (l+1), (j:ℝ) ≤ |t| ∧ |t| ≤ M)
    (avoid : ∀ z ∈ boxZeros χ (1/2) 2 (-M-1) (M+1), σ ≠ z.re)
    (hlog : ∀ t : ℝ, |t| ≤ M → (∀ z ∈ boxZeros χ (1/2) 2 (-M-1) (M+1), t ≠ z.im) →
      ‖contourLog χ (line σ t)‖ ≤ A*logHeight q t*(1+localZeroPotential (boxZeros χ (1/2) 2 (-M-1) (M+1)) σ t)) :
    (∫ t in l..l+1, ‖integrand χ a b β (line σ t)‖) ≤
      (A*logHeight q (M+2)*X^V)*profile J j *
      (1+4*∑ z ∈ bandZeros χ l,rootKernel (σ-z.re)) := by
  classical
  let Z := boxZeros χ (1/2) 2 (-M-1) (M+1)
  let S := bandZeros χ l
  let G (t : ℝ) := integrand χ a b β (line σ t)
  have hM : 0 ≤ M := (abs_nonneg _).trans (hgrid l ⟨le_rfl,by linarith⟩).2
  have hL := logHeight_ge_one q (M+2)
  have hpow : 0 ≤ X^V := Real.rpow_nonneg (by linarith) _
  have hprof := profile_nonneg J j
  have H : 0 ≤ (A*logHeight q (M+2)*X^V)*profile J j := by positivity
  have hc := integrable_box_line (a:=a) (b:=b) (β:=β) χ (by linarith : 1/2 ≤ σ) hs' (zero_lt_one.trans_le (hX.trans ha)) avoid
  have hcont : ContinuousOn G (Icc l (l+1)) := hc.mono (fun t ht => abs_le.mp (hgrid t ht).2)
  have hi : IntervalIntegrable (fun t => ‖G t‖) volume l (l+1) :=
    hcont.norm.intervalIntegrable_of_Icc (by linarith)
  apply band_integral_majorant S σ l _ H _ hi
  let μ := volume.restrict (Icc l (l+1))
  have hnull : μ (↑(Z.image Complex.im):Set ℝ) = 0 := (Z.image Complex.im).measure_zero μ
  filter_upwards [ae_restrict_mem measurableSet_Icc,measure_eq_zero_iff_ae_notMem.mp hnull] with t ht him
  have yt : ∀ z ∈ Z, t ≠ z.im := fun z hz e => him (Finset.mem_image.mpr ⟨z,hz,e.symm⟩)
  have hh := hlog t (hgrid t ht).2 yt
  have hl : logHeight q t ≤ logHeight q (M+2) := by
    apply logHeight_mono_abs
    rw [abs_of_nonneg (by linarith : 0 ≤ M+2)]
    linarith [(hgrid t ht).2]
  have hloc := potential_localize (Z:=Z) (S:=S) σ t (fun z hz h => near_zero_in_band χ l t M ht hz h)
  have hw := window_bin_bound hX ha hab hb (by linarith : 0 ≤ σ) (by linarith : σ ≤ 1) hV (hgrid t ht).1 hJ
  have hsum := localPotential_nonneg Z σ t
  have h1 := (mul_le_mul (mul_le_mul_of_nonneg_left hl hA) (add_le_add_right hloc 1)
    (by linarith : 0 ≤ 1+localZeroPotential Z σ t) (by positivity)).trans' hh
  change ‖contourLog χ (line σ t)*transform a b β (line σ t)‖ ≤ _
  rw [norm_mul]
  have wn : 0 ≤ ∑ z ∈ S,rootKernel (σ-z.re)*rootKernel (t-z.im) :=
    Finset.sum_nonneg fun z _ => mul_nonneg (rootKernel_nonneg _) (rootKernel_nonneg _)
  exact (mul_le_mul h1 hw (norm_nonneg _) (by positivity)).trans_eq (by ring)

end GoldbachTwistedMellin
end
end

section
open Set Filter MeasureTheory Complex Goldbach DirichletCharacter Finset
open scoped Topology Interval
noncomputable section
namespace GoldbachTwistedMellin

theorem averaged_vertical {d : ℝ} (hd : 0 < d) (hd' : d ≤ 1/8) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (M J : ℕ)
      (a b X β : ℝ), 1 ≤ X → X ≤ a → a+1 ≤ b → b+1 ≤ 2*X → 4 * |β| * X ≤ J →
      ∃ σ ∈ Ioo (1/2+d) (1/2+2*d), (∀ z ∈ boxZeros χ (1/2) 2 (-(M:ℝ)-1) ((M:ℝ)+1), σ ≠ z.re) ∧
        (∫ t : ℝ in -(M:ℝ)..(M:ℝ), ‖integrand χ a b β (line σ t)‖) ≤
          C*X^(1/2+2*d)*(logHeight q ((M:ℝ)+2))^2*
            (1+2*(3+5*Real.pi)*Real.sqrt J+20*(1+Real.log (M+1:ℝ))) := by
  classical
  obtain ⟨A,hA,logbound⟩ := log_control_via_potential hd
  obtain ⟨K,hK,cardbound⟩ := bandZeros_card
  let D := Real.sqrt d
  have hD : 0 < D := Real.sqrt_pos.mpr hd
  let C := 2*A*(1+16*K/D)
  have hC : 0 < C := by dsimp [C];positivity
  refine ⟨C,hC,?_⟩
  intro q _ χ M J a b X β hX ha hab hb hJ
  let u : ℝ := 1/2+d
  let v : ℝ := 1/2+2*d
  let L := logHeight q ((M:ℝ)+2)
  have hL : 1 ≤ L := logHeight_ge_one q _
  let Z := boxZeros χ (1/2) 2 (-(M:ℝ)-1) ((M:ℝ)+1)
  let S := fun p : Bool × ℕ => bandZeros χ (gridStart p)
  let w := fun p : Bool × ℕ => profile J p.2
  have hw (p : Bool × ℕ) (_ : p ∈ grid M) : 0 ≤ w p := profile_nonneg _ _
  have card (p : Bool × ℕ) (hp : p ∈ grid M) : ((S p).card:ℝ) ≤ K*L :=
    cardbound q χ (gridStart p) M (grid_geometry hp).1
  obtain ⟨σ,hσ,bad,avg⟩ := exists_cluster_average (grid M) S w hw (Z.image Complex.re)
    (by dsimp [u,v];linarith : u<v) card
  have hdiff : v-u=d := by dsimp [u,v];ring
  rw [hdiff] at avg
  have avoid (z : ℂ) (hz : z ∈ Z) : σ ≠ z.re := fun he => bad (Finset.mem_image.mpr ⟨z,hz,he.symm⟩)
  refine ⟨σ,hσ,avoid,?_⟩
  let V (t : ℝ) := ‖integrand χ a b β (line σ t)‖
  have hlo : 1/2+d ≤ σ := hσ.1.le
  have hup : σ ≤ 3/4 := by dsimp [v] at hσ;linarith [hσ.2]
  have cont := (integrable_box_line (a:=a) (b:=b) (β:=β) χ (by linarith : 1/2 ≤ σ) hup
    (zero_lt_one.trans_le (hX.trans ha)) avoid).norm
  have int (p : Bool × ℕ) (hp : p ∈ grid M) : IntervalIntegrable V volume (gridStart p) (gridStart p+1) :=
    (cont.mono fun t ht => abs_le.mp ((grid_geometry hp).2 t ht).2).intervalIntegrable_of_Icc (by linarith)
  have hlocal (p : Bool × ℕ) (hp : p ∈ grid M) :
      (∫ t in gridStart p..gridStart p+1,V t) ≤ (A*L*X^v)*
        (w p*(1+4*∑ z ∈ S p,rootKernel (σ-z.re))) := by
    have h := local_band_norm χ p.2 J hd hA.le hX ha hab hb hlo hup hσ.2.le hJ (grid_geometry hp).2
      avoid (fun t ht yt => logbound q χ σ t M hlo hup ht avoid yt)
    exact h.trans_eq (by dsimp [w,L,S];ring)
  have profileBound := profile_sum J M
  have prof : (∑ j ∈ range M,profile J j) ≤ 1+2*(3+5*Real.pi)*Real.sqrt J+20*(1+Real.log (M+1:ℝ)) :=
    (sum_le_sum_of_subset_of_nonneg (range_mono (Nat.le_succ M)) (fun i _ _ => profile_nonneg _ _)).trans profileBound
  have wsum : (∑ p ∈ grid M,w p) = 2*∑ j ∈ range M,profile J j := sum_grid_weight M (profile J)
  rw [wsum] at avg
  have hn := Finset.sum_nonneg (s:=range M) (fun i _ => profile_nonneg J i)
  have hvX : 0 ≤ X^v := Real.rpow_nonneg (by linarith) _
  have factor : 1+16*(K*L)/Real.sqrt d ≤ (1+16*K/D)*L := by dsimp [D]; simp only [div_eq_mul_inv]; nlinarith only [hL]
  have bound' := avg.trans (mul_le_mul factor (mul_le_mul_of_nonneg_left prof (by norm_num : (0:ℝ)≤2))
    (by positivity) (by positivity))
  change (∫ t in -(M:ℝ)..(M:ℝ), V t) ≤ _
  rw [sum_grid_integrals V int]
  have total := Finset.sum_le_sum hlocal
  rw [←Finset.mul_sum] at total
  exact (total.trans (mul_le_mul_of_nonneg_left bound' (by positivity))).trans_eq (by dsimp [C,v,L];ring)

end GoldbachTwistedMellin
end
end

section
open Set Filter MeasureTheory Complex Goldbach DirichletCharacter GoldbachSmoothing
open scoped Topology Interval
noncomputable section
namespace GoldbachTwistedMellin

/-- With a suitable contour the signed zero residues account for every term larger
than the square-root window error and the finite-height truncation error. -/
theorem unconditional_zero_model {d : ℝ} (hd : 0 < d) (hd' : d ≤ 1/8) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (B : ℝ)
      (M J a b : ℕ) (X β : ℝ), 2 ≤ B → B+1 ≤ (M:ℝ) →
      1 ≤ X → X ≤ (a:ℝ) → (a:ℝ)+1 ≤ b → (b:ℝ)+1 ≤ 2*X → |β| ≤ 1 → 4*|β| *X ≤ J →
      ∃ T ∈ Icc B (B+1), ∃ σ ∈ Ioo (1/2+d) (1/2+2*d),
        ‖(∑ n ∈ Finset.Ioc a b, twistedCoefficient χ n * phase β n) -
          (principalFlag χ*transform a b β 1 - zeroContribution χ a b β σ T)‖ ≤
        C*(X^(1/2+2*d)*(logHeight q ((M:ℝ)+2))^2*
           (1+2*(3+5*Real.pi)*Real.sqrt J+20*(1+Real.log (M+1:ℝ))) +
           X^4*(T⁻¹ + (logHeight q ((M:ℝ)+2))^2/T^2)) := by
  classical
  obtain ⟨A,hA,horiz⟩ := unconditional_horizontal_log hd
  obtain ⟨K,hK,tail⟩ := truncation_bound
  obtain ⟨D,hD,vertical⟩ := averaged_vertical hd hd'
  let c : ℝ := 1/(2*Real.pi)
  have hc : 0 < c := by dsimp [c];positivity
  let C := max (c*D) (max K (c*(2*(2*A*96))))
  have cv : c*D ≤ C := le_max_left ..
  have ct : K ≤ C := (le_max_left ..).trans (le_max_right ..)
  have ch : c*(2*(2*A*96)) ≤ C := (le_max_right ..).trans (le_max_right ..)
  refine ⟨C,hK.trans_le ct,?_⟩
  intro q _ χ B M J a b X β hB hBM hX ha hab hb hβ hJ
  obtain ⟨T,hTB,avoid,hlog⟩ := horiz q χ B hB
  obtain ⟨σ,hσ,avoidR,hV⟩ := vertical q χ M J a b X β hX ha hab hb hJ
  have hT : 0 < T := by linarith [hTB.1]
  have hTM : T ≤ (M:ℝ) := hTB.2.trans hBM
  have hs : σ < 1 := by linarith [hσ.2]
  have inner (z : ℂ) (hz : z ∈ boxZeros χ σ 2 (-T) T) : σ < z.re ∧ z.re < 2 ∧ -T < z.im ∧ z.im < T := by
    obtain ⟨h,z0⟩ := (mem_boxZeros χ _ _ _ _ z).mp hz
    obtain ⟨⟨hr,hr'⟩,hi,hi'⟩ := mem_reProdIm.mp h
    have hzZ : z ∈ boxZeros χ (1/2) 2 (-(M:ℝ)-1) ((M:ℝ)+1) := (mem_boxZeros χ _ _ _ _ z).mpr
      ⟨mem_reProdIm.mpr ⟨⟨by linarith [hσ.1],hr'⟩,by constructor <;> linarith⟩,z0⟩
    have him := avoid z (by linarith [hσ.1]) z0
    refine ⟨lt_of_le_of_ne hr (avoidR z hzZ),lt_of_le_of_ne hr' ?_,lt_of_le_of_ne hi ?_,lt_of_le_of_ne hi' ?_⟩
    · intro e;exact regularizedL_ne_zero_right χ (by rw [e];norm_num) z0
    · intro e;exact him (by rw [←e,abs_neg,abs_of_pos hT])
    · intro e;exact him (by rw [e,abs_of_pos hT])
  refine ⟨T,hTB,σ,hσ,?_⟩
  let F := integrand χ a b β
  let H (t : ℝ) := ∫ x : ℝ in σ..2, F (line x t)
  let V := ∫ t : ℝ in (-T)..T, F (line σ t)
  let R := truncationRemainder χ a b β T
  let L := logHeight q ((M:ℝ)+2)
  let P := 1+2*(3+5*Real.pi)*Real.sqrt J+20*(1+Real.log (M+1:ℝ))
  let U := X^(1/2+2*d)*L^2*P
  have logpos : 0 ≤ Real.log (M+1:ℝ) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α:=ℝ) M])
  have hU : 0 ≤ U := by dsimp [U,P];positivity
  have hcomp : logHeight q (B+1) ≤ L := by
    apply logHeight_mono_abs
    rw [abs_of_nonneg (by linarith : 0≤B+1),abs_of_nonneg (by positivity : 0≤(M:ℝ)+2)]
    linarith
  have hH := @horizontal_edge_bound d σ T B A X β q _ χ a b hX ha hab hb hβ hd hσ.1.le hs hT hA.le hlog
  have ho (t : ℝ) (ht : |t|=T) : ‖H t‖ ≤ (2*A*96)*X^4*L^2/T^2 := by
    apply (hH ht).trans
    gcongr
    exact (zero_le_one.trans (logHeight_ge_one q (B+1)))
  have hlo := ho (-T) (by simp [abs_of_pos hT])
  have hhi := ho T (abs_of_pos hT)
  have hR := tail q χ a b X β T hX ha hab hb hβ hT
  have hi := (integrable_box_line (a:=(a:ℝ)) (b:=(b:ℝ)) (β:=β) χ (by linarith [hσ.1] : 1/2 ≤ σ)
    (by linarith [hσ.2] : σ ≤ 3/4) (zero_lt_one.trans_le (hX.trans ha)) avoidR).norm
  have hsmall : ‖V‖ ≤ ∫ t in (-T)..T, ‖F (line σ t)‖ := by
    dsimp only [V]
    rw [intervalIntegral.integral_of_le (by linarith : -T≤T),intervalIntegral.integral_of_le (by linarith : -T≤T)]
    exact norm_integral_le_integral_norm _
  have hlarge : (∫ t in (-T)..T, ‖F (line σ t)‖) ≤ ∫ t in -(M:ℝ)..(M:ℝ), ‖F (line σ t)‖ := intervalIntegral.integral_mono_interval (neg_le_neg hTM) (by linarith : -T≤T) hTM
    (ae_of_all _ (fun t => norm_nonneg (F (line σ t)))) (hi.intervalIntegrable_of_Icc (by linarith))
  have hvert : c*‖V‖ ≤ C*U := by
    calc
      _ ≤ c*(D*U) := mul_le_mul_of_nonneg_left ((hsmall.trans hlarge).trans (hV.trans_eq (by dsimp [U,P,L];ring))) hc.le
      _ ≤ C*U := by rw [←mul_assoc];exact mul_le_mul_of_nonneg_right cv hU
  have hedge : c*‖H (-T)-H T‖ ≤ C*(X^4*(L^2/T^2)) := by
    calc
      _ ≤ c*(((2*A*96)*X^4*L^2/T^2)+((2*A*96)*X^4*L^2/T^2)) :=
        mul_le_mul_of_nonneg_left ((norm_sub_le ..).trans (add_le_add hlo hhi)) hc.le
      _ = (c*(2*(2*A*96)))*(X^4*(L^2/T^2)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right ch (by positivity)
  have htrunc : ‖R‖ ≤ C*(X^4*T⁻¹) := by
    apply hR.trans
    calc
      _ = K*(X^4*T⁻¹) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right ct (by positivity)
  rw [exact_twisted_box χ hX ha hab hb hβ hs hT inner]
  unfold contourRemainder
  change ‖_ + c • (V + I*(H (-T) - H T)) + R - _‖ ≤ _
  have cancel (p l r : ℂ) : p+l+r-p=l+r := by abel
  rw [cancel,smul_add]
  apply (norm_add_le _ _).trans
  apply (add_le_add_left (norm_add_le _ _) _).trans
  rw [norm_smul,norm_smul,norm_mul,norm_I,one_mul,Real.norm_eq_abs,abs_of_pos hc]
  exact (add_le_add (add_le_add hvert hedge) htrunc).trans_eq (by dsimp [U,P,L];ring)
end GoldbachTwistedMellin
end
end

section
open Set Complex Goldbach DirichletCharacter GoldbachSmoothing
noncomputable section
namespace GoldbachTwistedMellin

/-- At a polynomial height the two tails are absorbed by the oscillatory window bound. -/
theorem dyadic_zero_model {d : ℝ} (hd : 0 < d) (hd' : d ≤ 1/8) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
      (a b : ℕ) (X β : ℝ), 1 ≤ X → X ≤ (a:ℝ) → (a:ℝ)+1 ≤ b → (b:ℝ)+1 ≤ 2*X → |β| ≤ 1 →
      ∃ T ∈ Icc (heightCut X) (heightCut X+1), ∃ σ ∈ Ioo (1/2+d) (1/2+2*d),
        ‖(∑ n ∈ Finset.Ioc a b, twistedCoefficient χ n * phase β n) -
          (principalFlag χ*transform a b β 1 - zeroContribution χ a b β σ T)‖ ≤
        C*X^(1/2+2*d)*(logBudget q X)^2*
           (1+Real.sqrt (1+4*|β| *X)+Real.log (heightCut X)) := by
  obtain ⟨C,hC,model⟩ := unconditional_zero_model hd hd'
  refine ⟨1000*C,by positivity,?_⟩
  intro q _ χ a b X β hX ha hab hb hβ
  let B := heightCut X
  let M := ⌈B+1⌉₊
  let J := ⌈4*|β| *X⌉₊
  have hB : 2 ≤ B := by dsimp [B];linarith [heightCut_ge hX]
  have hB0 : 0 < B := by linarith
  have hM : B+1 ≤ (M:ℝ) := Nat.le_ceil _
  have hJ : 4*|β| *X ≤ (J:ℝ) := Nat.le_ceil _
  have hM' : (M:ℝ) < B+1+1 := Nat.ceil_lt_add_one (by linarith)
  have hJ' : (J:ℝ) < 4*|β| *X+1 := Nat.ceil_lt_add_one (by positivity)
  obtain ⟨T,hT,σ,hσ,err⟩ := model q χ B M J a b X β hB hM hX ha hab hb hβ hJ
  refine ⟨T,hT,σ,hσ,err.trans ?_⟩
  let L := logBudget q X
  let W := 1+Real.sqrt (1+4*|β| *X)+Real.log B
  let S := X^(1/2+2*d)
  have hS : 1 ≤ S := Real.one_le_rpow hX (by linarith)
  have hL : 1 ≤ L := by dsimp [L,logBudget];linarith [logHeight_ge_one q (heightCut X)]
  have hln := Real.log_nonneg (by linarith : 1≤B)
  have hW : 1 ≤ W := by dsimp [W];linarith [Real.sqrt_nonneg (1+4*|β| *X)]
  have hq : 0 < (q:ℝ) := by exact_mod_cast NeZero.pos q
  have h3 := Real.log_le_sub_one_of_pos (by norm_num : 0<(3:ℝ))
  have hlogM : Real.log (M+1:ℝ) ≤ 2+Real.log B := by
    have h := Real.log_le_log (by positivity : 0 < (M:ℝ)+1) (by linarith : (M:ℝ)+1 ≤ 3*B)
    rw [Real.log_mul (by norm_num) hB0.ne'] at h
    linarith
  have hlogL : logHeight q ((M:ℝ)+2) ≤ 3*L := by
    have h : Real.log (2*(q:ℝ)*(2+((M:ℝ)+2))) ≤ Real.log (3*(2*(q:ℝ)*(2+B))) :=
      Real.log_le_log (by positivity) (by nlinarith only [mul_le_mul_of_nonneg_left (by linarith : 2+((M:ℝ)+2) ≤ 3*(2+B)) (by positivity : 0 ≤ 2*(q:ℝ))])
    rw [Real.log_mul (by norm_num : (3:ℝ)≠0) (by positivity)] at h
    change Real.log (2*(q:ℝ)*(2+|(M:ℝ)+2|)) ≤ 3*(1+Real.log (2*(q:ℝ)*(2+|B|)))
    rw [abs_of_nonneg (by positivity : 0≤(M:ℝ)+2),abs_of_pos hB0]
    have hl := logHeight_ge_one q B
    change 1 ≤ Real.log (2*(q:ℝ)*(2+|B|)) at hl
    rw [abs_of_pos hB0] at hl
    linarith
  have hlsq : (logHeight q ((M:ℝ)+2))^2 ≤ 9*L^2 :=
    (pow_le_pow_left₀ (zero_le_one.trans (logHeight_ge_one q _)) hlogL 2).trans_eq (by ring)
  have hroot : Real.sqrt J ≤ Real.sqrt (1+4*|β| *X) := Real.sqrt_le_sqrt (by linarith)
  have hp : (1+2*(3+5*Real.pi)*Real.sqrt J+20*(1+Real.log (M+1:ℝ))) ≤ 100*W := by
    dsimp [W]
    nlinarith only [hlogM,hln,hroot,Real.sqrt_nonneg (1+4*|β| *X),
      mul_le_mul_of_nonneg_right Real.pi_lt_four.le (Real.sqrt_nonneg (J:ℝ))]
  have hp0 : 0 ≤ 1+2*(3+5*Real.pi)*Real.sqrt J+20*(1+Real.log (M+1:ℝ)) := by
    have := Real.log_nonneg (show 1≤(M:ℝ)+1 by linarith [Nat.cast_nonneg (α:=ℝ) M])
    positivity
  have hvert := mul_le_mul (mul_le_mul_of_nonneg_left hlsq (zero_le_one.trans hS)) hp hp0 (by positivity : 0 ≤ S*(9*L^2))
  have hXT : X^4 ≤ T := by
    have hx := pow_le_pow_right₀ hX (show 4 ≤ 8 by decide)
    have h : X^8 ≤ B := by dsimp [B,heightCut];rw [mul_pow];norm_num;linarith [pow_nonneg (by linarith : 0≤X) 8]
    exact hx.trans (h.trans hT.1)
  have hT1 : 1 ≤ T := by linarith [hT.1]
  have hT0 : 0 < T := by linarith
  have ht₁ : X^4*T⁻¹ ≤ 1 := by rw [←div_eq_mul_inv];exact (div_le_one hT0).mpr hXT
  have ht₂ : X^4/T^2 ≤ 1 := (div_le_one (sq_pos_of_pos hT0)).mpr (hXT.trans (le_self_pow₀ hT1 (by decide)))
  have htail : X^4*(T⁻¹+(logHeight q ((M:ℝ)+2))^2/T^2) ≤ 1+9*L^2 := by
    calc
      _ = X^4*T⁻¹+(X^4/T^2)*(logHeight q ((M:ℝ)+2))^2 := by ring
      _ ≤ 1+1*(9*L^2) := add_le_add ht₁ (mul_le_mul ht₂ hlsq (sq_nonneg _) zero_le_one)
      _ = _ := by ring
  have hL₂ : 1 ≤ L^2 := one_le_pow₀ hL
  have hprod : L^2 ≤ S*L^2*W := (le_mul_of_one_le_left (sq_nonneg L) hS).trans
    (le_mul_of_one_le_right (by positivity) hW)
  have hall : S*(logHeight q ((M:ℝ)+2))^2*(1+2*(3+5*Real.pi)*Real.sqrt J+20*(1+Real.log (M+1:ℝ)))+
      X^4*(T⁻¹+(logHeight q ((M:ℝ)+2))^2/T^2) ≤ 1000*(S*L^2*W) := by
    nlinarith only [hvert,htail,hL₂,hprod]
  exact (mul_le_mul_of_nonneg_left hall hC.le).trans_eq (by dsimp [S,L,W,B];ring)
end GoldbachTwistedMellin
end
end

section
section GoldbachGRHWindowParseval

open scoped BigOperators ComplexConjugate
open Finset

namespace GoldbachGRHWindow

noncomputable section

private theorem norm_energy_of_columns {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] (K : A → B → ℂ) (D : A → ℝ)
    (hK : ∀ r s : A, (∑ b : B, conj (K r b) * K s b) =
      if r = s then (D r : ℂ) else 0) (f : A → ℂ) :
    (∑ b : B, ‖∑ r : A, f r * K r b‖ ^ 2) =
      ∑ r : A, D r * ‖f r‖ ^ 2 := by
  apply Complex.ofReal_injective
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_pow, ← Complex.conj_mul']
  calc
    _ = ∑ b : B, ∑ r : A, ∑ s : A, conj (f r) * f s * (conj (K r b) * K s b) := by
      refine Finset.sum_congr rfl fun b _ => ?_
      simp only [map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
      ring
    _ = ∑ r : A, ∑ s : A, conj (f r) * f s * (∑ b : B, conj (K r b) * K s b) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ = _ := by
      refine Finset.sum_congr rfl fun r _ => ?_
      simp only [hK, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
      ring

variable {q : ℕ} [NeZero q]

local instance : DecidableEq (DirichletCharacter ℂ q) := Classical.decEq _

omit [NeZero q] in
private theorem char_conj_of_unit (χ : DirichletCharacter ℂ q) {r : ZMod q}
    (hr : IsUnit r) : conj (χ r) = χ r⁻¹ := by
  have hχr : χ r ≠ 0 := (hr.map χ).ne_zero
  have hi : χ r⁻¹ = (χ r)⁻¹ := by
    calc
      _ = χ r⁻¹ * (χ r * (χ r)⁻¹) := by rw [mul_inv_cancel₀ hχr, mul_one]
      _ = _ := by rw [← mul_assoc, ← map_mul, ZMod.inv_mul_of_unit r hr, map_one, one_mul]
  exact (MulChar.star_apply' χ r).trans ((MulChar.inv_apply_eq_inv' χ r).trans hi.symm)

theorem multiplicative_energy (f : ZMod q → ℂ) :
    (∑ χ : DirichletCharacter ℂ q, ‖∑ r : ZMod q, f r * χ r‖ ^ 2) =
      (q.totient : ℝ) * ∑ r ∈ (univ : Finset (ZMod q)).filter IsUnit, ‖f r‖ ^ 2 := by
  rw [Finset.sum_filter, Finset.mul_sum]
  have hParseval := norm_energy_of_columns (fun r (χ : DirichletCharacter ℂ q) => χ r)
    (fun r : ZMod q => if IsUnit r then (q.totient : ℝ) else 0)
    (f := f) (by
      intro r s
      by_cases hr : IsUnit r
      · simp only [char_conj_of_unit _ hr, ite_eq_left hr, Complex.ofReal_natCast]
        exact DirichletCharacter.sum_char_inv_mul_char_eq ℂ hr s
      · simp [hr, MulChar.map_nonunit _ hr])
  rw [hParseval]
  refine Finset.sum_congr rfl fun r _ => ?_
  by_cases hr : IsUnit r <;> simp [hr]

/-- The additive coefficient of the unit-uniform residue distribution. -/
noncomputable def additiveModel (q : ℕ) [NeZero q] (a : ZMod q) : ℂ :=
  (∑ u : (ZMod q)ˣ, ZMod.stdAddChar (a * (u : ZMod q))) / (q.totient : ℂ)
/-- The additive kernel written with the phase convention used in the frozen theorem. -/
theorem stdAddChar_mul_nat (a : ZMod q) (k : ℕ) :
    ZMod.stdAddChar (a * (k : ZMod q)) =
      Complex.exp (((2 * Real.pi * ((k : ℝ) * ((a.val : ℝ) / (q : ℝ))) : ℝ) : ℂ) *
        Complex.I) := by
  have ha : (↑(a.val * k) : ZMod q) = a * (k : ZMod q) := by
    rw [Nat.cast_mul, ZMod.natCast_zmod_val]
  calc
    _ = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (↑(a.val * k) : ℂ) / q) := by
      rw [← ha]
      simpa only [Int.cast_natCast] using ZMod.stdAddChar_coe (N := q) (a.val * k : ℕ)
    _ = _ := by
      congr 1
      push_cast
      ring

/-- Write the character of two natural residues without reducing either natural number. -/
theorem stdAddChar_nat_pair (a k : ℕ) :
    ZMod.stdAddChar ((a : ZMod q) * (k : ZMod q)) =
      Complex.exp (((2 * Real.pi * ((a : ℝ) * (k : ℝ) / (q : ℝ)) : ℝ) : ℂ) *
        Complex.I) := by
  have h := ZMod.stdAddChar_coe (N := q) (a * k : ℕ)
  push_cast at h
  rw [h]
  congr 1
  push_cast
  ring

/-- Express the unit-model coefficient as the exact reduced numerator sum
    occurring in the major-arc statements. -/
theorem additiveModel_eq_reduced_sum (a : ℕ) :
    additiveModel q (a : ZMod q) =
      (∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime r q),
        Complex.exp (((2 * Real.pi * ((a : ℝ) * (r : ℝ) / (q : ℝ)) : ℝ) : ℂ) *
          Complex.I)) / (q.totient : ℂ) := by
  unfold additiveModel
  congr 1
  apply Finset.sum_bij (fun (u : (ZMod q)ˣ) _ => (u : ZMod q).val)
  · intro u _
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (ZMod.val_lt (u : ZMod q)), ZMod.val_coe_unit_coprime u⟩
  · intro u _ v _ huv
    apply Units.ext
    simpa only [ZMod.natCast_zmod_val] using congrArg (fun x : ℕ => (x : ZMod q)) huv
  · intro r hr
    obtain ⟨hrange, hcop⟩ := Finset.mem_filter.mp hr
    let hrunit : IsUnit (r : ZMod q) := (ZMod.isUnit_iff_coprime r q).mpr hcop
    exact ⟨hrunit.unit, Finset.mem_univ _, by
      rw [IsUnit.unit_spec, ZMod.val_natCast_of_lt (Finset.mem_range.mp hrange)]⟩
  · intro u _
    rw [← stdAddChar_nat_pair (q := q) a ((u : ZMod q).val), ZMod.natCast_zmod_val]

/-- A reduced numerator changes only the order of the same unit residues. -/
theorem additiveModel_of_unit (a : ZMod q) (ha : IsUnit a) :
    additiveModel q a = additiveModel q 1 := by
  unfold additiveModel
  apply congrArg (fun z : ℂ => z / (q.totient : ℂ))
  let e : (ZMod q)ˣ ≃ (ZMod q)ˣ := Equiv.mulLeft ha.unit
  refine Fintype.sum_equiv e (fun u => ZMod.stdAddChar (a * (u : ZMod q)))
    (fun u => ZMod.stdAddChar (1 * (u : ZMod q))) ?_
  intro u
  change ZMod.stdAddChar (a * (u : ZMod q)) =
    ZMod.stdAddChar (1 * (((ha.unit * u) : (ZMod q)ˣ) : ZMod q))
  rw [one_mul, Units.val_mul, IsUnit.unit_spec]

/-- Prime-logarithmic weights, represented in the complex field. -/
noncomputable def primeLog (k : ℕ) : ℂ :=
  ((if Nat.Prime k then Real.log (k : ℝ) else 0 : ℝ) : ℂ)

/-- A prime in a nonunit residue must divide the modulus. Its total
    logarithmic mass in any window is at most the logarithm of the modulus. -/
theorem primeLog_nonunit_mass_le (I : Finset ℕ) :
    (∑ k ∈ I.filter (fun k : ℕ => ¬ IsUnit (k : ZMod q)), ‖primeLog k‖) ≤
      Real.log (q : ℝ) := by
  let J := I.filter (fun k : ℕ => ¬ IsUnit (k : ZMod q))
  change (∑ k ∈ J, ‖primeLog k‖) ≤ _
  have hsub : J.filter Nat.Prime ⊆ q.primeFactors := by
    intro k hk
    obtain ⟨hkJ, hp⟩ := Finset.mem_filter.mp hk
    have hnu := (Finset.mem_filter.mp hkJ).2
    have hd : k ∣ q := by
      by_contra hnd
      exact hnu ((ZMod.isUnit_iff_coprime k q).mpr ((hp.coprime_iff_not_dvd).mpr hnd))
    exact Nat.mem_primeFactors.mpr ⟨hp, hd, NeZero.ne q⟩
  calc
    _ = ∑ k ∈ J.filter Nat.Prime, Real.log (k : ℝ) := by
      conv_rhs => rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun k _ => ?_
      by_cases hp : Nat.Prime k
      · have hk : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (show 1 ≤ k from hp.pos)
        simp only [primeLog, ite_eq_left hp, Complex.norm_real, Real.norm_of_nonneg (Real.log_nonneg hk)]
      · simp [primeLog, hp]
    _ ≤ ∑ p ∈ q.primeFactors, Real.log (p : ℝ) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg hsub fun p hp _ => ?_
      exact Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos)
    _ = Real.log (∏ p ∈ q.primeFactors, (p : ℝ)) := by
      symm
      exact Real.log_prod fun p hp => by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
    _ ≤ _ := by
      apply Real.log_le_log (Finset.prod_pos fun p hp => by
        exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos)
      rw [← Nat.cast_prod]
      exact_mod_cast Nat.le_of_dvd (NeZero.pos q) (Nat.prod_primeFactors_dvd q)

end

end GoldbachGRHWindow

end GoldbachGRHWindowParseval
section GoldbachGRHBandBase

/- The arithmetic foundation is adapted from muxkin's goldbach-proofs PR #2458,
   commit 25c1ef60495052eb22212b5560f90bbc6a4a0917 (Apache-2.0).
   Its source notes attributing earlier components are retained below. -/

/- The finite Ramanujan identities, kernel identities, CRT and prime-power computations
used below adapt DFQDZZ's goldbach-proofs PR #316, commit
e4ab24712555ae8c2c926adf19d368a9fb392c35 (Apache-2.0). Original credits are
retained with the corresponding sections. The multiplicative averaging, sieve estimates,
convolution bounds and the moving-modulus-window argument are derived below. -/

section

/-!
# An explicit lower bound for the Ramanujan-weighted major-arc model

The arithmetic and kernel estimates below are extracted from DFQDZZ's
goldbach-proofs PR #316 (commit e4ab24712555ae8c2c926adf19d368a9fb392c35,
Apache-2.0). The CRT and prime-power computations are credited below.
The estimate applies to every positive even target.
-/

open Finset Filter MeasureTheory

namespace GoldbachExplicitModeledMajor
noncomputable section

def phase (x : ℝ) : ℂ := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

def cutoff (n : ℕ) : ℕ := (Nat.log 2 (n + 2)) ^ 2

def kernel (n : ℕ) (β : ℝ) : ℂ := ∑ k ∈ range (n + 1), phase ((k : ℝ) * β)

def width (n q : ℕ) : ℝ := (cutoff n : ℝ) / ((q : ℝ) * n)

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

theorem cutoff_positive (n : ℕ) : 1 ≤ cutoff n :=
  Nat.one_le_iff_ne_zero.mpr (pow_ne_zero 2 (Nat.log_pos (by decide : 1 < 2) (by omega : 2 ≤ n+2)).ne')

theorem width_nonneg (n q : ℕ) : 0 ≤ width n q := by unfold width; positivity

end
end GoldbachExplicitModeledMajor

/- The finite CRT and prime-power calculations below adapt goldbach-proofs PRs #207 (XianWu18) and #203 (wzhxzkk), Apache-2.0. -/
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


namespace GoldbachGRHWindow

/-- A reduced additive numerator has the exact Möbius/totient model. -/
theorem additiveModel_eq_moebius {q : ℕ} [NeZero q] (a : ZMod q) (ha : IsUnit a) :
    additiveModel q a = (ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ) := by
  rw [additiveModel_of_unit a ha]
  have h := additiveModel_eq_reduced_sum (q := q) 1
  have hr : additiveModel q 1 =
      GoldbachExplicitModeledMajor.ram q 1 / (q.totient : ℂ) := by
    simpa only [Nat.cast_one, GoldbachExplicitModeledMajor.ram,
      GoldbachExplicitModeledMajor.phase] using h
  rw [hr, GoldbachExplicitModeledMajor.ram_one_eq_moebius]

end GoldbachGRHWindow

end GoldbachGRHRamanujanMobius
end

section
/-!
This reduction uses the uniform prime-sum estimate in Friedlander and Goldston,
Sums of Three or More Primes, p. 290, formula (1.15), as an explicit hypothesis.
-/

namespace DeepThreeQuarters

noncomputable def cutoff (n : ℕ) : ℕ := ⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊

noncomputable def width (n : ℕ) : ℕ := 256 * cutoff n * (Nat.log 2 (n+2)) ^ 2

noncomputable def wideArcs (n : ℕ) : Set ℝ := {t | ∃ q a : ℕ,
  1 ≤ q ∧ q ≤ cutoff n ∧ a ≤ q ∧ a.Coprime q ∧
  |t - (a : ℝ) / q| ≤ (width n : ℝ) / ((q : ℝ) * n)}

noncomputable def B (n q : ℕ) (β : ℝ) : ℝ := max (q : ℝ) ((q : ℝ) * n * |β|)

/-- Dirichlet approximation at the exact real scale `sqrt n`, including the two
endpoint fractions of the unit interval. -/
theorem exists_dirichlet (n : ℕ) (hn : 1 ≤ n) (t : ℝ) (ht : t ∈ Set.Icc 0 1) :
    ∃ a q : ℕ, 1 ≤ q ∧ a ≤ q ∧ a.Coprime q ∧ (q : ℝ) ≤ Real.sqrt n ∧
      |t - (a : ℝ) / q| ≤ 1 / ((q : ℝ) * Real.sqrt n) := by
  let K := ⌊Real.sqrt n⌋₊
  have hs : 1 ≤ Real.sqrt n := by
    simpa using Real.sqrt_le_sqrt (show (1 : ℝ) ≤ n by exact_mod_cast hn)
  have hK : 1 ≤ K := Nat.le_floor (by simpa using hs)
  have hK' : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hfloor : Real.sqrt n ≤ (K : ℝ) + 1 := (Nat.lt_floor_add_one _).le
  obtain ⟨r, happrox, hr⟩ := Real.exists_rat_abs_sub_le_and_den_le t hK
  have hd : (0 : ℝ) < r.den := Nat.cast_pos.mpr r.den_pos
  have hscaled : |t * r.den - r.num| ≤ 1 / ((K : ℝ) + 1) := by
    rw [Rat.cast_def, ← div_div, le_div_iff₀ hd] at happrox
    rwa [← abs_of_pos hd, ← abs_mul, sub_mul, abs_of_pos hd, div_mul_cancel₀ _ hd.ne'] at happrox
  have hnear : |t * r.den - r.num| < 1 := hscaled.trans_lt <| by
    apply (div_lt_iff₀ (by positivity)).2
    linarith
  obtain ⟨hlo, hhi⟩ := abs_lt.mp hnear
  have hreal₀ := mul_nonneg ht.1 hd.le
  have hreal₁ := mul_le_mul_of_nonneg_right ht.2 hd.le
  have hn₀ : -1 < r.num := by exact_mod_cast (show (-1:ℝ) < r.num by linarith)
  have hn₁ : r.num < (r.den : ℤ) + 1 := by
    exact_mod_cast (show (r.num:ℝ) < (r.den:ℝ) + 1 by linarith)
  have habs : (r.num.natAbs : ℤ) = r.num := Int.natAbs_of_nonneg (by omega)
  have ha : r.num.natAbs ≤ r.den := by omega
  refine ⟨r.num.natAbs, r.den, r.den_pos, ha, r.reduced, ?_, ?_⟩
  · exact (Nat.cast_le.mpr hr).trans (Nat.floor_le (Real.sqrt_nonneg _))
  · have hnR : (r.num.natAbs : ℝ) = r.num := by
      rw [Nat.cast_natAbs, abs_of_nonneg (show 0 ≤ r.num by omega)]
    rw [hnR, ← Rat.cast_def]
    apply happrox.trans
    apply one_div_le_one_div_of_le (mul_pos hd (by linarith))
    simpa [mul_comm] using mul_le_mul_of_nonneg_right hfloor hd.le

/-- Effective heights of admissible approximants to points on the deep arcs. -/
theorem height_bounds {n q a : ℕ} {t : ℝ} (hn : 1 ≤ n) (hq : 1 ≤ q) (ha : a ≤ q)
    (hc : a.Coprime q) (hdeep : t ∉ wideArcs n) (hden : (q : ℝ) ≤ Real.sqrt n)
    (happrox : |t - (a : ℝ) / q| ≤ 1 / ((q : ℝ) * Real.sqrt n)) :
    (n : ℝ) ^ (1/3 : ℝ) ≤ B n q (t - (a : ℝ) / q) ∧
      B n q (t - (a : ℝ) / q) ≤ Real.sqrt n := by
  have hq' : 0 < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hn' : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.2 hn'
  constructor
  · by_cases hsmall : q ≤ cutoff n
    · have hout : (width n : ℝ) / ((q : ℝ) * n) < |t - (a : ℝ) / q| := by
        by_contra! hin
        exact hdeep ⟨q, a, hq, hsmall, ha, hc, hin⟩
      have hw : cutoff n + 1 ≤ width n := by
        have hQ : 1 ≤ (Nat.log 2 (n+2)) ^ 2 := by
          have h := Nat.log_pos (b:=2) (n:=n+2) (by decide) (by omega)
          exact Nat.one_le_pow _ _ h
        unfold width
        have := Nat.mul_le_mul_left (256 * cutoff n) hQ
        omega
      have hw' : (cutoff n : ℝ) + 1 ≤ width n := by exact_mod_cast hw
      apply le_trans ((Nat.lt_floor_add_one ((n : ℝ) ^ (1/3 : ℝ))).le.trans hw')
      exact (le_of_lt (by simpa [mul_comm] using (div_lt_iff₀ (mul_pos hq' hn')).mp hout)).trans
        (le_max_right _ _)
    · exact (Nat.lt_of_floor_lt (lt_of_not_ge hsmall)).le.trans (le_max_left _ _)
  · apply max_le hden
    have hmul := (le_div_iff₀ (mul_pos hq' hs)).mp happrox
    have hmul' := mul_le_mul_of_nonneg_right hmul hs.le
    calc
      (q : ℝ) * n * |t - (a : ℝ) / q| =
          (|t - (a : ℝ) / q| * ((q : ℝ) * Real.sqrt n)) * Real.sqrt n := by
        conv_lhs => rw [← Real.sq_sqrt hn'.le]
        ring
      _ ≤ Real.sqrt n := by simpa using hmul'

theorem exists_deep_approximation {n : ℕ} {t : ℝ} (hn : 1 ≤ n) (ht : t ∈ Set.Icc 0 1)
    (hdeep : t ∉ wideArcs n) : ∃ a q : ℕ, 1 ≤ q ∧ a ≤ q ∧ a.Coprime q ∧
      (q : ℝ) ≤ Real.sqrt n ∧ |t - (a : ℝ)/q| ≤ 1/((q : ℝ)*Real.sqrt n) ∧
      (n : ℝ) ^ (1/3 : ℝ) ≤ B n q (t - (a : ℝ)/q) ∧
      B n q (t - (a : ℝ)/q) ≤ Real.sqrt n := by
  obtain ⟨a,q,hq,ha,hc,hd,h⟩ := exists_dirichlet n hn t ht
  exact ⟨a,q,hq,ha,hc,hd,h,height_bounds hn hq ha hc hdeep hd h⟩

end DeepThreeQuarters

namespace DeepThreeQuarters

noncomputable def geometricPhase (x : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

noncomputable def geometricSum (n : ℕ) (β : ℝ) : ℂ :=
  ∑ k ∈ Finset.range n, geometricPhase ((k : ℝ)*β)

noncomputable def positiveGeometricSum (n : ℕ) (β : ℝ) : ℂ :=
  ∑ k ∈ Finset.Icc 1 n, geometricPhase ((k : ℝ)*β)

private theorem norm_geometricPhase (x : ℝ) : ‖geometricPhase x‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

private theorem geometricPhase_pow (j : ℕ) (β : ℝ) :
    geometricPhase ((j : ℝ) * β) = geometricPhase β ^ j := by
  unfold geometricPhase
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem norm_geometricSum_le (n : ℕ) (β : ℝ) : ‖geometricSum n β‖ ≤ n := by
  calc
    _ ≤ ∑ k ∈ Finset.range n, ‖geometricPhase ((k : ℝ)*β)‖ := norm_sum_le _ _
    _ = n := by simp [norm_geometricPhase]

/-- The chord bound and geometric-series argument specialize the proof of
`goldbach_geometric_sum_le_inv_twice_round_distance` in goldbach-proofs PR
2486 (revision f3613cf846dfb3e7fe7d04fe6ce51c6ee25e7d4f) to the central period.
The multiplicative estimate includes the offset zero. -/
theorem abs_mul_norm_geometricSum_le_half (n : ℕ) {β : ℝ} (hβ : |β| ≤ 1/2) :
    |β| * ‖geometricSum n β‖ ≤ 1/2 := by
  have harg : |Real.pi * β| ≤ Real.pi / 2 := by
    rw [abs_mul, abs_of_pos Real.pi_pos, show Real.pi / 2 = Real.pi * (1 / 2) by ring]
    exact mul_le_mul_of_nonneg_left hβ Real.pi_pos.le
  have hsin : 2 * |β| ≤ |Real.sin (Real.pi * β)| := calc
    _ = 2 / Real.pi * |Real.pi * β| := by
      rw [abs_mul, abs_of_pos Real.pi_pos]
      field_simp [Real.pi_pos.ne']
    _ ≤ _ := Real.mul_abs_le_abs_sin harg
  have hchord : 4 * |β| ≤ ‖geometricPhase β - 1‖ := by
    unfold geometricPhase
    rw [mul_comm _ Complex.I, Complex.norm_exp_I_mul_ofReal_sub_one,
      show (2 * Real.pi * β) / 2 = Real.pi * β by ring, Real.norm_eq_abs, abs_mul]
    norm_num
    linarith
  have hprod : ‖geometricSum n β‖ * ‖geometricPhase β - 1‖ ≤ 2 := by
    unfold geometricSum
    simp_rw [geometricPhase_pow]
    rw [← norm_mul, geom_sum_mul]
    calc
      _ ≤ ‖geometricPhase β ^ n‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by norm_num [norm_pow, norm_geometricPhase]
  linarith only [(mul_le_mul_of_nonneg_left hchord (norm_nonneg (geometricSum n β))).trans hprod]

theorem norm_positiveGeometricSum_eq (n : ℕ) (β : ℝ) :
    ‖positiveGeometricSum n β‖ = ‖geometricSum n β‖ := by
  have hshift : positiveGeometricSum n β = geometricSum n β * geometricPhase β := by
    unfold positiveGeometricSum geometricSum
    rw [Finset.sum_mul]
    symm
    refine Finset.sum_bij (fun j _ => j+1) ?_ ?_ ?_ ?_
    · intro j hj
      have := Finset.mem_range.mp hj
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    · intro i _ j _ hij
      omega
    · intro j hj
      obtain ⟨h₁,h₂⟩ := Finset.mem_Icc.mp hj
      exact ⟨j-1, Finset.mem_range.mpr (by omega), by omega⟩
    · intro j _
      rw [geometricPhase_pow, geometricPhase_pow, pow_succ]
  rw [hshift, norm_mul, show ‖geometricPhase β‖ = 1 from Complex.norm_exp_ofReal_mul_I _, mul_one]

theorem geometricSum_mul_B_le {n q : ℕ} {β : ℝ} (hn : 4 ≤ n) (hq : 1 ≤ q)
    (hβ : |β| ≤ 1 / ((q : ℝ) * Real.sqrt n)) :
    ‖geometricSum n β‖ * B n q β ≤ (n : ℝ) * q := by
  have hs : 2 ≤ Real.sqrt n := by
    apply Real.le_sqrt_of_sq_le
    norm_num
    exact_mod_cast hn
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hden : 2 ≤ (q : ℝ) * Real.sqrt n := by nlinarith [mul_nonneg (sub_nonneg.mpr hq') (Real.sqrt_nonneg n)]
  have hhalf := abs_mul_norm_geometricSum_le_half n
    (hβ.trans (one_div_le_one_div_of_le (by norm_num) hden))
  rw [B, mul_max_of_nonneg _ _ (norm_nonneg _)]
  refine max_le (mul_le_mul_of_nonneg_right (norm_geometricSum_le n β) (Nat.cast_nonneg q)) ?_
  have h := mul_le_mul_of_nonneg_left (hhalf.trans (by norm_num : (1/2:ℝ) ≤ 1))
    (show 0 ≤ (n:ℝ) * q by positivity)
  linarith only [h]

theorem positiveGeometricSum_mul_B_le {n q : ℕ} {β : ℝ} (hn : 4 ≤ n) (hq : 1 ≤ q)
    (hβ : |β| ≤ 1 / ((q : ℝ) * Real.sqrt n)) :
    ‖positiveGeometricSum n β‖ * B n q β ≤ (n : ℝ) * q := by
  rw [norm_positiveGeometricSum_eq]
  exact geometricSum_mul_B_le hn hq hβ

end DeepThreeQuarters

/-!
# Bounds for the reciprocal totient density

The finite-product argument and logarithmic bound below are the proof of the
private helpers `harm_prod` and `ratio_bound` from the accepted Goldbach Research
PR #1810 (TH-0073), https://github.com/CGandGameEngineLearner/goldbach-proofs/pull/1810/files.
The logarithmic estimate is exposed here for reuse independently of that PR's
energy theorem. The power bounds are consequences for the deep minor arcs.
-/

namespace DeepThreeQuarters

private theorem harm_prod (s : Finset ℕ) :
    (∀ p ∈ s, 2 ≤ p) → ∏ p ∈ s, (p:ℝ) / ((p:ℝ) - 1) ≤ (s.card : ℝ) + 1 := by
  induction s using Finset.induction_on_max with
  | empty => intro _; simp
  | insert a s hlt ih =>
    intro h2
    have ha : a ∉ s := fun h => lt_irrefl _ (hlt a h)
    have ha2 : 2 ≤ a := h2 a (Finset.mem_insert_self _ _)
    have ih' := ih (fun p hp => h2 p (Finset.mem_insert_of_mem hp))
    have hsub : s ⊆ Finset.Ico 2 a := by
      intro x hx
      rw [Finset.mem_Ico]
      exact ⟨h2 x (Finset.mem_insert_of_mem hx), hlt x hx⟩
    have hk : s.card ≤ a - 2 := by
      have := Finset.card_le_card hsub
      simpa using this
    have hk' : (s.card : ℝ) + 2 ≤ a := by
      have : s.card + 2 ≤ a := by omega
      exact_mod_cast this
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
    push_cast
    have ha' : (2:ℝ) ≤ a := by exact_mod_cast ha2
    have hpos : (0:ℝ) < (a:ℝ) - 1 := by linarith
    have hP : 0 ≤ ∏ p ∈ s, (p:ℝ) / ((p:ℝ) - 1) := by
      apply Finset.prod_nonneg
      intro p hp
      have : (2:ℝ) ≤ p := by exact_mod_cast h2 p (Finset.mem_insert_of_mem hp)
      apply div_nonneg <;> linarith
    have hfrac : (a:ℝ) / ((a:ℝ) - 1) * ((s.card : ℝ) + 1) ≤ (s.card : ℝ) + 1 + 1 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hpos]
      nlinarith [Nat.cast_nonneg (α := ℝ) s.card]
    calc (a:ℝ) / ((a:ℝ) - 1) * ∏ p ∈ s, (p:ℝ) / ((p:ℝ) - 1)
        ≤ (a:ℝ) / ((a:ℝ) - 1) * ((s.card : ℝ) + 1) := by
          apply mul_le_mul_of_nonneg_left ih' (by positivity)
      _ ≤ _ := hfrac

theorem totient_ratio_le_four_log (q : ℕ) (hq : 0 < q) :
    (q:ℝ) / (q.totient : ℝ) ≤ 4 * Real.log ((q + 2 : ℕ) : ℝ) := by
  have hprime : ∀ p ∈ q.primeFactors, 2 ≤ p := fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le
  have hh := harm_prod q.primeFactors hprime
  have hid := Nat.totient_mul_prod_primeFactors q
  have hφ : (0:ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.2 hq
  have hP : (0:ℝ) < ∏ p ∈ q.primeFactors, (p:ℝ) := by
    apply Finset.prod_pos
    intro p hp
    have : (2:ℝ) ≤ p := by exact_mod_cast hprime p hp
    linarith
  have hP1 : (0:ℝ) < ∏ p ∈ q.primeFactors, ((p:ℝ) - 1) := by
    apply Finset.prod_pos
    intro p hp
    have : (2:ℝ) ≤ p := by exact_mod_cast hprime p hp
    linarith
  have hid' : (q.totient : ℝ) * ∏ p ∈ q.primeFactors, (p:ℝ)
      = (q:ℝ) * ∏ p ∈ q.primeFactors, ((p:ℝ) - 1) := by
    have := congrArg (fun x : ℕ => (x : ℝ)) hid
    simp only [Nat.cast_mul, Nat.cast_prod] at this
    rw [this]
    congr 1
    apply Finset.prod_congr rfl
    intro p hp
    rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_le]
    simp
  have heq : (q:ℝ) / (q.totient : ℝ) = ∏ p ∈ q.primeFactors, (p:ℝ) / ((p:ℝ) - 1) := by
    rw [Finset.prod_div_distrib, div_eq_div_iff hφ.ne' hP1.ne']
    linarith
  have hpow : 2 ^ q.primeFactors.card ≤ q := by
    calc 2 ^ q.primeFactors.card ≤ ∏ p ∈ q.primeFactors, p :=
          Finset.pow_card_le_prod _ _ _ hprime
      _ ≤ q := Nat.le_of_dvd hq (Nat.prod_primeFactors_dvd q)
  have hlog2 : (1:ℝ) / 2 ≤ Real.log 2 := by
    have := Real.one_sub_inv_le_log_of_pos (x := 2) (by norm_num)
    norm_num at this
    linarith
  have hk : (q.primeFactors.card : ℝ) * Real.log 2 ≤ Real.log ((q + 2 : ℕ) : ℝ) := by
    rw [← Real.log_pow]
    apply Real.log_le_log (by positivity)
    have : ((2 ^ q.primeFactors.card : ℕ) : ℝ) ≤ ((q + 2 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 2 ^ q.primeFactors.card ≤ q + 2)
    simpa using this
  have hL : (1:ℝ) / 2 ≤ Real.log ((q + 2 : ℕ) : ℝ) := by
    refine hlog2.trans (Real.log_le_log (by norm_num) ?_)
    exact_mod_cast (by omega : 2 ≤ q + 2)
  have hc : (0:ℝ) ≤ q.primeFactors.card := Nat.cast_nonneg _
  rw [heq]
  have : (q.primeFactors.card : ℝ) * (1 / 2) ≤ q.primeFactors.card * Real.log 2 :=
    mul_le_mul_of_nonneg_left hlog2 hc
  linarith

/-- A modulus-uniform bound for every positive exponent, with an explicit constant. -/
theorem totient_ratio_le_rpow {ε : ℝ} (hε : 0 < ε) (q : ℕ) (hq : 0 < q) :
    (q : ℝ) / (q.totient : ℝ) ≤ (8 + 4 / ε) * (q : ℝ) ^ ε := by
  have hq₁ : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hpow : 1 ≤ (q : ℝ) ^ ε := Real.one_le_rpow hq₁ hε.le
  have hlog : Real.log ((q + 2 : ℕ) : ℝ) ≤ Real.log 3 + Real.log q := by
    rw [← Real.log_mul (by norm_num) (by positivity)]
    apply Real.log_le_log (by positivity)
    push_cast
    linarith
  have hthree : Real.log 3 ≤ 2 := by
    linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num)]
  calc
    (q : ℝ) / (q.totient : ℝ) ≤ 4 * Real.log ((q + 2 : ℕ) : ℝ) :=
      totient_ratio_le_four_log q hq
    _ ≤ 8 + 4 * ((q : ℝ) ^ ε / ε) := by
      linarith [Real.log_natCast_le_rpow_div q hε]
    _ ≤ 8 * (q : ℝ) ^ ε + 4 * ((q : ℝ) ^ ε / ε) := by linarith
    _ = (8 + 4 / ε) * (q : ℝ) ^ ε := by ring

end DeepThreeQuarters

namespace DeepThreeQuarters

/-- Convert a geometric-sum estimate at a rational approximation into the
bound for its Möbius-weighted main term. -/
theorem rational_term_le {ε b : ℝ} {n q : ℕ} {z : ℂ} (hε : 0 < ε)
    (hq : 0 < q) (hqn : (q : ℝ) ≤ n) (hb : 0 < b)
    (hz : ‖z‖ * b ≤ (n : ℝ) * q) :
    ‖(ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ) * z‖ ≤
      (8 + 4/ε) * (n : ℝ) ^ ε * ((n : ℝ) / b) := by
  have hmu : ‖(ArithmeticFunction.moebius q : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast, ← Int.cast_abs]
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := q))
  have hφ : 0 < (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
  have hz' := (le_div_iff₀ hb).mpr hz
  have hratio := (totient_ratio_le_rpow hε q hq).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (Nat.cast_nonneg _) hqn hε.le) (by positivity))
  calc
    _ = (‖(ArithmeticFunction.moebius q : ℂ)‖ / (q.totient : ℝ)) * ‖z‖ := by
      rw [norm_mul, norm_div, Complex.norm_natCast]
    _ ≤ (1 / (q.totient : ℝ)) * ((n : ℝ) * q / b) :=
      mul_le_mul (div_le_div_of_nonneg_right hmu hφ.le) hz' (norm_nonneg _) (by positivity)
    _ = ((q : ℝ) / (q.totient : ℝ)) * ((n : ℝ) / b) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hratio (by positivity)

end DeepThreeQuarters

open Filter

namespace DeepThreeQuarters

/-- Combine the rational main term with the error in its approximation. -/
theorem pointwise_budget {x B C ε : ℝ} (hx : 1 ≤ x) (hC : 0 ≤ C)
    (hlo : x ^ (1/3 : ℝ) ≤ B) (hhi : B ≤ Real.sqrt x)
    (P M : ℂ)
    (hmodel : ‖M‖ ≤ C * x ^ ε * (x / B))
    (herror : ‖P - M‖ ≤ C * x ^ ε * (Real.sqrt x * Real.sqrt B)) :
    ‖P‖ ≤ (2 * C) * x ^ (3/4 + ε) := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hquarter : x / B ≤ x ^ (3/4 : ℝ) := by
    calc
      _ ≤ x / x ^ (1/3 : ℝ) :=
        div_le_div_of_nonneg_left hx0.le (Real.rpow_pos_of_pos hx0 _) hlo
      _ = x ^ (1 - 1/3 : ℝ) := by rw [Real.rpow_sub hx0, Real.rpow_one]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
  have he : Real.sqrt x * Real.sqrt B ≤ x ^ (3/4 : ℝ) := by
    calc
      _ ≤ Real.sqrt x * Real.sqrt (Real.sqrt x) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hhi) (Real.sqrt_nonneg _)
      _ = _ := by
        simp only [Real.sqrt_eq_rpow, ← Real.rpow_mul hx0.le, ← Real.rpow_add hx0]
        norm_num
  have hfac : 0 ≤ C * x ^ ε := mul_nonneg hC (Real.rpow_nonneg hx0.le _)
  have htriangle : ‖P‖ ≤ ‖P - M‖ + ‖M‖ := by
    calc
      ‖P‖ = ‖(P - M) + M‖ := by rw [sub_add_cancel]
      _ ≤ _ := norm_add_le _ _
  have hsum := htriangle.trans (add_le_add
    (herror.trans (mul_le_mul_of_nonneg_left he hfac))
    (hmodel.trans (mul_le_mul_of_nonneg_left hquarter hfac)))
  rw [Real.rpow_add hx0]
  linarith only [hsum]

/-- Absorb every fixed constant into the arbitrarily small power in the
registered conclusion. The threshold is uniform in the point on the arc. -/
theorem eventually_absorb (C η : ℝ) (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop,
      C * (n : ℝ) ^ (3/4 + η/2) ≤ (n : ℝ) ^ (3/4 + η) := by
  have hlim : Tendsto (fun n : ℕ => (n : ℝ) ^ (η/2)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith : 0 < η/2)).comp tendsto_natCast_atTop_atTop
  filter_upwards [hlim.eventually_ge_atTop C, eventually_ge_atTop 1] with n hpow hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  calc
    _ ≤ (n : ℝ) ^ (η/2) * (n : ℝ) ^ (3/4 + η/2) :=
      mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hn'.le _)
    _ = _ := by rw [← Real.rpow_add hn']; congr 1; ring

end DeepThreeQuarters

namespace DeepThreeQuarters

/-- Absorb the two logarithmic losses in the Friedlander–Goldston (1.15)
error term. The constant is independent of the modulus and frequency. -/
private theorem log_product_bound {x ε : ℝ} (hx : 1 ≤ x) (hε : 0 < ε) :
    Real.log x * (Real.log x + 1) ≤ ((2 / ε)^2 + 1 / ε) * x ^ ε := by
  have hx' : 0 < x := zero_lt_one.trans_le hx
  have hlog := Real.log_nonneg hx
  have hhalf := Real.log_le_rpow_div hx'.le (half_pos hε)
  have hsq := mul_self_le_mul_self hlog hhalf
  have hp : x ^ (ε / 2) * x ^ (ε / 2) = x ^ ε := by
    rw [← Real.rpow_add hx', add_halves]
  have hsq' : Real.log x * Real.log x ≤ (2 / ε)^2 * x ^ ε := by
    calc
      _ ≤ (x ^ (ε / 2) / (ε/2)) * (x ^ (ε / 2) / (ε/2)) := hsq
      _ = (2 / ε)^2 * (x ^ (ε / 2) * x ^ (ε / 2)) := by ring
      _ = _ := by rw [hp]
  calc
    _ = Real.log x * Real.log x + Real.log x := by ring
    _ ≤ (2 / ε)^2 * x ^ ε + x ^ ε / ε := add_le_add hsq' (Real.log_le_rpow_div hx'.le hε)
    _ = _ := by ring

/-- Normalization of the numerical error term in Friedlander–Goldston (1.15).
This estimate holds for every frequency offset and modulus as soon as n ≥ 1.
The analytic assertion (1.15) itself is a separate input. -/
theorem friedlanderGoldston_error_normalize {ε : ℝ} (hε : 0 < ε)
    (n q : ℕ) (β : ℝ) (hn : 1 ≤ n) :
    Real.sqrt ((q : ℝ) * n) * Real.log n * (Real.log n + Real.sqrt (n * |β|)) ≤
      ((2 / ε)^2 + 1 / ε) * (n : ℝ)^ε * (Real.sqrt n * Real.sqrt (B n q β)) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog := Real.log_nonneg hn'
  have hq : Real.sqrt q ≤ Real.sqrt (B n q β) := Real.sqrt_le_sqrt (le_max_left _ _)
  have hshift : Real.sqrt q * Real.sqrt (n * |β|) ≤ Real.sqrt (B n q β) := by
    rw [← Real.sqrt_mul (Nat.cast_nonneg q)]
    apply Real.sqrt_le_sqrt
    rw [← mul_assoc]
    exact le_max_right _ _
  have hsum :
      Real.sqrt q * (Real.log n + Real.sqrt (n * |β|)) ≤
        Real.sqrt (B n q β) * (Real.log n + 1) := by
    simp only [mul_add, mul_one]
    linarith only [mul_le_mul_of_nonneg_right hq hlog, hshift]
  calc
    _ = (Real.sqrt n * Real.log n) * (Real.sqrt q * (Real.log n + Real.sqrt (n * |β|))) := by
      rw [Real.sqrt_mul (Nat.cast_nonneg q)]
      ring
    _ ≤ (Real.sqrt n * Real.log n) * (Real.sqrt (B n q β) * (Real.log n + 1)) :=
      mul_le_mul_of_nonneg_left hsum (mul_nonneg (Real.sqrt_nonneg _) hlog)
    _ = (Real.log n * (Real.log n + 1)) * (Real.sqrt n * Real.sqrt (B n q β)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (log_product_bound hn' hε)
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

end DeepThreeQuarters

namespace DeepThreeQuarters

noncomputable def primeWeight (k : ℕ) : ℝ := if k.Prime then Real.log k else 0

noncomputable def weightedSum (n : ℕ) (u : ℕ → ℝ) (t : ℝ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1), (u k : ℂ) *
    Complex.exp (((2 * Real.pi * ((k : ℝ) * t) : ℝ) : ℂ) * Complex.I)

end DeepThreeQuarters

open Filter

namespace DeepThreeQuarters

noncomputable def rationalModel (n q : ℕ) (β : ℝ) : ℂ :=
  (ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ) * positiveGeometricSum n β


end DeepThreeQuarters
end

section
open Set Filter MeasureTheory Complex
open scoped Topology Interval
noncomputable section
namespace GoldbachTwistedMellin

theorem phase_dist (β x y : ℝ) : ‖phase β x-phase β y‖ ≤ |β| * |x-y| := by
  exact (convex_univ (𝕜 := ℝ) (E := ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z _ => (phase_deriv β z).hasDerivWithinAt)
    (fun z _ => by simp [Real.norm_eq_abs]) (mem_univ y) (mem_univ x)

theorem phase_cell {u : ℝ} (hu : u ∈ Icc (0:ℝ) 1) (β : ℝ) (k : ℕ) :
    ‖(∫ x : ℝ in ((k:ℝ)+u)..((k:ℝ)+1+u), phase β x) - phase β ((k:ℝ)+1)‖ ≤ |β| := by
  have hi := (continuous_phase β).intervalIntegrable ((k:ℝ)+u) ((k:ℝ)+1+u) (μ := volume)
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const (a := (k:ℝ)+u) (b := (k:ℝ)+1+u)
    (f := fun x => phase β x-phase β ((k:ℝ)+1)) (C := |β|) (fun x hx => by
      rw [uIoc_of_le (by linarith)] at hx
      have h := phase_dist β x ((k:ℝ)+1)
      exact h.trans (by
        conv_rhs => rw [← mul_one |β|]
        exact mul_le_mul_of_nonneg_left (abs_le.mpr ⟨by linarith [hu.1,hx.1],by linarith [hu.2,hx.2]⟩) (abs_nonneg _)))
  rw [intervalIntegral.integral_sub hi intervalIntegrable_const,intervalIntegral.integral_const] at hh
  simpa [show (k:ℝ)+1+u-((k:ℝ)+u) = 1 by ring] using hh

theorem phase_cells {u : ℝ} (hu : u ∈ Icc (0:ℝ) 1) (β : ℝ) (a b : ℕ) (hab : a ≤ b) :
    ‖(∫ x : ℝ in ((a:ℝ)+u)..((b:ℝ)+u), phase β x) - ∑ k ∈ Finset.Ioc a b, phase β k‖ ≤
      ((b:ℝ)-a)*|β| := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    have hI : Finset.Ioc a (b+1) = insert (b+1) (Finset.Ioc a b) := by
      ext k; simp only [Finset.mem_Ioc,Finset.mem_insert]; omega
    have hk : b+1 ∉ Finset.Ioc a b := by simp
    rw [hI,Finset.sum_insert hk,Nat.cast_succ,← intervalIntegral.integral_add_adjacent_intervals
      ((continuous_phase β).intervalIntegrable _ ((b:ℝ)+u)) ((continuous_phase β).intervalIntegrable _ _)]
    have h := norm_add_le ((∫ x : ℝ in ((a:ℝ)+u)..((b:ℝ)+u), phase β x) - ∑ k ∈ Finset.Ioc a b, phase β k)
      ((∫ x : ℝ in ((b:ℝ)+u)..((b:ℝ)+1+u), phase β x) - phase β ((b:ℝ)+1))
    rw [show ∀ A B C D : ℂ, A+B-(D+C) = (A-C)+(B-D) by intros; ring]
    exact h.trans ((add_le_add ih (phase_cell hu β b)).trans_eq (by ring))

theorem principal_approx {a b : ℕ} (ha : 0 < a) (hab : a+1 ≤ b) (β : ℝ) :
    ‖transform a b β 1 - ∑ k ∈ Finset.Ioc a b, phase β k‖ ≤ ((b:ℝ)-a)*|β| := by
  let S := ∑ k ∈ Finset.Ioc a b, phase β k
  let H := fun u : ℝ => ∫ x : ℝ in ((a:ℝ)+u)..((b:ℝ)+u), phase β x
  have hi (x y : ℝ) := (continuous_phase β).intervalIntegrable x y (μ := volume)
  have hc : Continuous H := by
    let P := fun v : ℝ => ∫ x : ℝ in (0:ℝ)..v, phase β x
    have cp : Continuous P := intervalIntegral.continuous_primitive hi 0
    have eqH : H = fun u => P ((b:ℝ)+u)-P ((a:ℝ)+u) := by
      funext u
      exact (eq_sub_of_add_eq' (intervalIntegral.integral_add_adjacent_intervals (hi 0 ((a:ℝ)+u)) (hi ((a:ℝ)+u) ((b:ℝ)+u))))
    rw [eqH]
    exact (cp.comp (continuous_const.add continuous_id)).sub (cp.comp (continuous_const.add continuous_id))
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := 1)
    (f := fun u => H u-S) (C := ((b:ℝ)-a)*|β|) (fun u hu => by
      rw [uIoc_of_le zero_le_one] at hu
      exact phase_cells ⟨hu.1.le,hu.2⟩ β a b (by omega))
  rw [intervalIntegral.integral_sub (hc.intervalIntegrable _ _) intervalIntegrable_const,
    intervalIntegral.integral_const] at h
  rw [transform_eq_average (by exact_mod_cast ha) (by exact_mod_cast hab)]
  simpa [H,S,density] using h

end GoldbachTwistedMellin
end
end

section
open Finset Set Filter MeasureTheory Complex GoldbachGRHWindow GoldbachSmoothing Goldbach
open scoped Topology Interval
noncomputable section
namespace GoldbachTwistedMellin

private theorem nonprime_mass (n : ℕ) :
    (∑ k ∈ range (n+1), if k.Prime then 0 else ArithmeticFunction.vonMangoldt k) =
      Chebyshev.psi n - Chebyshev.theta n := by
  rw [Chebyshev.psi_eq_sum_Icc,Chebyshev.theta_eq_sum_Icc,Nat.floor_natCast,
    sum_filter,←sum_sub_distrib,Nat.range_succ_eq_Icc_zero]
  apply sum_congr rfl
  intro k _
  by_cases hk : k.Prime <;> simp [hk,ArithmeticFunction.vonMangoldt_apply_prime]

theorem prime_removal {q : ℕ} (χ : DirichletCharacter ℂ q) (a b n : ℕ)
    (hb : b ≤ n) (hn : 1 ≤ n) (β : ℝ) :
    ‖(∑ k ∈ Finset.Ioc a b, (primeLog k*phase β k)*χ (k:ZMod q)) -
      (∑ k ∈ Finset.Ioc a b, twistedCoefficient χ k*phase β k)‖ ≤
      2*Real.sqrt n*Real.log n := by
  rw [← sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ k ∈ Finset.Ioc a b, if k.Prime then 0 else ArithmeticFunction.vonMangoldt k := by
      apply sum_le_sum
      intro k _
      by_cases hk : k.Prime
      · simp [primeLog,twistedCoefficient,hk,ArithmeticFunction.vonMangoldt_apply_prime hk,mul_comm,mul_left_comm,mul_assoc]
      · simp only [primeLog,ite_eq_right hk,ofReal_zero,zero_mul,zero_sub,norm_neg,
          twistedCoefficient,Pi.mul_apply,norm_mul,norm_phase,mul_one,Complex.norm_real,
          Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
        exact (mul_le_mul_of_nonneg_right (χ.norm_le_one _) ArithmeticFunction.vonMangoldt_nonneg).trans_eq (one_mul _)
    _ ≤ ∑ k ∈ range (n+1), if k.Prime then 0 else ArithmeticFunction.vonMangoldt k := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro k hk; have := (mem_Ioc.mp hk).2; apply Finset.mem_range.mpr; omega
      · intro k _ _; split_ifs <;> positivity
    _ ≤ _ := by rw [nonprime_mass]; exact Chebyshev.psi_sub_theta_le (by exact_mod_cast hn)


end GoldbachTwistedMellin
end
end

section
open Finset Complex GoldbachGRHWindow
noncomputable section
namespace GoldbachTwistedMellin

def primeError {q : ℕ} [NeZero q] (r : ZMod q) (β : ℝ) (k : ℕ) : ℂ :=
  (primeLog k*phase β k)*ZMod.stdAddChar (r*(k:ZMod q)) - phase β k*additiveModel q r

theorem sum_primeError {q : ℕ} [NeZero q] (r : ZMod q) (β : ℝ) (a b : ℕ) :
    (∑ k ∈ Finset.Ioc a b, primeError r β k) =
    (∑ k ∈ Finset.Ioc a b, (primeLog k*phase β k)*ZMod.stdAddChar (r*(k:ZMod q))) -
      (∑ k ∈ Finset.Ioc a b, phase β k)*additiveModel q r := by
  simp only [primeError,sum_sub_distrib,sum_mul]

theorem norm_unit_model {q : ℕ} [NeZero q] (r : ZMod q) : ‖additiveModel q r‖ ≤ 1 := by
  have hphi : 0 < (q.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  rw [additiveModel,norm_div,Complex.norm_natCast,div_le_iff₀ hphi,one_mul]
  refine (norm_sum_le ..).trans ?_
  simp [ZMod.stdAddChar_apply,ZMod.card_units_eq_totient]

theorem primeError_small {q : ℕ} [NeZero q] (r : ZMod q) (β : ℝ) (j : ℕ) (hj : j ≤ 3) :
    ‖∑ k ∈ Finset.Ioc 0 j, primeError r β k‖ ≤ 12 := by
  refine (norm_sum_le ..).trans ?_
  calc
    _ ≤ ∑ _k ∈ Finset.Ioc 0 j, (4:ℝ) := by
      refine sum_le_sum fun k hk => ?_
      have hpos : 0 < k := (mem_Ioc.mp hk).1
      have hle : k ≤ 3 := (mem_Ioc.mp hk).2.trans hj
      have hposR : 1 ≤ (k:ℝ) := by exact_mod_cast hpos
      have hleR : (k:ℝ) ≤ 3 := by exact_mod_cast hle
      have hp : ‖primeLog k‖ ≤ 3 := by
        unfold primeLog
        by_cases h : k.Prime
        · simp only [ite_eq_left h,Complex.norm_real,Real.norm_of_nonneg (Real.log_nonneg hposR)]
          linarith only [Real.log_le_sub_one_of_pos (by linarith : 0 < (k:ℝ)),hleR]
        · simp [h]
      unfold primeError
      refine (norm_sub_le ..).trans ?_
      simpa [norm_mul,ZMod.stdAddChar_apply] using (add_le_add hp (norm_unit_model r)).trans_eq (by norm_num : (3:ℝ)+1=4)
    _ ≤ _ := by simp; exact_mod_cast (show j*4 ≤ 12 by omega)

end GoldbachTwistedMellin
end
end

section
open Set Real Goldbach
noncomputable section
namespace GoldbachTwistedMellin

def logScale (x : ℝ) := 1+Real.log (2*x)
theorem logScale_one {x : ℝ} (hx : 1 ≤ x) : 1 ≤ logScale x := by
  dsimp [logScale]
  linarith only [Real.log_nonneg (by linarith : 1 ≤ 2*x)]
theorem log_le_scale {x : ℝ} (hx : 1 ≤ x) : Real.log x ≤ logScale x := by
  dsimp [logScale]
  linarith only [Real.log_le_log (by linarith : 0 < x) (by linarith : x ≤ 2*x)]

theorem log_window_scale {X x : ℝ} {q : ℕ} [NeZero q] (hX : 1 ≤ X) (hXx : X ≤ x)
    (hq : (q:ℝ) ≤ x) : logBudget q X ≤ 10*logScale x ∧ Real.log (heightCut X) ≤ 8*logScale x := by
  have hx := hX.trans hXx
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hT : 1 ≤ heightCut X := by dsimp [heightCut]; exact one_le_pow₀ (by linarith)
  have hT0 := zero_lt_one.trans_le hT
  have qpos : 0 < (q:ℝ) := by exact_mod_cast NeZero.pos q
  have ht : Real.log (heightCut X) ≤ 8*Real.log (2*x) := by
    rw [heightCut,Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    exact mul_le_mul_of_nonneg_left (Real.log_le_log (by linarith) (by linarith)) (by norm_num)
  have ht' : 2+heightCut X ≤ 3*heightCut X := by linarith
  have hlog := Real.log_le_log (by linarith : 0 < 2+heightCut X) ht'
  rw [Real.log_mul (by norm_num) hT0.ne'] at hlog
  have hqlog := Real.log_le_log (by positivity : 0 < 2*(q:ℝ)) (by linarith : 2*(q:ℝ) ≤ 2*x)
  have hln3 := Real.log_le_sub_one_of_pos (by norm_num : 0<(3:ℝ))
  have hln := Real.log_nonneg (by linarith : 1 ≤ 2*x)
  dsimp only [logScale,logBudget,logHeight]
  rw [abs_of_pos hT0,Real.log_mul (by positivity) (by linarith : 2+heightCut X ≠ 0)]
  constructor <;> linarith

theorem sqrt_q_budget {x X γ : ℝ} {q : ℕ} [NeZero q]
    (hX : 1 ≤ X) (hXx : X ≤ x) (hq : (q:ℝ) ≤ x^(3/10 : ℝ))
    (hγ : (q:ℝ)*|γ| * x ≤ 8*x^(3/10 : ℝ)) :
    Real.sqrt q ≤ x^(3/20 : ℝ) ∧
    Real.sqrt q*(1+Real.sqrt (1+4*|γ| * X)+Real.log (heightCut X)) ≤ 17*logScale x*x^(3/20 : ℝ) := by
  have hx := hX.trans hXx
  have hx0 := (zero_lt_one.trans_le hx).le
  have hq' : (q:ℝ) ≤ x := hq.trans
    ((Real.rpow_le_rpow_of_exponent_le hx (show (3/10 : ℝ) ≤ 1 by norm_num)).trans_eq (Real.rpow_one x))
  have hQ : Real.sqrt (x^(3/10 : ℝ)) = x^(3/20 : ℝ) := by
    rw [Real.sqrt_eq_rpow,← Real.rpow_mul hx0]
    norm_num
  have hq₁ := (Real.sqrt_le_sqrt hq).trans_eq hQ
  have hq₂ : Real.sqrt q*Real.sqrt (1+4*|γ| * X) ≤ 8*x^(3/20 : ℝ) := by
    have hqq := mul_le_mul_of_nonneg_left hXx (mul_nonneg (Nat.cast_nonneg q) (abs_nonneg γ))
    have hcmp : (q:ℝ)*(1+4*|γ| * X) ≤ 64*x^(3/10 : ℝ) := by
      nlinarith only [hγ,hq,hqq,Real.rpow_nonneg hx0 (3/10 : ℝ)]
    rw [← Real.sqrt_mul (Nat.cast_nonneg q),← hQ]
    exact (Real.sqrt_le_sqrt hcmp).trans_eq (by rw [Real.sqrt_mul (by norm_num : 0 ≤ (64:ℝ))]; norm_num)
  have hlog := (log_window_scale hX hXx hq').2
  have hT : 1 ≤ heightCut X := by dsimp [heightCut]; exact one_le_pow₀ (by linarith)
  have hsqlog := mul_le_mul hq₁ hlog (Real.log_nonneg hT) (Real.rpow_nonneg hx0 _)
  have hL := mul_le_mul_of_nonneg_right (logScale_one hx) (Real.rpow_nonneg hx0 (3/20 : ℝ))
  exact ⟨hq₁,by nlinarith only [hq₁,hq₂,hsqlog,hL]⟩

end GoldbachTwistedMellin
end
end

section
open Set Real Complex Goldbach
noncomputable section
namespace GoldbachTwistedMellin

theorem block_budget {x X γ C : ℝ} {q : ℕ} [NeZero q] (hX : 1 ≤ X) (hXx : X ≤ x)
    (hC : 0 ≤ C) (hq : (q:ℝ) ≤ x^(3/10 : ℝ)) (hγ : (q:ℝ)*|γ| * x ≤ 8*x^(3/10 : ℝ)) :
    Real.sqrt q*(2*Real.sqrt x*Real.log x +
      C*X^(5/8 : ℝ)*logBudget q X*(1+Real.sqrt (1+4*|γ| * X)+Real.log (heightCut X)) +
      x*|γ| + Real.log q) ≤ (12+170*C)*x^(31/40 : ℝ)*logScale x^2 := by
  let L := logScale x
  let Q := x^(3/20 : ℝ)
  let S := x^(5/8 : ℝ)
  let U := x^(31/40 : ℝ)
  have hx := hX.trans hXx
  have hx0 := zero_lt_one.trans_le hx
  have hL : 1 ≤ L := logScale_one hx
  have hL0 : 0 ≤ L := by linarith
  have hLL : L ≤ L^2 := by nlinarith only [hL,sq_nonneg (L-1)]
  have hL2 : 1 ≤ L^2 := hL.trans hLL
  have hqpos : 1 ≤ (q:ℝ) := by exact_mod_cast NeZero.pos q
  have hBase : x^(3/10 : ℝ) ≤ Real.sqrt x := by
    rw [Real.sqrt_eq_rpow]; exact Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
  have hqx := (hq.trans hBase).trans (Real.sqrt_le_self_iff.mpr (Or.inr hx))
  have hlogq := (Real.log_le_log (by linarith : 0 < (q:ℝ)) hqx).trans (log_le_scale hx)
  have hS : Real.sqrt x ≤ S := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
  have hXS : X^(5/8 : ℝ) ≤ S := Real.rpow_le_rpow (zero_le_one.trans hX) hXx (by norm_num)
  have hQS : Q*S = U := by
    dsimp [Q,S,U]; rw [←Real.rpow_add hx0]; norm_num
  have hBudget := (log_window_scale hX hXx hqx).1
  have ⟨hQ,hWindow⟩ := sqrt_q_budget hX hXx hq hγ
  let W := 1+Real.sqrt (1+4*|γ| * X)+Real.log (heightCut X)
  have hT : 1 ≤ heightCut X := by dsimp [heightCut]; exact one_le_pow₀ (by linarith)
  have hW : 0 ≤ W := by dsimp [W]; linarith only [Real.sqrt_nonneg (1+4*|γ| * X),Real.log_nonneg hT]
  have hBL : 0 ≤ logBudget q X := by
    dsimp [logBudget]; linarith only [logHeight_ge_one q (heightCut X)]
  have hmain : Real.sqrt q*(C*X^(5/8 : ℝ)*logBudget q X*W) ≤ 170*C*U*L^2 := by
    calc
      _ = C*(X^(5/8 : ℝ)*logBudget q X)*(Real.sqrt q*W) := by ring
      _ ≤ C*(S*(10*L))*(17*L*Q) := mul_le_mul
        (mul_le_mul_of_nonneg_left (mul_le_mul hXS hBudget hBL (Real.rpow_nonneg hx0.le _)) hC)
        hWindow (mul_nonneg (Real.sqrt_nonneg _) hW)
        (mul_nonneg hC (mul_nonneg (Real.rpow_nonneg hx0.le _) (by positivity)))
      _ = _ := by rw [←hQS]; ring
  have hQS' : Real.sqrt q*Real.sqrt x ≤ U :=
    (mul_le_mul hQ hS (Real.sqrt_nonneg _) (Real.rpow_nonneg hx0.le _)).trans_eq hQS
  have hU0 : 0 ≤ U := Real.rpow_nonneg hx0.le _
  have hpsi : Real.sqrt q*(2*Real.sqrt x*Real.log x) ≤ 2*U*L^2 := by
    have sl := mul_le_mul hQS' ((log_le_scale hx).trans hLL) (Real.log_nonneg hx) hU0
    linarith only [show 2*(Real.sqrt q*Real.sqrt x*Real.log x) ≤ 2*(U*L^2) by linarith only [sl],
      show Real.sqrt q*(2*Real.sqrt x*Real.log x) = 2*(Real.sqrt q*Real.sqrt x*Real.log x) by ring,
      show 2*(U*L^2) = 2*U*L^2 by ring]
  have hg : x*|γ| ≤ 8*Real.sqrt x := by
    nlinarith only [(hγ.trans (mul_le_mul_of_nonneg_left hBase (by norm_num : (0 : ℝ) ≤ 8))),
      mul_le_mul_of_nonneg_right hqpos (mul_nonneg (abs_nonneg γ) hx0.le)]
  have herr : Real.sqrt q*(x*|γ|) ≤ 8*U*L^2 := by
    have A := mul_le_mul_of_nonneg_left hg (Real.sqrt_nonneg q)
    have B := mul_le_mul_of_nonneg_left hL2 hU0
    nlinarith only [A,B,hQS']
  have hqU : Real.sqrt q ≤ U := (le_mul_of_one_le_right (Real.sqrt_nonneg _) (by simpa using Real.sqrt_le_sqrt hx : 1 ≤ Real.sqrt x)).trans hQS'
  have hqlog := mul_le_mul hqU (hlogq.trans hLL) (Real.log_nonneg hqpos) hU0
  change Real.sqrt q*(2*Real.sqrt x*Real.log x + C*X^(5/8 : ℝ)*logBudget q X*W+x*|γ|+Real.log q) ≤ (12+170*C)*U*L^2
  nlinarith only [hmain,hpsi,herr,hqlog,mul_nonneg hU0 (sq_nonneg L)]

end GoldbachTwistedMellin
end
end

section
open Finset Complex Real Goldbach GoldbachGRHWindow DeepThreeQuarters
noncomputable section
namespace GoldbachTwistedMellin

theorem rational_phase {q : ℕ} [NeZero q] (a k : ℕ) (β : ℝ) :
    phase (2*Real.pi*β) k*ZMod.stdAddChar ((a:ZMod q)*(k:ZMod q)) =
      geometricPhase ((k:ℝ)*((a:ℝ)/q+β)) := by
  have hc (m : ℕ) : ZMod.stdAddChar ((m:ℕ):ZMod q) = Complex.exp (2*(Real.pi:ℂ)*I*(m:ℂ)/(q:ℂ)) := by
    simpa only [Int.cast_natCast] using ZMod.stdAddChar_coe (N := q) (m:ℤ)
  rw [← Nat.cast_mul,hc,phase,geometricPhase,←Complex.exp_add]
  congr 1
  push_cast
  ring

theorem primeError_prefix_eq {q : ℕ} [NeZero q] (a n : ℕ) (ha : a.Coprime q) (β : ℝ) :
    (∑ k ∈ Finset.Ioc 0 n, primeError (a:ZMod q) (2*Real.pi*β) k) =
        weightedSum n primeWeight ((a:ℝ)/q+β) - rationalModel n q β := by
  rw [sum_primeError]
  have hI : Finset.Ioc 0 n = Finset.Icc 1 n := by ext k; simp [Nat.lt_iff_add_one_le]
  have hR : range (n+1) = insert 0 (Finset.Ioc 0 n) := by
    ext k; simp only [mem_range,mem_insert,mem_Ioc]; omega
  apply congrArg₂ (fun x y : ℂ => x-y)
  · rw [weightedSum,hR,Finset.sum_insert (by simp)]
    simp only [primeWeight,Nat.not_prime_zero,ite_false,ofReal_zero,zero_mul,zero_add]
    apply sum_congr rfl
    intro k _
    rw [mul_assoc,rational_phase]
    rfl
  · rw [rationalModel,additiveModel_eq_moebius _ ((ZMod.isUnit_iff_coprime ..).mpr ha),mul_comm,hI]
    apply congrArg (fun z : ℂ => (ArithmeticFunction.moebius q:ℂ)/(q.totient:ℂ)*z)
    apply sum_congr rfl
    intro k _
    unfold phase geometricPhase
    congr 1
    push_cast
    ring

theorem angular_range {n q : ℕ} {β : ℝ} (hn : 64 ≤ n) (hq : 1 ≤ q)
    (hβ : |β| ≤ (n:ℝ)^(3/10 : ℝ)/((q:ℝ)*(n:ℝ))) :
    |2*Real.pi*β| ≤ 1 ∧ (q:ℝ)*|2*Real.pi*β| * (n:ℝ) ≤ 8*(n:ℝ)^(3/10 : ℝ) ∧
      |2*Real.pi*β|^2*(n:ℝ) ≤ 64 := by
  have hnR : (64:ℝ) ≤ n := by exact_mod_cast hn
  have hqR : (1:ℝ) ≤ q := by exact_mod_cast hq
  have hn₀ : 0 ≤ (n:ℝ) := by positivity
  have hDen : 0 < (q:ℝ)*(n:ℝ) := mul_pos (by linarith) (by linarith)
  have hs : (8:ℝ) ≤ Real.sqrt n := by
    calc
      _ = Real.sqrt 64 := by norm_num
      _ ≤ _ := Real.sqrt_le_sqrt hnR
  have hBase : (n:ℝ)^(3/10 : ℝ) ≤ Real.sqrt n := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hWidth : 8*(n:ℝ)^(3/10 : ℝ) ≤ (q:ℝ)*(n:ℝ) := calc
    _ ≤ 8*Real.sqrt n := mul_le_mul_of_nonneg_left hBase (by norm_num)
    _ ≤ Real.sqrt n * Real.sqrt n := mul_le_mul_of_nonneg_right hs (Real.sqrt_nonneg _)
    _ = n := by rw [← sq, Real.sq_sqrt hn₀]
    _ ≤ _ := le_mul_of_one_le_left hn₀ hqR
  have ht := (le_div_iff₀ hDen).mp hβ
  have hγ : (q:ℝ)*|2*Real.pi*β| * (n:ℝ) ≤ 8*(n:ℝ)^(3/10 : ℝ) := calc
    _ = (2*Real.pi) * (|β| * ((q:ℝ)*(n:ℝ))) := by
      rw [abs_mul, abs_of_pos (by positivity : 0 < 2*Real.pi)]
      ring
    _ ≤ (2*Real.pi)*(n:ℝ)^(3/10 : ℝ) := mul_le_mul_of_nonneg_left ht (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith [Real.pi_lt_four]) (by positivity)
  refine ⟨(mul_le_mul_iff_of_pos_right hDen).mp ?_,hγ,?_⟩
  · calc
      _ = (q:ℝ) * |2*Real.pi*β| * (n:ℝ) := by ring
      _ ≤ 8*(n:ℝ)^(3/10 : ℝ) := hγ
      _ ≤ 1*((q:ℝ)*(n:ℝ)) := by simpa only [one_mul] using hWidth
  · have hmul : |2*Real.pi*β| * (n:ℝ) ≤ 8*Real.sqrt n := calc
      _ ≤ (q:ℝ) * |2*Real.pi*β| * (n:ℝ) := mul_le_mul_of_nonneg_right
        (le_mul_of_one_le_left (abs_nonneg _) hqR) hn₀
      _ ≤ 8*(n:ℝ)^(3/10 : ℝ) := hγ
      _ ≤ _ := mul_le_mul_of_nonneg_left hBase (by norm_num)
    have hs₀ : 0 < Real.sqrt n := by linarith
    have hm : |2*Real.pi*β| * Real.sqrt n ≤ 8 := by
      apply (mul_le_mul_iff_of_pos_right hs₀).mp
      rw [mul_assoc, ← sq, Real.sq_sqrt hn₀]
      exact hmul
    have hSquare := pow_le_pow_left₀ (by positivity : 0 ≤ |2*Real.pi*β| * Real.sqrt n) hm 2
    simpa only [mul_pow, Real.sq_sqrt hn₀, show (8:ℝ)^2 = 64 by norm_num] using hSquare

theorem dyadic_count_le {n : ℕ} (hn : 4 ≤ n) : (Nat.log 2 (n-2):ℝ)+1 ≤ 3*logScale n := by
  have hn' : 1 ≤ (n:ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
  have hpos : 0 < ((n-2:ℕ):ℝ) := by exact_mod_cast (show 0 < n-2 by omega)
  have hle : ((n-2:ℕ):ℝ) ≤ n := by exact_mod_cast Nat.sub_le n 2
  have hlog2 : (1/2:ℝ) ≤ Real.log 2 := by
    have := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
    linarith
  have h := Real.natLog_le_logb (n-2) 2
  rw [Real.logb, Nat.cast_ofNat,le_div_iff₀ (by positivity)] at h
  have h' := mul_le_mul_of_nonneg_left hlog2 (Nat.cast_nonneg (Nat.log 2 (n-2)) (α := ℝ))
  linarith only [h,h',Real.log_le_log hpos hle,log_le_scale hn',logScale_one hn']

end GoldbachTwistedMellin
end
end

section
open Finset Complex GoldbachGRHWindow
open scoped ComplexConjugate
noncomputable section
namespace GoldbachTwistedMellin
variable {q : ℕ} [NeZero q]

/-- Fourier coefficient of the additive phase on the group of units. -/
noncomputable def additiveWeight (a : ZMod q) (χ : DirichletCharacter ℂ q) : ℂ :=
  conj (∑ r : ZMod q, conj (ZMod.stdAddChar (a*r))*χ r) / (q.totient:ℂ)

theorem weight_expansion (a : ZMod q) (χ : DirichletCharacter ℂ q) :
    additiveWeight a χ = (∑ r : ZMod q, ZMod.stdAddChar (a*r)*conj (χ r))/(q.totient:ℂ) := by
  simp [additiveWeight,map_sum]

private theorem units_filter (F : ZMod q → ℂ) :
    (∑ r : ZMod q, if IsUnit r then F r else 0) = ∑ u : (ZMod q)ˣ, F u := by
  classical
  rw [← Finset.sum_filter]
  have hs : (univ : Finset (ZMod q)).filter IsUnit = (univ : Finset (ZMod q)ˣ).map ⟨(↑), Units.val_injective⟩ := by
    ext r
    simp [IsUnit]
  rw [hs, Finset.sum_map]
  rfl

theorem additiveWeight_one (a : ZMod q) : additiveWeight a 1 = additiveModel q a := by
  classical
  rw [weight_expansion,additiveModel]
  congr 1
  rw [← units_filter (fun r : ZMod q => ZMod.stdAddChar (a*r))]
  refine sum_congr rfl fun r _ => ?_
  by_cases hr : IsUnit r
  · simp [MulChar.one_apply,hr]
  · simp [MulChar.map_nonunit _ hr,hr]

theorem additiveWeight_inversion (a s : ZMod q) :
    (∑ χ : DirichletCharacter ℂ q, additiveWeight a χ * χ s) =
      (if IsUnit s then ZMod.stdAddChar (a*s) else 0) := by
  classical
  have orth (r : ZMod q) : (∑ χ : DirichletCharacter ℂ q, conj (χ r)*χ s) =
      if r=s ∧ IsUnit s then (q.totient:ℂ) else 0 := by
    by_cases hr : IsUnit r
    · have inv (χ : DirichletCharacter ℂ q) : conj (χ r) = χ r⁻¹ := by
        have hχr : χ r ≠ 0 := (hr.map χ).ne_zero
        have hi : χ r⁻¹ = (χ r)⁻¹ := by
          calc
            _ = χ r⁻¹ * (χ r * (χ r)⁻¹) := by rw [mul_inv_cancel₀ hχr,mul_one]
            _ = _ := by rw [←mul_assoc,←map_mul,ZMod.inv_mul_of_unit r hr,map_one,one_mul]
        exact (MulChar.star_apply' χ r).trans ((MulChar.inv_apply_eq_inv' χ r).trans hi.symm)
      simp_rw [inv]
      rw [DirichletCharacter.sum_char_inv_mul_char_eq ℂ hr s]
      by_cases h : r=s
      · subst s;simp [hr]
      · simp [h]
    · simp only [MulChar.map_nonunit _ hr,map_zero,zero_mul,sum_const_zero]
      split_ifs with h
      · exact False.elim (hr (h.1.symm ▸ h.2))
      · rfl
  have hφ : (q.totient:ℂ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  calc
    _ = (∑ r : ZMod q, ZMod.stdAddChar (a*r)*(∑ χ : DirichletCharacter ℂ q, conj (χ r)*χ s))/(q.totient:ℂ) := by
      simp_rw [weight_expansion,div_mul_eq_mul_div,Finset.sum_mul,Finset.mul_sum,mul_assoc]
      rw [←Finset.sum_div,Finset.sum_comm]
    _ = _ := by
      simp_rw [orth]
      by_cases hs : IsUnit s
      · simp [hs,mul_ite,hφ]
      · simp [hs]

theorem sum_norm_additiveWeight_le (a : ZMod q) :
    (∑ χ : DirichletCharacter ℂ q, ‖additiveWeight a χ‖) ≤ Real.sqrt q := by
  classical
  let V : Finset (ZMod q) := univ.filter IsUnit
  have hφ : 0 < (q.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  have card : Fintype.card (DirichletCharacter ℂ q) = q.totient := by
    rw [←Nat.card_eq_fintype_card];exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
  have cV : (V.card:ℝ) ≤ q := by
    exact_mod_cast (V.card_le_univ.trans_eq (ZMod.card q))
  have energy : (∑ χ : DirichletCharacter ℂ q, ‖additiveWeight a χ‖^2) = (V.card:ℝ)/(q.totient:ℝ) := by
    simp only [additiveWeight,norm_div,norm_conj,Complex.norm_natCast,div_pow,←Finset.sum_div]
    rw [multiplicative_energy]
    simp only [norm_conj,ZMod.stdAddChar_apply,Circle.norm_coe,one_pow,Finset.sum_const,nsmul_eq_mul,mul_one]
    change (q.totient:ℝ)*(V.card:ℝ)/(q.totient:ℝ)^2 = _
    field_simp
  have raw := sq_sum_le_card_mul_sum_sq (s:=(univ:Finset (DirichletCharacter ℂ q))) (f:=fun χ => ‖additiveWeight a χ‖)
  rw [Finset.card_univ,card,energy] at raw
  have count : (q.totient:ℝ)*((V.card:ℝ)/(q.totient:ℝ)) = V.card := by field_simp
  rw [count] at raw
  exact (Real.le_sqrt (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) (Nat.cast_nonneg q)).mpr (raw.trans cV)
end GoldbachTwistedMellin
end
end

section
open Finset Complex Goldbach GoldbachSmoothing GoldbachGRHWindow
noncomputable section
namespace GoldbachTwistedMellin
variable {q : ℕ} [NeZero q]

/-- Inverting the unit characters leaves exactly the nonunit terms. -/
theorem sum_character_transfer (I : Finset ℕ) (w : ℕ → ℂ) (a : ZMod q) :
    (∑ k ∈ I, w k*ZMod.stdAddChar (a*(k:ZMod q))) =
      (∑ χ : DirichletCharacter ℂ q, additiveWeight a χ*(∑ k ∈ I,w k*χ (k:ZMod q))) +
      ∑ k ∈ I.filter (fun k : ℕ => ¬IsUnit (k:ZMod q)), w k*ZMod.stdAddChar (a*(k:ZMod q)) := by
  classical
  rw [Finset.sum_filter]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm,←Finset.sum_add_distrib]
  refine sum_congr rfl fun k _ => ?_
  have h := congrArg (w k * ·) (additiveWeight_inversion a (k:ZMod q))
  simp only [Finset.mul_sum] at h
  simp_rw [mul_left_comm (additiveWeight a _) (w k)]
  rw [h]
  by_cases hk : IsUnit (k:ZMod q) <;> simp [hk]

theorem signed_dyadic_transfer (r : ZMod q) {a b n : ℕ} {β B : ℝ}
    (hb : b ≤ n) (hn : 1 ≤ n) (ha : 0 < a) (hab : a+1≤b) (hB : 0≤B)
    (Z : DirichletCharacter ℂ q → ℂ)
    (hchr : ∀ χ : DirichletCharacter ℂ q,
      ‖(∑ k ∈ Finset.Ioc a b,twistedCoefficient χ k*phase β k) -
        (principalFlag χ*transform a b β 1 - Z χ)‖ ≤ B) :
    ‖(∑ k ∈ Finset.Ioc a b,primeError r β k) + ∑ χ : DirichletCharacter ℂ q,additiveWeight r χ*Z χ‖ ≤
      Real.sqrt q*(2*Real.sqrt n*Real.log n+B+((b:ℝ)-a)*|β|+Real.log q) := by
  classical
  let I := Finset.Ioc a b
  let w := fun k : ℕ => primeLog k*phase β k
  let S := ∑ k ∈ I,phase β k
  let P := fun χ : DirichletCharacter ℂ q => ∑ k ∈ I,w k*χ (k:ZMod q)
  let e := fun χ : DirichletCharacter ℂ q => P χ - (if χ=1 then S else 0) + Z χ
  let E := 2*Real.sqrt n*Real.log n+B+((b:ℝ)-a)*|β|
  have hnR : 1 ≤ (n:ℝ) := by exact_mod_cast hn
  have habR : (a:ℝ) ≤ b := by exact_mod_cast (show a≤b by omega)
  have hE : 0 ≤ E := by dsimp [E];have := Real.log_nonneg hnR;have := sub_nonneg.mpr habR;positivity
  have hev (χ : DirichletCharacter ℂ q) : ‖e χ‖ ≤ E := by
    let L := ∑ k ∈ I, twistedCoefficient χ k * phase β k
    let M := principalFlag χ * transform a b β 1
    have hm : ‖M-(if χ=1 then S else 0)‖ ≤ ((b:ℝ)-a)*|β| := by
      by_cases h : χ=1
      · simpa [M,S,I,principalFlag,h] using principal_approx ha hab β
      · simpa [M,principalFlag,h] using mul_nonneg (sub_nonneg.mpr habR) (abs_nonneg β)
    have he : e χ = ((P χ-L)+(L-(M-Z χ)))+(M-(if χ=1 then S else 0)) := by dsimp [e];abel
    rw [he]
    exact (norm_add_le ..).trans (add_le_add ((norm_add_le ..).trans
      (add_le_add (prime_removal χ a b n hb hn β) (hchr χ))) hm)
  let D := ∑ k ∈ I.filter (fun k : ℕ => ¬IsUnit (k:ZMod q)), w k*ZMod.stdAddChar (r*(k:ZMod q))
  have hnunit : ‖D‖ ≤ Real.log q := by
    apply (norm_sum_le ..).trans
    simpa [I,w,norm_mul,norm_phase,ZMod.stdAddChar_apply] using primeLog_nonunit_mass_le (q:=q) I
  have hsingle : (∑ χ : DirichletCharacter ℂ q, additiveWeight r χ*(if χ=1 then S else 0)) = S*additiveModel q r := by
    simp [mul_ite,additiveWeight_one,mul_comm]
  have heq : (∑ k ∈ I,primeError r β k) + ∑ χ : DirichletCharacter ℂ q,additiveWeight r χ*Z χ =
      (∑ χ : DirichletCharacter ℂ q, additiveWeight r χ*e χ)+D := by
    dsimp only [I]
    rw [sum_primeError,sum_character_transfer]
    simp only [e,mul_add,mul_sub,Finset.sum_add_distrib,Finset.sum_sub_distrib,hsingle]
    dsimp [I,P,S,D,w]
    abel
  change ‖(∑ k ∈ I,primeError r β k)+_‖ ≤ _
  rw [heq]
  have hsum : ‖∑ χ : DirichletCharacter ℂ q, additiveWeight r χ*e χ‖ ≤ Real.sqrt q*E := by
    apply (norm_sum_le ..).trans
    simp only [norm_mul]
    calc
      _ ≤ ∑ χ : DirichletCharacter ℂ q, ‖additiveWeight r χ‖*E := by
        apply sum_le_sum;intro χ _;exact mul_le_mul_of_nonneg_left (hev χ) (norm_nonneg _)
      _ ≤ _ := by rw [←Finset.sum_mul];exact mul_le_mul_of_nonneg_right (sum_norm_additiveWeight_le r) hE
  have hq : 1 ≤ (q:ℝ) := by exact_mod_cast NeZero.pos q
  have hs : 1 ≤ Real.sqrt q := by simpa using Real.sqrt_le_sqrt hq
  apply (norm_add_le ..).trans
  exact (add_le_add hsum hnunit).trans (by
    change Real.sqrt q*E+Real.log q ≤ Real.sqrt q*(E+Real.log q)
    calc
      _ ≤ Real.sqrt q*E + Real.sqrt q*Real.log q := add_le_add le_rfl (le_mul_of_one_le_left (Real.log_nonneg hq) hs)
      _ = _ := by ring)
end GoldbachTwistedMellin
end
end

section
open Finset
noncomputable section
namespace GoldbachTwistedMellin

/-- The ordered disjoint blocks covering the integers up to m+2 after the base interval. The first at most
three integers are left in the base estimate. -/
def prefixBlocks (m : ℕ) : List (ℕ × ℕ) :=
  if h : m < 2 then [] else (m/2+2,m+2)::prefixBlocks (m/2)
termination_by m
decreasing_by exact Nat.div_lt_self (by omega) (by decide)

theorem prefixBlocks_valid {m : ℕ} {p : ℕ × ℕ} (hp : p ∈ prefixBlocks m) :
    1 ≤ p.1 ∧ p.1+1 ≤ p.2 ∧ p.2+1 ≤ 2*p.1 ∧ p.2 ≤ m+2 := by
  induction m using Nat.strong_induction_on with
  | ind m ih =>
    rw [prefixBlocks] at hp
    split_ifs at hp with h
    · simp at hp
    rcases List.mem_cons.mp hp with h|h
    · subst p;dsimp;omega
    · obtain ⟨a,b,c,e⟩ := ih (m/2) (Nat.div_lt_self (by omega) (by decide)) h
      exact ⟨a,b,c,by omega⟩

/-- Attach a complex correction to each block before estimating the full sum. -/
theorem dyadic_prefix_corrected (f : ℕ → ℂ) (z : ℕ × ℕ → ℂ) (n : ℕ) (hn : 2 ≤ n) (D : ℝ)
    (base : ∀ k : ℕ, k ≤ 3 → ‖∑ j ∈ Finset.Ioc 0 k,f j‖ ≤ D)
    (block : ∀ p ∈ prefixBlocks (n-2), ‖(∑ k ∈ Finset.Ioc p.1 p.2,f k)+z p‖ ≤ D) :
    ‖(∑ k ∈ Finset.Ioc 0 n,f k) + ((prefixBlocks (n-2)).map z).sum‖ ≤ ((Nat.log 2 (n-2):ℝ)+1)*D := by
  have h (m : ℕ) (sub : ∀ p ∈ prefixBlocks m,p ∈ prefixBlocks (n-2)) :
      ‖(∑ k ∈ Finset.Ioc 0 (m+2),f k) + ((prefixBlocks m).map z).sum‖ ≤ ((Nat.log 2 m:ℝ)+1)*D := by
    induction m using Nat.strong_induction_on with
    | ind m ih =>
      by_cases hsmall : m<2
      · rw [prefixBlocks,dite_eq_left hsmall,Nat.log_of_lt hsmall]
        simpa using base (m+2) (by omega)
      · have hpos : 2 ≤ m := by omega
        let p := (m/2+2,m+2)
        have eqs : prefixBlocks m = p::prefixBlocks (m/2) := by rw [prefixBlocks,dite_eq_right hsmall]
        have hsm := ih (m/2) (Nat.div_lt_self (by omega) (by decide)) (fun i hi => sub i (by rw [eqs];exact List.mem_cons_of_mem _ hi))
        have hlg := block p (sub p (by rw [eqs];exact List.mem_cons_self))
        rw [eqs,List.map_cons,List.sum_cons,←Finset.sum_Ioc_consecutive f (Nat.zero_le (m/2+2)) (by omega : m/2+2 ≤ m+2)]
        have a : ∀ x y u v : ℂ, x+y+(u+v) = (x+v)+(y+u) := by intros;abel
        rw [a]
        exact (norm_add_le ..).trans ((add_le_add hsm hlg).trans_eq (by
          rw [Nat.log_of_one_lt_of_le (by decide : 1<2) hpos];push_cast;ring))
  simpa [Nat.sub_add_cancel hn] using h (n-2) (fun _ hp => hp)
end GoldbachTwistedMellin
end
end

section
open Finset Complex Goldbach GoldbachSmoothing GoldbachGRHWindow DeepThreeQuarters
noncomputable section
namespace GoldbachTwistedMellin

/-- The extra logarithm in the unconditional contour bound costs one extra
logarithm on the rational arc, uniformly in its denominator and numerator. -/
theorem signed_block_budget {n l r q : ℕ} [NeZero q] (v : ZMod q) {C γ : ℝ}
    (hn : 1 ≤ n) (hl : 1 ≤ l) (hlr : l+1≤r) (hrn : r≤n)
    (hC : 0≤C) (hqs : (q:ℝ)≤(n:ℝ)^(3/10 : ℝ))
    (hγq : (q:ℝ)*|γ| *(n:ℝ) ≤ 8*(n:ℝ)^(3/10 : ℝ))
    (Z : DirichletCharacter ℂ q → ℂ)
    (model : ∀ χ : DirichletCharacter ℂ q,
      ‖(∑ k ∈ Finset.Ioc l r,twistedCoefficient χ k*phase γ k) -
        (principalFlag χ*transform l r γ 1 - Z χ)‖ ≤
      C*(l:ℝ)^(5/8 : ℝ)*(logBudget q l)^2*(1+Real.sqrt (1+4*|γ| *l)+Real.log (heightCut l))) :
    ‖(∑ k ∈ Finset.Ioc l r,primeError v γ k) + ∑ χ : DirichletCharacter ℂ q,additiveWeight v χ*Z χ‖ ≤
      (12+1700*C)*(n:ℝ)^(31/40 : ℝ)*logScale n^3 := by
  let L := logScale n
  let S := (n:ℝ)^(31/40 : ℝ)
  let W := 1+Real.sqrt (1+4*|γ| *l)+Real.log (heightCut l)
  have hx : 1 ≤ (l:ℝ) := by exact_mod_cast hl
  have hnR : 1 ≤ (n:ℝ) := by exact_mod_cast hn
  have hxn : (l:ℝ) ≤ n := by exact_mod_cast (show l≤n by omega)
  have hL : 1 ≤ L := logScale_one hnR
  have hp : 0 ≤ (l:ℝ)^(5/8 : ℝ) := Real.rpow_nonneg (by positivity) _
  have hT : 1 ≤ heightCut l := by linarith [heightCut_ge hx]
  have hW : 0 ≤ W := by dsimp [W];linarith only [Real.sqrt_nonneg (1+4*|γ| *l),Real.log_nonneg hT]
  have hbudget : 0≤logBudget q l := by dsimp [logBudget];linarith only [logHeight_ge_one q (heightCut l)]
  have hqn : (q:ℝ) ≤ n := hqs.trans
    ((Real.rpow_le_rpow_of_exponent_le hnR (show (3/10 : ℝ) ≤ 1 by norm_num)).trans_eq (Real.rpow_one _))
  have hB := (log_window_scale hx hxn hqn).1
  let C' := 10*C*L
  have hC' : 0 ≤ C' := by dsimp [C'];positivity
  let R := C'*(l:ℝ)^(5/8 : ℝ)*logBudget q l*W
  have hR : 0 ≤ R := by dsimp [R];positivity
  have hres (χ : DirichletCharacter ℂ q) := (model χ).trans (show _ ≤ R from by
    calc
      C*(l:ℝ)^(5/8 : ℝ)*(logBudget q l)^2*W =
        (C*(l:ℝ)^(5/8 : ℝ)*logBudget q l*W)*logBudget q l := by ring
      _ ≤ (C*(l:ℝ)^(5/8 : ℝ)*logBudget q l*W)*(10*L) := mul_le_mul_of_nonneg_left hB (by positivity)
      _ = R := by dsimp [R,C'];ring)
  have m := signed_dyadic_transfer v hrn hn hl hlr hR Z hres
  have raw := block_budget hx hxn hC' hqs hγq
  have he := mul_le_mul_of_nonneg_right (by linarith [show (r:ℝ)≤n by exact_mod_cast hrn, Nat.cast_nonneg (α:=ℝ) l] : (r:ℝ)-l ≤ n) (abs_nonneg γ)
  have comp : Real.sqrt q*(2*Real.sqrt n*Real.log n+R+((r:ℝ)-l)*|γ|+Real.log q) ≤
        (12+170*C')*S*L^2 := by
    apply le_trans _ raw
    apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg q)
    dsimp only [R,W];linarith only [he]
  have hS : 0≤S := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have mul := mul_le_mul_of_nonneg_right hL (mul_nonneg hS (sq_nonneg L))
  exact (m.trans comp).trans (by dsimp only [C',S,L] at *;nlinarith only [mul])
end GoldbachTwistedMellin
end
end

section
open Set Finset Complex Goldbach DirichletCharacter
noncomputable section
namespace GoldbachTwistedMellin

private def zeroBin (t : ℝ) : Bool × ℕ := (decide (0≤t),⌊|t|⌋₊)
private def binCenter (p : Bool × ℕ) : ℝ := if p.1 then (p.2:ℝ) else -(p.2:ℝ)

private theorem bin_properties (t : ℝ) :
    ((zeroBin t).2:ℝ) ≤ |t| ∧ |t-binCenter (zeroBin t)| ≤ 1 := by
  have h := Nat.floor_le (abs_nonneg t)
  have h' := Nat.lt_floor_add_one |t|
  refine ⟨h,?_⟩
  by_cases ht : 0≤t
  · simp only [abs_of_nonneg ht] at h h'
    simp [binCenter,zeroBin,ht,abs_of_nonneg ht,abs_le];constructor <;> linarith
  · have hn := le_of_not_ge ht
    simp only [abs_of_nonpos hn] at h h'
    simp [binCenter,zeroBin,ht,abs_of_nonpos hn,abs_le];constructor <;> linarith

private theorem binCenter_abs (p : Bool × ℕ) : |binCenter p|=(p.2:ℝ) := by
  dsimp [binCenter];split <;> simp

private theorem reciprocalSquare_sum_Ico (J M : ℕ) (hJ : 2 ≤ J) :
    (∑ j ∈ Finset.Ico J M, 1 / (j : ℝ)^2) ≤ 1 / ((J : ℝ)-1) := by
  rw [Finset.sum_Ico_eq_sum_range]
  let f := fun j : ℕ => 1 / ((J : ℝ) + (j : ℝ) - 1)
  have hJ' : (2 : ℝ) ≤ J := by exact_mod_cast hJ
  calc
    _ ≤ ∑ j ∈ Finset.range (M-J), (f j - f (j+1)) := by
      apply Finset.sum_le_sum
      intro j _
      let x : ℝ := (J : ℝ) + (j : ℝ)
      have hx : 1 < x := by dsimp [x]; linarith [Nat.cast_nonneg (α := ℝ) j]
      have hf : f (j+1) = 1/x := by
        dsimp [f,x]
        push_cast
        congr 1
        ring
      rw [Nat.cast_add, hf]
      change 1/x^2 ≤ 1/(x-1) - 1/x
      rw [show 1/(x-1) - 1/x = 1/(x*(x-1)) by
        field_simp [show x ≠ 0 by linarith, show x-1 ≠ 0 by linarith]
        ring]
      apply div_le_div_of_nonneg_left zero_le_one (by positivity : 0 < x*(x-1))
      nlinarith
    _ = f 0 - f (M-J) := by
      calc
        _ = -(∑ j ∈ range (M-J), (f (j+1) - f j)) := by
          rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro j _
          ring
        _ = _ := by rw [Finset.sum_range_sub, neg_sub]
    _ ≤ _ := by
      have h : 0 ≤ f (M-J) :=
        one_div_nonneg.mpr (by linarith [Nat.cast_nonneg (α := ℝ) (M-J)])
      simpa [f] using sub_le_self (f 0) h

/-- Bound the full high-ordinate tail by summing the quadratic decay over
unit-height intervals with their multiplicities. -/
theorem high_ordinate_residues :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (Z : Finset ℂ)
      (a b X β T B : ℝ), 1 ≤ X → X ≤ a → a+1 ≤ b → b+1 ≤ 2*X →
      |β| ≤ 1 → |β|^2*X ≤ 64 → 4 ≤ T → T ≤ B →
      (∀ z ∈ Z, 1/2 ≤ z.re ∧ z.re ≤ 1 ∧ T ≤ |z.im| ∧ |z.im| ≤ B) →
      (∑ z ∈ Z, (analyticOrderNatAt (regularizedL χ) z : ℝ) * ‖transform a b β z‖) ≤
        C * X^2 * logHeight q B / T := by
  classical
  obtain ⟨K,hK,slice⟩ := unconditional_right_slice_count
  refine ⟨2400*K,by positivity,?_⟩
  intro q _ χ Z a b X β T B hX ha hab hb hβ hβX hT hTB geom
  have hB : 0 ≤ B := by linarith
  let M := ⌊B⌋₊
  let J := ⌊T⌋₊
  let y := fun z : ℂ => zeroBin z.im
  let mult := fun z : ℂ => (analyticOrderNatAt (regularizedL χ) z : ℝ)
  let w := fun j : ℕ => if J ≤ j then 1/(j:ℝ)^2 else 0
  let D := 600*X^2
  have hJ : 2 ≤ J := (Nat.le_floor_iff (by linarith : 0 ≤ T)).mpr (by push_cast; linarith)
  have hTpos : 0 < T := by linarith
  have hJhalf : T/2 ≤ (J:ℝ)-1 := by linarith only [Nat.lt_floor_add_one T,hT]
  have hgrid (z : ℂ) (hz : z ∈ Z) : y z ∈ grid (M+1) :=
    Finset.mem_product.mpr ⟨mem_univ _,mem_range.mpr (Nat.lt_succ_of_le (Nat.floor_mono (geom z hz).2.2.2))⟩
  have hper (p : Bool × ℕ) (hp : p ∈ grid (M+1)) :
      (∑ z ∈ Z.filter (fun z => y z = p), mult z * ‖transform a b β z‖) ≤
        (K * logHeight q B * D) * w p.2 := by
    let Y := Z.filter (fun z => y z = p)
    have hweight (z : ℂ) (hz : z ∈ Y) : ‖transform a b β z‖ ≤ D * w p.2 := by
      obtain ⟨hzZ,he⟩ := mem_filter.mp hz
      obtain ⟨hl,hr,ht,_⟩ := geom z hzZ
      have hpj : J ≤ p.2 := by
        rw [← he]
        exact Nat.floor_mono ht
      have hpos : 0 < (p.2 : ℝ) := by exact_mod_cast (show 0 < p.2 by omega)
      have hle : (p.2 : ℝ) ≤ |z.im| := by
        simpa only [← he,y] using (bin_properties z.im).1
      have h := norm_transform_major_tail hX ha hab hb hβ hβX z (by linarith) hr (hpos.trans_le hle)
      rw [show w p.2 = 1/(p.2:ℝ)^2 from ite_eq_left hpj]
      rw [mul_one_div]
      exact h.trans (div_le_div_of_nonneg_left (by positivity)
        (sq_pos_of_pos hpos) (pow_le_pow_left₀ hpos.le hle 2))
    have hc := slice q χ (binCenter p) Y (fun z hz => by
      obtain ⟨hzZ,he⟩ := mem_filter.mp hz
      obtain ⟨hl,hr,_,_⟩ := geom z hzZ
      exact ⟨hl,by linarith,by simpa only [← he,y] using (bin_properties z.im).2⟩)
    have hpM : p.2 ≤ M := Nat.lt_succ_iff.mp (mem_range.mp (mem_product.mp hp).2)
    have hlog : logHeight q (binCenter p) ≤ logHeight q B := by
      apply logHeight_mono_abs
      rw [binCenter_abs,abs_of_nonneg hB]
      exact (Nat.cast_le.mpr hpM).trans (Nat.floor_le hB)
    have hsum : (∑ z ∈ Y, mult z) ≤ K*logHeight q B :=
      hc.trans (mul_le_mul_of_nonneg_left hlog hK.le)
    calc
      _ ≤ ∑ z ∈ Y, mult z * (D*w p.2) :=
        sum_le_sum fun z hz => mul_le_mul_of_nonneg_left (hweight z hz) (by dsimp [mult]; positivity)
      _ = (∑ z ∈ Y, mult z) * (D*w p.2) := (Finset.sum_mul ..).symm
      _ ≤ (K*logHeight q B) * (D*w p.2) :=
        mul_le_mul_of_nonneg_right hsum (by dsimp [D,w]; split_ifs <;> positivity)
      _ = _ := by ring
  have hweightSum : (∑ j ∈ range (M+1), w j) ≤ 2/T := by
    rw [← Finset.sum_filter (fun j => J ≤ j)]
    have hEq : ((range (M+1)).filter (fun j => J ≤ j)) = Finset.Ico J (M+1) := by
      ext j
      simp [and_comm]
    rw [hEq]
    exact (reciprocalSquare_sum_Ico J (M+1) hJ).trans (calc
      _ ≤ 1/(T/2) := div_le_div_of_nonneg_left zero_le_one (by positivity) hJhalf
      _ = 2/T := by ring)
  have hsum := sum_le_sum hper
  rw [Finset.sum_fiberwise_of_maps_to hgrid, ← mul_sum, sum_grid_weight] at hsum
  refine hsum.trans ((mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hweightSum (by norm_num : (0:ℝ) ≤ 2))
    (mul_nonneg (mul_nonneg hK.le (zero_le_one.trans (logHeight_ge_one q B))) (by dsimp [D]; positivity))).trans_eq ?_)
  dsimp [D]
  ring

/-- Sum the Mellin transform over a narrow real-part strip, counting analytic
multiplicities. Uniform local Jensen bounds apply to every height bin. -/
theorem near_line_residues :
    ∃ C : ℝ, 0<C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (Z : Finset ℂ)
    (a b X β B V : ℝ), 1≤X → X≤a → a+1≤b → b+1≤2*X →
    2≤B → V≤1 → (∀ z∈Z, 1/2≤z.re ∧ z.re≤V ∧ |z.im|≤B) →
    (∑ z ∈ Z, (analyticOrderNatAt (regularizedL χ) z:ℝ)*‖transform a b β z‖) ≤
      C*X^V*logHeight q B*(1+Real.sqrt (1+4*|β| *X)+Real.log B) := by
  classical
  obtain ⟨K,hK,slice⟩ := unconditional_right_slice_count
  refine ⟨200*K,by positivity,?_⟩
  intro q _ χ Z a b X β B V hX ha hab hb hB hV geom
  let J := ⌈4*|β| *X⌉₊
  let M := ⌊B⌋₊
  let y := fun z : ℂ => zeroBin z.im
  let mult := fun z : ℂ => (analyticOrderNatAt (regularizedL χ) z:ℝ)
  let W := 1+Real.sqrt (1+4*|β| *X)+Real.log B
  have hJ : 4*|β| * X ≤ (J:ℝ) := Nat.le_ceil _
  have hJ' : (J:ℝ) < 4*|β| *X+1 := Nat.ceil_lt_add_one (by positivity)
  have hM : (M:ℝ) ≤ B := Nat.floor_le (by linarith)
  have hgrid (z : ℂ) (hz : z∈Z) : y z ∈ grid (M+1) := by
    apply Finset.mem_product.mpr
    exact ⟨mem_univ _,mem_range.mpr (Nat.lt_succ_of_le (Nat.floor_mono (geom z hz).2.2))⟩
  have per (p : Bool×ℕ) (hp : p∈grid (M+1)) :
      (∑ z ∈ Z.filter (fun z => y z=p), mult z*‖transform a b β z‖) ≤
        (K*logHeight q B*X^V)*profile J p.2 := by
    let Y := Z.filter (fun z => y z=p)
    have hwlt (z : ℂ) (hz : z∈Y) : ‖transform a b β z‖ ≤ X^V*profile J p.2 := by
      obtain ⟨hzZ,he⟩ := mem_filter.mp hz
      obtain ⟨hl,hr,_⟩ := geom z hzZ
      have h := window_bin_bound hX ha hab hb (by linarith : 0≤z.re) (hr.trans hV) hr (bin_properties z.im).1 hJ
      have heq : line z.re z.im = z := by apply Complex.ext <;> simp
      rw [heq] at h
      simpa only [←he,y] using h
    have hcount := slice q χ (binCenter p) Y (fun z hz => by
      obtain ⟨hzZ,he⟩ := mem_filter.mp hz
      obtain ⟨hl,hr,_⟩ := geom z hzZ
      exact ⟨hl,by linarith,by simpa only [←he,y] using (bin_properties z.im).2⟩)
    have hj : p.2 ≤ M := Nat.lt_succ_iff.mp (mem_range.mp (mem_product.mp hp).2)
    have hlog : logHeight q (binCenter p) ≤ logHeight q B := by
      apply logHeight_mono_abs;rw [binCenter_abs,abs_of_nonneg (by linarith : 0≤B)]
      exact (show (p.2:ℝ) ≤ M by exact_mod_cast hj).trans hM
    have hm : (∑ z ∈ Y,mult z) ≤ K*logHeight q B := hcount.trans (mul_le_mul_of_nonneg_left hlog hK.le)
    calc
      _ ≤ ∑ z ∈ Y,mult z*(X^V*profile J p.2) := sum_le_sum fun z hz =>
        mul_le_mul_of_nonneg_left (hwlt z hz) (Nat.cast_nonneg _)
      _ = (∑ z ∈ Y,mult z)*(X^V*profile J p.2) := (Finset.sum_mul ..).symm
      _ ≤ (K*logHeight q B)*(X^V*profile J p.2) :=
        mul_le_mul_of_nonneg_right hm (mul_nonneg (Real.rpow_nonneg (by linarith) _) (profile_nonneg ..))
      _ = _ := by ring
  have hlogB := Real.log_nonneg (by linarith : 1≤B)
  have hln : Real.log (M+1:ℝ) ≤ 1+Real.log B := by
    have hy := Real.log_le_log (by positivity : 0<(M:ℝ)+1) (by linarith : (M:ℝ)+1 ≤ 2*B)
    rw [Real.log_mul (by norm_num : (2:ℝ)≠0) (by linarith)] at hy
    linarith only [hy,Real.log_le_sub_one_of_pos (by norm_num : 0<(2:ℝ))]
  have hsqrt : Real.sqrt J ≤ Real.sqrt (1+4*|β| *X) := Real.sqrt_le_sqrt (by linarith)
  have hprof : (∑ j ∈ range (M+1),profile J j) ≤ 100*W := by
    apply (profile_sum J M).trans;dsimp [W]
    nlinarith only [hln,hlogB,hsqrt,Real.sqrt_nonneg (1+4*|β| *X),
      mul_le_mul_of_nonneg_right Real.pi_lt_four.le (Real.sqrt_nonneg (J:ℝ))]
  have tot := sum_le_sum per
  rw [Finset.sum_fiberwise_of_maps_to hgrid,←Finset.mul_sum,sum_grid_weight] at tot
  have hL : 0 ≤ logHeight q B := zero_le_one.trans (logHeight_ge_one q B)
  exact (tot.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hprof (by norm_num : (0:ℝ)≤2))
    (by positivity))).trans_eq (by dsimp [W,mult];ring)
end GoldbachTwistedMellin
end
end

section
open Set Finset Complex Goldbach DirichletCharacter
noncomputable section
namespace GoldbachTwistedMellin

theorem high_edge_residues :
    ∃ C : ℝ, 0<C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (Z : Finset ℂ)
    (a b X β B : ℝ), 1≤X → X≤a → a+1≤b → b+1≤2*X → |β|≤1 → 2≤B → X^4≤B^2 →
    (∀ z∈Z, 1/2≤z.re ∧ z.re≤2 ∧ B≤|z.im| ∧ |z.im|≤B+1) →
    (∑ z ∈ Z,(analyticOrderNatAt (regularizedL χ) z:ℝ)*‖transform a b β z‖) ≤ C*logHeight q B := by
  classical
  obtain ⟨K,hK,slice⟩ := unconditional_right_slice_count
  refine ⟨192*K,by positivity,?_⟩
  intro q _ χ Z a b X β B hX ha hab hb hβ hB hBX geom
  let m := fun z : ℂ => (analyticOrderNatAt (regularizedL χ) z:ℝ)
  let pos := fun z : ℂ => 0≤z.im
  have top := slice q χ B (Z.filter pos) (fun z hz => by
    obtain ⟨hzZ,hp⟩ := mem_filter.mp hz
    obtain ⟨hr,hr',hi,hi'⟩ := geom z hzZ
    rw [abs_of_nonneg hp] at hi hi'
    exact ⟨hr,hr',abs_le.mpr ⟨by linarith,by linarith⟩⟩)
  have bot := slice q χ (-B) (Z.filter fun z => ¬pos z) (fun z hz => by
    obtain ⟨hzZ,hn⟩ := mem_filter.mp hz
    obtain ⟨hr,hr',hi,hi'⟩ := geom z hzZ
    rw [abs_of_nonpos (le_of_not_ge hn)] at hi hi'
    exact ⟨hr,hr',abs_le.mpr ⟨by linarith,by linarith⟩⟩)
  rw [show logHeight q (-B)=logHeight q B by simp [logHeight]] at bot
  have cnt : (∑ z ∈ Z,m z) ≤ 2*K*logHeight q B := by
    rw [←Finset.sum_filter_add_sum_filter_not Z pos m]
    exact (add_le_add top bot).trans_eq (by ring)
  have hwin (z : ℂ) (hz : z∈Z) : ‖transform a b β z‖ ≤ 96 := by
    obtain ⟨hr,hr',hi,_⟩ := geom z hz
    apply (norm_transform_tail hX ha hab hb hβ z (by linarith) hr' (by linarith)).trans
    apply (div_le_iff₀ (sq_pos_of_pos (by linarith : 0 < |z.im|))).mpr
    exact mul_le_mul_of_nonneg_left (hBX.trans (pow_le_pow_left₀ (by linarith) hi _)) (by norm_num)
  calc
    _ ≤ ∑ z ∈ Z,m z*96 := sum_le_sum fun z hz => mul_le_mul_of_nonneg_left (hwin z hz) (Nat.cast_nonneg _)
    _ = (∑ z ∈ Z,m z)*96 := (Finset.sum_mul ..).symm
    _ ≤ (2*K*logHeight q B)*96 := mul_le_mul_of_nonneg_right cnt (by norm_num)
    _ = _ := by ring
end GoldbachTwistedMellin
end
end

section
open Set Finset Complex Goldbach DirichletCharacter GoldbachSmoothing
noncomputable section
namespace GoldbachTwistedMellin

/-- The zeros with real part greater than 5/8 and ordinate of modulus at most B. -/
noncomputable def exceptionalZeros {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (B : ℝ) : Finset ℂ :=
  (boxZeros χ (5/8) 2 (-B) B).filter (fun z => 5/8 < z.re)

theorem mem_exceptionalZeros {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (B : ℝ) (z : ℂ) :
    z ∈ exceptionalZeros χ B ↔ 5/8 < z.re ∧ |z.im| ≤ B ∧ regularizedL χ z = 0 := by
  classical
  rw [exceptionalZeros,mem_filter,mem_boxZeros,mem_reProdIm]
  constructor
  · rintro ⟨⟨⟨_,hi⟩,hz⟩,hl⟩
    exact ⟨hl,abs_le.mpr hi,hz⟩
  · rintro ⟨hl,hi,hz⟩
    have hr : z.re ≤ 2 := by by_contra! h;exact regularizedL_ne_zero_right χ (by linarith) hz
    exact ⟨⟨⟨⟨hl.le,hr⟩,abs_le.mp hi⟩,hz⟩,hl⟩

noncomputable def modelHeight (X : ℝ) : ℝ := 4*X^(3/2 : ℝ)

noncomputable def fixedZeroTerm {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (a b X β : ℝ) : ℂ :=
  ∑ z ∈ exceptionalZeros χ (modelHeight X), (analyticOrderNatAt (regularizedL χ) z:ℂ)*transform a b β z

theorem fixedZeroTerm_changeLevel {m q : ℕ} [NeZero m] [NeZero q] (hmq : m ∣ q)
    (χ : DirichletCharacter ℂ m) (a b X β : ℝ) :
    fixedZeroTerm (changeLevel hmq χ) a b X β = fixedZeroTerm χ a b X β := by
  classical
  let T := modelHeight X
  have hnotOne {k : ℕ} [NeZero k] (ψ : DirichletCharacter ℂ k) {z : ℂ}
      (hz : regularizedL ψ z = 0) : z ≠ 1 := by
    have h := re_lt_one_of_regularizedL_zero ψ hz
    intro he
    simp [he] at h
  have hSet : exceptionalZeros (changeLevel hmq χ) T = exceptionalZeros χ T := by
    ext z
    rw [mem_exceptionalZeros, mem_exceptionalZeros]
    constructor
    · rintro ⟨hre,him,hz⟩
      exact ⟨hre,him,(regularizedL_changeLevel_zero_and_order hmq χ z
        (by linarith) (hnotOne _ hz)).1.mp hz⟩
    · rintro ⟨hre,him,hz⟩
      exact ⟨hre,him,(regularizedL_changeLevel_zero_and_order hmq χ z
        (by linarith) (hnotOne _ hz)).1.mpr hz⟩
  unfold fixedZeroTerm
  change (∑ z ∈ exceptionalZeros (changeLevel hmq χ) T,
    (analyticOrderNatAt (regularizedL (changeLevel hmq χ)) z:ℂ)*transform a b β z) = _
  rw [hSet]
  apply Finset.sum_congr rfl
  intro z hz
  obtain ⟨hre,_,hzero⟩ := (mem_exceptionalZeros χ T z).mp hz
  rw [(regularizedL_changeLevel_zero_and_order hmq χ z (by linarith) (hnotOne χ hzero)).2]

/-- The zero profile of each character is exactly the profile of its inducing
primitive character. The additive Gauss weights still use the arc modulus. -/
theorem fixedZeroTerm_eq_primitive {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (a b X β : ℝ) :
    letI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    fixedZeroTerm χ a b X β = fixedZeroTerm χ.primitiveCharacter a b X β := by
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  calc
    _ = fixedZeroTerm (changeLevel χ.conductor_dvd_level χ.primitiveCharacter) a b X β :=
      congrArg (fun ψ : DirichletCharacter ℂ q => fixedZeroTerm ψ a b X β) χ.changeLevel_primitiveCharacter.symm
    _ = _ := fixedZeroTerm_changeLevel _ _ a b X β

/-- Fix the contour truncation and absorb the zeros of real part at most 5/8
and those above the model height into the error on a dyadic window. -/
theorem fixed_dyadic_model :
    ∃ C : ℝ, 0<C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (a b : ℕ) (X β : ℝ),
      1≤X → X≤(a:ℝ) → (a:ℝ)+1≤b → (b:ℝ)+1≤2*X → |β|≤1 → |β|^2*X ≤ 64 →
      ‖(∑ k ∈ Finset.Ioc a b,twistedCoefficient χ k*phase β k) -
        (principalFlag χ*transform a b β 1 - fixedZeroTerm χ a b X β)‖ ≤
      C*X^(5/8 : ℝ)*(logBudget q X)^2*(1+Real.sqrt (1+4*|β| *X)+Real.log (heightCut X)) := by
  classical
  obtain ⟨C,hC,model⟩ := dyadic_zero_model (d := 1/16) (by norm_num) (by norm_num)
  obtain ⟨K,hK,narrow⟩ := near_line_residues
  obtain ⟨A,hA,high⟩ := high_edge_residues
  obtain ⟨D,hD,tail⟩ := high_ordinate_residues
  refine ⟨C+K+A+D,by positivity,?_⟩
  intro q _ χ a b X β hX ha hab hb hβ hβX
  let B := heightCut X
  let U := modelHeight X
  obtain ⟨T,hT,σ,hσ,e⟩ := model q χ a b X β hX ha hab hb hβ
  let V : ℝ := 5/8
  let Z := exceptionalZeros χ B
  let Z₀ := exceptionalZeros χ U
  let Y := boxZeros χ σ 2 (-T) T
  let F := fun z : ℂ => (analyticOrderNatAt (regularizedL χ) z:ℂ)*transform a b β z
  let S := X^V
  let L := logBudget q X
  let W := 1+Real.sqrt (1+4*|β| *X)+Real.log B
  have hV : V≤1 := by dsimp [V];linarith
  have hS : 1 ≤ S := Real.one_le_rpow hX (by dsimp [V];linarith)
  have hB : 2≤B := by linarith [heightCut_ge hX]
  have hU : 4 ≤ U := by
    dsimp [U, modelHeight]
    linarith only [Real.one_le_rpow hX (by norm_num : (0:ℝ) ≤ 3/2)]
  have hUB : U ≤ B := by
    have hPower : X^(3/2 : ℝ) ≤ X^8 := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hX (by norm_num)
    dsimp [U,modelHeight,B,heightCut]
    rw [mul_pow]
    nlinarith only [hPower,show 0 ≤ X^8 by positivity]
  have hLB : 1≤logHeight q B := logHeight_ge_one _ _
  have hL : 1≤L := by dsimp [L,logBudget,B] at *;linarith only [hLB]
  have hW : 1≤W := by dsimp [W];linarith only [Real.sqrt_nonneg (1+4*|β| *X),Real.log_nonneg (by linarith : 1≤B)]
  have hLSq : logHeight q B ≤ L^2 := by
    have h' : logHeight q B ≤ L := by dsimp [L,logBudget,B];linarith
    exact h'.trans (le_self_pow₀ hL (by decide))
  have hSubset : Z ⊆ Y := by
    intro z hz
    obtain ⟨hr,hi,hzero⟩ := (mem_exceptionalZeros χ B z).mp hz
    have hright : z.re≤2 := by by_contra! h;exact regularizedL_ne_zero_right χ (by linarith) hzero
    exact (mem_boxZeros χ _ _ _ _ z).mpr ⟨mem_reProdIm.mpr
      ⟨⟨by linarith only [hσ.2,hr],hright⟩,abs_le.mp (hi.trans hT.1)⟩,hzero⟩
  let LZ := (Y \ Z).filter (fun z => |z.im| ≤ B)
  let HZ := (Y \ Z).filter (fun z => ¬ |z.im| ≤ B)
  have lowGeom (z : ℂ) (hz : z ∈ LZ) : 1/2 ≤ z.re ∧ z.re ≤ V ∧ |z.im| ≤ B := by
    obtain ⟨hz',hi⟩ := mem_filter.mp hz
    obtain ⟨hzY,hzZ⟩ := mem_sdiff.mp hz'
    obtain ⟨h,hzero⟩ := (mem_boxZeros χ _ _ _ _ z).mp hzY
    have hlower : 1/2 ≤ z.re := by linarith only [(mem_reProdIm.mp h).1.1,hσ.1]
    refine ⟨hlower,?_,hi⟩
    by_contra! hf
    exact hzZ ((mem_exceptionalZeros χ B z).mpr ⟨hf,hi,hzero⟩)
  have highGeom (z : ℂ) (hz : z ∈ HZ) : 1/2 ≤ z.re ∧ z.re ≤ 2 ∧ B ≤ |z.im| ∧ |z.im| ≤ B+1 := by
    obtain ⟨hz',hi'⟩ := mem_filter.mp hz
    have hzY := (mem_sdiff.mp hz').1
    obtain ⟨h,hzero⟩ := (mem_boxZeros χ _ _ _ _ z).mp hzY
    obtain ⟨hr,hi⟩ := mem_reProdIm.mp h
    exact ⟨by linarith only [hσ.1,hr.1],hr.2,le_of_lt (lt_of_not_ge hi'),(abs_le.mpr hi).trans hT.2⟩
  have hpow : X^4 ≤ B^2 := by
    have h8 := pow_le_pow_right₀ hX (show 4≤8 by decide)
    have h : X^8≤B := by dsimp [B,heightCut];rw [mul_pow];norm_num;linarith [pow_nonneg (by linarith : 0≤X) 8]
    exact (h8.trans h).trans (le_self_pow₀ (by linarith : 1≤B) (by decide))
  have low := narrow q χ LZ a b X β B V hX ha hab hb hB hV lowGeom
  have hi := high q χ HZ a b X β B hX ha hab hb hβ hB hpow highGeom
  have nf (z : ℂ) : ‖F z‖ = (analyticOrderNatAt (regularizedL χ) z:ℝ)*‖transform a b β z‖ := by simp [F]
  have hZ₀ : Z₀ ⊆ Z := by
    intro z hz
    obtain ⟨hr,hi,hzero⟩ := (mem_exceptionalZeros χ U z).mp hz
    exact (mem_exceptionalZeros χ B z).mpr ⟨hr,hi.trans hUB,hzero⟩
  have tailGeom (z : ℂ) (hz : z ∈ Z \ Z₀) : 1/2 ≤ z.re ∧ z.re ≤ 1 ∧
      U ≤ |z.im| ∧ |z.im| ≤ B := by
    obtain ⟨hzZ,hzZ₀⟩ := mem_sdiff.mp hz
    obtain ⟨hr,hi,hzero⟩ := (mem_exceptionalZeros χ B z).mp hzZ
    refine ⟨by linarith,(re_lt_one_of_regularizedL_zero χ hzero).le,?_,hi⟩
    by_contra! hf
    exact hzZ₀ ((mem_exceptionalZeros χ U z).mpr ⟨hr,hf.le,hzero⟩)
  have htrim : ‖(∑ z ∈ Z₀,F z)-(∑ z ∈ Z,F z)‖ ≤ D*S*L^2*W := by
    have hm := tail q χ (Z \ Z₀) a b X β U B hX ha hab hb hβ hβX hU hUB tailGeom
    have hUpos : 0 < U := by linarith
    have hUbudget : X^2/U ≤ S := calc
      _ = (1/4)*X^(1/2 : ℝ) := by
        apply (div_eq_iff hUpos.ne').mpr
        dsimp [U,modelHeight]
        calc
          _ = X^(1/2 : ℝ)*X^(3/2 : ℝ) * (4 * (1/4)) := by
            rw [← Real.rpow_add (zero_lt_one.trans_le hX)]
            norm_num
          _ = _ := by ring
      _ ≤ X^(1/2 : ℝ) := mul_le_of_le_one_left (Real.rpow_nonneg (by linarith) _) (by norm_num)
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hX (by norm_num [V])
    rw [←sum_sdiff_sub_sum_sdiff,Finset.sdiff_eq_empty_iff_subset.mpr hZ₀,sum_empty,zero_sub,norm_neg]
    apply (norm_sum_le ..).trans
    simp_rw [nf]
    refine hm.trans ?_
    rw [show D*X^2*logHeight q B/U = D*((X^2/U)*logHeight q B) by ring]
    have h := mul_le_mul_of_nonneg_left
      (mul_le_mul hUbudget hLSq (zero_le_one.trans hLB) (by positivity)) hD.le
    have hmW := le_mul_of_one_le_right (show 0 ≤ D*(S*L^2) by positivity) hW
    exact (h.trans hmW).trans_eq (by ring)
  have small : ‖(∑ z ∈ Z,F z)-(∑ z ∈ Y,F z)‖ ≤ (K+A)*S*L^2*W := by
    rw [←Finset.sum_sdiff_sub_sum_sdiff,Finset.sdiff_eq_empty_iff_subset.mpr hSubset,sum_empty,zero_sub,norm_neg,
      ←Finset.sum_filter_add_sum_filter_not (Y \ Z) (fun z => |z.im| ≤ B) F]
    change ‖(∑ z ∈ LZ,F z)+(∑ z ∈ HZ,F z)‖ ≤ _
    apply (norm_add_le ..).trans
    apply (add_le_add (norm_sum_le ..) (norm_sum_le ..)).trans
    simp_rw [nf]
    have low' : K*S*logHeight q B*W ≤ K*S*L^2*W := by gcongr
    have hh := (mul_le_mul_of_nonneg_left hLSq hA.le).trans (show A*L^2 ≤ A*S*L^2*W from by
      have h := le_mul_of_one_le_left (sq_nonneg L) hS
      have h' := le_mul_of_one_le_right (show 0≤S*L^2 by positivity) hW
      nlinarith only [mul_le_mul_of_nonneg_left (h.trans h') hA.le])
    exact (add_le_add (low.trans low') (hi.trans hh)).trans_eq (by ring)
  let P := ∑ k ∈ Finset.Ioc a b,twistedCoefficient χ k*phase β k
  let M := principalFlag χ*transform a b β 1
  change ‖P-(M-∑ z ∈ Z₀,F z)‖ ≤ _
  rw [show (1/2+2*(1/16) : ℝ) = 5/8 by norm_num] at e
  change ‖P-(M-∑ z ∈ Y,F z)‖ ≤ C*S*L^2*W at e
  have eq' : P-(M-∑ z ∈ Z₀,F z) = ((P-(M-∑ z ∈ Y,F z))+((∑ z ∈ Z,F z)-(∑ z ∈ Y,F z))) +
      ((∑ z ∈ Z₀,F z)-(∑ z ∈ Z,F z)) := by abel
  rw [eq']
  exact (norm_add_le ..).trans ((add_le_add ((norm_add_le ..).trans (add_le_add e small)) htrim).trans_eq
    (by dsimp [S,L,W,V,B];ring))
end GoldbachTwistedMellin
end
end

section
open Set Complex MeasureTheory Goldbach
open scoped Interval Topology
noncomputable section
namespace GoldbachTwistedMellin

/-- A zero contributes to a contiguous sequence of upper dyadic blocks.
This is the lower endpoint of their union, or the upper endpoint if it is empty. -/
def zeroWindowStart (m : ℕ) (t : ℝ) : ℕ :=
  if h : m < 2 then m + 2 else
    if |t| ≤ modelHeight (m / 2 + 2 : ℕ) then zeroWindowStart (m / 2) t else m + 2
termination_by m
decreasing_by exact Nat.div_lt_self (by omega) (by decide)

/-- The smoothing averages translates of the endpoint. A common antiderivative
makes the internal boundaries cancel before taking absolute values. -/
def windowEndpoint (a β : ℝ) (s : ℂ) : ℂ :=
  ∫ y in a..a+1, ∫ x in (1 : ℝ)..y, density β s x

theorem transform_eq_windowEndpoints {a b : ℝ} (ha : 1 ≤ a) (hab : a+1 ≤ b) (β : ℝ) (s : ℂ) :
    transform a b β s = windowEndpoint b β s - windowEndpoint a β s := by
  rw [transform_eq_taper_integral (zero_lt_one.trans_le ha) hab]
  apply window_primitive hab
  · exact fun x hx => (continuousAt_density β s (zero_lt_one.trans_le (ha.trans hx.1))).continuousWithinAt
  · intro x hx
    have hx1 := ha.trans hx.1
    have hx0 := zero_lt_one.trans_le hx1
    apply intervalIntegral.integral_hasDerivAt_right (integral_density zero_lt_one hx1 β s)
    · exact ContinuousAt.stronglyMeasurableAtFilter (s := Ioi (0:ℝ)) isOpen_Ioi
        (fun y hy => continuousAt_density β s hy) x hx0
    · exact continuousAt_density β s hx0

private theorem modelHeight_mono {a b : ℕ} (hab : a ≤ b) : modelHeight a ≤ modelHeight b := by
  unfold modelHeight
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hab)
    (by norm_num)) (by norm_num)

theorem zeroWindowStart_bounds (m : ℕ) (t : ℝ) :
    2 ≤ zeroWindowStart m t ∧ zeroWindowStart m t ≤ m+2 ∧
      (zeroWindowStart m t : ℝ) ≤ max 3 |t| := by
  induction m using Nat.strong_induction_on with
  | ind m ih =>
    rw [zeroWindowStart]
    split_ifs with h hkeep
    · exact ⟨by omega, le_rfl, (show ((m + 2 : ℕ) : ℝ) ≤ 3 by exact_mod_cast (show m+2 ≤ 3 by omega)).trans (le_max_left ..)⟩
    · obtain ⟨hl, hr, ht⟩ := ih (m/2) (Nat.div_lt_self (by omega) (by decide))
      exact ⟨hl, by omega, ht⟩
    · have ha : 1 ≤ ((m/2 + 2 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ m/2+2 by omega)
      have hp : ((m/2+2 : ℕ) : ℝ) ≤ ((m/2+2 : ℕ) : ℝ)^(3/2:ℝ) := by
        simpa using Real.rpow_le_rpow_of_exponent_le ha (show (1:ℝ) ≤ 3/2 by norm_num)
      have hb : ((m+2 : ℕ) : ℝ) ≤ 2*((m/2+2 : ℕ) : ℝ) := by exact_mod_cast (show m+2 ≤ 2*(m/2+2) by omega)
      have ht := lt_of_not_ge hkeep
      unfold modelHeight at ht
      exact ⟨by omega, le_rfl, (show ((m+2 : ℕ) : ℝ) ≤ |t| by linarith only [ha, hp, hb, ht]).trans (le_max_right ..)⟩

private theorem sum_zero_windows (m : ℕ) (β : ℝ) (s : ℂ) :
    ((prefixBlocks m).map fun p =>
      if |s.im| ≤ modelHeight p.1 then transform p.1 p.2 β s else 0).sum =
      windowEndpoint (m+2 : ℕ) β s - windowEndpoint (zeroWindowStart m s.im) β s := by
  induction m using Nat.strong_induction_on with
  | ind m ih =>
    by_cases h : m < 2
    · simp [prefixBlocks, zeroWindowStart, h]
    · have hlt := Nat.div_lt_self (show 0 < m by omega) (by decide : 1 < 2)
      rw [prefixBlocks, dite_eq_right h, List.map_cons, List.sum_cons, zeroWindowStart, dite_eq_right h]
      by_cases hk : |s.im| ≤ modelHeight (m/2+2 : ℕ)
      · rw [ite_eq_left hk, ite_eq_left hk, ih (m/2) hlt,
          transform_eq_windowEndpoints (by exact_mod_cast (show 1 ≤ m/2+2 by omega))
            (by exact_mod_cast (show m/2+2+1 ≤ m+2 by omega))]
        abel
      · rw [ite_eq_right hk, ite_eq_right hk, sub_self, zero_add]
        apply List.sum_eq_zero
        intro v hv
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hv
        obtain ⟨_, hl, _, hr⟩ := prefixBlocks_valid hp
        exact ite_eq_right (fun ht => hk (ht.trans (modelHeight_mono (by omega))))

/-- Each primitive zero occurs once, with its analytic multiplicity, in the
complete window. Its effective endpoints account for every block height cutoff. -/
theorem prefix_fixedZeroTerm_eq_zeroWindows {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (m : ℕ) (β : ℝ) :
    ((prefixBlocks m).map fun p => fixedZeroTerm χ p.1 p.2 p.1 β).sum =
      ∑ z ∈ exceptionalZeros χ (modelHeight (m+2 : ℕ)),
        (analyticOrderNatAt (regularizedL χ) z : ℂ) *
          (windowEndpoint (m+2 : ℕ) β z - windowEndpoint (zeroWindowStart m z.im) β z) := by
  classical
  let Z := exceptionalZeros χ (modelHeight (m+2 : ℕ))
  let mult := fun z : ℂ => (analyticOrderNatAt (regularizedL χ) z : ℂ)
  let U := fun (p : ℕ × ℕ) (s : ℂ) =>
    if |s.im| ≤ modelHeight p.1 then transform p.1 p.2 β s else 0
  have localSum (p : ℕ × ℕ) (hp : p ∈ prefixBlocks m) :
      fixedZeroTerm χ p.1 p.2 p.1 β = ∑ z ∈ Z, mult z * U p z := by
    obtain ⟨_, hl, _, hr⟩ := prefixBlocks_valid hp
    have hZ : exceptionalZeros χ (modelHeight p.1) = Z.filter (fun z => |z.im| ≤ modelHeight p.1) := by
      ext z
      simp only [Z, Finset.mem_filter, mem_exceptionalZeros]
      constructor
      · rintro ⟨hσ, hγ, hroot⟩
        exact ⟨⟨hσ, hγ.trans (modelHeight_mono (by omega)), hroot⟩, hγ⟩
      · rintro ⟨⟨hσ, _, hroot⟩, hγ⟩
        exact ⟨hσ, hγ, hroot⟩
    simp [fixedZeroTerm, hZ, Finset.sum_filter, mult, U, mul_ite]
  have commute (l : List (ℕ × ℕ)) :
      (l.map (fun p => ∑ z ∈ Z, mult z * U p z)).sum =
        ∑ z ∈ Z, mult z * (l.map (fun p => U p z)).sum := by
    induction l with
    | nil => simp
    | cons p l ih => simp only [List.map_cons, List.sum_cons, ih, mul_add, Finset.sum_add_distrib]
  rw [show ((prefixBlocks m).map fun p => fixedZeroTerm χ p.1 p.2 p.1 β) =
      ((prefixBlocks m).map fun p => ∑ z ∈ Z, mult z * U p z) from List.map_congr_left localSum,
    commute]
  exact Finset.sum_congr rfl (fun z _ => congrArg (fun a : ℂ => mult z * a) (sum_zero_windows m β z))

end GoldbachTwistedMellin
end
end

section
open Set Complex MeasureTheory
open scoped Interval Topology FourierTransform Convolution
noncomputable section
namespace GoldbachTwistedMellin

/-- Fourier integral of one sharp power profile, with angular frequency γ. -/
def sharpPower (B γ : ℝ) (s : ℂ) : ℂ := ∫ x in (0 : ℝ)..B, density γ s x

theorem density_intervalIntegrable (γ : ℝ) {s : ℂ} (hs : 0 < s.re) (a b : ℝ) :
    IntervalIntegrable (density γ s) volume a b := by
  exact (intervalIntegral.intervalIntegrable_cpow' (show -1 < (s-1).re by simpa using (show -1 < s.re-1 by linarith))).continuousOn_mul
    (continuous_phase γ).continuousOn

private theorem norm_density_pos (γ : ℝ) (s : ℂ) {x : ℝ} (hx : 0 < x) :
    ‖density γ s x‖ = x ^ (s.re-1) := by
  simp only [density, norm_mul, norm_phase, one_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.sub_re, Complex.one_re]

private theorem sharpPower_norm (γ : ℝ) {s : ℂ} (hs : 0 < s.re) {B : ℝ} (hB : 0 ≤ B) :
    ‖sharpPower B γ s‖ ≤ B ^ s.re / s.re := by
  calc
    _ ≤ ∫ x in (0:ℝ)..B, ‖density γ s x‖ := intervalIntegral.norm_integral_le_integral_norm hB
    _ = ∫ x in (0:ℝ)..B, x^(s.re-1) := by
      apply intervalIntegral.integral_congr_uIoo
      intro x hx
      rw [uIoo_of_le hB] at hx
      exact norm_density_pos _ _ hx.1
    _ = _ := by
      rw [integral_rpow (Or.inl (by linarith : -1 < s.re-1)),
        sub_add_cancel, Real.zero_rpow (ne_of_gt hs), sub_zero]

private theorem density_ibp {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (γ : ℝ) (s : ℂ) :
    ((γ : ℂ)*I) * (∫ x in a..b, density γ s x) =
      density γ s b - density γ s a - (s-1)*(∫ x in a..b, density γ (s-1) x) := by
  have hd (x : ℝ) (hx : x ∈ [[a,b]]) :
      HasDerivAt (density γ s)
        (((γ:ℂ)*I)*density γ s x + (s-1)*density γ (s-1) x) x := by
    have hpos := ha.trans_le (((uIcc_of_le hab) ▸ hx).1)
    by_cases he : s-1 = 0
    · have hs : s = 1 := sub_eq_zero.mp he
      subst s
      rw [show density γ 1 = phase γ by funext y; simp [density] ]
      simpa [mul_comm] using phase_deriv γ x
    · have h := (phase_deriv γ x).mul (hasDerivAt_ofReal_cpow_const hpos.ne' he)
      convert h using 1
      · rfl
      · unfold density; ring
  have i1 := (integral_density ha hab γ s).const_mul ((γ:ℂ)*I)
  have i2 := (integral_density ha hab γ (s-1)).const_mul (s-1)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (i1.add i2)
  rw [intervalIntegral.integral_add i1 i2, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at h
  exact eq_sub_of_add_eq h

private theorem unit_freq_bound {γ : ℝ} (hγ : |γ| = 1) {s : ℂ} (hσ : s.re ≤ 1)
    {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    ‖∫ x in a..b, density γ s x‖ ≤ 2 + ‖s-1‖ * (2 + ‖s-2‖) := by
  have aPos := zero_lt_one.trans_le ha
  have once (u : ℂ) (hu : u.re ≤ 1) :
      ‖∫ x in a..b, density γ u x‖ ≤ 2 + ‖u-1‖ * ‖∫ x in a..b, density γ (u-1) x‖ := by
    have hend {x : ℝ} (hx : 1 ≤ x) : ‖density γ u x‖ ≤ 1 := by
      rw [norm_density_pos _ _ (zero_lt_one.trans_le hx)]
      exact Real.rpow_le_one_of_one_le_of_nonpos hx (by linarith)
    have hi := congrArg norm (density_ibp aPos hab γ u)
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, hγ, one_mul] at hi
    rw [hi]
    apply (norm_sub_le ..).trans
    rw [norm_mul]
    linarith only [norm_sub_le (density γ u b) (density γ u a), hend ha, hend (ha.trans hab)]
  have htail : ‖∫ x in a..b, density γ (s-2) x‖ ≤ 1 := by
    let f := fun x : ℝ => x^(-2 : ℝ)
    have hf : IntervalIntegrable f volume a b := by
      exact (continuousOn_id.rpow_const fun x hx => Or.inl (aPos.trans_le (((uIcc_of_le hab) ▸ hx).1)).ne').intervalIntegrable
    calc
      _ ≤ ∫ x in a..b, ‖density γ (s-2) x‖ := intervalIntegral.norm_integral_le_integral_norm hab
      _ ≤ ∫ x in a..b, f x := by
        apply intervalIntegral.integral_mono_on hab (integral_density aPos hab γ (s-2)).norm hf
        intro x hx
        rw [norm_density_pos _ _ (aPos.trans_le hx.1)]
        apply Real.rpow_le_rpow_of_exponent_le (ha.trans hx.1)
        norm_num [sub_re]; linarith
      _ ≤ 1 := by
        dsimp only [f]
        rw [integral_rpow (Or.inr ⟨by norm_num, fun h => (not_lt_of_ge ((uIcc_of_le hab) ▸ h).1) aPos⟩)]
        norm_num
        have hb : 0 ≤ b⁻¹ := inv_nonneg.mpr (aPos.le.trans hab)
        have hal : a⁻¹ ≤ 1 := inv_le_one_of_one_le₀ ha
        rw [Real.rpow_neg_one, Real.rpow_neg_one]
        linarith
  have h₁ := once s hσ
  have h₂ := once (s-1) (by rw [sub_re, one_re]; linarith)
  rw [show s-1-1 = s-2 by ring] at h₂
  exact h₁.trans (by gcongr; exact h₂.trans (by simpa using add_le_add_right (mul_le_mul_of_nonneg_left htail (norm_nonneg (s-2))) 2))

private theorem sharpPower_unit_bound {γ : ℝ} (hγ : |γ| = 1) {s : ℂ}
    (hlo : 1/2 ≤ s.re) (hhi : s.re ≤ 1) {B : ℝ} (hB : 0 ≤ B) :
    ‖sharpPower B γ s‖ ≤ 4 + ‖s-1‖ * (2 + ‖s-2‖) := by
  have hs : 0 < s.re := by linarith
  have small (x : ℝ) (hx : 0 ≤ x) (hx' : x ≤ 1) : ‖sharpPower x γ s‖ ≤ 2 := by
    apply (sharpPower_norm γ hs hx).trans
    exact (div_le_iff₀ hs).mpr ((Real.rpow_le_one hx hx' hs.le).trans (by linarith))
  rcases le_or_gt B 1 with h | h
  · exact (small B hB h).trans (by linarith only [show 0 ≤ ‖s-1‖ * (2+‖s-2‖) by positivity])
  · have he : sharpPower B γ s = sharpPower 1 γ s + ∫ x in 1..B, density γ s x :=
      (intervalIntegral.integral_add_adjacent_intervals (density_intervalIntegrable γ hs 0 1)
        (density_intervalIntegrable γ hs 1 B)).symm
    rw [he]
    apply (norm_add_le ..).trans
    linarith only [small 1 zero_le_one le_rfl, unit_freq_bound hγ hhi le_rfl h.le]

/-- Uniform oscillatory decay through the endpoint σ=1. The constant is
polynomial in the ordinate, so it is uniform on each bounded-height family. -/
theorem sharpPower_decay {γ B : ℝ} (hγ : γ ≠ 0) (hB : 0 ≤ B) {s : ℂ}
    (hlo : 1/2 ≤ s.re) (hhi : s.re ≤ 1) :
    ‖sharpPower B γ s‖ ≤ (4 + ‖s-1‖ * (2 + ‖s-2‖)) / |γ|^s.re := by
  let c := |γ|
  have hc : 0 < c := abs_pos.mpr hγ
  have hunit : |γ/c| = 1 := by rw [abs_div, abs_of_pos hc, div_self hc.ne']
  have he : sharpPower (c*B) (γ/c) s = (c:ℂ)^s * sharpPower B γ s := by
    unfold sharpPower
    have h : (∫ x in (0:ℝ)..B, density (γ/c) s (c*x)) =
        (c:ℂ)^(s-1) * ∫ x in (0:ℝ)..B, density γ s x := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr_uIoo
      intro x hx
      rw [uIoo_of_le hB] at hx
      simp only [density, phase, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hc.le hx.1.le]
      have he : (γ/c : ℝ)*c*x = γ*x := by field_simp
      have hec := congrArg Complex.ofReal he
      simp only [Complex.ofReal_mul] at hec
      rw [mul_assoc] at hec
      rw [hec]
      ring
    calc
      _ = c • ∫ x in (0:ℝ)..B, density (γ/c) s (c*x) := by
        rw [intervalIntegral.smul_integral_comp_mul_left, mul_zero]
      _ = _ := by
        rw [h, Complex.real_smul, ← mul_assoc]
        congr 1
        calc
          (c:ℂ)*(c:ℂ)^(s-1) = (c:ℂ)^((1:ℂ)+(s-1)) := by
            rw [Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hc.ne'), Complex.cpow_one]
          _ = _ := by congr 1; ring
  have h := sharpPower_unit_bound hunit hlo hhi (mul_nonneg hc.le hB)
  rw [he, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hc] at h
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hc _)).mpr
  simpa only [mul_comm] using h

end GoldbachTwistedMellin
end
end

section
open Set Complex MeasureTheory Filter
open scoped Interval Topology
noncomputable section
namespace GoldbachTwistedMellin
theorem continuous_transform_frequency {a b : ℝ} (ha : 0 < a) (hab : a + 1 ≤ b) (s : ℂ) :
    Continuous (fun β => GoldbachTwistedMellin.transform a b β s) := by
  let w := fun x : ℝ => ((max x a : ℝ) : ℂ) ^ (s - 1)
  have hw : Continuous w := by
    have hmax : Continuous (fun x : ℝ => max x a) := continuous_id.max continuous_const
    apply continuous_iff_continuousAt.mpr
    intro x
    exact ContinuousAt.comp' (f := fun t : ℝ => max t a) (x := x)
      (Complex.continuousAt_ofReal_cpow_const (max x a) (s-1)
        (Or.inr (ha.trans_le (le_max_right x a)).ne')) hmax.continuousAt
  let f := fun β x => (GoldbachTwistedMellin.taper a b x : ℂ) *
    (GoldbachTwistedMellin.phase β x * w x)
  have hf : Continuous (Function.uncurry f) := by
    unfold f Function.uncurry GoldbachTwistedMellin.phase
    exact (Complex.continuous_ofReal.comp ((GoldbachTwistedMellin.continuous_taper a b).comp
      continuous_snd)).mul ((by fun_prop : Continuous (fun p : ℝ × ℝ =>
        Complex.exp (((p.1 * p.2 : ℝ) : ℂ) * Complex.I))).mul (hw.comp continuous_snd))
  have h := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (μ := volume) hf a (b+1)
  refine h.congr ?_
  intro β
  rw [GoldbachTwistedMellin.transform_eq_taper_integral ha hab]
  apply intervalIntegral.integral_congr
  intro x hx
  rw [Set.uIcc_of_le (by linarith)] at hx
  simp only [f, w, GoldbachTwistedMellin.density, max_eq_left hx.1]


def zeroPowerProfile (m : ℕ) (γ : ℝ) (s : ℂ) : ℂ :=
  windowEndpoint (m+2 : ℕ) γ s - windowEndpoint (zeroWindowStart m s.im) γ s

/-- Moving either end of the averaged window by at most one unit costs at
most one, uniformly in the frequency and the ordinate. -/
private theorem windowEndpoint_error {a c : ℝ} (ha : 1 ≤ a) (hc : c ∈ Icc a (a+1)) (γ : ℝ)
    {s : ℂ} (hs : 0 < s.re) (hs' : s.re ≤ 1) :
    ‖windowEndpoint a γ s - (sharpPower c γ s - sharpPower 1 γ s)‖ ≤ 1 := by
  let f := density γ s
  have hi (x y : ℝ) : IntervalIntegrable f volume x y := density_intervalIntegrable γ hs x y
  have hp := intervalIntegral.continuous_primitive hi 1
  have he : windowEndpoint a γ s - (sharpPower c γ s - sharpPower 1 γ s) =
      ∫ y in a..a+1, ∫ x in c..y, f x := by
    have hconst : sharpPower c γ s - sharpPower 1 γ s = ∫ x in (1:ℝ)..c, f x :=
      intervalIntegral.integral_interval_sub_left (hi 0 c) (hi 0 1)
    rw [windowEndpoint, hconst]
    change (∫ y in a..a+1, ∫ x in (1:ℝ)..y, f x) - _ = _
    calc
      _ = (∫ y in a..a+1, ∫ x in (1:ℝ)..y, f x) - ∫ _y in a..a+1, (∫ x in (1:ℝ)..c, f x) := by simp
      _ = _ := by
        rw [← intervalIntegral.integral_sub (hp.intervalIntegrable ..) intervalIntegrable_const]
        exact intervalIntegral.integral_congr fun y _ => intervalIntegral.integral_interval_sub_left (hi 1 y) (hi 1 c)
  rw [he]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := a+1) (C := 1)
    (f := fun y => ∫ x in c..y, f x) (fun y hy => by
      rw [uIoc_of_le (by linarith)] at hy
      have hyc : |y-c| ≤ 1 := abs_le.mpr ⟨by linarith only [hy.1, hc.2], by linarith only [hy.2, hc.1]⟩
      have hinner := intervalIntegral.norm_integral_le_of_norm_le_const (a := c) (b := y)
        (C := 1) (f := f) (fun x hx => by
          have hx1 : 1 ≤ x := (le_min (ha.trans hc.1) (ha.trans hy.1.le)).trans hx.1.le
          rw [show f x = density γ s x from rfl, norm_density_pos _ _ (zero_lt_one.trans_le hx1)]
          exact Real.rpow_le_one_of_one_le_of_nonpos hx1 (by linarith))
      simpa only [one_mul] using hinner.trans (by simpa only [one_mul] using hyc))
  simpa using h

/-- A bounded-height zero in the actual rational model differs from its sharp
power integral by a constant independent of X and of the frequency. -/
theorem zeroPowerProfile_error (m : ℕ) (γ : ℝ) {s : ℂ} (hs : 1/2 ≤ s.re) (hs' : s.re ≤ 1) :
    ‖zeroPowerProfile m γ s - sharpPower (m+3 : ℕ) γ s‖ ≤ 2+2*max 3 |s.im| := by
  let a : ℝ := zeroWindowStart m s.im
  let b : ℝ := (m+2 : ℕ)
  have hs0 : 0 < s.re := by linarith
  obtain ⟨ha₂, _, haT⟩ := zeroWindowStart_bounds m s.im
  have ha : 1 ≤ a := by dsimp [a]; exact_mod_cast (show 1 ≤ zeroWindowStart m s.im by omega)
  have hb : 1 ≤ b := by dsimp only [b]; exact_mod_cast (show 1 ≤ m+2 by omega)
  have e1 := windowEndpoint_error ha (show a ∈ Icc a (a+1) from ⟨le_rfl, by linarith⟩) γ hs0 hs'
  have e2 := windowEndpoint_error hb (show b+1 ∈ Icc b (b+1) from ⟨by linarith, le_rfl⟩) γ hs0 hs'
  have e3 : ‖sharpPower a γ s‖ ≤ 2*a := by
    apply (sharpPower_norm γ hs0 (zero_le_one.trans ha)).trans
    apply (div_le_iff₀ hs0).mpr
    have hp : a^s.re ≤ a := by simpa using Real.rpow_le_rpow_of_exponent_le ha hs'
    exact hp.trans (by nlinarith only [mul_le_mul_of_nonneg_left hs (zero_le_one.trans ha)])
  have htop : ((m+3 : ℕ):ℝ) = b+1 := by dsimp [b]; push_cast; ring
  rw [htop]
  have he : zeroPowerProfile m γ s - sharpPower (b+1) γ s =
      (windowEndpoint b γ s - (sharpPower (b+1) γ s - sharpPower 1 γ s)) -
      (windowEndpoint a γ s - (sharpPower a γ s - sharpPower 1 γ s)) - sharpPower a γ s := by
    change windowEndpoint b γ s - windowEndpoint a γ s - _ = _
    abel
  rw [he]
  apply (norm_sub_le ..).trans
  apply (add_le_add (norm_sub_le ..) e3).trans
  change a ≤ max 3 |s.im| at haT
  linarith only [e1, e2, haT]

end GoldbachTwistedMellin
end
end

section
open Set Complex MeasureTheory Filter
open scoped Interval Topology FourierTransform Convolution
noncomputable section
namespace GoldbachTwistedMellin

private def sharpWeight (B : ℝ) (s : ℂ) : ℝ → ℂ :=
  (Ioc 0 B).indicator (fun x : ℝ => (x:ℂ)^(s-1))

private theorem integrable_sharpWeight {B : ℝ} (hB : 0 ≤ B) {s : ℂ} (hs : 0 < s.re) :
    Integrable (sharpWeight B s) :=
  (integrable_indicator_iff measurableSet_Ioc).mpr ((intervalIntegrable_iff_integrableOn_Ioc_of_le hB).mp
    (intervalIntegral.intervalIntegrable_cpow' (by rw [sub_re, one_re]; linarith : -1 < (s-1).re)))

private theorem fourier_sharpWeight (B : ℝ) (hB : 0 ≤ B) (s : ℂ) (t : ℝ) :
    𝓕 (sharpWeight B s) t = sharpPower B (-2*Real.pi*t) s := by
  rw [Real.fourier_real_eq_integral_exp_smul, sharpPower, intervalIntegral.integral_of_le hB,
    ← integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x ∈ Ioc 0 B
  · simp only [sharpWeight, indicator_of_mem hx, smul_eq_mul, density, phase]
    congr 3
    push_cast
    ring
  · simp [sharpWeight, indicator_of_notMem hx]

private theorem continuous_sharpPowerFreq {B : ℝ} (hB : 0 ≤ B) {s : ℂ} (hs : 0 < s.re) :
    Continuous (fun t : ℝ => sharpPower B (2*Real.pi*t) s) := by
  have hf := (memLp_one_iff_integrable.mpr (integrable_sharpWeight hB hs))
  have hft : Continuous (𝓕 (sharpWeight B s)) := by
    rw [← Real.fourierTransform_toLp hf]
    exact (Real.Lp.fourierTransform hf.toLp).continuous
  refine (hft.comp continuous_neg).congr (fun t => ?_)
  dsimp only [Function.comp_apply]
  rw [fourier_sharpWeight B hB, show -2*Real.pi*(-t) = 2*Real.pi*t by ring]

private theorem sharpWeight_convolution {B n : ℝ} (hn : 0 < n) (hnB : n < B) (s t : ℂ) :
    (sharpWeight B s ⋆[ContinuousLinearMap.mul ℂ ℂ] sharpWeight B t) n =
      (n:ℂ)^(s+t-1) * Complex.betaIntegral s t := by
  rw [← Complex.betaIntegral_scaled s t hn, intervalIntegral.integral_of_le hn.le,
    integral_Ioc_eq_integral_Ioo, ← integral_indicator measurableSet_Ioo]
  apply integral_congr_ae
  filter_upwards with x
  change sharpWeight B s x * sharpWeight B t (n-x) = _
  by_cases hx : x ∈ Ioo 0 n
  · have h1 : x ∈ Ioc 0 B := ⟨hx.1, hx.2.le.trans hnB.le⟩
    have h2 : n-x ∈ Ioc 0 B := ⟨sub_pos.mpr hx.2, by linarith only [hx.1, hnB]⟩
    simp only [sharpWeight, indicator_of_mem h1, indicator_of_mem h2, indicator_of_mem hx, ofReal_sub]
  · rw [indicator_of_notMem hx]
    rcases le_or_gt x 0 with hx0 | hx0
    · simp [sharpWeight, indicator_of_notMem (show x ∉ Ioc 0 B from fun h => hx0.not_gt h.1)]
    · have hnx : n ≤ x := le_of_not_gt (fun h => hx ⟨hx0, h⟩)
      have h2 : n-x ∉ Ioc 0 B := fun h => (sub_nonpos.mpr hnx).not_gt h.1
      simp [sharpWeight, indicator_of_notMem h2]

/-- Absolute error when a Fourier integral whose two factors give more
than one power of decay is restricted to a symmetric major arc. -/
private theorem finite_arc_tail {f : ℝ → ℂ} (hf : Continuous f) {r D w : ℝ}
    (hr : 1 < r) (hw : 0 < w) (hdec : ∀ x : ℝ, x ≠ 0 → ‖f x‖ ≤ D * |x|^(-r)) :
    Integrable f ∧ ‖(∫ x in -w..w, f x) - ∫ x, f x‖ ≤ 2*D*w^(1-r)/(r-1) := by
  have hpow := integrableOn_Ioi_rpow_of_lt (show -r < -1 by linarith) hw
  have H (g : ℝ → ℂ) (hg : Continuous g)
      (h : ∀ x ∈ Ioi w, ‖g x‖ ≤ D*x^(-r)) :
      IntegrableOn g (Ioi w) ∧ ‖∫ x in Ioi w, g x‖ ≤ D*w^(1-r)/(r-1) := by
    have hd := (hpow.const_mul D)
    have hi : IntegrableOn g (Ioi w) := hd.mono' hg.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall h))
    refine ⟨hi, (norm_integral_le_integral_norm _).trans ?_⟩
    calc
      _ ≤ ∫ x in Ioi w, D*x^(-r) := integral_mono_ae hi.norm hd
        ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall h))
      _ = _ := by
        rw [integral_const_mul, integral_Ioi_rpow_of_lt (show -r < -1 by linarith) hw,
          show -r+1 = 1-r by ring]
        rw [show 1-r = -(r-1) by ring, neg_div_neg_eq]
        ring
  obtain ⟨hpos, ep⟩ := H f hf (fun x hx => by simpa only [abs_of_pos (hw.trans hx)] using hdec x (hw.trans hx).ne')
  obtain ⟨hneg', en⟩ := H (fun x => f (-x)) (hf.comp continuous_neg) (fun x hx => by
    simpa only [abs_neg, abs_of_pos (hw.trans hx)] using hdec (-x) (neg_ne_zero.mpr (hw.trans hx).ne'))
  have hneg : IntegrableOn f (Iic (-w)) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    let e : MeasurableEmbedding fun x : ℝ => -x := (Homeomorph.neg ℝ).measurableEmbedding
    rw [e.integrableOn_map_iff]
    simp only [neg_preimage, neg_Iic, neg_neg]
    exact Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi hneg'
  rw [integral_comp_neg_Ioi] at en
  have hleft : IntegrableOn f (Iic w) := by
    rw [← Iic_union_Ioc_eq_Iic (show -w ≤ w by linarith)]
    exact hneg.union (hf.intervalIntegrable (-w) w).1
  have htotal := hleft.union hpos
  rw [Iic_union_Ioi, integrableOn_univ] at htotal
  refine ⟨htotal, ?_⟩
  rw [← intervalIntegral.integral_Iic_sub_Iic hneg hleft,
    ← intervalIntegral.integral_Iic_add_Ioi hleft hpos]
  rw [show (∫ x in Iic w, f x) - (∫ x in Iic (-w), f x) -
      ((∫ x in Iic w, f x) + ∫ x in Ioi w, f x) =
      -((∫ x in Iic (-w), f x) + ∫ x in Ioi w, f x) by abel, norm_neg]
  exact (norm_add_le ..).trans ((add_le_add en ep).trans_eq (by ring))

def sharpDecayConstant (s : ℂ) : ℝ := 4 + ‖s-1‖*(2+‖s-2‖)

private theorem sharpPair_decay {B : ℝ} (hB : 0 ≤ B) {s t : ℂ}
    (hs : 1/2 ≤ s.re) (hs' : s.re ≤ 1) (ht : 1/2 ≤ t.re) (ht' : t.re ≤ 1)
    {u : ℝ} (hu : u ≠ 0) :
    ‖sharpPower B (2*Real.pi*u) s * sharpPower B (2*Real.pi*u) t‖ ≤
      sharpDecayConstant s * sharpDecayConstant t * |u|^(-(s.re+t.re)) := by
  have huPos := abs_pos.mpr hu
  have hscale : |u| ≤ |2*Real.pi*u| := by
    rw [abs_mul, abs_of_pos (by positivity : 0 < 2*Real.pi)]
    exact le_mul_of_one_le_left huPos.le (by linarith only [Real.pi_gt_three])
  have each (v : ℂ) (hlo : 1/2 ≤ v.re) (hhi : v.re ≤ 1) :
      ‖sharpPower B (2*Real.pi*u) v‖ ≤ sharpDecayConstant v * |u|^(-v.re) := by
    have hfreq : 2*Real.pi*u ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hu
    have h : ‖sharpPower B (2*Real.pi*u) v‖ ≤ sharpDecayConstant v / |2*Real.pi*u|^v.re :=
      sharpPower_decay hfreq hB hlo hhi
    have hC : 0 ≤ sharpDecayConstant v := by unfold sharpDecayConstant; positivity
    rw [Real.rpow_neg huPos.le, ← div_eq_mul_inv]
    exact h.trans (div_le_div_of_nonneg_left hC
      (Real.rpow_pos_of_pos huPos _) (Real.rpow_le_rpow huPos.le hscale (by linarith)))
  rw [norm_mul]
  have hC : 0 ≤ sharpDecayConstant s * |u|^(-s.re) := by unfold sharpDecayConstant; positivity
  apply (mul_le_mul (each s hs hs') (each t ht ht') (norm_nonneg _) hC).trans_eq
  rw [mul_mul_mul_comm, ← Real.rpow_add huPos]
  congr 2
  ring

/-- The two unrestricted sharp power profiles have the beta factor as their
Fourier coefficient. Truncating to the actual arc introduces the displayed
uniform tail, including the case that either exponent is one. -/
theorem sharpPair_arc_beta {B n w : ℝ} (hn : 0 < n) (hnB : n < B) (hw : 0 < w)
    {s t : ℂ} (hs : 1/2 ≤ s.re) (hs' : s.re ≤ 1) (ht : 1/2 ≤ t.re) (ht' : t.re ≤ 1)
    (hsum : 1 < s.re+t.re) :
    ‖(∫ u in -w..w, phase (-2*Real.pi*n) u *
      (sharpPower B (2*Real.pi*u) s * sharpPower B (2*Real.pi*u) t)) -
      (n : ℂ)^(s+t-1)*Complex.betaIntegral s t‖ ≤
      2*(sharpDecayConstant s*sharpDecayConstant t)*w^(1-(s.re+t.re))/(s.re+t.re-1) := by
  have hB := (hn.trans hnB).le
  have hs0 : 0 < s.re := by linarith
  have ht0 : 0 < t.re := by linarith
  let c := sharpWeight B s ⋆[ContinuousLinearMap.mul ℂ ℂ] sharpWeight B t
  have hc : Integrable c := (integrable_sharpWeight hB hs0).integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) (integrable_sharpWeight hB ht0)
  have hbeta {x : ℝ} (hx : 0 < x) (hxB : x < B) :
      c x = (x:ℂ)^(s+t-1)*Complex.betaIntegral s t := sharpWeight_convolution hx hxB s t
  have hcc : ContinuousAt c n := by
    have hcPow : ContinuousAt (fun x : ℝ => (x:ℂ)^(s+t-1)) n :=
      (differentiableAt_id.ofReal_cpow_const (s+t-1) hn.ne').continuousAt
    apply (hcPow.mul_const (Complex.betaIntegral s t)).congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds hn hnB] with x hx
    exact hbeta hx.1 hx.2
  let p := fun u : ℝ => sharpPower B (2*Real.pi*u) s * sharpPower B (2*Real.pi*u) t
  have hInv (u : ℝ) : 𝓕⁻ c u = p u := by
    rw [Real.fourierInv_eq_fourier_neg, Real.fourier_mul_convolution_eq (integrable_sharpWeight hB hs0)
      (integrable_sharpWeight hB ht0), fourier_sharpWeight B hB, fourier_sharpWeight B hB]
    simp only [p, neg_mul, mul_neg, neg_neg]
  let D := sharpDecayConstant s*sharpDecayConstant t
  have hpc : Continuous p := (continuous_sharpPowerFreq hB hs0).mul (continuous_sharpPowerFreq hB ht0)
  have hd : ∀ u : ℝ, u ≠ 0 → ‖p u‖ ≤ D*|u|^(-(s.re+t.re)) := fun _ hu =>
    sharpPair_decay hB hs hs' ht ht' hu
  have hpf := (finite_arc_tail hpc hsum hw hd).1
  have hft : Integrable (𝓕 c) := by
    have eq : 𝓕 c = fun u => p (-u) := funext fun u => by simpa only [Real.fourierInv_eq_fourier_neg, neg_neg] using hInv (-u)
    rw [eq]
    exact hpf.comp_neg
  have hfull := hc.fourier_fourierInv_eq hft hcc
  rw [Real.fourier_real_eq_integral_exp_smul, hbeta hn hnB] at hfull
  let f := fun u : ℝ => phase (-2*Real.pi*n) u * p u
  have he : (∫ u, f u) = (n:ℂ)^(s+t-1) * betaIntegral s t := by
    rw [← hfull]
    apply integral_congr_ae
    filter_upwards with u
    simp only [f, phase, hInv, smul_eq_mul]
    rw [show -2*Real.pi*n*u = -2*Real.pi*u*n by ring]
  have hfc : Continuous f := (continuous_phase (-2*Real.pi*n)).mul hpc
  have hfdec (u : ℝ) (hu : u ≠ 0) : ‖f u‖ ≤ D*|u|^(-(s.re+t.re)) := by
    rw [show f u = phase (-2*Real.pi*n) u * p u from rfl, norm_mul, norm_phase, one_mul]
    exact hd u hu
  have tail := (finite_arc_tail hfc hsum hw hfdec).2
  change ‖(∫ u in -w..w, f u) - _‖ ≤ _
  rw [← he]
  exact tail

end GoldbachTwistedMellin
end
end

section
open Set Complex MeasureTheory DeepThreeQuarters
open scoped Interval Topology
noncomputable section
namespace GoldbachTwistedMellin

/-- The integer principal profile and the sharp continuous one differ by a
uniform constant across the entire fundamental frequency interval. -/
theorem principalProfile_sharpPower (X : ℕ) {β : ℝ} (hβ : |β| ≤ 1/2) :
    ‖positiveGeometricSum X β - sharpPower (X+1 : ℕ) (2*Real.pi*β) 1‖ ≤ 1 + Real.pi := by
  let γ := 2*Real.pi*β
  let A := ∫ x in (0:ℝ)..1, phase γ x
  have hgeo (n : ℕ) : geometricPhase ((n:ℝ)*β) = phase γ n := by
    unfold geometricPhase phase γ
    congr 3
    ring
  have hsum (n : ℕ) : (∫ x in (0:ℝ)..(n:ℝ), phase γ x) = geometricSum n β * A := by
    induction n with
    | zero => simp [geometricSum]
    | succ n ih =>
      rw [Nat.cast_succ, ← intervalIntegral.integral_add_adjacent_intervals
        ((continuous_phase γ).intervalIntegrable 0 (n:ℝ)) ((continuous_phase γ).intervalIntegrable (n:ℝ) (n+1))]
      have hlast : (∫ x in (n:ℝ)..(n:ℝ)+1, phase γ x) = phase γ n * A := by
        calc
          _ = ∫ x in (0:ℝ)..1, phase γ ((n:ℝ)+x) := by rw [intervalIntegral.integral_comp_add_left]; simp
          _ = _ := by
            rw [show phase γ n * A = ∫ x in (0:ℝ)..1, phase γ n * phase γ x from (intervalIntegral.integral_const_mul _ _).symm]
            apply intervalIntegral.integral_congr
            intro x _
            simp only [phase, mul_add, ofReal_add, add_mul, Complex.exp_add]
      rw [ih, hlast]
      simp only [geometricSum, Finset.sum_range_succ, hgeo, add_mul]
  have hplus : positiveGeometricSum X β = geometricSum (X+1) β - 1 := by
    have he : Finset.range (X+1) = insert 0 (Finset.Icc 1 X) := by
      ext n; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
    simp [positiveGeometricSum, geometricSum, he, geometricPhase]
  have hsharp : sharpPower (X+1 : ℕ) γ 1 = geometricSum (X+1) β * A := by
    simpa only [sharpPower, density, sub_self, Complex.cpow_zero, mul_one] using hsum (X+1)
  have hdiff : ‖1-A‖ ≤ |γ| := by
    have he : (1:ℂ)-A = ∫ x in (0:ℝ)..1, 1 - phase γ x := by
      rw [intervalIntegral.integral_sub intervalIntegrable_const ((continuous_phase γ).intervalIntegrable 0 1)]
      simp [A]
    rw [he]
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := 1)
      (C := |γ|) (f := fun x => (1:ℂ)-phase γ x) (fun x hx => by
        rw [uIoc_of_le zero_le_one] at hx
        rw [norm_sub_rev]
        have he := Real.norm_exp_I_mul_ofReal_sub_one_le (x := γ*x)
        rw [mul_comm I] at he
        apply he.trans
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg γ) (by simpa only [abs_of_pos hx.1] using hx.2))
    simpa using h
  change ‖positiveGeometricSum X β - sharpPower (X+1 : ℕ) γ 1‖ ≤ _
  rw [hplus, hsharp, show geometricSum (X+1) β - 1 - geometricSum (X+1) β*A =
    geometricSum (X+1) β*(1-A)-1 by ring]
  calc
    _ ≤ ‖geometricSum (X+1) β * (1-A)‖ + ‖(1:ℂ)‖ := norm_sub_le ..
    _ ≤ _ := by
      rw [norm_mul, norm_one]
      have hh := mul_le_mul_of_nonneg_left hdiff (norm_nonneg (geometricSum (X+1) β))
      have hm := mul_le_mul_of_nonneg_left (abs_mul_norm_geometricSum_le_half (X+1) hβ) (show 0 ≤ 2*Real.pi by positivity)
      dsimp only [γ] at hh
      rw [abs_mul, abs_of_pos (by positivity : 0 < 2*Real.pi)] at hh
      linarith only [hh, hm]

end GoldbachTwistedMellin
end
end

section
open Set Complex MeasureTheory DeepThreeQuarters
open scoped Interval Topology
noncomputable section
namespace GoldbachTwistedMellin

/-- The pole contributes the integer geometric sum. Each Dirichlet zero
contributes its own effective window, with the sign carried by its residue. -/
def residueProfile (m : ℕ) (z : Option ℂ) (u : ℝ) : ℂ :=
  match z with
  | none => positiveGeometricSum (m+2) u
  | some s => zeroPowerProfile m (2*Real.pi*u) s

def residueEndpointError : Option ℂ → ℝ
  | none => 1 + Real.pi
  | some s => 2 + 2*max 3 |s.im|

theorem continuous_residueProfile (m : ℕ) (z : Option ℂ) : Continuous (residueProfile m z) := by
  cases z with
  | none =>
    unfold residueProfile positiveGeometricSum
    exact continuous_finsetSum _ (fun _ _ => by unfold geometricPhase; fun_prop)
  | some s =>
    obtain ⟨ha, hb, _⟩ := zeroWindowStart_bounds m s.im
    by_cases h : zeroWindowStart m s.im = m+2
    · have he : residueProfile m (some s) = fun _ : ℝ => (0:ℂ) := by
        funext u
        simp only [residueProfile, zeroPowerProfile, h, sub_self]
      rw [he]
      exact continuous_const
    · have hr : ((zeroWindowStart m s.im : ℕ):ℝ)+1 ≤ ((m+2 : ℕ):ℝ) := by
        exact_mod_cast (show zeroWindowStart m s.im + 1 ≤ m+2 by omega)
      have ha1 : (1:ℝ) ≤ zeroWindowStart m s.im := by exact_mod_cast (show 1 ≤ zeroWindowStart m s.im by omega)
      have e := continuous_transform_frequency (zero_lt_one.trans_le ha1) hr s
      exact (e.comp (show Continuous (fun u : ℝ => 2*Real.pi*u) by fun_prop)).congr
        (fun u => transform_eq_windowEndpoints ha1 hr _ _)

theorem residueProfile_sharpPower (m : ℕ) (z : Option ℂ) {u : ℝ} (hu : |u| ≤ 1/2)
    (hlo : 1/2 ≤ (z.getD 1).re) (hhi : (z.getD 1).re ≤ 1) :
    ‖residueProfile m z u - sharpPower (m+3 : ℕ) (2*Real.pi*u) (z.getD 1)‖ ≤ residueEndpointError z := by
  cases z with
  | none => exact principalProfile_sharpPower (m+2) hu
  | some s => exact zeroPowerProfile_error m _ hlo hhi

/-- Finite-arc coefficient of any pair of actual residues, including a mixed
pole and zero. The first loss is from the endpoints. The second is the
integrated Fourier tail of the sharp power profiles. -/
theorem residuePair_arc_beta (m : ℕ) (z z' : Option ℂ) {n w : ℝ} (hn : 0 < n)
    (hnB : n < (m+3 : ℕ)) (hw : 0 < w) (hw' : w ≤ 1/2)
    (hs : 1/2 ≤ (z.getD 1).re) (hs' : (z.getD 1).re ≤ 1)
    (ht : 1/2 ≤ (z'.getD 1).re) (ht' : (z'.getD 1).re ≤ 1)
    (hsum : 1 < (z.getD 1).re + (z'.getD 1).re) :
    let s := z.getD 1
    let t := z'.getD 1
    let B : ℝ := (m+3 : ℕ)
    let A := residueEndpointError z
    let A' := residueEndpointError z'
    ‖(∫ u in -w..w, phase (-2*Real.pi*n) u * (residueProfile m z u * residueProfile m z' u)) -
      (n:ℂ)^(s+t-1)*Complex.betaIntegral s t‖ ≤
      2*w*(A*(2*B+A') + 2*B*A') +
        2*(sharpDecayConstant s*sharpDecayConstant t)*w^(1-(s.re+t.re))/(s.re+t.re-1) := by
  intro s t B A A'
  let J (v : ℂ) (u : ℝ) := sharpPower B (2*Real.pi*u) v
  let H (u : ℝ) := phase (-2*Real.pi*n) u
  let F (u : ℝ) := H u*(residueProfile m z u*residueProfile m z' u)
  let G (u : ℝ) := H u*(J s u * J t u)
  have hB : 1 ≤ B := by dsimp only [B]; exact_mod_cast (show 1 ≤ m+3 by omega)
  have hs0 : 0 < s.re := by change 0 < (z.getD 1).re; linarith
  have ht0 : 0 < t.re := by change 0 < (z'.getD 1).re; linarith
  have hJ (v : ℂ) (hlo : 1/2 ≤ v.re) (hhi : v.re ≤ 1) (u : ℝ) : ‖J v u‖ ≤ 2*B := by
    have hv : 0 < v.re := by linarith
    apply (sharpPower_norm _ hv (zero_le_one.trans hB)).trans
    apply (div_le_iff₀ hv).mpr
    have hp : B^v.re ≤ B := by simpa using Real.rpow_le_rpow_of_exponent_le hB hhi
    exact hp.trans (by nlinarith only [mul_le_mul_of_nonneg_left hlo (zero_le_one.trans hB)])
  have hA : 0 ≤ A := (norm_nonneg _).trans (residueProfile_sharpPower m z (u := 0) (by norm_num) hs hs')
  have hF : Continuous F := (continuous_phase _).mul ((continuous_residueProfile m z).mul (continuous_residueProfile m z'))
  have hG : Continuous G := (continuous_phase _).mul ((continuous_sharpPowerFreq (zero_le_one.trans hB) hs0).mul
    (continuous_sharpPowerFreq (zero_le_one.trans hB) ht0))
  have err : ‖(∫ u in -w..w, F u) - (∫ u in -w..w, G u)‖ ≤ 2*w*(A*(2*B+A') + 2*B*A') := by
    rw [← intervalIntegral.integral_sub (hF.intervalIntegrable ..) (hG.intervalIntegrable ..)]
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := -w) (b := w)
      (C := A*(2*B+A') + 2*B*A') (f := fun u => F u-G u) (fun u hu => by
        rw [uIoc_of_le (by linarith)] at hu
        have hu' := (abs_le.mpr ⟨hu.1.le, hu.2⟩).trans hw'
        have ez := residueProfile_sharpPower m z hu' hs hs'
        have ez' := residueProfile_sharpPower m z' hu' ht ht'
        have mz : ‖residueProfile m z' u‖ ≤ 2*B+A' :=
          (norm_le_norm_add_norm_sub' (residueProfile m z' u) (J t u)).trans (add_le_add (hJ t ht ht' u) ez')
        change ‖H u * _ - H u * _‖ ≤ _
        rw [← mul_sub, norm_mul, show ‖H u‖ = 1 from norm_phase _ _, one_mul]
        rw [show residueProfile m z u * residueProfile m z' u - J s u * J t u =
          (residueProfile m z u-J s u)*residueProfile m z' u + J s u*(residueProfile m z' u-J t u) by ring]
        apply (norm_add_le ..).trans
        simp only [norm_mul]
        exact add_le_add (mul_le_mul ez mz (norm_nonneg _) hA)
          (mul_le_mul (hJ s hs hs' u) ez' (norm_nonneg _) (by positivity)))
    rw [abs_of_nonneg (by linarith : 0 ≤ w - -w)] at h
    convert h using 1
    ring
  have hβ := sharpPair_arc_beta hn hnB hw hs hs' ht ht' hsum
  exact (norm_sub_le_norm_sub_add_norm_sub (∫ u in -w..w, F u) (∫ u in -w..w, G u) _).trans
    (add_le_add err hβ)

end GoldbachTwistedMellin
end
end

section
open Complex MeasureTheory
open scoped Interval
noncomputable section
namespace GoldbachTwistedMellin

/-- On bounded-height residues, each local integral has error at most a
constant times `w*X + 1/w`. In particular it can be summed uniformly on
the denominators well below the arc cutoff. -/
theorem residuePair_arc_uniform {T : ℝ} (hT : 0 ≤ T) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (z t : Option ℂ) (n w : ℝ),
      0 < n → n < (m+3 : ℕ) → 0 < w → w ≤ 1/2 →
      5/8 ≤ (z.getD 1).re → (z.getD 1).re ≤ 1 → |(z.getD 1).im| ≤ T →
      5/8 ≤ (t.getD 1).re → (t.getD 1).re ≤ 1 → |(t.getD 1).im| ≤ T →
      ‖(∫ u in -w..w, phase (-2*Real.pi*n) u * (residueProfile m z u * residueProfile m t u)) -
        (n:ℂ)^((z.getD 1)+(t.getD 1)-1)*Complex.betaIntegral (z.getD 1) (t.getD 1)‖
        ≤ C * (w*(m+3 : ℕ) + 1/w) := by
  let E := 10+2*T
  let D := 4+(1+T)*(4+T)
  let A := E*(2+E)+2*E
  let C := 2*A + 8*(D*D)
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro m z t n w hn hb hw hw1 hs hs1 his ht ht1 hit
  have eBound (v : Option ℂ) (hi : |(v.getD 1).im| ≤ T) :
      0 ≤ residueEndpointError v ∧ residueEndpointError v ≤ E := by
    cases v with
    | none => exact ⟨by unfold residueEndpointError; positivity, by unfold residueEndpointError E; linarith [Real.pi_lt_four]⟩
    | some x =>
      change |x.im| ≤ T at hi
      have hm : max 3 |x.im| ≤ 3+T := max_le (by linarith) (by linarith)
      exact ⟨by unfold residueEndpointError; positivity, by unfold residueEndpointError E; linarith only [hm]⟩
  have dBound (v : ℂ) (hl : 5/8 ≤ v.re) (hh : v.re ≤ 1) (hi : |v.im| ≤ T) :
      0 ≤ sharpDecayConstant v ∧ sharpDecayConstant v ≤ D := by
    have h1 : ‖v-1‖ ≤ 1+T := by
      apply (Complex.norm_le_abs_re_add_abs_im _).trans
      simp only [sub_re, one_re, sub_im, one_im, sub_zero, abs_of_nonpos (sub_nonpos.mpr hh)]
      linarith
    have h2 : ‖v-2‖ ≤ 2+T := by
      apply (Complex.norm_le_abs_re_add_abs_im _).trans
      rw [sub_re, sub_im]
      norm_num
      rw [abs_of_nonpos (by linarith : v.re-2 ≤ 0)]
      linarith
    constructor
    · unfold sharpDecayConstant; positivity
    · unfold sharpDecayConstant D
      apply add_le_add_right
      exact mul_le_mul h1 (by linarith only [h2]) (by positivity) (by positivity)
  obtain ⟨e, ez⟩ := eBound z his
  obtain ⟨e', et⟩ := eBound t hit
  obtain ⟨d, dz⟩ := dBound _ hs hs1 his
  obtain ⟨d', dt⟩ := dBound _ ht ht1 hit
  let B : ℝ := (m+3 : ℕ)
  let r := (z.getD 1).re+(t.getD 1).re
  have hB : 1 ≤ B := by dsimp only [B]; exact_mod_cast (show 1 ≤ m+3 by omega)
  have hB0 := zero_le_one.trans hB
  have hr : (5/4:ℝ) ≤ r := by dsimp only [r]; linarith only [hs,ht]
  have hr2 : r ≤ 2 := by dsimp only [r]; linarith only [hs1,ht1]
  have hw2 : w^(1-r) ≤ 1/w := by
    rw [one_div, ← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_ge hw (by linarith only [hw1]) (by linarith only [hr2])
  have hE' : residueEndpointError t ≤ B*E := et.trans (le_mul_of_one_le_left hE hB)
  have hfirst : residueEndpointError z*(2*B+residueEndpointError t) + 2*B*residueEndpointError t ≤ A*B := calc
    _ ≤ E*(2*B+B*E)+2*B*E := add_le_add (mul_le_mul ez (add_le_add_right hE' _) (by positivity) hE)
      (mul_le_mul_of_nonneg_left et (by positivity))
    _ = _ := by dsimp only [A]; ring
  have hsecond : 2*(sharpDecayConstant (z.getD 1)*sharpDecayConstant (t.getD 1))*w^(1-r)/(r-1)
      ≤ 8*(D*D)*(1/w) := by
    apply (div_le_iff₀ (by linarith only [hr] : 0 < r-1)).mpr
    have hweight : 0 ≤ 2*(D*D)*(1/w) := by positivity
    calc
      _ ≤ 2*(D*D)*(1/w) := mul_le_mul
        (mul_le_mul_of_nonneg_left (mul_le_mul dz dt d' hD.le) (by norm_num)) hw2
        (Real.rpow_nonneg hw.le _) (by positivity)
      _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_left (show 1 ≤ 4*(r-1) by linarith only [hr]) hweight]
  have main := residuePair_arc_beta m z t hn hb hw hw1 (by linarith only [hs]) hs1
    (by linarith only [ht]) ht1 (by change 1 < r; linarith only [hr])
  apply main.trans
  apply (add_le_add (mul_le_mul_of_nonneg_left hfirst (by positivity : 0 ≤ 2*w)) hsecond).trans
  change 2*w*(A*B)+8*(D*D)*(1/w) ≤ C*(w*B+1/w)
  dsimp only [C]
  nlinarith only [show 0 ≤ A*(1/w) by positivity, show 0 ≤ (D*D)*(w*B) by positivity]

end GoldbachTwistedMellin
end
end

section
open Set Complex Goldbach GoldbachSmoothing GoldbachGRHWindow DeepThreeQuarters
noncomputable section
namespace GoldbachTwistedMellin

/-- Signed sum of the exceptional Dirichlet zeros with a deterministic height
on each dyadic block and the finite Fourier weights of the rational phase. -/
noncomputable def canonicalCorrection {q : ℕ} [NeZero q] (n : ℕ) (v : ZMod q) (β : ℝ) : ℂ :=
  ((prefixBlocks (n-2)).map fun p => ∑ χ : DirichletCharacter ℂ q,additiveWeight v χ *
    fixedZeroTerm χ p.1 p.2 p.1 (2*Real.pi*β)).sum

/-- Uniform rational approximation on the required major arcs.
The signed correction uses the zeros with real part greater than 5/8. -/
theorem rational_canonical_model :
    ∃ K : ℝ, 0<K ∧ ∀ n : ℕ, 64≤n → ∀ (a q : ℕ) [NeZero q], a.Coprime q →
      (q:ℝ) ≤ (n:ℝ)^(3/10 : ℝ) → ∀ β : ℝ, |β| ≤ (n:ℝ)^(3/10 : ℝ)/((q:ℝ)*(n:ℝ)) →
      ‖weightedSum n primeWeight ((a:ℝ)/q+β) - rationalModel n q β + canonicalCorrection n (a:ZMod q) β‖ ≤
        K*(n:ℝ)^(31/40 : ℝ)*logScale n^4 := by
  classical
  obtain ⟨C,hC,model⟩ := fixed_dyadic_model
  refine ⟨3*(12+1700*C),by positivity,?_⟩
  intro n hn a q _ hc hqs β hβ
  have hn1 : 1 ≤ n := by omega
  have hq : 1 ≤ q := NeZero.pos q
  have hnR : 1 ≤ (n:ℝ) := by exact_mod_cast hn1
  let γ := 2*Real.pi*β
  obtain ⟨hγ,hγq,hγWindow⟩ := angular_range hn hq hβ
  let pairs := prefixBlocks (n-2)
  let S := (n:ℝ)^(31/40 : ℝ)
  let L := logScale n
  let D := (12+1700*C)*S*L^3
  have hL : 1 ≤ L := logScale_one hnR
  have hS : 1 ≤ S := Real.one_le_rpow hnR (by norm_num)
  have hD : 12 ≤ D := by
    dsimp [D]
    calc
      (12:ℝ) ≤ (12+1700*C)*1*1 := by linarith
      _ ≤ _ := by gcongr;exact one_le_pow₀ hL
  have geom (p : ℕ×ℕ) (hp : p ∈ pairs) : 1≤p.1 ∧ p.1+1≤p.2 ∧ p.2+1≤2*p.1 ∧ p.2≤n := by
    have := prefixBlocks_valid hp
    simpa [Nat.sub_add_cancel (show 2≤n by omega)] using this
  let z := fun p : ℕ×ℕ => ∑ χ : DirichletCharacter ℂ q, additiveWeight (a:ZMod q) χ *
    fixedZeroTerm χ p.1 p.2 p.1 γ
  have pre := dyadic_prefix_corrected (primeError (a:ZMod q) γ) z n (by omega) D
    (fun j hj => (primeError_small _ _ _ hj).trans hD) (fun p hp => by
      obtain ⟨hl,hlr,hr,hrn⟩ := geom p hp
      have hp₁ : (p.1:ℝ) ≤ n := by exact_mod_cast (show p.1 ≤ n by omega)
      have hWindow : |γ|^2*(p.1:ℝ) ≤ 64 :=
        (mul_le_mul_of_nonneg_left hp₁ (sq_nonneg _)).trans hγWindow
      exact signed_block_budget (a:ZMod q) hn1 hl hlr hrn hC.le hqs hγq
        (fun χ => fixedZeroTerm χ p.1 p.2 p.1 γ) (fun χ =>
          model q χ p.1 p.2 p.1 γ (by exact_mod_cast hl) le_rfl (by exact_mod_cast hlr) (by exact_mod_cast hr)
            hγ hWindow))
  change ‖(∑ k ∈ Finset.Ioc 0 n,primeError (a:ZMod q) (2*Real.pi*β) k) + canonicalCorrection n (a:ZMod q) β‖ ≤ _ at pre
  rw [primeError_prefix_eq a n hc β] at pre
  exact pre.trans ((mul_le_mul_of_nonneg_right (dyadic_count_le (by omega : 4≤n)) (by linarith : 0≤D)).trans_eq
    (by dsimp [D,S,L];ring))
end GoldbachTwistedMellin
end
end

section
open Finset Real Complex Goldbach DeepThreeQuarters Filter
noncomputable section
namespace GoldbachTwistedMellin

theorem quartic_log_scale {e : ℝ} (he : 0 < e) :
    ∃ D : ℝ, 0 < D ∧ ∀ x : ℝ, 1 ≤ x → logScale x^4 ≤ D*x^e := by
  let u := e/4
  have hu : 0 < u := by dsimp [u]; positivity
  let c := 1+Real.log 2+1/u
  have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨c^4,by positivity,?_⟩
  intro x hx
  have hx0 := zero_lt_one.trans_le hx
  have hXu := Real.one_le_rpow hx hu.le
  have hlog := Real.log_le_rpow_div hx0.le hu
  have h : logScale x ≤ c*x^u := by
    rw [logScale,Real.log_mul (by norm_num) hx0.ne']
    dsimp [c]
    rw [one_div]
    rw [div_eq_mul_inv] at hlog
    nlinarith only [hlog,mul_le_mul_of_nonneg_left hXu (by linarith : 0 ≤ 1+Real.log 2)]
  refine (pow_le_pow_left₀ (zero_le_one.trans (logScale_one hx)) h 4).trans_eq ?_
  rw [mul_pow,←Real.rpow_mul_natCast hx0.le]
  have hu3 : u*(4:ℕ) = e := by dsimp [u]; ring
  rw [hu3]

end GoldbachTwistedMellin
end
end

end

-- The local logarithmic derivative estimates, the quadratic conjugation
-- argument and the 3,4,1 inequality are adapted from zxg0623, PR #3782,
-- revision 66b7bb6fba35f86bd59c3d4916fe1a72ee3a2bdf (Apache-2.0).
-- https://github.com/CGandGameEngineLearner/goldbach-proofs/pull/3782

namespace Conjectures.Goldbach.ExceptionalZeroCatalogue

open Complex Set Filter DirichletCharacter
open scoped Topology Classical

noncomputable def regular {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r) : ℂ → ℂ :=
  if χ=1 then LFunctionTrivChar₁ r else LFunction χ

def genuine {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r) (z : ℂ) : Prop :=
  (χ ≠ 1 ∨ z ≠ 1) ∧ LFunction χ z=0

theorem differentiable_regular {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r) :
    Differentiable ℂ (regular χ) := by
  by_cases h : χ=1
  · rw [regular,ite_eq_left h]
    exact differentiable_LFunctionTrivChar₁ r
  · rw [regular,ite_eq_right h]
    exact differentiable_LFunction h

theorem regular_zero {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r) (z : ℂ) :
    regular χ z=0 ↔ genuine χ z := by
  classical
  by_cases h : χ=1
  · subst χ
    rw [regular,ite_eq_left rfl]
    by_cases atone : z=1
    · subst z
      exact iff_of_false (LFunctionTrivChar₁_apply_one_ne_zero r) (by simp [genuine])
    · rw [LFunctionTrivChar₁,Function.update_of_ne atone]
      simp [genuine,atone,sub_ne_zero.mpr atone,LFunctionTrivChar]
  · simp [regular,h,genuine]

theorem regular_ne {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r) (z : ℂ)
    (h : 1 ≤ z.re) : regular χ z ≠ 0 := by
  intro H
  obtain ⟨ok,zero⟩ := (regular_zero χ z).mp H
  exact LFunction_ne_zero_of_one_le_re χ ok h zero

theorem order_positive {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r) {z : ℂ} (h : genuine χ z) :
    0 < analyticOrderNatAt (regular χ) z ∧
      analyticOrderAt (regular χ) z=(analyticOrderNatAt (regular χ) z : ℕ∞) := by
  have A (w : ℂ) := (differentiable_regular χ).analyticAt w
  have fne : regular χ ≠ 0 := fun eqn => regular_ne χ 1 (by simp) (congrFun eqn 1)
  have finite := mt (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero z A).mp fne
  have val := Nat.cast_analyticOrderNatAt finite
  refine ⟨?_,val.symm⟩
  by_contra! hz
  have top : analyticOrderAt (regular χ) z=0 := by rw [← val,show analyticOrderNatAt (regular χ) z=0 by omega]; rfl
  exact ((A z).analyticOrderAt_eq_zero.mp top) ((regular_zero χ z).mpr h)

/-- One open neighborhood works simultaneously for every character at
every positive modulus up to R, including the regularized principals. -/
theorem bounded_strip (R : ℕ) (T : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (r : ℕ) [NeZero r], r ≤ R → ∀ (χ : DirichletCharacter ℂ r) (z : ℂ),
      |z.im| ≤ T → 1-δ ≤ z.re → ¬genuine χ z := by
  classical
  let U : Set ℂ := ⋂ (k : Fin R) (χ : DirichletCharacter ℂ (k.val+1)), (regular χ) ⁻¹' ({0} : Set ℂ)ᶜ
  have hu : IsOpen U := isOpen_iInter_of_finite (fun k => isOpen_iInter_of_finite (fun χ =>
    isClosed_singleton.isOpen_compl.preimage (differentiable_regular χ).continuous))
  let v (t : ℝ) := (1:ℂ)+(t:ℂ)*I
  let line := v '' Icc (-T) T
  have comp : IsCompact line := isCompact_Icc.image (by dsimp [v]; fun_prop)
  have sub : line ⊆ U := by
    rintro z ⟨t,_,rfl⟩
    refine mem_iInter.mpr fun k => mem_iInter.mpr fun χ => ?_
    exact regular_ne χ _ (by simp [v])
  obtain ⟨δ,hd,inside⟩ := comp.exists_cthickening_subset_open hu sub
  refine ⟨δ,hd,?_⟩
  intro r _ hr χ z ht hz
  by_cases right : 1 ≤ z.re
  · exact mt (regular_zero χ z).mpr (regular_ne χ z right)
  have imag : v z.im ∈ line := ⟨z.im,abs_le.mp ht,rfl⟩
  have E : z-v z.im=((z.re-1:ℝ):ℂ) := by apply Complex.ext <;> simp [v]
  have dist : dist z (v z.im) ≤ δ := by
    rw [dist_eq_norm,E,Complex.norm_real,Real.norm_eq_abs,abs_of_nonpos (by linarith)]
    linarith
  have u := inside (Metric.mem_cthickening_of_dist_le z (v z.im) δ line imag dist)
  cases r with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n =>
    let i : Fin R := ⟨n,by omega⟩
    have H : regular χ z ≠ 0 := mem_iInter.mp (mem_iInter.mp u i) χ
    exact mt (regular_zero χ z).mpr H
end Conjectures.Goldbach.ExceptionalZeroCatalogue

namespace Conjectures.Goldbach.NearOneZeroMultiplicity

open Complex DirichletCharacter Metric Set Filter
open _root_.Goldbach GoldbachSmoothing
open scoped Classical Topology

theorem right_majorant {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    ‖logDeriv (LFunction χ) (⟨σ,t⟩ : ℂ)‖ ≤ (-logDeriv riemannZeta (σ:ℂ)).re := by
  let f : ℕ → ℂ := fun n => (ArithmeticFunction.vonMangoldt n : ℂ)
  let s : ℂ := ⟨σ,t⟩
  have hf : Summable (LSeries.term f (σ:ℂ)) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hσ)
  have hm (n : ℕ) : ‖LSeries.term (twistedCoefficient χ) s n‖ ≤ ‖LSeries.term f (σ:ℂ) n‖ := by
    rw [show ‖LSeries.term f (σ:ℂ) n‖ = ‖LSeries.term f s n‖ by simp [LSeries.norm_term_eq,s]]
    apply LSeries.norm_term_le
    change ‖χ (n:ZMod q)*(ArithmeticFunction.vonMangoldt n:ℂ)‖ ≤ ‖(ArithmeticFunction.vonMangoldt n:ℂ)‖
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one _)
  have hn := hf.norm.of_nonneg_of_le (fun _ => norm_nonneg _) hm
  have real_term (n : ℕ) : (LSeries.term f (σ:ℂ) n).re = ‖LSeries.term f (σ:ℂ) n‖ := by
    open scoped ComplexOrder in
    have nonneg := LSeries.term_nonneg (a:=f) (n:=n)
      (show 0 ≤ f n from Complex.zero_le_real.mpr ArithmeticFunction.vonMangoldt_nonneg) σ
    exact congrArg Complex.re (Complex.eq_coe_norm_of_nonneg nonneg)
  have hzeta : LSeries f (σ:ℂ) = -logDeriv riemannZeta (σ:ℂ) := by
    simpa [logDeriv, neg_div] using
      (ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (s:=(σ:ℂ)) (by simpa using hσ))
  calc
    _ = ‖LSeries (twistedCoefficient χ) s‖ := by
      rw [LSeries_twistedCoefficient_eq χ (show 1<s.re from hσ),norm_neg]
    _ ≤ ∑' n, ‖LSeries.term f (σ:ℂ) n‖ := (norm_tsum_le_tsum_norm hn).trans (hn.tsum_le_tsum hm hf.norm)
    _ = (LSeries f (σ:ℂ)).re := by rw [LSeries,Complex.re_tsum hf]; simp_rw [real_term]
    _ = _ := congrArg Complex.re hzeta

/-- Isolate the pole of zeta on the whole real segment [1,2]. -/
theorem right_edge :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
      (η t : ℝ), 0 < η → η ≤ 1 →
        ‖logDeriv (LFunction χ) (⟨1+η,t⟩ : ℂ)‖ ≤ 1/η + D := by
  let P : DirichletCharacter ℂ 1 := 1
  let f := regularizedL P
  have analytic (z : ℂ) := analytic_regularizedL P z (mem_univ z)
  have cont : ContinuousOn (fun x : ℝ => ‖logDeriv f (x:ℂ)‖) (Icc 1 2) := by
    intro x hx
    have ne : f (x:ℂ) ≠ 0 := ExceptionalZeroCatalogue.regular_ne P _ hx.1
    have c := (analytic _).deriv.continuousAt.div (analytic _).continuousAt ne
    exact (c.comp (Complex.continuous_ofReal.continuousAt)).norm.continuousWithinAt
  obtain ⟨D,hD⟩ := isCompact_Icc.bddAbove_image cont
  refine ⟨max D 0,le_max_right _ _,?_⟩
  intro q _ χ η t hη hη'
  let x := 1+η
  have hx : 1<x := by dsimp [x]; linarith
  have hxc : (x:ℂ) ≠ 1 := by exact_mod_cast hx.ne'
  have hζ : LFunction P (x:ℂ) ≠ 0 := LFunction_ne_zero_of_one_le_re P (Or.inr hxc) hx.le
  have eqn := logDeriv_regularizedL_eq P hxc hζ
  have eqn' : -logDeriv riemannZeta (x:ℂ) = ((1/η:ℝ):ℂ)-logDeriv f (x:ℂ) := by
    rw [LFunction_modOne_eq] at eqn
    have sub : (x:ℂ)-1=(η:ℂ) := by simp [x]
    simpa [f,P,principalFlag,sub] using (show -logDeriv riemannZeta (x:ℂ) =
      principalFlag P / ((x:ℂ)-1)-logDeriv (regularizedL P) (x:ℂ) by rw [eqn]; ring)
  have H := hD (mem_image_of_mem (fun u : ℝ => ‖logDeriv f (u:ℂ)‖)
    (show x ∈ Icc 1 2 from ⟨hx.le,by dsimp [x];linarith⟩))
  refine (right_majorant χ hx t).trans ?_
  rw [eqn',sub_re,ofReal_re]
  linarith [neg_le_abs (logDeriv f (x:ℂ)).re,abs_re_le_norm (logDeriv f (x:ℂ)),le_max_left D 0]

/-- The regularized logarithmic derivative and all zeros in the disk
of radius 33/25 have an error at most 694400 times the log-height. -/
theorem local_expansion {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ) :
    ∃ Z : Finset ℂ, (∀ z, z ∈ Z ↔ z ∈ closedBall (⟨2,t⟩:ℂ) (33/25) ∧
        ExceptionalZeroCatalogue.genuine χ z) ∧
      ∀ η : ℝ, 0 < η → η ≤ 1 → let s : ℂ := ⟨1+η,t⟩
        ‖logDeriv (regularizedL χ) s - ∑ z ∈ Z, (analyticOrderNatAt (regularizedL χ) z : ℂ)/(s-z)‖
          ≤ 694400 * logHeight q t := by
  let f := regularizedL χ
  let c : ℂ := ⟨2,t⟩
  let H := 2*(q:ℝ)*(2+|t|)
  have hq : (1:ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have ht := abs_nonneg t
  have hK : 2+|t| ≤ H := by dsimp [H]; nlinarith [mul_nonneg (sub_nonneg.mpr hq) (by positivity : 0≤2+|t|)]
  have hH : 4 ≤ H := by dsimp [H]; nlinarith [mul_nonneg (by positivity : 0 ≤ (q:ℝ)) ht]
  have hqH : (q:ℝ) ≤ H := by dsimp [H]; nlinarith [mul_nonneg (by positivity : 0 ≤ (q:ℝ)) ht]
  have hpos : 0 < H := by linarith
  have hAnchor : (1/4:ℝ) ≤ ‖f c‖ := norm_regularizedL_anchor χ t
  have hn : f c ≠ 0 := norm_pos_iff.mp (by linarith)
  have growth (w : ℂ) (hw : w ∈ closedBall c (24/25*(3/2))) : ‖f w‖ ≤ H^8 * ‖f c‖ := by
    have dist := mem_closedBall_iff_norm.mp hw
    have hre := abs_le.mp ((abs_re_le_norm (w-c)).trans dist)
    change -_ ≤ w.re-2 ∧ _ at hre
    have hr : (1/8:ℝ) ≤ w.re := by linarith [hre.1]
    have hg := GoldbachGrhGrowth.norm_regularizedLFunction_le χ hr
    have hraw : ‖f w‖ ≤ 25*q*(1+‖w‖)^2 := by
      by_cases hχ : χ=1 <;> simpa [f,regularizedL,hχ] using hg
    have hcn : ‖c‖ ≤ 2+|t| := by simpa [c] using norm_le_abs_re_add_abs_im c
    have hwH : 1+‖w‖ ≤ 3*H := by linarith only [norm_le_norm_sub_add w c,dist,hcn,hK,hH]
    have h5 : (4:ℝ)^5 ≤ H^5 := pow_le_pow_left₀ (by norm_num) hH 5
    calc
      _ ≤ 25*q*(1+‖w‖)^2 := hraw
      _ ≤ 25*H*(3*H)^2 := by gcongr
      _ = 225*H^3 := by ring
      _ ≤ (H^5/4)*H^3 := mul_le_mul_of_nonneg_right (by norm_num at h5;linarith) (by positivity)
      _ = H^8*(1/4) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hAnchor (by positivity)
  obtain ⟨Z,hZ,_,approx⟩ := GoldbachGrhLogDerivative.logDeriv_partial_fraction_disk
    (c:=c) (R:=(3/2:ℝ)) (f:=f) (B:=H^8) (by norm_num)
    ((analytic_regularizedL χ).mono (subset_univ _)) hn
    (le_trans (by norm_num : (2:ℝ)≤4^8) (pow_le_pow_left₀ (by norm_num) hH 8)) growth
  refine ⟨Z,?_,?_⟩
  · intro z
    change z ∈ (↑Z : Set ℂ) ↔ _
    rw [hZ]
    change (_ ∧ f z=0) ↔ _
    rw [show (22/25*(3/2):ℝ)=33/25 by norm_num]
    exact and_congr_right fun _ => ExceptionalZeroCatalogue.regular_zero χ z
  · intro η hη hη'
    let s : ℂ := ⟨1+η,t⟩
    have sub : s-c=((η-1:ℝ):ℂ) := by
      apply Complex.ext <;> simp [s,c]
      ring
    have mem : s ∈ closedBall c (83/100*(3/2)) := by
      rw [mem_closedBall_iff_norm,sub,Complex.norm_real,Real.norm_eq_abs,abs_of_nonpos (by linarith)]
      linarith
    have hs : f s ≠ 0 := ExceptionalZeroCatalogue.regular_ne χ s (by change 1≤1+η;linarith)
    have h := approx s mem hs
    rw [Real.log_pow] at h
    change _ ≤ 694400 * Real.log H
    convert h using 1
    norm_num
    ring

noncomputable def kernel (s z : ℂ) : ℝ := (s-z).re / Complex.normSq (s-z)

theorem kernel_eq (s z : ℂ) (n : ℕ) :
    ((n:ℂ)/(s-z)).re = n*kernel s z := by
  simp [kernel,Complex.div_re,mul_div_assoc]

theorem disk_potential :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
      (t η : ℝ), 0 < η → η ≤ 1 → ∀ S : Finset ℂ,
        (∀ z ∈ S, z ∈ closedBall (⟨2,t⟩:ℂ) (33/25) ∧ ExceptionalZeroCatalogue.genuine χ z) →
        let s : ℂ := ⟨1+η,t⟩
        ∑ z ∈ S, (analyticOrderNatAt (regularizedL χ) z : ℝ)*kernel s z ≤
          (logDeriv (LFunction χ) s).re + (principalFlag χ/(s-1)).re + 694400*logHeight q t ∧
        ∑ z ∈ S, (analyticOrderNatAt (regularizedL χ) z : ℝ)*kernel s z ≤
          2/η + D + 694400*logHeight q t := by
  obtain ⟨D,hD,right⟩ := right_edge
  refine ⟨D,hD,?_⟩
  intro q _ χ t η hη hη' S hS s
  obtain ⟨Z,mem,apr⟩ := local_expansion χ t
  have hs : 1<s.re := by change 1<1+η;linarith
  have hn : s ≠ 1 := by intro e; simp [e] at hs
  have hL := LFunction_ne_zero_of_one_le_re χ (Or.inr hn) hs.le
  let weight := fun z => (analyticOrderNatAt (regularizedL χ) z : ℝ)*kernel s z
  have sub : S ⊆ Z := fun z hz => (mem z).mpr (hS z hz)
  have hw (z : ℂ) (hz : z ∈ Z) : 0 ≤ weight z := by
    have h := ((mem z).mp hz).2
    have hzre : z.re < 1 := lt_of_not_ge fun e => ExceptionalZeroCatalogue.regular_ne χ z e
      ((ExceptionalZeroCatalogue.regular_zero χ z).mpr h)
    exact mul_nonneg (Nat.cast_nonneg _) (div_nonneg (sub_nonneg.mpr (hzre.trans hs).le) (normSq_nonneg _))
  have cmp : ∑ z ∈ S, weight z ≤ ∑ z ∈ Z, weight z :=
    Finset.sum_le_sum_of_subset_of_nonneg sub fun z hz _ => hw z hz
  let total : ℂ := ∑ z ∈ Z, (analyticOrderNatAt (regularizedL χ) z : ℂ)/(s-z)
  have reTot : total.re = ∑ z ∈ Z, weight z := by simp [total,Complex.re_sum,kernel_eq,weight]
  have major := abs_re_le_norm (logDeriv (regularizedL χ) s-total)
  have below := (abs_le.mp (major.trans (apr η hη hη'))).1
  rw [sub_re,reTot,logDeriv_regularizedL_eq χ hn hL,add_re] at below
  have bound : ∑ z ∈ S, weight z ≤ (logDeriv (LFunction χ) s).re +
      (principalFlag χ/(s-1)).re + 694400*logHeight q t := by linarith
  refine ⟨bound,?_⟩
  have flag : ‖principalFlag χ‖ ≤ 1 := by by_cases e : χ=1 <;> simp [principalFlag,e]
  have dist : η ≤ ‖s-1‖ := by
    have a := (le_abs_self (s-1).re).trans (abs_re_le_norm (s-1))
    simpa [s] using a
  have pf := (re_le_norm (principalFlag χ/(s-1))).trans
    (by rw [norm_div];exact div_le_div₀ zero_le_one flag hη dist : ‖principalFlag χ/(s-1)‖ ≤ 1/η)
  have r := (re_le_norm (logDeriv (LFunction χ) s)).trans (right q χ η t hη hη')
  change ∑ z ∈ S, weight z ≤ _
  linarith [show (2:ℝ)/η = 1/η+1/η by ring]

/-- Each near-one zero contributes almost its full multiplicity to the
Poisson kernel at horizontal distance 8h. -/
theorem near_kernel {t h : ℝ} (hh : 0<h) {z : ℂ}
    (lo : 1-h ≤ z.re) (hi : z.re ≤ 1) (ht : |z.im-t| ≤ h) :
    3 ≤ 32*h*kernel (⟨1+8*h,t⟩:ℂ) z := by
  let a := 1+8*h-z.re
  let b := t-z.im
  have a0 : 8*h ≤ a := by dsimp [a];linarith
  have a1 : a ≤ 9*h := by dsimp [a];linarith
  have ap : 0 < a := by linarith
  have b1 : |b| ≤ h := by simpa [b,abs_sub_comm] using ht
  have sq1 := pow_le_pow_left₀ ap.le a1 2
  have sq2 := (sq_le_sq₀ (abs_nonneg b) hh.le).mpr b1
  rw [sq_abs] at sq2
  change 3 ≤ 32*h*(a/(a*a+b*b))
  rw [← mul_div_assoc,le_div_iff₀ (add_pos_of_pos_of_nonneg (mul_pos ap ap) (mul_self_nonneg b))]
  nlinarith only [sq1,sq2,mul_le_mul_of_nonneg_left a0 hh.le,sq_nonneg h]

theorem rectangle_mass :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
      (t h : ℝ), 0<h → h≤1/8 → ∀ S : Finset ℂ,
      (∀ z ∈ S, 1-h ≤ z.re ∧ |z.im-t| ≤ h ∧ ExceptionalZeroCatalogue.genuine χ z) →
      let M := (∑ z ∈ S, analyticOrderNatAt (regularizedL χ) z : ℕ)
      3*(M:ℝ) ≤ 8+32*h*(D+694400*logHeight q t) ∧
        (χ ≠ 1 → 3*(M:ℝ) ≤ 4+32*h*(D+694400*logHeight q t)) := by
  obtain ⟨D,hD,potential⟩ := disk_potential
  obtain ⟨A,hA,right⟩ := right_edge
  refine ⟨max D A,hD.trans (le_max_left _ _),?_⟩
  intro q _ χ t h hh hh' S hS M
  let s : ℂ := ⟨1+8*h,t⟩
  have upper (z : ℂ) (hz : z ∈ S) : z.re ≤ 1 := le_of_lt (lt_of_not_ge fun e =>
    ExceptionalZeroCatalogue.regular_ne χ z e ((ExceptionalZeroCatalogue.regular_zero χ z).mpr (hS z hz).2.2))
  have inside (z : ℂ) (hz : z ∈ S) :
      z ∈ closedBall (⟨2,t⟩:ℂ) (33/25) ∧ ExceptionalZeroCatalogue.genuine χ z := by
    refine ⟨?_,(hS z hz).2.2⟩
    rw [mem_closedBall_iff_norm]
    have k := norm_le_abs_re_add_abs_im (z-(⟨2,t⟩:ℂ))
    change ‖_‖ ≤ |z.re-2|+|z.im-t| at k
    rw [abs_of_nonpos (by linarith [upper z hz] : z.re-2 ≤ 0)] at k
    linarith [(hS z hz).1,(hS z hz).2.1]
  let W := ∑ z ∈ S, (analyticOrderNatAt (regularizedL χ) z:ℝ)*kernel s z
  have weighted : 3*(M:ℝ) ≤ 32*h*W := by
    dsimp only [M,W]
    push_cast
    rw [Finset.mul_sum,Finset.mul_sum]
    refine Finset.sum_le_sum fun z hz => ?_
    have k := near_kernel hh (hS z hz).1 (upper z hz) (hS z hz).2.1
    calc
      _ ≤ (32*h*kernel s z)*(analyticOrderNatAt (regularizedL χ) z:ℝ) :=
        mul_le_mul_of_nonneg_right k (Nat.cast_nonneg _)
      _ = _ := by ring
  have h8 : 0<8*h := by positivity
  have h8' : 8*h≤1 := by linarith
  obtain ⟨p₁,p₂⟩ := potential q χ t (8*h) h8 h8' S inside
  have simp2 : 32*h*(2/(8*h))=8 := by field_simp;ring
  have simp1 : 32*h*(1/(8*h))=4 := by field_simp;ring
  constructor
  · calc
      _ ≤ 32*h*W := weighted
      _ ≤ 32*h*(2/(8*h)+D+694400*logHeight q t) := mul_le_mul_of_nonneg_left p₂ (by positivity)
      _ = 8+32*h*(D+694400*logHeight q t) := by linarith only [simp2]
      _ ≤ _ := by gcongr; exact le_max_left _ _
  · intro hn
    have P := (re_le_norm (logDeriv (LFunction χ) s)).trans (right q χ (8*h) t h8 h8')
    change W ≤ (logDeriv (LFunction χ) s).re + (principalFlag χ/(s-1)).re + _ at p₁
    simp [principalFlag,hn] at p₁
    have p : W ≤ 1/(8*h)+A+694400*logHeight q t := by linarith
    calc
      _ ≤ 32*h*W := weighted
      _ ≤ 32*h*(1/(8*h)+A+694400*logHeight q t) := mul_le_mul_of_nonneg_left p (by positivity)
      _ = 4+32*h*(A+694400*logHeight q t) := by linarith only [simp1]
      _ ≤ _ := by gcongr; exact le_max_right _ _

/-- In a logarithmically shrinking box every nonprincipal character
has at most one zero counted with multiplicity, uniformly in height. -/
theorem isolated :
    ∃ c : ℝ, 0<c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
      (t : ℝ) (S : Finset ℂ), let h := c/logHeight q t
      (∀ z ∈ S, 1-h ≤ z.re ∧ |z.im-t| ≤ h ∧ ExceptionalZeroCatalogue.genuine χ z) →
      let M := ∑ z ∈ S, analyticOrderNatAt (regularizedL χ) z
      M ≤ 2 ∧ (χ ≠ 1 → M ≤ 1) := by
  obtain ⟨D,hD,rect⟩ := rectangle_mass
  let A := D+694401
  have hA : 1 ≤ A := by dsimp [A];linarith
  have hAp : 0<A := by linarith
  let c := 1/(64*A)
  have hc : 0<c := by dsimp [c];positivity
  refine ⟨c,hc,?_⟩
  intro q _ χ t S h hS M
  let L := logHeight q t
  have hL : 1 ≤ L := logHeight_ge_one q t
  have hLp : 0<L := by linarith
  have hh : 0<h := div_pos hc hLp
  have hh' : h≤1/8 := by
    change 1/(64*A)/L ≤ 1/8
    rw [div_div]
    apply one_div_le_one_div_of_le (by norm_num)
    nlinarith [one_le_mul_of_one_le_of_one_le hA hL]
  have bound : D+694400*L ≤ A*L := by
    dsimp [A];nlinarith [mul_nonneg hD (sub_nonneg.mpr hL)]
  have cost : 32*h*(D+694400*L) ≤ 1/2 := calc
    _ ≤ 32*h*(A*L) := mul_le_mul_of_nonneg_left bound (by positivity)
    _ = 1/2 := by change 32*(1/(64*A)/L)*(A*L)=_;field_simp;ring
  have ⟨p₁,p₂⟩ := rect q χ t h hh hh' S hS
  change 3*(M:ℝ) ≤ 8+32*h*(D+694400*L) at p₁
  constructor
  · by_contra! H
    have H' : (3:ℝ) ≤ M := by exact_mod_cast (show 3≤M by omega)
    linarith
  · intro hn
    have p : 3*(M:ℝ) ≤ 4+32*h*(D+694400*L) := p₂ hn
    by_contra! H
    have H' : (2:ℝ) ≤ M := by exact_mod_cast (show 2≤M by omega)
    linarith

end Conjectures.Goldbach.NearOneZeroMultiplicity

namespace Conjectures.Goldbach.ExceptionalQuadraticUniqueness

open Complex DirichletCharacter Metric Set Filter
open _root_.Goldbach GoldbachSmoothing
open ExceptionalZeroCatalogue NearOneZeroMultiplicity
open scoped Classical Topology ComplexConjugate

theorem conjugate_value {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsQuadratic) (hn : χ ≠ 1) (s : ℂ) : LFunction χ (conj s) = conj (LFunction χ s) := by
  let f := LFunction χ
  let g := conj ∘ f ∘ conj
  have hf := differentiable_LFunction hn
  have hg : Differentiable ℂ g := fun z => by
    simpa only [g,Complex.conj_conj] using (hf (conj z)).conj_conj
  have hr (z : ℂ) (hz : 1<z.re) : f (conj z) = conj (f z) := by
    dsimp [f]
    rw [χ.LFunction_eq_LSeries (by simpa using hz),χ.LFunction_eq_LSeries hz]
    change (∑' n, LSeries.term _ (conj z) n) = conj (∑' n, LSeries.term _ z n)
    rw [Complex.conj_tsum]
    apply tsum_congr
    intro n
    by_cases e : n=0
    · subst n;simp
    rw [LSeries.term_of_ne_zero e,LSeries.term_of_ne_zero e]
    have arg : (n:ℂ).arg ≠ Real.pi := by
      rw [show (n:ℂ)=((n:ℝ):ℂ) from rfl,Complex.arg_ofReal_of_nonneg (Nat.cast_nonneg n)]
      exact Real.pi_pos.ne
    rw [Complex.cpow_conj _ _ arg,map_div₀]
    change χ (n:ZMod q) / _ = conj (χ (n:ZMod q)) / _
    rcases hχ (n:ZMod q) with a|a|a <;> simp [a]
  have same : g =ᶠ[𝓝 (2:ℂ)] f := by
    filter_upwards [(show IsOpen {u : ℂ | (1:ℝ)<u.re} from
      isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (1:ℝ)<(2:ℂ).re by norm_num)] with z hz
    simp only [g,Function.comp_apply,hr z hz,Complex.conj_conj]
  have all : g = f := (hg.differentiableOn.analyticOnNhd isOpen_univ).eq_of_eventuallyEq
    (hf.differentiableOn.analyticOnNhd isOpen_univ) same
  have eqn := congrFun all s
  change conj (f (conj s))=f s at eqn
  simpa [f] using congrArg conj eqn

theorem simple_real_at_level :
    ∃ c : ℝ, 0<c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsQuadratic → χ ≠ 1 → ∀ (h : ℝ), h≤c/logHeight q 0 →
      ∀ z w : ℂ, 1-h≤z.re → |z.im|≤h → genuine χ z →
        1-h≤w.re → |w.im|≤h → genuine χ w →
        z=w ∧ z.im=0 ∧ analyticOrderNatAt (LFunction χ) z=1 := by
  obtain ⟨c,hc,unique⟩ := isolated
  refine ⟨c,hc,?_⟩
  intro q _ χ qr hn h hsmall z w hz hiz zz hw hiw zw
  have hfit (v : ℂ) (lo : 1-h≤v.re) (ht : |v.im|≤h) (zero : genuine χ v) :
      1-c/logHeight q 0 ≤ v.re ∧ |v.im-0|≤c/logHeight q 0 ∧ genuine χ v :=
    ⟨by linarith,by simpa using ht.trans hsmall,zero⟩
  have eqv (u : ℂ) (lo : 1-h≤u.re) (ht : |u.im|≤h) (zero : genuine χ u) : z=u := by
    by_contra e
    have b := (unique q χ 0 {z,u} (by
      intro v hv
      simp only [Finset.mem_insert,Finset.mem_singleton] at hv
      rcases hv with rfl|rfl
      · exact hfit _ hz hiz zz
      · exact hfit _ lo ht zero)).2 hn
    simp only [Finset.sum_insert (by simpa using e : z ∉ ({u}:Finset ℂ)),Finset.sum_singleton] at b
    have pz : 0<analyticOrderNatAt (regularizedL χ) z := (order_positive χ zz).1
    have pu : 0<analyticOrderNatAt (regularizedL χ) u := (order_positive χ zero).1
    omega
  have conjz : genuine χ (conj z) := ⟨Or.inl hn,by rw [conjugate_value χ qr hn,zz.2,map_zero]⟩
  have real' := congrArg Complex.im (eqv (conj z) (by simpa using hz) (by simpa using hiz) conjz)
  have b := (unique q χ 0 {z} (by
    intro v hv; obtain rfl := Finset.mem_singleton.mp hv;exact hfit _ hz hiz zz)).2 hn
  simp only [Finset.sum_singleton] at b
  have pz : 0<analyticOrderNatAt (regularizedL χ) z := (order_positive χ zz).1
  have f : regularizedL χ = LFunction χ := by simp [regularizedL,hn]
  rw [f] at pz b
  simp only [Complex.conj_im] at real'
  exact ⟨eqv w hw hiw zw,by linarith,by omega⟩


end Conjectures.Goldbach.ExceptionalQuadraticUniqueness

namespace Conjectures.Goldbach.DirichletExceptionalZeroRegion

open Complex DirichletCharacter Metric Set
open _root_.Goldbach GoldbachSmoothing
open ExceptionalZeroCatalogue NearOneZeroMultiplicity
open scoped Classical

private theorem positive_polynomial (z : ℂ) (hz : ‖z‖ ≤ 1) :
    0 ≤ 3+4*z.re+(z*z).re := by
  have sq := pow_le_pow_left₀ (norm_nonneg z) hz 2
  rw [Complex.sq_norm,Complex.normSq_apply] at sq
  rw [Complex.mul_re]
  nlinarith [sq_nonneg (1+z.re)]

private theorem three_terms {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (x t : ℝ) (n : ℕ) :
    let f : ℕ → ℂ := fun k => (ArithmeticFunction.vonMangoldt k:ℂ)
    0 ≤ 3*(LSeries.term f (x:ℂ) n).re +
      4*(LSeries.term (twistedCoefficient χ) (⟨x,t⟩:ℂ) n).re +
      (LSeries.term (twistedCoefficient (χ*χ)) (⟨x,2*t⟩:ℂ) n).re := by
  intro f
  by_cases hn : n=0
  · subst n; simp
  have nc : (n:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  let l := Real.log (n:ℝ)
  let a := Real.exp (-(l*x))
  let phase := fun u : ℝ => Complex.exp (((-(l*u):ℝ):ℂ)*I)
  have factor (u : ℝ) : ((n:ℂ)^(⟨x,u⟩:ℂ))⁻¹ = (a:ℂ)*phase u := by
    rw [cpow_def_of_ne_zero nc,← Complex.exp_neg]
    dsimp only [a,phase]
    rw [Complex.ofReal_exp,← Complex.exp_add,← Complex.natCast_log]
    congr 1
    apply Complex.ext <;> simp [l,mul_re,mul_im]
    ring
  have ph2 : phase (2*t) = phase t*phase t := by
    dsimp only [phase];rw [← Complex.exp_add];congr 1;push_cast;ring
  have ph0 : phase 0=1 := by simp [phase]
  let d : ℝ := ArithmeticFunction.vonMangoldt n*a
  let u : ℂ := χ (n:ZMod q)*phase t
  have ud : ‖u‖ ≤ 1 := by
    dsimp only [u]
    rw [norm_mul,show ‖phase t‖=1 by simp [phase,Complex.norm_exp],mul_one]
    exact χ.norm_le_one _
  have e0 : LSeries.term f (x:ℂ) n = (d:ℂ) := by
    rw [LSeries.term_of_ne_zero hn,div_eq_mul_inv,show (x:ℂ)=(⟨x,0⟩:ℂ) from rfl,factor,ph0,mul_one]
    simp [d,f]
  have e1 : LSeries.term (twistedCoefficient χ) (⟨x,t⟩:ℂ) n = (d:ℂ)*u := by
    rw [LSeries.term_of_ne_zero hn,div_eq_mul_inv,factor]
    simp [twistedCoefficient,d,u];ring
  have e2 : LSeries.term (twistedCoefficient (χ*χ)) (⟨x,2*t⟩:ℂ) n = (d:ℂ)*(u*u) := by
    rw [LSeries.term_of_ne_zero hn,div_eq_mul_inv,factor,ph2]
    simp [twistedCoefficient,d,u,MulChar.mul_apply];ring
  rw [e0,e1,e2]
  have scale (v : ℂ) : ((d:ℂ)*v).re=d*v.re := by simp [Complex.mul_re]
  simp only [ofReal_re,scale]
  have dn : 0 ≤ d := mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.exp_pos _).le
  linarith only [mul_nonneg dn (positive_polynomial u ud)]

theorem three_four_one {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {x : ℝ} (hx : 1 < x) (t : ℝ) :
    3*(logDeriv riemannZeta (x:ℂ)).re + 4*(logDeriv (LFunction χ) (⟨x,t⟩:ℂ)).re +
      (logDeriv (LFunction (χ*χ)) (⟨x,2*t⟩:ℂ)).re ≤ 0 := by
  let f : ℕ → ℂ := fun n => (ArithmeticFunction.vonMangoldt n:ℂ)
  have h0 : LSeriesSummable f (x:ℂ) := ArithmeticFunction.LSeriesSummable_vonMangoldt hx
  have h1 : LSeriesSummable (twistedCoefficient χ) (⟨x,t⟩:ℂ) := χ.LSeriesSummable_twist_vonMangoldt hx
  have h2 : LSeriesSummable (twistedCoefficient (χ*χ)) (⟨x,2*t⟩:ℂ) :=
    (χ*χ).LSeriesSummable_twist_vonMangoldt hx
  have hzeta : LSeries f (x:ℂ) = -logDeriv riemannZeta (x:ℂ) := by
    simpa [logDeriv,neg_div] using ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div
      (s:=(x:ℂ)) (by simpa using hx)
  have total := ((((Complex.hasSum_re h0.hasSum).mul_left 3).add
    ((Complex.hasSum_re h1.hasSum).mul_left 4)).add (Complex.hasSum_re h2.hasSum)).tsum_eq
  have pos := (tsum_nonneg (fun n => three_terms χ x t n)).trans_eq total
  change 0 ≤ 3*(LSeries f (x:ℂ)).re + 4*(LSeries (twistedCoefficient χ) (⟨x,t⟩:ℂ)).re +
    (LSeries (twistedCoefficient (χ*χ)) (⟨x,2*t⟩:ℂ)).re at pos
  rw [hzeta,LSeries_twistedCoefficient_eq χ hx,LSeries_twistedCoefficient_eq (χ*χ) hx] at pos
  simp only [neg_re] at pos
  linarith

private theorem log_double (q : ℕ) [NeZero q] (t : ℝ) :
    logHeight q (2*t) ≤ 2*logHeight q t := by
  let H := 2*(q:ℝ)*(2+|t|)
  have Q1 : (1:ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have H2 : 2 ≤ H := by
    dsimp [H]
    nlinarith [mul_nonneg (Nat.cast_nonneg q) (abs_nonneg t)]
  change Real.log (2*(q:ℝ)*(2+|2*t|)) ≤ 2*Real.log H
  apply le_trans _ (show Real.log (H^2) = 2*Real.log H by simp).le
  apply Real.log_le_log (by positivity)
  rw [abs_mul,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  calc
    _ ≤ 2*H := by dsimp [H]; linarith only [Nat.cast_nonneg (α:=ℝ) q]
    _ ≤ H^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr H2) (show 0 ≤ H by linarith)]

private theorem imaginary_pole {h t : ℝ} (hp : 0 < h) (large : 64*h ≤ |t|) :
    (1/((⟨1+16*h,t⟩:ℂ)-1)).re ≤ 1/(256*h) := by
  have square := (sq_le_sq₀ (show 0 ≤ 64*h by positivity) (abs_nonneg t)).mpr large
  rw [sq_abs] at square
  rw [Complex.div_re,Complex.normSq_apply]
  simp only [sub_re,sub_im,one_re,one_im,add_sub_cancel_left,sub_zero,one_mul,zero_mul,
    zero_div,add_zero]
  apply (div_le_div_iff₀ (add_pos_of_pos_of_nonneg (mul_pos (by positivity) (by positivity))
    (mul_self_nonneg _)) (by positivity)).mpr
  nlinarith only [square,sq_nonneg h]

/-- A near-one zero of any character has quadratic character and
has very small height. Both conclusions hold in the same strip. -/
theorem zero_characteristics :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      ∀ (z : ℂ) (h : ℝ), 0 < h → h ≤ c/logHeight q z.im →
      1-h ≤ z.re → genuine χ z → χ.IsQuadratic ∧ |z.im| < 64*h := by
  obtain ⟨_,_,pot⟩ := disk_potential
  obtain ⟨D,hD,right⟩ := right_edge
  let A := 3*D+6*694400+1
  have A1 : 1 ≤ A := by dsimp [A];linarith
  have Ap : 0 < A := by linarith
  let c := 1/(128*A)
  refine ⟨c,by dsimp [c];positivity,?_⟩
  intro q _ χ z h hp small near zero
  let t := z.im
  let L := logHeight q t
  let s : ℂ := ⟨1+16*h,t⟩
  let s₂ : ℂ := ⟨1+16*h,2*t⟩
  have L1 : 1 ≤ L := logHeight_ge_one q t
  have Lp : 0 < L := by linarith
  have bound : h ≤ 1/(128*(A*L)) := by
    convert small using 1
    dsimp [c,L,t];rw [div_div];ring
  have budget : h*(128*(A*L)) ≤ 1 := (le_div_iff₀ (by positivity)).mp bound
  have smallH : h ≤ 1/16 := by
    apply bound.trans
    apply one_div_le_one_div_of_le (by norm_num)
    linarith [one_le_mul_of_one_le_of_one_le A1 L1]
  have ep : 0 < 16*h := by positivity
  have e1 : 16*h ≤ 1 := by linarith
  have zhi : z.re ≤ 1 := le_of_lt (lt_of_not_ge fun hz => regular_ne χ z hz ((regular_zero χ z).mpr zero))
  have mem : z ∈ closedBall (⟨2,t⟩:ℂ) (33/25) := by
    rw [mem_closedBall_iff_norm]
    have k := norm_le_abs_re_add_abs_im (z-(⟨2,t⟩:ℂ))
    change ‖_‖ ≤ |z.re-2|+|z.im-z.im| at k
    rw [sub_self,abs_zero,add_zero,abs_of_nonpos (by linarith : z.re-2 ≤ 0)] at k
    linarith
  have ab : 0 < 1+16*h-z.re := by linarith
  have k : 1 ≤ 17*h*kernel s z := by
    change 1 ≤ 17*h*((1+16*h-z.re)/((1+16*h-z.re)*(1+16*h-z.re)+(t-z.im)*(t-z.im)))
    rw [show t-z.im=0 from sub_self _,zero_mul,add_zero,← mul_div_assoc,
      le_div_iff₀ (mul_pos ab ab)]
    nlinarith only [mul_nonneg (show 0 ≤ 17*h-(1+16*h-z.re) by linarith) ab.le]
  have kn : 0 ≤ kernel s z := div_nonneg ab.le (normSq_nonneg _)
  have multiplicity : (1:ℝ) ≤ analyticOrderNatAt (regularizedL χ) z := by
    exact_mod_cast (order_positive χ zero).1
  have p1 := (pot q χ t (16*h) ep e1 {z} (by
    intro u hu;obtain rfl := Finset.mem_singleton.mp hu;exact ⟨mem,zero⟩)).1
  change _ ≤ (logDeriv (LFunction χ) s).re + (principalFlag χ/(s-1)).re + 694400*L at p1
  simp only [Finset.sum_singleton] at p1
  have single := k.trans (mul_le_mul_of_nonneg_left ((le_mul_of_one_le_left kn multiplicity).trans p1)
    (by positivity : 0 ≤ 17*h))
  by_contra absent
  have big (quad : χ.IsQuadratic) : 64*h ≤ |t| := le_of_not_gt fun hi => absent ⟨quad,hi⟩
  have pole1 : (principalFlag χ/(s-1)).re ≤ 1/(256*h) := by
    by_cases principal : χ=1
    · have quad : χ.IsQuadratic := MulChar.isQuadratic_iff_sq_eq_one.mpr (by simp [principal])
      simpa [principalFlag,principal,s] using imaginary_pole hp (big quad)
    · simp [principalFlag,principal]
      positivity
  have pole2 : (principalFlag (χ*χ)/(s₂-1)).re ≤ 1/(256*h) := by
    by_cases pair : χ*χ=1
    · have quad : χ.IsQuadratic := MulChar.isQuadratic_iff_sq_eq_one.mpr (by simpa [pow_two] using pair)
      have twice : 64*h ≤ |2*t| := by
        rw [abs_mul,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
        linarith [big quad,abs_nonneg t]
      simpa [principalFlag,pair,s₂] using imaginary_pole hp twice
    · simp [principalFlag,pair]
      positivity
  have p2 := (pot q (χ*χ) (2*t) (16*h) ep e1 ∅ (by simp)).1
  change _ ≤ (logDeriv (LFunction (χ*χ)) s₂).re + (principalFlag (χ*χ)/(s₂-1)).re +
    694400*logHeight q (2*t) at p2
  simp only [Finset.sum_empty] at p2
  let x := 1+16*h
  have hx : 1 < x := by dsimp [x];linarith
  have tri : 3*(logDeriv riemannZeta (x:ℂ)).re+4*(logDeriv (LFunction χ) s).re+
    (logDeriv (LFunction (χ*χ)) s₂).re ≤ 0 := three_four_one χ hx t
  have R := right 1 (1 : DirichletCharacter ℂ 1) (16*h) 0 ep e1
  rw [LFunction_modOne_eq] at R
  have pole : -(logDeriv riemannZeta (x:ℂ)).re ≤ 1/(16*h)+D :=
    ((neg_le_abs _).trans (abs_re_le_norm _)).trans R
  have log2 : logHeight q (2*t) ≤ 2*L := log_double q t
  have cost : 3*D+6*694400*L ≤ A*L := by
    dsimp [A];nlinarith [mul_nonneg hD (sub_nonneg.mpr L1)]
  have total : 4*((logDeriv (LFunction χ) s).re+(principalFlag χ/(s-1)).re+694400*L) ≤
      3*(1/(16*h))+5*(1/(256*h))+A*L := by
    linarith only [pole,p2,pole1,pole2,tri,log2,cost]
  have fees := mul_le_mul_of_nonneg_left total (by positivity : 0 ≤ 17*h)
  have factor : (17*h)*(3*(1/(16*h))+5*(1/(256*h)))=901/256 := by field_simp;ring
  linarith only [single,budget,fees,factor]

end Conjectures.Goldbach.DirichletExceptionalZeroRegion

section
open Complex DirichletCharacter Goldbach
noncomputable section
namespace GoldbachTwistedMellin

/-- The logarithmic strip is zero-free for every primitive character and
every ordinate. The remaining possible real quadratic zero is excluded by
the verified real-zero gap, on the same conductor scale. -/
theorem primitive_zero_free_logHeight :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → ∀ z : ℂ, regularizedL χ z = 0 → z.re < 1-c/logHeight q z.im := by
  obtain ⟨a, ha, profile⟩ := Conjectures.Goldbach.DirichletExceptionalZeroRegion.zero_characteristics
  obtain ⟨b, hb, realZero⟩ := Conjectures.Goldbach.ExceptionalQuadraticUniqueness.simple_real_at_level
  obtain ⟨δ, hδ, compact⟩ := Conjectures.Goldbach.ExceptionalZeroCatalogue.bounded_strip 1 1
  obtain ⟨d, hd, siegel⟩ := PEqualNP.Outside.L_goldbach_frontier_no_siegel_zero
  let c := min a (min (b/64) (min δ (min (1/64) (d/2))))
  have hc : 0 < c := lt_min ha (lt_min (by positivity) (lt_min hδ (lt_min (by norm_num) (by positivity))))
  have ca : c ≤ a := min_le_left ..
  have cb : c ≤ b/64 := (min_le_right ..).trans (min_le_left ..)
  have cd : c ≤ δ := (min_le_right ..).trans ((min_le_right ..).trans (min_le_left ..))
  have cc : c ≤ 1/64 := (min_le_right ..).trans ((min_le_right ..).trans ((min_le_right ..).trans (min_le_left ..)))
  have cs : c ≤ d/2 := (min_le_right ..).trans ((min_le_right ..).trans ((min_le_right ..).trans (min_le_right ..)))
  refine ⟨c, hc, ?_⟩
  intro q _ χ hprim z hz
  by_contra! hnear
  let L := logHeight q z.im
  let h := c/L
  have hL1 : 1 ≤ L := logHeight_ge_one q z.im
  have hL := zero_lt_one.trans_le hL1
  have hp : 0 < h := div_pos hc hL
  have hcap : h ≤ c := div_le_self hc.le hL1
  have hz' : Conjectures.Goldbach.ExceptionalZeroCatalogue.genuine χ z := (Conjectures.Goldbach.ExceptionalZeroCatalogue.regular_zero χ z).mp hz
  have hu : 1-h ≤ z.re := hnear
  obtain ⟨quad, low⟩ := profile q χ z h hp (div_le_div_of_nonneg_right ca hL.le) hu hz'
  have nχ : χ ≠ 1 := by
    intro hχ
    have level : 1 = q := by simpa only [hχ, IsPrimitive, conductor_one] using hprim
    exact compact q level.symm.le χ z (by linarith only [low, hcap, cc]) (by linarith only [hu, hcap, cd]) hz'
  have hbase : 0 < logHeight q 0 := zero_lt_one.trans_le (logHeight_ge_one q 0)
  have hmono : logHeight q 0 ≤ L := logHeight_mono_abs q (by simp)
  have hwidth : 64*h ≤ b/logHeight q 0 := calc
    _ = (64*c)/L := by dsimp only [h]; ring
    _ ≤ b/L := div_le_div_of_nonneg_right (by linarith only [cb]) hL.le
    _ ≤ _ := div_le_div_of_nonneg_left hb.le hbase hmono
  have hzbig : 1-64*h ≤ z.re := by linarith only [hu, hp]
  have him := (realZero q χ quad nχ (64*h) hwidth z z hzbig low.le hz' hzbig low.le hz').2.1
  have hright : z.re < 1 := lt_of_not_ge (fun h1 =>
    Conjectures.Goldbach.ExceptionalZeroCatalogue.regular_ne χ z h1 hz)
  have hq : 1 ≤ (q:ℝ) := by exact_mod_cast NeZero.pos q
  have hlog : 0 < Real.log ((q:ℝ)+2) := Real.log_pos (by linarith)
  have hlogLe : Real.log ((q:ℝ)+2) ≤ L := by
    apply Real.log_le_log (by positivity)
    nlinarith only [hq, mul_nonneg (Nat.cast_nonneg q) (abs_nonneg z.im)]
  have hstrict : h < d/Real.log ((q:ℝ)+2) :=
    (div_le_div_of_nonneg_left hc.le hlog hlogLe).trans_lt
      ((div_lt_div_iff_of_pos_right hlog).mpr (cs.trans_lt (half_lt_self hd)))
  have noc := siegel q χ z.re (MulChar.isQuadratic_iff_sq_eq_one.mp quad)
    (by linarith only [hu, hstrict]) hright
  have hre : (z.re:ℂ) = z := Complex.ext rfl (by simp [him])
  rw [hre] at noc
  exact noc hz'.2

/-- A zero in the strip used by Pintz, at bounded height, must already
have polynomially large conductor. This applies to the primitive characters
in the exact finite major-arc expansion. -/
theorem nearOne_zero_conductor_bound :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
      ∀ (X H T : ℝ) (z : ℂ), 1 < X → 0 < H → |z.im| ≤ T → 1-H/Real.log X ≤ z.re →
        regularizedL χ z = 0 → X^(c/H) < 2*(q:ℝ)*(2+T) := by
  obtain ⟨c, hc, hzfree⟩ := primitive_zero_free_logHeight
  refine ⟨c, hc, ?_⟩
  intro q _ χ hp X H T z hX hH hT hσ hroot
  have hx := Real.log_pos hX
  have hL := zero_lt_one.trans_le (logHeight_ge_one q z.im)
  have hzero := hzfree q χ hp z hroot
  have hdiv : c/logHeight q z.im < H/Real.log X := by linarith only [hσ, hzero]
  have hmul := (div_lt_div_iff₀ hL hx).mp hdiv
  have hlog : Real.log X*(c/H) < logHeight q z.im := by
    rw [← mul_div_assoc, div_lt_iff₀ hH]
    linarith only [hmul]
  calc
    _ = Real.exp (Real.log X*(c/H)) := Real.rpow_def_of_pos (zero_lt_one.trans hX) _
    _ < Real.exp (logHeight q z.im) := Real.exp_lt_exp.mpr hlog
    _ = 2*(q:ℝ)*(2+|z.im|) := Real.exp_log (by have := NeZero.pos q; positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith only [hT]) (by positivity)

end GoldbachTwistedMellin
end
end

-- Arithmetic evaluation and estimates for pairs of inducing characters.
-- Adapted from zxg0623, PR #3782 at 66b7bb6fba35f86bd59c3d4916fe1a72ee3a2bdf (Apache-2.0).
-- https://github.com/CGandGameEngineLearner/goldbach-proofs/pull/3782

/-! The generalized Goldbach singular series for two primitive Dirichlet
characters. Grouping finite Fourier frequencies by reduced denominator gives
the totient-normalized residue density. A uniform bound for the three Gauss
sums gives absolute convergence at every positive target. Taking finite
levels divisible by every fixed denominator proves the first inequality in
Pintz, “A new explicit formula in the additive theory of primes with
applications I”, §7, (7.7), https://arxiv.org/abs/1804.05561.

The Gauss sums here use the positive additive phase, so the target frequency
in the third Gauss sum is negative. -/

namespace Conjectures.Goldbach.TwistedGoldbachSingularSeries

open Finset DirichletCharacter
open scoped BigOperators Classical
open B13BilateralVaughanReductionProof

private theorem group_average {G H : Type*} [Group G] [Group H] [Fintype G] [Fintype H]
    (π : G →* H) (onto : Function.Surjective π) (F : H → ℂ) :
    (Fintype.card H : ℂ) * ∑ x : G, F (π x) = (Fintype.card G : ℂ) * ∑ y : H, F y := by
  have left (y : H) : (∑ x : G, F (y*π x)) = ∑ x : G, F (π x) := by
    obtain ⟨z,rfl⟩ := onto y
    simp_rw [← map_mul]
    exact Equiv.sum_comp (Equiv.mulLeft z) (fun x => F (π x))
  have right (x : G) : (∑ y : H, F (y*π x)) = ∑ y : H, F y :=
    Equiv.sum_comp (Equiv.mulRight (π x)) F
  calc
    _ = ∑ _y : H, ∑ x : G, F (π x) := by simp
    _ = ∑ y : H, ∑ x : G, F (y*π x) := sum_congr rfl (fun y _ => (left y).symm)
    _ = ∑ x : G, ∑ y : H, F (y*π x) := sum_comm
    _ = ∑ _x : G, ∑ y : H, F y := sum_congr rfl (fun x _ => right x)
    _ = _ := by simp

/-- Pushing a lifted character through the reduction of residues preserves
the totient-normalized weighted sum against every function on the divisor. -/
theorem induced_average {q d : ℕ} [NeZero q] [NeZero d] (h : d ∣ q)
    (θ : DirichletCharacter ℂ d) (F : ZMod d → ℂ) :
    (d.totient:ℂ)*(∑ x : ZMod q, changeLevel h θ x * F (ZMod.castHom h (ZMod d) x)) =
      (q.totient:ℂ)*(∑ y : ZMod d, θ y * F y) := by
  let _ : Fintype (ZMod q)ˣ := BombieriVinogradov.LargeSieve.characterReductionUnitFintype q
  let _ : Fintype (ZMod d)ˣ := BombieriVinogradov.LargeSieve.characterReductionUnitFintype d
  rw [← BombieriVinogradov.LargeSieve.sum_units_eq_sum_residues,
    ← BombieriVinogradov.LargeSieve.sum_units_eq_sum_residues θ]
  simp only [changeLevel_eq_cast_of_dvd, ZMod.castHom_apply]
  simpa only [ZMod.card_units_eq_totient, ZMod.unitsMap_val] using
    group_average (ZMod.unitsMap h) (ZMod.unitsMap_surjective h)
      (fun u : (ZMod d)ˣ => θ (u : ZMod d) * F u)

/-- When a character does not factor through the divisor, its whole
pushforward measure vanishes, even before choosing a Fourier phase. -/
theorem absent_average {q d : ℕ} [NeZero q] (h : d ∣ q) (χ : DirichletCharacter ℂ q)
    (hn : ¬χ.FactorsThrough d) (F : ZMod d → ℂ) :
    (∑ x : ZMod q, χ x * F (ZMod.castHom h (ZMod d) x)) = 0 := by
  classical
  have hk := mt (factorsThrough_iff_ker_unitsMap h).mpr hn
  obtain ⟨u,hu,hχ⟩ := Set.not_subset.mp hk
  have hmem : ZMod.unitsMap h u = 1 := hu
  have hne : χ (u : ZMod q) ≠ 1 := by
    intro he
    apply hχ
    apply Units.ext
    exact he
  have hu' : ZMod.castHom h (ZMod d) (u : ZMod q) = 1 := congrArg Units.val hmem
  apply eq_zero_of_mul_eq_self_left hne
  let G (x : ZMod q) := χ x * F (ZMod.castHom h (ZMod d) x)
  calc
    _ = ∑ x : ZMod q, G (u*x) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro x _
      simp only [G,map_mul,hu',one_mul,mul_assoc]
    _ = _ := u.mulLeft_bijective.sum_comp G

private theorem phase_descent {q d : ℕ} [NeZero q] [NeZero d] (h : d ∣ q)
    (k : ℕ) (x : ZMod q) :
    ZMod.stdAddChar (((q/d*k : ℕ) : ZMod q)*x) =
      ZMod.stdAddChar ((k : ZMod d)*ZMod.castHom h (ZMod d) x) := by
  obtain ⟨f,rfl⟩ := h
  obtain ⟨n,rfl⟩ : ∃ n : ℕ, (n : ZMod (d*f)) = x := ⟨x.val,ZMod.natCast_zmod_val x⟩
  rw [Nat.mul_div_cancel_left f (NeZero.pos d), map_natCast, ← Nat.cast_mul, ← Nat.cast_mul,
    DyadicMixedB4GaussLift.stdAddChar_nat_fraction, DyadicMixedB4GaussLift.stdAddChar_nat_fraction]
  congr 1
  have hf : f ≠ 0 := fun e => NeZero.ne (d*f) (by simp [e])
  push_cast
  field_simp [NeZero.ne d,hf]

noncomputable def amplitude {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (k : ℕ) : ℂ :=
  gaussSum χ (ZMod.stdAddChar.mulShift (k : ZMod q)) / (q.totient:ℂ)

theorem amplitude_at_divisor {q d : ℕ} [NeZero q] [NeZero d] (h : d ∣ q)
    (χ : DirichletCharacter ℂ q) (k : ℕ) :
    amplitude χ (q/d*k) = if H : χ.FactorsThrough d then amplitude H.χ₀ k else 0 := by
  classical
  unfold amplitude gaussSum
  simp only [AddChar.mulShift_apply,phase_descent h]
  split_ifs with H
  · apply (div_eq_div_iff (Nat.cast_ne_zero.mpr (NeZero.ne q.totient))
        (Nat.cast_ne_zero.mpr (NeZero.ne d.totient))).mpr
    calc
      _ = (d.totient:ℂ)*(∑ x : ZMod q, changeLevel h H.χ₀ x *
        ZMod.stdAddChar ((k : ZMod d)*ZMod.castHom h (ZMod d) x)) := by
          conv_lhs => rw [H.eq_changeLevel]
          ring
      _ = _ := (induced_average h H.χ₀ (fun y => ZMod.stdAddChar ((k : ZMod d)*y))).trans (mul_comm ..)
  · rw [absent_average h χ H (fun y => ZMod.stdAddChar ((k : ZMod d)*y)),zero_div]

/-- Sort the frequencies at level q by their reduced denominator.
The zero frequency is the unique reduced numerator at denominator one. -/
theorem reduced_denominators (q : ℕ) [NeZero q] (F : ℕ → ℂ) :
    ∑ k ∈ range q, F k =
      ∑ d ∈ q.divisors, ∑ a ∈ (range d).filter (fun a => d.Coprime a), F (q/d*a) := by
  classical
  let T (g : ℕ) := ∑ k ∈ (range q).filter (fun k => q.gcd k=g), F k
  have part : ∑ k ∈ range q, F k = ∑ g ∈ q.divisors, T g :=
    (sum_fiberwise_of_maps_to (fun k (_ : k ∈ range q) =>
      Nat.mem_divisors.mpr ⟨q.gcd_dvd_left k,NeZero.ne q⟩) F).symm
  rw [part, ← Nat.sum_div_divisors q T]
  apply sum_congr rfl
  intro d hd
  obtain ⟨g,hg⟩ := Nat.dvd_of_mem_divisors hd
  have hdpos := Nat.pos_of_mem_divisors hd
  have hgpos : 0 < g := by
    by_contra! hg0
    exact NeZero.ne q (by simp [hg,show g=0 by omega])
  have hquot : q/d=g := by rw [hg,Nat.mul_div_cancel_left g hdpos]
  rw [hquot]
  unfold T
  symm
  apply sum_bij (fun a _ => g*a)
  · intro a ha
    obtain ⟨ha,hc⟩ := mem_filter.mp ha
    have hq : q=g*d := hg.trans (mul_comm d g)
    exact mem_filter.mpr ⟨mem_range.mpr (hq ▸ Nat.mul_lt_mul_of_pos_left (mem_range.mp ha) hgpos),
      by rw [hq,Nat.gcd_mul_left,hc.gcd_eq_one,mul_one]⟩
  · intro a _ b _ hab
    exact Nat.eq_of_mul_eq_mul_left hgpos hab
  · intro k hk
    obtain ⟨hk,hc⟩ := mem_filter.mp hk
    obtain ⟨a,rfl⟩ : g ∣ k := hc ▸ q.gcd_dvd_right k
    have hq : q=g*d := hg.trans (mul_comm d g)
    rw [hq,Nat.gcd_mul_left] at hc
    have ha : a<d := (Nat.mul_lt_mul_left hgpos).mp (hq ▸ mem_range.mp hk)
    exact ⟨a,mem_filter.mpr ⟨mem_range.mpr ha, (mul_eq_left₀ hgpos.ne').mp hc⟩,rfl⟩
  · intro _ _
    rfl

noncomputable def normalized {q : ℕ} [NeZero q] (χ ψ : DirichletCharacter ℂ q) (m : ℕ) : ℂ :=
  ((q:ℂ)*∑ x : ZMod q, χ x * ψ ((m : ZMod q)-x)) / (q.totient:ℂ)^2

/-- The contribution of the reduced fractions of denominator d. It is zero
unless both characters descend. Its phases and Gauss sums are all at d. -/
noncomputable def denominatorTerm {q : ℕ} (χ ψ : DirichletCharacter ℂ q) (m d : ℕ) : ℂ := by
  classical
  exact if hd : d ≠ 0 then
    let _ : NeZero d := ⟨hd⟩
    if H : χ.FactorsThrough d then
      if K : ψ.FactorsThrough d then
        ∑ a ∈ (range d).filter (fun a => d.Coprime a),
          ZMod.stdAddChar ((a : ZMod d)*(-(m : ZMod d))) * amplitude H.χ₀ a * amplitude K.χ₀ a
      else 0
    else 0
  else 0

private theorem synthesis {q : ℕ} [NeZero q] (χ ψ : DirichletCharacter ℂ q) (m : ZMod q) :
    (∑ t : ZMod q, ZMod.stdAddChar (t*(-m)) * (gaussSum χ (ZMod.stdAddChar.mulShift t) *
      gaussSum ψ (ZMod.stdAddChar.mulShift t))) = (q:ℂ) * ∑ x : ZMod q, χ x * ψ (m-x) := by
  let J (s : ZMod q) := ∑ x : ZMod q, χ x * ψ (s-x)
  have h (t : ZMod q) : ZMod.dft J (-t) =
      gaussSum χ (ZMod.stdAddChar.mulShift t) * gaussSum ψ (ZMod.stdAddChar.mulShift t) := by
    rw [gaussSum_mul,ZMod.dft_apply]
    apply sum_congr rfl
    intro s _
    rw [← sum_mul]
    simp only [J,smul_eq_mul,mul_neg,neg_neg,AddChar.mulShift_apply,mul_comm]
  calc
    _ = ZMod.dft (fun t => ZMod.dft J (-t)) m := by
      rw [ZMod.dft_apply]
      apply sum_congr rfl
      intro t _
      rw [h,smul_eq_mul,mul_neg]
    _ = _ := by rw [ZMod.dft_comp_neg,ZMod.dft_dft]; simp only [J,neg_neg,smul_eq_mul]

theorem finite_expansion {q : ℕ} [NeZero q] (χ ψ : DirichletCharacter ℂ q) (m : ℕ) :
    normalized χ ψ m = ∑ d ∈ q.divisors, denominatorTerm χ ψ m d := by
  let F (k : ℕ) := ZMod.stdAddChar ((k : ZMod q)*(-(m : ZMod q))) * amplitude χ k * amplitude ψ k
  have H : normalized χ ψ m = ∑ k ∈ range q, F k := by
    unfold normalized
    rw [← synthesis, ← DyadicMixedB4DualCharacter.sum_natCast_range_eq_zmod, sum_div]
    apply sum_congr rfl
    intro k _
    dsimp only [F,amplitude]
    ring
  rw [H,reduced_denominators q F]
  apply sum_congr rfl
  intro d hd
  have hd0 := (Nat.pos_of_mem_divisors hd).ne'
  let _ : NeZero d := ⟨hd0⟩
  have divides := Nat.dvd_of_mem_divisors hd
  unfold denominatorTerm
  simp only [dite_eq_left hd0]
  by_cases Hχ : χ.FactorsThrough d <;> by_cases Hψ : ψ.FactorsThrough d <;>
    simp only [F,amplitude_at_divisor divides,phase_descent divides,map_neg,map_natCast,Hχ,Hψ,
      dite_true,dite_false,mul_zero,zero_mul,sum_const_zero]

theorem conductor_support {q : ℕ} [NeZero q] (χ ψ : DirichletCharacter ℂ q) (m d : ℕ)
    (h : ¬Nat.lcm χ.conductor ψ.conductor ∣ d) : denominatorTerm χ ψ m d = 0 := by
  unfold denominatorTerm
  split_ifs with hd hχ hψ
  · exact False.elim (h (Nat.lcm_dvd (conductor_dvd_of_mem_conductorSet χ hχ)
      (conductor_dvd_of_mem_conductorSet ψ hψ)))
  all_goals rfl

private theorem principal_count {q : ℕ} [NeZero q] (m : ZMod q) :
    (∑ x : ZMod q, (1 : DirichletCharacter ℂ q) x * (1 : DirichletCharacter ℂ q) (m-x)) =
      (((univ : Finset (ZMod q)).filter (fun x => IsUnit x ∧ IsUnit (m-x))).card:ℂ) := by
  calc
    _ = ∑ x : ZMod q, if IsUnit x ∧ IsUnit (m-x) then (1:ℂ) else 0 := by
      apply sum_congr rfl
      intro x _
      by_cases hu : IsUnit x <;> by_cases hv : IsUnit (m-x) <;>
        simp [hu,hv,MulChar.one_apply,MulChar.map_nonunit]
    _ = _ := by simp

/-- Absolute values of the finite twisted residue counts are bounded by the
ordinary count on the same modulus, including composite moduli. -/
theorem chars_le_units {q : ℕ} [NeZero q] (χ ψ : DirichletCharacter ℂ q)
    (m : ZMod q) : ‖∑ x : ZMod q, χ x * ψ (m-x)‖ ≤
      ‖∑ x : ZMod q, (1 : DirichletCharacter ℂ q) x * (1 : DirichletCharacter ℂ q) (m-x)‖ := by
  rw [principal_count,Complex.norm_natCast]
  calc
    _ ≤ ∑ x : ZMod q, ‖χ x * ψ (m-x)‖ := norm_sum_le _ _
    _ ≤ ∑ x : ZMod q, if IsUnit x ∧ IsUnit (m-x) then (1:ℝ) else 0 := by
      apply sum_le_sum
      intro x _
      by_cases hu : IsUnit x
      · by_cases hv : IsUnit (m-x)
        · rw [ite_eq_left ⟨hu,hv⟩,norm_mul]
          simpa only [one_mul] using mul_le_mul (χ.norm_le_one x) (ψ.norm_le_one (m-x))
            (norm_nonneg _) zero_le_one
        · simp [hv,ψ.map_nonunit hv]
      · simp [hu,χ.map_nonunit hu]
    _ = _ := by simp

/-- Every complete divisor sum is dominated by the ordinary singular-series
sum at the same level and target, without any primitivity assumption. -/
theorem domination {q : ℕ} [NeZero q] (χ ψ : DirichletCharacter ℂ q) (m : ℕ) :
    ‖∑ d ∈ q.divisors, denominatorTerm χ ψ m d‖ ≤
      ‖∑ d ∈ q.divisors, denominatorTerm (1 : DirichletCharacter ℂ q) 1 m d‖ := by
  rw [← finite_expansion,← finite_expansion]
  simp only [normalized,norm_div,norm_mul]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (chars_le_units χ ψ _) (norm_nonneg _))
    (norm_nonneg _)

/-- The numerator sum at a reduced denominator is a product of three Gauss
sums. The first two use frequency one, the third uses the actual target. -/
noncomputable def gaussCoefficient {d : ℕ} [NeZero d] (χ ψ : DirichletCharacter ℂ d) (m : ℕ) : ℂ :=
  (gaussSum χ ZMod.stdAddChar * gaussSum ψ ZMod.stdAddChar *
    gaussSum (χ*ψ)⁻¹ (ZMod.stdAddChar.mulShift (-(m : ZMod d)))) / (d.totient:ℂ)^2

theorem reduced_numerators {d : ℕ} [NeZero d] (χ ψ : DirichletCharacter ℂ d) (m : ℕ) :
    (∑ a ∈ (range d).filter (fun a => d.Coprime a), ZMod.stdAddChar ((a : ZMod d)*(-(m : ZMod d))) *
      amplitude χ a * amplitude ψ a) = gaussCoefficient χ ψ m := by
  let A := gaussSum χ ZMod.stdAddChar * gaussSum ψ ZMod.stdAddChar / (d.totient:ℂ)^2
  let F (z : ZMod d) := (χ*ψ)⁻¹ z * ZMod.stdAddChar ((-(m : ZMod d))*z)
  have shift (θ : DirichletCharacter ℂ d) (a : ℕ) (hc : a.Coprime d) :
      gaussSum θ (ZMod.stdAddChar.mulShift (a : ZMod d)) =
        θ⁻¹ (a : ZMod d) * gaussSum θ ZMod.stdAddChar :=
    gaussSum_mulShift_eq θ ZMod.stdAddChar (ZMod.unitOfCoprime a hc)
  rw [sum_filter]
  calc
    _ = ∑ a ∈ range d, A * F (a : ZMod d) := by
      apply sum_congr rfl
      intro a _
      by_cases hc : d.Coprime a
      · simp only [ite_eq_left hc,A,F,amplitude,shift _ _ hc.symm,mul_inv,MulChar.mul_apply]
        rw [mul_comm (a : ZMod d) (-(m : ZMod d))]
        ring
      · have hnu : ¬IsUnit (a : ZMod d) := fun hu => hc ((ZMod.isUnit_iff_coprime a d).mp hu).symm
        simp only [ite_eq_right hc,F,MulChar.map_nonunit _ hnu,zero_mul,mul_zero]
    _ = A * ∑ z : ZMod d, F z := by
      rw [← mul_sum,DyadicMixedB4DualCharacter.sum_natCast_range_eq_zmod F]
    _ = _ := by unfold A F gaussCoefficient gaussSum; simp only [AddChar.mulShift_apply]; ring

/-- Denominator coefficient for two primitive source characters. It is
defined independently of the finite ambient modulus used in the expansion. -/
noncomputable def coefficient {r s : ℕ} (α : DirichletCharacter ℂ r) (β : DirichletCharacter ℂ s)
    (m d : ℕ) : ℂ := by
  classical
  exact if hd : d ≠ 0 then
    let _ : NeZero d := ⟨hd⟩
    if h : r ∣ d ∧ s ∣ d then gaussCoefficient (changeLevel h.1 α) (changeLevel h.2 β) m else 0
  else 0

private theorem factors_iff_source {r q d : ℕ} [NeZero q] {α : DirichletCharacter ℂ r}
    (hα : α.IsPrimitive) (hr : r ∣ q) (hd : d ∣ q) :
    (changeLevel hr α).FactorsThrough d ↔ r ∣ d := by
  constructor
  · intro H
    simpa only [conductor_changeLevel,show α.conductor=r from hα] using
      conductor_dvd_of_mem_conductorSet (changeLevel hr α) H
  · intro h
    exact ⟨hd,changeLevel h α,changeLevel_trans α h hd⟩

private theorem descended_character {r q d : ℕ} [NeZero q] (α : DirichletCharacter ℂ r)
    (hr : r ∣ q) (hd : d ∣ q) (h : r ∣ d) (H : (changeLevel hr α).FactorsThrough d) :
    H.χ₀ = changeLevel h α :=
  changeLevel_injective hd (H.eq_changeLevel.symm.trans (changeLevel_trans α h hd))

theorem stable_denominator {r s q : ℕ} [NeZero q] {α : DirichletCharacter ℂ r}
    {β : DirichletCharacter ℂ s} (hα : α.IsPrimitive) (hβ : β.IsPrimitive)
    (hr : r ∣ q) (hs : s ∣ q) (m d : ℕ) (hd : d ∣ q) :
    denominatorTerm (changeLevel hr α) (changeLevel hs β) m d = coefficient α β m d := by
  have hd0 : d ≠ 0 := fun e => NeZero.ne q (Nat.eq_zero_of_zero_dvd (e ▸ hd))
  let _ : NeZero d := ⟨hd0⟩
  simp only [denominatorTerm,coefficient,dite_eq_left hd0]
  by_cases H : r ∣ d
  · have H' := (factors_iff_source hα hr hd).mpr H
    by_cases K : s ∣ d
    · have K' := (factors_iff_source hβ hs hd).mpr K
      simp only [dite_eq_left H',dite_eq_left K',dite_eq_left (And.intro H K),reduced_numerators,
        descended_character α hr hd H H',descended_character β hs hd K K']
    · have K' := mt (factors_iff_source hβ hs hd).mp K
      simp only [dite_eq_left H',dite_eq_right K',dite_eq_right (not_and_of_not_right _ K)]
  · have H' := mt (factors_iff_source hα hr hd).mp H
    simp only [dite_eq_right H',dite_eq_right (not_and_of_not_left _ H)]

private theorem estimate_at_multiple {r s d : ℕ} [NeZero r] [NeZero s] [NeZero d]
    (α : DirichletCharacter ℂ r) (β : DirichletCharacter ℂ s) (hr : r ∣ d) (hs : s ∣ d)
    (m : ℕ) (hm : 0 < m) :
    let R := Real.sqrt ((r*s:ℕ):ℝ)
    let M := ∑ f ∈ m.divisors, (f:ℝ)
    ‖gaussCoefficient (changeLevel hr α) (changeLevel hs β) m‖ ≤ R*R*(R*M)/(d.totient:ℝ)^2 := by
  intro R M
  let A := changeLevel hr α
  let B := changeLevel hs β
  let Z := (A*B)⁻¹
  have hrpos := Nat.mul_pos (NeZero.pos r) (NeZero.pos s)
  have cA : A.conductor ∣ r*s := by
    dsimp only [A]
    rw [conductor_changeLevel]
    exact α.conductor_dvd_level.trans (dvd_mul_right r s)
  have cB : B.conductor ∣ r*s := by
    dsimp only [B]
    rw [conductor_changeLevel]
    exact β.conductor_dvd_level.trans (dvd_mul_left s r)
  have cZ : Z.conductor ∣ r*s := by
    rw [show Z.conductor=(A*B).conductor from conductor_inv _]
    exact (conductor_mul_dvd_lcm_conductor A B).trans (Nat.lcm_dvd cA cB)
  have root {t : ℕ} (h : t ∣ r*s) : Real.sqrt t ≤ R :=
    Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_of_dvd hrpos h)
  have hA := (DyadicMixedB4CharacterFactorBound.norm_dirichlet_gauss_standard A).trans (root cA)
  have hB := (DyadicMixedB4CharacterFactorBound.norm_dirichlet_gauss_standard B).trans (root cB)
  have mass : (∑ f ∈ m.divisors.filter (fun f => Z.conductor*f ∣ d), (f:ℝ)) ≤ M :=
    sum_le_sum_of_subset_of_nonneg (filter_subset ..) (fun i _ _ => Nat.cast_nonneg i)
  have hsft := DyadicMixedB4CharacterFactorBound.norm_dirichlet_gauss_induced (dvd_refl d) Z m hm
  rw [changeLevel_self] at hsft
  have hZ := (DyadicMixedB4CharacterFactorBound.norm_gauss_neg_shift_le Z (m : ZMod d)).trans
    (hsft.trans (mul_le_mul (root cZ) mass (by positivity) (Real.sqrt_nonneg _)))
  change ‖(gaussSum A ZMod.stdAddChar * gaussSum B ZMod.stdAddChar *
    gaussSum Z (ZMod.stdAddChar.mulShift (-(m : ZMod d))))/(d.totient:ℂ)^2‖ ≤ _
  rw [norm_div,norm_pow,Complex.norm_natCast,norm_mul,norm_mul]
  exact div_le_div_of_nonneg_right (mul_le_mul
    (mul_le_mul hA hB (norm_nonneg _) (Real.sqrt_nonneg _)) hZ (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))) (sq_nonneg _)

private theorem totient_weight {d : ℕ} (hd : 0 < d) :
    1/(d.totient:ℝ)^2 ≤ 576 * (d:ℝ)^(-(3/2):ℝ) := by
  have h := DeepThreeQuarters.totient_ratio_le_rpow (show (0:ℝ)<1/4 by norm_num) d hd
  norm_num at h
  have dp : (0:ℝ)<d := by exact_mod_cast hd
  have hp : (0:ℝ)<d.totient := by exact_mod_cast Nat.totient_pos.mpr hd
  have invbound : 1/(d.totient:ℝ) ≤ 24*(d:ℝ)^(-(3/4):ℝ) := by
    calc
      _ = ((d:ℝ)/d.totient)/d := by field_simp
      _ ≤ (24*(d:ℝ)^(1/4:ℝ))/d := div_le_div_of_nonneg_right h dp.le
      _ = _ := by
        rw [show (-(3/4):ℝ)=1/4-1 by norm_num,Real.rpow_sub dp,Real.rpow_one]
        ring
  have square := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ 1/d.totient) invbound 2
  rw [div_pow,one_pow,mul_pow,← Real.rpow_mul_natCast dp.le] at square
  norm_num at square ⊢
  exact square

/-- Absolute convergence holds at every positive target. The divisor sum of
m controls the third Gauss sum uniformly as the reduced denominator varies. -/
theorem summable_coefficients {r s : ℕ} [NeZero r] [NeZero s]
    (α : DirichletCharacter ℂ r) (β : DirichletCharacter ℂ s) (m : ℕ) (hm : 0 < m) :
    Summable (fun d : ℕ => ‖coefficient α β m d‖) := by
  let R := Real.sqrt ((r*s:ℕ):ℝ)
  let M := ∑ f ∈ m.divisors, (f:ℝ)
  let C := R*R*(R*M)
  have hC : 0≤C := by dsimp [C,M,R]; positivity
  have summable : Summable (fun d : ℕ => (d:ℝ)^(-(3/2):ℝ)) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ (summable.mul_left (C*576))
  intro d
  by_cases hd : d=0
  · simp [coefficient,hd,Real.zero_rpow (by norm_num : (-(3/2):ℝ) ≠ 0)]
  have bound0 : 0 ≤ C*576*(d:ℝ)^(-(3/2):ℝ) := by positivity
  let _ : NeZero d := ⟨hd⟩
  by_cases h : r ∣ d ∧ s ∣ d
  · simp only [coefficient,dite_eq_left hd,dite_eq_left h]
    calc
      _ ≤ C/(d.totient:ℝ)^2 := estimate_at_multiple α β h.1 h.2 m hm
      _ = C*(1/(d.totient:ℝ)^2) := by ring
      _ ≤ C*(576*(d:ℝ)^(-(3/2):ℝ)) := mul_le_mul_of_nonneg_left (totient_weight (Nat.pos_of_ne_zero hd)) hC
      _ = _ := by ring
  · simpa only [coefficient,dite_eq_left hd,dite_eq_right h,norm_zero] using bound0

theorem ambient_sum {r s q : ℕ} [NeZero q] {α : DirichletCharacter ℂ r} {β : DirichletCharacter ℂ s}
    (hα : α.IsPrimitive) (hβ : β.IsPrimitive) (hr : r ∣ q) (hs : s ∣ q) (m : ℕ) :
    normalized (changeLevel hr α) (changeLevel hs β) m =
      ∑ d ∈ q.divisors, coefficient α β m d :=
  (finite_expansion _ _ m).trans (sum_congr rfl (fun d hd =>
    stable_denominator hα hβ hr hs m d (Nat.dvd_of_mem_divisors hd)))

open Filter Topology

private theorem cofinal_divisors (L : ℕ) (hL : L ≠ 0) :
    Tendsto (fun n : ℕ => insert 0 (L*n.factorial).divisors) atTop atTop := by
  apply tendsto_atTop.2
  intro S
  filter_upwards [eventually_ge_atTop (S.sup id)] with n hn
  intro d hd
  by_cases h : d=0
  · simp [h]
  apply mem_insert_of_mem
  have hdn : d≤n := (S.le_sup (f := id) hd).trans hn
  exact Nat.mem_divisors.mpr ⟨(Nat.dvd_factorial (Nat.pos_of_ne_zero h) hdn).trans
    (dvd_mul_left n.factorial L),mul_ne_zero hL n.factorial_ne_zero⟩

/-- Complete divisor sums at L times n! exhaust the absolutely convergent
series, starting from any positive base level L. -/
theorem partial_limit {r s : ℕ} [NeZero r] [NeZero s]
    (α : DirichletCharacter ℂ r) (β : DirichletCharacter ℂ s) (m : ℕ) (hm : 0 < m)
    (L : ℕ) (hL : L ≠ 0) :
    Tendsto (fun n : ℕ => ∑ d ∈ (L*n.factorial).divisors, coefficient α β m d)
      atTop (𝓝 (∑' d : ℕ, coefficient α β m d)) := by
  have h := (summable_coefficients α β m hm).of_norm.hasSum
  have hl := h.comp (cofinal_divisors L hL)
  apply hl.congr'
  filter_upwards with n
  simp [coefficient]

private theorem principal_real (q : ℕ) [NeZero q] (m : ℕ) :
    ‖normalized (1 : DirichletCharacter ℂ q) 1 m‖ = (normalized (1 : DirichletCharacter ℂ q) 1 m).re := by
  let N := ((univ : Finset (ZMod q)).filter (fun x => IsUnit x ∧ IsUnit ((m:ZMod q)-x))).card
  let v : ℝ := q*N/(q.totient:ℝ)^2
  have hv : 0≤v := by dsimp [v]; positivity
  have e : normalized (1 : DirichletCharacter ℂ q) 1 m = (v:ℂ) := by
    unfold normalized v
    rw [principal_count]
    push_cast
    rfl
  rw [e,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hv,Complex.ofReal_re]

/-- The absolute value of the full twisted singular series is at most the
ordinary singular series at each positive target. Both series converge
absolutely, with no zero-free hypothesis. -/
theorem infinite_domination {r s : ℕ} [NeZero r] [NeZero s]
    {α : DirichletCharacter ℂ r} {β : DirichletCharacter ℂ s}
    (hα : α.IsPrimitive) (hβ : β.IsPrimitive) (m : ℕ) (hm : 0 < m) :
    ‖∑' d : ℕ, coefficient α β m d‖ ≤
      (∑' d : ℕ, coefficient (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m d).re := by
  let L := r*s
  have hL : L ≠ 0 := mul_ne_zero (NeZero.ne r) (NeZero.ne s)
  let oneχ : DirichletCharacter ℂ 1 := 1
  have main := partial_limit oneχ oneχ m hm L hL
  apply le_of_tendsto_of_tendsto' (partial_limit α β m hm L hL).norm (Complex.continuous_re.tendsto _ |>.comp main)
  intro n
  let q := L*n.factorial
  let _ : NeZero q := ⟨mul_ne_zero hL n.factorial_ne_zero⟩
  have hr : r ∣ q := (dvd_mul_right r s).trans (dvd_mul_right L n.factorial)
  have hs : s ∣ q := (dvd_mul_left s r).trans (dvd_mul_right L n.factorial)
  have ordinary := ambient_sum (α := oneχ) (β := oneχ) isPrimitive_one_level_one
    isPrimitive_one_level_one (one_dvd q) (one_dvd q) m
  simp only [oneχ,map_one] at ordinary
  change ‖∑ d ∈ q.divisors, coefficient α β m d‖ ≤
    (∑ d ∈ q.divisors, coefficient oneχ oneχ m d).re
  rw [← ambient_sum hα hβ hr hs m,← ordinary,← principal_real]
  simpa only [← finite_expansion] using domination (changeLevel hr α) (changeLevel hs β) m

end Conjectures.Goldbach.TwistedGoldbachSingularSeries

/-! Reduction of an admissible binary residue pair through any divisor has
uniform fibers. This lets one recover the ratio of the full twisted and
ordinary singular series from a single modulus containing both conductors. -/

namespace Conjectures.Goldbach.TwistedGoldbachConductorRatio

open Finset DirichletCharacter
open scoped BigOperators Classical

def admissible {n : ℕ} (m x : ZMod n) : Prop := IsUnit x ∧ IsUnit (m-x)

noncomputable def fiber {q L : ℕ} [NeZero q] (h : L ∣ q) (m : ZMod q) (u : ZMod L) :
    Finset (ZMod q) := univ.filter (fun x => admissible m x ∧ ZMod.castHom h (ZMod L) x=u)

private theorem unit_criterion {q : ℕ} [NeZero q] (x : ZMod q) :
    IsUnit x ↔ ∀ (p : ℕ), p.Prime → ∀ h : p ∣ q, ZMod.castHom h (ZMod p) x ≠ 0 := by
  constructor
  · intro hx p hp h
    let _ : Fact p.Prime := ⟨hp⟩
    exact (hx.map (ZMod.castHom h (ZMod p))).ne_zero
  · obtain ⟨n,rfl⟩ : ∃ n : ℕ, (n : ZMod q)=x := ⟨x.val,ZMod.natCast_zmod_val x⟩
    intro H
    apply (ZMod.isUnit_iff_coprime n q).mpr
    apply Nat.coprime_of_dvd
    intro p hp hn hq
    exact H p hp hq (by rw [map_natCast,ZMod.natCast_eq_zero_iff]; exact hn)

private theorem reduce_twice {p q L : ℕ} [NeZero q] (h : L ∣ q) (g : p ∣ L) (x : ZMod q) :
    ZMod.castHom g (ZMod p) (ZMod.castHom h (ZMod L) x) = ZMod.castHom (g.trans h) (ZMod p) x := by
  obtain ⟨n,rfl⟩ : ∃ n : ℕ, (n : ZMod q)=x := ⟨x.val,ZMod.natCast_zmod_val x⟩
  simp only [map_natCast]

private theorem preserving_shift {q L : ℕ} [NeZero q] [NeZero L] (h : L ∣ q) (b : ZMod L) :
    ∃ c : ZMod q, ZMod.castHom h (ZMod L) c=b ∧
      ∀ p : ℕ, p.Prime → ∀ hp : p ∣ q, ¬p ∣ L → ZMod.castHom hp (ZMod p) c=0 := by
  let S := q.primeFactors.filter (fun p => ¬p ∣ L)
  let D := ∏ p ∈ S, p
  have hc : D.Coprime L := Nat.coprime_prod_left_iff.mpr (fun p hp =>
    (Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1).coprime_iff_not_dvd.mpr (mem_filter.mp hp).2)
  let u := ZMod.unitOfCoprime D hc
  let n := ((↑u⁻¹ : ZMod L)*b).val
  refine ⟨((D*n:ℕ):ZMod q),?_,?_⟩
  · rw [map_natCast,Nat.cast_mul,show (n : ZMod L) = (↑u⁻¹ : ZMod L)*b from ZMod.natCast_zmod_val _]
    change (↑u : ZMod L)*(↑u⁻¹*b)=b
    simp
  · intro p hp hq hL
    have hpS : p ∈ S := mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hp,hq,NeZero.ne q⟩,hL⟩
    rw [map_natCast,ZMod.natCast_eq_zero_iff]
    exact (dvd_prod_of_mem (fun z : ℕ => z) hpS).trans (dvd_mul_right D n)

private theorem patch_unit {q L : ℕ} [NeZero q] (h : L ∣ q) (x c : ZMod q) (hx : IsUnit x)
    (hl : IsUnit (ZMod.castHom h (ZMod L) (x+c)))
    (away : ∀ p : ℕ, p.Prime → ∀ hp : p ∣ q, ¬p ∣ L → ZMod.castHom hp (ZMod p) c=0) :
    IsUnit (x+c) := by
  apply (unit_criterion _).mpr
  intro p hprime hp
  by_cases hL : p ∣ L
  · let _ : Fact p.Prime := ⟨hprime⟩
    rw [← reduce_twice h hL]
    exact (hl.map (ZMod.castHom hL (ZMod p))).ne_zero
  · rw [map_add,away p hprime hp hL,add_zero]
    exact (unit_criterion x).mp hx p hprime hp

private theorem fiber_card_le {q L : ℕ} [NeZero q] [NeZero L] (h : L ∣ q)
    (m : ZMod q) (u v : ZMod L) (hv : admissible (ZMod.castHom h (ZMod L) m) v) :
    (fiber h m u).card ≤ (fiber h m v).card := by
  let π := ZMod.castHom h (ZMod L)
  obtain ⟨c,hc,away⟩ := preserving_shift h (v-u)
  apply card_le_card_of_injOn (fun x : ZMod q => x+c)
  · intro x hx
    obtain ⟨⟨hxunit,hother⟩,hπ⟩ := (mem_filter.mp hx).2
    have image : π (x+c)=v := by rw [map_add,hπ,hc]; abel
    refine mem_filter.mpr ⟨mem_univ _,⟨⟨?_,?_⟩,image⟩⟩
    · apply patch_unit h x c hxunit _ away
      exact image ▸ hv.1
    · rw [show m-(x+c)=(m-x)+(-c) by ring]
      apply patch_unit h (m-x) (-c) hother
      · change IsUnit (π ((m-x)+(-c)))
        rw [show (m-x)+(-c)=m-(x+c) by ring,map_sub,image]
        exact hv.2
      · intro p hprime hp hL
        rw [map_neg,away p hprime hp hL,neg_zero]
  · intro x _ y _ e
    exact add_right_cancel e

/-- Every lower admissible pair has the same number of admissible lifts,
including when q has prime factors absent from L. -/
theorem uniform_fibers {q L : ℕ} [NeZero q] [NeZero L] (h : L ∣ q) (m : ZMod q) :
    ∃ K : ℕ, ∀ u : ZMod L, (fiber h m u).card =
      if admissible (ZMod.castHom h (ZMod L) m) u then K else 0 := by
  let π := ZMod.castHom h (ZMod L)
  have empty (u : ZMod L) (hu : ¬admissible (π m) u) : fiber h m u=∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨⟨h₁,h₂⟩,e⟩ := (mem_filter.mp hx).2
    apply hu
    rw [← e]
    exact ⟨h₁.map π,by simpa only [map_sub] using h₂.map π⟩
  by_cases H : ∃ u : ZMod L, admissible (π m) u
  · obtain ⟨u,hu⟩ := H
    refine ⟨(fiber h m u).card,fun v => ?_⟩
    by_cases hv : admissible (π m) v
    · rw [ite_eq_left hv]
      exact le_antisymm (fiber_card_le h m v u hu) (fiber_card_le h m u v hv)
    · rw [ite_eq_right hv,empty v hv,card_empty]
  · refine ⟨0,fun u => ?_⟩
    have hu : ¬admissible (π m) u := fun h => H ⟨u,h⟩
    rw [ite_eq_right hu,empty u hu,card_empty]

private theorem reduce_admissible {q L : ℕ} (h : L ∣ q) {m x : ZMod q} (hx : admissible m x) :
    admissible (ZMod.castHom h (ZMod L) m) (ZMod.castHom h (ZMod L) x) :=
  ⟨hx.1.map _,by simpa only [map_sub] using hx.2.map (ZMod.castHom h (ZMod L))⟩

theorem fiber_weight {q L : ℕ} [NeZero q] [NeZero L] (h : L ∣ q) (m : ZMod q) :
    ∃ K : ℕ, ∀ F : ZMod L → ℂ,
      (∑ x ∈ univ.filter (admissible m), F (ZMod.castHom h (ZMod L) x)) =
        (K:ℂ)*∑ y ∈ univ.filter (admissible (ZMod.castHom h (ZMod L) m)), F y := by
  let π := ZMod.castHom h (ZMod L)
  let H := univ.filter (admissible m)
  let T := univ.filter (admissible (π m))
  obtain ⟨K,hK⟩ := uniform_fibers h m
  refine ⟨K, fun F => ?_⟩
  have maps : ∀ x ∈ H, π x ∈ T := fun x hx =>
    mem_filter.mpr ⟨mem_univ _,reduce_admissible h (mem_filter.mp hx).2⟩
  have group (u : ZMod L) : H.filter (fun x => π x=u) = fiber h m u := by
    ext x
    simp only [H,π,fiber,mem_filter,mem_univ,true_and]
  change (∑ x ∈ H, F (π x)) = (K:ℂ)*∑ u ∈ T, F u
  rw [← sum_fiberwise_of_maps_to' maps F,mul_sum]
  apply sum_congr rfl
  intro u hu
  have hu' : admissible (ZMod.castHom h (ZMod L) m) u := (mem_filter.mp hu).2
  rw [group,sum_const,nsmul_eq_mul,hK u,ite_eq_left hu']

noncomputable def J {q : ℕ} [NeZero q] (χ ψ : DirichletCharacter ℂ q) (m : ZMod q) : ℂ :=
  ∑ x : ZMod q, χ x * ψ (m-x)

private theorem restricted_eq {q : ℕ} [NeZero q] (χ ψ : DirichletCharacter ℂ q) (m : ZMod q) :
    (∑ x ∈ univ.filter (admissible m), χ x * ψ (m-x)) = J χ ψ m := by
  apply sum_subset (filter_subset ..)
  intro x _ hx
  by_cases hu : IsUnit x
  · have hv : ¬IsUnit (m-x) := fun hv => hx (mem_filter.mpr ⟨mem_univ _,hu,hv⟩)
    simp [ψ.map_nonunit hv]
  · simp [χ.map_nonunit hu]

/-- The same lift multiplicity works for all pairs of characters at L. -/
theorem jacobi_lift {q L : ℕ} [NeZero q] [NeZero L] (h : L ∣ q) (m : ZMod q) :
    ∃ K : ℕ, ∀ χ ψ : DirichletCharacter ℂ L,
      J (changeLevel h χ) (changeLevel h ψ) m = (K:ℂ)*J χ ψ (ZMod.castHom h (ZMod L) m) := by
  let π := ZMod.castHom h (ZMod L)
  obtain ⟨K,hK⟩ := fiber_weight h m
  refine ⟨K,fun χ ψ => ?_⟩
  have reduce (θ : DirichletCharacter ℂ L) (x : ZMod q) (hx : IsUnit x) :
      changeLevel h θ x = θ (π x) := by
    simpa only [π,IsUnit.unit_spec,ZMod.castHom_apply] using changeLevel_eq_cast_of_dvd θ h hx.unit
  rw [← restricted_eq,← restricted_eq χ ψ]
  calc
    _ = ∑ x ∈ univ.filter (admissible m), χ (π x)*ψ (π m-π x) := by
      apply sum_congr rfl
      intro x hx
      have h' := (mem_filter.mp hx).2
      rw [reduce χ x h'.1,reduce ψ (m-x) h'.2,map_sub]
    _ = _ := hK (fun x => χ x*ψ (π m-x))

open TwistedGoldbachSingularSeries

private theorem finite_cross {q L : ℕ} [NeZero q] [NeZero L] (h : L ∣ q)
    (χ ψ : DirichletCharacter ℂ L) (m : ℕ) :
    normalized (changeLevel h χ) (changeLevel h ψ) m * J (1 : DirichletCharacter ℂ L) 1 (m : ZMod L) =
      normalized (1 : DirichletCharacter ℂ q) 1 m * J χ ψ (m : ZMod L) := by
  obtain ⟨K,hK⟩ := jacobi_lift h (m : ZMod q)
  have weighted := hK χ ψ
  have ordinary := hK 1 1
  simp only [map_natCast,map_one] at weighted ordinary
  change ((q:ℂ)*J (changeLevel h χ) (changeLevel h ψ) (m : ZMod q)/(q.totient:ℂ)^2)*_ =
    ((q:ℂ)*J (1 : DirichletCharacter ℂ q) 1 (m : ZMod q)/(q.totient:ℂ)^2)*_
  rw [weighted,ordinary]
  ring

open Filter Topology

/-- The ratio of the two singular series is determined at any single common
multiple of the conductors. The identity also holds at targets for which the
principal residue count vanishes. -/
theorem conductor_identity {r s L : ℕ} [NeZero r] [NeZero s] [NeZero L]
    {α : DirichletCharacter ℂ r} {β : DirichletCharacter ℂ s}
    (hα : α.IsPrimitive) (hβ : β.IsPrimitive) (hr : r ∣ L) (hs : s ∣ L) (m : ℕ) (hm : 0 < m) :
    (∑' d : ℕ, coefficient α β m d) * J (1 : DirichletCharacter ℂ L) 1 (m : ZMod L) =
      (∑' d : ℕ, coefficient (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m d) *
        J (changeLevel hr α) (changeLevel hs β) (m : ZMod L) := by
  let oneχ : DirichletCharacter ℂ 1 := 1
  have left := (partial_limit α β m hm L (NeZero.ne L)).mul_const (J (1 : DirichletCharacter ℂ L) 1 (m : ZMod L))
  have right := (partial_limit oneχ oneχ m hm L (NeZero.ne L)).mul_const
    (J (changeLevel hr α) (changeLevel hs β) (m : ZMod L))
  apply tendsto_nhds_unique_of_eventuallyEq left right
  filter_upwards with n
  let q := L*n.factorial
  let _ : NeZero q := ⟨mul_ne_zero (NeZero.ne L) n.factorial_ne_zero⟩
  have h : L ∣ q := dvd_mul_right L n.factorial
  have ordinary := ambient_sum (α := oneχ) (β := oneχ) isPrimitive_one_level_one
    isPrimitive_one_level_one (one_dvd q) (one_dvd q) m
  simp only [oneχ,map_one] at ordinary
  change ((∑ d ∈ q.divisors, coefficient α β m d)*_) =
    ((∑ d ∈ q.divisors, coefficient oneχ oneχ m d)*_)
  rw [← ambient_sum hα hβ (hr.trans h) (hs.trans h) m, ← ordinary,
    changeLevel_trans α hr h, changeLevel_trans β hs h]
  exact finite_cross h (changeLevel hr α) (changeLevel hs β) m

/-- The principal-character convolution counts admissible residues. -/
theorem principal_card {L : ℕ} [NeZero L] (m : ZMod L) :
    J (1 : DirichletCharacter ℂ L) 1 m = ((univ.filter (admissible m)).card:ℂ) := by
  rw [← restricted_eq]
  calc
    _ = ∑ _x ∈ univ.filter (admissible m), (1:ℂ) := by
      apply sum_congr rfl
      intro x hx
      have H := (mem_filter.mp hx).2
      rw [MulChar.one_apply H.1,MulChar.one_apply H.2,one_mul]
    _ = _ := by simp

/-- An explicit admissible residue for every even target and every positive
modulus. At a prime where the target is one the polynomial selects minus one,
and otherwise it selects one. -/
theorem admissible_even (L : ℕ) [NeZero L] (m : ℕ) (he : Even m) :
    ∃ x : ZMod L, admissible (m : ZMod L) x := by
  let x : ZMod L := 2*((m:ZMod L)-1)^L.factorial-1
  have both (p : ℕ) (hp : p.Prime) (h : p ∣ L) :
      ZMod.castHom h (ZMod p) x ≠ 0 ∧ ZMod.castHom h (ZMod p) ((m:ZMod L)-x) ≠ 0 := by
    let _ : Fact p.Prime := ⟨hp⟩
    have red : ZMod.castHom h (ZMod p) x = 2*((m:ZMod p)-1)^L.factorial-1 := by
      simp only [x,map_sub,map_mul,map_ofNat,map_pow,map_natCast,map_one]
    have red' : ZMod.castHom h (ZMod p) ((m:ZMod L)-x) =
        (m:ZMod p) - (2*((m:ZMod p)-1)^L.factorial-1) := by
      rw [map_sub,map_natCast,red]
    rw [red,red']
    by_cases h1 : (m:ZMod p)=1
    · have p2 : p≠2 := by
        rintro rfl
        have hz : (m : ZMod 2)=0 := (ZMod.natCast_eq_zero_iff m 2).mpr (even_iff_two_dvd.mp he)
        exact one_ne_zero (h1.symm.trans hz)
      have nz : (2 : ZMod p) ≠ 0 := fun hz =>
        p2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp ((ZMod.natCast_eq_zero_iff 2 p).mp hz))
      simp only [h1,sub_self,zero_pow L.factorial_ne_zero,mul_zero,zero_sub,sub_neg_eq_add]
      exact ⟨neg_ne_zero.mpr one_ne_zero,by simpa only [one_add_one_eq_two] using nz⟩
    · have hpL : p≤L := Nat.le_of_dvd (NeZero.pos L) h
      obtain ⟨t,ht⟩ := Nat.dvd_factorial (Nat.sub_pos_of_lt hp.one_lt) ((Nat.sub_le p 1).trans hpL)
      have u : ((m:ZMod p)-1)^L.factorial = 1 := by
        rw [ht,pow_mul,ZMod.pow_card_sub_one_eq_one (sub_ne_zero.mpr h1),one_pow]
      rw [u,mul_one,show (2:ZMod p)-1=1 by ring]
      exact ⟨one_ne_zero,sub_ne_zero.mpr h1⟩
  exact ⟨x,(unit_criterion x).mpr (fun p hp h => (both p hp h).1),
    (unit_criterion _).mpr (fun p hp h => (both p hp h).2)⟩

/-- At even targets the ordinary count in the denominator is positive, so the
finite conductor-level correction can be used as a literal complex ratio. -/
theorem exact_ratio {r s L : ℕ} [NeZero r] [NeZero s] [NeZero L]
    {α : DirichletCharacter ℂ r} {β : DirichletCharacter ℂ s}
    (hα : α.IsPrimitive) (hβ : β.IsPrimitive) (hr : r ∣ L) (hs : s ∣ L) (m : ℕ)
    (hm : 0 < m) (he : Even m) :
    (∑' d : ℕ, coefficient α β m d) =
      (∑' d : ℕ, coefficient (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m d) *
        (J (changeLevel hr α) (changeLevel hs β) (m : ZMod L) /
          ((univ.filter (admissible (m : ZMod L))).card:ℂ)) := by
  obtain ⟨x,hx⟩ := admissible_even L m he
  have positive := card_pos.mpr (show (univ.filter (admissible (m : ZMod L))).Nonempty from
    ⟨x,mem_filter.mpr ⟨mem_univ _,hx⟩⟩)
  rw [← mul_div_assoc,eq_div_iff (Nat.cast_ne_zero.mpr positive.ne')]
  rw [← principal_card]
  exact conductor_identity hα hβ hr hs m hm

/-- At zero, orthogonality selects the inverse pair of characters. -/
theorem zero_jacobi {L : ℕ} [NeZero L] (A B : DirichletCharacter ℂ L) :
    J A B 0 = if A*B=1 then B (-1)*(L.totient:ℂ) else 0 := by
  have eqn (x : ZMod L) : A x * B (0-x) = B (-1)*(A*B) x := by
    rw [zero_sub,← neg_one_mul x,map_mul,MulChar.mul_apply]
    ring
  simp only [J,eqn,← mul_sum]
  by_cases h : A*B=1
  · rw [ite_eq_left h,h,MulChar.sum_one_eq_card_units,ZMod.card_units_eq_totient]
  · rw [ite_eq_right h,MulChar.sum_eq_zero_of_ne_one h,mul_zero]

/-- On a multiple of both conductors, all off-diagonal character pairs
vanish. The surviving inverse pair retains its parity at minus one. -/
theorem at_conductor_multiple {r s L : ℕ} [NeZero r] [NeZero s] [NeZero L]
    {α : DirichletCharacter ℂ r} {β : DirichletCharacter ℂ s} (hα : α.IsPrimitive) (hβ : β.IsPrimitive)
    (hr : r ∣ L) (hs : s ∣ L) (m : ℕ) (hm : 0 < m) (divides : L ∣ m) :
    (∑' d : ℕ, coefficient α β m d) = if changeLevel hr α * changeLevel hs β = 1 then
      (∑' d : ℕ, coefficient (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m d) *
      changeLevel hs β (-1) else 0 := by
  have ident := conductor_identity hα hβ hr hs m hm
  have hz := (ZMod.natCast_eq_zero_iff m L).mpr divides
  have principal : J (1 : DirichletCharacter ℂ L) 1 0 = (L.totient:ℂ) := by
    rw [zero_jacobi]
    simp [MulChar.one_apply (isUnit_neg_one : IsUnit (-1 : ZMod L))]
  rw [hz,principal,zero_jacobi] at ident
  apply mul_right_cancel₀ (Nat.cast_ne_zero.mpr (NeZero.ne L.totient) : (L.totient:ℂ) ≠ 0)
  split_ifs at ident ⊢ with h
  · simpa only [mul_assoc] using ident
  · simpa only [zero_mul,mul_zero] using ident

theorem unequal_conductors_vanish {r s L : ℕ} [NeZero r] [NeZero s] [NeZero L]
    {α : DirichletCharacter ℂ r} {β : DirichletCharacter ℂ s} (hα : α.IsPrimitive) (hβ : β.IsPrimitive)
    (hr : r ∣ L) (hs : s ∣ L) (hne : r≠s) (m : ℕ) (hm : 0 < m) (divides : L ∣ m) :
    (∑' d : ℕ, coefficient α β m d) = 0 := by
  rw [at_conductor_multiple hα hβ hr hs m hm divides]
  apply ite_eq_right
  intro hab
  have hinv : changeLevel hs β = (changeLevel hr α)⁻¹ := eq_inv_of_mul_eq_one_right hab
  have e := congrArg DirichletCharacter.conductor hinv
  simp only [conductor_inv,conductor_changeLevel,show α.conductor=r from hα,
    show β.conductor=s from hβ] at e
  exact hne e.symm

end Conjectures.Goldbach.TwistedGoldbachConductorRatio

/-! Finite character-twisted Goldbach densities at squarefree levels.
The sum is over all residues, with the two Dirichlet characters extended
by zero on nonunits. No primitivity or reality hypothesis is needed.
The comparison is with the untwisted density at the same level and target. -/

namespace Conjectures.Goldbach.SquarefreeTwistedGoldbachDensity

open Finset
open scoped BigOperators Classical

noncomputable def localSum {p : ℕ} [Fact p.Prime] (χ ψ : DirichletCharacter ℂ p)
    (m : ZMod p) : ℂ := ∑ a : ZMod p, χ a * ψ (m-a)

private theorem norm_jacobi {p : ℕ} [hp : Fact p.Prime] {χ ψ : DirichletCharacter ℂ p}
    (hχ : χ ≠ 1) (hψ : ψ ≠ 1) (hχψ : χ*ψ ≠ 1) :
    ‖jacobiSum χ ψ‖ = Real.sqrt p := by
  have hc : star (jacobiSum χ ψ) = jacobiSum χ⁻¹ ψ⁻¹ := by
    simp only [jacobiSum, star_sum, star_mul', MulChar.star_apply']
  have hchar : ringChar ℂ ≠ ringChar (ZMod p) := by
    rw [ZMod.ringChar_zmod_n, ringChar.eq ℂ 0]
    exact hp.out.ne_zero.symm
  have h := congrArg (fun z : ℂ => ‖z‖) (jacobiSum_mul_jacobiSum_inv hchar hχ hψ hχψ)
  simp only [← hc, norm_mul, norm_star, ZMod.card, Complex.norm_natCast] at h
  nlinarith [Real.sq_sqrt (Nat.cast_nonneg p), Real.sqrt_nonneg (p:ℝ), norm_nonneg (jacobiSum χ ψ)]

private theorem localSum_nonzero {p : ℕ} [Fact p.Prime] (χ ψ : DirichletCharacter ℂ p)
    {m : ZMod p} (hm : m ≠ 0) : localSum χ ψ m = (χ m*ψ m)*jacobiSum χ ψ := by
  have h := Equiv.sum_comp (Equiv.mulLeft₀ m hm) (fun a : ZMod p => χ a * ψ (m-a))
  calc
    _ = ∑ a : ZMod p, χ (m*a) * ψ (m-m*a) := h.symm
    _ = ∑ a : ZMod p, (χ m*ψ m)*(χ a*ψ (1-a)) := by
      apply sum_congr rfl
      intro a _
      rw [← mul_one_sub, map_mul, map_mul]
      ring
    _ = _ := (mul_sum ..).symm

private theorem localSum_zero {p : ℕ} [hp : Fact p.Prime] (χ ψ : DirichletCharacter ℂ p) :
    localSum χ ψ 0 = ψ (-1)*(if χ*ψ = 1 then ((p-1 : ℕ) : ℂ) else 0) := by
  classical
  have h : localSum χ ψ 0 = ψ (-1)*∑ a : ZMod p, (χ*ψ) a := by
    unfold localSum
    rw [mul_sum]
    apply sum_congr rfl
    intro a _
    rw [zero_sub, ← neg_one_mul a, map_mul, MulChar.mul_apply]
    ring
  rw [h]
  by_cases hprod : χ*ψ = 1
  · simp only [hprod, ite_true, MulChar.sum_one_eq_card_units, ZMod.card_units_eq_totient,
      Nat.totient_prime hp.out]
  · rw [ite_eq_right hprod, MulChar.sum_eq_zero_of_ne_one hprod]

/-- Complete table, including the primes 2 and 3 and imprimitive local factors. -/
theorem local_norm {p : ℕ} [hp : Fact p.Prime] (χ ψ : DirichletCharacter ℂ p) (m : ZMod p) :
    ‖localSum χ ψ m‖ =
      if m=0 then (if χ*ψ=1 then (p:ℝ)-1 else 0)
      else if χ=1 ∧ ψ=1 then (p:ℝ)-2
      else if χ=1 ∨ ψ=1 ∨ χ*ψ=1 then 1 else Real.sqrt p := by
  classical
  by_cases hm : m=0
  · subst m
    rw [ite_eq_left rfl,localSum_zero,norm_mul,ψ.norm_neg_one,one_mul]
    by_cases h : χ*ψ=1
    · rw [ite_eq_left h,ite_eq_left h,Complex.norm_natCast,Nat.cast_sub hp.out.one_le,Nat.cast_one]
    · simp [h]
  have hu := isUnit_iff_ne_zero.mpr hm
  have v (θ : DirichletCharacter ℂ p) : ‖θ m‖=1 := θ.unit_norm_eq_one hu.unit
  rw [ite_eq_right hm,localSum_nonzero χ ψ hm,norm_mul,norm_mul,
    v χ,v ψ,one_mul,one_mul]
  by_cases hχ : χ=1
  · subst χ
    by_cases hψ : ψ=1
    · subst ψ
      have hpos : (0:ℝ) ≤ p-2 := sub_nonneg.mpr (by exact_mod_cast hp.out.two_le)
      simp only [and_self,ite_true,jacobiSum_one_one,ZMod.card]
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_ofNat 2, ← Complex.ofReal_sub,
        Complex.norm_real, Real.norm_of_nonneg hpos]
    · simp [hψ,jacobiSum_one_nontrivial hψ]
  by_cases hψ : ψ=1
  · subst ψ
    rw [jacobiSum_comm,jacobiSum_one_nontrivial hχ]
    simp [hχ]
  by_cases hprod : χ*ψ=1
  · have hinv : ψ=χ⁻¹ := eq_inv_of_mul_eq_one_right hprod
    simp only [hχ,hψ,hprod,false_and,ite_false,false_or,ite_true]
    rw [hinv,jacobiSum_nontrivial_inv hχ,norm_neg,χ.norm_neg_one]
  · simp [hχ,hψ,hprod,norm_jacobi hχ hψ hprod]

private theorem local_le_principal {p : ℕ} [Fact p.Prime] (χ ψ : DirichletCharacter ℂ p)
    (m : ZMod p) : ‖localSum χ ψ m‖ ≤ ‖localSum (1 : DirichletCharacter ℂ p) 1 m‖ := by
  classical
  let U := univ.filter (fun a : ZMod p => IsUnit a ∧ IsUnit (m-a))
  have restrict (α β : DirichletCharacter ℂ p) :
      (∑ a ∈ U, α a * β (m-a)) = localSum α β m := by
    apply sum_subset (filter_subset _ _)
    intro a _ ha
    by_cases hu : IsUnit a
    · have hv : ¬IsUnit (m-a) := fun hv => ha (mem_filter.mpr ⟨mem_univ _,hu,hv⟩)
      simp [β.map_nonunit hv]
    · simp [α.map_nonunit hu]
  have triv : localSum (1 : DirichletCharacter ℂ p) 1 m = (U.card:ℂ) := by
    rw [← restrict]
    calc
      _ = ∑ _a ∈ U, (1:ℂ) := by
        apply sum_congr rfl
        intro a ha
        obtain ⟨_, hu, hv⟩ := mem_filter.mp ha
        rw [MulChar.one_apply hu,MulChar.one_apply hv,one_mul]
      _ = _ := by simp
  rw [triv,Complex.norm_natCast,← restrict]
  calc
    _ ≤ ∑ a ∈ U, ‖χ a * ψ (m-a)‖ := norm_sum_le _ _
    _ ≤ ∑ _a ∈ U, (1:ℝ) := by
      apply sum_le_sum
      intro a _
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_right (χ.norm_le_one _) (norm_nonneg _)).trans
        (by simpa only [one_mul] using ψ.norm_le_one (m-a))
    _ = _ := by simp

section Squarefree
variable {k : ℕ} (p : Fin k → ℕ) [∀ i, Fact (p i).Prime] [NeZero (∏ i, p i)]
    (cop : Pairwise (fun i j => (p i).Coprime (p j)))
    (χ ψ : (i : Fin k) → DirichletCharacter ℂ (p i))

/-- The complete sum over one actual residue ring, with both characters
assembled from their components by the Chinese remainder isomorphism. -/
noncomputable def twisted (m : ZMod (∏ i, p i)) : ℂ :=
  let e := ZMod.prodEquivPi p cop
  ∑ a : ZMod (∏ i, p i), (∏ i, χ i (e a i)) * (∏ i, ψ i (e (m-a) i))

theorem factorization (m : ZMod (∏ i, p i)) :
    twisted p cop χ ψ m = ∏ i, localSum (χ i) (ψ i) (ZMod.prodEquivPi p cop m i) := by
  classical
  let e := ZMod.prodEquivPi p cop
  let f (i : Fin k) (a : ZMod (p i)) := χ i a * ψ i (e m i-a)
  have hstep (a : ZMod (∏ i, p i)) :
      (∏ i, χ i (e a i)) * (∏ i, ψ i (e (m-a) i)) = ∏ i, f i (e a i) := by
    rw [← prod_mul_distrib,map_sub]
    rfl
  calc
    _ = ∑ a : ZMod (∏ i, p i), ∏ i, f i (e a i) := sum_congr rfl (fun a _ => hstep a)
    _ = ∑ a : (i : Fin k) → ZMod (p i), ∏ i, f i (a i) :=
      Equiv.sum_comp e.toEquiv (fun a => ∏ i, f i (a i))
    _ = _ := (Fintype.prod_sum f).symm

/-- A nonprincipal component at a prime away from the target costs a factor
of at least two for p ≥ 11. At every other prime the cost is at most one.
The saving therefore multiplies across the *distinct* offending primes. -/
theorem suppression (m : ZMod (∏ i, p i)) :
    let e := ZMod.prodEquivPi p cop
    let B := univ.filter (fun i => 11 ≤ p i ∧ e m i ≠ 0 ∧ (χ i ≠ 1 ∨ ψ i ≠ 1))
    (2:ℝ)^B.card * ‖twisted p cop χ ψ m‖ ≤
      ‖twisted p cop (fun _ => 1) (fun _ => 1) m‖ := by
  classical
  intro e B
  let w (i : Fin k) : ℝ := if i ∈ B then 2 else 1
  have hweight : (∏ i, w i) = (2:ℝ)^B.card := by
    simp [w, Finset.prod_ite_mem]
  rw [← hweight, factorization, factorization, norm_prod, norm_prod, ← prod_mul_distrib]
  apply prod_le_prod₀
  · intro i _
    exact mul_nonneg (by dsimp [w]; split <;> norm_num) (norm_nonneg _)
  · intro i _
    by_cases hi : i ∈ B
    · have ⟨hp,hm,hχψ⟩ := (mem_filter.mp hi).2
      change (ZMod.prodEquivPi p cop) m i ≠ 0 at hm
      have hn : ¬(χ i=1 ∧ ψ i=1) := by tauto
      have hpR : (11:ℝ) ≤ p i := by exact_mod_cast hp
      have hs := Real.sq_sqrt (Nat.cast_nonneg (p i))
      have hroot : 3 ≤ Real.sqrt (p i) := by nlinarith [Real.sqrt_nonneg (p i)]
      have hsmall : 2*Real.sqrt (p i) ≤ p i-2 := by nlinarith [sq_nonneg (Real.sqrt (p i)-3)]
      rw [show w i = 2 by simp [w,hi],local_norm,local_norm]
      simp only [hm,ite_false,hn,ite_true,and_self]
      split <;> linarith
    · rw [show w i = 1 by simp [w,hi],one_mul]
      exact local_le_principal _ _ _

/-- A prime dividing the target kills the entire sum when the two local
characters do not cancel one another on its units. -/
theorem vanishing (m : ZMod (∏ i, p i)) (i : Fin k)
    (hm : ZMod.prodEquivPi p cop m i = 0) (h : χ i * ψ i ≠ 1) :
    twisted p cop χ ψ m = 0 := by
  rw [factorization]
  apply prod_eq_zero (mem_univ i)
  apply norm_eq_zero.mp
  rw [local_norm,ite_eq_left hm,ite_eq_right h]

private theorem dft_convolution {N : ℕ} [NeZero N] (f g : ZMod N → ℂ) :
    ZMod.dft (fun m => ∑ a, f a * g (m-a)) =
      fun t => ZMod.dft f t * ZMod.dft g t := by
  classical
  funext t
  simp only [ZMod.dft_apply,smul_eq_mul]
  calc
    _ = ∑ a, ∑ m : ZMod N, ZMod.stdAddChar (-(m*t)) * (f a*g (m-a)) := by
      simp only [mul_sum]
      rw [sum_comm]
    _ = ∑ a, ∑ b : ZMod N, (ZMod.stdAddChar (-(a*t))*f a) *
        (ZMod.stdAddChar (-(b*t))*g b) := by
      apply sum_congr rfl
      intro a _
      let F (m : ZMod N) := ZMod.stdAddChar (-(m*t)) * (f a*g (m-a))
      calc
        _ = ∑ b : ZMod N, F (a+b) := (Equiv.sum_comp (Equiv.addLeft a) F).symm
        _ = _ := by
          apply sum_congr rfl
          intro b _
          simp only [F,add_sub_cancel_left,add_mul,neg_add_rev,AddChar.map_add_eq_mul]
          ring
    _ = _ := by simp only [sum_mul,mul_sum]; rw [sum_comm]

omit [∀ i, Fact (p i).Prime] in
/-- Normalized inverse Fourier synthesis of the product of the two complete
character sums gives the same finite local density. -/
theorem synthesis (m : ZMod (∏ i, p i)) :
    let e := ZMod.prodEquivPi p cop
    let f := fun a => ∏ i, χ i (e a i)
    let g := fun a => ∏ i, ψ i (e a i)
    ZMod.dft (fun t => ZMod.dft f t * ZMod.dft g t) (-m) =
      ((∏ i, p i : ℕ) : ℂ) * twisted p cop χ ψ m := by
  intro e f g
  rw [← dft_convolution f g,ZMod.dft_dft]
  simp only [neg_neg,smul_eq_mul]
  rfl

end Squarefree
end Conjectures.Goldbach.SquarefreeTwistedGoldbachDensity

/-! Complete twisted binary densities on arbitrary residue rings. For a pair of
primitive characters their convolution has exactly the norm of the Fourier
transform of the inverse product character. This also covers imprimitive
products, where the conductor can be much smaller than either input level. -/

namespace Conjectures.Goldbach.PrimePowerTwistedGoldbachDensity

open Finset DirichletCharacter
open scoped BigOperators Classical

noncomputable def density {q : ℕ} [NeZero q] (χ ψ : DirichletCharacter ℂ q) (m : ZMod q) :
    ℂ := ∑ a : ZMod q, χ a * ψ (m-a)

private theorem transform {q : ℕ} [NeZero q] (χ ψ : DirichletCharacter ℂ q) :
    ZMod.dft (density χ ψ) = fun t => ZMod.dft χ t * ZMod.dft ψ t := by
  funext t
  rw [fourierTransform_eq_gaussSum_mulShift,fourierTransform_eq_gaussSum_mulShift,gaussSum_mul,
    ZMod.dft_apply]
  apply sum_congr rfl
  intro m _
  rw [← sum_mul,smul_eq_mul,AddChar.mulShift_apply]
  simp only [density,mul_neg,mul_comm]

theorem phase_relation {q : ℕ} [NeZero q] {χ ψ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hψ : ψ.IsPrimitive) (m : ZMod q) :
    (q:ℂ)*density χ ψ m =
      (gaussSum χ ZMod.stdAddChar * gaussSum ψ ZMod.stdAddChar) *
      ZMod.dft (fun t => (χ*ψ)⁻¹ t) m := by
  let G := gaussSum χ ZMod.stdAddChar * gaussSum ψ ZMod.stdAddChar
  have ht : ZMod.dft (density χ ψ) = fun t => G*(χ*ψ)⁻¹ (-t) := by
    rw [transform]
    funext t
    rw [hχ.fourierTransform_eq_inv_mul_gaussSum,hψ.fourierTransform_eq_inv_mul_gaussSum]
    simp only [G,mul_inv,MulChar.mul_apply]
    ring
  have hi := congrFun (ZMod.dft_dft (density χ ψ)) (-m)
  rw [ht,ZMod.dft_const_mul G] at hi
  change G * ZMod.dft (fun t => (χ*ψ)⁻¹ (-t)) (-m) = (q:ℂ) • density χ ψ (- -m) at hi
  rw [ZMod.dft_comp_neg (fun t => (χ*ψ)⁻¹ t)] at hi
  simpa only [neg_neg,smul_eq_mul] using hi.symm

theorem primitive_norm {q : ℕ} [NeZero q] {χ ψ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hψ : ψ.IsPrimitive) (m : ZMod q) :
    ‖density χ ψ m‖ = ‖ZMod.dft (fun t => (χ*ψ)⁻¹ t) m‖ := by
  have h := congrArg (fun z : ℂ => ‖z‖) (phase_relation hχ hψ m)
  simp only [norm_mul,Complex.norm_natCast,norm_gaussSum_stdAddChar hχ,
    norm_gaussSum_stdAddChar hψ,Real.mul_self_sqrt (Nat.cast_nonneg q)] at h
  exact mul_left_cancel₀ (by exact_mod_cast NeZero.ne q : (q:ℝ)≠0) h

theorem primitive_product {q : ℕ} [NeZero q] {χ ψ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hψ : ψ.IsPrimitive) (hprod : (χ*ψ).IsPrimitive) (m : ZMod q) :
    ‖density χ ψ m‖ = if IsUnit m then Real.sqrt q else 0 := by
  rw [primitive_norm hχ hψ]
  change ‖ZMod.dft (⇑((χ*ψ)⁻¹)) m‖ = _
  rw [hprod.inv.fourierTransform_eq_inv_mul_gaussSum,norm_mul,norm_gaussSum_stdAddChar hprod.inv,
    inv_inv]
  by_cases hm : IsUnit m
  · have h : ‖(χ*ψ) (-m)‖ = 1 := (χ*ψ).unit_norm_eq_one hm.neg.unit
    rw [ite_eq_left hm,h,one_mul]
  · rw [ite_eq_right hm,MulChar.map_nonunit _ (by simpa using hm : ¬ IsUnit (-m)),norm_zero,zero_mul]

open B13BilateralVaughanReductionProof

private theorem lifted_character {d f : ℕ} [NeZero d] [NeZero f]
    (support : ∀ a : ℕ, a.Coprime d → a.Coprime f) (θ : DirichletCharacter ℂ d) (a : ℕ) :
    changeLevel (dvd_mul_right d f) θ (a : ZMod (d*f)) = θ (a : ZMod d) := by
  rw [DyadicMixedB4MoebiusGauss.changeLevel_nat_indicator]
  by_cases h : a.Coprime d
  · rw [ite_eq_left (Nat.coprime_mul_iff_right.mpr ⟨h,support a h⟩),one_mul]
  · have hz : θ (a : ZMod d)=0 := θ.map_nonunit (fun hu => h ((ZMod.isUnit_iff_coprime a d).mp hu))
    simp only [hz,mul_zero]

/-- Exact Fourier support of a lifted character whenever the larger modulus
has the same prime support. Lifting introduces a divisibility condition on the
frequency and multiplies the surviving lower-level Gauss sum by the fiber size. -/
theorem lifted_gauss {d f : ℕ} [NeZero d] [NeZero f] [NeZero (d*f)]
    (support : ∀ a : ℕ, a.Coprime d → a.Coprime f) (θ : DirichletCharacter ℂ d) (k : ℕ) :
    gaussSum (changeLevel (dvd_mul_right d f) θ) (ZMod.stdAddChar.mulShift (k : ZMod (d*f))) =
      if f ∣ k then (f:ℂ)*gaussSum θ (ZMod.stdAddChar.mulShift ((k/f : ℕ) : ZMod d)) else 0 := by
  rw [DyadicMixedB4GaussLift.gaussSum_as_fraction_sum]
  simp only [lifted_character support,Nat.cast_mul]
  exact DyadicMixedB4GaussLift.lift_gaussSum θ k

private theorem neg_frequency {q : ℕ} [NeZero q] {χ ψ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hψ : ψ.IsPrimitive) (k : ℕ) :
    ‖density χ ψ (-(k : ZMod q))‖ =
      ‖gaussSum (χ*ψ)⁻¹ (ZMod.stdAddChar.mulShift (k : ZMod q))‖ := by
  rw [primitive_norm hχ hψ]
  simp only [fourierTransform_eq_gaussSum_mulShift,neg_neg]

private theorem primitive_gauss {d : ℕ} [NeZero d] {θ : DirichletCharacter ℂ d}
    (hθ : θ.IsPrimitive) (a : ℕ) :
    ‖gaussSum θ (ZMod.stdAddChar.mulShift (a : ZMod d))‖ =
      if a.Coprime d then Real.sqrt d else 0 := by
  rw [gaussSum_mulShift_of_isPrimitive ZMod.stdAddChar hθ,norm_mul,norm_gaussSum_stdAddChar hθ]
  by_cases ha : a.Coprime d
  · rw [ite_eq_left ha]
    have v : ‖θ⁻¹ (a : ZMod d)‖=1 := θ⁻¹.unit_norm_eq_one (ZMod.unitOfCoprime a ha)
    rw [v,one_mul]
  · rw [ite_eq_right ha,MulChar.map_nonunit _ (fun hu => ha ((ZMod.isUnit_iff_coprime a d).mp hu)),
      norm_zero,zero_mul]

/-- Thin-shell support for a primitive pair whose product is induced from a
primitive character of positive level with the same prime factors. -/
theorem conductor_shell {d f : ℕ} [NeZero d] [NeZero f] [NeZero (d*f)]
    (support : ∀ a : ℕ, a.Coprime d → a.Coprime f)
    {χ ψ : DirichletCharacter ℂ (d*f)} (hχ : χ.IsPrimitive) (hψ : ψ.IsPrimitive)
    {θ : DirichletCharacter ℂ d} (hθ : θ.IsPrimitive)
    (lift : (χ*ψ)⁻¹ = changeLevel (dvd_mul_right d f) θ) (k : ℕ) :
    ‖density χ ψ (-(k : ZMod (d*f)))‖ =
      if f ∣ k ∧ (k/f).Coprime d then (f:ℝ)*Real.sqrt d else 0 := by
  rw [neg_frequency hχ hψ,lift,lifted_gauss support]
  by_cases h : f ∣ k
  · rw [ite_eq_left h,norm_mul,Complex.norm_natCast,primitive_gauss hθ]
    by_cases hc : (k/f).Coprime d <;> simp [h,hc]
  · simp [h]

/-- Primitive and properly lifted characters have disjoint Fourier supports if
no new prime divides the larger level. Their convolution vanishes at every
target, even the zero target. -/
theorem mixed_vanishes {d f : ℕ} [NeZero d] [NeZero f] [NeZero (d*f)]
    (hf : 1 < f) (support : ∀ a : ℕ, a.Coprime d → a.Coprime f)
    {χ : DirichletCharacter ℂ (d*f)} (hχ : χ.IsPrimitive) (ψ : DirichletCharacter ℂ d)
    (m : ZMod (d*f)) : density χ (changeLevel (dvd_mul_right d f) ψ) m = 0 := by
  have ht : ZMod.dft (density χ (changeLevel (dvd_mul_right d f) ψ)) = 0 := by
    rw [transform]
    funext t
    rw [hχ.fourierTransform_eq_inv_mul_gaussSum,fourierTransform_eq_gaussSum_mulShift]
    by_cases hu : IsUnit (-t)
    · let a := (-t).val
      have ha : (a : ZMod (d*f)) = -t := ZMod.natCast_zmod_val _
      have hc : a.Coprime (d*f) := (ZMod.isUnit_iff_coprime a (d*f)).mp (ha.symm ▸ hu)
      have hn : ¬ f ∣ a := fun hd => hf.ne' (Nat.eq_one_of_dvd_coprimes hc hd (dvd_mul_left f d))
      rw [← ha,lifted_gauss support,ite_eq_right hn,mul_zero]
      rfl
    · rw [MulChar.map_nonunit _ hu,zero_mul,zero_mul]
      rfl
  have h := ZMod.dft.injective (ht.trans ZMod.dft.map_zero.symm)
  exact congrFun h m

private theorem prime_gauss_one {p : ℕ} [hp : Fact p.Prime] (a : ℕ) :
    gaussSum (1 : DirichletCharacter ℂ p) (ZMod.stdAddChar.mulShift (a : ZMod p)) =
      if p ∣ a then ((p-1 : ℕ):ℂ) else -1 := by
  by_cases h : p ∣ a
  · rw [ite_eq_left h,(ZMod.natCast_eq_zero_iff a p).mpr h,AddChar.mulShift_zero,gaussSum_one_one,
      Nat.card_eq_fintype_card,ZMod.card_units_eq_totient,Nat.totient_prime hp.out]
  · rw [ite_eq_right h]
    exact gaussSum_one_left (ZMod.isPrimitive_stdAddChar p (fun z => h ((ZMod.natCast_eq_zero_iff a p).mp z)))

/-- The remaining (principal product) case gives the exact prime-power
Ramanujan magnitude, including at multiples of the whole modulus. -/
theorem principal_product_power {p : ℕ} [hp : Fact p.Prime] (j : ℕ)
    {χ ψ : DirichletCharacter ℂ (p*p^j)} (hχ : χ.IsPrimitive) (hψ : ψ.IsPrimitive)
    (invpair : χ*ψ=1) (k : ℕ) :
    ‖density χ ψ (-(k : ZMod (p*p^j)))‖ =
      if p^j ∣ k then ((p^j:ℕ):ℝ) * (if p ∣ k/p^j then (p:ℝ)-1 else 1) else 0 := by
  rw [neg_frequency hχ hψ,invpair,inv_one]
  have lift : (1 : DirichletCharacter ℂ (p*p^j)) =
      changeLevel (dvd_mul_right p (p^j)) (1 : DirichletCharacter ℂ p) := (map_one _).symm
  rw [lift,lifted_gauss (fun a (h : a.Coprime p) => h.pow_right j)]
  by_cases h : p^j ∣ k
  · rw [ite_eq_left h,ite_eq_left h,norm_mul,Complex.norm_natCast,prime_gauss_one]
    by_cases hq : p ∣ k/p^j
    · rw [ite_eq_left hq,ite_eq_left hq,Complex.norm_natCast,Nat.cast_sub hp.out.one_le,Nat.cast_one]
    · simp [hq]
  · simp [h]

/-- Reflection of the target changes only the phase, for arbitrary characters. -/
theorem reflected {q : ℕ} [NeZero q] (χ ψ : DirichletCharacter ℂ q) (m : ZMod q) :
    ‖density χ ψ (-m)‖ = ‖density χ ψ m‖ := by
  have h : density χ ψ (-m) = (χ (-1)*ψ (-1))*density χ ψ m := by
    let F (a : ZMod q) := χ a * ψ (-m-a)
    calc
      _ = ∑ a : ZMod q, F (-a) := (Equiv.sum_comp (Equiv.neg _) F).symm
      _ = ∑ a : ZMod q, (χ (-1)*ψ (-1))*(χ a*ψ (m-a)) := by
        apply sum_congr rfl
        intro a _
        change χ (-a) * ψ (-m - -a) = _
        rw [show -m - -a = (-1)*(m-a) by ring,← neg_one_mul a,map_mul,map_mul]
        ring
      _ = _ := (mul_sum ..).symm
  rw [h,norm_mul,norm_mul,χ.norm_neg_one,ψ.norm_neg_one,one_mul,one_mul]

private theorem shell_at_level {d q : ℕ} [NeZero d] [NeZero q] (hd : d ∣ q)
    (support : ∀ a : ℕ, a.Coprime d → a.Coprime (q/d))
    {χ ψ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hψ : ψ.IsPrimitive)
    {θ : DirichletCharacter ℂ d} (hθ : θ.IsPrimitive) (lift : (χ*ψ)⁻¹=changeLevel hd θ) (k : ℕ) :
    ‖density χ ψ (k : ZMod q)‖ =
      if q/d ∣ k ∧ (k/(q/d)).Coprime d then ((q/d:ℕ):ℝ)*Real.sqrt d else 0 := by
  obtain ⟨f,rfl⟩ := hd
  have hf : NeZero f := ⟨fun h => NeZero.ne (d*f) (by simp [h])⟩
  have hr : d*f/d=f := Nat.mul_div_cancel_left f (NeZero.pos d)
  rw [hr,← reflected]
  exact conductor_shell (by simpa only [hr] using support) hχ hψ hθ lift k

private theorem conductor_coprime {p d : ℕ} [hp : Fact p.Prime] (j : ℕ)
    (hd : d ∣ p*p^j) (hne : d≠1) {a : ℕ} (ha : a.Coprime d) : a.Coprime ((p*p^j)/d) := by
  have he : p*p^j=p^(j+1) := by ring
  rw [he] at hd ⊢
  obtain ⟨b,_,hb⟩ := (Nat.dvd_prime_pow hp.out).mp hd
  have hbpos : 0<b := by by_contra! hh; simp [hb, show b=0 by omega] at hne
  have hpa : a.Coprime p := (Nat.coprime_pow_right_iff hbpos _ _).mp (hb ▸ ha)
  exact (hpa.pow_right (j+1)).of_dvd_right (Nat.div_dvd_of_dvd hd)

/-- Complete prime-power norm when both characters are primitive.
The exceptional shell is determined by the conductor of their inverse product. -/
theorem prime_power_table {p : ℕ} [hp : Fact p.Prime] (j : ℕ)
    (χ ψ : DirichletCharacter ℂ (p*p^j)) (hχ : χ.IsPrimitive) (hψ : ψ.IsPrimitive) (k : ℕ) :
    let d := ((χ*ψ)⁻¹).conductor
    let f := (p*p^j)/d
    ‖density χ ψ (k : ZMod (p*p^j))‖ = if χ*ψ=1 then
      (if p^j ∣ k then ((p^j:ℕ):ℝ)*(if p ∣ k/p^j then (p:ℝ)-1 else 1) else 0)
      else if f ∣ k ∧ (k/f).Coprime d then (f:ℝ)*Real.sqrt d else 0 := by
  intro d f
  by_cases h : χ*ψ=1
  · rw [ite_eq_left h,← reflected]
    exact principal_product_power j hχ hψ h k
  rw [ite_eq_right h]
  let θ := (χ*ψ)⁻¹
  let _ : NeZero d := ⟨fun hzero => NeZero.ne (p*p^j) (conductor_eq_zero_iff_level_eq_zero.mp hzero)⟩
  have hd : d ∣ p*p^j := θ.conductor_dvd_level
  have hd1 : d≠1 := by
    intro h1
    have hθ : θ=1 := (eq_one_iff_conductor_eq_one (χ := θ)).mpr h1
    exact h (inv_eq_one.mp hθ)
  exact shell_at_level hd (fun _ ha => conductor_coprime j hd hd1 ha) hχ hψ
    θ.primitiveCharacter_isPrimitive θ.changeLevel_primitiveCharacter.symm k

private theorem lift_residue {d f : ℕ} [NeZero d] [NeZero f] [NeZero (d*f)]
    (support : ∀ a : ℕ, a.Coprime d → a.Coprime f) (θ : DirichletCharacter ℂ d)
    (z : ZMod (d*f)) : changeLevel (dvd_mul_right d f) θ z =
      θ (ZMod.castHom (dvd_mul_right d f) (ZMod d) z) := by
  have h := lifted_character support θ z.val
  simpa only [← map_natCast (ZMod.castHom (dvd_mul_right d f) (ZMod d)), ZMod.natCast_zmod_val] using h

/-- When both characters descend, the density at the higher level is exactly
the fiber size times the lower-level density, with the target reduced as well. -/
theorem both_lifted {d f : ℕ} [NeZero d] [NeZero f] [NeZero (d*f)]
    (support : ∀ a : ℕ, a.Coprime d → a.Coprime f) (χ ψ : DirichletCharacter ℂ d)
    (m : ZMod (d*f)) :
    density (changeLevel (dvd_mul_right d f) χ) (changeLevel (dvd_mul_right d f) ψ) m =
      (f:ℂ)*density χ ψ (ZMod.castHom (dvd_mul_right d f) (ZMod d) m) := by
  let π := ZMod.castHom (dvd_mul_right d f) (ZMod d)
  unfold density
  rw [← DyadicMixedB4DualCharacter.sum_natCast_range_eq_zmod]
  simp only [lift_residue support,map_natCast,map_sub]
  rw [DyadicMixedB4GaussLift.sum_range_blocks]
  simp only [Nat.cast_add,Nat.cast_mul,ZMod.natCast_self,zero_mul,zero_add,sum_const,card_range,
    nsmul_eq_mul]
  exact congrArg (fun z : ℂ => (f:ℂ)*z) (DyadicMixedB4DualCharacter.sum_natCast_range_eq_zmod
    (fun a : ZMod d => χ a * ψ (π m - a)))

end Conjectures.Goldbach.PrimePowerTwistedGoldbachDensity

/-! Factor the full complex singular series of two primitive source characters
through the local components of their actual common-level characters. -/

namespace Conjectures.Goldbach.TwistedGoldbachLocalProduct

open Finset DirichletCharacter TwistedGoldbachConductorRatio
open scoped BigOperators Classical

noncomputable def series {r s : ℕ} (α : DirichletCharacter ℂ r)
    (β : DirichletCharacter ℂ s) (m : ℕ) : ℂ :=
  ∑' d : ℕ, TwistedGoldbachSingularSeries.coefficient α β m d

section Coordinates
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ι → ℕ} [∀ i, NeZero (q i)]
  {L : ℕ} [NeZero L] (e : ZMod L ≃+* ∀ i, ZMod (q i))

/-- Restrict a common-level character to the units at one CRT coordinate.
The same formula extends it by zero on nonunits. -/
noncomputable def component (χ : DirichletCharacter ℂ L) (i : ι) : DirichletCharacter ℂ (q i) where
  toFun x := χ (e.symm (Pi.mulSingle i x))
  map_one' := by simp
  map_mul' x y := by simp only [Pi.mulSingle_mul,map_mul]
  map_nonunit' x hx := χ.map_nonunit (by
    intro hu
    have h := (hu.map e).map (Pi.evalRingHom (fun j => ZMod (q j)) i)
    exact hx (by simpa using h))

omit [Fintype ι] [∀ i, NeZero (q i)] [NeZero L] in
theorem component_one (i : ι) : component e (1 : DirichletCharacter ℂ L) i = 1 := by
  apply MulChar.ext
  intro u
  have hu := (u.isUnit.map (MonoidHom.mulSingle (fun j => ZMod (q j)) i)).map e.symm
  simp only [MonoidHom.mulSingle_apply] at hu
  change (1 : DirichletCharacter ℂ L) (e.symm (Pi.mulSingle i (u:ZMod (q i)))) = _
  rw [MulChar.one_apply hu,MulChar.one_apply u.isUnit]

omit [∀ i, NeZero (q i)] [NeZero L] in
theorem reassemble (χ : DirichletCharacter ℂ L) (x : ZMod L) :
    χ x = ∏ i, component e χ i (e x i) := by
  change χ x = ∏ i, χ (e.symm (Pi.mulSingle i (e x i)))
  rw [← map_prod,← map_prod,Finset.univ_prod_mulSingle,e.symm_apply_apply]

/-- Factor the convolution itself, including every phase. -/
theorem local_factors (A B : DirichletCharacter ℂ L) (m : ℕ) :
    J A B (m:ZMod L) = ∏ i, J (component e A i) (component e B i) (m:ZMod (q i)) := by
  let f (i : ι) (x : ZMod (q i)) := component e A i x * component e B i ((m:ZMod (q i))-x)
  have step (x : ZMod L) : A x * B ((m:ZMod L)-x) = ∏ i, f i (e x i) := by
    rw [reassemble e A x,reassemble e B ((m:ZMod L)-x),← prod_mul_distrib,map_sub,map_natCast]
    rfl
  calc
    _ = ∑ x : ZMod L, ∏ i, f i (e x i) := sum_congr rfl (fun x _ => step x)
    _ = ∑ x : ∀ i, ZMod (q i), ∏ i, f i (x i) :=
      Equiv.sum_comp e.toEquiv (fun x => ∏ i, f i (x i))
    _ = _ := (Fintype.prod_sum f).symm

theorem principal_ne_zero (d m : ℕ) [NeZero d] (he : Even m) :
    J (1 : DirichletCharacter ℂ d) 1 (m:ZMod d) ≠ 0 := by
  obtain ⟨x,hx⟩ := admissible_even d m he
  rw [principal_card]
  exact Nat.cast_ne_zero.mpr (card_pos.mpr ⟨x,mem_filter.mpr ⟨mem_univ _,hx⟩⟩).ne'

/-- Exact Euler product for the correction to the ordinary singular series,
over any CRT decomposition, including prime powers with unequal conductors. -/
theorem full_product {r s : ℕ} [NeZero r] [NeZero s] {α : DirichletCharacter ℂ r}
    {β : DirichletCharacter ℂ s} (hα : α.IsPrimitive) (hβ : β.IsPrimitive)
    (hr : r ∣ L) (hs : s ∣ L) (m : ℕ) (hm : 0 < m) (he : Even m) :
    series α β m = series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m *
      ∏ i, (J (component e (changeLevel hr α) i) (component e (changeLevel hs β) i) (m:ZMod (q i)) /
        J (1 : DirichletCharacter ℂ (q i)) 1 (m:ZMod (q i))) := by
  have h := conductor_identity hα hβ hr hs m hm
  rw [local_factors e (1 : DirichletCharacter ℂ L) 1,local_factors e (changeLevel hr α) (changeLevel hs β)] at h
  simp only [component_one] at h
  rw [prod_div_distrib,← mul_div_assoc,eq_div_iff (prod_ne_zero_iff.mpr (fun i _ => principal_ne_zero (q i) m he))]
  exact h

/-- A noninverse pair at any single CRT factor dividing the target kills the
entire series, even if all the other conductor factors are coprime to it. -/
theorem vanished_factor {r s : ℕ} [NeZero r] [NeZero s] {α : DirichletCharacter ℂ r}
    {β : DirichletCharacter ℂ s} (hα : α.IsPrimitive) (hβ : β.IsPrimitive)
    (hr : r ∣ L) (hs : s ∣ L) (m : ℕ) (hm : 0 < m) (he : Even m) (i : ι)
    (hdiv : q i ∣ m)
    (hne : component e (changeLevel hr α) i * component e (changeLevel hs β) i ≠ 1) :
    series α β m = 0 := by
  rw [full_product e hα hβ hr hs m hm he]
  apply mul_eq_zero_of_right
  apply prod_eq_zero (mem_univ i)
  rw [(ZMod.natCast_eq_zero_iff m (q i)).mpr hdiv,zero_jacobi,ite_eq_right hne,zero_div]

private theorem ratio_le_one {d : ℕ} [NeZero d] (A B : DirichletCharacter ℂ d)
    (m : ℕ) (he : Even m) :
    ‖J A B (m:ZMod d) / J (1 : DirichletCharacter ℂ d) 1 (m:ZMod d)‖ ≤ 1 := by
  rw [norm_div,div_le_one (norm_pos_iff.mpr (principal_ne_zero d m he))]
  exact TwistedGoldbachSingularSeries.chars_le_units A B _

private theorem simple_saving {p : ℕ} [hp : Fact p.Prime] (A B : DirichletCharacter ℂ p)
    (m : ℕ) (hmp : ¬ p ∣ m) (hab : A ≠ 1 ∨ B ≠ 1) :
    ‖J A B (m:ZMod p) / J (1 : DirichletCharacter ℂ p) 1 (m:ZMod p)‖ ≤
      Real.sqrt p / ((p:ℝ)-2) := by
  have hm0 : (m:ZMod p) ≠ 0 := fun h => hmp ((ZMod.natCast_eq_zero_iff m p).mp h)
  have hn : ¬(A=1 ∧ B=1) := by tauto
  have ht := SquarefreeTwistedGoldbachDensity.local_norm A B (m:ZMod p)
  have ht0 := SquarefreeTwistedGoldbachDensity.local_norm (1 : DirichletCharacter ℂ p) 1 (m:ZMod p)
  simp only [hm0,ite_false,hn] at ht
  simp only [hm0,ite_false,and_self,ite_true] at ht0
  change ‖SquarefreeTwistedGoldbachDensity.localSum A B (m:ZMod p) /
    SquarefreeTwistedGoldbachDensity.localSum (1 : DirichletCharacter ℂ p) 1 (m:ZMod p)‖ ≤ _
  rw [norm_div,ht,ht0]
  apply div_le_div_of_nonneg_right _ (sub_nonneg.mpr (by exact_mod_cast hp.out.two_le))
  split_ifs
  · exact (Real.one_le_sqrt.mpr (by exact_mod_cast hp.out.one_le))
  · exact le_rfl

/-- Multiplicative saving from any collection of distinct prime CRT
coordinates away from the target with a nontrivial character component. The
complementary factors may be prime powers or arbitrary composite factors. -/
theorem prime_suppression {r s : ℕ} [NeZero r] [NeZero s] {α : DirichletCharacter ℂ r}
    {β : DirichletCharacter ℂ s} (hα : α.IsPrimitive) (hβ : β.IsPrimitive)
    (hr : r ∣ L) (hs : s ∣ L) (m : ℕ) (hm : 0 < m) (he : Even m)
    (T : Finset ι) (good : ∀ i ∈ T, (q i).Prime ∧ 5 ≤ q i ∧ ¬q i ∣ m ∧
      (component e (changeLevel hr α) i ≠ 1 ∨ component e (changeLevel hs β) i ≠ 1)) :
    ‖series α β m‖ ≤ ‖series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m‖ *
      ∏ i ∈ T, Real.sqrt (q i) / ((q i:ℝ)-2) := by
  let w (i : ι) : ℝ := if i ∈ T then Real.sqrt (q i) / ((q i:ℝ)-2) else 1
  have weights : (∏ i, w i) = ∏ i ∈ T, Real.sqrt (q i) / ((q i:ℝ)-2) := by
    simp [w,prod_ite_mem]
  rw [full_product e hα hβ hr hs m hm he,norm_mul,norm_prod,← weights]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply prod_le_prod₀ (fun _ _ => norm_nonneg _)
  intro i _
  by_cases hi : i ∈ T
  · obtain ⟨hp,_,hd,hn⟩ := good i hi
    let _ : Fact (q i).Prime := ⟨hp⟩
    rw [show w i = _ from ite_eq_left hi]
    exact simple_saving _ _ m hd hn
  · rw [show w i = 1 from ite_eq_right hi]
    exact ratio_le_one _ _ m he

end Coordinates

theorem ordinary_prime_power {p : ℕ} [hp : Fact p.Prime] (j m : ℕ) :
    ‖J (1 : DirichletCharacter ℂ (p*p^j)) 1 (m:ZMod (p*p^j))‖ =
      ((p^j:ℕ):ℝ) * (if p ∣ m then (p:ℝ)-1 else (p:ℝ)-2) := by
  have h := PrimePowerTwistedGoldbachDensity.both_lifted (d := p) (f := p^j)
    (fun a (ha : a.Coprime p) => ha.pow_right j) (1 : DirichletCharacter ℂ p) 1 (m:ZMod (p*p^j))
  simp only [map_one,map_natCast] at h
  have here := SquarefreeTwistedGoldbachDensity.local_norm (1 : DirichletCharacter ℂ p) 1 (m:ZMod p)
  simp only [one_mul,and_self,ite_true,ZMod.natCast_eq_zero_iff] at here
  change ‖PrimePowerTwistedGoldbachDensity.density (1 : DirichletCharacter ℂ p) 1 (m:ZMod p)‖ = _ at here
  change ‖PrimePowerTwistedGoldbachDensity.density (1 : DirichletCharacter ℂ (p*p^j)) 1 (m:ZMod (p*p^j))‖ = _
  rw [h,norm_mul,Complex.norm_natCast,here]

/-- Complete norm table for the infinite twisted series at a pair of
primitive prime-power conductors. Clearing the ordinary local count makes
the formula valid even at odd targets and at the prime two. -/
theorem prime_power_shell {p : ℕ} [hp : Fact p.Prime] (j : ℕ)
    (A B : DirichletCharacter ℂ (p*p^j)) (hA : A.IsPrimitive) (hB : B.IsPrimitive)
    (m : ℕ) (hm : 0 < m) :
    let d := ((A*B)⁻¹).conductor
    let f := (p*p^j)/d
    ‖series A B m‖ * (((p^j:ℕ):ℝ) * (if p ∣ m then (p:ℝ)-1 else (p:ℝ)-2)) =
      ‖series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m‖ *
        (if A*B=1 then
          (if p^j ∣ m then ((p^j:ℕ):ℝ) * (if p ∣ m/p^j then (p:ℝ)-1 else 1) else 0)
         else if f ∣ m ∧ (m/f).Coprime d then (f:ℝ)*Real.sqrt d else 0) := by
  have h := congrArg (fun z : ℂ => ‖z‖)
    (conductor_identity hA hB (dvd_refl _) (dvd_refl _) m hm)
  simp only [norm_mul,changeLevel_self,ordinary_prime_power] at h
  have table := PrimePowerTwistedGoldbachDensity.prime_power_table j A B hA hB m
  change ‖J A B (m:ZMod (p*p^j))‖ = _ at table
  rw [table] at h
  exact h

/-- At a unit target and a repeated prime, only a primitive product can
survive. Its magnitude has an extra square-root saving with each level. -/
theorem unit_prime_power {p : ℕ} [hp : Fact p.Prime] (j : ℕ) (hj : 0 < j)
    (A B : DirichletCharacter ℂ (p*p^j)) (hA : A.IsPrimitive) (hB : B.IsPrimitive)
    (m : ℕ) (hm : 0 < m) (hmp : ¬p ∣ m) :
    ‖series A B m‖ * (((p^j:ℕ):ℝ) * ((p:ℝ)-2)) =
      ‖series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m‖ *
        (if ((A*B)⁻¹).conductor = p*p^j then Real.sqrt (p*p^j:ℕ) else 0) := by
  let Q := p*p^j
  let d := ((A*B)⁻¹).conductor
  have hd : d ∣ Q := ((A*B)⁻¹).conductor_dvd_level
  have hpQ : p ∣ Q := dvd_mul_right p (p^j)
  have hQ : 0 < Q := Nat.mul_pos hp.out.pos (pow_pos hp.out.pos _)
  have mp : m.Coprime p := (hp.out.coprime_iff_not_dvd.mpr hmp).symm
  have mQ := mp.mul_right (mp.pow_right j)
  have nf : Q/d ∣ m → d=Q := by
    intro h
    have one := Nat.eq_one_of_dvd_coprimes mQ h (Nat.div_dvd_of_dvd hd)
    have cancel := Nat.div_mul_cancel hd
    simpa only [one,one_mul] using cancel
  have table := prime_power_shell j A B hA hB m hm
  dsimp only at table
  rw [ite_eq_right hmp] at table
  rw [table]
  congr 1
  change (if A*B=1 then _ else if Q/d ∣ m ∧ (m/(Q/d)).Coprime d then _ else 0) =
    (if d=Q then _ else 0)
  by_cases invpair : A*B=1
  · have d1 : d=1 := (eq_one_iff_conductor_eq_one (χ := (A*B)⁻¹)).mp (by rw [invpair,inv_one])
    have neq : d ≠ Q := by
      intro h
      have h1 : p ∣ 1 := by simpa only [← h,d1] using hpQ
      exact hp.out.not_dvd_one h1
    have nopow : ¬p^j ∣ m := fun h => hmp ((dvd_pow_self p hj.ne').trans h)
    simp only [invpair,ite_true,neq,ite_false,nopow]
  rw [ite_eq_right invpair]
  by_cases same : d=Q
  · have red : Q/d=1 := by rw [same,Nat.div_self hQ]
    have hc : m.Coprime d := by rw [same]; exact mQ
    have hs : Q/d ∣ m ∧ (m/(Q/d)).Coprime d := by simpa only [red,one_dvd,Nat.div_one,true_and] using hc
    rw [ite_eq_left hs,ite_eq_left same,red,Nat.cast_one,one_mul]
    exact congrArg (fun a : ℕ => Real.sqrt a) same
  · have cannot : ¬(Q/d ∣ m ∧ (m/(Q/d)).Coprime d) := fun h => same (nf h.1)
    simp only [cannot,ite_false,same]

end Conjectures.Goldbach.TwistedGoldbachLocalProduct

/-! The primitive/principal pair contributing to the exceptional-zero
formula has an elementary exact numerator, including its phase. -/

namespace Conjectures.Goldbach.TwistedGoldbachMixedPrincipal

open Finset DirichletCharacter TwistedGoldbachConductorRatio TwistedGoldbachLocalProduct
open scoped BigOperators Classical
open B13BilateralVaughanReductionProof

private theorem principal_gauss (r : ℕ) [NeZero r] :
    gaussSum (1 : DirichletCharacter ℂ r) ZMod.stdAddChar = (ArithmeticFunction.moebius r : ℂ) := by
  by_cases one : r=1
  · subst r
    have trivial : (ZMod.stdAddChar : AddChar (ZMod 1) ℂ) = 1 := by
      ext x
      rw [show x=0 from Subsingleton.elim _ _]
      simp
    rw [trivial,gaussSum_one_one,Nat.card_eq_fintype_card,ZMod.card_units_eq_totient]
    norm_num
  have lower : 1 < r := by have := NeZero.pos r; omega
  have h := DyadicMixedB4Ramanujan.ramanujan_moebius lower 1
  rw [DyadicMixedB4Ramanujan.ramanujan_natural_gauss lower] at h
  simp only [Nat.cast_one,AddChar.mulShift_one] at h
  rw [h,sum_eq_single_of_mem r (Nat.mem_divisors_self _ (NeZero.ne r))]
  · simp [DyadicMixedB4MoebiusGauss.moebiusComplex,Nat.div_self (NeZero.pos r)]
  · intro d hd hne
    have h : ¬r/d ∣ 1 := by
      intro hone
      have he := Nat.eq_one_of_dvd_one hone
      apply hne
      simpa only [he,one_mul] using Nat.div_mul_cancel (Nat.mem_divisors.mp hd).1
    simp [h]

/-- The binary convolution of a primitive character with the principal
character equals the original character multiplied by the Möbius function of
its conductor. This identity holds on every residue, including nonunits. -/
theorem mixed_jacobi {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r) (hχ : χ.IsPrimitive)
    (m : ZMod r) : J χ 1 m = (ArithmeticFunction.moebius r:ℂ)*χ m := by
  have conv : ZMod.dft (J χ 1) = fun t => ZMod.dft χ t * ZMod.dft (1 : DirichletCharacter ℂ r) t := by
    funext t
    rw [fourierTransform_eq_gaussSum_mulShift,fourierTransform_eq_gaussSum_mulShift,gaussSum_mul,
      ZMod.dft_apply]
    apply sum_congr rfl
    intro y _
    rw [← sum_mul,smul_eq_mul,AddChar.mulShift_apply]
    simp only [J,mul_neg,mul_comm]
  have eqn : J χ 1 = fun y => (ArithmeticFunction.moebius r:ℂ)*χ y := by
    apply ZMod.dft.injective
    rw [conv,ZMod.dft_const_mul]
    funext t
    by_cases hu : IsUnit (-t)
    · have shift := gaussSum_mulShift_eq (1 : DirichletCharacter ℂ r) ZMod.stdAddChar hu.unit
      simp only [hu.unit_spec,inv_one,MulChar.one_apply hu,one_mul,principal_gauss] at shift
      rw [fourierTransform_eq_gaussSum_mulShift (1 : DirichletCharacter ℂ r),shift,mul_comm]
    · rw [hχ.fourierTransform_eq_inv_mul_gaussSum,(χ⁻¹).map_nonunit hu,zero_mul,zero_mul,mul_zero]
  exact congrFun eqn m

/-- The full mixed series, with no unsummed denominator terms. -/
theorem mixed_exact {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r) (hχ : χ.IsPrimitive)
    (m : ℕ) (hm : 0 < m) :
    series χ (1 : DirichletCharacter ℂ 1) m * J (1 : DirichletCharacter ℂ r) 1 (m:ZMod r) =
      series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m *
        ((ArithmeticFunction.moebius r:ℂ)*χ (m:ZMod r)) := by
  have h := conductor_identity (β := (1 : DirichletCharacter ℂ 1)) hχ isPrimitive_one_level_one
    (dvd_refl r) (one_dvd r) m hm
  simpa only [series,changeLevel_self,map_one,mixed_jacobi χ hχ] using h

noncomputable def localWeight (m p : ℕ) : ℝ :=
  if p ∣ m then (p:ℝ)/((p:ℝ)-1) else (p:ℝ)*((p:ℝ)-2)/((p:ℝ)-1)^2

noncomputable def ordinaryWeight (q m : ℕ) [NeZero q] : ℝ :=
  (q:ℝ) * ‖J (1 : DirichletCharacter ℂ q) 1 (m:ZMod q)‖ / (q.totient:ℝ)^2

private theorem weight_prime_power {p : ℕ} [hp : Fact p.Prime] (a m : ℕ) (ha : 0 < a) :
    ordinaryWeight (p^a) m = localWeight m p := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero ha.ne'
  have fpos : (0:ℝ) < ((p^j:ℕ):ℝ) := by exact_mod_cast pow_pos hp.out.pos j
  have ppos : (0:ℝ) < (p:ℝ)-1 := sub_pos.mpr (by exact_mod_cast hp.out.one_lt)
  have form (q : ℕ) [NeZero q] (hq : q=p*p^j) : ordinaryWeight q m = localWeight m p := by
    subst q
    have tot : (p*p^j).totient = p^j*(p-1) := by rw [← pow_succ',Nat.totient_prime_pow_succ hp.out]
    unfold ordinaryWeight
    rw [tot,ordinary_prime_power,Nat.cast_mul,Nat.cast_mul,Nat.cast_sub hp.out.one_le,Nat.cast_one]
    unfold localWeight
    split_ifs <;> field_simp [fpos.ne',ppos.ne']
  exact form _ (pow_succ' p j)

/-- The finite ordinary count has exactly the usual Euler factor at every
prime dividing the modulus, independent of its exponent. -/
theorem ordinary_product (q m : ℕ) [NeZero q] :
    ordinaryWeight q m = ∏ p ∈ q.primeFactors, localWeight m p := by
  let F (p : q.primeFactors) := (p:ℕ)^(q.factorization p)
  have pp (p : q.primeFactors) : (p:ℕ).Prime := Nat.prime_of_mem_primeFactors p.property
  let _ : ∀ p : q.primeFactors, Fact (p:ℕ).Prime := fun p => ⟨pp p⟩
  let _ : ∀ p : q.primeFactors, NeZero (F p) := fun p => ⟨pow_ne_zero _ (pp p).ne_zero⟩
  have expo (p : q.primeFactors) : 0 < q.factorization (p:ℕ) :=
    (pp p).factorization_pos_of_dvd (NeZero.ne q) (Nat.dvd_of_mem_primeFactors p.property)
  let e : ZMod q ≃+* ∀ p : q.primeFactors, ZMod (F p) := ZMod.equivPi q (NeZero.ne q)
  have hJ := local_factors e (1 : DirichletCharacter ℂ q) 1 m
  simp only [component_one] at hJ
  have hr : (q:ℝ) = ∏ p : q.primeFactors, (F p:ℝ) := by
    exact_mod_cast Nat.prod_primeFactors_coe_pow_factorization (NeZero.ne q)
  have hφ : q.totient = ∏ p : q.primeFactors, (F p).totient := by
    rw [Nat.totient_eq_prod_factorization (NeZero.ne q),Nat.prod_factorization_eq_prod_primeFactors]
    simp only [F,Nat.totient_prime_pow (pp _) (expo _)]
    exact (Finset.prod_coe_sort q.primeFactors (fun p : ℕ => p^(q.factorization p-1)*(p-1))).symm
  have hφr : (q.totient:ℝ) = ∏ p : q.primeFactors, ((F p).totient:ℝ) := by exact_mod_cast hφ
  unfold ordinaryWeight
  rw [hr,hφr,hJ,norm_prod,← prod_mul_distrib,← prod_pow,← prod_div_distrib]
  rw [← Finset.prod_coe_sort q.primeFactors (localWeight m)]
  apply prod_congr rfl
  intro p _
  exact weight_prime_power _ m (expo p)

private theorem local_minimum {p : ℕ} (hp : 2 ≤ p) (m : ℕ) :
    1-1/((p:ℝ)-1)^2 ≤ localWeight m p := by
  have hpos : (0:ℝ) < (p:ℝ)-1 := sub_pos.mpr (by exact_mod_cast (by omega : 1 < p))
  unfold localWeight
  split_ifs
  · apply (sub_le_self (1:ℝ) (by positivity)).trans
    exact (le_div_iff₀ hpos).mpr (by linarith)
  · apply le_of_eq
    field_simp [hpos.ne']
    ring

private theorem truncated_lower (S : Finset ℕ) (hp : ∀ p ∈ S, p.Prime) (m : ℕ) (he : Even m) :
    ∀ P : ℕ, 2 ≤ P →
      (if 2 ∈ S then (2:ℝ) else 1) * P / (2*((P:ℝ)-1)) ≤
        ∏ p ∈ range (P+1), (if p ∈ S then localWeight m p else 1) := by
  let a : ℝ := if 2 ∈ S then 2 else 1
  have ha : 0 < a := by dsimp [a]; split <;> norm_num
  intro P hP
  induction P,hP using Nat.le_induction with
  | base =>
    have h0 : 0 ∉ S := fun h => Nat.not_prime_zero (hp 0 h)
    have h1 : 1 ∉ S := fun h => Nat.not_prime_one (hp 1 h)
    have h2 : 2 ∣ m := even_iff_two_dvd.mp he
    rw [show range (2+1) = {0,1,2} by decide]
    by_cases ht : 2 ∈ S <;> norm_num [h0,h1,ht,localWeight,h2]
  | succ k hk ih =>
    have hk' : (2:ℝ) ≤ k := by exact_mod_cast hk
    let b : ℝ := 1-1/(k:ℝ)^2
    have hb : 0 ≤ b := by
      apply sub_nonneg.mpr
      apply (div_le_one (by positivity : 0 < (k:ℝ)^2)).mpr
      nlinarith [sq_nonneg ((k:ℝ)-2)]
    have hf : b ≤ (if k+1 ∈ S then localWeight m (k+1) else 1) := by
      split_ifs
      · simpa [b] using local_minimum (p := k+1) (by omega) m
      · exact sub_le_self _ (by positivity)
    change a*(k:ℝ)/(2*((k:ℝ)-1)) ≤ _ at ih
    have left : 0 ≤ a*(k:ℝ)/(2*((k:ℝ)-1)) :=
      div_nonneg (mul_nonneg ha.le (Nat.cast_nonneg k)) (by linarith)
    rw [prod_range_succ]
    refine le_trans ?_ (mul_le_mul ih hf hb (left.trans ih))
    change a*((k+1:ℕ):ℝ)/(2*(((k+1:ℕ):ℝ)-1)) ≤ (a*(k:ℝ)/(2*((k:ℝ)-1))) * b
    apply le_of_eq
    push_cast
    dsimp [b]
    field_simp [show (k:ℝ)-1 ≠ 0 by linarith,show (k:ℝ) ≠ 0 by linarith]
    ring

theorem uniform_weight (q m : ℕ) [NeZero q] (he : Even m) :
    (if 2 ∣ q then (1:ℝ) else 1/2) ≤ ordinaryWeight q m := by
  let P := max 2 q
  have hP : 2 ≤ P := le_max_left ..
  have hr : (2:ℝ) ≤ P := by exact_mod_cast hP
  have cover : q.primeFactors ⊆ range (P+1) := fun p hp =>
    mem_range.mpr (Nat.lt_succ_of_le ((Nat.le_of_mem_primeFactors hp).trans (le_max_right ..)))
  have h := truncated_lower q.primeFactors (fun _ hp => Nat.prime_of_mem_primeFactors hp) m he P hP
  simp only [prod_ite_mem,inter_eq_right.mpr cover] at h
  rw [ordinary_product]
  apply le_trans _ h
  have two : 2 ∈ q.primeFactors ↔ 2 ∣ q :=
    ⟨Nat.dvd_of_mem_primeFactors,fun h => Nat.mem_primeFactors.mpr ⟨Nat.prime_two,h,NeZero.ne q⟩⟩
  by_cases ht : 2 ∣ q <;> simp only [two,ht,ite_true,ite_false,one_mul]
  all_goals apply (le_div_iff₀ (by linarith : (0:ℝ) < 2*((P:ℝ)-1))).mpr; linarith

/-- The ordinary infinite series at a positive even target has real part
at least one. -/
theorem ordinary_at_least_one (m : ℕ) (hm : 0 < m) (he : Even m) :
    1 ≤ (series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m).re := by
  let O : DirichletCharacter ℂ 1 := 1
  have lim := (TwistedGoldbachSingularSeries.partial_limit O O m hm 2 (by decide)).norm
  have lower : 1 ≤ ‖series O O m‖ := by
    apply ge_of_tendsto' lim
    intro n
    let q := 2*n.factorial
    let _ : NeZero q := ⟨mul_ne_zero (by decide) n.factorial_ne_zero⟩
    have hf := uniform_weight q m he
    rw [ite_eq_left (dvd_mul_right 2 n.factorial)] at hf
    have amb := TwistedGoldbachSingularSeries.ambient_sum (α := O) (β := O)
      isPrimitive_one_level_one isPrimitive_one_level_one (one_dvd q) (one_dvd q) m
    simp only [O,map_one] at amb
    change 1 ≤ ‖∑ d ∈ q.divisors, TwistedGoldbachSingularSeries.coefficient O O m d‖
    rw [← amb]
    simpa only [TwistedGoldbachSingularSeries.normalized,norm_div,norm_mul,norm_pow,
      Complex.norm_natCast,ordinaryWeight,J] using hf
  exact lower.trans (TwistedGoldbachSingularSeries.infinite_domination (α := O) (β := O)
    isPrimitive_one_level_one isPrimitive_one_level_one m hm)

/-- A mixed contribution vanishes at a nonsquarefree conductor or a nonunit
target. -/
theorem mixed_zero {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r) (hχ : χ.IsPrimitive)
    (m : ℕ) (hm : 0 < m) (he : Even m) (bad : ¬Squarefree r ∨ ¬m.Coprime r) :
    series χ (1 : DirichletCharacter ℂ 1) m = 0 := by
  have h := mixed_exact χ hχ m hm
  apply (mul_eq_zero.mp (show series χ (1 : DirichletCharacter ℂ 1) m *
      J (1 : DirichletCharacter ℂ r) 1 (m:ZMod r) = 0 from ?_)).resolve_right (principal_ne_zero r m he)
  rw [h]
  rcases bad with hs | hc
  · simp [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hs]
  · simp [χ.map_nonunit (fun hu => hc ((ZMod.isUnit_iff_coprime m r).mp hu))]

/-- Explicit constant in the uniform mixed-pair bound used in (11.10) of
Pintz I and (8.1) of Bhowmik--Grimmelt. -/
theorem mixed_bound {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r) (hχ : χ.IsPrimitive)
    (m : ℕ) (hm : 0 < m) (he : Even m) :
    ‖series χ (1 : DirichletCharacter ℂ 1) m‖ ≤
      (2*(r:ℝ)/(r.totient:ℝ)^2) * ‖series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m‖ := by
  have h := congrArg (fun z : ℂ => ‖z‖) (mixed_exact χ hχ m hm)
  simp only [norm_mul] at h
  have small : ‖(ArithmeticFunction.moebius r:ℂ)‖ * ‖χ (m:ZMod r)‖ ≤ 1 :=
    (mul_le_mul (DyadicMixedB4MoebiusGauss.norm_moebiusComplex_le_one r)
      (χ.norm_le_one _) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  have hφ : (0:ℝ) < (r.totient:ℝ)^2 := sq_pos_of_pos (by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos r))
  have base : 1/2 ≤ ordinaryWeight r m := by
    apply le_trans _ (uniform_weight r m he)
    split <;> norm_num
  have total := (le_div_iff₀ hφ).mp base
  let O : ℝ := ‖series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m‖
  let T : ℝ := ‖series χ (1 : DirichletCharacter ℂ 1) m‖
  let D : ℝ := ‖J (1 : DirichletCharacter ℂ r) 1 (m:ZMod r)‖
  have a : T*D ≤ O := h.le.trans ((mul_le_mul_of_nonneg_left small (norm_nonneg _)).trans_eq (mul_one _))
  have b : (r.totient:ℝ)^2 ≤ 2*(r:ℝ)*D := by change 1/2*(r.totient:ℝ)^2 ≤ (r:ℝ)*D at total; linarith
  change T ≤ (2*(r:ℝ)/(r.totient:ℝ)^2)*O
  rw [div_mul_eq_mul_div,le_div_iff₀ hφ]
  calc
    T*(r.totient:ℝ)^2 ≤ T*(2*(r:ℝ)*D) := mul_le_mul_of_nonneg_left b (norm_nonneg _)
    _ = 2*(r:ℝ)*(T*D) := by ring
    _ ≤ 2*(r:ℝ)*O := mul_le_mul_of_nonneg_left a (by positivity)

end Conjectures.Goldbach.TwistedGoldbachMixedPrincipal

/-! Möbius inversion of the finite conductor quotient. At denominators
divisible by the least common multiple of the conductors, the remaining
Euler factors are real and multiplicative away from that common level. -/

namespace Conjectures.Goldbach.TwistedGoldbachCoefficientProduct

open Finset DirichletCharacter TwistedGoldbachConductorRatio
open TwistedGoldbachSingularSeries TwistedGoldbachLocalProduct TwistedGoldbachMixedPrincipal
open scoped BigOperators Classical

noncomputable def atom (L t : ℕ) (g : ℕ → ℝ) : ℝ :=
  if Squarefree t ∧ t.Coprime L then ∏ p ∈ t.primeFactors, g p else 0

theorem sum_atoms (L n : ℕ) (hL : L ≠ 0) (hn : n ≠ 0) (g : ℕ → ℝ) :
    ∑ t ∈ n.divisors, atom L t g = ∏ p ∈ n.primeFactors \ L.primeFactors, (1+g p) := by
  rw [prod_one_add]
  unfold atom
  rw [← sum_filter]
  apply sum_bij (fun d _ => d.primeFactors)
  · intro d hd
    obtain ⟨hm,_,hc⟩ := mem_filter.mp hd
    apply mem_powerset.mpr
    intro p hp
    exact mem_sdiff.mpr ⟨Nat.primeFactors_mono (Nat.dvd_of_mem_divisors hm) hn hp,
      fun h => disjoint_left.mp hc.disjoint_primeFactors hp h⟩
  · intro a ha b hb hab
    rw [← Nat.prod_primeFactors_of_squarefree (mem_filter.mp ha).2.1,
      ← Nat.prod_primeFactors_of_squarefree (mem_filter.mp hb).2.1,hab]
  · intro U hU
    have sub := mem_powerset.mp hU
    have prime (p : ℕ) (hp : p ∈ U) := Nat.prime_of_mem_primeFactors (mem_sdiff.mp (sub hp)).1
    let d := ∏ p ∈ U, p
    have factors : d.primeFactors=U := Nat.primeFactors_prod prime
    have hd : d ≠ 0 := (prod_pos (fun p hp => (prime p hp).pos)).ne'
    have square := Nat.squarefree_prod_primeFactors d
    rw [factors] at square
    have divides : d ∣ n := by
      have h := (Nat.prod_primeFactors_dvd_iff (n := d) hn).mpr
        (by rw [factors]; exact fun p hp => (mem_sdiff.mp (sub hp)).1)
      rwa [factors] at h
    have cop : d.Coprime L := (Nat.disjoint_primeFactors hd hL).mp (by
      rw [factors,disjoint_left]
      exact fun p hp => (mem_sdiff.mp (sub hp)).2)
    exact ⟨d,mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨divides,hn⟩,square,cop⟩,factors⟩
  · intro _ _
    rfl

private theorem eq_of_divisor_sums (f g : ℕ → ℂ)
    (h : ∀ n : ℕ, n ≠ 0 → ∑ d ∈ n.divisors, f d = ∑ d ∈ n.divisors, g d) :
    ∀ n : ℕ, n ≠ 0 → f n=g n := by
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro hn
    have ne := Nat.mem_divisors_self n hn
    have rest : ∑ d ∈ n.divisors.erase n, f d = ∑ d ∈ n.divisors.erase n, g d := by
      apply sum_congr rfl
      intro d hd
      have ⟨hneq,hmem⟩ := mem_erase.mp hd
      exact ih d (lt_of_le_of_ne (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Nat.dvd_of_mem_divisors hmem)) hneq)
        (Nat.pos_of_mem_divisors hmem).ne'
    have H := h n hn
    rw [← sum_erase_add _ _ ne,← sum_erase_add _ _ ne,rest] at H
    exact add_left_cancel H

private theorem multiples {M : Type*} [AddCommMonoid M] {L n : ℕ} (hL : L ≠ 0) (hn : n ≠ 0) (f : ℕ → M)
    (outside : ∀ d : ℕ, ¬L ∣ d → f d=0) :
    ∑ d ∈ n.divisors, f (L*d) = ∑ d ∈ (L*n).divisors, f d := by
  let S := (L*n).divisors.filter (fun d => L ∣ d)
  calc
    _ = ∑ d ∈ S, f d := by
      apply sum_bij (fun d _ => L*d)
      · intro d hd
        exact mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨Nat.mul_dvd_mul_left L (Nat.dvd_of_mem_divisors hd),
          mul_ne_zero hL hn⟩,dvd_mul_right L d⟩
      · intro a _ b _ h
        exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hL) h
      · intro d hd
        obtain ⟨hm,k,rfl⟩ := mem_filter.mp hd
        exact ⟨k,Nat.mem_divisors.mpr ⟨Nat.dvd_of_mul_dvd_mul_left (Nat.pos_of_ne_zero hL)
          (Nat.dvd_of_mem_divisors hm),hn⟩,rfl⟩
      · intro _ _
        rfl
    _ = _ := sum_subset (filter_subset _ _) (fun d hd hnot =>
      outside d (fun h => hnot (mem_filter.mpr ⟨hd,h⟩)))

private theorem complex_ordinary (q m : ℕ) [NeZero q] :
    normalized (1 : DirichletCharacter ℂ q) 1 m = (ordinaryWeight q m:ℂ) := by
  change (q:ℂ)*J (1 : DirichletCharacter ℂ q) 1 (m:ZMod q)/(q.totient:ℂ)^2 = _
  simp only [ordinaryWeight,principal_card,Complex.norm_natCast,Complex.ofReal_div,Complex.ofReal_mul,
    Complex.ofReal_natCast,Complex.ofReal_pow]

private theorem partial_sums {r s q : ℕ} [NeZero r] [NeZero s] [NeZero q]
    {α : DirichletCharacter ℂ r} {β : DirichletCharacter ℂ s} (hα : α.IsPrimitive) (hβ : β.IsPrimitive)
    (hr : r ∣ q) (hs : s ∣ q) (m : ℕ) (hm : 0 < m) (he : Even m) :
    ∑ d ∈ q.divisors, coefficient α β m d =
      (series α β m / series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m) *
        (ordinaryWeight q m:ℂ) := by
  let O := series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m
  have nz : O ≠ 0 := by
    intro hz
    have h := ordinary_at_least_one m hm he
    change 1 ≤ O.re at h
    rw [hz,Complex.zero_re] at h
    norm_num at h
  have id := conductor_identity hα hβ hr hs m hm
  change series α β m * J (1 : DirichletCharacter ℂ q) 1 (m:ZMod q) = O * _ at id
  rw [← ambient_sum hα hβ hr hs m,← complex_ordinary]
  change (q:ℂ)*J _ _ (m:ZMod q)/(q.totient:ℂ)^2 =
    (series α β m/O)*((q:ℂ)*J (1 : DirichletCharacter ℂ q) 1 (m:ZMod q)/(q.totient:ℂ)^2)
  have eqn : J (changeLevel hr α) (changeLevel hs β) (m:ZMod q) =
      (series α β m/O)*J (1 : DirichletCharacter ℂ q) 1 (m:ZMod q) := by
    rw [div_mul_eq_mul_div,eq_div_iff nz,mul_comm]
    exact id.symm
  rw [eqn]
  ring

theorem off_level {r s : ℕ} (α : DirichletCharacter ℂ r) (β : DirichletCharacter ℂ s)
    (m d : ℕ) (h : ¬Nat.lcm r s ∣ d) : coefficient α β m d = 0 := by
  unfold coefficient
  split_ifs with hd hdiv
  · exact False.elim (h (Nat.lcm_dvd hdiv.1 hdiv.2))
  all_goals rfl

private theorem new_weights {L t : ℕ} [NeZero L] [NeZero t] (m : ℕ) :
    ordinaryWeight (L*t) m = ordinaryWeight L m *
      ∏ p ∈ t.primeFactors \ L.primeFactors, localWeight m p := by
  rw [ordinary_product,ordinary_product,Nat.primeFactors_mul (NeZero.ne L) (NeZero.ne t)]
  have seteq : L.primeFactors ∪ t.primeFactors = L.primeFactors ∪ (t.primeFactors \ L.primeFactors) := by
    ext p
    simp only [mem_union,mem_sdiff]
    tauto
  rw [seteq,prod_union]
  exact disjoint_left.mpr (fun p hp h => (mem_sdiff.mp h).2 hp)

section Conductors
variable {r s : ℕ} [NeZero r] [NeZero s] {α : DirichletCharacter ℂ r} {β : DirichletCharacter ℂ s}
  (hα : α.IsPrimitive) (hβ : β.IsPrimitive) (m : ℕ) (hm : 0 < m) (he : Even m)
include hα hβ hm he

/-- At multiples of the least common conductor level, partial sums acquire
exactly the ordinary Euler factors for the newly introduced primes. -/
theorem partial_extension (t : ℕ) (ht : t ≠ 0) :
    let L := Nat.lcm r s
    ∑ d ∈ (L*t).divisors, coefficient α β m d =
      coefficient α β m L * ((∏ p ∈ t.primeFactors \ L.primeFactors, localWeight m p : ℝ):ℂ) := by
  intro L
  let _ : NeZero t := ⟨ht⟩
  let _ : NeZero L := ⟨(Nat.lcm_pos (NeZero.pos r) (NeZero.pos s)).ne'⟩
  have hr : r ∣ L := Nat.dvd_lcm_left ..
  have hs : s ∣ L := Nat.dvd_lcm_right ..
  have base := partial_sums hα hβ hr hs m hm he
  rw [sum_eq_single_of_mem L (Nat.mem_divisors_self L (NeZero.ne L))] at base
  · have h := partial_sums hα hβ (hr.trans (dvd_mul_right L t)) (hs.trans (dvd_mul_right L t)) m hm he
    rw [h,new_weights,Complex.ofReal_mul,← mul_assoc,← base]
  · intro d hd ne
    apply off_level
    intro h
    exact ne (Nat.dvd_antisymm (Nat.dvd_of_mem_divisors hd) h)

/-- Formula for every single coefficient, including every ramified or
nonsquarefree zero. No primitivity condition is imposed on the product of
the two source characters. -/
theorem coefficient_extension (t : ℕ) (ht : t ≠ 0) :
    let L := Nat.lcm r s
    coefficient α β m (L*t) =
      coefficient α β m L * (atom L t (fun p => localWeight m p-1):ℂ) := by
  intro L
  let c := coefficient α β m
  let g (p : ℕ) := localWeight m p-1
  have hL : L ≠ 0 := (Nat.lcm_pos (NeZero.pos r) (NeZero.pos s)).ne'
  apply eq_of_divisor_sums (fun d => c (L*d)) (fun d => c L * (atom L d g:ℂ)) _ t ht
  intro n hn
  rw [multiples hL hn c (fun d h => off_level α β m d h)]
  have H := partial_extension hα hβ m hm he n hn
  change ∑ d ∈ (L*n).divisors, c d = _ at H
  rw [H,← mul_sum,← Complex.ofReal_sum,sum_atoms _ _ hL hn]
  have eqn : (fun p => 1+g p) = localWeight m := funext (fun p => by dsimp [g]; ring)
  simp only [eqn]
  rfl

theorem absolute_partial (t : ℕ) (ht : t ≠ 0) :
    let L := Nat.lcm r s
    ∑ d ∈ (L*t).divisors, ‖coefficient α β m d‖ =
      ‖coefficient α β m L‖ * ∏ p ∈ t.primeFactors \ L.primeFactors, (1+|localWeight m p-1|) := by
  intro L
  let c := coefficient α β m
  let g (p : ℕ) := localWeight m p-1
  have hL : L ≠ 0 := (Nat.lcm_pos (NeZero.pos r) (NeZero.pos s)).ne'
  have absatom (d : ℕ) : |atom L d g| = atom L d (fun p => |g p|) := by
    unfold atom
    split_ifs <;> simp [Finset.abs_prod]
  rw [← multiples hL ht (fun d => ‖c d‖) (fun d h => by change ‖coefficient α β m d‖ = 0; rw [off_level α β m d h,norm_zero])]
  change ∑ d ∈ t.divisors, ‖c (L*d)‖ = ‖c L‖*_
  rw [← sum_atoms L t hL ht (fun p => |g p|),mul_sum]
  apply sum_congr rfl
  intro d hd
  have H := coefficient_extension hα hβ m hm he d (Nat.pos_of_mem_divisors hd).ne'
  change c (L*d) = c L * (atom L d g:ℂ) at H
  rw [H,norm_mul,Complex.norm_real,Real.norm_eq_abs,absatom]

end Conductors

open Filter Topology

/-- The ratio of the absolute Euler factor to the signed factor. A prime
dividing the conductor level or the even target contributes one. -/
noncomputable def correction (K p : ℕ) : ℝ :=
  if p.Prime ∧ 2 < p ∧ ¬p ∣ K then 1+2/((p:ℝ)*((p:ℝ)-2)) else 1

theorem correction_one_le (K p : ℕ) : 1 ≤ correction K p := by
  unfold correction
  split_ifs with h
  · have hp : (2:ℝ)<p := by exact_mod_cast h.2.1
    exact le_add_of_nonneg_right (by positivity)
  · rfl

private theorem factor_ratio {L p m : ℕ} (hp : p.Prime) (he : Even m) (hL : ¬p ∣ L) :
    1+|localWeight m p-1| = |localWeight m p| * correction (L*m) p := by
  have hp1 : (1:ℝ)<p := by exact_mod_cast hp.one_lt
  have h1 : 0 < (p:ℝ)-1 := by linarith
  by_cases hm : p ∣ m
  · have hm' : p ∣ L*m := hm.trans (dvd_mul_left m L)
    simp only [localWeight,ite_eq_left hm,correction,hm',not_true_eq_false,and_false,ite_false,mul_one]
    have hw : 1 ≤ (p:ℝ)/((p:ℝ)-1) := (le_div_iff₀ h1).mpr (by linarith)
    rw [abs_of_nonneg (sub_nonneg.mpr hw),abs_of_nonneg (by linarith : 0 ≤ (p:ℝ)/((p:ℝ)-1))]
    ring
  · have pn : 2 < p := by
      have := hp.two_le
      by_contra! bad
      exact hm (show p ∣ m by simpa [show p=2 by omega] using even_iff_two_dvd.mp he)
    have hp2 : (2:ℝ)<p := by exact_mod_cast pn
    have h2 : 0 < (p:ℝ)-2 := by linarith
    have h0 : 0 < (p:ℝ) := by linarith
    have hk : ¬p ∣ L*m := fun H => (hp.dvd_mul.mp H).elim hL hm
    simp only [localWeight,ite_eq_right hm,correction,ite_eq_left (And.intro hp (And.intro pn hk))]
    have hw : (p:ℝ)*((p:ℝ)-2)/((p:ℝ)-1)^2 ≤ 1 :=
      (div_le_one (sq_pos_of_pos h1)).mpr (by nlinarith)
    rw [abs_of_nonpos (sub_nonpos.mpr hw),abs_of_nonneg (div_nonneg (mul_nonneg h0.le h2.le) (sq_nonneg _))]
    field_simp [h0.ne',h1.ne',h2.ne']
    ring

theorem finite_ratio {r s : ℕ} [NeZero r] [NeZero s] {α : DirichletCharacter ℂ r}
    {β : DirichletCharacter ℂ s} (hα : α.IsPrimitive) (hβ : β.IsPrimitive)
    (m : ℕ) (hm : 0 < m) (he : Even m) (t : ℕ) (ht : t ≠ 0) :
    let L := Nat.lcm r s
    ∑ d ∈ (L*t).divisors, ‖coefficient α β m d‖ =
      ‖∑ d ∈ (L*t).divisors, coefficient α β m d‖ *
        ∏ p ∈ t.primeFactors, correction (L*m) p := by
  intro L
  have hL : L ≠ 0 := (Nat.lcm_pos (NeZero.pos r) (NeZero.pos s)).ne'
  have rest : ∏ p ∈ t.primeFactors \ L.primeFactors, correction (L*m) p =
      ∏ p ∈ t.primeFactors, correction (L*m) p := by
    apply prod_subset sdiff_subset
    intro p hp hnot
    have hpL : p ∈ L.primeFactors := by
      by_contra H
      exact hnot (mem_sdiff.mpr ⟨hp,H⟩)
    have hd := (Nat.dvd_of_mem_primeFactors hpL).trans (dvd_mul_right L m)
    simp [correction,hd]
  rw [absolute_partial hα hβ m hm he t ht,partial_extension hα hβ m hm he t ht,
    norm_mul,Complex.norm_real,Real.norm_eq_abs,Finset.abs_prod,← rest,mul_assoc,← prod_mul_distrib]
  congr 1
  apply prod_congr rfl
  intro p hp
  have prime := Nat.prime_of_mem_primeFactors (mem_sdiff.mp hp).1
  exact factor_ratio prime he (fun hd => (mem_sdiff.mp hp).2 (Nat.mem_primeFactors.mpr ⟨prime,hd,hL⟩))

private theorem correction_multipliable (K : ℕ) : Multipliable (correction K) := by
  let g (p : ℕ) := correction K p-1
  have base := (Real.summable_one_div_nat_pow.mpr (by decide : 1<2)).mul_left (6:ℝ)
  have hs : Summable g := base.of_norm_bounded (fun p => by
    have hg : 0 ≤ g p := sub_nonneg.mpr (correction_one_le K p)
    rw [Real.norm_eq_abs,abs_of_nonneg hg]
    dsimp [g,correction]
    split_ifs with h
    · have hp : (3:ℝ) ≤ p := by exact_mod_cast h.2.1
      have hp0 : 0 < (p:ℝ) := by linarith
      have hp2 : 0 < (p:ℝ)-2 := by linarith
      field_simp [hp0.ne',hp2.ne']
      nlinarith [mul_nonneg hp0.le (show 0 ≤ (p:ℝ)-3 by linarith)]
    · rw [sub_self]
      positivity)
  exact (Real.multipliable_one_add_of_summable hs).congr (fun p => by dsimp [g]; ring)

private theorem correction_bound_step {p : ℕ} (hp : 2<p) (K : ℕ) :
    correction K p ≤ (((p:ℝ)-1)^2/((p:ℝ)*((p:ℝ)-2)))^2 := by
  have h : (2:ℝ)<p := by exact_mod_cast hp
  have hd : 0 < (p:ℝ)*((p:ℝ)-2) := mul_pos (by linarith) (by linarith)
  have algebra : ((p:ℝ)-1)^2/((p:ℝ)*((p:ℝ)-2)) = 1+1/((p:ℝ)*((p:ℝ)-2)) := by
    field_simp [hd.ne']
    ring
  rw [algebra]
  have hinv : 0 ≤ 1/((p:ℝ)*((p:ℝ)-2)) := by positivity
  unfold correction
  split_ifs <;> nlinarith [sq_nonneg (1/((p:ℝ)*((p:ℝ)-2))),show 2/((p:ℝ)*((p:ℝ)-2))=2*(1/((p:ℝ)*((p:ℝ)-2))) by ring]

private theorem initial_product (K : ℕ) : ∀ n : ℕ, 2 ≤ n →
    ∏ p ∈ range (n+1), correction K p ≤ (2*((n:ℝ)-1)/(n:ℝ))^2 := by
  intro n hn
  induction n,hn using Nat.le_induction with
  | base => norm_num [prod_range_succ,correction]
  | succ k hk ih =>
    have h : (2:ℝ)≤k := by exact_mod_cast hk
    have hk0 : (k:ℝ) ≠ 0 := by linarith
    have hk1 : (k:ℝ)-1 ≠ 0 := by linarith
    have hks : (k:ℝ)+1 ≠ 0 := by linarith
    rw [prod_range_succ]
    refine (mul_le_mul ih (correction_bound_step (by omega : 2<k+1) K)
      (zero_le_one.trans (correction_one_le K _)) (sq_nonneg _)).trans_eq ?_
    push_cast
    field_simp [hk0,hk1,hks,show (k:ℝ)+1-2 ≠ 0 by linarith]
    ring

theorem correction_product_le_four (K : ℕ) : ∏' p : ℕ, correction K p ≤ 4 := by
  apply le_of_tendsto ((correction_multipliable K).hasProd.tendsto_prod_nat.comp (tendsto_add_atTop_nat 1))
  filter_upwards [eventually_ge_atTop 2] with n hn
  apply (initial_product K n hn).trans
  have h : (2:ℝ)≤n := by exact_mod_cast hn
  have hn0 : 0 < (n:ℝ) := by linarith
  have ht : 2*((n:ℝ)-1)/(n:ℝ) ≤ 2 := (div_le_iff₀ hn0).mpr (by linarith)
  have hb : 0 ≤ 2*((n:ℝ)-1)/(n:ℝ) := div_nonneg (by linarith) hn0.le
  nlinarith [mul_nonneg (sub_nonneg.mpr ht) (show 0 ≤ 2+2*((n:ℝ)-1)/(n:ℝ) by linarith)]

private theorem abs_limit {r s : ℕ} [NeZero r] [NeZero s] (α : DirichletCharacter ℂ r)
    (β : DirichletCharacter ℂ s) (m : ℕ) (hm : 0 < m) (L : ℕ) (hL : L ≠ 0) :
    Tendsto (fun n : ℕ => ∑ d ∈ (L*n.factorial).divisors, ‖coefficient α β m d‖)
      atTop (𝓝 (∑' d : ℕ, ‖coefficient α β m d‖)) := by
  have hf : Tendsto (fun n : ℕ => insert 0 (L*n.factorial).divisors) atTop atTop := by
    apply tendsto_atTop.2
    intro S
    filter_upwards [eventually_ge_atTop (S.sup id)] with n hn
    intro d hd
    by_cases h : d=0
    · simp [h]
    exact mem_insert_of_mem (Nat.mem_divisors.mpr ⟨(Nat.dvd_factorial (Nat.pos_of_ne_zero h)
      ((S.le_sup (f := id) hd).trans hn)).trans (dvd_mul_left n.factorial L),
      mul_ne_zero hL n.factorial_ne_zero⟩)
  apply ((summable_coefficients α β m hm).hasSum.comp hf).congr'
  filter_upwards with n
  simp [coefficient]

/-- Equality keeps precisely the odd primes outside the two conductors
and the target. It includes singular series which vanish. -/
theorem absolute_euler_product {r s : ℕ} [NeZero r] [NeZero s]
    {α : DirichletCharacter ℂ r} {β : DirichletCharacter ℂ s}
    (hα : α.IsPrimitive) (hβ : β.IsPrimitive) (m : ℕ) (hm : 0 < m) (he : Even m) :
    ∑' d : ℕ, ‖coefficient α β m d‖ =
      ‖∑' d : ℕ, coefficient α β m d‖ * ∏' p : ℕ, correction (Nat.lcm r s*m) p := by
  let L := Nat.lcm r s
  have hL : L ≠ 0 := (Nat.lcm_pos (NeZero.pos r) (NeZero.pos s)).ne'
  let K := L*m
  have h := (partial_limit α β m hm L hL).norm.mul
    ((correction_multipliable K).hasProd.tendsto_prod_nat.comp (tendsto_add_atTop_nat 1))
  refine tendsto_nhds_unique (abs_limit α β m hm L hL) (h.congr' ?_)
  filter_upwards with n
  change ‖∑ d ∈ (L*n.factorial).divisors, coefficient α β m d‖ * (∏ p ∈ range (n+1), correction K p) = _
  rw [finite_ratio hα hβ m hm he n.factorial n.factorial_ne_zero]
  congr 1
  symm
  apply prod_subset
  · intro p hp
    exact mem_range.mpr (Nat.lt_succ_of_le ((Nat.prime_of_mem_primeFactors hp).dvd_factorial.mp
      (Nat.dvd_of_mem_primeFactors hp)))
  · intro p hp hnot
    by_cases prime : p.Prime
    · exact False.elim (hnot (Nat.mem_primeFactors.mpr ⟨prime,prime.dvd_factorial.mpr
        (Nat.le_of_lt_succ (mem_range.mp hp)),n.factorial_ne_zero⟩))
    · simp [correction,prime]

theorem correction_le_universal (K : ℕ) : ∏' p : ℕ, correction K p ≤ ∏' p : ℕ, correction 1 p := by
  apply le_of_tendsto_of_tendsto' (correction_multipliable K).hasProd.tendsto_prod_nat
    (correction_multipliable 1).hasProd.tendsto_prod_nat
  intro n
  apply Finset.prod_le_prod₀ (fun p _ => zero_le_one.trans (correction_one_le K p))
  intro p _
  by_cases h : p.Prime ∧ 2<p ∧ ¬p ∣ K
  · have h1 : p.Prime ∧ 2<p ∧ ¬p ∣ 1 := ⟨h.1,h.2.1,h.1.not_dvd_one⟩
    simp only [correction,ite_eq_left h,ite_eq_left h1,le_refl]
  · rw [show correction K p = 1 by simp [correction,h]]
    exact correction_one_le 1 p

end Conjectures.Goldbach.TwistedGoldbachCoefficientProduct

/-! A power bound for truncating the generalized Goldbach singular series.
For primitive source characters, weight the coefficients at multiples of
their common level by a positive power of the excess denominator.
The primes dividing the target cost at most a divisor-type factor, while
the factors at all remaining primes have a convergent majorant.
This estimates the tail occurring in (10.21) of Pintz I.
https://arxiv.org/abs/1804.05561 -/

namespace Conjectures.Goldbach.TwistedGoldbachDenominatorTail

open Finset DirichletCharacter Filter Topology
open TwistedGoldbachCoefficientProduct TwistedGoldbachSingularSeries TwistedGoldbachMixedPrincipal
open scoped BigOperators Classical

private noncomputable def majorant (u : ℝ) (p : ℕ) := 1+4*(p:ℝ)^(u-2)

private theorem majorant_ge_one (u : ℝ) (p : ℕ) : 1 ≤ majorant u p :=
  le_add_of_nonneg_right (mul_nonneg (by norm_num) (Real.rpow_nonneg (Nat.cast_nonneg p) _))

private theorem majorant_converges {u : ℝ} (hu : u < 1) : Multipliable (majorant u) :=
  Real.multipliable_one_add_of_summable ((Real.summable_nat_rpow.mpr (by linarith : u-2 < -1)).mul_left 4)

private theorem weighted_atom (L t m : ℕ) (u : ℝ) :
    (t:ℝ)^u * |atom L t (fun p => localWeight m p-1)| =
      atom L t (fun p => (p:ℝ)^u*|localWeight m p-1|) := by
  unfold atom
  split_ifs with h
  · have square : (∏ p ∈ t.primeFactors, (p:ℝ)) = t := by
      rw [← Nat.cast_prod,Nat.prod_primeFactors_of_squarefree h.1]
    rw [Finset.abs_prod,prod_mul_distrib,Real.finsetProd_rpow _ _ (fun p _ => Nat.cast_nonneg p) u,square]
  · simp

private theorem prime_weight {p m : ℕ} (hp : p.Prime) (hm : 0 < m) {u : ℝ} (hu : u ≤ 1) :
    1+(p:ℝ)^u*|localWeight m p-1| ≤
      majorant u p * (if p ∈ m.primeFactors then 3 else 1) := by
  have h2 : (2:ℝ) ≤ p := by exact_mod_cast hp.two_le
  have h0 : 0 < (p:ℝ) := by linarith
  have h1 : 0 < (p:ℝ)-1 := by linarith
  have nonneg := Real.rpow_nonneg h0.le u
  by_cases hd : p ∣ m
  · have mem := Nat.mem_primeFactors.mpr ⟨hp,hd,hm.ne'⟩
    rw [ite_eq_left mem]
    have atom_eq : localWeight m p-1 = 1/((p:ℝ)-1) := by
      simp only [localWeight,ite_eq_left hd]
      field_simp
      ring
    rw [atom_eq,abs_of_nonneg (by positivity)]
    have hpu : (p:ℝ)^u ≤ (p:ℝ) := by simpa using Real.rpow_le_rpow_of_exponent_le (by linarith : (1:ℝ) ≤ p) hu
    have hrat : (p:ℝ)/((p:ℝ)-1) ≤ 2 := (div_le_iff₀ h1).mpr (by linarith)
    have hw := mul_le_mul_of_nonneg_right hpu (by positivity : 0 ≤ 1/((p:ℝ)-1))
    simp only [mul_one_div] at hw ⊢
    linarith [majorant_ge_one u p]
  · have mem : p ∉ m.primeFactors := fun h => hd (Nat.dvd_of_mem_primeFactors h)
    rw [ite_eq_right mem,mul_one]
    have atom_eq : localWeight m p-1 = -(1/((p:ℝ)-1)^2) := by
      simp only [localWeight,ite_eq_right hd]
      field_simp
      ring
    rw [atom_eq,abs_neg,abs_of_nonneg (by positivity)]
    unfold majorant
    rw [Real.rpow_sub h0,Real.rpow_two]
    apply add_le_add_right
    have denom : 1/((p:ℝ)-1)^2 ≤ 4/(p:ℝ)^2 := by
      rw [div_le_div_iff₀ (sq_pos_of_pos h1) (sq_pos_of_pos h0)]
      nlinarith [mul_nonneg (show 0 ≤ (p:ℝ)-2 by linarith) (show 0 ≤ 3*(p:ℝ)-2 by linarith)]
    calc
      _ ≤ (p:ℝ)^u*(4/(p:ℝ)^2) := mul_le_mul_of_nonneg_left denom nonneg
      _ = _ := by ring

private theorem product_bound (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) {m : ℕ} (hm : 0 < m)
    {u : ℝ} (hu : u < 1) :
    ∏ p ∈ S, (1+(p:ℝ)^u*|localWeight m p-1|) ≤
      (∏' p : ℕ, majorant u p) * 3^m.primeFactors.card := by
  calc
    _ ≤ ∏ p ∈ S, (majorant u p * (if p ∈ m.primeFactors then 3 else 1)) :=
      prod_le_prod₀ (fun p _ => by positivity) (fun p hp => prime_weight (hS p hp) hm hu.le)
    _ = (∏ p ∈ S, majorant u p) * (3:ℝ)^(S ∩ m.primeFactors).card := by
      rw [prod_mul_distrib,prod_ite_mem]
      simp
    _ ≤ _ := mul_le_mul
      ((majorant_converges hu).prod_le_tprod_of_nonneg (fun p _ => zero_le_one.trans (majorant_ge_one u p))
        (fun p _ => majorant_ge_one u p))
      (pow_le_pow_right₀ (by norm_num) (card_le_card inter_subset_right))
      (by positivity) (tprod_nonneg (fun p => zero_le_one.trans (majorant_ge_one u p)))

/-- The number of distinct primes dividing the target only costs an
arbitrarily small power, uniformly in the target. -/
theorem target_factor {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 0 < m → (3:ℝ)^m.primeFactors.card ≤ C*(m:ℝ)^ε := by
  have limit := (tendsto_rpow_atTop hε).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  obtain ⟨N,hN⟩ := (tendsto_atTop.1 limit (3:ℝ)).exists_forall_of_atTop
  refine ⟨3^N,by positivity,?_⟩
  intro m hm
  let S := m.primeFactors
  have small (p : ℕ) (hp : p ∈ S) :
      (3:ℝ) ≤ (if p ∈ range N then 3 else 1)*(p:ℝ)^ε := by
    have h := (Nat.prime_of_mem_primeFactors hp).one_le
    have hpow : (1:ℝ) ≤ (p:ℝ)^ε := Real.one_le_rpow (by exact_mod_cast h) hε.le
    by_cases H : p ∈ range N
    · rw [ite_eq_left H]
      linarith
    · rw [ite_eq_right H,one_mul]
      exact hN p (by simpa using H)
  have rad : ∏ p ∈ S, (p:ℝ) ≤ (m:ℝ) := by
    rw [← Nat.cast_prod]
    exact_mod_cast Nat.le_of_dvd hm (Nat.prod_primeFactors_dvd m)
  calc
    (3:ℝ)^S.card = ∏ _p ∈ S, (3:ℝ) := by simp
    _ ≤ ∏ p ∈ S, ((if p ∈ range N then 3 else 1)*(p:ℝ)^ε) := prod_le_prod₀ (by intros; positivity) small
    _ = (3:ℝ)^(S ∩ range N).card * (∏ p ∈ S, (p:ℝ))^ε := by
      rw [prod_mul_distrib,prod_ite_mem,Real.finsetProd_rpow _ _ (fun p _ => Nat.cast_nonneg p) ε]
      simp
    _ ≤ _ := mul_le_mul (pow_le_pow_right₀ (by norm_num)
        ((card_le_card (inter_subset_right (s₁ := S) (s₂ := range N))).trans_eq (card_range N)))
      (Real.rpow_le_rpow (prod_nonneg (fun p _ => Nat.cast_nonneg p)) rad hε.le)
      (by positivity) (by positivity)

section Estimates
variable {r s : ℕ} [NeZero r] [NeZero s] {α : DirichletCharacter ℂ r} {β : DirichletCharacter ℂ s}
  (hα : α.IsPrimitive) (hβ : β.IsPrimitive) (m : ℕ) (hm : 0 < m) (he : Even m)
include hα hβ hm he

private theorem weighted_divisors (n : ℕ) (hn : n ≠ 0) {u : ℝ} (hu : u < 1) :
    let L := Nat.lcm r s
    ∑ t ∈ n.divisors, (t:ℝ)^u * ‖coefficient α β m (L*t)‖ ≤
      ‖coefficient α β m L‖ * ((∏' p : ℕ, majorant u p) * 3^m.primeFactors.card) := by
  intro L
  have hL : L ≠ 0 := (Nat.lcm_pos (NeZero.pos r) (NeZero.pos s)).ne'
  let g (p : ℕ) := (p:ℝ)^u*|localWeight m p-1|
  have eqn : ∀ t ∈ n.divisors, (t:ℝ)^u * ‖coefficient α β m (L*t)‖ = ‖coefficient α β m L‖ * atom L t g := by
    intro t ht
    rw [coefficient_extension hα hβ m hm he t (Nat.pos_of_mem_divisors ht).ne',
      norm_mul,Complex.norm_real,Real.norm_eq_abs,mul_left_comm,weighted_atom]
  rw [sum_congr rfl eqn,← mul_sum,sum_atoms L n hL hn]
  exact mul_le_mul_of_nonneg_left (product_bound _ (fun _ hp => Nat.prime_of_mem_primeFactors (mem_sdiff.mp hp).1) hm hu) (norm_nonneg _)

private theorem weighted_finite {u : ℝ} (hu : u < 1) (S : Finset ℕ) :
    let L := Nat.lcm r s
    ∑ t ∈ S, (t:ℝ)^u * ‖coefficient α β m (L*t)‖ ≤
      ‖coefficient α β m L‖ * ((∏' p : ℕ, majorant u p) * 3^m.primeFactors.card) := by
  intro L
  let N := (S.sup id).factorial
  have hN : N ≠ 0 := Nat.factorial_ne_zero _
  have cover : S ⊆ insert 0 N.divisors := by
    intro d hd
    by_cases hz : d=0
    · simp [hz]
    · exact mem_insert_of_mem (Nat.mem_divisors.mpr ⟨Nat.dvd_factorial (Nat.pos_of_ne_zero hz) (S.le_sup (f:=id) hd),hN⟩)
  apply (sum_le_sum_of_subset_of_nonneg cover (fun p _ _ => mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg p) _) (norm_nonneg _))).trans
  simpa [L,N,coefficient] using weighted_divisors hα hβ m hm he N hN hu

theorem weighted_series {u : ℝ} (hu : u < 1) :
    let L := Nat.lcm r s
    let f := fun t : ℕ => (t:ℝ)^u*‖coefficient α β m (L*t)‖
    Summable f ∧ (∑' t : ℕ, f t) ≤
      ‖coefficient α β m L‖ * ((∏' p : ℕ, majorant u p) * 3^m.primeFactors.card) := by
  intro L f
  have nonneg : 0 ≤ f := fun t => mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg t) _) (norm_nonneg _)
  have sums := weighted_finite hα hβ m hm he hu
  exact ⟨summable_of_sum_le nonneg sums,Real.tsum_le_of_sum_le nonneg sums⟩

end Estimates

/-- Rankin's bound for the discarded denominators. Its constant is
independent of both primitive characters, their conductors and the target. -/
theorem uniform_tail {u ε : ℝ} (hu0 : 0 ≤ u) (hu : u < 1) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (r s : ℕ) [NeZero r] [NeZero s] (α : DirichletCharacter ℂ r) (β : DirichletCharacter ℂ s),
      α.IsPrimitive → β.IsPrimitive → ∀ m : ℕ, 0 < m → Even m → ∀ T : ℕ, 0<T →
      let L := Nat.lcm r s
      (∑' t : ℕ, if T ≤ t then ‖coefficient α β m (L*t)‖ else 0) ≤
        C * ‖∑' d : ℕ, coefficient α β m d‖ * (m:ℝ)^ε / (T:ℝ)^u := by
  obtain ⟨D,hD,Dm⟩ := target_factor hε
  let P := ∏' p : ℕ, majorant u p
  have Pone : 1 ≤ P := by
    simpa using (majorant_converges hu).prod_le_tprod_of_nonneg (s := (∅:Finset ℕ))
      (fun p _ => zero_le_one.trans (majorant_ge_one u p)) (fun p _ => majorant_ge_one u p)
  refine ⟨4*P*D,by positivity [zero_lt_one.trans_le Pone],?_⟩
  intro r s _ _ α β hα hβ m hm he T hT L
  let c := coefficient α β m
  have positive : 0 < (T:ℝ)^u := Real.rpow_pos_of_pos (by exact_mod_cast hT) u
  have single : ‖c L‖ ≤ ∑' d : ℕ, ‖c d‖ :=
    (summable_coefficients α β m hm).le_tsum L (fun d _ => norm_nonneg _)
  have comp := absolute_euler_product hα hβ m hm he
  have cL : ‖c L‖ ≤ ‖∑' d : ℕ, c d‖*4 :=
    single.trans ((le_of_eq comp).trans (mul_le_mul_of_nonneg_left (correction_product_le_four _) (norm_nonneg _)))
  have ⟨hws,hwb⟩ := weighted_series hα hβ m hm he hu
  let tail (t : ℕ) : ℝ := if T ≤ t then ‖c (L*t)‖ else 0
  have htail (t : ℕ) : (T:ℝ)^u*tail t ≤ (t:ℝ)^u*‖c (L*t)‖ := by
    dsimp [tail]
    split_ifs with ht
    · exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (Nat.cast_nonneg T) (by exact_mod_cast ht) hu0) (norm_nonneg _)
    · rw [mul_zero]
      exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg t) _) (norm_nonneg _)
  have hs : Summable (fun t : ℕ => (T:ℝ)^u*tail t) := Summable.of_nonneg_of_le
    (fun t => mul_nonneg positive.le (by dsimp [tail]; split_ifs <;> positivity)) htail hws
  have bound := hs.tsum_le_tsum htail hws
  rw [tsum_mul_left] at bound
  apply (le_div_iff₀ positive).mpr
  change (∑' t : ℕ, tail t)*(T:ℝ)^u ≤ _
  rw [mul_comm]
  calc
    _ ≤ ‖c L‖*(P*3^m.primeFactors.card) := bound.trans hwb
    _ ≤ (‖∑' d : ℕ, c d‖*4)*(P*(D*(m:ℝ)^ε)) :=
      mul_le_mul cL (mul_le_mul_of_nonneg_left (Dm m hm) (zero_le_one.trans Pone))
        (mul_nonneg (zero_le_one.trans Pone) (by positivity)) (mul_nonneg (norm_nonneg _) (by norm_num))
    _ = _ := by ring

/-- At excess denominator at least X^δ, the tail saves X^(δ/2)
uniformly for positive even targets at most X. -/
theorem power_cutoff {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (r s : ℕ) [NeZero r] [NeZero s] (α : DirichletCharacter ℂ r) (β : DirichletCharacter ℂ s),
      α.IsPrimitive → β.IsPrimitive → ∀ m X T : ℕ, 0 < m → Even m → m ≤ X → (X:ℝ)^δ ≤ (T:ℝ) →
      (∑' t : ℕ, if T ≤ t then ‖coefficient α β m (Nat.lcm r s*t)‖ else 0) ≤
        C * ‖∑' d : ℕ, coefficient α β m d‖ / (X:ℝ)^(δ/2) := by
  obtain ⟨C,hC,H⟩ := uniform_tail (by norm_num : 0 ≤ (3/4:ℝ)) (by norm_num) (by linarith : 0 < δ/4)
  refine ⟨C,hC,?_⟩
  intro r s _ _ α β hα hβ m X T hm he hX hT
  have hx : (0:ℝ) < X := by exact_mod_cast hm.trans_le hX
  have ht : (0:ℝ) < T := (Real.rpow_pos_of_pos hx δ).trans_le hT
  have h := H r s α β hα hβ m hm he T (by exact_mod_cast ht)
  have weights : (m:ℝ)^(δ/4) * (X:ℝ)^(δ/2) ≤ (T:ℝ)^(3/4:ℝ) := by
    calc
      _ ≤ (X:ℝ)^(δ/4) * (X:ℝ)^(δ/2) := mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow (Nat.cast_nonneg m) (by exact_mod_cast hX) (by linarith)) (by positivity)
      _ = ((X:ℝ)^δ)^(3/4:ℝ) := by
        rw [← Real.rpow_add hx,← Real.rpow_mul hx.le]
        congr 1
        ring
      _ ≤ _ := Real.rpow_le_rpow (Real.rpow_nonneg hx.le _) hT (by norm_num)
  refine h.trans ((div_le_div_iff₀ (Real.rpow_pos_of_pos ht _) (Real.rpow_pos_of_pos hx _)).mpr ?_)
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left weights (mul_nonneg hC.le (norm_nonneg _))

end Conjectures.Goldbach.TwistedGoldbachDenominatorTail

namespace Conjectures.Goldbach

private def representationCount (n : ℕ) : ℕ :=
  ((Finset.range (n + 1)).filter (fun p => Nat.Prime p ∧ Nat.Prime (n - p))).card

private def unshiftedExceptions (X : ℕ) : Finset ℕ :=
  (Finset.range (X + 1)).filter (fun n => 4 ≤ n ∧ n % 2 = 0 ∧ representationCount n = 0)

private def shiftedExceptions (X : ℕ) : Finset ℕ :=
  (Finset.Ico X (2 * X)).filter (fun n =>
    Even n ∧ 0 < ((Finset.Icc 1 (Nat.log 2 X / 2)).filter
      (fun e => representationCount (n - 2 ^ e) = 0)).card)

private theorem shiftedExceptions_card_le (X : ℕ) (hX : 8 ≤ X) :
    (shiftedExceptions X).card ≤ (Nat.log 2 X / 2) * (unshiftedExceptions (2 * X)).card := by
  classical
  let shifts := Finset.Icc 1 (Nat.log 2 X / 2)
  let pairs := shifts.product (unshiftedExceptions (2 * X))
  let addShift := fun pair : ℕ × ℕ => pair.2 + 2 ^ pair.1
  have hsubset : shiftedExceptions X ⊆ pairs.image addShift := by
    intro n hn
    unfold shiftedExceptions at hn
    obtain ⟨hnInterval, hnEven, hnMissing⟩ := Finset.mem_filter.mp hn
    obtain ⟨hnLower, hnUpper⟩ := Finset.mem_Ico.mp hnInterval
    obtain ⟨e, he⟩ := Finset.card_pos.mp hnMissing
    obtain ⟨heShift, heMissing⟩ := Finset.mem_filter.mp he
    obtain ⟨heLower, heUpper⟩ := Finset.mem_Icc.mp heShift
    have hpow : 2 ^ (e + 1) ≤ X :=
      (Nat.pow_le_pow_right (by decide) (show e + 1 ≤ Nat.log 2 X by omega)).trans
        (Nat.pow_log_le_self 2 (by omega))
    rw [pow_succ] at hpow
    have heEven : 2 ∣ (2 : ℕ) ^ e := dvd_pow_self 2 (by omega)
    have hsubEven : (n - 2 ^ e) % 2 = 0 :=
      Nat.dvd_iff_mod_eq_zero.mp (Nat.dvd_sub (even_iff_two_dvd.mp hnEven) heEven)
    have hsub : n - 2 ^ e ∈ unshiftedExceptions (2 * X) := by
      unfold unshiftedExceptions
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), by omega, hsubEven, heMissing⟩
    refine Finset.mem_image.mpr ⟨(e, n - 2 ^ e), Finset.mem_product.mpr ⟨heShift, hsub⟩, ?_⟩
    dsimp [addShift]
    omega
  calc
    _ ≤ (pairs.image addShift).card := Finset.card_le_card hsubset
    _ ≤ pairs.card := Finset.card_image_le
    _ = _ := by simp [pairs, shifts, Nat.card_Icc]

/-- Every ordinary exception in the translated dyadic interval contributes to
the shifted exceptional set through the shift `2^1`. -/
theorem dyadicExceptions_card_le_shifted (X : ℕ) (hX : 4 ≤ X) :
    ((Finset.Ico (X - 2) (2 * X - 2)).filter
      (fun n => 4 ≤ n ∧ n % 2 = 0 ∧ representationCount n = 0)).card ≤
    (shiftedExceptions X).card := by
  refine Finset.card_le_card_of_injOn (fun n : ℕ => n + 2) ?_ ?_
  · intro n hn
    obtain ⟨hnInterval, _, hnEven, hnMissing⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hn)
    obtain ⟨hnLower, hnUpper⟩ := Finset.mem_Ico.mp hnInterval
    change n + 2 ∈ shiftedExceptions X
    unfold shiftedExceptions
    refine Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega, by omega⟩, ?_, ?_⟩
    · exact Nat.even_iff.mpr (by omega)
    · apply Finset.card_pos.mpr
      refine ⟨1, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_rfl, ?_⟩, ?_⟩⟩
      · have hlog : 2 ≤ Nat.log 2 X := Nat.le_log_of_pow_le (by decide) (by simpa using hX)
        omega
      · simpa using hnMissing
  · intro a _ b _ h
    exact Nat.add_right_cancel h

private theorem shift_count_le_log_div (X : ℕ) (hX : 0 < X) :
    ((Nat.log 2 X / 2 : ℕ) : ℝ) ≤ Real.log (X : ℝ) / Real.log 2 := by
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpow : (2 : ℝ) ^ Nat.log 2 X ≤ (X : ℝ) := by
    exact_mod_cast Nat.pow_log_le_self 2 hX.ne'
  apply (le_div_iff₀ hlogTwo).mpr
  calc
    _ ≤ (Nat.log 2 X : ℝ) * Real.log 2 :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.div_le_self (Nat.log 2 X) 2) hlogTwo.le
    _ = Real.log ((2 : ℝ) ^ Nat.log 2 X) := (Real.log_pow 2 _).symm
    _ ≤ _ := Real.log_le_log (by positivity) hpow

/-- Any exponent strictly below `4/5` for the ordinary exceptional set implies
the registered bound. Pintz's exponent `18/25` qualifies
(https://arxiv.org/abs/1804.09084). -/
theorem binaryShiftExceptionUnion_of_exceptionBound
    {α : ℝ} (hα : α < 4/5)
    (h : ∃ (C : ℝ) (X₀ : ℕ), 0 < C ∧ ∀ X : ℕ, X₀ ≤ X →
      ((unshiftedExceptions X).card : ℝ) ≤ C * (X : ℝ) ^ α) :
    let G := fun m : ℕ =>
      ((Finset.range (m + 1)).filter (fun p => Nat.Prime p ∧ Nat.Prime (m - p))).card
    ∃ X₀ : ℕ, ∀ X ≥ X₀,
      let L := Nat.log 2 X / 2
      let E := (Finset.Ico X (2 * X)).filter (fun n =>
        Even n ∧ 0 < ((Finset.Icc 1 L).filter (fun e => G (n - 2 ^ e) = 0)).card)
      E.card ^ 5 ≤ X ^ 4 := by
  change ∃ X₀ : ℕ, ∀ X ≥ X₀, (shiftedExceptions X).card ^ 5 ≤ X ^ 4
  obtain ⟨C, X₀, hC, hcount⟩ := h
  let A := C * (2 : ℝ) ^ α
  have hA : 0 < A := by dsimp [A]; positivity
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp
    ((isLittleO_log_rpow_atTop (sub_pos.mpr hα)).const_mul_left (A / Real.log 2)).eventuallyLE
  refine ⟨max 8 (max X₀ ⌈T⌉₊), ?_⟩
  intro X hX
  have hXNonnegative : (0 : ℝ) ≤ X := Nat.cast_nonneg X
  have hXPositive : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hXT : T ≤ (X : ℝ) := (Nat.le_ceil _).trans (Nat.cast_le.mpr (by omega))
  let L := Nat.log 2 X / 2
  have hshiftFactor : A * (L : ℝ) ≤ (X : ℝ) ^ (4/5 - α) := by
    have hasymptotic := hT (X : ℝ) hXT
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hXNonnegative _)] at hasymptotic
    calc
      _ ≤ A * (Real.log X / Real.log 2) :=
        mul_le_mul_of_nonneg_left (shift_count_le_log_div X (by omega)) hA.le
      _ = (A / Real.log 2) * Real.log X := by ring
      _ ≤ _ := (Real.le_norm_self _).trans hasymptotic
  have hdouble := hcount (2 * X) (by omega)
  norm_num [Nat.cast_mul, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hXNonnegative] at hdouble
  have hcard : ((shiftedExceptions X).card : ℝ) ≤ (X : ℝ) ^ (4/5 : ℝ) := calc
    _ ≤ (L : ℝ) * ((unshiftedExceptions (2 * X)).card : ℝ) := by
      exact_mod_cast shiftedExceptions_card_le X (show 8 ≤ X by omega)
    _ ≤ (L : ℝ) * (C * ((2 : ℝ) ^ α * (X : ℝ) ^ α)) :=
      mul_le_mul_of_nonneg_left hdouble (Nat.cast_nonneg _)
    _ = (A * (L : ℝ)) * (X : ℝ) ^ α := by dsimp [A]; ring
    _ ≤ (X : ℝ) ^ (4/5 - α) * (X : ℝ) ^ α :=
      mul_le_mul_of_nonneg_right hshiftFactor (Real.rpow_nonneg hXNonnegative _)
    _ = _ := by rw [← Real.rpow_add hXPositive, sub_add_cancel]
  have hpower : ((shiftedExceptions X).card : ℝ) ^ 5 ≤ (X : ℝ) ^ (4 : ℕ) := calc
    _ ≤ ((X : ℝ) ^ (4/5 : ℝ)) ^ 5 := pow_le_pow_left₀ (Nat.cast_nonneg _) hcard 5
    _ = _ := by
      rw [← Real.rpow_mul_natCast hXNonnegative,
        show (4/5 : ℝ) * (5 : ℕ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  exact_mod_cast hpower

namespace BinaryShiftCircle

open Filter MeasureTheory
open scoped BigOperators Topology

noncomputable section

private def phase (t : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I)

private def primeWeight (p : ℕ) : ℝ :=
  if p.Prime then Real.log (p : ℝ) else 0

private def primeSum (X : ℕ) (t : ℝ) : ℂ :=
  ∑ p ∈ Finset.range (X + 1), (primeWeight p : ℂ) * phase ((p : ℝ) * t)

private def integrand (X n : ℕ) (t : ℝ) : ℂ :=
  (primeSum X t)^2 * phase (-(n : ℝ) * t)

def rationalArcs (X : ℕ) (P : ℝ) : Set ℝ :=
  { t : ℝ | ∃ (q : ℕ) (a : ℤ), 1 ≤ q ∧ (q : ℝ) ≤ P ∧ IsCoprime a (q : ℤ) ∧
    |t - (a : ℝ) / q| ≤ P / ((q : ℝ) * X) }

theorem rationalArcs_measurable (X : ℕ) (P : ℝ) : MeasurableSet (rationalArcs X P) := by
  simp only [rationalArcs, Set.ofPred_exists]
  refine MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun a => ?_
  by_cases h : 1 ≤ q ∧ (q : ℝ) ≤ P ∧ IsCoprime a (q : ℤ)
  · have hArc : MeasurableSet {t : ℝ | |t - (a : ℝ) / q| ≤ P / ((q : ℝ) * X)} :=
      measurableSet_le (show Continuous (fun t : ℝ => |t - (a : ℝ) / q|) by fun_prop).measurable
        measurable_const
    convert hArc using 1
    ext t
    simp [h.1, h.2.1, h.2.2]
  · convert MeasurableSet.empty (α := ℝ) using 1
    ext t
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨hq, hqP, hcop, _⟩
    exact h ⟨hq, hqP, hcop⟩

private def cutoff (X : ℕ) : ℕ := ⌊(X : ℝ) ^ (11/40 : ℝ)⌋₊

def baseArcs (X : ℕ) : Set ℝ := rationalArcs X (cutoff X)

theorem baseArcs_subset (X : ℕ) {P : ℝ} (hP : (cutoff X : ℝ) ≤ P) :
    baseArcs X ⊆ rationalArcs X P := by
  intro t ht
  obtain ⟨q, a, hq, hqP, hcop, hclose⟩ := ht
  exact ⟨q, a, hq, hqP.trans hP, hcop,
    hclose.trans (div_le_div_of_nonneg_right hP (by positivity))⟩

def arcCoefficient (X n : ℕ) (A : Set ℝ) : ℂ :=
  intervalIntegral (A.indicator (integrand X n)) (0 : ℝ) 1 volume

private def truncatedIntegrand (X Y n : ℕ) (t : ℝ) : ℂ :=
  (∑ p ∈ Finset.range (X + 1),
    (((if p ≤ Y then 0 else primeWeight p) : ℝ) : ℂ) * phase ((p : ℝ) * t))^2 *
    phase (-(n : ℝ) * t)

def truncatedArcCoefficient (X Y n : ℕ) (A : Set ℝ) : ℂ :=
  intervalIntegral (A.indicator (truncatedIntegrand X Y n)) (0 : ℝ) 1 volume

private theorem rationalArcs_add_one (X : ℕ) (P t : ℝ) :
    t + 1 ∈ rationalArcs X P ↔ t ∈ rationalArcs X P := by
  have translate (x : ℝ) (j : ℤ) (hx : x ∈ rationalArcs X P) :
      x + (j : ℝ) ∈ rationalArcs X P := by
    obtain ⟨q, a, hq, hqP, hcop, hnear⟩ := hx
    have hcop' : IsCoprime (a + j * (q : ℤ)) (q : ℤ) := by
      obtain ⟨u, v, huv⟩ := hcop
      exact ⟨u, v - u * j, by linear_combination huv⟩
    refine ⟨q, a + j * (q : ℤ), hq, hqP, hcop', ?_⟩
    have hqNe : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have heq : x + (j : ℝ) - ((a + j * (q : ℤ) : ℤ) : ℝ) / (q : ℝ) =
        x - (a : ℝ) / (q : ℝ) := by
      push_cast
      field_simp [hqNe]
      ring
    rw [heq]
    exact hnear
  constructor
  · intro h
    simpa using translate (t + 1) (-1) h
  · intro h
    simpa using translate t 1 h

private theorem phase_mul_add_one (k : ℤ) (t : ℝ) :
    phase ((k : ℝ) * (t + 1)) = phase ((k : ℝ) * t) := by
  unfold phase
  have hAdd : ((2 * Real.pi * ((k : ℝ) * (t + 1)) : ℝ) : ℂ) * Complex.I =
      (((2 * Real.pi * ((k : ℝ) * t) : ℝ) : ℂ) * Complex.I) +
        (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [hAdd, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- The integral can use Pintz's translated fundamental interval. -/
theorem truncatedArcCoefficient_eq_translated (X Y n : ℕ) (P b : ℝ) :
    truncatedArcCoefficient X Y n (rationalArcs X P) =
      intervalIntegral ((rationalArcs X P).indicator (truncatedIntegrand X Y n))
        b (b + 1) volume := by
  have hPeriod : Function.Periodic
      ((rationalArcs X P).indicator (truncatedIntegrand X Y n)) 1 := by
    intro t
    by_cases ht : t ∈ rationalArcs X P
    · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ((rationalArcs_add_one X P t).mpr ht)]
      have hFreq : phase (-(n : ℝ) * (t + 1)) = phase (-(n : ℝ) * t) := by
        simpa using phase_mul_add_one (-(n : ℤ)) t
      have hPrime (p : ℕ) : phase ((p : ℝ) * (t + 1)) = phase ((p : ℝ) * t) := by
        simpa using phase_mul_add_one (p : ℤ) t
      simp only [truncatedIntegrand, hFreq, hPrime]
    · rw [Set.indicator_of_notMem ht,
        Set.indicator_of_notMem (fun h => ht ((rationalArcs_add_one X P t).mp h))]
  simpa only [truncatedArcCoefficient, zero_add] using hPeriod.intervalIntegral_add_eq 0 b

theorem norm_betaIntegral_le_diagonal {b : ℝ} (hb : 0 < b) {u v : ℂ}
    (hu : b ≤ u.re) (hv : b ≤ v.re) :
    ‖Complex.betaIntegral u v‖ ≤ ‖Complex.betaIntegral (b : ℂ) (b : ℂ)‖ := by
  let g : ℝ → ℂ := fun t => (t : ℂ) ^ ((b : ℂ) - 1) * (1 - (t : ℂ)) ^ ((b : ℂ) - 1)
  have hg : IntervalIntegrable g volume 0 1 :=
    Complex.betaIntegral_convergent (by simpa using hb) (by simpa using hb)
  have hgReal (t : ℝ) (ht : t ∈ Set.Ioo 0 1) :
      g t = ((t ^ (b - 1) * (1 - t) ^ (b - 1) : ℝ) : ℂ) := by
    dsimp [g]
    rw [Complex.ofReal_mul, Complex.ofReal_cpow ht.1.le, Complex.ofReal_cpow (by linarith [ht.2])]
    push_cast
    rfl
  have hgNorm (t : ℝ) (ht : t ∈ Set.Ioo 0 1) :
      ‖g t‖ = t ^ (b - 1) * (1 - t) ^ (b - 1) := by
    rw [hgReal t ht, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by
      exact mul_nonneg (Real.rpow_nonneg ht.1.le _) (Real.rpow_nonneg (by linarith [ht.2]) _))]
  have hIntegral : ‖Complex.betaIntegral u v‖ ≤ ∫ t in (0 : ℝ)..1, ‖g t‖ := by
    apply intervalIntegral.norm_integral_le_of_norm_le zero_le_one _ hg.norm
    filter_upwards [volume.ae_ne (1 : ℝ)] with t htOne ht
    have ht' : t ∈ Set.Ioo (0 : ℝ) 1 := ⟨ht.1, lt_of_le_of_ne ht.2 htOne⟩
    rw [hgNorm t ht', norm_mul, show (1 : ℂ) - (t : ℂ) = ((1 - t : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_cpow_eq_rpow_re_of_pos ht'.1,
      Complex.norm_cpow_eq_rpow_re_of_pos (sub_pos.mpr ht'.2)]
    simp only [Complex.sub_re, Complex.one_re]
    exact mul_le_mul
      (Real.rpow_le_rpow_of_exponent_ge ht'.1 ht'.2.le (sub_le_sub_right hu 1))
      (Real.rpow_le_rpow_of_exponent_ge (sub_pos.mpr ht'.2) (by linarith [ht'.1])
        (sub_le_sub_right hv 1))
      (Real.rpow_nonneg (by linarith [ht'.2]) _) (Real.rpow_nonneg ht'.1.le _)
  calc
    _ ≤ ∫ t in (0 : ℝ)..1, ‖g t‖ := hIntegral
    _ = ∫ t in (0 : ℝ)..1, (g t).re := by
      apply intervalIntegral.integral_congr_Ioo_of_le zero_le_one
      intro t ht
      change ‖g t‖ = (g t).re
      rw [hgNorm t ht, hgReal t ht, Complex.ofReal_re]
    _ = (Complex.betaIntegral (b : ℂ) (b : ℂ)).re :=
      intervalIntegral.intervalIntegral_re hg
    _ ≤ _ := Complex.re_le_norm _

/-- Uniform control of the beta factor in the contributions of zeros whose
real parts are close to one, as used in Pintz's equations (2.19)–(2.21). -/
theorem norm_betaIntegral_le_one_add {ε : ℝ} (hε : 0 < ε) :
    ∃ d : ℝ, 0 < d ∧ ∀ u v : ℂ, 1 - d ≤ u.re → 1 - d ≤ v.re →
      ‖Complex.betaIntegral u v‖ ≤ 1 + ε := by
  let gamma := fun b : ℝ => Complex.Gamma (b : ℂ)
  let gamma₂ := fun b : ℝ => Complex.Gamma ((b : ℂ) + (b : ℂ))
  let F := fun b => ‖gamma b * gamma b / gamma₂ b‖
  have hcast : ContinuousAt (fun b : ℝ => (b : ℂ)) 1 := Complex.continuous_ofReal.continuousAt
  have hΓ : ContinuousAt gamma 1 := by
    have h : ContinuousAt Complex.Gamma ((fun b : ℝ => (b : ℂ)) 1) := by
      simpa only [Complex.ofReal_one] using Complex.continuousAt_Gamma_one
    exact h.comp hcast
  have hΓ₂ : ContinuousAt gamma₂ 1 := by
    have h := Complex.continuousAt_Gamma (1 + 1) (by
      intro m he
      have hh := congrArg Complex.re he
      norm_num at hh
      linarith [Nat.cast_nonneg (α := ℝ) m])
    have hcast₂ : ContinuousAt (fun b : ℝ => (b : ℂ) + (b : ℂ)) 1 := hcast.add hcast
    exact h.comp_of_eq hcast₂ (by norm_num)
  have hΓ₂One : gamma₂ 1 = 1 := by
    change Complex.Gamma ((1 : ℂ) + 1) = 1
    rw [Complex.Gamma_add_one 1 one_ne_zero, Complex.Gamma_one, mul_one]
  have hF : ContinuousAt F 1 := ((hΓ.mul hΓ).div hΓ₂ (by rw [hΓ₂One]; exact one_ne_zero)).norm
  have hFOne : F 1 = 1 := by simp [F, gamma, hΓ₂One, Complex.Gamma_one]
  obtain ⟨r, hr, h⟩ := Metric.eventually_nhds_iff.mp <| hF (Iio_mem_nhds (by linarith : F 1 < 1 + ε))
  let d := min (1 / 2 : ℝ) (r / 2)
  have hd : 0 < d := lt_min (by norm_num) (by positivity)
  have hb : 0 < 1 - d := by linarith [min_le_left (1 / 2 : ℝ) (r / 2)]
  have hdist : dist (1 - d) 1 < r := by
    rw [Real.dist_eq, show 1 - d - 1 = -d by ring, abs_neg, abs_of_pos hd]
    linarith [min_le_right (1 / 2 : ℝ) (r / 2)]
  have hbeta : ‖Complex.betaIntegral ((1 - d : ℝ) : ℂ) ((1 - d : ℝ) : ℂ)‖ ≤ 1 + ε := by
    rw [Complex.betaIntegral_eq_Gamma_mul_div _ _ (by simpa using hb) (by simpa using hb)]
    exact (h hdist).le
  exact ⟨d, hd, fun u v hu hv => (norm_betaIntegral_le_diagonal hb hu hv).trans hbeta⟩

/-- A bound on the weights of nonprincipal zero pairs gives a positive real
part for the major-arc coefficient once the explicit formula is available. -/
theorem majorArcFloor_from_zeroPairSum {ι : Type*} {ε : ℝ} (hε : 0 < ε) :
    ∃ d : ℝ, 0 < d ∧
      ∀ (n s : ℝ) (value : ℂ) (I : Finset ι) (ρ σ coeff : ι → ℂ),
        0 < n → 0 ≤ s →
        (∀ i ∈ I, 1 - d ≤ (ρ i).re ∧ 1 - d ≤ (σ i).re ∧ ‖coeff i‖ ≤ s) →
        (∑ i ∈ I, n ^ ((ρ i).re + (σ i).re - 2)) ≤ 1 - ε →
        (let terms := ∑ i ∈ I, coeff i * Complex.betaIntegral (ρ i) (σ i) *
            (n : ℂ) ^ (ρ i + σ i - 1)
         ‖value - ((s * n : ℝ) + terms)‖ ≤ ε / 4 * (s * n)) →
        ε / 2 * (s * n) ≤ value.re := by
  obtain ⟨d, hd, hbeta⟩ := norm_betaIntegral_le_one_add (show 0 < ε / 4 by positivity)
  refine ⟨d, hd, ?_⟩
  intro n s value I ρ σ coeff hn hs hdata hweights herr
  let term := fun i => coeff i * Complex.betaIntegral (ρ i) (σ i) *
      (n : ℂ) ^ (ρ i + σ i - 1)
  have hterm (i : ι) (hi : i ∈ I) :
      ‖term i‖ ≤ (1 + ε / 4) * (s * n) * n ^ ((ρ i).re + (σ i).re - 2) := by
    obtain ⟨hρ, hσ, hcoef⟩ := hdata i hi
    have hfactor : ‖(n : ℂ) ^ (ρ i + σ i - 1)‖ = n * n ^ ((ρ i).re + (σ i).re - 2) := by
      calc
        _ = n ^ ((ρ i).re + (σ i).re - 1) := by
          rw [Complex.norm_cpow_eq_rpow_re_of_pos hn, Complex.sub_re, Complex.add_re, Complex.one_re]
        _ = n ^ (1 : ℝ) * n ^ ((ρ i).re + (σ i).re - 2) := by
          rw [← Real.rpow_add hn,
            show 1 + ((ρ i).re + (σ i).re - 2) = (ρ i).re + (σ i).re - 1 by ring]
        _ = _ := by rw [Real.rpow_one]
    calc
      _ = ‖coeff i‖ * ‖Complex.betaIntegral (ρ i) (σ i)‖ *
          (n * n ^ ((ρ i).re + (σ i).re - 2)) := by simp only [term, norm_mul, hfactor]
      _ ≤ s * (1 + ε / 4) * (n * n ^ ((ρ i).re + (σ i).re - 2)) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul hcoef (hbeta _ _ hρ hσ) (norm_nonneg _) hs) (by positivity)
      _ = _ := by ring
  have hsum : ‖∑ i ∈ I, term i‖ ≤ (1 - 3 * ε / 4) * (s * n) := calc
    _ ≤ ∑ i ∈ I, ‖term i‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ I, (1 + ε / 4) * (s * n) * n ^ ((ρ i).re + (σ i).re - 2) :=
      Finset.sum_le_sum hterm
    _ = (1 + ε / 4) * (s * n) * (∑ i ∈ I, n ^ ((ρ i).re + (σ i).re - 2)) := by
      rw [Finset.mul_sum]
    _ ≤ (1 + ε / 4) * (s * n) * (1 - ε) :=
      mul_le_mul_of_nonneg_left hweights (by positivity)
    _ ≤ _ := by nlinarith only [mul_nonneg (sq_nonneg ε) (mul_nonneg hs hn.le)]
  have hsumRe := Complex.re_le_norm (-(∑ i ∈ I, term i))
  rw [Complex.neg_re, norm_neg] at hsumRe
  change ‖value - (((s * n : ℝ) : ℂ) + ∑ i ∈ I, term i)‖ ≤ ε / 4 * (s * n) at herr
  have herrRe := Complex.re_le_norm (-(value - (((s * n : ℝ) : ℂ) + ∑ i ∈ I, term i)))
  simp only [Complex.neg_re, Complex.sub_re, Complex.add_re, Complex.ofReal_re, norm_neg] at herrRe
  linarith only [hsum, hsumRe, herr, herrRe]

/-- The cutoff used in Pintz's explicit formula changes each masked
coefficient by an arbitrarily small linear error. -/
private theorem truncationLoss {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ X : ℕ, N ≤ X → ∀ n : ℕ, ∀ A : Set ℝ, MeasurableSet A →
      ‖arcCoefficient X n A -
        truncatedArcCoefficient X ⌊(X : ℝ) ^ (1 - δ)⌋₊ n A‖ ≤ ε * (X : ℝ) := by
  let K := 2 * Real.log 4
  have hK : 0 < K := mul_pos (by norm_num) (Real.log_pos (by norm_num))
  have hLogEventually := ((isLittleO_log_rpow_atTop (r := δ / 2) (by positivity)).comp_tendsto
    tendsto_natCast_atTop_atTop).bound (div_pos hε hK)
  apply Filter.eventually_atTop.mp
  filter_upwards [eventually_ge_atTop (2 : ℕ), hLogEventually] with X hX hLog
  intro n A hA
  let x : ℝ := X
  let Y := ⌊x ^ (1 - δ)⌋₊
  have hx : 0 < x := Nat.cast_pos.mpr (by omega)
  have hx₁ : 1 ≤ x := by dsimp [x]; exact_mod_cast (show 1 ≤ X by omega)
  have hY : Y ≤ X := Nat.floor_le_of_le <|
    (Real.rpow_le_rpow_of_exponent_le hx₁ (by linarith : 1 - δ ≤ 1)).trans_eq (Real.rpow_one x)
  have hSqrt : Real.sqrt ((Y : ℝ) * x) ≤ x ^ (1 - δ / 2) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨Real.rpow_nonneg hx.le _, ?_⟩
    calc
      _ ≤ x ^ (1 - δ) * x :=
        mul_le_mul_of_nonneg_right (Nat.floor_le (Real.rpow_nonneg hx.le _)) hx.le
      _ = x ^ (2 - δ) := by
        rw [show (2 - δ : ℝ) = (1 - δ) + 1 by ring, Real.rpow_add hx, Real.rpow_one]
      _ = _ := by
        rw [← Real.rpow_mul_natCast hx.le]
        congr 1
        push_cast
        ring
  have hLogNonneg : 0 ≤ Real.log x := Real.log_nonneg hx₁
  change ‖Real.log x‖ ≤ ε / K * ‖x ^ (δ / 2)‖ at hLog
  rw [Real.norm_of_nonneg hLogNonneg, Real.norm_of_nonneg (Real.rpow_nonneg hx.le _)] at hLog
  have hcut : ‖arcCoefficient X n A - truncatedArcCoefficient X Y n A‖ ≤
      K * Real.log x * Real.sqrt ((Y : ℝ) * x) :=
    MaskedPrimeCutoffLoss X Y hX hY A hA (n : ℝ)
  calc
    _ ≤ _ := hcut
    _ ≤ K * Real.log x * x ^ (1 - δ / 2) :=
      mul_le_mul_of_nonneg_left hSqrt (mul_nonneg hK.le hLogNonneg)
    _ ≤ K * (ε / K * x ^ (δ / 2)) * x ^ (1 - δ / 2) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hLog hK.le) (Real.rpow_nonneg hx.le _)
    _ = ε * (x ^ (δ / 2) * x ^ (1 - δ / 2)) := by field_simp [hK.ne']
    _ = _ := by
      rw [← Real.rpow_add hx, show (δ / 2 + (1 - δ / 2) : ℝ) = 1 by ring, Real.rpow_one]

private theorem minorRational {P X : ℕ} {t : ℝ} (hP : 1 ≤ P) (hPX : P ≤ X)
    (ht : t ∉ rationalArcs X P) :
    ∃ (q : ℕ) (a : ℤ), P < q ∧ q ≤ X / P ∧ IsCoprime a (q : ℤ) ∧
      |t - (a : ℝ) / q| ≤ 1 / (q : ℝ)^2 := by
  let B := X / P
  obtain ⟨s, hclose, hden⟩ := Real.exists_rat_abs_sub_le_and_den_le t (Nat.div_pos hPX hP :
    0 < B)
  have hcop : IsCoprime s.num (s.den : ℤ) := Int.isCoprime_iff_nat_coprime.mpr s.reduced
  have hd : 0 < (s.den : ℝ) := Nat.cast_pos.mpr s.pos
  have hXPos : 0 < (X : ℝ) := Nat.cast_pos.mpr (hP.trans hPX)
  rw [Rat.cast_def, mul_comm ((B : ℝ) + 1) (s.den : ℝ)] at hclose
  have hlarge : P < s.den := by
    by_contra! h
    apply ht
    refine ⟨s.den, s.num, s.pos, Nat.cast_le.mpr h, hcop, hclose.trans ?_⟩
    have hbound : (X : ℝ) < (P : ℝ) * ((B : ℝ) + 1) := by
      exact_mod_cast Nat.lt_mul_div_succ X hP
    apply (div_le_div_iff₀ (by positivity) (mul_pos hd hXPos)).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hbound.le hd.le]
  refine ⟨s.den, s.num, hlarge, hden, hcop, hclose.trans ?_⟩
  apply one_div_le_one_div_of_le (by positivity)
  rw [sq]
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.le_succ_of_le hden) hd.le

private def mangoldtSum (X : ℕ) (t : ℝ) : ℂ :=
  ∑ p ∈ Finset.range (X + 1), (ArithmeticFunction.vonMangoldt p : ℂ) * phase ((p : ℝ) * t)

private theorem mangoldtSum_sub_primeSum (X : ℕ) (hX : 1 ≤ X) (t : ℝ) :
    ‖mangoldtSum X t - primeSum X t‖ ≤ 2 * Real.sqrt X * Real.log X := by
  have hnon (p : ℕ) : 0 ≤ ArithmeticFunction.vonMangoldt p - primeWeight p := by
    by_cases hp : p.Prime <;> simp [primeWeight, hp, ArithmeticFunction.vonMangoldt_apply_prime]
  unfold mangoldtSum primeSum
  rw [← Finset.sum_sub_distrib]
  simp_rw [← sub_mul, ← Complex.ofReal_sub]
  calc
    _ ≤ ∑ p ∈ Finset.range (X + 1),
        ‖((ArithmeticFunction.vonMangoldt p - primeWeight p : ℝ) : ℂ) *
          phase ((p : ℝ) * t)‖ := norm_sum_le _ _
    _ = ∑ p ∈ Finset.range (X + 1), (ArithmeticFunction.vonMangoldt p - primeWeight p) := by
      simp only [norm_mul, phase, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (hnon _)]
    _ = Chebyshev.psi X - Chebyshev.theta X := by
      rw [Nat.range_succ_eq_Icc_zero, ← Finset.add_sum_Ioc_eq_sum_Icc (Nat.zero_le X)]
      simp [Chebyshev.psi, Chebyshev.theta, primeWeight, Finset.sum_filter, Finset.sum_sub_distrib]
    _ ≤ _ := Chebyshev.psi_sub_theta_le (by exact_mod_cast hX)

/-- The ordinary Vaughan estimate at the denominator cutoff `X^(11/40)`.
This cutoff is below the `X^0.28` parameter in Pintz's proof. -/
private theorem minorSup :
    ∃ N : ℕ, ∀ X : ℕ, N ≤ X → ∀ t : ℝ, t ∉ baseArcs X →
      ‖primeSum X t‖ ≤ (X : ℝ) ^ (69/80 + 1/160 : ℝ) := by
  have ht : Tendsto (fun X : ℕ => (X : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hsmall := ((isLittleO_log_rpow_rpow_atTop (4 : ℝ)
    (by norm_num : (0 : ℝ) < 1/160)).comp_tendsto ht).bound (by norm_num : (0 : ℝ) < 1/100000)
  have hcut := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 11/40)).comp ht
  have hlog := Real.tendsto_log_atTop.comp ht
  apply Filter.eventually_atTop.mp
  filter_upwards [eventually_ge_atTop (2 : ℕ), hsmall, hcut.eventually_ge_atTop 2,
    hlog.eventually_ge_atTop 1, OAI.Problem337.Vaughan.eventually_vonMangoldt_sum_log_bound]
    with X hX hlogs hcut' hL hVaughan
  intro t htA
  let x : ℝ := X
  let L := Real.log x
  let P := cutoff X
  have hx : 0 < x := Nat.cast_pos.mpr (by omega)
  have hx₁ : 1 ≤ x := by dsimp [x]; exact_mod_cast (show 1 ≤ X by omega)
  change 1 ≤ L at hL
  change 2 ≤ x ^ (11/40 : ℝ) at hcut'
  have hP : 1 ≤ P := (Nat.le_floor_iff (Real.rpow_nonneg hx.le _)).mpr (by push_cast; linarith)
  have hPX : P ≤ X := Nat.floor_le_of_le <|
    (Real.rpow_le_rpow_of_exponent_le hx₁ (by norm_num : (11/40 : ℝ) ≤ 1)).trans_eq
      (Real.rpow_one x)
  obtain ⟨q, a, hqLow, hqHigh, hcop, hclose⟩ := minorRational hP hPX htA
  have hq : 0 < q := by omega
  have hPPos : 0 < (P : ℝ) := Nat.cast_pos.mpr hP
  have hqPos : 0 < (q : ℝ) := Nat.cast_pos.mpr hq
  have hqX : q ≤ X := hqHigh.trans (Nat.div_le_self _ _)
  have hqHigh' : (q : ℝ) ≤ x / P := (le_div_iff₀ hPPos).mpr (by
    dsimp [x]
    exact_mod_cast (Nat.le_div_iff_mul_le hP).mp hqHigh)
  let T := x ^ (11/80 : ℝ) / 2
  have hT : 0 < T := by dsimp [T]; positivity
  have hTsq : (x ^ (11/80 : ℝ))^2 = x ^ (11/40 : ℝ) := by
    rw [← Real.rpow_mul_natCast hx.le]
    congr 1
    norm_num
  have hTP : T ≤ Real.sqrt P := by
    apply (Real.le_sqrt hT.le hPPos.le).mpr
    have hfloor : x ^ (11/40 : ℝ) < (P : ℝ) + 1 := Nat.lt_floor_add_one _
    dsimp [T]
    nlinarith only [hcut', hfloor, hTsq]
  have hleft : x / Real.sqrt q ≤ x / T :=
    div_le_div_of_nonneg_left hx.le hT
      (hTP.trans (Real.sqrt_le_sqrt (Nat.cast_le.mpr hqLow.le)))
  have hright : Real.sqrt (x * q) ≤ x / T := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    rw [div_pow, le_div_iff₀ (sq_pos_of_pos hT)]
    have hT2 := (Real.le_sqrt hT.le hPPos.le).mp hTP
    nlinarith only [mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hT2 hqPos.le) hx.le,
      mul_le_mul_of_nonneg_left ((le_div_iff₀ hPPos).mp hqHigh') hx.le]
  have hscale : x / T = 2 * x ^ (69/80 : ℝ) := by
    have hpow : x ^ (69/80 : ℝ) * x ^ (11/80 : ℝ) = x := by
      rw [← Real.rpow_add hx]
      norm_num
    dsimp [T]
    field_simp [(Real.rpow_pos_of_pos hx (11/80 : ℝ)).ne']
    nlinarith only [hpow]
  rw [hscale] at hleft hright
  have hmangoldt : ‖mangoldtSum X t‖ ≤ 81000 * L^4 * x ^ (69/80 : ℝ) := by
    have hsum : mangoldtSum X t = OAI.Problem337.Vaughan.weightedSum
        (Finset.Ioc 0 X) (fun p => OAI.Problem337.VaughanBilinear.phase (t * p))
        ArithmeticFunction.vonMangoldt := by
      dsimp [mangoldtSum, phase, OAI.Problem337.Vaughan.weightedSum,
        OAI.Problem337.VaughanBilinear.phase]
      rw [Nat.range_succ_eq_Icc_zero, ← Finset.add_sum_Ioc_eq_sum_Icc (Nat.zero_le X)]
      simp only [ArithmeticFunction.map_zero, Complex.ofReal_zero, zero_mul, zero_add,
        Real.fourierChar_apply]
      apply Finset.sum_congr rfl
      intro p _
      rw [mul_comm t (p : ℝ)]
    rw [hsum]
    apply (hVaughan t a q hq hcop hclose hqX).trans
    change 16200*L^4*(x/Real.sqrt q + x^(4/5 : ℝ) + Real.sqrt (x*q)) ≤ _
    have hmiddle := Real.rpow_le_rpow_of_exponent_le hx₁ (by norm_num : (4/5 : ℝ) ≤ 69/80)
    calc
      _ ≤ 16200 * L^4 * (5 * x ^ (69/80 : ℝ)) := by gcongr; linarith only [hleft, hmiddle, hright]
      _ = _ := by ring
  have herror := mangoldtSum_sub_primeSum X (by omega) t
  change ‖mangoldtSum X t - primeSum X t‖ ≤ 2 * Real.sqrt x * L at herror
  have hsqrt : Real.sqrt x ≤ x ^ (69/80 : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hx₁ (by norm_num)
  have hlogLe : L ≤ L^4 := by
    simpa only [pow_one] using pow_le_pow_right₀ hL (by decide : 1 ≤ 4)
  have herror' : 2 * Real.sqrt x * L ≤ 2 * L^4 * x ^ (69/80 : ℝ) := calc
    _ = 2 * (L * Real.sqrt x) := by ring
    _ ≤ 2 * (L^4 * x ^ (69/80 : ℝ)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul hlogLe hsqrt (Real.sqrt_nonneg _) (by positivity))
        (by norm_num)
    _ = _ := by ring
  have htriangle := norm_sub_le (mangoldtSum X t) (mangoldtSum X t - primeSum X t)
  rw [sub_sub_cancel] at htriangle
  have hlogs' : L^4 ≤ (1/100000 : ℝ) * x ^ (1/160 : ℝ) := by
    change ‖L^(4 : ℝ)‖ ≤ (1/100000 : ℝ) * ‖x ^ (1/160 : ℝ)‖ at hlogs
    simpa only [Real.rpow_ofNat, Real.norm_of_nonneg (show 0 ≤ L^4 by positivity),
      Real.norm_of_nonneg (Real.rpow_nonneg hx.le _)] using hlogs
  change ‖primeSum X t‖ ≤ x^(69/80 + 1/160 : ℝ)
  rw [Real.rpow_add hx]
  have hsave := mul_le_mul_of_nonneg_right hlogs' (Real.rpow_nonneg hx.le (69/80 : ℝ))
  nlinarith only [htriangle, herror, herror', hmangoldt, hsave,
    mul_nonneg (show 0 ≤ L^4 by positivity) (Real.rpow_nonneg hx.le (69/80 : ℝ))]

/-- A fixed truncation and a fixed measurable arc set give a moment over
all target frequencies up to the truncation. -/
private theorem minorMoment :
    ∃ N : ℕ, ∀ X : ℕ, N ≤ X → ∀ A : Set ℝ, MeasurableSet A → baseArcs X ⊆ A →
      (∑ n ∈ Finset.range (X + 1), ‖arcCoefficient X n Aᶜ‖^2) ≤ (X : ℝ) ^ (11/4 : ℝ) := by
  obtain ⟨N, hN⟩ := minorSup
  have hlogEventually := ((isLittleO_log_rpow_rpow_atTop (2 : ℝ)
    (by norm_num : (0 : ℝ) < 1/80)).comp_tendsto tendsto_natCast_atTop_atTop).bound
      (by norm_num : (0 : ℝ) < 1/2)
  apply Filter.eventually_atTop.mp
  filter_upwards [eventually_ge_atTop N, eventually_ge_atTop (2 : ℕ), hlogEventually]
    with X hX hX₂ hlog
  intro A hA hWide
  have hXPos : 0 < (X : ℝ) := by exact_mod_cast (show 0 < X by omega)
  have hXOne : 1 ≤ (X : ℝ) := by exact_mod_cast (show 1 ≤ X by omega)
  have hlogSq : (Real.log (X : ℝ))^2 ≤ (1/2 : ℝ) * (X : ℝ) ^ (1/80 : ℝ) := by
    change ‖Real.log (X : ℝ) ^ (2 : ℝ)‖ ≤ (1/2 : ℝ) * ‖(X : ℝ) ^ (1/80 : ℝ)‖ at hlog
    simpa only [Real.rpow_ofNat, Real.norm_of_nonneg (sq_nonneg (Real.log (X : ℝ))),
      Real.norm_of_nonneg (Real.rpow_nonneg hXPos.le _)] using hlog
  let U := (X : ℝ) ^ (69/80 + 1/160 : ℝ)
  have hsup (t : ℝ) (_ : t ∈ Set.Icc (0 : ℝ) 1) (htA : t ∉ A) : ‖primeSum X t‖ ≤ U :=
    hN X hX t (fun h => htA (hWide h))
  have hBessel := PEqualNP.Outside.frontierSourceBesselCap X (X + 1) primeWeight A U hA
    (Real.rpow_nonneg hXPos.le _) hsup
  have hweights : (∑ p ∈ Finset.range (X + 1), (primeWeight p)^2) ≤
      (X : ℝ) * (X : ℝ) ^ (1/80 : ℝ) := calc
    _ ≤ ∑ _p ∈ Finset.range (X + 1), (Real.log (X : ℝ))^2 := by
      apply Finset.sum_le_sum
      intro p hp
      by_cases hprime : p.Prime
      · simp only [primeWeight, hprime, ite_true]
        exact pow_le_pow_left₀ (Real.log_natCast_nonneg p)
          (Real.log_le_log (Nat.cast_pos.mpr hprime.pos)
            (Nat.cast_le.mpr (Nat.le_of_lt_succ (Finset.mem_range.mp hp)))) 2
      · simpa [primeWeight, hprime] using sq_nonneg (Real.log (X : ℝ))
    _ = ((X : ℝ) + 1) * (Real.log (X : ℝ))^2 := by simp
    _ ≤ (2 * (X : ℝ)) * ((1/2 : ℝ) * (X : ℝ) ^ (1/80 : ℝ)) :=
      mul_le_mul (by linarith) hlogSq (sq_nonneg _) (by positivity)
    _ = _ := by ring
  calc
    _ ≤ U^2 * ∑ p ∈ Finset.range (X + 1), (primeWeight p)^2 := hBessel
    _ ≤ U^2 * ((X : ℝ) * (X : ℝ) ^ (1/80 : ℝ)) :=
      mul_le_mul_of_nonneg_left hweights (sq_nonneg _)
    _ = _ := by
      have hU : U^2 = (X : ℝ) ^ (139/80 : ℝ) := by
        dsimp [U]
        rw [← Real.rpow_mul_natCast hXPos.le]
        congr 1
        norm_num
      have hW : (X : ℝ) * (X : ℝ) ^ (1/80 : ℝ) = (X : ℝ) ^ (81/80 : ℝ) := by
        rw [show (81/80 : ℝ) = 1 + 1/80 by norm_num, Real.rpow_add hXPos, Real.rpow_one]
      rw [hU, hW, ← Real.rpow_add hXPos]
      congr 1
      norm_num

private theorem zeroCoefficient {X n : ℕ} (he : GoldbachDensityTransfer.exceptional n) :
    intervalIntegral (integrand X n) (0 : ℝ) 1 volume = 0 := by
  apply EstermannAlmostAllPolylog_aux.WindowBessel.ExceptionalCoefficients.zero_from_pairs
  intro p q hpq
  by_cases hp : p.Prime
  · by_cases hq : q.Prime
    · have hmem : p ∈ (Finset.range (n + 1)).filter
          (fun k => k.Prime ∧ (n - k).Prime) :=
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hp, by
          rwa [show n - p = q by omega]⟩
      have hpos : 0 < representationCount n := Finset.card_pos.mpr ⟨p, hmem⟩
      exact (hpos.ne' he.2.2).elim
    · simp [primeWeight, hq]
  · simp [primeWeight, hp]

private theorem minor_large_of_exception {X n : ℕ} {A : Set ℝ} {b : ℝ}
    (hA : MeasurableSet A) (he : GoldbachDensityTransfer.exceptional n)
    (hmain : b ≤ (arcCoefficient X n A).re) :
    b ≤ ‖arcCoefficient X n Aᶜ‖ := by
  have hcont : Continuous (integrand X n) := by
    unfold integrand primeSum phase
    fun_prop
  have hsum := EstermannAlmostAllPolylog_aux.WindowBessel.ExceptionalCoefficients.indicator_integral_split
    hA (hcont.intervalIntegrable 0 1)
  change arcCoefficient X n A + arcCoefficient X n Aᶜ =
    intervalIntegral (integrand X n) (0 : ℝ) 1 volume at hsum
  rw [zeroCoefficient he] at hsum
  have hneg : arcCoefficient X n Aᶜ = -arcCoefficient X n A := by linear_combination hsum
  rw [hneg, norm_neg]
  exact hmain.trans (Complex.re_le_norm _)

private theorem largeCoefficient_card_le {X : ℕ} {f : ℕ → ℂ} {c M : ℝ}
    (hX : 0 < (X : ℝ)) (hc : 0 < c) (B : Finset ℕ)
    (hB : B ⊆ Finset.range (X + 1))
    (hlarge : ∀ n ∈ B, c * (X : ℝ) ≤ ‖f n‖)
    (hmoment : (∑ n ∈ Finset.range (X + 1), ‖f n‖^2) ≤ M * (X : ℝ) ^ (11/4 : ℝ)) :
    (B.card : ℝ) ≤ (M / c^2) * (X : ℝ) ^ (3/4 : ℝ) := by
  apply le_of_mul_le_mul_right _ (show 0 < (c * (X : ℝ))^2 by positivity)
  calc
    _ = ∑ _n ∈ B, (c * (X : ℝ))^2 := by simp
    _ ≤ ∑ n ∈ B, ‖f n‖^2 :=
      Finset.sum_le_sum fun n hn => pow_le_pow_left₀ (by positivity) (hlarge n hn) 2
    _ ≤ ∑ n ∈ Finset.range (X + 1), ‖f n‖^2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hB fun _ _ _ => sq_nonneg _
    _ ≤ M * (X : ℝ) ^ (11/4 : ℝ) := hmoment
    _ = _ := by
      rw [show (11/4 : ℝ) = 2 + 3/4 by norm_num, Real.rpow_add hX, Real.rpow_two]
      field_simp [hc.ne']

private def conductorMultiples (X K q : ℕ) : Finset ℕ :=
  (Finset.range (X + 1)).filter fun n => q ∣ K * n

private def largeConductorLcms (X : ℕ) (R : Finset ℕ) : Finset ℕ := by
  classical
  exact (R.powerset.image fun T => T.lcm id).filter fun q => (X : ℝ) ^ (1/4 : ℝ) ≤ (q : ℝ)

private def conductorOutliers (X K : ℕ) (R : Finset ℕ) : Finset ℕ :=
  (largeConductorLcms X R).biUnion (conductorMultiples X K)

private theorem conductorMultiples_card_le {X K q : ℕ} (hX : 1 ≤ X) (hK : 0 < K)
    (hq : (X : ℝ) ^ (1/4 : ℝ) ≤ (q : ℝ)) :
    ((conductorMultiples X K q).card : ℝ) ≤ ((K : ℝ) + 1) * (X : ℝ) ^ (3/4 : ℝ) := by
  have hCard : (conductorMultiples X K q).card ≤ K * X / q + 1 := by
    rw [← Finset.card_range (K * X / q + 1)]
    refine Finset.card_le_card_of_injOn (fun n : ℕ => K * n / q) ?_ ?_
    · intro n hn
      have hnRange := (Finset.mem_filter.mp (Finset.mem_coe.mp hn)).1
      have hnLe : n ≤ X := Nat.le_of_lt_succ (Finset.mem_range.mp hnRange)
      exact Finset.mem_coe.mpr (Finset.mem_range.mpr (Nat.lt_succ_of_le
        (Nat.div_le_div_right (Nat.mul_le_mul_left K hnLe))))
    · intro m hm n hn he
      have hmDvd := (Finset.mem_filter.mp (Finset.mem_coe.mp hm)).2
      have hnDvd := (Finset.mem_filter.mp (Finset.mem_coe.mp hn)).2
      change K * m / q = K * n / q at he
      apply Nat.eq_of_mul_eq_mul_left hK
      calc
        K * m = (K * m / q) * q := (Nat.div_mul_cancel hmDvd).symm
        _ = (K * n / q) * q := by rw [he]
        _ = K * n := Nat.div_mul_cancel hnDvd
  have hX₁ : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hXPos : 0 < (X : ℝ) := zero_lt_one.trans_le hX₁
  have hquarter : 0 < (X : ℝ) ^ (1/4 : ℝ) := Real.rpow_pos_of_pos hXPos _
  have hqPos : 0 < (q : ℝ) := hquarter.trans_le hq
  have hdiv : ((K * X / q : ℕ) : ℝ) ≤ (K : ℝ) * (X : ℝ) / (q : ℝ) :=
    (le_div_iff₀ hqPos).mpr (by exact_mod_cast Nat.div_mul_le_self (K * X) q)
  have hquot : (K : ℝ) * (X : ℝ) / (q : ℝ) ≤ (K : ℝ) * (X : ℝ) ^ (3/4 : ℝ) := by
    refine (div_le_div_of_nonneg_left (by positivity) hquarter hq).trans_eq ?_
    apply (div_eq_iff hquarter.ne').mpr
    rw [mul_assoc, ← Real.rpow_add hXPos]
    norm_num
  calc
    _ ≤ ((K * X / q : ℕ) : ℝ) + 1 := by exact_mod_cast hCard
    _ ≤ (K : ℝ) * (X : ℝ) / (q : ℝ) + 1 := add_le_add hdiv le_rfl
    _ ≤ (K : ℝ) * (X : ℝ) ^ (3/4 : ℝ) + (X : ℝ) ^ (3/4 : ℝ) :=
      add_le_add hquot (Real.one_le_rpow hX₁ (by norm_num))
    _ = _ := by ring

/-- The large-lcm classes in Section 2 of Pintz's proof fit the exceptional
budget when the number of conductors and the multiplier are bounded. -/
private theorem conductorOutliers_card_le (X K : ℕ) (R : Finset ℕ) (hX : 1 ≤ X) (hK : 0 < K) :
    ((conductorOutliers X K R).card : ℝ) ≤
      (2 : ℝ)^R.card * ((K : ℝ) + 1) * (X : ℝ) ^ (3/4 : ℝ) := by
  classical
  let Q := largeConductorLcms X R
  have hQ : Q.card ≤ 2^R.card := by
    unfold Q largeConductorLcms
    exact (Finset.card_filter_le _ _).trans
      (Finset.card_image_le.trans_eq (Finset.card_powerset R))
  calc
    _ ≤ ∑ q ∈ Q, ((conductorMultiples X K q).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le (s := Q) (t := conductorMultiples X K)
    _ ≤ ∑ _q ∈ Q, ((K : ℝ) + 1) * (X : ℝ) ^ (3/4 : ℝ) := by
      apply Finset.sum_le_sum
      intro q hq
      exact conductorMultiples_card_le hX hK (Finset.mem_filter.mp hq).2
    _ = (Q.card : ℝ) * (((K : ℝ) + 1) * (X : ℝ) ^ (3/4 : ℝ)) := by simp
    _ ≤ (2 : ℝ)^R.card * (((K : ℝ) + 1) * (X : ℝ) ^ (3/4 : ℝ)) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hQ) (by positivity)
    _ = _ := by ring

private theorem small_lcm_of_not_mem_conductorOutliers {X K n : ℕ} {R : Finset ℕ}
    (hn : n ≤ X) (hOutlier : n ∉ conductorOutliers X K R) :
    ((((R.filter fun r => r ∣ K * n).lcm id) : ℕ) : ℝ) < (X : ℝ) ^ (1/4 : ℝ) := by
  classical
  let T := R.filter fun r => r ∣ K * n
  let q := T.lcm id
  change (q : ℝ) < (X : ℝ) ^ (1/4 : ℝ)
  by_contra! hq
  apply hOutlier
  have hT : T ∈ R.powerset := Finset.mem_powerset.mpr (Finset.filter_subset _ _)
  have hqMem : q ∈ largeConductorLcms X R :=
    Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ hT, hq⟩
  have hDvd : q ∣ K * n := Finset.lcm_dvd (fun r hr => (Finset.mem_filter.mp hr).2)
  exact Finset.mem_biUnion.mpr ⟨q, hqMem,
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hn), hDvd⟩⟩

end

end BinaryShiftCircle

namespace BinaryShiftMajorModel

open AddCircle MeasureTheory Filter GoldbachDensityCircle EstermannAlmostAllPolylog_aux
open scoped Topology

noncomputable section

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

private def circleArcs (X : ℕ) (P : ℝ) : Set (AddCircle (1 : ℝ)) :=
  {x | ∃ i ∈ majorArcIndices ⌊P⌋₊, |arcCoordinate i x| ≤ arcWidth X P i.1}

private def realArcs (X : ℕ) (P : ℝ) : Set ℝ :=
  (fun t : ℝ => (t : AddCircle (1 : ℝ))) ⁻¹' circleArcs X P

private theorem measurable_circleArcs (X : ℕ) (P : ℝ) : MeasurableSet (circleArcs X P) := by
  simp only [circleArcs, Set.ofPred_exists]
  apply MeasurableSet.iUnion
  intro i
  by_cases hi : i ∈ majorArcIndices ⌊P⌋₊
  · simpa only [hi, true_and] using
      measurableSet_le (measurable_arcCoordinate i).abs
        (measurable_const (a := arcWidth X P i.1))
  · simp [hi]

private theorem measurable_realArcs (X : ℕ) (P : ℝ) : MeasurableSet (realArcs X P) :=
  (measurable_circleArcs X P).preimage AddCircle.measurable_mk'

private theorem rationalArcs_subset_realArcs {X : ℕ} {P : ℝ} (hX : 0 < (X : ℝ))
    (hRadius : P / (X : ℝ) < 1 / 2) : BinaryShiftCircle.rationalArcs X P ⊆ realArcs X P := by
  intro t ht
  obtain ⟨q, a, hq, hqP, hcoprime, hclose⟩ := ht
  have hqZ : 0 < (q : ℤ) := by exact_mod_cast hq
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hP : 0 ≤ P := hqR.le.trans hqP
  let b : ℕ := (a % (q : ℤ)).toNat
  let j : ℤ := a / (q : ℤ)
  have hbZ : (b : ℤ) = a % (q : ℤ) := Int.toNat_of_nonneg (Int.emod_nonneg _ hqZ.ne')
  have hb : b < q := by
    have h := Int.emod_lt_of_pos a hqZ
    rw [← hbZ] at h
    exact_mod_cast h
  have hab : (b : ℤ) + j * (q : ℤ) = a := by
    rw [hbZ]
    exact Int.emod_add_ediv_mul _ _
  have hbCoprime : b.Coprime q := by
    have h : IsCoprime (b : ℤ) (q : ℤ) := by
      obtain ⟨u, v, h⟩ := hcoprime
      refine ⟨u, v + u * j, ?_⟩
      calc
        _ = u * ((b : ℤ) + j * (q : ℤ)) + v * (q : ℤ) := by ring
        _ = 1 := by rw [hab, h]
    simpa using Int.isCoprime_iff_nat_coprime.mp h
  let i : ℕ × ℕ := (q, b)
  refine ⟨i, mem_majorArcIndices.mpr ⟨hq, (Nat.le_floor_iff hP).mpr hqP, hb, hbCoprime⟩, ?_⟩
  let β : ℝ := t - (a : ℝ) / q
  have hWidth : P / ((q : ℝ) * X) ≤ P / (X : ℝ) :=
    div_le_div_of_nonneg_left hP hX (le_mul_of_one_le_left hX.le (by exact_mod_cast hq))
  have hBetaRadius : |β| < 1 / 2 := hclose.trans_lt (hWidth.trans_lt hRadius)
  have hBeta : β ∈ Set.Ioc (-1 / 2 : ℝ) (-1 / 2 + 1) := by
    obtain ⟨hl, hr⟩ := abs_lt.mp hBetaRadius
    exact ⟨by linarith, by linarith⟩
  have hCenter : (a : ℝ) / q = arcCenter i + (j : ℝ) := by
    have hz : (b : ℝ) + (j : ℝ) * (q : ℝ) = (a : ℝ) := by exact_mod_cast hab
    apply (div_eq_iff hqR.ne').mpr
    dsimp [arcCenter, i]
    rw [add_mul, div_mul_cancel₀ _ hqR.ne', hz]
  have hJ : ((j : ℝ) : AddCircle (1 : ℝ)) = 0 := by
    rw [AddCircle.coe_eq_zero_iff]
    exact ⟨j, by simp [zsmul_eq_mul]⟩
  have hCircle : (β : AddCircle (1 : ℝ)) =
      (t : AddCircle (1 : ℝ)) - (arcCenter i : AddCircle (1 : ℝ)) := by
    change ((t - (a : ℝ) / q : ℝ) : AddCircle (1 : ℝ)) = _
    rw [hCenter]
    simp only [AddCircle.coe_sub, AddCircle.coe_add, hJ, add_zero]
  change |arcCoordinate i (t : AddCircle (1 : ℝ))| ≤ arcWidth X P q
  rw [arcCoordinate, ← hCircle, equivIoc_coe_of_mem hBeta]
  exact hclose

private def circlePrimeSum (X : ℕ) (t : AddCircle (1 : ℝ)) : ℂ :=
  ∑ k ∈ Finset.range (X + 1), (BinaryShiftCircle.primeWeight k : ℂ) * fourier (k : ℤ) t

private theorem fourier_coe_eq_phase (k : ℤ) (t : ℝ) :
    fourier k (t : AddCircle (1 : ℝ)) = BinaryShiftCircle.phase ((k : ℝ) * t) := by
  simp only [fourier_coe_apply, BinaryShiftCircle.phase, Complex.ofReal_one, div_one]
  congr 1
  push_cast
  ring

private theorem circlePrimeSum_coe (X : ℕ) (t : ℝ) :
    circlePrimeSum X (t : AddCircle (1 : ℝ)) = BinaryShiftCircle.primeSum X t := by
  unfold circlePrimeSum BinaryShiftCircle.primeSum
  apply Finset.sum_congr rfl
  intro k _
  simp only [fourier_coe_eq_phase, Int.cast_natCast]

private def primeMajorPart (X : ℕ) (P : ℝ) : AddCircle (1 : ℝ) → ℂ :=
  (circleArcs X P).indicator (circlePrimeSum X)

private theorem primeMajorPart_coeff (X n : ℕ) (P : ℝ) :
    fourierCoeff (fun t => (primeMajorPart X P t)^2) (n : ℤ) =
      BinaryShiftCircle.arcCoefficient X n (realArcs X P) := by
  rw [fourierCoeff_eq_intervalIntegral _ _ 0]
  simp only [zero_add, div_one, one_smul]
  apply intervalIntegral.integral_congr
  intro t _
  have hphase : fourier (-(n : ℤ)) (t : AddCircle (1 : ℝ)) =
      BinaryShiftCircle.phase (-(n : ℝ) * t) := by
    simp only [fourier_coe_eq_phase, Int.cast_neg, Int.cast_natCast]
  change fourier (-(n : ℤ)) (t : AddCircle (1 : ℝ)) •
      (primeMajorPart X P (t : AddCircle (1 : ℝ))) ^ 2 =
        (realArcs X P).indicator (BinaryShiftCircle.integrand X n) t
  rw [hphase, smul_eq_mul, mul_comm]
  by_cases h : (t : AddCircle (1 : ℝ)) ∈ circleArcs X P
  · have ht : t ∈ realArcs X P := h
    simp [primeMajorPart, h, ht, circlePrimeSum_coe, BinaryShiftCircle.integrand]
  · have ht : t ∉ realArcs X P := h
    simp [primeMajorPart, h, ht]

/-- Group all blocks of the primitive inducing character by their common zero. -/
private def characterCorrection (X : ℕ) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (β : ℝ) : ℂ :=
  letI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  let m := X - 2
  let γ := 2 * Real.pi * β
  ∑ z ∈ GoldbachTwistedMellin.exceptionalZeros χ.primitiveCharacter
      (GoldbachTwistedMellin.modelHeight (m + 2 : ℕ)),
    (analyticOrderNatAt (Goldbach.regularizedL χ.primitiveCharacter) z : ℂ) *
      GoldbachTwistedMellin.zeroPowerProfile m γ z

private theorem characterCorrection_eq_blocks (X : ℕ) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (β : ℝ) :
    letI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    characterCorrection X χ β =
      ((GoldbachTwistedMellin.prefixBlocks (X - 2)).map fun p =>
        GoldbachTwistedMellin.fixedZeroTerm χ.primitiveCharacter p.1 p.2 p.1 (2 * Real.pi * β)).sum := by
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  exact (GoldbachTwistedMellin.prefix_fixedZeroTerm_eq_zeroWindows χ.primitiveCharacter _ _).symm

private theorem continuous_characterCorrection (X : ℕ) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) : Continuous (characterCorrection X χ) := by
  classical
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  let g := fun (p : ℕ × ℕ) (β : ℝ) =>
    GoldbachTwistedMellin.fixedZeroTerm χ.primitiveCharacter p.1 p.2 p.1 (2 * Real.pi * β)
  have hlist (l : List (ℕ × ℕ)) (hl : ∀ p ∈ l, Continuous (g p)) :
      Continuous (fun β => (l.map fun p => g p β).sum) := by
    induction l with
    | nil => exact continuous_const
    | cons p l ih =>
      exact (hl p (List.mem_cons_self ..)).add (ih (fun r hr => hl r (List.mem_cons_of_mem p hr)))
  rw [show characterCorrection X χ = fun β =>
      ((GoldbachTwistedMellin.prefixBlocks (X-2)).map fun p => g p β).sum from
    funext (characterCorrection_eq_blocks X χ)]
  apply hlist
  intro p hp
  unfold g
  obtain ⟨hl, hlr, _, _⟩ := GoldbachTwistedMellin.prefixBlocks_valid hp
  unfold GoldbachTwistedMellin.fixedZeroTerm
  exact continuous_finsetSum _ fun z _ => continuous_const.mul
    ((GoldbachTwistedMellin.continuous_transform_frequency (by exact_mod_cast hl) (by exact_mod_cast hlr) z).comp (by fun_prop))

private theorem canonicalCorrection_eq_sum (X q a : ℕ) [NeZero q] (β : ℝ) :
    GoldbachTwistedMellin.canonicalCorrection X (a : ZMod q) β =
      ∑ χ : DirichletCharacter ℂ q,
        GoldbachTwistedMellin.additiveWeight (a : ZMod q) χ * characterCorrection X χ β := by
  let w := GoldbachTwistedMellin.additiveWeight (a : ZMod q)
  let g := fun (p : ℕ × ℕ) (χ : DirichletCharacter ℂ q) =>
    GoldbachTwistedMellin.fixedZeroTerm χ p.1 p.2 p.1 (2 * Real.pi * β)
  have sum_comm (l : List (ℕ × ℕ)) :
      (l.map (fun p => ∑ χ, w χ * g p χ)).sum =
        ∑ χ, w χ * (l.map fun p => g p χ).sum := by
    induction l with
    | nil => simp
    | cons p l ih =>
      simp only [List.map_cons, List.sum_cons, ih, mul_add, Finset.sum_add_distrib]
  calc
    _ = ∑ χ : DirichletCharacter ℂ q,
        w χ * ((GoldbachTwistedMellin.prefixBlocks (X - 2)).map fun p => g p χ).sum := sum_comm _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro χ _
      apply congrArg (fun z : ℂ => w χ * z)
      rw [characterCorrection_eq_blocks]
      apply congrArg List.sum
      apply List.map_congr_left
      intro p _
      exact GoldbachTwistedMellin.fixedZeroTerm_eq_primitive χ p.1 p.2 p.1 (2 * Real.pi * β)

private theorem continuous_canonicalCorrection (X q a : ℕ) [NeZero q] :
    Continuous (GoldbachTwistedMellin.canonicalCorrection X (a : ZMod q)) := by
  simp_rw [show GoldbachTwistedMellin.canonicalCorrection X (a : ZMod q) =
      fun β => ∑ χ, GoldbachTwistedMellin.additiveWeight (a : ZMod q) χ * characterCorrection X χ β
    from funext (canonicalCorrection_eq_sum X q a)]
  exact continuous_finsetSum _ fun χ _ => continuous_const.mul (continuous_characterCorrection X χ)

private theorem continuous_positiveGeometricSum (X : ℕ) :
    Continuous (DeepThreeQuarters.positiveGeometricSum X) := by
  unfold DeepThreeQuarters.positiveGeometricSum
  exact continuous_finsetSum _ fun _ _ => by
    unfold DeepThreeQuarters.geometricPhase
    fun_prop

private def characterProfile (X : ℕ) {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (β : ℝ) : ℂ := by
  classical
  exact (if χ = 1 then DeepThreeQuarters.positiveGeometricSum X β else 0) - characterCorrection X χ β

private theorem continuous_characterProfile (X : ℕ) {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    Continuous (characterProfile X χ) := by
  have h := continuous_characterCorrection X χ
  by_cases he : χ = 1
  · exact ((continuous_positiveGeometricSum X).sub h).congr (fun β => by simp [characterProfile, he])
  · exact (continuous_const.sub h : Continuous (fun β => 0 - characterCorrection X χ β)).congr
      (fun β => by simp [characterProfile, he])

/-- Residues in the finite explicit formula of a single inducing character.
The symbol `none` carries the pole, with weight zero for nonprincipal characters. -/
private def characterResidues (m : ℕ) {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) : Finset (Option ℂ) := by
  classical
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  exact insert none ((GoldbachTwistedMellin.exceptionalZeros χ.primitiveCharacter
    (GoldbachTwistedMellin.modelHeight (m+2 : ℕ))).image some)

private def residueMultiplier {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (z : Option ℂ) : ℂ := by
  classical
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  exact match z with
    | none => if χ = 1 then 1 else 0
    | some ρ => -(analyticOrderNatAt (Goldbach.regularizedL χ.primitiveCharacter) ρ : ℂ)

private theorem characterProfile_eq_residues (m : ℕ) {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (u : ℝ) :
    characterProfile (m+2) χ u = ∑ z ∈ characterResidues m χ,
      residueMultiplier χ z * GoldbachTwistedMellin.residueProfile m z u := by
  classical
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  unfold characterResidues
  rw [Finset.sum_insert (by simp), Finset.sum_image (fun a _ b _ h => Option.some.inj h)]
  by_cases hχ : χ = 1 <;>
    simp [characterProfile, characterCorrection, residueMultiplier, GoldbachTwistedMellin.residueProfile,
      hχ, Finset.sum_neg_distrib, sub_eq_add_neg]

/-- A near-one zero in the actual character-pair expansion forces a large
primitive conductor, uniformly in the original arc modulus and target. -/
theorem nearOne_characterResidue_conductor :
    ∃ c : ℝ, 0 < c ∧ ∀ (m q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (z : ℂ),
      some z ∈ characterResidues m χ → ∀ X H T : ℝ, 1 < X → 0 < H → |z.im| ≤ T →
        1-H/Real.log X ≤ z.re → X^(c/H) < 2*(χ.conductor:ℝ)*(2+T) := by
  classical
  obtain ⟨c, hc, lower⟩ := GoldbachTwistedMellin.nearOne_zero_conductor_bound
  refine ⟨c, hc, ?_⟩
  intro m q _ χ z hz X H T hX hH hT hnear
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hmem : z ∈ GoldbachTwistedMellin.exceptionalZeros χ.primitiveCharacter
      (GoldbachTwistedMellin.modelHeight (m+2 : ℕ)) := by simpa [characterResidues] using hz
  have hroot := (GoldbachTwistedMellin.mem_exceptionalZeros _ _ z).mp hmem
  exact lower χ.conductor χ.primitiveCharacter χ.primitiveCharacter_isPrimitive X H T z hX hH hT hnear hroot.2.2

/-- Expand the character-pair integral in the rational-arc coefficient into
the residue pairs estimated by `residuePair_arc_beta`, with their signs and
analytic multiplicities. -/
theorem localCharacterPair_eq_residuePairs (m n : ℕ) {q : ℕ} [NeZero q] (χ ψ : DirichletCharacter ℂ q) (w : ℝ) :
    (∫ u in -w..w, fourier (-(n:ℤ)) (u : AddCircle (1:ℝ)) *
      characterProfile (m+2) χ u * characterProfile (m+2) ψ u) =
    ∑ z ∈ characterResidues m χ, ∑ t ∈ characterResidues m ψ,
      (residueMultiplier χ z * residueMultiplier ψ t) *
      ∫ u in -w..w, GoldbachTwistedMellin.phase (-2*Real.pi*(n:ℝ)) u *
        (GoldbachTwistedMellin.residueProfile m z u * GoldbachTwistedMellin.residueProfile m t u) := by
  classical
  let F := fun u : ℝ => GoldbachTwistedMellin.phase (-2*Real.pi*(n:ℝ)) u
  let K := fun (z t : Option ℂ) (u : ℝ) => F u *
    (GoldbachTwistedMellin.residueProfile m z u * GoldbachTwistedMellin.residueProfile m t u)
  let g := fun (z t : Option ℂ) (u : ℝ) => (residueMultiplier χ z * residueMultiplier ψ t) * K z t u
  have hg (z t : Option ℂ) : Continuous (g z t) := continuous_const.mul
    ((GoldbachTwistedMellin.continuous_phase _).mul
      ((GoldbachTwistedMellin.continuous_residueProfile m z).mul (GoldbachTwistedMellin.continuous_residueProfile m t)))
  have hphase (u : ℝ) : fourier (-(n:ℤ)) (u : AddCircle (1:ℝ)) = F u := by
    rw [fourier_coe_eq_phase]
    change Complex.exp (((2*Real.pi*(((-(n:ℤ)):ℝ)*u) : ℝ):ℂ)*Complex.I) =
      Complex.exp (((-2*Real.pi*(n:ℝ)*u : ℝ):ℂ)*Complex.I)
    congr 3
    push_cast
    ring
  have he (u : ℝ) : fourier (-(n:ℤ)) (u : AddCircle (1:ℝ)) * characterProfile (m+2) χ u *
      characterProfile (m+2) ψ u = ∑ z ∈ characterResidues m χ, ∑ t ∈ characterResidues m ψ, g z t u := by
    rw [hphase, characterProfile_eq_residues m χ, characterProfile_eq_residues m ψ, mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z _
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun t _ => by dsimp only [g, K]; ring)
  simp_rw [he]
  rw [intervalIntegral.integral_finsetSum (fun z _ =>
    (continuous_finsetSum _ (fun t _ => hg z t)).intervalIntegrable ..)]
  apply Finset.sum_congr rfl
  intro z _
  rw [intervalIntegral.integral_finsetSum (fun t _ => (hg z t).intervalIntegrable ..)]
  exact Finset.sum_congr rfl (fun t _ => intervalIntegral.integral_const_mul _ _)

private def profile (X : ℕ) (i : ℕ × ℕ) (β : ℝ) : ℂ :=
  if h : i.1 = 0 then 0 else
    letI : NeZero i.1 := ⟨h⟩
    DeepThreeQuarters.rationalModel X i.1 β -
      GoldbachTwistedMellin.canonicalCorrection X (i.2 : ZMod i.1) β

private theorem continuous_profile (X : ℕ) (i : ℕ × ℕ) : Continuous (profile X i) := by
  by_cases h : i.1 = 0
  · exact (show Continuous (fun _ : ℝ => (0 : ℂ)) from continuous_const).congr
      (fun β => by simp [profile, h])
  · let _ : NeZero i.1 := ⟨h⟩
    have hmodel : Continuous (DeepThreeQuarters.rationalModel X i.1) := by
      unfold DeepThreeQuarters.rationalModel
      exact continuous_const.mul (continuous_positiveGeometricSum X)
    exact (hmodel.sub (continuous_canonicalCorrection X i.1 i.2)).congr
      (fun β => by simp [profile, h])

private theorem profile_eq_characterSum (X q a : ℕ) [NeZero q] (ha : a.Coprime q) (β : ℝ) :
    profile X (q, a) β = ∑ χ : DirichletCharacter ℂ q,
      GoldbachTwistedMellin.additiveWeight (a : ZMod q) χ * characterProfile X χ β := by
  classical
  let w := GoldbachTwistedMellin.additiveWeight (a : ZMod q)
  have hPrime :
      (∑ χ : DirichletCharacter ℂ q, w χ *
        (if χ = 1 then DeepThreeQuarters.positiveGeometricSum X β else 0)) =
      DeepThreeQuarters.rationalModel X q β := by
    rw [Finset.sum_eq_single_of_mem (1 : DirichletCharacter ℂ q) (Finset.mem_univ _)]
    · rw [ite_eq_left rfl]
      change GoldbachTwistedMellin.additiveWeight (a : ZMod q) 1 * _ = _
      rw [GoldbachTwistedMellin.additiveWeight_one,
        GoldbachGRHWindow.additiveModel_eq_moebius _ ((ZMod.isUnit_iff_coprime a q).mpr ha)]
      rfl
    · intro χ _ hχ
      simp [hχ]
  have hq := NeZero.ne q
  calc
    _ = DeepThreeQuarters.rationalModel X q β -
        GoldbachTwistedMellin.canonicalCorrection X (a : ZMod q) β := by simp [profile, hq]
    _ = _ := by
      simp only [characterProfile, mul_sub, Finset.sum_sub_distrib]
      rw [hPrime, canonicalCorrection_eq_sum]

private def term (X : ℕ) (P : ℝ) (i : ℕ × ℕ) (t : AddCircle (1 : ℝ)) : ℂ :=
  if |arcCoordinate i t| ≤ arcWidth X P i.1 then profile X i (arcCoordinate i t) else 0

/-- The prime-sum model with the finite Dirichlet zero corrections for
each reduced rational center. -/
def exponentialSum (X : ℕ) (P : ℝ) (t : AddCircle (1 : ℝ)) : ℂ :=
  ∑ i ∈ majorArcIndices ⌊P⌋₊, term X P i t

private theorem term_memLp (X : ℕ) (P : ℝ) (i : ℕ × ℕ) :
    MemLp (term X P i) 2 haarAddCircle := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Set.Icc (-(arcWidth X P i.1)) (arcWidth X P i.1))
    (continuous_profile X i).continuousOn
  have hCoord := measurable_arcCoordinate i
  refine MemLp.of_bound ?_ (max C 0) ?_
  · exact (Measurable.ite (measurableSet_le hCoord.abs measurable_const)
      ((continuous_profile X i).measurable.comp hCoord) measurable_const).aestronglyMeasurable
  · filter_upwards with t
    by_cases h : |arcCoordinate i t| ≤ arcWidth X P i.1
    · simpa [term, h] using (hC _ (abs_le.mp h)).trans (le_max_left _ 0)
    · simp [term, h]

private theorem exponentialSum_memLp (X : ℕ) (P : ℝ) :
    MemLp (exponentialSum X P) 2 haarAddCircle :=
  memLp_finsetSum (majorArcIndices ⌊P⌋₊) (f := term X P) (fun i _ => term_memLp X P i)

private theorem exponentialSum_eq_of_mem {X : ℕ} {P : ℝ} (hX : 0 < (X : ℝ)) (hP : 0 ≤ P)
    (hSmall : 2 * P * (⌊P⌋₊ : ℕ) < (X : ℝ)) {t : AddCircle (1 : ℝ)} {i : ℕ × ℕ}
    (hi : i ∈ majorArcIndices ⌊P⌋₊) (h : |arcCoordinate i t| ≤ arcWidth X P i.1) :
    exponentialSum X P t = profile X i (arcCoordinate i t) := by
  classical
  unfold exponentialSum
  rw [Finset.sum_eq_single_of_mem i hi]
  · simp [term, h]
  · intro j hj hne
    have hj' : ¬ |arcCoordinate j t| ≤ arcWidth X P j.1 := fun hh =>
      hne (unique_arc_of_equal_lifts hX hP hSmall hj hi hh h
        ((lift_arcCoordinate j t).trans (lift_arcCoordinate i t).symm))
    simp [term, hj']

private theorem exponentialSum_eq_zero {X : ℕ} {P : ℝ} {t : AddCircle (1 : ℝ)}
    (ht : t ∉ circleArcs X P) : exponentialSum X P t = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  exact ite_eq_right (fun h => ht ⟨i, hi, h⟩)

private theorem arcIndicator_energy {X : ℕ} {P : ℝ} (hX : 0 < (X : ℝ)) (hP : 0 ≤ P)
    (hSmall : 2 * P * (⌊P⌋₊ : ℕ) < (X : ℝ)) :
    (∫ t, ‖(circleArcs X P).indicator (fun _ => (1 : ℂ)) t‖^2 ∂haarAddCircle) ≤
      2 * P^2 / (X : ℝ) := by
  let Q := ⌊P⌋₊
  have he : (circleArcs X P).indicator (fun _ => (1 : ℂ)) =
      arcModel X P Q (fun _ _ => 1) := by
    classical
    funext t
    by_cases ht : t ∈ circleArcs X P
    · rw [Set.indicator_of_mem ht]
      obtain ⟨i, hi, hw⟩ := ht
      exact (arcModel_eq_of_mem (fun _ _ => (1 : ℂ)) hX hP hSmall t hi hw).symm
    · rw [Set.indicator_of_notMem ht]
      exact (arcModel_eq_zero_of_not_mem _ t fun i hi => lt_of_not_ge
        (fun h => ht ⟨i, hi, h⟩)).symm
  rw [he, arcModel_energy _ _ _ _ (fun _ => continuous_const) hX hP hSmall, sum_arcIndices]
  calc
    _ ≤ ∑ _q ∈ Finset.Icc 1 Q, 2 * P / (X : ℝ) := by
      apply Finset.sum_le_sum
      intro q hq
      have hqR : 0 < (q : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hq).1
      simp only [norm_one, one_pow, intervalIntegral.integral_const, smul_eq_mul, mul_one,
        Finset.sum_const, nsmul_eq_mul]
      calc
        _ ≤ (q : ℝ) * (arcWidth X P q - -arcWidth X P q) := by
          apply mul_le_mul_of_nonneg_right
          · exact_mod_cast (Finset.card_filter_le (Finset.range q) (fun a : ℕ => a.Coprime q)).trans_eq
              (Finset.card_range q)
          · have hw : 0 ≤ arcWidth X P q := div_nonneg hP (by positivity)
            linarith
        _ = _ := by
          unfold arcWidth
          field_simp [hX.ne', hqR.ne']
          ring
    _ = (Q : ℝ) * (2 * P / (X : ℝ)) := by simp [Nat.card_Icc]
    _ ≤ P * (2 * P / (X : ℝ)) := mul_le_mul_of_nonneg_right (Nat.floor_le hP) (by positivity)
    _ = _ := by ring

private theorem circlePrimeSum_memLp (X : ℕ) :
    MemLp (circlePrimeSum X) 2 haarAddCircle := by
  have hc : Continuous (circlePrimeSum X) :=
    continuous_finsetSum _ fun k _ => continuous_const.mul (fourier (k : ℤ)).continuous
  exact hc.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

private theorem primeMajorPart_memLp (X : ℕ) (P : ℝ) :
    MemLp (primeMajorPart X P) 2 haarAddCircle :=
  (circlePrimeSum_memLp X).indicator (measurable_circleArcs X P).nullMeasurableSet

private theorem circlePrimeSum_energy {X : ℕ} (hX : 1 ≤ X) :
    (∫ t, ‖circlePrimeSum X t‖^2 ∂haarAddCircle) ≤
      2 * (X : ℝ) * (Real.log (X : ℝ))^2 := by
  have hvol : (volume : Measure (AddCircle (1 : ℝ))) = haarAddCircle := by
    rw [AddCircle.volume_eq_smul_haarAddCircle, ENNReal.ofReal_one, one_smul]
  rw [← hvol, ← AddCircle.intervalIntegral_preimage (1 : ℝ) 0 (fun t => ‖circlePrimeSum X t‖^2)]
  simp only [zero_add, circlePrimeSum_coe]
  have hParseval := PEqualNP.Outside.L_goldbach_continuous_parseval X BinaryShiftCircle.primeWeight
  change (∫ t in (0 : ℝ)..1, ‖BinaryShiftCircle.primeSum X t‖^2) =
    ∑ p ∈ Finset.range (X + 1), (BinaryShiftCircle.primeWeight p)^2 at hParseval
  rw [hParseval]
  calc
    _ ≤ ∑ _p ∈ Finset.range (X + 1), (Real.log (X : ℝ))^2 := by
      apply Finset.sum_le_sum
      intro p hp
      by_cases hPrime : p.Prime
      · simp only [BinaryShiftCircle.primeWeight, hPrime, ite_true]
        exact pow_le_pow_left₀ (Real.log_natCast_nonneg p)
          (Real.log_le_log (Nat.cast_pos.mpr hPrime.pos)
            (Nat.cast_le.mpr (Nat.le_of_lt_succ (Finset.mem_range.mp hp)))) 2
      · simpa [BinaryShiftCircle.primeWeight, hPrime] using sq_nonneg (Real.log (X : ℝ))
    _ = ((X : ℝ) + 1) * (Real.log (X : ℝ))^2 := by simp
    _ ≤ _ := by
      have hX₁ : 1 ≤ (X : ℝ) := by exact_mod_cast hX
      exact mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)

private theorem exponentialSum_error :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ, 64 ≤ X → ∀ P : ℝ, 0 ≤ P → P ≤ (X : ℝ)^(3/10 : ℝ) →
      2 * P * (⌊P⌋₊ : ℕ) < (X : ℝ) → ∀ t : AddCircle (1 : ℝ),
        ‖primeMajorPart X P t - exponentialSum X P t‖ ≤
          C * (X : ℝ)^(39/50 : ℝ) * ‖(circleArcs X P).indicator (fun _ => (1 : ℂ)) t‖ := by
  obtain ⟨K, hK, hFormula⟩ := GoldbachTwistedMellin.rational_canonical_model
  obtain ⟨D, hD, hLog⟩ := GoldbachTwistedMellin.quartic_log_scale (e := 1 / 200) (by norm_num)
  refine ⟨K * D, mul_pos hK hD, ?_⟩
  intro X hX P hP hPUpper hSmall t
  have hX₁ : 1 ≤ (X : ℝ) := by exact_mod_cast (show 1 ≤ X by omega)
  have hXPos : 0 < (X : ℝ) := zero_lt_one.trans_le hX₁
  by_cases ht : t ∈ circleArcs X P
  · have haArc := ht
    obtain ⟨i, hi, hw⟩ := haArc
    obtain ⟨hq, hqP, _, ha⟩ := mem_majorArcIndices.mp hi
    let q := i.1
    let a := i.2
    let β := arcCoordinate i t
    have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
    let _ : NeZero q := ⟨Nat.ne_of_gt hq⟩
    have hqScale : (q : ℝ) ≤ (X : ℝ)^(3/10 : ℝ) :=
      (Nat.cast_le.mpr hqP).trans ((Nat.floor_le hP).trans hPUpper)
    have hβ : |β| ≤ (X : ℝ)^(3/10 : ℝ) / ((q : ℝ) * X) :=
      hw.trans (div_le_div_of_nonneg_right hPUpper (by positivity))
    have hS : primeMajorPart X P t =
        DeepThreeQuarters.weightedSum X DeepThreeQuarters.primeWeight ((a : ℝ) / q + β) := by
      rw [primeMajorPart, Set.indicator_of_mem ht]
      calc
        _ = circlePrimeSum X ((β + arcCenter i : ℝ) : AddCircle (1 : ℝ)) :=
          congrArg (circlePrimeSum X) (lift_arcCoordinate i t).symm
        _ = _ := by
          rw [circlePrimeSum_coe, add_comm β]
          rfl
    have hV : exponentialSum X P t =
        DeepThreeQuarters.rationalModel X q β -
          GoldbachTwistedMellin.canonicalCorrection X (a : ZMod q) β := by
      rw [exponentialSum_eq_of_mem hXPos hP hSmall hi hw]
      simp only [profile, dite_eq_right (show i.1 ≠ 0 from Nat.ne_of_gt hq)]
      rfl
    rw [Set.indicator_of_mem ht, norm_one, mul_one, hS, hV, sub_sub_eq_add_sub,
      ← sub_add_eq_add_sub]
    calc
      _ ≤ K * (X : ℝ)^(31/40 : ℝ) * GoldbachTwistedMellin.logScale X ^ 4 :=
        hFormula X hX a q ha hqScale β hβ
      _ ≤ K * (X : ℝ)^(31/40 : ℝ) * (D * (X : ℝ)^(1/200 : ℝ)) :=
        mul_le_mul_of_nonneg_left (hLog X hX₁) (by positivity)
      _ = (K * D) * ((X : ℝ)^(31/40 : ℝ) * (X : ℝ)^(1/200 : ℝ)) := by ring
      _ = _ := by
        rw [← Real.rpow_add hXPos, show (31/40 + 1/200 : ℝ) = 39/50 by norm_num]
  · simp [primeMajorPart, ht, exponentialSum_eq_zero ht]

def coefficient (X n : ℕ) (P : ℝ) : ℂ :=
  fourierCoeff (fun t => (exponentialSum X P t)^2) (n : ℤ)

private theorem term_square_coefficient (X : ℕ) (n : ℤ) (P : ℝ) (i : ℕ × ℕ)
    (hw : 0 ≤ arcWidth X P i.1) (hwSmall : arcWidth X P i.1 < 1/2) :
    fourierCoeff (fun t => (term X P i t)^2) n =
      fourier (-n) (arcCenter i : AddCircle (1 : ℝ)) *
        ∫ t in -(arcWidth X P i.1)..arcWidth X P i.1,
          fourier (-n) (t : AddCircle (1 : ℝ)) * (profile X i t)^2 := by
  let w := arcWidth X P i.1
  let C := (Set.Icc (-w) w).indicator (fun t => (profile X i t)^2)
  let G := AddCircle.liftIoc (1 : ℝ) (-1/2) C
  have he : (fun t => (term X P i t)^2) =
      fun t => G (t - (arcCenter i : AddCircle (1 : ℝ))) := by
    funext t
    let β := arcCoordinate i t
    change (if |β| ≤ w then profile X i β else 0)^2 = C β
    by_cases h : |β| ≤ w
    · simp [C, h, abs_le.mp h]
    · simp [C, h, show β ∉ Set.Icc (-w) w from fun h' => h (abs_le.mpr h')]
  rw [he, fourierCoeff_translate]
  congr 1
  rw [fourierCoeff_eq_intervalIntegral _ _ (-1/2 : ℝ)]
  simp only [div_one, one_smul]
  let f := fun t : ℝ => fourier (-n) (t : AddCircle (1 : ℝ)) * (profile X i t)^2
  have hInterval : (∫ t in (-1/2 : ℝ)..(-1/2+1 : ℝ), fourier (-n) (t : AddCircle (1 : ℝ)) • G t) =
      ∫ t in (-1/2 : ℝ)..(-1/2+1 : ℝ), (Set.Icc (-w) w).indicator f t := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards with t ht
    rw [Set.uIoc_of_le (by norm_num)] at ht
    change _ • AddCircle.liftIoc 1 (-1/2 : ℝ) C t = _
    rw [AddCircle.liftIoc_coe_apply ht, smul_eq_mul]
    by_cases h : t ∈ Set.Icc (-w) w <;> simp [C, f, h]
  rw [hInterval, intervalIntegral.integral_of_le (by norm_num), integral_indicator measurableSet_Icc,
    Measure.restrict_restrict measurableSet_Icc,
    intervalIntegral.integral_of_le (by linarith only [hw])]
  have hsub : Set.Icc (-w) w ⊆ Set.Ioc (-1/2 : ℝ) (-1/2+1) := by
    intro t ht
    have hSmall : w < 1/2 := hwSmall
    exact ⟨by linarith only [ht.1, hSmall], by linarith only [ht.2, hSmall]⟩
  rw [Set.inter_eq_left.mpr hsub]
  exact setIntegral_congr_set Ioc_ae_eq_Icc.symm

/-- The model separates into integrals of the explicit Dirichlet profiles
at each reduced rational center. -/
theorem coefficient_eq_profiles {X n : ℕ} {P : ℝ} (hX : 0 < (X : ℝ)) (hP : 0 ≤ P)
    (hSmall : 2 * P * (⌊P⌋₊ : ℕ) < (X : ℝ)) :
    coefficient X n P =
      ∑ i ∈ majorArcIndices ⌊P⌋₊, fourier (-(n : ℤ)) (arcCenter i : AddCircle (1 : ℝ)) *
        ∫ t in -(arcWidth X P i.1)..arcWidth X P i.1,
          fourier (-(n : ℤ)) (t : AddCircle (1 : ℝ)) * (profile X i t)^2 := by
  classical
  let g := fun (i : ℕ × ℕ) (t : AddCircle (1 : ℝ)) => (term X P i t)^2
  have hSquare : (fun t => (exponentialSum X P t)^2) =
      ∑ i ∈ majorArcIndices ⌊P⌋₊, g i := by
    funext t
    simp only [Finset.sum_apply]
    by_cases ht : t ∈ circleArcs X P
    · obtain ⟨i, hi, hw⟩ := ht
      rw [exponentialSum_eq_of_mem hX hP hSmall hi hw, Finset.sum_eq_single_of_mem i hi]
      · simp [g, term, hw]
      · intro j hj hne
        have hj' : ¬ |arcCoordinate j t| ≤ arcWidth X P j.1 := fun h =>
          hne (unique_arc_of_equal_lifts hX hP hSmall hj hi h hw
            ((lift_arcCoordinate j t).trans (lift_arcCoordinate i t).symm))
        simp [g, term, hj']
    · rw [exponentialSum_eq_zero ht, zero_pow two_ne_zero]
      symm
      apply Finset.sum_eq_zero
      intro i hi
      have hi' : ¬ |arcCoordinate i t| ≤ arcWidth X P i.1 := fun h => ht ⟨i, hi, h⟩
      simp [g, term, hi']
  have hi (i : ℕ × ℕ) : Integrable (g i) haarAddCircle := by
    have h := term_memLp X P i
    simpa only [g, pow_two] using
      (memLp_one_iff_integrable.mp
        (h.fun_mul h : MemLp (fun t => term X P i t * term X P i t) 1 haarAddCircle))
  rw [coefficient, hSquare, fourierCoeff.sum _ _ (fun i _ => hi i), Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i hi
  obtain ⟨hq, hqQ, _, _⟩ := mem_majorArcIndices.mp hi
  have hq₁ : 1 ≤ (i.1 : ℝ) := by exact_mod_cast hq
  have hQ : 1 ≤ ((⌊P⌋₊ : ℕ) : ℝ) := by exact_mod_cast hq.trans_le hqQ
  apply term_square_coefficient X (n : ℤ) P i (div_nonneg hP (by positivity))
  apply (div_lt_iff₀ (mul_pos (by linarith) hX)).mpr
  nlinarith only [hSmall, mul_le_mul_of_nonneg_left hQ hP, mul_le_mul_of_nonneg_right hq₁ hX.le]

/-- At one modulus the arithmetic character-pair factors separate from the
zero profiles inside each local integral. -/
theorem localCoefficient_eq_characterPairs (X n q : ℕ) [NeZero q] (P : ℝ) :
    let W := fun a : ℕ => GoldbachTwistedMellin.additiveWeight (a : ZMod q)
    let C := fun a : ℕ => fourier (-(n : ℤ)) (arcCenter (q, a) : AddCircle (1 : ℝ))
    let Z := fun t : ℝ => fourier (-(n : ℤ)) (t : AddCircle (1 : ℝ))
    let U := (Finset.range q).filter (fun a => a.Coprime q)
    let w := arcWidth X P q
    (∑ a ∈ U, C a * ∫ t in -w..w, Z t * (profile X (q, a) t)^2) =
      ∑ χ : DirichletCharacter ℂ q, ∑ ψ : DirichletCharacter ℂ q,
        (∑ a ∈ U, C a * W a χ * W a ψ) *
          ∫ t in -w..w, Z t * characterProfile X χ t * characterProfile X ψ t := by
  classical
  intro W C Z U w
  let g := fun (χ ψ : DirichletCharacter ℂ q) t =>
    Z t * characterProfile X χ t * characterProfile X ψ t
  let K := fun χ ψ => ∫ t in -w..w, g χ ψ t
  have hZ : Continuous Z :=
    (fourier (-(n : ℤ))).continuous.comp (AddCircle.continuous_mk' (1 : ℝ))
  have hg (χ ψ : DirichletCharacter ℂ q) : Continuous (g χ ψ) :=
    (hZ.mul (continuous_characterProfile X χ)).mul (continuous_characterProfile X ψ)
  have hIntegral (a : ℕ) (ha : a ∈ U) :
      (∫ t in -w..w, Z t * (profile X (q, a) t)^2) =
        ∑ χ : DirichletCharacter ℂ q, ∑ ψ : DirichletCharacter ℂ q,
          (W a χ * W a ψ) * K χ ψ := by
    have hcoprime : a.Coprime q := (Finset.mem_filter.mp ha).2
    have hAt (t : ℝ) : Z t * (profile X (q, a) t)^2 =
        ∑ χ : DirichletCharacter ℂ q, ∑ ψ : DirichletCharacter ℂ q,
          (W a χ * W a ψ) * g χ ψ t := by
      rw [profile_eq_characterSum X q a hcoprime t, pow_two, Finset.sum_mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro χ _
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun ψ _ => by
        dsimp [W, g]
        ring
    have hcont (χ ψ : DirichletCharacter ℂ q) :
        Continuous (fun t => (W a χ * W a ψ) * g χ ψ t) := continuous_const.mul (hg χ ψ)
    simp_rw [hAt]
    rw [intervalIntegral.integral_finsetSum (fun χ _ =>
      (continuous_finsetSum _ (fun ψ _ => hcont χ ψ)).intervalIntegrable _ _)]
    apply Finset.sum_congr rfl
    intro χ _
    rw [intervalIntegral.integral_finsetSum (fun ψ _ => (hcont χ ψ).intervalIntegrable _ _)]
    exact Finset.sum_congr rfl fun ψ _ => intervalIntegral.integral_const_mul _ _
  change (∑ a ∈ U, C a * ∫ t in -w..w, Z t * (profile X (q, a) t)^2) =
     ∑ χ : DirichletCharacter ℂ q, ∑ ψ : DirichletCharacter ℂ q,
       (∑ a ∈ U, C a * W a χ * W a ψ) * K χ ψ
  calc
    _ = ∑ a ∈ U, ∑ χ : DirichletCharacter ℂ q, ∑ ψ : DirichletCharacter ℂ q,
        C a * ((W a χ * W a ψ) * K χ ψ) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [hIntegral a ha]
      simp only [Finset.mul_sum]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro χ _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro ψ _
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun a _ => by ring

private theorem additiveWeight_gaussSum {q : ℕ} [NeZero q] (a : ZMod q)
    (χ : DirichletCharacter ℂ q) :
    GoldbachTwistedMellin.additiveWeight a χ =
      gaussSum χ⁻¹ (ZMod.stdAddChar.mulShift a) / (q.totient : ℂ) := by
  rw [GoldbachTwistedMellin.weight_expansion, gaussSum]
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  rw [mul_comm, AddChar.mulShift_apply]
  change star (χ r) * _ = _
  rw [MulChar.star_apply']

private theorem additiveWeight_unit {q : ℕ} [NeZero q] (a : ZMod q) (ha : IsUnit a)
    (χ : DirichletCharacter ℂ q) :
    GoldbachTwistedMellin.additiveWeight a χ =
      χ a * (gaussSum χ⁻¹ ZMod.stdAddChar / (q.totient : ℂ)) := by
  obtain ⟨u, rfl⟩ := ha
  rw [additiveWeight_gaussSum, gaussSum_mulShift_eq, inv_inv, mul_div_assoc]

/-- The arithmetic coefficient in the local pair formula is the product of
two normalized Gauss sums times the twisted reduced-residue sum. -/
theorem characterPairFactor_eq_gaussSums (n q : ℕ) [NeZero q] (χ ψ : DirichletCharacter ℂ q) :
    let U := (Finset.range q).filter (fun a => a.Coprime q)
    let C := fun a : ℕ => fourier (-(n : ℤ)) (arcCenter (q, a) : AddCircle (1 : ℝ))
    (∑ a ∈ U, C a * GoldbachTwistedMellin.additiveWeight (a : ZMod q) χ *
        GoldbachTwistedMellin.additiveWeight (a : ZMod q) ψ) =
      (gaussSum χ⁻¹ ZMod.stdAddChar / (q.totient : ℂ)) *
        (gaussSum ψ⁻¹ ZMod.stdAddChar / (q.totient : ℂ)) *
        ∑ a ∈ U, C a * χ (a : ZMod q) * ψ (a : ZMod q) := by
  intro U C
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  have hUnit : IsUnit (a : ZMod q) := (ZMod.isUnit_iff_coprime a q).mpr (Finset.mem_filter.mp ha).2
  rw [additiveWeight_unit _ hUnit χ, additiveWeight_unit _ hUnit ψ]
  ring

open DirichletCharacter in
/-- The arithmetic coefficient multiplying each pair of actual profiles is
the denominator coefficient of the generalized singular series. The inverse
characters here come from finite Fourier inversion of the rational phase. -/
theorem characterPairFactor_eq_primitiveCoefficient (n q : ℕ) [NeZero q] (χ ψ : DirichletCharacter ℂ q) :
    (∑ a ∈ (Finset.range q).filter (fun a => a.Coprime q),
      fourier (-(n:ℤ)) (arcCenter (q,a) : AddCircle (1:ℝ)) *
        GoldbachTwistedMellin.additiveWeight (a:ZMod q) χ * GoldbachTwistedMellin.additiveWeight (a:ZMod q) ψ) =
      TwistedGoldbachSingularSeries.coefficient χ.primitiveCharacter⁻¹ ψ.primitiveCharacter⁻¹ n q := by
  classical
  rw [TwistedGoldbachSingularSeries.coefficient, dite_eq_left (NeZero.ne q),
    dite_eq_left ⟨χ.conductor_dvd_level, ψ.conductor_dvd_level⟩, map_inv, map_inv,
    χ.changeLevel_primitiveCharacter, ψ.changeLevel_primitiveCharacter,
    ← TwistedGoldbachSingularSeries.reduced_numerators χ⁻¹ ψ⁻¹]
  have e : (Finset.range q).filter (fun a => a.Coprime q) =
      (Finset.range q).filter (fun a => q.Coprime a) := by
    apply Finset.filter_congr
    exact fun i _ => Nat.coprime_comm
  rw [e]
  apply Finset.sum_congr rfl
  intro a _
  have ef : fourier (-(n:ℤ)) (arcCenter (q,a) : AddCircle (1:ℝ)) =
      ZMod.stdAddChar ((a:ZMod q)*(-(n:ZMod q))) := by
    rw [fourier_coe_eq_phase]
    have ch := ZMod.stdAddChar_coe (N := q) ((a:ℤ)*(-(n:ℤ)))
    push_cast at ch
    rw [ch]
    change Complex.exp (((2*Real.pi*(((-(n:ℤ)):ℝ)*((a:ℝ)/q)) : ℝ):ℂ)*Complex.I) = _
    congr 1
    push_cast
    ring
  rw [ef, additiveWeight_gaussSum, additiveWeight_gaussSum]
  rfl

open DirichletCharacter in
/-- The real part of the ordinary singular series dominates in modulus every
complete primitive singular series in the rational-arc expansion. -/
theorem complete_characterPair_bound (n q : ℕ) [NeZero q] (hn : 0 < n) (χ ψ : DirichletCharacter ℂ q) :
    ‖∑' d : ℕ, TwistedGoldbachSingularSeries.coefficient χ.primitiveCharacter⁻¹ ψ.primitiveCharacter⁻¹ n d‖ ≤
      (∑' d : ℕ, TwistedGoldbachSingularSeries.coefficient (1 : DirichletCharacter ℂ 1)
        (1 : DirichletCharacter ℂ 1) n d).re := by
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  let : NeZero ψ.conductor := ⟨ψ.conductor_ne_zero⟩
  exact TwistedGoldbachSingularSeries.infinite_domination χ.primitiveCharacter_isPrimitive.inv
    ψ.primitiveCharacter_isPrimitive.inv n hn


private theorem phase_add (a b : ℝ) :
    BinaryShiftCircle.phase (a + b) = BinaryShiftCircle.phase a * BinaryShiftCircle.phase b := by
  unfold BinaryShiftCircle.phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem positiveGeometricSum_eq_kernel {X : ℕ} (hX : 1 ≤ X) (t : ℝ) :
    DeepThreeQuarters.positiveGeometricSum X t =
      GoldbachEstermannKernel.kernel (X - 1) t * BinaryShiftCircle.phase t := by
  unfold DeepThreeQuarters.positiveGeometricSum GoldbachEstermannKernel.kernel
  rw [Finset.sum_mul, Nat.sub_add_cancel hX]
  symm
  refine Finset.sum_bij (fun k _ => k+1) ?_ ?_ ?_ ?_
  · intro k hk
    have hk' := Finset.mem_range.mp hk
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · intro a _ b _ hab
    omega
  · intro j hj
    obtain ⟨h₁, h₂⟩ := Finset.mem_Icc.mp hj
    exact ⟨j - 1, Finset.mem_range.mpr (by omega), by omega⟩
  · intro k _
    change BinaryShiftCircle.phase ((k : ℝ)*t) * BinaryShiftCircle.phase t =
      BinaryShiftCircle.phase (((k + 1 : ℕ) : ℝ)*t)
    rw [← phase_add]
    congr 1
    push_cast
    ring

private def principalIntegrand (X n : ℕ) (t : ℝ) : ℂ :=
  fourier (-(n : ℤ)) (t : AddCircle (1 : ℝ)) * (DeepThreeQuarters.positiveGeometricSum X t)^2

private theorem continuous_principalIntegrand (X n : ℕ) : Continuous (principalIntegrand X n) :=
  ((fourier (-(n : ℤ))).continuous.comp (AddCircle.continuous_mk' (1 : ℝ))).mul
    ((continuous_positiveGeometricSum X).pow 2)

private theorem full_principalIntegral {X n : ℕ} (hn : 2 ≤ n) (hnX : n ≤ X) :
    (∫ t in (-(1/2) : ℝ)..1/2, principalIntegrand X n t) = ((n-1 : ℕ) : ℂ) := by
  calc
    _ = ∫ t in (-(1/2) : ℝ)..1/2, GoldbachEstermannKernel.twisted (X - 1) (n - 2) t := by
      apply intervalIntegral.integral_congr
      intro t _
      have hphase : BinaryShiftCircle.phase (-(n : ℝ)*t) * BinaryShiftCircle.phase t ^ 2 =
          BinaryShiftCircle.phase (-((n-2 : ℕ) : ℝ)*t) := by
        rw [pow_two, ← phase_add, ← phase_add]
        congr 1
        rw [Nat.cast_sub hn]
        push_cast
        ring
      have hFourier : fourier (-(n : ℤ)) (t : AddCircle (1 : ℝ)) =
          BinaryShiftCircle.phase (-(n : ℝ) * t) := by
        simp only [fourier_coe_eq_phase, Int.cast_neg, Int.cast_natCast]
      rw [principalIntegrand, hFourier, positiveGeometricSum_eq_kernel (by omega), mul_pow]
      change _ = (GoldbachEstermannKernel.kernel (X - 1) t)^2 *
        BinaryShiftCircle.phase (-((n-2 : ℕ) : ℝ)*t)
      rw [← hphase]
      ring
    _ = ((n-2 : ℕ) : ℂ) + 1 := GoldbachEstermannKernel.full_coefficient _ _ (by omega)
    _ = _ := by exact_mod_cast (show n - 2 + 1 = n - 1 by omega)

private theorem principalIntegrand_norm_le (X n : ℕ) (t : ℝ) (ht : 0 < |t|) (hHalf : |t| ≤ 1/2) :
    ‖principalIntegrand X n t‖ ≤ (1/4 : ℝ) * |t|^(-2 : ℤ) := by
  have hPhase : ‖fourier (-(n : ℤ)) (t : AddCircle (1 : ℝ))‖ = 1 := by
    rw [fourier_coe_eq_phase]
    exact Complex.norm_exp_ofReal_mul_I _
  have hGeo := DeepThreeQuarters.abs_mul_norm_geometricSum_le_half X hHalf
  have hGeo' : ‖DeepThreeQuarters.geometricSum X t‖ ≤ 1/(2*|t|) :=
    (le_div_iff₀ (by positivity)).mpr (by linarith only [hGeo])
  rw [principalIntegrand, norm_mul, hPhase, one_mul, norm_pow,
    DeepThreeQuarters.norm_positiveGeometricSum_eq]
  calc
    _ ≤ (1/(2*|t|))^2 := pow_le_pow_left₀ (norm_nonneg _) hGeo' 2
    _ = _ := by
      rw [zpow_neg]
      field_simp [ht.ne']
      ring

private theorem clipped_principalIntegral_error {X n : ℕ} (hn : 2 ≤ n) (hnX : n ≤ X)
    {w : ℝ} (hw : 0 < w) (hwHalf : w ≤ 1/2) :
    ‖(∫ t in -w..w, principalIntegrand X n t) - ((n-1 : ℕ) : ℂ)‖ ≤ 1/(2*w) := by
  let f := principalIntegrand X n
  have hf : Continuous f := continuous_principalIntegrand X n
  have hNo : (0 : ℝ) ∉ Set.uIcc w (1/2) := by
    rw [Set.uIcc_of_le hwHalf]
    exact fun h => hw.not_ge h.1
  have hI : IntervalIntegrable (fun t : ℝ => (1/4 : ℝ)*t^(-2 : ℤ)) volume w (1/2) :=
    (intervalIntegral.intervalIntegrable_zpow (n := (-2 : ℤ)) (Or.inr hNo)).const_mul _
  have hTail (g : ℝ → ℂ) (hg : ∀ t ∈ Set.Ioc w (1/2), ‖g t‖ ≤ (1/4 : ℝ)*t^(-2 : ℤ)) :
      ‖∫ t in w..(1/2 : ℝ), g t‖ ≤ 1/(4*w) := by
    calc
      _ ≤ ∫ t in w..(1/2 : ℝ), (1/4 : ℝ)*t^(-2 : ℤ) :=
        intervalIntegral.norm_integral_le_of_norm_le hwHalf (Eventually.of_forall hg) hI
      _ = (1/4 : ℝ) * (w⁻¹ - 2) := by
        rw [intervalIntegral.integral_const_mul, integral_zpow (Or.inr ⟨by norm_num, hNo⟩)]
        norm_num [zpow_neg_one]
        ring
      _ ≤ 1/(4*w) := by
        calc
          _ ≤ (1/4 : ℝ)*w⁻¹ := mul_le_mul_of_nonneg_left (sub_le_self _ (by norm_num)) (by norm_num)
          _ = _ := by field_simp [hw.ne']
  have hRight := hTail f fun t ht => by
    have ht₀ := hw.trans ht.1
    simpa only [abs_of_pos ht₀] using principalIntegrand_norm_le X n t
      (by simpa only [abs_of_pos ht₀] using ht₀) (by simpa only [abs_of_pos ht₀] using ht.2)
  have hLeft := hTail (fun t => f (-t)) fun t ht => by
    have ht₀ := hw.trans ht.1
    simpa only [abs_neg, abs_of_pos ht₀] using principalIntegrand_norm_le X n (-t)
      (by simpa only [abs_neg, abs_of_pos ht₀] using ht₀)
      (by simpa only [abs_neg, abs_of_pos ht₀] using ht.2)
  rw [intervalIntegral.integral_comp_neg] at hLeft
  have he := full_principalIntegral hn hnX
  change (∫ t in (-(1/2) : ℝ)..1/2, f t) = _ at he
  rw [← intervalIntegral.integral_add_adjacent_intervals
      (hf.intervalIntegrable (-(1/2)) w) (hf.intervalIntegrable w (1/2)),
    ← intervalIntegral.integral_add_adjacent_intervals
      (hf.intervalIntegrable (-(1/2)) (-w)) (hf.intervalIntegrable (-w) w)] at he
  change ‖(∫ t in -w..w, f t) - ((n-1 : ℕ) : ℂ)‖ ≤ _
  rw [← he, show ∀ u v z : ℂ, v - (u + v + z) = -(u + z) by intros; ring, norm_neg]
  exact (norm_add_le _ _).trans ((add_le_add hLeft hRight).trans_eq (by
    field_simp [hw.ne']
    norm_num))

private theorem principal_ramanujan (q : ℕ) :
    GoldbachMajorArc.ram q 1 = (ArithmeticFunction.moebius q : ℂ) :=
  GoldbachExplicitModeledMajor.ram_one_eq_moebius q

private theorem coefficient_primeSupport (n : ℕ) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    GoldbachMajorArc.coefficient (GoldbachDensity.modulusOf S) n =
      (GoldbachDensity.localProduct n S : ℂ) := by
  induction S using Finset.induction_on with
  | empty => simp [GoldbachDensity.modulusOf, GoldbachDensity.localProduct, GoldbachMajorArc.coefficient_one]
  | @insert p S hp ih =>
    have hPrime := hS p (Finset.mem_insert_self _ _)
    have hS' (q : ℕ) (hq : q ∈ S) := hS q (Finset.mem_insert_of_mem hq)
    have hPos : 0 < ∏ q ∈ S, q := Finset.prod_pos fun q hq => (hS' q hq).pos
    have hCoprime : p.Coprime (∏ q ∈ S, q) :=
      Nat.coprime_prod_right_iff.mpr fun q hq =>
        (Nat.coprime_primes hPrime (hS' q hq)).mpr fun h => hp (h ▸ hq)
    unfold GoldbachDensity.modulusOf GoldbachDensity.localProduct at *
    rw [Finset.prod_insert hp, GoldbachMajorArc.coefficient_mul hPrime.pos hPos hCoprime,
      GoldbachMajorArc.coefficient_prime hPrime, ih hS', Finset.prod_insert hp, Complex.ofReal_mul]
    simp [GoldbachMajorArc.localCoefficient, GoldbachDensity.localTerm, neg_div]

private theorem principal_sum_by_support (n Q : ℕ) (J : ℕ → ℂ) :
    (∑ q ∈ Finset.Icc 1 Q, GoldbachMajorArc.coefficient q n * J q) =
      ∑ s ∈ (GoldbachDensity.primesThrough Q).powerset,
        if GoldbachDensity.modulusOf s ≤ Q then (GoldbachDensity.localProduct n s : ℂ) * J (GoldbachDensity.modulusOf s)
        else 0 := by
  classical
  let T := ((GoldbachDensity.primesThrough Q).powerset).filter (fun s => GoldbachDensity.modulusOf s ≤ Q)
  rw [← Finset.sum_filter]
  symm
  have hPrime (s : Finset ℕ) (hs : s ∈ T) : ∀ p ∈ s, p.Prime :=
    fun p hp => (Finset.mem_filter.mp (Finset.mem_powerset.mp (Finset.mem_filter.mp hs).1 hp)).2
  refine Finset.sum_bij_ne_zero (fun s _ _ => GoldbachDensity.modulusOf s) ?_ ?_ ?_ ?_
  · intro s hs _
    exact Finset.mem_Icc.mpr ⟨Finset.prod_pos (fun p hp => (hPrime s hs p hp).pos),
      (Finset.mem_filter.mp hs).2⟩
  · intro s hs _ t ht _ he
    exact (Nat.primeFactors_prod (hPrime s hs)).symm.trans
      ((congrArg Nat.primeFactors he).trans (Nat.primeFactors_prod (hPrime t ht)))
  · intro q hq hqNe
    have hsq : Squarefree q := by
      by_contra h
      have hzero := ArithmeticFunction.moebius_eq_zero_of_not_squarefree h
      exact hqNe (by simp [GoldbachMajorArc.coefficient, principal_ramanujan, hzero])
    have he : GoldbachDensity.modulusOf q.primeFactors = q := Nat.prod_primeFactors_of_squarefree hsq
    have hqT : q.primeFactors ∈ T := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ?_, ?_⟩
      · intro p hp
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le
          ((Nat.le_of_mem_primeFactors hp).trans (Finset.mem_Icc.mp hq).2)), Nat.prime_of_mem_primeFactors hp⟩
      · rw [he]
        exact (Finset.mem_Icc.mp hq).2
    refine ⟨q.primeFactors, hqT, ?_, he⟩
    rw [← coefficient_primeSupport n _ (hPrime q.primeFactors hqT), he]
    exact hqNe
  · intro s hs _
    rw [coefficient_primeSupport n s (hPrime s hs)]

/-- The principal profiles at the same rational centers, before adding
the Dirichlet zero corrections. -/
def principalCoefficient (X n : ℕ) (P : ℝ) : ℂ :=
  fourierCoeff (fun t => (arcModel X P ⌊P⌋₊ (DeepThreeQuarters.rationalModel X) t)^2) (n : ℤ)

private theorem principalCoefficient_eq_supportSum {X n : ℕ} {P : ℝ}
    (hX : 0 < (X : ℝ)) (hP : 0 ≤ P) (hSmall : 2 * P * (⌊P⌋₊ : ℕ) < (X : ℝ)) :
    principalCoefficient X n P =
      ∑ s ∈ (GoldbachDensity.primesThrough ⌊P⌋₊).powerset,
        if GoldbachDensity.modulusOf s ≤ ⌊P⌋₊ then (GoldbachDensity.localProduct n s : ℂ) *
          ∫ t in -(arcWidth X P (GoldbachDensity.modulusOf s))..arcWidth X P (GoldbachDensity.modulusOf s),
            principalIntegrand X n t
        else 0 := by
  let J := fun q => ∫ t in -(arcWidth X P q)..arcWidth X P q, principalIntegrand X n t
  have hCont (q : ℕ) : Continuous (DeepThreeQuarters.rationalModel X q) :=
    continuous_const.mul (continuous_positiveGeometricSum X)
  rw [principalCoefficient, arcModel_square_coeff _ _ _ _ hCont hX hP hSmall, sum_arcIndices,
    ← principal_sum_by_support n ⌊P⌋₊ J]
  apply Finset.sum_congr rfl
  intro q _
  have hIntegral :
      (∫ t in -(arcWidth X P q)..arcWidth X P q, fourier (-(n : ℤ)) (t : AddCircle (1 : ℝ)) *
        (DeepThreeQuarters.rationalModel X q t)^2) =
        ((ArithmeticFunction.moebius q : ℂ) / q.totient)^2 * J q := by
    dsimp only [J]
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _
    unfold DeepThreeQuarters.rationalModel principalIntegrand
    ring
  simp only [hIntegral, ← mul_assoc]
  rw [← Finset.sum_mul]
  congr 1
  rw [← GoldbachMajorArc.sum_centers_eq_coefficient]
  apply Finset.sum_congr rfl
  intro a ha
  rw [GoldbachMajorArc.unitMean_eq_ram (Finset.mem_filter.mp ha).2, principal_ramanujan]
  rw [fourier_coe_eq_phase]
  simp only [arcCenter, Int.cast_neg, Int.cast_natCast, BinaryShiftCircle.phase, GoldbachMajorArc.phase]
  ring

private theorem principalCoefficient_error {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {X n : ℕ} {P : ℝ},
      0 < (X : ℝ) → 0 < P → 2 * P * (⌊P⌋₊ : ℕ) < (X : ℝ) → 2 ≤ n → n ≤ X →
      ‖principalCoefficient X n P -
        ((GoldbachDensity.truncatedSingular n ⌊P⌋₊ * ((n-1 : ℕ) : ℝ) : ℝ) : ℂ)‖ ≤
          (X : ℝ)/(2*Real.sqrt P) * (C*(n : ℝ)^ε) := by
  obtain ⟨C, hC, hEuler⟩ := GoldbachDensity.weighted_euler_bound hε
  refine ⟨C, hC, ?_⟩
  intro X n P hX hP hSmall hn hnX
  let Q := ⌊P⌋₊
  let T := (GoldbachDensity.primesThrough Q).powerset
  let J := fun q => ∫ t in -(arcWidth X P q)..arcWidth X P q, principalIntegrand X n t
  let v := ((n - 1 : ℕ) : ℂ)
  let F := fun s =>
    if GoldbachDensity.modulusOf s ≤ Q then
      (GoldbachDensity.localProduct n s : ℂ) * (J (GoldbachDensity.modulusOf s) - v)
    else 0
  have hSum : principalCoefficient X n P -
      ((GoldbachDensity.truncatedSingular n Q * ((n-1 : ℕ) : ℝ) : ℝ) : ℂ) = ∑ s ∈ T, F s := by
    rw [principalCoefficient_eq_supportSum hX hP.le hSmall, GoldbachDensity.truncatedSingular]
    push_cast
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro s _
    by_cases hs : GoldbachDensity.modulusOf s ≤ ⌊P⌋₊ <;> simp [F, J, v, Q, hs, mul_sub]
  have hError (s : Finset ℕ) (hs : s ∈ T) : ‖F s‖ ≤
      ((X : ℝ)/(2*Real.sqrt P)) * (Real.sqrt (GoldbachDensity.modulusOf s) * |GoldbachDensity.localProduct n s|) := by
    let q := GoldbachDensity.modulusOf s
    have hq : 0 < q :=
      Finset.prod_pos fun p hp => (Finset.mem_filter.mp (Finset.mem_powerset.mp hs hp)).2.pos
    have hqR : 0 < (q : ℝ) := Nat.cast_pos.mpr hq
    have hq₁ : 1 ≤ (q : ℝ) := by exact_mod_cast hq
    have hSqrt := Real.sqrt_pos_of_pos hP
    dsimp only [F]
    split_ifs with hsQ
    · have hqP : (q : ℝ) ≤ P := (Nat.cast_le.mpr hsQ).trans (Nat.floor_le hP.le)
      have hQ₁ : (1 : ℝ) ≤ (Q : ℝ) := hq₁.trans (Nat.cast_le.mpr hsQ)
      let w := arcWidth X P q
      have hw : 0 < w := div_pos hP (mul_pos hqR hX)
      have hwHalf : w ≤ 1/2 := (div_le_iff₀ (mul_pos hqR hX)).mpr (by
        nlinarith only [hSmall, mul_le_mul_of_nonneg_left hQ₁ (show 0 ≤ 2*P by positivity),
          mul_le_mul_of_nonneg_right hq₁ hX.le])
      have hTail : ‖J q - v‖ ≤ (X : ℝ)/(2*Real.sqrt P) * Real.sqrt q := calc
        _ ≤ 1/(2*w) := clipped_principalIntegral_error hn hnX hw hwHalf
        _ = (X : ℝ) * (Real.sqrt q)^2/(2*(Real.sqrt P)^2) := by
          rw [Real.sq_sqrt hqR.le, Real.sq_sqrt hP.le]
          dsimp [w, arcWidth]
          field_simp [hqR.ne', hX.ne', hP.ne']
        _ = (X : ℝ)/(2*Real.sqrt P) * Real.sqrt q * (Real.sqrt q/Real.sqrt P) := by
          ring
        _ ≤ _ := mul_le_of_le_one_right (by positivity) ((div_le_one hSqrt).mpr (Real.sqrt_le_sqrt hqP))
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact (mul_le_mul_of_nonneg_left hTail (abs_nonneg _)).trans_eq (by ring)
    · rw [norm_zero]
      positivity
  rw [hSum]
  apply (norm_sum_le _ _).trans ((Finset.sum_le_sum hError).trans _)
  rw [← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact (GoldbachDensity.weighted_singular_sum n Q).le.trans (hEuler n Q (by omega))

/-- The principal profiles have a uniform positive real part throughout the
upper half of the window. The remaining contributions come from zero terms. -/
theorem principalCoefficient_floor :
    ∃ N Q₀ : ℕ, ∀ X : ℕ, N ≤ X → ∀ (P : ℝ) (n : ℕ),
      (X : ℝ)^(11/40 : ℝ) ≤ P → 2 * P * (⌊P⌋₊ : ℕ) < (X : ℝ) →
      Q₀ ≤ ⌊P⌋₊ → n ≤ ⌊P⌋₊^4 → X/2 < n → n ≤ X → Even n →
      (X : ℝ)/16 ≤ (principalCoefficient X n P).re := by
  obtain ⟨C, hC, hError⟩ := principalCoefficient_error (ε := 1/16) (by norm_num)
  obtain ⟨Q₀, hPos⟩ := GoldbachDensity.truncated_singular_positive
  have hScale := ((tendsto_rpow_atTop (by norm_num : (0 : ℝ)<3/40)).comp
    tendsto_natCast_atTop_atTop).eventually_ge_atTop (8*C)
  obtain ⟨M, hM⟩ := eventually_atTop.mp hScale
  refine ⟨max 4 M, Q₀, ?_⟩
  intro X hX P n hP hSmall hQ hSize hHalf hn hEven
  let x : ℝ := X
  have hx : 0 < x := Nat.cast_pos.mpr (by omega)
  have hX₄ : (4 : ℝ) ≤ x := by
    change (4 : ℝ) ≤ (X : ℝ)
    exact_mod_cast (show 4 ≤ X by omega)
  have hPPos : 0 < P := (Real.rpow_pos_of_pos hx _).trans_le hP
  have hSqrt := Real.sqrt_pos_of_pos hPPos
  have hn₀ : 2 ≤ n := by omega
  have hSingular := hPos ⌊P⌋₊ hQ n (by omega) hSize hEven
  have hPowP : x^(11/80 : ℝ) ≤ Real.sqrt P := by
    have h := Real.sqrt_le_sqrt hP
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx.le, show ((11/40 : ℝ)*(1/2)) = 11/80 by norm_num] at h
    exact h
  have hPowX : 8*C ≤ x^(3/40 : ℝ) := hM X (le_trans (le_max_right _ _) hX)
  have hNumerator : C*(n : ℝ)^(1/16 : ℝ) ≤ Real.sqrt P/8 := calc
    _ ≤ C*x^(1/16 : ℝ) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.cast_le.mpr hn) (by norm_num)) hC.le
    _ ≤ x^(3/40 : ℝ)/8 * x^(1/16 : ℝ) :=
      mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hx.le _)
    _ = x^(11/80 : ℝ)/8 := by
      rw [div_mul_eq_mul_div, ← Real.rpow_add hx, show (3/40 + 1/16 : ℝ) = 11/80 by norm_num]
    _ ≤ _ := div_le_div_of_nonneg_right hPowP (by norm_num)
  have hCost : (x/(2*Real.sqrt P))*(C*(n : ℝ)^(1/16 : ℝ)) ≤ x/16 :=
    (mul_le_mul_of_nonneg_left hNumerator (by positivity)).trans_eq (by field_simp [hSqrt.ne']; ring)
  have hN : x < 2*(n : ℝ) := by
    change (X : ℝ) < 2*(n : ℝ)
    exact_mod_cast (show X < 2*n by omega)
  have hMain : x/8 ≤ GoldbachDensity.truncatedSingular n ⌊P⌋₊ * ((n-1 : ℕ) : ℝ) := calc
    _ ≤ (1/2 : ℝ) * ((n-1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
      linarith
    _ ≤ _ := mul_le_mul_of_nonneg_right hSingular (Nat.cast_nonneg _)
  have hRe := Complex.re_le_norm
    (- (principalCoefficient X n P -
      ((GoldbachDensity.truncatedSingular n ⌊P⌋₊ * ((n-1 : ℕ) : ℝ) : ℝ) : ℂ)))
  rw [Complex.neg_re, Complex.sub_re, Complex.ofReal_re, norm_neg] at hRe
  have hBound := (hRe.trans (hError hx hPPos hSmall hn₀ hn)).trans hCost
  linarith only [hMain, hBound]

private theorem eventually_arcScales (Q₀ : ℕ) :
    ∃ N : ℕ, ∀ X : ℕ, N ≤ X → ∀ P : ℝ,
      (X : ℝ)^(11/40 : ℝ) ≤ P → P ≤ (X : ℝ)^(3/10 : ℝ) →
      2 * P * (⌊P⌋₊ : ℕ) < (X : ℝ) ∧ Q₀ ≤ ⌊P⌋₊ ∧ X ≤ ⌊P⌋₊^4 := by
  let castN : ℕ → ℝ := fun X => X
  have hCast : Tendsto castN atTop atTop := tendsto_natCast_atTop_atTop
  have hPSize := ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 11/40)).comp hCast).eventually_ge_atTop
    (max 2 (Q₀ : ℝ))
  have hLarge := ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/10)).comp hCast).eventually_ge_atTop 16
  have hDisjoint := ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2/5)).comp hCast).eventually_gt_atTop 2
  apply eventually_atTop.mp
  filter_upwards [eventually_ge_atTop (1 : ℕ), hPSize, hLarge, hDisjoint] with X hX hSize hxBig hxDisjoint
  intro P hPlo hPhi
  let x : ℝ := X
  have hx : 0 < x := Nat.cast_pos.mpr hX
  have hP₂ : 2 ≤ P := (le_max_left _ _).trans (hSize.trans hPlo)
  have hP : 0 ≤ P := by linarith
  have hQ₀ : Q₀ ≤ ⌊P⌋₊ := (Nat.le_floor_iff hP).mpr
    ((le_max_right _ _).trans (hSize.trans hPlo))
  have hCut : P/2 ≤ (⌊P⌋₊ : ℕ) := by linarith only [hP₂, Nat.lt_floor_add_one P]
  have hQ : X ≤ ⌊P⌋₊^4 := by
    have hPow : (x^(11/40 : ℝ)/2)^4 = x*x^(1/10 : ℝ)/16 := by
      rw [div_pow, ← Real.rpow_mul_natCast hx.le,
        show (11/40 : ℝ)*(4 : ℕ) = 1 + 1/10 by norm_num, Real.rpow_add hx, Real.rpow_one]
      norm_num
    have rhs : x ≤ (x^(11/40 : ℝ)/2)^4 := by
      rw [hPow, le_div_iff₀ (by norm_num)]
      exact mul_le_mul_of_nonneg_left hxBig hx.le
    have hLower := (div_le_div_of_nonneg_right hPlo (by norm_num : (0 : ℝ) ≤ 2)).trans hCut
    have h := rhs.trans (pow_le_pow_left₀ (by positivity) hLower 4)
    change (X : ℝ) ≤ ((⌊P⌋₊ : ℕ) : ℝ)^4 at h
    exact_mod_cast h
  refine ⟨?_, hQ₀, hQ⟩
  calc
    _ ≤ 2*P^2 := by nlinarith only [mul_le_mul_of_nonneg_left (Nat.floor_le hP) hP]
    _ ≤ 2*(x^(3/10 : ℝ))^2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hP hPhi 2) (by norm_num)
    _ = 2*x^(3/5 : ℝ) := by
      rw [← Real.rpow_mul_natCast hx.le, show (3/10 : ℝ)*(2 : ℕ) = 3/5 by norm_num]
    _ < x^(2/5 : ℝ)*x^(3/5 : ℝ) := mul_lt_mul_of_pos_right hxDisjoint (Real.rpow_pos_of_pos hx _)
    _ = _ := by rw [← Real.rpow_add hx, show (2/5+3/5 : ℝ) = 1 by norm_num, Real.rpow_one]

/-- The explicit formula on individual rational arcs suffices to approximate
the major-arc coefficients in a second moment over the entire window. -/
theorem coefficientMoment :
    ∃ (A : ℝ) (N : ℕ), 0 < A ∧ ∀ X : ℕ, N ≤ X → ∀ P : ℝ,
      (X : ℝ)^(11/40 : ℝ) ≤ P → P ≤ (X : ℝ)^(3/10 : ℝ) →
        BinaryShiftCircle.baseArcs X ⊆ realArcs X P ∧
        (∑ n ∈ Finset.range (X + 1),
          ‖BinaryShiftCircle.arcCoefficient X n (realArcs X P) - coefficient X n P‖^2)
          ≤ A * (X : ℝ)^(11/4 : ℝ) := by
  obtain ⟨C, hC, hError⟩ := exponentialSum_error
  let A := C^2 * (8 + 4*C^2)
  have hA : 0 < A := by dsimp [A]; positivity
  have hCast : Tendsto (fun X : ℕ => (X : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  obtain ⟨G₀, hGeometry⟩ := eventually_arcScales 1
  have hLog := ((isLittleO_log_rpow_rpow_atTop (2 : ℝ) (by norm_num : 0 < (1/8 : ℝ))).comp_tendsto
    hCast).bound (by norm_num : (0 : ℝ) < 1/2)
  refine ⟨A, ?_⟩
  have hEventually : ∀ᶠ X : ℕ in atTop, ∀ P : ℝ,
      (X : ℝ)^(11/40 : ℝ) ≤ P → P ≤ (X : ℝ)^(3/10 : ℝ) →
        BinaryShiftCircle.baseArcs X ⊆ realArcs X P ∧
        (∑ n ∈ Finset.range (X + 1),
          ‖BinaryShiftCircle.arcCoefficient X n (realArcs X P) - coefficient X n P‖^2)
          ≤ A * (X : ℝ)^(11/4 : ℝ) := by
    filter_upwards [eventually_ge_atTop (64 : ℕ), eventually_ge_atTop G₀, hLog] with X hX hGX hLogX
    intro P hPlo hPhi
    let x : ℝ := X
    have hx₁ : 1 ≤ x := by
      change (1 : ℝ) ≤ X
      exact_mod_cast (show 1 ≤ X by omega)
    have hx : 0 < x := zero_lt_one.trans_le hx₁
    have hP₁ : 1 ≤ P := (Real.one_le_rpow hx₁ (by norm_num)).trans hPlo
    have hP : 0 ≤ P := zero_le_one.trans hP₁
    obtain ⟨hSmall, hQ₁, _⟩ := hGeometry X hGX P hPlo hPhi
    have hPpow : (x^(3/10 : ℝ))^2 = x^(3/5 : ℝ) := by
      rw [← Real.rpow_mul_natCast hx.le]
      congr 1
      norm_num
    have hRadius : P / x < 1/2 := (div_lt_iff₀ hx).mpr (by
      have hQ : (1 : ℝ) ≤ ((⌊P⌋₊ : ℕ) : ℝ) := by exact_mod_cast hQ₁
      have h := mul_le_mul_of_nonneg_left hQ (show 0 ≤ 2*P by positivity)
      linarith only [hSmall, h])
    refine ⟨(BinaryShiftCircle.baseArcs_subset X
      ((Nat.floor_le (Real.rpow_nonneg hx.le _)).trans hPlo)).trans
        (rationalArcs_subset_realArcs hx hRadius), ?_⟩
    let μ := haarAddCircle (T := (1 : ℝ))
    let F := primeMajorPart X P
    let V := exponentialSum X P
    let G := (circleArcs X P).indicator (fun _ => (1 : ℂ))
    let U := C * x^(39/50 : ℝ)
    have hU : 0 ≤ U := by dsimp [U]; positivity
    have hF : MemLp F 2 μ := primeMajorPart_memLp X P
    have hV : MemLp V 2 μ := exponentialSum_memLp X P
    have hG : MemLp G 2 μ :=
      (memLp_const (1 : ℂ)).indicator (measurable_circleArcs X P).nullMeasurableSet
    have herr (t : AddCircle (1 : ℝ)) : ‖F t - V t‖ ≤ U * ‖G t‖ :=
      hError X hX P hP hPhi hSmall t
    have hGBound (t : AddCircle (1 : ℝ)) : ‖G t‖ ≤ 1 := by
      by_cases ht : t ∈ circleArcs X P <;> simp [G, ht]
    have hlog : (Real.log x)^2 ≤ (1/2 : ℝ) * x^(1/8 : ℝ) := by
      change ‖Real.log x ^ (2 : ℝ)‖ ≤ (1/2 : ℝ) * ‖x ^ (1/8 : ℝ)‖ at hLogX
      simpa only [Real.rpow_ofNat, Real.norm_of_nonneg (sq_nonneg (Real.log x)),
        Real.norm_of_nonneg (Real.rpow_nonneg hx.le _)] using hLogX
    have hFenergy : (∫ t, ‖F t‖^2 ∂μ) ≤ x^(29/25 : ℝ) := calc
      _ ≤ ∫ t, ‖circlePrimeSum X t‖^2 ∂μ := by
        apply integral_mono_ae hF.norm.integrable_sq (circlePrimeSum_memLp X).norm.integrable_sq
        filter_upwards with t
        by_cases ht : t ∈ circleArcs X P
        · simp [F, primeMajorPart, ht]
        · simp [F, primeMajorPart, ht]
      _ ≤ 2*x*(Real.log x)^2 := circlePrimeSum_energy (by omega)
      _ ≤ 2*x*((1/2 : ℝ)*x^(1/8 : ℝ)) := mul_le_mul_of_nonneg_left hlog (by positivity)
      _ = x^(9/8 : ℝ) := by
        rw [show (9/8 : ℝ) = 1 + 1/8 by norm_num, Real.rpow_add hx, Real.rpow_one]
        ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx₁ (by norm_num)
    have hU2 : U^2 = C^2*x^(39/25 : ℝ) := by
      dsimp [U]
      rw [mul_pow, ← Real.rpow_mul_natCast hx.le]
      congr 1
      norm_num
    have hDenergy : (∫ t, ‖F t - V t‖^2 ∂μ) ≤ 2*C^2*x^(29/25 : ℝ) := calc
      _ ≤ U^2 * ∫ t, ‖G t‖^2 ∂μ := by
        rw [← integral_const_mul]
        apply integral_mono_ae (hF.sub hV).norm.integrable_sq (hG.norm.integrable_sq.const_mul _)
        filter_upwards with t
        change ‖F t - V t‖^2 ≤ U^2 * ‖G t‖^2
        simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (herr t) 2
      _ ≤ U^2 * (2*P^2/x) := mul_le_mul_of_nonneg_left (arcIndicator_energy hx hP hSmall) (sq_nonneg _)
      _ ≤ U^2 * (2*(x^(3/10 : ℝ))^2/x) := by
        gcongr
      _ = (2*C^2)*x^(29/25 : ℝ) := by
        have hWidth : 2*x^(3/5 : ℝ)/x = 2*x^(-2/5 : ℝ) := by
          rw [mul_div_assoc, ← Real.rpow_sub_one hx.ne', show (3/5-1 : ℝ) = -2/5 by norm_num]
        rw [hU2, hPpow, hWidth]
        calc
          _ = (2*C^2) * (x^(39/25 : ℝ)*x^(-2/5 : ℝ)) := by ring
          _ = _ := by rw [← Real.rpow_add hx]; norm_num
    have hsumEnergy : (∫ t, ‖F t + V t‖^2 ∂μ) ≤ (8+4*C^2)*x^(29/25 : ℝ) := calc
      _ ≤ ∫ t, 8*‖F t‖^2 + 2*‖F t - V t‖^2 ∂μ := by
        apply integral_mono_ae (hF.add hV).norm.integrable_sq
          ((hF.norm.integrable_sq.const_mul 8).add ((hF.sub hV).norm.integrable_sq.const_mul 2))
        filter_upwards with t
        change ‖F t + V t‖^2 ≤ 8*‖F t‖^2 + 2*‖F t - V t‖^2
        have hPoint : ‖F t + V t‖ ≤ 2*‖F t‖ + ‖F t - V t‖ := by
          rw [show F t + V t = 2*F t - (F t - V t) by ring]
          simpa only [norm_mul, show ‖(2 : ℂ)‖ = 2 by norm_num] using norm_sub_le (2*F t) (F t - V t)
        nlinarith only [pow_le_pow_left₀ (norm_nonneg _) hPoint 2,
          sq_nonneg (2*‖F t‖ - ‖F t - V t‖)]
      _ = 8*(∫ t, ‖F t‖^2 ∂μ) + 2*(∫ t, ‖F t - V t‖^2 ∂μ) := by
        simpa only [Pi.add_apply, Pi.sub_apply, integral_const_mul] using
          integral_add (hF.norm.integrable_sq.const_mul 8) ((hF.sub hV).norm.integrable_sq.const_mul 2)
      _ ≤ 8*x^(29/25 : ℝ) + 2*(2*C^2*x^(29/25 : ℝ)) :=
        add_le_add (mul_le_mul_of_nonneg_left hFenergy (by norm_num))
          (mul_le_mul_of_nonneg_left hDenergy (by norm_num))
      _ = _ := by ring
    have hBessel := finite_coefficient_error (Finset.range (X + 1)) F V hF hV
      (A := U) (Eventually.of_forall fun t => (herr t).trans (mul_le_of_le_one_right hU (hGBound t)))
    change (∑ n ∈ Finset.range (X + 1),
      ‖fourierCoeff (fun t => primeMajorPart X P t ^ 2) (n : ℤ) - coefficient X n P‖^2)
      ≤ U^2 * ∫ t, ‖F t + V t‖^2 ∂μ at hBessel
    simp_rw [primeMajorPart_coeff] at hBessel
    calc
      _ ≤ U^2 * ∫ t, ‖F t + V t‖^2 ∂μ := hBessel
      _ ≤ U^2 * ((8+4*C^2)*x^(29/25 : ℝ)) := mul_le_mul_of_nonneg_left hsumEnergy (sq_nonneg _)
      _ = A*x^(68/25 : ℝ) := by
        rw [hU2]
        calc
          _ = A*(x^(39/25 : ℝ)*x^(29/25 : ℝ)) := by dsimp [A]; ring
          _ = _ := by rw [← Real.rpow_add hx]; norm_num
      _ ≤ A*x^(11/4 : ℝ) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx₁ (by norm_num)) hA.le
  obtain ⟨N, hN⟩ := eventually_atTop.mp hEventually
  exact ⟨N, hA, hN⟩

end

end BinaryShiftMajorModel

private def freshExceptions (X : ℕ) : Finset ℕ :=
  GoldbachDensityTransfer.exceptionSet X \ GoldbachDensityTransfer.exceptionSet (X / 2)

/-- The widened major-arc coefficient only needs a linear lower bound outside
a set with at most a constant times `X^(3/4)` elements. The minor-arc moment
is supplied unconditionally by the verified Vaughan and Bessel estimates. -/
theorem binaryShiftExceptionUnion_of_majorArcFloor
    (hmajor : ∃ (c C : ℝ) (N : ℕ) (arcs : ℕ → Set ℝ), 0 < c ∧ 0 ≤ C ∧
      ∀ X : ℕ, N ≤ X →
        ((freshExceptions X).card : ℝ) ≤ C * (X : ℝ) ^ (3/4 : ℝ) ∨
          (MeasurableSet (arcs X) ∧ BinaryShiftCircle.baseArcs X ⊆ arcs X ∧
          ∃ D : Finset ℕ, (D.card : ℝ) ≤ C * (X : ℝ) ^ (3/4 : ℝ) ∧
            ∀ n : ℕ, X / 2 < n → n ≤ X → n % 2 = 0 → n ∉ D →
              c * (X : ℝ) ≤ (BinaryShiftCircle.arcCoefficient X n (arcs X)).re)) :
    ∃ X₀ : ℕ, ∀ X ≥ X₀, (shiftedExceptions X).card ^ 5 ≤ X ^ 4 := by
  classical
  obtain ⟨c, C, N, arcs, hc, _, hN⟩ := hmajor
  obtain ⟨M, hM⟩ := BinaryShiftCircle.minorMoment
  let L := max 2 (max N M)
  have hfresh (X : ℕ) (hX : L ≤ X) :
      ((freshExceptions X).card : ℝ) ≤
      (C + 1 / c^2) * (X : ℝ) ^ (3/4 : ℝ) := by
    have hXL : max 2 (max N M) ≤ X := hX
    have hPos : 0 < (X : ℝ) := by exact_mod_cast (show 0 < X by omega)
    rcases hN X (by omega) with hSmall | ⟨hA, hWide, D, hD, hFloor⟩
    · exact hSmall.trans <| mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_right (by positivity)) (Real.rpow_nonneg hPos.le _)
    let B := (Finset.range (X + 1)).filter
      (fun n => c * (X : ℝ) ≤ ‖BinaryShiftCircle.arcCoefficient X n (arcs X)ᶜ‖)
    have hB := BinaryShiftCircle.largeCoefficient_card_le (M := 1) hPos hc B (Finset.filter_subset _ _)
      (fun n hn => (Finset.mem_filter.mp hn).2) (by simpa only [one_mul] using hM X (by omega) _ hA hWide)
    have hsub : freshExceptions X ⊆ D ∪ B := by
      intro n hn
      obtain ⟨hin, hout⟩ := Finset.mem_sdiff.mp hn
      obtain ⟨hnRange, hex⟩ := Finset.mem_filter.mp hin
      have hnLe := Nat.le_of_lt_succ (Finset.mem_range.mp hnRange)
      have hnHalf : X / 2 < n := by
        by_contra! hh
        exact hout (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hh), hex⟩)
      by_cases hnD : n ∈ D
      · exact Finset.mem_union_left _ hnD
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hnRange,
          BinaryShiftCircle.minor_large_of_exception hA hex
            (hFloor n hnHalf hnLe hex.2.1 hnD)⟩)
    calc
      _ ≤ ((D ∪ B).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
      _ ≤ (D.card : ℝ) + (B.card : ℝ) := by exact_mod_cast Finset.card_union_le D B
      _ ≤ C * (X : ℝ) ^ (3/4 : ℝ) + (1 / c^2) * (X : ℝ) ^ (3/4 : ℝ) := add_le_add hD hB
      _ = _ := by ring
  obtain ⟨K, hK, hCount⟩ := GoldbachDensityTransfer.exceptionalCount_of_half_intervals
    (by norm_num : (0 : ℝ) < 3/4) L hfresh
  apply binaryShiftExceptionUnion_of_exceptionBound (α := 3/4) (by norm_num)
  refine ⟨K, 1, hK, fun X hX => ?_⟩
  have heq : unshiftedExceptions X = GoldbachDensityTransfer.exceptionSet X := by
    ext n
    unfold unshiftedExceptions GoldbachDensityTransfer.exceptionSet
    simp [GoldbachDensityTransfer.exceptional, representationCount]
  rw [heq]
  exact hCount X hX

/-- This form accepts the truncated prime sum from Pintz and also permits a
direct exception bound in the exceptional-zero case. -/
theorem binaryShiftExceptionUnion_of_truncatedMajorArcs {δ : ℝ} (hδ : 0 < δ)
    (hmajor : ∃ (c C : ℝ) (N : ℕ) (P : ℕ → ℝ), 0 < c ∧ 0 ≤ C ∧
      ∀ X : ℕ, N ≤ X →
        ((freshExceptions X).card : ℝ) ≤ C * (X : ℝ) ^ (3/4 : ℝ) ∨
          ((X : ℝ) ^ (11/40 : ℝ) ≤ P X ∧
          ∃ D : Finset ℕ, (D.card : ℝ) ≤ C * (X : ℝ) ^ (3/4 : ℝ) ∧
            ∀ n : ℕ, X / 2 < n → n ≤ X → n % 2 = 0 → n ∉ D →
              c * (X : ℝ) ≤ (BinaryShiftCircle.truncatedArcCoefficient X
                ⌊(X : ℝ) ^ (1 - δ)⌋₊ n (BinaryShiftCircle.rationalArcs X (P X))).re)) :
    ∃ X₀ : ℕ, ∀ X ≥ X₀, (shiftedExceptions X).card ^ 5 ≤ X ^ 4 := by
  obtain ⟨c, C, N, P, hc, hC, hN⟩ := hmajor
  obtain ⟨M, hLoss⟩ := BinaryShiftCircle.truncationLoss hδ (show 0 < c / 2 by positivity)
  apply binaryShiftExceptionUnion_of_majorArcFloor
  refine ⟨c / 2, C, max N M, fun X => BinaryShiftCircle.rationalArcs X (P X),
    by positivity, hC, ?_⟩
  intro X hX
  rcases hN X (le_trans (le_max_left _ _) hX) with hSmall | ⟨hP, D, hD, hFloor⟩
  · exact Or.inl hSmall
  · right
    have hA := BinaryShiftCircle.rationalArcs_measurable X (P X)
    refine ⟨hA, BinaryShiftCircle.baseArcs_subset X
      ((Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg X) (11/40 : ℝ))).trans hP),
      D, hD, ?_⟩
    intro n hnHalf hnLe hnEven hnD
    have hcost := Complex.re_le_norm (BinaryShiftCircle.truncatedArcCoefficient X
      ⌊(X : ℝ) ^ (1 - δ)⌋₊ n (BinaryShiftCircle.rationalArcs X (P X)) -
      BinaryShiftCircle.arcCoefficient X n (BinaryShiftCircle.rationalArcs X (P X)))
    rw [Complex.sub_re, norm_sub_rev] at hcost
    have hComparison := hcost.trans (hLoss X (le_trans (le_max_right _ _) hX) n _ hA)
    linarith only [hComparison, hFloor n hnHalf hnLe hnEven hnD]

/-- The remaining main-case estimate is a positive truncated major-arc
coefficient for targets whose contributing conductors have small lcm. -/
theorem binaryShiftExceptionUnion_of_conductorFloor {δ : ℝ} (hδ : 0 < δ)
    (hmajor : ∃ (c C : ℝ) (N K B : ℕ) (P : ℕ → ℝ) (R : ℕ → Finset ℕ),
      0 < c ∧ 0 ≤ C ∧ 0 < K ∧ ∀ X : ℕ, N ≤ X →
        ((freshExceptions X).card : ℝ) ≤ C * (X : ℝ) ^ (3/4 : ℝ) ∨
          ((X : ℝ) ^ (11/40 : ℝ) ≤ P X ∧ (R X).card ≤ B ∧
            ∀ n : ℕ, X / 2 < n → n ≤ X → n % 2 = 0 →
              ((((R X).filter fun r => r ∣ K * n).lcm id : ℕ) : ℝ) <
                (X : ℝ) ^ (1/4 : ℝ) →
              c * (X : ℝ) ≤ (BinaryShiftCircle.truncatedArcCoefficient X
                ⌊(X : ℝ) ^ (1 - δ)⌋₊ n (BinaryShiftCircle.rationalArcs X (P X))).re)) :
    ∃ X₀ : ℕ, ∀ X ≥ X₀, (shiftedExceptions X).card ^ 5 ≤ X ^ 4 := by
  classical
  obtain ⟨c, C, N, K, B, P, R, hc, hC, hK, hN⟩ := hmajor
  let M := (2 : ℝ)^B * ((K : ℝ) + 1)
  apply binaryShiftExceptionUnion_of_truncatedMajorArcs hδ
  refine ⟨c, max C M, max 1 N, P, hc, hC.trans (le_max_left _ _), ?_⟩
  intro X hX
  have hX₁ := (le_max_left 1 N).trans hX
  rcases hN X ((le_max_right 1 N).trans hX) with hSmall | ⟨hP, hR, hFloor⟩
  · exact Or.inl (hSmall.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.rpow_nonneg (Nat.cast_nonneg X) _)))
  · right
    let D := BinaryShiftCircle.conductorOutliers X K (R X)
    have hD : (D.card : ℝ) ≤ max C M * (X : ℝ) ^ (3/4 : ℝ) := calc
      _ ≤ (2 : ℝ)^(R X).card * ((K : ℝ) + 1) * (X : ℝ) ^ (3/4 : ℝ) :=
        BinaryShiftCircle.conductorOutliers_card_le X K (R X) hX₁ hK
      _ ≤ M * (X : ℝ) ^ (3/4 : ℝ) := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hR) (by positivity))
        (Real.rpow_nonneg (Nat.cast_nonneg X) _)
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (Nat.cast_nonneg X) _)
    refine ⟨hP, D, hD, ?_⟩
    intro n hnHalf hnLe hnEven hnD
    exact hFloor n hnHalf hnLe hnEven (BinaryShiftCircle.small_lcm_of_not_mem_conductorOutliers hnLe hnD)

private def quadraticZeroFree (X : ℕ) (h : ℝ) : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), q ≤ X → χ ^ 2 = 1 →
    ∀ β : ℝ, 1 - h / Real.log (X : ℝ) ≤ β → β < 1 →
      DirichletCharacter.LFunction χ (β : ℂ) ≠ 0

/-- The verified quadratic-character zero gap also applies on the scale
of the prime-sum cutoff, simultaneously for all moduli up to that cutoff. -/
theorem quadraticZeroFree_at_cutoff :
    ∃ h : ℝ, 0 < h ∧ ∀ X : ℕ, 2 ≤ X → quadraticZeroFree X h := by
  obtain ⟨c, hc, hzero⟩ := PEqualNP.Outside.L_goldbach_frontier_no_siegel_zero
  refine ⟨c / 4, by positivity, ?_⟩
  intro X hX q _ χ hq hχ β hβ hβOne
  have hX₂ : (2 : ℝ) ≤ X := by exact_mod_cast hX
  have hqX : (q : ℝ) ≤ X := by exact_mod_cast hq
  have hlogX : 0 < Real.log (X : ℝ) := Real.log_pos (by linarith)
  have hlogq : 0 < Real.log ((q : ℝ) + 2) :=
    Real.log_pos (by linarith [Nat.cast_nonneg (α := ℝ) q])
  have hsize : (q : ℝ) + 2 ≤ (X : ℝ)^2 := by
    nlinarith only [hqX, mul_nonneg (show 0 ≤ (X : ℝ) - 2 by linarith) (show 0 ≤ (X : ℝ) + 1 by positivity)]
  have hlogLe : Real.log ((q : ℝ) + 2) ≤ 2 * Real.log (X : ℝ) := by
    simpa only [Real.log_pow, Nat.cast_ofNat] using Real.log_le_log (by positivity) hsize
  have hgap : c / 4 / Real.log (X : ℝ) < c / Real.log ((q : ℝ) + 2) := by
    rw [div_div]
    exact (div_lt_div_of_pos_left hc (show 0 < 2 * Real.log (X : ℝ) by positivity)
      (show 2 * Real.log (X : ℝ) < 4 * Real.log (X : ℝ) by linarith)).trans_le
      (div_le_div_of_nonneg_left hc.le hlogq hlogLe)
  exact hzero q χ β hχ (by linarith) hβOne

/-- Only the small-lcm major-arc floor in the zero-free case remains as input.
The quadratic zero gap supplies the hypothesis on every sufficiently large window. -/
theorem binaryShiftExceptionUnion_of_zeroFreeMajorArcs
    (hmajor : ∀ h : ℝ, 0 < h →
      ∃ (δ c : ℝ) (N K B : ℕ) (P : ℕ → ℝ) (R : ℕ → Finset ℕ),
        0 < δ ∧ 0 < c ∧ 0 < K ∧ ∀ X : ℕ, N ≤ X → quadraticZeroFree X h →
          (X : ℝ) ^ (11/40 : ℝ) ≤ P X ∧ (R X).card ≤ B ∧
            ∀ n : ℕ, X / 2 < n → n ≤ X → n % 2 = 0 →
              ((((R X).filter fun r => r ∣ K * n).lcm id : ℕ) : ℝ) <
                (X : ℝ) ^ (1/4 : ℝ) →
              c * (X : ℝ) ≤ (BinaryShiftCircle.truncatedArcCoefficient X
                ⌊(X : ℝ) ^ (1 - δ)⌋₊ n (BinaryShiftCircle.rationalArcs X (P X))).re) :
    ∃ X₀ : ℕ, ∀ X ≥ X₀, (shiftedExceptions X).card ^ 5 ≤ X ^ 4 := by
  obtain ⟨h, hh, hzero⟩ := quadraticZeroFree_at_cutoff
  obtain ⟨δ, c, N, K, B, P, R, hδ, hc, hK, hFloor⟩ := hmajor h hh
  apply binaryShiftExceptionUnion_of_conductorFloor hδ
  refine ⟨c, 0, max 2 N, K, B, P, R, hc, le_rfl, hK, ?_⟩
  intro X hX
  exact Or.inr (hFloor X ((le_max_right _ _).trans hX) (hzero X ((le_max_left _ _).trans hX)))

/-- The frozen claim follows from a lower bound for the explicit model
on the small-lcm classes. The Fourier coefficient error, minor arcs,
and discarded classes are already controlled by the same power bound. -/
theorem binaryShiftExceptionUnion_of_explicitMajorModel
    (hmajor : ∀ h : ℝ, 0 < h →
      ∃ (c : ℝ) (N K B : ℕ) (P : ℕ → ℝ) (R : ℕ → Finset ℕ),
        0 < c ∧ 0 < K ∧ ∀ X : ℕ, N ≤ X → quadraticZeroFree X h →
          (X : ℝ) ^ (11/40 : ℝ) ≤ P X ∧ P X ≤ (X : ℝ) ^ (3/10 : ℝ) ∧ (R X).card ≤ B ∧
            ∀ n : ℕ, X / 2 < n → n ≤ X → n % 2 = 0 →
              ((((R X).filter fun r => r ∣ K * n).lcm id : ℕ) : ℝ) < (X : ℝ) ^ (1/4 : ℝ) →
              c * (X : ℝ) ≤ (BinaryShiftMajorModel.coefficient X n (P X)).re) :
    ∃ X₀ : ℕ, ∀ X ≥ X₀, (shiftedExceptions X).card ^ 5 ≤ X ^ 4 := by
  classical
  obtain ⟨h, hh, hZero⟩ := quadraticZeroFree_at_cutoff
  obtain ⟨c, N, K, B, P, R, hc, hK, hFloor⟩ := hmajor h hh
  obtain ⟨A, M, hA, hM⟩ := BinaryShiftMajorModel.coefficientMoment
  let D := (2 : ℝ)^B * ((K : ℝ) + 1)
  let g := fun X => BinaryShiftMajorModel.realArcs X (P X)
  have hsmall : 0 < c/2 := by positivity
  apply binaryShiftExceptionUnion_of_majorArcFloor
  refine ⟨c/2, D + A/(c/2)^2, max 2 (max N M), g, hsmall, by dsimp [D]; positivity, ?_⟩
  intro X hX
  have hX₂ := (le_max_left 2 (max N M)).trans hX
  have hN : N ≤ X := (le_max_left N M).trans ((le_max_right 2 (max N M)).trans hX)
  have hMX : M ≤ X := (le_max_right N M).trans ((le_max_right 2 (max N M)).trans hX)
  obtain ⟨hPlo, hPhi, hR, hMajor⟩ := hFloor X hN (hZero X hX₂)
  obtain ⟨hSubset, hMoment⟩ := hM X hMX (P X) hPlo hPhi
  let L := BinaryShiftCircle.conductorOutliers X K (R X)
  let f := fun n => BinaryShiftCircle.arcCoefficient X n (g X) - BinaryShiftMajorModel.coefficient X n (P X)
  let J := (Finset.range (X + 1)).filter fun n => c/2 * (X : ℝ) ≤ ‖f n‖
  have hXPos : 0 < (X : ℝ) := by exact_mod_cast (show 0 < X by omega)
  have hL : (L.card : ℝ) ≤ D * (X : ℝ) ^ (3/4 : ℝ) := calc
    _ ≤ (2 : ℝ)^(R X).card * ((K : ℝ) + 1) * (X : ℝ) ^ (3/4 : ℝ) :=
      BinaryShiftCircle.conductorOutliers_card_le X K (R X) (by omega) hK
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hXPos.le _)
      exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hR) (by positivity)
  have hJ := BinaryShiftCircle.largeCoefficient_card_le (f := f) hXPos hsmall J
    (Finset.filter_subset _ _) (fun n hn => (Finset.mem_filter.mp hn).2) hMoment
  have hUnion : ((L ∪ J).card : ℝ) ≤ (D + A/(c/2)^2) * (X : ℝ) ^ (3/4 : ℝ) :=
    (show ((L ∪ J).card : ℝ) ≤ (L.card : ℝ) + J.card by exact_mod_cast Finset.card_union_le L J).trans
      ((add_le_add hL hJ).trans_eq (by ring))
  refine Or.inr ⟨BinaryShiftMajorModel.measurable_realArcs X (P X), hSubset, L ∪ J, hUnion, ?_⟩
  intro n hnHalf hnX hnEven hn
  have hnL : n ∉ L := fun h => hn (Finset.mem_union_left _ h)
  have hnJ : ‖f n‖ < c/2 * (X : ℝ) := by
    by_contra! h
    exact hn (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), h⟩))
  have hModel := hMajor n hnHalf hnX hnEven (BinaryShiftCircle.small_lcm_of_not_mem_conductorOutliers hnX hnL)
  have hReal := Complex.re_le_norm (-f n)
  rw [Complex.neg_re, norm_neg] at hReal
  change -((BinaryShiftCircle.arcCoefficient X n (g X)).re -
    (BinaryShiftMajorModel.coefficient X n (P X)).re) ≤ ‖f n‖ at hReal
  linarith only [hModel, hnJ, hReal]

/-- The analytic input is the signed contribution of the Dirichlet zero
profiles on the small-lcm classes. The principal profiles and all
Fourier approximation losses are supplied by the preceding estimates. -/
theorem binaryShiftExceptionUnion_of_zeroCorrections
    (hzeros : ∀ h : ℝ, 0 < h →
      ∃ (η : ℝ) (N K B : ℕ) (P : ℕ → ℝ) (R : ℕ → Finset ℕ),
        0 < η ∧ 0 < K ∧ ∀ X : ℕ, N ≤ X → quadraticZeroFree X h →
          (X : ℝ)^(11/40 : ℝ) ≤ P X ∧ P X ≤ (X : ℝ)^(3/10 : ℝ) ∧ (R X).card ≤ B ∧
            ∀ n : ℕ, X/2 < n → n ≤ X → n % 2 = 0 →
              ((((R X).filter fun r => r ∣ K * n).lcm id : ℕ) : ℝ) < (X : ℝ)^(1/4 : ℝ) →
              -(1 - η) * (BinaryShiftMajorModel.principalCoefficient X n (P X)).re ≤
                (BinaryShiftMajorModel.coefficient X n (P X) -
                BinaryShiftMajorModel.principalCoefficient X n (P X)).re) :
    ∃ X₀ : ℕ, ∀ X ≥ X₀, (shiftedExceptions X).card ^ 5 ≤ X ^ 4 := by
  obtain ⟨M, Q₀, hMain⟩ := BinaryShiftMajorModel.principalCoefficient_floor
  obtain ⟨G, hScales⟩ := BinaryShiftMajorModel.eventually_arcScales Q₀
  apply binaryShiftExceptionUnion_of_explicitMajorModel
  intro h hh
  obtain ⟨η, N, K, B, P, R, hη, hK, hZero⟩ := hzeros h hh
  refine ⟨η/16, max N (max G M), K, B, P, R, by positivity, hK, ?_⟩
  intro X hX hNoSiegel
  obtain ⟨hPlo, hPhi, hR, hBound⟩ := hZero X (by omega) hNoSiegel
  obtain ⟨hSmall, hQ₀, hPower⟩ := hScales X (by omega) (P X) hPlo hPhi
  refine ⟨hPlo, hPhi, hR, ?_⟩
  intro n hnHalf hn hEven hLcm
  have hm := hMain X (by omega) (P X) n hPlo hSmall hQ₀ (hn.trans hPower) hnHalf hn
    (Nat.even_iff.mpr hEven)
  have hz := hBound n hnHalf hn hEven hLcm
  rw [Complex.sub_re] at hz
  calc
    _ = η * ((X : ℝ)/16) := by ring
    _ ≤ η * (BinaryShiftMajorModel.principalCoefficient X n (P X)).re :=
      mul_le_mul_of_nonneg_left hm hη.le
    _ ≤ _ := by linarith only [hz]

/-- The verified Dirichlet GRH estimate gives the registered conclusion at
the ordinary exception exponent `1/2 + 1/4`. -/
theorem binaryShiftExceptionUnion_of_dirichletGRH
    (hGRH : ∀ (Q : ℕ) [NeZero Q] (χ : DirichletCharacter ℂ Q) (s : ℂ),
      0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2) :
    ∃ X₀ : ℕ, ∀ X ≥ X₀, (shiftedExceptions X).card ^ 5 ≤ X ^ 4 := by
  apply binaryShiftExceptionUnion_of_exceptionBound (α := 3/4) (by norm_num)
  obtain ⟨C, N, hC, hcount⟩ :=
    PEqualNP.Outside.L_goldbach_grh_goldbach_exception_density hGRH (1 / 4) (by norm_num)
  refine ⟨C, N, hC, ?_⟩
  intro X hX
  have estimate := hcount X hX
  rw [show (1 / 2 : ℝ) + 1 / 4 = 3 / 4 by norm_num] at estimate
  exact estimate

/-- The unconditional Estermann bound supplies every fixed logarithmic saving
for the same shifted exceptional set. -/
theorem binaryShiftExceptions_card_le_polylog (A : ℝ) (hA : 0 < A) :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      ((shiftedExceptions X).card : ℝ) ≤
        (2 / Real.log 2) * (X : ℝ) * Real.log (X : ℝ) ^ (-A) := by
  obtain ⟨N, hcount⟩ := EstermannAlmostAllPolylog.1 (A + 1) (by linarith)
  have hEven (Y : ℕ) : unshiftedExceptions Y =
      (Finset.range (Y + 1)).filter (fun n => 4 ≤ n ∧ Even n ∧ representationCount n = 0) := by
    ext n
    simp only [unshiftedExceptions, Finset.mem_filter, Nat.even_iff]
  refine ⟨max 8 N, ?_⟩
  intro X hX
  have hXPos : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogX : 0 < Real.log (X : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  let L := Nat.log 2 X / 2
  have hdouble : ((unshiftedExceptions (2 * X)).card : ℝ) ≤
      2 * (X : ℝ) * Real.log (2 * (X : ℝ)) ^ (-(A + 1)) := by
    rw [hEven]
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using! hcount (2 * X) (by omega)
  have hlogLe : Real.log (X : ℝ) ≤ Real.log (2 * (X : ℝ)) :=
    Real.log_le_log hXPos (by linarith)
  have hpower : Real.log (2 * (X : ℝ)) ^ (-(A + 1)) ≤
      Real.log (X : ℝ) ^ (-(A + 1)) :=
    Real.rpow_le_rpow_of_nonpos hlogX hlogLe (by linarith)
  have habsorb : Real.log (X : ℝ) * Real.log (X : ℝ) ^ (-(A + 1)) =
      Real.log (X : ℝ) ^ (-A) := calc
    _ = Real.log (X : ℝ) ^ (1 : ℝ) * Real.log (X : ℝ) ^ (-(A + 1)) := by rw [Real.rpow_one]
    _ = _ := by rw [← Real.rpow_add hlogX, show 1 + -(A + 1) = -A by ring]
  calc
    _ ≤ (L : ℝ) * ((unshiftedExceptions (2 * X)).card : ℝ) := by
      exact_mod_cast shiftedExceptions_card_le X (show 8 ≤ X by omega)
    _ ≤ (L : ℝ) * (2 * (X : ℝ) * Real.log (2 * (X : ℝ)) ^ (-(A + 1))) :=
      mul_le_mul_of_nonneg_left hdouble (Nat.cast_nonneg _)
    _ ≤ (Real.log (X : ℝ) / Real.log 2) * (2 * (X : ℝ) * Real.log (X : ℝ) ^ (-(A + 1))) :=
      mul_le_mul (shift_count_le_log_div X (by omega))
        (mul_le_mul_of_nonneg_left hpower (by positivity))
        (mul_nonneg (by positivity) (Real.rpow_nonneg (hlogX.le.trans hlogLe) _))
        (div_nonneg hlogX.le hlogTwo.le)
    _ = (2 / Real.log 2) * (X : ℝ) * (Real.log (X : ℝ) * Real.log (X : ℝ) ^ (-(A + 1))) :=
      by ring
    _ = _ := by rw [habsorb]

end Conjectures.Goldbach

namespace Conjectures.Goldbach.BinaryShiftMajorModel
/-- Choose one admissible arc cutoff at which every included conductor
lcm is separated from the cutoff by a power of X. The exponent depends
only on the number of conductors. -/
theorem conductor_lcm_arc_gap (B : ℕ) : ∃ δ : ℝ, 0 < δ ∧ ∀ (X : ℝ), 1 < X →
    ∀ R : Finset ℕ, R.card ≤ B → ∃ P : ℝ, X^(11/40:ℝ) ≤ P ∧ P ≤ X^(3/10:ℝ) ∧
      ∀ r ∈ R, ∀ s ∈ R, (Nat.lcm r s : ℝ) ≤ P → (Nat.lcm r s : ℝ)*X^δ ≤ P := by
  classical
  let M := B*B
  let δ : ℝ := (1/40)/((M:ℝ)+1)
  have hd : 0 < δ := by dsimp [δ]; positivity
  refine ⟨δ, hd, ?_⟩
  intro X hX R hR
  let S := (R ×ˢ R).image (fun p : ℕ × ℕ => Nat.lcm p.1 p.2)
  have hS : S.card ≤ M := Finset.card_image_le.trans (by rw [Finset.card_product]; exact Nat.mul_le_mul hR hR)
  let t := fun j : ℕ => X^((11/40:ℝ)+(j:ℝ)*δ)
  have mono : Monotone t := fun i j hij => Real.rpow_le_rpow_of_exponent_le hX.le
    (add_le_add_right (mul_le_mul_of_nonneg_right (by exact_mod_cast hij) hd.le) _)
  have step (j : ℕ) : t j*X^δ = t (j+1) := by
    dsimp only [t]
    rw [← Real.rpow_add (zero_lt_one.trans hX)]
    congr 1
    push_cast
    ring
  have free : ∃ j : Fin (M+1), ∀ d ∈ S, ¬(t j < (d:ℝ) ∧ (d:ℝ) ≤ t (j.val+1)) := by
    by_contra! hfill
    choose d hm hlo hhi using hfill
    let f (j : Fin (M+1)) : ↥S := ⟨d j, hm j⟩
    have distinct {i j : Fin (M+1)} (hij : i.val < j.val) : f i ≠ f j := by
      intro h
      have eqv : d i = d j := congrArg Subtype.val h
      have le := (hhi i).trans (mono (by omega : i.val+1 ≤ j.val))
      rw [eqv] at le
      exact (hlo j).not_ge le
    have hinj : Function.Injective f := by
      intro i j h
      apply Fin.ext
      rcases lt_trichotomy i.val j.val with hlt | heq | hgt
      · exact (distinct hlt h).elim
      · exact heq
      · exact (distinct hgt h.symm).elim
    have hc : M+1 ≤ S.card := by simpa using Fintype.card_le_of_injective f hinj
    omega
  obtain ⟨j, hgap⟩ := free
  refine ⟨t (j.val+1), ?_, ?_, ?_⟩
  · simpa [t] using mono (Nat.zero_le (j.val+1))
  · apply (mono (show j.val+1 ≤ M+1 by have := j.isLt; omega)).trans
    dsimp only [t]
    apply Real.rpow_le_rpow_of_exponent_le hX.le
    have e : ((M:ℝ)+1)*δ = 1/40 := by dsimp [δ]; field_simp
    push_cast
    rw [e]
    norm_num
  · intro r hr s hs hle
    have hm : Nat.lcm r s ∈ S := Finset.mem_image.mpr ⟨(r,s), Finset.mem_product.mpr ⟨hr,hs⟩, rfl⟩
    have hlo : (Nat.lcm r s : ℝ) ≤ t j := le_of_not_gt (fun h => hgap _ hm ⟨h,hle⟩)
    exact (mul_le_mul_of_nonneg_right hlo (Real.rpow_nonneg (zero_lt_one.trans hX).le _)).trans_eq (step j)

end Conjectures.Goldbach.BinaryShiftMajorModel

section
open Finset Complex MeasureTheory Filter
open scoped BigOperators
noncomputable section
namespace Conjectures.Goldbach.BinaryShiftMajorModel

/-- Bound the error of a finite denominator sum relative to its infinite
main term. The denominator index is the multiplier of the conductor lcm. -/
private theorem weighted_cutoff_error {c I : ℕ → ℂ} {V : ℂ} {J N : ℕ} {a b : ℝ}
    (hc : Summable (fun k => ‖c k‖)) (hc0 : c 0 = 0) (hJN : J ≤ N) (ha : 0 ≤ a)
    (low : ∀ k : ℕ, 0 < k → k < J → ‖I k - V‖ ≤ a)
    (high : ∀ k : ℕ, J ≤ k → k < N → 0 < k → ‖I k - V‖ ≤ b) (missing : ‖V‖ ≤ b) :
    ‖(∑ k ∈ range N, c k*I k) - (∑' k, c k)*V‖ ≤
      a*(∑' k, ‖c k‖) + b*(∑' k, if J ≤ k then ‖c k‖ else 0) := by
  classical
  let f := fun k : ℕ => if k < N then c k*I k else 0
  have hf : Summable f := summable_of_ne_finset_zero (s := range N) (fun k hk => ite_eq_right (fun h => hk (mem_range.mpr h)))
  have hg := (summable_norm_iff.mp hc).mul_right V
  have he : (∑ k ∈ range N, c k*I k) - (∑' k, c k)*V = ∑' k, (f k-c k*V) := by
    rw [hf.tsum_sub hg, tsum_mul_right, tsum_eq_sum (s := range N) (fun k hk => ite_eq_right (fun h => hk (mem_range.mpr h)) : ∀ k ∉ range N, f k = 0)]
    congr 1
    exact sum_congr rfl (fun k hk => (ite_eq_left (mem_range.mp hk)).symm)
  let tail := fun k : ℕ => if J ≤ k then ‖c k‖ else 0
  have ht : Summable tail := Summable.of_nonneg_of_le
    (fun k => by dsimp only [tail]; split <;> positivity)
    (fun k => by dsimp only [tail]; split <;> first | rfl | positivity) hc
  have hmaj := (hc.mul_left a).add (ht.mul_left b)
  have hbound (k : ℕ) : ‖f k-c k*V‖ ≤ a*‖c k‖+b*tail k := by
    by_cases h0 : k = 0
    · subst k; simp [f, tail, hc0]
    have hk0 : 0 < k := Nat.pos_of_ne_zero h0
    by_cases hk : k < J
    · simp only [f, ite_eq_left (hk.trans_le hJN), ← mul_sub, norm_mul, tail, ite_eq_right (not_le_of_gt hk),
        mul_zero, add_zero, mul_comm a]
      exact mul_le_mul_of_nonneg_left (low k hk0 hk) (norm_nonneg _)
    · have hj : J ≤ k := Nat.le_of_not_gt hk
      rw [show tail k = ‖c k‖ by simp [tail, hj]]
      apply (le_add_of_nonneg_left (mul_nonneg ha (norm_nonneg (c k))) : b*‖c k‖ ≤ _).trans'
      by_cases hn : k < N
      · simp only [f, ite_eq_left hn, ← mul_sub, norm_mul, mul_comm b]
        exact mul_le_mul_of_nonneg_left (high k hj hn hk0) (norm_nonneg _)
      · simp only [f, ite_eq_right hn, zero_sub, norm_neg, norm_mul, mul_comm b]
        exact mul_le_mul_of_nonneg_left missing (norm_nonneg _)
  have hnorm := (hf.sub hg).norm
  rw [he]
  apply (norm_tsum_le_tsum_norm hnorm).trans
  apply (hnorm.tsum_le_tsum hbound hmaj).trans_eq
  rw [Summable.tsum_add (hc.mul_left a) (ht.mul_left b), tsum_mul_left, tsum_mul_left]

end Conjectures.Goldbach.BinaryShiftMajorModel
end
end

section
open Complex DirichletCharacter MeasureTheory Finset GoldbachTwistedMellin
open scoped Interval
noncomputable section
namespace Conjectures.Goldbach.BinaryShiftMajorModel
open TwistedGoldbachSingularSeries TwistedGoldbachCoefficientProduct

/-- A fixed bounded-height residue pair can be replaced, after summing its
actual arcs over ambient denominators, by the complete primitive singular
series times its beta factor. The lower denominators use Fourier decay and
the upper denominators use the normalized Euler-product tail. -/
theorem residuePair_denominator_sum {T δ : ℝ} (hT : 0 ≤ T) (hδ : 0 < δ) :
    ∃ A D : ℝ, 0 < A ∧ 0 < D ∧ ∀ (r s : ℕ) [NeZero r] [NeZero s]
      (α : DirichletCharacter ℂ r) (β : DirichletCharacter ℂ s),
      α.IsPrimitive → β.IsPrimitive → ∀ (m n J Q : ℕ) (P : ℝ) (z t : Option ℂ),
      let X : ℝ := (m+2 : ℕ)
      let L := Nat.lcm r s
      let a := z.getD 1
      let b := t.getD 1
      let S := ∑' d, TwistedGoldbachSingularSeries.coefficient α β n d
      let w (j : ℕ) := P/(((L*j : ℕ):ℝ)*X)
      0 < n → n ≤ m+2 → Even n → 0 < P → 2*P ≤ X → (L*Q : ℕ) ≤ P →
      J ≤ Q+1 → X^δ ≤ (J:ℝ) →
      5/8 ≤ a.re → a.re ≤ 1 → |a.im| ≤ T → 5/8 ≤ b.re → b.re ≤ 1 → |b.im| ≤ T →
      ‖(∑ j ∈ range (Q+1), TwistedGoldbachSingularSeries.coefficient α β n (L*j) *
          ∫ u in -(w j)..w j, phase (-2*Real.pi*(n:ℝ)) u * (residueProfile m z u * residueProfile m t u)) -
        S*((n:ℂ)^(a+b-1)*Complex.betaIntegral a b)‖ ≤
        ‖S‖*(A*(2*P + (L*J : ℕ)*X/P) + D*(X/(X^(δ/2)))) := by
  classical
  obtain ⟨C, hC, kernel⟩ := residuePair_arc_uniform hT
  obtain ⟨D, hD, tail⟩ := TwistedGoldbachDenominatorTail.power_cutoff hδ
  let B := ‖Complex.betaIntegral ((5/8:ℝ):ℂ) ((5/8:ℝ):ℂ)‖
  have hB : 0 ≤ B := norm_nonneg _
  refine ⟨4*C, (2*C+B)*D, by positivity, by positivity, ?_⟩
  intro r s _ _ α β hα hβ m n J Q P z t X L a b S w hn hnX he hP hPX hQ hJ hcut ha ha' haz hb hb' hbt
  let c := TwistedGoldbachSingularSeries.coefficient α β n
  let V := (n:ℂ)^(a+b-1)*Complex.betaIntegral a b
  let I (j : ℕ) := ∫ u in -(w j)..w j, phase (-2*Real.pi*(n:ℝ)) u * (residueProfile m z u * residueProfile m t u)
  let E := C*(2*P + ((L*J : ℕ):ℝ)*X/P)
  let F := (2*C+B)*X
  have hX1 : 1 ≤ X := by dsimp only [X]; exact_mod_cast (show 1 ≤ m+2 by omega)
  have hX := zero_lt_one.trans_le hX1
  have hL : 0 < L := Nat.lcm_pos (NeZero.pos r) (NeZero.pos s)
  have hnR : 1 ≤ (n:ℝ) := by exact_mod_cast hn
  have hn0 := zero_lt_one.trans_le hnR
  have hnB : (n:ℝ) < (m+3 : ℕ) := by exact_mod_cast (show n < m+3 by omega)
  have hBF : ((m+3 : ℕ):ℝ) ≤ 2*X := by dsimp only [X]; exact_mod_cast (show m+3 ≤ 2*(m+2) by omega)
  have hV : ‖V‖ ≤ F := by
    have hpow : ‖(n:ℂ)^(a+b-1)‖ ≤ n := by
      rw [show (n:ℂ) = ((n:ℝ):ℂ) from rfl, Complex.norm_cpow_eq_rpow_re_of_pos hn0, sub_re, add_re, one_re]
      simpa using Real.rpow_le_rpow_of_exponent_le hnR (show a.re+b.re-1 ≤ 1 by linarith only [ha',hb'])
    have hbeta : ‖Complex.betaIntegral a b‖ ≤ B := BinaryShiftCircle.norm_betaIntegral_le_diagonal
      (by norm_num : 0 < (5/8:ℝ)) ha hb
    calc
      _ = ‖(n:ℂ)^(a+b-1)‖ * ‖Complex.betaIntegral a b‖  := norm_mul ..
      _ ≤ (n:ℝ)*B := mul_le_mul hpow hbeta (norm_nonneg _) hn0.le
      _ ≤ X*B := mul_le_mul_of_nonneg_right (by dsimp only [X]; exact_mod_cast hnX) hB
      _ ≤ F := by dsimp only [F]; nlinarith only [mul_nonneg hC.le hX.le]
  have base (k : ℕ) (hk : 0 < k) :
      ‖I k - V‖ ≤ C*(2*P + ((L*k : ℕ):ℝ)*X/P) := by
    have hq : (1:ℝ) ≤ (L*k : ℕ) := by exact_mod_cast Nat.mul_pos hL hk
    have hden : 0 < ((L*k : ℕ):ℝ)*X := mul_pos (zero_lt_one.trans_le hq) hX
    have hdenX : X ≤ ((L*k : ℕ):ℝ)*X := le_mul_of_one_le_left hX.le hq
    have hw : 0 < w k := div_pos hP hden
    have hw' : w k ≤ 1/2 := (div_le_iff₀ hden).mpr (by linarith only [hPX,hdenX])
    have hil := kernel m z t n (w k) hn0 hnB hw hw' ha ha' haz hb hb' hbt
    have hfour : w k * ((m+3 : ℕ):ℝ) ≤ 2*P := by
      calc
        _ ≤ (P/X) * (2*X) := mul_le_mul (div_le_div_of_nonneg_left hP.le hX hdenX) hBF
          (Nat.cast_nonneg _) (div_nonneg hP.le hX.le)
        _ = _ := by field_simp
    have invw : 1/w k = ((L*k : ℕ):ℝ)*X/P := by dsimp only [w]; rw [one_div_div]
    exact hil.trans (mul_le_mul_of_nonneg_left (add_le_add hfour invw.le) hC.le)
  have low (k : ℕ) (hk : 0 < k) (hkJ : k < J) : ‖I k-V‖ ≤ E := by
    apply (base k hk).trans
    apply mul_le_mul_of_nonneg_left _ hC.le
    exact add_le_add_right (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
      (by exact_mod_cast Nat.mul_le_mul_left L hkJ.le) hX.le) hP.le) _
  have high (k : ℕ) (_ : J ≤ k) (hkQ : k < Q+1) (hk : 0 < k) : ‖I k-V‖ ≤ F := by
    have hq : ((L*k : ℕ):ℝ) ≤ P :=
      (show ((L*k : ℕ):ℝ) ≤ (L*Q : ℕ) by exact_mod_cast Nat.mul_le_mul_left L (Nat.le_of_lt_succ hkQ)).trans hQ
    have hq' : ((L*k : ℕ):ℝ)*X/P ≤ X :=
      (div_le_iff₀ hP).mpr (by simpa only [mul_comm X P] using mul_le_mul_of_nonneg_right hq hX.le)
    calc
      _ ≤ C*(2*P+((L*k : ℕ):ℝ)*X/P) := base k hk
      _ ≤ C*(X+X) := mul_le_mul_of_nonneg_left (add_le_add hPX hq') hC.le
      _ ≤ F := by dsimp only [F]; nlinarith only [mul_nonneg hB hX.le]
  have hinj : Function.Injective (fun k : ℕ => L*k) := fun i j hij => Nat.eq_of_mul_eq_mul_left hL hij
  have habs : Summable (fun k => ‖c (L*k)‖) := (summable_coefficients α β n hn).comp_injective hinj
  have hsupp {d : ℕ} (hd : c d ≠ 0) : d ∈ Set.range (fun k : ℕ => L*k) := by
    have hl : L ∣ d := Classical.byContradiction (fun h => hd (off_level α β n d h))
    obtain ⟨k,hk⟩ := hl
    exact ⟨k,hk.symm⟩
  have hsum : (∑' k, c (L*k)) = S := hinj.tsum_eq (fun _ hd => hsupp hd)
  have hnorm : (∑' k, ‖c (L*k)‖) ≤ 4*‖S‖ := by
    rw [hinj.tsum_eq (f := fun d => ‖c d‖) (fun d hd => hsupp (fun h => hd (by simp [h])))]
    rw [show (∑' d, ‖c d‖) = ‖S‖*∏' p : ℕ, correction (L*n) p from absolute_euler_product hα hβ n hn he]
    simpa only [mul_comm (4:ℝ)] using mul_le_mul_of_nonneg_left (correction_product_le_four (L*n)) (norm_nonneg S)
  have hc0 : c (L*0) = 0 := by simp [c, TwistedGoldbachSingularSeries.coefficient]
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hF : 0 ≤ F := by dsimp only [F]; positivity
  have h := weighted_cutoff_error habs hc0 hJ hE low high hV
  have htail := tail r s α β hα hβ n (m+2) J hn he hnX hcut
  rw [hsum] at h
  apply h.trans
  apply (add_le_add (mul_le_mul_of_nonneg_left hnorm hE) (mul_le_mul_of_nonneg_left htail hF)).trans_eq
  dsimp only [E, F, X, S, c, L]
  ring

end Conjectures.Goldbach.BinaryShiftMajorModel
end
end

section
open Complex DirichletCharacter MeasureTheory Finset GoldbachTwistedMellin
open scoped Interval
noncomputable section
namespace Conjectures.Goldbach.BinaryShiftMajorModel

/-- Contribution from a fixed primitive character pair and two selected
residues, up to the rational-arc cutoff. -/
def primitiveResidueContribution {r s : ℕ} (α : DirichletCharacter ℂ r)
    (β : DirichletCharacter ℂ s) (m n : ℕ) (P : ℝ) (z t : Option ℂ) : ℂ :=
  let L := Nat.lcm r s
  let w (j : ℕ) := P/(((L*j : ℕ):ℝ)*(m+2 : ℕ))
  ∑ j ∈ range (⌊P/(L:ℝ)⌋₊+1), TwistedGoldbachSingularSeries.coefficient α β n (L*j) *
    ∫ u in -(w j)..w j, phase (-2*Real.pi*(n:ℝ)) u * (residueProfile m z u * residueProfile m t u)

/-- A single arc cutoff gives a power saving, relative to its own
singular series, for every bounded-height residue pair in any bounded
family of conductors. Both the exponent and the constant are uniform in
the conductors, characters, residues and target. -/
theorem residuePair_common_power_saving (B : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    ∃ κ C : ℝ, 0 < κ ∧ 0 < C ∧ ∀ m : ℕ, 2 ≤ m → ∀ R : Finset ℕ, R.card ≤ B →
      let X : ℝ := (m+2 : ℕ)
      ∃ P : ℝ, X^(11/40:ℝ) ≤ P ∧ P ≤ X^(3/10:ℝ) ∧
      ∀ (r s : ℕ) [NeZero r] [NeZero s] (α : DirichletCharacter ℂ r) (β : DirichletCharacter ℂ s),
        r ∈ R → s ∈ R → (Nat.lcm r s:ℝ) ≤ P → α.IsPrimitive → β.IsPrimitive →
        ∀ (n : ℕ) (z t : Option ℂ), 0 < n → n ≤ m+2 → Even n →
        let a := z.getD 1
        let b := t.getD 1
        let S := ∑' d, TwistedGoldbachSingularSeries.coefficient α β n d
        5/8 ≤ a.re → a.re ≤ 1 → |a.im| ≤ T → 5/8 ≤ b.re → b.re ≤ 1 → |b.im| ≤ T →
        ‖primitiveResidueContribution α β m n P z t -
          S*((n:ℂ)^(a+b-1)*Complex.betaIntegral a b)‖ ≤ ‖S‖*(C*X^(1-κ)) := by
  obtain ⟨δ,hδ,chooseP⟩ := conductor_lcm_arc_gap B
  let e := min δ (1/5:ℝ)
  have he : 0 < e := lt_min hδ (by norm_num)
  have heδ : e ≤ δ := min_le_left ..
  have he' : e ≤ 1/5 := min_le_right ..
  obtain ⟨A,D,hA,hD,estimate⟩ := residuePair_denominator_sum hT (show 0 < e/2 by positivity)
  refine ⟨e/4, 4*A+D, by positivity, by positivity, ?_⟩
  intro m hm R hR X
  have hX4 : 4 ≤ X := by dsimp only [X]; exact_mod_cast (show 4 ≤ m+2 by omega)
  have hX : 1 < X := by linarith only [hX4]
  have hx := zero_lt_one.trans hX
  obtain ⟨P,hlo,hhi,hgap⟩ := chooseP X hX R hR
  have hp := (Real.rpow_pos_of_pos hx _).trans_le hlo
  have hP2 : 2*P ≤ X := by
    have h : P ≤ Real.sqrt X := hhi.trans (by rw [Real.sqrt_eq_rpow]; exact Real.rpow_le_rpow_of_exponent_le hX.le (by norm_num))
    have hs := Real.sq_sqrt hx.le
    have hs2 : 2 ≤ Real.sqrt X := by nlinarith only [hX4, hs, Real.sqrt_nonneg X, sq_nonneg (Real.sqrt X+2)]
    nlinarith only [h, hs, mul_nonneg (Real.sqrt_nonneg X) (sub_nonneg.mpr hs2)]
  refine ⟨P, hlo, hhi, ?_⟩
  intro r s _ _ α β hr hs hin hα hβ n z t hn hnX hEven a b S ha ha' haz hb hb' hbt
  let L := Nat.lcm r s
  have hL : (0:ℝ) < L := by exact_mod_cast Nat.lcm_pos (NeZero.pos r) (NeZero.pos s)
  have hLP : (L:ℝ)*X^e ≤ P := (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hX.le heδ) hL.le).trans (hgap r hr s hs hin)
  let Q := ⌊P/(L:ℝ)⌋₊
  let J := ⌈X^(e/2)⌉₊
  let V := X^(1-e/4)
  have hpow := Real.rpow_pos_of_pos hx (e/2)
  have h1 := Real.one_le_rpow hX.le (show 0 ≤ e/2 by positivity)
  have floorBound : ((L*Q : ℕ):ℝ) ≤ P := by
    rw [Nat.cast_mul, mul_comm]
    exact (le_div_iff₀ hL).mp (Nat.floor_le (div_nonneg hp.le hL.le))
  have hJ : J ≤ Q+1 := by
    apply Nat.ceil_le.mpr
    have hcut : X^e ≤ P/(L:ℝ) := (le_div_iff₀ hL).mpr (by simpa only [mul_comm] using hLP)
    apply (Real.rpow_le_rpow_of_exponent_le hX.le (show e/2 ≤ e by linarith only [he])).trans
    simpa only [Nat.cast_add, Nat.cast_one] using hcut.trans (Nat.lt_floor_add_one (P/(L:ℝ))).le
  have hsmall := estimate r s α β hα hβ m n J Q P z t hn hnX hEven hp hP2 floorBound hJ
    (Nat.le_ceil (X^(e/2))) ha ha' haz hb hb' hbt
  have Jupper : (J:ℝ) ≤ 2*X^(e/2) := (Nat.ceil_lt_add_one hpow.le).le.trans (by linarith only [h1])
  have hmult : ((L*J : ℕ):ℝ)*X^(e/2) ≤ 2*P := calc
    _ = (L:ℝ)*((J:ℝ)*X^(e/2)) := by push_cast; ring
    _ ≤ (L:ℝ)*((2*X^(e/2))*X^(e/2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right Jupper hpow.le) hL.le
    _ = 2*((L:ℝ)*X^e) := by rw [mul_assoc 2, ←Real.rpow_add hx, add_halves]; ring
    _ ≤ 2*P := by linarith only [hLP]
  have divPow (u : ℝ) : X/X^u = X^(1-u) := by rw [Real.rpow_sub hx, Real.rpow_one]
  have invle : X/X^(e/2) ≤ V := by
    rw [divPow]
    exact Real.rpow_le_rpow_of_exponent_le hX.le (by linarith only [he])
  have Jcost : ((L*J : ℕ):ℝ)*X/P ≤ 2*V := calc
    _ = (((L*J : ℕ):ℝ)*X^(e/2))*(X/X^(e/2))/P := by field_simp
    _ ≤ (2*P)*(X/X^(e/2))/P := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hmult (div_nonneg hx.le hpow.le)) hp.le
    _ = 2*(X/X^(e/2)) := by field_simp
    _ ≤ 2*V := by linarith only [invle]
  have pV : P ≤ V := hhi.trans (Real.rpow_le_rpow_of_exponent_le hX.le (by linarith only [he']))
  have tailEq : X/X^(e/2/2) = V := by rw [show e/2/2 = e/4 by ring, divPow]
  apply hsmall.trans
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg S)
  calc
    _ ≤ A*(2*V+2*V)+D*V := add_le_add (mul_le_mul_of_nonneg_left (add_le_add (by linarith only [pV]) Jcost) hA.le)
      (mul_le_mul_of_nonneg_left tailEq.le hD.le)
    _ = _ := by ring

end Conjectures.Goldbach.BinaryShiftMajorModel
end
end

section
open Complex DirichletCharacter Finset MeasureTheory GoldbachGrhGrowth
noncomputable section
namespace Conjectures.Goldbach.BinaryShiftZeroDensity

/-- Partial character Dirichlet series, including all positive integers
through the endpoint. -/
def dirichletPrefix {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ) (N : ℕ) : ℂ :=
  ∑ k ∈ Finset.Icc 1 N, (k:ℂ)^(-s) * χ (k:ZMod q)

/-- A truncation bound to the right of zero for a nonprincipal character.
Periodicity controls the boundary term and the remaining Abel integral
uniformly in the level, ordinate, and truncation length. -/
theorem prefix_error {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {s : ℂ} (hs : 0 < s.re) (N : ℕ) (hN : 0 < N) :
    ‖dirichletPrefix χ s N - χ.LFunction s‖ ≤ 2*(q:ℝ)*(1+‖s‖/s.re)*(N:ℝ)^(-s.re) := by
  classical
  let c (k : ℕ) : ℂ := if k=0 then 0 else χ (k:ZMod q)
  let f (x : ℝ) := (x:ℂ)^(-s)
  let G (x : ℝ) := (x:ℂ)^(-s-1)*charPartialSum χ ⌊x⌋₊
  have hmean : charMean χ = 0 := by simp [charMean_eq, hχ]
  have hc (k : ℕ) : (∑ d ∈ Finset.Icc 0 k, c d) = charPartialSum χ k := by
    rw [← Nat.range_succ_eq_Icc_zero, Finset.sum_range_succ']
    simp [c, charPartialSum]
  have hpartial (k : ℕ) : ‖charPartialSum χ k‖ ≤ 2*(q:ℝ) := by
    simpa only [integerRemainder, hmean, mul_zero, sub_zero] using norm_integerRemainder_le χ k
  have hN1 : 1 ≤ (N:ℝ) := by exact_mod_cast hN
  have hN0 := zero_lt_one.trans_le hN1
  have hpow : -s.re-1 < -1 := by linarith
  have hbound (x : ℝ) (hx : 0 < x) : ‖G x‖ ≤ (2*(q:ℝ))*x^(-s.re-1) := by
    dsimp only [G]
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hx, sub_re, neg_re, one_re]
    simpa only [mul_comm (2*(q:ℝ))] using mul_le_mul_of_nonneg_left
      (hpartial ⌊x⌋₊) (Real.rpow_nonneg hx.le (-s.re-1))
  have hG : IntegrableOn G (Set.Ioi 1) := by
    apply ((integrableOn_Ioi_rpow_of_lt hpow zero_lt_one).const_mul (2*(q:ℝ))).mono'
    · have hK : ContinuousOn (fun x : ℝ => (x:ℂ)^(-s-1)) (Set.Ioi 1) := fun x hx =>
        (continuousAt_ofReal_cpow_const x _ (Or.inr (zero_lt_one.trans hx).ne')).continuousWithinAt
      exact (hK.aestronglyMeasurable measurableSet_Ioi).mul
        ((measurable_of_countable (charPartialSum χ)).comp measurable_id.nat_floor).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact hbound x (zero_lt_one.trans hx)
  have hg (x : ℝ) (hx : 0 < x) : HasDerivAt f ((-s)*(x:ℂ)^(-s-1)) x :=
    hasDerivAt_ofReal_cpow_const hx.ne' (neg_ne_zero.mpr (fun h => by simp [h] at hs))
  have hd : IntegrableOn (deriv f) (Set.Icc (1:ℝ) N) := by
    have cont : ContinuousOn (fun x : ℝ => (-s)*(x:ℂ)^(-s-1)) (Set.Icc (1:ℝ) N) :=
      continuousOn_const.mul (fun x hx => (continuousAt_ofReal_cpow_const x _
        (Or.inr (zero_lt_one.trans_le hx.1).ne')).continuousWithinAt)
    exact cont.integrableOn_Icc.congr_fun (fun x hx => (hg x (zero_lt_one.trans_le hx.1)).deriv.symm) measurableSet_Icc
  have E := sum_mul_eq_sub_integral_mul₀' (f := f) c (by simp [c]) N
    (fun x hx => (hg x (zero_lt_one.trans_le hx.1)).differentiableAt) hd
  have hshort : ∑ k ∈ Finset.Icc 0 N, f k*c k = dirichletPrefix χ s N := by
    have setEq : Finset.Icc 0 N = insert 0 (Finset.Icc 1 N) := by
      ext k
      simp only [mem_Icc, mem_insert]
      omega
    rw [setEq, sum_insert (by simp), show c 0 = 0 by simp [c], mul_zero, zero_add]
    exact sum_congr rfl (fun k hk => by simp only [f, c, ite_eq_right (Nat.ne_of_gt (mem_Icc.mp hk).1)]; rfl)
  have heq : (∫ x in Set.Ioc (1:ℝ) N, deriv f x * ∑ k ∈ Finset.Icc 0 ⌊x⌋₊, c k) =
      -s*(∫ x in Set.Ioc (1:ℝ) N, G x) := by
    rw [← integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Ioc (fun x hx => by rw [(hg x (zero_lt_one.trans hx.1)).deriv, hc]; simp only [G, mul_assoc])
  rw [hshort, hc, heq] at E
  have hL : χ.LFunction s = s*((∫ x in Set.Ioc (1:ℝ) N, G x)+(∫ x in Set.Ioi (N:ℝ), G x)) := by
    rw [LFunction_eq_remainderMellin χ hχ hs, remainderMellin_eq_integral]
    simp only [hmean, mul_zero, sub_zero]
    congr 1
    change (∫ x in Set.Ioi (1:ℝ), G x) = _
    rw [← Set.Ioc_union_Ioi_eq_Ioi hN1, setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi
      (hG.mono_set Set.Ioc_subset_Ioi_self) (hG.mono_set (Set.Ioi_subset_Ioi hN1))]
  have tail : ‖∫ x in Set.Ioi (N:ℝ), G x‖ ≤ (2*(q:ℝ))*((N:ℝ)^(-s.re)/s.re) := by
    apply (norm_integral_le_of_norm_le ((integrableOn_Ioi_rpow_of_lt hpow hN0).const_mul (2*(q:ℝ))) ?_).trans_eq
    · rw [integral_const_mul, integral_Ioi_rpow_of_lt hpow hN0, show -s.re-1+1 = -s.re by ring]
      ring
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact hbound x (hN0.trans hx)
  have eqn : dirichletPrefix χ s N - χ.LFunction s = f N * charPartialSum χ N - s*(∫ x in Set.Ioi (N:ℝ), G x) := by
    rw [E, hL]
    ring
  rw [eqn]
  apply (norm_sub_le ..).trans
  simp only [norm_mul, f, ofReal_natCast, norm_natCast_cpow_of_pos hN, neg_re]
  exact (add_le_add (mul_le_mul_of_nonneg_left (hpartial N) (Real.rpow_nonneg hN0.le _))
    (mul_le_mul_of_nonneg_left tail (norm_nonneg s))).trans_eq (by ring)

end Conjectures.Goldbach.BinaryShiftZeroDensity
end
end

section
open Complex DirichletCharacter Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius
noncomputable section
namespace Conjectures.Goldbach.BinaryShiftZeroDensity

/-- Coefficients of the finite product of a Möbius mollifier of length
U with the character Dirichlet polynomial of length K. -/
def detectorCoefficient (U K n : ℕ) : ℤ :=
  ∑ p ∈ ((Finset.Icc 1 U ×ˢ Finset.Icc 1 K).filter fun p : ℕ×ℕ => p.1*p.2 = n), μ p.1

private theorem detectorCoefficient_small {U K n : ℕ} (hn : 0 < n) (hU : n ≤ U) (hK : n ≤ K) :
    detectorCoefficient U K n = if n = 1 then 1 else 0 := by
  have hf : ((Finset.Icc 1 U ×ˢ Finset.Icc 1 K).filter fun p : ℕ×ℕ => p.1*p.2 = n) = n.divisorsAntidiagonal := by
    ext p
    simp only [mem_filter, mem_product, mem_Icc, Nat.mem_divisorsAntidiagonal]
    refine ⟨fun h => ⟨h.2,hn.ne'⟩, fun h => ⟨?_,h.1⟩⟩
    have hprod : 0 < p.1*p.2 := by simpa only [h.1] using hn
    have hd : p.1 ∣ n := ⟨p.2,h.1.symm⟩
    have hk : p.2 ∣ n := ⟨p.1,by simpa only [mul_comm] using h.1.symm⟩
    exact ⟨⟨Nat.pos_of_mul_pos_right hprod, (Nat.le_of_dvd hn hd).trans hU⟩,
      ⟨Nat.pos_of_mul_pos_left hprod, (Nat.le_of_dvd hn hk).trans hK⟩⟩
  rw [detectorCoefficient, hf, Nat.sum_divisorsAntidiagonal (f := fun d _ => μ d),
    ← ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.moebius_mul_coe_zeta, ArithmeticFunction.one_apply]

private theorem detector_product {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ) (U K : ℕ) :
    (∑ d ∈ Finset.Icc 1 U, (μ d:ℂ)*((d:ℂ)^(-s)*χ (d:ZMod q))) * dirichletPrefix χ s K =
      ∑ n ∈ Finset.Icc 1 (U*K), (detectorCoefficient U K n:ℂ)*((n:ℂ)^(-s)*χ (n:ZMod q)) := by
  classical
  let f (n : ℕ) := (n:ℂ)^(-s)*χ (n:ZMod q)
  let D := Finset.Icc 1 U ×ˢ Finset.Icc 1 K
  let prodIndex (p : ℕ×ℕ) := p.1*p.2
  have mult (a b : ℕ) : f a*f b = f (a*b) := by
    dsimp only [f]
    rw [Nat.cast_mul, natCast_mul_natCast_cpow, Nat.cast_mul, map_mul]
    ring
  have hmem (p : ℕ×ℕ) (hp : p ∈ D) : prodIndex p ∈ Finset.Icc 1 (U*K) := by
    obtain ⟨a,b⟩ := mem_product.mp hp
    exact mem_Icc.mpr ⟨Nat.mul_pos (mem_Icc.mp a).1 (mem_Icc.mp b).1,
      Nat.mul_le_mul (mem_Icc.mp a).2 (mem_Icc.mp b).2⟩
  calc
    _ = ∑ p ∈ D, (μ p.1:ℂ)*f (prodIndex p) := by
      simp only [dirichletPrefix, Finset.sum_mul_sum, D, Finset.sum_product]
      apply sum_congr rfl
      intro d _
      exact sum_congr rfl fun k _ => by change ((μ d:ℂ)*f d)*f k = (μ d:ℂ)*f (d*k); rw [mul_assoc,mult]
    _ = ∑ n ∈ Finset.Icc 1 (U*K), ∑ p ∈ D.filter (prodIndex · = n), (μ p.1:ℂ)*f (prodIndex p) :=
      (sum_fiberwise_of_maps_to hmem _).symm
    _ = _ := by
      apply sum_congr rfl
      intro n _
      change _ = ((∑ p ∈ D.filter (prodIndex · = n), μ p.1):ℤ)*f n
      push_cast
      rw [sum_mul]
      exact sum_congr rfl fun p hp => by rw [(mem_filter.mp hp).2]

/-- Every zero of a nonprincipal character forces a large value of a
finite Dirichlet polynomial supported strictly above the mollifier length.
Its integer coefficients are independent of the zero and character. -/
theorem zero_detector {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {s : ℂ} (hs : 0 < s.re) (hz : χ.LFunction s = 0) {U K : ℕ} (hU : 0 < U) (hUK : U ≤ K) :
    1 - (U:ℝ)*(2*(q:ℝ)*(1+‖s‖/s.re)*(K:ℝ)^(-s.re)) ≤
      ‖∑ n ∈ Finset.Ioc U (U*K), (detectorCoefficient U K n:ℂ)*((n:ℂ)^(-s)*χ (n:ZMod q))‖ := by
  classical
  let M := ∑ d ∈ Finset.Icc 1 U, (μ d:ℂ)*((d:ℂ)^(-s)*χ (d:ZMod q))
  let f (n : ℕ) := (detectorCoefficient U K n:ℂ)*((n:ℂ)^(-s)*χ (n:ZMod q))
  have hshort : ∑ n ∈ Finset.Icc 1 U, f n = 1 := by
    rw [sum_eq_single_of_mem 1 (mem_Icc.mpr ⟨le_rfl,hU⟩)]
    · simp [f, detectorCoefficient_small (Nat.zero_lt_one) hU (hU.trans_le hUK)]
    · intro n hn hne
      obtain ⟨hn1,hnU⟩ := mem_Icc.mp hn
      simp [f, detectorCoefficient_small hn1 hnU (hnU.trans hUK), hne]
  have cut : Finset.Icc 1 (U*K) = Finset.Icc 1 U ∪ Finset.Ioc U (U*K) := by
    have hk := Nat.le_mul_of_pos_right U (hU.trans_le hUK)
    ext n
    simp only [mem_union,mem_Icc,mem_Ioc]
    omega
  have hprod : M*dirichletPrefix χ s K = 1+∑ n ∈ Finset.Ioc U (U*K), f n := by
    rw [show M*dirichletPrefix χ s K = ∑ n ∈ Finset.Icc 1 (U*K), f n from detector_product χ s U K,
      cut, sum_union (disjoint_left.mpr (fun n hn hn' => (mem_Ioc.mp hn').1.not_ge (mem_Icc.mp hn).2)), hshort]
  have hM : ‖M‖ ≤ (U:ℝ) := by
    dsimp only [M]
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _d ∈ Finset.Icc 1 U, (1:ℝ) := by
        apply sum_le_sum
        intro d hd
        have hd1 := (mem_Icc.mp hd).1
        have d1 : 1 ≤ (d:ℝ) := by exact_mod_cast hd1
        have hμ : ‖(μ d:ℂ)‖ ≤ 1 := by rcases moebius_eq_or d with h|h|h <;> simp [h]
        have hp : ‖(d:ℂ)^(-s)‖ ≤ 1 := by
          rw [norm_natCast_cpow_of_pos hd1,neg_re]
          simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le d1 (neg_nonpos.mpr hs.le)
        simp only [norm_mul]
        exact (mul_le_mul hμ (mul_le_mul hp (χ.norm_le_one _) (norm_nonneg _) zero_le_one)
          (mul_nonneg (norm_nonneg _) (norm_nonneg _)) zero_le_one).trans_eq (by norm_num)
      _ = _ := by simp
  have hp := prefix_error χ hχ hs K (hU.trans_le hUK)
  rw [hz, sub_zero] at hp
  have hreverse : (1:ℝ) ≤ ‖M*dirichletPrefix χ s K‖ + ‖∑ n ∈ Finset.Ioc U (U*K), f n‖ := by
    calc
      _ = ‖M*dirichletPrefix χ s K - (∑ n ∈ Finset.Ioc U (U*K), f n)‖ := by rw [hprod,add_sub_cancel_right,norm_one]
      _ ≤ _ := norm_sub_le ..
  have h := (mul_le_mul hM hp (norm_nonneg _) (Nat.cast_nonneg U))
  rw [←norm_mul] at h
  change 1-_ ≤ ‖∑ n ∈ Finset.Ioc U (U*K), f n‖
  linarith only [hreverse,h]

end Conjectures.Goldbach.BinaryShiftZeroDensity
end
end

section
open Complex Finset
open scoped ComplexConjugate
noncomputable section
namespace Conjectures.Goldbach.BinaryShiftZeroDensity

/-- Finite weighted Halász inequality for the correlated values of
Dirichlet polynomials, as in Pintz, "Some new density theorems for
Dirichlet L-functions", Lemma 3. -/
private theorem halasz_correlation {ι : Type*} (Z : Finset ι) (I : Finset ℕ)
    (a : ℕ → ℂ) (b : ℕ → ℝ) (hb : ∀ n ∈ I, 0 ≤ b n)
    (hsupp : ∀ n ∈ I, b n = 0 → a n = 0) (F : ι → ℕ → ℂ) :
    (∑ i ∈ Z, ‖∑ n ∈ I, a n*F i n‖)^2 ≤
      (∑ n ∈ I, ‖a n‖^2/b n) *
        ∑ i ∈ Z, ∑ j ∈ Z, ‖∑ n ∈ I, (b n:ℂ)*F i n*conj (F j n)‖ := by
  classical
  let L (i : ι) := ∑ n ∈ I, a n*F i n
  let u (i : ι) := conj (L i)/(‖L i‖:ℂ)
  let v (n : ℕ) := ∑ i ∈ Z, u i*F i n
  let K (i j : ι) := ∑ n ∈ I, (b n:ℂ)*F i n*conj (F j n)
  have hu (i : ι) : ‖u i‖ ≤ 1 := by
    dsimp only [u]
    rw [norm_div, norm_conj, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
    exact div_self_le_one ..
  have huL (i : ι) : u i*L i = (‖L i‖:ℂ) := by
    dsimp only [u]
    rw [div_mul_eq_mul_div, conj_mul']
    by_cases h : L i = 0
    · simp [h]
    · have h' : (‖L i‖:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr h)
      field_simp
  have swapSum : (∑ i ∈ Z, ‖L i‖) = ‖∑ n ∈ I, a n*v n‖ := by
    have eqn : Complex.ofReal (∑ i ∈ Z, ‖L i‖) = ∑ n ∈ I, a n*v n := by
      rw [Complex.ofReal_sum]
      simp_rw [←huL, L, mul_sum]
      rw [sum_comm]
      exact sum_congr rfl fun n _ => by
        dsimp only [v]
        rw [mul_sum]
        exact sum_congr rfl (fun i _ => by ring)
    rw [←eqn, Complex.norm_real, Real.norm_of_nonneg (sum_nonneg (fun i _ => norm_nonneg (L i)))]
  have expand : (∑ n ∈ I, (b n:ℂ)*(v n*conj (v n))) =
      ∑ i ∈ Z, ∑ j ∈ Z, (u i*conj (u j))*K i j := by
    calc
      _ = ∑ n ∈ I, ∑ i ∈ Z, ∑ j ∈ Z, (u i*conj (u j))*((b n:ℂ)*F i n*conj (F j n)) := by
        apply sum_congr rfl
        intro n _
        simp only [v, map_sum, map_mul]
        rw [sum_mul_sum]
        simp only [mul_sum]
        apply sum_congr rfl
        intro i _
        exact sum_congr rfl (fun j _ => by ring)
      _ = _ := by
        rw [sum_comm]
        apply sum_congr rfl
        intro i _
        rw [sum_comm]
        exact sum_congr rfl (fun j _ => (mul_sum _ _ _).symm)
  have hG : (∑ n ∈ I, b n*‖v n‖^2) ≤ ∑ i ∈ Z, ∑ j ∈ Z, ‖K i j‖ := by
    have hc : Complex.ofReal (∑ n ∈ I, b n*‖v n‖^2) = ∑ n ∈ I, (b n:ℂ)*(v n*conj (v n)) := by
      simp only [ofReal_sum, ofReal_mul, ofReal_pow, mul_conj']
    calc
      _ = ‖∑ i ∈ Z, ∑ j ∈ Z, (u i*conj (u j))*K i j‖ := by
        rw [←expand,←hc,Complex.norm_real,Real.norm_of_nonneg
          (sum_nonneg (fun n hn => mul_nonneg (hb n hn) (sq_nonneg _)))]
      _ ≤ _ := by
        apply (norm_sum_le ..).trans
        apply sum_le_sum
        intro i _
        apply (norm_sum_le ..).trans
        apply sum_le_sum
        intro j _
        simp only [norm_mul,norm_conj]
        apply mul_le_of_le_one_left (norm_nonneg _)
        exact (mul_le_mul (hu i) (hu j) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  have hcs := sum_sq_le_sum_mul_sum_of_sq_le_mul I (f := fun n => ‖a n‖^2/b n)
    (g := fun n => b n*‖v n‖^2) (r := fun n => ‖a n‖*‖v n‖)
    (fun n hn => div_nonneg (sq_nonneg _) (hb n hn))
    (fun n hn => mul_nonneg (hb n hn) (sq_nonneg _))
    (fun n hn => by
      by_cases h : b n = 0
      · simp [h,hsupp n hn h]
      · apply le_of_eq
        field_simp [h])
  have hlin : ‖∑ n ∈ I, a n*v n‖ ≤ ∑ n ∈ I, ‖a n‖*‖v n‖ := by simpa only [norm_mul] using norm_sum_le (I) (fun n => a n*v n)
  change (∑ i ∈ Z, ‖L i‖)^2 ≤ _
  rw [swapSum]
  exact ((pow_le_pow_left₀ (norm_nonneg _) hlin 2).trans hcs).trans
    (mul_le_mul_of_nonneg_left hG (sum_nonneg (fun n hn => div_nonneg (sq_nonneg _) (hb n hn))))

end Conjectures.Goldbach.BinaryShiftZeroDensity
end
end

section
open Complex DirichletCharacter Finset
open scoped ComplexConjugate
noncomputable section
namespace Conjectures.Goldbach.BinaryShiftZeroDensity

/-- At suitably chosen polynomial lengths, the count of an arbitrary
finite family of nonprincipal L-function zeros is bounded by its weighted
character correlations. The real parts and heights may vary across the
family. The coefficients contain no character or zero parameters. -/
theorem zero_family_correlation_bound {ι : Type*} (Z : Finset ι) (q : ι → ℕ)
    [∀ i, NeZero (q i)] (χ : (i : ι) → DirichletCharacter ℂ (q i)) (s : ι → ℂ)
    {Q U K : ℕ} {σ T : ℝ} (hU : 0 < U) (hUK : U ≤ K) (hσ : 0 < σ)
    (hzero : ∀ i ∈ Z, q i ≤ Q ∧ χ i ≠ 1 ∧ (χ i).LFunction (s i) = 0 ∧ σ ≤ (s i).re ∧ ‖s i‖ ≤ T)
    (hcut : (U:ℝ)*(2*(Q:ℝ)*(1+T/σ)*(K:ℝ)^(-σ)) ≤ 1/2) (b : ℕ → ℝ)
    (hb : ∀ n ∈ Finset.Ioc U (U*K), 0 ≤ b n)
    (hsupp : ∀ n ∈ Finset.Ioc U (U*K), b n = 0 → detectorCoefficient U K n = 0) :
    let I := Finset.Ioc U (U*K)
    ((Z.card:ℝ)/2)^2 ≤ (∑ n ∈ I, ‖(detectorCoefficient U K n:ℂ)‖^2/b n) *
      ∑ i ∈ Z, ∑ j ∈ Z, ‖∑ n ∈ I, (b n:ℂ)*(n:ℂ)^(-(s i+conj (s j))) *
        χ i (n:ZMod (q i))*conj (χ j (n:ZMod (q j)))‖ := by
  classical
  intro I
  let a (n : ℕ) : ℂ := detectorCoefficient U K n
  let F (i : ι) (n : ℕ) := (n:ℂ)^(-s i)*χ i (n:ZMod (q i))
  have hK : 1 ≤ (K:ℝ) := by exact_mod_cast hU.trans_le hUK
  have large (i : ι) (hi : i ∈ Z) : 1/2 ≤ ‖∑ n ∈ I, a n*F i n‖ := by
    obtain ⟨hq,hn,hz,hl,ht⟩ := hzero i hi
    have hp := hσ.trans_le hl
    have scale : 2*(q i:ℝ)*(1+‖s i‖/(s i).re)*(K:ℝ)^(-(s i).re) ≤ 2*(Q:ℝ)*(1+T/σ)*(K:ℝ)^(-σ) := by
      have divl : ‖s i‖/(s i).re ≤ T/σ := (div_le_div_of_nonneg_right ht hp.le).trans
        (div_le_div_of_nonneg_left ((norm_nonneg _).trans ht) hσ hl)
      have ql : 2*(q i:ℝ) ≤ 2*(Q:ℝ) := by exact_mod_cast Nat.mul_le_mul_left 2 hq
      exact mul_le_mul (mul_le_mul ql (add_le_add_right divl 1)
        (by positivity) (by positivity)) (Real.rpow_le_rpow_of_exponent_le hK (neg_le_neg hl))
        (Real.rpow_nonneg (Nat.cast_nonneg _) _) (by have := (norm_nonneg _).trans ht; positivity)
    apply (show 1/2 ≤ 1-(U:ℝ)*(2*(q i:ℝ)*(1+‖s i‖/(s i).re)*(K:ℝ)^(-(s i).re)) by
      linarith only [hcut,mul_le_mul_of_nonneg_left scale (Nat.cast_nonneg U)]).trans
    exact zero_detector (χ i) hn hp hz hU hUK
  have hcount : (Z.card:ℝ)/2 ≤ ∑ i ∈ Z, ‖∑ n ∈ I, a n*F i n‖ := calc
    _ = ∑ _i ∈ Z, (1/2:ℝ) := by simp; ring
    _ ≤ _ := sum_le_sum large
  have hGram := halasz_correlation Z I a b hb (fun n hn he => by simp [a, hsupp n hn he]) F
  apply ((pow_le_pow_left₀ (by positivity) hcount 2).trans hGram).trans_eq
  congr 1
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  congr 1
  apply sum_congr rfl
  intro n hn
  have hn0 : 0 < n := hU.trans (mem_Ioc.mp hn).1
  have hnC : (n:ℂ) ≠ 0 := by exact_mod_cast hn0.ne'
  have harg : (n:ℂ).arg ≠ Real.pi := by simp [Real.pi_ne_zero.symm]
  have hc : conj ((n:ℂ)^(-s j)) = (n:ℂ)^(-conj (s j)) := by
    simpa only [map_neg, map_natCast] using (cpow_conj (n:ℂ) (-s j) harg).symm
  simp only [F, map_mul, hc, neg_add, cpow_add _ _ hnC]
  ring

end Conjectures.Goldbach.BinaryShiftZeroDensity
end
end

section
open Complex DirichletCharacter Finset
open scoped ComplexConjugate
noncomputable section
namespace Conjectures.Goldbach.BinaryShiftZeroDensity

private def correlationCharacter {r s : ℕ} (χ : DirichletCharacter ℂ r) (ψ : DirichletCharacter ℂ s) :
    DirichletCharacter ℂ (r*s) :=
  changeLevel (Nat.dvd_mul_right r s) χ * (changeLevel (Nat.dvd_mul_left s r) ψ)⁻¹

private theorem correlationCharacter_apply {r s : ℕ} [NeZero s] (χ : DirichletCharacter ℂ r)
    (ψ : DirichletCharacter ℂ s) (n : ℕ) :
    correlationCharacter χ ψ (n:ZMod (r*s)) = χ (n:ZMod r)*conj (ψ (n:ZMod s)) := by
  by_cases hu : n.Coprime (r*s)
  · have lift {d : ℕ} (hd : d ∣ r*s) (α : DirichletCharacter ℂ d) :
        changeLevel hd α (n:ZMod (r*s)) = α (n:ZMod d) := by
      have hi : IsCoprime (n:ℤ) ((r*s:ℕ):ℤ) := Nat.isCoprime_iff_coprime.mpr hu
      simpa only [Int.cast_natCast] using changeLevel_eq_cast_of_dvd' α hd hi
    rw [correlationCharacter, ←map_inv, MulChar.mul_apply, lift, lift]
    exact congrArg (χ (n:ZMod r)*·) (MulChar.star_apply' ψ (n:ZMod s)).symm
  · rw [MulChar.map_nonunit _ (fun h => hu ((ZMod.isUnit_iff_coprime n (r*s)).mp h))]
    by_cases hr : n.Coprime r
    · have hs : ¬n.Coprime s := fun h => hu (hr.mul_right h)
      simp [MulChar.map_nonunit ψ (fun h => hs ((ZMod.isUnit_iff_coprime n s).mp h))]
    · simp [MulChar.map_nonunit χ (fun h => hr ((ZMod.isUnit_iff_coprime n r).mp h))]

private theorem correlationCharacter_nonprincipal {r s : ℕ} [NeZero r] [NeZero s]
    (χ : DirichletCharacter ℂ r) (ψ : DirichletCharacter ℂ s) (hχ : χ.IsPrimitive) (hψ : ψ.IsPrimitive)
    (hne : (⟨r,χ⟩ : Σ k : ℕ, DirichletCharacter ℂ k) ≠ ⟨s,ψ⟩) : correlationCharacter χ ψ ≠ 1 := by
  intro h
  have e := mul_inv_eq_one.mp h
  have hc := congrArg DirichletCharacter.conductor e
  rw [conductor_changeLevel,conductor_changeLevel,hχ,hψ] at hc
  subst s
  exact hne (congrArg (Sigma.mk r) (changeLevel_injective (Nat.dvd_mul_right r r) e))

/-- In a Gram matrix of distinct primitive characters, a cross term has
no pole. Periodic cancellation bounds its tail even when the two complex
ordinates differ. -/
theorem distinct_character_correlation {r s : ℕ} [NeZero r] [NeZero s]
    (χ : DirichletCharacter ℂ r) (ψ : DirichletCharacter ℂ s)
    (hχ : χ.IsPrimitive) (hψ : ψ.IsPrimitive)
    (hne : (⟨r,χ⟩ : Σ k : ℕ, DirichletCharacter ℂ k) ≠ ⟨s,ψ⟩)
    (u v : ℂ) (hσ : 1 < u.re+v.re) {U Y : ℕ} (hU : 0 < U) (hY : U ≤ Y) :
    let w := u+conj v-1
    ‖∑ n ∈ Finset.Ioc U Y, (n:ℂ)*(n:ℂ)^(-(u+conj v)) *
        χ (n:ZMod r)*conj (ψ (n:ZMod s))‖ ≤ 4*(r*s:ℕ)*(1+‖w‖/w.re)*(U:ℝ)^(-w.re) := by
  classical
  intro w
  let θ := correlationCharacter χ ψ
  have hn := correlationCharacter_nonprincipal χ ψ hχ hψ hne
  have hw : 0 < w.re := by simpa [w,sub_re,add_re] using sub_pos.mpr hσ
  have eqn : (∑ n ∈ Finset.Ioc U Y, (n:ℂ)*(n:ℂ)^(-(u+conj v))*χ (n:ZMod r)*conj (ψ (n:ZMod s))) =
      dirichletPrefix θ w Y - dirichletPrefix θ w U := by
    have cut : Finset.Icc 1 Y = Finset.Icc 1 U ∪ Finset.Ioc U Y := by
      ext n
      simp only [mem_Icc,mem_Ioc,mem_union]
      omega
    dsimp only [dirichletPrefix]
    rw [cut, sum_union (disjoint_left.mpr (fun n hn hn' => (mem_Ioc.mp hn').1.not_ge (mem_Icc.mp hn).2)),add_sub_cancel_left]
    apply sum_congr rfl
    intro n hm
    have hn0 : (n:ℂ) ≠ 0 := by exact_mod_cast (hU.trans (mem_Ioc.mp hm).1).ne'
    dsimp only [θ]
    rw [correlationCharacter_apply, show -w = 1+ -(u+conj v) by dsimp [w]; ring, cpow_add _ _ hn0, cpow_one]
    ring
  rw [eqn]
  have hfirst := prefix_error θ hn hw Y (hU.trans_le hY)
  have hsecond := prefix_error θ hn hw U hU
  have hpow := Real.rpow_le_rpow_of_nonpos (by exact_mod_cast hU : 0 < (U:ℝ))
    (by exact_mod_cast hY : (U:ℝ) ≤ Y) (neg_nonpos.mpr hw.le)
  have hcoef : 0 ≤ 2*(r*s:ℕ)*(1+‖w‖/w.re) := by positivity
  have hsub := norm_sub_le_norm_sub_add_norm_sub (dirichletPrefix θ w Y) (θ.LFunction w) (dirichletPrefix θ w U)
  rw [norm_sub_rev (θ.LFunction w)] at hsub
  exact (hsub.trans (add_le_add (hfirst.trans (mul_le_mul_of_nonneg_left hpow hcoef)) hsecond)).trans_eq (by ring)

end Conjectures.Goldbach.BinaryShiftZeroDensity
end
end

section
open Complex Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open OAI.Problem337.DivisorSquareMean
noncomputable section
namespace Conjectures.Goldbach.BinaryShiftZeroDensity

private theorem positive_reindex (N : ℕ) (f : ℕ → ℝ) :
    (∑ j ∈ range N, f (j+1)) = ∑ n ∈ Finset.Ioc 0 N, f n := by
  induction N with
  | zero => simp
  | succ k ih => rw [sum_range_succ, sum_Ioc_succ_top (Nat.zero_le k), ih]

/-- The rectangular mollifier has coefficient at most the number of
positive divisors of its index. -/
theorem detectorCoefficient_le_divisors (U K n : ℕ) (hn : 0 < n) :
    ‖(detectorCoefficient U K n:ℂ)‖ ≤ (n.divisors.card:ℝ) := by
  let D := (Finset.Icc 1 U ×ˢ Finset.Icc 1 K).filter (fun p : ℕ×ℕ => p.1*p.2 = n)
  have hsub : D ⊆ n.divisorsAntidiagonal := fun p hp => Nat.mem_divisorsAntidiagonal.mpr ⟨(mem_filter.mp hp).2,hn.ne'⟩
  have hcard : n.divisorsAntidiagonal.card = n.divisors.card := by rw [← Nat.map_div_right_divisors, card_map]
  change ‖((∑ p ∈ D, μ p.1 : ℤ):ℂ)‖ ≤ _
  rw [Int.cast_sum]
  calc
    _ ≤ ∑ p ∈ D, ‖(μ p.1:ℂ)‖ := norm_sum_le ..
    _ ≤ ∑ _p ∈ D, (1:ℝ) := sum_le_sum (fun p _ => by rcases moebius_eq_or p.1 with h|h|h <;> simp [h])
    _ = (D.card:ℝ) := by simp
    _ ≤ _ := by exact_mod_cast (card_le_card hsub).trans_eq hcard

/-- The actual zero detector has fourth-logarithmic harmonic energy,
uniformly in the mollifier lengths. -/
theorem detector_harmonic_energy (U K N : ℕ) :
    (∑ n ∈ Finset.Ioc U N, ‖(detectorCoefficient U K n:ℂ)‖^2/(n:ℝ)) ≤
      (1+Real.log N)^4 := by
  let H := (harmonic N:ℝ)
  let f (n : ℕ) := (n.divisors.card:ℝ)^2
  have hH : 0 ≤ H := real_harmonic_nonneg N
  have hp (k : ℕ) (hk : k ≤ N) : (∑ j ∈ range k, f (j+1)) ≤ ∑ _j ∈ range k, H^3 := by
    rw [positive_reindex, sum_const, nsmul_eq_mul, card_range]
    exact (sum_card_divisors_sq_le_harmonic k).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (real_harmonic_nonneg _) (real_harmonic_mono hk) 3) (Nat.cast_nonneg k))
  let g (j : ℕ) := ((j+1:ℕ):ℝ)⁻¹
  have hg : 0 ≤ g := fun j => inv_nonneg.mpr (Nat.cast_nonneg _)
  have hanti : AntitoneOn g (Set.Iio N) := fun i _ j _ hij =>
    (inv_le_inv₀ (show (0:ℝ) < (j+1:ℕ) by positivity) (show (0:ℝ) < (i+1:ℕ) by positivity)).mpr (by exact_mod_cast Nat.succ_le_succ hij)
  have hweighted := sum_mul_le_sum_mul_of_sum_range_le hp hg hanti
  calc
    _ ≤ ∑ n ∈ Finset.Ioc U N, f n/(n:ℝ) := sum_le_sum (fun n hn =>
      div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (detectorCoefficient_le_divisors U K n
        ((Nat.zero_le U).trans_lt (mem_Ioc.mp hn).1)) 2) (Nat.cast_nonneg _))
    _ ≤ ∑ n ∈ Finset.Ioc 0 N, f n/(n:ℝ) := sum_le_sum_of_subset_of_nonneg
      (Ioc_subset_Ioc_left (Nat.zero_le U)) (fun n _ _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
    _ = ∑ j ∈ range N, f (j+1)*g j := by rw [← positive_reindex]; rfl
    _ ≤ ∑ j ∈ range N, H^3*g j := hweighted
    _ = H^4 := by
      rw [←mul_sum, show (∑ j ∈ range N, g j) = H from
        (positive_reindex N (fun n => (n:ℝ)⁻¹)).trans (real_harmonic_eq_sum N).symm, ←pow_succ]
    _ ≤ _ := pow_le_pow_left₀ hH (harmonic_le_one_add_log N) 4

end Conjectures.Goldbach.BinaryShiftZeroDensity
end
end

section
open Complex DirichletCharacter Finset OAI.Problem337.DivisorSquareMean
open scoped ComplexConjugate
noncomputable section
namespace Conjectures.Goldbach.BinaryShiftZeroDensity

private theorem diagonal_correlation {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ)
    {σ : ℝ} (hs : σ ≤ s.re) (hσ : σ ≤ 1) {U Y : ℕ} (hU : 0 < U) :
    ‖∑ n ∈ Finset.Ioc U Y, (n:ℂ)*(n:ℂ)^(-(s+conj s))*χ (n:ZMod q)*conj (χ (n:ZMod q))‖ ≤
      (Y:ℝ)^(2*(1-σ))*(1+Real.log Y) := by
  have hp : 0 ≤ 2*(1-σ) := by linarith
  apply (norm_sum_le ..).trans
  calc
    _ ≤ ∑ n ∈ Finset.Ioc U Y, (Y:ℝ)^(2*(1-σ))*(n:ℝ)⁻¹ := by
      apply sum_le_sum
      intro n hn
      obtain ⟨lo,hi⟩ := mem_Ioc.mp hn
      have h := hU.trans lo
      have h1 : 1 ≤ (n:ℝ) := by exact_mod_cast h
      have hn0 := zero_lt_one.trans_le h1
      have hc := χ.norm_le_one (n:ZMod q)
      rw [norm_mul, norm_mul, norm_mul, norm_natCast, norm_conj, norm_natCast_cpow_of_pos h, neg_re, add_re, conj_re]
      calc
        _ ≤ (n:ℝ)*(n:ℝ)^(-(s.re+s.re)) := by
          have hn' : 0 ≤ (n:ℝ)*(n:ℝ)^(-(s.re+s.re)) := by positivity
          exact (mul_le_of_le_one_right (mul_nonneg hn' (norm_nonneg _)) hc).trans (mul_le_of_le_one_right hn' hc)
        _ = (n:ℝ)^(2-(s.re+s.re))*(n:ℝ)⁻¹ := by
          rw [Real.rpow_sub hn0, Real.rpow_neg hn0.le, Real.rpow_two]
          field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_right ((Real.rpow_le_rpow_of_exponent_le h1 (by linarith only [hs])).trans
          (Real.rpow_le_rpow hn0.le (by exact_mod_cast hi) hp)) (inv_nonneg.mpr hn0.le)
    _ = (Y:ℝ)^(2*(1-σ))*(∑ n ∈ Finset.Ioc U Y, (n:ℝ)⁻¹) := (mul_sum ..).symm
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      apply (sum_le_sum_of_subset_of_nonneg (Ioc_subset_Ioc_left (Nat.zero_le U)) (fun n _ _ => inv_nonneg.mpr (Nat.cast_nonneg n))).trans
      rw [←real_harmonic_eq_sum]
      exact harmonic_le_one_add_log Y

/-- Count distinct primitive characters represented by actual zeros in a
right-hand rectangle. The two explicit size conditions on U and K make
the detector large and absorb all off-diagonal correlations. -/
theorem distinct_primitive_zero_density {ι : Type*} (Z : Finset ι) (q : ι → ℕ)
    [∀ i, NeZero (q i)] (χ : (i : ι) → DirichletCharacter ℂ (q i)) (s : ι → ℂ)
    (distinct : Set.InjOn (fun i => (⟨q i,χ i⟩ : Σ k : ℕ, DirichletCharacter ℂ k)) (Z:Set ι))
    {Q U K : ℕ} {σ T : ℝ} (hU : 0 < U) (hUK : U ≤ K) (hσ : 1/2 < σ) (hσ' : σ ≤ 1) (hT : 0 ≤ T)
    (hzero : ∀ i ∈ Z, q i ≤ Q ∧ (χ i).IsPrimitive ∧ χ i ≠ 1 ∧ (χ i).LFunction (s i) = 0 ∧ σ ≤ (s i).re ∧ ‖s i‖ ≤ T)
    (hcut : (U:ℝ)*(2*(Q:ℝ)*(1+T/σ)*(K:ℝ)^(-σ)) ≤ 1/2)
    (hcross : (1+Real.log (U*K:ℕ))^4 * (4*(Q:ℝ)^2*(1+(2*T+1)/(2*σ-1))*(U:ℝ)^(-(2*σ-1))) ≤ 1/8) :
    (Z.card:ℝ) ≤ 8*(1+Real.log (U*K:ℕ))^5*(U*K:ℕ)^(2*(1-σ)) := by
  classical
  let Y := U*K
  let H := 1+Real.log (Y:ℝ)
  let A := (Y:ℝ)^(2*(1-σ))*H
  let E := 4*(Q:ℝ)^2*(1+(2*T+1)/(2*σ-1))*(U:ℝ)^(-(2*σ-1))
  let J := (Z.card:ℝ)
  let G (i j : ι) := ‖∑ n ∈ Finset.Ioc U Y, (n:ℂ)*(n:ℂ)^(-(s i+conj (s j))) *
    χ i (n:ZMod (q i))*conj (χ j (n:ZMod (q j)))‖
  have hσ0 : 0 < σ := by linarith
  have hbase : 0 < 2*σ-1 := by linarith
  have hH : 0 ≤ H := by dsimp only [H]; linarith [Real.log_natCast_nonneg Y]
  have hA : 0 ≤ A := mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) hH
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hJ : 0 ≤ J := Nat.cast_nonneg _
  have hUY : U ≤ Y := Nat.le_mul_of_pos_right U (hU.trans_le hUK)
  have hU1 : 1 ≤ (U:ℝ) := by exact_mod_cast hU
  have bound (i : ι) (hi : i ∈ Z) (j : ι) (hj : j ∈ Z) (hij : i ≠ j) : G i j ≤ E := by
    obtain ⟨qi,pi,_,_,si,ti⟩ := hzero i hi
    obtain ⟨qj,pj,_,_,sj,tj⟩ := hzero j hj
    let w := s i+conj (s j)-1
    have re : 2*σ-1 ≤ w.re := by simp only [w,sub_re,add_re,conj_re,one_re]; linarith only [si,sj]
    have ht : ‖w‖ ≤ 2*T+1 := calc
      _ ≤ ‖s i+conj (s j)‖+‖(1:ℂ)‖ := norm_sub_le ..
      _ ≤ (‖s i‖+‖s j‖)+1 := by rw [norm_one]; apply add_le_add_left; simpa using norm_add_le (s i) (conj (s j))
      _ ≤ _ := by linarith only [ti,tj]
    have den : ‖w‖/w.re ≤ (2*T+1)/(2*σ-1) := (div_le_div_of_nonneg_right ht (hbase.le.trans re)).trans
      (div_le_div_of_nonneg_left (by positivity) hbase re)
    have pq : 4*(((q i*q j:ℕ):ℝ)) ≤ 4*(Q:ℝ)^2 := by
      rw [sq, Nat.cast_mul]
      gcongr
    apply (distinct_character_correlation (χ i) (χ j) pi pj (fun e => hij (distinct hi hj e))
      (s i) (s j) (by linarith only [si,sj,hσ]) hU hUY).trans
    exact mul_le_mul (mul_le_mul pq (add_le_add_right den 1)
      (by have := hbase.trans_le re; positivity) (by positivity))
      (Real.rpow_le_rpow_of_exponent_le hU1 (neg_le_neg re)) (Real.rpow_nonneg (Nat.cast_nonneg _) _) (by positivity)
  have row (i : ι) (hi : i ∈ Z) : (∑ j ∈ Z, G i j) ≤ A+J*E := calc
    _ ≤ ∑ j ∈ Z, ((if j=i then A else 0)+E) := by
      apply sum_le_sum
      intro j hj
      by_cases h : j=i
      · subst j
        simpa only [ite_true] using ((diagonal_correlation (χ i) (s i) (hzero i hi).2.2.2.2.1 hσ' hU :
          G i i ≤ A).trans (le_add_of_nonneg_right hE))
      · simpa only [ite_eq_right h, zero_add] using bound i hi j hj (Ne.symm h)
    _ = _ := by simp [sum_add_distrib,hi,J]
  have hmass : (∑ i ∈ Z, ∑ j ∈ Z, G i j) ≤ J*(A+J*E) :=
    (sum_le_sum row).trans_eq (by simp [J, mul_add])
  have hdet := zero_family_correlation_bound Z q χ s hU hUK hσ0
    (fun i hi => ⟨(hzero i hi).1,(hzero i hi).2.2⟩) hcut (fun n => (n:ℝ))
    (fun n _ => Nat.cast_nonneg n) (fun n hn h => False.elim
      ((Nat.cast_ne_zero.mpr (hU.trans (mem_Ioc.mp hn).1).ne') h))
  have htop : (J/2)^2 ≤ H^4*(J*(A+J*E)) :=
    hdet.trans (mul_le_mul (detector_harmonic_energy U K Y) hmass
      (sum_nonneg fun i _ => sum_nonneg fun j _ => norm_nonneg _) (by positivity))
  have hlast : H^4*E ≤ 1/8 := hcross
  have absorb := mul_le_mul_of_nonneg_left hlast (sq_nonneg J)
  have prod : J*J ≤ (8*H^4*A)*J := by nlinarith only [htop,absorb]
  have final : J ≤ 8*H^4*A := by
    rcases eq_or_lt_of_le hJ with hh|hh
    · rw [←hh]; positivity
    · exact le_of_mul_le_mul_right prod hh
  exact final.trans_eq (by dsimp only [H,A,Y]; ring)

end Conjectures.Goldbach.BinaryShiftZeroDensity
end
end

section
open Complex DirichletCharacter Finset Filter Asymptotics
open scoped Topology
noncomputable section
namespace Conjectures.Goldbach.BinaryShiftZeroDensity

/-- At bounded height the number of distinct primitive characters admitting
a zero to the right of 1-H/log Q costs only five logarithms of the
conductor cutoff. Each character may contribute any one of its zeros. -/
theorem primitive_nearOne_log_count {ι : Type*} (H T : ℝ) (hH : 0 ≤ H) (hT : 0 ≤ T) :
    ∀ᶠ Q : ℕ in atTop, ∀ (Z : Finset ι) (q : ι → ℕ) [∀ i, NeZero (q i)]
      (χ : (i : ι) → DirichletCharacter ℂ (q i)) (s : ι → ℂ),
      Set.InjOn (fun i => (⟨q i,χ i⟩ : Σ k : ℕ, DirichletCharacter ℂ k)) (Z:Set ι) →
      (∀ i ∈ Z, q i ≤ Q ∧ (χ i).IsPrimitive ∧ χ i ≠ 1 ∧ (χ i).LFunction (s i) = 0 ∧
        1-H/Real.log Q ≤ (s i).re ∧ ‖s i‖ ≤ T) →
      (Z.card:ℝ) ≤ (8*32^5*Real.exp (64*H))*(1+Real.log Q)^5 := by
  have castT : Tendsto (fun Q : ℕ => (Q:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have logT := Real.tendsto_log_atTop.comp castT
  have little := ((isLittleO_log_rpow_rpow_atTop (4:ℝ) (show (0:ℝ) < 1 by norm_num)).comp_tendsto castT).eventuallyLE
  let D := 33^4*(4*(1+2*(2*T+1)))
  have hD : 0 ≤ D := by dsimp [D]; positivity
  filter_upwards [little,logT.eventually_ge_atTop (max 1 (4*H)),castT.eventually_ge_atTop (max (4*(1+2*T)) (8*D)),
    eventually_ge_atTop (2:ℕ)] with Q hlog4 hlower hlarge hQ
  intro Z q _ χ s hinj hz
  let x := (Q:ℝ)
  let l := Real.log x
  let σ := 1-H/l
  let U := Q^8
  let K := Q^24
  let Y := U*K
  have hx1 : 1 ≤ x := by dsimp only [x]; exact_mod_cast (show 1 ≤ Q by omega)
  have hx := zero_lt_one.trans_le hx1
  have hl : 1 ≤ l := (le_max_left ..).trans hlower
  have hl0 := zero_lt_one.trans_le hl
  have hHlog : 4*H ≤ l := (le_max_right ..).trans hlower
  have hl4 : l^4 ≤ x := by
    change ‖l^(4:ℝ)‖ ≤ ‖x^(1:ℝ)‖ at hlog4
    simpa only [Real.rpow_one, show (4:ℝ) = (4:ℕ) from rfl, Real.rpow_natCast, Real.norm_of_nonneg (pow_nonneg hl0.le 4),
      Real.norm_of_nonneg hx.le] using hlog4
  have hs : 3/4 ≤ σ := by
    have := (div_le_iff₀ hl0).mpr (show H ≤ (1/4)*l by linarith only [hHlog])
    dsimp only [σ]; linarith
  have hs1 : σ ≤ 1 := sub_le_self _ (div_nonneg hH hl0.le)
  have hs0 : 0 < σ := by linarith only [hs]
  have hb : 1/2 ≤ 2*σ-1 := by linarith only [hs]
  have hU : 0 < U := pow_pos (by omega) _
  have hUK : U ≤ K := Nat.pow_le_pow_right (by omega) (by norm_num : 8 ≤ 24)
  have hu1 : (1:ℝ) ≤ U := by exact_mod_cast hU
  have hk1 : (1:ℝ) ≤ K := by exact_mod_cast hU.trans_le hUK
  have invHalf (m : ℕ) : (x^(2*m:ℕ))^(-(1/2:ℝ)) = (x^m)⁻¹ := by
    rw [←Real.rpow_natCast_mul hx.le, show ((2*m:ℕ):ℝ)*(-(1/2)) = -(m:ℝ) by push_cast; ring, Real.rpow_neg hx.le,Real.rpow_natCast]
  have Uk : (U:ℝ) = x^8 := Nat.cast_pow Q 8
  have Kk : (K:ℝ) = x^24 := Nat.cast_pow Q 24
  have Yk : (Y:ℝ) = x^32 := by rw [show (Y:ℝ) = (U:ℝ)*K from Nat.cast_mul ..,Uk,Kk,←pow_add]
  have Ylog : Real.log (Y:ℝ) = 32*l := by rw [Yk,Real.log_pow]; rfl
  have recipK : (K:ℝ)^(-σ) ≤ (x^12)⁻¹ := (Real.rpow_le_rpow_of_exponent_le hk1 (show -σ ≤ -(1/2) by linarith only [hs])).trans_eq
    (by rw [Kk]; exact invHalf 12)
  have recipU : (U:ℝ)^(-(2*σ-1)) ≤ (x^4)⁻¹ := (Real.rpow_le_rpow_of_exponent_le hu1 (neg_le_neg hb)).trans_eq
    (by rw [Uk]; exact invHalf 4)
  have tdiv : T/σ ≤ 2*T := (div_le_div_of_nonneg_left hT (by norm_num : (0:ℝ) < 1/2) (by linarith only [hs])).trans_eq (by ring)
  have cut : (U:ℝ)*(2*(Q:ℝ)*(1+T/σ)*(K:ℝ)^(-σ)) ≤ 1/2 := calc
    _ ≤ x^8*(2*x*(1+2*T)*(x^12)⁻¹) := by
      rw [Uk]
      exact mul_le_mul_of_nonneg_left (mul_le_mul (mul_le_mul_of_nonneg_left (add_le_add_right tdiv _) (by positivity))
        recipK (Real.rpow_nonneg (by positivity) _) (by positivity)) (by positivity)
    _ = 2*(1+2*T)/x^3 := by field_simp
    _ ≤ _ := by
      apply (div_le_iff₀ (pow_pos hx 3)).mpr
      have hbig : 4*(1+2*T) ≤ x := (le_max_left ..).trans hlarge
      have h3 : x ≤ x^3 := by simpa using pow_le_pow_right₀ hx1 (show 1 ≤ 3 by norm_num)
      linarith only [hbig,h3]
  have invσ : (2*T+1)/(2*σ-1) ≤ 2*(2*T+1) :=
    (div_le_div_of_nonneg_left (by positivity) (by norm_num : (0:ℝ) < 1/2) hb).trans_eq (by ring)
  have largeH : (1+Real.log (Y:ℝ))^4 ≤ 33^4*l^4 := by
    rw [←mul_pow,Ylog]
    exact pow_le_pow_left₀ (by positivity) (by linarith only [hl]) 4
  have corr : (1+Real.log (Y:ℝ))^4 * (4*(Q:ℝ)^2*(1+(2*T+1)/(2*σ-1))*(U:ℝ)^(-(2*σ-1))) ≤ 1/8 := calc
    _ ≤ (33^4*l^4)*(4*x^2*(1+2*(2*T+1))*(x^4)⁻¹) := mul_le_mul largeH
      (mul_le_mul (mul_le_mul_of_nonneg_left (add_le_add_right invσ _) (by positivity))
        recipU (Real.rpow_nonneg (by positivity) _) (by positivity)) (by positivity) (by positivity)
    _ = D*l^4/x^2 := by dsimp only [D]; field_simp
    _ ≤ D*x/x^2 := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hl4 hD) (sq_nonneg _)
    _ = D/x := by field_simp
    _ ≤ _ := (div_le_iff₀ hx).mpr (by have hh : 8*D ≤ x := (le_max_right ..).trans hlarge; linarith only [hh])
  have fixed := distinct_primitive_zero_density Z q χ s hinj hU hUK (by linarith only [hs] : 1/2 < σ) hs1 hT hz cut corr
  have yp : (Y:ℝ)^(2*(1-σ)) = Real.exp (64*H) := by
    rw [Real.rpow_def_of_pos (by exact_mod_cast Nat.mul_pos hU (hU.trans_le hUK) : 0 < (Y:ℝ)) _, Ylog]
    congr 1
    dsimp only [σ]
    field_simp
    ring
  have hlog5 : (1+Real.log (Y:ℝ))^5 ≤ 32^5*(1+l)^5 := by
    rw [←mul_pow,Ylog]
    exact pow_le_pow_left₀ (by positivity) (by linarith) 5
  apply fixed.trans
  change 8*(1+Real.log (Y:ℝ))^5*(Y:ℝ)^(2*(1-σ)) ≤ _
  rw [yp]
  exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlog5 (by norm_num : (0:ℝ) ≤ 8)) (Real.exp_pos _).le).trans_eq (by dsimp only [l,x]; ring)

end Conjectures.Goldbach.BinaryShiftZeroDensity
end
end

section
open Complex DirichletCharacter Finset Filter Goldbach GoldbachTwistedMellin
noncomputable section
namespace Conjectures.Goldbach.BinaryShiftZeroDensity

/-- Writing a positive level as k+1 permits a finite dependent sum over
all primitive characters with a zero in the indicated rectangle. -/
abbrev PositiveLevelCharacter := Σ k : ℕ, DirichletCharacter ℂ (k+1)

def nearOneRoots (m : ℕ) {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (σ T : ℝ) : Finset ℂ := by
  classical
  exact (exceptionalZeros χ (modelHeight (m+2:ℕ))).filter (fun z => σ ≤ z.re ∧ |z.im| ≤ T)

def nearOneCharacters (m Q : ℕ) (σ T : ℝ) : Finset PositiveLevelCharacter := by
  classical
  exact (range Q).sigma (fun k => univ.filter (fun χ : DirichletCharacter ℂ (k+1) =>
    χ.IsPrimitive ∧ (nearOneRoots m χ σ T).Nonempty))

private theorem positiveLevel_injective :
    Function.Injective (fun p : PositiveLevelCharacter => (⟨p.1+1,p.2⟩ : Σ k : ℕ, DirichletCharacter ℂ k)) := by
  rintro ⟨k,χ⟩ ⟨j,ψ⟩ h
  have e : k+1 = j+1 := congrArg Sigma.fst h
  obtain rfl : k = j := Nat.add_right_cancel e
  exact congrArg (Sigma.mk k) (eq_of_heq (Sigma.mk.inj_iff.mp h).2)

private theorem nearOneCharacters_witnesses (H T : ℝ) (hH : 0 ≤ H) :
    ∀ᶠ Q : ℕ in atTop, ∀ m X : ℕ, Q ≤ X →
      ∃ z : PositiveLevelCharacter → ℂ, ∀ p ∈ nearOneCharacters m Q (1-H/Real.log X) T,
        p.1+1 ≤ Q ∧ p.2.IsPrimitive ∧ p.2 ≠ 1 ∧ p.2.LFunction (z p) = 0 ∧
        1-H/Real.log Q ≤ (z p).re ∧ ‖z p‖ ≤ 1+T := by
  classical
  obtain ⟨d,hd,compact⟩ := ExceptionalZeroCatalogue.bounded_strip 1 T
  have logT := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [logT.eventually_ge_atTop (H/d),eventually_ge_atTop (2:ℕ)] with Q hL hQ
  intro m X hQX
  let Z := nearOneCharacters m Q (1-H/Real.log X) T
  have hqpos : 0 < Real.log Q := Real.log_pos (by exact_mod_cast (show 1 < Q by omega))
  have hQ0 : (0:ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  have logle := Real.log_le_log hQ0 (show (Q:ℝ) ≤ X by exact_mod_cast hQX)
  have hXpos := hqpos.trans_le logle
  have hXd : H/Real.log X ≤ d := (div_le_iff₀ hXpos).mpr (by
    have := (div_le_iff₀ hd).mp (show H/d ≤ Real.log X from hL.trans logle)
    linarith only [this])
  have chosen (p : PositiveLevelCharacter) : ∃ z : ℂ, p ∈ Z → p.1+1 ≤ Q ∧ p.2.IsPrimitive ∧
      p.2 ≠ 1 ∧ p.2.LFunction z = 0 ∧ 1-H/Real.log Q ≤ z.re ∧ ‖z‖ ≤ 1+T := by
    by_cases hin : p ∈ Z
    · obtain ⟨hr,hχ⟩ := Finset.mem_sigma.mp hin
      obtain ⟨hp,⟨z,hz⟩⟩ := (Finset.mem_filter.mp hχ).2
      obtain ⟨root,hnear,him⟩ := Finset.mem_filter.mp hz
      have hh := (mem_exceptionalZeros _ _ z).mp root
      have hnon : p.2 ≠ 1 := by
        intro h
        have e : 1 = p.1+1 := by simpa only [IsPrimitive,h,conductor_one] using hp
        exact compact (p.1+1) e.ge p.2 z him (by linarith only [hnear,hXd]) ((ExceptionalZeroCatalogue.regular_zero p.2 z).mp hh.2.2)
      refine ⟨z,fun _ => ⟨(mem_range.mp hr),hp,hnon,by simpa [regularizedL,hnon] using hh.2.2,?_,?_⟩⟩
      · linarith only [hnear,div_le_div_of_nonneg_left hH hqpos logle]
      · have hright := re_lt_one_of_regularizedL_zero p.2 hh.2.2
        apply (norm_le_abs_re_add_abs_im _).trans
        rw [abs_of_nonneg (by linarith only [hh.1] : 0 ≤ z.re)]
        linarith only [hright,him]
    · exact ⟨0,fun h => (hin h).elim⟩
  choose z hz using chosen
  exact ⟨z,hz⟩

/-- The logarithmic count applies simultaneously at every explicit-formula
height and all scales X at least the primitive-conductor cutoff. This
catalogue includes the primitive principal character. -/
theorem nearOneCharacters_card (H T : ℝ) (hH : 0 ≤ H) (hT : 0 ≤ T) :
    ∀ᶠ Q : ℕ in atTop, ∀ m X : ℕ, Q ≤ X →
      ((nearOneCharacters m Q (1-H/Real.log X) T).card:ℝ) ≤
        (8*32^5*Real.exp (64*H))*(1+Real.log Q)^5 := by
  filter_upwards [primitive_nearOne_log_count (ι := PositiveLevelCharacter) H (1+T) hH (by linarith),
      nearOneCharacters_witnesses H T hH] with Q law choices
  intro m X hQX
  obtain ⟨z,hz⟩ := choices m X hQX
  exact law _ (fun p => p.1+1) (fun p => p.2) z positiveLevel_injective.injOn hz

end Conjectures.Goldbach.BinaryShiftZeroDensity
end
end

section
open Complex DirichletCharacter Finset Filter Goldbach GoldbachTwistedMellin
noncomputable section
namespace Conjectures.Goldbach.BinaryShiftZeroDensity

private theorem nearOneRoots_mass (T : ℝ) (hT : 0 ≤ T) :
    ∃ A : ℝ, 0 < A ∧ ∀ (m q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (σ : ℝ),
      (∑ z ∈ nearOneRoots m χ σ T, (analyticOrderNatAt (regularizedL χ) z:ℝ)) ≤
        A*(1+Real.log q) := by
  classical
  obtain ⟨C,hC,slice⟩ := unconditional_right_slice_count
  let I := Finset.Icc ⌊-T⌋ ⌊T⌋
  let L := Real.log (2*(3+T))
  have hL : 0 ≤ L := Real.log_nonneg (by linarith)
  refine ⟨((I.card:ℝ)+1)*C*(1+L),by positivity,?_⟩
  intro m q _ χ σ
  let Z := nearOneRoots m χ σ T
  let w (z : ℂ) := (analyticOrderNatAt (regularizedL χ) z:ℝ)
  have geom (z : ℂ) (hz : z ∈ Z) : 1/2 ≤ z.re ∧ z.re ≤ 2 ∧ |z.im| ≤ T := by
    obtain ⟨hz,_,hi⟩ := Finset.mem_filter.mp hz
    obtain ⟨hl,_,hr⟩ := (mem_exceptionalZeros ..).mp hz
    have hright := re_lt_one_of_regularizedL_zero χ hr
    exact ⟨by linarith only [hl],by linarith only [hright],hi⟩
  have member (z : ℂ) (hz : z ∈ Z) : ⌊z.im⌋ ∈ I := by
    obtain ⟨lo,hi⟩ := abs_le.mp (geom z hz).2.2
    exact mem_Icc.mpr ⟨Int.floor_mono lo,Int.floor_mono hi⟩
  have hlogq := Real.log_natCast_nonneg q
  have each (j : ℤ) (hj : j ∈ I) : (∑ z ∈ Z.filter (fun z => ⌊z.im⌋=j), w z) ≤
      C*((1+L)*(1+Real.log q)) := by
    have hdist : |(j:ℝ)| ≤ T+1 := by
      have low : (⌊-T⌋:ℝ) ≤ j := by exact_mod_cast (mem_Icc.mp hj).1
      have upper : (j:ℝ) ≤ ⌊T⌋ := by exact_mod_cast (mem_Icc.mp hj).2
      exact abs_le.mpr ⟨by linarith only [low,Int.lt_floor_add_one (-T)],by linarith only [upper,Int.floor_le T]⟩
    have logb : logHeight q j ≤ (1+L)*(1+Real.log q) := calc
      _ ≤ Real.log ((2*(3+T))*(q:ℝ)) := Real.log_le_log (by have := NeZero.pos q; positivity) (by
        nlinarith only [mul_le_mul_of_nonneg_left hdist (Nat.cast_nonneg q)])
      _ = L+Real.log q := Real.log_mul (by positivity) (Nat.cast_ne_zero.mpr (NeZero.ne q))
      _ ≤ _ := by nlinarith only [mul_nonneg hL hlogq]
    apply (slice q χ (j:ℝ) (Z.filter (fun z => ⌊z.im⌋=j)) ?_).trans (mul_le_mul_of_nonneg_left logb hC.le)
    intro z hz
    obtain ⟨hz,eqn⟩ := Finset.mem_filter.mp hz
    refine ⟨(geom _ hz).1,(geom _ hz).2.1,?_⟩
    rw [←eqn]
    exact abs_le.mpr ⟨by linarith only [Int.floor_le z.im],by linarith only [Int.lt_floor_add_one z.im]⟩
  change (∑ z ∈ Z, w z) ≤ _
  calc
    _ = ∑ j ∈ I, ∑ z ∈ Z.filter (fun z => ⌊z.im⌋=j), w z := (sum_fiberwise_of_maps_to member w).symm
    _ ≤ ∑ _j ∈ I, C*((1+L)*(1+Real.log q)) := sum_le_sum each
    _ = (I.card:ℝ)*(C*((1+L)*(1+Real.log q))) := by simp
    _ ≤ _ := by nlinarith only [mul_nonneg hC.le (mul_nonneg (by linarith only [hL] : 0 ≤ 1+L) (by linarith only [hlogq] : 0 ≤ 1+Real.log q))]

/-- A family bound for the actual bounded-height zeros in the signed arc
model, including their analytic multiplicities. -/
theorem nearOne_zero_multiplicity_total (H T : ℝ) (hH : 0 ≤ H) (hT : 0 ≤ T) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ Q : ℕ in atTop, ∀ m X : ℕ, Q ≤ X →
      (∑ p ∈ nearOneCharacters m Q (1-H/Real.log X) T,
        ∑ z ∈ nearOneRoots m p.2 (1-H/Real.log X) T,
          (analyticOrderNatAt (regularizedL p.2) z:ℝ)) ≤ C*(1+Real.log Q)^6 := by
  obtain ⟨A,hA,per⟩ := nearOneRoots_mass T hT
  let D := 8*32^5*Real.exp (64*H)
  have hD : 0 < D := by dsimp only [D]; positivity
  refine ⟨D*A, mul_pos hD hA, ?_⟩
  filter_upwards [nearOneCharacters_card H T hH hT] with Q hc
  intro m X hQX
  let Z := nearOneCharacters m Q (1-H/Real.log X) T
  let l := 1+Real.log (Q:ℝ)
  have hl : 0 ≤ l := by dsimp only [l]; linarith [Real.log_natCast_nonneg Q]
  calc
    _ ≤ ∑ _p ∈ Z, A*l := by
      apply sum_le_sum
      intro p hp
      have hq : p.1+1 ≤ Q := mem_range.mp (Finset.mem_sigma.mp hp).1
      apply (per m _ p.2 _).trans
      apply mul_le_mul_of_nonneg_left _ hA.le
      exact add_le_add_right (Real.log_le_log (by positivity) (by exact_mod_cast hq)) 1
    _ = (Z.card:ℝ)*(A*l) := by simp
    _ ≤ (D*l^5)*(A*l) := mul_le_mul_of_nonneg_right (hc m X hQX) (mul_nonneg hA.le hl)
    _ = _ := by ring

end Conjectures.Goldbach.BinaryShiftZeroDensity
end
end

section
open Finset Filter MeasureTheory Set
noncomputable section
namespace Conjectures.Goldbach.BinaryShiftZeroDensity

private def rankinPower (s : ℝ) : ℕ →* ℝ where
  toFun n := (n:ℝ)^(-s)
  map_one' := by simp
  map_mul' m n := by simp only [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]

private theorem rankinPower_nonneg (s : ℝ) (n : ℕ) : 0 ≤ rankinPower s n :=
  Real.rpow_nonneg (Nat.cast_nonneg _) _

private def rankinSieve (V : ℕ) (s : ℝ) (hs : 0 < s) : BoundingSieve where
  support := ∅
  prodPrimes := primorial V
  prodPrimes_squarefree := squarefree_primorial V
  weights := fun _ => 0
  weights_nonneg _ := le_rfl
  totalMass := 0
  nu := ⟨rankinPower s, by change (0:ℝ)^(-s) = 0; exact Real.zero_rpow (neg_ne_zero.mpr hs.ne')⟩
  nu_mult := ⟨(rankinPower s).map_one, fun {m n} _ => (rankinPower s).map_mul m n⟩
  nu_pos_of_prime p hp _ := Real.rpow_pos_of_pos (Nat.cast_pos.mpr hp.pos) _
  nu_lt_one_of_prime p hp _ := Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (neg_lt_zero.mpr hs)

private theorem rankin_fiber_le (s : ℝ) (hs : 0 < s) (d : ℕ) (J : Finset ℕ)
    (hJ : ∀ n ∈ J, n ≠ 0 ∧ ∏ p ∈ n.primeFactors, p = d) :
    ∑ n ∈ J, rankinPower s n ≤ rankinPower s d *
      ∏ p ∈ d.primeFactors, (1-rankinPower s p)⁻¹ := by
  classical
  let b := rankinPower s
  have hd (n : ℕ) (hn : n ∈ J) : d ∣ n := (hJ n hn).2 ▸ Nat.prod_primeFactors_dvd n
  let K := J.image (fun n => n/d)
  have hK (k : ℕ) (hk : k ∈ K) : k ∈ Nat.factoredNumbers d.primeFactors := by
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hk
    apply Nat.mem_factoredNumbers_of_dvd _ (Nat.div_dvd_of_dvd (hd n hn))
    apply Nat.mem_factoredNumbers_iff_primeFactors_subset.mpr
    exact ⟨(hJ n hn).1,by rw [←(hJ n hn).2,Nat.primeFactors_prod_primeFactors]⟩
  have split_sum : (∑ n ∈ J, b n) = b d * ∑ k ∈ K, b k := by
    rw [Finset.mul_sum,Finset.sum_image]
    · exact Finset.sum_congr rfl (fun n hn => by rw [←map_mul, Nat.mul_div_cancel' (hd n hn)])
    · intro n hn k hk eqn
      change n/d=k/d at eqn
      simpa only [Nat.mul_div_cancel' (hd n hn),Nat.mul_div_cancel' (hd k hk)] using congrArg (d*·) eqn
  have euler := (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
    (f := b) (fun {p} hp => by
      rw [Real.norm_eq_abs,abs_of_nonneg (rankinPower_nonneg s p)]
      exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (neg_lt_zero.mpr hs)) d.primeFactors).2
  have primes : d.primeFactors.filter Nat.Prime = d.primeFactors :=
    Finset.filter_eq_self.mpr (fun p hp => Nat.prime_of_mem_primeFactors hp)
  rw [primes] at euler
  change (∑ n ∈ J, b n) ≤ _
  rw [split_sum]
  apply mul_le_mul_of_nonneg_left _ (rankinPower_nonneg s d)
  calc
    _ = ∑ k ∈ K.subtype (fun k => k ∈ Nat.factoredNumbers d.primeFactors), b k :=
      (Finset.sum_subtype_of_mem b hK).symm
    _ ≤ ∑' k : Nat.factoredNumbers d.primeFactors, b k :=
      euler.summable.sum_le_tsum _ (fun k _ => rankinPower_nonneg s k)
    _ = _ := euler.tsum_eq

/-- Grouping positive integers by their squarefree kernels compares the
truncated Selberg denominator with the initial Dirichlet sum. -/
theorem rankin_initial_sum_le (V : ℕ) (s : ℝ) (hs : 0 < s) :
    (∑ n ∈ Finset.Icc 1 V, (n:ℝ)^(-s)) ≤
      ∑ d ∈ (primorial V).divisors, if d ≤ V then (rankinSieve V s hs).selbergTerms d else 0 := by
  classical
  let rad (n : ℕ) := ∏ p ∈ n.primeFactors, p
  let S := Finset.Icc 1 V
  let D := (primorial V).divisors.filter (· ≤ V)
  have maps (n : ℕ) (hn : n ∈ S) : rad n ∈ D := by
    obtain ⟨hn1,hnV⟩ := Finset.mem_Icc.mp hn
    have bound : rad n ≤ V := (Nat.le_of_dvd hn1 (Nat.prod_primeFactors_dvd n)).trans hnV
    exact Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨(Nat.squarefree_prod_primeFactors n).dvd_primorial.trans
      (primorial_dvd_primorial bound),(primorial_pos V).ne'⟩,bound⟩
  rw [←Finset.sum_filter]
  change (∑ n ∈ S, rankinPower s n) ≤ ∑ d ∈ D, _
  rw [←Finset.sum_fiberwise_of_maps_to maps]
  apply Finset.sum_le_sum
  intro d _
  rw [BoundingSieve.selbergTerms_apply]
  apply rankin_fiber_le s hs
  intro n hn
  obtain ⟨hn,eqn⟩ := Finset.mem_filter.mp hn
  exact ⟨(show 0 < n from (Finset.mem_Icc.mp hn).1).ne',eqn⟩

end Conjectures.Goldbach.BinaryShiftZeroDensity
end
end

section
open Finset Filter MeasureTheory Set OAI.Problem337
noncomputable section
namespace Conjectures.Goldbach.BinaryShiftZeroDensity

/-- The divisor sum associated to a finitely supported sieve weight. -/
def sievePolynomial (D : Finset ℕ) (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ d ∈ D, if d ∣ n then a d else 0

private theorem sievePolynomial_product (D E : Finset ℕ) (a b : ℕ → ℝ) (n : ℕ) (w : ℝ) :
    sievePolynomial D a n * sievePolynomial E b n * w =
      ∑ d ∈ D, ∑ e ∈ E, if Nat.lcm d e ∣ n then a d*b e*w else 0 := by
  simp only [sievePolynomial,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro e _
  by_cases hd : d ∣ n <;> by_cases he : e ∣ n <;> simp [Nat.lcm_dvd_iff,hd,he]

private theorem rankin_multiples_hasSum (s : ℝ) (hs : 1 < s) (d : ℕ) (hd : 0 < d) :
    HasSum (fun n : ℕ => if d ∣ n then rankinPower s n else 0)
      (rankinPower s d * ∑' k : ℕ, rankinPower s k) := by
  have sum : Summable (rankinPower s) := Real.summable_nat_rpow.mpr (by linarith)
  have inj : Function.Injective (d*·) := fun _ _ h => Nat.eq_of_mul_eq_mul_left hd h
  apply (inj.hasSum_iff _).mp
  · simpa [Function.comp_def, map_mul] using sum.hasSum.mul_left (rankinPower s d)
  · intro n hn
    exact ite_eq_right (by rintro ⟨k,rfl⟩; exact hn ⟨k,rfl⟩)

private theorem sievePolynomial_energy (V : ℕ) (hV : 1 ≤ V) (s : ℝ) (hs : 1 < s) :
    let S := rankinSieve V s (by linarith)
    let a := SelbergOptimal.optimalWeight S V
    HasSum (fun n : ℕ => (sievePolynomial S.prodPrimes.divisors a n)^2 * rankinPower s n)
      ((∑' n : ℕ, rankinPower s n) / SelbergOptimal.normalizer S V) := by
  intro S a
  let D := S.prodPrimes.divisors
  let Z := ∑' n : ℕ, rankinPower s n
  have term (d : ℕ) (hd : d ∈ D) (e : ℕ) (he : e ∈ D) :
      HasSum (fun n : ℕ => if Nat.lcm d e ∣ n then a d*a e*rankinPower s n else 0)
        (a d*a e*rankinPower s (Nat.lcm d e)*Z) := by
    have pos := Nat.lcm_pos (Nat.pos_of_mem_divisors hd) (Nat.pos_of_mem_divisors he)
    simpa only [mul_ite,mul_zero,mul_assoc,Z] using (rankin_multiples_hasSum s hs _ pos).mul_left (a d*a e)
  have hsum := hasSum_sum (s := D) (fun d hd => hasSum_sum (s := D) (fun e he => term d hd e he))
  have main : (∑ d ∈ D, ∑ e ∈ D, a d*a e*rankinPower s (Nat.lcm d e)) =
      1 / SelbergOptimal.normalizer S V := by
    rw [←SelbergOptimal.mainSum_optimalWeight S hV]
    change _ = ∑ k ∈ D, BoundingSieve.lambdaSquared a k * rankinPower s k
    exact (SelbergError.sum_lambdaSquared_mul _ S.prodPrimes_ne_zero a (rankinPower s)).symm
  change HasSum (fun n : ℕ => _ ) (Z / SelbergOptimal.normalizer S V)
  rw [show Z / SelbergOptimal.normalizer S V = (∑ d ∈ D, ∑ e ∈ D, a d*a e*rankinPower s (Nat.lcm d e))*Z by rw [main];ring]
  simp only [Finset.sum_mul]
  apply hsum.congr_fun
  intro n
  exact (sievePolynomial_product D D a a n (rankinPower s n)) ▸ by rw [sq]

private theorem rankin_tail (V : ℕ) (hV : 1 ≤ V) (η : ℝ) (hη : 0 < η) :
    let Z := ∑' n : ℕ, rankinPower (1+η) n
    1/η ≤ Z ∧ Z - ∑ n ∈ Finset.Icc 1 V, rankinPower (1+η) n ≤ (V:ℝ)^(-η)/η := by
  intro Z
  let f (x : ℝ) := x^(-(1+η))
  have sum : Summable (fun n : ℕ => f n) := Real.summable_nat_rpow.mpr (by linarith)
  have anti (k : ℕ) (hk : 1 ≤ k) : AntitoneOn f (Set.Ici (k:ℝ)) := by
    intro x hx y _ hxy
    exact Real.rpow_le_rpow_of_nonpos ((Nat.cast_pos.mpr (show 0 < k from hk)).trans_le hx) hxy (by linarith)
  have nonneg (k : ℕ) (x : ℝ) (hx : x ∈ Set.Ioi (k:ℝ)) : 0 ≤ f x :=
    Real.rpow_nonneg ((Nat.cast_nonneg _).trans hx.le) _
  have integral (k : ℕ) (hk : 1 ≤ k) : (∫ x in Set.Ioi (k:ℝ), f x) = (k:ℝ)^(-η)/η := by
    rw [show (∫ x in Set.Ioi (k:ℝ), f x) = _ from integral_Ioi_rpow_of_lt (by linarith : -(1+η)< -1)
      (Nat.cast_pos.mpr (show 0 < k from hk)),show -(1+η)+1 = -η by ring]
    ring
  have f0 : f 0 = 0 := Real.zero_rpow (by linarith)
  have allsum := sum.sum_add_tsum_nat_add 1
  have lower := (anti 1 le_rfl).integral_le_tsum_comp_add 1 sum (nonneg 1)
  rw [integral 1 le_rfl] at lower
  simp only [Nat.cast_one,Real.one_rpow] at lower
  simp only [Finset.sum_range_one,Nat.cast_zero,f0,zero_add] at allsum
  constructor
  · exact lower.trans_eq allsum
  · have hi := (anti V hV).tsum_comp_add_le_integral V
           (integrableOn_Ioi_rpow_of_lt (by linarith : -(1+η)< -1) (Nat.cast_pos.mpr (show 0 < V from hV))) (nonneg V)
    rw [integral V hV] at hi
    have initial : (∑ n ∈ Finset.Icc 1 V, rankinPower (1+η) n) = ∑ n ∈ Finset.range (V+1), f n := by
      rw [←Finset.Ico_add_one_right_eq_Icc,Finset.sum_Ico_eq_sub (fun n => rankinPower (1+η) n) (by omega)]
      simp only [Finset.sum_range_one,show rankinPower (1+η) 0=0 from f0,sub_zero]
      rfl
    rw [initial]
    change (∑' n : ℕ, f n) - _ ≤ _
    rw [←sum.sum_add_tsum_nat_add (V+1),add_sub_cancel_left]
    simpa only [Nat.add_assoc] using hi

end Conjectures.Goldbach.BinaryShiftZeroDensity
end
end

section
open Finset Filter OAI.Problem337
noncomputable section
namespace Conjectures.Goldbach.BinaryShiftZeroDensity

/-- Selberg weights for a Dirichlet polynomial. The harmonic mass away
from 1 has a geometric bound in the product of the tilt and the logarithm
of the support. The same weights work for every finite sample. -/
theorem exists_sievePolynomial_harmonic (V : ℕ) (hV : 1 < V) (η : ℝ) (hη : 0 < η) :
    ∃ a : ℕ → ℝ, a 1 = 1 ∧ (∀ d, |a d| ≤ 1) ∧
      ∀ (Y : ℕ) (I : Finset ℕ), (∀ n ∈ I, 2 ≤ n ∧ n ≤ Y) →
        (∑ n ∈ I, (sievePolynomial (Finset.Icc 1 V) a n)^2 / (n:ℝ)) ≤
          (Y:ℝ)^η * ((V:ℝ)^(-η) / (1-(V:ℝ)^(-η))) := by
  classical
  let s := 1+η
  have hs : 1 < s := by dsimp only [s]; linarith
  let S := rankinSieve V s (zero_lt_one.trans hs)
  let D := S.prodPrimes.divisors
  let R := Finset.Icc 1 V
  let a := SelbergOptimal.optimalWeight S V
  have a1 : a 1 = 1 := SelbergOptimal.optimalWeight_one S hV.le
  have off (d : ℕ) (hd : d ∉ D) : a d = 0 := by
    have h : ¬d ∣ S.prodPrimes := fun hd' => hd (Nat.mem_divisors.mpr ⟨hd',S.prodPrimes_ne_zero⟩)
    simp only [a,SelbergOptimal.optimalWeight,ite_eq_right h]
  refine ⟨a,a1,?_,?_⟩
  · intro d
    by_cases hd : d ∈ D
    · rw [show a d = _ from SelbergOptimal.optimalWeight_formula S V d (Nat.dvd_of_mem_divisors hd)]
      convert SelbergOptimal.abs_normalized_complement_le_one S hV.le (Nat.dvd_of_mem_divisors hd) using 1
      unfold SelbergOptimal.complementNormalizer
      congr 1
      ring
    · simp [off d hd]
  intro Y I hI
  have same (n : ℕ) : sievePolynomial R a n = sievePolynomial D a n := by
    let f (d : ℕ) := if d ∣ n then a d else 0
    change (∑ d ∈ R, f d) = ∑ d ∈ D, f d
    calc
      _ = ∑ d ∈ R ∩ D, f d := (Finset.sum_subset Finset.inter_subset_left (fun d hr h => by
        have hd : d ∉ D := fun hd => h (Finset.mem_inter.mpr ⟨hr,hd⟩)
        simp [f,off d hd])).symm
      _ = _ := Finset.sum_subset Finset.inter_subset_right (fun d hd h => by
        have hVd : V < d := lt_of_not_ge (fun h' => h (Finset.mem_inter.mpr
          ⟨Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd,h'⟩,hd⟩))
        simp [f,a,SelbergOptimal.optimalWeight_eq_zero_of_lt S hVd])
  let f (n : ℕ) := (sievePolynomial D a n)^2 * rankinPower s n
  let Z := ∑' n : ℕ, rankinPower s n
  let G := SelbergOptimal.normalizer S V
  let c := (V:ℝ)^(-η)
  have hc : 0 ≤ c := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hc1 : c < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hV) (by linarith)
  have hG : 0 < G := SelbergOptimal.normalizer_pos _ hV.le
  obtain ⟨hZ,tail⟩ := rankin_tail V hV.le η hη
  have init : (∑ n ∈ Finset.Icc 1 V, rankinPower s n) ≤ G :=
    rankin_initial_sum_le V s (zero_lt_one.trans hs)
  have tail' : Z-G ≤ c*(1/η) := by
    change Z - _ ≤ c/η at tail
    linarith only [tail,init,show c/η=c*(1/η) by ring]
  have Glo : (1-c)*Z ≤ G := by
    have h := mul_le_mul_of_nonneg_left hZ hc
    change c*(1/η) ≤ c*Z at h
    linarith only [tail',h]
  have ratio : Z/G - 1 ≤ c/(1-c) := by
    have main : Z/G ≤ 1/(1-c) := (div_le_div_iff₀ hG (sub_pos.mpr hc1)).mpr (by linarith only [Glo])
    calc
      Z/G-1 ≤ 1/(1-c)-1 := by linarith only [main]
      _ = _ := by field_simp [ne_of_gt (sub_pos.mpr hc1)]; ring
  have sum : HasSum f (Z/G) := sievePolynomial_energy V hV.le s hs
  have f0 (n : ℕ) : 0 ≤ f n := mul_nonneg (sq_nonneg _) (rankinPower_nonneg s n)
  have f1 : f 1 = 1 := by
    have p1 : sievePolynomial D a 1 = 1 := by
      simp [sievePolynomial,Nat.dvd_one,Finset.sum_ite_eq',D,S.prodPrimes_ne_zero,a1]
    simp [f,p1]
  have h1 : (1:ℕ) ∉ I := fun h => by have := (hI 1 h).1; omega
  have small := sum.summable.sum_le_tsum (insert 1 I) (fun n _ => f0 n)
  rw [sum.tsum_eq,Finset.sum_insert h1,f1] at small
  have lowmass : ∑ n ∈ I, f n ≤ c/(1-c) := by linarith only [small,ratio]
  change _ ≤ (Y:ℝ)^η*(c/(1-c))
  calc
    _ ≤ ∑ n ∈ I, (Y:ℝ)^η*f n := by
      apply Finset.sum_le_sum
      intro n hn
      obtain ⟨hn1,hnY⟩ := hI n hn
      have hn0 : 0 < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
      have ident : (n:ℝ)^η * rankinPower s n = (n:ℝ)⁻¹ := by
        change _*(n:ℝ)^(-(1+η)) = _
        rw [←Real.rpow_add hn0,show η + -(1+η) = -1 by ring,Real.rpow_neg_one]
      change (sievePolynomial R a n)^2 / _ ≤ _
      rw [same n,div_eq_mul_inv,←ident,show _^2*((n:ℝ)^η*rankinPower s n) = (n:ℝ)^η*f n by dsimp only [f];ring]
      exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hn0.le (by exact_mod_cast hnY) hη.le) (f0 n)
    _ = (Y:ℝ)^η * ∑ n ∈ I, f n := (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left lowmass (Real.rpow_nonneg (Nat.cast_nonneg _) _)

end Conjectures.Goldbach.BinaryShiftZeroDensity
end
end

section
open Complex Finset DirichletCharacter
noncomputable section
namespace Conjectures.Goldbach.BinaryShiftZeroDensity

private def sample {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ) (n : ℕ) : ℂ :=
  (n:ℂ)^(-s)*χ (n:ZMod q)

private theorem sample_mul {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ) (l k : ℕ) :
    sample χ s (l*k) = sample χ s l * sample χ s k := by
  simp only [sample,Nat.cast_mul,natCast_mul_natCast_cpow,map_mul]
  ring

private theorem multiples_prefix {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ) (Y l : ℕ) (hl : 0 < l) :
    (∑ n ∈ Finset.Icc 1 Y, if l ∣ n then sample χ s n else 0) = sample χ s l * dirichletPrefix χ s (Y/l) := by
  have sets : ((Finset.Icc 1 (Y/l)).image (l*·)) = (Finset.Icc 1 Y).filter (l ∣ ·) := by
    ext n
    constructor
    · intro h
      obtain ⟨k,hk,rfl⟩ := mem_image.mp h
      obtain ⟨hk1,hkY⟩ := mem_Icc.mp hk
      have leY : l*k ≤ Y := by simpa only [Nat.mul_comm l] using (Nat.le_div_iff_mul_le hl).mp hkY
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.mul_pos hl hk1,leY⟩,dvd_mul_right ..⟩
    · intro h
      obtain ⟨hn,d,k⟩ := mem_filter.mp h
      subst n
      have hd1 : 1 ≤ d := by
        have hn1 := (mem_Icc.mp hn).1
        cases d with
        | zero => simp at hn1
        | succ k => omega
      exact mem_image.mpr ⟨d,mem_Icc.mpr ⟨hd1,
        (Nat.le_div_iff_mul_le hl).mpr (by simpa only [Nat.mul_comm d] using (mem_Icc.mp hn).2)⟩,rfl⟩
  rw [←Finset.sum_filter,←sets,Finset.sum_image (fun _ _ _ _ h => Nat.mul_left_cancel hl h)]
  change _ = sample χ s l * ∑ k ∈ Finset.Icc 1 (Y/l), sample χ s k
  simp only [Finset.mul_sum,sample_mul]

private theorem floor_rpow_scale (l Y : ℕ) (hl : 0 < l) (hlY : l ≤ Y) (σ : ℝ) (hσ : 0 < σ) (hσ1 : σ ≤ 1) :
    (l:ℝ)^(-σ) * ((Y/l:ℕ):ℝ)^(-σ) ≤ 2*(Y:ℝ)^(-σ) := by
  let K := Y/l
  have k1 : 1 ≤ K := Nat.div_pos hlY hl
  have hk : (1:ℝ) ≤ K := by exact_mod_cast k1
  have l0 : 0 < (l:ℝ) := Nat.cast_pos.mpr hl
  have Y0 : 0 < (Y:ℝ) := Nat.cast_pos.mpr (hl.trans_le hlY)
  have hfloor : (Y:ℝ) < (l:ℝ)*(K+1) := by exact_mod_cast Nat.lt_mul_div_succ Y hl
  have cmp : (Y:ℝ)/2 ≤ (l:ℝ)*K := by nlinarith only [hfloor,mul_le_mul_of_nonneg_left hk l0.le]
  have pw : (2:ℝ)^σ ≤ 2 := by simpa only [Real.rpow_one] using
    Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hσ1
  calc
    _ = ((l:ℝ)*(K:ℝ))^(-σ) := (Real.mul_rpow l0.le (Nat.cast_nonneg _)).symm
    _ ≤ ((Y:ℝ)/2)^(-σ) := Real.rpow_le_rpow_of_nonpos (by positivity) cmp (neg_nonpos.mpr hσ.le)
    _ = (Y:ℝ)^(-σ)*(2:ℝ)^σ := by rw [Real.div_rpow Y0.le (by norm_num),Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),div_inv_eq_mul]
    _ ≤ _ := (mul_le_mul_of_nonneg_left pw (Real.rpow_nonneg Y0.le _)).trans_eq (mul_comm ..)

private def sieveSample {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ) (V W : ℕ) (a b : ℕ → ℝ) (n : ℕ) : ℂ :=
  ((sievePolynomial (Finset.Icc 1 V) a n * sievePolynomial (Finset.Icc 1 W) b n : ℝ):ℂ) * sample χ s n

private def sievePrefixMain {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ) (V W : ℕ) (a b : ℕ → ℝ) : ℂ :=
  ∑ d ∈ Finset.Icc 1 V, ∑ e ∈ Finset.Icc 1 W, ((a d*b e:ℝ):ℂ)*sample χ s (Nat.lcm d e)*χ.LFunction s

private theorem sievePrefix_exact {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ)
    (V W Y : ℕ) (a b : ℕ → ℝ) :
    (∑ n ∈ Finset.Icc 1 Y, sieveSample χ s V W a b n) =
      ∑ d ∈ Finset.Icc 1 V, ∑ e ∈ Finset.Icc 1 W,
        ((a d*b e:ℝ):ℂ)*sample χ s (Nat.lcm d e)*dirichletPrefix χ s (Y/Nat.lcm d e) := by
  classical
  let D := Finset.Icc 1 V
  let E := Finset.Icc 1 W
  let I := Finset.Icc 1 Y
  let w (d e : ℕ) : ℂ := ((a d*b e:ℝ):ℂ)*sample χ s (Nat.lcm d e)
  have split (n : ℕ) : sieveSample χ s V W a b n =
      ∑ d ∈ D, ∑ e ∈ E, ((a d*b e:ℝ):ℂ)*(if Nat.lcm d e ∣ n then sample χ s n else 0) := by
    have h := sievePolynomial_product D E a b n 1
    simp only [mul_one] at h
    change ((_ : ℝ):ℂ)*sample χ s n = _
    rw [h]
    simp only [Complex.ofReal_sum,Finset.sum_mul]
    apply sum_congr rfl
    intro d _
    apply sum_congr rfl
    intro e _
    split_ifs <;> simp
  have expanded : (∑ n ∈ I, sieveSample χ s V W a b n) =
      ∑ d ∈ D, ∑ e ∈ E, w d e*dirichletPrefix χ s (Y/Nat.lcm d e) := by
    simp only [split]
    rw [sum_comm]
    apply sum_congr rfl
    intro d hd
    rw [sum_comm]
    apply sum_congr rfl
    intro e he
    rw [←Finset.mul_sum,multiples_prefix χ s Y _ (Nat.lcm_pos (mem_Icc.mp hd).1 (mem_Icc.mp he).1)]
    dsimp only [w]
    ring
  exact expanded

/-- The two divisor weights may have different lengths. Each pair is
summed on multiples of its lcm; the character L-value in the main term
is independent of the truncation endpoint. -/
theorem weighted_prefix_error {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (s : ℂ) (hs : 0 < s.re) (hs1 : s.re ≤ 1) (V W Y : ℕ) (hY : V*W ≤ Y)
    (a b : ℕ → ℝ) (ha : ∀ d, |a d| ≤ 1) (hb : ∀ e, |b e| ≤ 1) :
    ‖(∑ n ∈ Finset.Icc 1 Y, sieveSample χ s V W a b n) - sievePrefixMain χ s V W a b‖ ≤
      (V:ℝ)*W*(4*(q:ℝ)*(1+‖s‖/s.re)*(Y:ℝ)^(-s.re)) := by
  classical
  let D := Finset.Icc 1 V
  let E := Finset.Icc 1 W
  let I := Finset.Icc 1 Y
  let w (d e : ℕ) : ℂ := ((a d*b e:ℝ):ℂ)*sample χ s (Nat.lcm d e)
  have dl (d : ℕ) (hd : d ∈ D) (e : ℕ) (he : e ∈ E) :
      0 < Nat.lcm d e ∧ Nat.lcm d e ≤ Y :=
    ⟨Nat.lcm_pos (mem_Icc.mp hd).1 (mem_Icc.mp he).1,
     (Nat.lcm_le_mul (mem_Icc.mp hd).1 (mem_Icc.mp he).1).trans ((Nat.mul_le_mul (mem_Icc.mp hd).2 (mem_Icc.mp he).2).trans hY)⟩
  have expanded : (∑ n ∈ I, sieveSample χ s V W a b n) =
      ∑ d ∈ D, ∑ e ∈ E, w d e*dirichletPrefix χ s (Y/Nat.lcm d e) :=
    sievePrefix_exact χ s V W Y a b
  let C := 2*(q:ℝ)*(1+‖s‖/s.re)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  let B := 4*(q:ℝ)*(1+‖s‖/s.re)*(Y:ℝ)^(-s.re)
  have error (d : ℕ) (hd : d ∈ D) (e : ℕ) (he : e ∈ E) :
      ‖w d e*(dirichletPrefix χ s (Y/Nat.lcm d e)-χ.LFunction s)‖ ≤ B := by
    let l := Nat.lcm d e
    obtain ⟨hl,hlY⟩ := dl d hd e he
    have ab : ‖((a d*b e:ℝ):ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real,Real.norm_eq_abs,abs_mul]
      simpa only [one_mul] using mul_le_mul (ha d) (hb e) (abs_nonneg _) zero_le_one
    have wt : ‖w d e‖ ≤ (l:ℝ)^(-s.re) := by
      dsimp only [w,sample]
      simp only [norm_mul,norm_natCast_cpow_of_pos hl,neg_re]
      exact (mul_le_mul ab (mul_le_mul_of_nonneg_left (χ.norm_le_one _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
        (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (norm_nonneg _)) zero_le_one).trans_eq (by ring)
    have p := prefix_error χ hχ hs (Y/l) (Nat.div_pos hlY hl)
    rw [norm_mul]
    apply (mul_le_mul wt p (norm_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)).trans
    change _*(C*_) ≤ B
    calc
      _ = C*((l:ℝ)^(-s.re)*((Y/l:ℕ):ℝ)^(-s.re)) := by ring
      _ ≤ C*(2*(Y:ℝ)^(-s.re)) := mul_le_mul_of_nonneg_left (floor_rpow_scale l Y hl hlY _ hs hs1) hC
      _ = _ := by dsimp only [C,B];ring
  change ‖(∑ n ∈ I, _) - ∑ d ∈ D, ∑ e ∈ E, w d e*χ.LFunction s‖ ≤ (V:ℝ)*W*B
  rw [expanded,←Finset.sum_sub_distrib]
  simp only [←Finset.sum_sub_distrib,←mul_sub]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _d ∈ D, ∑ _e ∈ E, B := by
      apply sum_le_sum
      intro d hd
      exact (norm_sum_le _ _).trans (sum_le_sum (error d hd))
    _ = _ := by simp [D,E]; ring

end Conjectures.Goldbach.BinaryShiftZeroDensity
end
end

section
open Complex Finset DirichletCharacter
noncomputable section
namespace Conjectures.Goldbach.BinaryShiftZeroDensity

private theorem sample_norm_comparison {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ)
    (σ : ℝ) (hσ : σ ≤ s.re) (h1 : σ ≤ 1) (n Y : ℕ) (hn : 1 ≤ n) (hnY : n ≤ Y) :
    ‖sample χ s n‖ ≤ (Y:ℝ)^(1-σ)/(n:ℝ) := by
  have n1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have n0 := zero_lt_one.trans_le n1
  have P : (n:ℝ)^(1-s.re) ≤ (Y:ℝ)^(1-σ) :=
    (Real.rpow_le_rpow_of_exponent_le n1 (by linarith)).trans
      (Real.rpow_le_rpow n0.le (by exact_mod_cast hnY) (sub_nonneg.mpr h1))
  calc
    _ ≤ (n:ℝ)^(-s.re) := by
      rw [sample,norm_mul,norm_natCast_cpow_of_pos hn,neg_re]
      exact mul_le_of_le_one_right (Real.rpow_nonneg n0.le _) (χ.norm_le_one _)
    _ = (n:ℝ)^(1-s.re)/(n:ℝ) := by rw [sub_eq_add_neg,Real.rpow_add n0,Real.rpow_one];field_simp
    _ ≤ _ := div_le_div_of_nonneg_right P n0.le

private theorem short_weighted_sum {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ)
    (σ : ℝ) (hσ : σ ≤ s.re) (h1 : σ ≤ 1) (U V W : ℕ) (a b : ℕ → ℝ) :
    let J := Finset.Ioc 1 U
    let A := sievePolynomial (Finset.Icc 1 V) a
    let B := sievePolynomial (Finset.Icc 1 W) b
    ‖∑ n ∈ J, sieveSample χ s V W a b n‖ ≤ (U:ℝ)^(1-σ)*
      (√(∑ n ∈ J, (A n)^2/(n:ℝ)) * √(∑ n ∈ J, (B n)^2/(n:ℝ))) := by
  intro J A B
  let e (F : ℕ → ℝ) (n : ℕ) := (F n)^2/(n:ℝ)
  have en (F : ℕ → ℝ) (n : ℕ) : 0 ≤ e F n := div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)
  have factor (n : ℕ) (hn : n ∈ J) : |A n*B n|/(n:ℝ) = √(e A n)*√(e B n) := by
    have n0 : 0 < (n:ℝ) := Nat.cast_pos.mpr (Nat.zero_lt_one.trans (mem_Ioc.mp hn).1)
    dsimp only [e]
    rw [Real.sqrt_div (sq_nonneg _),Real.sqrt_div (sq_nonneg _),Real.sqrt_sq_eq_abs,Real.sqrt_sq_eq_abs,abs_mul,
      div_mul_div_comm,Real.mul_self_sqrt n0.le]
  apply (norm_sum_le ..).trans
  calc
    _ ≤ ∑ n ∈ J, (U:ℝ)^(1-σ)*(√(e A n)*√(e B n)) := by
      apply sum_le_sum
      intro n hn
      obtain ⟨hlo,hhi⟩ := mem_Ioc.mp hn
      change ‖((A n*B n:ℝ):ℂ)*sample χ s n‖ ≤ _
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,←factor n hn]
      exact (mul_le_mul_of_nonneg_left (sample_norm_comparison χ s σ hσ h1 n U hlo.le hhi) (abs_nonneg _)).trans_eq
        (by ring)
    _ = (U:ℝ)^(1-σ)*∑ n ∈ J, √(e A n)*√(e B n) := (mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.sum_sqrt_mul_sqrt_le J (en A) (en B)) (Real.rpow_nonneg (Nat.cast_nonneg _) _)

/-- Two short Selberg weights detect an actual L-zero on a long interval.
Their short initial leakage is measured by the product of harmonic
square energies rather than a divisor-function bound. -/
theorem sieved_zero_detector {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (s : ℂ) (hs : 0 < s.re) (hz : χ.LFunction s = 0) (σ : ℝ) (hσ : σ ≤ s.re)
    (U V W Y : ℕ) (hU : 1 ≤ U) (hV : 1 ≤ V) (hW : 1 ≤ W) (hUY : U ≤ Y) (hY : V*W ≤ Y)
    (a b : ℕ → ℝ) (ha : ∀ d, |a d| ≤ 1) (hb : ∀ e, |b e| ≤ 1) (ha1 : a 1=1) (hb1 : b 1=1) :
    let J := Finset.Ioc 1 U
    let A := sievePolynomial (Finset.Icc 1 V) a
    let B := sievePolynomial (Finset.Icc 1 W) b
    1-(V:ℝ)*W*(4*(q:ℝ)*(1+‖s‖/s.re)*(Y:ℝ)^(-s.re))-
      (U:ℝ)^(1-σ)*(√(∑ n ∈ J, (A n)^2/(n:ℝ))*√(∑ n ∈ J, (B n)^2/(n:ℝ))) ≤
      ‖∑ n ∈ Finset.Ioc U Y, sieveSample χ s V W a b n‖ := by
  intro J A B
  have hs1 : s.re < 1 := lt_of_not_ge (fun h => (χ.LFunction_ne_zero_of_one_le_re (Or.inl hχ) h) hz)
  have rough := weighted_prefix_error χ hχ s hs hs1.le V W Y hY a b ha hb
  simp only [sievePrefixMain,hz,mul_zero,sum_const_zero,sub_zero] at rough
  have sh := short_weighted_sum χ s σ hσ (hσ.trans hs1.le) U V W a b
  let f := sieveSample χ s V W a b
  have cut : Finset.Icc 1 Y = insert 1 (J ∪ Finset.Ioc U Y) := by
    ext n
    simp only [J,mem_Icc,mem_insert,mem_union,mem_Ioc]
    omega
  have apart : Disjoint J (Finset.Ioc U Y) :=
    disjoint_left.mpr (fun _ hn hm => (mem_Ioc.mp hm).1.not_ge (mem_Ioc.mp hn).2)
  have once : 1 ∉ J ∪ Finset.Ioc U Y := by
    simp only [J,mem_union,mem_Ioc]; omega
  have f1 : f 1 = 1 := by
    simp [f,sieveSample,sievePolynomial,Nat.dvd_one,hV,hW,ha1,hb1,sample]
  have total : (∑ n ∈ Finset.Icc 1 Y, f n) = 1 + (∑ n ∈ J, f n) + ∑ n ∈ Finset.Ioc U Y, f n := by
    rw [cut,sum_insert once,sum_union apart,f1,add_assoc]
  have tri : (1:ℝ) ≤ ‖∑ n ∈ Finset.Icc 1 Y, f n‖ + ‖∑ n ∈ J, f n‖ + ‖∑ n ∈ Finset.Ioc U Y, f n‖ := by
    have rev : (1:ℂ) = (∑ n ∈ Finset.Icc 1 Y, f n) - (∑ n ∈ J, f n) - ∑ n ∈ Finset.Ioc U Y, f n := by rw [total]; abel
    calc
      (1:ℝ) = ‖(1:ℂ)‖ := norm_one.symm
      _ = _ := congrArg norm rev
      _ ≤ _ := (norm_sub_le ..).trans (add_le_add_left (norm_sub_le ..) _)
  change 1-_ - _ ≤ ‖∑ n ∈ Finset.Ioc U Y, f n‖
  change ‖∑ n ∈ Finset.Icc 1 Y, f n‖ ≤ _ at rough
  change ‖∑ n ∈ J, f n‖ ≤ _ at sh
  linarith only [tri,sh,rough]

end Conjectures.Goldbach.BinaryShiftZeroDensity
end
end

section
open Complex Finset DirichletCharacter
open scoped ComplexConjugate
noncomputable section
namespace Conjectures.Goldbach.BinaryShiftZeroDensity

private def sieveGram {r t : ℕ} (χ : DirichletCharacter ℂ r) (ψ : DirichletCharacter ℂ t)
    (u v : ℂ) (B : ℕ → ℝ) (n : ℕ) : ℂ :=
  ((n*(B n)^2:ℝ):ℂ)*sample χ u n*conj (sample ψ v n)

private theorem sieveGram_diagonal {q : ℕ} (χ : DirichletCharacter ℂ q)
    (s : ℂ) (σ : ℝ) (hσ : σ ≤ s.re) (h1 : σ ≤ 1) (U Y : ℕ) (B : ℕ → ℝ) :
    ‖∑ n ∈ Finset.Ioc U Y, sieveGram χ χ s s B n‖ ≤
      ((Y:ℝ)^(1-σ))^2 * ∑ n ∈ Finset.Ioc U Y, (B n)^2/(n:ℝ) := by
  apply (norm_sum_le ..).trans
  rw [Finset.mul_sum]
  apply sum_le_sum
  intro n hn
  obtain ⟨lo,hi⟩ := mem_Ioc.mp hn
  have hn1 := Nat.zero_lt_of_lt lo
  have hn0 : 0 < (n:ℝ) := Nat.cast_pos.mpr hn1
  have k : 0 ≤ (n:ℝ)*(B n)^2 := mul_nonneg hn0.le (sq_nonneg _)
  rw [sieveGram,norm_mul,norm_mul,norm_conj,Complex.norm_real,Real.norm_of_nonneg k,mul_assoc,←sq]
  apply (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (sample_norm_comparison χ s σ hσ h1 n Y hn1 hi) 2) k).trans_eq
  field_simp

private theorem sieveGram_as_sample {r t : ℕ} [NeZero t] (χ : DirichletCharacter ℂ r)
    (ψ : DirichletCharacter ℂ t) (u v : ℂ) (W : ℕ) (b : ℕ → ℝ) (n : ℕ) (hn : 0 < n) :
    sieveGram χ ψ u v (sievePolynomial (Finset.Icc 1 W) b) n =
      sieveSample (correlationCharacter χ ψ) (u+conj v-1) W W b b n := by
  have hnC : (n:ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have harg : (n:ℂ).arg ≠ Real.pi := by simp [Real.pi_ne_zero.symm]
  have hc : conj ((n:ℂ)^(-v)) = (n:ℂ)^(-conj v) := by
    simpa only [map_neg,map_natCast] using (cpow_conj (n:ℂ) (-v) harg).symm
  simp only [sieveGram,sieveSample,sample,ofReal_mul,ofReal_natCast,ofReal_pow,map_mul,hc,correlationCharacter_apply]
  rw [show -(u+conj v-1) = 1+(-u + -conj v) by ring,cpow_add _ _ hnC,cpow_one,cpow_add _ _ hnC]
  ring

private theorem sieveGram_cross {r t : ℕ} [NeZero r] [NeZero t] (χ : DirichletCharacter ℂ r)
    (ψ : DirichletCharacter ℂ t) (hχ : χ.IsPrimitive) (hψ : ψ.IsPrimitive)
    (hne : (⟨r,χ⟩ : Σ k : ℕ, DirichletCharacter ℂ k) ≠ ⟨t,ψ⟩)
    (u v : ℂ) (T : ℝ) (hu : 3/4 ≤ u.re) (hv : 3/4 ≤ v.re) (hu1 : u.re ≤ 1) (hv1 : v.re ≤ 1)
    (hut : ‖u‖ ≤ T) (hvt : ‖v‖ ≤ T) (U W Y : ℕ) (hU : 1 ≤ U) (hWU : W*W ≤ U) (hUY : U ≤ Y)
    (b : ℕ → ℝ) (hb : ∀ d, |b d| ≤ 1) :
    ‖∑ n ∈ Finset.Ioc U Y, sieveGram χ ψ u v (sievePolynomial (Finset.Icc 1 W) b) n‖ ≤
      (W:ℝ)^2 * (8*((r*t:ℕ):ℝ)*(1+2*(2*T+1))*(U:ℝ)^(-(1/2:ℝ))) := by
  let θ := correlationCharacter χ ψ
  let w := u+conj v-1
  have hw : 1/2 ≤ w.re := by simp only [w,sub_re,add_re,conj_re,one_re]; linarith only [hu,hv]
  have hw1 : w.re ≤ 1 := by simp only [w,sub_re,add_re,conj_re,one_re]; linarith only [hu1,hv1]
  have hw0 : 0 < w.re := lt_of_lt_of_le (by norm_num) hw
  have ht : ‖w‖ ≤ 2*T+1 := calc
    _ ≤ ‖u+conj v‖+‖(1:ℂ)‖ := norm_sub_le ..
    _ ≤ (‖u‖+‖v‖)+1 := by rw [norm_one];apply add_le_add_left;simpa using norm_add_le u (conj v)
    _ ≤ _ := by linarith only [hut,hvt]
  have ht0 := (norm_nonneg w).trans ht
  have hdiv : ‖w‖/w.re ≤ 2*(2*T+1) := (div_le_iff₀ hw0).mpr (by nlinarith only [ht,mul_le_mul_of_nonneg_left hw ht0])
  let F (N : ℕ) := ∑ n ∈ Finset.Icc 1 N, sieveSample θ w W W b b n
  let M := sievePrefixMain θ w W W b b
  let C := (W:ℝ)^2 * (4*((r*t:ℕ):ℝ)*(1+2*(2*T+1))*(U:ℝ)^(-(1/2:ℝ)))
  have per (N : ℕ) (hN : U ≤ N) : ‖F N-M‖ ≤ C := by
    have raw := weighted_prefix_error θ (correlationCharacter_nonprincipal χ ψ hχ hψ hne) w hw0 hw1 W W N
      (hWU.trans hN) b b hb hb
    apply raw.trans
    dsimp only [C]
    rw [sq]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply mul_le_mul (mul_le_mul_of_nonneg_left (add_le_add_right hdiv 1) (by positivity)) _
      (Real.rpow_nonneg (Nat.cast_nonneg _) _) (by positivity)
    have u1 : 1 ≤ (U:ℝ) := by exact_mod_cast hU
    exact (Real.rpow_le_rpow_of_nonpos (zero_lt_one.trans_le u1) (by exact_mod_cast hN) (neg_nonpos.mpr hw0.le)).trans
      (Real.rpow_le_rpow_of_exponent_le u1 (neg_le_neg hw))
  have cut : Finset.Icc 1 Y = Finset.Icc 1 U ∪ Finset.Ioc U Y := by
    ext n
    simp only [mem_Icc,mem_Ioc,mem_union]
    omega
  have eqn : (∑ n ∈ Finset.Ioc U Y, sieveGram χ ψ u v (sievePolynomial (Finset.Icc 1 W) b) n) = F Y-F U := by
    simp only [F,cut, sum_union (disjoint_left.mpr (fun _ hx hy => (mem_Ioc.mp hy).1.not_ge (mem_Icc.mp hx).2)),add_sub_cancel_left]
    exact sum_congr rfl (fun n hn => sieveGram_as_sample χ ψ u v W b n (Nat.zero_lt_of_lt (mem_Ioc.mp hn).1))
  rw [eqn]
  have tri := norm_sub_le_norm_sub_add_norm_sub (F Y) M (F U)
  rw [norm_sub_rev M] at tri
  exact (tri.trans (add_le_add (per Y hUY) (per U le_rfl))).trans_eq (by dsimp only [C];ring)

end Conjectures.Goldbach.BinaryShiftZeroDensity
end
end

section
open Complex Finset DirichletCharacter
open scoped ComplexConjugate
noncomputable section
namespace Conjectures.Goldbach.BinaryShiftZeroDensity

private theorem sieved_density_with_cross {ι : Type*} (Z : Finset ι) (q : ι → ℕ)
    [∀ i, NeZero (q i)] (χ : (i : ι) → DirichletCharacter ℂ (q i)) (s : ι → ℂ)
    (U V W Y : ℕ) (σ A B E : ℝ) (hσ1 : σ ≤ 1) (hA : 0 ≤ A) (hB : 0 ≤ B) (hE : 0 ≤ E)
    (a b : ℕ → ℝ) (hre : ∀ i ∈ Z, σ ≤ (s i).re)
    (sep : ∀ i ∈ Z, ∀ j ∈ Z, i ≠ j →
      ‖∑ n ∈ Finset.Ioc U Y, sieveGram (χ i) (χ j) (s i) (s j) (sievePolynomial (Finset.Icc 1 W) b) n‖ ≤ E)
    (large : ∀ i ∈ Z, 1/2 ≤ ‖∑ n ∈ Finset.Ioc U Y, sieveSample (χ i) (s i) V W a b n‖)
    (energyA : (∑ n ∈ Finset.Ioc U Y, (sievePolynomial (Finset.Icc 1 V) a n)^2/(n:ℝ)) ≤ A)
    (energyB : (∑ n ∈ Finset.Ioc U Y, (sievePolynomial (Finset.Icc 1 W) b n)^2/(n:ℝ)) ≤ B)
    (hcross : A*E ≤ 1/8) :
    (Z.card:ℝ) ≤ 8*A*((Y:ℝ)^(1-σ))^2*B := by
  classical
  let J := (Z.card:ℝ)
  let I := Finset.Ioc U Y
  let F := sievePolynomial (Finset.Icc 1 V) a
  let G := sievePolynomial (Finset.Icc 1 W) b
  let w (n : ℕ) := (n:ℝ)*(G n)^2
  let c (n : ℕ) := ((F n*G n:ℝ):ℂ)
  let D := ((Y:ℝ)^(1-σ))^2 * B
  let K (i j : ι) := ‖∑ n ∈ I, sieveGram (χ i) (χ j) (s i) (s j) G n‖
  have hJ : 0 ≤ J := Nat.cast_nonneg _
  have hD : 0 ≤ D := mul_nonneg (sq_nonneg _) hB
  have hw (n : ℕ) : 0 ≤ w n := mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  have support (n : ℕ) (hn : n ∈ I) (hz : w n=0) : c n = 0 := by
    have n0 : (n:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.zero_lt_of_lt (mem_Ioc.mp hn).1).ne'
    have zero : G n=0 := by
      have h : (G n)^2 = 0 := (mul_eq_zero.mp hz).resolve_left n0
      exact pow_eq_zero_iff (by decide : 2 ≠ 0) |>.mp h
    simp [c,zero]
  have energy : (∑ n ∈ I, ‖c n‖^2/w n) ≤ A := by
    apply le_trans _ energyA
    apply sum_le_sum
    intro n hn
    have n0 : 0 < (n:ℝ) := Nat.cast_pos.mpr (Nat.zero_lt_of_lt (mem_Ioc.mp hn).1)
    by_cases zero : G n = 0
    · simp [c,w,zero,div_nonneg (sq_nonneg _) n0.le]
    · apply le_of_eq
      change ‖((F n*G n:ℝ):ℂ)‖^2 / (_*(G n)^2) = _
      rw [Complex.norm_real,Real.norm_eq_abs,sq_abs]
      change _ = (F n)^2/(n:ℝ)
      field_simp
  have row (i : ι) (hi : i ∈ Z) : (∑ j ∈ Z, K i j) ≤ D+J*E := calc
    _ ≤ ∑ j ∈ Z, ((if j=i then D else 0) + E) := by
      apply sum_le_sum
      intro j hj
      by_cases e : j=i
      · subst j
        rw [ite_eq_left (show i=i from rfl)]
        apply le_trans _ (le_add_of_nonneg_right hE)
        apply (sieveGram_diagonal (χ i) (s i) σ (hre i hi) hσ1 U Y G).trans
        exact mul_le_mul_of_nonneg_left energyB (sq_nonneg _)
      · simpa only [ite_eq_right e,zero_add] using sep i hi j hj (Ne.symm e)
    _ = _ := by simp [sum_add_distrib,hi,J]
  have gram : (∑ i ∈ Z, ∑ j ∈ Z, K i j) ≤ J*(D+J*E) :=
    (sum_le_sum row).trans_eq (by simp [J,mul_add])
  have ha := halasz_correlation Z I c w (fun n _ => hw n) support (fun i => sample (χ i) (s i))
  change (∑ i ∈ Z, ‖∑ n ∈ I, sieveSample (χ i) (s i) V W a b n‖)^2 ≤
    (∑ n ∈ I, ‖c n‖^2/w n) * ∑ i ∈ Z, ∑ j ∈ Z, K i j at ha
  have low : J/2 ≤ ∑ i ∈ Z, ‖∑ n ∈ I, sieveSample (χ i) (s i) V W a b n‖ := by
    exact (show J/2 = ∑ _i ∈ Z, (1/2:ℝ) by simp [J];ring).trans_le (sum_le_sum large)
  have scale : (J/2)^2 ≤ A*(J*(D+J*E)) := (pow_le_pow_left₀ (by positivity) low 2).trans
    (ha.trans (mul_le_mul energy gram (sum_nonneg fun _ _ => sum_nonneg fun _ _ => norm_nonneg _) hA))
  have absrb := mul_le_mul_of_nonneg_left hcross (sq_nonneg J)
  change J^2*(A*E) ≤ _ at absrb
  have hprod : J*J ≤ (8*A*D)*J := by nlinarith only [scale,absrb]
  change J ≤ _
  rcases eq_or_lt_of_le hJ with hj|hj
  · rw [←hj]
    positivity
  · exact (le_of_mul_le_mul_right hprod hj).trans_eq (by dsimp only [D];ring)

end Conjectures.Goldbach.BinaryShiftZeroDensity
end
end

section
open Complex Finset Filter DirichletCharacter
open scoped Topology
noncomputable section
namespace Conjectures.Goldbach.BinaryShiftZeroDensity

private def tiltLoss (v : ℕ) : ℝ := Real.exp (-(v:ℝ))/(1-Real.exp (-(v:ℝ)))

private theorem tiltLoss_pos {v : ℕ} (hv : 0 < v) : 0 < tiltLoss v :=
  div_pos (Real.exp_pos _) (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by exact_mod_cast neg_lt_zero.mpr (Nat.cast_pos.mpr hv : (0:ℝ) < v))))

private theorem select_sieve_length (H : ℝ) : ∃ v : ℕ, 1 ≤ v ∧
    Real.exp (12*H)*(√(Real.exp 12*tiltLoss v)*√(Real.exp 12*tiltLoss 1)) ≤ 1/4 := by
  have expT : Tendsto (fun v : ℕ => Real.exp (-(v:ℝ))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp (tendsto_natCast_atTop_atTop (R := ℝ)))
  have loss : Tendsto tiltLoss atTop (𝓝 0) := by
    change Tendsto (fun v : ℕ => Real.exp (-(v:ℝ))/(1-Real.exp (-(v:ℝ)))) atTop (𝓝 0)
    have den : Tendsto (fun v : ℕ => 1-Real.exp (-(v:ℝ))) atTop (𝓝 (1-(0:ℝ))) := tendsto_const_nhds.sub expT
    convert expT.div den (by norm_num) using 1
    simp
  have lim : Tendsto (fun v : ℕ => Real.exp (12*H)*
      (√(Real.exp 12*tiltLoss v)*√(Real.exp 12*tiltLoss 1))) atTop (𝓝 0) := by
    have l1 := (loss.const_mul (Real.exp 12)).sqrt
    simpa only [mul_zero,Real.sqrt_zero,zero_mul] using (l1.mul_const (√(Real.exp 12*tiltLoss 1))).const_mul (Real.exp (12*H))
  exact ((eventually_ge_atTop (1:ℕ)).and (lim.eventually_le_const (by norm_num : (0:ℝ) < 1/4))).exists

private theorem tilt_identity {Q : ℕ} (hQ : 1 < Q) (k : ℕ) (t : ℝ) :
    ((Q^k:ℕ):ℝ)^(t/Real.log Q) = Real.exp ((k:ℝ)*t) := by
  have hx : 1 < (Q:ℝ) := by exact_mod_cast hQ
  have logpos := Real.log_pos hx
  rw [Nat.cast_pow,Real.rpow_def_of_pos (pow_pos (zero_lt_one.trans hx) _),Real.log_pow]
  congr 1
  field_simp

end Conjectures.Goldbach.BinaryShiftZeroDensity
end
end

section
open Complex Finset MeasureTheory DirichletCharacter GoldbachGrhGrowth
noncomputable section
namespace Conjectures.Goldbach.BinaryShiftZeroDensity

private def sieveArithmetic {q : ℕ} (χ : DirichletCharacter ℂ q) (W : ℕ) (b : ℕ → ℝ) (n : ℕ) : ℂ :=
  if n=0 then 0 else sieveSample χ 0 W W b b n

private def sieveMean {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (W : ℕ) (b : ℕ → ℝ) : ℂ :=
  ∑ d ∈ Finset.Icc 1 W, ∑ e ∈ Finset.Icc 1 W,
    ((b d*b e:ℝ):ℂ)*χ (Nat.lcm d e:ZMod q)*charMean χ/(Nat.lcm d e:ℂ)

private theorem character_real_discrepancy {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (x : ℝ)
    (hx : 0 ≤ x) :
    ‖charPartialSum χ ⌊x⌋₊ - (x:ℂ)*charMean χ‖ ≤ 3*(q:ℝ) := by
  have frac : ‖(⌊x⌋₊:ℂ)-(x:ℂ)‖ ≤ 1 := by
    rw [←ofReal_natCast,←ofReal_sub,Complex.norm_real,Real.norm_eq_abs,abs_of_nonpos (sub_nonpos.mpr (Nat.floor_le hx))]
    linarith only [Nat.lt_floor_add_one x]
  have q1 : 1 ≤ (q:ℝ) := by exact_mod_cast NeZero.pos q
  calc
    _ = ‖integerRemainder χ ⌊x⌋₊ + ((⌊x⌋₊:ℂ)-x)*charMean χ‖ := by congr 1;dsimp only [integerRemainder];ring
    _ ≤ _ := norm_add_le ..
    _ ≤ 2*(q:ℝ)+1 := by
      rw [norm_mul]
      exact add_le_add (norm_integerRemainder_le χ _) ((mul_le_mul frac (norm_charMean_le_one χ) (norm_nonneg _) zero_le_one).trans_eq (one_mul _))
    _ ≤ _ := by linarith only [q1]

private theorem dirichletPrefix_zero {q : ℕ} (χ : DirichletCharacter ℂ q) (k : ℕ) :
    dirichletPrefix χ 0 k = charPartialSum χ k := by
  unfold dirichletPrefix charPartialSum
  rw [←Finset.Ico_add_one_right_eq_Icc,Finset.sum_Ico_eq_sum_range]
  simp [Nat.add_comm 1]

/-- A finite divisor square against a character has bounded discrepancy
from its explicit linear mean. Expanding on lcm multiples keeps the
error proportional to the number of divisor pairs. -/
theorem sieveArithmetic_discrepancy {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (W : ℕ) (b : ℕ → ℝ) (hb : ∀ d, |b d| ≤ 1) (x : ℝ) (hx : 0 ≤ x) :
    ‖(∑ n ∈ Finset.Icc 0 ⌊x⌋₊, sieveArithmetic χ W b n) - (x:ℂ)*sieveMean χ W b‖ ≤
      (W:ℝ)^2*(3*q) := by
  let D := Finset.Icc 1 W
  let a (d e : ℕ) : ℂ := ((b d*b e:ℝ):ℂ)*χ (Nat.lcm d e:ZMod q)
  have sum0 : (∑ n ∈ Finset.Icc 0 ⌊x⌋₊, sieveArithmetic χ W b n) =
      ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, sieveSample χ 0 W W b b n := by
    have S : Finset.Icc 0 ⌊x⌋₊ = insert 0 (Finset.Icc 1 ⌊x⌋₊) := by ext n;simp;omega
    rw [S,sum_insert (by simp),sieveArithmetic,ite_eq_left rfl,zero_add]
    exact sum_congr rfl (fun n hn => ite_eq_right (show n ≠ 0 from (show 0 < n from (mem_Icc.mp hn).1).ne'))
  rw [sum0,sievePrefix_exact]
  simp only [sample,neg_zero,cpow_zero,one_mul,dirichletPrefix_zero]
  change ‖(∑ d ∈ D, ∑ e ∈ D, a d e*charPartialSum χ (⌊x⌋₊/Nat.lcm d e)) -
    (x:ℂ)*∑ d ∈ D, ∑ e ∈ D, a d e*charMean χ/(Nat.lcm d e:ℂ)‖ ≤ _
  simp only [Finset.mul_sum,←Finset.sum_sub_distrib]
  apply (norm_sum_le ..).trans
  calc
    _ ≤ ∑ _d ∈ D, ∑ _e ∈ D, (3*(q:ℝ)) := by
      apply sum_le_sum
      intro d hd
      apply (norm_sum_le ..).trans
      apply sum_le_sum
      intro e he
      let l := Nat.lcm d e
      have hl : 0 < l := Nat.lcm_pos (mem_Icc.mp hd).1 (mem_Icc.mp he).1
      have normA : ‖a d e‖ ≤ 1 := by
        dsimp only [a]
        rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_mul]
        exact (mul_le_mul (mul_le_mul (hb d) (hb e) (abs_nonneg _) zero_le_one) (χ.norm_le_one _) (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)
      change ‖a d e*charPartialSum χ (⌊x⌋₊/l) - (x:ℂ)*(a d e*charMean χ/(l:ℂ))‖ ≤ _
      rw [←Nat.floor_div_natCast,show a d e*charPartialSum χ ⌊x/(l:ℝ)⌋₊-(x:ℂ)*(a d e*charMean χ/(l:ℂ)) =
        a d e*(charPartialSum χ ⌊x/(l:ℝ)⌋₊-((x/(l:ℝ):ℝ):ℂ)*charMean χ) by push_cast;ring,norm_mul]
      exact (mul_le_mul normA (character_real_discrepancy χ _ (div_nonneg hx (Nat.cast_nonneg _))) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
    _ = _ := by simp [D];ring

end Conjectures.Goldbach.BinaryShiftZeroDensity
end
end

section
open Complex Finset MeasureTheory Set
noncomputable section
namespace Conjectures.Goldbach.BinaryShiftZeroDensity

/-- A bounded error in the cumulative arithmetic weight gives a uniform
power-saving error for its Mellin integral on every positive interval. -/
theorem discrepancy_mellin_interval (c : ℕ → ℂ) (M : ℂ) (B : ℝ) (hB : 0 ≤ B)
    (s : ℂ) (hs : 0 < s.re) (U Y : ℕ) (hU : 0 < U) (hUY : U ≤ Y)
    (disc : ∀ x : ℝ, (U:ℝ) ≤ x → x ≤ Y →
      ‖(∑ n ∈ Finset.Icc 0 ⌊x⌋₊, c n) - (x:ℂ)*M‖ ≤ B) :
    ‖(∑ n ∈ Finset.Ioc U Y, (n:ℂ)^(-s)*c n) -
      (∫ x in (U:ℝ)..Y, (x:ℂ)^(-s))*M‖ ≤ B*(2+‖s‖/s.re)*(U:ℝ)^(-s.re) := by
  let a := (U:ℝ)
  let b := (Y:ℝ)
  have ha : 0 < a := Nat.cast_pos.mpr hU
  have hab : a ≤ b := Nat.cast_le.mpr hUY
  let f (x : ℝ) := (x:ℂ)^(-s)
  let g (x : ℝ) := (-s)*(x:ℂ)^(-s-1)
  let S (x : ℝ) := ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, c n
  let R (x : ℝ) := S x - (x:ℂ)*M
  let J := Set.Ioc a b
  have gf (x : ℝ) (hx : 0 < x) : HasDerivAt f (g x) x :=
    hasDerivAt_ofReal_cpow_const hx.ne' (neg_ne_zero.mpr (fun e => by simp [e] at hs))
  have cf : ContinuousOn f (Set.Icc a b) := fun x hx => (gf x (ha.trans_le hx.1)).continuousAt.continuousWithinAt
  have cg : ContinuousOn g (Set.Icc a b) := continuousOn_const.mul
    (fun x hx => (continuousAt_ofReal_cpow_const x _ (Or.inr (ha.trans_le hx.1).ne')).continuousWithinAt)
  have ider : IntegrableOn (deriv f) (Set.Icc a b) :=
    cg.integrableOn_Icc.congr_fun (fun x hx => (gf x (ha.trans_le hx.1)).deriv.symm) measurableSet_Icc
  have hAbel := sum_mul_eq_sub_sub_integral_mul' (f := f) c hUY (fun x hx => (gf x (ha.trans_le hx.1)).differentiableAt) ider
  have ends (N : ℕ) : S (N:ℝ) = ∑ n ∈ Finset.Icc 0 N, c n := by simp [S]
  have Aeq : (∑ n ∈ Finset.Ioc U Y, (n:ℂ)^(-s)*c n) =
      f b*S b-f a*S a-∫ x in J, g x*S x := by
    rw [show (∑ n ∈ Finset.Ioc U Y, (n:ℂ)^(-s)*c n) = ∑ n ∈ Finset.Ioc U Y, f n*c n by simp [f],hAbel]
    rw [show S b = _ from ends Y,show S a = _ from ends U]
    congr 1
    exact setIntegral_congr_fun measurableSet_Ioc (fun x hx => by rw [(gf x (ha.trans hx.1)).deriv])
  have ip : (∫ x in a..b, f x) = f b*(b:ℂ)-f a*(a:ℂ)-(∫ x in a..b, g x*(x:ℂ)) := by
    have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt (u := f) (v := fun x : ℝ => (x:ℂ))
      (u' := g) (v' := fun _ => (1:ℂ)) ((uIcc_of_le hab) ▸ cf) continuous_ofReal.continuousOn
      (fun x hx => gf x (ha.trans (by simpa [min_eq_left hab] using hx.1)))
      (fun x _ => Complex.ofRealCLM.hasDerivAt) (cg.intervalIntegrable_of_Icc hab) intervalIntegrable_const
    simpa only [mul_one] using h
  have bound (x : ℝ) (hx : x ∈ Set.Icc a b) : ‖R x‖ ≤ B := disc x hx.1 hx.2
  have k0 : 0 ≤ ‖s‖*B := mul_nonneg (norm_nonneg _) hB
  let major (x : ℝ) := (‖s‖*B)*x^(-s.re-1)
  have p : -s.re-1 < -1 := by linarith
  have imaj : IntegrableOn major (Set.Ioi a) := (integrableOn_Ioi_rpow_of_lt p ha).const_mul (‖s‖*B)
  have sub : J ⊆ Set.Ioi a := fun _ hx => hx.1
  have inorm (x : ℝ) (hx : x ∈ J) : ‖g x*R x‖ ≤ major x := by
    have x0 := ha.trans hx.1
    simp only [g,norm_mul,norm_neg,norm_cpow_eq_rpow_re_of_pos x0,sub_re,neg_re,one_re]
    exact (mul_le_mul_of_nonneg_left (bound x ⟨hx.1.le,hx.2⟩) (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg x0.le _))).trans_eq (by dsimp only [major];ring)
  have iR : IntegrableOn (fun x => g x*R x) J := by
    apply (imaj.mono_set sub).mono'
    · have ms : Measurable S := (measurable_of_countable (fun N : ℕ => ∑ n ∈ Finset.Icc 0 N, c n)).comp measurable_id.nat_floor
      exact ((cg.mono Set.Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc).mul
        ((ms.sub (continuous_ofReal.measurable.mul_const M)).aestronglyMeasurable)
    · filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioc] with x hx using inorm x hx
  have iLin : IntegrableOn (fun x : ℝ => (g x*(x:ℂ))*M) J :=
    ((cg.mul continuous_ofReal.continuousOn).mul continuousOn_const).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have split : (∫ x in J, g x*S x) = (∫ x in J, g x*R x)+(∫ x in J, g x*(x:ℂ))*M := by
    rw [←integral_mul_const,←integral_add iR iLin]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro x _
    dsimp only [R]
    ring
  have triangle : ‖∫ x in J, g x*R x‖ ≤ (‖s‖*B)*(a^(-s.re)/s.re) := calc
    _ ≤ ∫ x in J, major x := norm_integral_le_of_norm_le (imaj.mono_set sub) (by
      filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioc] with x hx using inorm x hx)
    _ ≤ ∫ x in Set.Ioi a, major x := setIntegral_mono_set imaj (by
      filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with x hx using mul_nonneg k0 (Real.rpow_nonneg (ha.trans hx).le _)) (Filter.Eventually.of_forall sub)
    _ = _ := by
      rw [show (∫ x in Set.Ioi a, major x) = _ from integral_const_mul ..,integral_Ioi_rpow_of_lt p ha,show -s.re-1+1 = -s.re by ring]
      ring
  have boundary (x : ℝ) (hx : x ∈ Set.Icc a b) : ‖f x*R x‖ ≤ a^(-s.re)*B := by
    rw [norm_mul,show ‖f x‖ = x^(-s.re) by dsimp only [f];rw [norm_cpow_eq_rpow_re_of_pos (ha.trans_le hx.1),neg_re]]
    exact mul_le_mul (Real.rpow_le_rpow_of_nonpos ha hx.1 (neg_nonpos.mpr hs.le)) (bound x hx) (norm_nonneg _) (Real.rpow_nonneg ha.le _)
  have form : (∑ n ∈ Finset.Ioc U Y, (n:ℂ)^(-s)*c n) -(∫ x in a..b, f x)*M =
      f b*R b-f a*R a-∫ x in J, g x*R x := by
    rw [Aeq,ip,intervalIntegral.integral_of_le hab,split]
    dsimp only [R]
    ring
  rw [form]
  exact ((norm_sub_le ..).trans (add_le_add ((norm_sub_le ..).trans
    (add_le_add (boundary b ⟨hab,le_rfl⟩) (boundary a ⟨le_rfl,hab⟩))) triangle)).trans_eq (by dsimp only [a];ring)

end Conjectures.Goldbach.BinaryShiftZeroDensity
end
end

section
open Complex Finset MeasureTheory Set DirichletCharacter
noncomputable section
namespace Conjectures.Goldbach.BinaryShiftZeroDensity

private theorem sieve_mellin_mean {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (W : ℕ) (b : ℕ → ℝ) (hb : ∀ d, |b d| ≤ 1) (s : ℂ) (hs : 0 < s.re)
    (U Y : ℕ) (hU : 0 < U) (hUY : U ≤ Y) :
    ‖(∑ n ∈ Finset.Ioc U Y, sieveSample χ s W W b b n) -
      (∫ x in (U:ℝ)..Y, (x:ℂ)^(-s))*sieveMean χ W b‖ ≤
      (W:ℝ)^2*(3*q)*(2+‖s‖/s.re)*(U:ℝ)^(-s.re) := by
  have eqn (n : ℕ) (hn : n ∈ Finset.Ioc U Y) :
      sieveSample χ s W W b b n = (n:ℂ)^(-s)*sieveArithmetic χ W b n := by
    simp only [sieveArithmetic,ite_eq_right (Nat.zero_lt_of_lt (mem_Ioc.mp hn).1).ne',sieveSample,sample,neg_zero,cpow_zero,one_mul]
    ring
  rw [sum_congr rfl eqn]
  apply discrepancy_mellin_interval _ _ _ (by positivity) _ hs _ _ hU hUY
  intro x hx _
  exact sieveArithmetic_discrepancy χ W b hb x ((Nat.cast_nonneg _).trans hx)

private theorem harmonic_complex_integral (U Y : ℕ) (hU : 0 < U) (hUY : U ≤ Y) :
    (∫ x in (U:ℝ)..Y, (x:ℂ)^(-(1:ℂ))) = (Real.log ((Y:ℝ)/U):ℂ) := by
  have u0 : 0 < (U:ℝ) := Nat.cast_pos.mpr hU
  have h : (0:ℝ) ∉ Set.uIcc (U:ℝ) Y := by
    rw [Set.uIcc_of_le (Nat.cast_le.mpr hUY)]
    exact fun hz => u0.not_ge hz.1
  calc
    _ = ∫ x in (U:ℝ)..Y, ((x⁻¹:ℝ):ℂ) := by
      apply intervalIntegral.integral_congr
      intro x _
      simp [Complex.cpow_neg_one]
    _ = ((∫ x in (U:ℝ)..Y, x⁻¹:ℝ):ℂ) := by rw [intervalIntegral.integral_ofReal]
    _ = _ := congrArg Complex.ofReal (integral_inv h)

private theorem sieve_mean_log_bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (W : ℕ) (b : ℕ → ℝ) (hb : ∀ d, |b d| ≤ 1) (U Y : ℕ) (hU : 0 < U) (hUY : U ≤ Y) :
    Real.log ((Y:ℝ)/U)*‖sieveMean χ W b‖ ≤
      (∑ n ∈ Finset.Ioc U Y, (sievePolynomial (Finset.Icc 1 W) b n)^2/(n:ℝ)) +
        (W:ℝ)^2*(9*q)*(U:ℝ)⁻¹ := by
  let L := ∑ n ∈ Finset.Ioc U Y, sieveSample χ 1 W W b b n
  let B := sievePolynomial (Finset.Icc 1 W) b
  let M := sieveMean χ W b
  have hlog : 0 ≤ Real.log ((Y:ℝ)/U) := Real.log_nonneg ((one_le_div (Nat.cast_pos.mpr hU)).mpr (Nat.cast_le.mpr hUY))
  have harm : ‖L‖ ≤ ∑ n ∈ Finset.Ioc U Y, (B n)^2/(n:ℝ) := by
    apply (norm_sum_le ..).trans (sum_le_sum ?_)
    intro n hn
    have hn1 := Nat.zero_lt_of_lt (mem_Ioc.mp hn).1
    have ht := sample_norm_comparison χ 1 1 (by simp) le_rfl n Y hn1 (mem_Ioc.mp hn).2
    simp only [sub_self,Real.rpow_zero] at ht
    change ‖((B n*B n:ℝ):ℂ)*sample χ 1 n‖ ≤ _
    rw [←sq,norm_mul,Complex.norm_real,Real.norm_of_nonneg (sq_nonneg _)]
    exact (mul_le_mul_of_nonneg_left ht (sq_nonneg _)).trans_eq (by ring)
  have error := sieve_mellin_mean χ W b hb 1 (by simp) U Y hU hUY
  rw [harmonic_complex_integral U Y hU hUY] at error
  simp only [one_re,norm_one,div_one,Real.rpow_neg_one] at error
  change ‖L-(Real.log ((Y:ℝ)/U):ℂ)*M‖ ≤ _ at error
  have tri := norm_sub_le L (L-(Real.log ((Y:ℝ)/U):ℂ)*M)
  rw [sub_sub_cancel,norm_mul,Complex.norm_real,Real.norm_of_nonneg hlog] at tri
  change _*‖M‖ ≤ _
  exact (tri.trans (add_le_add harm error)).trans_eq (by ring)

private theorem mellin_integral_separation (s : ℂ) (hsi : 0 < |s.im|) (hs : s.re ≤ 1)
    (U Y : ℕ) (hU : 0 < U) (hUY : U ≤ Y) :
    ‖∫ x in (U:ℝ)..Y, (x:ℂ)^(-s)‖ ≤ 2*(Y:ℝ)^(1-s.re)/|s.im| := by
  have u0 : 0 < (U:ℝ) := Nat.cast_pos.mpr hU
  have y0 : 0 < (Y:ℝ) := Nat.cast_pos.mpr (hU.trans_le hUY)
  have lhs : -s ≠ -1 := by
    intro h
    have k := congrArg Complex.im (neg_inj.mp h)
    simp only [one_im] at k
    simp [k] at hsi
  have h : (0:ℝ) ∉ Set.uIcc (U:ℝ) Y := by
    rw [Set.uIcc_of_le (Nat.cast_le.mpr hUY)]
    exact fun hz => u0.not_ge hz.1
  have den : |s.im| ≤ ‖-s+1‖ := by simpa only [add_im,neg_im,one_im,add_zero,abs_neg] using abs_im_le_norm (-s+1)
  rw [integral_cpow (Or.inr ⟨lhs,h⟩),norm_div]
  apply div_le_div₀ (by positivity) _ hsi den
  apply (norm_sub_le ..).trans
  rw [norm_cpow_eq_rpow_re_of_pos y0,norm_cpow_eq_rpow_re_of_pos u0,add_re,neg_re,one_re,show -s.re+1=1-s.re by ring]
  linarith only [Real.rpow_le_rpow u0.le (Nat.cast_le.mpr hUY) (sub_nonneg.mpr hs)]

/-- For separated frequencies the conductor-weighted main term is damped
by the product of their spacing and the logarithmic length of the interval. -/
theorem sieve_mellin_separated {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (W : ℕ) (b : ℕ → ℝ) (hb : ∀ d, |b d| ≤ 1) (s : ℂ)
    (hs : 0 < s.re) (hs1 : s.re ≤ 1) (hsi : 0 < |s.im|)
    (U Y : ℕ) (hU : 0 < U) (hUY : U < Y) :
    ‖∑ n ∈ Finset.Ioc U Y, sieveSample χ s W W b b n‖ ≤
      (W:ℝ)^2*(3*q)*(2+‖s‖/s.re)*(U:ℝ)^(-s.re) +
        (2*(Y:ℝ)^(1-s.re) / (|s.im| * Real.log ((Y:ℝ)/U))) *
          ((∑ n ∈ Finset.Ioc U Y, (sievePolynomial (Finset.Icc 1 W) b n)^2/(n:ℝ))+
            (W:ℝ)^2*(9*q)*(U:ℝ)⁻¹) := by
  let L := ∑ n ∈ Finset.Ioc U Y, sieveSample χ s W W b b n
  let I := ∫ x in (U:ℝ)..Y, (x:ℂ)^(-s)
  let M := sieveMean χ W b
  let E := (∑ n ∈ Finset.Ioc U Y, (sievePolynomial (Finset.Icc 1 W) b n)^2/(n:ℝ))+(W:ℝ)^2*(9*q)*(U:ℝ)⁻¹
  have hp := Real.log_pos ((one_lt_div (Nat.cast_pos.mpr hU)).mpr (Nat.cast_lt.mpr hUY))
  have boundM : ‖M‖ ≤ E/Real.log ((Y:ℝ)/U) := (le_div_iff₀ hp).mpr (by rw [mul_comm];exact sieve_mean_log_bound χ W b hb U Y hU hUY.le)
  have prod : ‖I*M‖ ≤ (2*(Y:ℝ)^(1-s.re)/(|s.im| * Real.log ((Y:ℝ)/U)))*E := by
    rw [norm_mul]
    apply (mul_le_mul (mellin_integral_separation s hsi hs1 U Y hU hUY.le) boundM (norm_nonneg _) (by positivity)).trans_eq
    ring
  have tri := norm_add_le (L-I*M) (I*M)
  rw [sub_add_cancel] at tri
  exact tri.trans (add_le_add (sieve_mellin_mean χ W b hb s hs U Y hU hUY.le) prod)

end Conjectures.Goldbach.BinaryShiftZeroDensity
end
end

section
open Complex Finset DirichletCharacter
open scoped ComplexConjugate
noncomputable section
namespace Conjectures.Goldbach.BinaryShiftZeroDensity

private theorem separated_gram_at_scale {Q y r t : ℕ} [NeZero r] [NeZero t]
    (χ : DirichletCharacter ℂ r) (ψ : DirichletCharacter ℂ t) (b : ℕ → ℝ) (hb : ∀ d, |b d| ≤ 1)
    (u v : ℂ) (H T A B D : ℝ) (hQ : 9 ≤ Q) (hy : 13 ≤ y) (hr : r ≤ Q) (ht : t ≤ Q)
    (hT : 0 ≤ T) (hA : 0 < A) (hD : 0 < D)
    (hs : 3/4 ≤ 1-H/Real.log Q) (u0 : 1-H/Real.log Q ≤ u.re) (v0 : 1-H/Real.log Q ≤ v.re)
    (u1 : u.re ≤ 1) (v1 : v.re ≤ 1) (uT : ‖u‖ ≤ T) (vT : ‖v‖ ≤ T)
    (hsep : D/Real.log Q ≤ |u.im-v.im|)
    (hsize : 16*A*(3*(2+2*(2*T+1))) ≤ Q)
    (hspace : 32*A*Real.exp ((y:ℝ)*(2*H))*(B+1) ≤ D)
    (henergy : (∑ n ∈ Finset.Ioc (Q^12) (Q^y), (sievePolynomial (Finset.Icc 1 Q) b n)^2/(n:ℝ)) ≤ B) :
    ‖∑ n ∈ Finset.Ioc (Q^12) (Q^y), sieveGram χ ψ u v (sievePolynomial (Finset.Icc 1 Q) b) n‖ ≤ 1/(8*A) := by
  let x := (Q:ℝ)
  let l := Real.log x
  let U := Q^12
  let Y := Q^y
  let w := u+conj v-1
  let K := 2+2*(2*T+1)
  have q1 : 1 < Q := by omega
  have x1 : 1 < x := by dsimp only [x]; exact_mod_cast q1
  have x0 := zero_lt_one.trans x1
  have hl : 0 < l := Real.log_pos x1
  have hU : 0 < U := pow_pos (by omega) _
  have hUY : U < Y := Nat.pow_lt_pow_right q1 (by omega)
  have ureal : (U:ℝ) = x^12 := Nat.cast_pow Q 12
  have yreal : (Y:ℝ) = x^y := Nat.cast_pow Q y
  have Q2 : ((r*t:ℕ):ℝ) ≤ x^2 := by dsimp only [x];exact_mod_cast (Nat.mul_le_mul hr ht).trans_eq (sq Q).symm
  have X2 : x ≤ x^2 := by simpa only [pow_one] using pow_le_pow_right₀ x1.le (by decide : 1 ≤ 2)
  have X8 : x ≤ x^8 := by simpa only [pow_one] using pow_le_pow_right₀ x1.le (by decide : 1 ≤ 8)
  have hK : 0 < K := by dsimp only [K];positivity
  have loglen : l ≤ Real.log ((Y:ℝ)/U) := by
    rw [ureal,yreal,Real.log_div (pow_pos x0 _).ne' (pow_pos x0 _).ne', Real.log_pow, Real.log_pow]
    have yy : (13:ℝ) ≤ y := Nat.cast_le.mpr hy
    change l ≤ y*l-12*l
    nlinarith only [mul_le_mul_of_nonneg_right yy hl.le]
  have hactual : 0 < |w.im| := by
    change 0 < |(u+conj v-1).im|
    simpa only [sub_im,one_im,sub_zero,add_im,conj_im,←sub_eq_add_neg] using (div_pos hD hl).trans_le hsep
  have wr : 1/2 ≤ w.re := by
    simp only [w,sub_re,add_re,conj_re,one_re]
    linarith only [hs,u0,v0]
  have wr0 : 0 < w.re := lt_of_lt_of_le (by norm_num) wr
  have wr1 : w.re ≤ 1 := by simp only [w,sub_re,add_re,conj_re,one_re];linarith only [u1,v1]
  have wt : ‖w‖ ≤ 2*T+1 := calc
    _ ≤ ‖u+conj v‖+‖(1:ℂ)‖ := norm_sub_le ..
    _ ≤ (‖u‖+‖v‖)+1 := by rw [norm_one];apply add_le_add_left;simpa using norm_add_le u (conj v)
    _ ≤ _ := by linarith only [uT,vT]
  have wratio : 2+‖w‖/w.re ≤ K := add_le_add_right ((div_le_iff₀ wr0).mpr (by
    nlinarith only [wt,mul_le_mul_of_nonneg_left wr ((norm_nonneg _).trans wt)])) 2
  have yexp : (Y:ℝ)^(1-w.re) ≤ Real.exp ((y:ℝ)*(2*H)) := by
    apply le_trans _ (tilt_identity q1 y (2*H)).le
    apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ Y from (hU.trans hUY)) : (1:ℝ) ≤ Y)
    change 1-(u+conj v-1).re ≤ 2*H/l
    simp only [sub_re,add_re,conj_re,one_re]
    linarith only [u0,v0,show 2*H/l=2*(H/l) by ring]
  have denom : D ≤ |w.im| * Real.log ((Y:ℝ)/U) := by
    have a : D/l ≤ |w.im| := by simpa only [w,sub_im,one_im,sub_zero,add_im,conj_im,←sub_eq_add_neg] using hsep
    exact ((div_le_iff₀ hl).mp a).trans (mul_le_mul_of_nonneg_left loglen hactual.le)
  have u1r : 1 ≤ (U:ℝ) := by exact_mod_cast hU
  have pu : (U:ℝ)^(-w.re) ≤ (x^6)⁻¹ := calc
    _ ≤ (U:ℝ)^(-(1/2:ℝ)) := Real.rpow_le_rpow_of_exponent_le u1r (neg_le_neg wr)
    _ = _ := by rw [ureal,←Real.rpow_natCast_mul x0.le,show ((12:ℕ):ℝ)*(-(1/2)) = -(6:ℝ) by norm_num,Real.rpow_neg x0.le];norm_cast
  have first : x^2*(3*((r*t:ℕ):ℝ))*(2+‖w‖/w.re)*(U:ℝ)^(-w.re) ≤ 1/(16*A) := calc
    _ ≤ x^2*(3*x^2)*K*(x^6)⁻¹ := by gcongr
    _ = (3*K)/x^2 := by field_simp
    _ ≤ _ := (div_le_div_iff₀ (pow_pos x0 2) (by positivity)).mpr (by
      have h : 16*A*(3*K) ≤ x^2 := hsize.trans X2
      linarith only [h])
  have rem : x^2*(9*((r*t:ℕ):ℝ))*(U:ℝ)⁻¹ ≤ 1 := calc
    _ ≤ x^2*(9*x^2)*(x^12)⁻¹ := by rw [ureal];gcongr
    _ = 9/x^8 := by field_simp
    _ ≤ _ := (div_le_one (pow_pos x0 8)).mpr ((show (9:ℝ) ≤ x by dsimp only [x];exact_mod_cast hQ).trans X8)
  have frac : 2*(Y:ℝ)^(1-w.re)/(|w.im| * Real.log ((Y:ℝ)/U)) ≤ 2*Real.exp ((y:ℝ)*(2*H))/D :=
    div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left yexp (by norm_num)) hD denom
  have mainBound : (2*Real.exp ((y:ℝ)*(2*H))/D)*(B+1) ≤ 1/(16*A) := by
    rw [div_mul_eq_mul_div]
    exact (div_le_div_iff₀ hD (by positivity)).mpr (by linarith only [hspace])
  let θ := correlationCharacter χ ψ
  have est := sieve_mellin_separated θ Q b hb w wr0 wr1 hactual U Y hU hUY
  have rewriteSum : (∑ n ∈ Finset.Ioc U Y, sieveGram χ ψ u v (sievePolynomial (Finset.Icc 1 Q) b) n) =
      ∑ n ∈ Finset.Ioc U Y, sieveSample θ w Q Q b b n :=
    sum_congr rfl (fun n hn => sieveGram_as_sample χ ψ u v Q b n (Nat.zero_lt_of_lt (mem_Ioc.mp hn).1))
  rw [rewriteSum]
  apply est.trans
  have final := mul_le_mul frac (add_le_add henergy rem) (add_nonneg (sum_nonneg (fun _ _ => by positivity)) (by positivity)) (by positivity)
  exact (add_le_add first (final.trans mainBound)).trans_eq (by ring)

end Conjectures.Goldbach.BinaryShiftZeroDensity
end
end

section
open Complex Finset Filter DirichletCharacter
open scoped Topology
noncomputable section
namespace Conjectures.Goldbach.BinaryShiftZeroDensity

/-- Bounded-height near-one zeros with repeated character labels can be counted
simultaneously when the ordinates from each character are separated on
the reciprocal-conductor-logarithm scale. -/
theorem primitive_nearOne_separated {ι : Type*} (H T : ℝ) (hH : 0 ≤ H) (hT : 0 ≤ T) :
    ∃ D C : ℝ, 0 < D ∧ 0 < C ∧ ∀ᶠ Q : ℕ in atTop, ∀ (Z : Finset ι) (q : ι → ℕ) [∀ i, NeZero (q i)]
      (χ : (i : ι) → DirichletCharacter ℂ (q i)) (s : ι → ℂ),
      (∀ i ∈ Z, ∀ j ∈ Z, i ≠ j →
        (⟨q i,χ i⟩ : Σ k : ℕ, DirichletCharacter ℂ k) ≠ ⟨q j,χ j⟩ ∨ D/Real.log Q ≤ |(s i).im-(s j).im|) →
      (∀ i ∈ Z, q i ≤ Q ∧ (χ i).IsPrimitive ∧ χ i ≠ 1 ∧ (χ i).LFunction (s i) = 0 ∧
        1-H/Real.log Q ≤ (s i).re ∧ ‖s i‖ ≤ T) → (Z.card:ℝ) ≤ C := by
  obtain ⟨v,hv,short⟩ := select_sieve_length H
  let y := 2*(v+8)
  let A := Real.exp y*tiltLoss v
  let B := Real.exp y*tiltLoss 1
  have hA : 0 < A := mul_pos (Real.exp_pos _) (tiltLoss_pos hv)
  have hB : 0 < B := mul_pos (Real.exp_pos _) (tiltLoss_pos (by decide))
  let C := 8*A*(Real.exp ((y:ℝ)*H))^2*B
  let D := 32*A*Real.exp ((y:ℝ)*(2*H))*(B+1)
  have hD : 0 < D := by dsimp only [D];positivity
  refine ⟨D,C,hD,by dsimp only [C]; positivity,?_⟩
  have castT := tendsto_natCast_atTop_atTop (R := ℝ)
  have logT := Real.tendsto_log_atTop.comp castT
  let M := 8*(A*(8*(1+2*(2*T+1))))
  filter_upwards [eventually_ge_atTop (9:ℕ),logT.eventually_ge_atTop (4*H),
      castT.eventually_ge_atTop (16*(1+2*T)),castT.eventually_ge_atTop M,castT.eventually_ge_atTop (16*A*(3*(2+2*(2*T+1))))] with Q hQ9 hlog hrough hcross hextra
  have hQ : 2 ≤ Q := by omega
  let x := (Q:ℝ)
  let l := Real.log x
  let η := 1/l
  let σ := 1-H/l
  let U := Q^12
  let V := Q^v
  let W := Q
  let Y := Q^y
  have x1 : 1 < x := by dsimp only [x]; exact_mod_cast hQ
  have x0 := zero_lt_one.trans x1
  have hl : 0 < l := Real.log_pos x1
  have hη : 0 < η := one_div_pos.mpr hl
  have Hlo : H/l ≤ 1/4 := (div_le_iff₀ hl).mpr (by change 4*H ≤ l at hlog; linarith only [hlog])
  have hs : 3/4 ≤ σ := by dsimp only [σ]; linarith only [Hlo]
  have hs1 : σ ≤ 1 := sub_le_self _ (div_nonneg hH hl.le)
  have hU : 1 ≤ U := Nat.one_le_pow _ _ (by omega)
  have hV : 1 < V := Nat.one_lt_pow (show 0 < v from hv).ne' hQ
  have hUY : U ≤ Y := Nat.pow_le_pow_right (by omega) (show 12 ≤ y by dsimp only [y];omega)
  have hWU : W*W ≤ U := (sq W).symm.le.trans (Nat.pow_le_pow_right (by omega) (by decide : 2 ≤ 12))
  have hVW : V*W ≤ Y := (pow_succ Q v).symm.le.trans (Nat.pow_le_pow_right (by omega) (show v+1 ≤ y by dsimp only [y];omega))
  obtain ⟨a,ha1,ha,EA⟩ := exists_sievePolynomial_harmonic V hV η hη
  obtain ⟨b,hb1,hb,EB⟩ := exists_sievePolynomial_harmonic W hQ η hη
  have Uη : (U:ℝ)^η = Real.exp 12 := by simpa only [Nat.cast_ofNat,mul_one] using tilt_identity hQ 12 1
  have Yη : (Y:ℝ)^η = Real.exp y := by simpa only [mul_one] using tilt_identity hQ y 1
  have lossV : (V:ℝ)^(-η)/(1-(V:ℝ)^(-η)) = tiltLoss v := by
    have e := tilt_identity hQ v (-1)
    dsimp only [V,η,l,x,tiltLoss]
    rw [←neg_div,e,mul_neg_one]
  have lossW : (W:ℝ)^(-η)/(1-(W:ℝ)^(-η)) = tiltLoss 1 := by
    have e := tilt_identity hQ 1 (-1)
    simp only [pow_one,Nat.cast_one,one_mul] at e
    dsimp only [W,η,l,x,tiltLoss]
    rw [←neg_div,e,Nat.cast_one]
  have Uσ : (U:ℝ)^(1-σ) = Real.exp (12*H) := by
    rw [show 1-σ = H/l by dsimp only [σ];ring]
    exact tilt_identity hQ 12 H
  have Yσ : (Y:ℝ)^(1-σ) = Real.exp ((y:ℝ)*H) := by
    rw [show 1-σ = H/l by dsimp only [σ];ring]
    exact tilt_identity hQ y H
  have member {K n : ℕ} (hn : n ∈ Finset.Ioc 1 K) : 2 ≤ n ∧ n ≤ K := mem_Ioc.mp hn
  have long {n : ℕ} (hn : n ∈ Finset.Ioc U Y) : 2 ≤ n ∧ n ≤ Y :=
    ⟨by have := (mem_Ioc.mp hn).1;omega,(mem_Ioc.mp hn).2⟩
  have aU := EA U (Finset.Ioc 1 U) (fun _ hn => member hn)
  have bU := EB U (Finset.Ioc 1 U) (fun _ hn => member hn)
  have aY := EA Y (Finset.Ioc U Y) (fun _ hn => long hn)
  have bY := EB Y (Finset.Ioc U Y) (fun _ hn => long hn)
  rw [Uη,lossV] at aU
  rw [Uη,lossW] at bU
  rw [Yη,lossV] at aY
  rw [Yη,lossW] at bY
  have half (m : ℕ) : ((Q^(2*m):ℕ):ℝ)^(-(1/2:ℝ)) = (x^m)⁻¹ := by
    rw [Nat.cast_pow,←Real.rpow_natCast_mul x0.le,show ((2*m:ℕ):ℝ)*(-(1/2))= -(m:ℝ) by push_cast;ring,
      Real.rpow_neg x0.le,Real.rpow_natCast]
  have X6 : x ≤ x^6 := by simpa only [pow_one] using pow_le_pow_right₀ x1.le (by decide : 1 ≤ 6)
  have X2 : x ≤ x^2 := by simpa only [pow_one] using pow_le_pow_right₀ x1.le (by decide : 1 ≤ 2)
  have cross : A*((W:ℝ)^2*(8*x^2*(1+2*(2*T+1))*(U:ℝ)^(-(1/2:ℝ)))) ≤ 1/8 := by
    rw [show (U:ℝ)^(-(1/2:ℝ)) = (x^6)⁻¹ from half 6]
    change A*(x^2*(8*x^2*(1+2*(2*T+1))*(x^6)⁻¹)) ≤ 1/8
    rw [show A*(x^2*(8*x^2*(1+2*(2*T+1))*(x^6)⁻¹)) = (A*(8*(1+2*(2*T+1))))/(x^2) by field_simp]
    apply (div_le_iff₀ (pow_pos x0 2)).mpr
    have h : 8*(A*(8*(1+2*(2*T+1)))) ≤ x^2 := hcross.trans X2
    linarith only [h]
  intro Z q _ χ s distinct zeros
  have htop (i : ι) (hi : i ∈ Z) : (s i).re < 1 := by
    obtain ⟨_,_,hn,hz,_⟩ := zeros i hi
    exact lt_of_not_ge (fun re => ((χ i).LFunction_ne_zero_of_one_le_re (Or.inl hn) re) hz)
  have large (i : ι) (hi : i ∈ Z) : 1/2 ≤ ‖∑ n ∈ Finset.Ioc U Y, sieveSample (χ i) (s i) V W a b n‖ := by
    obtain ⟨qle,_,hn,hz,hre,ht⟩ := zeros i hi
    have hhalf : 1/2 ≤ (s i).re := by linarith only [hs,hre]
    have hpos : 0 < (s i).re := by linarith only [hhalf]
    have h := sieved_zero_detector (χ i) hn (s i) hpos hz σ hre U V W Y hU hV.le (by omega) hUY hVW a b ha hb ha1 hb1
    rw [Uσ] at h
    have short' := (mul_le_mul_of_nonneg_left (mul_le_mul (Real.sqrt_le_sqrt aU) (Real.sqrt_le_sqrt bU)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) (Real.exp_pos _).le).trans short
    have div : ‖s i‖/(s i).re ≤ 2*T := (div_le_iff₀ hpos).mpr (by nlinarith only [ht,mul_le_mul_of_nonneg_left hhalf hT])
    have Y1 : (1:ℝ) ≤ Y := by exact_mod_cast hU.trans hUY
    have py := (Real.rpow_le_rpow_of_exponent_le Y1 (neg_le_neg hhalf)).trans_eq (half (v+8))
    have rough : (V:ℝ)*W*(4*(q i:ℝ)*(1+‖s i‖/(s i).re)*(Y:ℝ)^(-(s i).re)) ≤ 1/4 := calc
      _ ≤ x^v*x*(4*x*(1+2*T)*(x^(v+8))⁻¹) := by
        rw [show (V:ℝ) = x^v from Nat.cast_pow Q v]
        change x^v*x*(4*(q i:ℝ)*(1+‖s i‖/(s i).re)*(Y:ℝ)^(-(s i).re)) ≤ _
        gcongr
        exact (Nat.cast_le.mpr qle : (q i:ℝ) ≤ (Q:ℝ))
      _ = (4*(1+2*T))/x^6 := by rw [pow_add];field_simp
      _ ≤ _ := (div_le_iff₀ (pow_pos x0 6)).mpr (by have h : 16*(1+2*T) ≤ x^6 := hrough.trans X6; linarith only [h])
    linarith only [rough,short',h]
  let E := 1/(8*A)
  have hE : 0 < E := by dsimp only [E];positivity
  have absorb : A*E ≤ 1/8 := le_of_eq (by dsimp only [E];field_simp)
  have pair (i : ι) (hi : i ∈ Z) (j : ι) (hj : j ∈ Z) (hij : i ≠ j) :
      ‖∑ n ∈ Finset.Ioc U Y, sieveGram (χ i) (χ j) (s i) (s j) (sievePolynomial (Finset.Icc 1 W) b) n‖ ≤ E := by
    obtain ⟨qi,pi,_,_,si,ti⟩ := zeros i hi
    obtain ⟨qj,pj,_,_,sj,tj⟩ := zeros j hj
    rcases distinct i hi j hj hij with hd|hsep
    · apply (sieveGram_cross (χ i) (χ j) pi pj hd (s i) (s j) T (hs.trans si) (hs.trans sj)
        (htop i hi).le (htop j hj).le ti tj U W Y hU hWU hUY b hb).trans
      have qq : ((q i*q j:ℕ):ℝ) ≤ x^2 := by dsimp only [x];exact_mod_cast (Nat.mul_le_mul qi qj).trans_eq (sq Q).symm
      apply le_trans (b := (W:ℝ)^2*(8*x^2*(1+2*(2*T+1))*(U:ℝ)^(-(1/2:ℝ)))) (by gcongr)
      apply (le_div_iff₀ (by positivity : (0:ℝ) < 8*A)).mpr
      linarith only [cross]
    · exact separated_gram_at_scale (χ i) (χ j) b hb (s i) (s j) H T A B D hQ9
        (show 13 ≤ y by dsimp only [y]; omega) qi qj hT hA hD hs si sj (htop i hi).le (htop j hj).le
        ti tj hsep hextra le_rfl bY
  have result := sieved_density_with_cross Z q χ s U V W Y σ A B E hs1 hA.le hB.le hE.le a b
    (fun i hi => (zeros i hi).2.2.2.2.1) pair large aY bY absorb
  rwa [Yσ] at result

end Conjectures.Goldbach.BinaryShiftZeroDensity
end
end

section
open Complex Finset Filter DirichletCharacter
noncomputable section
namespace Conjectures.Goldbach.BinaryShiftZeroDensity

/-- At fixed logarithmic distance from 1 and bounded height the number
of distinct primitive characters carrying a zero is bounded independently
of their conductor cutoff. -/
theorem primitive_nearOne_bounded {ι : Type*} (H T : ℝ) (hH : 0 ≤ H) (hT : 0 ≤ T) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ Q : ℕ in atTop, ∀ (Z : Finset ι) (q : ι → ℕ) [∀ i, NeZero (q i)]
      (χ : (i : ι) → DirichletCharacter ℂ (q i)) (s : ι → ℂ),
      Set.InjOn (fun i => (⟨q i,χ i⟩ : Σ k : ℕ, DirichletCharacter ℂ k)) (Z:Set ι) →
      (∀ i ∈ Z, q i ≤ Q ∧ (χ i).IsPrimitive ∧ χ i ≠ 1 ∧ (χ i).LFunction (s i) = 0 ∧
        1-H/Real.log Q ≤ (s i).re ∧ ‖s i‖ ≤ T) → (Z.card:ℝ) ≤ C := by
  obtain ⟨D,C,_,hC,law⟩ := primitive_nearOne_separated (ι := ι) H T hH hT
  refine ⟨C,hC,?_⟩
  filter_upwards [law] with Q count
  intro Z q _ χ s distinct zeros
  exact count Z q χ s (fun i hi j hj hij => Or.inl (fun e => hij (distinct hi hj e))) zeros

end Conjectures.Goldbach.BinaryShiftZeroDensity
end
end

section
open Complex Finset Filter DirichletCharacter Goldbach GoldbachTwistedMellin
noncomputable section
namespace Conjectures.Goldbach.BinaryShiftZeroDensity

/-- The actual finite list used by the signed explicit formula has a
uniformly bounded number of primitive character labels in the near-one
rectangle at every truncation height and every larger ambient scale. -/
theorem nearOneCharacters_bounded (H T : ℝ) (hH : 0 ≤ H) (hT : 0 ≤ T) :
    ∃ B : ℕ, ∀ᶠ Q : ℕ in atTop, ∀ m X : ℕ, Q ≤ X →
      (nearOneCharacters m Q (1-H/Real.log X) T).card ≤ B := by
  obtain ⟨C,_,count⟩ := primitive_nearOne_bounded (ι := PositiveLevelCharacter) H (1+T) hH (by linarith)
  obtain ⟨B,hB⟩ := exists_nat_ge C
  refine ⟨B,?_⟩
  filter_upwards [count,nearOneCharacters_witnesses H T hH] with Q law choices
  intro m X hQX
  obtain ⟨z,hz⟩ := choices m X hQX
  have h := law (nearOneCharacters m Q (1-H/Real.log X) T) (fun p => p.1+1)
    (fun p => p.2) z positiveLevel_injective.injOn hz
  exact_mod_cast h.trans hB

/-- The catalogue with analytic multiplicities costs at most one factor
of the conductor logarithm by the unit-height slice estimate. -/
theorem nearOne_zero_multiplicity_log (H T : ℝ) (hH : 0 ≤ H) (hT : 0 ≤ T) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ Q : ℕ in atTop, ∀ m X : ℕ, Q ≤ X →
      (∑ p ∈ nearOneCharacters m Q (1-H/Real.log X) T,
        ∑ z ∈ nearOneRoots m p.2 (1-H/Real.log X) T,
          (analyticOrderNatAt (regularizedL p.2) z:ℝ)) ≤ C*(1+Real.log Q) := by
  obtain ⟨A,hA,per⟩ := nearOneRoots_mass T hT
  obtain ⟨B,count⟩ := nearOneCharacters_bounded H T hH hT
  refine ⟨(B+1:ℝ)*A,by positivity,?_⟩
  filter_upwards [count] with Q law
  intro m X hQX
  let Z := nearOneCharacters m Q (1-H/Real.log X) T
  let l := 1+Real.log (Q:ℝ)
  have hl : 0 ≤ l := by dsimp only [l];linarith [Real.log_natCast_nonneg Q]
  calc
    _ ≤ ∑ _p ∈ Z, A*l := by
      apply sum_le_sum
      intro p hp
      have hq : p.1+1 ≤ Q := mem_range.mp (Finset.mem_sigma.mp hp).1
      apply (per m _ p.2 _).trans
      exact mul_le_mul_of_nonneg_left (add_le_add_right (Real.log_le_log (by positivity) (by exact_mod_cast hq)) 1) hA.le
    _ = (Z.card:ℝ)*(A*l) := by simp
    _ ≤ (B+1:ℝ)*(A*l) := by
      have h : (Z.card:ℝ) ≤ B := by exact_mod_cast law m X hQX
      exact mul_le_mul_of_nonneg_right (h.trans (by linarith)) (mul_nonneg hA.le hl)
    _ = _ := by ring

/-- The conductor 1 supplies the pole profile in addition to the actual
primitive characters that carry a bounded-height near-one zero. -/
def nearOneConductors (m Q X : ℕ) (H T : ℝ) : Finset ℕ :=
  insert 1 ((nearOneCharacters m Q (1-H/Real.log X) T).image (fun p => p.1+1))

/-- One common denominator cutoff and one positive saving exponent work
for all residue pairs in the actual near-one catalogue, including the
pole. No bound on the size of the catalogue is assumed. -/
theorem nearOne_residuePair_power_saving (H T : ℝ) (hH : 0 ≤ H) (hT : 0 ≤ T) :
    ∃ κ C : ℝ, 0 < κ ∧ 0 < C ∧ ∀ᶠ Q : ℕ in atTop, ∀ m : ℕ, 2 ≤ m → Q ≤ m+2 →
      let X : ℝ := (m+2:ℕ)
      ∃ P : ℝ, X^(11/40:ℝ) ≤ P ∧ P ≤ X^(3/10:ℝ) ∧
        ∀ (r s : ℕ) [NeZero r] [NeZero s] (α : DirichletCharacter ℂ r) (β : DirichletCharacter ℂ s),
        r ∈ nearOneConductors m Q (m+2) H T → s ∈ nearOneConductors m Q (m+2) H T →
        (Nat.lcm r s:ℝ) ≤ P → α.IsPrimitive → β.IsPrimitive →
        ∀ (n : ℕ) (z t : Option ℂ), 0 < n → n ≤ m+2 → Even n →
          let a := z.getD 1
          let b := t.getD 1
          let S := ∑' d, TwistedGoldbachSingularSeries.coefficient α β n d
          5/8 ≤ a.re → a.re ≤ 1 → |a.im| ≤ T → 5/8 ≤ b.re → b.re ≤ 1 → |b.im| ≤ T →
          ‖BinaryShiftMajorModel.primitiveResidueContribution α β m n P z t -
            S*((n:ℂ)^(a+b-1)*Complex.betaIntegral a b)‖ ≤ ‖S‖*(C*X^(1-κ)) := by
  obtain ⟨B,count⟩ := nearOneCharacters_bounded H T hH hT
  obtain ⟨κ,C,hκ,hC,common⟩ := BinaryShiftMajorModel.residuePair_common_power_saving (B+1) hT
  refine ⟨κ,C,hκ,hC,?_⟩
  filter_upwards [count] with Q law
  intro m hm hQ
  apply common m hm (nearOneConductors m Q (m+2) H T)
  apply (Finset.card_insert_le ..).trans
  exact Nat.add_le_add_right (Finset.card_image_le.trans (law m (m+2) hQ)) 1

end Conjectures.Goldbach.BinaryShiftZeroDensity
end
end

section
open Complex Finset DirichletCharacter Filter Goldbach GoldbachTwistedMellin
noncomputable section
namespace Conjectures.Goldbach.BinaryShiftZeroDensity

private theorem packing_and_cover {ι : Type*} (S : Finset ι) (f : ι → ℝ) (δ : ℝ) (hδ : 0 ≤ δ) :
    ∃ P : Finset ι, P ⊆ S ∧ (∀ i ∈ P, ∀ j ∈ P, i ≠ j → δ ≤ |f i-f j|) ∧
      ∀ i ∈ S, ∃ j ∈ P, |f i-f j| ≤ δ := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨∅,by simp,by simp,by simp⟩
  | @insert k S hk ih =>
    obtain ⟨P,hP,sep,cov⟩ := ih
    by_cases near : ∃ j ∈ P, |f k-f j| ≤ δ
    · refine ⟨P,hP.trans (Finset.subset_insert ..),sep,?_⟩
      intro i hi
      rcases mem_insert.mp hi with e|hin
      · simpa only [e] using near
      · exact cov i hin
    · have far (j : ι) (hj : j ∈ P) : δ ≤ |f k-f j| :=
        (lt_of_not_ge (fun h => near ⟨j,hj,h⟩)).le
      refine ⟨insert k P,Finset.insert_subset_insert _ hP,?_,?_⟩
      · intro i hi j hj hne
        by_cases ei : i=k
        · subst i
          exact far j ((mem_insert.mp hj).resolve_left hne.symm)
        · have iP := (mem_insert.mp hi).resolve_left ei
          rcases mem_insert.mp hj with ej|jP
          · subst j
            rw [abs_sub_comm]
            exact far i iP
          · exact sep i iP j jP hne
      · intro i hi
        rcases mem_insert.mp hi with rfl|hi
        · exact ⟨_,mem_insert_self ..,by simpa using hδ⟩
        · obtain ⟨j,hj,h⟩ := cov _ hi
          exact ⟨j,mem_insert_of_mem hj,h⟩

private theorem nearOneRoots_uniform_mass (H T : ℝ) (hH : 0 ≤ H) (hT : 0 ≤ T) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ Q : ℕ in atTop, ∀ (m X : ℕ), Q ≤ X →
      ∀ p ∈ nearOneCharacters m Q (1-H/Real.log X) T,
        (∑ z ∈ nearOneRoots m p.2 (1-H/Real.log X) T, (analyticOrderNatAt (regularizedL p.2) z:ℝ)) ≤ C := by
  classical
  obtain ⟨D,F,hD,hF,count⟩ := primitive_nearOne_separated (ι := ℂ) H (1+T) hH (by linarith)
  obtain ⟨A,hA,rect⟩ := NearOneZeroMultiplicity.rectangle_mass
  let K := H+D+1
  let L := Real.log (2*(2+T))
  let B := A+694400*(1+L)
  let C := 8+32*K*B
  have hK : 0 < K := by dsimp only [K];linarith
  have hL : 0 ≤ L := Real.log_nonneg (by linarith)
  have hB : 0 ≤ B := by dsimp only [B];positivity
  have hC : 0 < C := by dsimp only [C];positivity
  refine ⟨F*C,mul_pos hF hC,?_⟩
  have logT := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [count,nearOneCharacters_witnesses H T hH,logT.eventually_ge_atTop (max 1 (8*K)),eventually_ge_atTop (2:ℕ)] with Q law witnesses hg hQ
  intro m X hQX p hp
  let l := Real.log (Q:ℝ)
  let h := K/l
  let δ := D/l
  have l1 : 1 ≤ l := (le_max_left ..).trans hg
  have l0 := zero_lt_one.trans_le l1
  have hq0 : (0:ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  have logle : l ≤ Real.log X := Real.log_le_log hq0 (Nat.cast_le.mpr hQX)
  have hη : 0 < h := div_pos hK l0
  have h8 : h ≤ 1/8 := (div_le_iff₀ l0).mpr (by have h8 : 8*K ≤ l := (le_max_right ..).trans hg;linarith)
  have hδ : 0 < δ := div_pos hD l0
  have δh : δ ≤ h := div_le_div_of_nonneg_right (by dsimp only [K];linarith) l0.le
  have HH : H/Real.log X ≤ H/l := div_le_div_of_nonneg_left hH l0 logle
  have Hh : H/l ≤ h := div_le_div_of_nonneg_right (by dsimp only [K];linarith) l0.le
  obtain ⟨w,allw⟩ := witnesses m X hQX
  obtain ⟨pq,pprim,pnon,_,_,_⟩ := allw p hp
  let Z := nearOneRoots m p.2 (1-H/Real.log X) T
  let wt (z : ℂ) := (analyticOrderNatAt (regularizedL p.2) z:ℝ)
  have points (z : ℂ) (hz : z ∈ Z) :
      p.2.LFunction z=0 ∧ ExceptionalZeroCatalogue.genuine p.2 z ∧
      1-H/l ≤ z.re ∧ ‖z‖ ≤ 1+T ∧ |z.im| ≤ T := by
    obtain ⟨hz,hre,ht⟩ := Finset.mem_filter.mp hz
    obtain ⟨hr,_,root⟩ := (mem_exceptionalZeros ..).mp hz
    have right := re_lt_one_of_regularizedL_zero p.2 root
    refine ⟨by simpa [regularizedL,pnon] using root,(ExceptionalZeroCatalogue.regular_zero p.2 z).mp root,by linarith only [HH,hre],?_,ht⟩
    apply (norm_le_abs_re_add_abs_im z).trans
    rw [abs_of_nonneg (by linarith only [hr] : 0 ≤ z.re)]
    linarith only [right,ht]
  obtain ⟨P,hP,sep,cov⟩ := packing_and_cover Z Complex.im δ hδ.le
  have card : (P.card:ℝ) ≤ F := law P (fun _ => p.1+1) (fun _ => p.2) id
    (fun i hi j hj e => Or.inr (sep i hi j hj e))
    (fun i hi => ⟨pq,pprim,pnon,(points i (hP hi)).1,(points i (hP hi)).2.2.1,(points i (hP hi)).2.2.2.1⟩)
  have each (t : ℂ) (ht : t ∈ P) : (∑ z ∈ Z.filter (fun z => |z.im-t.im| ≤ δ), wt z) ≤ C := by
    have hy := (points t (hP ht)).2.2.2.2
    have logb : logHeight (p.1+1) t.im ≤ L+l := calc
      _ ≤ Real.log ((2*(2+T))*(Q:ℝ)) := by
        apply Real.log_le_log (by change 0 < 2*((p.1+1:ℕ):ℝ)*(2+|t.im|);positivity)
        calc
          _ ≤ 2*(Q:ℝ)*(2+T) := by gcongr
          _ = _ := by ring
      _ = _ := Real.log_mul (by positivity) hq0.ne'
    have budget : A+694400*logHeight (p.1+1) t.im ≤ B*l := by
      have t1 := mul_le_mul_of_nonneg_left l1 (by positivity : 0 ≤ A+694400*L)
      dsimp only [B]
      nlinarith only [logb,t1]
    let S := Z.filter (fun z => |z.im-t.im| ≤ δ)
    have r := (rect (p.1+1) p.2 t.im h hη h8 S (fun z hz => by
      obtain ⟨hzin,hγ⟩ := mem_filter.mp hz
      have info := points z hzin
      exact ⟨by linarith only [info.2.2.1,Hh],hγ.trans δh,info.2.1⟩)).1
    let N := (∑ z ∈ S, analyticOrderNatAt (regularizedL p.2) z : ℕ)
    change 3*(N:ℝ) ≤ 8+32*h*(A+694400*logHeight (p.1+1) t.im) at r
    have rhs := mul_le_mul_of_nonneg_left budget (mul_nonneg (by norm_num : (0:ℝ) ≤ 32) hη.le)
    have cost : 32*h*(B*l) = 32*K*B := by dsimp only [h];field_simp
    have mpos : 0 ≤ (N:ℝ) := Nat.cast_nonneg _
    change (∑ z ∈ S,(analyticOrderNatAt (regularizedL p.2) z:ℝ)) ≤ C
    rw [←Nat.cast_sum]
    change (N:ℝ) ≤ 8+32*K*B
    linarith only [r,rhs,cost,mpos]
  change (∑ z ∈ Z, wt z) ≤ F*C
  calc
    _ ≤ ∑ z ∈ Z, ∑ t ∈ P, if |z.im-t.im| ≤ δ then wt z else 0 := by
      apply sum_le_sum
      intro z hz
      obtain ⟨t,ht,hzt⟩ := cov z hz
      exact (show wt z = (if |z.im-t.im| ≤ δ then wt z else 0) from (ite_eq_left hzt).symm).trans_le
        (single_le_sum (f := fun t : ℂ => if |z.im-t.im| ≤ δ then wt z else 0)
          (fun _ _ => by split_ifs; exact Nat.cast_nonneg _; exact le_rfl) ht)
    _ = ∑ t ∈ P, ∑ z ∈ Z.filter (fun z => |z.im-t.im| ≤ δ), wt z := by rw [sum_comm];simp only [sum_filter]
    _ ≤ ∑ _t ∈ P, C := sum_le_sum each
    _ = (P.card:ℝ)*C := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right card hC.le

/-- Uniform bounded-height log-free zero density on the actual primitive
catalogue, counting analytic multiplicities. Both the explicit-formula
height and the ambient scale can vary. -/
theorem nearOne_zero_multiplicity_bounded (H T : ℝ) (hH : 0 ≤ H) (hT : 0 ≤ T) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ Q : ℕ in atTop, ∀ m X : ℕ, Q ≤ X →
      (∑ p ∈ nearOneCharacters m Q (1-H/Real.log X) T,
        ∑ z ∈ nearOneRoots m p.2 (1-H/Real.log X) T,
          (analyticOrderNatAt (regularizedL p.2) z:ℝ)) ≤ C := by
  obtain ⟨A,hA,each⟩ := nearOneRoots_uniform_mass H T hH hT
  obtain ⟨B,count⟩ := nearOneCharacters_bounded H T hH hT
  refine ⟨(B+1:ℝ)*A,by positivity,?_⟩
  filter_upwards [each,count] with Q mass card
  intro m X hQ
  apply (sum_le_sum (mass m X hQ)).trans
  rw [sum_const,nsmul_eq_mul]
  have h : ((nearOneCharacters m Q (1-H/Real.log X) T).card:ℝ) ≤ B := by exact_mod_cast card m X hQ
  exact mul_le_mul_of_nonneg_right (h.trans (by linarith)) hA.le

end Conjectures.Goldbach.BinaryShiftZeroDensity
end
end

section
open Complex Finset Filter DirichletCharacter Goldbach GoldbachTwistedMellin
noncomputable section
namespace Conjectures.Goldbach.BinaryShiftZeroDensity

/-- The pole is labelled by none, and a zero by its primitive character
and its position. Multiplicities remain in the signed coefficients. -/
abbrev CatalogueEntry := Option (Σ _p : PositiveLevelCharacter, ℂ)

def nearOneCatalogue (m Q X : ℕ) (H T : ℝ) : Finset CatalogueEntry := by
  classical
  exact insert none (((nearOneCharacters m Q (1-H/Real.log X) T).sigma
    (fun p => nearOneRoots m p.2 (1-H/Real.log X) T)).image some)

def catalogueLevel : CatalogueEntry → ℕ
  | none => 1
  | some v => v.1.1+1

instance (v : CatalogueEntry) : NeZero (catalogueLevel v) := by cases v <;> exact ⟨by simp [catalogueLevel]⟩

def catalogueCharacter : (v : CatalogueEntry) → DirichletCharacter ℂ (catalogueLevel v)
  | none => 1
  | some v => v.1.2

def catalogueRoot : CatalogueEntry → Option ℂ
  | none => none
  | some v => some v.2

def catalogueWeight : CatalogueEntry → ℂ
  | none => 1
  | some v => -(analyticOrderNatAt (regularizedL v.1.2) v.2:ℂ)

private theorem catalogue_mass (m Q X : ℕ) (H T : ℝ) :
    (∑ v ∈ nearOneCatalogue m Q X H T, ‖catalogueWeight v‖) =
      1 + ∑ p ∈ nearOneCharacters m Q (1-H/Real.log X) T,
        ∑ z ∈ nearOneRoots m p.2 (1-H/Real.log X) T, (analyticOrderNatAt (regularizedL p.2) z:ℝ) := by
  classical
  rw [nearOneCatalogue,sum_insert (by simp),sum_image (fun _ _ _ _ h => Option.some.inj h),Finset.sum_sigma]
  simp [catalogueWeight]

private theorem catalogue_properties (m Q X : ℕ) (H T : ℝ) (hT : 0 ≤ T) (v : CatalogueEntry)
    (hv : v ∈ nearOneCatalogue m Q X H T) :
    catalogueLevel v ∈ nearOneConductors m Q X H T ∧ (catalogueCharacter v).IsPrimitive ∧
      5/8 ≤ ((catalogueRoot v).getD 1).re ∧ ((catalogueRoot v).getD 1).re ≤ 1 ∧
      |((catalogueRoot v).getD 1).im| ≤ T := by
  classical
  cases v with
  | none =>
    exact ⟨mem_insert_self ..,isPrimitive_one_level_one,by norm_num [catalogueRoot],by simp [catalogueRoot],by simpa [catalogueRoot] using hT⟩
  | some v =>
    obtain ⟨p,z⟩ := v
    have hz : (⟨p,z⟩ : Σ _ : PositiveLevelCharacter, ℂ) ∈ (nearOneCharacters m Q (1-H/Real.log X) T).sigma
        (fun a => nearOneRoots m a.2 (1-H/Real.log X) T) := by simpa [nearOneCatalogue] using hv
    obtain ⟨hp,root⟩ := Finset.mem_sigma.mp hz
    have pr := (mem_filter.mp (Finset.mem_sigma.mp hp).2).2.1
    obtain ⟨rect,_,height⟩ := Finset.mem_filter.mp root
    obtain ⟨lo,_,zero⟩ := (mem_exceptionalZeros ..).mp rect
    exact ⟨mem_insert_of_mem (mem_image_of_mem _ hp),pr,lo.le,(re_lt_one_of_regularizedL_zero p.2 zero).le,height⟩

/-- The exact signed residue sum on the retained conductor pairs. A
kernel can be chosen either from the finite arc integral or its full
Beta integral. -/
def cataloguePairSum (Z : Finset CatalogueEntry) (P : ℝ) (f : CatalogueEntry → CatalogueEntry → ℂ) : ℂ :=
  ∑ v ∈ Z, ∑ w ∈ Z, if (Nat.lcm (catalogueLevel v) (catalogueLevel w):ℝ) ≤ P
    then catalogueWeight v*catalogueWeight w*f v w else 0

/-- Fourier inversion pairs the zeros of each character with the
coefficient of its inverse. -/
def catalogueArcTerm (m n : ℕ) (P : ℝ) (v w : CatalogueEntry) : ℂ :=
  BinaryShiftMajorModel.primitiveResidueContribution (catalogueCharacter v)⁻¹ (catalogueCharacter w)⁻¹ m n P
    (catalogueRoot v) (catalogueRoot w)

def catalogueBetaTerm (n : ℕ) (v w : CatalogueEntry) : ℂ :=
  let s := (catalogueRoot v).getD 1
  let t := (catalogueRoot w).getD 1
  (∑' d, TwistedGoldbachSingularSeries.coefficient (catalogueCharacter v)⁻¹ (catalogueCharacter w)⁻¹ n d) *
    ((n:ℂ)^(s+t-1)*Complex.betaIntegral s t)

private theorem catalogue_pair_sum_error (Z : Finset CatalogueEntry) (P B : ℝ) (hB : 0 ≤ B)
    (f g : CatalogueEntry → CatalogueEntry → ℂ)
    (h : ∀ i ∈ Z, ∀ j ∈ Z, (Nat.lcm (catalogueLevel i) (catalogueLevel j):ℝ) ≤ P → ‖f i j-g i j‖ ≤ B) :
    ‖cataloguePairSum Z P f-cataloguePairSum Z P g‖ ≤ (∑ i ∈ Z, ‖catalogueWeight i‖)^2*B := by
  simp only [cataloguePairSum,←Finset.sum_sub_distrib]
  apply (norm_sum_le ..).trans
  calc
    _ ≤ ∑ i ∈ Z, ∑ j ∈ Z, ‖catalogueWeight i‖*‖catalogueWeight j‖*B := by
      apply sum_le_sum
      intro i hi
      apply (norm_sum_le ..).trans
      apply sum_le_sum
      intro j hj
      split_ifs with yes
      · rw [←mul_sub,norm_mul,norm_mul]
        exact mul_le_mul_of_nonneg_left (h i hi j hj yes) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      · simp only [sub_zero,norm_zero];positivity
    _ = _ := by simp_rw [←Finset.sum_mul,←Finset.mul_sum];rw [←Finset.sum_mul,←sq]

/-- Total power-saving error on the bounded-height near-one part of the
signed Goldbach major arcs. The ordinary singular series dominates
every twisted one, and all zero multiplicities are included uniformly. -/
theorem nearOneCatalogue_summed_power_saving (H T : ℝ) (hH : 0 ≤ H) (hT : 0 ≤ T) :
    ∃ κ C : ℝ, 0 < κ ∧ 0 < C ∧ ∀ᶠ Q : ℕ in atTop, ∀ m : ℕ, 2 ≤ m → Q ≤ m+2 →
      let X : ℝ := (m+2:ℕ)
      let Z := nearOneCatalogue m Q (m+2) H T
      ∃ P : ℝ, X^(11/40:ℝ) ≤ P ∧ P ≤ X^(3/10:ℝ) ∧ ∀ n : ℕ, 0 < n → n ≤ m+2 → Even n →
        let S := (∑' d, TwistedGoldbachSingularSeries.coefficient
          (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) n d).re
        ‖cataloguePairSum Z P (catalogueArcTerm m n P)-cataloguePairSum Z P (catalogueBetaTerm n)‖ ≤
          S*(C*X^(1-κ)) := by
  obtain ⟨D,hD,mass⟩ := nearOne_zero_multiplicity_bounded H T hH hT
  obtain ⟨κ,C,hκ,hC,per⟩ := nearOne_residuePair_power_saving H T hH hT
  refine ⟨κ,(1+D)^2*C,hκ,by positivity,?_⟩
  filter_upwards [mass,per] with Q total rule
  intro m hm hQ X Z
  obtain ⟨P,hP,hP',arc⟩ := rule m hm hQ
  refine ⟨P,hP,hP',?_⟩
  intro n hn hn' hEven S
  have S0 : 0 ≤ S := (norm_nonneg _).trans (TwistedGoldbachSingularSeries.infinite_domination isPrimitive_one_level_one isPrimitive_one_level_one n hn)
  have hX : 0 ≤ X := Nat.cast_nonneg _
  have factor : 0 ≤ C*X^(1-κ) := mul_nonneg hC.le (Real.rpow_nonneg hX _)
  have hpair (i : CatalogueEntry) (hi : i ∈ Z) (j : CatalogueEntry) (hj : j ∈ Z)
      (hij : (Nat.lcm (catalogueLevel i) (catalogueLevel j):ℝ) ≤ P) :
      ‖catalogueArcTerm m n P i j-catalogueBetaTerm n i j‖ ≤ S*(C*X^(1-κ)) := by
    obtain ⟨ic,ip,ir,ir',it⟩ := catalogue_properties m Q (m+2) H T hT i hi
    obtain ⟨jc,jp,jr,jr',jt⟩ := catalogue_properties m Q (m+2) H T hT j hj
    have bound := arc _ _ (catalogueCharacter i)⁻¹ (catalogueCharacter j)⁻¹ ic jc hij ip.inv jp.inv n (catalogueRoot i) (catalogueRoot j)
      hn hn' hEven ir ir' it jr jr' jt
    exact bound.trans (mul_le_mul_of_nonneg_right (TwistedGoldbachSingularSeries.infinite_domination ip.inv jp.inv n hn) factor)
  have hsum : (∑ i ∈ Z, ‖catalogueWeight i‖) ≤ 1+D := by
    change (∑ i ∈ nearOneCatalogue m Q (m+2) H T, _) ≤ _
    rw [catalogue_mass]
    exact add_le_add_right (total m (m+2) hQ) 1
  apply (catalogue_pair_sum_error Z P _ (mul_nonneg S0 factor) _ _ hpair).trans
  exact (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (sum_nonneg (fun _ _ => norm_nonneg _)) hsum 2)
    (mul_nonneg S0 factor)).trans_eq (by ring)

end Conjectures.Goldbach.BinaryShiftZeroDensity
end
end

section
open Complex Finset DirichletCharacter MeasureTheory GoldbachTwistedMellin
noncomputable section
namespace Conjectures.Goldbach.BinaryShiftZeroDensity

private theorem sum_multiples_supported {M : Type*} [AddCommMonoid M] (N l : ℕ) (hl : 0 < l)
    (f : ℕ → M) (support : ∀ n, ¬l ∣ n → f n = 0) (f0 : f 0 = 0) :
    (∑ k ∈ Finset.range (N/l+1), f (l*k)) = ∑ n ∈ Finset.Icc 1 N, f n := by
  have sets : (Finset.range (N/l+1)).image (l*·) = (Finset.range (N+1)).filter (l ∣ ·) := by
    ext n
    simp only [mem_image,mem_range,mem_filter,Nat.lt_succ_iff]
    constructor
    · rintro ⟨k,hk,rfl⟩
      exact ⟨by simpa only [Nat.mul_comm l] using (Nat.le_div_iff_mul_le hl).mp hk,dvd_mul_right ..⟩
    · rintro ⟨hN,⟨k,rfl⟩⟩
      exact ⟨k,(Nat.le_div_iff_mul_le hl).mpr (by simpa only [Nat.mul_comm k] using hN),rfl⟩
  have nozero : (0:ℕ) ∉ Finset.Icc 1 N := by simp
  have endpoints : Finset.range (N+1) = insert 0 (Finset.Icc 1 N) := by ext n;simp;omega
  calc
    _ = ∑ n ∈ (Finset.range (N+1)).filter (l ∣ ·), f n := by
      rw [←sets,Finset.sum_image (fun _ _ _ _ e => Nat.mul_left_cancel hl e)]
    _ = ∑ n ∈ Finset.range (N+1), f n := sum_subset (filter_subset ..) (fun n hn h =>
      support n (fun dv => h (mem_filter.mpr ⟨hn,dv⟩)))
    _ = _ := by simp [endpoints,nozero,f0]

/-- A single denominator of the retained primitive-character arc integral. -/
def catalogueDenominatorTerm (m n : ℕ) (P : ℝ) (q : ℕ) (v w : CatalogueEntry) : ℂ :=
  let width := P/((q:ℝ)*(m+2:ℕ))
  TwistedGoldbachSingularSeries.coefficient (catalogueCharacter v)⁻¹ (catalogueCharacter w)⁻¹ n q *
    ∫ u in -width..width, phase (-2*Real.pi*(n:ℝ)) u *
      (residueProfile m (catalogueRoot v) u * residueProfile m (catalogueRoot w) u)

private theorem denom_support (m n : ℕ) (P : ℝ) (q : ℕ) (v w : CatalogueEntry)
    (h : ¬ Nat.lcm (catalogueLevel v) (catalogueLevel w) ∣ q) :
    catalogueDenominatorTerm m n P q v w = 0 := by
  have neither := fun e => h (Nat.lcm_dvd_iff.mpr e)
  by_cases hq : q=0
  · simp [catalogueDenominatorTerm,TwistedGoldbachSingularSeries.coefficient,hq]
  · simp only [catalogueDenominatorTerm,TwistedGoldbachSingularSeries.coefficient,dite_eq_left hq,dite_eq_right neither,zero_mul]

theorem catalogueArcTerm_eq_sum_denominators (m n : ℕ) (P : ℝ) (v w : CatalogueEntry) :
    catalogueArcTerm m n P v w = ∑ q ∈ Finset.Icc 1 ⌊P⌋₊, catalogueDenominatorTerm m n P q v w := by
  let l := Nat.lcm (catalogueLevel v) (catalogueLevel w)
  have hl : 0 < l := Nat.lcm_pos (NeZero.pos _) (NeZero.pos _)
  let f (q : ℕ) := catalogueDenominatorTerm m n P q v w
  change (∑ k ∈ range (⌊P/(l:ℝ)⌋₊+1), f (l*k)) = _
  rw [Nat.floor_div_natCast]
  apply sum_multiples_supported _ _ hl f (fun q h => denom_support m n P q v w h)
  simp [f,catalogueDenominatorTerm,TwistedGoldbachSingularSeries.coefficient]

/-- Sum first over the actual positive major-arc denominators. Terms
whose conductor lcm does not divide the denominator vanish identically. -/
theorem catalogueArc_by_denominators (Z : Finset CatalogueEntry) (m n : ℕ) (P : ℝ) (hP : 0 ≤ P) :
    cataloguePairSum Z P (catalogueArcTerm m n P) =
      ∑ q ∈ Finset.Icc 1 ⌊P⌋₊, ∑ v ∈ Z, ∑ w ∈ Z,
        catalogueWeight v*catalogueWeight w*catalogueDenominatorTerm m n P q v w := by
  let D := Finset.Icc 1 ⌊P⌋₊
  let f (v w : CatalogueEntry) (q : ℕ) := catalogueWeight v*catalogueWeight w*catalogueDenominatorTerm m n P q v w
  have pair (v w : CatalogueEntry) :
      (if (Nat.lcm (catalogueLevel v) (catalogueLevel w):ℝ) ≤ P
      then catalogueWeight v*catalogueWeight w*catalogueArcTerm m n P v w else 0) = ∑ q ∈ D, f v w q := by
    split_ifs with yes
    · rw [catalogueArcTerm_eq_sum_denominators,Finset.mul_sum]
    · symm
      apply sum_eq_zero
      intro q hq
      obtain ⟨q1,qhigh⟩ := mem_Icc.mp hq
      have nodiv : ¬ Nat.lcm (catalogueLevel v) (catalogueLevel w) ∣ q := by
        intro hd
        exact yes ((Nat.cast_le.mpr ((Nat.le_of_dvd q1 hd).trans qhigh)).trans (Nat.floor_le hP))
      simp only [f,denom_support m n P q v w nodiv,mul_zero]
  change (∑ v ∈ Z, ∑ w ∈ Z, _) = ∑ q ∈ D, ∑ v ∈ Z, ∑ w ∈ Z, f v w q
  simp_rw [pair]
  calc
    (∑ v ∈ Z, ∑ w ∈ Z, ∑ q ∈ D, f v w q) = ∑ v ∈ Z, ∑ q ∈ D, ∑ w ∈ Z, f v w q :=
      sum_congr rfl (fun v _ => Finset.sum_comm)
    _ = _ := Finset.sum_comm

end Conjectures.Goldbach.BinaryShiftZeroDensity
end
end

section
open Complex Finset DirichletCharacter Goldbach GoldbachTwistedMellin
noncomputable section
namespace Conjectures.Goldbach.BinaryShiftZeroDensity

/-- The character label of a retained pole or zero at an ambient modulus. -/
def catalogueLift (q : ℕ) (v : CatalogueEntry) : DirichletCharacter ℂ q :=
  if h : catalogueLevel v ∣ q then changeLevel h (catalogueCharacter v) else 1

private theorem packed_eq_of_lifts {r t q : ℕ} [NeZero q] (α : DirichletCharacter ℂ r)
    (β : DirichletCharacter ℂ t) (hα : α.IsPrimitive) (hβ : β.IsPrimitive) (hr : r ∣ q) (ht : t ∣ q)
    (eqn : changeLevel hr α = changeLevel ht β) :
    (⟨r,α⟩ : Σ d : ℕ, DirichletCharacter ℂ d) = ⟨t,β⟩ := by
  have e := congrArg DirichletCharacter.conductor eqn
  rw [conductor_changeLevel,conductor_changeLevel,hα,hβ] at e
  subst t
  exact congrArg (Sigma.mk r) (changeLevel_injective hr eqn)

private theorem packed_primitive_lift (q : ℕ) [NeZero q] (v : CatalogueEntry)
    (hv : catalogueLevel v ∣ q) (hp : (catalogueCharacter v).IsPrimitive) :
    (⟨(catalogueLift q v).conductor,(catalogueLift q v).primitiveCharacter⟩ : Σ d : ℕ, DirichletCharacter ℂ d) =
      ⟨catalogueLevel v,catalogueCharacter v⟩ := by
  apply packed_eq_of_lifts _ _ (catalogueLift q v).primitiveCharacter_isPrimitive hp (catalogueLift q v).conductor_dvd_level hv
  rw [changeLevel_primitiveCharacter,catalogueLift,dite_eq_left hv]

private theorem root_transport {r t : ℕ} [NeZero r] [NeZero t] {α : DirichletCharacter ℂ r} {β : DirichletCharacter ℂ t}
    (e : (⟨r,α⟩ : Σ d : ℕ, DirichletCharacter ℂ d) = ⟨t,β⟩) (z : ℂ) (B : ℝ) :
    exceptionalZeros α B = exceptionalZeros β B ∧
      analyticOrderNatAt (regularizedL α) z = analyticOrderNatAt (regularizedL β) z := by
  obtain rfl : r=t := congrArg Sigma.fst e
  obtain rfl : α=β := eq_of_heq (Sigma.mk.inj_iff.mp e).2
  exact ⟨rfl,rfl⟩

/-- Each global catalogue label that occurs at q is an actual local
Dirichlet residue with the same signed analytic multiplicity. -/
theorem catalogueLift_residue (m Q X : ℕ) (H T : ℝ) (hT : 0 ≤ T) (v : CatalogueEntry)
    (hv : v ∈ nearOneCatalogue m Q X H T) (q : ℕ) [NeZero q] (hq : catalogueLevel v ∣ q) :
    catalogueRoot v ∈ BinaryShiftMajorModel.characterResidues m (catalogueLift q v) ∧
      BinaryShiftMajorModel.residueMultiplier (catalogueLift q v) (catalogueRoot v) = catalogueWeight v := by
  classical
  have prim := (catalogue_properties m Q X H T hT v hv).2.1
  have e := packed_primitive_lift q v hq prim
  let _ : NeZero (catalogueLift q v).conductor := ⟨(catalogueLift q v).conductor_ne_zero⟩
  cases v with
  | none =>
    have principal : catalogueLift q none = 1 := by
      simp only [catalogueLift,dite_eq_left hq,catalogueCharacter,map_one]
    exact ⟨mem_insert_self ..,by simp [BinaryShiftMajorModel.residueMultiplier,principal,catalogueWeight,catalogueRoot]⟩
  | some v =>
    obtain ⟨p,z⟩ := v
    have hz : (⟨p,z⟩ : Σ _ : PositiveLevelCharacter, ℂ) ∈ (nearOneCharacters m Q (1-H/Real.log X) T).sigma
        (fun a => nearOneRoots m a.2 (1-H/Real.log X) T) := by simpa [nearOneCatalogue] using hv
    have root := (Finset.mem_filter.mp (Finset.mem_sigma.mp hz).2).1
    have pair := root_transport e z (modelHeight (m+2:ℕ))
    constructor
    · apply mem_insert_of_mem
      apply mem_image_of_mem
      rw [pair.1]
      exact root
    · simp only [BinaryShiftMajorModel.residueMultiplier,catalogueRoot,catalogueWeight,pair.2,catalogueCharacter]
      rfl

/-- At a positive modulus, retaining primitive catalogue labels cannot
count any local character/residue pair twice. -/
theorem catalogueLift_injective (m Q X : ℕ) (H T : ℝ) (hT : 0 ≤ T) (q : ℕ) [NeZero q] :
    Set.InjOn (fun v : CatalogueEntry => (catalogueLift q v,catalogueRoot v))
      ((nearOneCatalogue m Q X H T).filter (fun v => catalogueLevel v ∣ q) : Finset CatalogueEntry) := by
  classical
  intro v hv w hw eqn
  obtain ⟨hv,dv⟩ := mem_filter.mp hv
  obtain ⟨hw,dw⟩ := mem_filter.mp hw
  have pv := (catalogue_properties m Q X H T hT v hv).2.1
  have pw := (catalogue_properties m Q X H T hT w hw).2.1
  have lifts := congrArg Prod.fst eqn
  have roots := congrArg Prod.snd eqn
  change catalogueRoot v = catalogueRoot w at roots
  have same : (⟨catalogueLevel v,catalogueCharacter v⟩ : Σ d : ℕ, DirichletCharacter ℂ d) =
      ⟨catalogueLevel w,catalogueCharacter w⟩ := packed_eq_of_lifts _ _ pv pw dv dw (by simpa only [catalogueLift,dite_eq_left dv,dite_eq_left dw] using lifts)
  cases v with
  | none =>
    cases w with
    | none => rfl
    | some t => simp [catalogueRoot] at roots
  | some v =>
    cases w with
    | none => simp [catalogueRoot] at roots
    | some w =>
      obtain ⟨p,z⟩ := v
      obtain ⟨t,v⟩ := w
      have ep : p=t := positiveLevel_injective same
      obtain rfl : z=v := Option.some.inj roots
      subst t
      rfl

end Conjectures.Goldbach.BinaryShiftZeroDensity
end
end

section
open Complex Finset Filter DirichletCharacter Goldbach GoldbachTwistedMellin
noncomputable section
namespace Conjectures.Goldbach.BinaryShiftZeroDensity

private theorem coefficient_symmetric {r t : ℕ} (α : DirichletCharacter ℂ r) (β : DirichletCharacter ℂ t) (n d : ℕ) :
    TwistedGoldbachSingularSeries.coefficient α β n d = TwistedGoldbachSingularSeries.coefficient β α n d := by
  classical
  by_cases hd : d=0
  · simp [hd,TwistedGoldbachSingularSeries.coefficient]
  let _ : NeZero d := ⟨hd⟩
  simp only [TwistedGoldbachSingularSeries.coefficient,dite_eq_left hd]
  by_cases h : r ∣ d ∧ t ∣ d
  · simp only [dite_eq_left h,dite_eq_left h.symm,TwistedGoldbachSingularSeries.gaussCoefficient]
    rw [mul_comm (changeLevel h.1 α) (changeLevel h.2 β),mul_comm (gaussSum _ _) (gaussSum _ _)]
  · simp [h,show ¬(t ∣ d ∧ r ∣ d) from fun e => h e.symm]

private theorem catalogueBetaTerm_swap (n : ℕ) (v w : CatalogueEntry) :
    catalogueBetaTerm n v w = catalogueBetaTerm n w v := by
  dsimp only [catalogueBetaTerm]
  rw [add_comm ((catalogueRoot v).getD 1) ((catalogueRoot w).getD 1),
    Complex.betaIntegral_symm ((catalogueRoot w).getD 1) ((catalogueRoot v).getD 1)]
  exact congrArg (· * _) (tsum_congr (coefficient_symmetric _ _ n))

private theorem mixed_series_decay {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r) (hp : χ.IsPrimitive)
    (n : ℕ) (hn : 0 < n) (he : Even n) :
    ‖∑' d, TwistedGoldbachSingularSeries.coefficient χ (1 : DirichletCharacter ℂ 1) n d‖ ≤
      (1152*(r:ℝ)^(-(1/2:ℝ))) *
        (∑' d, TwistedGoldbachSingularSeries.coefficient (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) n d).re := by
  let S := (∑' d, TwistedGoldbachSingularSeries.coefficient (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) n d)
  have dom : ‖S‖ ≤ S.re := TwistedGoldbachSingularSeries.infinite_domination isPrimitive_one_level_one isPrimitive_one_level_one n hn
  have r0 : 0 < (r:ℝ) := Nat.cast_pos.mpr (NeZero.pos _)
  have small : 2*(r:ℝ)/(r.totient:ℝ)^2 ≤ 1152*(r:ℝ)^(-(1/2:ℝ)) := calc
    _ = (2*(r:ℝ))*(1/(r.totient:ℝ)^2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (TwistedGoldbachSingularSeries.totient_weight (NeZero.pos r)) (by positivity : 0 ≤ 2*(r:ℝ))
    _ = _ := by
      rw [show -(1/2:ℝ) = 1+ -(3/2:ℝ) by norm_num,Real.rpow_add r0,Real.rpow_one];ring
  exact (TwistedGoldbachMixedPrincipal.mixed_bound χ hp n hn he).trans
    (mul_le_mul small dom (norm_nonneg _) (by positivity))

/-- A pole paired with a true near-one zero receives a power saving from
the primitive conductor, uniformly for every even target. -/
theorem catalogue_mixed_beta_decay (H T : ℝ) (hH : 0 ≤ H) (hT : 0 ≤ T) :
    ∃ κ C : ℝ, 0 < κ ∧ 0 < C ∧ ∀ (m Q X n : ℕ), 1 < X → 0 < n → n ≤ X → Even n →
      ∀ v ∈ nearOneCatalogue m Q X H T, v ≠ none →
      ‖catalogueBetaTerm n v none‖ ≤
        (∑' d, TwistedGoldbachSingularSeries.coefficient (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) n d).re *
        (C*(X:ℝ)^(1-κ)) := by
  classical
  obtain ⟨c,hc,conductor⟩ := nearOne_zero_conductor_bound
  let k := c/(2*(H+1))
  let A := 2*(2+T)
  have hA : 0 < A := by dsimp only [A];linarith
  have hk : 0 < k := by dsimp only [k];positivity
  refine ⟨k,2304*A^(1/2:ℝ),hk,by positivity,?_⟩
  intro m Q X n hX hn hnX he v hv hv'
  cases v with
  | none => exact (hv' rfl).elim
  | some v =>
    obtain ⟨p,z⟩ := v
    let χ := p.2
    let r := p.1+1
    let S := (∑' d, TwistedGoldbachSingularSeries.coefficient (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) n d).re
    have membership : (⟨p,z⟩ : Σ _ : PositiveLevelCharacter, ℂ) ∈ (nearOneCharacters m Q (1-H/Real.log X) T).sigma
        (fun a => nearOneRoots m a.2 (1-H/Real.log X) T) := by simpa [nearOneCatalogue] using hv
    obtain ⟨hχ,hz⟩ := mem_sigma.mp membership
    have hp : χ.IsPrimitive := (mem_filter.mp (mem_sigma.mp hχ).2).2.1
    obtain ⟨root,near,height⟩ := mem_filter.mp hz
    obtain ⟨left,_,zero⟩ := (mem_exceptionalZeros ..).mp root
    have x1 : 1 < (X:ℝ) := by exact_mod_cast hX
    have x0 := zero_lt_one.trans x1
    have lpos := Real.log_pos x1
    have r0 : 0 < (r:ℝ) := by dsimp only [r];positivity
    have hs := re_lt_one_of_regularizedL_zero χ zero
    have widened : 1-(H+1)/Real.log X ≤ z.re := by
      linarith only [near,div_le_div_of_nonneg_right (le_add_of_nonneg_right zero_le_one : H ≤ H+1) lpos.le]
    have big := conductor r χ hp X (H+1) T z x1 (by positivity) height widened zero
    have scale : (X:ℝ)^(c/(H+1)) ≤ A*(r:ℝ) := big.le.trans_eq (by dsimp only [A];ring)
    have save : (r:ℝ)^(-(1/2:ℝ)) ≤ A^(1/2:ℝ)*(X:ℝ)^(-k) := calc
      _ = A^(1/2:ℝ)*(A*(r:ℝ))^(-(1/2:ℝ)) := by
        rw [Real.mul_rpow hA.le r0.le,←mul_assoc,←Real.rpow_add hA,add_neg_cancel,Real.rpow_zero,one_mul]
      _ ≤ A^(1/2:ℝ)*((X:ℝ)^(c/(H+1)))^(-(1/2:ℝ)) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos x0 _) scale (by norm_num)) (Real.rpow_nonneg hA.le _)
      _ = _ := by rw [←Real.rpow_mul x0.le,show c/(H+1)*(-(1/2:ℝ)) = -k by dsimp only [k];rw [div_mul_eq_div_div_swap];ring]
    have absre : (1/2:ℝ) ≤ ‖z‖ := (by linarith only [left] : (1/2:ℝ) ≤ z.re).trans (Complex.re_le_norm _)
    have inv : ‖z⁻¹‖ ≤ 2 := by
      rw [norm_inv,inv_le_comm₀ (by linarith only [absre]) (by norm_num : (0:ℝ)<2)]
      simpa only [one_div] using absre
    have np : ‖(n:ℂ)^z‖ ≤ (X:ℝ) := by
      rw [norm_natCast_cpow_of_pos hn]
      exact (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn : 1 ≤ (n:ℝ)) hs.le).trans
        ((Real.rpow_one (n:ℝ)).le.trans (Nat.cast_le.mpr hnX))
    have mag := mixed_series_decay χ⁻¹ hp.inv n hn he
    have s0 : 0 ≤ S := (norm_nonneg _).trans (TwistedGoldbachSingularSeries.infinite_domination isPrimitive_one_level_one isPrimitive_one_level_one n hn)
    change ‖(∑' d, TwistedGoldbachSingularSeries.coefficient χ⁻¹ (1 : DirichletCharacter ℂ 1)⁻¹ n d) *
      ((n:ℂ)^(z+1-1)*Complex.betaIntegral z 1)‖ ≤ S*_
    rw [inv_one,add_sub_cancel_right,Complex.betaIntegral_eval_one_right (by linarith only [left]),one_div,norm_mul,norm_mul]
    apply (mul_le_mul mag (mul_le_mul np inv (norm_nonneg _) x0.le) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (mul_nonneg (by positivity) s0)).trans
    change 1152*(r:ℝ)^(-(1/2:ℝ))*S*((X:ℝ)*2) ≤ _
    apply (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left save (by norm_num : (0:ℝ) ≤ 1152)) s0)
      (by positivity : 0 ≤ (X:ℝ)*2)).trans_eq
    rw [sub_eq_add_neg,Real.rpow_add x0,Real.rpow_one];ring

end Conjectures.Goldbach.BinaryShiftZeroDensity
end
end

section
open Complex Finset Filter DirichletCharacter Goldbach GoldbachTwistedMellin
noncomputable section
namespace Conjectures.Goldbach.BinaryShiftZeroDensity

private def unmixedBetaTerm (n : ℕ) (v w : CatalogueEntry) : ℂ :=
  if v.isSome = w.isSome then catalogueBetaTerm n v w else 0

private theorem catalogue_pole_term (n : ℕ) :
    catalogueBetaTerm n none none = (∑' d, TwistedGoldbachSingularSeries.coefficient
      (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) n d) * (n:ℂ) := by
  change (∑' d, TwistedGoldbachSingularSeries.coefficient (1 : DirichletCharacter ℂ 1)⁻¹ (1 : DirichletCharacter ℂ 1)⁻¹ n d) *
    ((n:ℂ)^((1:ℂ)+1-1)*Complex.betaIntegral 1 1) = _
  rw [inv_one,add_sub_cancel_right,Complex.cpow_one,Complex.betaIntegral_eval_one_right (by norm_num)]
  simp only [div_one,mul_one]

private theorem unmixed_sum (Z : Finset CatalogueEntry) (n : ℕ) (P : ℝ) (hZ : none ∈ Z) (hP : 1 ≤ P) :
    cataloguePairSum Z P (unmixedBetaTerm n) = catalogueBetaTerm n none none +
      cataloguePairSum (Z.erase none) P (catalogueBetaTerm n) := by
  classical
  let W := Z.erase none
  have nz : none ∉ W := Finset.notMem_erase none Z
  have someOf (v : CatalogueEntry) (hv : v ∈ W) : v.isSome = true := by
    cases v with
    | none => exact (nz hv).elim
    | some v => rfl
  have levels : ((Nat.lcm (catalogueLevel none) (catalogueLevel none):ℕ):ℝ) ≤ P := by simpa [catalogueLevel] using hP
  have zsplit : Z = insert none W := (insert_erase hZ).symm
  have rwZ := congrArg (fun U => cataloguePairSum U P (unmixedBetaTerm n)) zsplit
  rw [rwZ,cataloguePairSum,cataloguePairSum,sum_insert nz,sum_insert nz]
  simp only [ite_eq_left levels,show catalogueWeight none = 1 by rfl,one_mul]
  have row0 : (∑ w ∈ W, if (Nat.lcm (catalogueLevel none) (catalogueLevel w):ℝ) ≤ P then
      catalogueWeight w * unmixedBetaTerm n none w else 0) = 0 := by
    apply sum_eq_zero
    intro w hw
    simp [unmixedBetaTerm,someOf w hw]
  rw [row0,add_zero]
  change catalogueBetaTerm n none none + _ = _
  apply congrArg (_+·)
  apply sum_congr rfl
  intro v hv
  rw [sum_insert nz]
  have first : (if (Nat.lcm (catalogueLevel v) (catalogueLevel none):ℝ) ≤ P then
      catalogueWeight v * catalogueWeight none * unmixedBetaTerm n v none else 0) = 0 := by
    simp [unmixedBetaTerm,someOf v hv]
  rw [first,zero_add]
  apply sum_congr rfl
  intro w hw
  simp only [unmixedBetaTerm,someOf v hv,someOf w hw,ite_true]

/-- After removing all pole--zero interactions, the retained major arcs
are the ordinary main term plus a sum over pairs of actual zeros. The
remainder saves a positive power uniformly at every positive even target. -/
theorem nearOneCatalogue_pole_and_zero_pairs (H T : ℝ) (hH : 0 ≤ H) (hT : 0 ≤ T) :
    ∃ κ C : ℝ, 0 < κ ∧ 0 < C ∧ ∀ᶠ Q : ℕ in atTop, ∀ m : ℕ, 2 ≤ m → Q ≤ m+2 →
      let X : ℝ := (m+2:ℕ)
      let Z := nearOneCatalogue m Q (m+2) H T
      ∃ P : ℝ, X^(11/40:ℝ) ≤ P ∧ P ≤ X^(3/10:ℝ) ∧ ∀ n : ℕ, 0 < n → n ≤ m+2 → Even n →
        let S := ∑' d, TwistedGoldbachSingularSeries.coefficient
          (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) n d
        ‖cataloguePairSum Z P (catalogueArcTerm m n P) -
          (S*(n:ℂ) + cataloguePairSum (Z.erase none) P (catalogueBetaTerm n))‖ ≤
            S.re*(C*X^(1-κ)) := by
  classical
  obtain ⟨a,A,ha,hA,arcs⟩ := nearOneCatalogue_summed_power_saving H T hH hT
  obtain ⟨b,B,hb,hB,mixed⟩ := catalogue_mixed_beta_decay H T hH hT
  obtain ⟨D,hD,mass⟩ := nearOne_zero_multiplicity_bounded H T hH hT
  refine ⟨min a b,A+(1+D)^2*B,lt_min ha hb,by positivity,?_⟩
  filter_upwards [arcs,mass] with Q arc total
  intro m hm hQ X Z
  obtain ⟨P,hP,hP',rule⟩ := arc m hm hQ
  refine ⟨P,hP,hP',?_⟩
  intro n hn hn' he S
  have x1 : 1 ≤ X := by dsimp only [X];exact_mod_cast (by omega : 1 ≤ m+2)
  have s0 : 0 ≤ S.re := (norm_nonneg _).trans (TwistedGoldbachSingularSeries.infinite_domination isPrimitive_one_level_one isPrimitive_one_level_one n hn)
  have factor : 0 ≤ S.re*(B*X^(1-b)) := by positivity
  have point (i : CatalogueEntry) (hi : i ∈ Z) (j : CatalogueEntry) (hj : j ∈ Z)
      (_ : (Nat.lcm (catalogueLevel i) (catalogueLevel j):ℝ) ≤ P) :
      ‖catalogueBetaTerm n i j - unmixedBetaTerm n i j‖ ≤ S.re*(B*X^(1-b)) := by
    by_cases h : i.isSome = j.isSome
    · simpa only [unmixedBetaTerm,ite_eq_left h,sub_self,norm_zero] using factor
    · simp only [unmixedBetaTerm,ite_eq_right h,sub_zero]
      cases i with
      | none =>
        cases j with
        | none => exact (h rfl).elim
        | some j => rw [catalogueBetaTerm_swap];exact mixed m Q (m+2) n (by omega) hn hn' he _ hj (by simp)
      | some i =>
        cases j with
        | none => exact mixed m Q (m+2) n (by omega) hn hn' he _ hi (by simp)
        | some j => exact (h rfl).elim
  have hsum : (∑ i ∈ Z, ‖catalogueWeight i‖) ≤ 1+D := by
    change (∑ i ∈ nearOneCatalogue m Q (m+2) H T, _) ≤ _
    rw [catalogue_mass]
    exact add_le_add_right (total m (m+2) hQ) 1
  have approx := (catalogue_pair_sum_error Z P _ factor _ _ point).trans
    (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (sum_nonneg (fun _ _ => norm_nonneg _)) hsum 2) factor)
  have zmem : none ∈ Z := by change none ∈ nearOneCatalogue ..;exact mem_insert_self ..
  have p1 : 1 ≤ P := (Real.one_le_rpow x1 (by norm_num : 0 ≤ (11/40:ℝ))).trans hP
  rw [unmixed_sum Z n P zmem p1,catalogue_pole_term] at approx
  apply (norm_sub_le_norm_sub_add_norm_sub _ (cataloguePairSum Z P (catalogueBetaTerm n)) _).trans ((add_le_add (rule n hn hn' he) approx).trans ?_)
  have pa := Real.rpow_le_rpow_of_exponent_le x1 (sub_le_sub_left (min_le_left a b) 1)
  have pb := Real.rpow_le_rpow_of_exponent_le x1 (sub_le_sub_left (min_le_right a b) 1)
  calc
    _ = S.re*(A*X^(1-a)) + ((1+D)^2*(S.re*B))*X^(1-b) := by ring
    _ ≤ S.re*(A*X^(1-min a b)) + ((1+D)^2*(S.re*B))*X^(1-min a b) := add_le_add
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left pa hA.le) s0)
      (mul_le_mul_of_nonneg_left pb (by positivity))
    _ = _ := by ring

end Conjectures.Goldbach.BinaryShiftZeroDensity
end
end

section
open Complex Finset DirichletCharacter
open scoped ComplexConjugate
noncomputable section
namespace Conjectures.Goldbach.TwistedGoldbachPairMean
open TwistedGoldbachLocalProduct TwistedGoldbachMixedPrincipal TwistedGoldbachSingularSeries

/-- Sum of squared target-frequency Gauss sums over an entire residue period. -/
private theorem gauss_target_energy {L : ℕ} [NeZero L] (χ : DirichletCharacter ℂ L) :
    (∑ u : ZMod L, ‖gaussSum χ (ZMod.stdAddChar.mulShift (-u))‖^2) ≤ (L:ℝ)^2 := by
  let K (r u : ZMod L) : ℂ := ZMod.stdAddChar (-u*r)
  have conjPhase (v : ZMod L) : conj (ZMod.stdAddChar v) = ZMod.stdAddChar (-v) := by
    rw [ZMod.stdAddChar_apply,ZMod.stdAddChar_apply,AddChar.map_neg_eq_inv,Circle.coe_inv_eq_conj]
  have cols (r s : ZMod L) : (∑ u : ZMod L, conj (K r u)*K s u) = if r=s then (L:ℂ) else 0 := by
    have prod (u : ZMod L) : conj (K r u)*K s u = ZMod.stdAddChar ((r-s)*u) := by
      change conj (ZMod.stdAddChar (-u*r)) * ZMod.stdAddChar (-u*s) = _
      rw [conjPhase,←AddChar.map_add_eq_mul]
      exact congrArg ZMod.stdAddChar (by ring)
    simp_rw [prod]
    by_cases h : r=s
    · simp [h]
    · rw [ite_eq_right h]
      exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar L (sub_ne_zero.mpr h))
  have energy := GoldbachGRHWindow.norm_energy_of_columns K (fun _ => (L:ℝ)) (by simpa only [Complex.ofReal_natCast] using cols) (fun r => χ r)
  change (∑ u : ZMod L, ‖∑ r : ZMod L, χ r*K r u‖^2) ≤ _
  rw [energy,←mul_sum]
  have h : (∑ r : ZMod L, ‖χ r‖^2) ≤ (L:ℝ) := calc
    _ ≤ ∑ _r : ZMod L, (1:ℝ)^2 := sum_le_sum (fun r _ => pow_le_pow_left₀ (norm_nonneg _) (χ.norm_le_one r) 2)
    _ = _ := by simp
  exact (mul_le_mul_of_nonneg_left h (Nat.cast_nonneg L)).trans_eq (sq _).symm

/-- Twice the absolute least-denominator Fourier coefficient. This is a
periodic majorant for the ratio to the ordinary singular series at positive even targets. -/
def relativeMajorant {L : ℕ} [NeZero L] (A B : DirichletCharacter ℂ L) (u : ZMod L) : ℝ :=
  2*‖gaussSum A ZMod.stdAddChar * gaussSum B ZMod.stdAddChar *
    gaussSum (A*B)⁻¹ (ZMod.stdAddChar.mulShift (-u))/(L.totient:ℂ)^2‖

theorem relativeMajorant_energy {L : ℕ} [NeZero L] (A B : DirichletCharacter ℂ L) :
    (∑ u : ZMod L, relativeMajorant A B u ^ 2) ≤ 4*((L:ℝ)/L.totient)^4 := by
  let Z := (A*B)⁻¹
  let F := 2*‖gaussSum A ZMod.stdAddChar * gaussSum B ZMod.stdAddChar‖/(L.totient:ℝ)^2
  have point (u : ZMod L) : relativeMajorant A B u ^ 2 = F^2 * ‖gaussSum Z (ZMod.stdAddChar.mulShift (-u))‖^2 := by
    dsimp only [F,relativeMajorant,Z];rw [norm_div,norm_pow,Complex.norm_natCast,norm_mul];ring
  have amp (χ : DirichletCharacter ℂ L) : ‖gaussSum χ ZMod.stdAddChar‖ ≤ Real.sqrt L :=
    (B13BilateralVaughanReductionProof.DyadicMixedB4CharacterFactorBound.norm_dirichlet_gauss_standard χ).trans
      (Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_of_dvd (NeZero.pos L) χ.conductor_dvd_level))
  have fbound : F ≤ 2*(L:ℝ)/(L.totient:ℝ)^2 := by
    apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 2)
    rw [norm_mul]
    exact (mul_le_mul (amp A) (amp B) (norm_nonneg _) (Real.sqrt_nonneg _)).trans_eq (Real.mul_self_sqrt (Nat.cast_nonneg L))
  have f0 : 0 ≤ F := by dsimp only [F];positivity
  simp_rw [point]
  rw [←mul_sum]
  apply (mul_le_mul (pow_le_pow_left₀ f0 fbound 2) (gauss_target_energy Z) (sum_nonneg (fun _ _ => sq_nonneg _)) (sq_nonneg _)).trans_eq
  ring

/-- The normalized infinite singular series is pointwise dominated by a single
periodic function at the *least* common conductor. -/
theorem series_le_relativeMajorant {r s : ℕ} [NeZero r] [NeZero s] {α : DirichletCharacter ℂ r}
    {β : DirichletCharacter ℂ s} (hα : α.IsPrimitive) (hβ : β.IsPrimitive) (n : ℕ) (hn : 0 < n) (he : Even n) :
    let L := Nat.lcm r s
    let _ : NeZero L := ⟨(Nat.lcm_pos (NeZero.pos r) (NeZero.pos s)).ne'⟩
    ‖series α β n / series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) n‖ ≤
      relativeMajorant (changeLevel (Nat.dvd_lcm_left r s) α) (changeLevel (Nat.dvd_lcm_right r s) β) (n:ZMod L) := by
  intro L inst
  let _ : NeZero L := inst
  let A := changeLevel (Nat.dvd_lcm_left r s) α
  let B := changeLevel (Nat.dvd_lcm_right r s) β
  let R := series α β n / series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) n
  have h := TwistedGoldbachCoefficientProduct.partial_sums hα hβ (Nat.dvd_lcm_left r s) (Nat.dvd_lcm_right r s) n hn he
  rw [sum_eq_single_of_mem L (Nat.mem_divisors_self L (NeZero.ne L))] at h
  · have point : ‖coefficient α β n L‖ = ‖R‖ * |ordinaryWeight L n| := by
      rw [h,norm_mul,Complex.norm_real,Real.norm_eq_abs]
    have low : 1/2 ≤ ordinaryWeight L n := by
      apply le_trans _ (uniform_weight L n he);split <;> norm_num
    have low' : (1/2:ℝ) ≤ |ordinaryWeight L n| := low.trans (le_abs_self _)
    have cmp := (mul_le_mul_of_nonneg_left low' (norm_nonneg R)).trans_eq point.symm
    change ‖R‖ ≤ relativeMajorant A B (n:ZMod L)
    have eqnorm : relativeMajorant A B (n:ZMod L) = 2*‖coefficient α β n L‖ := by
      have div : r ∣ L ∧ s ∣ L := ⟨Nat.dvd_lcm_left ..,Nat.dvd_lcm_right ..⟩
      simp only [relativeMajorant,coefficient,dite_eq_left (NeZero.ne L),dite_eq_left div,gaussCoefficient,A,B]
      rfl
    rw [eqnorm];linarith only [cmp]
  · intro d hd ne
    apply TwistedGoldbachCoefficientProduct.off_level
    intro div
    exact ne (Nat.dvd_antisymm (Nat.dvd_of_mem_divisors hd) div)

end Conjectures.Goldbach.TwistedGoldbachPairMean
end
end

section
open Complex Finset DirichletCharacter
noncomputable section
namespace Conjectures.Goldbach.TwistedGoldbachPairMean
open TwistedGoldbachLocalProduct

private theorem periodic_energy {L : ℕ} [NeZero L] (f : ZMod L → ℝ) (X : ℕ) :
    (∑ n ∈ range (X+1), f n ^ 2) ≤ ((X:ℝ)/L+1)*(∑ u : ZMod L, f u ^ 2) := by
  let B := X/L+1
  have cover : X+1 ≤ L*B := by
    have h := (Nat.div_lt_iff_lt_mul (NeZero.pos L)).mp (Nat.lt_succ_self (X/L))
    simpa only [B,Nat.mul_comm (X/L+1) L,Nat.succ_eq_add_one] using Nat.succ_le_of_lt h
  calc
    _ ≤ ∑ n ∈ range (L*B), f n ^ 2 := sum_le_sum_of_subset_of_nonneg (range_mono cover) (fun _ _ _ => sq_nonneg _)
    _ = (B:ℝ)*(∑ u : ZMod L, f u ^ 2) := by
      rw [B13BilateralVaughanReductionProof.DyadicMixedB4GaussLift.sum_range_blocks]
      simp only [Nat.cast_add,Nat.cast_mul,ZMod.natCast_self,zero_mul,zero_add,sum_const,card_range,nsmul_eq_mul]
      exact congrArg ((B:ℝ)*·) (B13BilateralVaughanReductionProof.DyadicMixedB4DualCharacter.sum_natCast_range_eq_zmod (fun u : ZMod L => f u ^ 2))
    _ ≤ _ := mul_le_mul_of_nonneg_right (by simpa only [B,Nat.cast_add,Nat.cast_one] using
      (add_le_add_left (Nat.cast_div_le (α := ℝ) (m := X) (n := L)) 1)) (sum_nonneg (fun _ _ => sq_nonneg _))

def largePairTargets {r s : ℕ} (α : DirichletCharacter ℂ r) (β : DirichletCharacter ℂ s) (X : ℕ) (η : ℝ) : Finset ℕ := by
  classical
  exact (range (X+1)).filter (fun n => 0 < n ∧ Even n ∧
    η ≤ ‖series α β n / series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) n‖)

/-- For a fixed pair, a singular series comparable to the ordinary one can
occur on only a small number of targets per least-conductor period. -/
theorem largePairTargets_card {r s : ℕ} [NeZero r] [NeZero s] {α : DirichletCharacter ℂ r}
    {β : DirichletCharacter ℂ s} (hα : α.IsPrimitive) (hβ : β.IsPrimitive) (X : ℕ) (η : ℝ) (hη : 0 < η) :
    let L := Nat.lcm r s
    ((largePairTargets α β X η).card:ℝ)*η^2 ≤ ((X:ℝ)/L+1)*(4*((L:ℝ)/L.totient)^4) := by
  classical
  intro L
  let _ : NeZero L := ⟨(Nat.lcm_pos (NeZero.pos r) (NeZero.pos s)).ne'⟩
  let A := changeLevel (Nat.dvd_lcm_left r s) α
  let B := changeLevel (Nat.dvd_lcm_right r s) β
  let D := largePairTargets α β X η
  calc
    _ = ∑ _n ∈ D, η^2 := by rw [sum_const,nsmul_eq_mul]
    _ ≤ ∑ n ∈ D, relativeMajorant A B (n:ZMod L)^2 := by
      apply sum_le_sum
      intro n hn
      obtain ⟨_,hn,he,big⟩ := mem_filter.mp hn
      exact pow_le_pow_left₀ hη.le (big.trans (series_le_relativeMajorant hα hβ n hn he)) 2
    _ ≤ ∑ n ∈ range (X+1), relativeMajorant A B (n:ZMod L)^2 :=
      sum_le_sum_of_subset_of_nonneg (filter_subset ..) (fun _ _ _ => sq_nonneg _)
    _ ≤ _ := (periodic_energy (relativeMajorant A B) X).trans
      (mul_le_mul_of_nonneg_left (relativeMajorant_energy A B) (by positivity))

/-- A least common conductor at least X^a costs at most O(X^(1-a+ε))
exceptional targets, uniformly in both primitive characters. -/
theorem largePairTargets_power (a ε η : ℝ) (hε : 0 < ε) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X r s : ℕ) [NeZero r] [NeZero s] (α : DirichletCharacter ℂ r) (β : DirichletCharacter ℂ s),
      α.IsPrimitive → β.IsPrimitive → 0 < X → (X:ℝ)^a ≤ Nat.lcm r s → Nat.lcm r s ≤ X →
        ((largePairTargets α β X η).card:ℝ) ≤ C*(X:ℝ)^(1-a+ε) := by
  let M := 8+4/(ε/4)
  have hm : 0 < M := by dsimp only [M];positivity
  refine ⟨8*M^4/η^2,by positivity,?_⟩
  intro X r s _ _ α β hα hβ hX low high
  let L := Nat.lcm r s
  have l0 : 0 < L := Nat.lcm_pos (NeZero.pos r) (NeZero.pos s)
  have lpos : 0 < (L:ℝ) := Nat.cast_pos.mpr l0
  have x0 : 0 < (X:ℝ) := Nat.cast_pos.mpr hX
  have lx : (L:ℝ) ≤ X := Nat.cast_le.mpr high
  have block : (X:ℝ)/L + 1 ≤ 2*(X:ℝ)^(1-a) := calc
    _ ≤ (X:ℝ)/L + X/L := add_le_add_right ((one_le_div lpos).mpr lx) _
    _ ≤ 2*((X:ℝ)/(X:ℝ)^a) := by
      have h := div_le_div_of_nonneg_left x0.le (Real.rpow_pos_of_pos x0 a) low
      linarith only [h]
    _ = _ := by rw [Real.rpow_sub x0,Real.rpow_one]
  have phi : (L:ℝ)/L.totient ≤ M*(X:ℝ)^(ε/4) :=
    (DeepThreeQuarters.totient_ratio_le_rpow (show 0 < ε/4 by positivity) L l0).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow lpos.le lx (by positivity)) hm.le)
  have four : ((L:ℝ)/L.totient)^4 ≤ M^4*(X:ℝ)^ε := by
    apply (pow_le_pow_left₀ (by positivity) phi 4).trans_eq
    rw [mul_pow,←Real.rpow_mul_natCast x0.le];congr 2;ring
  have combined := (largePairTargets_card hα hβ X η hη).trans
    (mul_le_mul block (mul_le_mul_of_nonneg_left four (by norm_num : (0:ℝ) ≤ 4)) (by positivity) (by positivity))
  calc
    _ ≤ (2*(X:ℝ)^(1-a)*(4*(M^4*(X:ℝ)^ε)))/η^2 := (le_div_iff₀ (sq_pos_of_pos hη)).mpr combined
    _ = _ := by rw [Real.rpow_add x0];ring

end Conjectures.Goldbach.TwistedGoldbachPairMean
end
end

section
open Complex Finset DirichletCharacter
noncomputable section
namespace Conjectures.Goldbach.TwistedGoldbachPairMean
open TwistedGoldbachSingularSeries TwistedGoldbachMixedPrincipal B13BilateralVaughanReductionProof

/-- Additive order of the target reduced modulo the least common conductor. -/
def targetOrder (L n : ℕ) := L / n.gcd L

private theorem order_data {L : ℕ} [NeZero L] (n : ℕ) :
    0 < targetOrder L n ∧ targetOrder L n ∣ L ∧
      L/(targetOrder L n)*(n/(n.gcd L)) = n ∧ (n/(n.gcd L)).Coprime (targetOrder L n) := by
  let g := n.gcd L
  let R := targetOrder L n
  have gd : g ∣ L := Nat.gcd_dvd_right ..
  have pos := Nat.div_pos (Nat.le_of_dvd (NeZero.pos L) gd) (Nat.gcd_pos_of_pos_right n (NeZero.pos L))
  have rg : R*g = L := Nat.div_mul_cancel gd
  have quotient : L/R = g := (congrArg (·/R) rg.symm).trans (Nat.mul_div_cancel_left g (show 0 < R from pos))
  exact ⟨pos,Nat.div_dvd_of_dvd gd,by change L/R*(n/g)=n; rw [quotient,Nat.mul_div_cancel' (Nat.gcd_dvd_left ..)],
    Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_right n (NeZero.pos L))⟩

/-- Descent to the denominator of the target frequency enforces divisibility
by the product conductor and bounds the surviving Gauss sum sharply. -/
private theorem target_gauss_bound {L : ℕ} [NeZero L] (χ : DirichletCharacter ℂ L) (n : ℕ) :
    let R := targetOrder L n
    ‖gaussSum χ (ZMod.stdAddChar.mulShift (-(n:ZMod L)))‖/(L.totient:ℝ) ≤
      if χ.conductor ∣ R then Real.sqrt R / R.totient else 0 := by
  classical
  intro R
  obtain ⟨pos,div,nrepr,cop⟩ := order_data (L := L) n
  let _ : NeZero R := ⟨pos.ne'⟩
  let k := n/(n.gcd L)
  have bound : ‖gaussSum χ (ZMod.stdAddChar.mulShift (-(n:ZMod L)))‖/(L.totient:ℝ) ≤ ‖amplitude χ n‖ := by
    rw [amplitude,norm_div,Complex.norm_natCast]
    exact div_le_div_of_nonneg_right (DyadicMixedB4CharacterFactorBound.norm_gauss_neg_shift_le χ (n:ZMod L)) (Nat.cast_nonneg _)
  apply bound.trans
  have eqn := amplitude_at_divisor div χ k
  change L/R*k=n at nrepr
  rw [nrepr] at eqn
  rw [eqn]
  split_ifs with h cd cd
  · let θ : DirichletCharacter ℂ R := h.χ₀
    have gauss : gaussSum θ (ZMod.stdAddChar.mulShift (k:ZMod R)) = θ⁻¹ (k:ZMod R)*gaussSum θ ZMod.stdAddChar :=
      gaussSum_mulShift_eq θ ZMod.stdAddChar (ZMod.unitOfCoprime k cop)
    change ‖amplitude θ k‖ ≤ _
    rw [amplitude,norm_div,Complex.norm_natCast,gauss,norm_mul]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    have g : ‖gaussSum θ ZMod.stdAddChar‖ ≤ Real.sqrt R := (DyadicMixedB4CharacterFactorBound.norm_dirichlet_gauss_standard θ).trans
      (Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_of_dvd pos θ.conductor_dvd_level))
    exact (mul_le_mul (θ⁻¹.norm_le_one _) g (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  · exact (cd (conductor_dvd_of_mem_conductorSet χ h)).elim
  · simp only [norm_zero];positivity
  · simp only [norm_zero,le_refl]

private theorem phi_prod (q : ℕ) (hq : 0 < q) :
    (q:ℝ)/q.totient = ∏ p ∈ q.primeFactors, (p:ℝ)/((p:ℝ)-1) := by
  have nz : (∏ p ∈ q.primeFactors, ((p:ℝ)-1)) ≠ 0 := by
    apply ne_of_gt;apply prod_pos;intro p h
    exact sub_pos.mpr (by exact_mod_cast (Nat.prime_of_mem_primeFactors h).one_lt)
  have φ : (q.totient:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr hq).ne'
  have id := congrArg (fun v : ℕ => (v:ℝ)) (Nat.totient_mul_prod_primeFactors q)
  simp only [Nat.cast_mul,Nat.cast_prod] at id
  have prod : (∏ p ∈ q.primeFactors, ((p-1:ℕ):ℝ)) = ∏ p ∈ q.primeFactors, ((p:ℝ)-1) := by
    apply prod_congr rfl
    intro p hp
    rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_le,Nat.cast_one]
  rw [prod] at id
  rw [prod_div_distrib,div_eq_div_iff φ nz];linarith only [id]

/-- The local factors at primes dividing the target exactly absorb the
ordinary totient loss. Only primes of the reduced target order remain. -/
theorem phi_relative_weight {L : ℕ} [NeZero L] (n : ℕ) (he : Even n) :
    let R := targetOrder L n
    (L:ℝ)/L.totient ≤ ordinaryWeight L n * ((R:ℝ)/R.totient)^2 := by
  classical
  intro R
  obtain ⟨r0,rl,_,_⟩ := order_data (L := L) n
  let F (p : ℕ) : ℝ := (p:ℝ)/((p:ℝ)-1)
  let V (p : ℕ) := if p ∈ R.primeFactors then F p ^ 2 else 1
  have pos (p : ℕ) (hp : p.Prime) : 0 < (p:ℝ)-1 := sub_pos.mpr (by exact_mod_cast hp.one_lt)
  have one (p : ℕ) (hp : p.Prime) : 1 ≤ F p := (one_le_div (pos p hp)).mpr (sub_le_self _ zero_le_one)
  have step (p : ℕ) (hp : p ∈ L.primeFactors) : F p ≤ localWeight n p * V p := by
    have pr := Nat.prime_of_mem_primeFactors hp
    by_cases hn : p ∣ n
    · have v : 1 ≤ V p := by
        dsimp only [V];split_ifs
        · exact one_le_pow₀ (one p pr)
        · rfl
      have eqn : localWeight n p = F p := by simp only [localWeight,ite_eq_left hn,F]
      rw [eqn];simpa only [mul_one] using mul_le_mul_of_nonneg_left v (zero_le_one.trans (one p pr))
    · have hR : p ∣ R := by
        have d := Nat.dvd_of_mem_primeFactors hp
        have rg : R*n.gcd L=L := Nat.div_mul_cancel (Nat.gcd_dvd_right ..)
        rw [←rg] at d
        exact (pr.dvd_mul.mp d).resolve_right (fun e => hn (e.trans (Nat.gcd_dvd_left ..)))
      have mem : p ∈ R.primeFactors := Nat.mem_primeFactors.mpr ⟨pr,hR,r0.ne'⟩
      have p3 : 3 ≤ p := by
        have h2 : p ≠ 2 := fun e => hn (e ▸ even_iff_two_dvd.mp he)
        have := pr.two_le
        omega
      have pp : (3:ℝ) ≤ p := by exact_mod_cast p3
      rw [show V p = F p^2 from ite_eq_left mem,localWeight,ite_eq_right hn]
      dsimp only [F]
      field_simp [show (0:ℝ)<(p:ℝ)-1 from pos p pr]
      nlinarith only [mul_nonneg (by positivity : 0 ≤ (p:ℝ)) (by linarith only [pp] : 0 ≤ (p:ℝ)-3)]
  have subset : R.primeFactors ⊆ L.primeFactors := Nat.primeFactors_mono rl (NeZero.ne L)
  have prodV : (∏ p ∈ L.primeFactors, V p) = (∏ p ∈ R.primeFactors, F p)^2 := by
    simp only [V,prod_ite_mem,inter_eq_right.mpr subset,prod_pow]
  rw [phi_prod L (NeZero.pos L),ordinary_product,phi_prod R r0,←prodV,←prod_mul_distrib]
  exact prod_le_prod₀ (fun p hp => zero_le_one.trans (one p (Nat.prime_of_mem_primeFactors hp))) step

end Conjectures.Goldbach.TwistedGoldbachPairMean
end
end

section
open Complex Finset DirichletCharacter
noncomputable section
namespace Conjectures.Goldbach.TwistedGoldbachPairMean
open TwistedGoldbachSingularSeries TwistedGoldbachMixedPrincipal TwistedGoldbachLocalProduct B13BilateralVaughanReductionProof

/-- Conductor of the product after the two primitive source characters have
been lifted to their least common level. -/
def jointConductor {r s : ℕ} (α : DirichletCharacter ℂ r) (β : DirichletCharacter ℂ s) :=
  (changeLevel (Nat.dvd_lcm_left r s) α * changeLevel (Nat.dvd_lcm_right r s) β).conductor

/-- Uniform decay with the additive order of the target. The conductor of
the product of the two lifted characters must divide this order for the
infinite singular series to contribute. -/
theorem relative_order_bound {r s : ℕ} [NeZero r] [NeZero s] {α : DirichletCharacter ℂ r}
    {β : DirichletCharacter ℂ s} (hα : α.IsPrimitive) (hβ : β.IsPrimitive) (n : ℕ) (hn : 0 < n) (he : Even n) :
    let R := targetOrder (Nat.lcm r s) n
    ‖series α β n / series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) n‖ ≤
      if jointConductor α β ∣ R then ((R:ℝ)/R.totient)^3 * (R:ℝ)^(-(1/2:ℝ)) else 0 := by
  intro R
  let L := Nat.lcm r s
  let _ : NeZero L := ⟨(Nat.lcm_pos (NeZero.pos r) (NeZero.pos s)).ne'⟩
  let A := changeLevel (Nat.dvd_lcm_left r s) α
  let B := changeLevel (Nat.dvd_lcm_right r s) β
  let Z := (A*B)⁻¹
  let F := (R:ℝ)/R.totient
  let rel := series α β n / series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) n
  let W := ordinaryWeight L n
  have r0 : 0 < R := (order_data (L := L) n).1
  have rp : 0 < (R:ℝ) := Nat.cast_pos.mpr r0
  have φL : 0 < (L.totient:ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr (NeZero.pos L))
  have w0 : 0 < W := by
    apply lt_of_lt_of_le _ (uniform_weight L n he);split <;> norm_num
  have id := TwistedGoldbachCoefficientProduct.partial_sums hα hβ (Nat.dvd_lcm_left r s) (Nat.dvd_lcm_right r s) n hn he
  rw [sum_eq_single_of_mem L (Nat.mem_divisors_self L (NeZero.ne L))] at id
  rotate_left
  · intro d hd hne
    apply TwistedGoldbachCoefficientProduct.off_level;intro dv
    exact hne (Nat.dvd_antisymm (Nat.dvd_of_mem_divisors hd) dv)
  have absid : ‖rel‖*W = ‖coefficient α β n L‖ := by
    rw [id,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg w0.le]
  let G := ‖gaussSum Z (ZMod.stdAddChar.mulShift (-(n:ZMod L)))‖/(L.totient:ℝ)
  have product : ‖coefficient α β n L‖ =
      (‖gaussSum A ZMod.stdAddChar * gaussSum B ZMod.stdAddChar‖/(L.totient:ℝ))*G := by
    have div : r ∣ L ∧ s ∣ L := ⟨Nat.dvd_lcm_left ..,Nat.dvd_lcm_right ..⟩
    simp only [coefficient,dite_eq_left (NeZero.ne L),dite_eq_left div,gaussCoefficient,norm_div,norm_pow,Complex.norm_natCast]
    change ‖(gaussSum A ZMod.stdAddChar * gaussSum B ZMod.stdAddChar)*_‖ / (L.totient:ℝ)^2 = _
    rw [norm_mul];dsimp only [G,Z];ring
  have amp (χ : DirichletCharacter ℂ L) : ‖gaussSum χ ZMod.stdAddChar‖ ≤ Real.sqrt L :=
    (DyadicMixedB4CharacterFactorBound.norm_dirichlet_gauss_standard χ).trans
      (Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_of_dvd (NeZero.pos L) χ.conductor_dvd_level))
  have pair : ‖gaussSum A ZMod.stdAddChar * gaussSum B ZMod.stdAddChar‖/(L.totient:ℝ) ≤ (L:ℝ)/L.totient := by
    apply div_le_div_of_nonneg_right _ φL.le;rw [norm_mul]
    exact (mul_le_mul (amp A) (amp B) (norm_nonneg _) (Real.sqrt_nonneg _)).trans_eq (Real.mul_self_sqrt (Nat.cast_nonneg L))
  have gauss := target_gauss_bound Z n
  have joint : Z.conductor = jointConductor α β := conductor_inv _
  change G ≤ if Z.conductor ∣ R then Real.sqrt R / R.totient else 0 at gauss
  rw [joint] at gauss
  have major := (absid.trans product).le.trans (mul_le_mul pair gauss (by dsimp only [G];positivity) (div_nonneg (Nat.cast_nonneg _) φL.le))
  by_cases hd : jointConductor α β ∣ R
  · rw [ite_eq_left hd] at major ⊢
    have phi := phi_relative_weight (L := L) n he
    have mult := major.trans (mul_le_mul_of_nonneg_right phi (by positivity : 0 ≤ Real.sqrt R/(R.totient:ℝ)))
    have final : F^2*(Real.sqrt R/(R.totient:ℝ)) = F^3*(R:ℝ)^(-(1/2:ℝ)) := by
      rw [Real.rpow_neg rp.le,←Real.sqrt_eq_rpow]
      dsimp only [F]
      field_simp [Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr r0).ne',(Real.sqrt_pos.mpr rp).ne']
      nlinarith only [Real.sq_sqrt rp.le]
    apply le_of_mul_le_mul_right _ w0
    calc
      _ ≤ (W*F^2)*(Real.sqrt R/(R.totient:ℝ)) := mult
      _ = W*(F^2*(Real.sqrt R/(R.totient:ℝ))) := mul_assoc ..
      _ = _ := by rw [final,mul_comm]
  · rw [ite_eq_right hd,mul_zero] at major
    rw [ite_eq_right hd]
    exact le_of_mul_le_mul_right (major.trans_eq (zero_mul W).symm) w0

/-- A fixed constant controls the full singular-series ratio by the inverse
fourth root of the reduced target order, for every pair and every even target. -/
theorem relative_order_decay {r s : ℕ} [NeZero r] [NeZero s] {α : DirichletCharacter ℂ r}
    {β : DirichletCharacter ℂ s} (hα : α.IsPrimitive) (hβ : β.IsPrimitive) (n : ℕ) (hn : 0 < n) (he : Even n) :
    let R := targetOrder (Nat.lcm r s) n
    ‖series α β n / series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) n‖ ≤
      if jointConductor α β ∣ R then 56^3 * (R:ℝ)^(-(1/4:ℝ)) else 0 := by
  intro R
  let _ : NeZero (Nat.lcm r s) := ⟨(Nat.lcm_pos (NeZero.pos r) (NeZero.pos s)).ne'⟩
  have pos : 0 < R := (order_data (L := Nat.lcm r s) n).1
  have rp : 0 < (R:ℝ) := Nat.cast_pos.mpr pos
  have h := DeepThreeQuarters.totient_ratio_le_rpow (show (0:ℝ) < 1/12 by norm_num) R pos
  norm_num at h
  apply (relative_order_bound hα hβ n hn he).trans
  change (if jointConductor α β ∣ R then _ else (0:ℝ)) ≤ _
  split_ifs with hd
  · apply (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) h 3) (Real.rpow_nonneg rp.le _)).trans_eq
    rw [mul_pow,←Real.rpow_mul_natCast rp.le,mul_assoc,←Real.rpow_add rp]
    norm_num
  · rfl

end Conjectures.Goldbach.TwistedGoldbachPairMean
end
end

section
open Complex Finset Filter DirichletCharacter Goldbach GoldbachTwistedMellin
noncomputable section
namespace Conjectures.Goldbach.TwistedGoldbachPairMean
open TwistedGoldbachLocalProduct

/-- The same fixed multiplier works for all pairs and targets. A correction
of a prescribed relative size forces both the least common level to divide
K times the target and the product conductor to divide K. -/
theorem large_series_forces_levels (η : ℝ) (hη : 0 < η) :
    ∃ K : ℕ, 0 < K ∧ ∀ (r s : ℕ) [NeZero r] [NeZero s] (α : DirichletCharacter ℂ r)
      (β : DirichletCharacter ℂ s), α.IsPrimitive → β.IsPrimitive → ∀ n : ℕ, 0 < n → Even n →
      η ≤ ‖series α β n / series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) n‖ →
        Nat.lcm r s ∣ K*n ∧ jointConductor α β ∣ K := by
  let A : ℝ := 56^3
  let M := ⌈(A/η)^4⌉₊
  refine ⟨M.factorial,Nat.factorial_pos _,?_⟩
  intro r s _ _ α β hα hβ n hn he big
  let L := Nat.lcm r s
  let R := targetOrder L n
  have lpos : 0 < L := Nat.lcm_pos (NeZero.pos r) (NeZero.pos s)
  have gpos := Nat.gcd_pos_of_pos_right n lpos
  have rpos : 0 < R := Nat.div_pos (Nat.le_of_dvd lpos (Nat.gcd_dvd_right ..)) gpos
  have rp : 0 < (R:ℝ) := Nat.cast_pos.mpr rpos
  have bd := big.trans (relative_order_decay hα hβ n hn he)
  change η ≤ if jointConductor α β ∣ R then A*(R:ℝ)^(-(1/4:ℝ)) else 0 at bd
  split_ifs at bd with div
  · rw [Real.rpow_neg rp.le,←div_eq_mul_inv] at bd
    have width : (R:ℝ)^(1/4:ℝ) ≤ A/η := (le_div_iff₀ hη).mpr
      ((mul_comm _ _).trans_le ((le_div_iff₀ (Real.rpow_pos_of_pos rp _)).mp bd))
    have raised := pow_le_pow_left₀ (Real.rpow_nonneg rp.le _) width 4
    rw [←Real.rpow_mul_natCast rp.le,show (1/4:ℝ)*(4:ℕ) = 1 by norm_num,Real.rpow_one] at raised
    have rM : R ≤ M := Nat.cast_le.mp (raised.trans (Nat.le_ceil _))
    have rK := Nat.dvd_factorial rpos rM
    have base : R*n.gcd L = L := Nat.div_mul_cancel (Nat.gcd_dvd_right ..)
    have both : R*n.gcd L ∣ M.factorial*n := Nat.mul_dvd_mul rK (Nat.gcd_dvd_left ..)
    rw [base] at both
    exact ⟨both,div.trans rK⟩
  · exact (hη.not_ge bd).elim

end Conjectures.Goldbach.TwistedGoldbachPairMean

namespace Conjectures.Goldbach.BinaryShiftZeroDensity
open TwistedGoldbachPairMean TwistedGoldbachLocalProduct

/-- Portion of the zero-pair term supported on levels dividing K*n and on
pairs whose product character has conductor dividing the fixed integer K. -/
def relatedBetaTerm (K n : ℕ) (v w : CatalogueEntry) : ℂ :=
  if Nat.lcm (catalogueLevel v) (catalogueLevel w) ∣ K*n ∧
    jointConductor (catalogueCharacter v)⁻¹ (catalogueCharacter w)⁻¹ ∣ K then
    catalogueBetaTerm n v w else 0

/-- Every bounded-height near-one zero pair failing either arithmetic
condition can be discarded. Their combined effect is at most ε times the
ordinary main term, uniformly in the common major-arc width. -/
theorem nearOne_unrelated_pairs_small (H T ε : ℝ) (hH : 0 ≤ H) (hT : 0 ≤ T) (hε : 0 < ε) :
    ∃ K : ℕ, 0 < K ∧ ∀ᶠ Q : ℕ in atTop, ∀ m X : ℕ, Q ≤ X →
      let Z := (nearOneCatalogue m Q X H T).erase none
      ∀ (n : ℕ) (P : ℝ), 0 < n → Even n →
      let S := series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) n
      ‖cataloguePairSum Z P (catalogueBetaTerm n)-cataloguePairSum Z P (relatedBetaTerm K n)‖ ≤ S.re*((n:ℝ)*ε) := by
  classical
  obtain ⟨D,hD,total⟩ := nearOne_zero_multiplicity_bounded H T hH hT
  let B := 1+‖Complex.betaIntegral (5/8:ℂ) (5/8:ℂ)‖
  have b0 : 0 < B := by dsimp only [B];positivity
  let η := ε/((1+D)^2*B)
  have hη : 0 < η := by dsimp only [η];positivity
  obtain ⟨K,hK,force⟩ := large_series_forces_levels η hη
  refine ⟨K,hK,?_⟩
  filter_upwards [total] with Q mass
  intro m X hQ Z n P hn he S
  have unit : 1 ≤ S.re := TwistedGoldbachMixedPrincipal.ordinary_at_least_one n hn he
  have sn : ‖S‖ ≤ S.re := TwistedGoldbachSingularSeries.infinite_domination isPrimitive_one_level_one isPrimitive_one_level_one n hn
  have nz : S ≠ 0 := fun eqn => by rw [eqn,Complex.zero_re] at unit;norm_num at unit
  have hpos : 0 ≤ S.re := zero_le_one.trans unit
  have nn : 1 ≤ (n:ℝ) := by exact_mod_cast hn
  have factor : 0 ≤ (η*S.re)*((n:ℝ)*B) := by positivity
  have point (i : CatalogueEntry) (hi : i ∈ Z) (j : CatalogueEntry) (hj : j ∈ Z)
      (_ : (Nat.lcm (catalogueLevel i) (catalogueLevel j):ℝ) ≤ P) :
      ‖catalogueBetaTerm n i j-relatedBetaTerm K n i j‖ ≤ (η*S.re)*((n:ℝ)*B) := by
    unfold relatedBetaTerm
    split_ifs with keep
    · simpa only [sub_self,norm_zero] using factor
    rw [sub_zero]
    have pi := (catalogue_properties m Q X H T hT i (mem_of_mem_erase hi)).2
    have pj := (catalogue_properties m Q X H T hT j (mem_of_mem_erase hj)).2
    let α := (catalogueCharacter i)⁻¹
    let β := (catalogueCharacter j)⁻¹
    have small : ‖series α β n / S‖ < η := lt_of_not_ge (fun h => keep (force _ _ α β pi.1.inv pj.1.inv n hn he h))
    have ser : ‖series α β n‖ ≤ η*S.re := calc
      _ = ‖series α β n / S‖*‖S‖ := by rw [←norm_mul,div_mul_cancel₀ _ nz]
      _ ≤ _ := mul_le_mul small.le sn (norm_nonneg _) hη.le
    let s := (catalogueRoot i).getD 1
    let t := (catalogueRoot j).getD 1
    have pow : ‖(n:ℂ)^(s+t-1)‖ ≤ n := by
      rw [norm_natCast_cpow_of_pos hn,sub_re,add_re,one_re]
      have ls : s.re ≤ 1 := pi.2.2.1
      have lt : t.re ≤ 1 := pj.2.2.1
      simpa using Real.rpow_le_rpow_of_exponent_le nn (show s.re+t.re-1 ≤ 1 by linarith only [ls,lt])
    have beta : ‖Complex.betaIntegral s t‖ ≤ B := by
      apply (BinaryShiftCircle.norm_betaIntegral_le_diagonal (by norm_num : 0 < (5/8:ℝ)) pi.2.1 pj.2.1).trans
      change ‖Complex.betaIntegral ((5/8:ℝ):ℂ) ((5/8:ℝ):ℂ)‖ ≤ 1+‖Complex.betaIntegral (5/8:ℂ) (5/8:ℂ)‖
      push_cast;linarith
    change ‖series α β n*((n:ℂ)^(s+t-1)*Complex.betaIntegral s t)‖ ≤ _
    rw [norm_mul,norm_mul]
    exact mul_le_mul ser (mul_le_mul pow beta (norm_nonneg _) (Nat.cast_nonneg _)) (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (mul_nonneg hη.le hpos)
  have weight : (∑ v ∈ Z, ‖catalogueWeight v‖) ≤ 1+D := calc
    _ ≤ ∑ v ∈ nearOneCatalogue m Q X H T, ‖catalogueWeight v‖ :=
      sum_le_sum_of_subset_of_nonneg (erase_subset ..) (fun _ _ _ => norm_nonneg _)
    _ ≤ _ := by rw [catalogue_mass];exact add_le_add_right (mass m X hQ) 1
  apply (catalogue_pair_sum_error Z P _ factor _ _ point).trans
  apply (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (sum_nonneg (fun _ _ => norm_nonneg _)) weight 2) factor).trans_eq
  dsimp only [η]
  field_simp [b0.ne',show 1+D ≠ 0 by positivity]

end Conjectures.Goldbach.BinaryShiftZeroDensity
end
end

section
open Complex Finset Filter DirichletCharacter Goldbach GoldbachTwistedMellin
open scoped Topology
noncomputable section
namespace Conjectures.Goldbach.BinaryShiftZeroDensity
open TwistedGoldbachPairMean TwistedGoldbachLocalProduct

/-- On the entire upper half of the target interval the bounded-height near-one
arcs equal the ordinary main term plus the arithmetically retained pairs,
to within an arbitrarily small fixed fraction of the ordinary main term. -/
theorem nearOne_related_formula (H T ε : ℝ) (hH : 0 ≤ H) (hT : 0 ≤ T) (hε : 0 < ε) :
    ∃ K : ℕ, 0 < K ∧ ∀ᶠ Q : ℕ in atTop, ∀ m : ℕ, 2 ≤ m → Q ≤ m+2 →
      let X : ℝ := (m+2:ℕ)
      let Z := nearOneCatalogue m Q (m+2) H T
      ∃ P : ℝ, X^(11/40:ℝ) ≤ P ∧ P ≤ X^(3/10:ℝ) ∧ ∀ n : ℕ, 0 < n → n ≤ m+2 → m+2 ≤ 2*n → Even n →
        let S := series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) n
        ‖cataloguePairSum Z P (catalogueArcTerm m n P) -
          (S*(n:ℂ) + cataloguePairSum (Z.erase none) P (relatedBetaTerm K n))‖ ≤ S.re*((n:ℝ)*ε) := by
  obtain ⟨κ,C,hκ,hC,arc⟩ := nearOneCatalogue_pole_and_zero_pairs H T hH hT
  obtain ⟨K,hK,res⟩ := nearOne_unrelated_pairs_small H T (ε/2) hH hT (by positivity)
  have lim : Tendsto (fun x : ℕ => C*(x:ℝ)^(-κ)) atTop (𝓝 0) := by
    simpa only [Function.comp_apply,mul_zero] using (tendsto_rpow_neg_atTop hκ |>.comp tendsto_natCast_atTop_atTop).const_mul C
  obtain ⟨N,sm⟩ := eventually_atTop.mp (lim.eventually (Iio_mem_nhds (by positivity : (0:ℝ) < ε/4)))
  refine ⟨K,hK,?_⟩
  filter_upwards [arc,res,eventually_ge_atTop N] with Q exactArc rest hN
  intro m hm hQ X Z
  obtain ⟨P,hP,hP',rule⟩ := exactArc m hm hQ
  refine ⟨P,hP,hP',?_⟩
  intro n hn nX xn he S
  have pos : 0 < X := by dsimp only [X];positivity
  have s0 : 0 ≤ S.re := zero_le_one.trans (TwistedGoldbachMixedPrincipal.ordinary_at_least_one n hn he)
  have half : X ≤ 2*(n:ℝ) := by dsimp only [X];exact_mod_cast xn
  have small : C*X^(-κ) ≤ ε/4 := (sm (m+2) (hN.trans hQ)).le
  have power : C*X^(1-κ) ≤ (n:ℝ)*(ε/2) := calc
    _ = X*(C*X^(-κ)) := by rw [sub_eq_add_neg,Real.rpow_add pos,Real.rpow_one];ring
    _ ≤ (2*(n:ℝ))*(ε/4) := mul_le_mul half small (mul_nonneg hC.le (Real.rpow_nonneg pos.le _)) (by positivity)
    _ = _ := by ring
  let U := S*(n:ℂ)+cataloguePairSum (Z.erase none) P (catalogueBetaTerm n)
  have a := (rule n hn nX he).trans (mul_le_mul_of_nonneg_left power s0)
  have b := rest m (m+2) hQ n P hn he
  change ‖cataloguePairSum Z P (catalogueArcTerm m n P)-U‖ ≤ S.re*((n:ℝ)*(ε/2)) at a
  have b' : ‖U-(S*(n:ℂ)+cataloguePairSum (Z.erase none) P (relatedBetaTerm K n))‖ ≤ S.re*((n:ℝ)*(ε/2)) := by
    simpa only [U,add_sub_add_left_eq_sub] using b
  apply (norm_sub_le_norm_sub_add_norm_sub _ U _).trans ((add_le_add a b').trans_eq ?_)
  ring

end Conjectures.Goldbach.BinaryShiftZeroDensity
end
end

section
open Complex Finset DirichletCharacter
open scoped Classical
noncomputable section
namespace Conjectures.Goldbach.TwistedGoldbachPairMean

/-- Small twists at a common positive modulus: the range of the characters
lifted from the greatest common divisor with the fixed multiplier. -/
def lowCharacters (q K : ℕ) : Subgroup (DirichletCharacter ℂ q) :=
  (changeLevel (R := ℂ) (Nat.gcd_dvd_left q K)).range

def classOf (q K : ℕ) : DirichletCharacter ℂ q →* ((DirichletCharacter ℂ q) ⧸ lowCharacters q K) :=
  QuotientGroup.mk' (lowCharacters q K)

private theorem low_iff {q : ℕ} [NeZero q] (K : ℕ) (χ : DirichletCharacter ℂ q) :
    χ ∈ lowCharacters q K ↔ χ.conductor ∣ K := by
  constructor
  · rintro ⟨θ,rfl⟩
    rw [conductor_changeLevel]
    exact θ.conductor_dvd_level.trans (Nat.gcd_dvd_right ..)
  · intro dvd
    have factor : χ.FactorsThrough (q.gcd K) := (χ.mem_conductorSet_iff_conductor_dvd (Nat.gcd_dvd_left ..)).mpr
      (Nat.dvd_gcd χ.conductor_dvd_level dvd)
    exact ⟨factor.χ₀,factor.eq_changeLevel.symm⟩

/-- Two labels at any common modulus give a retained product conductor
exactly when their classes are inverse in the quotient by small twists. -/
theorem inverse_classes_iff {r s q : ℕ} [NeZero q] (K : ℕ) (α : DirichletCharacter ℂ r) (β : DirichletCharacter ℂ s)
    (hr : r ∣ q) (hs : s ∣ q) :
    classOf q K (changeLevel hr α) * classOf q K (changeLevel hs β) = 1 ↔ jointConductor α⁻¹ β⁻¹ ∣ K := by
  rw [←map_mul]
  change QuotientGroup.mk (changeLevel hr α * changeLevel hs β) = (1 : (DirichletCharacter ℂ q) ⧸ lowCharacters q K) ↔ _
  rw [QuotientGroup.eq_one_iff,low_iff]
  let L := Nat.lcm r s
  have lq : L ∣ q := Nat.lcm_dvd hr hs
  have stab : changeLevel lq (changeLevel (Nat.dvd_lcm_left r s) α * changeLevel (Nat.dvd_lcm_right r s) β) =
      changeLevel hr α * changeLevel hs β := by rw [map_mul,←changeLevel_trans,←changeLevel_trans]
  rw [←stab,conductor_changeLevel]
  simp only [jointConductor,map_inv,←mul_inv,conductor_inv]

/-- Energy of the classes that occur, including the inverse classes so
that inversion permutes the indexing finset. -/
def classEnergy {ι G : Type*} [CommGroup G] (Z : Finset ι) (f : ι → G) (w : ι → ℝ) : ℝ := by
  classical
  exact ∑ c ∈ Z.image f ∪ Z.image (fun i => (f i)⁻¹), (∑ i ∈ Z.filter (fun i => f i=c), w i)^2

/-- The total product of weights over inverse-class pairs is controlled by
the sum of squared masses of the individual classes, even when the original
catalogue has different numbers of zeros in the two inverse classes. -/
theorem inverse_pairs_le_classEnergy {ι G : Type*} [CommGroup G]
    (Z : Finset ι) (f : ι → G) (w : ι → ℝ) :
    (∑ i ∈ Z, ∑ j ∈ Z, if f i*f j=1 then w i*w j else 0) ≤ classEnergy Z f w := by
  classical
  let S := Z.image f ∪ Z.image (fun i => (f i)⁻¹)
  let W (c : G) := ∑ i ∈ Z.filter (fun i => f i=c), w i
  have cover (i : ι) (hi : i ∈ Z) : f i ∈ S := mem_union_left _ (mem_image_of_mem _ hi)
  have closed (c : G) (hc : c ∈ S) : c⁻¹ ∈ S := by
    rcases mem_union.mp hc with h|h
    · obtain ⟨i,hi,rfl⟩ := mem_image.mp h;exact mem_union_right _ (mem_image_of_mem _ hi)
    · obtain ⟨i,hi,rfl⟩ := mem_image.mp h;simpa only [inv_inv] using cover i hi
  have invsum : (∑ c ∈ S, W (c⁻¹)^2) = ∑ c ∈ S, W c^2 := by
    apply sum_bij (fun c _ => c⁻¹)
    · exact closed
    · intro i hi j hj h;exact inv_injective h
    · intro i hi;exact ⟨i⁻¹,closed i hi,inv_inv _⟩
    · intros;rfl
  have row (i : ι) : (∑ j ∈ Z, if f i*f j=1 then w i*w j else 0) = w i*W ((f i)⁻¹) := by
    change _ = w i * ∑ j ∈ Z.filter (fun j => f j = (f i)⁻¹), w j
    rw [Finset.mul_sum,Finset.sum_filter]
    apply sum_congr rfl
    intro j _
    have eqn : f i * f j = 1 ↔ f j=(f i)⁻¹ := ⟨eq_inv_of_mul_eq_one_right,fun h => by rw [h,mul_inv_cancel]⟩
    simp only [eqn]
  have group_sum : (∑ i ∈ Z, w i*W ((f i)⁻¹)) = ∑ c ∈ S, W c*W (c⁻¹) := by
    calc
      _ = ∑ c ∈ S, ∑ i ∈ Z.filter (fun i => f i=c), w i*W ((f i)⁻¹) := (sum_fiberwise_of_maps_to cover _).symm
      _ = _ := by
        apply sum_congr rfl;intro c hc
        rw [show W c = ∑ i ∈ Z.filter (fun i => f i=c), w i from rfl,Finset.sum_mul]
        apply sum_congr rfl
        intro i hi
        rw [(mem_filter.mp hi).2]
  simp_rw [row]
  rw [group_sum]
  unfold classEnergy
  change _ ≤ ∑ c ∈ S, W c^2
  have pair := sum_le_sum (s := S) (fun c _ => show 2*(W c * W (c⁻¹)) ≤ W c^2+W (c⁻¹)^2 by nlinarith only [sq_nonneg (W c-W (c⁻¹))])
  rw [←Finset.mul_sum,Finset.sum_add_distrib,invsum] at pair
  linarith only [pair]

end Conjectures.Goldbach.TwistedGoldbachPairMean
end
end

section
open Complex Finset DirichletCharacter
open scoped Classical
noncomputable section
namespace Conjectures.Goldbach.BinaryShiftZeroDensity
open TwistedGoldbachPairMean TwistedGoldbachLocalProduct

def activeEntries (Z : Finset CatalogueEntry) (K n : ℕ) : Finset CatalogueEntry :=
  Z.filter (fun v => catalogueLevel v ∣ K*n)

def catalogueClass (q K : ℕ) (v : CatalogueEntry) := classOf q K (catalogueLift q v)

def zeroWeight (n : ℕ) (v : CatalogueEntry) : ℝ :=
  ‖catalogueWeight v‖ * (n:ℝ)^(((catalogueRoot v).getD 1).re-1)

private theorem related_terms_supported (Z : Finset CatalogueEntry) (K n : ℕ) (P : ℝ) :
    cataloguePairSum Z P (relatedBetaTerm K n) = cataloguePairSum (activeEntries Z K n) P (relatedBetaTerm K n) := by
  classical
  let V := activeEntries Z K n
  let f (i j : CatalogueEntry) := if (Nat.lcm (catalogueLevel i) (catalogueLevel j):ℝ) ≤ P then
    catalogueWeight i*catalogueWeight j*relatedBetaTerm K n i j else 0
  have missing (i : CatalogueEntry) (hi : i ∈ Z) (no : i ∉ V) : ¬catalogueLevel i ∣ K*n :=
    fun dv => no (mem_filter.mpr ⟨hi,dv⟩)
  have zero (i j : CatalogueEntry) (no : ¬Nat.lcm (catalogueLevel i) (catalogueLevel j) ∣ K*n) : f i j=0 := by
    simp only [f,relatedBetaTerm,not_and_of_not_left _ no,ite_false,mul_zero,ite_self]
  change (∑ i ∈ Z, ∑ j ∈ Z, f i j) = ∑ i ∈ V, ∑ j ∈ V, f i j
  calc
    _ = ∑ i ∈ V, ∑ j ∈ Z, f i j := (sum_subset (filter_subset ..) (fun i hi no => sum_eq_zero (fun j _ =>
      zero i j (fun dv => missing i hi no ((Nat.dvd_lcm_left ..).trans dv))))).symm
    _ = _ := sum_congr rfl (fun i _ => (sum_subset (filter_subset ..) (fun j hj no =>
      zero i j (fun dv => missing j hj no ((Nat.dvd_lcm_right ..).trans dv)))).symm)

/-- Actual signed multiplicities enter the nonnegative zero weight. Uniformly
bounding the Beta factor leaves precisely a class energy. -/
theorem related_pairs_le_energy {q : ℕ} [NeZero q] (Z : Finset CatalogueEntry) (K n : ℕ) (P B : ℝ)
    (hn : 0 < n) (hB : 0 ≤ B)
    (level : ∀ v ∈ activeEntries Z K n, catalogueLevel v ∣ q)
    (prim : ∀ v ∈ activeEntries Z K n, (catalogueCharacter v).IsPrimitive)
    (beta : ∀ i ∈ activeEntries Z K n, ∀ j ∈ activeEntries Z K n,
      ‖Complex.betaIntegral ((catalogueRoot i).getD 1) ((catalogueRoot j).getD 1)‖ ≤ B) :
    let S := series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) n
    ‖cataloguePairSum Z P (relatedBetaTerm K n)‖ ≤
      (S.re*(n:ℝ)*B) * classEnergy (activeEntries Z K n) (catalogueClass q K) (zeroWeight n) := by
  classical
  intro S
  let V := activeEntries Z K n
  let c := catalogueClass q K
  let w := zeroWeight n
  let M := S.re*(n:ℝ)*B
  have s0 : 0 ≤ S.re := (norm_nonneg _).trans (TwistedGoldbachSingularSeries.infinite_domination isPrimitive_one_level_one isPrimitive_one_level_one n hn)
  have m0 : 0 ≤ M := by dsimp only [M];positivity
  have w0 (v : CatalogueEntry) : 0 ≤ w v := by dsimp only [w,zeroWeight];positivity
  have actual (i : CatalogueEntry) (hi : i ∈ V) (j : CatalogueEntry) (hj : j ∈ V) :
      ‖catalogueWeight i*catalogueWeight j*catalogueBetaTerm n i j‖ ≤ M*(w i*w j) := by
    let s := (catalogueRoot i).getD 1
    let t := (catalogueRoot j).getD 1
    have npos : 0 < (n:ℝ) := Nat.cast_pos.mpr hn
    have power : ‖(n:ℂ)^(s+t-1)‖ = (n:ℝ)*((n:ℝ)^(s.re-1)*(n:ℝ)^(t.re-1)) := by
      rw [norm_natCast_cpow_of_pos hn,sub_re,add_re,one_re,←Real.rpow_add npos]
      conv_rhs => lhs;rw [←Real.rpow_one (n:ℝ)]
      rw [←Real.rpow_add npos];congr 1;ring
    have dom := TwistedGoldbachSingularSeries.infinite_domination (prim i hi).inv (prim j hj).inv n hn
    let C := series (catalogueCharacter i)⁻¹ (catalogueCharacter j)⁻¹ n
    change ‖C‖ ≤ S.re at dom
    change ‖catalogueWeight i*catalogueWeight j*(C*((n:ℂ)^(s+t-1)*Complex.betaIntegral s t))‖ ≤ _
    simp only [norm_mul,power]
    have pos : 0 ≤ (n:ℝ)*((n:ℝ)^(s.re-1)*(n:ℝ)^(t.re-1)) := by positivity
    apply (mul_le_mul_of_nonneg_left (mul_le_mul dom (mul_le_mul_of_nonneg_left (beta i hi j hj) pos)
      (mul_nonneg pos (norm_nonneg _)) s0) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).trans_eq
    dsimp only [M,w,zeroWeight,s,t];ring
  let f (i j : CatalogueEntry) := if (Nat.lcm (catalogueLevel i) (catalogueLevel j):ℝ) ≤ P then
    catalogueWeight i*catalogueWeight j*relatedBetaTerm K n i j else 0
  let g (i j : CatalogueEntry) := if c i*c j=1 then w i*w j else 0
  have g0 (i j : CatalogueEntry) : 0 ≤ g i j := by dsimp only [g];split_ifs;exact mul_nonneg (w0 _) (w0 _);rfl
  have each (i : CatalogueEntry) (hi : i ∈ V) (j : CatalogueEntry) (hj : j ∈ V) : ‖f i j‖ ≤ M*g i j := by
    dsimp only [f,relatedBetaTerm]
    split_ifs with cut keep
    · have same := (inverse_classes_iff K (catalogueCharacter i) (catalogueCharacter j) (level i hi) (level j hj)).mpr keep.2
      have eqn : c i*c j=1 := by simpa only [c,catalogueClass,catalogueLift,dite_eq_left (level i hi),dite_eq_left (level j hj)] using same
      rw [show g i j = w i*w j from ite_eq_left eqn]
      exact actual i hi j hj
    all_goals simp only [mul_zero,norm_zero]; exact mul_nonneg m0 (g0 i j)
  rw [related_terms_supported]
  change ‖∑ i ∈ V, ∑ j ∈ V, f i j‖ ≤ _
  calc
    _ ≤ ∑ i ∈ V, ∑ j ∈ V, M*g i j := (norm_sum_le ..).trans (sum_le_sum (fun i hi =>
      (norm_sum_le ..).trans (sum_le_sum (each i hi))))
    _ = M*(∑ i ∈ V, ∑ j ∈ V, g i j) := by simp_rw [←Finset.mul_sum]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ m0
      apply le_trans _ (inverse_pairs_le_classEnergy V c w)
      apply sum_le_sum;intro i hi
      apply sum_le_sum;intro j hj
      by_cases h : c i*c j=1 <;> simp only [g,h,ite_true,ite_false,le_refl]

end Conjectures.Goldbach.BinaryShiftZeroDensity
end
end

section
open Complex Finset Filter DirichletCharacter Goldbach GoldbachTwistedMellin
open scoped Topology Classical
noncomputable section
namespace Conjectures.Goldbach.BinaryShiftZeroDensity
open TwistedGoldbachPairMean TwistedGoldbachLocalProduct

/-- The common modulus for the characters with levels dividing the fixed
multiplier times a particular target. -/
def activeModulus (m Q X : ℕ) (H T : ℝ) (K n : ℕ) :=
  ((nearOneConductors m Q X H T).filter (fun r => r ∣ K*n)).lcm id

private theorem activeModulus_pos (m Q X : ℕ) (H T : ℝ) (K n : ℕ) : 0 < activeModulus m Q X H T K n := by
  apply Nat.pos_of_ne_zero;apply Finset.lcm_ne_zero_iff.mpr
  intro r hr;obtain ⟨h,_⟩ := mem_filter.mp hr
  rcases mem_insert.mp h with rfl|mem
  · decide
  · obtain ⟨p,_,rfl⟩ := mem_image.mp mem;exact Nat.succ_ne_zero _

private theorem actual_zero_strip (m Q X : ℕ) (H T : ℝ) (v : CatalogueEntry)
    (hv : v ∈ (nearOneCatalogue m Q X H T).erase none) : 1-H/Real.log X ≤ ((catalogueRoot v).getD 1).re := by
  classical
  obtain ⟨ne,mem⟩ := mem_erase.mp hv
  cases v with
  | none => exact (ne rfl).elim
  | some v =>
    have root : v ∈ (nearOneCharacters m Q (1-H/Real.log X) T).sigma
        (fun a => nearOneRoots m a.2 (1-H/Real.log X) T) := by simpa [nearOneCatalogue] using mem
    exact (mem_filter.mp (mem_sigma.mp root).2).2.1

/-- Apart from O(X^(3/4)) targets the surviving characters share a single
modulus below X^(1/4). A deficit in the weighted zero-class energy then gives
a positive lower bound on the retained part of the *actual* signed arcs. -/
theorem nearOne_class_energy_floor (H T η : ℝ) (hH : 0 ≤ H) (hT : 0 ≤ T) (hη : 0 < η) :
    ∃ (K : ℕ) (C : ℝ), 0 < K ∧ 0 < C ∧ ∀ᶠ Q : ℕ in atTop, ∀ m : ℕ, 2 ≤ m → Q ≤ m+2 →
      let X : ℝ := (m+2:ℕ)
      let Z := nearOneCatalogue m Q (m+2) H T
      ∃ (P : ℝ) (D : Finset ℕ), X^(11/40:ℝ) ≤ P ∧ P ≤ X^(3/10:ℝ) ∧ (D.card:ℝ) ≤ C*X^(3/4:ℝ) ∧
        ∀ n : ℕ, 0 < n → n ≤ m+2 → m+2 ≤ 2*n → Even n → n ∉ D →
          let q := activeModulus m Q (m+2) H T K n
          let V := activeEntries (Z.erase none) K n
          0 < q ∧ (q:ℝ) < X^(1/4:ℝ) ∧ (∀ v ∈ V, catalogueLevel v ∣ q) ∧
            (classEnergy V (catalogueClass q K) (zeroWeight n) ≤ 1-η →
              (η/2)*((series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) n).re*(n:ℝ)) ≤
                (cataloguePairSum Z P (catalogueArcTerm m n P)).re) := by
  obtain ⟨K,hK,formula⟩ := nearOne_related_formula H T (η/4) hH hT (by positivity)
  obtain ⟨B,hNum⟩ := nearOneCharacters_bounded H T hH hT
  obtain ⟨d,hd,kernel⟩ := BinaryShiftCircle.norm_betaIntegral_le_one_add (show 0 < η/4 by positivity)
  have ltend := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  obtain ⟨N,logs⟩ := eventually_atTop.mp (ltend.eventually_ge_atTop (H/d))
  refine ⟨K,2^(B+1)*((K:ℝ)+1),hK,by positivity,?_⟩
  filter_upwards [formula,hNum,eventually_ge_atTop N] with Q exactArc size hN
  intro m hm hQ X Z
  obtain ⟨P,hP,hP',rule⟩ := exactArc m hm hQ
  let R := nearOneConductors m Q (m+2) H T
  let D := BinaryShiftCircle.conductorOutliers (m+2) K R
  have count : R.card ≤ B+1 := (Finset.card_insert_le ..).trans
    (Nat.add_le_add_right (Finset.card_image_le.trans (size m (m+2) hQ)) 1)
  have cd := BinaryShiftCircle.conductorOutliers_card_le (m+2) K R (by omega) hK
  have total : (D.card:ℝ) ≤ 2^(B+1)*((K:ℝ)+1)*X^(3/4:ℝ) := cd.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) count) (by positivity)) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  refine ⟨P,D,hP,hP',total,?_⟩
  intro n hn nX xn he notbad q V
  have qp : 0 < q := activeModulus_pos ..
  let _ : NeZero q := ⟨qp.ne'⟩
  have pre (v : CatalogueEntry) (hv : v ∈ V) : v ∈ Z.erase none ∧ catalogueLevel v ∣ K*n := mem_filter.mp hv
  have raw (v : CatalogueEntry) (hv : v ∈ V) := catalogue_properties m Q (m+2) H T hT v (mem_of_mem_erase (pre v hv).1)
  have lev (v : CatalogueEntry) (hv : v ∈ V) : catalogueLevel v ∣ q :=
    Finset.dvd_lcm (mem_filter.mpr ⟨(raw v hv).1,(pre v hv).2⟩)
  refine ⟨qp,BinaryShiftCircle.small_lcm_of_not_mem_conductorOutliers nX notbad,lev,?_⟩
  intro energy
  have x1 : 1 < X := by dsimp only [X];exact_mod_cast (by omega : 1 < m+2)
  have hlog : H/d ≤ Real.log X := logs (m+2) (hN.trans hQ)
  have strip (i : CatalogueEntry) (hi : i ∈ V) : 1-d ≤ ((catalogueRoot i).getD 1).re := by
    have low := actual_zero_strip m Q (m+2) H T i (pre i hi).1
    have h : H/Real.log X ≤ d := (div_le_iff₀ (Real.log_pos x1)).mpr
      (((div_le_iff₀ hd).mp hlog).trans_eq (mul_comm ..))
    exact (sub_le_sub_left h 1).trans low
  let S := series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) n
  let E := cataloguePairSum (Z.erase none) P (relatedBetaTerm K n)
  let A := cataloguePairSum Z P (catalogueArcTerm m n P)
  have sn : 0 ≤ S.re := zero_le_one.trans (TwistedGoldbachMixedPrincipal.ordinary_at_least_one n hn he)
  have s0 : 0 ≤ S.re*(n:ℝ) := mul_nonneg sn (Nat.cast_nonneg _)
  have e := related_pairs_le_energy (Z.erase none) K n P (1+η/4) hn (by positivity) lev
    (fun i hi => (raw i hi).2.1) (fun i hi j hj => kernel _ _ (strip i hi) (strip j hj))
  change ‖E‖ ≤ S.re*(n:ℝ)*(1+η/4)*classEnergy V (catalogueClass q K) (zeroWeight n) at e
  have loss := e.trans (mul_le_mul_of_nonneg_left energy (mul_nonneg s0 (by positivity)))
  have err := rule n hn nX xn he
  change ‖A-(S*(n:ℂ)+E)‖ ≤ S.re*((n:ℝ)*(η/4)) at err
  have reE := ((Complex.re_le_norm (-E)).trans_eq (norm_neg E)).trans loss
  have reA := ((Complex.re_le_norm (-(A-(S*(n:ℂ)+E)))).trans_eq (norm_neg _)).trans err
  simp only [Complex.neg_re,Complex.sub_re,Complex.add_re,Complex.mul_re,Complex.natCast_re,Complex.natCast_im,mul_zero,sub_zero] at reE reA
  change (η/2)*(S.re*(n:ℝ)) ≤ A.re
  nlinarith only [reE,reA,mul_nonneg (sq_nonneg η) s0]

end Conjectures.Goldbach.BinaryShiftZeroDensity
end
end
