import Mathlib.Tactic.NormNum.Prime
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.ZetaValues

/- Constant certificate adapted from DDT666444888, Goldbach PR 4861,
   revision a2c4f0cf4a3c1fa555c908dc71b40c8669491408, Apache-2.0.
   This file retains the Euler-product tail and the numerical inputs for
   Euler–Mascheroni, log zeta at 3, and the finite prime correction.
   Credits for individual numerical inputs are retained below. -/

-- Adapted from Severin189, https://github.com/CGandGameEngineLearner/goldbach-proofs/pull/4835
-- The certificate is placed in a local namespace and its entry point is renamed.
namespace SmallRangeInputs
section
open Filter
open scoped Topology

namespace MertensGamma

private noncomputable def lower (n : ℕ) : ℝ :=
  (harmonic n : ℝ) - Real.log n - (1 / 2) / n

private noncomputable def upper (n : ℕ) : ℝ :=
  lower n + (1 / 8) * ((1 : ℝ) / n) ^ 2

private lemma log_trapezoid (x : ℝ) (hx : 0 < x) :
    (1 / 2) / x + (1 / 2) / (x+1) - (1 / 8) * ((1/x)^2 - (1/(x+1))^2) ≤
      Real.log ((x+1)/x) ∧
    Real.log ((x+1)/x) ≤ (1 / 2) / x + (1 / 2) / (x+1) := by
  let t : ℝ := 1/(2*x+1)
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hs : t < 1 := (div_lt_one (by positivity : 0 < 2*x+1)).2 (by linarith)
  have hid : (1+t)/(1-t) = (x+1)/x := by dsimp [t]; field_simp; ring
  have hL := Real.sum_range_le_log_div ht hs 1
  have hU := Real.log_div_le_sum_range_add ht hs 0
  rw [hid] at hL hU
  simp at hL hU
  have htpos : 0 < 1-t^2 := by nlinarith [mul_pos (sub_pos.mpr hs) (show 0 < 1+t by linarith)]
  have hid' : t/(1-t^2) = ((1/2)/x + (1/2)/(x+1))/2 := by
    apply (div_eq_iff htpos.ne').2
    dsimp [t]
    field_simp
    ring
  constructor
  · apply le_trans (b := 2*t)
    · dsimp [t]
      field_simp
      nlinarith
    · linarith only [hL]
  · rw [hid'] at hU
    linarith only [hU]

private lemma steps (n : ℕ) (hn : 0 < n) :
    lower n ≤ lower (n+1) ∧ upper (n+1) ≤ upper n := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  obtain ⟨h₁,h₂⟩ := log_trapezoid (n : ℝ) hnR
  rw [Real.log_div (by positivity) hnR.ne'] at h₁ h₂
  simp only [upper, lower, harmonic_succ]
  push_cast
  simp only [div_eq_mul_inv] at h₁ h₂ ⊢
  constructor <;> linarith only [h₁,h₂]

theorem enclosure (N : ℕ) (hN : 0 < N) :
    lower N ≤ Real.eulerMascheroniConstant ∧ Real.eulerMascheroniConstant ≤ upper N := by
  have hL : Tendsto lower atTop (𝓝 Real.eulerMascheroniConstant) := by
    change Tendsto (fun n : ℕ => (harmonic n : ℝ) - Real.log n - (1/2)/n) _ _
    simpa only [sub_zero] using Real.tendsto_harmonic_sub_log.sub
      (tendsto_const_div_atTop_nhds_zero_nat (1/2 : ℝ))
  have hU : Tendsto upper atTop (𝓝 Real.eulerMascheroniConstant) := by
    change Tendsto (fun n : ℕ => lower n + 1/8*((1:ℝ)/n)^2) _ _
    simpa only [zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero] using hL.add ((tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).pow 2 |>.const_mul (1/8 : ℝ))
  have hb : ∀ k, N ≤ k → lower N ≤ lower k ∧ upper k ≤ upper N := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => exact ⟨le_rfl,le_rfl⟩
    | succ k hk ih =>
      have h := steps k (hN.trans_le hk)
      exact ⟨ih.1.trans h.1, h.2.trans ih.2⟩
  constructor
  · apply ge_of_tendsto hL
    filter_upwards [eventually_ge_atTop N] with k hk using (hb k hk).1
  · apply le_of_tendsto hU
    filter_upwards [eventually_ge_atTop N] with k hk using (hb k hk).2

private def truncSum : ℕ → ℕ
  | 0 => 0
  | n+1 => truncSum n + 10^13 / (n+1)

private lemma harmonic_rounded (n : ℕ) :
    (truncSum n : ℝ) ≤ (10^13 : ℝ) * (harmonic n : ℝ) ∧
    (10^13 : ℝ) * (harmonic n : ℝ) ≤ (truncSum n : ℝ) + n := by
  induction n with
  | zero => simp [truncSum, harmonic_zero]
  | succ n ih =>
    let q : ℕ := 10^13 / (n+1)
    have hn : 0 < (n : ℝ) + 1 := by positivity
    have hleft : (q : ℝ) ≤ (10^13 : ℝ) / (n+1) := by
      rw [le_div_iff₀ hn]
      exact_mod_cast Nat.div_mul_le_self (10^13) (n+1)
    have hright : (10^13 : ℝ) / (n+1) ≤ (q : ℝ) + 1 := by
      rw [div_le_iff₀ hn]
      rw [mul_comm]
      exact_mod_cast (Nat.lt_mul_div_succ (10^13) (Nat.succ_pos n)).le
    change (↑(truncSum n + q) : ℝ) ≤ _ ∧ _ ≤ (↑(truncSum n + q) : ℝ) + _
    simp only [harmonic_succ, Rat.cast_add, Rat.cast_inv, Rat.cast_natCast, Nat.cast_add,
      Nat.cast_one, mul_add, ← div_eq_mul_inv]
    constructor <;> linarith only [ih.1,ih.2,hleft,hright]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2500000 in
private theorem truncated : truncSum 4096 = 88951038967732 := by decide +kernel

theorem gamma_bounds :
    (0.57721565 : ℝ) ≤ Real.eulerMascheroniConstant ∧
    Real.eulerMascheroniConstant ≤ (0.57721568 : ℝ) := by
  obtain ⟨hA,hB⟩ := enclosure 4096 (by decide)
  obtain ⟨hP,hQ⟩ := harmonic_rounded 4096
  rw [truncated] at hP hQ
  have hlog : Real.log (4096 : ℝ) = 12 * Real.log 2 := by
    convert Real.log_pow (2:ℝ) 12 using 1; norm_num
  norm_num only [upper, lower, Nat.cast_ofNat] at hA hB hP hQ
  rw [hlog] at hA hB
  constructor <;> linarith only [hA,hB,hP,hQ,Real.log_two_lt_d9,Real.log_two_gt_d9]

end MertensGamma

theorem gammaBound : (0.57721562 ≤ Real.eulerMascheroniConstant ∧ Real.eulerMascheroniConstant ≤ 0.57721571) := by
  obtain ⟨h₁, h₂⟩ := MertensGamma.gamma_bounds
  constructor <;> linarith
end
end SmallRangeInputs

-- Adapted from Liang-Chengyuan, https://github.com/CGandGameEngineLearner/goldbach-proofs/pull/4843
-- The certificate is placed in a local namespace and its entry point is renamed.
namespace SmallRangeInputs
section
-- The scaled logarithm upper bound is adapted from the Apache-2.0 proof of
-- Task8f9f08650abf4d04bfa7122e, revision ed0b2428d69a876757ab067a438fcf6afce8e743.
-- Here 16 terms and 14 decimal places suffice for the short prime sum.
namespace MertensFiniteCorrection
open Finset

def scale : ℕ := 10 ^ 14

def roundedUp (u v : ℕ) : ℕ :=
  17 + ∑ i ∈ range 16,
    (2 * scale * (u - v) ^ (2 * i + 1)) / ((2 * i + 1) * (u + v) ^ (2 * i + 1))

theorem log_le_roundedUp (u v : ℕ) (hv : 0 < v) (hvu : v ≤ u) (huv : u ≤ 2 * v) :
    Real.log ((u : ℝ) / (v : ℝ)) ≤ (roundedUp u v : ℝ) / (scale : ℝ) := by
  have hscale : 0 < (scale : ℝ) := by norm_num [scale]
  have hvR : 0 < (v : ℝ) := by exact_mod_cast hv
  have hvuR : (v : ℝ) ≤ (u : ℝ) := by exact_mod_cast hvu
  have huR := hvR.trans_le hvuR
  have huvR : (u : ℝ) ≤ 2 * (v : ℝ) := by exact_mod_cast huv
  have hpos : 0 < (u : ℝ) + (v : ℝ) := by positivity
  let t : ℝ := ((u : ℝ) - (v : ℝ)) / ((u : ℝ) + (v : ℝ))
  have ht0 : 0 ≤ t := div_nonneg (sub_nonneg.mpr hvuR) hpos.le
  have ht3 : t ≤ 1 / 3 := by
    apply (div_le_iff₀ hpos).2
    linarith only [huvR]
  have ht1 : t < 1 := ht3.trans_lt (by norm_num)
  have htRatio : (1 + t) / (1 - t) = (u : ℝ) / (v : ℝ) := by
    apply (div_eq_div_iff (sub_ne_zero.mpr ht1.ne') hvR.ne').2
    dsimp [t]
    field_simp
    ring
  have htail : 2 * (scale : ℝ) * (t ^ (33 : ℕ) / (1 - t ^ 2)) ≤ 1 := by
    have htSq : t ^ (2 : ℕ) ≤ (1 / 3 : ℝ) ^ (2 : ℕ) := pow_le_pow_left₀ ht0 ht3 2
    have hden : (0 : ℝ) < 1 - (1 / 3 : ℝ) ^ (2 : ℕ) := by norm_num
    have hden_le : 1 - (1 / 3 : ℝ) ^ (2 : ℕ) ≤ 1 - t ^ (2 : ℕ) := by linarith
    calc
      _ ≤ 2 * (scale : ℝ) * ((1 / 3 : ℝ) ^ (33 : ℕ) / (1 - (1 / 3 : ℝ) ^ (2 : ℕ))) := by
        gcongr
      _ ≤ _ := by norm_num [scale]
  let term : ℕ → ℕ := fun i =>
    (2 * scale * (u - v) ^ (2 * i + 1)) / ((2 * i + 1) * (u + v) ^ (2 * i + 1))
  have hround (i : ℕ) :
      2 * (scale : ℝ) * (t ^ (2 * i + 1) / ((2 * i + 1 : ℕ) : ℝ)) ≤ (term i : ℝ) + 1 := by
    let A : ℕ := 2 * scale * (u - v) ^ (2 * i + 1)
    let B : ℕ := (2 * i + 1) * (u + v) ^ (2 * i + 1)
    have hB : 0 < B := by dsimp [B]; positivity
    have hBR : 0 < (B : ℝ) := by exact_mod_cast hB
    have hf : (A : ℝ) / (B : ℝ) ≤ (term i : ℝ) + 1 := by
      apply (div_le_iff₀ hBR).2
      have h := (Nat.lt_mul_div_succ A hB).le
      simpa [term, A, B, Nat.cast_mul, Nat.cast_add, mul_comm] using
        (show (A : ℝ) ≤ ((B * (A / B + 1) : ℕ) : ℝ) by exact_mod_cast h)
    have heq : 2 * (scale : ℝ) * (t ^ (2 * i + 1) / ((2 * i + 1 : ℕ) : ℝ)) =
        (A : ℝ) / (B : ℝ) := by
      dsimp [t, A, B]
      push_cast [Nat.cast_sub hvu]
      rw [div_pow]
      field_simp [hpos.ne']
    exact heq.le.trans hf
  have hsum : 2 * (scale : ℝ) * (∑ i ∈ range 16, t ^ (2 * i + 1) / ((2 * i + 1 : ℕ) : ℝ)) ≤
      (∑ i ∈ range 16, (term i : ℝ)) + 16 := by
    rw [mul_sum]
    calc
      _ ≤ ∑ i ∈ range 16, ((term i : ℝ) + 1) := sum_le_sum (fun i _ => hround i)
      _ = _ := by simp [sum_add_distrib]
  have hseries := Real.log_div_le_sum_range_add ht0 ht1 16
  rw [htRatio] at hseries
  have hscaled : Real.log ((u : ℝ) / (v : ℝ)) * (scale : ℝ) ≤
      2 * (scale : ℝ) * (∑ i ∈ range 16, t ^ (2 * i + 1) / ((2 * i + 1 : ℕ) : ℝ)) +
        2 * (scale : ℝ) * (t ^ (33 : ℕ) / (1 - t ^ 2)) := by
    calc
      _ = (2 * (scale : ℝ)) * (1 / 2 * Real.log ((u : ℝ) / (v : ℝ))) := by ring
      _ ≤ _ := by
        rw [← mul_add]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        simpa only [Nat.reduceMul, Nat.reduceAdd, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
          Nat.cast_one] using hseries
  apply (le_div_iff₀ hscale).2
  change _ ≤ ((17 + ∑ i ∈ range 16, term i : ℕ) : ℝ)
  push_cast
  linarith only [hscaled, hsum, htail]

def upper (a b : ℕ) : ℚ := (roundedUp a b : ℚ) / scale
def lower (a b : ℕ) : ℚ := 0.6931471803 - upper (2*b) a

theorem log_bounds (a b : ℕ) (hb : 0 < b) (hlo : b ≤ a) (hhi : a ≤ 2*b) :
    (lower a b : ℝ) ≤ Real.log ((a:ℝ)/b) ∧ Real.log ((a:ℝ)/b) ≤ (upper a b : ℝ) := by
  have bpos : 0 < (b:ℝ) := by exact_mod_cast hb
  have apos : 0 < (a:ℝ) := by exact_mod_cast hb.trans_le hlo
  constructor
  · have u := log_le_roundedUp (2*b) a (by omega) hhi (by omega)
    have ratio : Real.log ((2*b:ℕ)/ (a:ℝ)) = Real.log 2 - Real.log ((a:ℝ)/b) := by
      push_cast
      rw [Real.log_div (by positivity) apos.ne',Real.log_mul (by norm_num) bpos.ne',
        Real.log_div apos.ne' bpos.ne']
      ring
    rw [ratio] at u
    unfold lower upper
    push_cast
    linarith only [Real.log_two_gt_d9,u]
  · unfold upper
    push_cast
    exact log_le_roundedUp a b hb hlo hhi

def lowerTerm (p : ℕ) : ℚ := -upper p (p-1) + 1/(p:ℚ)
    + lower (p^2) (p^2-1)/2 + lower (p^3) (p^3-1)/3
def upperTerm (p : ℕ) : ℚ := -lower p (p-1) + 1/(p:ℚ)
    + upper (p^2) (p^2-1)/2 + upper (p^3) (p^3-1)/3

noncomputable def term (p : ℕ) : ℝ := Real.log (1 - 1/(p:ℝ)) + 1/(p:ℝ) -
  Real.log (1 - 1/(p:ℝ)^2)/2 - Real.log (1 - 1/(p:ℝ)^3)/3

private theorem signed_log_bounds {a : ℕ} (ha : 2 ≤ a) :
    -(upper a (a-1) : ℝ) ≤ Real.log (1 - 1/(a:ℝ)) ∧
    Real.log (1 - 1/(a:ℝ)) ≤ -(lower a (a-1) : ℝ) := by
  have h := log_bounds a (a-1) (by omega) (by omega) (by omega)
  have ar : 1 < (a:ℝ) := by exact_mod_cast (show 1 < a by omega)
  have iden : Real.log (1 - 1/(a:ℝ)) = -Real.log ((a:ℝ)/(a-1:ℕ)) := by
    rw [← Real.log_inv]
    congr 1
    rw [Nat.cast_sub (by omega : 1 ≤ a),Nat.cast_one,inv_div]
    field_simp
  rw [iden]
  exact ⟨neg_le_neg h.2,neg_le_neg h.1⟩

private theorem term_bounds (p : ℕ) (hp : p.Prime) :
    (lowerTerm p : ℝ) ≤ term p ∧ term p ≤ (upperTerm p : ℝ) := by
  have h1 := signed_log_bounds hp.two_le
  have h2 := signed_log_bounds (a:=p^2) (by nlinarith [hp.two_le])
  have p3 : 2^3 ≤ p^3 := Nat.pow_le_pow_left hp.two_le _
  have h3 := signed_log_bounds (a:=p^3) (by omega)
  push_cast at h2 h3
  unfold term lowerTerm upperTerm
  push_cast
  constructor <;> linarith only [h1.1,h1.2,h2.1,h2.2,h3.1,h3.2]

def piLo : ℕ := 3141592653589
def piHi : ℕ := 3141592653590
def piDen : ℕ := 6*10^24
private theorem piTerm :
    (lower (piLo^2) piDen : ℝ) ≤ Real.log (Real.pi^2/6) ∧
    Real.log (Real.pi^2/6) ≤ (upper (piHi^2) piDen : ℝ) := by
  have l := (log_bounds (piLo^2) piDen (by decide) (by decide) (by decide)).1
  have u := (log_bounds (piHi^2) piDen (by decide) (by decide) (by decide)).2
  have a : (3141592653589/10^12 : ℝ) < Real.pi := by linarith only [Real.pi_gt_d20]
  have b : Real.pi < (3141592653590/10^12 : ℝ) := by linarith only [Real.pi_lt_d20]
  refine ⟨l.trans (Real.log_le_log (by norm_num [piLo,piDen]) ?_),
    (Real.log_le_log (by positivity) ?_).trans u⟩
  · norm_num [piLo,piDen]
    nlinarith [sq_nonneg (Real.pi-3141592653589/10^12),
      mul_self_le_mul_self (by norm_num) a.le]
  · norm_num [piHi,piDen]
    nlinarith [mul_self_le_mul_self Real.pi_pos.le b.le]

private theorem numerics :
    (-0.25437377 : ℚ) ≤ -(upper (piHi^2) piDen)/2 +
      ∑ p ∈ (range 101).filter Nat.Prime, lowerTerm p ∧
    -(lower (piLo^2) piDen)/2 + ∑ p ∈ (range 101).filter Nat.Prime, upperTerm p
      ≤ (-0.25437368 : ℚ) := by decide +kernel

end MertensFiniteCorrection

open MertensFiniteCorrection Finset in
theorem finiteCorrection :
    let w := fun p : ℕ => Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ) -
      Real.log (1 - 1 / (p : ℝ)^2)/2 - Real.log (1 - 1 / (p : ℝ)^3)/3
    let c := -(Real.log (Real.pi^2/6)/2) + ∑ p ∈ (range 101).filter Nat.Prime, w p
    (-0.25437377 : ℝ) ≤ c ∧ c ≤ -0.25437368 := by
  change _ ≤ -(Real.log (Real.pi^2/6)/2) + ∑ p ∈ (range 101).filter Nat.Prime, term p ∧ _
  have L := Finset.sum_le_sum (s := (range 101).filter Nat.Prime)
    (fun p hp => (term_bounds p (mem_filter.mp hp).2).1)
  have U := Finset.sum_le_sum (s := (range 101).filter Nat.Prime)
    (fun p hp => (term_bounds p (mem_filter.mp hp).2).2)
  have lo := (Rat.cast_le (K := ℝ)).mpr numerics.1
  have hi := (Rat.cast_le (K := ℝ)).mpr numerics.2
  push_cast at lo hi
  change _ ∧ -(Real.log (Real.pi^2/6)/2) + ∑ p ∈ (range 101).filter Nat.Prime, term p ≤ _
  constructor <;> linarith only [L,U,lo,hi,piTerm.1,piTerm.2]
end
end SmallRangeInputs

-- Adapted from bz7777777, https://github.com/CGandGameEngineLearner/goldbach-proofs/pull/4829
-- The certificate is placed in a local namespace and its entry point is renamed.
namespace SmallRangeInputs
section
-- child 1 zh: 用 Euler 乘积消去低阶项，并认证截断在素数 100 以下时的尾项。
-- child 1 en: Cancel the low-order prime contributions with Euler products and bound the tail beyond 100.
-- child 2 zh: 认证 Euler–Mascheroni 常数的数值区间。
-- child 2 en: Certify the numerical enclosure of the Euler–Mascheroni constant.
-- child 3 zh: 认证 ζ(3) 的对数的数值区间。
-- child 3 en: Certify the numerical enclosure of the logarithm of zeta at 3.
-- child 4 zh: 认证有限素数余项与 ζ(2) 对数贡献之和的数值区间。
-- child 4 en: Certify the finite prime correction together with the logarithmic zeta-at-2 contribution.

theorem assembleConstant
    (tail :
      let M₀ : ℝ := Real.eulerMascheroniConstant +
        ∑' p : Nat.Primes, (Real.log (1 - 1 / (p.1 : ℝ)) + 1 / (p.1 : ℝ))
      let Z₃ : ℝ := ∑' j : ℕ, (1 : ℝ) / (((j + 1 : ℕ) : ℝ) ^ 3)
      let F (p : ℕ) : ℝ :=
        Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ) -
          Real.log (1 - 1 / (p : ℝ) ^ 2) / 2 - Real.log (1 - 1 / (p : ℝ) ^ 3) / 3
      let C : ℝ := -(Real.log (Real.pi ^ 2 / 6) / 2) +
        ∑ p ∈ (Finset.range 101).filter Nat.Prime, F p
      |M₀ - (Real.eulerMascheroniConstant - Real.log Z₃ / 3 + C)| ≤ (8e-9 : ℝ))
    (gamma :
      (0.57721562 : ℝ) ≤ Real.eulerMascheroniConstant ∧
      Real.eulerMascheroniConstant ≤ (0.57721571 : ℝ))
    (zetaThree :
      let Z₃ : ℝ := ∑' j : ℕ, (1 : ℝ) / (((j + 1 : ℕ) : ℝ) ^ 3)
      (0.18403413 : ℝ) ≤ Real.log Z₃ ∧ Real.log Z₃ ≤ (0.18403422 : ℝ))
    (finiteCorrection :
      let F (p : ℕ) : ℝ :=
        Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ) -
          Real.log (1 - 1 / (p : ℝ) ^ 2) / 2 - Real.log (1 - 1 / (p : ℝ) ^ 3) / 3
      let C : ℝ := -(Real.log (Real.pi ^ 2 / 6) / 2) +
        ∑ p ∈ (Finset.range 101).filter Nat.Prime, F p
      (-0.25437377 : ℝ) ≤ C ∧ C ≤ (-0.25437368 : ℝ)) :
    (have x1 : ℝ := Real.eulerMascheroniConstant + ∑' (x1 : Nat.Primes), (Real.log ((1 : ℝ) - (1 : ℝ) / ↑↑x1) + (1 : ℝ) / ↑↑x1); 0.261497 ≤ x1 ∧ x1 ≤ 0.261498) := by
  dsimp only at tail zetaThree finiteCorrection ⊢
  obtain ⟨hTailLower, hTailUpper⟩ := abs_le.mp tail
  constructor
  · linarith only [hTailLower, gamma.1, zetaThree.2, finiteCorrection.1]
  · linarith only [hTailUpper, gamma.2, zetaThree.1, finiteCorrection.2]
end
end SmallRangeInputs

namespace ZetaThreeCertificate

-- Each term is rounded down to an integer multiple of 1 / scale.
private def scaledPrefix (scale : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => scaledPrefix scale n + scale / (n + 1)^3

private theorem scaledBounds (scale n : ℕ) :
    (scaledPrefix scale n : ℝ) ≤ scale * (∑ j ∈ Finset.range n, 1 / ((j + 1 : ℕ) : ℝ)^3) ∧
    scale * (∑ j ∈ Finset.range n, 1 / ((j + 1 : ℕ) : ℝ)^3) ≤ (scaledPrefix scale n : ℝ) + n := by
  induction n with
  | zero => simp [scaledPrefix]
  | succ n ih =>
    let k := (n + 1)^3
    have hk : 0 < k := by dsimp [k]; positivity
    have hl : ((scale / k : ℕ) : ℝ) ≤ (scale : ℝ) / k := Nat.cast_div_le
    have hu : (scale : ℝ) / k ≤ ((scale / k : ℕ) : ℝ) + 1 := by
      apply (div_le_iff₀ (Nat.cast_pos.mpr hk : (0 : ℝ) < k)).mpr
      exact_mod_cast (by simpa only [Nat.mul_comm k] using (Nat.lt_mul_div_succ scale hk).le :
        scale ≤ (scale / k + 1) * k)
    rw [Finset.sum_range_succ, mul_add, scaledPrefix]
    simp only [Nat.cast_add, Nat.cast_succ, mul_one_div] at *
    dsimp only [k] at hl hu
    simp only [Nat.cast_pow, Nat.cast_add, Nat.cast_one] at hl hu
    constructor <;> linarith [ih.1, ih.2]

theorem prefix_bounds :
    (1.20205499953 : ℝ) ≤ (∑ n ∈ Finset.range 512, 1 / ((n + 1 : ℕ) : ℝ)^3) ∧
    (∑ n ∈ Finset.range 512, 1 / ((n + 1 : ℕ) : ℝ)^3) ≤ (1.20205499954 : ℝ) := by
  have hsum : scaledPrefix 1000000000000000 512 = 1202054999532377 := by
    decide +kernel
  obtain ⟨hl, hu⟩ := scaledBounds 1000000000000000 512
  rw [hsum] at hl hu
  norm_num only [Nat.cast_ofNat] at hl hu
  constructor <;> linarith

private theorem between_cubes (x : ℝ) (hx : 0 < x) :
    1 / (x + 1)^3 ≤ 1 / (2*x^2) - 1 / (2*(x+1)^2) ∧
    1 / (2*x^2) - 1 / (2*(x+1)^2) ≤ 1 / x^3 := by
  constructor <;> field_simp <;> nlinarith [sq_nonneg x]

private noncomputable def halfSquare (n : ℕ) : ℝ := (1/2 : ℝ) * (1 / (n : ℝ)^2)

private theorem shifted_square_summable (k : ℕ) :
    Summable (fun n : ℕ => halfSquare (n + k)) := by
  apply (summable_nat_add_iff k).mpr
  exact (Real.summable_one_div_nat_pow.mpr (by decide : 1 < 2)).mul_left (1/2)

private theorem difference_hasSum (k : ℕ) :
    HasSum (fun n : ℕ => halfSquare (n+k) - halfSquare ((n+1)+k)) (halfSquare k) := by
  have h := shifted_square_summable k
  have h' := (summable_nat_add_iff 1).mpr h
  have ht := h.sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one, zero_add] at ht
  have hd := h.hasSum.sub h'.hasSum
  convert hd using 1
  linarith

theorem tail_bounds :
    let partialSum := ∑ n ∈ Finset.range 512, (1 : ℝ) / ((n + 1 : ℕ) : ℝ)^3
    let total := ∑' n : ℕ, (1 : ℝ) / ((n + 1 : ℕ) : ℝ)^3
    partialSum + 1/(2*513^2) ≤ total ∧ total ≤ partialSum + 1/(2*512^2) := by
  let f := fun n : ℕ => (1 : ℝ) / ((n+1 : ℕ) : ℝ)^3
  have hf : Summable f :=
    (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by decide : 1 < 3))
  have ht := ((summable_nat_add_iff 512).mpr hf).hasSum
  have hl : halfSquare 513 ≤ ∑' n : ℕ, f (n+512) := by
    apply hasSum_le _ (difference_hasSum 513) ht
    intro n
    have h := (between_cubes ((n : ℝ) + 513) (by positivity)).2
    unfold halfSquare f
    push_cast
    simp only [one_div, mul_inv_rev] at h ⊢
    convert h using 1 <;> ring
  have hu : (∑' n : ℕ, f (n+512)) ≤ halfSquare 512 := by
    apply hasSum_le _ ht (difference_hasSum 512)
    intro n
    have h := (between_cubes ((n : ℝ) + 512) (by positivity)).1
    unfold halfSquare f
    push_cast
    simp only [one_div, mul_inv_rev] at h ⊢
    convert h using 1
    ring
  change (∑ n ∈ Finset.range 512, f n) + _ ≤ (∑' n, f n) ∧
    (∑' n, f n) ≤ (∑ n ∈ Finset.range 512, f n) + _
  rw [← hf.sum_add_tsum_nat_add 512]
  refine ⟨add_le_add (le_refl _) ?_, add_le_add (le_refl _) ?_⟩
  · convert hl using 1
    norm_num [halfSquare]
  · convert hu using 1
    norm_num [halfSquare]

theorem log_bounds (x : ℝ) (hl : 1.20205689 ≤ x) (hu : x ≤ 1.20205691) :
    0.18403413 ≤ Real.log x ∧ Real.log x ≤ 0.18403422 := by
  have hx : 0 < x := lt_of_lt_of_le (by norm_num) hl
  constructor
  · apply (Real.le_log_iff_exp_le hx).2
    refine (Real.exp_bound' (x := 0.18403413) (by norm_num) (by norm_num)
      (n := 7) (by decide)).trans (le_trans ?_ hl)
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · apply (Real.log_le_iff_le_exp hx).2
    refine hu.trans (le_trans ?_ (Real.sum_le_exp_of_nonneg
      (x := 0.18403422) (by norm_num) 7))
    norm_num [Finset.sum_range_succ, Nat.factorial]

end ZetaThreeCertificate

theorem SmallRangeInputs.logZetaThree : (have x1 : ℝ := ∑' (x1 : ℕ), (1 : ℝ) / ↑(x1 + (1 : ℕ)) ^ (3 : ℕ); 0.18403413 ≤ Real.log x1 ∧ Real.log x1 ≤ 0.18403422) := by
  intro z
  obtain ⟨hpl, hpu⟩ := ZetaThreeCertificate.prefix_bounds
  obtain ⟨htl, htu⟩ := ZetaThreeCertificate.tail_bounds
  apply ZetaThreeCertificate.log_bounds
  · dsimp only [z]
    linarith
  · dsimp only [z]
    linarith

namespace MertensCert

private theorem log_euler_nat (k : ℕ) (hk : 1 < k) :
    HasSum (fun p : Nat.Primes => Real.log (1 - 1 / (p.1 : ℝ)^k))
      (-Real.log (∑' n : ℕ, (1 : ℝ) / (n : ℝ)^k)) := by
  let f : ℕ →*₀ ℝ :=
    { toFun := fun n => 1 / (n : ℝ)^k
      map_zero' := by simp [zero_pow (by omega : k ≠ 0)]
      map_one' := by simp
      map_mul' := by intro x y; simp [mul_pow, one_div, mul_comm] }
  have hs : Summable (fun n : ℕ => f n) := Real.summable_one_div_nat_pow.mpr hk
  have hn (n : ℕ) : 0 ≤ f n := by change 0 ≤ 1 / (n : ℝ)^k; positivity
  have hsn : Summable (fun n : ℕ => ‖f n‖) := by simpa [Real.norm_eq_abs, abs_of_nonneg, hn] using hs
  have hprod := EulerProduct.eulerProduct_completely_multiplicative_hasProd hsn
  have hpos : 0 < ∑' n : ℕ, f n := hs.tsum_pos hn 1 (by simp)
  have fac (p : Nat.Primes) : 0 < 1 - f p := by
    change 0 < 1 - 1 / (p.1 : ℝ)^k
    have hprime : 1 < (p.1 : ℝ) := by exact_mod_cast p.prop.one_lt
    have hpow : 1 < (p.1 : ℝ)^k := one_lt_pow₀ hprime (by omega)
    exact sub_pos.mpr ((div_lt_iff₀ (by positivity)).mpr (by simpa using hpow))
  have hlog : HasSum (fun p : Nat.Primes => Real.log ((1-f p)⁻¹))
      (Real.log (∑' n : ℕ, f n)) := by
    have h := (Real.continuousAt_log hpos.ne').tendsto.comp hprod
    unfold HasSum
    simpa only [Function.comp_def, Real.log_prod (fun p _ => inv_ne_zero (fac p).ne')] using h
  simpa [f, Real.log_inv] using hlog.neg

theorem log_two : HasSum (fun p : Nat.Primes => Real.log (1 - 1 / (p.1 : ℝ)^2))
    (-Real.log (Real.pi^2/6)) := by
  simpa only [hasSum_zeta_two.tsum_eq] using log_euler_nat 2 (by decide)

theorem log_three : HasSum (fun p : Nat.Primes => Real.log (1 - 1 / (p.1 : ℝ)^3))
    (-Real.log (∑' n : ℕ, (1 : ℝ) / ((n+1 : ℕ) : ℝ)^3)) := by
  have h := (Real.summable_one_div_nat_pow.mpr (by decide : 1 < 3)).sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one, Nat.cast_zero, zero_pow (by decide : 3 ≠ 0), div_zero, zero_add] at h
  rw [h]
  exact log_euler_nat 3 (by decide)

end MertensCert


namespace MertensCert

noncomputable def rem (p : ℕ) : ℝ :=
  Real.log (1 - 1/(p : ℝ)) + 1/(p : ℝ) -
    Real.log (1 - 1/(p : ℝ)^2)/2 - Real.log (1 - 1/(p : ℝ)^3)/3

private theorem remainder_at {x : ℝ} (hx : 0 ≤ x) (hsmall : x ≤ 1/4) :
    |Real.log (1-x) + x - Real.log (1-x^2)/2 - Real.log (1-x^3)/3| ≤ 2*x^5 := by
  have xsq := pow_le_pow_of_le_one hx (by linarith : x ≤ 1) (show 1 ≤ 2 by decide)
  have xcu := pow_le_pow_of_le_one hx (by linarith : x ≤ 1) (show 1 ≤ 3 by decide)
  rw [pow_one] at xsq xcu
  have approx (a : ℝ) (ha : 0 ≤ a) (hs : a ≤ 1/4) (n : ℕ) :
      |(∑ i ∈ Finset.range n, a^(i+1)/((i:ℝ)+1)) + Real.log (1-a)| ≤ (4/3)*a^(n+1) := by
    have h := Real.abs_log_sub_add_sum_range_le (x := a) (by rw [abs_of_nonneg ha]; linarith) n
    rw [abs_of_nonneg ha] at h
    apply h.trans
    apply (div_le_iff₀ (by linarith : 0 < 1-a)).mpr
    nlinarith [mul_le_mul_of_nonneg_right hs (pow_nonneg ha (n+1))]
  have h₁ := approx x hx hsmall 4
  have h₂ := approx (x^2) (by positivity) (xsq.trans hsmall) 2
  have h₃ := approx (x^3) (by positivity) (xcu.trans hsmall) 1
  norm_num [Finset.sum_range_succ, ← pow_mul] at h₁ h₂ h₃
  have h₆ : x^6 ≤ x^5/4 := by
    rw [pow_succ x 5]
    nlinarith [mul_le_mul_of_nonneg_left hsmall (pow_nonneg hx 5)]
  rw [abs_le] at *
  constructor <;> linarith [h₁.1,h₁.2,h₂.1,h₂.2,h₃.1,h₃.2,pow_nonneg hx 5]

theorem rem_bound {p : ℕ} (hp : 100 < p) : |rem p| ≤ 2/(p : ℝ)^5 := by
  have hpos : 0 < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
  have hs : 1 / (p : ℝ) ≤ 1/4 := by
    rw [div_le_iff₀ hpos]
    have hlarge : (100:ℝ) < p := by exact_mod_cast hp
    linarith
  simpa only [rem, div_pow, one_pow, mul_one_div] using
    remainder_at (x := 1/(p:ℝ)) (by positivity) hs

end MertensCert


namespace MertensCert

private theorem tail_step (x : ℝ) (hx : 0 < x) :
    2 / (x + 1) ^ 5 ≤ 1 / (2 * x ^ 4) - 1 / (2 * (x + 1) ^ 4) := by
  have hx1 : 0 < x + 1 := by positivity
  apply sub_nonneg.mp
  field_simp
  ring_nf
  positivity

theorem prime_tail (r : ℕ → ℝ) (hr : ∀ n : ℕ, 100 < n → |r n| ≤ 2 / (n : ℝ)^5) :
    Summable (fun p : Nat.Primes => r p.1) ∧
    |(∑' p : Nat.Primes, r p.1) - ∑ p ∈ (Finset.range 101).filter Nat.Prime, r p| ≤ 8e-9 := by
  classical
  let f : ℕ → ℝ := {p : ℕ | p.Prime}.indicator r
  let B (n : ℕ) : ℝ := 1 / (2 * ((n : ℝ) + 100)^4)
  have hpn (n : ℕ) : |f (n+101)| ≤ B n - B (n+1) := by
    have hstep := tail_step ((n : ℝ) + 100) (by positivity)
    have he : (n : ℝ) + 100 + 1 = (n : ℝ) + 101 := by ring
    have he' : (n : ℝ) + 1 + 100 = (n : ℝ) + 101 := by ring
    simp only [B, Nat.cast_add, Nat.cast_one, he', he] at *
    have he2 : 2 / ((n : ℝ) + 101)^5 ≤
        1 / (2 * ((n : ℝ) + 100)^4) - 1 / (2 * ((n : ℝ) + 101)^4) := hstep
    apply le_trans _ he2
    by_cases hp : (n + 101).Prime
    · simpa [f, hp] using hr (n+101) (by omega)
    · simp [f, hp]
      positivity
  have hfinite (N : ℕ) : ∑ k ∈ Finset.range N, |f (k+101)| ≤ 8e-9 := by
    calc
      _ ≤ ∑ k ∈ Finset.range N, (B k - B (k+1)) := Finset.sum_le_sum fun k _ => hpn k
      _ = B 0 - B N := Finset.sum_range_sub' B N
      _ ≤ B 0 := sub_le_self _ (by dsimp [B]; positivity)
      _ ≤ _ := by norm_num [B]
  have hsabs : Summable (fun k : ℕ => |f (k+101)|) :=
    summable_of_sum_range_le (fun _ => abs_nonneg _) hfinite
  have hstail : Summable (fun k : ℕ => f (k+101)) := by
    apply hsabs.of_norm_bounded
    simp
  have hs : Summable f := (summable_nat_add_iff 101).mp hstail
  refine ⟨summable_subtype_iff_indicator.mpr hs, ?_⟩
  have hsub : (∑' p : Nat.Primes, r p.1) = ∑' n, f n :=
    tsum_subtype {p : ℕ | p.Prime} r
  rw [hsub, ← hs.sum_add_tsum_nat_add 101]
  have hprefix : ∑ p ∈ Finset.range 101, f p = ∑ p ∈ (Finset.range 101).filter Nat.Prime, r p := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n _
    by_cases h : n.Prime <;> simp [f, h]
  rw [hprefix, add_sub_cancel_left]
  calc
    _ ≤ ∑' k : ℕ, |f (k+101)| := by simpa [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hstail.norm
    _ ≤ _ := Real.tsum_le_of_sum_range_le (fun _ => abs_nonneg _) hfinite

end MertensCert

namespace MertensCert

theorem cancellation : have x1 : ℝ := Real.eulerMascheroniConstant + ∑' (x1 : Nat.Primes), (Real.log ((1 : ℝ) - (1 : ℝ) / (↑(↑x1 : ℕ) : ℝ)) + (1 : ℝ) / (↑(↑x1 : ℕ) : ℝ)); have x2 : ℝ := ∑' (x2 : ℕ), (1 : ℝ) / (↑(x2 + (1 : ℕ)) : ℝ) ^ (3 : ℕ); have x3 : ℕ → ℝ := fun (x3 : ℕ) => Real.log ((1 : ℝ) - (1 : ℝ) / (↑x3 : ℝ)) + (1 : ℝ) / (↑x3 : ℝ) - Real.log ((1 : ℝ) - (1 : ℝ) / (↑x3 : ℝ) ^ (2 : ℕ)) / (2 : ℝ) - Real.log ((1 : ℝ) - (1 : ℝ) / (↑x3 : ℝ) ^ (3 : ℕ)) / (3 : ℝ); have x4 : ℝ := -(Real.log (Real.pi ^ (2 : ℕ) / (6 : ℝ)) / (2 : ℝ)) + ∑ x4 ∈ Finset.range (101 : ℕ) with Nat.Prime x4, x3 x4; |x1 - (Real.eulerMascheroniConstant - Real.log x2 / (3 : ℝ) + x4)| ≤ 8e-9 := by

  let Z := ∑' n : ℕ, (1 : ℝ) / ((n+1 : ℕ) : ℝ)^3
  let a (p : Nat.Primes) := Real.log (1 - 1 / (p.1 : ℝ)) + 1 / (p.1 : ℝ)
  let X := ∑' p : Nat.Primes, rem p.1
  let Y := ∑ p ∈ (Finset.range 101).filter Nat.Prime, rem p
  have htail := prime_tail rem (fun _ hn => rem_bound hn)
  have hsum : HasSum a (X + (-Real.log (Real.pi^2/6))/2 + (-Real.log Z)/3) := by
    apply ((htail.1.hasSum.add (log_two.div_const 2)).add (log_three.div_const 3)).congr_fun
    intro p
    dsimp [a, rem]
    ring
  change |Real.eulerMascheroniConstant + (∑' p, a p) -
        (Real.eulerMascheroniConstant - Real.log Z/3 + (-(Real.log (Real.pi^2/6)/2) + Y))| ≤ 8e-9
  rw [hsum.tsum_eq]
  convert htail.2 using 2
  change _ = X - Y
  ring

end MertensCert

theorem Conjectures.Cuts.Task298ca1546730f07e729c0762 : (0.261497 ≤ Real.eulerMascheroniConstant + ∑' (x1 : Nat.Primes), (Real.log ((1 : ℝ) - (1 : ℝ) / ↑↑x1) + (1 : ℝ) / ↑↑x1)) := by
  exact (SmallRangeInputs.assembleConstant MertensCert.cancellation
    SmallRangeInputs.gammaBound SmallRangeInputs.logZetaThree
    SmallRangeInputs.finiteCorrection).1
