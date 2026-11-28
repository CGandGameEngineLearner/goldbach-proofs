import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

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

theorem Conjectures.Cuts.Taskfe7ba8275bd444832d5c353b : (0.57721562 ≤ Real.eulerMascheroniConstant ∧ Real.eulerMascheroniConstant ≤ 0.57721571) := by
  obtain ⟨h₁, h₂⟩ := MertensGamma.gamma_bounds
  constructor <;> linarith
