import Mathlib

/- Original proof by Li2O0577. SPDX-License-Identifier: Apache-2.0.
Source: https://github.com/Li2O0577/goldbach-proofs/blob/8285b92599f89df7c3cbc8aba5ec45b5e0f7f3ae/research/checkpoint/packet-deep-late-levels/ChildPreview.lean
This adaptation replaces the final preview theorem with the assigned theorem
and its frozen statement. The proof and its auxiliary results are reproduced unchanged. -/

/- The change of variables for doubling follows the verified PacketUpperTailHalf module.
The weighted transfer inequality uses the identity cos(2x) = 2 cos(x)^2 - 1. -/
namespace QuarterPacket
noncomputable section
open Real Finset
private theorem pairHalves (f : ℝ → ℝ) (hf : Continuous f) :
    (∫ t in (0:ℝ)..1, f t) = ∫ t in (0:ℝ)..(1/2), f t + f (t+1/2) := by
  have hs : Continuous (fun t : ℝ => f (t+1/2)) := hf.comp (continuous_id.add continuous_const)
  rw [intervalIntegral.integral_add (hf.intervalIntegrable ..) (hs.intervalIntegrable ..),
    intervalIntegral.integral_comp_add_right]
  norm_num only [zero_add, show (1/2:ℝ)+1/2 = 1 by norm_num]
  exact (intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable ..) (hf.intervalIntegrable ..)).symm

private theorem scaleHalf (g : ℝ → ℝ) :
    (∫ t in (0:ℝ)..(1/2), g (2*t)) = (1/2) * ∫ t in (0:ℝ)..1, g t := by
  rw [intervalIntegral.integral_comp_mul_left g (by norm_num : (2:ℝ) ≠ 0)]
  norm_num

private theorem doublePeriod (g : ℝ → ℝ) (hc : Continuous g) (hp : Function.Periodic g 1) :
    (∫ t in (0:ℝ)..1, g (2*t)) = ∫ t in (0:ℝ)..1, g t := by
  have hd : Continuous (fun t : ℝ => g (2*t)) := hc.comp (continuous_const.mul continuous_id)
  rw [pairHalves _ hd]
  simp only [show ∀ t : ℝ, 2*(t+1/2) = 2*t+1 by intro t; ring, show ∀ y : ℝ, g (y+1) = g y from hp]
  rw [intervalIntegral.integral_add (hd.intervalIntegrable ..) (hd.intervalIntegrable ..), scaleHalf]
  ring

private def series (m : ℕ) (t : ℝ) := ∑ j ∈ Finset.range m, Real.cos (2*Real.pi*(2:ℝ)^j*t)
private def packet (m : ℕ) (t : ℝ) := ∑ j ∈ Finset.range m, Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t)

private theorem periodSeries (m : ℕ) : Function.Periodic (series m) 1 := by
  intro t
  unfold series
  apply Finset.sum_congr rfl
  intro j _
  have heq : 2*Real.pi*(2:ℝ)^j*(t+1) = 2*Real.pi*(2:ℝ)^j*t + ((2^j:ℕ):ℝ)*(2*Real.pi) := by
    push_cast
    ring
  rw [heq, Real.cos_add_nat_mul_two_pi]

private theorem seriesSucc (m : ℕ) (t : ℝ) :
    series (m+1) t = Real.cos (2*Real.pi*t) + series m (2*t) := by
  unfold series
  rw [Finset.sum_range_succ']
  simp only [pow_zero, mul_one]
  rw [add_comm (∑ j ∈ Finset.range m, _) _]
  apply congrArg (fun u : ℝ => Real.cos (2*Real.pi*t) + u)
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  rw [pow_succ]
  ring

private def wave (t : ℝ) := cos (2*Real.pi*t)
private def bal (t : ℝ) := exp ((2/19)*wave t)
private def a : ℝ := log 2 - 2/19
private def rate : ℝ := (19/16)*exp (-(1/19))

private theorem cosh_chord_sq {u : ℝ} (hu : |u| ≤ 1) :
    cosh (log 2*u) ≤ 1 + u^2/4 := by
  let b := log 2
  let f := fun (x : ℝ) (n : ℕ) => x^(2*n)/(↑((2*n).factorial):ℝ)
  have h₃ : ∀ x : ℝ, Summable (f x) := fun x => (Real.hasSum_cosh x).summable
  have hS (x : ℝ) : cosh x = 1 + ∑' n, f x (n+1) := by
    rw [Real.cosh_eq_tsum]
    change (∑' n, f x n) = _
    rw [← (h₃ x).sum_add_tsum_nat_add 1]
    simp [f]
  have hN : ∀ n : ℕ, f (b*u) (n+1) ≤ u^2 * f b (n+1) := by
    intro n
    have hu' : |u|^(2*n) ≤ 1 := pow_le_one₀ (abs_nonneg u) hu
    have hh : u^(2*(n+1)) ≤ u^2 := by
      calc
        _ = u^2 * (|u|^(2*n)) := by rw [show 2*(n+1)=2+2*n by omega,pow_add, (even_two_mul n).pow_abs]
        _ ≤ u^2*1 := mul_le_mul_of_nonneg_left hu' (sq_nonneg u)
        _ = _ := mul_one _
    unfold f
    rw [mul_pow, ← mul_div_assoc, mul_comm (u^2) (b^_)]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hh (by dsimp [b]; positivity)) (by positivity)
  have h := (summable_nat_add_iff 1).mpr (h₃ (b*u))
  have hh := h.tsum_le_tsum hN (((summable_nat_add_iff 1).mpr (h₃ b)).mul_left (u^2))
  rw [tsum_mul_left] at hh
  have hb : cosh b = 5/4 := by rw [Real.cosh_eq,Real.exp_neg,Real.exp_log (by norm_num : (0:ℝ)<2)]; norm_num
  rw [hS b] at hb
  change cosh (b*u) ≤ _
  rw [hS]
  nlinarith only [hh,hb,mul_eq_zero_of_left (show (∑' n, f b (n+1))-1/4=0 by linarith) (u^2)]

private theorem tilt (t : ℝ) : cosh (log 2*wave t) ≤ rate*bal (2*t) := by
  have hc := cosh_chord_sq (u := wave t) (abs_le.mpr ⟨Real.neg_one_le_cos _,Real.cos_le_one _⟩)
  have hd : wave (2*t) = 2*(wave t)^2-1 := by
    unfold wave
    rw [show 2*Real.pi*(2*t)=2*(2*Real.pi*t) by ring,Real.cos_two_mul]
  have he := Real.add_one_le_exp ((4/19)*((wave t)^2-3/4))
  have hs : -(1/19:ℝ)+(2/19)*wave (2*t) = (4/19)*((wave t)^2-3/4) := by rw [hd]; ring
  unfold rate bal
  rw [mul_assoc,←Real.exp_add,hs]
  linarith only [hc,he]

private theorem transfer (g : ℝ → ℝ) (hg : Continuous g) (hp : Function.Periodic g 1)
    (hn : ∀ t, 0 ≤ g t) :
    (∫ t in (0:ℝ)..1, exp (a*wave t)*bal t*g (2*t)) ≤
      rate*(∫ t in (0:ℝ)..1, bal t*g t) := by
  let f := fun t : ℝ => exp (log 2*wave t)*g (2*t)
  have hf : Continuous f := by dsimp [f,wave]; fun_prop
  have hs : Continuous (fun t : ℝ => f (t+1/2)) := hf.comp (continuous_id.add continuous_const)
  have hb : Continuous bal := by unfold bal wave; fun_prop
  have hr : Continuous (fun t : ℝ => 2*rate*(bal (2*t)*g (2*t))) := by fun_prop
  have eq (t : ℝ) : exp (a*wave t)*bal t*g (2*t)=f t := by
    dsimp [f,bal,a]; rw [←Real.exp_add]; congr 2; ring
  simp only [eq]
  rw [pairHalves f hf]
  calc
    _ ≤ ∫ t in (0:ℝ)..(1/2), 2*rate*(bal (2*t)*g (2*t)) := by
      apply intervalIntegral.integral_mono_on (by norm_num) ((hf.add hs).intervalIntegrable ..) (hr.intervalIntegrable ..)
      intro t _
      have flip : wave (t+1/2) = -wave t := by
        unfold wave; rw [show 2*Real.pi*(t+1/2)=2*Real.pi*t+Real.pi by ring,Real.cos_add_pi]
      change exp (log 2*wave t)*g (2*t)+exp (log 2*wave (t+1/2))*g (2*(t+1/2)) ≤ _
      rw [flip,show 2*(t+1/2)=2*t+1 by ring,hp (2*t),mul_neg,←add_mul]
      have h := tilt t
      rw [Real.cosh_eq] at h
      have h' : (exp (log 2 * wave t) + exp (-(log 2 * wave t))) ≤ 2*(rate*bal (2*t)) := by linarith
      exact (mul_le_mul_of_nonneg_right h' (hn _)).trans_eq (by ring)
    _ = _ := by rw [intervalIntegral.integral_const_mul,scaleHalf (fun t => bal t*g t)]; ring

private theorem bal_bound (t : ℝ) : exp (-(2/19)) ≤ bal t ∧ bal t ≤ exp (2/19) := by
  unfold bal
  have h := Real.neg_one_le_cos (2*Real.pi*t)
  have h' := Real.cos_le_one (2*Real.pi*t)
  unfold wave
  constructor <;> apply Real.exp_le_exp.mpr <;> linarith

private theorem moment (m : ℕ) :
    (∫ t in (0:ℝ)..1, exp (a*packet m t)) ≤ exp (4/19)*rate^m := by
  have hc (k : ℕ) : Continuous (fun t => exp (a*series k t)) := by unfold series; fun_prop
  have hb : Continuous bal := by unfold bal wave; fun_prop
  have hp (k : ℕ) : Function.Periodic (fun t => exp (a*series k t)) 1 :=
    fun t => congrArg (fun u : ℝ => exp (a*u)) (periodSeries k t)
  have h (k : ℕ) : (∫ t in (0:ℝ)..1, bal t * exp (a*series k t)) ≤ rate^k*exp (2/19) := by
    induction k with
    | zero =>
      simp only [series,Finset.range_zero,Finset.sum_empty,mul_zero,Real.exp_zero,mul_one,pow_zero,one_mul]
      calc
        _ ≤ ∫ _t in (0:ℝ)..1, exp (2/19) := intervalIntegral.integral_mono_on (by norm_num)
          (hb.intervalIntegrable ..) intervalIntegrable_const (fun t _ => (bal_bound t).2)
        _ = _ := by simp
    | succ k ih =>
      simp only [seriesSucc,mul_add,Real.exp_add]
      have z := transfer _ (hc k) (hp k) (fun t => (Real.exp_pos _).le)
      change (∫ t in (0:ℝ)..1, exp (a*Real.cos (2*Real.pi*t))*bal t*exp (a*series k (2*t))) ≤ _ at z
      simp_rw [show ∀ x y z : ℝ, x*(y*z)=y*x*z by intros; ring]
      exact z.trans ((mul_le_mul_of_nonneg_left ih (by dsimp [rate]; positivity)).trans_eq (by rw [pow_succ]; ring))
  have sh (t : ℝ) : packet m t = series m (2*t) := by
    unfold packet series; apply Finset.sum_congr rfl; intro j _; congr 1; rw [pow_succ]; ring
  simp only [sh]
  rw [doublePeriod _ (hc m) (hp m)]
  have hl (t : ℝ) : 1 ≤ exp (2/19)*bal t := by
    have z := mul_le_mul_of_nonneg_left (bal_bound t).1 (Real.exp_pos (2/19)).le
    rwa [←Real.exp_add,add_neg_cancel, Real.exp_zero] at z
  calc
    _ ≤ ∫ t in (0:ℝ)..1, exp (2/19)*(bal t*exp (a*series m t)) := by
      apply intervalIntegral.integral_mono_on (by norm_num) ((hc m).intervalIntegrable ..)
        ((continuous_const.mul (hb.mul (hc m))).intervalIntegrable ..)
      intro t _
      change exp (a*series m t) ≤ exp (2/19)*(bal t*exp (a*series m t))
      simpa only [one_mul,mul_assoc] using mul_le_mul_of_nonneg_right (hl t) (Real.exp_pos (a*series m t)).le
    _ ≤ exp (2/19)*(rate^m*exp (2/19)) := by
      rw [intervalIntegral.integral_const_mul]; exact mul_le_mul_of_nonneg_left (h m) (Real.exp_pos _).le
    _ = _ := by rw [show (4/19:ℝ)=2/19+2/19 by norm_num, Real.exp_add]; ring

theorem quarterTail (m : ℕ) :
    (∫ t in (0:ℝ)..1, if (m:ℝ)/2 < packet m t then (1:ℝ) else 0) ≤ 2*(21/25:ℝ)^m := by
  let A := {t : ℝ | (m:ℝ)/2 < packet m t}
  have hc : Continuous (packet m) := by unfold packet; fun_prop
  have hA : MeasurableSet A := (isOpen_lt (continuous_const : Continuous (fun _ : ℝ => (m:ℝ)/2)) hc).measurableSet
  have hi : IntervalIntegrable (A.indicator (fun _ => (1:ℝ))) MeasureTheory.volume (0:ℝ) 1 :=
    ⟨intervalIntegrable_const.1.indicator hA,intervalIntegrable_const.2.indicator hA⟩
  have ha : 0 < a := by unfold a; linarith [Real.log_two_gt_d9]
  have he : Continuous (fun t => exp (-a*(m:ℝ)/2) * exp (a*packet m t)) := by fun_prop
  change (∫ t in (0:ℝ)..1, A.indicator (fun _ => (1:ℝ)) t) ≤ _
  have compare : exp (-(log 2)/2) * (19/16:ℝ) ≤ 21/25 := by
    have hh : (exp (-(log 2)/2))^2 = 1/2 := by
      rw [sq, ←Real.exp_add,show -(log 2)/2 + -(log 2)/2 = -(log 2) by ring,
        Real.exp_neg,Real.exp_log (by norm_num : (0:ℝ)<2)]; norm_num
    nlinarith [sq_nonneg (exp (-(log 2)/2)-336/475)]
  have hC : exp (4/19) ≤ 2 := by
    rw [←Real.exp_log (by norm_num : (0:ℝ)<2)]
    apply Real.exp_le_exp.mpr; linarith [Real.log_two_gt_d9]
  calc
    _ ≤ ∫ t in (0:ℝ)..1, exp (-a*(m:ℝ)/2) * exp (a*packet m t) := by
      apply intervalIntegral.integral_mono_on (by norm_num) hi (he.intervalIntegrable ..)
      intro t _
      by_cases h : t ∈ A
      · rw [Set.indicator_of_mem h,←Real.exp_add]
        apply Real.one_le_exp_iff.mpr
        change (m:ℝ)/2 < packet m t at h
        nlinarith only [mul_pos ha (sub_pos.mpr h)]
      · rw [Set.indicator_of_notMem h]; positivity
    _ ≤ exp (-a*(m:ℝ)/2) * (exp (4/19)*rate^m) := by
      rw [intervalIntegral.integral_const_mul]; exact mul_le_mul_of_nonneg_left (moment m) (Real.exp_pos _).le
    _ = exp (4/19)*(exp (-(log 2)/2)*(19/16))^m := by
      have hh : exp (-a/2)*rate = exp (-(log 2)/2)*(19/16) := by
        unfold a rate
        rw [mul_left_comm,←Real.exp_add,show -(log 2-2/19)/2 + -(1/19) = -(log 2)/2 by ring,mul_comm]
      rw [←hh,mul_pow,←Real.exp_nat_mul,show (m:ℝ)*(-a/2) = -a*(m:ℝ)/2 by ring]; ring
    _ ≤ _ := mul_le_mul hC (pow_le_pow_left₀ (by positivity) compare m) (by positivity) (by norm_num)

end
end QuarterPacket

theorem Conjectures.Cuts.Taskc47543a5f4a9f338db5e8f4e : (∀ (x1 : ℕ), (∫ (x2 : ℝ) in (0 : ℝ)..(1 : ℝ), if ↑x1 / (2 : ℝ) < ∑ x3 ∈ Finset.range x1, Real.cos ((2 : ℝ) * Real.pi * (2 : ℝ) ^ (x3 + (1 : ℕ)) * x2) then (1 : ℝ) else (0 : ℝ)) ≤ (2 : ℝ) * (21 / 25 : ℝ) ^ x1) := QuarterPacket.quarterTail
