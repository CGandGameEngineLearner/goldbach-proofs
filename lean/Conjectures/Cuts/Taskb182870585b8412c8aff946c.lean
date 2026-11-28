import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Real

namespace EulerM0
open Filter
open scoped Topology
noncomputable section

private def weight (k : ℕ) (hk : 1 < k) : ℕ →*₀ ℝ where
  toFun n := 1 / (n : ℝ)^k
  map_zero' := by simp [show k ≠ 0 by omega]
  map_one' := by simp
  map_mul' a b := by simp [mul_pow, div_eq_mul_inv, mul_comm]

theorem log_product (k : ℕ) (hk : 1 < k) (z : ℝ) (hz : 0 < z)
    (hs : HasSum (fun n : ℕ => 1 / (n : ℝ)^k) z) :
    HasSum (fun p : Nat.Primes => -Real.log (1 - 1 / ((p : ℕ) : ℝ)^k)) (Real.log z) := by
  have hnorm : Summable (fun n => ‖weight k hk n‖) := by
    change Summable (fun n : ℕ => ‖1 / (n : ℝ)^k‖)
    exact hs.summable.norm
  have h := EulerProduct.eulerProduct_completely_multiplicative_hasProd hnorm
  change HasProd (fun p : Nat.Primes => (1 - 1 / ((p : ℕ) : ℝ)^k)⁻¹)
    (∑' n : ℕ, 1 / (n : ℝ)^k) at h
  rw [hs.tsum_eq] at h
  unfold HasProd at h
  have he := (Real.continuousAt_log hz.ne').tendsto.comp h
  have hpos (p : Nat.Primes) : 0 < 1 - 1 / ((p : ℕ) : ℝ)^k := by
    have hp : (1 : ℝ) < (p : ℕ) := by exact_mod_cast p.property.one_lt
    have ht := one_lt_pow₀ hp (by omega : k ≠ 0)
    exact sub_pos.mpr ((div_lt_one (zero_lt_one.trans ht)).mpr ht)
  unfold HasSum
  apply he.congr'
  filter_upwards with S
  change Real.log (∏ p ∈ S, (1 - 1 / ((p : ℕ) : ℝ)^k)⁻¹) = _
  rw [Real.log_prod (fun p _ => inv_ne_zero (hpos p).ne')]
  simp only [Real.log_inv]

def residual (x : ℝ) :=
  Real.log (1-x) + x - Real.log (1-x^2)/2 - Real.log (1-x^3)/3

private lemma expansion {u : ℝ} (hu : 0 ≤ u) (hu' : u ≤ 1/2) (n : ℕ) :
    |(∑ j ∈ Finset.range n, u^(j+1)/((j:ℝ)+1)) + Real.log (1-u)| ≤ 2*u^(n+1) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := u)
    (by rw [abs_of_nonneg hu]; linarith) n
  rw [abs_of_nonneg hu] at h
  apply h.trans
  apply (div_le_iff₀ (by linarith)).2
  nlinarith [mul_nonneg (by positivity : 0 ≤ u^(n+1)) (by linarith : 0 ≤ 1/2-u)]

theorem residual_small {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 1/2) :
    |residual x| ≤ 3*x^5 := by
  have xstep (i : ℕ) : x^(i+1) ≤ x^i/2 := by
    rw [pow_succ]; nlinarith [mul_nonneg (by positivity : 0 ≤ x^i) (by linarith : 0 ≤ 1/2-x)]
  have ha := expansion hx hx' 4
  have hb := expansion (sq_nonneg x) (by nlinarith [xstep 1] : x^2 ≤ 1/2) 2
  have hc := expansion (by positivity : 0 ≤ x^3) (by nlinarith [xstep 2, xstep 1] : x^3 ≤ 1/2) 1
  norm_num [Finset.sum_range_succ, ← pow_mul, abs_le] at ha hb hc
  unfold residual
  rw [abs_le]
  constructor <;> linarith [xstep 5]

end
end EulerM0


namespace EulerM0

private lemma power_tail_step (x : ℝ) (hx : 0 < x) :
    3 / (x+1)^5 ≤ (3/4) / x^4 - (3/4) / (x+1)^4 := by
  have hx' : 0 < x+1 := by linarith
  field_simp
  ring_nf
  nlinarith only [hx.le, sq_nonneg x, pow_nonneg hx.le 3, pow_nonneg hx.le 4, pow_nonneg hx.le 5, pow_nonneg hx.le 6, pow_nonneg hx.le 7, pow_nonneg hx.le 8]

theorem tail_100 (g : ℕ → ℝ) (hg : ∀ p : ℕ, Nat.Prime p → |g p| ≤ 3 / (p : ℝ)^5) :
    Summable (fun p : Nat.Primes => g p.val) ∧
    |(∑' p : Nat.Primes, g p.val) - ∑ p ∈ (Finset.range 101).filter Nat.Prime, g p| ≤
      (8 / 1000000000 : ℝ) := by
  classical
  let f : ℕ → ℝ := fun n => if Nat.Prime n then g n else 0
  let b : ℕ → ℝ := fun k => (3/4)/((k:ℝ)+100)^4
  have hb (k : ℕ) : 0 ≤ b k := by dsimp [b]; positivity
  have hstep (k : ℕ) : ‖f (k+101)‖ ≤ b k - b (k+1) := by
    have hbound : ‖f (k+101)‖ ≤ 3 / ((k:ℝ)+101)^5 := by
      dsimp only [f]
      by_cases hp : Nat.Prime (k+101)
      · simpa only [ite_eq_left hp, Real.norm_eq_abs, Nat.cast_add, Nat.cast_ofNat] using hg (k+101) hp
      · rw [ite_eq_right hp, norm_zero]; positivity
    apply hbound.trans
    convert power_tail_step ((k:ℝ)+100) (by positivity) using 1 <;> (try simp [b]) <;> ring_nf
  have hsum (N : ℕ) :
      (∑ k ∈ Finset.range N, ‖f (k+101)‖) ≤ b 0 - b N := by
    induction N with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      linarith [hstep n]
  have hle (N : ℕ) : (∑ k ∈ Finset.range N, ‖f (k+101)‖) ≤ b 0 := by
    linarith [hsum N, hb N]
  have hnorm : Summable (fun k : ℕ => ‖f (k+101)‖) :=
    summable_of_sum_range_le (fun _ => norm_nonneg _) hle
  have hf : Summable f := (summable_nat_add_iff 101).1 hnorm.of_norm
  let primes : Set ℕ := {n | Nat.Prime n}
  have hi : primes.indicator g = f := by
    funext n
    by_cases hp : n.Prime <;> simp [primes, Set.indicator, f, hp]
  constructor
  · exact (summable_subtype_iff_indicator (s := primes)).2 (hi ▸ hf)
  · have ht : (∑' p : Nat.Primes, g p.val) = ∑' n, f n := (tsum_subtype primes g).trans (congrArg tsum hi)
    have hs : (∑ p ∈ (Finset.range 101).filter Nat.Prime, g p) = ∑ n ∈ Finset.range 101, f n := by
      rw [Finset.sum_filter]
    rw [ht, hs, ← hf.sum_add_tsum_nat_add 101, add_sub_cancel_left, ← Real.norm_eq_abs]
    calc
      _ ≤ ∑' n : ℕ, ‖f (n+101)‖ := norm_tsum_le_tsum_norm hnorm
      _ ≤ b 0 := Real.tsum_le_of_sum_range_le (fun _ => norm_nonneg _) hle
      _ ≤ _ := by norm_num [b]

end EulerM0


namespace EulerM0

private lemma isolate_tail (a b c d e t s : ℝ)
    (hab : b = t - c/2 - d/3) (hh : |t-e| ≤ s) :
    |a+b-(a-d/3+(-(c/2)+e))| ≤ s := by
  rw [hab]
  convert hh using 1
  congr 1
  ring

set_option maxHeartbeats 1000000 in
theorem assembly : (have x1 : ℝ := Real.eulerMascheroniConstant + ∑' (x1 : Nat.Primes), (Real.log ((1 : ℝ) - (1 : ℝ) / (↑(↑x1 : ℕ) : ℝ)) + (1 : ℝ) / (↑(↑x1 : ℕ) : ℝ)); have x2 : ℝ := ∑' (x2 : ℕ), (1 : ℝ) / (↑(x2 + (1 : ℕ)) : ℝ) ^ (3 : ℕ); have x3 : ℕ → ℝ := fun (x3 : ℕ) => Real.log ((1 : ℝ) - (1 : ℝ) / (↑x3 : ℝ)) + (1 : ℝ) / (↑x3 : ℝ) - Real.log ((1 : ℝ) - (1 : ℝ) / (↑x3 : ℝ) ^ (2 : ℕ)) / (2 : ℝ) - Real.log ((1 : ℝ) - (1 : ℝ) / (↑x3 : ℝ) ^ (3 : ℕ)) / (3 : ℝ); have x4 : ℝ := -(Real.log (Real.pi ^ (2 : ℕ) / (6 : ℝ)) / (2 : ℝ)) + ∑ x4 ∈ Finset.range (101 : ℕ) with Nat.Prime x4, x3 x4; |x1 - (Real.eulerMascheroniConstant - Real.log x2 / (3 : ℝ) + x4)| ≤ 8e-9) := by
  let z := ∑' n : ℕ, (1:ℝ) / ((n+1 : ℕ) : ℝ)^3
  let g := fun n : ℕ => Real.log (1-1/(n:ℝ)) + 1/(n:ℝ) -
    Real.log (1-1/(n:ℝ)^2)/2 - Real.log (1-1/(n:ℝ)^3)/3
  let orig := fun p : Nat.Primes => Real.log (1-1/((p:ℕ):ℝ)) + 1/((p:ℕ):ℝ)
  have bound (p : ℕ) (hp : Nat.Prime p) : |g p| ≤ 3/(p:ℝ)^5 := by
    have h2 : (2:ℝ) ≤ p := by exact_mod_cast hp.two_le
    have hp0 : 0 < (p:ℝ) := by linarith
    have H := residual_small (x := 1/(p:ℝ)) (by positivity)
      ((div_le_iff₀ hp0).2 (by linarith))
    simpa only [g, residual, div_pow, one_pow, mul_one_div] using H
  obtain ⟨hr,hrem⟩ := tail_100 g bound
  have hZ := log_product 2 (by decide) (Real.pi ^ 2/6) (by positivity) hasSum_zeta_two
  have hS := Real.summable_one_div_nat_pow.mpr (by decide : 1 < 3)
  have hz : HasSum (fun n : ℕ => (1:ℝ)/(n:ℝ)^3) z := by
    have hs := hS.sum_add_tsum_nat_add 1
    have heq : z = ∑' n : ℕ, (1:ℝ)/(n:ℝ)^3 := by simpa only [z, Finset.sum_range_one, Nat.cast_zero, zero_pow (by decide : 3 ≠ 0), div_zero, zero_add] using hs
    rw [heq]
    exact hS.hasSum
  have hzpos : 0 < z := by
    rw [← hz.tsum_eq]
    exact hS.tsum_pos (fun _ => by positivity) 1 (by norm_num)
  have hZ3 := log_product 3 (by decide) z hzpos hz
  have hs : HasSum orig (((∑' p : Nat.Primes, g p.val) - Real.log (Real.pi^2/6)/2) - Real.log z/3) := by
    apply ((hr.hasSum.sub (hZ.div_const 2)).sub (hZ3.div_const 3)).congr_fun
    intro p
    dsimp [orig,g]
    ring
  change |Real.eulerMascheroniConstant + (∑' p, orig p) - (Real.eulerMascheroniConstant -
    Real.log z/3 + (-(Real.log (Real.pi^2/6)/2) + ∑ p ∈ (Finset.range 101).filter Nat.Prime, g p))| ≤ _
  apply isolate_tail _ _ _ _ _ _ _ hs.tsum_eq
  exact hrem.trans (by norm_num : (8 / 1000000000 : ℝ) ≤ 8e-9)

end EulerM0

namespace M0Finite
open Finset

def approx (q : ℚ) : ℚ :=
  2 * ∑ i ∈ Finset.range 15, ((q-1)/(q+1))^(2*i+1) / (2*(i:ℚ)+1)

theorem log_bounds (q : ℚ) (hq : 1 ≤ q) (h2 : q ≤ 2) :
    (approx q : ℝ) ≤ Real.log (q:ℝ) ∧ Real.log (q:ℝ) ≤ (approx q:ℝ) + 1/1000000000000 := by
  let x := ((q:ℝ)-1)/(q+1)
  have hq' : (1:ℝ) ≤ q := by exact_mod_cast hq
  have h2' : (q:ℝ) ≤ 2 := by exact_mod_cast h2
  have hp : (0:ℝ) < q+1 := by linarith
  have hx : 0 ≤ x := div_nonneg (by linarith) hp.le
  have hx3 : x ≤ 1/3 := (div_le_iff₀ hp).2 (by linarith)
  have hx1 : x < 1 := by linarith
  have hid : (1+x)/(1-x) = q := by
    apply (div_eq_iff (by linarith : 1-x ≠ 0)).2
    dsimp [x]
    field_simp
    ring
  have hlo := Real.sum_range_le_log_div hx hx1 15
  have hhi := Real.log_div_le_sum_range_add hx hx1 15
  rw [hid] at hlo hhi
  have hv : (approx q : ℝ) = 2 * ∑ i ∈ range 15, x ^ (2*i+1) / (2*(i:ℝ)+1) := by
    unfold approx
    push_cast
    rfl
  rw [hv]
  constructor
  · linarith
  · have hs := pow_le_pow_left₀ hx hx3 2
    have hh := pow_le_pow_left₀ hx hx3 31
    have err : x^31 / (1-x^2) ≤ 1/2000000000000 := by
      apply (div_le_iff₀ (by norm_num at hs; linarith)).2
      norm_num at hh hs
      linarith
    norm_num only at hhi
    linarith

noncomputable def term (p : ℕ) : ℝ :=
  Real.log (1 - 1/(p:ℝ)) + 1/(p:ℝ) - Real.log (1 - 1/(p:ℝ)^2)/2 -
    Real.log (1 - 1/(p:ℝ)^3)/3

def quotR (n : ℕ) : ℚ := (n:ℚ)/(n-1)

theorem neglog (n : ℕ) (hn : 2 ≤ n) :
    -(approx (quotR n):ℝ) - 1/1000000000000 ≤ Real.log (1 - 1/(n:ℝ)) ∧
    Real.log (1 - 1/(n:ℝ)) ≤ -(approx (quotR n):ℝ) := by
  have hn' : (2:ℚ) ≤ n := by exact_mod_cast hn
  have hp : 0 < (n:ℚ)-1 := by linarith
  obtain ⟨hlo,hhi⟩ := log_bounds (quotR n) ((le_div_iff₀ hp).2 (by linarith))
    ((div_le_iff₀ hp).2 (by linarith))
  have hn2 : (2:ℝ) ≤ n := by exact_mod_cast hn
  have eq : 1-1/(n:ℝ) = ((quotR n:ℚ):ℝ)⁻¹ := by
    unfold quotR
    push_cast
    rw [inv_div]
    field_simp
  rw [eq, Real.log_inv]
  constructor <;> linarith

def termApprox (p : ℕ) : ℚ := -(approx (quotR p)) + 1/(p:ℚ) +
  approx (quotR (p^2))/2 + approx (quotR (p^3))/3

theorem term_bounds (p : ℕ) (hp : 2 ≤ p) :
    (termApprox p:ℝ) - 2/1000000000000 ≤ term p ∧
    term p ≤ (termApprox p:ℝ) + 2/1000000000000 := by
  have h1 := neglog p hp
  have hp1 : p ≤ p^2 := Nat.le_self_pow (by decide) _
  have hp2 : p ≤ p^3 := Nat.le_self_pow (by decide) _
  have h2 := neglog (p^2) (hp.trans hp1)
  have h3 := neglog (p^3) (hp.trans hp2)
  push_cast at h2 h3
  unfold termApprox term
  push_cast
  constructor <;> linarith


private theorem bound_transfer (p : ℕ) (l u : ℤ) (hp : 2 ≤ p)
    (hl : (l:ℚ)/1000000000000 ≤ termApprox p - 2/1000000000000)
    (hu : termApprox p + 2/1000000000000 ≤ (u:ℚ)/1000000000000) :
    (l:ℝ)/1000000000000 ≤ term p ∧ term p ≤ (u:ℝ)/1000000000000 := by
  constructor
  · refine le_trans ?_ (term_bounds p hp).1
    have h := (Rat.cast_le (K := ℝ)).mpr hl
    push_cast at h
    exact h
  · refine le_trans (term_bounds p hp).2 ?_
    have h := (Rat.cast_le (K := ℝ)).mpr hu
    push_cast at h
    exact h

private theorem cert2 : (-4795680129:ℝ)/1000000000000 ≤ term 2 ∧ term 2 ≤ (-4795680122:ℝ)/1000000000000 :=
  bound_transfer 2 (-4795680129) (-4795680122) (by decide) (by decide +kernel) (by decide +kernel)
private theorem cert3 : (-660147623:ℝ)/1000000000000 ≤ term 3 ∧ term 3 ≤ (-660147616:ℝ)/1000000000000 :=
  bound_transfer 3 (-660147623) (-660147616) (by decide) (by decide +kernel) (by decide +kernel)
private theorem cert5 : (-55163492:ℝ)/1000000000000 ≤ term 5 ∧ term 5 ≤ (-55163485:ℝ)/1000000000000 :=
  bound_transfer 5 (-55163492) (-55163485) (by decide) (by decide +kernel) (by decide +kernel)
private theorem cert7 : (-10656671:ℝ)/1000000000000 ≤ term 7 ∧ term 7 ≤ (-10656664:ℝ)/1000000000000 :=
  bound_transfer 7 (-10656671) (-10656664) (by decide) (by decide +kernel) (by decide +kernel)
private theorem cert11 : (-1155098:ℝ)/1000000000000 ≤ term 11 ∧ term 11 ≤ (-1155091:ℝ)/1000000000000 :=
  bound_transfer 11 (-1155098) (-1155091) (by decide) (by decide +kernel) (by decide +kernel)
private theorem cert13 : (-506409:ℝ)/1000000000000 ≤ term 13 ∧ term 13 ≤ (-506402:ℝ)/1000000000000 :=
  bound_transfer 13 (-506409) (-506402) (by decide) (by decide +kernel) (by decide +kernel)
private theorem cert17 : (-134306:ℝ)/1000000000000 ≤ term 17 ∧ term 17 ≤ (-134299:ℝ)/1000000000000 :=
  bound_transfer 17 (-134306) (-134299) (by decide) (by decide +kernel) (by decide +kernel)
private theorem cert19 : (-77393:ℝ)/1000000000000 ≤ term 19 ∧ term 19 ≤ (-77386:ℝ)/1000000000000 :=
  bound_transfer 19 (-77393) (-77386) (by decide) (by decide +kernel) (by decide +kernel)
private theorem cert23 : (-29993:ℝ)/1000000000000 ≤ term 23 ∧ term 23 ≤ (-29986:ℝ)/1000000000000 :=
  bound_transfer 23 (-29993) (-29986) (by decide) (by decide +kernel) (by decide +kernel)
private theorem cert29 : (-9482:ℝ)/1000000000000 ≤ term 29 ∧ term 29 ≤ (-9475:ℝ)/1000000000000 :=
  bound_transfer 29 (-9482) (-9475) (by decide) (by decide +kernel) (by decide +kernel)
private theorem cert31 : (-6807:ℝ)/1000000000000 ≤ term 31 ∧ term 31 ≤ (-6800:ℝ)/1000000000000 :=
  bound_transfer 31 (-6807) (-6800) (by decide) (by decide +kernel) (by decide +kernel)
private theorem cert37 : (-2824:ℝ)/1000000000000 ≤ term 37 ∧ term 37 ≤ (-2817:ℝ)/1000000000000 :=
  bound_transfer 37 (-2824) (-2817) (by decide) (by decide +kernel) (by decide +kernel)
private theorem cert41 : (-1695:ℝ)/1000000000000 ≤ term 41 ∧ term 41 ≤ (-1688:ℝ)/1000000000000 :=
  bound_transfer 41 (-1695) (-1688) (by decide) (by decide +kernel) (by decide +kernel)
private theorem cert43 : (-1338:ℝ)/1000000000000 ≤ term 43 ∧ term 43 ≤ (-1331:ℝ)/1000000000000 :=
  bound_transfer 43 (-1338) (-1331) (by decide) (by decide +kernel) (by decide +kernel)
private theorem cert47 : (-860:ℝ)/1000000000000 ≤ term 47 ∧ term 47 ≤ (-853:ℝ)/1000000000000 :=
  bound_transfer 47 (-860) (-853) (by decide) (by decide +kernel) (by decide +kernel)
private theorem cert53 : (-474:ℝ)/1000000000000 ≤ term 53 ∧ term 53 ≤ (-467:ℝ)/1000000000000 :=
  bound_transfer 53 (-474) (-467) (by decide) (by decide +kernel) (by decide +kernel)
private theorem cert59 : (-279:ℝ)/1000000000000 ≤ term 59 ∧ term 59 ≤ (-272:ℝ)/1000000000000 :=
  bound_transfer 59 (-279) (-272) (by decide) (by decide +kernel) (by decide +kernel)
private theorem cert61 : (-237:ℝ)/1000000000000 ≤ term 61 ∧ term 61 ≤ (-230:ℝ)/1000000000000 :=
  bound_transfer 61 (-237) (-230) (by decide) (by decide +kernel) (by decide +kernel)
private theorem cert67 : (-150:ℝ)/1000000000000 ≤ term 67 ∧ term 67 ≤ (-143:ℝ)/1000000000000 :=
  bound_transfer 67 (-150) (-143) (by decide) (by decide +kernel) (by decide +kernel)
private theorem cert71 : (-113:ℝ)/1000000000000 ≤ term 71 ∧ term 71 ≤ (-106:ℝ)/1000000000000 :=
  bound_transfer 71 (-113) (-106) (by decide) (by decide +kernel) (by decide +kernel)
private theorem cert73 : (-99:ℝ)/1000000000000 ≤ term 73 ∧ term 73 ≤ (-92:ℝ)/1000000000000 :=
  bound_transfer 73 (-99) (-92) (by decide) (by decide +kernel) (by decide +kernel)
private theorem cert79 : (-68:ℝ)/1000000000000 ≤ term 79 ∧ term 79 ≤ (-61:ℝ)/1000000000000 :=
  bound_transfer 79 (-68) (-61) (by decide) (by decide +kernel) (by decide +kernel)
private theorem cert83 : (-54:ℝ)/1000000000000 ≤ term 83 ∧ term 83 ≤ (-47:ℝ)/1000000000000 :=
  bound_transfer 83 (-54) (-47) (by decide) (by decide +kernel) (by decide +kernel)
private theorem cert89 : (-39:ℝ)/1000000000000 ≤ term 89 ∧ term 89 ≤ (-32:ℝ)/1000000000000 :=
  bound_transfer 89 (-39) (-32) (by decide) (by decide +kernel) (by decide +kernel)
private theorem cert97 : (-27:ℝ)/1000000000000 ≤ term 97 ∧ term 97 ≤ (-20:ℝ)/1000000000000 :=
  bound_transfer 97 (-27) (-20) (by decide) (by decide +kernel) (by decide +kernel)

private theorem piLog : (49770030245:ℝ)/100000000000 ≤ Real.log (Real.pi^2/6) ∧
    Real.log (Real.pi^2/6) ≤ (49770030249:ℝ)/100000000000 := by
  let a : ℚ := 164493406683/100000000000
  let b : ℚ := 164493406686/100000000000
  have ha : (a:ℝ) ≤ Real.pi^2/6 := by
    have h := pow_le_pow_left₀ (by norm_num) Real.pi_gt_d20.le 2
    norm_num [a] at *
    linarith
  have hb : Real.pi^2/6 ≤ (b:ℝ) := by
    have h := pow_le_pow_left₀ Real.pi_pos.le Real.pi_lt_d20.le 2
    norm_num [b] at *
    linarith
  have hla := (log_bounds a (by norm_num [a]) (by norm_num [a])).1
  have hlb := (log_bounds b (by norm_num [b]) (by norm_num [b])).2
  have h1 : (49770030245:ℚ)/100000000000 ≤ approx a := by decide +kernel
  have h2 : approx b + 1/1000000000000 ≤ (49770030249:ℚ)/100000000000 := by decide +kernel
  constructor
  · apply le_trans _ (Real.log_le_log (by norm_num [a]) ha)
    have h := (Rat.cast_le (K := ℝ)).mpr h1
    push_cast at h
    exact h.trans hla
  · apply le_trans (Real.log_le_log (by positivity) hb)
    have h := (Rat.cast_le (K := ℝ)).mpr h2
    push_cast at h
    exact hlb.trans h

theorem proof : have x1 : ℕ → ℝ := fun (x1 : ℕ) => Real.log ((1 : ℝ) - (1 : ℝ) / (↑x1 : ℝ)) + (1 : ℝ) / (↑x1 : ℝ) - Real.log ((1 : ℝ) - (1 : ℝ) / (↑x1 : ℝ) ^ (2 : ℕ)) / (2 : ℝ) - Real.log ((1 : ℝ) - (1 : ℝ) / (↑x1 : ℝ) ^ (3 : ℕ)) / (3 : ℝ); have x2 : ℝ := -(Real.log (Real.pi ^ (2 : ℕ) / (6 : ℝ)) / (2 : ℝ)) + ∑ x2 ∈ Finset.range (101 : ℕ) with Nat.Prime x2, x1 x2; -0.25437377 ≤ x2 ∧ x2 ≤ -0.25437368 := by
  let val := -(Real.log (Real.pi^2/6)/2) + ∑ p ∈ (Finset.range 101).filter Nat.Prime, term p
  change -0.25437377 ≤ val ∧ val ≤ -0.25437368
  have heq : ((Finset.range 101).filter Nat.Prime) = {2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97} := by decide +kernel
  dsimp only [val]
  rw [heq]
  norm_num only [Finset.sum_insert, Finset.sum_singleton, Finset.mem_insert, Finset.mem_singleton, or_false, false_or, not_false_eq_true]
  constructor
  · linarith only [piLog.2, cert2.1, cert3.1, cert5.1, cert7.1, cert11.1, cert13.1, cert17.1, cert19.1, cert23.1, cert29.1, cert31.1, cert37.1, cert41.1, cert43.1, cert47.1, cert53.1, cert59.1, cert61.1, cert67.1, cert71.1, cert73.1, cert79.1, cert83.1, cert89.1, cert97.1]
  · linarith only [piLog.1, cert2.2, cert3.2, cert5.2, cert7.2, cert11.2, cert13.2, cert17.2, cert19.2, cert23.2, cert29.2, cert31.2, cert37.2, cert41.2, cert43.2, cert47.2, cert53.2, cert59.2, cert61.2, cert67.2, cert71.2, cert73.2, cert79.2, cert83.2, cert89.2, cert97.2]
end M0Finite

open Filter Finset
open scoped Topology

namespace MertensZeta

private noncomputable def term (n : ℕ) : ℝ := 1 / ((n+1 : ℕ) : ℝ)^3
private noncomputable def total : ℝ := ∑' n, term n
private noncomputable def upto (N : ℕ) : ℝ := ∑ n ∈ range N, term n
private noncomputable def upper (N : ℕ) : ℝ := upto N + ((1 : ℝ)/N)^2

private lemma summable_terms : Summable term :=
  (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.mpr (by decide : 1 < 3))

private lemma bracket (N : ℕ) (hN : 0 < N) :
    upto N ≤ total ∧ total ≤ upper N := by
  have U : Tendsto upper atTop (𝓝 total) := by
    change Tendsto (fun n : ℕ => upto n + ((1 : ℝ)/n)^2) _ _
    simpa only [upto, total, zero_pow (by decide : 2 ≠ 0), add_zero] using
      summable_terms.hasSum.tendsto_sum_nat.add ((tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).pow 2)
  have step (k : ℕ) (hk : 0 < k) : upper (k+1) ≤ upper k := by
    have hk' : 0 < (k : ℝ) := by exact_mod_cast hk
    simp only [upper, upto, sum_range_succ, term, Nat.cast_add_one]
    field_simp
    nlinarith
  refine ⟨summable_terms.sum_le_tsum _ (fun n _ => by dsimp [term]; positivity), ?_⟩
  apply le_of_tendsto U
  filter_upwards [eventually_ge_atTop N] with k hk
  induction k, hk using Nat.le_induction with
  | base => exact le_rfl
  | succ j hj ih => exact (step j (hN.trans_le hj)).trans ih

private def truncSum : ℕ → ℕ
  | 0 => 0
  | n+1 => truncSum n + 10^14 / (n+1)^3

private lemma rounded (n : ℕ) :
    (truncSum n : ℝ) ≤ (10^14 : ℝ) * upto n ∧
    (10^14 : ℝ) * upto n ≤ (truncSum n : ℝ) + n := by
  induction n with
  | zero => simp [truncSum, upto]
  | succ n ih =>
    let q : ℕ := 10^14 / (n+1)^3
    have hn : 0 < ((n : ℝ) + 1)^3 := by positivity
    have hleft : (q : ℝ) ≤ (10^14 : ℝ) / (n+1)^3 := by
      rw [le_div_iff₀ hn]
      exact_mod_cast Nat.div_mul_le_self (10^14) ((n+1)^3)
    have hright : (10^14 : ℝ) / (n+1)^3 ≤ (q : ℝ) + 1 := by
      rw [div_le_iff₀ hn, mul_comm]
      exact_mod_cast (Nat.lt_mul_div_succ (10^14) (pow_pos (Nat.succ_pos n) 3)).le
    change (↑(truncSum n + q) : ℝ) ≤ _ ∧ _ ≤ (↑(truncSum n + q) : ℝ) + _
    have he : upto (n+1) = upto n + 1 / ((n:ℝ)+1)^3 := by
      simp [upto, term, sum_range_succ]
    simp only [he, Nat.cast_add, Nat.cast_one, mul_add, mul_one_div]
    constructor <;> linarith only [ih.1,ih.2,hleft,hright]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem truncated : truncSum 8192 = 120205689566938 := by decide +kernel

private lemma zeta_bracket : (1.20205689 : ℝ) ≤ total ∧ total ≤ (1.20205692 : ℝ) := by
  obtain ⟨hA,hB⟩ := bracket 8192 (by decide)
  obtain ⟨hF,hG⟩ := rounded 8192
  rw [truncated] at hF hG
  norm_num only [upper, Nat.cast_ofNat] at hB hF hG
  constructor <;> linarith only [hA,hB,hF,hG]

theorem log_bounds : (0.18403413 : ℝ) ≤ Real.log total ∧ Real.log total ≤ 0.18403422 := by
  obtain ⟨hL,hU⟩ := zeta_bracket
  have hz : 0 < total := lt_of_lt_of_le (by norm_num) hL
  constructor
  · apply le_trans _ (Real.log_le_log (by norm_num : (0:ℝ) < 1.20205689) hL)
    have h := Real.sum_range_le_log_div (x := 20205689 / 220205689) (by norm_num) (by norm_num) 5
    norm_num [sum_range_succ] at h ⊢
    linarith
  · apply le_trans (Real.log_le_log hz hU)
    have h := Real.log_div_le_sum_range_add (x := 20205692 / 220205692) (by norm_num) (by norm_num) 5
    norm_num [sum_range_succ] at h ⊢
    linarith

end MertensZeta

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
namespace MertensNumeric

-- The four analytic and numerical inputs follow the decomposition by
-- bz7777777 in goldbach-proofs pull request 4829.
private lemma collect (m γ z c : ℝ) (ht : |m - (γ-z/3+c)| ≤ 8e-9)
    (hγ : 0.57721565 ≤ γ ∧ γ ≤ 0.57721568)
    (hz : 0.18403413 ≤ z ∧ z ≤ 0.18403422)
    (hc : -0.25437377 ≤ c ∧ c ≤ -0.25437368) :
    0.261497 ≤ m ∧ m ≤ 0.261498 := by
  obtain ⟨h₁,h₂⟩ := abs_le.mp ht
  constructor <;> linarith only [h₁,h₂,hγ.1,hγ.2,hz.1,hz.2,hc.1,hc.2]

theorem constant : (have x1 : ℝ := Real.eulerMascheroniConstant + ∑' (x1 : Nat.Primes), (Real.log ((1 : ℝ) - (1 : ℝ) / ↑↑x1) + (1 : ℝ) / ↑↑x1); 0.261497 ≤ x1 ∧ x1 ≤ 0.261498) := by
  let z := ∑' n : ℕ, (1:ℝ)/((n+1:ℕ):ℝ)^3
  let m := Real.eulerMascheroniConstant + ∑' p : Nat.Primes,
    (Real.log (1-1/((p:ℕ):ℝ)) + 1/((p:ℕ):ℝ))
  let c := -(Real.log (Real.pi^2/6)/2) + ∑ p ∈ (Finset.range 101).filter Nat.Prime,
    (Real.log (1-1/(p:ℝ)) + 1/(p:ℝ) - Real.log (1-1/(p:ℝ)^2)/2 -
      Real.log (1-1/(p:ℝ)^3)/3)
  exact collect m Real.eulerMascheroniConstant (Real.log z) c EulerM0.assembly
    MertensGamma.gamma_bounds MertensZeta.log_bounds M0Finite.proof

end MertensNumeric

theorem Conjectures.Cuts.Taskb182870585b8412c8aff946c : (have x1 : ℝ := Real.eulerMascheroniConstant + ∑' (x1 : Nat.Primes), (Real.log ((1 : ℝ) - (1 : ℝ) / ↑↑x1) + (1 : ℝ) / ↑↑x1); 0.261497 ≤ x1 ∧ x1 ≤ 0.261498) := by
  exact MertensNumeric.constant
