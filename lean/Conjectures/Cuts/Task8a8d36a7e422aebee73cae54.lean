import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Nat.Prime.Basic
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

theorem Conjectures.Cuts.Task8a8d36a7e422aebee73cae54 : (have x1 : ℝ := Real.eulerMascheroniConstant + ∑' (x1 : Nat.Primes), (Real.log ((1 : ℝ) - (1 : ℝ) / (↑(↑x1 : ℕ) : ℝ)) + (1 : ℝ) / (↑(↑x1 : ℕ) : ℝ)); have x2 : ℝ := ∑' (x2 : ℕ), (1 : ℝ) / (↑(x2 + (1 : ℕ)) : ℝ) ^ (3 : ℕ); have x3 : ℕ → ℝ := fun (x3 : ℕ) => Real.log ((1 : ℝ) - (1 : ℝ) / (↑x3 : ℝ)) + (1 : ℝ) / (↑x3 : ℝ) - Real.log ((1 : ℝ) - (1 : ℝ) / (↑x3 : ℝ) ^ (2 : ℕ)) / (2 : ℝ) - Real.log ((1 : ℝ) - (1 : ℝ) / (↑x3 : ℝ) ^ (3 : ℕ)) / (3 : ℝ); have x4 : ℝ := -(Real.log (Real.pi ^ (2 : ℕ) / (6 : ℝ)) / (2 : ℝ)) + ∑ x4 ∈ Finset.range (101 : ℕ) with Nat.Prime x4, x3 x4; |x1 - (Real.eulerMascheroniConstant - Real.log x2 / (3 : ℝ) + x4)| ≤ 8e-9) := by
  exact EulerM0.assembly
