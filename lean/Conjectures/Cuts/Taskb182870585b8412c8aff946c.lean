import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.Tactic


open Filter Finset
open scoped Topology

namespace DotMertens

private theorem gamma_step (t : ℝ) (ht : 0 < t) :
    1 / (2 * (t + 1) * (t + 2)) ≤ Real.log ((t+1)/t) - 1/(t+1) ∧
    Real.log ((t+1)/t) - 1/(t+1) ≤ 1/(2*t*(t+1)) := by
  let u : ℝ := 1 / (2*t+1)
  have h0 : 0 ≤ u := by dsimp [u]; positivity
  have hu : u < 1 := by
    dsimp [u]
    apply (div_lt_iff₀ (by positivity : 0 < 2 * t + 1)).mpr
    linarith
  have he : (1+u)/(1-u) = (t+1)/t := by
    dsimp [u]
    field_simp
    <;> ring
  have lo := Real.sum_range_le_log_div h0 hu 1
  have hi := Real.log_div_le_sum_range_add h0 hu 1
  simp only [sum_range_one, Nat.mul_zero, zero_add, pow_one] at lo hi
  rw [he] at lo hi
  constructor
  · calc
      1 / (2 * (t + 1) * (t + 2)) ≤ 2*u - 1/(t+1) := by
        dsimp [u]
        field_simp [show t + 1 ≠ 0 by positivity, show t + 2 ≠ 0 by positivity,
          show 2*t+1 ≠ 0 by positivity]
        nlinarith
      _ ≤ _ := by linarith
  · calc
      Real.log ((t+1)/t) - 1/(t+1) ≤ 2*(u + u^3/(1-u^2)) - 1/(t+1) := by linarith
      _ = _ := by
        have hne : 1-u^2 ≠ 0 := by nlinarith [mul_nonneg h0 (sub_nonneg.mpr hu.le)]
        dsimp [u] at hne ⊢
        field_simp [hne, show t + 1 ≠ 0 by positivity, show 2*t+1 ≠ 0 by positivity,
          show t ≠ 0 by positivity]
        have hD : t * 4 + t ^ 2 * 4 ≠ 0 := by positivity
        ring_nf
        field_simp [hD]
        <;> ring

private noncomputable def harmonicLog (n : ℕ) : ℝ := harmonic n - Real.log n
private noncomputable def gammaLo (n : ℕ) : ℝ :=
  harmonicLog (n+1) - (2 * ((n:ℝ)+1))⁻¹
private noncomputable def gammaHi (n : ℕ) : ℝ :=
  harmonicLog (n+1) - (2 * ((n:ℝ)+2))⁻¹

private theorem harmonicLog_step (n : ℕ) :
    harmonicLog (n+1+1) - harmonicLog (n+1) =
      -(Real.log ((((n:ℝ)+1)+1)/((n:ℝ)+1)) - 1/(((n:ℝ)+1)+1)) := by
  simp only [harmonicLog, harmonic_succ, Rat.cast_add, Rat.cast_inv, Rat.cast_natCast,
    Rat.cast_one, Nat.cast_add, Nat.cast_one]
  rw [Real.log_div (by positivity) (by positivity)]
  ring

private theorem gammaBracket (n : ℕ) :
    gammaLo n ≤ Real.eulerMascheroniConstant ∧
      Real.eulerMascheroniConstant ≤ gammaHi n := by
  have hH : Tendsto (fun n : ℕ => harmonicLog (n+1)) atTop
      (𝓝 Real.eulerMascheroniConstant) :=
    Real.tendsto_harmonic_sub_log.comp (tendsto_add_atTop_nat 1)
  have hInv (c : ℝ) : Tendsto (fun n : ℕ => (2 * ((n:ℝ)+c))⁻¹) atTop (𝓝 0) := by
    have hA : Tendsto (fun n : ℕ => (n:ℝ) + c) atTop atTop :=
      tendsto_atTop_add_const_right atTop c tendsto_natCast_atTop_atTop
    have hB : Tendsto (fun n : ℕ => 2 * ((n:ℝ) + c)) atTop atTop :=
      hA.const_mul_atTop (by norm_num)
    exact tendsto_inv_atTop_zero.comp hB
  have hL : Tendsto gammaLo atTop (𝓝 Real.eulerMascheroniConstant) := by
    unfold gammaLo; simpa only [sub_zero] using hH.sub (hInv 1)
  have hU : Tendsto gammaHi atTop (𝓝 Real.eulerMascheroniConstant) := by
    unfold gammaHi; simpa only [sub_zero] using hH.sub (hInv 2)
  have hML : Monotone gammaLo := by
    apply monotone_nat_of_le_succ
    intro k
    have hs := harmonicLog_step k
    obtain ⟨_, h⟩ := gamma_step ((k:ℝ)+1) (by positivity)
    have hAlg : (2 * ((k:ℝ)+1))⁻¹ - (2 * (((k:ℝ)+1)+1))⁻¹ =
        1 / (2*((k:ℝ)+1)*(((k:ℝ)+1)+1)) := by
      field_simp [show (k:ℝ)+1 ≠ 0 by positivity,
        show (k:ℝ)+1+1 ≠ 0 by positivity]
      <;> ring
    simp only [gammaLo, Nat.cast_add, Nat.cast_one]
    linarith
  have hMU : Antitone gammaHi := by
    apply antitone_nat_of_succ_le
    intro k
    have hs := harmonicLog_step k
    obtain ⟨h, _⟩ := gamma_step ((k:ℝ)+1) (by positivity)
    have hAlg : (2 * ((k:ℝ)+2))⁻¹ - (2 * (((k:ℝ)+1)+2))⁻¹ =
        1 / (2*(((k:ℝ)+1)+1)*(((k:ℝ)+1)+2)) := by
      rw [show (k:ℝ)+1+1 = (k:ℝ)+2 by ring]
      field_simp [show (k:ℝ)+2 ≠ 0 by positivity,
        show (k:ℝ)+1+2 ≠ 0 by positivity]
      <;> ring
    simp only [gammaHi, Nat.cast_add, Nat.cast_one]
    linarith
  exact ⟨hML.ge_of_tendsto hL n, hMU.le_of_tendsto hU n⟩

end DotMertens

open Filter Finset
open scoped Topology
namespace DotMertens

private noncomputable def realZeta (k : ℕ) : ℝ := ∑' n : ℕ, ((n:ℝ)^k)⁻¹

private theorem realZeta_pos {k : ℕ} (hk : 1 < k) : 0 < realZeta k := by
  have hs := Real.summable_nat_pow_inv.mpr hk
  have h : ((1:ℝ)^k)⁻¹ ≤ realZeta k := by
    apply hs.le_tsum 1
    exact fun _ _ => by positivity
  simp at h
  linarith

private theorem log_euler {k : ℕ} (hk : 1 < k) :
    HasSum (fun p : Nat.Primes => -Real.log (1 - ((p.val:ℝ)^k)⁻¹))
      (Real.log (realZeta k)) := by
  let f : ℕ →*₀ ℝ :=
    invMonoidWithZeroHom.comp ((powMonoidWithZeroHom (show k ≠ 0 by omega)).comp
      (Nat.castRingHom ℝ).toMonoidWithZeroHom)
  have hf (n : ℕ) : f n = ((n:ℝ)^k)⁻¹ := rfl
  have hs : Summable (fun n => ‖f n‖) := by
    simp_rw [hf, Real.norm_of_nonneg (inv_nonneg.mpr (pow_nonneg (Nat.cast_nonneg _) _))]
    exact Real.summable_nat_pow_inv.mpr hk
  have hp := EulerProduct.eulerProduct_completely_multiplicative_hasProd hs
  simp only [hf] at hp
  change Tendsto (fun s : Finset Nat.Primes =>
    ∏ p ∈ s, (1-((p.val:ℝ)^k)⁻¹)⁻¹) atTop (𝓝 (realZeta k)) at hp
  have hpos (p : Nat.Primes) : 0 < (1-((p.val:ℝ)^k)⁻¹) := by
    have hp2 : (1:ℝ) < p.val := by exact_mod_cast p.prop.one_lt
    have hpow : (1:ℝ) < (p.val:ℝ)^k := one_lt_pow₀ hp2 (by omega)
    exact sub_pos.mpr (inv_lt_one_of_one_lt₀ hpow)
  have hl := (Real.continuousAt_log (realZeta_pos hk).ne').tendsto.comp hp
  change Tendsto (fun s : Finset Nat.Primes =>
    ∑ p ∈ s, -Real.log (1-((p.val:ℝ)^k)⁻¹)) atTop (𝓝 (Real.log (realZeta k)))
  apply hl.congr
  intro s
  change Real.log (∏ p ∈ s, (1-((p.val:ℝ)^k)⁻¹)⁻¹) = _
  have he : ∀ p ∈ s, (1-((p.val:ℝ)^k)⁻¹)⁻¹ ≠ 0 :=
    fun p _ => (inv_pos.mpr (hpos p)).ne'
  rw [Real.log_prod he]
  simp only [Real.log_inv]


private theorem complexZeta_real {k : ℕ} (hk : 1 < k) :
    (realZeta k : ℂ) = riemannZeta k := by
  rw [zeta_nat_eq_tsum_of_gt_one hk]
  simp only [realZeta, Complex.ofReal_tsum, Complex.ofReal_inv, Complex.ofReal_pow,
    Complex.ofReal_natCast, one_div]

private theorem zetaTwo : realZeta 2 = Real.pi^2/6 := by
  apply Complex.ofReal_injective
  rw [complexZeta_real (by decide : 1 < 2)]
  norm_num [riemannZeta_two]

private theorem zetaSix : realZeta 6 = Real.pi^6/945 := by
  have hb : bernoulli 6 = 1/42 := by decide +kernel
  apply Complex.ofReal_injective
  rw [complexZeta_real (by decide : 1 < 6)]
  have h := riemannZeta_two_mul_nat (k := 3) (by decide)
  norm_num [hb] at h
  norm_num [h]
  ring

end DotMertens

open Finset
namespace DotMertens
private noncomputable def R (x : ℝ) : ℝ :=
  -Real.log (1-x) - x + Real.log (1-x^2)/2 +
    Real.log (1-x^3)/3 - Real.log (1-x^6)/6

private theorem R_abs_le {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1/2) :
    |R x| ≤ 4*x^5 := by
  have hx : x < 1 := by linarith
  have hxk (k : ℕ) (hk : 1 ≤ k) : x^k ≤ x := by
    calc
      x^k ≤ x^1 := pow_le_pow_of_le_one h0 hx.le hk
      _ = x := pow_one _
  have hq (k : ℕ) (hk : 1 ≤ k) : x^6 / (1-x^k) ≤ 2*x^5 := by
    calc
      _ ≤ x^6 / (1-x) := by
        exact div_le_div_of_nonneg_left (by positivity) (by linarith) (by linarith [hxk k hk])
      _ ≤ (x^5) / (1-x) := by
        exact div_le_div_of_nonneg_right (pow_le_pow_of_le_one h0 hx.le (by decide : 5 ≤ 6))
          (by linarith)
      _ ≤ _ := by
        apply (div_le_iff₀ (by linarith : 0 < 1-x)).mpr
        nlinarith [mul_nonneg (pow_nonneg h0 5) (show 0 ≤ 1-2*x by linarith)]
  have e1 := Real.abs_log_sub_add_sum_range_le (show |x| < 1 by rwa [abs_of_nonneg h0]) 4
  have e2 := Real.abs_log_sub_add_sum_range_le (show |x^2| < 1 by
    rw [abs_of_nonneg (by positivity)]
    exact (hxk 2 (by decide)).trans_lt hx) 2
  have e3 := Real.abs_log_sub_add_sum_range_le (show |x^3| < 1 by
    rw [abs_of_nonneg (by positivity)]
    exact (hxk 3 (by decide)).trans_lt hx) 1
  have e6 := Real.abs_log_sub_add_sum_range_le (show |x^6| < 1 by
    rw [abs_of_nonneg (by positivity)]
    exact (hxk 6 (by decide)).trans_lt hx) 0
  have hfirst : x^5/(1-x) ≤ 2*x^5 := by
    apply (div_le_iff₀ (by linarith : 0 < 1-x)).mpr
    nlinarith [mul_nonneg (pow_nonneg h0 5) (show 0 ≤ 1-2*x by linarith)]
  simp only [abs_of_nonneg h0, abs_of_nonneg (pow_nonneg h0 _)] at e1 e2 e3 e6
  norm_num [Finset.sum_range_succ, ← pow_mul] at e1 e2 e3 e6
  have u1 := abs_le.mp (e1.trans hfirst)
  have u2 := abs_le.mp (e2.trans (hq 2 (by decide)))
  have u3 := abs_le.mp (e3.trans (hq 3 (by decide)))
  have u6 := abs_le.mp (e6.trans (hq 6 (by decide)))
  unfold R
  rw [abs_le]
  constructor <;> linarith only [u1.1,u1.2,u2.1,u2.2,u3.1,u3.2,u6.1,u6.2]

end DotMertens

open Set MeasureTheory
namespace DotMertens

private theorem pow_tail (k N : ℕ) (hk : 1 < k) (hN : 0 < N) :
    (∑' n : ℕ, (((n+N+1:ℕ):ℝ)^k)⁻¹) ≤
      -((N:ℝ)^(-(k:ℝ)+1))/(-(k:ℝ)+1) := by
  have hNp : (0:ℝ) < N := by exact_mod_cast hN
  have hkp : (1:ℝ) < k := by exact_mod_cast hk
  have hkn : -(k:ℝ) < -1 := by linarith
  have hanti : AntitoneOn (fun x : ℝ => x^(-(k:ℝ))) (Ici (N:ℝ)) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_nonpos (hNp.trans_le hx) hxy (by linarith)
  have h := hanti.tsum_comp_add_le_integral N
    (integrableOn_Ioi_rpow_of_lt hkn hNp)
    (fun x hx => Real.rpow_nonneg (hNp.trans hx).le _)
  rw [integral_Ioi_rpow_of_lt hkn hNp] at h
  convert h using 2
  funext n
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast]

private theorem pow_tail_three :
    (∑' n : ℕ, (((n+1025:ℕ):ℝ)^3)⁻¹) ≤ 1/(2*(1024:ℝ)^2) := by
  have h := pow_tail 3 1024 (by decide) (by decide)
  change (∑' n : ℕ, (((n+1025:ℕ):ℝ)^3)⁻¹) ≤ _ at h
  convert h using 1
  norm_num [show (-(3:ℝ)+1) = -(2:ℝ) by norm_num, Real.rpow_neg (by positivity : (0:ℝ) ≤ 1024), Real.rpow_natCast]

private theorem pow_tail_five :
    (∑' n : ℕ, (((n+101:ℕ):ℝ)^5)⁻¹) ≤ 1/(4*(100:ℝ)^4) := by
  have h := pow_tail 5 100 (by decide) (by decide)
  change (∑' n : ℕ, (((n+101:ℕ):ℝ)^5)⁻¹) ≤ _ at h
  convert h using 1
  norm_num [show (-(5:ℝ)+1) = -(4:ℝ) by norm_num, Real.rpow_neg (by positivity : (0:ℝ) ≤ 100), Real.rpow_natCast]

end DotMertens
open Finset
namespace DotMertens

private theorem logApprox (y : ℝ) (hy : 0 < y) (m : ℕ) :
    |Real.log y - 2 * (∑ i ∈ range m, ((y-1)/(y+1))^(2*i+1)/(2*i+1))| ≤
      2 * |(y-1)/(y+1)|^(2*m+1)/(1-((y-1)/(y+1))^2) := by
  let t := (y-1)/(y+1)
  have ht : |t| < 1 := by
    apply abs_lt.mpr
    constructor <;> dsimp [t]
    · apply (lt_div_iff₀ (by positivity : 0 < y+1)).2
      linarith
    · apply (div_lt_iff₀ (by positivity : 0 < y+1)).2
      linarith
  have he : (1+t)/(1-t) = y := by
    dsimp [t]
    field_simp
    <;> ring
  have h := Real.sum_range_sub_log_div_le ht m
  rw [he] at h
  change |Real.log y - 2*_| ≤ 2*|t|^(2*m+1)/(1-t^2)
  rw [show Real.log y - 2 * (∑ i ∈ range m, t ^ (2*i+1) / (2*i+1)) =
      2 * (1/2 * Real.log y - (∑ i ∈ range m, t ^ (2*i+1)/(2*i+1))) by ring, abs_mul]
  norm_num [mul_div_assoc]
  linarith

private theorem log2bounds :
    (0.693147180559 : ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ 0.693147180561 := by
  have h := logApprox 2 (by norm_num) 16
  norm_num [Finset.sum_range_succ] at h
  have hu := abs_le.mp h
  constructor <;> linarith only [hu.1,hu.2]

end DotMertens
open Finset Filter MeasureTheory
open scoped Topology
namespace DotMertens

private noncomputable def rNat (n : ℕ) : ℝ :=
  if n.Prime then R (1/(n:ℝ)) else 0

private theorem rNat_bound (n : ℕ) : |rNat n| ≤ 4*((n:ℝ)^5)⁻¹ := by
  unfold rNat
  split_ifs with h
  · have hn : (2:ℝ) ≤ n := by exact_mod_cast h.two_le
    have hx : 1/(n:ℝ) ≤ 1/2 := by
      exact one_div_le_one_div_of_le (by norm_num) hn
    simpa [one_div, inv_pow] using R_abs_le (by positivity : 0 ≤ 1/(n:ℝ)) hx
  · simp

private theorem scalar5 : Summable (fun n : ℕ => 4*((n:ℝ)^5)⁻¹) :=
  (Real.summable_nat_pow_inv.mpr (by decide : 1 < 5)).mul_left 4

private theorem rNat_sum : Summable rNat :=
  scalar5.of_norm_bounded (fun n => by simpa [Real.norm_eq_abs] using rNat_bound n)

private theorem rTail :
    |(∑' n, rNat n) - ∑ n ∈ range 101, rNat n| ≤ (1:ℝ)/100^4 := by
  rw [← rNat_sum.sum_add_tsum_nat_add 101, add_sub_cancel_left]
  have hscalar := (summable_nat_add_iff 101).2 scalar5
  have hsn : Summable (fun i : ℕ => ‖rNat (i+101)‖) :=
    hscalar.of_nonneg_of_le (fun _ => norm_nonneg _) (fun i => by
      simpa [Real.norm_eq_abs] using rNat_bound (i+101))
  calc
    _ = ‖∑' i, rNat (i+101)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∑' i, ‖rNat (i+101)‖ := norm_tsum_le_tsum_norm hsn
    _ ≤ ∑' i : ℕ, 4*(((i+101:ℕ):ℝ)^5)⁻¹ := by
      exact hsn.tsum_le_tsum (fun i => by
        simpa [Real.norm_eq_abs] using rNat_bound (i+101)) hscalar
    _ ≤ _ := by
      rw [tsum_mul_left]
      linarith [pow_tail_five]

private theorem residual_prime_sum :
    HasSum (fun p : Nat.Primes => R (1/(p.val:ℝ))) (∑' n, rNat n) := by
  let S : Set ℕ := {p | Nat.Prime p}
  have hz : (∑' p : Nat.Primes, R (1/(p.val:ℝ))) = ∑' n, rNat n := by
    change (∑' p : S, R (1/(p.val:ℝ))) = _
    rw [tsum_subtype S (fun n => R (1/(n:ℝ)))]
    congr 1
    funext n
    by_cases h : n.Prime <;> simp [S, rNat, h, Set.indicator]
  rw [← hz]
  have hs := rNat_sum.comp_injective (show Function.Injective (fun p : Nat.Primes => p.val) from Subtype.val_injective)
  apply Summable.hasSum
  convert hs using 1
  funext p
  simp [rNat, p.prop]

private theorem mertensIdentity :
    Real.eulerMascheroniConstant + ∑' p : Nat.Primes,
      (Real.log (1-1/(p.val:ℝ)) + 1/(p.val:ℝ)) =
    Real.eulerMascheroniConstant -
      ((∑' n, rNat n) + Real.log (realZeta 2)/2 +
       Real.log (realZeta 3)/3 - Real.log (realZeta 6)/6) := by
  have h2 := (log_euler (k := 2) (by decide)).div_const 2
  have h3 := (log_euler (k := 3) (by decide)).div_const 3
  have h6 := (log_euler (k := 6) (by decide)).div_const 6
  have ht := ((residual_prime_sum.add h2).add h3).sub h6
  have hc : HasSum (fun p : Nat.Primes =>
      Real.log (1-1/(p.val:ℝ)) + 1/(p.val:ℝ))
      (-((∑' n, rNat n) + Real.log (realZeta 2)/2 +
        Real.log (realZeta 3)/3 - Real.log (realZeta 6)/6)) := by
    refine ht.neg.congr_fun ?_
    intro p
    simp only [R, one_div, inv_pow]
    ring
  rw [hc.tsum_eq]
  ring

end DotMertens
open Finset
namespace DotMertens
private def clipped (m i : ℕ) : ℕ := 10000000000000000 / (i+1)^m

private theorem clip_bounds (m i : ℕ) :
    ((clipped m i : ℕ):ℝ)/10000000000000000 ≤ (((i+1:ℕ):ℝ)^m)⁻¹ ∧
    (((i+1:ℕ):ℝ)^m)⁻¹ ≤ ((clipped m i : ℕ):ℝ)/10000000000000000 + 1/10000000000000000 := by
  let D : ℝ := 10000000000000000
  let B : ℝ := (((i+1:ℕ):ℝ)^m)
  have hB : 0 < B := by dsimp [B]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have hlo : (clipped m i:ℝ)*B ≤ D := by
    dsimp only [B,D]
    exact_mod_cast (Nat.div_mul_le_self 10000000000000000 ((i+1)^m))
  have hhi : D ≤ B*((clipped m i:ℝ)+1) := by
    dsimp only [B,D]
    exact_mod_cast (Nat.lt_mul_div_succ 10000000000000000
      (show 0 < (i+1)^m by positivity)).le
  change (clipped m i:ℝ)/D ≤ B⁻¹ ∧ B⁻¹ ≤ (clipped m i:ℝ)/D+1/D
  rw [← add_div]
  constructor
  · rw [← one_div, div_le_div_iff₀ hD hB]
    simpa only [one_mul] using hlo
  · rw [← one_div, div_le_div_iff₀ hB hD]
    simpa only [one_mul, mul_comm] using hhi

private theorem clip_sums (m n : ℕ) :
    ((∑ i ∈ range n, clipped m i : ℕ):ℝ)/10000000000000000 ≤
      ∑ i ∈ range n, (((i+1:ℕ):ℝ)^m)⁻¹ ∧
    (∑ i ∈ range n, (((i+1:ℕ):ℝ)^m)⁻¹) ≤
      ((∑ i ∈ range n, clipped m i : ℕ):ℝ)/10000000000000000 + n/10000000000000000 := by
  push_cast
  rw [sum_div]
  constructor
  · exact sum_le_sum (fun i _ => by simpa only [Nat.cast_add, Nat.cast_one] using (clip_bounds m i).1)
  · calc
      _ ≤ ∑ i ∈ range n, (((clipped m i : ℕ):ℝ)/10000000000000000 + 1/10000000000000000) :=
        sum_le_sum (fun i _ => by simpa only [Nat.cast_add, Nat.cast_one] using (clip_bounds m i).2)
      _ = _ := by
        rw [sum_add_distrib, sum_const, card_range, nsmul_eq_mul]
        ring

private theorem clipList (m n : ℕ) :
    (∑ i ∈ range n, clipped m i) = ((List.range n).map (clipped m)).sum := by
  rw [← List.sum_toFinset _ List.nodup_range, List.toFinset_range]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private theorem clipOne : (∑ i ∈ range 1024, clipped 1 i) = 75091756722780876 := by
  rw [clipList]
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private theorem clipThree : (∑ i ∈ range 1024, clipped 3 i) = 12020564267878199 := by
  rw [clipList]
  decide +kernel

end DotMertens
open Finset
namespace DotMertens

private theorem R2 : ((371020314357/50000000000000):ℝ) ≤ R (1/2) ∧ R (1/2) ≤ (1449298103/195312500000) := by
  have h0 := logApprox ((1/2) : ℝ) (by norm_num) 15
  norm_num [Finset.sum_range_succ] at h0
  have a0 := abs_le.mp h0
  have h1 := logApprox ((3/4) : ℝ) (by norm_num) 8
  norm_num [Finset.sum_range_succ] at h1
  have a1 := abs_le.mp h1
  have h2 := logApprox ((7/8) : ℝ) (by norm_num) 6
  norm_num [Finset.sum_range_succ] at h2
  have a2 := abs_le.mp h2
  have h3 := logApprox ((63/64) : ℝ) (by norm_num) 3
  norm_num [Finset.sum_range_succ] at h3
  have a3 := abs_le.mp h3
  unfold R
  norm_num at *
  constructor <;> linarith only [a0.1,a0.2,a1.1,a1.2,a2.1,a2.2,a3.1,a3.2]

private theorem R3 : ((5555801589/6250000000000):ℝ) ≤ R (1/3) ∧ R (1/3) ≤ (44446412723/50000000000000) := by
  have h0 := logApprox ((2/3) : ℝ) (by norm_num) 10
  norm_num [Finset.sum_range_succ] at h0
  have a0 := abs_le.mp h0
  have h1 := logApprox ((8/9) : ℝ) (by norm_num) 6
  norm_num [Finset.sum_range_succ] at h1
  have a1 := abs_le.mp h1
  have h2 := logApprox ((26/27) : ℝ) (by norm_num) 4
  norm_num [Finset.sum_range_succ] at h2
  have a2 := abs_le.mp h2
  have h3 := logApprox ((728/729) : ℝ) (by norm_num) 2
  norm_num [Finset.sum_range_succ] at h3
  have a3 := abs_le.mp h3
  unfold R
  norm_num at *
  constructor <;> linarith only [a0.1,a0.2,a1.1,a1.2,a2.1,a2.2,a3.1,a3.2]

private theorem R5 : ((4937287213/75000000000000):ℝ) ≤ R (1/5) ∧ R (1/5) ≤ (4937287237/75000000000000) := by
  have h0 := logApprox ((4/5) : ℝ) (by norm_num) 7
  norm_num [Finset.sum_range_succ] at h0
  have a0 := abs_le.mp h0
  have h1 := logApprox ((24/25) : ℝ) (by norm_num) 4
  norm_num [Finset.sum_range_succ] at h1
  have a1 := abs_le.mp h1
  have h2 := logApprox ((124/125) : ℝ) (by norm_num) 3
  norm_num [Finset.sum_range_succ] at h2
  have a2 := abs_le.mp h2
  have h3 := logApprox ((15624/15625) : ℝ) (by norm_num) 2
  norm_num [Finset.sum_range_succ] at h3
  have a3 := abs_le.mp h3
  unfold R
  norm_num at *
  constructor <;> linarith only [a0.1,a0.2,a1.1,a1.2,a2.1,a2.2,a3.1,a3.2]

private theorem R7 : ((25353965309/2100000000000000):ℝ) ≤ R (1/7) ∧ R (1/7) ≤ (25353965771/2100000000000000) := by
  have h0 := logApprox ((6/7) : ℝ) (by norm_num) 6
  norm_num [Finset.sum_range_succ] at h0
  have a0 := abs_le.mp h0
  have h1 := logApprox ((48/49) : ℝ) (by norm_num) 4
  norm_num [Finset.sum_range_succ] at h1
  have a1 := abs_le.mp h1
  have h2 := logApprox ((342/343) : ℝ) (by norm_num) 3
  norm_num [Finset.sum_range_succ] at h2
  have a2 := abs_le.mp h2
  have h3 := logApprox ((117648/117649) : ℝ) (by norm_num) 1
  norm_num [Finset.sum_range_succ] at h3
  have a3 := abs_le.mp h3
  unfold R
  norm_num at *
  constructor <;> linarith only [a0.1,a0.2,a1.1,a1.2,a2.1,a2.2,a3.1,a3.2]

private theorem R11 : ((2061136631/1650000000000000):ℝ) ≤ R (1/11) ∧ R (1/11) ≤ (1030568497/825000000000000) := by
  have h0 := logApprox ((10/11) : ℝ) (by norm_num) 5
  norm_num [Finset.sum_range_succ] at h0
  have a0 := abs_le.mp h0
  have h1 := logApprox ((120/121) : ℝ) (by norm_num) 3
  norm_num [Finset.sum_range_succ] at h1
  have a1 := abs_le.mp h1
  have h2 := logApprox ((1330/1331) : ℝ) (by norm_num) 2
  norm_num [Finset.sum_range_succ] at h2
  have a2 := abs_le.mp h2
  have h3 := logApprox ((1771560/1771561) : ℝ) (by norm_num) 1
  norm_num [Finset.sum_range_succ] at h3
  have a3 := abs_le.mp h3
  unfold R
  norm_num at *
  constructor <;> linarith only [a0.1,a0.2,a1.1,a1.2,a2.1,a2.2,a3.1,a3.2]

private theorem R13 : ((87901899/162500000000000):ℝ) ≤ R (1/13) ∧ R (1/13) ≤ (351607739/650000000000000) := by
  have h0 := logApprox ((12/13) : ℝ) (by norm_num) 5
  norm_num [Finset.sum_range_succ] at h0
  have a0 := abs_le.mp h0
  have h1 := logApprox ((168/169) : ℝ) (by norm_num) 3
  norm_num [Finset.sum_range_succ] at h1
  have a1 := abs_le.mp h1
  have h2 := logApprox ((2196/2197) : ℝ) (by norm_num) 2
  norm_num [Finset.sum_range_succ] at h2
  have a2 := abs_le.mp h2
  have h3 := logApprox ((4826808/4826809) : ℝ) (by norm_num) 1
  norm_num [Finset.sum_range_succ] at h3
  have a3 := abs_le.mp h3
  unfold R
  norm_num at *
  constructor <;> linarith only [a0.1,a0.2,a1.1,a1.2,a2.1,a2.2,a3.1,a3.2]

private theorem R17 : ((240052453/1700000000000000):ℝ) ≤ R (1/17) ∧ R (1/17) ≤ (240052827/1700000000000000) := by
  have h0 := logApprox ((16/17) : ℝ) (by norm_num) 5
  norm_num [Finset.sum_range_succ] at h0
  have a0 := abs_le.mp h0
  have h1 := logApprox ((288/289) : ℝ) (by norm_num) 3
  norm_num [Finset.sum_range_succ] at h1
  have a1 := abs_le.mp h1
  have h2 := logApprox ((4912/4913) : ℝ) (by norm_num) 2
  norm_num [Finset.sum_range_succ] at h2
  have a2 := abs_le.mp h2
  have h3 := logApprox ((24137568/24137569) : ℝ) (by norm_num) 1
  norm_num [Finset.sum_range_succ] at h3
  have a3 := abs_le.mp h3
  unfold R
  norm_num at *
  constructor <;> linarith only [a0.1,a0.2,a1.1,a1.2,a2.1,a2.2,a3.1,a3.2]

private theorem R19 : ((461311763/5700000000000000):ℝ) ≤ R (1/19) ∧ R (1/19) ≤ (461313017/5700000000000000) := by
  have h0 := logApprox ((18/19) : ℝ) (by norm_num) 5
  norm_num [Finset.sum_range_succ] at h0
  have a0 := abs_le.mp h0
  have h1 := logApprox ((360/361) : ℝ) (by norm_num) 3
  norm_num [Finset.sum_range_succ] at h1
  have a1 := abs_le.mp h1
  have h2 := logApprox ((6858/6859) : ℝ) (by norm_num) 2
  norm_num [Finset.sum_range_succ] at h2
  have a2 := abs_le.mp h2
  have h3 := logApprox ((47045880/47045881) : ℝ) (by norm_num) 1
  norm_num [Finset.sum_range_succ] at h3
  have a3 := abs_le.mp h3
  unfold R
  norm_num at *
  constructor <;> linarith only [a0.1,a0.2,a1.1,a1.2,a2.1,a2.2,a3.1,a3.2]

private theorem R23 : ((71565477/2300000000000000):ℝ) ≤ R (1/23) ∧ R (1/23) ≤ (71565983/2300000000000000) := by
  have h0 := logApprox ((22/23) : ℝ) (by norm_num) 4
  norm_num [Finset.sum_range_succ] at h0
  have a0 := abs_le.mp h0
  have h1 := logApprox ((528/529) : ℝ) (by norm_num) 2
  norm_num [Finset.sum_range_succ] at h1
  have a1 := abs_le.mp h1
  have h2 := logApprox ((12166/12167) : ℝ) (by norm_num) 2
  norm_num [Finset.sum_range_succ] at h2
  have a2 := abs_le.mp h2
  have h3 := logApprox ((148035888/148035889) : ℝ) (by norm_num) 1
  norm_num [Finset.sum_range_succ] at h3
  have a3 := abs_le.mp h3
  unfold R
  norm_num at *
  constructor <;> linarith only [a0.1,a0.2,a1.1,a1.2,a2.1,a2.2,a3.1,a3.2]

private theorem R29 : ((7075239/725000000000000):ℝ) ≤ R (1/29) ∧ R (1/29) ≤ (14150797/1450000000000000) := by
  have h0 := logApprox ((28/29) : ℝ) (by norm_num) 4
  norm_num [Finset.sum_range_succ] at h0
  have a0 := abs_le.mp h0
  have h1 := logApprox ((840/841) : ℝ) (by norm_num) 2
  norm_num [Finset.sum_range_succ] at h1
  have a1 := abs_le.mp h1
  have h2 := logApprox ((24388/24389) : ℝ) (by norm_num) 2
  norm_num [Finset.sum_range_succ] at h2
  have a2 := abs_le.mp h2
  have h3 := logApprox ((594823320/594823321) : ℝ) (by norm_num) 1
  norm_num [Finset.sum_range_succ] at h3
  have a3 := abs_le.mp h3
  unfold R
  norm_num at *
  constructor <;> linarith only [a0.1,a0.2,a1.1,a1.2,a2.1,a2.2,a3.1,a3.2]

private theorem R31 : ((65015317/9300000000000000):ℝ) ≤ R (1/31) ∧ R (1/31) ≤ (65017673/9300000000000000) := by
  have h0 := logApprox ((30/31) : ℝ) (by norm_num) 4
  norm_num [Finset.sum_range_succ] at h0
  have a0 := abs_le.mp h0
  have h1 := logApprox ((960/961) : ℝ) (by norm_num) 2
  norm_num [Finset.sum_range_succ] at h1
  have a1 := abs_le.mp h1
  have h2 := logApprox ((29790/29791) : ℝ) (by norm_num) 1
  norm_num [Finset.sum_range_succ] at h2
  have a2 := abs_le.mp h2
  have h3 := logApprox ((887503680/887503681) : ℝ) (by norm_num) 1
  norm_num [Finset.sum_range_succ] at h3
  have a3 := abs_le.mp h3
  unfold R
  norm_num at *
  constructor <;> linarith only [a0.1,a0.2,a1.1,a1.2,a2.1,a2.2,a3.1,a3.2]

private theorem R37 : ((333649/115625000000000):ℝ) ≤ R (1/37) ∧ R (1/37) ≤ (5338791/1850000000000000) := by
  have h0 := logApprox ((36/37) : ℝ) (by norm_num) 4
  norm_num [Finset.sum_range_succ] at h0
  have a0 := abs_le.mp h0
  have h1 := logApprox ((1368/1369) : ℝ) (by norm_num) 2
  norm_num [Finset.sum_range_succ] at h1
  have a1 := abs_le.mp h1
  have h2 := logApprox ((50652/50653) : ℝ) (by norm_num) 1
  norm_num [Finset.sum_range_succ] at h2
  have a2 := abs_le.mp h2
  have h3 := logApprox ((2565726408/2565726409) : ℝ) (by norm_num) 1
  norm_num [Finset.sum_range_succ] at h3
  have a3 := abs_le.mp h3
  unfold R
  norm_num at *
  constructor <;> linarith only [a0.1,a0.2,a1.1,a1.2,a2.1,a2.2,a3.1,a3.2]

private theorem R41 : ((2655059/1537500000000000):ℝ) ≤ R (1/41) ∧ R (1/41) ≤ (10621589/6150000000000000) := by
  have h0 := logApprox ((40/41) : ℝ) (by norm_num) 4
  norm_num [Finset.sum_range_succ] at h0
  have a0 := abs_le.mp h0
  have h1 := logApprox ((1680/1681) : ℝ) (by norm_num) 2
  norm_num [Finset.sum_range_succ] at h1
  have a1 := abs_le.mp h1
  have h2 := logApprox ((68920/68921) : ℝ) (by norm_num) 1
  norm_num [Finset.sum_range_succ] at h2
  have a2 := abs_le.mp h2
  have h3 := logApprox ((4750104240/4750104241) : ℝ) (by norm_num) 1
  norm_num [Finset.sum_range_succ] at h3
  have a3 := abs_le.mp h3
  unfold R
  norm_num at *
  constructor <;> linarith only [a0.1,a0.2,a1.1,a1.2,a2.1,a2.2,a3.1,a3.2]

private theorem R43 : ((17555201/12900000000000000):ℝ) ≤ R (1/43) ∧ R (1/43) ≤ (17558039/12900000000000000) := by
  have h0 := logApprox ((42/43) : ℝ) (by norm_num) 4
  norm_num [Finset.sum_range_succ] at h0
  have a0 := abs_le.mp h0
  have h1 := logApprox ((1848/1849) : ℝ) (by norm_num) 2
  norm_num [Finset.sum_range_succ] at h1
  have a1 := abs_le.mp h1
  have h2 := logApprox ((79506/79507) : ℝ) (by norm_num) 1
  norm_num [Finset.sum_range_succ] at h2
  have a2 := abs_le.mp h2
  have h3 := logApprox ((6321363048/6321363049) : ℝ) (by norm_num) 1
  norm_num [Finset.sum_range_succ] at h3
  have a3 := abs_le.mp h3
  unfold R
  norm_num at *
  constructor <;> linarith only [a0.1,a0.2,a1.1,a1.2,a2.1,a2.2,a3.1,a3.2]

private theorem R47 : ((6148957/7050000000000000):ℝ) ≤ R (1/47) ∧ R (1/47) ≤ (1537627/1762500000000000) := by
  have h0 := logApprox ((46/47) : ℝ) (by norm_num) 4
  norm_num [Finset.sum_range_succ] at h0
  have a0 := abs_le.mp h0
  have h1 := logApprox ((2208/2209) : ℝ) (by norm_num) 2
  norm_num [Finset.sum_range_succ] at h1
  have a1 := abs_le.mp h1
  have h2 := logApprox ((103822/103823) : ℝ) (by norm_num) 1
  norm_num [Finset.sum_range_succ] at h2
  have a2 := abs_le.mp h2
  have h3 := logApprox ((10779215328/10779215329) : ℝ) (by norm_num) 1
  norm_num [Finset.sum_range_succ] at h3
  have a3 := abs_le.mp h3
  unfold R
  norm_num at *
  constructor <;> linarith only [a0.1,a0.2,a1.1,a1.2,a2.1,a2.2,a3.1,a3.2]

private theorem R53 : ((29701/62109375000000):ℝ) ≤ R (1/53) ∧ R (1/53) ≤ (3803477/7950000000000000) := by
  have h0 := logApprox ((52/53) : ℝ) (by norm_num) 4
  norm_num [Finset.sum_range_succ] at h0
  have a0 := abs_le.mp h0
  have h1 := logApprox ((2808/2809) : ℝ) (by norm_num) 2
  norm_num [Finset.sum_range_succ] at h1
  have a1 := abs_le.mp h1
  have h2 := logApprox ((148876/148877) : ℝ) (by norm_num) 1
  norm_num [Finset.sum_range_succ] at h2
  have a2 := abs_le.mp h2
  have h3 := logApprox ((22164361128/22164361129) : ℝ) (by norm_num) 1
  norm_num [Finset.sum_range_succ] at h3
  have a3 := abs_le.mp h3
  unfold R
  norm_num at *
  constructor <;> linarith only [a0.1,a0.2,a1.1,a1.2,a2.1,a2.2,a3.1,a3.2]

private theorem R59 : ((2474759/8850000000000000):ℝ) ≤ R (1/59) ∧ R (1/59) ≤ (2477591/8850000000000000) := by
  have h0 := logApprox ((58/59) : ℝ) (by norm_num) 3
  norm_num [Finset.sum_range_succ] at h0
  have a0 := abs_le.mp h0
  have h1 := logApprox ((3480/3481) : ℝ) (by norm_num) 2
  norm_num [Finset.sum_range_succ] at h1
  have a1 := abs_le.mp h1
  have h2 := logApprox ((205378/205379) : ℝ) (by norm_num) 1
  norm_num [Finset.sum_range_succ] at h2
  have a2 := abs_le.mp h2
  have h3 := logApprox ((42180533640/42180533641) : ℝ) (by norm_num) 1
  norm_num [Finset.sum_range_succ] at h3
  have a3 := abs_le.mp h3
  unfold R
  norm_num at *
  constructor <;> linarith only [a0.1,a0.2,a1.1,a1.2,a2.1,a2.2,a3.1,a3.2]

private theorem R61 : ((541579/2287500000000000):ℝ) ≤ R (1/61) ∧ R (1/61) ≤ (2168329/9150000000000000) := by
  have h0 := logApprox ((60/61) : ℝ) (by norm_num) 3
  norm_num [Finset.sum_range_succ] at h0
  have a0 := abs_le.mp h0
  have h1 := logApprox ((3720/3721) : ℝ) (by norm_num) 2
  norm_num [Finset.sum_range_succ] at h1
  have a1 := abs_le.mp h1
  have h2 := logApprox ((226980/226981) : ℝ) (by norm_num) 1
  norm_num [Finset.sum_range_succ] at h2
  have a2 := abs_le.mp h2
  have h3 := logApprox ((51520374360/51520374361) : ℝ) (by norm_num) 1
  norm_num [Finset.sum_range_succ] at h3
  have a3 := abs_le.mp h3
  unfold R
  norm_num at *
  constructor <;> linarith only [a0.1,a0.2,a1.1,a1.2,a2.1,a2.2,a3.1,a3.2]

private theorem R67 : ((2976709/20100000000000000):ℝ) ≤ R (1/67) ∧ R (1/67) ≤ (2981131/20100000000000000) := by
  have h0 := logApprox ((66/67) : ℝ) (by norm_num) 3
  norm_num [Finset.sum_range_succ] at h0
  have a0 := abs_le.mp h0
  have h1 := logApprox ((4488/4489) : ℝ) (by norm_num) 2
  norm_num [Finset.sum_range_succ] at h1
  have a1 := abs_le.mp h1
  have h2 := logApprox ((300762/300763) : ℝ) (by norm_num) 1
  norm_num [Finset.sum_range_succ] at h2
  have a2 := abs_le.mp h2
  have h3 := logApprox ((90458382168/90458382169) : ℝ) (by norm_num) 1
  norm_num [Finset.sum_range_succ] at h3
  have a3 := abs_le.mp h3
  unfold R
  norm_num at *
  constructor <;> linarith only [a0.1,a0.2,a1.1,a1.2,a2.1,a2.2,a3.1,a3.2]

private theorem R71 : ((1179521/10650000000000000):ℝ) ≤ R (1/71) ∧ R (1/71) ≤ (147733/1331250000000000) := by
  have h0 := logApprox ((70/71) : ℝ) (by norm_num) 3
  norm_num [Finset.sum_range_succ] at h0
  have a0 := abs_le.mp h0
  have h1 := logApprox ((5040/5041) : ℝ) (by norm_num) 2
  norm_num [Finset.sum_range_succ] at h1
  have a1 := abs_le.mp h1
  have h2 := logApprox ((357910/357911) : ℝ) (by norm_num) 1
  norm_num [Finset.sum_range_succ] at h2
  have a2 := abs_le.mp h2
  have h3 := logApprox ((128100283920/128100283921) : ℝ) (by norm_num) 1
  norm_num [Finset.sum_range_succ] at h3
  have a3 := abs_le.mp h3
  unfold R
  norm_num at *
  constructor <;> linarith only [a0.1,a0.2,a1.1,a1.2,a2.1,a2.2,a3.1,a3.2]

private theorem R73 : ((703747/7300000000000000):ℝ) ≤ R (1/73) ∧ R (1/73) ≤ (705353/7300000000000000) := by
  have h0 := logApprox ((72/73) : ℝ) (by norm_num) 3
  norm_num [Finset.sum_range_succ] at h0
  have a0 := abs_le.mp h0
  have h1 := logApprox ((5328/5329) : ℝ) (by norm_num) 2
  norm_num [Finset.sum_range_succ] at h1
  have a1 := abs_le.mp h1
  have h2 := logApprox ((389016/389017) : ℝ) (by norm_num) 1
  norm_num [Finset.sum_range_succ] at h2
  have a2 := abs_le.mp h2
  have h3 := logApprox ((151334226288/151334226289) : ℝ) (by norm_num) 1
  norm_num [Finset.sum_range_succ] at h3
  have a3 := abs_le.mp h3
  unfold R
  norm_num at *
  constructor <;> linarith only [a0.1,a0.2,a1.1,a1.2,a2.1,a2.2,a3.1,a3.2]

private theorem R79 : ((64127/987500000000000):ℝ) ≤ R (1/79) ∧ R (1/79) ≤ (257377/3950000000000000) := by
  have h0 := logApprox ((78/79) : ℝ) (by norm_num) 3
  norm_num [Finset.sum_range_succ] at h0
  have a0 := abs_le.mp h0
  have h1 := logApprox ((6240/6241) : ℝ) (by norm_num) 2
  norm_num [Finset.sum_range_succ] at h1
  have a1 := abs_le.mp h1
  have h2 := logApprox ((493038/493039) : ℝ) (by norm_num) 1
  norm_num [Finset.sum_range_succ] at h2
  have a2 := abs_le.mp h2
  have h3 := logApprox ((243087455520/243087455521) : ℝ) (by norm_num) 1
  norm_num [Finset.sum_range_succ] at h3
  have a3 := abs_le.mp h3
  unfold R
  norm_num at *
  constructor <;> linarith only [a0.1,a0.2,a1.1,a1.2,a2.1,a2.2,a3.1,a3.2]

private theorem R83 : ((210221/4150000000000000):ℝ) ≤ R (1/83) ∧ R (1/83) ≤ (105567/2075000000000000) := by
  have h0 := logApprox ((82/83) : ℝ) (by norm_num) 3
  norm_num [Finset.sum_range_succ] at h0
  have a0 := abs_le.mp h0
  have h1 := logApprox ((6888/6889) : ℝ) (by norm_num) 2
  norm_num [Finset.sum_range_succ] at h1
  have a1 := abs_le.mp h1
  have h2 := logApprox ((571786/571787) : ℝ) (by norm_num) 1
  norm_num [Finset.sum_range_succ] at h2
  have a2 := abs_le.mp h2
  have h3 := logApprox ((326940373368/326940373369) : ℝ) (by norm_num) 1
  norm_num [Finset.sum_range_succ] at h3
  have a3 := abs_le.mp h3
  unfold R
  norm_num at *
  constructor <;> linarith only [a0.1,a0.2,a1.1,a1.2,a2.1,a2.2,a3.1,a3.2]

private theorem R89 : ((238477/6675000000000000):ℝ) ≤ R (1/89) ∧ R (1/89) ≤ (479891/13350000000000000) := by
  have h0 := logApprox ((88/89) : ℝ) (by norm_num) 3
  norm_num [Finset.sum_range_succ] at h0
  have a0 := abs_le.mp h0
  have h1 := logApprox ((7920/7921) : ℝ) (by norm_num) 2
  norm_num [Finset.sum_range_succ] at h1
  have a1 := abs_le.mp h1
  have h2 := logApprox ((704968/704969) : ℝ) (by norm_num) 1
  norm_num [Finset.sum_range_succ] at h2
  have a2 := abs_le.mp h2
  have h3 := logApprox ((496981290960/496981290961) : ℝ) (by norm_num) 1
  norm_num [Finset.sum_range_succ] at h3
  have a3 := abs_le.mp h3
  unfold R
  norm_num at *
  constructor <;> linarith only [a0.1,a0.2,a1.1,a1.2,a2.1,a2.2,a3.1,a3.2]

private theorem R97 : ((675349/29100000000000000):ℝ) ≤ R (1/97) ∧ R (1/97) ≤ (681751/29100000000000000) := by
  have h0 := logApprox ((96/97) : ℝ) (by norm_num) 3
  norm_num [Finset.sum_range_succ] at h0
  have a0 := abs_le.mp h0
  have h1 := logApprox ((9408/9409) : ℝ) (by norm_num) 2
  norm_num [Finset.sum_range_succ] at h1
  have a1 := abs_le.mp h1
  have h2 := logApprox ((912672/912673) : ℝ) (by norm_num) 1
  norm_num [Finset.sum_range_succ] at h2
  have a2 := abs_le.mp h2
  have h3 := logApprox ((832972004928/832972004929) : ℝ) (by norm_num) 1
  norm_num [Finset.sum_range_succ] at h3
  have a3 := abs_le.mp h3
  unfold R
  norm_num at *
  constructor <;> linarith only [a0.1,a0.2,a1.1,a1.2,a2.1,a2.2,a3.1,a3.2]

private theorem finiteR :
    ((8389306837/1000000000000):ℝ) ≤ ∑ i ∈ range 101, rNat i ∧
    (∑ i ∈ range 101, rNat i) ≤ (8389306843/1000000000000) := by
  classical
  have hp : ((range 101).filter Nat.Prime) = ({2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97} : Finset ℕ) := by decide +kernel
  simp only [rNat, ← sum_filter, hp]
  norm_num [sum_insert]
  constructor <;> linarith only [R2.1, R2.2, R3.1, R3.2, R5.1, R5.2, R7.1, R7.2, R11.1, R11.2, R13.1, R13.2, R17.1, R17.2, R19.1, R19.2, R23.1, R23.2, R29.1, R29.2, R31.1, R31.2, R37.1, R37.2, R41.1, R41.2, R43.1, R43.2, R47.1, R47.2, R53.1, R53.2, R59.1, R59.2, R61.1, R61.2, R67.1, R67.2, R71.1, R71.2, R73.1, R73.2, R79.1, R79.2, R83.1, R83.2, R89.1, R89.2, R97.1, R97.2]

end DotMertens
open Finset
namespace DotMertens

set_option maxRecDepth 100000 in
private theorem gammaNum :
    (0.5772155854 : ℝ) ≤ Real.eulerMascheroniConstant ∧
    Real.eulerMascheroniConstant ≤ (0.5772160619 : ℝ) := by
  have h := gammaBracket 1023
  have hh := clip_sums 1 1024
  rw [clipOne] at hh
  have he : (harmonic 1024 : ℝ) =
      ∑ i ∈ range 1024, (((i+1:ℕ):ℝ)^1)⁻¹ := by
    simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, pow_one]
  have hlog : Real.log 1024 = 10 * Real.log 2 := by
    rw [show (1024:ℝ) = 2^10 by norm_num, Real.log_pow]
    norm_num
  change (harmonic 1024 : ℝ) - Real.log 1024 - (2*((1023:ℝ)+1))⁻¹ ≤
    Real.eulerMascheroniConstant ∧ Real.eulerMascheroniConstant ≤
      (harmonic 1024 : ℝ) - Real.log 1024 - (2*((1023:ℝ)+2))⁻¹ at h
  rw [he,hlog] at h
  constructor <;> linarith only [h.1,h.2,hh.1,hh.2,log2bounds.1,log2bounds.2]

set_option maxRecDepth 100000 in
private theorem zeta3Num :
    (1.202056426787 : ℝ) ≤ realZeta 3 ∧ realZeta 3 ≤ 1.202056903626 := by
  have hs := Real.summable_nat_pow_inv.mpr (by decide : 1 < 3)
  have he : (∑ i ∈ range 1024, (((i+1:ℕ):ℝ)^3)⁻¹) +
      (∑' n : ℕ, (((n+1025:ℕ):ℝ)^3)⁻¹) = realZeta 3 := by
    have h := (hs.tsum_eq_zero_add)
    have h' := ((summable_nat_add_iff 1).2 hs).sum_add_tsum_nat_add 1024
    unfold realZeta
    have h0 : (((0:ℕ):ℝ)^3)⁻¹ = 0 := by norm_num
    rw [h,h0,zero_add]
    exact h' 
  have h := clip_sums 3 1024
  rw [clipThree] at h
  have hT : 0 ≤ ∑' n : ℕ, (((n+1025:ℕ):ℝ)^3)⁻¹ :=
    tsum_nonneg (fun _ => by positivity)
  constructor <;> linarith only [h.1,h.2,he,hT,pow_tail_three]

private theorem zeta2Num :
    (1.6449340668482 : ℝ) ≤ realZeta 2 ∧ realZeta 2 ≤ 1.6449340668483 := by
  rw [zetaTwo]
  have hlo := Real.pi_gt_d20
  have hhi := Real.pi_lt_d20
  have hl : (3.14159265358979323846 : ℝ)^2 ≤ Real.pi^2 := by gcongr
  have hu : Real.pi^2 ≤ (3.14159265358979323847 : ℝ)^2 := by gcongr
  constructor <;> linarith only [hl,hu]

private theorem zeta6Num :
    (1.0173430619844 : ℝ) ≤ realZeta 6 ∧ realZeta 6 ≤ 1.0173430619845 := by
  rw [zetaSix]
  have hlo := Real.pi_gt_d20
  have hhi := Real.pi_lt_d20
  have hl : (3.14159265358979323846 : ℝ)^6 ≤ Real.pi^6 := by gcongr
  have hu : Real.pi^6 ≤ (3.14159265358979323847 : ℝ)^6 := by gcongr
  constructor <;> linarith only [hl,hu]


private theorem logZ2 :
    (0.497700302470:ℝ) ≤ Real.log (realZeta 2) ∧ Real.log (realZeta 2) ≤ 0.497700302472 := by
  have hl := logApprox (1.6449340668482:ℝ) (by norm_num) 14
  have hu := logApprox (1.6449340668483:ℝ) (by norm_num) 14
  norm_num [Finset.sum_range_succ] at hl hu
  have h1 := Real.log_le_log (by norm_num : (0:ℝ) < 1.6449340668482) zeta2Num.1
  have h2 := Real.log_le_log (realZeta_pos (k := 2) (by decide)) zeta2Num.2
  constructor <;> linarith only [(abs_le.mp hl).1,(abs_le.mp hu).2,h1,h2]

private theorem logZ3 :
    (0.184033779093:ℝ) ≤ Real.log (realZeta 3) ∧ Real.log (realZeta 3) ≤ 0.184034175780 := by
  have hl := logApprox (1.202056426787:ℝ) (by norm_num) 10
  have hu := logApprox (1.202056903626:ℝ) (by norm_num) 10
  norm_num [Finset.sum_range_succ] at hl hu
  have h1 := Real.log_le_log (by norm_num : (0:ℝ) < 1.202056426787) zeta3Num.1
  have h2 := Real.log_le_log (realZeta_pos (k := 3) (by decide)) zeta3Num.2
  constructor <;> linarith only [(abs_le.mp hl).1,(abs_le.mp hu).2,h1,h2]

private theorem logZ6 :
    (0.017194387602:ℝ) ≤ Real.log (realZeta 6) ∧ Real.log (realZeta 6) ≤ 0.017194387604 := by
  have hl := logApprox (1.0173430619844:ℝ) (by norm_num) 7
  have hu := logApprox (1.0173430619845:ℝ) (by norm_num) 7
  norm_num [Finset.sum_range_succ] at hl hu
  have h1 := Real.log_le_log (by norm_num : (0:ℝ) < 1.0173430619844) zeta6Num.1
  have h2 := Real.log_le_log (realZeta_pos (k := 6) (by decide)) zeta6Num.2
  constructor <;> linarith only [(abs_le.mp hl).1,(abs_le.mp hu).2,h1,h2]

end DotMertens
open Finset
namespace DotMertens
private theorem mertensBounds :
    (0.261497 : ℝ) ≤ Real.eulerMascheroniConstant + ∑' p : Nat.Primes,
      (Real.log (1-1/(p.val:ℝ)) + 1/(p.val:ℝ)) ∧
    Real.eulerMascheroniConstant + ∑' p : Nat.Primes,
      (Real.log (1-1/(p.val:ℝ)) + 1/(p.val:ℝ)) ≤ (0.261498 : ℝ) := by
  simp only [mertensIdentity]
  have ht := abs_le.mp rTail
  constructor <;> linarith only [ht.1,ht.2,finiteR.1,finiteR.2,gammaNum.1,gammaNum.2,
    logZ2.1,logZ2.2,logZ3.1,logZ3.2,logZ6.1,logZ6.2]
end DotMertens

theorem Conjectures.Cuts.Taskb182870585b8412c8aff946c : (have x1 : ℝ := Real.eulerMascheroniConstant + ∑' (x1 : Nat.Primes), (Real.log ((1 : ℝ) - (1 : ℝ) / ↑↑x1) + (1 : ℝ) / ↑↑x1); 0.261497 ≤ x1 ∧ x1 ≤ 0.261498) :=
  DotMertens.mertensBounds

