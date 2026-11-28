import Mathlib

/-!
Small-range reciprocal-prime estimates and the Meissel–Mertens constant.

The Euler-product argument and the explicit prime-tail bound are given
below. The finite certificates and their two assembly lemmas are reproduced
from Apache-2.0 contributions to the goldbach-proofs repository. Each source
is credited at its use. Their verified revisions were awaiting publication as
importable community modules when this proof was prepared.
-/

-- Adapted from bz7777777, https://github.com/CGandGameEngineLearner/goldbach-proofs/pull/4807
-- The certificate is placed in a local namespace and its entry point is renamed.
namespace SmallRangeInputs
section
open Finset

namespace GoldbachGridLog

def scale : ℕ := 10 ^ 9

def coreUpper (u v : ℕ) : ℕ :=
  12 + ∑ i ∈ range 11,
    (2 * scale * (u - v) ^ (2 * i + 1)) / ((2 * i + 1) * (u + v) ^ (2 * i + 1))

def logUpper (u v : ℕ) : ℕ :=
  let k := Nat.log 2 (u / v)
  k * coreUpper 2 1 + coreUpper u (v * 2 ^ k)

def logLogUpper (n : ℕ) : ℕ := logUpper (logUpper n 1) scale

theorem log_le_coreUpper (u v : ℕ) (hv : 0 < v) (hvu : v ≤ u) (huv : u ≤ 2 * v) :
    Real.log ((u : ℝ) / (v : ℝ)) ≤ (coreUpper u v : ℝ) / (scale : ℝ) := by
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
  have htail : 2 * (scale : ℝ) * (t ^ (23 : ℕ) / (1 - t ^ 2)) ≤ 1 := by
    have htSq : t ^ (2 : ℕ) ≤ (1 / 3 : ℝ) ^ (2 : ℕ) := pow_le_pow_left₀ ht0 ht3 2
    have hden : (0 : ℝ) < 1 - (1 / 3 : ℝ) ^ (2 : ℕ) := by norm_num
    have hden_le : 1 - (1 / 3 : ℝ) ^ (2 : ℕ) ≤ 1 - t ^ (2 : ℕ) := by linarith
    calc
      _ ≤ 2 * (scale : ℝ) * ((1 / 3 : ℝ) ^ (23 : ℕ) / (1 - (1 / 3 : ℝ) ^ (2 : ℕ))) := by
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
  have hsum : 2 * (scale : ℝ) * (∑ i ∈ range 11, t ^ (2 * i + 1) / ((2 * i + 1 : ℕ) : ℝ)) ≤
      (∑ i ∈ range 11, (term i : ℝ)) + 11 := by
    rw [mul_sum]
    calc
      _ ≤ ∑ i ∈ range 11, ((term i : ℝ) + 1) := sum_le_sum (fun i _ => hround i)
      _ = _ := by simp [sum_add_distrib]
  have hseries := Real.log_div_le_sum_range_add ht0 ht1 11
  rw [htRatio] at hseries
  have hscaled : Real.log ((u : ℝ) / (v : ℝ)) * (scale : ℝ) ≤
      2 * (scale : ℝ) * (∑ i ∈ range 11, t ^ (2 * i + 1) / ((2 * i + 1 : ℕ) : ℝ)) +
        2 * (scale : ℝ) * (t ^ (23 : ℕ) / (1 - t ^ 2)) := by
    calc
      _ = (2 * (scale : ℝ)) * (1 / 2 * Real.log ((u : ℝ) / (v : ℝ))) := by ring
      _ ≤ _ := by
        rw [← mul_add]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        simpa only [Nat.reduceMul, Nat.reduceAdd, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
          Nat.cast_one] using hseries
  apply (le_div_iff₀ hscale).2
  change _ ≤ ((12 + ∑ i ∈ range 11, term i : ℕ) : ℝ)
  push_cast
  linarith only [hscaled, hsum, htail]

theorem log_le_logUpper (u v : ℕ) (hv : 0 < v) (hvu : v ≤ u) :
    Real.log ((u : ℝ) / (v : ℝ)) ≤ (logUpper u v : ℝ) / (scale : ℝ) := by
  let k := Nat.log 2 (u / v)
  have hquot : 0 < u / v := (Nat.le_div_iff_mul_le hv).2 (by simpa using hvu)
  have hlow : v * 2 ^ k ≤ u := by
    simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hv).1
      (Nat.pow_log_le_self 2 hquot.ne')
  have hhigh : u ≤ 2 * (v * 2 ^ k) := by
    have h := (Nat.div_lt_iff_lt_mul hv).1 (Nat.lt_pow_succ_log_self (by decide : 1 < 2) (u / v))
    simpa [k, pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h.le
  have hvR : 0 < (v : ℝ) := by exact_mod_cast hv
  have huR : 0 < (u : ℝ) := by exact_mod_cast hv.trans_le hvu
  have hfactor : (u : ℝ) / (v : ℝ) = (2 : ℝ) ^ k * ((u : ℝ) / ((v * 2 ^ k : ℕ) : ℝ)) := by
    push_cast
    field_simp [hvR.ne']
  have hbase : Real.log 2 ≤ (coreUpper 2 1 : ℝ) / (scale : ℝ) := by
    simpa only [Nat.cast_ofNat, Nat.cast_one, div_one] using log_le_coreUpper 2 1 (by decide) (by decide) (by decide)
  have hres := log_le_coreUpper u (v * 2 ^ k) (by positivity) hlow hhigh
  rw [hfactor, Real.log_mul (by positivity) (by positivity), Real.log_pow]
  change _ ≤ ((k * coreUpper 2 1 + coreUpper u (v * 2 ^ k) : ℕ) : ℝ) / (scale : ℝ)
  push_cast
  push_cast at hres
  calc
    _ ≤ (k : ℝ) * ((coreUpper 2 1 : ℝ) / (scale : ℝ)) +
        (coreUpper u (v * 2 ^ k) : ℝ) / (scale : ℝ) := by
      exact add_le_add (mul_le_mul_of_nonneg_left hbase (Nat.cast_nonneg k)) hres
    _ = _ := by ring

theorem log_log_le_logLogUpper (n : ℕ) (hn : 3 ≤ n) :
    Real.log (Real.log (n : ℝ)) ≤ (logLogUpper n : ℝ) / (scale : ℝ) := by
  have hnR : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlog3 : (1 : ℝ) < Real.log 3 := (by norm_num : (1 : ℝ) < 1.0986122885).trans Real.log_three_gt_d9
  have hlog : 1 < Real.log (n : ℝ) := hlog3.trans_le (Real.log_le_log (by norm_num) hnR)
  have h := log_le_logUpper n 1 (by decide) (by omega)
  simp only [Nat.cast_one, div_one] at h
  have hscale : (0 : ℝ) < (scale : ℝ) := by norm_num [scale]
  have hbound : (scale : ℝ) ≤ (logUpper n 1 : ℝ) := by
    simpa only [one_mul] using (le_div_iff₀ hscale).1 (hlog.le.trans h)
  have hnat : scale ≤ logUpper n 1 := by exact_mod_cast hbound
  exact (Real.log_le_log (by linarith) h).trans
    (log_le_logUpper (logUpper n 1) scale (by decide) hnat)

end GoldbachGridLog

namespace GoldbachGridPrimes

open Finset

def primorial : ℕ := 10014646650599190067509233131649940057366334653200433090

theorem primorial_eq : primorial = ∏ p ∈ (range 149).filter Nat.Prime, p := by
  decide +kernel

def fastPrime (n : ℕ) : Bool :=
  if n ≤ 148 then decide (Nat.Prime n) else decide (n.Coprime primorial)

private theorem coprime_of_prime {n : ℕ} (hn : 148 < n) (hp : Nat.Prime n) :
    n.Coprime primorial := by
  rw [primorial_eq, Nat.coprime_prod_right_iff]
  intro p hMem
  obtain ⟨hRange, hPrime⟩ := mem_filter.mp hMem
  have hp149 : p < 149 := mem_range.mp hRange
  exact hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hPrime.pos (by omega))

/-- The bounded least-factor argument follows the accepted Taskdc0a505371b58c19da53c009. -/
private theorem prime_of_coprime {n : ℕ} (hn : 148 < n) (hN : n ≤ 22144)
    (hc : n.Coprime primorial) : Nat.Prime n := by
  by_contra hNot
  have hPrime := Nat.minFac_prime (show n ≠ 1 by omega)
  have hSquare := Nat.minFac_sq_le_self (show 0 < n by omega) hNot
  have hSmall : n.minFac < 149 := by
    by_contra! hLarge
    have h := Nat.pow_le_pow_left hLarge 2
    norm_num at h
    omega
  have hFactor : n.minFac ∣ primorial := by
    rw [primorial_eq]
    exact dvd_prod_of_mem (fun p : ℕ => p) (mem_filter.mpr ⟨mem_range.mpr hSmall, hPrime⟩)
  have hGcd := Nat.dvd_gcd (Nat.minFac_dvd n) hFactor
  rw [Nat.coprime_iff_gcd_eq_one.mp hc] at hGcd
  exact hPrime.not_dvd_one hGcd

theorem fastPrime_spec {n : ℕ} (hN : n ≤ 22144) : fastPrime n = true ↔ Nat.Prime n := by
  by_cases h : n ≤ 148
  · rw [fastPrime, ite_eq_left h, decide_eq_true_eq]
  · rw [fastPrime, ite_eq_right h, decide_eq_true_eq]
    have hn : 148 < n := Nat.lt_of_not_ge h
    exact ⟨prime_of_coprime hn hN, coprime_of_prime hn⟩

def charge (n : ℕ) : ℕ :=
  if fastPrime n then 10 ^ 9 / n else 0

private theorem charge_le (p : ℕ) (hp : p ≤ 22144) :
    (charge p : ℝ) / (10^9 : ℝ) ≤ if Nat.Prime p then 1 / (p : ℝ) else 0 := by
  by_cases h : Nat.Prime p
  · rw [charge, ite_eq_left ((fastPrime_spec hp).mpr h), ite_eq_left h]
    have hp0 : 0 < (p : ℝ) := by exact_mod_cast h.pos
    have hCast : (((10^9 : ℕ) / p : ℕ) : ℝ) * (p : ℝ) ≤ (10^9 : ℝ) := by
      exact_mod_cast Nat.div_mul_le_self (10^9 : ℕ) p
    apply (div_le_div_iff₀ (by positivity) hp0).mpr
    simpa only [one_mul] using hCast
  · have hFast : ¬ fastPrime p = true := fun he => h ((fastPrime_spec hp).mp he)
    rw [charge, ite_eq_right hFast, ite_eq_right h, Nat.cast_zero, zero_div]

theorem charge_lower_sum {n : ℕ} (hn : n ≤ 22144) :
    ((∑ p ∈ range n, charge p : ℕ) : ℝ) / (10^9 : ℝ) ≤
      ∑ p ∈ (range n).filter Nat.Prime, 1 / (p : ℝ) := by
  rw [Nat.cast_sum, sum_div, sum_filter]
  exact sum_le_sum fun p hp => charge_le p ((Nat.le_of_lt (mem_range.mp hp)).trans hn)

end GoldbachGridPrimes

namespace GoldbachGridScan

def scan (charge : ℕ → ℕ) (check : ℕ → ℕ → Bool) (n len seed : ℕ) : ℕ × Bool :=
  match len with
  | 0 => (seed, true)
  | l+1 =>
      let out := scan charge check (n+1) l (seed+charge n)
      (out.1, check n seed && out.2)
termination_by structural len

def Verified (charge : ℕ → ℕ) (check : ℕ → ℕ → Bool) (stop seed : ℕ) : Prop :=
  (∀ j < stop, check j (∑ p ∈ Finset.range j, charge p) = true) ∧
    (∑ p ∈ Finset.range stop, charge p) = seed

theorem verified_zero (charge : ℕ → ℕ) (check : ℕ → ℕ → Bool) :
    Verified charge check 0 0 := by
  refine ⟨?_, by simp⟩
  intro j hj
  omega

private theorem verified_step {charge : ℕ → ℕ} {check : ℕ → ℕ → Bool}
    {start seed : ℕ} (h : Verified charge check start seed) (hcheck : check start seed = true) :
    Verified charge check (start+1) (seed+charge start) := by
  refine ⟨?_, ?_⟩
  · intro j hj
    obtain hlt | rfl := lt_or_eq_of_le (Nat.lt_succ_iff.mp hj)
    · exact h.1 j hlt
    · rw [h.2]
      exact hcheck
  · rw [Finset.sum_range_succ, h.2]

theorem verified_extend {charge : ℕ → ℕ} {check : ℕ → ℕ → Bool}
    {start len seed next : ℕ} (h : Verified charge check start seed)
    (hscan : scan charge check start len seed = (next, true)) :
    Verified charge check (start+len) next := by
  induction len generalizing start seed with
  | zero =>
      have hseed : seed = next := congrArg Prod.fst hscan
      simpa only [Nat.add_zero, hseed] using h
  | succ len ih =>
      let out := scan charge check (start+1) len (seed+charge start)
      have hnext : out.1 = next := congrArg Prod.fst hscan
      have hboth : (check start seed && out.2) = true := congrArg Prod.snd hscan
      obtain ⟨hcheck, hout⟩ := Bool.and_eq_true_iff.mp hboth
      have hstep := verified_step h hcheck
      have hout' : out = (next, true) := Prod.ext hnext hout
      have hresult := ih hstep hout'
      simpa only [show start+1+len = start+(len+1) by omega] using hresult

end GoldbachGridScan

namespace GoldbachGridEndpoints

theorem ceil_exp_ten_le : Nat.ceil (Real.exp (10:ℝ)) ≤ 22027 := by
  have hr : (1+(5643/38411:ℝ))/(1-(5643/38411:ℝ)) = (22027:ℝ)/16384 := by
    norm_num
  have ht := Real.sum_range_le_log_div (x := (5643/38411:ℝ))
    (by norm_num) (by norm_num) 3
  rw [hr] at ht
  have hsum :
      (29595/200000:ℝ) <
        ∑ i ∈ Finset.range 3, (5643/38411:ℝ)^(2*i+1)/(2*i+1) := by
    norm_num [Finset.sum_range_succ]
  have hsmall : (29595/100000:ℝ) < Real.log ((22027:ℝ)/16384) := by
    linarith only [ht,hsum]
  have hlog : Real.log (22027:ℝ) =
      14 * Real.log 2 + Real.log ((22027:ℝ)/16384) := by
    calc
      _ = Real.log ((2:ℝ)^14*((22027:ℝ)/16384)) := congrArg Real.log (by norm_num)
      _ = _ := by
        rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
        norm_num
  have hten : (10:ℝ) ≤ Real.log (22027:ℝ) := by
    rw [hlog]
    linarith only [hsmall, Real.log_two_gt_d9]
  exact Nat.ceil_le.mpr (by
    simpa only [Nat.cast_ofNat, Real.exp_log (by norm_num : (0:ℝ) < 22027)] using
      Real.exp_le_exp.mpr hten)

theorem log_log_two_add_mertens_upper_le :
    Real.log (Real.log (2:ℝ)) + (0.261498:ℝ) ≤ 0 := by
  have hp := Real.log_pos (by norm_num : (1:ℝ) < 2)
  have h := Real.log_le_sub_one_of_pos hp
  linarith only [h, Real.log_two_lt_d9]

end GoldbachGridEndpoints

namespace GoldbachGridCertificates

def check (n s : ℕ) : Bool :=
  if 3 ≤ n ∧ (GoldbachGridPrimes.fastPrime n = true ∨ n = 22027) then
    decide (GoldbachGridLog.logLogUpper n + 261498000 ≤ s)
  else true

private theorem verified0 : GoldbachGridScan.Verified GoldbachGridPrimes.charge check 0 0 :=
  GoldbachGridScan.verified_zero GoldbachGridPrimes.charge check

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified128 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 128 1857670592 :=
  GoldbachGridScan.verified_extend verified0
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 0 128 0
      = (1857670592, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified256 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 256 1983639174 :=
  GoldbachGridScan.verified_extend verified128
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 128 128 1857670592
      = (1983639174, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified384 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 384 2053686904 :=
  GoldbachGridScan.verified_extend verified256
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 256 128 1983639174
      = (2053686904, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified512 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 512 2100662213 :=
  GoldbachGridScan.verified_extend verified384
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 384 128 2053686904
      = (2100662213, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified640 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 640 2131806703 :=
  GoldbachGridScan.verified_extend verified512
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 512 128 2100662213
      = (2131806703, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified768 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 768 2160536820 :=
  GoldbachGridScan.verified_extend verified640
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 640 128 2131806703
      = (2160536820, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified896 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 896 2183363115 :=
  GoldbachGridScan.verified_extend verified768
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 768 128 2160536820
      = (2183363115, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified1024 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 1024 2202019073 :=
  GoldbachGridScan.verified_extend verified896
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 896 128 2183363115
      = (2202019073, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified1152 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 1152 2218654625 :=
  GoldbachGridScan.verified_extend verified1024
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 1024 128 2202019073
      = (2218654625, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified1280 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 1280 2232653846 :=
  GoldbachGridScan.verified_extend verified1152
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 1152 128 2218654625
      = (2232653846, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified1408 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 1408 2243958127 :=
  GoldbachGridScan.verified_extend verified1280
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 1280 128 2232653846
      = (2243958127, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified1536 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 1536 2257599710 :=
  GoldbachGridScan.verified_extend verified1408
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 1408 128 2243958127
      = (2257599710, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified1664 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 1664 2269497865 :=
  GoldbachGridScan.verified_extend verified1536
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 1536 128 2257599710
      = (2269497865, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified1792 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 1792 2279316951 :=
  GoldbachGridScan.verified_extend verified1664
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 1664 128 2269497865
      = (2279316951, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified1920 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 1920 2287369332 :=
  GoldbachGridScan.verified_extend verified1792
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 1792 128 2279316951
      = (2287369332, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified2048 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 2048 2295417272 :=
  GoldbachGridScan.verified_extend verified1920
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 1920 128 2287369332
      = (2295417272, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified2176 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 2176 2303482106 :=
  GoldbachGridScan.verified_extend verified2048
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 2048 128 2295417272
      = (2303482106, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified2304 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 2304 2310602812 :=
  GoldbachGridScan.verified_extend verified2176
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 2176 128 2303482106
      = (2310602812, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified2432 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 2432 2318204249 :=
  GoldbachGridScan.verified_extend verified2304
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 2304 128 2310602812
      = (2318204249, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified2560 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 2560 2324206794 :=
  GoldbachGridScan.verified_extend verified2432
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 2432 128 2318204249
      = (2324206794, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified2688 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 2688 2329891445 :=
  GoldbachGridScan.verified_extend verified2560
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 2560 128 2324206794
      = (2329891445, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified2816 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 2816 2336813911 :=
  GoldbachGridScan.verified_extend verified2688
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 2688 128 2329891445
      = (2336813911, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified2944 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 2944 2342028004 :=
  GoldbachGridScan.verified_extend verified2816
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 2816 128 2336813911
      = (2342028004, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified3072 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 3072 2347015358 :=
  GoldbachGridScan.verified_extend verified2944
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 2944 128 2342028004
      = (2347015358, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified3200 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 3200 2351158660 :=
  GoldbachGridScan.verified_extend verified3072
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 3072 128 2347015358
      = (2351158660, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified3328 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 3328 2356060603 :=
  GoldbachGridScan.verified_extend verified3200
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 3200 128 2351158660
      = (2356060603, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified3456 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 3456 2360205174 :=
  GoldbachGridScan.verified_extend verified3328
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 3328 128 2356060603
      = (2360205174, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified3584 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 3584 2365887566 :=
  GoldbachGridScan.verified_extend verified3456
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 3456 128 2360205174
      = (2365887566, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified3712 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 3712 2370268391 :=
  GoldbachGridScan.verified_extend verified3584
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 3584 128 2365887566
      = (2370268391, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified3840 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 3840 2373976350 :=
  GoldbachGridScan.verified_extend verified3712
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 3712 128 2370268391
      = (2373976350, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified3968 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 3968 2378332061 :=
  GoldbachGridScan.verified_extend verified3840
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 3840 128 2373976350
      = (2378332061, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified4096 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 4096 2382046835 :=
  GoldbachGridScan.verified_extend verified3968
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 3968 128 2378332061
      = (2382046835, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified4224 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 4224 2385412961 :=
  GoldbachGridScan.verified_extend verified4096
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 4096 128 2382046835
      = (2385412961, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified4352 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 4352 2389151462 :=
  GoldbachGridScan.verified_extend verified4224
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 4224 128 2385412961
      = (2389151462, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified4480 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 4480 2392096250 :=
  GoldbachGridScan.verified_extend verified4352
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 4352 128 2389151462
      = (2392096250, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified4608 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 4608 2395621030 :=
  GoldbachGridScan.verified_extend verified4480
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 4480 128 2392096250
      = (2395621030, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified4736 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 4736 2399043130 :=
  GoldbachGridScan.verified_extend verified4608
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 4608 128 2395621030
      = (2399043130, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified4864 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 4864 2401543907 :=
  GoldbachGridScan.verified_extend verified4736
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 4736 128 2399043130
      = (2401543907, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified4992 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 4992 2404788009 :=
  GoldbachGridScan.verified_extend verified4864
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 4864 128 2401543907
      = (2404788009, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified5120 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 5120 2408349004 :=
  GoldbachGridScan.verified_extend verified4992
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 4992 128 2404788009
      = (2408349004, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified5248 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 5248 2410658993 :=
  GoldbachGridScan.verified_extend verified5120
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 5120 128 2408349004
      = (2410658993, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified5376 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 5376 2412732493 :=
  GoldbachGridScan.verified_extend verified5248
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 5248 128 2410658993
      = (2412732493, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified5504 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 5504 2416226276 :=
  GoldbachGridScan.verified_extend verified5376
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 5376 128 2412732493
      = (2416226276, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified5632 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 5632 2418386500 :=
  GoldbachGridScan.verified_extend verified5504
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 5504 128 2416226276
      = (2418386500, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified5760 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 5760 2421551305 :=
  GoldbachGridScan.verified_extend verified5632
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 5632 128 2418386500
      = (2421551305, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified5888 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 5888 2424636572 :=
  GoldbachGridScan.verified_extend verified5760
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 5760 128 2421551305
      = (2424636572, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified6016 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 6016 2426316523 :=
  GoldbachGridScan.verified_extend verified5888
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 5888 128 2424636572
      = (2426316523, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified6144 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 6144 2428946291 :=
  GoldbachGridScan.verified_extend verified6016
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 6016 128 2426316523
      = (2428946291, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified6272 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 6272 2431358695 :=
  GoldbachGridScan.verified_extend verified6144
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 6144 128 2428946291
      = (2431358695, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified6400 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 6400 2434198334 :=
  GoldbachGridScan.verified_extend verified6272
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 6272 128 2431358695
      = (2434198334, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified6528 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 6528 2435590517 :=
  GoldbachGridScan.verified_extend verified6400
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 6400 128 2434198334
      = (2435590517, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified6656 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 6656 2437717398 :=
  GoldbachGridScan.verified_extend verified6528
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 6528 128 2435590517
      = (2437717398, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified6784 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 6784 2440100241 :=
  GoldbachGridScan.verified_extend verified6656
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 6656 128 2437717398
      = (2440100241, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified6912 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 6912 2442436069 :=
  GoldbachGridScan.verified_extend verified6784
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 6784 128 2440100241
      = (2442436069, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified7040 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 7040 2444727593 :=
  GoldbachGridScan.verified_extend verified6912
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 6912 128 2442436069
      = (2444727593, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified7168 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 7168 2446275991 :=
  GoldbachGridScan.verified_extend verified7040
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 7040 128 2444727593
      = (2446275991, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified7296 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 7296 2448075819 :=
  GoldbachGridScan.verified_extend verified7168
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 7168 128 2446275991
      = (2448075819, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified7424 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 7424 2449708734 :=
  GoldbachGridScan.verified_extend verified7296
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 7296 128 2448075819
      = (2449708734, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified7552 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 7552 2451975744 :=
  GoldbachGridScan.verified_extend verified7424
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 7424 128 2449708734
      = (2451975744, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified7680 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 7680 2453947098 :=
  GoldbachGridScan.verified_extend verified7552
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 7552 128 2451975744
      = (2453947098, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified7808 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 7808 2455758255 :=
  GoldbachGridScan.verified_extend verified7680
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 7680 128 2453947098
      = (2455758255, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified7936 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 7936 2457662986 :=
  GoldbachGridScan.verified_extend verified7808
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 7808 128 2455758255
      = (2457662986, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified8064 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 8064 2459038313 :=
  GoldbachGridScan.verified_extend verified7936
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 7936 128 2457662986
      = (2459038313, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified8192 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 8192 2460884322 :=
  GoldbachGridScan.verified_extend verified8064
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 8064 128 2459038313
      = (2460884322, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified8320 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 8320 2462820894 :=
  GoldbachGridScan.verified_extend verified8192
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 8192 128 2460884322
      = (2462820894, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified8448 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 8448 2464369117 :=
  GoldbachGridScan.verified_extend verified8320
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 8320 128 2462820894
      = (2464369117, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified8576 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 8576 2465659868 :=
  GoldbachGridScan.verified_extend verified8448
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 8448 128 2464369117
      = (2465659868, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified8704 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 8704 2467510622 :=
  GoldbachGridScan.verified_extend verified8576
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 8576 128 2465659868
      = (2467510622, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified8832 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 8832 2469335939 :=
  GoldbachGridScan.verified_extend verified8704
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 8704 128 2467510622
      = (2469335939, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified8960 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 8960 2470798239 :=
  GoldbachGridScan.verified_extend verified8832
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 8832 128 2469335939
      = (2470798239, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified9088 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 9088 2472351072 :=
  GoldbachGridScan.verified_extend verified8960
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 8960 128 2470798239
      = (2472351072, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified9216 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 9216 2473989588 :=
  GoldbachGridScan.verified_extend verified9088
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 9088 128 2472351072
      = (2473989588, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified9344 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 9344 2475604911 :=
  GoldbachGridScan.verified_extend verified9216
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 9216 128 2473989588
      = (2475604911, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified9472 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 9472 2477303979 :=
  GoldbachGridScan.verified_extend verified9344
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 9344 128 2475604911
      = (2477303979, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified9600 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 9600 2478459349 :=
  GoldbachGridScan.verified_extend verified9472
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 9472 128 2477303979
      = (2478459349, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified9728 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 9728 2480012683 :=
  GoldbachGridScan.verified_extend verified9600
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 9600 128 2478459349
      = (2480012683, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified9856 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 9856 2481646998 :=
  GoldbachGridScan.verified_extend verified9728
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 9728 128 2480012683
      = (2481646998, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified9984 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 9984 2483059336 :=
  GoldbachGridScan.verified_extend verified9856
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 9856 128 2481646998
      = (2483059336, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified10112 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 10112 2484350752 :=
  GoldbachGridScan.verified_extend verified9984
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 9984 128 2483059336
      = (2484350752, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified10240 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 10240 2485530696 :=
  GoldbachGridScan.verified_extend verified10112
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 10112 128 2484350752
      = (2485530696, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified10368 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 10368 2487181749 :=
  GoldbachGridScan.verified_extend verified10240
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 10240 128 2485530696
      = (2487181749, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified10496 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 10496 2488331512 :=
  GoldbachGridScan.verified_extend verified10368
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 10368 128 2487181749
      = (2488331512, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified10624 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 10624 2489468013 :=
  GoldbachGridScan.verified_extend verified10496
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 10496 128 2488331512
      = (2489468013, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified10752 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 10752 2490872017 :=
  GoldbachGridScan.verified_extend verified10624
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 10624 128 2489468013
      = (2490872017, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified10880 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 10880 2491981013 :=
  GoldbachGridScan.verified_extend verified10752
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 10752 128 2490872017
      = (2491981013, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified11008 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 11008 2493260461 :=
  GoldbachGridScan.verified_extend verified10880
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 10880 128 2491981013
      = (2493260461, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified11136 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 11136 2494433481 :=
  GoldbachGridScan.verified_extend verified11008
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 11008 128 2493260461
      = (2494433481, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified11264 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 11264 2495593797 :=
  GoldbachGridScan.verified_extend verified11136
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 11136 128 2494433481
      = (2495593797, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified11392 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 11392 2496653622 :=
  GoldbachGridScan.verified_extend verified11264
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 11264 128 2495593797
      = (2496653622, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified11520 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 11520 2497962735 :=
  GoldbachGridScan.verified_extend verified11392
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 11392 128 2496653622
      = (2497962735, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified11648 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 11648 2498825892 :=
  GoldbachGridScan.verified_extend verified11520
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 11520 128 2497962735
      = (2498825892, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified11776 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 11776 2499680491 :=
  GoldbachGridScan.verified_extend verified11648
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 11648 128 2498825892
      = (2499680491, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified11904 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 11904 2501117473 :=
  GoldbachGridScan.verified_extend verified11776
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 11776 128 2499680491
      = (2501117473, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified12032 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 12032 2502288255 :=
  GoldbachGridScan.verified_extend verified11904
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 11904 128 2501117473
      = (2502288255, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified12160 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 12160 2503528552 :=
  GoldbachGridScan.verified_extend verified12032
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 12032 128 2502288255
      = (2503528552, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified12288 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 12288 2504673177 :=
  GoldbachGridScan.verified_extend verified12160
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 12160 128 2503528552
      = (2504673177, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified12416 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 12416 2505724994 :=
  GoldbachGridScan.verified_extend verified12288
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 12288 128 2504673177
      = (2505724994, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified12544 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 12544 2507006510 :=
  GoldbachGridScan.verified_extend verified12416
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 12416 128 2505724994
      = (2507006510, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified12672 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 12672 2508275285 :=
  GoldbachGridScan.verified_extend verified12544
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 12544 128 2507006510
      = (2508275285, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified12800 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 12800 2509217104 :=
  GoldbachGridScan.verified_extend verified12672
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 12672 128 2508275285
      = (2509217104, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified12928 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 12928 2510304584 :=
  GoldbachGridScan.verified_extend verified12800
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 12800 128 2509217104
      = (2510304584, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified13056 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 13056 2511458803 :=
  GoldbachGridScan.verified_extend verified12928
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 12928 128 2510304584
      = (2511458803, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified13184 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 13184 2512524796 :=
  GoldbachGridScan.verified_extend verified13056
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 13056 128 2511458803
      = (2512524796, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified13312 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 13312 2513354899 :=
  GoldbachGridScan.verified_extend verified13184
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 13184 128 2512524796
      = (2513354899, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified13440 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 13440 2514252433 :=
  GoldbachGridScan.verified_extend verified13312
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 13312 128 2513354899
      = (2514252433, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified13568 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 13568 2515215743 :=
  GoldbachGridScan.verified_extend verified13440
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 13440 128 2514252433
      = (2515215743, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified13696 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 13696 2516241891 :=
  GoldbachGridScan.verified_extend verified13568
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 13568 128 2515215743
      = (2516241891, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified13824 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 13824 2517260093 :=
  GoldbachGridScan.verified_extend verified13696
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 13696 128 2516241891
      = (2517260093, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified13952 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 13952 2518340364 :=
  GoldbachGridScan.verified_extend verified13824
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 13824 128 2517260093
      = (2518340364, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified14080 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 14080 2519125123 :=
  GoldbachGridScan.verified_extend verified13952
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 13952 128 2518340364
      = (2519125123, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified14208 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 14208 2519973600 :=
  GoldbachGridScan.verified_extend verified14080
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 14080 128 2519125123
      = (2519973600, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified14336 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 14336 2520673821 :=
  GoldbachGridScan.verified_extend verified14208
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 14208 128 2519973600
      = (2520673821, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified14464 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 14464 2521714912 :=
  GoldbachGridScan.verified_extend verified14336
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 14336 128 2520673821
      = (2521714912, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified14592 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 14592 2522609207 :=
  GoldbachGridScan.verified_extend verified14464
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 14464 128 2521714912
      = (2522609207, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified14720 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 14720 2523496190 :=
  GoldbachGridScan.verified_extend verified14592
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 14592 128 2522609207
      = (2523496190, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified14848 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 14848 2524646562 :=
  GoldbachGridScan.verified_extend verified14720
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 14720 128 2523496190
      = (2524646562, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified14976 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 14976 2525585456 :=
  GoldbachGridScan.verified_extend verified14848
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 14848 128 2524646562
      = (2525585456, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified15104 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 15104 2526316205 :=
  GoldbachGridScan.verified_extend verified14976
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 14976 128 2525585456
      = (2526316205, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified15232 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 15232 2527173456 :=
  GoldbachGridScan.verified_extend verified15104
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 15104 128 2526316205
      = (2527173456, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified15360 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 15360 2528285012 :=
  GoldbachGridScan.verified_extend verified15232
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 15232 128 2527173456
      = (2528285012, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified15488 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 15488 2529193006 :=
  GoldbachGridScan.verified_extend verified15360
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 15360 128 2528285012
      = (2529193006, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified15616 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 15616 2529964625 :=
  GoldbachGridScan.verified_extend verified15488
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 15488 128 2529193006
      = (2529964625, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified15744 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 15744 2530985129 :=
  GoldbachGridScan.verified_extend verified15616
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 15616 128 2529964625
      = (2530985129, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified15872 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 15872 2531744878 :=
  GoldbachGridScan.verified_extend verified15744
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 15744 128 2530985129
      = (2531744878, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified16000 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 16000 2532624085 :=
  GoldbachGridScan.verified_extend verified15872
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 15872 128 2531744878
      = (2532624085, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified16128 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 16128 2533557510 :=
  GoldbachGridScan.verified_extend verified16000
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 16000 128 2532624085
      = (2533557510, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified16256 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 16256 2534298120 :=
  GoldbachGridScan.verified_extend verified16128
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 16128 128 2533557510
      = (2534298120, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified16384 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 16384 2534971631 :=
  GoldbachGridScan.verified_extend verified16256
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 16256 128 2534298120
      = (2534971631, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified16512 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 16512 2535701117 :=
  GoldbachGridScan.verified_extend verified16384
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 16384 128 2534971631
      = (2535701117, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified16640 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 16640 2536424944 :=
  GoldbachGridScan.verified_extend verified16512
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 16512 128 2535701117
      = (2536424944, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified16768 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 16768 2537263208 :=
  GoldbachGridScan.verified_extend verified16640
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 16640 128 2536424944
      = (2537263208, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified16896 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 16896 2537856868 :=
  GoldbachGridScan.verified_extend verified16768
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 16768 128 2537263208
      = (2537856868, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified17024 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 17024 2538682484 :=
  GoldbachGridScan.verified_extend verified16896
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 16896 128 2537856868
      = (2538682484, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified17152 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 17152 2539443801 :=
  GoldbachGridScan.verified_extend verified17024
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 17024 128 2538682484
      = (2539443801, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified17280 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 17280 2540083214 :=
  GoldbachGridScan.verified_extend verified17152
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 17152 128 2539443801
      = (2540083214, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified17408 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 17408 2541005526 :=
  GoldbachGridScan.verified_extend verified17280
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 17280 128 2540083214
      = (2541005526, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified17536 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 17536 2541806954 :=
  GoldbachGridScan.verified_extend verified17408
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 17408 128 2541005526
      = (2541806954, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified17664 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 17664 2542545707 :=
  GoldbachGridScan.verified_extend verified17536
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 17536 128 2541806954
      = (2542545707, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified17792 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 17792 2543278769 :=
  GoldbachGridScan.verified_extend verified17664
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 17664 128 2542545707
      = (2543278769, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified17920 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 17920 2543894482 :=
  GoldbachGridScan.verified_extend verified17792
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 17792 128 2543278769
      = (2543894482, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified18048 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 18048 2544728811 :=
  GoldbachGridScan.verified_extend verified17920
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 17920 128 2543894482
      = (2544728811, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified18176 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 18176 2545501909 :=
  GoldbachGridScan.verified_extend verified18048
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 18048 128 2544728811
      = (2545501909, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified18304 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 18304 2546324299 :=
  GoldbachGridScan.verified_extend verified18176
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 18176 128 2545501909
      = (2546324299, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified18432 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 18432 2547032270 :=
  GoldbachGridScan.verified_extend verified18304
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 18304 128 2546324299
      = (2547032270, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified18560 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 18560 2547843500 :=
  GoldbachGridScan.verified_extend verified18432
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 18432 128 2547032270
      = (2547843500, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified18688 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 18688 2548272947 :=
  GoldbachGridScan.verified_extend verified18560
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 18560 128 2547843500
      = (2548272947, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified18816 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 18816 2548966257 :=
  GoldbachGridScan.verified_extend verified18688
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 18688 128 2548272947
      = (2548966257, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified18944 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 18944 2549389741 :=
  GoldbachGridScan.verified_extend verified18816
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 18816 128 2548966257
      = (2549389741, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified19072 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 19072 2549968493 :=
  GoldbachGridScan.verified_extend verified18944
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 18944 128 2549389741
      = (2549968493, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified19200 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 19200 2550543571 :=
  GoldbachGridScan.verified_extend verified19072
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 19072 128 2549968493
      = (2550543571, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified19328 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 19328 2551270614 :=
  GoldbachGridScan.verified_extend verified19200
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 19200 128 2550543571
      = (2551270614, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified19456 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 19456 2552043578 :=
  GoldbachGridScan.verified_extend verified19328
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 19328 128 2551270614
      = (2552043578, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified19584 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 19584 2552914646 :=
  GoldbachGridScan.verified_extend verified19456
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 19456 128 2552043578
      = (2552914646, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified19712 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 19712 2553372418 :=
  GoldbachGridScan.verified_extend verified19584
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 19584 128 2552914646
      = (2553372418, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified19840 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 19840 2553979464 :=
  GoldbachGridScan.verified_extend verified19712
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 19712 128 2553372418
      = (2553979464, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified19968 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 19968 2554682941 :=
  GoldbachGridScan.verified_extend verified19840
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 19840 128 2553979464
      = (2554682941, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified20096 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 20096 2555382091 :=
  GoldbachGridScan.verified_extend verified19968
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 19968 128 2554682941
      = (2555382091, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified20224 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 20224 2556126521 :=
  GoldbachGridScan.verified_extend verified20096
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 20096 128 2555382091
      = (2556126521, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified20352 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 20352 2556717899 :=
  GoldbachGridScan.verified_extend verified20224
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 20224 128 2556126521
      = (2556717899, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified20480 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 20480 2557403912 :=
  GoldbachGridScan.verified_extend verified20352
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 20352 128 2556717899
      = (2557403912, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified20608 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 20608 2557939424 :=
  GoldbachGridScan.verified_extend verified20480
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 20480 128 2557403912
      = (2557939424, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified20736 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 20736 2558471453 :=
  GoldbachGridScan.verified_extend verified20608
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 20608 128 2557939424
      = (2558471453, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified20864 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 20864 2559048821 :=
  GoldbachGridScan.verified_extend verified20736
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 20736 128 2558471453
      = (2559048821, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified20992 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 20992 2559717850 :=
  GoldbachGridScan.verified_extend verified20864
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 20864 128 2559048821
      = (2559717850, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified21120 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 21120 2560335538 :=
  GoldbachGridScan.verified_extend verified20992
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 20992 128 2559717850
      = (2560335538, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified21248 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 21248 2561043753 :=
  GoldbachGridScan.verified_extend verified21120
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 21120 128 2560335538
      = (2561043753, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified21376 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 21376 2561466087 :=
  GoldbachGridScan.verified_extend verified21248
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 21248 128 2561043753
      = (2561466087, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified21504 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 21504 2562212421 :=
  GoldbachGridScan.verified_extend verified21376
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 21376 128 2561466087
      = (2562212421, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified21632 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 21632 2562954158 :=
  GoldbachGridScan.verified_extend verified21504
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 21504 128 2562212421
      = (2562954158, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified21760 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 21760 2563507068 :=
  GoldbachGridScan.verified_extend verified21632
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 21632 128 2562954158
      = (2563507068, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified21888 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 21888 2564148482 :=
  GoldbachGridScan.verified_extend verified21760
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 21760 128 2563507068
      = (2564148482, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem verified22016 :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 22016 2564649400 :=
  GoldbachGridScan.verified_extend verified21888
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 21888 128 2564148482
      = (2564649400, true) by decide +kernel)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
theorem allVerified :
    GoldbachGridScan.Verified GoldbachGridPrimes.charge check 22028 2564694798 :=
  GoldbachGridScan.verified_extend verified22016
    (show GoldbachGridScan.scan GoldbachGridPrimes.charge check 22016 12 2564649400
      = (2564694798, true) by decide +kernel)

end GoldbachGridCertificates

theorem lowerGrid :
    ∀ n : ℕ, 2 ≤ n → n ≤ Nat.ceil (Real.exp (10 : ℝ)) →
      Real.log (Real.log (n : ℝ)) + (0.261498 : ℝ) - (2964e-9 : ℝ) / Real.log (n : ℝ) ≤
        ∑ p ∈ (Finset.range n).filter Nat.Prime, (1 : ℝ) / (p : ℝ) := by
  intro n hn₂ hnExp
  let S (m : ℕ) := ∑ p ∈ (Finset.range m).filter Nat.Prime, (1 : ℝ) / (p : ℝ)
  let target (m : ℕ) := Real.log (Real.log (m : ℝ)) + (0.261498 : ℝ) ≤ S m
  have hnCap : n ≤ 22027 := hnExp.trans GoldbachGridEndpoints.ceil_exp_ten_le

  have at_tested (m : ℕ) (hm₃ : 3 ≤ m) (hmCap : m ≤ 22027)
      (hTest : m.Prime ∨ m = 22027) : target m := by
    have hMod : m ≤ 22144 := by omega
    have hChecked := GoldbachGridCertificates.allVerified.1 m (by omega)
    have hCondition : 3 ≤ m ∧ (GoldbachGridPrimes.fastPrime m = true ∨ m = 22027) := by
      refine ⟨hm₃, ?_⟩
      exact hTest.imp (GoldbachGridPrimes.fastPrime_spec hMod).mpr id
    have hNumeric :
        GoldbachGridLog.logLogUpper m + 261498000 ≤
          ∑ p ∈ Finset.range m, GoldbachGridPrimes.charge p := by
      apply of_decide_eq_true
      simpa only [GoldbachGridCertificates.check, ite_eq_left hCondition] using hChecked
    have hLog : Real.log (Real.log (m : ℝ)) ≤
        (GoldbachGridLog.logLogUpper m : ℝ) / (10 ^ 9 : ℝ) := by
      simpa only [GoldbachGridLog.scale, Nat.cast_pow, Nat.cast_ofNat] using
        GoldbachGridLog.log_log_le_logLogUpper m hm₃
    change Real.log (Real.log (m : ℝ)) + (0.261498 : ℝ) ≤ S m
    calc
      _ ≤ (GoldbachGridLog.logLogUpper m : ℝ) / (10 ^ 9 : ℝ) + 0.261498 := by
        exact add_le_add hLog le_rfl
      _ = ((GoldbachGridLog.logLogUpper m + 261498000 : ℕ) : ℝ) / (10 ^ 9 : ℝ) := by
        push_cast
        ring
      _ ≤ ((∑ p ∈ Finset.range m, GoldbachGridPrimes.charge p : ℕ) : ℝ) / (10 ^ 9 : ℝ) :=
        div_le_div_of_nonneg_right (by exact_mod_cast hNumeric) (by positivity)
      _ ≤ S m := GoldbachGridPrimes.charge_lower_sum hMod

  have all_above_two (m : ℕ) (hmCap : m ≤ 22027) : 3 ≤ m → target m := by
    refine Nat.decreasingInduction (motive := fun k _ => 3 ≤ k → target k) ?_ ?_ hmCap
    · intro k hk hNext hk₃
      by_cases hPrime : Nat.Prime k
      · exact at_tested k hk₃ hk.le (Or.inl hPrime)
      · have hSum : S (k + 1) = S k := by
          simp only [S, Finset.range_add_one, Finset.filter_insert, ite_eq_right hPrime]
        have hR : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ k
        have hKpos : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
        have hLogPos : 0 < Real.log (k : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < k by omega))
        have hLogLe := Real.log_le_log hLogPos (Real.log_le_log hKpos hR)
        have hNext' : Real.log (Real.log ((k + 1 : ℕ) : ℝ)) + (0.261498 : ℝ) ≤ S (k + 1) :=
          hNext (by omega)
        exact (add_le_add hLogLe le_rfl).trans (hNext'.trans_eq hSum)
    · intro _
      exact at_tested 22027 (by decide) le_rfl (Or.inr rfl)

  have hStrong : target n := by
    by_cases hnTwo : n = 2
    · subst n
      exact GoldbachGridEndpoints.log_log_two_add_mertens_upper_le.trans
        (Finset.sum_nonneg fun _ _ => by positivity)
    · exact all_above_two n hnCap (by omega)
  have hLogNonneg : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  exact (sub_le_self _ (div_nonneg (by positivity) hLogNonneg)).trans hStrong
end
end SmallRangeInputs

-- Adapted from Qmhou, https://github.com/CGandGameEngineLearner/goldbach-proofs/pull/4820
-- The certificate is placed in a local namespace and its entry point is renamed.
namespace SmallRangeInputs
section
open Finset

namespace MertensGridUpper

private abbrev D : ℕ := 10^22
private abbrev K : ℕ := 1073741824
private def up (a b : ℕ) := a / b + 1

private theorem up_ge (a b : ℕ) (hb : 0 < b) : (a:ℝ)/b ≤ (up a b : ℝ) := by
  apply (div_le_iff₀ (by exact_mod_cast hb)).2
  exact_mod_cast (Nat.lt_mul_of_div_lt (Nat.lt_succ_self (a/b)) hb).le

private def sq : ℕ → ℕ → ℕ
  | 0, a => a
  | k+1, a => let b := sq k a; up (b*b) D
private def ex (a : ℕ) := sq 30 (up (D*D*K) (D*K-a))

private theorem sq_ge (k a : ℕ) (t : ℝ) (h : Real.exp t ≤ (a:ℝ)/D) :
    Real.exp ((2:ℝ)^k*t) ≤ (sq k a : ℝ)/D := by
  induction k with
  | zero => simpa [sq] using h
  | succ k ih =>
    rw [show (2:ℝ)^(k+1)*t=2^k*t+2^k*t by ring, Real.exp_add]
    apply (mul_self_le_mul_self (Real.exp_pos _).le ih).trans
    have hh := up_ge (sq k a * sq k a) D (by decide)
    push_cast at hh
    change _ ≤ (up (sq k a * sq k a) D : ℝ)/D
    norm_num [D] at hh ⊢
    linarith

private theorem ex_ge (a : ℕ) (ha : a < D*K) : Real.exp ((a:ℝ)/D) ≤ (ex a : ℝ)/D := by
  have hpos : 0 < D*K-a := by omega
  have hk : (a:ℝ) < (D:ℝ)*K := by exact_mod_cast ha
  have hh := up_ge (D*D*K) (D*K-a) hpos
  rw [Nat.cast_sub ha.le] at hh
  push_cast at hh
  have hfrac : (a:ℝ)/D/K < 1 := by
    apply (div_lt_iff₀ (by norm_num [K])).mpr
    apply (div_lt_iff₀ (by norm_num [D])).mpr
    simpa [mul_comm] using hk
  have ht := Real.exp_bound_div_one_sub_of_interval (by positivity : 0 ≤ (a:ℝ)/D/K) hfrac
  have h1 : Real.exp ((a:ℝ)/D/K) ≤ (up (D*D*K) (D*K-a) : ℝ)/D := by
    refine ht.trans ?_
    calc 1/(1-(a:ℝ)/D/K) = (((D:ℝ)*D*K)/((D:ℝ)*K-a))/D := by
           field_simp
           <;> ring
         _ ≤ _ := div_le_div_of_nonneg_right (by norm_num [D,K] at hh ⊢; exact hh) (by norm_num [D])
  have h2 := sq_ge 30 _ _ h1
  convert h2 using 2 <;> norm_num [K,ex] <;> ring

private noncomputable def S (i : ℕ) : ℝ := ∑ p ∈ (range i).filter Nat.Prime, (1:ℝ)/p
private theorem S_succ (i : ℕ) :
    S (i+1) = S i + if Nat.Prime i then (1:ℝ)/i else 0 := by
  simp [S,sum_filter,sum_range_succ]
private theorem S_mono : Monotone S := by
  apply monotone_nat_of_le_succ
  intro i
  rw [S_succ]
  apply le_add_of_nonneg_right; split <;> positivity
-- Bounded primality criterion adapted from the accepted lower-grid proof, commit
-- ed0b2428d69a876757ab067a438fcf6afce8e743.
def primorial : ℕ := 10014646650599190067509233131649940057366334653200433090

theorem primorial_eq : primorial = ∏ p ∈ (range 149).filter Nat.Prime, p := by
  decide +kernel

def fastPrime (n : ℕ) : Bool :=
  if n ≤ 148 then decide (Nat.Prime n) else decide (n.Coprime primorial)

private theorem coprime_of_prime {n : ℕ} (hn : 148 < n) (hp : Nat.Prime n) :
    n.Coprime primorial := by
  rw [primorial_eq, Nat.coprime_prod_right_iff]
  intro p hMem
  obtain ⟨hRange, hPrime⟩ := mem_filter.mp hMem
  have hp149 : p < 149 := mem_range.mp hRange
  exact hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hPrime.pos (by omega))

/-- The bounded least-factor argument follows the accepted Taskdc0a505371b58c19da53c009. -/
private theorem prime_of_coprime {n : ℕ} (hn : 148 < n) (hN : n ≤ 22144)
    (hc : n.Coprime primorial) : Nat.Prime n := by
  by_contra hNot
  have hPrime := Nat.minFac_prime (show n ≠ 1 by omega)
  have hSquare := Nat.minFac_sq_le_self (show 0 < n by omega) hNot
  have hSmall : n.minFac < 149 := by
    by_contra! hLarge
    have h := Nat.pow_le_pow_left hLarge 2
    norm_num at h
    omega
  have hFactor : n.minFac ∣ primorial := by
    rw [primorial_eq]
    exact dvd_prod_of_mem (fun p : ℕ => p) (mem_filter.mpr ⟨mem_range.mpr hSmall, hPrime⟩)
  have hGcd := Nat.dvd_gcd (Nat.minFac_dvd n) hFactor
  rw [Nat.coprime_iff_gcd_eq_one.mp hc] at hGcd
  exact hPrime.not_dvd_one hGcd

theorem fastPrime_spec {n : ℕ} (hN : n ≤ 22144) : fastPrime n = true ↔ Nat.Prime n := by
  by_cases h : n ≤ 148
  · rw [fastPrime, ite_eq_left h, decide_eq_true_eq]
  · rw [fastPrime, ite_eq_right h, decide_eq_true_eq]
    have hn : 148 < n := Nat.lt_of_not_ge h
    exact ⟨prime_of_coprime hn hN, coprime_of_prime hn⟩


private def primeTest (n : ℕ) : Bool := if n ≤ 22144 then fastPrime n else decide (Nat.Prime n)
private theorem primeTest_spec (n : ℕ) : primeTest n = true ↔ Nat.Prime n := by
  by_cases hn : n ≤ 22144
  · simpa [primeTest, hn] using fastPrime_spec hn
  · simp [primeTest, hn]
private def gain (i : ℕ) : ℕ → ℕ
  | 0 => 0
  | k+1 => gain i k + if primeTest (i+k) then up D (i+k) else 0
private theorem gain_ge (i k : ℕ) : S (i+k)-S i ≤ (gain i k : ℝ)/D := by
  induction k with
  | zero => simp [gain]
  | succ k ih =>
    rw [← Nat.add_assoc,S_succ]
    simp only [gain,Nat.cast_add,add_div]
    simp only [primeTest_spec]
    split_ifs with h
    · have hu := up_ge D (i+k) h.pos
      push_cast at hu
      norm_num [D,div_eq_mul_inv] at hu ih ⊢
      linarith
    · simp_all

private def Block (c i j s t : ℕ) : Prop := S i ≤ (s:ℝ)/D → S j ≤ (t:ℝ)/D ∧
  ∀ x : ℕ, i < x → x ≤ j → S x ≤ Real.log (Real.log ((max 2 (x-1):ℕ):ℝ)) + (c:ℝ)/D

private theorem segment (c i j s t : ℕ) (hij : i ≤ j) (hi : 2 ≤ i)
    (ht : s+gain i (j-i) ≤ t) (h1 : t-c < D*K) (h2 : ex (t-c) < D*K)
    (h3 : ex (ex (t-c)) ≤ i*D) : Block c i j s t := by
  intro hs
  have hg := gain_ge i (j-i)
  rw [Nat.add_sub_of_le hij] at hg
  have hh : (s:ℝ)+(gain i (j-i):ℝ) ≤ (t:ℝ) := by exact_mod_cast ht
  have hj : S j ≤ (t:ℝ)/D := by norm_num [D] at hs hg ⊢; linarith
  refine ⟨hj,?_⟩
  intro x hx hxj
  have hsub : (t:ℝ)/D-(c:ℝ)/D ≤ ((t-c:ℕ):ℝ)/D := by
    by_cases h : c≤t
    · rw [Nat.cast_sub h]; ring_nf; rfl
    · rw [Nat.sub_eq_zero_of_le (by omega)]; push_cast; have h' : (t:ℝ) ≤ c := by exact_mod_cast (show t≤c by omega)
      norm_num [D]; linarith
  have h4 := (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr hsub)).trans
    ((Real.exp_le_exp.mpr (ex_ge _ h1)).trans (ex_ge _ h2))
  have h5 : ((ex (ex (t-c))):ℝ) ≤ (i:ℝ)*D := by exact_mod_cast h3
  have lb : i ≤ max 2 (x-1) := by omega
  have hp : 0 < Real.log ((max 2 (x-1):ℕ):ℝ) := Real.log_pos (by exact_mod_cast (show 1 < max 2 (x-1) by omega))
  have h6 : Real.exp (Real.exp ((t:ℝ)/D-(c:ℝ)/D)) ≤ ((max 2 (x-1):ℕ):ℝ) := by
    apply h4.trans
    apply le_trans _ (Nat.cast_le.mpr lb)
    exact (div_le_iff₀ (by norm_num [D])).mpr h5
  have h7 := (Real.le_log_iff_exp_le (by positivity : (0:ℝ)<((max 2 (x-1):ℕ):ℝ))).mpr h6
  have h8 := (Real.le_log_iff_exp_le hp).mpr h7
  linarith [S_mono hxj]
private theorem join {c i j k s t u : ℕ} (a : Block c i j s t) (b : Block c j k t u) :
    Block c i k s u := by
  intro hs
  obtain ⟨ht,ha⟩ := a hs
  obtain ⟨hu,hb⟩ := b ht
  refine ⟨hu,fun x hi hk => ?_⟩
  by_cases h : x ≤ j
  · exact ha x hi h
  · exact hb x (by omega) hk



private theorem start_S : S 3 ≤ (5000000000000000000000:ℝ)/D := by
  norm_num [S,D,Finset.sum_filter,Finset.sum_range_succ]

private theorem log_cut : Real.log (7200:ℝ) ≤ 8.9 := by
  apply (Real.log_le_iff_le_exp (by norm_num)).mpr
  apply le_of_pow_le_pow_left₀ (n := 10) (by decide) (Real.exp_pos _).le
  rw [← Real.exp_nat_mul]
  norm_num1
  have h := pow_le_pow_left₀ (by norm_num : 0 ≤ (2.7182818283:ℝ)) Real.exp_one_gt_d9.le 89
  rw [← Real.exp_nat_mul] at h
  norm_num1 at h
  exact le_trans (by norm_num) h
private theorem b3 : Block 12614970000000000000000 3 17 5000000000000000000000 13440226440226440226444 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b17 : Block 12614970000000000000000 17 145 13440226440226440226444 18797977110648115591851 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b145 : Block 12614970000000000000000 145 273 18797977110648115591851 19987400431470443580043 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b273 : Block 12614970000000000000000 273 401 19987400431470443580043 20587765264224639184330 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b401 : Block 12614970000000000000000 401 529 20587765264224639184330 21044936926371312603697 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b529 : Block 12614970000000000000000 529 657 21044936926371312603697 21379990211254000644901 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b657 : Block 12614970000000000000000 657 785 21379990211254000644901 21631309390794561136810 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b785 : Block 12614970000000000000000 785 913 21631309390794561136810 21855634238659123026139 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b913 : Block 12614970000000000000000 913 1041 21855634238659123026139 22049196107055484121062 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b1041 : Block 12614970000000000000000 1041 1169 22049196107055484121062 22203818683777570761735 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b1169 : Block 12614970000000000000000 1169 1297 22203818683777570761735 22349837626952061985258 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b1297 : Block 12614970000000000000000 1297 1425 22349837626952061985258 22453707027768375439189 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b1425 : Block 12614970000000000000000 1425 1553 22453707027768375439189 22588934988278769424070 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b1553 : Block 12614970000000000000000 1553 1681 22588934988278769424070 22706970366969245440929 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b1681 : Block 12614970000000000000000 1681 1809 22706970366969245440929 22798723352283233071765 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b1809 : Block 12614970000000000000000 1809 1937 22798723352283233071765 22884046739300084359001 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b1937 : Block 12614970000000000000000 1937 2065 22884046739300084359001 22963892470117951147276 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b2065 : Block 12614970000000000000000 2065 2193 22963892470117951147276 23039411922867175838382 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b2193 : Block 12614970000000000000000 2193 2321 23039411922867175838382 23114687803657079118165 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b2321 : Block 12614970000000000000000 2321 2449 23114687803657079118165 23194330976321320631769 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b2449 : Block 12614970000000000000000 2449 2577 23194330976321320631769 23242069776195165338629 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b2577 : Block 12614970000000000000000 2577 2705 23242069776195165338629 23310053617529352627714 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b2705 : Block 12614970000000000000000 2705 2833 23310053617529352627714 23371688464634447864689 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b2833 : Block 12614970000000000000000 2833 2961 23371688464634447864689 23427050306186377385657 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b2961 : Block 12614970000000000000000 2961 3089 23427050306186377385657 23476647123912264631067 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b3089 : Block 12614970000000000000000 3089 3217 23476647123912264631067 23517827124461189813677 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b3217 : Block 12614970000000000000000 3217 3345 23517827124461189813677 23569605661685777481788 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b3345 : Block 12614970000000000000000 3345 3473 23569605661685777481788 23616490802688195787116 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b3473 : Block 12614970000000000000000 3473 3601 23616490802688195787116 23661661321736224862553 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b3601 : Block 12614970000000000000000 3601 3729 23661661321736224862553 23708058471646538664887 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b3729 : Block 12614970000000000000000 3729 3857 23708058471646538664887 23747557638612810577413 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b3857 : Block 12614970000000000000000 3857 3985 23747557638612810577413 23783323304547102461821 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b3985 : Block 12614970000000000000000 3985 4113 23783323304547102461821 23825343221710961656115 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b4113 : Block 12614970000000000000000 4113 4241 23825343221710961656115 23858860576511878011564 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b4241 : Block 12614970000000000000000 4241 4369 23858860576511878011564 23896104689558900867508 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b4369 : Block 12614970000000000000000 4369 4497 23896104689558900867508 23927653464710003036299 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b4497 : Block 12614970000000000000000 4497 4625 23927653464710003036299 23958377389825816503630 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b4625 : Block 12614970000000000000000 4625 4753 23958377389825816503630 23992539252383827305375 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b4753 : Block 12614970000000000000000 4753 4881 23992539252383827305375 24019545673815143278238 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b4881 : Block 12614970000000000000000 4881 5009 24019545673815143278238 24053885377625321811663 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b5009 : Block 12614970000000000000000 5009 5137 24053885377625321811663 24083493422759821368692 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b5137 : Block 12614970000000000000000 5137 5265 24083493422759821368692 24108494152626562609493 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b5265 : Block 12614970000000000000000 5265 5393 24108494152626562609493 24131043150820740939195 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b5393 : Block 12614970000000000000000 5393 5521 24131043150820740939195 24165894150163932795876 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b5521 : Block 12614970000000000000000 5521 5649 24165894150163932795876 24189185594590887668343 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b5649 : Block 12614970000000000000000 5649 5777 24189185594590887668343 24215516783490971464344 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b5777 : Block 12614970000000000000000 5777 5905 24215516783490971464344 24249759395473992209772 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b5905 : Block 12614970000000000000000 5905 6033 24249759395473992209772 24264827771611114835892 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b6033 : Block 12614970000000000000000 6033 6161 24264827771611114835892 24291092643374112271484 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b6161 : Block 12614970000000000000000 6161 6289 24291092643374112271484 24316774702045754303629 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b6289 : Block 12614970000000000000000 6289 6417 24316774702045754303629 24341987499748097385512 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b6417 : Block 12614970000000000000000 6417 6545 24341987499748097385512 24357441015115651319098 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b6545 : Block 12614970000000000000000 6545 6673 24357441015115651319098 24380181263688963530851 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b6673 : Block 12614970000000000000000 6673 6801 24380181263688963530851 24403951403088799783138 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b6801 : Block 12614970000000000000000 6801 6929 24403951403088799783138 24425810839455003272896 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b6929 : Block 12614970000000000000000 6929 7057 24425810839455003272896 24448700289202811727921 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b7057 : Block 12614970000000000000000 7057 7185 24448700289202811727921 24464157823655523709042 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b7185 : Block 12614970000000000000000 7185 7200 24464157823655523709042 24466939465308081152893 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem early : Block 12614970000000000000000 3 7200 5000000000000000000000 24466939465308081152893 := (join (join (join (join (join (join b3 b17) (join b145 b273)) (join (join b401 b529) (join b657 b785))) (join (join (join b913 b1041) (join b1169 b1297)) (join (join b1425 b1553) (join b1681 b1809)))) (join (join (join (join b1937 b2065) (join b2193 b2321)) (join (join b2449 b2577) (join b2705 b2833))) (join (join (join b2961 b3089) (join b3217 b3345)) (join (join b3473 b3601) (join b3729 b3857))))) (join (join (join (join (join b3985 b4113) (join b4241 b4369)) (join (join b4497 b4625) (join b4753 b4881))) (join (join (join b5009 b5137) (join b5265 b5393)) (join (join b5521 b5649) (join b5777 b5905)))) (join (join (join (join b6033 b6161) (join b6289 b6417)) (join (join b6545 b6673) (join b6801 b6929))) (join b7057 b7185))))
private theorem b7200 : Block 2631110000000000000000 7200 7219 24466939465308081152893 24471100161104528537202 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b7219 : Block 2631110000000000000000 7219 7237 24471100161104528537202 24473868711710991159825 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b7237 : Block 2631110000000000000000 7237 7247 24473868711710991159825 24476631143124521781636 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b7247 : Block 2631110000000000000000 7247 7253 24476631143124521781636 24478011024454727383955 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b7253 : Block 2631110000000000000000 7253 7283 24478011024454727383955 24479389764286521124477 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b7283 : Block 2631110000000000000000 7283 7309 24479389764286521124477 24483501801745844072081 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b7309 : Block 2631110000000000000000 7309 7333 24483501801745844072081 24487599981968599549222 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b7333 : Block 2631110000000000000000 7333 7369 24487599981968599549222 24491684768804268235679 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b7369 : Block 2631110000000000000000 7369 7433 24491684768804268235679 24497092035482627532994 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b7433 : Block 2631110000000000000000 7433 7489 24497092035482627532994 24506470976116523669302 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b7489 : Block 2631110000000000000000 7489 7537 24506470976116523669302 24514459641589043649147 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b7537 : Block 2631110000000000000000 7537 7573 24514459641589043649147 24522407724779757676111 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b7573 : Block 2631110000000000000000 7573 7591 24522407724779757676111 24527684424941683721324 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b7591 : Block 2631110000000000000000 7591 7607 24527684424941683721324 24530317044722548359671 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b7607 : Block 2631110000000000000000 7607 7621 24530317044722548359671 24531631623400082210072 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b7621 : Block 2631110000000000000000 7621 7643 24531631623400082210072 24534252859026164768792 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b7643 : Block 2631110000000000000000 7643 7673 24534252859026164768792 24538172557196007347759 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b7673 : Block 2631110000000000000000 7673 7691 24538172557196007347759 24542078639839409218285 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b7691 : Block 2631110000000000000000 7691 7703 24542078639839409218285 24544677730860100296491 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b7703 : Block 2631110000000000000000 7703 7717 24544677730860100296491 24545975926368343837969 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b7717 : Block 2631110000000000000000 7717 7727 24545975926368343837969 24548566600334693030182 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b7727 : Block 2631110000000000000000 7727 7741 24548566600334693030182 24549860763658104444703 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b7741 : Block 2631110000000000000000 7741 7753 24549860763658104444703 24551152586420021509682 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b7753 : Block 2631110000000000000000 7753 7759 24551152586420021509682 24553731567893938853344 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b7759 : Block 2631110000000000000000 7759 7789 24553731567893938853344 24555020393773562516188 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b7789 : Block 2631110000000000000000 7789 7823 24555020393773562516188 24558866721648830008242 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b7823 : Block 2631110000000000000000 7823 7867 24558866721648830008242 24563971052208635910729 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b7867 : Block 2631110000000000000000 7867 7901 24563971052208635910729 24570319616671313287139 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b7901 : Block 2631110000000000000000 7901 7927 24570319616671313287139 24574112767113577477890 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b7927 : Block 2631110000000000000000 7927 7949 24574112767113577477890 24577894757455214158056 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b7949 : Block 2631110000000000000000 7949 7993 24577894757455214158056 24581666288877978990559 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b7993 : Block 2631110000000000000000 7993 8053 24581666288877978990559 24587905547721612150721 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b8053 : Block 2631110000000000000000 8053 8093 24587905547721612150721 24595337750514049004270 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b8093 : Block 2631110000000000000000 8093 8147 24595337750514049004270 24601503749877572748550 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b8147 : Block 2631110000000000000000 8147 8209 24601503749877572748550 24608848311334690708903 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b8209 : Block 2631110000000000000000 8209 8263 24608848311334690708903 24617356304638091630541 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b8263 : Block 2631110000000000000000 8263 8297 24617356304638091630541 24624603278957312202421 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b8297 : Block 2631110000000000000000 8297 8353 24624603278957312202421 24629414739454388640260 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b8353 : Block 2631110000000000000000 8353 8419 24629414739454388640260 24636580646583730627944 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b8419 : Block 2631110000000000000000 8419 8467 24636580646583730627944 24644878299607483976995 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b8467 : Block 2631110000000000000000 8467 8539 24644878299607483976995 24651928049945894869854 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b8539 : Block 2631110000000000000000 8539 8623 24651928049945894869854 24661257026910008038812 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b8623 : Block 2631110000000000000000 8623 8689 24661257026910008038812 24671660777553138351293 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b8689 : Block 2631110000000000000000 8689 8737 24671660777553138351293 24679700042472241848292 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b8737 : Block 2631110000000000000000 8737 8783 24679700042472241848292 24686554852630588018932 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b8783 : Block 2631110000000000000000 8783 8831 24686554852630588018932 24692232426290103436926 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b8831 : Block 2631110000000000000000 8831 8863 24692232426290103436926 24697886368319602235426 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b8863 : Block 2631110000000000000000 8863 8923 24697886368319602235426 24702392150645545435688 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b8923 : Block 2631110000000000000000 8923 8969 24702392150645545435688 24709103575565737136314 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b8969 : Block 2631110000000000000000 8969 9011 24709103575565737136314 24714665699831884180556 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b9011 : Block 2631110000000000000000 9011 9049 24714665699831884180556 24720204405476494359072 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b9049 : Block 2631110000000000000000 9049 9103 24720204405476494359072 24724616264190681690827 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b9103 : Block 2631110000000000000000 9103 9157 24724616264190681690827 24731190427100162907776 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b9157 : Block 2631110000000000000000 9157 9203 24731190427100162907776 24737729002862084303926 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b9203 : Block 2631110000000000000000 9203 9241 24737729002862084303926 24743152124463545613861 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b9241 : Block 2631110000000000000000 9241 9283 24743152124463545613861 24747469926793408731465 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b9283 : Block 2631110000000000000000 9283 9337 24747469926793408731465 24752842934641691671906 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b9337 : Block 2631110000000000000000 9337 9391 24752842934641691671906 24759258005925000399748 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b9391 : Block 2631110000000000000000 9391 9431 24759258005925000399748 24765636017879637174943 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b9431 : Block 2631110000000000000000 9431 9461 24765636017879637174943 24769875552007184825354 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b9461 : Block 2631110000000000000000 9461 9473 24769875552007184825354 24773045570895286475083 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b9473 : Block 2631110000000000000000 9473 9491 24773045570895286475083 24775156166294671829880 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b9491 : Block 2631110000000000000000 9491 9511 24775156166294671829880 24777262760143100494260 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b9511 : Block 2631110000000000000000 9511 9533 24777262760143100494260 24779364484136538194594 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b9533 : Block 2631110000000000000000 9533 9547 24779364484136538194594 24781461799780354219500 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b9547 : Block 2631110000000000000000 9547 9587 24781461799780354219500 24783556260025128824685 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b9587 : Block 2631110000000000000000 9587 9623 24783556260025128824685 24787720764456817461435 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b9623 : Block 2631110000000000000000 9623 9649 24787720764456817461435 24791873806323142276102 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b9649 : Block 2631110000000000000000 9649 9679 24791873806323142276102 24794978650798052797254 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b9679 : Block 2631110000000000000000 9679 9719 24794978650798052797254 24798075160414278656512 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b9719 : Block 2631110000000000000000 9719 9749 24798075160414278656512 24803213383429509857497 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b9749 : Block 2631110000000000000000 9749 9781 24803213383429509857497 24806286631728853684626 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b9781 : Block 2631110000000000000000 9781 9803 24806286631728853684626 24809352131775604986469 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b9803 : Block 2631110000000000000000 9803 9829 24809352131775604986469 24812410132888673555923 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b9829 : Block 2631110000000000000000 9829 9851 24812410132888673555923 24815460877464009606665 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b9851 : Block 2631110000000000000000 9851 9859 24815460877464009606665 24817490510288622358789 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b9859 : Block 2631110000000000000000 9859 9871 24817490510288622358789 24818504811941934053688 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b9871 : Block 2631110000000000000000 9871 9883 24818504811941934053688 24819517880526677240802 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b9883 : Block 2631110000000000000000 9883 9901 24819517880526677240802 24821541148186639038603 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b9901 : Block 2631110000000000000000 9901 9923 24821541148186639038603 24823560534478547790603 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b9923 : Block 2631110000000000000000 9923 9931 24823560534478547790603 24825575444999093711995 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b9931 : Block 2631110000000000000000 9931 9941 24825575444999093711995 24826582392939885173077 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b9941 : Block 2631110000000000000000 9941 9949 24826582392939885173077 24827588327956483100851 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b9949 : Block 2631110000000000000000 9949 9967 24827588327956483100851 24828593454099814088890 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b9967 : Block 2631110000000000000000 9967 10007 24828593454099814088890 24830599472335606361618 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b10007 : Block 2631110000000000000000 10007 10061 24830599472335606361618 24834590302424980427643 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b10061 : Block 2631110000000000000000 10061 10099 24834590302424980427643 24840544660961461223305 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b10099 : Block 2631110000000000000000 10099 10139 24840544660961461223305 24844500559444712783783 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b10139 : Block 2631110000000000000000 10139 10163 24844500559444712783783 24848442419523164766036 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b10163 : Block 2631110000000000000000 10163 10181 24848442419523164766036 24851392369656495731460 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b10181 : Block 2631110000000000000000 10181 10211 24851392369656495731460 24853355656879239590038 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b10211 : Block 2631110000000000000000 10211 10247 24853355656879239590038 24856289455813260154445 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b10247 : Block 2631110000000000000000 10247 10271 24856289455813260154445 24860189423718082601572 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b10271 : Block 2631110000000000000000 10271 10301 24860189423718082601572 24863108375985390946088 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b10301 : Block 2631110000000000000000 10301 10321 24863108375985390946088 24866019396567697873901 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b10321 : Block 2631110000000000000000 10321 10333 24866019396567697873901 24867956255437470946951 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b10333 : Block 2631110000000000000000 10333 10337 24867956255437470946951 24868924028591443655749 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b10337 : Block 2631110000000000000000 10337 10343 24868924028591443655749 24869891427256433498064 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b10343 : Block 2631110000000000000000 10343 10357 24869891427256433498064 24870858264731054014356 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b10357 : Block 2631110000000000000000 10357 10369 24870858264731054014356 24871823795290096208042 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b10369 : Block 2631110000000000000000 10369 10391 24871823795290096208042 24872788208444691636724 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b10391 : Block 2631110000000000000000 10391 10429 24872788208444691636724 24875671259277348363435 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b10429 : Block 2631110000000000000000 10429 10459 24875671259277348363435 24879501581434199367328 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b10459 : Block 2631110000000000000000 10459 10487 24879501581434199367328 24882367916314597561756 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b10487 : Block 2631110000000000000000 10487 10513 24882367916314597561756 24885226239789034425952 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b10513 : Block 2631110000000000000000 10513 10559 24885226239789034425952 24888076778310971755990 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b10559 : Block 2631110000000000000000 10559 10607 24888076778310971755990 24892801526853864954991 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b10607 : Block 2631110000000000000000 10607 10651 24892801526853864954991 24897508123730234283528 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b10651 : Block 2631110000000000000000 10651 10691 24897508123730234283528 24902196362460068882661 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b10691 : Block 2631110000000000000000 10691 10729 24902196362460068882661 24905931717143465188192 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b10729 : Block 2631110000000000000000 10729 10771 24905931717143465188192 24909656634840310811814 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b10771 : Block 2631110000000000000000 10771 10837 24909656634840310811814 24914288768893756844124 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b10837 : Block 2631110000000000000000 10837 10889 24914288768893756844124 24920735553706544048159 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b10889 : Block 2631110000000000000000 10889 10949 24920735553706544048159 24926234441932721350904 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b10949 : Block 2631110000000000000000 10949 11003 24926234441932721350904 24931702419845869951651 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b11003 : Block 2631110000000000000000 11003 11071 24931702419845869951651 24937135420310301421304 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b11071 : Block 2631110000000000000000 11071 11131 24937135420310301421304 24943443122231498223981 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b11131 : Block 2631110000000000000000 11131 11197 24943443122231498223981 24949715454485788769693 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b11197 : Block 2631110000000000000000 11197 11273 24949715454485788769693 24955944740670268916253 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b11273 : Block 2631110000000000000000 11273 11351 24955944740670268916253 24963023154661282975314 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b11351 : Block 2631110000000000000000 11351 11443 24963023154661282975314 24970924177823478293459 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b11443 : Block 2631110000000000000000 11443 11527 24970924177823478293459 24979634255196447838869 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b11527 : Block 2631110000000000000000 11527 11633 24979634255196447838869 24987406253998552132095 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b11633 : Block 2631110000000000000000 11633 11761 24987406253998552132095 24996811902773275880837 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b11761 : Block 2631110000000000000000 11761 11887 24996811902773275880837 25008659881027494294965 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b11887 : Block 2631110000000000000000 11887 11981 25008659881027494294965 25019555356799972582829 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b11981 : Block 2631110000000000000000 11981 12101 25019555356799972582829 25028694613837006757991 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b12101 : Block 2631110000000000000000 12101 12211 25028694613837006757991 25038576517040470209271 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b12211 : Block 2631110000000000000000 12211 12323 25038576517040470209271 25048365684966846239318 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b12323 : Block 2631110000000000000000 12323 12433 25048365684966846239318 25058062327805383114362 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b12433 : Block 2631110000000000000000 12433 12527 25058062327805383114362 25067679298650479339225 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b12527 : Block 2631110000000000000000 12527 12611 25067679298650479339225 25075639461837314710852 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b12611 : Block 2631110000000000000000 12611 12689 25075639461837314710852 25082760295951853064348 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b12689 : Block 2631110000000000000000 12689 12763 25082760295951853064348 25089049500372077911616 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b12763 : Block 2631110000000000000000 12763 12841 25089049500372077911616 25095298541476076553559 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b12841 : Block 2631110000000000000000 12841 12919 25095298541476076553559 25101505529743551066626 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b12919 : Block 2631110000000000000000 12919 13001 25101505529743551066626 25108452555324107843054 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b13001 : Block 2631110000000000000000 13001 13063 25108452555324107843054 25114595663317558123079 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b13063 : Block 2631110000000000000000 13063 13147 25114595663317558123079 25119938312617079146646 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b13147 : Block 2631110000000000000000 13147 13219 25119938312617079146646 25126770600758907050861 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b13219 : Block 2631110000000000000000 13219 13309 25126770600758907050861 25132805399347658817601 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b13309 : Block 2631110000000000000000 13309 13399 25132805399347658817601 25139549754071663887054 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b13399 : Block 2631110000000000000000 13399 13487 25139549754071663887054 25146989925133494266848 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b13487 : Block 2631110000000000000000 13487 13597 25146989925133494266848 25153637648013679317712 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b13597 : Block 2631110000000000000000 13597 13697 25153637648013679317712 25162426868520100331686 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b13697 : Block 2631110000000000000000 13697 13781 25162426868520100331686 25169709148558315155063 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b13781 : Block 2631110000000000000000 13781 13877 25169709148558315155063 25176219961708837533476 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b13877 : Block 2631110000000000000000 13877 13963 25176219961708837533476 25183411736768257152054 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b13963 : Block 2631110000000000000000 13963 14057 25183411736768257152054 25189837324207453854241 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b14057 : Block 2631110000000000000000 14057 14173 25189837324207453854241 25196925046036720907511 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b14173 : Block 2631110000000000000000 14173 14301 25196925046036720907511 25203952901086359883936 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b14301 : Block 2631110000000000000000 14301 14429 25203952901086359883936 25213696076176532471431 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b14429 : Block 2631110000000000000000 14429 14557 25213696076176532471431 25223354758163664246072 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b14557 : Block 2631110000000000000000 14557 14685 25223354758163664246072 25232930938371729824005 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b14685 : Block 2631110000000000000000 14685 14797 25232930938371729824005 25242426169474640582452 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b14797 : Block 2631110000000000000000 14797 14897 25242426169474640582452 25250508097961428750457 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b14897 : Block 2631110000000000000000 14897 15025 25250508097961428750457 25257862643843213576226 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b15025 : Block 2631110000000000000000 15025 15149 25257862643843213576226 25266476123925588711923 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b15149 : Block 2631110000000000000000 15149 15271 25266476123925588711923 25275021414053294937724 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b15271 : Block 2631110000000000000000 15271 15373 25275021414053294937724 25283510024817947545262 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b15373 : Block 2631110000000000000000 15373 15467 25283510024817947545262 25290646210996611386544 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b15467 : Block 2631110000000000000000 15467 15569 25290646210996611386544 25296447737538455829591 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b15569 : Block 2631110000000000000000 15569 15661 25296447737538455829591 25303492104067321349034 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b15661 : Block 2631110000000000000000 15661 15749 25303492104067321349034 25309860420313079567568 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b15749 : Block 2631110000000000000000 15749 15817 25309860420313079567568 25315563168231735196436 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b15817 : Block 2631110000000000000000 15817 15901 25315563168231735196436 25319976284427751830394 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b15901 : Block 2631110000000000000000 15901 15991 25319976284427751830394 25325624716963865084388 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b15991 : Block 2631110000000000000000 15991 16073 25325624716963865084388 25331236136217739980294 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b16073 : Block 2631110000000000000000 16073 16141 25331236136217739980294 25336204008173709048601 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b16141 : Block 2631110000000000000000 16141 16231 25336204008173709048601 25341143741320735316681 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b16231 : Block 2631110000000000000000 16231 16349 25341143741320735316681 25346670328057293153575 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b16349 : Block 2631110000000000000000 16349 16453 25346670328057293153575 25353986318218057365677 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b16453 : Block 2631110000000000000000 16453 16573 25353986318218057365677 25360646890231524704780 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b16573 : Block 2631110000000000000000 16573 16693 25360646890231524704780 25367859610765013966787 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b16693 : Block 2631110000000000000000 16693 16821 25367859610765013966787 25373832213382561234042 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b16821 : Block 2631110000000000000000 16821 16949 25373832213382561234042 25382714624518215789111 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b16949 : Block 2631110000000000000000 16949 17077 25382714624518215789111 25390355999012210337443 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b17077 : Block 2631110000000000000000 17077 17205 25390355999012210337443 25397939788517545826992 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b17205 : Block 2631110000000000000000 17205 17333 25397939788517545826992 25404308550418750391724 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b17333 : Block 2631110000000000000000 17333 17461 25404308550418750391724 25412933471069199884209 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b17461 : Block 2631110000000000000000 17461 17589 25412933471069199884209 25421495323540926525991 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b17589 : Block 2631110000000000000000 17589 17717 25421495323540926525991 25428293452907220462747 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b17717 : Block 2631110000000000000000 17717 17845 25428293452907220462747 25435041500244393207166 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b17845 : Block 2631110000000000000000 17845 17973 25435041500244393207166 25442856271591311440812 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b17973 : Block 2631110000000000000000 17973 18101 25442856271591311440812 25450618376858860917767 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b18101 : Block 2631110000000000000000 18101 18229 25450618376858860917767 25458325415918995145823 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b18229 : Block 2631110000000000000000 18229 18341 25458325415918995145823 25465437363409297818385 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b18341 : Block 2631110000000000000000 18341 18451 25465437363409297818385 25471960187438272238382 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b18451 : Block 2631110000000000000000 18451 18553 25471960187438272238382 25477906530054814273577 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b18553 : Block 2631110000000000000000 18553 18681 25477906530054814273577 25482740037941062504287 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b18681 : Block 2631110000000000000000 18681 18809 25482740037941062504287 25489673198617266873179 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b18809 : Block 2631110000000000000000 18809 18937 25489673198617266873179 25493908085303715133407 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b18937 : Block 2631110000000000000000 18937 19065 25493908085303715133407 25499171259007863174521 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b19065 : Block 2631110000000000000000 19065 19193 25499171259007863174521 25505446509350673294276 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b19193 : Block 2631110000000000000000 19193 19321 25505446509350673294276 25512716997090043299720 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b19321 : Block 2631110000000000000000 19321 19449 25512716997090043299720 25520446716674982738153 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b19449 : Block 2631110000000000000000 19449 19577 25520446716674982738153 25528136029435988331465 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b19577 : Block 2631110000000000000000 19577 19705 25528136029435988331465 25533227864326275342053 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b19705 : Block 2631110000000000000000 19705 19833 25533227864326275342053 25539805781680736440896 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b19833 : Block 2631110000000000000000 19833 19961 25539805781680736440896 25545838731460229509314 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b19961 : Block 2631110000000000000000 19961 20089 25545838731460229509314 25553334431352190345857 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b20089 : Block 2631110000000000000000 20089 20217 25553334431352190345857 25560781994749823847717 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b20217 : Block 2631110000000000000000 20217 20345 25560781994749823847717 25566698936182368238003 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b20345 : Block 2631110000000000000000 20345 20473 25566698936182368238003 25573073929060122406865 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b20473 : Block 2631110000000000000000 20473 20601 25573073929060122406865 25579405744992750482042 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b20601 : Block 2631110000000000000000 20601 20729 25579405744992750482042 25584243736810806221149 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b20729 : Block 2631110000000000000000 20729 20857 25584243736810806221149 25590020388005036550881 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b20857 : Block 2631110000000000000000 20857 20985 25590020388005036550881 25597190196148219525993 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b20985 : Block 2631110000000000000000 20985 21113 25597190196148219525993 25603367136559811439593 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b21113 : Block 2631110000000000000000 21113 21241 25603367136559811439593 25609978720784788498840 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b21241 : Block 2631110000000000000000 21241 21369 25609978720784788498840 25614672773140129198035 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b21369 : Block 2631110000000000000000 21369 21497 25614672773140129198035 25621206002846523890234 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b21497 : Block 2631110000000000000000 21497 21625 25621206002846523890234 25629553661635436290215 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b21625 : Block 2631110000000000000000 21625 21753 25629553661635436290215 25634623203587922373431 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b21753 : Block 2631110000000000000000 21753 21881 25634623203587922373431 25641040025553414673251 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b21881 : Block 2631110000000000000000 21881 22009 25641040025553414673251 25646051992254759736017 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem b22009 : Block 2631110000000000000000 22009 22027 25646051992254759736017 25646506269272885389041 := segment _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem late : Block 2631110000000000000000 7200 22027 24466939465308081152893 25646506269272885389041 := (join (join (join (join (join (join (join (join b7200 b7219) (join b7237 b7247)) (join (join b7253 b7283) (join b7309 b7333))) (join (join (join b7369 b7433) (join b7489 b7537)) (join (join b7573 b7591) (join b7607 b7621)))) (join (join (join (join b7643 b7673) (join b7691 b7703)) (join (join b7717 b7727) (join b7741 b7753))) (join (join (join b7759 b7789) (join b7823 b7867)) (join (join b7901 b7927) (join b7949 b7993))))) (join (join (join (join (join b8053 b8093) (join b8147 b8209)) (join (join b8263 b8297) (join b8353 b8419))) (join (join (join b8467 b8539) (join b8623 b8689)) (join (join b8737 b8783) (join b8831 b8863)))) (join (join (join (join b8923 b8969) (join b9011 b9049)) (join (join b9103 b9157) (join b9203 b9241))) (join (join (join b9283 b9337) (join b9391 b9431)) (join (join b9461 b9473) (join b9491 b9511)))))) (join (join (join (join (join (join b9533 b9547) (join b9587 b9623)) (join (join b9649 b9679) (join b9719 b9749))) (join (join (join b9781 b9803) (join b9829 b9851)) (join (join b9859 b9871) (join b9883 b9901)))) (join (join (join (join b9923 b9931) (join b9941 b9949)) (join (join b9967 b10007) (join b10061 b10099))) (join (join (join b10139 b10163) (join b10181 b10211)) (join (join b10247 b10271) (join b10301 b10321))))) (join (join (join (join (join b10333 b10337) (join b10343 b10357)) (join (join b10369 b10391) (join b10429 b10459))) (join (join (join b10487 b10513) (join b10559 b10607)) (join (join b10651 b10691) (join b10729 b10771)))) (join (join (join (join b10837 b10889) (join b10949 b11003)) (join (join b11071 b11131) (join b11197 b11273))) (join (join (join b11351 b11443) (join b11527 b11633)) (join (join b11761 b11887) (join b11981 b12101))))))) (join (join (join (join (join (join (join b12211 b12323) (join b12433 b12527)) (join (join b12611 b12689) (join b12763 b12841))) (join (join (join b12919 b13001) (join b13063 b13147)) (join (join b13219 b13309) (join b13399 b13487)))) (join (join (join (join b13597 b13697) (join b13781 b13877)) (join (join b13963 b14057) (join b14173 b14301))) (join (join (join b14429 b14557) (join b14685 b14797)) (join (join b14897 b15025) (join b15149 b15271))))) (join (join (join (join (join b15373 b15467) (join b15569 b15661)) (join (join b15749 b15817) (join b15901 b15991))) (join (join (join b16073 b16141) (join b16231 b16349)) (join (join b16453 b16573) (join b16693 b16821)))) (join (join (join (join b16949 b17077) (join b17205 b17333)) (join (join b17461 b17589) (join b17717 b17845))) (join (join (join b17973 b18101) (join b18229 b18341)) (join (join b18451 b18553) (join b18681 b18809)))))) (join (join (join (join (join b18937 b19065) (join b19193 b19321)) (join (join b19449 b19577) (join b19705 b19833))) (join (join (join b19961 b20089) (join b20217 b20345)) (join (join b20473 b20601) (join b20729 b20857)))) (join (join (join (join b20985 b21113) (join b21241 b21369)) (join (join b21497 b21625) (join b21753 b21881))) b22009))))

end MertensGridUpper

open MertensGridUpper in
theorem upperGrid :
  ∀ (x : ℕ), 2 ≤ x → x ≤ ⌈Real.exp (10 : ℝ)⌉₊ →
    ∑ p ∈ Finset.range x with Nat.Prime p, (1 : ℝ)/p ≤
      Real.log (Real.log ((max 2 (x-1):ℕ):ℝ)) + 0.261497 +
       if 8.9 < Real.log (x:ℝ) then 1614e-6 else 1 := by
  intro x hx hupper
  change S x ≤ _
  have h10 : Real.exp (10:ℝ) = (Real.exp 1)^10 := by simpa using Real.exp_nat_mul 1 10
  have hcap : ⌈Real.exp (10:ℝ)⌉₊ ≤ 22027 := by
    apply Nat.ceil_le.mpr
    rw [h10]
    exact (pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 10).trans (by norm_num)
  obtain ⟨h7200,he⟩ := early start_S
  by_cases hu : x ≤ 7200
  · have hsmall := (Real.log_le_log (by positivity : (0:ℝ)<x)
        (by exact_mod_cast hu : (x:ℝ) ≤ 7200)).trans log_cut
    rw [ite_eq_right (not_lt.mpr hsmall)]
    by_cases hx3 : 3 < x
    · have h := he x hx3 hu
      norm_num [D] at h ⊢
      linarith
    · have h2 : max 2 (x-1)=2 := by omega
      rw [h2]
      have hm := (S_mono (show x≤3 by omega)).trans start_S
      have hh := Real.log_le_log (by norm_num : (0:ℝ)<2⁻¹) (by linarith [Real.log_two_gt_d9] : (2:ℝ)⁻¹ ≤ Real.log 2)
      rw [Real.log_inv] at hh
      norm_num [D] at hm ⊢
      linarith [Real.log_two_lt_d9]
  · have h := (late h7200).2 x (by omega) (hupper.trans hcap)
    split_ifs <;> norm_num [D] at h ⊢ <;> linarith
end
end SmallRangeInputs

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

-- Adapted from bz7777777, https://github.com/CGandGameEngineLearner/goldbach-proofs/pull/4789
-- The certificate is placed in a local namespace and its entry point is renamed.
namespace SmallRangeInputs
section
-- child 1 zh: 认证 Meissel–Mertens 常数的上下界。
-- child 1 en: Certify the numerical lower and upper bounds for the Meissel–Mertens constant.
-- child 2 zh: 在有限整数网格上，用常数上界认证素数倒数和的下界。
-- child 2 en: Certify the lower reciprocal-prime inequality on the finite integer grid using the upper constant bound.
-- child 3 zh: 用左端点对数与常数下界，认证每个整数格对应的素数倒数和上界。
-- child 3 en: Certify the upper reciprocal-prime inequality on each grid cell using its left endpoint and the lower constant bound.

theorem assembleGrid
    (constant :
      let M₀ : ℝ := Real.eulerMascheroniConstant +
        ∑' p : Nat.Primes, (Real.log (1 - 1 / (p.1 : ℝ)) + 1 / (p.1 : ℝ))
      0.261497 ≤ M₀ ∧ M₀ ≤ 0.261498)
    (lowerGrid : ∀ n : ℕ, 2 ≤ n → n ≤ Nat.ceil (Real.exp (10 : ℝ)) →
      Real.log (Real.log (n : ℝ)) + (0.261498 : ℝ) - (2.964e-6 : ℝ) / Real.log (n : ℝ) ≤
        ∑ p ∈ (Finset.range n).filter Nat.Prime, (1 : ℝ) / (p : ℝ))
    (upperGrid : ∀ n : ℕ, 2 ≤ n → n ≤ Nat.ceil (Real.exp (10 : ℝ)) →
      (∑ p ∈ (Finset.range n).filter Nat.Prime, (1 : ℝ) / (p : ℝ)) ≤
        Real.log (Real.log ((max 2 (n - 1) : ℕ) : ℝ)) + (0.261497 : ℝ) +
          if (8.9 : ℝ) < Real.log (n : ℝ) then (1.614e-3 : ℝ) else 1) :
    (let M0 : ℝ := Real.eulerMascheroniConstant + ∑' p : Nat.Primes, (Real.log (1 - 1 / (p.1 : ℝ)) + 1 / (p.1 : ℝ)); (0.261497 ≤ M0 ∧ M0 ≤ 0.261498) ∧ ∀ x : ℝ, 2 ≤ x → x ≤ Real.exp 10 → Real.log (Real.log x) + M0 - (2.964e-6 : ℝ) / Real.log x ≤ (∑ p ∈ (Finset.range (Nat.ceil x)).filter Nat.Prime, (1 : ℝ) / (p : ℝ)) ∧ (∑ p ∈ (Finset.range (Nat.ceil x)).filter Nat.Prime, (1 : ℝ) / (p : ℝ)) ≤ Real.log (Real.log x) + M0 + (if Real.log x > 8.9 then (1.614e-3 : ℝ) else (1 : ℝ))) := by
  have ceilBounds {x : ℝ} (hx : 2 ≤ x) :
      let n := Nat.ceil x
      2 ≤ n ∧ x ≤ (n : ℝ) ∧ ((max 2 (n - 1) : ℕ) : ℝ) ≤ x := by
    intro n
    have hxn : x ≤ (n : ℝ) := Nat.le_ceil x
    have hn2 : 2 ≤ n := by exact_mod_cast hx.trans hxn
    have hStrict : (n : ℝ) < x + 1 :=
      Nat.ceil_lt_add_one (show 0 ≤ x by linarith)
    have hPrev : ((n - 1 : ℕ) : ℝ) ≤ x := by
      rw [Nat.cast_sub (show 1 ≤ n by omega), Nat.cast_one]
      linarith
    refine ⟨hn2, hxn, ?_⟩
    rw [Nat.cast_max]
    exact max_le hx hPrev

  have ceilLeExpTen {x : ℝ} (hx : x ≤ Real.exp 10) :
      Nat.ceil x ≤ Nat.ceil (Real.exp 10) :=
    Nat.ceil_mono hx

  let M₀ : ℝ := Real.eulerMascheroniConstant +
    ∑' p : Nat.Primes, (Real.log (1 - 1 / (p.1 : ℝ)) + 1 / (p.1 : ℝ))
  have hC : (0.261497 : ℝ) ≤ M₀ ∧ M₀ ≤ (0.261498 : ℝ) := constant
  refine ⟨hC, ?_⟩
  intro x hx hTop
  let n := Nat.ceil x
  obtain ⟨hn, hxN, hLeftX⟩ := ceilBounds hx
  have hnTop : n ≤ Nat.ceil (Real.exp (10 : ℝ)) := ceilLeExpTen hTop
  have hLogX : 0 < Real.log x := Real.log_pos (by linarith)
  have hLogXN : Real.log x ≤ Real.log (n : ℝ) :=
    Real.log_le_log (by linarith) hxN
  have hLogLogXN : Real.log (Real.log x) ≤ Real.log (Real.log (n : ℝ)) :=
    Real.log_le_log hLogX hLogXN
  have hRecip : (2.964e-6 : ℝ) / Real.log (n : ℝ) ≤ (2.964e-6 : ℝ) / Real.log x := by
    have hinv := one_div_le_one_div_of_le hLogX hLogXN
    simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hinv (by positivity : 0 ≤ (2.964e-6 : ℝ))
  have hLeftTwo : (2 : ℝ) ≤ ((max 2 (n - 1) : ℕ) : ℝ) := by
    exact_mod_cast (le_max_left (2 : ℕ) (n - 1))
  have hLogLeft : 0 < Real.log ((max 2 (n - 1) : ℕ) : ℝ) := Real.log_pos (by linarith)
  have hLogLogLeft : Real.log (Real.log ((max 2 (n - 1) : ℕ) : ℝ)) ≤ Real.log (Real.log x) :=
    Real.log_le_log hLogLeft (Real.log_le_log (by linarith) hLeftX)
  have hAllowance :
      (if (8.9 : ℝ) < Real.log (n : ℝ) then (1.614e-3 : ℝ) else 1) ≤
        if (8.9 : ℝ) < Real.log x then (1.614e-3 : ℝ) else 1 := by
    by_cases hxLarge : (8.9 : ℝ) < Real.log x
    · have hnLarge := hxLarge.trans_le hLogXN
      simp only [ite_eq_left hxLarge, ite_eq_left hnLarge, le_refl]
    · rw [ite_eq_right hxLarge]
      split <;> norm_num
  constructor
  · calc
      Real.log (Real.log x) + M₀ - (2.964e-6 : ℝ) / Real.log x ≤
          Real.log (Real.log (n : ℝ)) + (0.261498 : ℝ) - (2.964e-6 : ℝ) / Real.log (n : ℝ) :=
        sub_le_sub (add_le_add hLogLogXN hC.2) hRecip
      _ ≤ _ := lowerGrid n hn hnTop
  · calc
      _ ≤ Real.log (Real.log ((max 2 (n - 1) : ℕ) : ℝ)) + (0.261497 : ℝ) +
          (if (8.9 : ℝ) < Real.log (n : ℝ) then (1.614e-3 : ℝ) else 1) :=
        upperGrid n hn hnTop
      _ ≤ _ := add_le_add (add_le_add hLogLogLeft hC.1) hAllowance
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

theorem Conjectures.Goldbach.MertensSmallRangeCert : (let M0 : ℝ := Real.eulerMascheroniConstant + ∑' p : Nat.Primes, (Real.log (1 - 1 / (p.1 : ℝ)) + 1 / (p.1 : ℝ)); (0.261497 ≤ M0 ∧ M0 ≤ 0.261498) ∧ ∀ x : ℝ, 2 ≤ x → x ≤ Real.exp 10 → Real.log (Real.log x) + M0 - (2.964e-6 : ℝ) / Real.log x ≤ (∑ p ∈ (Finset.range (Nat.ceil x)).filter Nat.Prime, (1 : ℝ) / (p : ℝ)) ∧ (∑ p ∈ (Finset.range (Nat.ceil x)).filter Nat.Prime, (1 : ℝ) / (p : ℝ)) ≤ Real.log (Real.log x) + M0 + (if Real.log x > 8.9 then (1.614e-3 : ℝ) else (1 : ℝ))) := by
  have constant := SmallRangeInputs.assembleConstant MertensCert.cancellation
    SmallRangeInputs.gammaBound SmallRangeInputs.logZetaThree SmallRangeInputs.finiteCorrection
  exact SmallRangeInputs.assembleGrid constant SmallRangeInputs.lowerGrid SmallRangeInputs.upperGrid
