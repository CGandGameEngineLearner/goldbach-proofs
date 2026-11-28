import Mathlib

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

theorem Conjectures.Cuts.Task8f9f08650abf4d04bfa7122e :
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
