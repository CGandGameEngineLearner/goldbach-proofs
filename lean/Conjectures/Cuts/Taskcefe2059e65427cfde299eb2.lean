import Mathlib


-- child 1 zh: 认证 Meissel–Mertens 常数的上下界。
-- child 1 en: Certify the numerical lower and upper bounds for the Meissel–Mertens constant.
-- child 2 zh: 在有限整数网格上，用常数上界认证素数倒数和的下界。
-- child 2 en: Certify the lower reciprocal-prime inequality on the finite integer grid using the upper constant bound.
-- child 3 zh: 用左端点对数与常数下界，认证每个整数格对应的素数倒数和上界。
-- child 3 en: Certify the upper reciprocal-prime inequality on each grid cell using its left endpoint and the lower constant bound.

theorem Conjectures.Cuts.Cutdde1e7ef243203eb1faa06c9
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
theorem Conjectures.Cuts.Taskabc64269ad130e923b36a98e :
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


open Finset
namespace MertensPrefix
def scale : ℕ := 10^18
noncomputable def exactTerms (p : ℕ) : ℕ → ℝ
 | 0 => 0
 | n+1 => exactTerms p n + 1 / ((n+2:ℕ) * (p:ℝ)^(n+2))
def terms (p : ℕ) : ℕ → ℕ
 | 0 => 0
 | n+1 => terms p n + scale / ((n+2)*p^(n+2))
def errs (p n : ℕ) := n+1+scale/(p^(n+1)*(p-1))
noncomputable def correction (p : ℕ) : ℝ := -Real.log (1-1/(p:ℝ)) - 1/(p:ℝ)
theorem floorBounds (a b : ℕ) (h : 0 < b) :
    ((a/b:ℕ):ℝ) ≤ (a:ℝ)/b ∧ (a:ℝ)/b ≤ (a/b:ℕ)+1 := by
  constructor
  · apply (le_div_iff₀ (by exact_mod_cast h)).2
    exact_mod_cast Nat.div_mul_le_self a b
  · apply (div_le_iff₀ (by exact_mod_cast h)).2
    exact_mod_cast (Nat.lt_div_mul_add h : a < a / b * b + b).le.trans_eq (by ring : a / b * b + b = (a / b + 1) * b)
theorem termsBounds (p n : ℕ) (hp : 2 ≤ p) : (terms p n : ℝ) ≤ scale * exactTerms p n ∧
    (scale:ℝ) * exactTerms p n ≤ (terms p n:ℝ)+n := by
  induction n with
  | zero => simp [terms,exactTerms]
  | succ n ih =>
    have h := floorBounds scale ((n+2)*p^(n+2)) (by positivity)
    simp only [terms,exactTerms,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,
      Nat.cast_succ,mul_add,mul_one_div] at *
    constructor <;> linarith
theorem series_eq (p n : ℕ) (hp : 2 ≤ p) :
    (∑ i ∈ range (n+1), ((1/(p:ℝ))^(i+1))/((i:ℝ)+1)) = 1/(p:ℝ) + exactTerms p n := by
  induction n with
  | zero => simp [exactTerms]
  | succ n ih =>
    rw [sum_range_succ,ih]
    simp only [exactTerms,Nat.cast_add,Nat.cast_ofNat,one_div,← inv_pow,mul_inv_rev]
    ring
theorem correction_bounds (p n : ℕ) (hp : 2 ≤ p) :
    (terms p n:ℝ) ≤ (scale:ℝ)*correction p ∧
    (scale:ℝ)*correction p ≤ (terms p n:ℝ) + (errs p n:ℝ) := by
  have hp1 : 1 < (p:ℝ) := by exact_mod_cast (show 1 < p by omega)
  have hp0 : 0 < (p:ℝ) := by linarith
  have hx : |1/(p:ℝ)| < 1 := by rw [abs_of_pos (by positivity)]; exact (div_lt_one hp0).2 hp1
  have hs := Real.hasSum_pow_div_log_of_abs_lt_one hx
  have hlow := sum_le_hasSum (range (n+1)) (fun i _ => by positivity) hs
  have hhigh := Real.abs_log_sub_add_sum_range_le hx (n+1)
  rw [series_eq p n hp] at hlow hhigh
  rw [abs_of_pos (by positivity : 0 < 1/(p:ℝ))] at hhigh
  have he := termsBounds p n hp
  have hpn : 0 < p^(n+1)*(p-1) := Nat.mul_pos (by positivity) (by omega)
  have hfl := (floorBounds scale _ hpn).2
  rw [Nat.cast_mul,Nat.cast_pow,Nat.cast_sub (by omega : 1 ≤ p),Nat.cast_one] at hfl
  have hre : (1/(p:ℝ))^(n+1+1)/(1-1/(p:ℝ)) = 1/((p:ℝ)^(n+1)*(p-1)) := by
    rw [pow_succ,div_pow]; field_simp <;> ring
  rw [hre,abs_le] at hhigh
  have z : (0:ℝ) ≤ scale := by positivity
  unfold correction errs
  push_cast
  constructor
  · exact he.1.trans (mul_le_mul_of_nonneg_left (by linarith) z)
  · have ht : -Real.log (1-1/(p:ℝ)) - 1/(p:ℝ) ≤ exactTerms p n + 1/((p:ℝ)^(n+1)*(p-1)) := by linarith
    have h := mul_le_mul_of_nonneg_left ht z
    rw [mul_add,mul_one_div] at h
    linarith
end MertensPrefix


open Finset
namespace MertensSieve
private def stripe (q : ℕ) : ℕ → ℕ
  | 0 => 1
  | k+1 =>
    let h := q*2^k
    let s := stripe q k
    if h < 16384 then s ||| (s <<< h) else s
private theorem stripe_spec (q k i : ℕ) (hq : 0 < q) (hi : i < 16384) :
    (stripe q k).testBit i = true ↔ i < q*2^k ∧ q ∣ i := by
  induction k generalizing i with
  | zero =>
    simp only [stripe,pow_zero,mul_one,Nat.testBit_one_eq_true_iff_self_eq_zero]
    constructor
    · rintro rfl; simp [hq]
    · rintro ⟨hl,hd⟩
      by_contra hn
      have := Nat.le_of_dvd (by omega : 0 < i) hd
      omega
  | succ k ih =>
    have hd : q ∣ q*2^k := dvd_mul_right _ _
    simp only [stripe,pow_succ,← Nat.mul_assoc]
    split_ifs with h
    · rw [Nat.testBit_or,Nat.testBit_shiftLeft,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq,ih _ hi,
        ih _ (by omega : i-q*2^k < 16384)]
      by_cases hl : q*2^k ≤ i
      · rw [Nat.dvd_sub_iff_left hl hd]; omega
      · omega
    · rw [ih _ hi]; omega
private def freeOf (p : ℕ) : ℕ → Bool
  | 0 => true
  | k+1 => freeOf p k && decide (p % (k+2) ≠ 0)
private theorem freeOf_spec (p k : ℕ) : freeOf p k = true ↔ ∀ d, 2 ≤ d → d ≤ k+1 → ¬ d ∣ p := by
  induction k with
  | zero => simp [freeOf]; omega
  | succ k ih =>
    simp only [freeOf, Bool.and_eq_true, decide_eq_true_eq, ih]
    constructor
    · intro ⟨h1,h2⟩ d hd hu
      by_cases h : d = k+2
      · subst d; exact fun hh => h2 (Nat.mod_eq_zero_of_dvd hh)
      · exact h1 d hd (by omega)
    · intro h
      exact ⟨fun d hd hu => h d hd (by omega), fun hh => h _ (by omega) (by omega) (Nat.dvd_of_mod_eq_zero hh)⟩
def fastPrime (p : ℕ) : Bool := if p < 1733 then decide (2 ≤ p) && freeOf p (min (p-2) 40) else decide (Nat.Prime p)
theorem fastPrime_iff (p : ℕ) : fastPrime p = true ↔ Nat.Prime p := by
  unfold fastPrime
  split_ifs with hsmall
  · rw [Bool.and_eq_true,decide_eq_true_eq,freeOf_spec]
    constructor
    · rintro ⟨hp,h⟩
      refine Nat.prime_def_le_sqrt.mpr ⟨hp, fun d hd hsq => h d hd ?_⟩
      have hlt : p.sqrt < 42 := Nat.sqrt_lt.mpr (by omega)
      have hsp : p.sqrt < p := Nat.sqrt_lt_self (by omega)
      omega
    · intro hp
      refine ⟨hp.two_le, fun d hd hu hh => ?_⟩
      have := (Nat.dvd_prime hp).mp hh
      omega
  · simp

private def bases := (List.range 1733).filter (fun p => decide (Nat.Prime p))
private def mark (a : ℕ) : List ℕ → ℕ
  | [] => 0
  | q::qs => (stripe q 14 >>> (a % q)) ||| mark a qs
private theorem mark_spec (a j : ℕ) (qs : List ℕ) (hj : j < 8192)
    (hb : ∀ q ∈ qs, 2 ≤ q ∧ q ≤ 1732) :
    (mark a qs).testBit j = true ↔ ∃ q ∈ qs, q ∣ a+j := by
  induction qs with
  | nil => simp [mark]
  | cons q qs ih =>
    have hq := hb q (by simp)
    have hp := Nat.mod_lt a (by omega : 0 < q)
    rw [mark,Nat.testBit_or,Nat.testBit_shiftRight,Bool.or_eq_true,stripe_spec _ _ _ (by omega) (by omega),
      ih (fun p hp => hb p (by simp [hp]))]
    have hu : a % q+j < q*2^14 := by norm_num; omega
    have hh : q ∣ a % q + j ↔ q ∣ a+j := by
      rw [Nat.dvd_iff_mod_eq_zero,Nat.dvd_iff_mod_eq_zero,Nat.mod_add_mod]
    norm_num at hu; simp [hu,hh]
def verifiedBases : List ℕ := [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113,127,131,137,139,149,151,157,163,167,173,179,181,191,193,197,199,211,223,227,229,233,239,241,251,257,263,269,271,277,281,283,293,307,311,313,317,331,337,347,349,353,359,367,373,379,383,389,397,401,409,419,421,431,433,439,443,449,457,461,463,467,479,487,491,499,503,509,521,523,541,547,557,563,569,571,577,587,593,599,601,607,613,617,619,631,641,643,647,653,659,661,673,677,683,691,701,709,719,727,733,739,743,751,757,761,769,773,787,797,809,811,821,823,827,829,839,853,857,859,863,877,881,883,887,907,911,919,929,937,941,947,953,967,971,977,983,991,997,1009,1013,1019,1021,1031,1033,1039,1049,1051,1061,1063,1069,1087,1091,1093,1097,1103,1109,1117,1123,1129,1151,1153,1163,1171,1181,1187,1193,1201,1213,1217,1223,1229,1231,1237,1249,1259,1277,1279,1283,1289,1291,1297,1301,1303,1307,1319,1321,1327,1361,1367,1373,1381,1399,1409,1423,1427,1429,1433,1439,1447,1451,1453,1459,1471,1481,1483,1487,1489,1493,1499,1511,1523,1531,1543,1549,1553,1559,1567,1571,1579,1583,1597,1601,1607,1609,1613,1619,1621,1627,1637,1657,1663,1667,1669,1693,1697,1699,1709,1721,1723]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem bases_eq : bases = verifiedBases := by
  have h : bases = (List.range 1733).filter fastPrime := by
    simp only [bases]; congr 1
    funext p
    exact Bool.eq_iff_iff.mpr (by simp [fastPrime_iff])
  rw [h]; decide +kernel
def bits (a : ℕ) := mark a verifiedBases % 2^8192
theorem bits_spec (a j : ℕ) (ha : 1732 < a) (hj : j < 8192) (hN : a+j ≤ 3000000) :
    (bits a).testBit j = false ↔ Nat.Prime (a+j) := by
  have hb : ∀ q ∈ bases, 2 ≤ q ∧ q ≤ 1732 := by
    intro q hq
    simp only [bases,List.mem_filter,List.mem_range,decide_eq_true_eq] at hq
    exact ⟨hq.2.two_le, by omega⟩
  have h := mark_spec a j bases hj hb
  unfold bits
  simp only [Nat.testBit_mod_two_pow, hj, decide_true, Bool.true_and]
  rw [← bases_eq]
  rw [Bool.eq_false_iff]; change (¬ (mark a bases).testBit j = true) ↔ _; rw [h]
  constructor
  · intro hn
    apply Nat.prime_def_le_sqrt.mpr
    refine ⟨by omega, fun d hd hs hdiv => ?_⟩
    have hm := Nat.minFac_prime (show d ≠ 1 by omega)
    have hle := Nat.minFac_le (by omega : 0 < d)
    have hu : (a+j).sqrt < 1733 := Nat.sqrt_lt.mpr (by omega)
    exact hn ⟨_,by simp [bases,hm,show d.minFac < 1733 by omega],dvd_trans (Nat.minFac_dvd d) hdiv⟩
  · rintro hp ⟨q,hq,hd⟩
    have hh := hb q hq
    have hh' := (Nat.dvd_prime hp).mp hd
    omega
end MertensSieve


namespace MertensTree
open Finset
def tree (f : ℕ → ℕ) (a m : ℕ) : ℕ → ℕ
  | 0 => if m.testBit 0 then f a else 0
  | d+1 => if m = 0 then 0 else
    tree f a (m % (2^(2^d))) d + tree f (a+2^d) (m >>> (2^d)) d

theorem tree_spec (f : ℕ → ℕ) (a m d : ℕ) : tree f a m d =
    ∑ j ∈ range (2^d), if m.testBit j then f (a+j) else 0 := by
  induction d generalizing a m with
  | zero => simp [tree]
  | succ d ih =>
    by_cases hm : m = 0
    · subst m; simp [tree]
    rw [tree, if_neg hm, ih, ih, pow_succ, Nat.mul_two, sum_range_add]
    congr 1
    · apply sum_congr rfl; intro j hj
      have hj' := mem_range.mp hj
      simp [Nat.testBit_mod_two_pow, hj']
    · apply sum_congr rfl; intro j hj
      simp [Nat.testBit_shiftRight,Nat.add_assoc]
end MertensTree


open Finset

namespace MertensFold

def depth (p : ℕ) := if p < 32 then 63 else if p < 1000 then 5 else 2

def charge (p : ℕ) (prime : Bool) : ℕ × ℕ :=
  if prime then (MertensPrefix.terms p (depth p), MertensPrefix.errs p (depth p)) else (0,0)

def go (a : ℕ) (isPrime : ℕ → Bool) : ℕ → ℕ → ℕ × ℕ → ℕ × ℕ
  | 0, _, acc => acc
  | k+1, j, acc =>
    let c := charge (a+j) (isPrime j)
    go a isPrime k (j+1) (acc.1+c.1, acc.2+c.2)

def blockFromMask (a w mask : ℕ) : ℕ × ℕ :=
  let live := (mask ^^^ (2^w-1)) % 2^w
  (MertensTree.tree (fun p => MertensPrefix.terms p (depth p)) a live 13,
    MertensTree.tree (fun p => MertensPrefix.errs p (depth p)) a live 13)

def block (a w : ℕ) : ℕ × ℕ :=
  if a = 0 then go a (fun j => MertensSieve.fastPrime (a+j)) w 0 (0,0)
  else blockFromMask a w (MertensSieve.bits a)

noncomputable def term (p : ℕ) : ℝ :=
  if Nat.Prime p then -(Real.log (1-1/(p:ℝ)) + 1/(p:ℝ)) else 0

noncomputable def cumulative (a : ℕ) : ℝ :=
  (MertensPrefix.scale:ℝ) * ∑ p ∈ range a, term p

def B (a b lo err : ℕ) : Prop :=
  (lo:ℝ) ≤ cumulative b - cumulative a ∧ cumulative b - cumulative a ≤ (lo:ℝ) + err

private theorem single (p : ℕ) (flag : Bool) (hf : flag = true ↔ Nat.Prime p) :
    B p (p+1) (charge p flag).1 (charge p flag).2 := by
  have hstep : cumulative (p+1)-cumulative p = (MertensPrefix.scale:ℝ)*term p := by
    simp [cumulative,sum_range_succ,mul_add]
  unfold B
  rw [hstep]
  by_cases hp : Nat.Prime p
  · have hreal : term p = MertensPrefix.correction p := by
      simp [term,hp,MertensPrefix.correction]; ring
    rw [hf.mpr hp,hreal]
    exact MertensPrefix.correction_bounds p (depth p) hp.two_le
  · have he : flag = false := by cases flag <;> simp_all
    simp [term,hp,charge,he]

theorem join {a b c l₁ e₁ l₂ e₂ : ℕ} (h : B a b l₁ e₁) (h' : B b c l₂ e₂) :
    B a c (l₁+l₂) (e₁+e₂) := by
  unfold B at *
  push_cast
  constructor <;> linarith [h.1,h.2,h'.1,h'.2]

private theorem go_spec (a : ℕ) (test : ℕ → Bool) (k j l e : ℕ)
    (hf : ∀ u, j ≤ u → u < j+k → (test u = true ↔ Nat.Prime (a+u)))
    (hacc : B a (a+j) l e) :
    B a (a+(j+k)) (go a test k j (l,e)).1 (go a test k j (l,e)).2 := by
  induction k generalizing j l e with
  | zero => simpa only [Nat.add_zero,go] using hacc
  | succ k ih =>
    have h := single (a+j) (test j) (hf j le_rfl (by omega))
    have hh := join hacc h
    rw [Nat.add_assoc] at hh
    have hnext := ih (j+1) _ _ (fun u h1 h2 => hf u (by omega) (by omega)) hh
    simpa only [go, Nat.add_right_comm j 1 k,Nat.add_assoc] using hnext

private theorem sums_spec (a k : ℕ) (test : ℕ → Bool)
    (hf : ∀ j < k, test j = true ↔ Nat.Prime (a+j)) :
    B a (a+k) (∑ j ∈ range k, (charge (a+j) (test j)).1)
      (∑ j ∈ range k, (charge (a+j) (test j)).2) := by
  induction k with
  | zero => simp [B]
  | succ k ih =>
    rw [sum_range_succ,sum_range_succ]
    exact join (ih (fun j hj => hf j (by omega)))
      (single (a+k) (test k) (hf k (by omega)))

private theorem mask_spec (a w mask : ℕ) (hmask : MertensSieve.bits a = mask)
    (ha : 1732 < a) (hw : w ≤ 8192) (hN : a+w ≤ 3000001) :
    B a (a+w) (blockFromMask a w mask).1 (blockFromMask a w mask).2 := by
  let test := fun j : ℕ => !(mask.testBit j)
  have hf : ∀ j < w, test j = true ↔ Nat.Prime (a+j) := by
    intro j hj
    simpa only [test,← hmask,Bool.not_eq_true'] using
      MertensSieve.bits_spec a j ha (by omega) (by omega)
  let live := (mask ^^^ (2^w-1)) % 2^w
  have eqSum (g : ℕ → ℕ) :
      MertensTree.tree g a live 13 =
        ∑ j ∈ range w, if test j then g (a+j) else 0 := by
    rw [MertensTree.tree_spec, show 2^13=8192 by decide]
    calc
      _ = ∑ j ∈ range w, if live.testBit j then g (a+j) else 0 := by
        symm
        apply sum_subset (range_mono hw)
        intro j hj hnot
        have hj' : ¬ j < w := by simpa using hnot
        simp [live,Nat.testBit_mod_two_pow,hj']
      _ = _ := by
        apply sum_congr rfl
        intro j hj
        have hj' := mem_range.mp hj
        simp [live,test,Nat.testBit_mod_two_pow,Nat.testBit_xor,Nat.testBit_two_pow_sub_one,hj']
  have hg := sums_spec a w test hf
  change B a (a+w) (MertensTree.tree _ a live 13) (MertensTree.tree _ a live 13)
  rw [eqSum,eqSum]
  convert hg using 1
  · apply sum_congr rfl
    intro j hj
    cases hf' : test j <;> simp [charge]
  · apply sum_congr rfl
    intro j hj
    cases hf' : test j <;> simp [charge]

theorem block_of_mask (a w lo err mask : ℕ) (ha : 1732 < a) (hw : w ≤ 8192)
    (hN : a+w ≤ 3000001) (hMask : MertensSieve.bits a = mask)
    (hcert : blockFromMask a w mask = (lo,err)) : B a (a+w) lo err := by
  have h := mask_spec a w mask hMask ha hw hN
  rwa [hcert] at h

theorem segment (a w lo err : ℕ) (ha : a = 0 ∨ 1732 < a) (hw : w ≤ 8192)
    (hN : a+w ≤ 3000001) (hcert : block a w = (lo,err)) :
    B a (a+w) lo err := by
  have h0 : B a (a+0) 0 0 := by simp [B]
  by_cases hz : a=0
  · let f := fun j : ℕ => MertensSieve.fastPrime (a+j)
    have h := go_spec a f w 0 0 0 (by simp [f,MertensSieve.fastPrime_iff]) h0
    change _ at hcert
    simp only [block, hz, ↓reduceIte] at hcert
    subst a
    change go 0 (fun j => MertensSieve.fastPrime (0+j)) w 0 (0,0) = (lo,err) at hcert
    dsimp only [f] at h
    rw [hcert] at h
    simpa only [Nat.zero_add] using h
  · apply block_of_mask a w lo err (MertensSieve.bits a) (by omega) hw hN rfl
    simpa only [block,hz,↓reduceIte] using hcert

theorem bounds {K lo err : ℕ} (h : B 0 (K+1) lo err) :
    (lo:ℝ)/MertensPrefix.scale ≤ ∑ p ∈ range (K+1), term p ∧
    (∑ p ∈ range (K+1), term p) ≤ ((lo:ℝ)+err)/MertensPrefix.scale := by
  simp only [B,cumulative,range_zero,sum_empty,mul_zero,sub_zero] at h
  have hp : (0:ℝ) < MertensPrefix.scale := by norm_num [MertensPrefix.scale]
  exact ⟨(div_le_iff₀ hp).2 (by simpa only [mul_comm] using h.1),
         (le_div_iff₀ hp).2 (by simpa only [mul_comm] using h.2)⟩

theorem finish {lo err : ℕ} (h : B 0 3000001 lo err)
    (hl : 315718430000000000 ≤ lo) (hu : lo+err ≤ 315718450000000000) :
    0.31571843 ≤ ∑ p ∈ range 3000001, term p ∧
      (∑ p ∈ range 3000001, term p) ≤ 0.31571845 := by
  have h1 : (315718430000000000:ℝ) ≤ lo := by exact_mod_cast hl
  have h2 : (lo:ℝ)+err ≤ 315718450000000000 := by exact_mod_cast hu
  simp only [B,cumulative,range_zero,sum_empty,mul_zero,sub_zero] at h
  norm_num [MertensPrefix.scale] at h
  constructor <;> linarith only [h.1,h.2,h1,h2]

end MertensFold

namespace MertensMasks
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask1733 : MertensSieve.bits 1733 = 0xbfffbefffbbffbffafbffbeeffefbfbffbbeffebfffefbbeffebffffefeffafffeffefbffafbbeffefffbffffffffbbfbeffeffbffefbffbefbafffffaebfebeffbefbffefbffffefaefffbbfbfffeffaeffffefffebffbeffefbbffbefeffeefbffeefbfffefbffbfffffbfbfefaffefffebbebffffffafbffbfefeefbffffffefbffffbaffeffafbfebffbbffffbbfffefefbeefbffbefbfbeefeefefbfffbeffebbffeffafffefeffbffffbaffbefeffeffffffffbefffbbffafbbffffffebfefefbfefffffeffefbffeebbffeefbffffbeebfebfeffffbffbfbbefffbfffffbefbfefeebeffeffbefffbffffefafffefffffffbffaffeefbfbffbeffffbaefbffeffeffefbefffffeefffffffaeffefffbbefffbbfbbefeeffffefbbfffefffbbffafbeeffebfebeefefbeffbfbfebeeffffafbfffefffefbfffefffffeffffafffebfeffebfefffbffffffefbbefeffbebbffefbfeffffbfbffffebeffefbfffffbfeffefffbbffbfbeffeefbfbefbbebfebffffffefbbfbfffbffafbefffefeebbffffbfebfebfffafffffeefffbfefaffaffbeffebefffeffffbffbfbfffeefafbfebbfffefefffffffbfefeeffffafffffbefffffefeffbefbebeffbefefbefbfebffbfefafbeffbfffefeefbfbafffffeffbffbfbfebfefeffeffaffbefbffefbbefeffffbbffffbeffffffefffbffbbffffbefffebfebeefafbbffbefefbeffbfbbffffffefaeffffefbfefeefbffeffaebbebfffbfffffffbfefeefbeffffffbbebffbaffffbafbffffefaefbffaefbfbefbefffffffbbffeffbffefbefffebeffefffffeebbfffeffefeffbfbbffefbffffffbefbebffbeeffffbfbffbfffaffafbbefbffeebfefbfbeebffbfefbffeffefbfefffffffbffeeffebeebbfffffbfbfffeefaffffbffbffbeffbefafbafffeffffbefbfbfffbeffebfffffbaefbffeffaffffbefbbeffffaffeffefbfffeffbefeffaffbffffffefefbfebfebeffaffaffafbfefffffeffffaefffbeebfffbffbebffbefffefafffffbebefbaffefffffbffffbbffafbafbbfffefeefffbfebbffeffaffffbeefffbfebefffffbefbfbfefeefbffeebffbfffbefbfbeefbffeffaffbffaffbebeebfefbffbfbffffebaefefffeffffefbfffafffebfebffbbffafbbefbebffffffbffaebffffefeefefbffbbeffebbfffffefffebfeffffefbbffbeffefeefffbbfbfebffffffafbeefffbffbfefefbeffbfbfffeefbfbeefffbfffaefaffeffbffeefeffaffbebbfbeebbefbfbaffbffeffeefefffebffbffffefafbbfbfeffffbfffffeefbfbffbeefffbefbffbeefaefbffefbbebefffffaffeefbefeebfffbfbafffefefbbfffffbfffefeffaefafffebffbfebaffefbfefffbfebfefbfbaefbfbefffffafffebfffefbeffeffaebbefffbfffbfbffbfeffebbeffffbefbefe := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask9925 : MertensSieve.bits 9925 = 0xffffefeffefffebfebaffffffefffffebeefbffaffffbfefaffafbffbfeffffbffbffaffbffffbfffafbffffeffebfefefffefbfffffaffeffafffffffbbffeffafffebeeffffbffbffffbfeffefafbefbbfffefbffbffafffefeebbeffffbfbfefefbeeffffbebfffffffeffffbfbffffebbffafbfffbfbffffefffbeffbfbefffefffffefbefeebeffbfffefbebfffbffffbefbbeffffaffefbbfbffffffbffafbffbfffffbfffffbbffbeffeffffffbbebfffeffeefafffebffbffbbffffffefbefefbfffeffbfffffefbeefffffebbffefbeefbffffffeffefaffeffbefffbfffeffffffefbffeeffffafbefffffeebbfffffffffebffbfffbfbefbbffeebaefffffeffffffbeffbfffebffbffffefffbbefbeffebeeffffbffffffffbefefbefbbffefbeffeffaebbffffffffffbbfbbeffebaffeffbffbeffffaffeffbfbfefffbfffbffeeffffefbeffbfbbffbffeffeffbfbeeffebfeffffaffbefbfbfebfefafbbfffefefbfeffffbefbffeffeffeffafbfefffbeffbfbeeffefefffffbffeefffffffbffeffefbbfbfefbfffffefbbfbfebfffbfbffbbefefffefffbbfbbfbefbeefbfbeefffbfffbffeffeefffbeebeffffffebffffffaefafbeefffbfffbffeffbfffeffebfefbfbbfbbeffebfffefffffbefffbaffffbfeffefffffffafbffffefffbfeffffeefffbeefbffffffffbffffbaffbffefbfffeeffffaffafffffffbbffffffebfefefbaffffbaefffbfffeffafffffbfbfefeffffbafbffffefaffaffeebbebfeffffefffefbfbefffefbffeffbffefffefffbfefffbffbfefefbefbfeffffeefbffafffefffbffffffafbbffeeffefbfffffbfbfefeffeffafffffffbbefbfbbfbbffffbeffefbbefffffffbffefbeefffffebaffffbbefbfbeffeffffbafbbfbeeffffffffeffeffefaffeffbfbfeffffbefffbbfffefeffbefeffffbffbefbeeffffbebfeffefbefefffefbebffbfefbfbefbbfbefffefbffeeffefeefeffbffaeffffffbbffefbffffeffefeefefbfebfebffbfffbfbeffffffffaefefbfffffbeebeefffffebffffefaeffffffbbffffbeffaffbeffebefbbffefbeffbffffbbfffffbebbefefbeffefbaffffffffbffbffafffebfefeeffffefffffeffeeffffeefbfbffffffafffffbfbfffbefafbffbbffffbbefffbffbffbeffbffefffebffffefeefbffbffbfbeffeefbfbbfffffefffeffffeebfebfeffffbffaeffffefbbffaffaffbffffbfffffbfefbfbefffefeffaffffffefbffafbfffbebefbfefbfffffffbfefeffbfffefffbeefbffaffffbbffffbbefbffbfbbffefbeefefffffbfbffffffafffeffebffbfefffbaeffffeebffffffbfbffffeffefffbeebfefeffaffefffebbfbefbbffffbffbfffeffeefefbbfbfebefffffbfbbebffbfebefffffaffffffebfffffffefbfffefeffaf := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask18117 : MertensSieve.bits 18117 = 0xffeeffffffbaffaffeffbfffefbffefbefbfefeffefffffbebbfbfffbffffffeffeffefeefffbafffeffeffffbfbbebffbeffbffefffefbfffebefffffbfffebefffffbfbbffbefefffefffbfefffbefbfefffbbeffeffefaffefbafffeffffeefffbffffffffffffafbeefbfbfffbffaffffbfffefbfefefbbfffeffebafffffffffefefbbefeffbffffffefbffafbfefbffffbeefbffeffbffefffeffffeebfffefffffeffafbbffeffbffffbaffbfffeffeffffbfbbeffffeffeffbeffefffbbffefffefffffeffefbfbefbffbffffffbfbffbfffefffffbffffbbffefbfefeffbfffefeeffffffbbfffebefbfffbffbebffbffffefeffeffffffffefffffffbbfbfefbffffbefffebfeffffbffeeffefeebbefbfbefbfeffefbffefbbffbefeffeefbffeffffffeffefaffbefbfbeeffefffffebbfbeffeffefffefbefefbafffffbffffffebfefafbffffffeebbffefbbeffefffbaefeffafbffffeffefffffefffbffbfffbffeffffbffffffaffeffffbefbeffbffeebffbfeffffbfffffbfffefaefefffefbfbfffbffbffeffffbffbeffbfbaeffebfebeefbfbfeffffeffaffffbefffefffbefffffefbfebeffffffffefbbffffbbefeffffbfebffbeefeffafbffbfeffffbfbafffebefffffffffebbfffefaffbffffbfeffffaffefffefbefefffffeffefbfeffebfffefbffffffffbbffbfbaebffbffbfffeffffffffeeffffbffaefbffeefbffafffebffbefbbffbffafbbffeffbefbffefffeffffbefeffffbfffeffeffbfbbfbfebfffeefffbbffbffefbfefbffaffbffeffeffffbfeffeffebffffffeebfebfebfefefbaffffffefaefffbbebbefffbfffffffefffbffbeefbfbafffffffbeffffbaefffffffbefefffffbffffbeffbfffebbfbfefbefefbbfffefffbeffefffffbebffffffbfbaebfeffffaffffbbffbfbfefeffffbaffbfbefffefefffffffffebfffefffebffbeebbffbffaffbffeffeffffbffffebffbfffbffbefffffffbffafbfeffeffebfffffbaffffffffaffbffffbbfbeeffffeffaefbefefbbfffffeffbfffefeffefffebffbfffeffffbeeffeffebbffefbeefbeffeffffbfbffbbfffefaffbffeebffbeffaffeffeffbfbefffffafffffbefeffafffffbeffefefffefffbbebffbffbfefeffaffbeffffeffffffffffffefbefffbefbffbeffaffbfffffbeffefbefafbeffbefeebaefffbffbbebefffffffffefffbfefeffefffefbfbfeffefbffbebbfffffaffffbefffebfffeffffffffbebeeffffbffefbfffeefefffffbefffbffbffffffaebffbffffffeffbffffbffffffffbeefbffefffefefbffbffbeffeffbffbfbfefffffeffffefffffefbbffffffeffebfffaefffbfeffeffffeefbfbbefbffeffeeffffbfbbffeffeffefffebbeffebfffeffeebfffeefbefbffbfbfeffeffffefbfebbeb := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask26309 : MertensSieve.bits 26309 = 0xbffbbffaffeffffbfefeffffbffffeffebeffbffeffbfbeffaefffbfefbebefffffbffeebffffffbffbffaffbeffebbffffffffffffffeeffffbebffbffffefffffffbeffffeefbfbffbfffeeffffbfbefbffffebfffaffefbfffeebfefaffbfffefeffbfffffbfffffffbeefefbaeffebfebeefefbfffbffeefeffffbfefbfbfefeefffffffbffeefbffbffeffffbeebbffaffefbfeffebfffffffffbfffffbffbfbbfbfebfffeffafffffffbefbfffbfbfebfffeeffefefbfefffbefbbffaffefffebefffefafffffbfffeffffffbbebffffffaefefbbfbffffefffffffaefbffefbfffffffefbffeffeffafbfffbfbeefafffffeebfffffbbefbffbffbfffffaffefbfebfeffffeefafbbeffefffbaffefbaffffffffeefbffeeffffeffbffafbfefffbfffafffffaffffbfefbefefbafbffffebfffefbffbfefeffbeffffffffffffbfffbfbfefffbfebffffffeffffbefffffaffffbfeffebafffffbffbffffbbefefbfffbffffbeffffbfefbffffbaffbffeebffffefeefefffffffffffffffffeebbfbffffeffffeefbebffbffffffefbbfbeebfefbfbbfffffeefaeffffbebbfbfffafffffffbfebfefbffbffbefffbefffffffbefbffffefeefbffffbfffeffeffaffbebfebfeffefefbffffefeffbefffffffbffefbbefeffefbfeffefbefbffffffffefffeffffaefffbfeffefeffeebffffebfffeffffbbfffffbffafffffbffffbeffffbbefbffefffffaffbeffeffffbffbfbeffbeffefefffffaefffbeefbefaffffbffbffbfffefffebffffefbfffffbffbffffbeeffffffffebefbbffbffeefffbfffbffeffffffebeffeffffbeffffffffbffafbffffefeeffffbffbffbefeebffffffefbbfffffeffffbfeffffeffbefefbffbfebfebbffffbfffbfbefbfffbfbeffbfffeffffbfbffbfeffebeffbffbefbffefbfefafbffffefffffefffbbfffffefbaefefffffffbfffeffefffefbeffefefffffbfbbfbfffbeffffeefbffeeffffbffbebffffefbffbfbeffbfffefaefefbffbbebffbbefbffbebffbfebeeffffeefffbefffefffbfffbfbeeffffafbfefbffffffffafffffffbfebfefefbafffffffffffeffbfbfeffffaffffbffbffffffbffaffaffbeffeffefbffffbbfbfffeefffbfffbefefbafffffafffefeffbfffffffbbffffbbefefbbebffbefbbffafbaefffffffeefafffeffffefbfffbffefbffffffafffffffbfebfebfffefffffbebffffefeffefbbfffebfefffffffbefffffefefffffffbfffaefbffbeffebffffffbffefbffbffffffffbfffbfffebbffbffeefbebfffbffbffefbfffefbefffffbebbffffbeffffbfebfebfffaffeffbeffefeffeffffbeffffbffffefafbeebfebefbaffefffffbefefbffffffefbfffeffeeffffbfffffeffeefeffbffffbfeffefbfbeffbfbefbfffbffeffbfbfffeefe := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask34501 : MertensSieve.bits 34501 = 0xefbeffbfffefafffffffbffffeffefaffefffffefffffeffbfbbffefbaefbfbeefffffebbefbffbefffbfeffefbfbfffbfbeffafffffeffffbffbaffeffeefbebfeffeffffbfbffffffeffefbfebfeffffbffffbaefffbfffaffeffaefbefffbfffbfbeefbfbfffbffafbffffffeefefffffefbfebffffefeffbfffffffbeffeffbfbbefffbeefafbeefffbffffffefbbfffebefbfffbffbffbffeffbffffffebffbfebefffffefbfefeffffffffbfffeffefbefffbfebbefeffaffefbafffeffefaffbffeefffffffeeffffefbbfbfffbefbfffeffffeffeffeffbefbfffffbefffbbffbffeebeffefbbeffefffbfffbfbbfbffbffffffeffaefffffffffffffaffbfffeffefbfbeffffbfffbffaffbffbfbefbbffbffbfffffeebbffffffffbfffffeefbfbffffffffffffefbefffffeffeefbfffeffffeeffefefbfebffffebbffbffbefbfffffbfffffafbfffeeffffefbbfbfffefffefeffffffefffbbefefbeffbebfebefffffbfbffbfefeffefffefbfbfefbfffffbfbbfbffffffbfbbffbfffffeffefbffbfeffffeffafbbffffffffeffbfbbffffbfeffefffbfebbfbfffaffffbeeffefeffffffffffbfebeebfefeffbfbfeffffaeffffbefffbefbbefeffbfffffffbaffffbbfffffefffefbffbeffffeffaefffbffbfffefbeffbffbeffeffffbffbfbfffbfffebfefefbfebbfbefffefafffebffbfeffffafbfefffffebeefffbfffffffffefffffffffebeebfffbffffffffefffefbffffbfffeebeefffbbffbefeffefffffafbffbfffeefefbeffbffeefffffffbefffffffbffefffefbfbffffffbffeebbffffbbefbffffffffffbfefeffbfbfefefbfffbfffebffbfffaffffffffbffffffeffffbebffffffbefefbfefffbffbfffaffbebbeffebfefeffefbbefeefbffffbfffbeffffbffeffeffffbfefaeffffafffefeebffffffeeffffeffbffffbefffebfefeffbffbffffbfffbeffffeffbfffffeefeffbfffebeffbeffffbeffffffbbffafbbeffebffbfefbffeffbffeffeffefffebbebffbeffeffbfffefeeffefbfbefbfffeffbefefffffbfbffbbffbfbbfbfeffebbfffffeefffbeebfefbfffeffffffffffefbfeffffeffafffffbefbfbefffefefbffbfeffeffefeffffbbfffffeffbffefbffffebfefffbfefbefffffeffffeebbfbeffbefefbffbfffeffbffbffaffffbfefbffbffafbffffefaeffffffbffbefbfffaffffffffffffefbffffffffffffefffbeebfffeeffffffbeebbeffebfffbffffffeffebfefffbbffbefeffeffffbfefffbffbbefbffffbfebffbfefbfffffbeffffefffffffbffbeefeffeffefbbfbfefaffeffbebfffffbbfffffffffeffffaffeffbffffbefffefffbefbffffebafffffbffbfffffeffffbaffbfbfefeffffbfefbfbefbfffaffffbfffefbbffafbfffffffefbeffffbebfe := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask42693 : MertensSieve.bits 42693 = 0xffefbfefeffbeffefffffffeffeefbffeffeffffbfffbfffffbffbffffbbffffbffffffbebbefffffffafbbffbffeffbeffffffffebfffeffffbefbfffffbbefffbbfffefeefeffbffffbbffeffafffffffbbefffbffffffeffffbefbfffafbbfbfefefbfefefffebbffeffafffffbebfffffffefffbaffbebffffffbffefbfffeffbffbfbffbbeffebbfffffeffbebffbfffbffefffeffebbfffffbefbffeffbefffffffffbfebfefafbfffffbfffeefffbbfbfffeeffefafffebffffebbfffffbebfffffbfeffffafffefefffffffbffbbebefffefaffeffffbfffaefefbffffeffeffefffbeebffbfefbffafffeffffefbfffffffffbfffefbffaffaffbfffffaefeffbffbebffbeefbfffebffffffffffffaeffeffebfffffbbfbfffeeffffbfbffffebefbbfffffefbbebeffbffeffefffffeebfefffbffbfffeffeefffffebffbfffeffbffbffbfbfffefffffeefbfbfffbeffffffbfebfeffffbffbefffffeffffefbeffffffffeefefbffbbfbefffefbfbffffeffeffefffbeffffbfebfefbffaffffffffaeffffeebfebfffefffffaefffbfefbffeffbfbfeffefbffffbfefbefefbeefbfffffffbfffeffbffaffbfffebeffffbfebffbffffefefbeefbfbfeffffbffefffefffbfffeffffffeffebbefefbbfbfffefbffffffafbfefffffeffffeeffffffffefffffefffbfffeffeffeffbefefffffaffafbbffffffffaffefbbffffbbffffbffbbebfffbffefbbefffbfffeffafffefbfbfeffffffbffbbfbfeffefbffefbbebffffffbffbfffefffffffaffeffbfffebefffffbebfefffffefeffbffffbffbaffbfffefbefefffffffbbebfffeffeffafffffbefffffffeffbfbffbeefbfffffffffffefbfffefbfeffefefbaefffffffffbffbbefbffefffffffbfefbffeefbfbfffeffbfffefffbfebfffeffeeffefeffbffffbefbfeffffffffffbefbffeffbffeffefffeffffaefeffaffbffeefeffffbbffbffeffffffffefbfebfffefffffafbbebffffffffbefffefefffffffffefbffffbbffbfbbefffbffbfefefffefbfbffbfffbfbbffffbfeffefeffeebfffeffeffeffffbfebffbbfffffefbbefeffaefffffffbfbfffbffefbeebffbffbeefbfbffffffeefffffffeffffffefaffbffefbfffffffffffffeffebeebbefeffffffefffbaffeffbfbffbffffffafbbfbfeffebfffbffbeffeffebeeffffefbbffeefaffbfbfeffffefffffafffffbffeffffffffffffefeebaeffffbefffffffeefbffffbffffefeffafffefbffeebfefbffaefffffffafffffeffffbffbefffffefbfefffbfffbfbafbffffffffffffffbfebefffffbfbffbfefffffefffbfffbeffeffeffffbfbfffefffefffbfeffffffbbffaffeffffbeffbffeffbffbefeffbefefbffffebffffffffbbeffebfefefffffeefbffefbfffbfbeffbfbfefaef := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask50885 : MertensSieve.bits 50885 = 0xfefbfebffffefaffaffefbffbffbbffffbefffefeebeefeffffffffffffffbfffffffffebfffbfbefffefefbfffbffbefbfbfffeeffffffbfffeffafffffbefbfffefbeffffffbffffffeefffffebfebffbfefbfbfebffbfebbfffffefffefeefffffffffbffffffbefaffefbbfbeeffffafffebbfffeffffaffbfffffefbeefefbffbbffefffffbffeeffffffbbffffbefffebfffefffffbefbfbfeffffefbfebbefefffffbffefbbfbeeffefeffbffbffeefeeffffffffefefbfffbffaffffffebfffffbfefbffffbfefffffffbffefffefefbfefbfffebfffaffffffefffbbffaffbfbfeffffaffffbfebffbeffbffefbbfbffbffbfefeffeefffbffbeefffffffffbeefbffffbefbfeffefaffaffeebfffefffefffbfffbefeebfffffbbefbffffbfefbfffebfefffbeffbfbbfffffeeffffbffafbffffeffffffbfebbfbfefaffeffaefbffeffbefbffefffefeffbefeffbfffffefffffbffbffffffebbffeffaffffffebfeffffbfbbfffeffffbfbfeffebefbeffffffeffebffffffefbeffbffffbfffefffebbeffffaefeffffbffffefbefefbaefbfbefbfffffbffffffeffeefbffefbfefefbafffffbebfebfefbffeffbfffffffbeffeffffbfefffbfffeffefffebffffffbffbfffefefffffbfbaebfffefffffbfffffffbfefbffeffaefbefffffffbfbfffbffffbfefefbfffffbeffeefaffffffeffefeffffbbefffbfefefffffaffbfffffeefeffffbfffeefffffffbffbfbefbfffbfffffbefeefffffffbefbffffbfffafbefffeffffaefffbbffbebfffeefffbaefffffeffffefbefffebeefafffffefbbefffbfffbfbbfbfffefbfefeffffbfffffffefffffeffefffbbffbffbeffeffffeffbfbfffffbfeffefffffebfefefbffffffbfbffbffbbeffffafbbeffffeefeffffbffbefffffbfbeefffbffffffbffaffffbeffefffffeefffbeefbefaffeebffffeffffafffffbffffbbfffffbfffffeffeeffffbfbbeffffeeffffbeffffffbbffeffbfffebfebffffffbebffffffeefefffebfeffebfffeffeeffefeebfefeffffbbffffffefffbbfffefefbbefbffeffffbfffaffefbbfffebffffeffffeefbfffffbffeffeffbffefbeffaffefbfffefbffffffbfbbfffeffffffbbfbbefeffaffeffefbfeffefffffffeeffffeffffffffffbbfbfefafffffffffefeffeffafffffbfbeeffefffbffffeffefaefffbfefbffffbeffffbffffeffebfefbfffffbeffeffffbffeebffffefeffefffefbfbefffffaffbefffbfebfefffbeffbfffebfffeffffffebefffffbfbbefffbffbfefbfffefbfbeffeefffbffbffbfffeefbfbfffbebeffeffeffafbbebefbfffffbffffeffebaffefffffbffffbbffffbefffebfeffefffbaefffffeffefbffeebffffefffffffffbfebffbbffbffffffefeeffffaffefbffffefbffefffebf := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask59077 : MertensSieve.bits 59077 = 0xfefffbfffbffaebffffebeffeffeeffebfefeffffbfffffbeffeefefbfeffeffffbfffffeefffbfebbffbfbbffffffefbefffbfebfeffffeffeffefbffffffbffaffbeffefeffeefffbffffffeffbffeffefffefefbfffafffeffefeefbffeffbfbfffffbbefeffffbfffeffbffffbeeffebffbbeffffffffefefffffbfffffffbfffefffffffbffbeefefffffeffffffebbffefbffbbffffbeefeffffffffeffaffffbefbffffebefffffbfffefffbfffbfbafbbfffeffffeffefffefffffffaffaefbebffbfeffffefbbffeeffefeffbffbebfffbefbfbafffebffffeffffbffffffebfefffbbefbffeffeffbffeeffffffbbffefffefbfffebfeffffbfffffeffbffffbbebbffffbeffefbbfbfebfeffffbfbfeffffeebfffbfbeffffffeffffbffeffbebfffeffbffafbfffeefffffffefbfffeffaffffbfffbffffffefefffefffbffbaffffffefbefeefeffbffaffbffefffffffffefffbfefbffffffebffbefffffffbbfffefefffffffffefbfbfffaffffbbfbfffffffefbfbeffffffebfffbffeebffffffbffeffffbfefffbbfffffeefffbefbfeffffeffffffeffffefffefbefffffffffbeeffebfffbffefbbeffefeffeffffbeffbfbfefbefaffffbbfbfebfffeffefbbebfebfeffffbfffefefbefffffbefbffefbbffffbbfffebfeffefaffeffbefefbfefbffeebffbfffeefffffffbefffffffbffaffffbffffffeffffbbffeffbeffffbefbfbffffffafffffffffebaffafffffffbfebeffffbefffffeefeffbfffffbfbfffeffbfffeffefeffbffbfbffffefffbbfffffbefffbefbfefffbefbfeffffbffeffbeffffffbeefffbeefbfbffffffffbefffeffffbfffffffbbffffbbffbfbafffffefffffffffefffbefbeffaffffbffffffaefaffbffffbfffeffbffeefbfbffffefbfbffbbebffbeffefffefbfffefffffffbfbfeffffbeffffbefffffffefffffefbffffefbefffbfffbefefbfefbfbefbbffeefbffffbffffebefbbfffffbfbbffefbbffafbffffefffffefefbffffebfffbefffbbebfffffffefbfbffffefefffffbfbffbfffffffffefffebfeffefefffffbfbfffffffefbfbffbbffffbefffffffffefeffbefffbaeffebfebfffeffbffffffffeffbfffefffbeffaeffffeefbfbfffbffeffbfffebfebfefbfbefbbeffeffffffffffffbffbeffeffeeffffffffefefbfffbffefffefffbfeffffeffbefbffefffffeeffffbffafbffffffbefefffffffffebeffeffbefbffffbaffafbeffffffffeefeffeefffbfffeffbffefbffffefeffffffffbfbfffbffffffefffffeffefbffbfbfffefbbffefbfffbfbefffffafbbfbffffebeefbffffffefffbeeffffbfffffeeffefffffebbffefbafffffaffbfbefbfefeffafbfefeffffffffffffefeffbffffbbeffebfebfefffbfffbfbfefeffffbbefbffeffbe := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask67269 : MertensSieve.bits 67269 = 0xfffffefbfffffbaffaffeffbffefbfefefbfffbfffeffefefffefffbffbbefafffeffeffebeffefffefffffeffffffbbffffffffeefeffeebffffffffffffbfffefeefbffffbefbbffeefeefffbffbbefffffeffffbfbfebffbfffaffaefbfbffbfffffffefffffffbffaffeffbffefbeffbffffbbeffebfffeffffbfffeefefffffbebffffffaefffbeefffffffbefbffeefbfbffffeffffffbffbfefaefeffeffbebfefbffbffffffebefffefbffffbbffffbeeffffbfffffeffeffbfbbfffffffbfefffbeffbfbfebfffffbbffffffffbffbffefbfffffbeffeffbeffebefffffbfbefffffeebfefefbffbfefefbfffefbeffffffffbefbffbeffffeffeefffffffbfbfefaffbffffbbfffefbffbffeffffbfffbefffffffffffefefffffffffefefbefffffffbffbfffaffffbaffffbeeffeffffeefffbeeffefbfbffbbefeefbffaffbffffffffbeffffefffffffbbfffffbefbfbffbeffeffbebfeffebbffffbeeffffffffeffffbfbbffefffffffbeeffeffebefffffffbfefffffffffbbffbffeffeefffffefbffffbfefafffebffffebaffbffffffffeebefffffbffffffefaffaffeeffffefbbffbffbffffbefbbffbfbfffbefefffefeffbffbebffbeffefbefffeffebfffeffefffeffffefffffbebbfbefffffbfbfffbffeffffffffeefffffefbffaffeffbfffffbffffbbebfffeffbefeffbebffbfebfffffbbefbebeebfefffffefbfffffaefeffeefffffeffffbffffbbefefbbffeffbffffffefeffeffbffffbfffbffbffafbfebfeffefaffefffebeffeffbffaffbffeefaffffbffffffeffbffefffefffffeffefefffffbffffbbeffffbffbebffbfffefbfebffffeffefefffffbeffebefffffafbffbfefbffffffeffebefffffbfffffbefeeffefeffffbffffefeefefbfffbebfffaefffbefffebfffaefbffbffffbffbeffbffbffffbfefaefbfffffffbfffeffaffffbffbffffeffffaffbffeebeffefffffffbffbafffffaffffffeffefbffefffefefffffffbffffffeffffffffeffffbfffffffffaebfefefbbeffffbfbbfffffaffefbbfbffffffeeffffeeffffffffffffbaffbfbeffeffffbeebffffffbffafbfffbfbfeffffffffefbefffffffaffbfbfefefffffffbfffbffffbfefefbafbfebfffbfffffffffebefffffbffefbbfffefbefefffebffbffbbffeffbffffbefffffbffefffefffbfffffbbfbfefffbeffafbeefffffebbefffffffffbfeffffbffffbffffeffffbffffffebfffefffffbffbfbeebffffffffbfefffbeffffffebffbffbfffbffbeffeffffbffffffefbfbffbeefffbbebbfffffeffbfbfffbffeffbffeffbffbeffefbefffbafbfefeffbffeffbffffbffffffbffffbffbffbeffeffaffbfbffbfefbfbffbffbeefeefffffefbffeebeffaffbfbffffeffffefbbfffffffbfffefffeb := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask75461 : MertensSieve.bits 75461 = 0xffebfffeefeffefbffbfffaeffffefffffffffeffffefbffbfefbefbfbeffbebfefbfffffefffebffffffbffbfffffeebfefffbfebbebffbbfffffefffffffffeffffefffefeeffefbfbbffbfffffbffefbefffeffffbfffffbfffffeffbffafbffffffffbfefffffebffbefbeffffbaffffffebafffffbfffffffffefbfffefffbeefeffbffffbbebfeffffafffffbfbefbbffafbeffffffffeffffffefbffeffeffaffbfffffffbefffffbffbeffffeefbfbaffbffeefbffbfbfeffebfefffffffffffffefbfffbffafbfefeebbffffffebbffeffbefaffbfffebfffbffefffefbfbffffeffffbfffffeefeffeffeffbffffbaffeffefbbfffebfefeffbfbfffffffffefbbebbffefbfefefffffffffffbeffffbfffeffefeffffffebffbeefbffbfffffbfbeffaffffffffffbeffbffffbafffefeffbeffffffbffbfffeefffbefbffffebaffbfbaeffeffeffffffbfeffffeefbefaffeffffffffbffefffebffbfefbffefbafffeffebfefffffeffefffbaefaffefbffffebeffbfbbfffffffbfeffffeffbffefffffafffebffffebfffefffffbffffbfffefbfffbeffeffefefffffbfbeffbffbffbebfeffebfffbffeefbffeebefffffffbbffffffefbffffbffbfffefffffaffbfbefbfffffbbfffffffbaffefffefbefffbaffefbeebfefffffefeffeffffffffffffffaebbfffeffefffffebbefeefeffeffbfffebfeffefbffffffffeffefffffffbfffefbbffbffaefffbffbfefeffeefffbfefeffffbbefffbfffeffaffffffefefbefffffbebbfbefffffbfbfffbfffffbffffbbfbfffffffffeffaffffffffeffeffbfffefeebfeffffeefffbfffbffefbefbbebfffffffffefffefefbfefbffffffffeefbffffbfffbffeffbefafffeffebffffefaffeffbfbffbffffffaffbfffffeffffffffbffffbefffffefbbeffffbeffffbfffefeeffffffbfebffbefbbeffffafffeffffefffffbffffbfefeffbffeffbfbfffbefeffffbfffeefffffffbeffffffbbffeffbfffffeffeefffbfeffefffbbffbfbbebffbfebefffffbffbeffffeefbffffbbffeefbefafbfffbefeeffffaffafbfffffbfffbffaffffffffbefeffbfbbfbfffbeffffffbffbfebaffefbafffffeffeffbffffbbffeffeeffffffffefeffeffefffffbeffefbefffbffbffffffaffefbfffffbefbfffffbfebfffffbfefaffbfffeffffeefbffeeffffefffeffffeffffbefbfffaffffbfffffbbeffffbfffeffffaeffffbfbbffefbeffbfbffffeffffaffffbfffbfbfebfffffbfefffffffbffefbffffebeefbffbfffefbffffffffffbaffbfffefbffffbbfbfebfffffffffbfbffffffaefafbbffbfffffeefbfffefffffffbffefffeffffeffefffffeefbefefbfffffbffbfeffebbffefbbffffbeffeffeffafbffffffbefbffeeffebefbeffbfbfffffbffff := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask83653 : MertensSieve.bits 83653 = 0xeefffbfebbeffffeffbffeeffffefffffbfbffbfffeffffffffbfbfefffffffbfbeebffffffeffefffefffbefffffffbaeffffeffbffbffeefbefeebffffffffbffffefbefbfbffffffeefbefefffffffbeffbffffbbebfebfebefffffafffebffffffffffefffbfeffefeffefbfffffbfffbffefbbefffbfffffbfffbefeffaffffbfefbffffffffeffffbffffefbeffffaffffbffbeffbffaffffbfffbffffffffbffeebbffbffbfffefeefffffffafffffffbaeffffbebffbefffffffffefffffefeffbfbfffbfbffbfefffbafbbffeffbffefffffbefffbfffefffebbfbefffffbfbafbbeffefbefffbbffffbfffbefeffafbfffffbfffeffbeffebfeffefffbbffbfbefffffffffffffffefeffaffaeffffefbfffbfbafbfffffbaffffffefbebeffeffbffeffffbfefbffbffeefffbefbeffbfbfffffffeffefffbfeffffeefefffffefbbffeefbffeffffffffefffefffbbefbefffbbffaffefbfeffffeefefbeefffffeffffbffeffffbfffbefffbfefbefeffbfffffaebbebeeffffbfffffbeffefefffffffffefffbaefbfbfffffffebfffaffffffffffbfffffbfefffbefffffafbffffffffbbffbffeffffbfffffffffaffbeffffeffeffffffebfffeefffbffbfffffffefefffffffffeffefffffefffbfefffffffeffffbffbaffbffeeffebfffbffbffefbfffffbeefefffeffffefffffbfbeeffffffbfffbfbbfffebfffeefbfbbfbffffefaffafbfefffffebbfffffaefbebfffbefaffffbfefefffffffbfefbefffbbffffbfffffbffffefffbeefffbeffeeffffeebffffffaffbfffffbebffffffafffeffebffbbffffbffbffffefeefffffebfffeffeffeffbfbffbfebbffffffffffffefeefbfbefffffefffffffbffbbffeffbffeffbfbfffeeffefffffffffffebffffffbffbfbeffefffffbebffffefeffbffeffbefeffeffffbfefffbfefeffaffeebfeffffbffbffeebbfffefbefefbbffffffefeefffbbfbfeffffbefbffeebffffffbefefffffffffebfefbffbfbfffffffffffffebffffefbffeffffffffefbbefaffafffffeffefffffffbfffefffefbfbffbffffebeffffbbffbebffbeeffffefbffffeffffbfbeeffffffbfffefffebbfbfebfffbffffffeffefaffffffebfffeffbefffffffffbffbbefefbfeffebeffffffffbffbffeffeffefbfebbeffffeffeffeffbeffeffffbffaffbefffbffffffbeffffffffffaffafffffffbfffafffefbfffffeffbffefbffbeffeefbfffefffbeeffffafffffffffefffffffbfbfffeffaffefbbfffefffbbefefbefbfefffbeffaffeffffffebffffffaefbfbffffffffbfffbfbfefaffbffbfbfebfffbffffbefbbefffffffefffffbebefbffffffefbfffffbbffefffffffbeffeffbfbffbfffeeffefffbfeffffefffffbffeeffefffffeffffafffeffeffffffbfe := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask91845 : MertensSieve.bits 91845 = 0xffffbfffbffaffffbfefffffffefbfffbeffffeefbffbffffbeefbefefffefbffffbeffffffeffebeebfffeffbffbeffffbffffbffbbfffffeefbfbbfbffffebbfffffeffbfffefffffffbfbffffefeefbffefbbfffebffffffeffffffeffeffffafbfefeffbfffffffbfefefffffeffaebffbfefbffefbbfffffeffeffffbeefffbeffeffffbfefbfbfebfffaffaefbffeebfffeffeffffffebefffffbeffffffffefaffeebffffeffffefbffffebffbefffffefffffeffaffffbfefffbffbfffbffbefbfbeffbffeffbfbbfffebfefefffffbffffbaeffffaffffffeffefbfffffbefefbffffffbffffffffbffefbffffeffffefffffeffbefffffefafffffbffefbeffffbffbbfbffffffffbbfbfebfebaffefffefffffebfefbfffffffffeffffbfffffbffefffffaffffffffeebfffffbafbfefeebfffffbffbfebffffffffbbeffeffefbfffffeffbebeebfffffffffbfffffaffffbfffffbfffeffbfffeffffffbfefaffafbfffffbfefffbffffefeffffffffbfffefffbaefeffbefffbefffffbffffbbffeffffffffefbbffffbafffffaffbfbfefbefeffafbffffffbeffffffbbeffffbfffffffffeffebefffffeeffffffbfeffffeefbfbfefeefbfbffbffbfffefffffefffffefffefafbffffffeefeffefbbfffffeffaffbffbfffebffbfefeffefffffffffeffffbffffbeffbfffffeeffeffebfffbffaffbfffefbefbffffbfefeeffefffffffffbeffaffafbfeffffffbfefbfbeefbeffffffffffffbfffeefeefffbefffeffefeffeffbfbbffffbfffffbbfbbeffffaffeffbeffefeffbffefffffffbffbfefbfffffbfbefbeeffffbebffbeffbffaffefffffeffbffbffffbbefeebbffbfbffffffffbeffefbbefffffffeffafffeffffffbbffefffefffffebeefffbbfbfffeefeefbfffffbffffbbffefffefbffffffffaffffffefeffbefffbfeffebffbaffafffefffffffbefffbfffbebefbefffffaffffbffffffafbffbbeffebfffbfffeffefefffffeffbffbefffffffefffebffffffeefaffbffffbfffbefefffefffffebfefffbbfbbfffefeefffbfebfefeebfffbffffbfffffbfffafffffbfffffafffffbffffbfffaffffbffffffffffefefffffbeffffeffffbaefffffefbffffbeebbebfffbffffffffbfbffbfffffbefbfffffffefefbbffbffffbaffffbeebfebfefffffffbffbfbfeffffbffbebfffeffbefefbeffffbefbffffffffffefefbffffffafbfefffbefffffbeffffffbaefeffffbfeffefeffaffbffbefefffefffbeffbfbeffaffaffeffbebffbbffffffeffeffebfefbffffffffffbbffeffbffbebffffffbffbeffebffbaefefbeefbffefffefbffeffffffeffffbfbeefbebfffbffeffaeffffeffbfffffbfbbfffffbeffffffbfefefffffefbeffffffebeefbfbbfffeffeffffffffefbfffff := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask100037 : MertensSieve.bits 100037 = 0xfbefbfbfebbfbfffefffffbfbbfffebfffeffbfffeffffeefffbfebbfbfffeffbffffbfefffbbffffbefffefefbfefffbaffbffffffffbffeeffefffbefffffaefffbefbfffbfffffbeffffeffefbbfffeffffbffffffffffffebfffffffefbffeefefffffffffffffffeffffefbbfbfffbffefffffffbeeffffbfbfffbfffefeefffbffbfffffffefffbbfffebfeffefaffeeffffeffeffffffefffbfffaefeffefffefffbbfffffefbbebefffffffbffffefffbafffffbebbfbffbeffffbbeffeffefaefeffeffbebffffffbfffffffffffaefbffffffefffbfffffffebfefefbfefbffefbfffefbbefeffffbfebffbbefbffaeffeffffbfffffaefbfffebeffffbfffffffefaffefbfffbffffffffffffebffbefffefffbefbbffeffbffefffefbfbfffbffbfbfffffffeffefffffffffffebeffbfffefbfffffeffbfbfefbffeefffffffbefbefffffffffbefffefeebfefefbbfbfffffbfffeffefffffffbeefeffbefbebfffeefbfbbfffffffffefefbfebffbfebfffbffbfffffefbfffffbefffffffbfeffffffbfffffffefbfbbffffbffbfffbffbefbffefffefbffffbffbfeffffaffffbbfffffaffeffbeffebfffbffefbefbbefeffaeffffbfbffbfffbfffffeefffbfffeffafbeffbffefffffbffbebffbfffffffffeffffbeffaffefffffbffffbbffaffeffbefffffffffbbebfffffbfffffbbeffeffebfffffbbefbfffebffffffbefbffeffeffefbeebfebfebbffbfffffffbeffbffefffffbfffffaefffffebfefffbfffefffffffffffbffffbbffbeffeffefbfbfffffbefffffbfbeefbefeeffffeffffbffffffbffbffefbffffffaffeffbebbffffffefefffefffbffbfffaffffffffffffefbffeffffffffbefbffffffeffffbfffffbebbfbfebfffefbffffffffbeffffbfffbffefffffafffebffffffeefbffbfffeffeffffbffeefffffefaffffffffffffffefffffaefbffefbbfffffffbbffefbfffffbbfbbfbeffbffffbafffeffffeffbffeefffffebfefffffffbfbffffefeffefffebeffffffffbebfefeeffefffbafbfeffffeffeffbfffefffbafffffafbfebfffbffbfbbeffebffbfefffbeffffbfefeeffffffbffbeefbfffffaeffffffbfefeffffbffffebeefffbbfffefeffeffffbfeffefffbfffbfbbfffefeffefffffeebbffeffaffefbeffbfffeffffeffbfbffbfffbefffbbffbefeffbffffffefbebefbffffffffffeffebbefffbfeffebfefefffffaebbfffefeffffbffbfffffbeffeffbffbefffffefffbefbbffefbffffffffffffefbfffefbffbfebffbfffefffffbefefffffffbbeffffeeffffeffffffefeeffffbfffffffbfebfefffbafbfefeffbffeffbffbffffffefbfbfebffbfffaefffbfeffffefffefbffbfbbffffffefffffefbffeefbffefffebffffeffffefbfffffffeffefefbf := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask108229 : MertensSieve.bits 108229 = 0xffbfffffbeffbffbfbfeffeffffffffefffbeeffefffbbffffffffeffaffeffbfbfffeffbfffefbebfeffffffffffbefffbfffefffffbebfffbffffffebffffffaffbfbaeffebeeffefbfbffbbffeffaefafbefbfefefbfffffffefffbfffbeffffefbfffeffaefeffffbfefefbfffffbfefffbffffffaffbffffffefefffffbffffffffaffffbefbbebfefafffffbffffbfeffefffbffbfeffffbffffbfebfffefbbeffffbffffbffbeeffffffffebeffeefffffefbfffffeffffffeffeffefbfffffbffbffefbfffeffafffefeefeefefbffffffefffffaffbfbfebfefafffffeeffebefffefbfffefbffffffffffffefbfbefbfffbfffffffbffbffffffefbffffffbffeffbfbffbfffeefeffbffffffefeefffbaeffffffbeefffbffffffefffffefbeefbfffffaffbfffeffeffefbffefbeffbffeffeffefbbfbfffffffffffbeffffbfeffefffbafffebfeffffbfbaffffffffbfffffeffbfffffafffffffbfffffbfeffffafffffeffeefefffffbffefffeffffeffffffffaffbfbafffeffebfffffffffbfbffffffffffefbffeeffffeffeebbebeebbffbfbefbfffeefaffffbffbfebffbaefbffeffffbffbfffbffbffbebeefefffffeffffbfffbffbfffffbfbffbfffbffafffeffffffffffffbbfffffbefffbffffeffffaffefbeebffbfffbffffffffbeffffefffffbffffffeffffffbeffffffffaffeffafbbfffffbefaffbfffefeebeefffbfefbfbfffeffffbfefffbfefeffbfbeffbfffebefffffffbffbffffeffffeefffbeefffffffbeffffefffffafbeffbffeebefffffbfbfebefbfffbfffebfefffffefffffffbfbeffeefffbffbffbeffeefffffffffbeffeffeffeebbffffbfffffbbfbbfffeffffffffeffffffbeefffbefffefffffffafbfefffffebfefbffffbbffffffffefbfffbebfefbffbffffffffeefbffafffffffffeffefeffffbbfbefbaefeffbfffebfffbffeffffffebefbffffffefbfffeeffffaffffbffffffefffffffbbeffefbffefbeffbefeebbefffbfefbfffffaffbffaffffbfffeefbffbffffffffffffffbffffbfffaffbffffbfefeefeffbffeeffefffffffffbffffefffffffeffbffffffffbffefbbfbffbfffbefffffffbfffffeffffbeffffbeffbefbfbfefffbfebaffaffbffbffeefffffffffbfeffffeeffffffffffeffafffffbfffebfeffefefbbffbffffbeeffffaffbfffffeffafffebfefeffbfffffefbbfbffbbeffffffbfefeffbeffffbffbffefffffeffffbfebffffffaffbffbebeffeffbfbefffffeffbffeffefffffeffeffbffffbbebfebbffefbeffbffefbaefefbffffffffbeffffbbebffffefeffbffbffbfffebffffffeffffffefbefbffffffffffbfffbffeeffefeeffefffbaffffffffaeffffbfffefeffefffffaffffbffbbfffffffffefeebfffbfbfffbffef := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask116421 : MertensSieve.bits 116421 = 0xffefffffeffbeffffaffefffeffffeeffefbffbffbffeebffffffffffffffbbffafbaffffffefaefbffeffffffebfffbfffefffbeffaffbfffefbfbeffafffffeffbffffbffffffffffeffffeefefbbeffffeffeffbfbffbfffffbfffffbfeffffeefeefffbffbbffffffeffffeebbfbffbefffffeffbefefffefbffbfffefeffaffffffebbffffbfefffbbebffbffffefeffbefbfbffbeeffffaefffffffeffffbffbbfffeffffeffbffffbfeffefefbffbffffeffffffbfffbefefffffbfbeffffbfeffffbffeffbefffffffbfbeefffbfefefffffffbbfffebeffeffbefbfbffffffeffefffefeffafffffbfffefefffffffbfebfffffffffaffaffffbfffeefffffefbfffefaefeffefbfffeefbfffffffffebeebfffffbfffbffffbafffffbffffbefbbffbffffbffbfebaffffffefbfffebfffbffeffffbfffeffefffebfebeebeffbffeeffffffbbffaffefbfeffeffffefbfffbffeffbffffffffffffebfffffbffffffffbeffbffeffbfffffefffffeebfeffebfffbffafbffbefbfffbfbfffbefefbfffefffefbebfffeffffbfffffbfebfefafbfefbefeeffffbfbffbbfbffffffefffffffffefeffaffefbffbfffbfffffffffefffbafffffbfffebefbeeffffefffffffbaefeffaffbfbfeffefbfbffbbffeefbefbfffffffbffbbffeffafffefeeffffaffefbfefffbeffffbbffbffffbfefefbefbffbffffffbfbffffffeffffffffffbbffeffeefbfbffbffffeffffbffbffffbeffbefffffffbffeffbffeffbeffefffbbeffffffffeffffbefbffaffbfffebefffffefbfffeffaffbfbfefffffefafffffffbfeffeffffaffbfbbffeeffefffbfebffbffbfefffbffffebfebfefbffaeffffefbfefbffffbffffefbefafffeffffeffbffeffffffffffbfffeffaffffffeffffffbbffffffffeffbffaebfffffbfffffbeefbffffffffbfbbefffbffffffafffffbebfebbffeffeffbfbefbffffffffffffefbffffffffbbffefbaefbfffeffeffffbffbffbfffebffbffffffefbbfbffffefeffffbbefeefeffffffeffebfffbffefbffbffffefbffeffffffffefffffbfbeefffffefbffaffbffbffeefeffffbffffffffffeffffeefffbeebffffffbebffffeffffafbfffbffffbfffffffeffeffffeefbfbeeffffffffffaffaefffbffffeffffefbffbfefaeffffffbfebefffffaffeffbfbeffbefbffffbbeffefafffffbebffbfffbfffffafffffffffefbfbffffebfeffefbfbafffffffffffffbefbbffefffffefffebfefefffffaffbffbfffffeffeffbfbfebfffbffefbfebfffffbbffffffefbfbfefefffffffbfffeffaefffbefffffeefeffeffbeffffeebbffbfbffffefffbfffefffefbfbfffbefaffffffffffbeffbffbffbfffebeffffbeffffbffffffffffefffbffffffeffaebfffffbfffbfbffbfefffbbefffb := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask124613 : MertensSieve.bits 124613 = 0xffffffffffaefaffbfffeffebeefeffbffbefffbfefbfbbfbbfffeffffffffffbefeebbffbffbfbffffefffffffafffeffefbffffbffbbefffbfffafffefffbffbbffffbeffbefeefffffffbfffffeeffefbffefffffeefbfffffffbffbfebffffffbfffefffffffeffbffbebefbfffeffbebffffffeffeffafffffffffefffbafbffbfefbffbfffebbefffbfffbffffffebffbfefbffffbfeffffeffffbfffffbffbeefeffaffffffebeefbfffefffffffeffbfbeffffffffeefbfbeeffffffbfffaffffbfefeffbfffffffbffffefbffefffebfefffffffbfbbfffeffffbffafffffbefeeffefffffffbffffffffffffefffbfffaffeffefbbffffbbffefffffffffefffffffbefbefffffefafbbebfebffffffeffbfffffefbfffbfbeefffffefbefeffeffbfbfffbffaffbffffbfebbffefbefffffffbbfffffbffbebeffeffffbffbfebfffbffbfffffbffffbefffffbffbfbeeffefbfbfffbeffffbfffffffbbfbefffeffffafffefefbfffffffeffefffffffffbfefffffefbefeffeefffbffbffffffffbffffffaffafffffbffeebeffffffefffbeebfefeffafbffffefeefefbbffffbfffafffffbfffefffbeffffffeffffeebeefffbfffffffefaffeffeefbfffeffffffffffbebefffefefbffffeffeffefffbffbfefefbaffaffbfbfebfffbffffbfffffbeffeeffffeebffbefffffffffffbeffebffffffefffffeffbefefbaffffffefeffffbbfbffffffbffaffffffebfeffffefbeefbeffeffefbfffebffbeeffeffffffbbebffbeffbffffbbffefffeffffafffefeffaffefffefffbefbffffffbebffbffffffffffefbffeffefffffeffffbefffffbffffbfefeffffffffeefbfbfefbeffffaffbfffffeffffbfffbfbefbfefafbffbfebfefbefefbeffffffebeefbfbbffffffefeffefffffbffefbeffffffefbfffffbffffbbfffffeffbffffbffbfeffffeefaffefbfeffebefffffaffbfffeffffffbeffffbeffbffffbffffebffffffbffeebfffffffffefffffbeffefbffffbfefffffffffffffafbffbffbbfffffffffeffffeefbfbbefffbeffbffbfbffffffeffeffbfffebfeffffbfffffffbbefffffeffffbebbefeffeefffbfeffefffffefffffffffbfefeefffbefbbffffffffbffefffefeebbffbffbfffffefffffbfbffbbffffbfeffffbffbffffbeefbfbbebfefffffffffbbfffefeebefffffaffbfffffbfffffffffefeffbffaffefffffeffbefbffefbbffefbbffeffbfbfebffbeeffffefbfffffffffbffbffbfffebfeffffffbfffeffeffefbfffbfbffbbffbfffefffbfeffffbfbbffbfffefeffffbffbfebffbeefffbfffffffefeffbffaefbefefffffffbfefffffeffefffbffbbebffffffbfffffffbfebfeffffffffffefbfffffbbffffbeffaefaffbefffbfffeefffbbefffbeeffffffbfefffff := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask132805 : MertensSieve.bits 132805 = 0xfefbefffffffffbfeffffeffeebffffebbfffffafbbffefffeffffbeffebfffeffaffeffffffefaefffbbffffbfebfefbfbfefbffffffefafffefbeffffffffffeeffffeefbffffbafbbeffffeffffbffbffbeffeeffffefffeffefbffeffeffbefffbfefbffefbbfbfffbffffbffbfffffffffaffeeffffffffffeffbfbbeffebfffffbbfffefffbeffbfbffbfefffffefbfffeffefffbffffffbefbfbfefeffefbefffeffffaffffffffbfbfeffefaffffbfffffbfeffffffbfefefbbfffffaffffbfefbffeffeefbfffebeffffbbeffffeefaefbfffefbfffffefffffffffebffbfefeffffffffeffaffeffffbffbffbfffffffeffeffffffffffeffbfbffffefffbeffffbeefbffefbffffeffefefffffaefffffffbfffffbfbbffffffffffbbfffefffbeefeffeffffbffbeefafbbffbffffffefbffeefffffefeffafffefbffffbaffefffebffffeffefffbbfbffffefbfffffffbbebffffffeffefbfebfffbefffbbfffffefbefffffafbffbeffeffffffffbfbeffbfffffeffbefefbfffaffffffffeebfffeffffbbfffffbffbffefbffffffbefffbfefbfbfffffffffbefffbeffbfffffeefbffefbffffffeffffbffbfffbfbefffffefbbefffffefffbefbbffefbbeffebfffeffffbfffffbefffffbffbffffbfefeefbfbefffffefbbffbffaffffffebfefffffffffffefffffffbebbfbeffbffafbffffffffffefefbbfffebfefeffffffebfffffffefefffebffbefbfffafffebfffffffefaffffffefffbaffffffefffbffbeefbfbbfbfeffffaffbfbfefbfffefeefffbaefffbeffeffbfbeefbfbfefbfffffeeffefffbfefffbeffbffeeffefffbfffffbefffffbffbefffffebfefffbfefbffeffffffffafffffffffefefffebffbefbffffffbfbfeffefffffffbffbefffffefffbffbbebfffeeffffffbfeffebfefffbeefbebeefeffbffbfffffefffffbffeffffbfebaffefffebbfffefbffafffffbffeebfffeffbfffeffffaefbffefffeffffeffaffeeffefefffffbffffbffbfffeffeffeffffbfefbffeffaffbfbfefffffffffbbfffffaefefffffbffefbfefbffafffffffbfffeffefffffeffeffbfffffbfbfffaefefffffffbffffffeffeebbeffffffffffffffffefbbffeffffbffffffbeffffefffebffffffafbbeffebefbfffffffebbfffefbefffbfffbfbefbfffbffefbfefefffffeffffffffeebeeffffbefbfbeffffffffbeffebffbbffefffffffbfffffffffeeffffeffbffbfffebfeffffeffeffffffffeffbefaffefbfffeeffefefffebfffffffefffbffbffbfffafffffbffffbeffefffffffbbfbffffefffbffbbfbffffffaffeffbebfffbffffbafbfefeffeffffffeffefffbbffeffeefffffffeefefbeffbffeeffffbffbeffffefffffeffffbbefeebfffeffffbfffefbfffffbafbfffefffefff := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask140997 : MertensSieve.bits 140997 = 0xfbfeffebeffbfffffbebfebffbfefeffaeffffefbeffbffefbffffffeefefffebbefefffffbfffefbebefffffeffefffffeffaffffbfffbffffbaffbfffebffffebbfffffbefbfffefffffffbefffffeffefbffeeffeffffbffaffeffffbfeffffbfbbffbefffbefffffbfbffffffafffffbffffffefbffefffffbebefffffbffeebbfbfffbfffffffbffbeffafffffffffefefffeffffeffffffeffeffffbffffffffeffffbbeffffffbfffbffbefbfbeefeffffbbffbfffefbffefffebfefffbfffeffeefbfffffbffbffefbbefffffefffbfffbefffffefafffffffbfefeefbffefffffefbeffbffbfbffbeefbffffbfefffffebeffaffeffffbfffbffbffafffffffbfefefbfeffffffbfffaffffbffffebbefffffeffefeffeefffffebfffffffefefbeefffbffbefffffeffbfffefbfffffbfffeffffaefefffffbfbffffefefbffffeffffbffffbbffbebeffffffffeffffffeffefffbeffbfffefaffeffbffbfffffbefeffafbfffefffffeffbfffefeffbefbfffeffeffffefffffeffffbefffefffbafbfffeffaffaffffbbfffebbffefffebffffffbeffffbfffefffffffefbbffbfbffffefbffaefffffffaffefbfffbebfffeffffbeefffffffaffeffeffffffebbffbffeebfefffbfefbfbbfbfefeffbeffffbfbfeffffeffeffffffffffbbffefbfffbfbeffffffffbefbffefffefffffffffbeffeffeffffbffffefbffffbefbfeffebfffffbfefbeffffeffbffeffffbfebbffffffffbfbfeffeffffffbffbeffbefbffefbffbfefefffffffbbfbffffffeffffbfffeefbefefbffffebffffffbffefffebfffeffbffbffbffeebfffffbbffffffefeffffbffbbfbfeffffbffbefbeffffbffffbffffffeebafffffbffffffffbffffffebfefffffefbfffefffbfffeefbfffefbffffffffeffffffebefffffffffebbefefbfefbffbffffffffbffeffbfbffbffbfefefffebffffeffefefffeffffeebfffbffeffbfbeefaffefbeffbeffffbfffffbeffefffbffffffefffffeefffffffffbbeffffaefefbbfffffffffeffffeffffbfffeefffffebbffefffffffbfeffffffffffffffeffebeefbffeffbfffffffbbefffffebbfffffeeffffffbffbfebfffbffafffffefffffbffafffffefffefffffffffbfebeffafffefbfbefbbefeffffffefffffffefffeffffefbeffffbffbfeffeffefffffffbfbffffeffffffbfffffffefbfbefbfffeefbffeffafbffffffbffbffafffffffbeefeffbfbffbffbfffbffffbfebfffeefbffeffbffffffffbfbfebfffeeffffbfbfeffffeebefffffffbffbfebfefeffafbbffeeffefefbbeffefffbffffffffbffbfeffffaffafffeffffeffffbbfffffeffbeffffffbffbeffffffffbfbbeffffbefefbefffefeffaffeffbfffebfffeeffffffbfefffbefffffbefbeffffeffffbffffff := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask149189 : MertensSieve.bits 149189 = 0xffffbffafffffbefffbbffbffaebffbefbbffaffafbbfffefeefffbffffefefbfffefbffffeffffeefaffeffffbefbffffffbfbbfffffaffffffeffebffbffffffffffefeffbeffffafffefffffffefffefbfbffbbffbfbafbffbfffeffbfbbfffefeeffefffffffffbfffeffbfffebbffffbffffffefffebfffffffffffbfefefbfffeffbffbffffffffeffaeffeffebfeffffffffffffffefbffbfbbfbfeffffeffffbfebfffefffffbfbbffffffffffffffffffffeffffffebbfffffaffafffeffeffefeefffbeeffffffbeffbfbaffbfbeeffffbfbeeffffffbeffeffbeffebfeffeffffafffeffefeffffffeffefeffbffffbfefffbffbaefbffffffffefbfefffbbfbffffeffffbffffbffbfefaffbffffbbefefffeffffbfffffffbaffefffffbffffbfefefbffbfefffffffffbeefbffffffefffbeebffffefeffffbfffbfbfebfffefffefbffefbbfffffbfbfeffebfffffbffffebefffffaffbebffffffbffffbffffefefbffffffbffffbfffbefefffffbffeeffffbffbeffefeffbffbffaffbffffbbffefffebffffffafffffaeffffffbfffbffeffbebefbeefffbfffbfffffeefbffffffffeebeffefffebffffebfefbffffffefffffefffffffffffffbefefbbefffbfffeffefffffffffefeffffbffbbfffeffffffbefffffeefaffaffbffbfffeffefefbeffbeffebffffffbfbffbeffbeffffbeffffffbeefaffbffbfffffffffffffbfffffffffbffeeffffefbfffeffeebbfbfffffffffffffefeefefffffbefbebffffffeffaffffbffffefbfbaeffebfeffffbfbeffbffefffffefbeffffffffeffbffefffebfefbeffffafffffffbbfffffbebffbfffefffffffffebfffaffefbaffbffeefeefffbffffffffffffbffeefbffffbfffeffbfbffbeffbefefbffffffffbfffffbffbfffeffaefffbffffebfebfefffbfffffffebffffffaffffffefaefffbffbffffebefffffeefffbffbbffaffffffffeeffefffbfefbefefbfffbfbefbffffebbeffffbeffefeeffefbfbeffbfbfffbefbffffbfffeefbfffffefbfebffffefffbaffffffffbffeffbeffffefbaefffffeffeffeffffafbeeffeffffefffffffbfffffffefafffffbffeebfffaffbffbebffffffeffbffbefeefaffefffffbffefbffffffefbffbfebfffffbffffefffbfefffffffffbfefffffffefbbfffebbffbffbfbfffeffbefffbefffffeffffffffbfbbffefbeffffbaefffffffbffefbffffebffbfffffffffbfbfffaefafbeefffffeffffbffffbfffffbfefafbeffbefeffefffffffbfefefffffafffefffbfffeffaffbeffffefbefffffaffbfffffbffbffffbbfbfeffffaffeebffffeffffffffffffffebbffffbfffffbfffaffbfbfebfebfffbefafffffffbfffeffffbafbffbeffeefbffffbfefeffbffeffeffbfffeffefaffbfffffefffeff := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask157381 : MertensSieve.bits 157381 = 0xeffbebfefefbbffbfffffffbfefbefefbefffffffffefbfbbffbfffefbffbffeebfffefbfffffffffbffeeffffbfbffffefeffeffffffefffffffbffefbbffffbfebeeffffffffebffbfffffbfeffffffffffbfffeffeffffffffffafbfeffeffffeffffbbfffffbffefffffbeffffbefffbfeffffffbaeffffbffbeffefffffffffbfffeffbfffffefbffffebbffaffbeffffffbfefbfbefffeffffeffeffbfbffbffbfffaffbebffffefeffbfbfefffffebffffffeeffffeeffffbffefbffbfffbffbffeebbebefffffffffffbfffefeffffbffbfebefbefffffbfbffffefeffbfffeffefeefffffffeffffbeffeffffbeefbefeffeffffffefbeffffbfffffefffffffbaefeffffffffefffefafbfeffffffbbffbffeffbeffebfffffffffffbfefbffffbffbffbeffeffaffffbbfffebfefefffffffffffaffffffffbebfffbefefffebfffffbfeffffeffbeffefefffffbefbfbfefafffffffbbfbffffffaffbfbbffeefbffbfbefbffffefeffefbffbfefefffefffbeefffffebbeffffbeffffefffefbffbffffbefffffafffffffbfffbfffffffffffeebfefefbefbffffefeffeffffffffffffffffbfffffbfeffffbffbffffbeffffffffefbbfbfffbefaffeffbfffffaffbffffffebeefffffffbfbfffffbfffffbbebfefeffaffaffeffffffffbfffffbfffebffbfffbffbfbfffeefaffffbffbbefffbbfffffffbfebeffffffffffbbffffbfefffbffffebeffbffefbffffefffbbfffffeeffeffffeffffffffbfbfefeefffbffffffefbfffbffbefbfbefffefeffefffeffebfffffffeffffffbbffffbafffeffffeffeffeefbfffefefffffeebffbfffbffaffeffbeffefbffaffaffbebfffbffbfbbfffffeffeffffffffbfbfffaffffffeffeffffbffefbeffbffefbfefffbfffffbeefffffffffffffeffbffbffeffbeffffbffefbbfffefffffefffffebbebefffffefffebffbfefefffffafffffffffefbffffbffbffffffaffeefffbefffffbffbebbfbeefbfffffafffefffbeefffbfebbffffffffafbeffffffeffffafbfeffebfffeffffbbfbfffeefbeffffefbfefffbbffeffffffeffebfeffffbfbfffefbffffffffffffefbbffeffbebffbfebeefffffffffbefffeffffbefffbffffffffbeeffffeffefffffbfffefffbbffeffffffefffbbffefbfffffffffbffbffefbfebfebfffbfffffffbffffffffbeffbffeffeefbffefbfefefbbffbffeffbfbffbfffefffffffffefbffeffbffbffefffffbfbafbfeffeffffffbfefffffefeffffbfebbfffefeffeffffffeffffaffefffeffffffffefbfffffbfffeffefefbbfbfffffffffbfffebfffffbeefeffeffbfffffeefbfbfefffbefffffafffffbfbeffeffffffffffbfebfffeffaffbfffffffffffbfbfebfffbffffbbefffffefbeffffefffffeebfffbfffefff := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask165573 : MertensSieve.bits 165573 = 0xfffffaffefffefbfbffbbffaffbfbbfffeffeffffbfffffeffeffefbbfbffffffeefbfbfeffffffffffafffffffffffffffffaffbffffffffeffeebfffefbbffefffffffbfebfffafbeffffffefeefffffffffbffbefffffbefffbfffafffffbefbefeeffffffffeffffffffffffbefbbfbeeffffefffffbefffbffffffbfbfeffffeefefffffbefeffbefefbfefffbffbbefefbfeffefeffefffffaffbfffefffffffffffebefbaffbffbfffffefffefbfbffbfefefbfefffbbffffbfffbffffbaefffbfffeffaffeefbffffbffffffeefffbfeffffeffffbbeffefefffffffffffffbfefefbeffffffefeefefbffbfffffbbffbfbbefffffffaefffffefffbefbfeffffbebffbeffeefeffeffffffffbffbffbeffebfeffeffffffbfefeebfffeffbffbfffffaffffbfffffffffeffeffeffffbefffffbfbfebfffefffffffbfffffbfebafffffffbffffffbffbffafffffeebbffefbfffbffffffffbffeeffffffbefffffbffbefefffefbfbeffbffeefefffffeefbebfefefffffffbbeffeffffefffffbefefbfffefbfffffbffffefbffaffffffefbefffbfeffffffbeffffffeffffeefbffafbfebbefffbffffffbefffbffbbffefbbfbbffefbfefeffbffbfffffeffffbffbfebfffeffffbeffbfffefeffffbffbbffffffefbfbeefffbeeffffafffffffbfffbefbfbeffffffefbefefffebfffefffffefffebfefffbeefeffbefbffffbfffbfbfffbffefffffbfbffffefeefbffbffefffffffbfffeffbfffffeefeffffbbffbebefbfffffbfffffbfefafffffaffffbfffeeffffbfbffffeffffbffeefffbfebbffefffffffbfebbffbffeffffffffbefffffeffebefbfffefbffbfffffffffffbffffeffefeffffbefbffbefffeffffeefffffffbffaffefffebfffffffffbfffefefbbfffffbfbfeffffbefafffefffffeffffbffffffffefbfffbfbffffffeffeefefbfefbffffbfffbffeeffffffffffbfbfffbfffeffffefbffbbfffffbefefbfeffffffbfffbfffeffffffffefbffbfbbfbeffaffffffffffffefefffffafbffbffbfffeffffbffffffbefffbffffefefbaffbffeeffffffffffffbefffefffffffbfbffbffffefaefefbfefbffeffefffffffffebfeffefafffffffffebeffeffffffefefffefbffeefffbfefffffffaefbfbffbeefbffffbbfbeffaefefffffbfbefbfffeffffbffbfefffffffffbbefeebaffffbfffbfbfffafffffffffebfffbffffbfefffbfebfefffbffbbfbeefaeffffffbbeffffefffffffffffffbfffbffeffffffeffefefbbefffffffbefafffffffbfffaefefffefffbffbfeffffbffbfffefbffeffefbbfffffffffffbfffeffffbffffbffbbefefffffffbffffefffbeffbffffffefffbbeffffefffffeeffefbffbffffbffffffeffffffebeebaffffffefbffeffffffffefbfeffebfff := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask173765 : MertensSieve.bits 173765 = 0xfffbffbbfbeffbffafffebfffffffefffffefffffebfefffbafbffbfefeefbfffefffffebffffffbffffbfebbfffffffffffeeffefffbfeffebfffffffffaffffbfffeffeffaffbfffffeffffffffffffffaefffbeeffffeffbfffffbebfebeffbfffffefffeffffbffffffffbeffffafffffbfbffbfffaffffffffffbfeffffffffffbfffffbffbfffffbffffffffbffaefffbefffffaffffbffffffefffffbffbffffbfffefbefffffffffffefbfffbebefffffbfbefbfffeffbfffffeffffbefffffbffbfbfefffbfefbffefbbfffebeffffbbffbebeffeffbffffffebfffefffffefffffffffeffffeebfffeffbffffbfffbebfefeffeffeebbfbfffbefefbafffffffffffefffefbebefbefffffbffffffefbeffffafffffeebfffbffafbfffeffbffffbfebfebeffbffefffefbfbffffefffbbfbfefeffeefeffffbbffeffaffeffefbfffffbeefffffffbeffefeffffbfeffffeefbffffffefbeffffbfffffbfbbfbfefbfffffefbfefeefeffffffffbffefffffbffbebfeffebbefeffeefffbefffffbffaefbfbeffefffffeefffffffffffffeebfefffffffffbbffbefeefaeffffffbbebffffefbfffeffeffebeffefffffbebffffefffbeefffffffeffafffefbffffbeffeffffffebfebfffbfbfffbffffbbffeffffbfefffbfefffbfebffffebffffffafffeffffefffffbffbffeefbffeffeefbffeebbfffffffffebfffbffbffefbbfffffaffffbbfffffffffffbffafffffffbfffffbffffeffeffffffffefffbefffffbfffefbefefbfffffffebbeffeffffffbbfffffffbfefffbbfffeffffbffeffeffffbfffbefaffffffffefbffffffffbbffeefeffbfffffffffffbfffffbebbfffefbeffffffbfffefbaffffbbffbffffffefefffffffbfebfefaffafffffefbeffffffebffbffffeffffffbfeffeffffaffafbfffefffefaffefbfeffebbefefffffbebffffffbffaeffeffefbffeffeefbffeebeefffbbffffffffeffffbeffbefefbeffbffbfffebefffffefbfffffffebeffffbfebbeffffaefffffebffbfffaffeffaffffbfeffefbfffefffbeffbefeffffbffffffafffffaeffffffbbffeffbfbbffeffbffefffebfeffffeffffffefffffffbffffbbffffbeffeffffbfefbffefffffbfbfebffffffeffefffefbfffefbffbffeffbefffffffeffffbffffffffffffffffeffeffffffbffffebfebefffffbfffffeffbffafffffffbfffbffaffeffbefefffeffffbfbffffefefffffbfffffefbaffeffefffeffffbfffffbefffbeeffefbffeefffbfffbffaffffffffefbffffffffbbeffebfefffbffbfffefbfffefffffbffffbfefaffffbffbfefeffffbafffeffffefffffeffffffeffefefbefffeffffeffbffafbbeffebffffffaffbffeffeefeffffffffeffbefeffefbfffffbeffbffbffbfbffbfffffbaeff := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask181957 : MertensSieve.bits 181957 = 0xbfffefefffffeefffffffbffbffffbbffffffefefbeffbeffebfffefffeffefffbeeffffbebffffffbeffffafffffffbfefffbfeffffeffeefbffffbfefeffbfffffaefffbeffbfffffbffbfffefbefefffebffbefbbfffffaeffefffbeffaffefffefeebfeffffffbbffffffffbffeebffbfefbfffffbffbfffeffffaffbffbffffffffffffffbeffffafffffafbffbfffbfffffeeffebefbfffbffffbffffefaefffbfebbfffffeffbffbffbffefffffeffbfbbefefbeefffffeffffeffeffefbfffffbfffbffffffefbfbffffffbfbfefffbfffbefbffeffbeffeffffeffbfbfffeffbefbfbbfbfefeffeffeffffffffffffefeffbfbffbffbbefffffffbffffffffffffffffffefeefbfffffbffeffbffbffffbbeffebfefffbefbfeffffbffffbffffffefbfffffbffbffffffeffbffbffbfffefeffbffaebfffffffefffffefffbffbfffbfffefbffffffefafbffffefeffbefefffefbfbefbeffeffaffffffffbfffffeeffffffffefffbafbfffeefeefbfbffffebeebbffbffffbfefeebfffefbfffbfffefbffffffffffbffbffffffeffffffefbefaffbfffeffffffffffbeffffeffaefffbfefbfffebeffeffbfbfffeebfffeffbfffefffbaffeffffbffffffffffffffffebfeffffbffeffffbffffefbffaffffffffbfffffefbfebfffbffbffbefbfbfebfffbffffbbfffffaefefffffffbefbbeffffffbffffefeefffbbefbffefbfffbffafbbfffffbefffbeeffffeeffffefffebfebefffefefffffbffeebfefffbffbbfbeffaeffffffbfeffffefffffbefffffebfefbfbbebbfbffffffbfbeffbfffffeffeffffffefffffffafbbfffffffbbffefbbfbfffffbfffffbfeffefffffffefbeffbefeeffefbfbfffffbfeffefafbefbfffffbefffffaefffffebfefeffffffffeffafffffbffffbfffbefafbffffffffffefffffeffffefbeffbfbfefbfffeffffafffebbfffebffffffefbbfbefffffffbefbffffebfefffbfffbefffffefefffffffffeffffbffeeffeffeffffbffbebffbfffeffbffffbffbfebefffffeeffffefffefbfffffbefefffefffbbfbfffefbbfffffbebffbfefbfffffaffbfffffeefbfffffffffefbffeffeffffffffafffffffffffeebfefbfbffffefffffeffffffbfffefbeefaffffffffffbbffafbaffbfbeffeffbffafffffffffefefbeeffeffefbffeffaffbebfefbffffbbffbffffffffffbffbfffffbfffbfffffffbffffffafffffbfbffbeefffbfffffbfffeffeffeeffffeebefffffbefbffffbfefbffbfffefeffbffeffbeffffffbfffffffebfefffbefffffaeffebffbfefffbbefbfbfffeffeffeffffbfefbffefffebbffeffbffbfbeffffffebfffffffeffebefffffeffeffffbfffeffffbbefffffefefffffaffbfbfffeffafbffbbebfefffffffaffbeffebfffaffefffefffbfe := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask190149 : MertensSieve.bits 190149 = 0xefffbfeffeffffeeffffafbfeffffafffffeefffbeffffffffbffbfffeffefbfbfeffffffbbffbffeeffffffffffafbaffbffefbeffefffebbfffffffffffefbfffffbbfffffbefbfbeffeffffffebffbfefbeffffffbbeffffeffeffafffffeebfffbffbfffefffbffffffbfffffeffeffffbbffffffefaffaffbffbebffffffbffaefffbeefeefffbfeffefffbbfffffffffebffbfefffbefffeffefbefffbbfffffeffbffefbfebffffffeffffffffbfbffbefffffbebfffefffefbffeffffbffffffaffffbffbffbfefeffbffbeffffaefffbffffffefffefffbbfffeffefaffffbbfffebffffeffffbefffbfeffffffffffbfbfffffffffefbfffffbbffbffafbfffffbffffffffffefefbeefaffbffffbffffefbfffffbefefffffbfbbefffffffbefbffeebbffffffffaffbefbffefbbffefbffffffffffefeffffbbeffffeffbfbaebffffeffefbffeffffbffffffffffffffbeffefffffffffebffbfffbffeefffbfeffefffbfffbffefbeffefffffffbeffaffeffbfbffffffeefbffbeffeffeffffffbeefffffffaeffffefbbeffffbffeffefbfffeebbffefbfffffffefeefffbffffffefffefbffbfbffffebafffffbffbfbeefffffffffbbfffeffffefbeefbffffbaffbffbefbffffffffeffffbfeffeffffffbfffbefffbfffffbbfbffffffbffbfffeffffffffefbfffefffffffbffefffffffffebbfffffbffffffffbeffffbffbfffefefffffbeffefefbbffaffefffffffbfefffbfefffbffffefbfbafffffffffffbfbeebfebffbeffffffebffbeeffffbfbefbfefffbbffffbfffffbfffbffefffffffbffbaeffffeefffbfefeffffffefbffefffffefbffbbefeffbffffffefbebefbfeffffeffbfffffeffffbffffefffbbfffffffffeffefaffffbfefbfbefffffffffeffffefffefbfbffbfffeefbffbffafbfeffeffffbfbeffffffebbeffffbefbffefffefbffbfbfefffbfefefbefffffffffeffffeffbffffffefaffeebfefffbaffbffeefbfbfefffffffaffffffffafffffffbfffffbfffbfbeeffffffbaffffbaffbffffffffbfbbfbffbeeffffffffebbffeffeffefffeffefeffbefbffffffffefbbefefffefbfbffffefefffefffffeffffbfbbffffffffefffffeebbfffffaffbfbfefffffebffffffeffbfbeeffefaffefffffffbefffffbffffbfffaffbffeebffbfebfefbfffefbebeebeffffffeffffffffffffffeffebfffffffffafffefffffffaffefbbffffffffefffeffeffffaefffbbffffbfeffffbffeffbfbefbefffffeffffbfffffffffffffefeefeffaffffbffffffbefefbffbbffefbbffefbbeffffffffefaffbffffffebfefeffbeffffefbfffbfbaefffffffbefefbfffbffffffffbffffffffffffffefbffbbfffebfeffffbfbfefeffeefffbffbfeffefbffffffffbfffffefffffbff := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask198341 : MertensSieve.bits 198341 = 0xfbfbfffeffefbeffbefffbffffffbebbfbfffbffeffffbbefffffffffbbfbfebeffbffaffeeffeffefbefbfbafffffefffffffbfffffffffaefeffffbbfbefbeffefffebfefffbbefaffefffffefffffffbbfffffffbfefffbeffffffffbffffbbffffffffeffffbfffffffffaefbfffefbfbffbbffefffffffbeeffefeffbffbffefbbefffbfeffefefbaeffffafbfffffffeffffbffbfbffbfefffffffbffefffefffbfebfefffbfffbffefbfefeeffffbfbefffeffefbffffbfebffbffffffffbbeffffffbfffbfbeeffffffbfffbffaffffffffeffffbeebfefffffffafffefffbffbffffffbffbfffffeffffbfeffebffbbffffbeffffffffeefafffffbeffffeffffbafbbffffffeffffefbbebefffffaffbfbfebfffffffffffbfffeffffffffffffffeffaffbfbeeffffffbeffffffffbfbffbfffffbbefbfbfeffefafffefbfffffeffaffefffffeeffefffbffffeffebfffefffebbefffffffffffeffffffffffefbaeffefffbfeffffffbffbfefbffeffffbffffffffffffffffebfeffffaffafffffefbaffffbfebfebfffaefafffefffbffffffefffefbefeebfffffbfefffffffefffffeffffffffffffffefbffbfffbefbffbffbefefbfffefffebfefffbfffeffaffffbfffeffffbeffffbffffeffffeebbffeeffefffffefffbffbefffffaffbefefffffbffeffbfffeffffeffbfffffeffeffbffffffefffffffefbfefbeffffeefffbbffbfffeffffaffeffffffffbffbffbfffefffbbffffffffffffebeffeffbffbffffbaffeffffbfeffffeeffffbeffefefbfefffbbfbbffeefeffffffffbffeebaffeffefbbeffebfefffbffbffffefeffffbfefbefefffffefbffbffbfefeeffffeffbffffffefbffaebfffefffffaffefffffeffaffefffffffbffffefefffffbffffbefffffffbbffefffffafbfeffffffbbffbffbfffebffbeffffffefffffeffefbffffbbfffebbffbfffffffffebfffefbbfbfeffebeffffbffffffffbfefeffbfbfffffffffbfbfefffbfeffffbffeffffbffffffeffefbbfbeefffffffffffffefffffffbfffbeffffbefffffffbeffffaffbfbefbfeffefbfffffeeffffefffeffffefbbfffffeffbfbefbffbefffffbffefffffffbfffffbffffefeefbefefbbfffffffbeffffffebfeffeffffeffeeffffefffffbffbebbfbfffbefffffebfebfefefffffeffbfbeeffeffffefffeffffaffffbfffbfbffffffffbffffebfebbfffffeefbfffeffefbfbbffffbefffefffbefffefefffffefffffbefffbffffffffbbffeffeffffffebfffffffffefbffffefffffffeffaeffefffffeffffefbbfbeffaefeffffffebfffffffffbfbfebeebbefbfffffffffefeffffffefffbfffeffefffefffbffbeefffbfefffbeeffffbfffeffffeeffffffbffbffbfefafffffaffbffeeffefbffeffffffebf := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask206533 : MertensSieve.bits 206533 = 0xbfffffffbfffefbbefbffbfbfffffbbffeffffffebfffeffbffaffbfbfffaffefbefbffbeffffffffbfbfefeffbffbfffffffffeffefffbfffffbfffbeffffbebffffeffefffbfffbefeefffffffffbbfffefbffbfbfebfeffebbffeffeeffffeebbffeffbfffefffbefffffbffbffefbefffffbfbfffffffffbffeffbefefffffffffffffbfefeefffbfebffbfefffffffeefffbeffbfffffffbfefffbeffeffffffffffbfefbfbffffebfeffefeffbffbfffebeffffbfefbfffefbefefbfeffefefffffeffbebffbffffefbffbffbfffffbffefbbffffbffbeffefffffffffffbefefbefffefeebfffbfbeffbfffffeffbffeffffffffffffffffffeffffbefaffffbfffefbfffffffefbfbeffeeffffffffffffbefffffbffbefefbfefffbbfbffffffbffefffefffffffffffffeeffefffffffffbbffbfffebbffffbfffbeffffeffbfbeffffbfffefffffeffffbfefffffffeffffbfeffffefbfebbffffffffaffaefbfbfffffffffefbfeffefeefffffffbefffbbffbfffebfeffffaefffbbffffbffffefffbfebffbfffbffffffffbebefffffeffefffefefbfffffbffffffeeffffeffbefffbefffefbfbffbfffffbeffaffaefffbefbfefffffebffffefffffffeeffffefbaffaffbfffffffbfffffffffbeffffbffefbfebbefffffffeffeefffbffbbffafbffffffeffefffffbfbffbeefffffffffbffbfffbffbffbfffebfffffffffefffffefbbfffffbfbbefffbefffffefffefffbaffbffffffebffbfffffbaffffbfffbefffbeffbefeeffffefffebbffeeffefffbbfbbffeefeeffffffbfffefffefbffbfbfffffbbefbffbefffbfebfefffffffbfffffeefbffefffebeefeffeffffbbfffffbfffffaffbefffbfffeffbffbfbfffafffffefffebfebbffefbfefffbffffeffffefbffbfefeffbffffffefeffeffbffaefbffefbfefbffbffffffebbefefffefbefeffaffeffbefffbffbfffffbfffffffeffffbfbfffffbfefefffffeebffffffaffffffebbffffbfffaffeffffffffbefffffffbfbffbffffffbffffbfefefffffaffbffefbfeffffffbbfffeffffaffefffffefffffeffbebfebeeffffefbafffefefffffefffebbfbffbffffffeefffbfeffffbfbafffefefffffbfbeefbfffeffffffffffbebfefeffbffbfffffefbfefeffeffffffefaefffffebbffefbeffbfbffffffffffefefffffbffeffeffbffaffffffefbffffbffffebfefffffffbebfefeffbffeffbfffffeeffffefbffbbeffffaefaffefbfebfefbefffbfefffffefefffffefbbfffffaffafffffbefefbfffeffefffebffbffffffafbbfffefffffffbffbefeffffffffbeffeffffeefeffeeffffefffffffffebffbeffbefaffeffbfbffffffffffffbebefbbffffbbffffffeffffffffffffbfffffffffffbfebffbbffffbeeffffffffffbfbff := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask214725 : MertensSieve.bits 214725 = 0xefffffffbefffbefffebfffbfffffbebbfbeffffffffffbfffefbffffffbffffbffbbfffffbeffefffbffffffeeffffefbfffbffbefffffffefffffeffffbfffbffeffbffbeffebfefefbefbfffeeffffefffffbfffffffffffaefffffffaffaffeffbffeebfffffffefbfbfffaffefbffbbfbfebffffffeebfefffffffeffffbfffefffffeffffbbffefbfefffffeffffffbfefefbaefbffffffefbffaefffffffaffffbfffbefffbfffeffaffffffeffefeffefbfefefbfffffffebfebeffffffffffffffffbfefbfbffffeffffeffbffbefbfbfefaefffffebffbfffffffffffffefefbbefaffbffbfffffefffffffffffeffffffffbebffbffbaefeffaeffebfffefffffffbbffeefbffbffeffbfffffeffeffbffbefefbbfffffffffffefffffeffbefffbeffbefefffebfffffffffafffffbfffffeffbfbbfbfffeefeefbfffefbffffbeffbffbffffffffbfffffeffffffeffefefbffbbeffffbffffffffffffffbeffffffffebeeffffffbafbffbeffaefbffefbffffefeffbffffbbfbfefbffeffaffbffffbaefeffffbbefffbfffefbaffffffebfffeffbefbfbffbfefffffffbffeefbefffbffbfffffbbffbffeefffffebfffeffefbfefefffffffffebfefeffeeffffffbffffffbefffffffbfffeffffffbfefffbfffbefbfbffbffbeffeffbffafffefeebfffafbfffbeffffbffffffffbffefffefefbbefffbfeffefffbffffeffeffefffbafbffffffeeffffefbfeffebbffbffbfbffbffffffaffffbbefeefffffffbfffebefbfefffbafffeffefeffbfbefffffffffffffffffbfbffffffefffefbffefffffbffffbffffefbefbffefbbffffbaefefffffbfffffeffffbffffebfefffffffeefffffebeffffffffffbfeffffefbffffffeffeffbfffffbfbefbfeffffefbbefffbeffffbfffffbfffffffffaeffebfffffffffaffffbfeffffffbeffffbfefeffaffeffbfffebaffbffaefffbeebffffffffbfffeffeffefbbffbebffffffefbeffffffffeefbffffffeffeffefffffefbfffffaffbfffefbffffbffffffafbfebffffeffffbfbfeffeffffffbffbbebfffeefbfbffbffbfffbfffffbfffefeebefffffeffbffffffefafffebffffffbffefffeffefffffffbffffbfeffffeeffffbebfffffbfffeffaffffffeffffffbbfffffefffefbfffffffbefffefefffefbfbefbbffbffffbfefffffefffbfffffffffafffffbefffbffbeffeffbefffffffbefbfbfefbfffffeeffffffbbffefffefffbffffffeebefffffbeffffffffefffffffbffeffbfffffffbfefffbbefffbffbfebffbbfffffeffffbeefefffffbebffffeffefeffeffffbeffeffeffbfffffffffefbfbbfffefeffaffffbffffffffbfefffbffbfffffffffffffefbffffbfffffbbfffffefffffbfbfffbffeeffffbffefbbfffebbffbfbbfffefeef := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask222917 : MertensSieve.bits 222917 = 0xbffffffbffbffeffeffbffafffebffffefeffbfffebeefffffffffbfffeffaffefffefbfbffbffffffbebbeffffbffeffbfffffeffbffffbfefbffffffffbffefffffffbaffbffbfffffffbefffffbfbbffeeffffbffffffffeebbffeffeeffebffbfffafbffbfefefffeffffbefbefeffbffefffffffffefbefffbeffbeffefeefffbbffbffffffefffbffffebfffaffeffaffffffffbefffffffffffebeeffffbefffbfffeefafbbebffbffbfefbfbbeffeffffffffffafbbffeffeffafbffffefeebfffeffbffbfbffbfffeffbfffffeffbffefbbeffffefffffbfbffffeffeffffffbfffbefeebfefffbeefffbfefeffbffeefffbefbbffffffeffeffffffffffeffbfffffbffefbffffebefffffefbfebfefffbaffeffbefbeffefffffffaeffffefffefbffeebfffefbffffffefffffffbfeffffafbfefefbeeffffbffffbfffaefafffffffbfefeefbfbfffbebfeffffffbfffffbeffeefbffffbbebfffefffffefbfffeffbffbfbafffeffffffffffbfbbffeffbeffffefffeffeffffffbfeffffeeffeffffffbbffffffffffffeffffeeffffefffffbffffffefefffffffffffbffeffbffbfbefffffbfbfebffffebfffafbeeffeffebefffffeebffbfffeefefffebbfbefffffbffbffbfbefbfefbfbffffffffffffffbbfffefffbfefbfffebffbffbfffaffeffbfbefbfffbfffebfffeefeffffffeffffffbfffbffffbfffffffffffbefffffefbafffffffbffffffbffffbaefffbfefbefefffeffeffffffffffefbffffefbefefbefbfeffefefffffffbfffeebfffbffffbfffffbbffffbfebfffefbfffeffefffebffbfeffffefffffefbfffffbfffbfffffeffbffefffebfefbffeffffffefeefbffffbbffbfffffbffffffffbffefbeffefbefffeffefaffbffbffffffeffffbffbffffbfefeffeffffffebfebfffafffeffefffffefefbffbfffffffefeffbebfeffffaffefffffffffebbffefbbefffbfffeeffffffbbffffffffffbfebfffeebaffffffffbfbfebfffffbefffefffbaeffffffffffffbaefefbfefffbfeffffeffaffbefffffefffbffffffefffefeffffbbfffefeffaffefbfeffefbfffffffbfffefffeffffffbffbfffbefeffefbffbfffbefeffffffffeeffefbfbffbffbfefbffffffffbffeffeffbfffefbeffefbffefbffffefffffffffbbfbfffffbfefefbbfbfffffbeffbffbeffeffefeeffffefbfffeeffffafffeffefffffffaffeffbefefbfffbffbffffffefbfffffbfffebfffbffffffffffffefaefafbfffffffffefffffaefbffffffffbffefffebffbffffffeeffefffffffeffeffffffebbffefffffbffeffeffefbffffebfefbffffbffffefffbefffffafbffbeffbffbfbeefffbefbaffeffafbbfffffffffffffbfffeeffffffbbffbfffffaffaffeffffbfebfffbffaffbffefbeffbffb := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask231109 : MertensSieve.bits 231109 = 0xeffbffeffbffbfbeebffffffefffffbfbbffffbfeffffbfffffffbeffefffeffffffbbeffffffbfffffbfffefbbfffebffffefffbaffffbeffeefeffffffeffefefffffbffbfffebbffefbffbfefefffefeffbffbffffffffbfffeffffffbfffaffbffffbfffeefbfbffbffbfffbeffffefffffeefafffffbfbfefefbfffbfffffbefffbfefefbfefbeffffeffbfbafbfefffffffefbbeffebfffffffffafbffbfefeeffffeebbfbffffffeffffbfeffffbeffffafbffffffefffffffbfefffbbffeffeeffffffbeffafbfeffffffffffbffbffbfffffeffbfbfffbffffffffefffffbffffbfffffffffffffefefffffbeffeffffbffbffbeffefffbbefbffefffffefffefffbfffffbeffaefbfbefffffffffffafffebbffeffbfffffbfbfffeffaffffffffbffffffefeffeebfebfebffffffffffffefbfffffbbebffffeffefefbfefbebfffefffffbeffefffbfffeffffffffeffbffefffffbfbffbbfffffafbfeffeffffefffffbfbffbeefffffffffbeefbfffffeefbfffffefffffffbffbfebfffffffffbffeffbffeffffbbffffbfefefbfefffffffeeffffeffffbffbfffbfffffbfbfffeffaffefbffffeffffffffebfffeebbfffffffbbfffffbfffffbffffbeffafffffffffefffbeffbffeffffbeffeefffbbeffffeefbffffffffbebfffffffffeffffffeffffeffeffffffebfffefffefffffffaffbffffbffbfffeefbffbfffffffffefbffbfbffffeffefbfbffffffeebbffeffaffbebffbfffbffeffbffefffffefbffbbffefffffafbbfbfeffeffffefbfefbefefffffffbfefffbefffffefffefffbfebfffbfffffbebfebfffbffbfffffefbaeffffffbfffffffffffbffffeffffaffbfbafffffefbeffbffbffffbffffefbfbeebbefffbeffeffbfbfeffffbffefbfffbfffffbffefffffbffeffbffeffffffebfffaefbffffffebfffeffbffeffffffffffffffeffffbffbbffffffeffffeebbffefbffffeffffeefeffbfbfffffffefafffffffffeffffeffefffffffffefffbaffbffffffffbffeefbeffebbfffffeefffbffbfffbffbfbfeffffeffffbfeffebfffafffffeefffffffbffafffffffffffeffffffffbfffffafffffeffffbffbeffbffefbfefefbfffffbbfbfefffffefffffebfefffffffaffbfffeffefbffffbfeffefffbfefbffffbbfffeffffffbfefffbffbffffffafbffbefffefaffffbfefffbbefffffeffffffbbffffffffffbfffffffffeffbfffebfffbfffefffffeffefefbffbfebefffffaffffffffefbbffffffffbefffbbffffbbfffefefffefbffbfffebffbaffeffbffffbffffffffffffffbfefefffffefffeffffbffbfffebbfbfeffffbfbbfbbffeeffffffbfeffebfffaffffbfebffbfefffffffbffbfbfebfffbfbeffffbeeffefaffffffeffffbfffffeffffffefffffffffbffffe := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask239301 : MertensSieve.bits 239301 = 0xfffffffbffbffbeffeffefffebfeffefbffffbaffffffefefffffbffffbfefeffefbffffefeffbfffffffffeffffffffffbffbffeebffffffffbfffffbefffffbfbfffffbeefafbbefbfbfeffffffffffffbefffefafbfefbefeefffffffbfbfffeebfffefbffffeffffaefffffebbfbffffefeffeffffbffbbffaffefffffeefffffffbffffffffbffbffffbfeffefbffeffaffffffeffefbffffbbeffffbefefbfefbffefbfffbfffebfebffffefffffefffffefffffffefbffffefaefffbffffefffffffaffafffeffffbffaffffffefffffffefbffbffbefbeffffbbfbffffffaffbfffefffbfebeffffffebbfffffaffffffefbebeffefffffeebfffffffeffffafbbfffefbffffffffffbfffeeffffbfbffbfefeefbfffffffffeffffffbeebffffeffffafffffbffffbbffbfffffffbeefbfffffefffffffffefffbbffffffffeefeffeeffebfffaefffffeffffffbefffffbefbffeffeffbfbffbbfffebffffffaefffbfffbefefbfffbefefbfffefffffbffeffeffbfbefbffffefbffbfbbeffebffbfefbffbeffffeffaefbffffffefefbbfffffaffffbffffeffffaffbeffefeffeffffbbffffffffffbfeffeffefbffefffeffffefffffbffefbffffeffffbfbefbffbfeffffeffbffbeffeffffffffffffffebaffffffebfffffbbffbfbfefffffebbefffffefffbefbeefffffffbfbeefefffffeebfeffffaffbfffffbfffffbfffffffbfefffffffffbbffffbefbfffefbefffffffbeefeffefffebfefeffbffeeffffffffffbffffbffbfeffffbffffffffffbbffbfffffbffefbbffffffffffbefbfefeffbeffffffbfffafffefffffefeeffffbffbfbeefeefffbffbfffffffffbfffeffebfeffffbfbbffbffeebefffffbefffbefffefbffeffffffeffffefffffffbeffeefffbfffbfffffeefffffebfefffbfffeffbfffefeffbffeffafffffffffffefffeffebeffbffbffbfbfebffbbffffbeefbefffbfffffbefbbffeffaffbfffffffbffbfffbffffbbfbffbbffbfbbffffffffaefefffffbebfffbeffffeebffffeffffefbfeffeffefeffffffebffffffaffffbeefbefeffbffbffffbfebeeffffefffffbfffffbefeffffffefffbfefffffefffbfebeffaffeffbffefffefffffffbfbeffbffffffefffbeffaffeffbeffeffeffffbffeffffffefbffffbbefbfbffbefffffeffffbfffeffbfbfffbfbfebfffbffffbfffffffefefbffbffbeffffffffeeffeffffffffffbfbfffeebefffffbfffffffbbffbfbafffffffffffefbefffffeeffffbffbfbfffeefeffefffefffbfebafffffefbbfbffffefffbeffbffeeffffffffefffbefffefafbffbfffffbbffffbbfffffefffefbfffebffbfeffffbffffffefeffbffbffeffbfbffbfefffbbfbbeffeffffeffffffeffffeffafbeffffffebbfffffeffbffeefffffff := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask247493 : MertensSieve.bits 247493 = 0xfbffbfbeefeeffffeefffffebfffbffffbffffffbefbfbbffbffeebfefffbfffffbefffffffbffbfeffeffffefffefffffffffffffbebbfbffffefeffeebfebefffffeffeefbefffbfefffbefbfffeefbffffbbffbffefbfefbfbbfffeffebfffbffbffbfbeeffefffffebbfffffbffbfbeeffffefbeffafffefffbffffffffbbffbffffbbffffffeffffffffeffffeffffbffffffaffffffefffbfefffffefbfffefbefefffffffffefffffffbfbfebffffefeffffffffeebfeffffbfffefffbefffffbffffffffbffbfffefbebffbeffffbbefbfffeffffaffeffffbfebefffffbfbbffefffffffbbfbfeffebfefefbffbfefefffefffbffffebfffeffbffaeffffeebeffffffefbffeffbefbfffffbefeffeffefffffbfbefbbefffffffbeffebeffefbffffefffbfffffffeffffffbbffefffffffffffffffffaeffffefffffefbffffeffffbffeffffffffeffbffffbbfbffffeffeffffbebffbefbeefefffffffffebbefffffffffbffbefffffefbbffeeffffbfffffbfffffefffffefbbfffefbfffffbfffefefffffeffffffeffffbefefbffbffbfefeffbfbfffffbfffeffffbbeffffeefbefffffeffffeffbffefffeffefeefbefbfbbffffffffefffffbfffffffffefeffeeffeffffbffafffffbebffffefffbeefbfbfffeefffbfebffffeffffaffffffefffffefffffffbefffffefffbfefffbfffaffaffffffffffbeffffbbefbfbeffeffbfbeefbfffffbefaffefffffefbffffffbefbfffffbfffffefbbfffffaefffffebfebfffaefbffafbffbfefbfffffeffffbffbeffbfbafbfffefffffffbfefffbfebbffafffffffbffffffeffffbbffeffeefefffefbfbefbfefffffebfebffbeffefbfefbefefffffffbfffffbffffffffbfffffffffbfffffffffebfefffffffffbfefeffbffefbfffffffffeffffbffffffffbefffffbffbfbefffffffffffffbffffffefffefbfffffbffeffffbfffefffefafbefbbffefbfffefffebbffffbbffffbffbffffffeffbfbaeffffefbfffbffeffffbfffbffeffeffbeffffbfffffefbffbffbfffffffffbffeefbffffbffffebeffeefffbaffffffffbffeffaefbebffffefffbeffbfffffeffeffefbfffffbffffffeeffffeeffefbffbffbefffffffffbfebbffffbbefeffbffffbffffeffffefffffffbeffbffffffffffffffefbfebbfbfebeffbffbffbefefffefefbbfffffeeffefffbbffbeffffbfffffefffebffbeffeffeefbfbfeffffffbeefffffeffffffbeeffefffbeffbfffffbeffeffffbffefbffffffbefeffbebfffffbfefffbffbffffffaffeffaffbeffffeeffffaffffbfeffefbfbefbfefeffefffffaebfffffffefffbbfffffeffeffeffbeffffefbfffefffebffbfffeffaffbffffbfeffefbffeebfffffffffafffeffffeebaffbffbfffffefbfffaffbfffeff := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask255685 : MertensSieve.bits 255685 = 0xfebbffefbfffbebfffbfffffffffebffffefefbffffffffffeffffefbbfffffeffaffefbfffefbefffffeeffebeffbffafffffffffffbefefbffbfebffbbffefffffffffffbffffbfefbffeebfeffffbffbffeefeffbfbffbbffffffffeffbfbfeffefbefbfbfffbfffffbffeffffffefffffefeffeffffffefeefffbefffffeffffffffbffbfffffaffffffffbebeffbffeffeeffefffffefafbfffbefffffefffbfffbffeffafffffbebfeffeffffeffbfffffefffffbffbfbbfffeffffaffefbfefeffbfffffffbfefefffefbffefffffefbfffffffebbfbefbeffafbfffffbfeffffafffffbffffbfffffbeebffbfffffffffefffffffbeffffffffbfffffbfffffbfbbffeffeeffffbfffefefbfefffffefffffffaefbffbfffefefbeefffbeffffffefbffeffffffffffbbffbffbebbffffbfffeffbfffffefbfefefbffffeffffeffbffffbfeffefbffffffffffffebfffffffffbfffffeffeffefbfebfffbffbffeebffbffbbffeffbfbfeffffeffffffefffbeffaefefffffffffebfffbfffeffefefbfffffbeeffffffffefbffffbbfffeffffefffffbefeeffffafbbffbffffffffefbfffbefeffefffffaebffbffbfffffbfffffbfeffefffffffffffefbfffffffbfffeebeffaffbfbfffffffeffffffbffffefeffffffffbfffffbefafbfebfffffbfffefbeeffffffbfffffffffbfffffeefefbfeffeffffaffbffffbfffeffbeffffefbfefffbfefffbbfbbebfffbffffbefffffffbfefbffeffbfbfffffffffbebffffefeffbffeffbebfffffffffbfffeffefffffffefbfffffffffeffbebfeffffbefefbafbffffffafffffbfffffffffffffffefffbfefeffbfbefbbfbfefffffffafffffffbfffbfffffbffffbfffefbfffbfbfffbffffbeeffefffbbefbffeefffbffffefbfbeebbfffffeffefbffbffbffbefffffbfbbfffeffffefbefffefefbbffefffeffffefffefaffaffffbfffbefffffeffefefffffbffefffffeffeefffbffbbfbeebeffffffffbefffffffbfbbfffffeebeffffffefbfffffeffffbfefffbfebaeffffefffffffffefbfbffffffffffffbffeebbfffebfffbffeffffbffbfffbffffbffffffefffffbffffbfffaefefffefffbffbbefffffffbebfffeffbfffebffbfffeffbffeefbefeffbffeffbfffebffffffeffefbfeffffeffffbfffbfbefffefefffeffffffffefffbffffefffbfeffffbfbffffffaffeffeeffffffffffbfffeffebffffffbffeffffffffafffffbffbfffffeffbfbbffffffefbffeffaffbeffffefffffeffffbeefbffaffffffeffffbffffffebffffefbffeffefffffefbefffffbffffffffffffffbfbffbfebeffefbfffbffeefeefffffefffbffffefefffebfebffffffeffeebfefffbfffffbaffbffffbfefeffbfbbebffffffffbffffffffbbefffbfeffffeeffffff := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask263877 : MertensSieve.bits 263877 = 0xffbefffbfeffffafbffffeffebffffffbffbfbfffbeffffbffbefeefeffeffffbbffffbfffafffefffffefbffffbfeffffffffefbffaffffbfffbefffffebfffeefffffffefffebfefbffbfbffbffffeffffefffeffffffbbefbfffeffffffffffeffaeffefeffeffbffefbffffffeefefbfffffffebfffeffeffffbffbfefffbfffbefeffbffffffefbefefffefbfbfefffbfffffffffbfffefeffefffffafbffffffaffeffeffffbfefeffeffbffbfbefffffbffbfffefefbbefffbfebbfbffbfffefffefffffffaffbfbefffefffbffffffbfbffffffbefefbffbbfbffbfffaffffffebfefbefeffffbfffffbbefffbfebfefffffefffffebffbffffefaffffffefffbeffffffefbfbfffbfffffefbbfbffffffbffffffffffffffbfbbfffeffefeffffbbeffeffffbffffbffbfeffffbeffffeffffbeffeffffbbffbfbefffffffffeffeffffeffaffbeffffeebbeffffffbfefefbfeffffffffefffffefbffefbfebfefeffefbaffbfffffeffbffeffffffeffffefbefffebfefbfffffaefffbeefffffffeffbefeeffefffbffffeffffaffffbaebffffefaefbffaffbffeefeffffffefffffffeffffbefffffefbfffffffeffffffbfefaffaffbefefbffffffbffffbffffffffbffffffffffffffbffffffffffefbfbffbbffefffeffffffbbfbfeffffbfffeffffeffbfffffffbffffefbffefbffffffeffbfffffffffebfffeffefffefbebefbfefffbefffffeeffffbfbefbfeffffbffeffaffbebeffffffffafbbeffebbefefffebfefefbeffeffefbfeffffaefbffeeffebfeffffbffbebffbeffaffafffeffffeffefffffeffbebffffefbffbfffffeebfefffbbefbffffbfffffbbebfffffffefffffffffffeffeffffeffffbeffbefbffeefbffefbeffeffafbfffffbbfffffafffeffffeefffffffbfbfffffffffbfbfeffebaefbfbfffbefefffffffbbffbffffffffeffffffefffffffaffaffffffebffffffefbfeffffeffeffbebfffeffffffffeebfeffefefffffbfffefffffffffbeffffbefffefeffefbffbeefafffffbebbfffebbffefbfffbfffffeeffffffffefffffffbfbfebfefffbeffbffbefbffffbefffffeffbfbfeffefafbfffffffffffffffffffebefbffffffbfbbefffbaffffffebfffeffbffbffbfbfffffbbefffbbfffeffffffffffaeffffeffffffffeebfeffebeffbfffffbffefffffefbefbfeffefbefffffebffbfffffffffefffefffbbefbffefffebfeffffbffbffffbeefeffbfffffffbfebfffbfffebbfbfefbefefbbfbfffffffefffffffffbfffbefbffbfffebfffeeffffbefffffebfffffffffbfffffbffffbeffffffffbffbffffbffbeefbffbfbffffeffefbffefbfffffffffeffbfffffffbfebffffffaefbffeffeffbfbffbffbefffffafffefbfffffbfffffeebfefefbfffaffbfffef := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask272069 : MertensSieve.bits 272069 = 0xfeefbffefbbffbfbffbbffffffffffbfefeffffbaffffffefefffffefbfffeefeffbffeffbfffefefffffbefffffffbffffbeffbfffffbefffffffffbffbeffbffffbffffebfffeffbffffbfefeeffffbefbffeffbefbffeebfeffffbffbffffffebffffffbfbffbfefefbfeffffffffffefffefeffefbfffffffffefffffffffffeffbfbfffbfbefffffffbefbbebfeffffffffeffffffbfffefbfffbeffffeffffffffbffffffefafbffbfebffbfffefbfffbfbeebeffffffffbffeffafffffefffeffebfffbffffbffbffbbefaffffbfeffffaefefbfffffffffaefaffbffffbffffefffffeffffefbfffffbfefbfffefeffffffffffbfefefffffeefbfbfebfffbffeffffffebbffffbbfbfffffbfffbfbffbfeffeffeffffbefffffffeffffffffffbfffbefafbfffffbffbfffefffeffffeebffffffefbbefffffffffbffbbfffffbefffbaffffffffaeffffaffbfffebfffbfffefffbeffbffffffffffffebeffbffffffffeffbfffffffbffffefeeffffbeffebffbfffbfbeefffffffbefefbeffffffffffffffaffbffeffbffbffffffefffbbfffffefffefeeffffeffaffbeffffbffefffffbfbefbaeffffffffebffbbfffffbfffefffbfffffffebfffffffefefbfffffbeebefffffeeffffffbfefffbbffbffffbeffefbbffffffffeffefffebffbffbbefffbbfffffefffeffffefbbfbfeffffeffffbbefefffffbffefffffefffffbfbbffffffebaeffffbfbbfbffbeffefbffffebfefaefbffefffeffffffffffeffbffefffffffbfefbfffffeffeffbfbffbffffefeffefbfeffffbfffffbebfebefffffefbffbfeffffbffaffffffebeebfffffbbffffbeeffffbffeffffbfffaffeffbffffffefbffbfffffbffffbeffffbfffbebefbfffaffffffffffbbfffffbefbfbffbfffffbfeffffeffeefbfbffbffffeffffeffffbbefefbbefaffefbfffffbbeffffffbffbfffbffaffeefffbffbeffffffffbfffeffffbfbbfffffffffffeffeffffffeffffbffeebfeffffbffffbfffffffffeefefffefffffffeffffbefbffbfffbefffbfeffebffbfefbfbfffbfbfffaefffbfeffeffefeffffffefffbffbfeffffbfbbfffffaffeffbeffebfffefffffefffffffbeffffbeffbffeffffffffbffbfbfeffeffffffffffeffaffeffeeffefffffffeffffbfffffbeefffbffffffefffefffffeffffffffffffffffbfbfeffffffbfebffffefaffafffeffffefffffffffefbefffffefeffffbbffefbfffffbfefbebffbbffeffffffebfefaffbffbfffffefbfefbfbfffbfbfffbfffffffffffeebffffffefbfebffffeffffafffffeffbfffffbfbffffffeffffbffffefffbbffeffaeffffffbffffffefffffeeffffffbefbbfbfffaffeffbebbefeeffeffffbffbfffebbefeffffbbfffffaffafbbfbffffffeffbffffffffeffffff := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask280261 : MertensSieve.bits 280261 = 0xffffefbffeffbffefbffffebfefffffffeefbffeffbfffffeffbefffbfffefbbfbfebfffffffffeffffffeffffeffefffefeeffffffbfffbffffffefffffffffbeffeffffffffbffefbbefaffffffefeffeffefbffffffffbfffbffffffeffefeffafffffffffeffffbffeffffbffffefeffeffffffffaffbfffffffffeffeffffffffffefbbffffffffbefefbefffffefbfebfeffefbffaefffbffffffbffbefbfbfefeeffffeffbfbefbffffffaffbffffffffffbbffbefefffffffffffbffffffffffffefffbffffffbfffeffeffeffefbfbfebfffeffeffbfbeffbffefffffbfffefffbeeffffaffffffffefbafffffbefffbefbbefeffaeffffffbeffbffeeffeffebfffffffefffffffeffefffffffffefbffffffffffbffffffbfbfffffffeffffffbffffffeffaffefbfffffbfefeefffbafffffeeffeffffffffffffffffbffffffebffbbfffffffffefefbbefeffffbfeffebfefffffefbeffffaffafffebffbffffffeffaefffbeffeeffffefffffeefbefbfffeffeffffffffffeffffffffbfffffefffeffebafffffffbfffffbefffffbfbffbfffeffbffbfffebeffeffbffbfbffffeffffbfbfffbfffeffffeffefffffffbfeffffafffefffffeffffbebffbefbbffffbeffffbfebaefafbfffbeffefefffffafbfffeffbffffffebbffeffeffbffbffbeffebfffefbeffbffffbfffefbfefbffffbfefeffefffefffffffbfffefffffebeffffbeebbfffffeffbfffeffebeeffffaffefbfffeffbfffffafbfeffffbffffbfffffbfffeefeffeffffffeffffffffeffebffffefbffeefbfbefffffafbffffeffffefffffeffbfffefffffffafbffffebeffffbbebfffeffefffffbfbfeffebfffffbfffbffffffffbfbeffffffeffffffffffffffffbffeffeffbfffffffffffffbbffeffaffffbbffffbeffeefbffaefffbffffffbfffffbfffebeffbffeefffbfffffffffeebbfffefeffeffffbbffefbfffeffefffffeebffffffffffffefbbefbfbafbfeffffffffffeffffbfeffefbfbbfffffffffffffffefbeffffefffffbffbffeebfffafbeffffffeffffffffebbfbffbeffffffeffebfefefffffffffffffbfefffbfffbfffffaefaffffbffbeffffffffbfbfefeeffffbffbffbffefbaffffffefbffffbfefeffaeffffffbbefbfbeffbefffbfeffffaffffffffbffefbfebbefffbaffeffffffebfffbefaffbfbbfffefffffffffffffffffffafbbffffffffeffffbeefffbffbeeffffefbffbefffffafbfefbffffbfffafffffbfbefffffbffeffffffffeffefbfeffffeffbfffffeffffbffbbefeffbefbefeeffefffbbfbffbfffbeffffefbfffffffffaffbfbffffeffefbfbafffefeffffffffbffbffefbbefafbffffeffebeefffffefbfbffbfffffbffbfffffffffaffffffffefffffbffaffbeffffbeffffeffff := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask288453 : MertensSieve.bits 288453 = 0xffffbffffffffbbebfffaefbfffffffbfebbffeffaefffffffeeffffffffffffffefefbfefbfffffffffffbffbfbeeffffafbefffefeffeffffbfffffbffffefeffeffffbfffbffbfffffbefffbfefbfffeffffeffeffafbeffffffefafffffaebfefefbbefbffbfffffffbfefeffbfbfffffbfffffbbefffffffbffffffffffffffeffbffffbbffeffefffffeefffffffffffffbfffebeeffefbfffffbfffffbefffffefffbefffffbfbefbffbffbfeffffbfffebffbfffffffefffffefbffbffffffebefffffeffaeffffffbfefaffbfffffeebfffffbbfbfffefbfffeffbffffffefeffefbbefbefeffeefbffffbffffffbffffffefffbfebeffeffffffffffffffffbffbffffefbffeffbffffbffbefffffbfbffffffbefbfbffffffefbeeffffaebfffeeffefeffffbbefffbbffbffbfffebfebfefeffffbbfffffbffffffffbfbeffbffefbfeffebfefbfffffefffeffffffffffbefffffffafffffffbbfffffbffbfffefbfffeffffefbefffeffffeeffffbfbffbeffeefffbbfffffffffffffbffffffffbfffffbfefbfbeffeffbfffefffbfffffffffefbffbfeffffbfffffffffefaeffffffffefefbefffffaefffffebfffefbfffbfbefbeffbfffffffffffeffffffefffbeeffffffffeffeffefffffffbffbfffefeeffffbffbefefffeffffbeffffffbfefafbfefffbefbefffffffbbfffffefffffeeffeffefeffbffefffffeefbefaffbfffefffbfffffffeffefffbbffbfbfffffbfefeffffbfffbfffefeffbfbfffffffffafffffeffbefefffffffffebfebfeffeffffeffbefffffefffbbfbfffffffffffbffffebffbfefeffeeffffeeffeffffffbffbffffffbfbfffbeffffeffaffefffeffebffffffbfffffffffffefbbffbfbfffeffefbffbfefffffefffbaffffbfffffffffeebbfbfeffefbfffffffbefbfffbffeeffffffffefeffbfbfffeebfffffbffffffefbaffeffeffffffffaefffffefbfbefbfffbfbbffffffffbfffffeffffbfefefffffaffbeffffbffbfffffbefffffeffffffbbefffffefafbafffffffbaefbffeeffffffffeffffbebbfffeffefefffebfffffbaffeffbffffbeffbffeffbfbbffffbfeffffffffffffffffefbfefffbfefeffefbffffeffffeeffffbefbfffffbfffffeffbebefbaffbffbffbffefbfefbffefffffffffefeffffbffbefbaefffffffffffeffffbfbbfffefefbeefffffffffffeffefffbefffffffbbffeffeefffbfffbfffffffbffffeffefefbfefffbfffbeffffefffeffefeffefbfffffbfeffefbfbfeffffeefaffffffeffffeefeffaffffbfebfebfffafbbfffffffbbffeffbebfebfffeefaffbeffffffbfffafffefbffffffefffffebffbeffbefffbffffffefbfffbfffebfffffffefefbbfffefeebfffffffffffffffbefbffbfbffbfebffffffbeffefffbeff := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask296645 : MertensSieve.bits 296645 = 0xfbfffefbfffefeffbfbefbffbfefbffefffffbfffffbffbfbffbffffeffeffffffffebeffeefffbefbfeffefeeffffaffffbeeffefbfffebfffeffbefeffffbffffffafffffbffffbefffffffbefbfffefffffefbfebfffffbffffffbfbfeffebbffeffbeffefeeffefffbfffffbffffefbffeffbfffeffffbffbffffbffbfefffbffffefffbfffeffffbbffeffbffafbbffffffebbfffffaeffffefbeffbfffebbfbfefffffffeebfffeefbfffffffbfeffeffffeffafbbeffffeefffbfefbfbefbbffbffefffffffffefffffffbffffffefbfbbffffbffffefafffeffffeeffffeffbebbfbfefbefaffbfffefffbeffefbffbfffefffefbfbeebffffffeffbffbffbfbffbfffffbffbffffffeffffbfffbfffeffffeffeefbebefbbffbffffffffefbfffffbfffffbfffbffeffefbffbffffffffffffffffeffeffffaffbfbeffeffffffffbefefffffafffebbfffffbffffbffbfffffffffffffeffffffffffeffaebffbffffffefbfefbffefbeeffffeffbfffffaffbfffeffffeefffffffbebbffffffffbfbffffefeeffefefbfffbfbfffeffbfbafffffffffffbffffffefeebfffbfbbffbfffefbffefbffffeffffaffefffebffbfffbffffffffbffffbaeffffbfbffffffaeffffbeffefffbbffffffffffbefffefbffbffbffefffeffffeefbefefffffaffffffffeeffefeffefbffffffaffeffbffbfbfffeefefbbeffebffffffbfbfefbeffebfffbfbffffffeefaffeffefffffffffffbffaebfeffffbfffffbfbbffefffefffffffbffffbbffbfbafffebffffefffffffbfbeefeffffffebbfffffbffaffeffffbfeffffefffefffffffbffffbeffbffeffbefeffffbfefefffffefbffbfeffffeefffbffffffffbffffffefbffffefbffbfbffbfebfffaffbfffefffffffbefffbfffffffebffffffbffbefeffefffffaebfffffbffffffafffefeeffffbfbafffffeeffefbfffffbeffffefffffbfffffefffefbffbfbfffffbfefffffefbfbffbfffffbbefffffebfefbffbeffffffffffffbefffffffffeffffffffefefbefffffafffebffffeffffafffffeffbffefffebbebffbfffbffffbfefffbeffefbbffffbffffffffffefffffffbeffffffbfffffbfffaffbfffffeeffffefbbffbffffbbffffbffffefffbfefffbfebfefffbfffaffaefffffffffffffbefbfffffbffefbffbfefefffffaffffbbffefffffbffffbbffeefeffffffeffefefffffaffeefffbffffefffffffbfbffbfffbfbfffffbfffeffefbeefbeffefefffffffffffeffbffefbfffbeffebfeffffbfffeffffbefbffefbffbfffffffffeffffffeffffffbefbbffeffffffffffbffffefeffbfffeffffefffefffbbffbeffeffffffbbfffffffbaffaffffffeffefeffaffffffffffffffffbfebbfbfffeefffffebbffeefeffaffbeffffefbbffefbffbf := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask304837 : MertensSieve.bits 304837 = 0xffffefbffeffbfbbfffffaefafffffffbffbfffffbefffebfffffffffbffffbefffefffbeffbfffefafffffaefffffffbffffbafffeffefaffffbfebfffffbfefefffffffffeffffbfffffbffefbeefffbffbfffeefbffbfffebffffefaffefffebfefeeffefafbaffffffffefffffffffefffbeffefbfebfffffbbffafbfffbfffffeffffbefbffffffffffffefffeffebfffffffffbefffbbffbfffffffffebbefffffebfffffbaeffffbeffffffffffefbfffffffebeefbffaeffffffffffffffeffffefbffffffbffbffefffffbffbffbeffefbffffbbebffbfffffffffeffffffffbefefbeeffffefffefffbffbffbfffffffffffffefefbeffeffeffbfffeffffeffffbbfffffeffefbfffbefffffffafbbfffeffefeffbfffffbefeebeffbffeefffffffbffffbfffbffffffffbffefbbfbefbffffffffbbeffefeffffbbffbfbeffbfffffeffffbfffaefffffeffffefffffbfbfefffffffbefafbffffffffbeffefffffffffebfefbffffbbefffffffefbfffbebffffffeffefffffffffefafffffffbffffeffffeebffffffbffbffefffebfefffffffefbfffefbffffffefbbffffffefefbfffffbfffbefbffbfffebfffaffffbfeffebfefeeffffeefffffffbffbffffbbfbfffffffffeebfffeeffefaffbfbfeffffbffffffeffffefbfeffffefbfeffebfffbfbbffffbffffefbffbebbfbfefffffffffbffbeebbfffffbffbffffffefafffffbffeefeffffffeffefffffffffbfeffeffffeffffbffffebfffefffffeffbffeeffffbffeffbebfebeffafffffbffffbfefffbffbffffffbfffffbfffffefbbefafbfebffffffbffefffffffbeffffffffffffffeefeefeffeffbefeffefffffffbfefffbfefffbfffffffefffffffbffffbfffbffbfffebffbfffbffbfbeffffffffffffffbfffffefffffbfffebbfffeffffbffbebbfffeffffefbeffffffffbefefbffbffffffeffbffffbffffffbffeffafffefffbefffffaffffffffeffefbeefbebeffbfffffffffeffebfffafbfffbfffefeffffbfebffbffbfffffffebffbfeffffbffffffffeebefffffbefffbeffbefbffeefbfffebeffeffffffeffffbffeffbffbffffbaffeffffffefeffbffffffffffffebfefffbffffefeeffefbfbffbffbeffbeffffefbfebffbfffeffeffbfbfebfffaffffffefffffffffbbefbfbffffffefffebffffebfefeffbeffefffffffbfbfffffffefeffefbffbffbffffffbfffffbffefbfeffffffffffefbeefeffbfffeffffbffffbffbfebfefafffffafffffffffffffbfffffbeffeffbfbeeffeffffbffbfffeffefffffefefbafbffffefeffffbbebbefffffefefbfebffbfefffffffefffefffbfffffbefbffbfefffffffffffffffbbffbffbebfefefffffefffffbffeefaeffffffffebfffeffefbeeffffffbaefffbbffbfffebff := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask313029 : MertensSieve.bits 313029 = 0xffffbbefbfffefbffffbfffffffeffffbffeeffffefbfefbffeffbffffffffffffeffebffbbffbffbfffffffbeffbfbbeffefffffffbfffffbfbfffeffffffefffbefbfffeffaffbffffbfffaffffbffffffafffffbeffefefffffffbefbffffeffffbffefffeffebfefffffffffbfeffefffbfebfffeebffffffaffffbeefffffffbfffffeefafffffbefbeffffaffffbeeffebffbfffafffeffefefbffffffefbbfbfffeefffbfffffffeffffaffafbfffffffffffbeffbffeebffffffbfbbebeffffffffbfffffffbeffaffeffbffffbefffffbfbffbfefbefefffeffebefbfffbffbfbbffffffefbfbbffbefefffffeffbffffbffffefffbffbfeffffbffeffbffbffeebfeffffeefffffefeefeffefbbfffffefffffbffffffefffffffafbbfffefaffffbffffefeffbefafffeffefffffffafbefffffeffeffbfbafbfffeffeffeffffffeffefeffeffaffffffffbffffbffffffefbfefffbffbffbffbbfffffeffffffebfefffbbeffebfebeffbffbffbffeeffffafbffbfebeffefffffeffbffffbbfffffefffffffffffffbfffbefffbbffafbaffffffffaffffbfffbffffffeffffbfbbffffffefefbeebffffffaffaffefbfefefffffbfbffbffffffeefeffbebbfffffbeffffbffffffffbffafbfffffbefffefbffbfbffbffffffbfbfebfffefbaffffffffffbfebbefffffffbfffeffefeffbfbffbffffffffbfffffffebfefbfbfffbfffefeffbfbffbffffffeefbffeffffbffbbffbffbfffebefbffffffafffefeffbefeffbeffffffffefffbafbfeffffaffeffeeffefffffffffbefbbffffffffbfffffbebefffffafffefffbfefbffffbffbfffeffbffffbbfffeffffeefbffffbffbfffaffffbbeffefeeffefffffefffbefffffeffeffbffefbfffbffeebffffffbfffffeffbeffeffefffffffbfbeffafffffefbffffeffffbfbfffffbffffffbfbbffffffffaefbffefbffffffbffbffeefffbeeffffeffbfbbfffebeefffffeffefffbeffaffefffeffebfffeffeeffeffeffffffffefffffffeffeffefbbfffffbfffffbeffebffffffffffffbfffefbefffbfffbfbffbfefffffebffffefbfffffeeffffefbfefffbfffffbffffffbfffffbffefbffffffafbfefffbfffffbbfbbffeffffffffffbfefffbbffffbafbfeffeffffefbfffbffefffefbfffffbffeffeffffbfffbebfffffffffafbffbfefffffffbfffffffbaefffbbefbfbefffffefffeffebffffefeffeefbffffffefffbbffffffffeffffbeebbebfefeffefffebfeffeffefefbbfffffeeffffefffffffffffbefffbffffebffbeefbffbffffbfefefffffaffffbeffbefefbffbbefeefbfffffeffbffffffefbffffffffffffffeffbffbefefffffbfbfebfefffbeefefffefbfffefefffffbfbbffffffffffbfebbffeebfffefffffbeffffffffffefb := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask321221 : MertensSieve.bits 321221 = 0xffefefbfffffffffbffeffeefeffaeffeffebfefffbfefffffebeffbffeffbfffffbffffbffbfeffefafffffbeffffffbfffeffffffeffffefffffffbfebfffeefbfbfffffffebfefefffefffffebeefffffefffffffeffefffffbffffbfffbffaeffebffffffaffbffffffffbfffffbebffffffeffffffffffbfefeffbffefffebefffefffbfebbfffffbffbfbefbffffefbffffffeffffffffefbfffffffffebeffefbfeffffffbaffbfbefffffffbfffffbbffbffeffeffffbeffffffefeffafffebffbfebbffeffaffffbffffeffffafffefffbfffefffefbefffbfffeffbffffbfffaffbffaefffffeffefbffbebffbeefbffffbfeffebfebefffffffffffffbbefbffafbbfffeffefffbffbbffffffffafbfefffbfffbffffffefbfffffffffffbfbffbffffffffbefbbebeffbfffffffbbebfffbffffbffffefeebbfffffffbffffffffffffbefffffffeefffffffbefefbeffffbafffffefffefaffeeffefffbaffeffaffffffffbeffffbffbfffefeeffffffffffffffffefffebffffffbffeffffffffffffefbfffffffbfffbffeffffbffbeebafffffbeffebffbbffffbeffffffffbfffffbefbffffffefbfbbfffeffffeffafbefffeffeffffffffefbfffffaefefffebbfffefbffeffeebfefefbfffffbffbbffffbfeffffffbffffffaeffffeeffffffbfefffbbefbfbfffeffbfffffffbffffffefbfefffbfebefffffffbffffeffffaffafffeffebeffffbfeffffefffffffffeffebfffbffbfbfffbebfefeefbfbafffffeefeffbffffffefeeffffafffffbfbffffffaffbfbfefeffbefffbfeffffffbfefefffeffefffbeeffffafffffeebffffffeffffffefbefffbefbfffeeffffaffafbbfbfffbefbffffffeffffeffeffbfffebeffffffffffbffbfffbefaffbffffbfffeffbfbffbffbeffeefefffefbffefffffbffffbfffffbffffffefbfffefbbffffbbffffbfffffffffeffffbfffaefefffffbfbfffffffffefbbfbfffffffffffbbeffffbfffffafbfebffbfffeffeffffffebfffffffebbfffffafffffbefffffffaefaffbfffebeffffffffffffffefffffafbfeffffffbeffffffffffffeffefbfbffffefefbbefffffeffffffbfffefbaffffffefbffbffbfffebfffeffbffefbffbfeffffffffffbfffffaffaffeffbffffbfffefffffffffeffffefffebbffefbfffafbfebffbfeffefffbbeffefffffffffbbfffffeeffefefbefffffffffffaffbffbfbfffffffffffbfeffebbefefffeffffefffffafffffffbffffffaffeefffbefbfefbffafffffeefeffbfbffffeffebffffffffbfeffefffffffffbbffeefaeffffbffffbffffefbfbfeffeffebffffffbfffefffbfffbffafbfffefffefafffefbffffffffefffffffffebfffefbfffbffeffbefffbffbbfbfffeffafbbebfeffeffffffffffbfbffbe := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask329413 : MertensSieve.bits 329413 = 0xfffffbfffffffffaefeffefbffffebffffffeeffffffbfffbffeffffffebeffefbbffbffeffeffbfbafffefffffffffbaeffeffeffffffffefffffffefffffefbfeffeffffeffbfbfefefffefefbefffefffffffeffffbfebffbfffbfbeffffffebbffffbbeffffeebeefffffffbfffffbffefbffbbffeefbffbfffefffbefbfefbfbffbfffeebeffffbbfbffffffbfffffeffffbfffbefffffeffefeffffffffeffbffffffffffbfebbfbffbaffbffbfffeffffbefbfbffffefeefafffffbffffbfffeffafffffffbfffffffffeeffefffffeffffeefffbffffefffbfeffefeebffffffffbfffffbbffeffbfffffeefeffefbfeffefefffffeffffbffbffbfeffffbffbfbffbffffffeefffbeeffffeffefbffffffaffffffffbeffffbfffffbfffefeffeffeffffffefefbfffffffebfeffeffffbfbeefbfffefeeffffefbbffeefeffefffebbffeffbfffffffbfffffffefaffefffeffffbfffffffffffefbbefbffbebfffffbeeffffbeffefffbeffbfbeffffbfffbfffffffffeffebeffffffebbffefbfffffffffbfffebaffffbfefbfbfffbffefffebffbffffefeffffffefffbfffbfffffffbfefbefbffefffffefbffffffbefffffeffefefbffbfefffffefefffefffbfffeffefbffbfffffffffbffeffffffffeffffbfebbfbfeffeffffefffebeffeffbffbefbffffbfffbfbfffffffefeffffbfffffbefffefffbeebffbffffefaffbefbfbffffefffbfffbfffefeefbfbfffffbffbbffafffeffffefbfffeffeffbfffffefffffbfbfffffbaeffffffbffffefeffafbbfffffeebffffffffbbffeffeffffbfffbefefffffbffeffffffffbffbffbffbfffefbffeffffbffbffbffffffffffeffffbefbffffffffeebefffffffffffeeffffeffeebbefffbefffffefbffbeffffffffffffffffffefefbfffbffeffbffbffffffebffbaffbfbbfffebffbffffffeefffbfffeffefffefffbffffffaffafffffefbfefffbefffeffebfefefbffbffffffafffffbfffeffffeefefffefffbffffffbffeebffffffbffbffffffffeefbffeffafffffeebbefffbbfbfeffefffffffffbbfffffbfffffbfbffffebfffeffaefffbffbeffffbeffffbfefeffbffeefbfffffbffbffbefbefffbffffffbfffeffffbffffbffbbffefffefffbfffffffffbfffffeffbfbffbfeffffaefffbfffaffffffebbffffbfffeffffbfebfffbefefbbfffefeffaffffbffbbffffbfffefbefffffffffffefffffffffefffffffbebbffeeffffefbfffffbffbfffafffebffffebfffbfffffbefeebfefffbbfffffffbfffeffbebffffffbefffffffbefefbeeffffaffffbefffefeffefbbeffffffffffbfbfffefbbffffffffffffffaffeffbeffefffffffefbefbfffffbbefbfbeffffbfebfefffbefbbffffffefbfffefffbfffbffefffebfffffffffbffbf := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask337605 : MertensSieve.bits 337605 = 0xfbfffeeffefeffbebbffffbeffeffbefffbffbbefffffffbebfffeefbffffbbffefffefbfffffbfbeffaffbffffbfffeffffffffbfffffffffffeffffbbffffffffbfbbffffffebeffffffeffefffffffffbbefffffeffffefffffbffffbefffffafbfefffbfffefbafffeffffeefefffefbffeffbefffbffffebffbeefbfffffffbeefffffffbfffffeffaffbfffefffbfefeffbffbffbffffbfffffbffffffffffefffbbfffffefffffefbefffffffffffbfbfefbffffbeffffffebfffeefbefafbefbfefeebfffeffeebbefeffffffffefbffffffbffffffefffbfffeeffffeffffffffbffbfbbeffffeffeefbffffffffffffffafbeeffebffbfffaffffffffffbfffefffffbffffbeffeffbfbbfffffeffafbbfffebffbbffaffeffffffefefffffffffffeffbffbfffebfebeffffffffeefbffeebbffefffffbefeffbeffffbffffbefffefefbfeffefffbfffffffffbefeffeffbffeffffbffffffeffffbffffeffffefffffffbfeffffafbfffbefeffeffffbbfbffffffeefffffeffffffffefbffbefffbefbfffffffffbfbefffffefffefbffffbefffffefffeffebfffaffffffefefffffeffbebffbffbaeffffbffffbfffafffffefffebefffffbfbefbbfbffffffffbffbfffffbefffffeebfebfebfeffffffffffeffbffffbbebbffffbfffbfffffffbfffbffbffbffbefeffffffffeebffffefbffeffffffefffbefffffbffbeffefbefffbeffbfffeffefffbffffefffbeffbffefffebffbbffffbfffffffffffffffeffbfbeffaffbfbfefbefeeffffffffefbfbfffbffbffbfbffffffeffffbffffffffbbffffbafffefffbfeffffbffffbffffeffffaebbfbeefbefeffeffffbfefffffffbfbfefeebfeffffeffffffffbffefffefbfffffeefefbfefffbfffeffbfbaefffbfffefffffbffffffffeefffffebbfffeffffeffeefbeffefffffffafffefffffefffbfffbefffffeffffffbfeffffbffefffffffffebeefbfbfffffbeffaefeffefbbffffbfffbfffffffbfffbffffffffbffffbfffffbffffebffbeefbffbffffffefeffafffffbffffbffffffbebffbeeffefbffeeffeffefbfffffeffffbffbfeffffffbfffffbfffffffeffffefffffefffefffffffeffbfbfffbfffeffffffbeffbfbfffbffbfffffbffeffeffbffaffbefffbbffbffffbbfffeffffffbfffffbeffffffffbfffffffbfffefffeffffffbfefbffbffffffffbffbffeeffefefbfffbffeffbffffbbffeffbfffffffffffeffffffebefbbffffbffbfffffffeffffeeffeffeffffbfbfebbfffefbffefffffbebfffaffeffeefbfbfebbffbffefbfffefbbefffbffbbebeffeeffffbffffffffffffffffffffefbfeffffbfffffeeffefefffffffbffbaffbfffebbebefffeffffefffffeffefffffbfbfeffffefffffefbfeffefeffbffbefbfffeb := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask345797 : MertensSieve.bits 345797 = 0xffffffbfffffbfefeefbffefbffbfebfffffffefffbefbfefffbeffbffffbfeffffffbffbffbeeffffeeffeffebeffbfbffffffffbfeffffffbbfffffeffefffebffbeffbffeffffbfeffefffffffbfffefeefeefffffefffffffbfffffeffffffffafffffbeffeffebfefffbeffffbfffeffeffeefbfffffeffbffffbfffefffffaffbfbffffebfffffbfffbffeffeefbffaeffffffffffbffeeffebffffffbffffbffffffefffffeefffbffbeffeffbffffffefbffffbffbfffeefaffffbbfffeffffaffafbbfffeffebeefefffefbfffefeffffffebbfffeffefeffefffefeffefffffffffffeffbffaffefffefeeffefefbffffefffbfffbffffbffbffffffaffbeffffffbfffffbbfbbfffeffffbfbeffffbeffbffafffebbffffbfffbfffffbefeffbffffffffffbffbfffffbffbffffeffefffbeffffbfeffeffffeffbffeffeefbfbffffebffbafffffffbfefeebfffeffaffffffefbefffffffffbffffefbfffeffefffffeffffafffebefbeefbfbffbffffefaffbfbfffbeffffffffffbfbbeffeffffbfbfffffffefbffefbffbbffffbeefaffbfbffbffffefffbeffffffefeefffffefbfffffaffeffffffeffffbffffffffffbefbbefafbffbffffffeeffffffbbffffffffffffeffefffffefeffeffffbefffffbffbffffbffffeffffffbbffeebfffffffffffbeeffffffbffffefffbbffeffbebbfbefbbfffffffbffffefeefaffbeffefefbffffffbefffffeffefeffefffffffbbfffffeffffffffbffeffbffbffefffffeffbffbfbeffbefbfffffffffffbffafbaffbebeeffefffbefbfffeffbffbfffffffffffefffffffbbfbffbbefbffffffffeffeffeffbeffebffffffbfbbfffffffbfffafffffffffeffefffbafbffffefbfffffffbffbefbfffbfffffffbfefbeffffbfbffffefffffffffbfeffffbefeffefffffffbbffbfbbefbffffbfffffffffbfffffaefbfbeebfebffbeffefffffbffefffffffbfffbffffbfffeffbefbebfffeefeffffbfeffffbffeffffffffffffefffbefffffeffbffbffefbfefeebaffeffafbfffeefffffffbfbbffefffffeffffffefeffefffffbebffbffbfffaffeffbffffffffbffffbffffefeffeffffbbfbfffafffffbefffbeeffffefffffffffffbeffffffbfeffffffffffbfffeffeffeffffaffbffffffefbffbefbfffefeefffbeefbeffffaffafffffffbffffffafbafbfefefffffffbfffffffffaffffbbefffffffbffbffeefbfffeffffbffffffffefffffffbffbffbfffeffbffbffffffebfefaffbffbffffbeffeffffffebefbbffeffffffefffffffefffefbebeefeeffffaebfffeefeffeffefbfeffefbfffffefffebffffffffbeffbefffbfffefffffbebefffefbffefbffbffffffbfbbfffffefffeffffbfffffefffefffbfffbfffebeffefffefffffffbefbfbf := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask353989 : MertensSieve.bits 353989 = 0xefffefffbbefffffffbfbeffeffeffbebfffffbfffffbfefffbefbeffffbfffbfbfefafffffeebffffffbffffffffbfbeebfffefbfffbffffbbffffffffbfbfffbffafbeffffffffffffffefffeffefeffbfbffbbfbfffeffefbffbbefeffeffaffffffffeffbefaffeffbefeffffffffbfbffffffeefffbaebffffffbfffffbfffffffffffbfffebffffeffffffffeffffeffaffeffaefffbeebfffffffffbefffffffefbfebfffffbaefffbffffebfeffffefffffffffffffffffffffffeeffeffffffbfffeefffffffffbfefffffffaffeffffffffeeffffbfffefffbfffbffffffffffffefffbeffbffeebfefbffefffffeefbfffffeefbeffebbfffffffffffffffffaffffbfffeeffefffbfffbffffbeffffffffffffeffffbffeffffffeffffbffefffffffffffffbfffbefefbfffbffbeffefffffffffbefffefeffefffffbffbeffffaffeffbffffffefeffffbaffffffefefffffaffbfffeffeffffeeffffffbbffbffafbffbffbbffffbffbffffebffffffffbbffefbbefeffffbfefffffffefbffffefffbfefffbbefbfbefffffbffffbffffebafffffaffbebffbfffeffffbfffeffbffefffefbffefbbffbfbefbfeffebffffffefffffefbeefbfffebffffffeffbfffffffbffbbffbffbffbeffebfeffffffffffefffffeffffbbffeffeefaffaefffffffbffefbbeffeffffefffffaeffffffffffefbfffffbeeffffbffffbfffffffefefbeffbffffffffffffefffffffbfffffbffffbfefbefefffefbebffbffffffaefbfffffbffefbefbbebeefffffffbebfffefbbffafbbfbfffffffefefbffffffeffffffffefbfefffffffeffeffffbeebffffffbfffffeffaffbfbffffebfeffffbffaffffbfefffffffbfbffffebbffffbbeffffffbfffbfffffffbfefeefeffbffbffeebfffffffefbfffefffffffffbfebfffbfffffffffeffeffefbffffffefefffffffbfffbfffffefffffffbffbffbaffefffefffffefefffffbffbffeefaffffffffffbffbffffffffbfffefbfffbffbffbfffffaffffbfffffbffffefffffebffffffaefefbfeffefefffefffffffffbfffbffffffffffffebfffbffaeffffeeffffbfffffbffefbefffffbfbffbfffbefffbfefffffffaeffffeffffbfeffffbfbfefffffeffffbfffebffbfefeffeffaefbebfffbffffbefffefffbfefffffffffbfffaffffbbfbfefffbfeffffffffeffffffffffffbfffefffffbfffffffbffbfffaffbefbffeffbefeffafbbfffebfefffbbebfefeffffffffffbffffffaefefffffbfbeefffffffbfbffbfffbffbfbeffbfffffaffeffeffbefffbbfffffbfffffffbeffffffebffbefffffffffffffbfefaffbfbbfffeffffeffbfbeebfffefffefefbeefbefffffffbffaebbffffffffeffffffeffefbffefbbfffefffffefbfffeffffffbaefbfbeffbefff := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask362181 : MertensSieve.bits 362181 = 0xfffffffffffffffffffffffffffefffbefffffeefbfbefffffeffbffbffeffeffffbffbfefffbeefffffeffeffefbefbfbbfffebffbffffffeeffffefffeffffffbfefeebeffffffebfffffffffbffbfbffffefbffffffeffebffbfefffffffffffffefffffeefffbfffffffffffbbfffeffffffffffffbfebffffffffffefefffffbffbfffefeffbffefbfefbffffffffbffefbfeffeffffffbeefffbffffeffffafbbffffffffefbfefbfffffffffffeffbfbffffffbffbfffefefffefffffefffffffaffafbfefffffffbefeffeffffffeffffffffebbffefffffeffeefffbffffffbffbfbfefefbfffbffffbfffefbbfffffffbffbffffffefbbfffffffbbffffffefbfbefffffffbfebbffffffefeffffbfffeefeffeffefbbfbfefbeffffbffbfffefefffffffffffffffefefffffffffeffffefbbffbffeefeffbfbbffffffefeefbffffbffbeffeffbffbffbffeffbffaffefffefeffbefffffeffebffbeffbffbfffefffffffeffeeffffffbffffffefbffffeffeffffffffefeebffffffeeffebfffbffaffbffbeffefeffffbfffffbffbafffffeffffffeffffefffefbebffbeefffbfefbffeffeffffbeffbeffefeffeffbebfeffeffffbffffbbffffffffffffefbefeffaefffbefffffffffffbfffffbfbefffffffffffbfffffeefbffeffffbffbafffffaefffbfeffefffbffffffffbaffefffefbffefbfefeffbffffbffbeefbffbeffefeebefffffbefbfffffbeffffefffffefffffaffbeffeffffbffeffffffefeeffffffbffffffffffffbffaffffffeffefbffbefffbfebfffffffffffbfefbffeffffffebffbfffbffffbbfffebfeffffefbbffeebfffeffbebbeffffeffffbbebfffffffefeffefffffefbfffffbeebfffffffefaffffbfffeffefffffbefffbffbfefeffbffbfffeffffefbfffffbfffeefffbeefffbfffeffffbefffebfeffffbfbbeffffefffffeffffffeffffffffffbebbfbffffeffffbfbbfffeffefffbfffbefffbeffffbffbffffffaefffbfefffbffffffbffbfbbffeffbefbfffefffbefffffeffeeffefeffbffaffffbbfffffeffffbfeffffefbbffbffffffeffebfffffbfffffbeefffffffffbbffffffffeffeffbfbfebefffffefbfeffebfffbffffffefeeffffeffbfffffefbeefbffffbffbffffffbfbeffffbfffffffffbfbffffefeefefbefbfefeefbfffffefbfeffffbfffffafbffffffaeffffbebbebfffbffeffeeffffffffefaffefffffffffefbffbffffbeffeefafffffffbffffffffffffbebffbbeffffafffffffbbefefffebfefffbfffbfbefffffffbbffbfffffffffffeffffffffffbeefaffffbeffbffeffffffffefffffeefffffffbfffeffefefffffffffefffffffffffefffbfefbffaffbffbffeffeefbfbeefbfbefffffefbfebfeffffffffffeeffefeffbffbff := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask370373 : MertensSieve.bits 370373 = 0xfbfbfffeffbffefbfeffffffbbffeffbfffffffbefffffbfffefeffffffffeffffffefbefefffeffebfefbffffffefffbffbbffaffeffbfffffeffefbffbffffffeffffbbfbffbfffeffffbffffffffffffbfffffbffefffffbfbffbbfffefeffeffbfbfeffeffeffffefbfffffbeffffffeffffeffbeffffbeffeffffaefffbeffbefefffffbffefbffbfffffffffffffffefbfffafffefbfbfebffffffefbbfffffbeffffffbffbffffefffbfebfffffbfefefbfffffbffffffbffbfbffffffeffbfffffffffefbffefffebbefffffefaffffffffefbeefffbbfbbefefbfffeffaffffffefeffeffbffbfbffffeffffbebbfffefbffefbeeffffffbfffaffffbfeffffbefafbffffffffffeffffbeffffefffffbffffffffffbfefbfbfffffffffeefbfffffffbfffbffbfffefbffefbffffffafffeffffbffeffbfffeffefaefffbbfbbffffffffbfbffffebfffffffffefffefeffffffffbffbfbeffeefffbfffffffebbffffffefbffffbbffbfbfffbffefffffefbbeffffefbbffaffffffefffbfefafbffffffefbfffbfffebbfbfffefffffffbffffffafffffaebbffefbbffefbfffffffefbefefffffbebeffaefbfbfffffbfefbffeffafffffeebeefffffefffbfeffffefbfefbfbffffffeffaffffbffbfefefbffbfefeffeffeffbeffefffbaefefffeffebffffffffbfffbffffffeffffefbffffffeffffbffffefffbaffffffffffbfefffffffbfbbffeffeeffffbebbfffffffffffbffffbfffbffeffeefffbfeffefffbefbfffeefbffefbfffbebfeffffeffbffbeffefbffbfbeffffffefbfffffffffebffffefffbfffffffffbeffffeefffffffeefffffefffffefeefeffffbfefefffffffffffbefeffffffffefffeffebfffffbbefbffffffffffffefffbfffaefefbbffbfffffeefbfffeffffffffffafffebbfbefbaffbffefbfffffbffffffffbfffeffbffefffffffbffbbfffffbebffffffafffffefffeffffeefbffbffbfbeeffefefbefffffeefbffbffbefffbfebfffeffeffbefefffefefffebbffffffffffffffffbfffbffbffefffefeffeffbfbffffffeefeeffffefbbffefffffffffebffbeeffefafbffffeffffbffffffffffbefbfffeffefbfefffbfffffffffbebfeffefffbfefffbfffeffbffefbfebfebffffffefffffeeffefbfbefbfffffffeffffbfffffffffeffffbffffbffffffefbfffffbefbfefffffffbffeffeffeffffffffeeffffbffbfbfffefbffffffeffffffebbfffffbeffebeffeffbfbbfbfefffffefaffeefbffefffffbffafffffeffaffbfffffffbffbbffaffeffffffebffffffffffffffffffefffffffbffffefbfbbebfffffffefffffeffefeffffffffbffffffffbffffffefbfbeffafffffffbffbeefbeffffffbfefffbfefeffffbfffeffbefbfbffbfebffbaffbffbffbffe := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask378565 : MertensSieve.bits 378565 = 0xffbfffbfbbeffffeeffeffffffbbeffefeffafffffbfffeffffefbefffeffffeffeffffbfffffffefafffebfeffffaffafbfffffbeeffffffbaffffbfffbffeffeefbfbffffffffffeffebeefbffaffafffffeffbfffffffbbebffffeffffefbfffffbfffffbbffbffffbeeffffeffffbfffbefbffefbfffeffbffbffffffebffffffefffffffffffaeffffbfbfefffbfefaffbebffbffffefbffbfffefeffeffbffffffffefffefffbeebffbffffffbffffbbefffffffaffbffbeffeffffffbfffffbefffffbffbeffebfebfffefffffbebfeffeffffbffbffeffeffffffeffeffffefffffbefbfffefffffffffbbefffbeefffffffffbefffefbffeefffbfffeefbfffefffffffeffffbbfbffbfefeefffffffbffefffffeffeffbebeefffffffefffffffbbffffbfffbfbfffbffbffefffebfebfeffffaefbffffbfffffbfefbffefffefbfbfeffffefbfffeffbffbeffeffffeffefffefffbbffefbffbfeffffbefeffffbffffefffffffaeffefefbfefbffeffbfbefffffefbffffffeffafffffafbfffefbbffafffffbffefffefefffefbebffffffefbfffffbffffffeffaffffbefffffbfffffbfffffeffffbefbfefffbefffffffffebfffffffffbfbfffefbbffffffefbebfffaefeffffbfeffefbffbffbffffbfffefffffbefffbffffffffbfebbefffbbffffffefbefffffefefbffbbfffebfffefbfefffffffaffefbffbfeffffeffefbbffbffeefefffffbfbbffefffffffbeffffffebffffffffbfffeffbefbffffbffffffbfffffffbbffeffeffafffffffffeffffbfbffffffffffefffbfffbffeefefffffefffeffffaffaffeffffffefbeffffefbffffffffffffbeffefffffefffffebffffffeefeffafffffefbfefffffefffbffffefafffffbffffffffeffbfffefeebbffefffffbefffbeffffbbffffbeffeffefbeebfffffbbffffbbfffeffebfffffffefffbeffaffeffffffeffebfffffffffffffffbeffffefbfefffbfeffffbfbfeffffbefbffefbffffeffefeffffffebfebfffffbaffffbfffbeffffefffffefffffefffefbfffffffffffefbfeffefafffffffbffffffbefffffefffffffbffffbffffebefbeffffbeffffffffbefffbffffffeebfffaffbfbbfffebfffbffffbfffffbaefeffbfffffffbeffaffefffffffffffbffbffbeffffffffffaefffbfffbfffffffbbffeefbffeffeffffbeeffeffffefbfffffbfeffffffbfffffbaffffbbeffebffbbffefffeffffffbfeffffbebffffefeffbfffeffebfffffffffbfbfebefffeffffafbbfffeffffffbfefffbffbfffefbeeffffffffffffffffbfbfebfefffbeffbffeffbffffbeffbefeffffffffbeffffeebfeffffeffbffeefeffeffbfffefeffbffefffffffffffaefefffefffbfffeeffffbeffffefffffbfbffbbefffffffeffbfffefeffbffaf := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask386757 : MertensSieve.bits 386757 = 0xfbffbfffffffeffffbfffefffffefeffaebfffffbffffffbffbfbeebeeffffbfffffefffffffbeebffbfffefffffafbffffeffffefbfffbeffefeffffffeffffffffffafffefffffebbefffffffbfbffffffbffffbffbfefeffffbffbfefffbfffeffeefffffefbfffffbfffffeffbffeffbffffbffbfefeffefffefffbfffaffbfffefffffffbfbaefbfffffffffffeffffbfffeffeffbffbefeeffefffbefbbfffeffefeffffbfffefbaefbffefbfebfffeefffffffbfbefffffbffffffffeffaffffbeeffefffffffbffffbfebffbfffbffeffbefffffffefbffbbeffffeefffbefffeffefbefffbaefffbffffffbffeefbfffffaffefbeffffffebbffbfffefffbffffefaffefbbfffebbffffffffbebfffeefffbfffffbffffffefbfffbfffeffffbffbefffffeffffefbffbffbfffbffeffeefbfffffbefffbfffffffefbffffbffbbfbeffefffffafffebfebaffbffbeffefeefefffffeffffbeefbffbfffebfebffbfffeffbeffffefffffbffbffbffffbefffffbfffefffbbffaffbeffefffbfffffbefffeffefffffffeebffbefffefbfffebffbfffefffffbfbbfbeffffffffbfffffefffeffffbfffffffbfffffffebfefffffffffbaefbfbefbfffbffefbffffffeffbfbfefffffebfffbffaffffbffffefffbbfbfffefffefffbffffffefbbefeffffbfebfeffffafffffbebeffffffffffffffeefbefeffffbffffefeffeffffbfeffffbffbfbaffbefffbbffffffebfffefbfffffffffffffffeffffffefffbffbfffffbbebbfbfffbffeffeeffebefbfffafffefbfbefbbffffbfffbfffefeffffbfffffffffbffaffbebffffffeefbfffffffbeebeefffbeffbfffffbfffffffffebfefeffbffeefbefffbbffbfbefbfffffbfffeffbffffbffffefbfbfeffeffefbffffbfefffbffbfffffbbfbffffefefffffffbffbfebafffffbebbffefbfffffbbfffefffbfeffffffffebfffeffeffefffffffffffffbaffbffeefffffffffbbfbffffffefffebbeffefefffffefbffbfefbfffffeffbeffebbffffbffbffffffafffffeebffffffaefbffbffffbffffefffbfeffffeefeeffffefffffffbfffbffaebfffefffefbffffffefffffffffffefbfffffeffeffbffffbfefaefbffbfffffffffffffbffbfffeefbffbfffffffbeffefffffeefffbefffefbffffbfffffbaefefbbfffffefffefaffbfffefffbfefbfffffffffefffffffeebbffeffffffffeebffffffffffffeefffbfffffffffbfbfeffffbffefbfffbefffbfffffbaffffbfffeffbfbfeffffffbfeffffffbffffeffffefbfefffffffbffeffeefffffffbeffffffbffffffeffefffefbfffffeffefbfeffffffbfffffbaffbffeefeffbffeffffffeffffefbefbfffffbfffbffeffbffeebfefffbffffffffbefffffffbbffffffffbffbffffffefffffffefffff := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask394949 : MertensSieve.bits 394949 = 0xfefffffffbeffffbfffaefefbeffffffffaffbfffffffffebbffffbfffffffffeffefbbfbbfffffbefffbeffffffebaefbffbfffffffffefbffffffffffffffbfffeffefefbafffffbfbfeffebfefbfbfffbffffffffffbfffffbfffbffffbbfbfebfffaffafffefbfbffffefffbfefffbfffafffffeffffffffffffffaebfffffbfffaffffbfffeefbefefbffffffefbefffffaefffbffffefefbfffbffffbefffffbffbffeeffffffffebffffffbfffffffbbfffeffffaffffbffffebfffffffefbffffbfffbffaffffbffbffffffeefffffffffffffefbbffeffeffbfffffbeffefeffafffffbfbffffffffbefbffffefefffffbeffeffffffffffbeffefffbfefeffeefffbfeffeffffeffffffffbffefbffbbfffffbfffffffbffbeeffefffbfffffffffffffffbefffbfffaffbfbffffebffffefbfbfffffbffbeeffffbffffbffffffffbfffffffffeffbffefffeffeffefeffffbfeffffffffffbfbfefefbfefbffefffeffebbeffffeffbfbffbffffffefbffffffbffefffefbfffebfffbfffebffffeffffefbbfffffeffeefffffebffbffbfffbfffebfffffffffffffefbeffefeeffffbfbbfbffffffaffeffbffffbbfffffeeffefffbbefbffefffefffbbfffffbebfefeffffffffbefffffefaffaffbfffffefffffffffffffffffaefbfbffffebffbefffffefffefeffbffaffefbfffffbeeffffbfbbfbfffbffbfbfffffffeffefeffffffefeffeefffbfffbfffffbefffffeffebeffffffffffbffbffffffaffffbfffeffaffeffffffffffbeffaffffbfeffeffefefbbffffffeffffbffeebbfbfffeffffbeffbffefffffeffeefbebfffbffbfbfffbffefbeffefffffbfbefbffffffffbffffefbffeffaeffffffbfefffbbefffbeefbffbffffffefeffbffbffbfffefffbfefffffffbfffeffffeffffbbfbffffffffbaebffffefafffffeffbffefffffffbfeffffffffefafffffbfffebafffffafffffeeffffeffbfffffeebfffffffffffbeffeefbffeffffffffaefefbfffffbefffefffbefbffffffaffffffebfffffbffffffbeffffeffbefbffeffbffefffefffbffbfffefbbefbffbfffffffbaffbffffffffeffffffffffffffffffffffffefffbeefbfffffbffbffffbfefafbbfffeffffeefffbfffbefefbbffefffffffbffffffefbeffbffeffffffffaeffffeeffffffbffbfebefffffeffbffbfbffffefffbafffefefffefffffffffbffbbffbffbfffeffffaffaffffffefffffffbffbefffffffeffeffefbbffefffffafffffffffffbffffffffbfffefeeffffbfffefffbfefbffefffffffbeffbffefffefffffffffbeeffffeeffffbfffffffbeefbffafffffbfffffbefffffffffffffaffefbfefbffeffeffbfbffbffffffeffafffefffbffbeeffffbebbffeeffffefffffbfbffbbffffffefbeffebbfff := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask403141 : MertensSieve.bits 403141 = 0xfffffbfffffbffffffbebfefefffffbffeeffffffbfefffbfffbfbeffeffffbffbbfffefeffbfffebbebfffbffffffefffffeffffffbbfffffffffefffffefffbffbeffefbfffffbfebeffbffefffefffbfffbffbfbffffefaefffffffbfffffeffbfffffffbefbfefaffefffefefffffffffebfefefbbfffffbeffebfffbeffffbfffebffffefffbbebffffffbffffffebffffefafffffafffffefbfffffbfffffffeffffeffbefbffffbeffbfbfefffffefeefaffbffbeffffeffbfbeefffffffeefefffeffffeefbffafffebfffffffeffffbffffffeffefeffbefffffffbffefbeffffbfffbefbfbffffefeefffffffefbffbfeffffaffeefbffffffffaffffbbebffffeffffefffffffbfefffbfefffffffefffffbfffeffefbffffbfefbefffbfeffffbfbffbeffbffffbfebfffffffffeffefffefffffefefbfffbffeefbffffbfffffbeffaffaffeffffbfffbefbfbfffbffffffffffbfefffbeffffffffefbffbfefefffffeebbffeffbffeffbfffefffbeeffffffbffffffbffbfbffbfeffefbefafbefffffeefffffffefbbffffffffbffefbffffefefffffbfbfffefffefaffbffbfffffbeffffbefffbfffeefffbfeffefffbeffafbffffffffbeffffbeefbfbffffffeffefbffbeffefffffbffbfbefbfffffffffbeffefaffefbffbfffffffeffffffffeffffbefeffaffbfffffeefbffbfbbffeffbefefffeffebffbbffbffafffffeeffeffffbffffffffbfffffbffbfffffbffffffeffeffeffffbffffffffffbfffffbfefffbffffeffffefbbfffeffffffffffffbfeffeffffafffffeffeffefffebfffffffffbfbaeffebffbfffbffeefbebfffeffffffffbfffffbffffbefffeffffeffeffbfbbffeefffffffffbbffefbfffffffffbfffffbefafffffffffffbefffffeffffefbffffffeffbffefffefafffffbfbfebffffffefffefefffffafbeffffffebfeffffbfffefffbbffeffffbffbfefaffefbaffbfbfffefffffffbbfbffffefffffeffeffebefffffafbbffeffffffffafffffefbeffffffeffffffbaffffbfffffbffbfefefffefbebffbeffbffbffffbffffefffbffffffffffffafffebffffebfefeffffbfeffffaefeffbfbfeffffffffffffffffffffffafbeffbfbffffffffbbeffffffffffffffefffbefffffbfffffffffffffffffefffffffffeffffbebbffefbfefefbffffeffeffffafbbffffbfebefffffeffffffffaffeffffbfffeebfffaffffffefefffefaffeffbefffffffffbbefffbfffefffffffbffffefeefafffeffebfeffefbfffefffffffeffeffeffbeffeffffaffefffffffbbfffffeffffffefeefffbfffbebfffeffeffffffefffbbffbffeffbffeebfeffffffbffbfffbffffffffffbeffffffffffbbfffefbfffffbfbbfffefeffefffffbefeffafffffbffffffffeffffbbfffe := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask411333 : MertensSieve.bits 411333 = 0xffefffffbfbeefbfbfefbffefbefffeffffbfffffffbffffeffefffbefbfeffffeffeffffbffffffeffafbffbfefffbefffffffffffffbffffffaebbfffffffffffeefbeffffefffffbefbeffeffffefbffbbeffefbeffffbebffbefbbffbfbffbffbfffeffeffbfffffffbfeffffeebffffffaefffffffffbeffffffffffbfffefffffbffbffbffffbbfffffffbfefefffefafbafbfeffffbffeffbefffbfffffffffbffbfbfefeefeffeffffffeffffefffffbfbeeffffbfbffbbfffebfefffbffffebefbeffbfffffffbfffaffefbfffffbfffeffbfffeffffeffbffbffeebbebffffffbffffbffffefbffbfbeffffffffaeffffbeffeffffbffafffebffbffffefbffeffffbffffffffbafbfffffffefbffefbfffeffbffbffffbffbffbfefffbffbbefeefeffffffefbfbefffefeffffffffffffefffbaffbfffeffffffbeffbffffffffffffffbefefffffaffbeffefffffeffffffffeffffffffffbfffffefffeffffbffffffefaffffffefffbefffffffbffbfffeffaefbffeefffbfffafffffaefbebeebffffffbfffffeffffffffffbfeffffbefefbbffffbfffeffffffffbfbeebfffffffffbfffeffefbfffffffffffbffbffbefffbfefbefaffefbffffffefffffbeffefffffffffbbfffebffbbfffffbffffffefeeffffefbbffeefeffbfbffbbfffebbfffffeffbfbeffbffffbeffbfffeffefefffffbffffbfffeffffbfebffffffffbfffffbffffffffffebfffefffffbfffeffeffebfffbffbefbefefffffaffeffbffeefefffffbfbfffefffffbffefbffbfeffffefbfefffbeeffffbffefffffefffffefbfefffbeebbfffffefbfeffebbefbfbafffffeffaffeffffbbffffffefbffbefffbfffeffffbfffbffffbeefbfffebfffefffefefbfffbefffbfffafffebffffffbefeffbfffeffffeefefbbffffbffffeffffffbffffebeefffbefffefeeffffbffaefffffffefffffffbffffffbffbfffffbfbfebbffefffffbffffbfffffbbffffbefffeffffbebffffefaffffffefffffefffffffeffbfbffffefbffeefbeffffffffffefffeffffbffeffefbfffffffffffffefffffffffffffbeffffffbbffbfbfeffffffbeefffbfffbfbfffaffefffebfffeebeffafffeffffefbfffefffffbffffbfffefbbffffffffaffbfffffffbfeffffbfffffbffefffffbfffffffbffffeffffffffffffbbffbffaffbfbfefbffaffffbbefffffeffffffffffefbeffffbefffffffffffbffeffbffffffffffbbefffffffbffeffeeffffeefffffffbebfefeebfffbffeffbffefbbffeffbfffefefbfffbffaebffbffbeffbfffffbffffbeefffbbffffffffbfffffffffefeffaffeffbffffbffffffbfbaffbeffebbffffbbffbfffffeeffffeebffffefbefefbeffffffebfffffbffbffbeeffffefbffffeffefffffffbfbfefffbfef := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask419525 : MertensSieve.bits 419525 = 0xfbffffffeffffffffffffffebffffefbffbffffffffeffefbeeffffffffeffffefbbfbeefaefffbffffebfeffffbfffefbfffebfffffbbffffffebaefffffefffffffeffeffffbfffffffefffbffffebeebfffffbbfffffeffeefffffebffffffeffbffaeffffeeffffbfbbfffeffffffffffbffbfbeffaefffbafbffffebfefbffffffeffffeefbffffbffffffbffffbfebfefffbfffffffffbfffeffffffffffbefffbeffefbffffffefffffbffbfbfefffbfffffffeffffeeffffbffeefffffffafffffffbffffffbffaffeeffeffffffffffffbbfffebfeffffbffffbffffffbfbbffffbfefeefbffaffffbeffeffbfbbfffffffffffffffeffeffffeffffffeffefffffffefbffbffffffbffefffeffebfffeffefffebffffffaffffbafffffefbfefffbffffffeeffefeffefbfebefffffbffeeffffffbfefefffffffffebfffffbfffbeffffbffbffaffffbffbfffffbefffffffbefffffbfffffeefbffafffffbeffefaffeffafbfffffffefaffeffffffebfffefffefbfbffbefffffbffffffffeeffffeefffbfebfeffffbfffffeffeffbffffbfffeefbfffffefffffffffffbfbbfbfffefffffffffebbefffbbffbfbfffffbffbfffefbeffbfbfefeefffbfebffbfffffffffeffbfbffbaffaffefffeffeffffbffffffffffbbffeffbefbfffffbffffbffbfebfefbffafffffbffefbfefffffffbfffefffffffefffefffbefffffaffbefffffffefbefffeffefaeffffbfbbffeffbffeffffffffffbeffffbfffbfbfebeeffffafbfffeefeffeffffbffbefffffffffefbeffefbefbfbfffbefeffbfffffbeffefffbfffeffffffffffbbffbffaeffebfebeefffffffbfffffbefeffffffebeefffffffffbbeffefffffffefffffffbefffffffffefefbbefaffeffffffffffffffbffffbefffffbfffffbffefffefefbfefffbfffeffaffffbbffffbfffefbbfbffffefbffffbfffffffffeefefffebfebfebbefefbefffeffefffffffeffbffefffffffbffffffefbfffbffffffffffbfffbfffffbeffffbfffffffffebffbfefafbafbffffffeefffbbeffeffebfffffffffffbfffffffffefffefeffbffaffbeffffeffbefeffefffeffffeffeffbfbfffeffbfffffbefffffffeffffffffbfffefeefffbbffbffeffaffffbfeffebffffffeffeefffbfeffeffffeffbfffffeffeffbffffbfffffffffaebfffffffffafbbfffebfeffefffbefbfffffffffbfbefbfffffffffffffefffbefffffaffefbffffffeffffbbfffebffbfeffffbfffebffffefffbfffbefeefeffbfbaefbffefffffafbfeffeffffeffffffebffffffbffefffffffffffbefffffeffffffbeefeffffffebfffffffffbeffffeebeffffffeffffeffffffffffbbeffffaffaffefffffeffbfffffffbfefefbffffffffbffffffbffefbafbffbffbaeffffeffb := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask427717 : MertensSieve.bits 427717 = 0xbffeefefffffaffbfbffffefffffffffbfefbffbffbebffffefffffffbfffefeebeefffbbfffffeffbefafbbeffeffeffffffbffffefffffffbffaffbfbfffaeffffffbffbfefbfffffeffbffffbbefffbeffbfffffafffffffbbebfffeffbfbbfbffffebbffffffffffbfffeefffffffffffefeefffbeffbfbefbaffeffffffefefbfefeffbfbbefefbbffffbffffeffffbfffffaffffbfefbfffffbffbffffffffbffeeffffeffafffffffffeffefefffffbfbfebffffefbffffbbfffebbefffbfefbfffffbffbfbeeffffffbeffefbefffeffefeffbffbffbfffffefffffeebbffffbeffffffffffbfeffffaffffffefffbbffffbffbfffffffffefbefffebffbffffffeeffffffbeeffffbffbfffefbffffbffffebeffaffbffbefbffffbffffffefbffffeffffffffefbefffffffafffefffbfefefffffbeffffeefeefbffeffffbfeffffbffffbbebeefeffefffffbefefbffffffffbfeffffbeffffbefbfbeffeffafffefffffffbffefbbfffebffffffbfbfffbffefffffeffeffbffeffffffffaeffefffffffefbeffbefeffffffffffffebffffefbfffefffffebfefeffaffffbffbfffbfbbfbffbffffefeffeeffffeffeffafffefffbfefbefffbefffefffbeeffffffbfefffbfffffbbfffffffbaffefbafffefffffefffffefbfbeffbefbfbfffbefeffbffffffffbffeeffffbfbffbbeffebbefffffebfffffbaeffffeffffbffffffafffffbffefffffbfbaffffffffeefbfbefffefffbfffffffeffefeffffffffbffffffebeffefbfffffbfffeefefbfffffbfeffffbffeffbfffebfefbffeffffbeffbffbfffeffffefbeffffffffbfbfffbefffbffbbfffefeeffffbffbebffffefeffffffeffebfefbfbbeffefffbeffffbbfbffbfefbffefffebbebfffbffeffafbffffffbffefffffffffffaffeffbfbfffeffbfffffeebffbffbfffffffeffffefbfffbfffeffffffffefffbfefffbfffbffeffaffbfbfffffffffffffffefffffffffffbfbfffeffffffebfeffffeefffffffffbeebfffbfffebfffeffbefaffefbbebfebeffffffebfffffbbeffffefbfffefffffffffebbfbfffeffffbaeffebfffbffbfffffffbfebeffffbffbbfffefeffafbeffbfffebbffeffffbbffeeffefefffffbeffebfffefffffffffffaefbffbfffefffbbefbffefffeffffefffffaffbfbfefeffffbfffffffffbfffffeffbffffffeffffefbffffffffffffbfffffeffbffbfbfefffffebeeffffeffffbfffeffbffffffffeffbefbfbeffffbeeffffffffffffbfebbefbffbfbffffefbffefffebfffffffffeffffbfefffffffefffefffbffffffffbafffffefffffaffffbbeffffffffffeefbeffebbeffffffffffeffbffffffffbebefbbffffbeebffffebfefaffbffffbefffffffbaffffbfeffffffffefffffebefffffffbfffefbbe := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask435909 : MertensSieve.bits 435909 = 0xffeffbfffffffbbffefffffbebffbbffffffeffebffffefeffbeffebeebfffbffefffffffffffbffefbfebeeffffbffffbfeffebffffffbffffffeffffefbffbbffffbaffbfbfefffffffeffefffffbffefffefbfbbefbfffeffffefbfefbefffffffffffebfefeffbffefbefbbeffffbffeffffbbebefbfffefbeffffffeffefffbafffebffffefbffefbbfbeffaffffffffffbfffbfffffbfffeffffbefafbeffbfffefeefefbfefbffeffeffffbbfbfffffffffffffefffbfefefffffaebfffffffefbffefffebfebfffeffeffbfbfffffffffafffffffbbffffffefbfbffffffbfbffbffffffbefeffeffbefeffeefbffefbbfbfffeffeffeffffffefeffffffebbfbfebbfffffffbfffefffefffbfefbffffbfeffffffffebfebfffbffaffbffffffffbffefffffeffbefffffffbffffbfffbffbefbffffbfffefbeffbffffbbeffffbffffbfffeffefbffffeffffbfffffffffebfefffffffbffbfffffeffffbefbbfffeffffffffebbfbfeffefffffffbefeebefffffbeffffeffaffeffffbffffebbfffffbeffebffffffbfbfefffffffbffeffffbfeffebfffffffeffefefffffbfbefbffffffaefefffebfeffffffffffffffebfebfffafbeffbfffebeeffffffbffffffaffbfffffffbeefbffbfffffbfbeeffffbfbffffeffefefffffbffbefffbbffffbafbffbffffffbffffffefefbfffffffffbfbfffbffeffffbfefeefeffefffffffbfffbffbfbfffbefeeffffffbffbffbffbeffbfbbefffffefbffeffeefbffffbefffffbfbfffeffeffffbeefbfbfffefffffbfbfffefffffbfbbfffeffebeffeffffffefffbfefeffbffffffffbffeffbeffffeffffffffeffffbfffbffbfbefffefeffbfffffffffeffffbffffffffffffebfffefbbffbefeffeefffffefffbffbfefefffefbffeebfffffffefffffefeffffffeffefffbefffffffbbefffffefbfbffbfeffeffffeffffbfffefbaeffffbffffbffbfffffbbffffbfefeffbffeffffffffeffefffeffefffbeffbffbeffefeffbffbfbfffffffeffffffbfebfffffffffbfffffffffebfffeffefffefffffeffffbefbfffffbffeffffffefffbeffeffeffffbfefffffffffbfffeffbffeffbfffffefbeefffffebfeffeffffffffffbffffffefffbbefbfbfefeefffffebbffffffffffffeffeffebfffffbefbffffffeffffffefbfbeffbffffbeffffbfffeffbfffffffbeefeefffffebfffeffbefbffffffffefffffbffbefffbefbbeffffffffffefffffeffffbfffeffeffbffbfbfeffffffffffefffebfebfefffffefbffefffffafffffbefffbfffbffffbffffebfffafbfffbfffffaefffbbffffbffbfeffffbfffffffffefffbffffffeebfffbfbbeffffefffffbffeffffffffeffbffefbbffffbffffffefbbeffffeffffffffbffeffbefffbfefffffebfffffbfef := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask444101 : MertensSieve.bits 444101 = 0xfffbfefffffffbefbffeffeffbffffbfebffffffbffffffffffbbeffffffffefefbfefefffffbffffbefffffaeffeffefaeffffbefffbffffefbfbfffffbeffbffbfffefbfffffbffeffbfbfebfebbeffffefffeffefefffffbfffffefbeffffbbffffbfffefffffffffebffffffbffeffbfffffeffffbefbfffeefafffffaffffffeffffffffffbeffffaeffffbfffffffffffefbeefffffeffefbffbfffffefffefbffffbffffefbffeffeefffbefbafffffbffbebfeffefafbaffbffffbeffffffffbfbffbfffbffeffffffefafffffefffebffbeffffbefffffeeffffffbfefbebefffffbffffbfefeffbffbfbeffbeffefbfffffffbfebefbfeffffaffffbffbbefeffbefffffefefffffeffbffeffaffffbefbbffffffffeffbfbfeffebfffbfbbfbfeffefeffffffffffbffffffbfffeffefffbfefffbfefbfbfffeffffffffffbeefeefbfbfefffffefeffeffffbffffebbefefbffffffffffffffffefffbfffeeffffafbffbfffeffffbfefbffeffeffbfbbffbfffefaffefbfffbfffefaffffffebfefeeffffaffeffbffeffbeffffffbfffffffffbfbaefffffefffffffbffbffffbfffffbbebbfbeffbffefffffbefefffffeffffffefefbfffffbeffbffffbfffffffebbffffbfeffffffffefffffffbffbffffffffffffffffbffffffefffffeffbfbefbbffbffffffefeefbffffffffffffefeffffffffbfbefbfefeffafffebfffeffbfffeffffefbfeffffffbbffeffbffbfbffffeffffbffffffffbefeffbeffffbfffeffebbefffffebffbffffefefbfffffffffaffffbeffffffffeeffffefbfffffffffaffffffefffbeffeffffffefffbbffafbbffbfffefefffffffffffefffffbfbbfbfffffffffffbaffbffeffeefbffeefffbeffffffffeefffbffbefffffbffbffeffffffffbfbfeffffbffeffffbfffeffeffafffebfeffffbfffffbffbfbffffffffffefbfbefffffbffeefffffffffffffeffbffffffffefbeffffffefeffefffefffffffbfffffeeffefffbefffffefffebfebfffffbfeffffeffbffefffefffbeffafffffffbbefffffefaffbffffffffeffefbffbfffffbeffffffeffefffffffefbfffffffebfffffbefbfffffffffbfbefbfffefbfffefffffbfbfeffffafffffbefffffffffbbfbfffffffefefffebffbffffefefbfefbfffffeefffffffbfbffffefffbfefbffefbfffffffffffffffbfffffbfffefffbfefffbbfbfefffffffefffffffbffbbffeffefffefffffffffbefbbfffeffffffffebfebfffefffffbfbbffefffefeffffffefefbbefefbbfffefefffefbfbfebfffffbffffffbfffffeffefffffefbffffefeefffbfffbfffeffffeffeefbfbfebbefffffffbffeefaffefbffffeffffaffffffffffffebaffffffffbffeebeffbfffeffffffffffefffffbebefbfffbffffbbefeeff := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask452293 : MertensSieve.bits 452293 = 0xfefffbffbfffffffefefbfefbfbefffffeffeffffffffeefefffffbffffbfffbffefbffffefeffbffeffbffffbfffbffbfbbebeffbffbffbfffffeffffffffffffefffffefefbfefffffffbffffffffbeffeffefffbffbffffffbffefffffffffffbffbffefbffffebfffbfbbfbbffefffffffffffffffffaffefffffffbfebbffffbfffbefffffefffbeeffffeffaeffffeeffefefffffbffefffffeefbffeffffffeffebfffffffffbffefffffaffffffffffbfefafbfefbffefbeefbfbaffbfffefeeffffefbffbfffbffefffffffbffbfefaffffffffffbfffeffbfffeffffbffefbffbffbfefeffbffbeffffeebfffffbfebffffffeffffbeffffffeffffffffffbebffffefffbefffffefbbefefffffffffffffffffbffffbffbfefaffbeffffffffffffbbfffffffffffefbeefbfbffbfffefffffbebffffffffbffffffeffbffeffffbfffffffefeffeefffbfefffffffeffffbffffffbffeffbfbeefeffbfbffffeffebffffffffbffbefbffffffefbbffffffffeffbfffffeffeffbfbaeffefffbbfffffbefffbffbffffffafbbffeffeffefffeffeffefbffffffebffbffffeffffafbbffffffefefbffffefeffaffbffbffffbfeffffffbffffebfffeefbfffffffffffeffaffffbffffebbfffffeffbffffffefffbbfffffeebeffffbfebbffffbeffbffaefffbfefbefffbbffffffffeefbffbffbfffefbfffffeffbffeeffffeffffffffeffbfffffffffefeffbffffffeffffffbfffafffffffbfebfffbffffffefffbfefffbfefbfbeeffefefffeffefeffefffffbfffeffffbffeffffbbfffeffffefbffffefffffeffffefbfefffbafffffbffbffffbfffffbaffffbefffeffffefbbffefffffaffbebfeffffbefbffbffbefeffeffffffeffebeffeefeffffbffffefafffffeefbfbfffefffffefbbfbfeffffffbfffffbefffffffffefbffefffffbfbffbfffeebfffffbffbfebffbfffafffffffbfebbffffbfffffbffffefffbbffffffffaffafffffffbeffffffffeffbfffefbfffffafffffffbaffffffefbeffffbffffffebfffffffefefffffbfbfffeefbffffbfffeffbeffffefffffefbfffaffbebffbfffbfffffbfbfefffffffefffffffbfffafffffbebfeffeffffbfbefffeffeffffbfbfefbfffeffeffffffbbffeffbfffffafffffffffeffffeffffffebbffffbffbbfbfffaefbffefffebffffffaffbeffffffbfffffffffffffffeffbffffffeffffffffffafbbffffbfffeffefbfefeeffffefffffbfbffbfefeffafffeffffeefffbeefffbffbfffffffeffffefffffefbfffffffefbfffffeefffffffbfffffffffffeeffeffffffbfefefbfefffffefffbffffffbffffffeffebfffbffffffffeeffffbffeffbfbffffffeffaebfebffffeffffffffffeffbfffffffffefefffefffbfffffffefffffffee := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask460485 : MertensSieve.bits 460485 = 0xffbefefbeffffbbefffbeffeeffffefbfffffbfffeffbebfffeffbffbffbfffefffffffeffffbffbefffffffbbffffffeffefbfffeffebfffffffffbfbbffefffefbffeeffefeebffffffbfbbfbfeffffeffbfbfefffffefffbfeffefffbfffffbaeffebfebfffffffefbffefffffffbfefffffefbefefffefffbfefeffaffefbfefeebfefbffffbbffffffefefbffbbffffbbefbffaebfffffbfefbffeffffbffffffbfffeffffeeffeffffeefffffffefffffafffffeeffefffbffbfffffbeffffbbfffeffffaffffbfffffffffeefefbefffffffffefbfffffffbeeffefffffffffbeffffffffbfffefffbfeffffffbbffeefbeffffffffffefffffaffeffffbfffbfffffbefbefefbfeffffeffffffffbfffffffbfeffffbffeffffffffeeffeffffbfbfeffffbffffbfefbefffbbfffffffffeffffaffbfffefffbfffefffffffbbfbeefeffffbfefbfbfeffffeffefffffffbfffaffefffefefbffffffffffefeffeffeffafffeffffeffffbbfffeffffefffffbffffbfefbffbffffbfffffbefffffffbfeffefbffffffffffffefbffffffefffbffbfffffbbeffffffffefbffaffffbeffeefbffbfffffffffffafffffbffeebaffbfffefffbffbfffeffafbbeffffefffffbebbfbeffbffffbfebfebffbbefeffeffffbffffefffbfffffbeefafffffeebbffeebeffffffffffbffbfffffbfffbfffffeefffbffbbfffffeefeffafffefffffffffbbffbfbffbfeffffbefffffffaffbffffbfffffbfffaffffbfebfffbefbffefffffeffeefffffebffffffaefaffbffffffefeffefffffbffeffeffbfbfefbffeffbffeffffffebffbfffafffefbeffeffffafbfffbffffbeffffbfefbefffffefbfffefffbfffbffefbfefbffeffffffffbffffffeffefbfbfebfeffffbfffffaebbffeffffffffbffbfffffbffffbbfffebeffbefbfbffffeffebfefbffbefbfffefefffffefffffffffffffbfeffffffffffffffebffffffbffffbffffffefbfeffffffbfebffbeffbfbffbfefffbffffffffffffeffffffffbefbfbefffeffffeefbfbeffaffefffffbfffeffefaffeffbeffefffffffbebfefffbfffffbefffebfefefffffeeffefffffefbffffbbffffffffbfbfffffbfffefffffbfbfefffffffeffffbfffeefbeffffbefbfffffeffffffefffffffbefbffefffffeffeeffffffbbfffffeffffbfffffbfffaffffffffffffffffffffeffbffeebfefffffefffbffbfffefbbfffeffefefffffffffefffbffffffbffbfffffaefffffebbffeffefffffbfffffefbbefeffafffffeeffeffffbeffffffbfffbfbffbfffffbbfffffbfffefeffffffffbebfffffffefaffffbbebeeffffaffeffffbefbbffbffffbffffffaffefffeffffefbfefbfffffffffffeffaffefffffefffefffbeefbfbfeffffeffffbfeffffbffbfffffffffff := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask468677 : MertensSieve.bits 468677 = 0xfbffaffffbffffffbffffbfffffbeffbeffffbeffeffffafffffbffbfbefffffbfbbfbbfbffffffffffffffbefbffffffaffbffffffffefbbffbeffffeffefbffbbffffffeffffbffffbffffffefbeefffbffffffffbfffbfffffbeffffffbbeffebefffffbfffebfebbffeffefbfffefffefffffefbefffbbefeffaffffbfffeefbfbfffbffeeffefffbbebffffefefffffeebfebfeffffeffafffebefffefffbfffffffeffffefbffbffffffbffeffefffeffebeefffbffffebfebfffbfffebbfffffeefefbfebffffffbffeffbffbffffffffeffbfbbefffffffefbfebfefefffffbffefffffffffffffbeffffbfefeefbfbefbbfbfffffffffeffbfbffffffafffffbfbfeffefbffeffffffebffffffffbbfbffbfffeffbffffffffaffaffeffbefefffffffbafbffbffffffffbeeffffefffffaffbffffbffbbeffffbfbbfffeffffffbffffeffffbffbffeffffffefbffbfbeffbfbfffefffffeefffbfefbefeffeffffbffbeffbfffebffbfebbffbffbffbffffbeeffffbeffffffffffeffffffeffffaffefbbffffffffffffffbffbffefffefbffeffffbffffffefffebbfbefbbeffffafbfffeffafffffbfbffffffaefffffebfffffbeffbfffefbfbffffefffffffbfbfffaefbfffefbfbffbefffffefffeffefffffffffffffffbeffefffefffffffbfffffafffeffebfffffbfffffbffbfefbffeffffbefffffffbffbfeffffeffaffefbbfffeffffffbbfbfffffffefffffeffebfffaffffbffffffffffefeffeffffffffeffbffbebffffeffffefffebffbfefeffefffeffefeebffffffffffffeeffffffbbfbffbefbbffbfbffffffffbbefbfffffbfbffffefffffffffbfefbffafbfffbefefffffbfffefbefffffefffbffbfeffeffffeffffffebfffbefffbeebffbfefefffffaffbffeeffffbfffefffbeffeffefbfffbefffbfffbffbfffffffbbffaffffffffefffffffffeffebfffaeffffbeffefffffefefffefbfbeffefffffaffffffffeffafffeffeffffeffffffffbfbeffffffffaffbefefbfffffbffbbefffbbfffffefbffbffffffbfbbffffffeffffbffbfbffffeffffefbfebbffffbeffeffaefffbffffffbffbfbfefeffeffefffebfefefbbffeffeebffbfefffffffbffbffefffefffbaffffbfffbffbfbfffbfbeebefffffbffbefeeffffbfffffffffebaeffffbffffbfffeffffffefffbfeffeffffbffffbffbfffbffaffffffefeffffbffbfefefbfffeffeefbfffffbeffffffbbffefffefeffffbbffefffffefbffffeffffaffeffffffefffbffffffeffffbfeffffbffeffffbfebbffbffffbfeffffbffffbbffbffeffeefeffbffbffefffffefffeffefffbefffffbffffffefffffffefbffffeffffffbfefbffefffffffffefffbeebbffeffbfbfeffffeefffbffffefeffefffffaffffbfefbefbfbf := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask476869 : MertensSieve.bits 476869 = 0xbeffeffefefffffbffbffffffffbfffffbffffffffffffffbffefffffeffffffffffbfefefbffbfffefbfffffbffbfffffffffffbbfffefeebfeffffeffffffffbffbffffffffeebffffffaffbfbffffefbffefffffeefefffffbffbfffffaffffbfffffbfffbffefffffbefeffeffbfffebffffefbefbffffbffbffbefffffeffbfbffffffbffffbfffefffefefffffbfffffbffefbfefffbfebfffafffffbffefbeefbfffefbfbfeffeffffffbffffefbffeffbfbfffffffefffbefbfeffffbffffbbfbfefffbfffffbfefffffebfefeffeffbffffbfefffbeffffffefefffffffbbfbeefeffafffffffbffbbfffffbffbffffffeffffffbfefffffffbffefffffffffffbffeffbefffffeffffafffffeffafffffeffbfbfffbffefffefbfbeffbffbffafbbfffebbffffbbfffefefbefffffeefffffefffffffbffbfbeebeffffbfffffffffeefffbfefbebefbfffbffbfbbfffffbffeffffffeffffbffffbfebbffeffbffeffbfffffffffffffbefffebefffffbffffbffbeefeeffffeffffffffbfffffbffffffeffffffbbffbeffebbefffffefbefffbfffefffebffffffefffffaeffefefbfffbffbefffbffffffeffefbffffeffffbfffeffeffeffffefffffbffefffefefffffbfbeffbffffbffffffffbaefffffffffffeffffbffffbbfbfffeefbffeefbefeffbffeffeefbffefbfffbfbffffeffefaffeffbffbfbfffeefeffbfbffffffeffffffefffbffbfffffbfffbffeffeffeffefbfffefbffffffffffefffbffffffffffffffbbffefbfeffefefbeefefbbffffffffaffafffffbfbfeffffbfbbefbfffefaffeffeffffbffbffffffffffffffffffefbfffffffebfefffbfeffffefbeffbffffbfebfebbffffbaeffffffffffbffeebffbffffffefbffbfebfffefffffbeffefefffefffbefbfefeefffffffffffefffffffffffffffbfefbfffffbeffeffefeffffbfeffffeeffefefffeffeffffeffaffbfffffffbfefbffefffffffbfefeffbffbffffbbffffbbfbfeffefeffaffffffffefbfefbfffffffffffefffffffffeffebbfffffbfbfffffbbffffbefbbffeffeeffffbfbfefeffbffbfbfebfefffbfffefbfffbebfebfffbffeffffbffffffbffefbbfffffbffeffbebfffffffffbfbffffffeffafffffbebfefefbeefbfbbfbfffffffffbfbbfffefffffffffffebffbeffaffffffefbfbfeffffaffeffffbfeffffbffbffbfffebbfffffbffffffffeffbffeeffffffbeffffffefffbfffeffffbeffbfbfffaffaffefbffffebffffffbfbbeffffffffffefbfffffffefffbbfffffefffefbffeebffbfffbefbffeffffffefefffffbffffffeffffffbffffebfffeffeffeeffffefffeffffbffffffefeffefffffffffffbffeffffbfffffffffbffeeffffffbfffbffaebffffefeefffffffffffefeffbffffbbfffe := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask485061 : MertensSieve.bits 485061 = 0xefbffbffafbfefefffefeffbffbfbefbaffafffeffffffbfffefbfffbefeffefffffbffbfffffffffffffbfefeffbffbfffefffbfffffffffbfffeffefaeffffffbfebffbfffffffebffbffbeffaffafffefffbfffffbffbffffffbffbffffbbffffbbfffffffbfefeefbefeffeffffffffffffffbffffbeffefffffeebfffffbfffffffffffffffffffffffffffeffbffffbeffbebefbfffeffeefbfffffbefeffffbffffffbfffffbfffffefbfefbffeefffbffffefefbfeffffffbfefbffbffbffffffefefffebffbefbfffbfffebfeffffffffffafbbfffffaefefbffffefffffffefbefffffffffefbffeeffebeebffffffaffffbeffeffbfffffffbeffefffffffbbfbfeffefefffffffffffafffffbfffebffffffffbfebffffebfefaffeffbefefffffbffeffffbfeffefefffffffffffbffaffffffefeffffffffeffffffffaffffbffbbfbffffffbffaebffbfefaeffffbffffbeffeffffbbefffffffeefffffeffffffbffffffbfffffeeffffffbefbbfffebeffffbfffbeffffbffeffbfbffffffeefbfbefffffffffefffffebffbfffaffeffefffebfffaffffffebfefffbfffaffffbbffeffbefffbbebffffffeffffbfeffffffffffaffaefffbefffffbfffeffffffffffbffeebffbfeffffffffefbfbffffefeffbfbbfffebfffefffffbeffffbefefffffffbfffbffffbefffebffffeffffefbffbfffeefffffefbffeefefffffffffefeffbfffffbfbfefeffefffffbffbfffffeffeffeefffbfffeffffffefbefffffefbffbffffbfefbffefbefbfeffebffffffffbfebefbfefbfbffffffefbffffffbfffffeffbffffffefffbfffefffffaffbebfffeffffffefbfbeefeefafbfffbfffffaffeffbebbfffebbeffffffbfefeefbfffffbfffffffffffeffefbffffffeffafbeffffbefffffffbfeffffffffefafffefffffffbffaffbfbfffeefbffeffefffefefbfefefbffbfefffffefaffefffffffbaffeffffffefffffffffffffbfffefeefafbeffbfffebbfffffefbbeffffbffeffffffffefbbffffbffffefffbffffffbebfffffbbeffffffffffefffffbffbefffbefffefaffffffefefbfffbffefbffffebbffefbfffbffffffffefffffffbeffeeffffefffeffebfeffffffffefefffefffbafbbffeffaeffffefffeffefbffeffbffffbffbfffafbffbfefffffffefbfeffffffbfefaffaffffffefeffafbfefbffeffeffffffffbfffffaffffbfeffebfffbfffffbefffbfffbffbffffbfefeffaefffbffffffefffeffffbfffeffffbffeffbeffffffffffffffebbfbfffffffffefffffefffffaffefffeffeffffbffeffbffffffffefbfefbffffbfffffbfffffbfeffeffffbfffffffbfefffbefbffffefbffbfbffbbffffffffbfffffffffffbffffffffffffebefffffffbbefffffefbfbfeffeffffeffffb := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask493253 : MertensSieve.bits 493253 = 0xffffbfbfefeffffbfffbfffffafffffeffffbffbfffbffefffffeefbefefbefbbffefffeffffbebfeffffbffeffeffffffffbefaffbeffefffffeffffeefbffeffaffaffffbbefeffefffffbfbffffebfffbffeffffffffeffefbbefffbefffefbfffffffffeffffffbfffbfbffbfffffffffbfbfefeffffbfebffbfffbffbffeeffffeeffffefbffffefeffeeffffbffbffffffefeffaebffffeffeffffaefbffeffffffffbebbfffffbffeffefffeffeffffefffffffbeeffefffbfffbfffffbefffbbfffffeffffffffbfffefffbeffffffffbfbfeffefbfffebbfbeefaffeffeeffefffbeffbffffbffbfeffffffbbffbffeffafffffbffffbfffbffffbefbffffffaffefffffbeffeffffffbeffbffefffffeffffbffffefafffffafbfebeebfeffffbfffffffbbfffffbefbefffffffeffeeffefffbfefbfbfffbfffffefffffafffffefffffffbffbbebffbeffeffbeffffffffffaffbfffffefbbffffffebffbfffbeffffefbfffffbafffffeefffffebefffffbffffffefaefbfffffbeffffbffbffffffefffffffbffafffffffbfffeffffffefffbbffffbfffffbfffaffefffeffefefffffffffefffbeeffefefbeffffffefffffffbfffffeebfffbffbfbfffeffeffffffebffffffeefeffbfbfeffeffefbfbbfffffefffffffbeffbfbfffeefbffefffeffebeffbffbeffeffeffffffbefbffffefffffffffbffbfffbffefbefbfebfefeeffffbfffffffffeffffefbfffeffeeffffeebfffefffffeffffbbefffffefbffaffffffffbffefffffffbeffeefaffefbffffefefffffeefffffeffffffbfffbffefffffbfbfffbeffefffffffffbffffeffffffbbffffffefffffffffbffbefbeefbffbefffbffbffffffbfffefffffffffbbeffffeffbefafbfffffbffffffaffffbfffefbfffffbffffffffbbffffffffffbeffbffbffbffffbffbfffffbfefbfbefbfffbfbfffffbefffeffffffbffffebefffffafbbffeeffefaffffffffefbefffffbffbffffbfefeffaebffffebfffafbafffffffbfffbffffbffffffeefeffeeffefeffeffeffefbfebffbbefffbfffbeffeffefeffffffeffffeffbffbfffeffffeffaffbefffbeefffffffffbbfffffaeffffefffffffbffffffbffffbefbfefffbbfffffefffffefbfffffffffbffefbffffebfefbefbfbbefffbefbfefbffffbbfbfffeefeffffbbffffbafffffbfffebffffeffffffbffffffaffffffefbffffbaffeffbeffefffbfefffffffbeffebfefbffefffffefffffbfffffbffffbeffefffffbefeffbefeffffbfeffefbffffffefffbefbffffffafbffbffffeffffeefffbeffffffffeebbffefffefffffffbffeefeffafffeffffffffefffbfffbefffbfffffbbefbfffffeffbfbfffffffffeffffbeffbffefffffffbaefffffeffffbfffeffffeffeffbffaffffff := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask501445 : MertensSieve.bits 501445 = 0xeffbffffbffbfefeefbefefbffffefeffffffffeffffffefeffeffeeffffeeffffffbbffffffeffeffffeefbeffffbfffffbffbeffffbffffffffffffebfefffbffffefffbfffbfbfeffffffbbffffffffbffeefeefbfbffbffbeefaffffffffbffffbefffffefbffbfeffffbffffffffffbfffefffefffffffeffffbefffebffffffffbaffbfbfeffffbffeefffbfeffefbffffbffbefffffffffeffffefbbffeffffbbfffffeefffffebffbfffbefefbfeffffffbfffbffbffffffeffffffbefbbffeffffffffeeffebfefffffffbfbfefefffeffffaffbeffffbffffffffffbffbeffefbefffebffffefffbfffffbefffefbfffefbfffffeffbfffffbfbeeffffbffeffffffffbffffbafbffffffefffffffbfeffffeffffbffbfebfebfffeffeeffeffefffffffffffffffffeffffeefffffffbffaffaffffbeefbfffffafbffffeffffefffffffbeffbffffbffffeffeffffbfbbefbffeffeffffbeffffffeffefbfbfefffffffbffafffffffbfebbffffbfffbfffeffffeffbebfffeffbffbffeebfffffbeffbffbfffebfeffffffbefffffeffefffffefbbfbeebffffffffbfeffefbffbffffffffeffeffffbfebfffffbfffbffbeffeffffbffbfffffbffffffffffffffffbfefeffefffffbfbffbffffffefbbffffffffffbbfbffffffeefffbbfffffffbfffafffebffffefbefffbbefffbefbeffffffefffbffffefffbfebfefeffeffeffbffbfffeffffaffbffffffebfeffffbffbebeffeffffbafffffffffefbfffeffefffbefffffaffffbfefbefbffefbfffefbeffafffebbffffffffafbfffbffefbbefeffffffefefffefbffeebffffffeeffffaffbffffbfffffffffbffffffffffbefbbefffffffbffaffbfbefffffffbfffbffffbaffffffffffbeffeefffffffffffffbffeffaffffbeeffefffbffbbfbfeffffefffffbfffffeffeffeffbefffffefafbbfffeffffbffffffeffefffbffffffefbfeffefbffefbbffbfbfebfffbfffffffbfeffefbfffffbebfffbffbffafbfffeffbfffffeffbffffffffffbfefbfffffaffaffbefffffffbffafbfffffffffeffffbffffffeffeffbfbfefbfffefaffeffbfbffbffffefffbeffbffffbfffefffebbffefbfefffffffffbffbfefbfbffffffffffefffffefffbffffefffbffffffeffefffffefffebffffffffbffffefffbeffeffbffbffffbeffafffffffffeffefffbbffbfffeffffbfbfebfffefffefbffffffffeefbfffffeffbebffbffffffffbfeffefeffefffefffffffffffffbfffeffffefffffefffebffbfeffffeffffffffeffbffffffefeffeffffffefbebfffbefffbbfffffeffeeffffffbbffefbfffbffffbffffeffffffbffffeffebeefffbfffffbfefffffffffbffbffbaffbfffffffbffffefffbefffefefffefffbffffffffffffbfbfefffffffbffbf := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask509637 : MertensSieve.bits 509637 = 0xfbefffffffffffffffffbfbeefeefbfffffffffffffffffaffffbeefbefeffefbfffeebfffffffebbebffbeffaffafffffffffefbfbbeffefefbfffffbeffffffffbffeffeffbeffefaffeffefbbfffefbefeffffbffffefffffffffbbebefbeffffbfffffffffbffbffaefffbfebfffbffffbbfffffbefbfffffbfbfefeffbfffeffffffffefffffffbefeefeffeffbeffffeffbffffbafbffbfebfffffbffffebfffeeffffbefffffeffefeffeebfefffbfffbffefbfebfeffffffbbfffffeffbefffffebbffefbbffeffbefffbfefaefbfffffbffffffffbffefffffeeffffffbefffffefffffeffffbfeffefbefffffffbffeffeefffbbfffffeffbffffbeebfeffffeeffffffffefefbeefffbfebffbfffeffbffeffbfbfffbfffffbffffbffbffffffefffffffffffeffffffeffffeefaffefbffffffbffbfffefffbfffffffffeebbffffffffbfffeffffeefbfffffffbffffebffffffffffeffffffffffffffffffbfffeffbefffffffbffefffefbfbefbeffbfbbfffffeffbffeffefbbebefffffbffffffeffeffffafbafffeffffffffffffbfeffffbffafbbefffbffffffffffeffffeeffeffffbffffbfffeefffbfeffffeeffffeffefbffffebbffeffbfffefffbfefffffffbffffbbefffbfeffebfffeefaffffffefeefeffbffeffffffffbefffbeffffbfffeffbffffffebfefffffffffffeffebeffeffbfbbfbffffefbfbbefffffefeffbffffffffeffffffffffffffeeffffaffffffebeffffffffbfbbfbffbfeffffffbbffefbefffffbebbfffffbefeffeffffbffffffffbffffffeebfeffffefbffffefaffffbfffbfbefbeffbffeeffebfeffeffffbffffffebeefffbbfbfffffffffefbffffebfffbeffffbffbefffbefffffeebffffffbffbfbefffeffffeffeffeebfebeeffffffbefbfefffbbefffffffbfffffbffeffbffffffeffffffffeffffeffeffbfffffbfffeffffaffffffffffbfffffffffbffffbfeffffffffefeffffffffbffbfffffeffaffefbffffffafffffbefffffeffefbfffefbfbfffbffbffffbfefefbffffffeffffffffbffbfbffbffffeffffffffebbfffffbffbfbbefffbfefeffffbbffbffffbfefffbeefbfbffffefeffffbbfffffeffbffeefbffffffefeffbfffeffffbefffbfebfefefffefafbfebffffffbffafffffbfffffeeffffbefffbeffeffefffffffffffaffbffbffbfffeffffffffffbffffbbefffbfeffffefbfffbfffffffffebfffbfbeffffffffffffffaebffffefaffefffebffffefffffffffffeffffbefafffffffffffaffffbbfffefffffffbffbfbffbffbfffbfffefbefefbfefffbbffffbffffeffffeffbeffffeffeffaefbeffebfffbfffffbfffeffffffbbffbfbfffeffafffffffbffbbffffbeefffffffeefffbfffbfffffeefbfbfffffbeebefffffbefbff := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask517829 : MertensSieve.bits 517829 = 0xfffffffffbbfffefeebfefffbfeffffefbfffafffffffbffffefeffffffefeefffffffbfbbfbeeffeffffefbffffefeffffffffbfbeffbffbffffffefeeffefffffebfffffbeeffffbebffffeffefbffaeffebefffffffffefffbfffffffffeefbeffffeffeffbebfffffbbefffbeffbfffffeffffffffffffffbffeffeeffebfffaffafbaffbebeffefffffbeffffeefbeffffffbbfffffaffefffffffffffbffbfffffbeffffaffeffffffffeffffffffbebffffffffffffffffebfebfeffffffffffefffffefffebffffebfffefffebbefffffffefffffbfffefeefffbffbfebfffaefeffffbffffeffffffbbefffbffbeffbfbeefbfffffffffffeffbfffeffffeffeffbffffbbfffffeffbffffbfffeffffffefefffefbfbbfffeffeffeffffffffefeebfeffffafbffffffbeffffeebfffeffafffffbfbfffeebfffffbbfffffefbfefffbfffbffffffefafffeffffffbfeffffffffeffffffffffbefbffffffefefffffffffeffffeffeeffffffffffeffffbfefffbfffeffffffebffbbfffffbfffffffbaffbffeefffbfebfffbfffffbfffffaefeffeffffbffbbffeffaeffebffffefffbffffefffffffefffeffeffffaeffffeffffbfeffffeffbfffffeeffffbfbfebfffffffefffbeffffffefafffffbfbffbeebfffbffbfbfffffbeefffffffbffefffffffbbeffebffbfeffffeffffbeffeffffffffffffefbffffbeffbebfefefffffffbffbeeffffaffeffbffeefbffffbfffbffefffffaffafffefffffffffbffffefffbfefbffaefbfbfffbefbfbffbfffffbfffeffffffebefffefefbaffffffeffefeffbfffefffbfffbfbffbffffffefffffaefbefefffeffffbffbffffffffffbffbbebfffaffeffffffeffebbefffbffffefefffffefffffbffeffeefffffeffffffbfffffbbffbfffffeefffbbfbffbffffffefffebfeffebfffeffffbbfffebfffefffffffffffffffffffbbffefbbffafffeffebfefaefeffbfffffeebfefbffbffffffffeffffffeffffeffffffffffbffffefbffbfbffffffefbbffffbffbfebffffefeffffbfffffbbffbfbaffbfffefeffffbffffffffffefffbeefbfffefffffffeeffffeffbffbfbfffbffffbbfffffbfbfffffbeefffffebffbffbaffeffbffbffffffefffffefbffefffffbfbfebffbeeffffffffffbefffbbffeffeffbfffebfefffffefffffffeffbffffbfebffbfefafbfffbffffffefbffffbffffefaffffffeffffefffffbfffeffffffbbfffffffbfffeebafffffbffbebffbaefeffeffffbfefffffffeffffffffeffbffeffbfbffffffffbfeffeffeffffffffebbffffbfffaffefbffffebffffffffffefffbfffbffbfbffffffeffeffaefffffebfffbffbfbffbefffefafbfeffebfffbfffffaffbffffffeffffbfbfefffbfffeffffbbfbfffefffffeeffefffffffb := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask526021 : MertensSieve.bits 526021 = 0xbfbbfffffefbffffffefffffeffeffbffeefffbfebbffeffbefbfbeeffffafbbfffffffbeffefffefbfbffffeffffefbfeffefefffffefffffffbfefffbbebfffefffffbffffffefefffffffffeffefefffffefbfffffffeffffffffffffbefbfffffffefffbfeffffbfbfeffffffbeefffbeffffffffaefeffeffbfbefffffaffeffbfffeffffeffffbffffeffefffbfebfffefffffafbbeffefffffffafffffffbffbfffffffffbffeeffffffbffbfeffefaffbffefbffbefffffeffffbbfffefbfffffbeffebffbafffffffffefffbfefafbffffeffeffffffffebbfbfffeefffbffbffbefffffefffebbffefbfffffbeffbeffefeffffffffffbefbbffffbbeffeffffffffffbefffffefeffffffefbfffefeefefbeffffffffffffffbfbfefffffefbfbeffbefefbafffffbefffffffffffffffbffffffeffefffefbffffffefbfbfebffffefeffaffffbbfffffefffffefffefffffeffffffffffffffffffbfffffbefbbefbfffffffbffbeffffbfefffbfeffffffbefffffeefbffffbfeffeffffafffffbfbffffffbffffbeffffffefbefefffffbffffffffbffeffffffefeefbfbeeffffffbfefffffefbffeffaffbfffebfefefffffeffbeffefffffffefbafffffffbfffeffbebbffefbefffffffffffffbbffeffffffefeefffffffbefffbeeffffffbeefffbffbeffaffeffbfffefbefffbeffffffffbefeffffffffefbfffffbffbfefffbeeffffbffbebeffeeffffbefbfffffffffffffbfffffbfffeffbebbfffffffffffffbbeffffbffefffebbefefffefeffeffffbfffbfffffafffffffbfffbffaefffffeffffbfffffffffffaffbfffeffefffffefefbfffbffefbeffffffebffbfffeefefffefffffffafffffeefffffebeefffbefffffffffffafbeefbffffbbffbfffebbffffbfffeffffbffffffaefffbffffffeffaffbffbfbffbfffbffffffffffbfebfffbffbefbfbffffffafbffbffffffffffffbfffffffbfffaffffbbfffeffffffffefffbeffaffbfbfeffffffffffeffeefffbfeffffffbfffbfffffbeffffefbfffffbbfffffefbbffffbfefbffffffffeffaffffffeffefefbafffffffffeffefeffeffefffeffeffffbfbfffffbfefbffeffffffffeefeffeffffffebffffffbffffffffefbbffffbbfbfeffffbefffffeffffffbfffeffffffffefbefffffbfbbfbeffeefffffefbffefbffffffffbfefefffffbffeffffffebbfffffbeffebfffbffefbfffffbfffeffafbeefffffffffffffeefffffffbefbfbefbfffeefffffffffbffbefffefafffffffffffeefffbbfffebefffefefbffffebffbfefaffeefbfbfffeffffbfebffffffbffbffffbfebfffbfffffbeffeffefbfffffefbbefefbffffffffffffffbfefafbffbffffeffffbfbfefffbeefffffffaffffbfffeefffffffbffeebbffaffeffbf := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask534213 : MertensSieve.bits 534213 = 0xefffffffbfffffffffffbfffffbeffeffffaffbffeffffbffbfefefbfffbffeefeffbfbafbfffeffaffbfbfeffffffbafffffbebbffffbfffbfffffbfffffeffefffffffbffffefbffeffffbfffeefbfbbfffffffbeffbffbefffffefeeffffffbfffefffffeffafbffffebbefafbffbbfffffbffefffffbfbffffeffffffbfeffefaffeffbffffffefeffffbffbbfffeffefbffefffefeffeffffffeffefeefffffffeffbfffffeffefffffbffffbeffeffffffefffffffffffffbefffffefbfbffbffffffbffefbffffebeeffffbffffffffeffbefaffafffffffffffeffbebffbffbfeffffafffebffffefafffffffffefefffffeeffffffffffafbeefbfffebbffffffffbeffffbffaffffbfffefffefffbfffbebefbfefeffbfffebfffefffffbfffeffffefffffffffffefffffffffffbfffffefffffafffeffffbffefbafffffffffefffbffffeffffbffefbfebfffffbfefffbfeffebeefefffffffffffefffffffffefffffebafffffbffffffebffffffffffeffefffffffffbbfbfffaffafbfefffffebefffffeefffbffbffffffffbbfbeffeffefffebbefeeffffffffffbfbffffffefbfffbffffffffffbbfbbeffffffffffefbffffffeffefbefffebfeffefbfbffbffbfffaffaffefffffffffffaffffffefffffefeffbffbefefffffefbbebfffffbeffbffeffffffffbffbffafffffffbfefffffebffffefaefffbfffbfbfebffffffffffebffffffffbafbbffffbaefffffefffbefffffafffffffbfffeffbfffffffffffefffffbefffbfffbefffffefbefffffffbfffefbefeeffffefbbffffffefbfffffbeffefffffeffffffbffbffbbffefffffbffffbffffffeffffffffffffffffffffeffafffffbeffffffbbffbfffffbffffbeffeffffffefeffefffffefbfeffeffefffbfefbffffffffbffbfbbfffffeefefbffbbebfeffffbfffefbffeefbefeffffbffffebfefeffbffffffffaffbffaebffffefbffeffaffffbffbfefbffffbfffeffeffefffefffffffaffffffebfffeeffffbffbffbefeebaffffbfffbfbffffeffffeefffffffbffbfffefbebefbfffffbfefbfbeffbffafffffffffebefffffffbfebffbfffeffafbffffffbeffffbfbfffefbfefffbaffffbfffffffffbfffebfefffffffffbfffeffbffbffefbfefffbfffeffeffffbeefbfffffeffbfffebfffefffebfffffbfffefbffbffbfebeffffffffffffffffffffbfbbfffffeffafffefffbfffbffffffefffffffbefeffbffbffeffeffeffbfbfffeffbffffbbffffffffefffffeefffbeffffffffffbffffefbffbfbfefffffefbfffffefbfebffbfffbffbffffffffffffffbfffffffbfeffffffbfebfebfefaffeffbeffffeefbfffefffffeffffbffffbfffeffffffffbfbfffffbbfffffffbbfffffeffefbffbbeffffbffffffeffeffeffff := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask542405 : MertensSieve.bits 542405 = 0xffffefffffeffeffbffbefffffeffffaffeffbebffbfffffffffffbfeffffbffeffffffeffffefbbffbfffffeffffffebffffefeefefbfffffbfebfefbffffffffeffaffefffffbfffebffffffaffffffefbeffffffbffffffbefffbfffffbefffeffffffffffffbfffaffaefffbefbeffbfbfffbfffefaffffbfffbfffebfffefffebbffefffefafbffffefffffffefbffbfeffffbffbffbfffffffffffbfbbefffffffefffffaffbfffefeffffbfefffffebaffeffbfffefffffefaffffbfffffffefffbbebfefffffffffbeeffffffbfffefbeefffffefeffbfbeebbffffffffbfbffbfefeefffffffbffbffefbfefbffeffffffefbfffffffbffbffbfefffbfeffebfffaffeffffffebeffeffffbeffbfbefffffbfbffbbfffffbffeffffbffffffbffffbbffbefeffeffeffffffffeffbffffbeffffbfefbffeffbffffbffffffffbbfffffffffefbfffffffffefeffeffffbfffeeffffbfbafffffffbfffefbfefbefffbfffeffffffeffffaffffbbffbfbfefeffffbeffbfbffffefefffeffebefbbffbfffeffefffffffbffaffbffeefaeffffffffeffffeffbfffebffffefeefefbffffffffffffbfffffffbeffeffffbeefbfffffefffffefffefffbffffffeffbefffbbeffffbfffffeffeffefbbfffeffffffffffffffeffffffffffbfbffbfeffffbfbefbfeffffbffbffaefffbffbbffefffffbfffffbffefffffffbffbefffffffffffffffffbfffefbefeefeffffbeffffffefbffffbfeffebefffffbffeffffbefffffaffeffffffefaeffffffbbffefbfffbffafffeffffffffffbffbfbeeffefbffbeffffeffbffffbfffbffffffffafffefffbfebfffbfbffbfffffffffffbffbbeffffeefeffbffffbffffffafbfefbefffffefffbeefffffefbefeffffffffffbfffbfffffffffefffffffffbfffffbfeffffbfbfffeffbffeffffffeffffaffbffefffffeebfffffbefffffeefbffffffffffbfffafffffeffbfbfffbefefbafffefffffefffffefbffeffeffbffafffffffbaeffffbfffffffbfffbffffbbffeffeffffffffffffefbfffffeeffefffbfefbffffbffffeffffffbbfffffefbfffffffffffffffffffffaefffbffffffffbfffffbfffbefbfffffffbeefbffeffaffffffffffffffffbfefeebeeffffffbbffffffffeffffbfeffebbefbffaeffefffbfffbffeebbffeefffffffffffffefbbffeffbfbfebffffeffffefbbefefffffffffebffbffffffefbeffffffffbffffffffbffffbfffffbbffffbeefeffffffebbfbfebefffffbeffefefbbefffbfffbfffffaefefbbfbfffefffeffffffffefffffffeffaffffbffbefffffffbbfbeffaffbffffbfffeffffffffefbfefffffefbfbffbfefffbfffffbbeffffefbbfffffffffffffffffffbbffbfbffbfefbffaefffbffffefefbfffbefffbefffffffff := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask550597 : MertensSieve.bits 550597 = 0xbeffeffeffffffbfeffffbffffbffffeffffbffeffffbffbffbbffffbffffebeefefffffafbffbeeffeffffffbbefeffeffffffffffffffbfffffbffbfffebfffffffebfeffffbffefbeffffbffbfffeffbfffefeeffffbfbfffbffefffffeffeffbffffbefffffffffffffbfffffbbfbffffffaeffffffbffffffaffeffbfffebffbaffaffefffffefffffbfbfffffbefffffbffffbfffefbfffbffeeffebffffffefbffffeffefbffffbffffffffffefafffffffbfefeffefbffffefeefeffffffffffffffeefffffffffbeffffffffffffffefbfffeffafffefefbeeffffbffbefffbfefffbbfbfffffffffbfbfffbebfefeffffbafbffbeefeffefbfeffefffbbffeffeebbfbffffffbffbffbffeebeffffbbefffbffffeffffbeffffffbbeffffbfffefffffffffbbfffffefffffbfbffbbefefffffeffbebbefeffbffeffbfbffffffeeffffbffffffffbffffbfefffffebfffbfbeffbefffbfffffffffbffeffeffbffffffffffffffbffeefffffebbfffffffffffffbeffffbbfffffffbfefbfbefbfefffffeffffffffffeefffffffeffffffffafffffffbbfffffefffffbfffebffffffbfbffffeffeffefffffffbefefbfeffffeebffffffeffeffffffffffbfffffbfffffbfeffefbfbeeffffeffaffeffffffffffffefeffbfbfffffbbfffffbebbffffffffefbaeffeffffbefaffbffbfbefbfffbffffbbfbffffefefbffffebefbfffbffefffffeefffffffffbbfffffbffffffffbffefbfffbffaffffffffbefffffffbffffffefffbbefffffefbfffffeefffffebfffeffbfbbffffffefefbeffffffebfeffffffbfffffffefbfbffbfeffffaffffffeffebfffeefffffefbfffeffeffffffbffffeffffeffaffbffefbfffffbbffbefffbfffefbfffbffffbeffafbfeffeffefbffeffeefbfffffeffbfbeffbfbefffefbfffffffffefbffbfffffffffefffffffafffffeeffffeffffbbffeffeffbfffeffebfffbffffbaeffffefbfefbfbefffffefffffbfbffbffffffffffffeefffbffbbfffffbffbefeffeffefffebbffffffefaffffbffffebbfffffeffffbfefffffffffbffffefaffffffeffffffbbffbfffebfefeeffffffffffffffffaeffffbfffffeffefffffefffeffffbffbfbbfffebffffefffffefffbfffffffffeffbffefbbffafffffffbefbfffaffffbfeffffeffffbbfbfffefbfefafffffffffffeffefbffffffeefeffffffefbffeffbffafbeeffffeeffffbffbebffffffffffffeffbeffeffefefbbffffbfffbffefbffffeffffbffffbfffbffffbeffffbfffbfbfffeffbffefffeffeffffffffebffbffbfeffffbffffffffbffefffefbfbefffffefbbffffbffbfefffbeeffffeefeffbffaffffffefbfffffffffebfffaffbfffebfeffeffffffbefffffeffeefffbffbffbfffaefbffefbfeffebff := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask558789 : MertensSieve.bits 558789 = 0xefbfbfffbfbffffffbfffffffbffffefbfffeffefffffffbfffffbfbffffefffbaffbefeffeeffffbefffbefffeffffffffffffbbefafbafffeffffffffffffffffeffaefaffeeffffefbfffffffffbfffffbffbffffffffefffffffffebbffeffeffffbbeffeffeffffbfffffbeffeffeffffeffbfffffbffbffeffffbeffffffffefffebfebfffafffffbfffeffffffffeffffefbfffaffffffffffbbfffffffffffffbeffbffefffffeffbefefbffbbfbeefffffffafbbfffefbffefbffbfeffebfffffffebbebfffeffffbeefffbfffbffefbfeffebffbeefffffffbfffefbefbfbffffffffbfffafffffffffeffefeffbfffffefffefefbbefffbffffefffbaffffbfffeffbffffffffffbffffffeefffbfffefffffffffffeefafffffbfbbffeffbfffffeffbffeffffffffffffffeffbfffffefbfffffbbefeffeffffbfebeffbfffebbfbefffffffbfefbebffffffaffefbfffeebffffffefbfffeffbffefffefbfffffbefeffffffebfefefffffeefffbffbfffbfffffbffeefffffffeffbeffeffffbffefbfefeefffffffefffffffbbffffbffffffffffffffbeffffffffbfffffbefbfffffeffbfbfffffffffaffefffffbfffebffffffaebfefffffeffffafbfffffbfffffffffbfffffbffefffffffbffffefffbffffffeeffffbffaefffbfffeeffffffbbebfffeffaffeffbfbefbbffefbffbffffefeeffffffbffffffeffbfffefffffefeffffbbefffbfffeffbfbbebfffeefbffbfffebfefefbfffaffafffffffffeffffafffefefffeffffbffffbffbeefefbbffffffffeefaffeeffffefbeefbfbfebffbffffffbffffffefeffeffefffffbfffeffffffbffbfffffffffffbffffebffbfefffbfeffefffbbffbfbeffbffffffffffffffffbfeffffeffeffbffffbeffffffeffffeffbffffffffbffffffffffffffbfbfffffffffbebffffefeffffffffffffffefffffbffffbfeffffeffeefbfbffbbffffffefbffffffeffffffbffffefffffffbfbfefeffeffffffffffffefaefbfbbfffebefbffffffbfffffffffefeffffffebfefffffffeebbffeefbfffffeffbfffffbefffbffbbefefffeffffbfffeffefbffefffeffebfffeeffffeffffffffeffbfbffbffffffaffaffafbffbffbfeffffffbfffefffffffffeffefffffefbffaeffefffffffefbaefbefefbfffbffbebffbfeffefffbeefbffeefaffffffffbfbfefbeffffffbfffefbffffffbfffffefbeffffbeffffbfefeffbfffefbfbfffeefffffffbfbffffffefbfffbfbefbfffeffbebfffffffefbfbefbfeffebeffefbfebffffffbffeffbfbffffffefffffeffffffebfefffbfffffbefffeffffeffffbfffbffbffaebfeffffbeffffefffffeffbfffffbeffefffbfffafffffffffffeeffffbeffffffbfefbfffeffffeffeffefbfffffffebfffffffeb := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask566981 : MertensSieve.bits 566981 = 0xffffefffefafbbfffffffbfefffbfeffffefbfffefffffffffebbffeffbeffffefbfffffffffffbfffffffffeeffebfefffffffffffefefbbffbfbbffbffffbfefffbffbbebffffeffffffffffffbbffefffffbefeeffefffffffffbeefbffffffeffffefbbffffffffffffebfefefbbfffeffffffffffbfffeffffaffefbafffffffbfffeffbfffeffffeffbfffebffffffbfffffeefbffeffeffeffffffebffbbffbfbffbbfffeffefeffffbbfffffaeffffaffffbffffffbffbeffffffbfeffffffffffffffffaffefffffffbbffaffeefbebefffefbffeffffffeffffffbbfbffffffaffeffeffffbfeffefffbfefbfffffffffffeffffbfffaffffbfffffbfebefffffffffffffbfffbfffffbffefffffefbffffebefbfffefbffffebffbfffffbfefbefefbeffbffeffffffefffffffffbbfbffbbfffffaebffbeeffffeffaffbefefbfffeffffffebffffefbffbfbfeffeffefffbaffffbffbffffffefffffeefaffbfbffffeffeffffbffbeffffffbfffffbafffefffffefffffffbffefbfffefbbebfefffbbfffffffffffeefffffffbefffffffbfffffeebbefefbefffffffbfebfefbeffffbfbfeffffeefeffbffffbefffefffffefffffffaffefbbffffffffeffbffffffffffffefbfffeffffefffffeffafffeffefffffffbfbfeffffbfffffbffbefffffffafbffbfebffffffffbeffbffefffffbffbefffffeffffeffefbffbfffeffbfffffbebfeffeffffbfffefffbefffffbebfebffbefffffffffefffffffffbeefffbffffefffbefbbfbfefbefffffeffefffbfffefffefbfbfebfffaffafbbffffbafffffffffebefbbffaffbefffbffffffeffffffffffffffffffeffffeffeeffffffbfefeffefffffbfbfffeebfffbfbafbffffebaffefffeffeffffbfffffeffffbffbfffffbeefbfffefeffbfbbfbffbeeffefffffebffbffbfffaffeebffffffbffbfbbffffffffbefefbbfffebefffffffffeffffffbfeffffbfffefffbfffbfbafffffffffffefffffffffffaffffffffffffebbffafbefffffeefeefeffffffebfffeeffffefbffffffaefbffeefbfffffeffbfbbfbbfbfffbfffffffffefefbbffbffefffffefffffbfbfffbffffbbfffffffbffffffbffeffbfbffbfeffefffbfffbfbfefffffffeffffffefeffffbffffffeffeffbfffeffebeffffffffffbbffffbbffefffffffffffbffeffbefffffffeefbfffffbefeebfefbfbfebfffefffffeffefbffffeffffefffefbfbffffefbffbfffeffebbefffffffffbfffaefbfbefffeffeffffbfffefffbffbeffbffeffffbffffffefffefbebeeffffbfffffbefffffffeffffffffeebffffffbefbffffbfffaffbfffffffbeffefbeffbffffffffffbbfffffffffefffbefffffffffffefffffbebffffffffbffffefffbeefffffffbfbefffffbfffebffbffbf := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask575173 : MertensSieve.bits 575173 = 0xfffbffaffffffffeffbffbefbfffeffefefffefbfffefeffafffefbfbffbfffffffffbfffefffffffffbfebefbfffffbfebfeffeffefbfffffffbffbffffffbebffffffeffefffeffefefbafffffefbbebffffffaffeffffffefbffffbffffefffbfffffbffbfefffffffaffbffffffeffefbfffefbfbfeffffbffffbffffffffffffaffffbfffffffffffbbffffbaffefbffffefefbeeffffaffffbffffffffbfffbffffffefbffeebffffffaffffffefbeffffeffeffffbfffeefbefffbffffeffeffefffffefbffeffbffaffffffebffbbffffbeffffbffffeffffafffffefffefafffffbefffffffbfffefffbffbbffeffffbbffefffefefffebfefeffbffbfbfefffffffafffffaffbfffffeefffbeebffffefbeffffffffebfeffffafffffbeffefffffffefffeffefffffffbffbfbeffeffaffffbffbfffbefffffefbffefbfffffbaffbffefffefbfffebbffeffbfffffbebbffffbffffffefffefeeffffefffeffffffbfefbffffffffffffefeffffffebeffeefffbbfbffffffaffbfffffffbffffffbffbeffefffbbffefbffffffefffffffffeffebffffffffffebffffffeffffbfefbeffebfffffffffbffeffaefeffffbffffeffffefffffffbeffbeffffefffefefbeffffffeffffeffaefefffebfffffbbffafbffffebeefeefffbafffffefffffbfffefbfffebffffffbfffffefffffbffffbfffffbaefffbbfbffbfffffffffaffffbffffffffffefffbefbfffffbbfffffefffffffbefbffbffffffbffaffffffffbeffffffffeffffeefffbbffbebfffbffeffaffffffffeffeffbfffefeebffffffbffbfffffeffefbeffbefeffbfffffeefffffefbefefbeffbffeffefffffbffbebffffffbfbfeffffffbfefaffafffffffbfffbffffffffeefbffbfbfffbffffffffbffefffffefffefffbfffbeffefefffffffffebffffeffffafbffbfefeeffffbefbfffeffffbffeffbfbfffefffffefbffbfffefffffffffffffbffffffaffbffeffeffefffefffbffbfefafbeefffffffbffbfbeeffffffbffffffaffbfffffbffafffebbffffbffffffbfbffbfefffffffbfffffefffefefffebbfffffbffbffefffeffebbffffbfefffffebffffffeffbfffefbffffffffffbfefaffffffffffffffffffffffbbfffeffefefbbfbbeffffaffefbefbffbfebfeffffeefffffffeefffffebffbeefbffefffeffffeefefffffbfbbefffffffbffaffffffffefffffbefffbefbffffffffffffffbaefbfbfefffbffbeffbffffbffbfffeffefffffffffefeffaffbeffefffbfffffbafffeffffaffffbfeffffffbbefeffefffefffffffbffefffffefbfffffbefbffbeeffefeffffbbfffffbffbfffebfebefffefbffffffffeffbffeffbefffffffeffaffefffefffffffaffbfffffffffefffbfffffffffeefafbffbffbeffbfffffee := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask583365 : MertensSieve.bits 583365 = 0xefffffffbffeffbffffffeffefffbffbfefffbbffbffeffffffffefffffafffeffebfffbffbfffffefffffffffeffeffffafffffefbbffefffffaffbffbefefffffffbffffffffbbffffbbffffffefafffffbfffffffbffffffbefffbeeffeffffffbfffeffefffffaeffffffffffeffaffbefffbfffeffbeffffefbfffffbefffffffffffeffffffffffffefbfffffbfbfefbefffbefffffffbaffefffffffbfebbffbfbffffffffbefffffffbfffeffeefafbbffffbffffefbffffffefefbefffffeeffffffffffffffeffeffffbfffffeeffebffbfffeffffbbffeffbffffbbebfffffffefbffffffefffffffffbbffffffebeffbfbbfffffffffffafffffbffeffeffbfffebffbffffffefffffbffffffefeffffbbffffffefafffefffffffaffbffbefbfffebeffffbbffffbfffbffafffffffffffbffefffffbeffffffffffefffffeebeeffffffbfffeffeefbfffffffbffbfffbfffffffbefbfffffbeefffffffbffffbfefbfffebeffbffbfffffffffffafffffffffefeefefbfeffeffffbfffffeefffffffbefefbffffebffbffffffffbfffefffeffffefffebfefffffffbfbfffeebfffbffffbfefefffefffbbeffeffffbeffffbfbffbfebfffaffbffbffefbffffffefbbfffffbffefffefbffefffffefffebfffeebfefbffffbfffefbfefeffbfffffeffaefffbbffffbfffbffaffbefbfbefffefffffefbfbfffeefeffeeffffffbeffbffffffefffffffffbeffbeffebbffffffffffbfffeffeffbefffffefbefbfbeffbefffbfffffbeebfffeffeeffffffffebeffeffbffbeffebfefbeffffffbffffefeeffffbebfefefbfffeffffffeffffbffbfffefffbffbfffffffebbfffefaffeffefbbfffffafffffffffebefffffbfbafffffeeffffffbfffbffffbaffefffffffbfefeffbffeeffffffffefffffefffffeffffffffefbfbfefaffbfffffbffefbfefbffeffffffeffefeffffffffeffffffffaebffbfefaefffbeefbebfffffffffbfbffbffffefefbeefbefffffffbffefbfffeffbfffffbfffefefbeefeffffbbffffffefffbfeffffffbeffffbefffffefffffbfbfffbfffffeeffffeefffffefbffaffffbfffffffeffffbffffffffbffeffffbffbefbffffffeebfeffefaefbfbbffffbeffeffbfbffbffffffbefbffeffffbeefbffefffffffffeffffaffeffbffffffefffbbefbfbefffefffbbfffffffbeffefbbefbfffffeeffffffbffffeffffffffebfffffbfffeffefbffbefbfeffffaffbffffffffffbffffebfffeffefffffffffffbffffbfffbffeffeffffffffffbfffeffffbeeffffefbfffbffefbfeffefffffffeffffffefbfffffbeffebeffefffffffffeffefbefefffeffffefbffffffefffffeeffefbffffbfebeffbfffffeffffffffbefffbbfbfefeffeffeffbffbfffffeefefbefbfffffb := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask591557 : MertensSieve.bits 591557 = 0xfefffffbeffebeffeffffbeffffffefbffbfbefbffffffeffbffeffffbefffffbffafffffffffffeffbefbfbffbbffbffbeffeffffeffefbffffefefffffbfbffbfffefffffbffffffffeebbfffffefffffffbfffefffffffffffaffefbbffbefefbbffffffebffffffbffbfbeffbffeffefffffeffffbfefbefffffffffffebeffbffffbbeffeffefafbffffffeffffffffffbffffffeeffffffffeffebfffffbeffbfbffbefffffbffbfbfefbffffffeffffffbbfffffffffefffffffeffbfffffeebfffffbbfbfefffbbfffffbefffbffffefaffffffffffbfefffffffbffffffffefbffffebfeffffeffbeffffefbbffffbffffeffebeeffffffffffffffefeffaebffbfffbefffffefffbeefeeffffbfbffbfffafffffefffffefffffbffeefffbfebbffbfbfffbefeeffffffffffbefffffffafbfefffbfffeffefffffffffefffffffeebbffffffffffffefffbeeffffbffffffffffbbefffbffffefeebfeffffbffffbfffaefbffbfbfeffffbffeffbffbfffefeefffffffbffefffffafbfeffffeffbffbffbefbfbeefffffffefffffffbbffeffffffefffffffffbbffffbffffffefbffffefffffefffffebffbeffeefbfbffbbfffefffffffbffffbffbbfffffafffffeffaffeffbefbffffbeffeffffffefffbaefafbbffbfffffffffffeefffffffbfffffeffbeffffffffffffffefefffefafbfffbffffffffffffffbffeffffffffafbffffebfffffbbefffffffeffffffebfffffffffbffffffebeffbffbffbefffbeffbffbffefbbefefbfffefffffbeffffafffffafffebfefbeffffeefbefeeffefffbaffffffffbffeffefffebefffffaffefbffbfefffffffeffffffebaffffffeffffefffffaffbfffeffeffeffffbffbffeffeeffffefffffffffefafbffbfffeffaffbffbffffffebfefefffffbeffffaeffffbffbfbffffffefffebffbffbaffbffffffefffbfffbfbfefffbfffaefbffeffffbffbbffbffffffffffbfefffbffffffefbfefeffffbfffefffffffbbffffffefbffbffbfffffffffffffbeffbfffffffffffffbbfffefffffffffbbefeebfffffbeffbffeffffffffbfbffbefbeefbffbefffffebfffefffffbebffbeffffffefffffffafffffeebfffeffeffbfffebbffeebfffffbbfbffffefafffffbfbffffffaffbffbfbfeffeffffffbfefbffefbffffffbfbffbfffbeffffeeffefeefbfffffffffffefffffffbbffbefffbbffffffeffeffffaffefbbfffeffefeefeffefffefffbfffbffeffbfffefbffefbfebffffeffffffffebbfffebfefbfbefffeffebbffeffffffefffffefffbaffffbfffffffffeffffbeefefffffbffbffeffeefefffffbfbffffffffffefffbffffeffffffffefefbeffffbfffbefffbffffffffbffbffffefafbbffffffeffffbfffefffbeeffffffbffbfebfffefffffb := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask599749 : MertensSieve.bits 599749 = 0xbebfeffeffffefbffffeffffbefffbbeffffffffffeffffffefffbaffffbefffeffebfffffffffbfbffffffffbfefffffeffffbffefffffefffffbfffffffffffaefffffffffffffbefeffafbffbfebafffffffffefeefffffffbefffbfffeffffbeebbfffebfffeffeebfefffbbffefbefffffffbaeffffffbbebfffbfffffbefffbffffffffbeffbfbeeffffbffffbfffffffefffbeebfefffffffffffefffbeefbffffffffbfffebeffeffbffffbffbeffffbeeffffffffffefbfeffffefffffffbbffffffffeffffbfebfebfffffffffffbbeffffbfffffffffefeffffffffffbfefefffffbfbaffffbfefeefaffefffffefbfefffffefbffeffeffefffefbfbefbeffeffeffffffeffffeffbffffffffffffffbffbffffbffffffffffebfeffefefbaeffffefffffbfbfebffffefbeffffefbffffffbffffffebfefefffffefffffbffeefbffefffffffffffeefeffaeffefffffffbffeefbffffbfffffbeeffffffffffaffffbffbfffaffeffefffffefffefeffbfbfffffbfffffbfffbebffffefefbbfbfefffbefffffbeffffeebfffbffaffffffffeffafffffffbeefbffeffbffffbffbfffeffeffffffffeeffffffffefefbfffbffeffffbfefeffefbbffffbeeffffbffeffffbfefbefffbfffffffeffffbfffffffffffffffffffffffeefbeffffffbfffefbeffefffffffffebfefbfbaefbebeffefffffbebbffeffeefffffebfeffefeffeffbfbffbffffffeffbffbfffffeffffbfefbffffffffefbeeffeffefaffffbfffbffffbfefffbffbffffffeffafffffffffefffffffbfbffffffbfffffefffffffbfefefbffbfffefffffefffebffffffaffbffefffffffbfffffbfebffbfffbefbffffbbfffeffffeffffbbffefbffffffbfbfeffffefffffbefffbeffbffeffeebffffebfefffffffbfbffbeffffbeeffffffffffbfbffffefeffeffeffafffefefffffbffffbfeffffbeffffffbfefeffeefaffeffffbfebfefffffefbeffffeeffffbfffffeffaeffffffbffbefbafffffeffbfbeefffffffffffeffefeffefbfffffffffbefefbfefffffeffffbfbbefbefffffffbfbbfbbffffffeffffeffbfffeffffbffffbfffffbfffafffffffffffaffffffffbffffbffffffefbffbfffbffbffeffffbffffeffffbefffbeeffefbfbfffbfbffbeffbffbffbefeebfffffffffbffffbfffffffefffbffbeffffbafbfefffffffffbbeffebfebfffbffffffffeefaeffffefffefefbbfffffffbfffffffffbfffffbfffffaefefffefffbfffeffbfbffffefffffefeffeffffffeffefffffffbfffefbffafffeffefffbafffffffbbebffffeffffafbbffeefbffefffffbebeffeefffbfffffffebfffffffffffffefeffbfffebfffeffbfffffffbffbeffbfffffbfffebefbffffffbfbffffeffefffbffbffffffbffffbbffffbff := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask607941 : MertensSieve.bits 607941 = 0xeffefbfbfffffbeeffffbfffffbfffffbeffffffbffffefefffffbffbffffbbffeffffffffeebefffffbeffffefbeffafbbfbfeffefffffffafffefffffffffbeffbfbffffeffffeffffbfffeffeffeebffbefffffeffefbbffeffaffeffbffbfffffaefffffefffbfeffffeffbeffffeeffffffffffbfffffeffbffefffffffbaffffffffbffefbfffbffbffffffffaffffbffffffffbfefefffeffeffffbffafbfffbffffffffffffefffbeefaffeffefffefefbbffbffaffffbeffbefafffffffffefaffffbffbbfffffbffffbefffffffffeffffeeffffffbfeffffffffffeffefffffeebffbffbfffffffffffbffffffffbaffbffefbbffefffeffefefffffbfbffbfeffffffffffbeffeffebfefffffffffffffbffefbffffeffefeffeffeefbffffffffffbbffbefeffffffffbfffffefbeffbffeefffffebfeffffeefffbfeffffffbfffbfbefffffafbffbbebffbefffffffffefffbbeffffefffffffffefeffbffbffefbbffaffbefffbfefeefefbfeffeffffffffffaffffffffeffeffffffffeebffffffefbbffffbfffefbfffffffeffefefffefbeffffbefaffefbffffffbffbffeffbfbeffffffffbfbffffefbefffffebffffefbffffffeffffffffffbffefffeffffffffffbfffffffbeffffbeebffffefeffbffaffbefffffffffbbffffffefbefffffeffefeeffffeffeeffffeebfffffbffbbeffefaefffbffbffbefffefeffeebffbffbeffffbfffbfbeffffffffaefbfffffaffbffffffffefffffefffffbffefffffbffefffeffffeffffbfffbfffffeefafbffbfffffffefffbfffbfbeefefffffbfbfffeefffffffffffffeffbfffffeefffbfffbeffffffffffefbfffeffffffffffbfefbfffebfeffffeffaffefffffefbfffbfffefffffeffefffffeffebefffffbffaffbfffebbefefbefffefffbaffffbffffebeffeffffbbfffefffbeffbffbefffbffffffffbbffbfbeffaffffbffffefffffffeffeffbfbfeffefeffffbffffffffffffbfbbfffffeffeffbfbffffffbffeffaffffbefbfffffbeffffffffbfffffffffeffffbfffffffbfffffffefaffbfffffffffffefbfebbffffbfeffffbffffffffeffefbffffebffffefbfbfffffffefeffffbfefffffffefffffaefbebeeffffbffffffefefbfefefbfffbfffffeffffbefffefffbbefbffbeffebffffefffffefbfffefbefefffeffefefbeffeffbffffbeffbffefbffffffefbefffffbfbbffffbbffffffffffbfebfefffffefbefffffffffbaffbffeffbefbfbffbffbffffffefffffbfbfefbeffffffffefefffefeffbeffffefffffafffebfefffffffffffffbebffffefffbffbffbffffffafbffbfefeefbffaffaffbfbffffffffbafffffeefffffffffffffefbfffbffefffefffbfffafbeffffbfebffffffffffffeeffffbfffebfffffbeffbff := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask616133 : MertensSieve.bits 616133 = 0xfbebfffffffefbffbfbfefeeffffefbbfbffffffbffeffbefffbffffefefffffbfffebfefbfffffbfffefbefffbeffbffeefbffffffeffebfebfffbffbffffffffbfffffffbbfbfffbffefbaffffbfffaefafffeffefeffeeffffffbffffffbfffffefbfeffffffffffefffffffffefbfbefffefefbbffffffebfefffbeffffbbfbfebfefafffffffffeffefffffffffbfffffffffffffffbffffffffbffafffeffffbefefbeffbffffbfefffbfffbfffffeffeffbfffeffeffffffffeffffeffeeffffffbffffefbffefffffffffefbfffffafffebefbbfffffefbfeffebfffeffbeffffeffaefffffffffffffbfffffafffffffbfffbffeebfffeffefffffeffffffebaffffffffffffebfeffffafbfffeefbffefbffbfffefbfffafbfffffbfeffefffbfffffffffeefffbfeffffeffbffaffffffffeffefffffbffffbfeffefeffbfffeffffaeffffbfbffffffeffaffafbffffffbfffffffffefffbefffffffffffeffeffbfbffbbfbffffffeffffbffbefbbeffffefffeffefffffffbfffebffbbeffffffffffffffffffbbeffffefffefffbfffffbfffbffaffeefbfbfffefffffeffbffeeffffafffffbfffeffffeffffbbefeffffffffeebffbfffbffbffefffffeeffffbfbeffbfbfffbffffbfffffbfebeffeffffbffbffbfffbfffffbeffffeefefffeffefeffbefffbbfbffffeffefbfbeffffffffeffbffaefbfffffeefffbffbfebfffffffffefbffbfffffffffffbfffeeffffffbbffbebffbffffffffffeffeffefffffffbfffefeffbffbebbffefffffbfbfeffebffffffbfffefbeffeffeffffffffefefbbffefbfeffeffffbeffffffbfffffffefbfffffffffffffffffefbfffeffbfffffffbfffeefbfffffaeffefefbfffffffffbfffebeffeffbffffbffffefbfffffffbffbeefffffefbfbfebfefbffbfbffffffeffefffefffffffbffeffaffbefeffbfffffbfffffffffffffffffffbffbbfffffbfbffffffbeffffbfffffeebeefbffbffbfffffeffefffffffffffbfffffafffefefbffffffefffeffebfefefbffbfefffbfffaffeefffffebffffffbfffffeffefffffffbffbffffffffbffffffeefeffafffffffffffbffbfbbfbfffffffefffffffbfbefffefffbfffffbfefeffbffeffbebffffffbfbaffbfbeefeeffffefbbffffffffffffffbfbfffffffffefbfeffefffffffbebbffefbfffeffffbfefffbfffefbbfffebefbfffbfffeffffeeffefeffeebfffffffffaffffffefefbfffaffbffbffffbfeffffbebffbffbfffbffafbffffffeffbfbfefffffeffeffffefbffffefaffefffffffbeebbffeffefffeffefbefffbffffffeeffffffbbfffffffffefeffbfffffffbfefefbbefbeffefeffffbbffffbefffffafffebbffffbeffffffffbefefbfffeffefffeffffbffefbbfbbfffffeffaffeeffebf := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask624325 : MertensSieve.bits 624325 = 0xfffaefffbfefffbffbffffffffffffeefeffbfbfebbfffebafffffafffffefbfefbffffbbeffeffffeffffffffefbeffffbefffeffebaffffffeffeffeffffffffebbfbfffffffffefbbffeffaffefffffbebefbbfffffaffffffeffffffffebffbeffbefbffffffebffbfffffbfffffbefffefffbeefffbfeffefafffefbffffbbffaffaefffffeffffeffbfbbfffffeeffffbfffffffbfffbfffebffbfebfffefbffffffffbeffbffeebffbeffeffffffffffffffefffffbfffffeffbefffffffbfffffefffffbfbbebefffffbfbffffefffbbffffbeffffffffffffffeefffbeefeffeffeffffbffffffffffefbffeebbeffffbffffffefaffffffeffefefbfffbfffeffffffffffbffffffffeefffffffbffbfbfffeffffbfffbfffefffffffeeffeffebbffbfffffbffffbeffffffffbfffffbffefbeffffffebfefffbfffffbfebeffffbafbfffeffeefffbfffffbffbbfffffbefbffffbbefffbffbfeffebbffffffefffffffbefafffebffffebffffffefffffeeffffbfbfffbfffeffffeffefbfeffffaffbffffbfebffffffbffffffeffffbffefbfffffffffbfffffefbffffffbefffffefffffffefffffbffffffefbffafbeeffffeffffffffafffefeefffffffefffeffffefffffbfbfebffbafffffaefffffffeffeffbffbebefffffbffffffffffffffbfbffffefffbfffffffffffbefbfefffffffbffffbbfffffbfbffbeffbefffffffffbfffeffefffffbefffffffbffaefbffeefbffbfffffffbffbffffffeefffffffbefaffefffefefffffffffeffefefbbfffffbfbfeffffffffffbfffefffffffbffafbbffefffffefffeffeffeffffffffefbebfffbeffffafbfffeffffffffbffbefffffffbffffbfebffffffefffeffffffffffbfbafffffeeffffeffffffefefffffaffefbfffffbfeffffefbffffefbfffffbfbffbfffeffafbfebffbfffefffffefffffffbfffffbbefbfffefeefffffffbfffffefffffeefffffeffefffbffbfeffefeffffbfebfefefbbffffbfffffffebaefaffafffeffffffffffbefffbffffffeffeffffffffbfffffffffffeeffefffbfffbefeffbefffffffffffffeffbffbfffffffbeffaffeefffbffbffffffeeffffffffffffbffbfffefffffaffeffffbfeffffffbbffbffeeffffffbffbfefffffefbffbfbffffeffefffbfffffffffffffffaffffffffaefffbefbbeffeffffafffffffffffbffeffeffbfffefbeffffffbfffffffffeffeffffffebfffbfbfffffbffbfffffbbffbffefffefbfffefffbffbeffaffffffffeeffffafbfffbfffffbefffffeffffffbfefffbeeffeffffffffffeffffffffffffffbfbbfbfeffffefbefbbfffefbfffffefbbeffebfffffbfffbfffefbffffffffbebefffeffffffffebfffeefeffeffbfbfebfffbfbfffffbfffeffbffffffffffbfffaf := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask632517 : MertensSieve.bits 632517 = 0xffffbbfffebbffeffffbfefefffffefbbfffffffffffafffffffbfffbefffbeffffffffeffbfffffffffefbffffffeffffffbbfffffbffbebfebfffafbbfffffefffffffbfebffbffbeffeffbffffffefeffefbbffbfbfebfefffbfffffbfefeeffffffbbfffffffffffeebffbeffffffffffffffffffeffffbfbffbeffaefeffafbfffffbfefbffffffebfeffefbfbfffbffefffefbfffebbffffffffbffbeffffffffffbffffbfefffffefeffffbbfbffffffefbaeffffffffffbffffffeffebfefbfbefffffffffffbfbffffffeefbfffffffbbfbefffefbffbfffffeffbffffffefffffffeeffffbffffbfffeffffffffbfffffffffffaffffbfeffffefbffffffeefeffffffffbefffbfffffffffbfffffeffefffffbfbefffefbfbffffffffffffbffbffbffffbfefffbfffffffefbffffffefffffffefffffafbfebffbfffffbeffffffffeffffbbfbbfffffbffffffffffffffffffffaefffffeffffffbfefffffffeffaffefffffffbaffbffffbffffebbefaffbfbffffeffefffffffbffffbaefffffefffffffbffaffbefffbfeffffbfbbffbfffffaffefffffffbfeffffeffaffbebfeffefbfbefbffffffbffeffffffebffffffbfbeffffbfefffffffeffffbefbfffffffffffffffaefffbfffbffefbfffbffafffffffffefffbffbffffefeefeffffffefeffaffeffbfbfebffffefffffeffffefffffbffbeffffffffffefbfefbebeffffffffbfffffeefffffffffffeffebbffffffffffbeffbffbffbeffefffbbefffbeffbefffffefbfffeffffffffffeffeefffffebfffffffebfebfffbffffbeffffffefaefeffbffffbfffbefefffebffbffbfffeffefffefeefefffffefffffffffefaffffbbfffefffffffbefffbffffefffbbfffffffbbffffffefbfbffbfffffbffbfeffefeffbfbfefffffebfffffbbebbfbefffefefffebbfbffbbffaffffffffffbbefffffffffffebffffffbfffffffbffffffefbffbfffeffffbfffffbfeffffffbaffbfffffaffbffffbfebeffefffffeffbffeffffffffaffbefffbfefefbfffbebffffffafbfffffffefbeffffeefbfffffeffbfbbfbffbeffbffbffffffeffffefffffefffffefbfffffbffbbffefbefffffbefbefffbeefffbffbffbffbeefeffafffefffffffffbefbffbfffefffffffbfffeffbffbfffffbefeffbefbfbfffffffffbeffffffffffeffbffffbaebfefffbfefbffbfffffffffffffffffbffeeffffefbfefffbfffbffaffbffffffffffffffeffbffeebaffefffffbffffbeffffbaffffbffffeffffeffbffffbfffbfbeefffffffeffeffeffbfffffeffbfffeffffffffffbffbffbffefffefffffeffefefbfefbffffffebfffbffbffefffefffffefbfbbfffffeffffffffeeffffffbbfffffeefffbfffbefefffffbfffebbffeffffbffffffeeffffffffef := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask640709 : MertensSieve.bits 640709 = 0xffebfffbfbbfffefffffffffbfffffbfffbfffffffbffbfeffffeffefbfffeeffffaffaffbffffffffffbffffffffffffeffffffefffffffeffeeffffffffffbfbafbffffffaffbffefffffeefbffeffaffffbfeffefbffbfbfefefffffffffefffbffbeeffffbeffebffbeffeffbffbffffbfffffbfebfffffffefefffebffffffeffbffafffeffeffffefbffbfffefbaffffbbfffffefbfffffbbfbfefffbfefefffefbfbffffefbffffbbfffefbffeffefffffeffeffeffefffebffffffbfbafffefefbeffffbfefffffffaffffffffffbfefeffeffffffefffbfffbffeebffbfffeffeffeffbfbefffffbfffebfebffffeffffeffbffeeffefefbbefffbfffbefbfbfffffffffeffbffeffffffffeffffffffbfffeffffffbefbffbfefffffffeebffffefbefffbbfffffffffffffffeffffeffaffbfbeffffbfffffffffbffffffebeffbfffebbfbefffefffffffffbeefaffeffaffbffffffffffbbfffffefbffffffbffbffeffbfffffbefffffffeefffffffbefeeffeffffefbffbefffffffbfffbfffffbffbffaffbffeffbffbfbffffeffebeffeffffbffbfffaefbfffffffffebeffffbaeffefffbfffffbfebffbfeffefffbfffbffefbfffefffefffffffffffffefffffefffffffffffbfbffffffeffefbfffffffefbfbeffbfffefeefffbbebffbffffeffffffbfffeffbffaffbfffeffebbefffbeffffffffeefefbfffbffefbfffaffefffefffbfffafffefbfffeffeffffaefffffefbefeffffbffbefbfffaffffffffffbbffbffffbfeffffaefffbbeffefffbffffffefbffffffeeffffbffbfffffeefbfffefffbeffaffafbeffbeffefffffffeebbfffeffffeffffbffffefeefefffffbfbffffffefbbefffbfebfffffffffffffffefffffffbffffefbffffbeebfeffffeffaffbefffbffffffefbfffbffefbfffffbfffbffefffffefbeefffbfefeffffbffffffeeffffffffffffffffaffffffefffffffbffbffeefffbffbbffffffffffffefefffffbffbefeffeffbfbbfbfeffeffeffffeeffffefbfefbfffffbfbfffeefafffeffffefffffeffafbffbfefffffffaffffffffeffffbfeffffffffffffbfefffffffeffffbeffbffeebfefffffffbffffffefffffffbfbffbbffffffeffebffffffffffffffffffeffffffefbefeffbefbffaffffffffbefafffeffefeffffffffafbffffeffffffffebffffffeffeffbffffffefbffeffefbfefefbbffffbfefbebeffbffaffffffeffebfffffffeffeffffeffffffffffbeffbfffffffffebffffffaffffffebefffffbffbfbbffeffeeffffbebfffffbfffbffffffffffbfeffffbffbfbfffefffffbffbffeffbefffffffbfffffbffaffffffefeefbeffffefbfffffffffffffeffffefbbefefbfefffbffbeffbfffefffbefbfeffffffffffefffefbffffffefefbffff := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask648901 : MertensSieve.bits 648901 = 0xaffbfbfeffebfffeffefffffeeffeffffbfbffbfffbeffffffbffffffffffffbefffbfeffffbfbffbfffeefeefffffffbefffbaffbffefbfffffffffefbaffbfffffeffffffffbfbffffffffbbfbffbffffffefbfffbfffeffefbfffffbffeefaffbfbefbfffefbbfffffefffeffffffffffffbfffefbeffeffbeffffffffefffbfffffbfffbffffffffbfffffeffffbfffbffeefeffffbfffffbfebfffffffffbfffffffffffefffffffbbefffffefbffffffefafbeffffffffeefffbbfffebffbeffbffefbbfffeffffbfffefffbfffffffffbffbfbefffefbffefbffffffeffefbfefbeffffaffefbbfbffffffefffffeffffffffeffbfbfffbfffeffffffbeeffefeffaffbfffffbfffffbffbfbeffffffeffefffffefffbffbeefffbbfffebffbfffefbbffbfffffeeffffbfbfffffffffefbfebfefefbfffbfffeffebfebfffeffbfbffffffffffffbffbefefffeffffffbffffefbffffbfffbefeffffffffefffffeefaffeffffbbfffebaffefffffbffffbfffefffffbffefbfffefbbfbfefefffefefbffbfeffebfffffbbeffebfffffffffffbffbfffeefeffefffeffefbffffffebbffefbffffffbfbbeffffaefffffefffbfffafffffaffffbffbaffbfffeffefffffffbffffffffffffffffbeffffbfffeffbffffffefefbfffffbfffffffebbeffffffffffeffbfffffeebffffffbfffffefffffeffffffffafbffffeffefffbeebfefeefbfffffffbfffeeffefbffffbfffffbffffffbefbebefbbfffffbfffffffbfefbfffffbeffebeffbffeefbfbfefaffffffffbfbefffffffffebbfffeffefbffffffefeefeefffbbfbfebffffffbfbbfffeffffaefeffeffbfffeffffffffefffffffeefffffffbebfffbfffffbefffbffffeffffffbffffffbffffffeffeffffeefefbeeffebfffeffafbfefffffebfffffffebbffffffefefbfffbfffebefffffefffffffbffffffffffffffffefefbfffbefeffefffffaffffffffeeffffffffefffbfffbfbffffffeefeffbffefbbfbfffaffffffebfebfeffffffbbffbfffefbeffffffbbfffffbffeffafffffffbfffbfffeffffefbfefbffffffffeefaffbfffefbefeffffffffbfffebfffffffffffffefffffffeffffffffffbbffeffbfbfefffbbffefbeffffbffffffffbaffffffeffffffffeffefffbffffffbffbfffebfeffffffbfeffefeffffffffbffefffffefbbfffffffffffffffffbfbfffeffbffbfffffffffefbffffbfeffefffffffefffefffbfeffffafbbfffefbffefffeffebefbbefaffffbffbffffefeffeffffffffeefbfbbebffbeffffffffeefbfbfffeffeffffbbebffbbffaffefffffffbaffffbffffebfffefffffffffefffbfffbfbaeffeffffffffffeffffffffbfffffefbbeffffbffffffefbebeefbfffffbfffffffbeeffffffbfefefffefbffefbff := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask657093 : MertensSieve.bits 657093 = 0xfbffbfffbffbeffefefbefffffafffffeffeffbfbeebffffeffffefffebbfbfeffefbffefffffefbfffefffeffffffffffbffbffffffebbffffffffffbeeffefbffeffffbffffffbfffebbfbfebaffffffeffebeffbefefbbfbfeffeffefeffffbbffffffffbffbfffefffbeffffbffffebfeffeffffffbffbffffffefffebfffeffbfffffffbffbefffeffffffbfefeffaefeffbfbfffffbeffffbfffffbfeffefbfbaefbebffffefffffffbffeffeffeffeeffffffbafffffeffbfffffbfffffefffffeeffffffbffffebefffffbffffffebfebaffafbeffbebfeffefffffffffffffbfffffeffffffebffffffffbffbfeffffbffbfffeffffaffefbffffebffffffefbffbfffffbaffefffffbffffffeffffffbfffeeffefbfffffbebfffffffffeebbebffffeffffafffffffbfffffbbefffbffffefefffebffffffbfffffbeffffeefeffbffeffbfbffffeffffffbfffffbfffbffafbbffefffffbfbeffffffefbffffffffbefffffffeffeebffbffbbffefffffbefffbeffbffffbbfffffbfffffeffffffefafffffffbbfffffbffffbbffbfffefeffffbfefbfffffeffaffbfbffffeffefefbaefffffeffffffbffffffffffefeffffffeffffefffffeffffbeffbfffffffffefefbbfffffffffffefbefffffeefffffffaeffffbffffbfffeefffffeffffeffeffffbfffbefffffffffffffbfbefffefbffefffeffebbffffffffffbfffeefefbaebffffffeffefffffbfbfeffffffbfefffffefeffffbefffebefbfffffffebfffefffefaffbfbbfffeffefffffebbfbffffffffbffffebfffbfffffaffbebeeffffffbaffbfffefeffefbfeffffffffffefffffffffefbffbffaffbfffebfefefffffffbfffeefbffffbfefffbfeffffafffefffbfeffffefbffbfffbefffffebbefefbfffefffeffebfffbffffbffbbefffffeffffbfffefeffbffefbffbffbffffffffbffffebfffeffffbfeffffeeffffaffeefffbfefeffaffefbffffefbfffffbfbfefeffeefffffefbffefffefffbbfffffffffffbfffeffffefbfeffffbffffbffffffbffefbfefffffffeffeebffbffffeffffffffefffffefefbbffbfffffbffbffefbffbfefaffffbfffffbefbfefffbfebffffffeefbffeffbfffffbffffffebfffffffffffbffffeffffbffefbbeffffefbeffaffbefffffebfffffffffbffffbfefffffefbffefffefffbffbffbffbfffafffffbebfefbfffffafffefefbffffffbfbffbffbfffeffbefffbffbbefbfffffffbfeffefbfbfffffffffeffffbfefffbffbfffaffffbfffefffffffbffffefffbfffefffefffbffffffffbfffffbffbbfffffffffebeefffffffeffbfffefafffffeffffbfefbfffffaebfffeeffffbffbfbfffeffbffffbffffefffbfffffbfebffbfefeffeffefffffeffffffffeefbfffffffffffffbbefefffff := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask665285 : MertensSieve.bits 665285 = 0xfeffafbbeffebfffbfbafbfefffffffeffbffbffefffefbfffebfffffbeffffbfffbebeffffffffeffffffefeefafffebfffeefbfffffbffffbffffffffbeffbffeefbefffffeffeffffbffafbffffffffbbefbfbbffbebffbfefffbfffffffffbffffffffbffeffaffeffffffffefbfeffffeffffffffefffffbeffffefffffffbbffffffffffffffaffffffefeffffbefbfffeefbffbffffbffffebbffefffeffeffebfffbfbefbbffffbbeffffbefffbfffaffeffbffffbfffeffafffffbebeffeefbfbfefbffffffffbffefbfffffffffbffafffffeffbffeffefffeffffefffffffbbffefffffefbffbfefffffeffffeefffbfffefffffefbbfffffbffbffefffeffffbffeffeefffbfffbffffbbffbfffefeefefffefffbfffeffeffffffebfffeffbfbffffffefbeffffbbffffbfeffefffbffbbfffffbffbffffbffbfffbeffffeffbffeeffffffbffbffffffeefffbfffffbfebfffbfffeffffeefffffffbffbfbefffefffbeffffbfffafffffefbbffeebfffbffeffbffffffffeffbffffbfffbffefbfeffeffffbeffffbfffeffeffefbfbefbffbefffefffffffbfbfefffffffafffffffffffaffafbffffffeffeffffbfffffbbefbfbfeffefffbfffefbaefbfbfffffffffffbbfffffbffffffeffffffbeffeffaefbebfeffeffffffbbffffffeffffffbfffffbffffffffffebfffbffbffeefffbeffeffbffafbffbffffffeffffbfeffebbffbfffffbeffffffffffffffefefbfffffffefbefefbfffaffeffffffeffffefbfffffbfeffffffbbffbfbfeffffffbfffffbeebfffbffffffefeffbffbffffffefffbeeffffbefffbffbfefbfffffffffffbefaffbfffebffbfffffbbebbffeefffffffffbffffffffffffeffbffffffffffffffbffffffffffbffffffefffffffbffffeffefafffffbffffbeffefffffffbfffeeffffeffffbbffeeffffeffbfbbfffffbffeffffffeffffbffffbfffbebffffefeffafffeffffeffefffeffefffbffffffafbbffefffefefbffbffffffffffffefffebeebfffbffbffbefffbfefffbffffefffbaefffffffffbffbaffbfffeffeffeffffffbfefffffffaffeffffbffffffeffbffffffeffebbffffbffbfeffffffffffffffebefffffefbbffffbffffefeffffffeffeffffbffeffffffefaffbffffffffeeffffaffeefbffffbfefffbffbbfffebbefffffffbfbfffffffffafffeffebfffbfffeffffffbefffffaebbfffffbfffffffffffefffffeffffffefffffefeffffffffeeffffffbffbbffefbfffffbbffffbfeffffaffbefbfffffeffbfbbeffffeffaffffffefbfffffafffffefffffffffefffbffffffeffaffefbfeffefffbfffffbbeffffffffeffffbfffffeeffefffbffbfffeefbefefffffbffffbafffffbfffffffbfffeffbfffffffbeffeffbfbfffffffffbfbbeff := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask673477 : MertensSieve.bits 673477 = 0xfffffbfffbfbfefbfffeffffffbeffffbfffafffffeefbefffffffafffffbfbfebbfffffffbbeffffeeffffffbfffefffffbffaebffffefeffffffffffbffbfffbffeffbffefffffafffffbeffebefffffbfbfefeebfffbffbffffffeffeffffffffebeffeeffffffbffffefbffffbfffbfbfeffffffffffbfffffefffffefbfffeffbffbffeffbfffebffffffbfbffffebbffeffffffffeffaffbffefbfebffbfefffffefbefffbefffffaebffffffbffeffefffffeefbffeffefffebffffffefbfffbfffffaeffffbffffbffbfffffbbeffeffefeefbfffefffbfebfefbfbbffbfbfffbefefbfffbffeffeffffffebbefefffffeffbfbfeffefffffffbeffffffbbeffffffffefffffefbffafffefffbfffffbffbfffeffbefefbffffefeefaffffffefffbfeffeffffaffffffeffffefbbffbfffffbffaffeeffffffbbffbfffffbffffbfffbffaeffffffffffeffffbffbfefaffffffffbeffffbffbffbfffffeefbffefffffffbefbaefeffbfbfebffffffffffffffbeebeefbffffbbfbeffeefffbfeffefeffffffffbeffebfffbffbffefffefeebeffffbffbbfffffaffefffffffbfeffffffffefffffefeefbfbbfbffbfeffefffffefffffffafffffefffefffbfefffbfffffffffbfffffbefbffffbffffffffbfffffffefffffffbffefffffbfbbffbffffffeffffefffffffbafffffeffbfbffbfffffffffbfffffaffffbbebfffffffffffffebfebffbeffffbffffffffbfffbffefffffeffaffafffffffffffffffffbebbffeffffffffeffbffffbffffffbebbfffffeeffffefffeffefeffbfffefbebffbeffffbefbbfbfefbffbfbffffebffffffefffffbffffffffbfbffbbffefbeefffbfffffbfffeffefffffffffffeefefffeffffffffffffbffffffefffffefbffffffffbeffaffffbbffeffbffeffafffffffffefeffbffffbeffefffffafbfffffffffbfffffbfffeffffbfbbffffffefeefbfbefbffffebffffffaefffbffffffafbfffffffefeefffbbfffebffbbeffffefffefffffffbfbbfffffefffffffffffffffffbffeffefbbefeffeffeffbebfebffffffbffffffeffffbefefffffffbefbfffbffffffffffbefffffbefffbffffffbfbfebbfbfffefffffeffbfbeffaffbfffebfffeeffefffbbfbbffffffffeffffffffffbfeffffeeffeffeffffffbfffffbffbfefbffeebbffefffffeffffbbebfefeffbffafbfebeffbefefffffbffffffffffbfffffffffbffbffeefffffffeffffbffffeffeffffbffbfffffefffffbfbeffbfffffefffffbfffffeefbffeffbfbbffffffffefbfeffebffffffbfbeffffbfffbffbffafffffffffeffffffbffbfffeffbfbffffefffffffbffbfffffffffeffffefbfefefbeffefffffbffffffffffffffffffebfffefbaffffbeefffffffbefbffeeffffefffefffbffbff := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask681669 : MertensSieve.bits 681669 = 0xffbffffbbffffbbefeffbfbfefffffffffbfefffbeffffffffffffeffefeffffbaffbeffffeffbfffffffffeffffffffffbebfffeffbffffbfffeefbffeffefffeffffeefeffffbffbffbeeffffeefffbfffeffffffffbfffffeffbfffefbffeefeefbfbffffefeffefffffbffffbfeffefbffbfffffffbfffeffffbbefffffffffffefffbfffbefffbeffbefeeffeffffeffffbfefeeffffefbbefffffffbfffeffeffffbffbffffbfffffffefffffebbffeffbffbfbeefffbffffeffffbefffffeffeffffefffffeeffffffbefffefffbffffffbffbfbefffffbffeffbffefbbfffffffbbffeffbfffffefffeffeffffbfbefffefefffffffffffbfbfefbffefffffbfbefbfffeffefffefffbfffbfbbfffffffbeefffbffffffeffefffffbfbfeffffaeffffbfffefeffeefffbeebfffeffbefefbfffffbfffaffbffefbbfbfeffeffffffffffeffbffffffffffbfffaffbffbfbfeffebeffffbfeffeffffeffbfbaefbffeeffefafbfffbffffffffbffeebffbfffbffffbeffffffffeefefffeffefffffefafbffffffffbfffafffffffbffffffbfffefffffffbffbfffffffbeffbfffffbeffffeeffefffbefffffffffffffbbefffbeffeefffffefffffebfffffffffffffefeeffffeefffffefaffbffeffffbfebffffffefbfebfebfffafbffbbffeefbfffffbfffffffbfffffffffffbfefffffffbfffffeffefffffbefbfbeffbeffffeffffbfeffffeffefbfefeeffffbffffffffffbeeffffbebfffefffffbffbefffffebfefffffeffeffebefffffaffffbfffeeffffffbffffebfffbfffffffbffffefeffffffeffffbffefbbeffefeffbefbffbfbffbfffeffeffeeffeffeffffffbfffffffeffffeffefffeffeffffeffbebfffeebfefbffffbbffefffffffbffffffffbbeffffeffffbffbeffeffaffbffffbfffffffeffffeeffffbfbfefbfbffbffffffbefffffebfefeffffbfffeebfffefffffffbfffeeffffffbffffffbefffffffbebeeffffbffffffffefffeffffeffbfffffbfffffeffffbeffbffaffbffbffeffaefffbfebfebffbfffefbeffffbffbfefbffbeffebefbeffffffebfffffffffffbefbfffffbffffffffffffeffbffefbafbfefefbfefffffffbeffffeeffffefbfeffffbefffbbfffffefffefbffffbffffffeffffffffffbfefbffeffbfffffffbbffbfffffbeffffeffffbffffffffbfffbfbfefffffffeffffffffffffffffffffbfbffffeffefffbffbffbeefbfffffaffffbefffeffffefffffffbfeffffffffffffbfffbffbfbffffefbffbfbfffbfbffbeefbffffffffeffefffffeefbefffbbffaffeffffbffbfefeffbffbfffffbffffffebbefffffffffffffffbfefbffeffeffffffefeefffbafbffffefbffbfffefffbfffbfffffffffebeffbffefffffbefeffbfffffffbbfbffffffeffeef := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask689861 : MertensSieve.bits 689861 = 0xbffbfffeeffffbefffbefbfffbffefffffeeffefbffefffffffffffbffbfffffffbffffffafffffeebfffffbfebbefefffffffbeffffffffaffbfbbfffffefffffffbbebbfffffefffffeefbeffffbffeffaffbebefffffbfffffbfffffbfffffffbbebfffffffffefbfeffffefffffefffefefbeffbfffefbfbfefbffefffefffbeeffffaffffffefffffefefffffbffeebfffffffebfffefbbffafffefffffffbefffbefffebffffffbffbffffbefffffefbefbbffffffffefffffbffeffbefffbefbfefffffefffffefbffeffbfffffbeffebfefbffffbeefffffffeffbfbeefffbfffffffffffffefffffffefffffffbfebfffffbaffbefeffffffffbffffbffffffffffffffbffbfeffffbfffebefbfffffbbffffffefeffbffefbffffefbfffffbfffeffebfefffbbfffefffbeffffbbeffefefbeffffffffffffefbffbffeffbffffbefffffffbbfffeffefafffffbfffebbffeffeeffeffefbefffbbfffffffbffffffffbffffffeffbffefbffbfebeffeffbffbfffffeefffbaffbfbffffefbfffffffbfffefffffbebbffffffffafffffffffefaffffbfffbfffffeeffffffffffffffffafffefffbfeffefbffffbbfbfefeffffbfebfffffbaffbffefffffffbfffeffffbbefefbeefeffbefbfbeffffffffeebfebffffffffbfffbefeeffffffffffffffffbfffffffbbebfefefffffbefffbffffffefffffbeffffbffffffffffffffeefbffbfbffffebfffeffbefffbffffefffbbebbfffffeefafbefffebffffffeffbffbefffffffaffffffffeebbffffbfefbfffffffffffefbfeffefaefffffefffbefffefffbeffffffffbfffffeffffffffbffffffffffbfebfefeffeffbfffffbefeffbfffeffffeeffffbffffffffbffefbefffffeebfefffffefffffffbffbffffffefffffffeffbfbfefeffbffeffefbbfffeffffffbffbbeffffefffffffbfefffbfffffbafffefefffffffffffbfbeffeffbfbfefbebfebfffbfffefbffefbfffeffaffbefeeffffeffbfffefffffffbffffffeffebefffffeffffbfeffffbfbbfbfffffffefeffefbffbefffffeffffbfebffbbefbffefbffffffaefefffefffbffbfffffbbffffbfebaffeffeefbeffffeffbffefbfffffffffafbfeffffefffffbfffffffbfeffffffbffbfffefffffeffbfffeffffbffefbeefffffeffefefffffbfffffeffbfffffffbeefaffffffebbfffefeffafffffffbfffbffbffeffffffffeeffffffffffefffffeffbffffffebfffaffffffebffffefffffefbffffffeffffffffebffffffefffeffefffffffeffffbbfffefbffffffeffefefffffafffebfffffbfffeffbefbfbffbfeffffeffbfffffeffffbffffffeffeffaffbfffffefffffffffffbfffffbffffbbffbfbfffbffefffefffbffffeffffffffffffbeffffbafbffffefeefffbfebffbeebf := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask698053 : MertensSieve.bits 698053 = 0xfffefffefbefeffbfffffafbfefefffefeffbfffffffbfffaffbefffbfefaffefffefbfffeffeffffbffffbfffbffbfbffffefeebeffffffffbebfefbffbffefffffefffffefffffffffffbffbfffefffffffffffffbfffffeffefffffbebffffffefffffeffbeffefbffefffffffffffffffffeffbffefffefeffbffbffffffffeffefbfeffebafffffeffbfbefffeffffbeffffeffbffbffeebffbeefbffffffffbffeefffffffefffffffbaefeffbefffbffbeefffbafbfefffbfffbffbeffffffbeffffbeffbffffffefffbfeffebfebfffafffffbefffbffffffefffefeebefffffbffffbeffffffffeffffffffeffefbbffbebfeffffbfbfefffbefffffefbefffefeffeffbffefbfefffbfffeffbffffffebbefefbffbfefffffefefbffffffffbbefffbfeffeffeffeffffbffffffeffffffbfeffffeffeffaffbfbffbeffbefffbffbffffffffffffffffebffffefbfffffffbfeffffbfbbffbefffffffbfffefffbffffefeffffbbeffefefffffeffbfffefbffafbefbfffefffffeffffffebffbaeffffffffeffffffffffbeffffefffffbfbffffffffffefffffeffffefbeffefffebbffffbfefefbfffbffefffffffbfebfefffbeffffbbfbfffffffffffbfefbfbfebffffffefbffbfefbefbfbeffffffeffffbffbebfffefbfffbffbfffffeebeefefbfebffffffaffeffeffffbffffffbfbbefffbeffffffffafbbffeffefffffeffbfffffffffffefbbffffffffefbefbfffffffffffbffffeffffbfffffeffffbffffffbfbffffeffffeffbffbfbffbfffeffafffefffffebeffafffeffebffffffeffffbbfffebfefeffbeffffefbbfffffaeffebfffbeffffafffeffefffffffbfbffbffffefffffffbebfefffffffaffffbffbffffffeffffffeffffffffffbffeffbffafffefffffffbffeffeefffbffbfefffbefbffffeffefbffffbfeffefefffffbfbfffffffefffbffffefefffffffbbefbffffffefbffeebfefffffefffbfffffbffffffbffbfffffeefbffffffebbffffbafffffbfbffbffbbfffffaffffffffeefefbffbfebffffffbfffffffffebfffefbbffbebffbfefffffffbfffffeffffffffbefefbbffbffffffffffffffffbfffffffffbefffffebfffffbeefffffefffbfeffefffffffffffefeffbffeffffffffeffbffefffebfebeffbfffefffffefbffefbeffbfffffeffffbbefbfffffbffffbbffffbfebfffbfffeffeffffeefbffefbbfffeffefbfffefffbefffffeffeefffbefffefffffffbeffffbefffffffffbfffbffffbbfbfffffffffefffffbeffffffffffbeffffffffffefbfeffefffffffefffeffeffffffffffffbfffffbfefffbbfbbefffbfffbfbffbfffffbfeffffaeffffefbfffbffbffffbfeffffbffeefbffeffaffaffbfffffffffffffbffbffffffffffffffbffffffbefffffe := by rfl
end MertensMasks

namespace MertensCertificate
open MertensFold
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b0 : B 0 1733 315684388066545112 61977157 := segment 0 1733 315684388066545112 61977157 (Or.inl rfl) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b1733 : B 1733 9925 29125636570929 8028090 := block_of_mask 1733 8192 29125636570929 8028090 _ (by decide) (by decide) (by decide) MertensMasks.mask1733 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b9925 : B 9925 18117 2372414246126 31823 := block_of_mask 9925 8192 2372414246126 31823 _ (by decide) (by decide) (by decide) MertensMasks.mask9925 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b18117 : B 18117 26309 857955451968 5840 := block_of_mask 18117 8192 857955451968 5840 _ (by decide) (by decide) (by decide) MertensMasks.mask18117 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b26309 : B 26309 34501 437660667119 2923 := block_of_mask 26309 8192 437660667119 2923 _ (by decide) (by decide) (by decide) MertensMasks.mask26309 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b34501 : B 34501 42693 263298874111 2331 := block_of_mask 34501 8192 263298874111 2331 _ (by decide) (by decide) (by decide) MertensMasks.mask34501 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b42693 : B 42693 50885 172294407118 2247 := block_of_mask 42693 8192 172294407118 2247 _ (by decide) (by decide) (by decide) MertensMasks.mask42693 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b50885 : B 50885 59077 126551801919 2283 := block_of_mask 50885 8192 126551801919 2283 _ (by decide) (by decide) (by decide) MertensMasks.mask50885 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b59077 : B 59077 67269 91842249504 2190 := block_of_mask 59077 8192 91842249504 2190 _ (by decide) (by decide) (by decide) MertensMasks.mask59077 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b67269 : B 67269 75461 72075070739 2196 := block_of_mask 67269 8192 72075070739 2196 _ (by decide) (by decide) (by decide) MertensMasks.mask67269 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b75461 : B 75461 83653 57806621944 2190 := block_of_mask 75461 8192 57806621944 2190 _ (by decide) (by decide) (by decide) MertensMasks.mask75461 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b83653 : B 83653 91845 46239157963 2133 := block_of_mask 83653 8192 46239157963 2133 _ (by decide) (by decide) (by decide) MertensMasks.mask83653 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b91845 : B 91845 100037 39171378441 2157 := block_of_mask 91845 8192 39171378441 2157 _ (by decide) (by decide) (by decide) MertensMasks.mask91845 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b100037 : B 100037 108229 32475057650 2109 := block_of_mask 100037 8192 32475057650 2109 _ (by decide) (by decide) (by decide) MertensMasks.mask100037 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b108229 : B 108229 116421 27739806786 2097 := block_of_mask 108229 8192 27739806786 2097 _ (by decide) (by decide) (by decide) MertensMasks.mask108229 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b116421 : B 116421 124613 24292347783 2115 := block_of_mask 116421 8192 24292347783 2115 _ (by decide) (by decide) (by decide) MertensMasks.mask116421 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b124613 : B 124613 132805 21027325430 2088 := block_of_mask 124613 8192 21027325430 2088 _ (by decide) (by decide) (by decide) MertensMasks.mask124613 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b132805 : B 132805 140997 18685578466 2100 := block_of_mask 132805 8192 18685578466 2100 _ (by decide) (by decide) (by decide) MertensMasks.mask132805 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b140997 : B 140997 149189 16177504100 2043 := block_of_mask 140997 8192 16177504100 2043 _ (by decide) (by decide) (by decide) MertensMasks.mask140997 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b149189 : B 149189 157381 14805700189 2085 := block_of_mask 149189 8192 14805700189 2085 _ (by decide) (by decide) (by decide) MertensMasks.mask149189 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b157381 : B 157381 165573 12814603288 2004 := block_of_mask 157381 8192 12814603288 2004 _ (by decide) (by decide) (by decide) MertensMasks.mask157381 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b165573 : B 165573 173765 11656426034 2013 := block_of_mask 165573 8192 11656426034 2013 _ (by decide) (by decide) (by decide) MertensMasks.mask165573 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b173765 : B 173765 181957 10694226100 2028 := block_of_mask 173765 8192 10694226100 2028 _ (by decide) (by decide) (by decide) MertensMasks.mask173765 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b181957 : B 181957 190149 9989698300 2073 := block_of_mask 181957 8192 9989698300 2073 _ (by decide) (by decide) (by decide) MertensMasks.mask181957 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b190149 : B 190149 198341 8881053502 2010 := block_of_mask 190149 8192 8881053502 2010 _ (by decide) (by decide) (by decide) MertensMasks.mask190149 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b198341 : B 198341 206533 8125865618 1998 := block_of_mask 198341 8192 8125865618 1998 _ (by decide) (by decide) (by decide) MertensMasks.mask198341 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b206533 : B 206533 214725 7601219234 2022 := block_of_mask 206533 8192 7601219234 2022 _ (by decide) (by decide) (by decide) MertensMasks.mask206533 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b214725 : B 214725 222917 6881304063 1977 := block_of_mask 214725 8192 6881304063 1977 _ (by decide) (by decide) (by decide) MertensMasks.mask214725 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b222917 : B 222917 231109 6617047482 2046 := block_of_mask 222917 8192 6617047482 2046 _ (by decide) (by decide) (by decide) MertensMasks.mask222917 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b231109 : B 231109 239301 5738958312 1905 := block_of_mask 231109 8192 5738958312 1905 _ (by decide) (by decide) (by decide) MertensMasks.mask231109 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b239301 : B 239301 247493 5623474206 1998 := block_of_mask 239301 8192 5623474206 1998 _ (by decide) (by decide) (by decide) MertensMasks.mask239301 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b247493 : B 247493 255685 5279030654 2004 := block_of_mask 247493 8192 5279030654 2004 _ (by decide) (by decide) (by decide) MertensMasks.mask247493 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b255685 : B 255685 263877 4742146580 1920 := block_of_mask 255685 8192 4742146580 1920 _ (by decide) (by decide) (by decide) MertensMasks.mask255685 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b263877 : B 263877 272069 4680626856 2016 := block_of_mask 263877 8192 4680626856 2016 _ (by decide) (by decide) (by decide) MertensMasks.mask263877 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b272069 : B 272069 280261 4223085000 1932 := block_of_mask 272069 8192 4223085000 1932 _ (by decide) (by decide) (by decide) MertensMasks.mask272069 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b280261 : B 280261 288453 3961777977 1920 := block_of_mask 280261 8192 3961777977 1920 _ (by decide) (by decide) (by decide) MertensMasks.mask280261 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b288453 : B 288453 296645 3770966449 1935 := block_of_mask 288453 8192 3770966449 1935 _ (by decide) (by decide) (by decide) MertensMasks.mask288453 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b296645 : B 296645 304837 3608898767 1959 := block_of_mask 296645 8192 3608898767 1959 _ (by decide) (by decide) (by decide) MertensMasks.mask296645 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b304837 : B 304837 313029 3370045257 1929 := block_of_mask 304837 8192 3370045257 1929 _ (by decide) (by decide) (by decide) MertensMasks.mask304837 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b313029 : B 313029 321221 3321662984 2004 := block_of_mask 313029 8192 3321662984 2004 _ (by decide) (by decide) (by decide) MertensMasks.mask313029 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b321221 : B 321221 329413 3085788255 1959 := block_of_mask 321221 8192 3085788255 1959 _ (by decide) (by decide) (by decide) MertensMasks.mask321221 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b329413 : B 329413 337605 2900106173 1935 := block_of_mask 329413 8192 2900106173 1935 _ (by decide) (by decide) (by decide) MertensMasks.mask329413 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b337605 : B 337605 345797 2736650603 1917 := block_of_mask 337605 8192 2736650603 1917 _ (by decide) (by decide) (by decide) MertensMasks.mask337605 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b345797 : B 345797 353989 2651088317 1947 := block_of_mask 345797 8192 2651088317 1947 _ (by decide) (by decide) (by decide) MertensMasks.mask345797 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b353989 : B 353989 362181 2453875078 1887 := block_of_mask 353989 8192 2453875078 1887 _ (by decide) (by decide) (by decide) MertensMasks.mask353989 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b362181 : B 362181 370373 2334918857 1878 := block_of_mask 362181 8192 2334918857 1878 _ (by decide) (by decide) (by decide) MertensMasks.mask362181 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b370373 : B 370373 378565 2271773624 1911 := block_of_mask 370373 8192 2271773624 1911 _ (by decide) (by decide) (by decide) MertensMasks.mask370373 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b378565 : B 378565 386757 2198811876 1932 := block_of_mask 378565 8192 2198811876 1932 _ (by decide) (by decide) (by decide) MertensMasks.mask378565 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b386757 : B 386757 394949 2103582283 1929 := block_of_mask 386757 8192 2103582283 1929 _ (by decide) (by decide) (by decide) MertensMasks.mask386757 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b394949 : B 394949 403141 1947265504 1860 := block_of_mask 394949 8192 1947265504 1860 _ (by decide) (by decide) (by decide) MertensMasks.mask394949 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b403141 : B 403141 411333 1883967685 1875 := block_of_mask 403141 8192 1883967685 1875 _ (by decide) (by decide) (by decide) MertensMasks.mask403141 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b411333 : B 411333 419525 1851308391 1917 := block_of_mask 411333 8192 1851308391 1917 _ (by decide) (by decide) (by decide) MertensMasks.mask411333 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b419525 : B 419525 427717 1739047007 1872 := block_of_mask 419525 8192 1739047007 1872 _ (by decide) (by decide) (by decide) MertensMasks.mask419525 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b427717 : B 427717 435909 1780249506 1992 := block_of_mask 427717 8192 1780249506 1992 _ (by decide) (by decide) (by decide) MertensMasks.mask427717 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b435909 : B 435909 444101 1628728215 1893 := block_of_mask 435909 8192 1628728215 1893 _ (by decide) (by decide) (by decide) MertensMasks.mask435909 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b444101 : B 444101 452293 1547821317 1866 := block_of_mask 444101 8192 1547821317 1866 _ (by decide) (by decide) (by decide) MertensMasks.mask444101 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b452293 : B 452293 460485 1442562688 1803 := block_of_mask 452293 8192 1442562688 1803 _ (by decide) (by decide) (by decide) MertensMasks.mask452293 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b460485 : B 460485 468677 1454454516 1884 := block_of_mask 460485 8192 1454454516 1884 _ (by decide) (by decide) (by decide) MertensMasks.mask460485 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b468677 : B 468677 476869 1449549695 1944 := block_of_mask 468677 8192 1449549695 1944 _ (by decide) (by decide) (by decide) MertensMasks.mask468677 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b476869 : B 476869 485061 1331711919 1848 := block_of_mask 476869 8192 1331711919 1848 _ (by decide) (by decide) (by decide) MertensMasks.mask476869 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b485061 : B 485061 493253 1310062950 1881 := block_of_mask 485061 8192 1310062950 1881 _ (by decide) (by decide) (by decide) MertensMasks.mask485061 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b493253 : B 493253 501445 1295643468 1923 := block_of_mask 493253 8192 1295643468 1923 _ (by decide) (by decide) (by decide) MertensMasks.mask493253 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b501445 : B 501445 509637 1185393744 1818 := block_of_mask 501445 8192 1185393744 1818 _ (by decide) (by decide) (by decide) MertensMasks.mask501445 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b509637 : B 509637 517829 1199063801 1899 := block_of_mask 509637 8192 1199063801 1899 _ (by decide) (by decide) (by decide) MertensMasks.mask509637 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b517829 : B 517829 526021 1150936623 1881 := block_of_mask 517829 8192 1150936623 1881 _ (by decide) (by decide) (by decide) MertensMasks.mask517829 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b526021 : B 526021 534213 1110386542 1872 := block_of_mask 526021 8192 1110386542 1872 _ (by decide) (by decide) (by decide) MertensMasks.mask526021 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b534213 : B 534213 542405 1052461202 1830 := block_of_mask 534213 8192 1052461202 1830 _ (by decide) (by decide) (by decide) MertensMasks.mask534213 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b542405 : B 542405 550597 1021230685 1830 := block_of_mask 542405 8192 1021230685 1830 _ (by decide) (by decide) (by decide) MertensMasks.mask542405 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b550597 : B 550597 558789 999612097 1845 := block_of_mask 550597 8192 999612097 1845 _ (by decide) (by decide) (by decide) MertensMasks.mask550597 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b558789 : B 558789 566981 969127614 1842 := block_of_mask 558789 8192 969127614 1842 _ (by decide) (by decide) (by decide) MertensMasks.mask558789 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b566981 : B 566981 575173 953668922 1866 := block_of_mask 566981 8192 953668922 1866 _ (by decide) (by decide) (by decide) MertensMasks.mask566981 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b575173 : B 575173 583365 931415455 1875 := block_of_mask 575173 8192 931415455 1875 _ (by decide) (by decide) (by decide) MertensMasks.mask575173 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b583365 : B 583365 591557 895696263 1854 := block_of_mask 583365 8192 895696263 1854 _ (by decide) (by decide) (by decide) MertensMasks.mask583365 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b591557 : B 591557 599749 875295639 1863 := block_of_mask 591557 8192 875295639 1863 _ (by decide) (by decide) (by decide) MertensMasks.mask591557 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b599749 : B 599749 607941 847499467 1854 := block_of_mask 599749 8192 847499467 1854 _ (by decide) (by decide) (by decide) MertensMasks.mask599749 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b607941 : B 607941 616133 825006280 1854 := block_of_mask 607941 8192 825006280 1854 _ (by decide) (by decide) (by decide) MertensMasks.mask607941 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b616133 : B 616133 624325 804745340 1857 := block_of_mask 616133 8192 804745340 1857 _ (by decide) (by decide) (by decide) MertensMasks.mask616133 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b624325 : B 624325 632517 755669710 1791 := block_of_mask 624325 8192 755669710 1791 _ (by decide) (by decide) (by decide) MertensMasks.mask624325 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b632517 : B 632517 640709 735443953 1788 := block_of_mask 632517 8192 735443953 1788 _ (by decide) (by decide) (by decide) MertensMasks.mask632517 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b640709 : B 640709 648901 734699392 1833 := block_of_mask 640709 8192 734699392 1833 _ (by decide) (by decide) (by decide) MertensMasks.mask640709 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b648901 : B 648901 657093 717673069 1836 := block_of_mask 648901 8192 717673069 1836 _ (by decide) (by decide) (by decide) MertensMasks.mask648901 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b657093 : B 657093 665285 710119373 1863 := block_of_mask 657093 8192 710119373 1863 _ (by decide) (by decide) (by decide) MertensMasks.mask657093 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b665285 : B 665285 673477 676047257 1818 := block_of_mask 665285 8192 676047257 1818 _ (by decide) (by decide) (by decide) MertensMasks.mask665285 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b673477 : B 673477 681669 666356011 1836 := block_of_mask 673477 8192 666356011 1836 _ (by decide) (by decide) (by decide) MertensMasks.mask673477 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b681669 : B 681669 689861 647460435 1827 := block_of_mask 681669 8192 647460435 1827 _ (by decide) (by decide) (by decide) MertensMasks.mask681669 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b689861 : B 689861 698053 637417235 1842 := block_of_mask 689861 8192 637417235 1842 _ (by decide) (by decide) (by decide) MertensMasks.mask689861 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b698053 : B 698053 706245 614409148 1818 := block_of_mask 698053 8192 614409148 1818 _ (by decide) (by decide) (by decide) MertensMasks.mask698053 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t1_0 : B 0 9925 315713513703116041 70005247 := @join 0 1733 9925 315684388066545112 61977157 29125636570929 8028090 b0 b1733
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t1_9925 : B 9925 26309 3230369698094 37663 := @join 9925 18117 26309 2372414246126 31823 857955451968 5840 b9925 b18117
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t1_26309 : B 26309 42693 700959541230 5254 := @join 26309 34501 42693 437660667119 2923 263298874111 2331 b26309 b34501
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t1_42693 : B 42693 59077 298846209037 4530 := @join 42693 50885 59077 172294407118 2247 126551801919 2283 b42693 b50885
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t1_59077 : B 59077 75461 163917320243 4386 := @join 59077 67269 75461 91842249504 2190 72075070739 2196 b59077 b67269
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t1_75461 : B 75461 91845 104045779907 4323 := @join 75461 83653 91845 57806621944 2190 46239157963 2133 b75461 b83653
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t1_91845 : B 91845 108229 71646436091 4266 := @join 91845 100037 108229 39171378441 2157 32475057650 2109 b91845 b100037
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t1_108229 : B 108229 124613 52032154569 4212 := @join 108229 116421 124613 27739806786 2097 24292347783 2115 b108229 b116421
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t1_124613 : B 124613 140997 39712903896 4188 := @join 124613 132805 140997 21027325430 2088 18685578466 2100 b124613 b132805
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t1_140997 : B 140997 157381 30983204289 4128 := @join 140997 149189 157381 16177504100 2043 14805700189 2085 b140997 b149189
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t1_157381 : B 157381 173765 24471029322 4017 := @join 157381 165573 173765 12814603288 2004 11656426034 2013 b157381 b165573
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t1_173765 : B 173765 190149 20683924400 4101 := @join 173765 181957 190149 10694226100 2028 9989698300 2073 b173765 b181957
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t1_190149 : B 190149 206533 17006919120 4008 := @join 190149 198341 206533 8881053502 2010 8125865618 1998 b190149 b198341
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t1_206533 : B 206533 222917 14482523297 3999 := @join 206533 214725 222917 7601219234 2022 6881304063 1977 b206533 b214725
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t1_222917 : B 222917 239301 12356005794 3951 := @join 222917 231109 239301 6617047482 2046 5738958312 1905 b222917 b231109
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t1_239301 : B 239301 255685 10902504860 4002 := @join 239301 247493 255685 5623474206 1998 5279030654 2004 b239301 b247493
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t1_255685 : B 255685 272069 9422773436 3936 := @join 255685 263877 272069 4742146580 1920 4680626856 2016 b255685 b263877
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t1_272069 : B 272069 288453 8184862977 3852 := @join 272069 280261 288453 4223085000 1932 3961777977 1920 b272069 b280261
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t1_288453 : B 288453 304837 7379865216 3894 := @join 288453 296645 304837 3770966449 1935 3608898767 1959 b288453 b296645
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t1_304837 : B 304837 321221 6691708241 3933 := @join 304837 313029 321221 3370045257 1929 3321662984 2004 b304837 b313029
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t1_321221 : B 321221 337605 5985894428 3894 := @join 321221 329413 337605 3085788255 1959 2900106173 1935 b321221 b329413
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t1_337605 : B 337605 353989 5387738920 3864 := @join 337605 345797 353989 2736650603 1917 2651088317 1947 b337605 b345797
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t1_353989 : B 353989 370373 4788793935 3765 := @join 353989 362181 370373 2453875078 1887 2334918857 1878 b353989 b362181
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t1_370373 : B 370373 386757 4470585500 3843 := @join 370373 378565 386757 2271773624 1911 2198811876 1932 b370373 b378565
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t1_386757 : B 386757 403141 4050847787 3789 := @join 386757 394949 403141 2103582283 1929 1947265504 1860 b386757 b394949
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t1_403141 : B 403141 419525 3735276076 3792 := @join 403141 411333 419525 1883967685 1875 1851308391 1917 b403141 b411333
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t1_419525 : B 419525 435909 3519296513 3864 := @join 419525 427717 435909 1739047007 1872 1780249506 1992 b419525 b427717
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t1_435909 : B 435909 452293 3176549532 3759 := @join 435909 444101 452293 1628728215 1893 1547821317 1866 b435909 b444101
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t1_452293 : B 452293 468677 2897017204 3687 := @join 452293 460485 468677 1442562688 1803 1454454516 1884 b452293 b460485
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t1_468677 : B 468677 485061 2781261614 3792 := @join 468677 476869 485061 1449549695 1944 1331711919 1848 b468677 b476869
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t1_485061 : B 485061 501445 2605706418 3804 := @join 485061 493253 501445 1310062950 1881 1295643468 1923 b485061 b493253
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t1_501445 : B 501445 517829 2384457545 3717 := @join 501445 509637 517829 1185393744 1818 1199063801 1899 b501445 b509637
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t1_517829 : B 517829 534213 2261323165 3753 := @join 517829 526021 534213 1150936623 1881 1110386542 1872 b517829 b526021
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t1_534213 : B 534213 550597 2073691887 3660 := @join 534213 542405 550597 1052461202 1830 1021230685 1830 b534213 b542405
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t1_550597 : B 550597 566981 1968739711 3687 := @join 550597 558789 566981 999612097 1845 969127614 1842 b550597 b558789
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t1_566981 : B 566981 583365 1885084377 3741 := @join 566981 575173 583365 953668922 1866 931415455 1875 b566981 b575173
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t1_583365 : B 583365 599749 1770991902 3717 := @join 583365 591557 599749 895696263 1854 875295639 1863 b583365 b591557
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t1_599749 : B 599749 616133 1672505747 3708 := @join 599749 607941 616133 847499467 1854 825006280 1854 b599749 b607941
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t1_616133 : B 616133 632517 1560415050 3648 := @join 616133 624325 632517 804745340 1857 755669710 1791 b616133 b624325
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t1_632517 : B 632517 648901 1470143345 3621 := @join 632517 640709 648901 735443953 1788 734699392 1833 b632517 b640709
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t1_648901 : B 648901 665285 1427792442 3699 := @join 648901 657093 665285 717673069 1836 710119373 1863 b648901 b657093
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t1_665285 : B 665285 681669 1342403268 3654 := @join 665285 673477 681669 676047257 1818 666356011 1836 b665285 b673477
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t1_681669 : B 681669 698053 1284877670 3669 := @join 681669 689861 698053 647460435 1827 637417235 1842 b681669 b689861
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t2_0 : B 0 26309 315716744072814135 70042910 := @join 0 9925 26309 315713513703116041 70005247 3230369698094 37663 t1_0 t1_9925
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t2_26309 : B 26309 59077 999805750267 9784 := @join 26309 42693 59077 700959541230 5254 298846209037 4530 t1_26309 t1_42693
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t2_59077 : B 59077 91845 267963100150 8709 := @join 59077 75461 91845 163917320243 4386 104045779907 4323 t1_59077 t1_75461
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t2_91845 : B 91845 124613 123678590660 8478 := @join 91845 108229 124613 71646436091 4266 52032154569 4212 t1_91845 t1_108229
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t2_124613 : B 124613 157381 70696108185 8316 := @join 124613 140997 157381 39712903896 4188 30983204289 4128 t1_124613 t1_140997
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t2_157381 : B 157381 190149 45154953722 8118 := @join 157381 173765 190149 24471029322 4017 20683924400 4101 t1_157381 t1_173765
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t2_190149 : B 190149 222917 31489442417 8007 := @join 190149 206533 222917 17006919120 4008 14482523297 3999 t1_190149 t1_206533
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t2_222917 : B 222917 255685 23258510654 7953 := @join 222917 239301 255685 12356005794 3951 10902504860 4002 t1_222917 t1_239301
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t2_255685 : B 255685 288453 17607636413 7788 := @join 255685 272069 288453 9422773436 3936 8184862977 3852 t1_255685 t1_272069
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t2_288453 : B 288453 321221 14071573457 7827 := @join 288453 304837 321221 7379865216 3894 6691708241 3933 t1_288453 t1_304837
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t2_321221 : B 321221 353989 11373633348 7758 := @join 321221 337605 353989 5985894428 3894 5387738920 3864 t1_321221 t1_337605
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t2_353989 : B 353989 386757 9259379435 7608 := @join 353989 370373 386757 4788793935 3765 4470585500 3843 t1_353989 t1_370373
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t2_386757 : B 386757 419525 7786123863 7581 := @join 386757 403141 419525 4050847787 3789 3735276076 3792 t1_386757 t1_403141
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t2_419525 : B 419525 452293 6695846045 7623 := @join 419525 435909 452293 3519296513 3864 3176549532 3759 t1_419525 t1_435909
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t2_452293 : B 452293 485061 5678278818 7479 := @join 452293 468677 485061 2897017204 3687 2781261614 3792 t1_452293 t1_468677
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t2_485061 : B 485061 517829 4990163963 7521 := @join 485061 501445 517829 2605706418 3804 2384457545 3717 t1_485061 t1_501445
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t2_517829 : B 517829 550597 4335015052 7413 := @join 517829 534213 550597 2261323165 3753 2073691887 3660 t1_517829 t1_534213
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t2_550597 : B 550597 583365 3853824088 7428 := @join 550597 566981 583365 1968739711 3687 1885084377 3741 t1_550597 t1_566981
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t2_583365 : B 583365 616133 3443497649 7425 := @join 583365 599749 616133 1770991902 3717 1672505747 3708 t1_583365 t1_599749
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t2_616133 : B 616133 648901 3030558395 7269 := @join 616133 632517 648901 1560415050 3648 1470143345 3621 t1_616133 t1_632517
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t2_648901 : B 648901 681669 2770195710 7353 := @join 648901 665285 681669 1427792442 3699 1342403268 3654 t1_648901 t1_665285
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t2_681669 : B 681669 706245 1899286818 5487 := @join 681669 698053 706245 1284877670 3669 614409148 1818 t1_681669 b698053
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t3_0 : B 0 59077 315717743878564402 70052694 := @join 0 26309 59077 315716744072814135 70042910 999805750267 9784 t2_0 t2_26309
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t3_59077 : B 59077 124613 391641690810 17187 := @join 59077 91845 124613 267963100150 8709 123678590660 8478 t2_59077 t2_91845
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t3_124613 : B 124613 190149 115851061907 16434 := @join 124613 157381 190149 70696108185 8316 45154953722 8118 t2_124613 t2_157381
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t3_190149 : B 190149 255685 54747953071 15960 := @join 190149 222917 255685 31489442417 8007 23258510654 7953 t2_190149 t2_222917
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t3_255685 : B 255685 321221 31679209870 15615 := @join 255685 288453 321221 17607636413 7788 14071573457 7827 t2_255685 t2_288453
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t3_321221 : B 321221 386757 20633012783 15366 := @join 321221 353989 386757 11373633348 7758 9259379435 7608 t2_321221 t2_353989
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t3_386757 : B 386757 452293 14481969908 15204 := @join 386757 419525 452293 7786123863 7581 6695846045 7623 t2_386757 t2_419525
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t3_452293 : B 452293 517829 10668442781 15000 := @join 452293 485061 517829 5678278818 7479 4990163963 7521 t2_452293 t2_485061
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t3_517829 : B 517829 583365 8188839140 14841 := @join 517829 550597 583365 4335015052 7413 3853824088 7428 t2_517829 t2_550597
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t3_583365 : B 583365 648901 6474056044 14694 := @join 583365 616133 648901 3443497649 7425 3030558395 7269 t2_583365 t2_616133
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t3_648901 : B 648901 706245 4669482528 12840 := @join 648901 681669 706245 2770195710 7353 1899286818 5487 t2_648901 t2_681669
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t4_0 : B 0 124613 315718135520255212 70069881 := @join 0 59077 124613 315717743878564402 70052694 391641690810 17187 t3_0 t3_59077
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t4_124613 : B 124613 255685 170599014978 32394 := @join 124613 190149 255685 115851061907 16434 54747953071 15960 t3_124613 t3_190149
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t4_255685 : B 255685 386757 52312222653 30981 := @join 255685 321221 386757 31679209870 15615 20633012783 15366 t3_255685 t3_321221
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t4_386757 : B 386757 517829 25150412689 30204 := @join 386757 452293 517829 14481969908 15204 10668442781 15000 t3_386757 t3_452293
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t4_517829 : B 517829 648901 14662895184 29535 := @join 517829 583365 648901 8188839140 14841 6474056044 14694 t3_517829 t3_583365
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t5_0 : B 0 255685 315718306119270190 70102275 := @join 0 124613 255685 315718135520255212 70069881 170599014978 32394 t4_0 t4_124613
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t5_255685 : B 255685 517829 77462635342 61185 := @join 255685 386757 517829 52312222653 30981 25150412689 30204 t4_255685 t4_386757
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t5_517829 : B 517829 706245 19332377712 42375 := @join 517829 648901 706245 14662895184 29535 4669482528 12840 t4_517829 t3_648901
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t6_0 : B 0 517829 315718383581905532 70163460 := @join 0 255685 517829 315718306119270190 70102275 77462635342 61185 t5_0 t5_255685
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t7_0 : B 0 706245 315718402914283244 70205835 := @join 0 517829 706245 315718383581905532 70163460 19332377712 42375 t6_0 t5_517829
theorem checked : B 0 706245 315718402914283244 70205835 := t7_0
end MertensCertificate

open Filter Real
open scoped Topology
noncomputable section
namespace GammaCertificate

private def c (b : Bool) (t : ℝ) : ℝ :=
  -t/2+t^2/12-(if b then t^4/120 else 0)
private def cp (b : Bool) (t : ℝ) : ℝ :=
  -1/2+t/6-(if b then t^3/30 else 0)
private theorem dc (b : Bool) (t : ℝ) : HasDerivAt (c b) (cp b t) t := by
  have h := hasDerivAt_id t
  cases b
  · convert (((h.neg.div_const 2).add ((h.pow 2).div_const 12)).sub (hasDerivAt_const t (0 : ℝ))) using 1
    · funext x; rfl
    · simp [cp]; ring
  · convert (((h.neg.div_const 2).add ((h.pow 2).div_const 12)).sub ((h.pow 4).div_const 120)) using 1
    · funext x; rfl
    · simp [cp]; ring

private def gap (b : Bool) (t : ℝ) :=
  t/(1+t) - log (1+t) + c b (t/(1+t)) - c b t
private def gp (b : Bool) (t : ℝ) :=
  if b then t^6*(5+5*t+t^2)/(30*(1+t)^5) else -t^4/(6*(1+t)^3)

private theorem dg (b : Bool) (t : ℝ) (ht : 0 ≤ t) : HasDerivAt (gap b) (gp b t) t := by
  have hn : 1+t ≠ 0 := by positivity
  have h := hasDerivAt_id t
  have h1 := h.const_add 1
  have hu := h.div h1 hn
  convert (((hu.sub (h1.log hn)).add ((dc b _).comp t hu)).sub (dc b t)) using 1
  · funext x; rfl
  · cases b <;> simp [gp,cp,Pi.div_apply] <;> field_simp <;> ring

private theorem gsign (t : ℝ) (ht : 0 ≤ t) : gap false t ≤ 0 ∧ 0 ≤ gap true t := by
  have hcont (b : Bool) : ContinuousOn (gap b) (Set.Ici 0) := fun x hx => (dg b x hx).continuousAt.continuousWithinAt
  have hd (b : Bool) (x : ℝ) (hx : x ∈ interior (Set.Ici (0 : ℝ))) :=
    (dg b x (interior_subset hx)).hasDerivWithinAt (s := interior (Set.Ici (0 : ℝ)))
  have ha := antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici (0 : ℝ)) (hcont false) (hd false) (by
    intro x hx; have h : 0 ≤ x := interior_subset hx; change -x^4/(6*(1+x)^3) ≤ 0; exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) (by positivity))
  have hm := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici (0 : ℝ)) (hcont true) (hd true) (by
    intro x hx; have h : 0 ≤ x := interior_subset hx; simp only [gp, ↓reduceIte]; positivity)
  exact ⟨by simpa [gap,c] using ha (show (0 : ℝ) ∈ Set.Ici 0 from by simp) ht ht,
    by simpa [gap,c] using hm (show (0 : ℝ) ∈ Set.Ici 0 from by simp) ht ht⟩

private def f (b : Bool) (n : ℕ) : ℝ :=
  (harmonic (n+1) : ℝ)-log (n+1)+c b (1/(n+1))

private theorem diff (b : Bool) (n : ℕ) : f b (n+1) - f b n = gap b (1/(n+1)) := by
  let x : ℝ := n+1
  have hx : 0 < x := by dsimp [x]; positivity
  have hy : 0 < x+1 := by positivity
  have hl : log (x+1) - log x = log (1+1/x) := by
    rw [← log_div hy.ne' hx.ne']; congr 1; field_simp
  have hr : (1/x)/(1+1/x) = 1/(x+1) := by field_simp
  simp only [f,gap, harmonic_succ (n+1), Rat.cast_add, Rat.cast_inv, Rat.cast_natCast, Nat.cast_add_one]
  change (↑(harmonic (n+1)) + (x+1)⁻¹ - log (x+1) + c b (1/(x+1))) -
    (↑(harmonic (n+1)) - log x + c b (1/x)) = _
  change _ = (1/x)/(1+1/x)-log (1+1/x)+c b ((1/x)/(1+1/x))-c b (1/x)
  rw [hr, ← hl]; ring

private theorem limf (b : Bool) : Tendsto (f b) atTop (𝓝 eulerMascheroniConstant) := by
  have ha := Real.tendsto_harmonic_sub_log.comp (tendsto_add_atTop_nat 1)
  have hb : Tendsto (fun n : ℕ => 1/((n:ℝ)+1)) atTop (𝓝 0) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hc := ((dc b 0).continuousAt.tendsto).comp hb
  unfold f
  simpa [Function.comp_def,c] using ha.add hc

theorem gamma_bounds : 0.57721565 < eulerMascheroniConstant ∧ eulerMascheroniConstant < 0.57721568 := by
  have hu : Antitone (f false) := antitone_nat_of_succ_le (fun n => by
    exact sub_nonpos.mp ((diff false n).trans_le (gsign _ (by positivity)).1))
  have hl : Monotone (f true) := monotone_nat_of_le_succ (fun n => by
    apply sub_nonneg.mp; rw [diff]; exact (gsign _ (by positivity)).2)
  have ub := hu.le_of_tendsto (limf false) 63
  have lb := hl.ge_of_tendsto (limf true) 63
  have hr : (4.7438909036 : ℝ) < (harmonic 64 : ℝ) ∧ (harmonic 64 : ℝ) < 4.743890904 := by norm_num [harmonic,Finset.sum_range_succ]
  have hlog : log 64 = 6 * log 2 := by
    rw [show (64 : ℝ) = 2^6 by norm_num, log_pow]; norm_num
  norm_num [f,c] at ub lb
  constructor <;> linarith [Real.log_two_gt_d9, Real.log_two_lt_d9, hr.1, hr.2]

end GammaCertificate

namespace MertensPrimeTail

theorem correction_bounds {p : ℝ} (hp : 1 < p) :
    0 ≤ -(Real.log (1-1/p) + 1/p) ∧
    -(Real.log (1-1/p) + 1/p) ≤ 1/(2*(p-1)) - 1/(2*p) := by
  have hp0 : 0 < p := by linarith
  have hm : 0 < p-1 := by linarith
  have hz : 1-1/p = (p/(p-1))⁻¹ := by field_simp
  have hx : 1 ≤ p/(p-1) := (le_div_iff₀ hm).2 (by linarith)
  constructor
  · have h := Real.log_le_sub_one_of_pos (show 0 < 1-1/p by rw [hz]; positivity)
    linarith
  · have h := Real.self_le_sinh_iff.mpr (Real.log_nonneg hx)
    rw [Real.sinh_eq, Real.exp_neg, Real.exp_log (by positivity : 0 < p/(p-1))] at h
    rw [hz,Real.log_inv]
    calc
      -(-Real.log (p/(p-1))+1/p) ≤ ((p/(p-1))-(p/(p-1))⁻¹)/2-1/p := by linarith
      _ = _ := by field_simp; ring

end MertensPrimeTail

namespace MertensPrimeTail
noncomputable def after (K i : ℕ) : ℝ :=
  if (K+i+1).Prime then -(Real.log (1-1/(K+i+1:ℝ))+1/(K+i+1:ℝ)) else 0

theorem tail_sum {K : ℕ} (hK : 0 < K) :
    Summable (after K) ∧ (∑' i, after K i) ≤ 1/(2*(K:ℝ)) := by
  let B (i : ℕ) : ℝ := 1/(2*((K:ℝ)+i))
  have hh (i : ℕ) : 0 ≤ after K i ∧ after K i ≤ B i - B (i+1) := by
    have h : (1:ℝ) < K+i+1 := by
      have hk : (0:ℝ) < K := by exact_mod_cast hK
      linarith [Nat.cast_nonneg (α := ℝ) i]
    have hp := correction_bounds h
    have he : (K:ℝ)+i+1-1 = K+i := by ring
    simp only [he] at hp
    simp only [after, B, Nat.cast_add, Nat.cast_one]
    split_ifs
    · exact ⟨hp.1, by simpa only [add_assoc] using hp.2⟩
    · exact ⟨le_rfl, by simpa only [add_assoc] using hp.1.trans hp.2⟩
  have hs (n : ℕ) : ∑ i ∈ Finset.range n, after K i ≤ B 0 - B n := by
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ]; linarith [(hh n).2]
  have bound (n : ℕ) : ∑ i ∈ Finset.range n, after K i ≤ 1/(2*(K:ℝ)) := by
    have hn : 0 ≤ B n := by dsimp [B]; positivity
    simpa [B] using (hs n).trans (sub_le_self _ hn)
  exact ⟨summable_of_sum_range_le (fun i => (hh i).1) bound, Real.tsum_le_of_sum_range_le (fun i => (hh i).1) bound⟩
end MertensPrimeTail


namespace MertensAssembly

noncomputable def correction (n : ℕ) : ℝ :=
  -(Real.log (1-1/(n:ℝ))+1/(n:ℝ))

noncomputable def term (n : ℕ) : ℝ :=
  if n.Prime then correction n else 0

theorem assemble {K : ℕ} {tail : ℕ → ℝ}
    (shift : ∀ i, term (i+(K+1)) = tail i)
    (hs : Summable tail)
    (ht : 0 ≤ ∑' i, tail i)
    (hu : (∑' i, tail i) ≤ 1/(2*(K:ℝ)))
    (hK : 3000000 ≤ K)
    (hp₁ : 0.31571843 ≤ ∑ n ∈ Finset.range (K+1), term n)
    (hp₂ : (∑ n ∈ Finset.range (K+1), term n) ≤ 0.31571845)
    (hg : 0.57721565 < Real.eulerMascheroniConstant ∧ Real.eulerMascheroniConstant < 0.57721568) :
    let x : ℝ := Real.eulerMascheroniConstant + ∑' p : Nat.Primes, (Real.log (1-1/(p:ℝ))+1/(p:ℝ))
    0.261497 ≤ x ∧ x ≤ 0.261498 := by
  have he : (fun i => term (i+(K+1))) = tail := funext shift
  have hfull : Summable term := (summable_nat_add_iff (K+1)).1 (he ▸ hs)
  have hsplit := hfull.sum_add_tsum_nat_add (K+1)
  rw [he] at hsplit
  have hpr : (∑' p : Nat.Primes, correction p) = ∑' n, term n :=
    Nat.Primes.tsum_eq_tsum_ite correction
  have hneg : (∑' p : Nat.Primes, (Real.log (1-1/(p:ℝ))+1/(p:ℝ))) = -(∑' n, term n) := by
    rw [← hpr, ← tsum_neg]
    congr 1; funext p; simp [correction]
  dsimp only
  rw [hneg, ← hsplit]
  have hreal : (3000000 : ℝ) ≤ K := by exact_mod_cast hK
  have hinv : 1/(2*(K:ℝ)) ≤ 1/6000000 := by
    apply one_div_le_one_div_of_le (by norm_num : (0:ℝ)<6000000)
    linarith
  constructor <;> linarith [hg.1,hg.2]

end MertensAssembly
namespace MertensSix
open Finset MertensPrimeTail
private abbrev K := 706244
private noncomputable def S (n : ℕ) : ℝ := 1 / (6*(706238+6*(n:ℝ)))

private theorem alive (n j : ℕ) (hn : j < 6) (hp : Nat.Prime (K+(6*n+j)+1)) : j=2 ∨ j=4 := by
  have h2 : ¬ 2 ∣ (K+(6*n+j)+1) := by
    intro h; have := (Nat.dvd_prime hp).1 h; unfold K at *; omega
  have h3 : ¬ 3 ∣ (K+(6*n+j)+1) := by
    intro h; have := (Nat.dvd_prime hp).1 h; unfold K at *; omega
  unfold K at *; omega

private theorem pos (i : ℕ) : 0 ≤ after K i := by
  simp only [after]; split_ifs
  · apply (correction_bounds _).1
    change (1 : ℝ) < 706244 + (i:ℝ) + 1
    linarith [Nat.cast_nonneg i (α := ℝ)]
  · exact le_rfl

private theorem single (n j : ℕ) : after K (6*n+j) ≤ (S n-S (n+1))/2 := by
  let x : ℝ := 706238+6*(n:ℝ)
  let p : ℝ := (K:ℝ)+(6*(n:ℝ)+j)+1
  have hx : 0 < x := by dsimp [x]; positivity
  have hp : x+6 ≤ p-1 := by dsimp [x,p,K]; linarith [Nat.cast_nonneg j (α:=ℝ)]
  have hp1 : 1 < p := by linarith
  have hh : (S n - S (n+1))/2 = 1/(2*x*(x+6)) := by
    unfold S; push_cast; dsimp [x]; field_simp; ring
  rw [hh]
  simp only [after]
  split_ifs
  · have ht := (correction_bounds hp1).2
    have he : 1/(2*(p-1))-1/(2*p) = 1/(2*(p-1)*p) := by
      field_simp; ring
    rw [he] at ht
    have hab : 1/(2*(p-1)*p) ≤ 1/(2*x*(x+6)) := by
      apply one_div_le_one_div_of_le (by positivity)
      gcongr <;> linarith
    simpa [p] using ht.trans hab
  · positivity

private theorem six (n : ℕ) :
    ∑ j ∈ range 6, after K (6*n+j) ≤ S n - S (n+1) := by
  have hz (j : ℕ) (hj : j<6) (h2 : j≠2) (h4 : j≠4) : after K (6*n+j) = 0 := by
    have h : ¬ (K+(6*n+j)+1).Prime := fun h => (alive n j hj h).elim h2 h4
    simp [after,h]
  rw [show (6:ℕ) = 5+1 by decide, sum_range_succ, sum_range_succ, sum_range_succ, sum_range_succ, sum_range_succ, sum_range_succ]
  simp only [range_zero,sum_empty]
  rw [hz 0 (by decide) (by decide) (by decide),hz 1 (by decide) (by decide) (by decide),hz 3 (by decide) (by decide) (by decide),hz 5 (by decide) (by decide) (by decide)]
  linarith [single n 2,single n 4]

theorem tailSix : (∑' i, after K i) ≤ 1/(6*706238) := by
  have h (n : ℕ) : ∑ i ∈ range (6*n), after K i ≤ S 0 - S n := by
    induction n with
    | zero => simp
    | succ n ih => rw [Nat.mul_succ,sum_range_add]; linarith [six n]
  apply Real.tsum_le_of_sum_range_le pos
  intro n
  have hle : ∑ i ∈ range n, after K i ≤ ∑ i ∈ range (6*n), after K i :=
    sum_le_sum_of_subset_of_nonneg (range_mono (by omega)) (fun i _ _ => pos i)
  have hs : 0 ≤ S n := by unfold S; positivity
  simpa [S] using (hle.trans (h n)).trans (sub_le_self _ hs)


open MertensAssembly
theorem of_prefix
    (hp₁ : (315718402914283244:ℝ)/10^18 ≤ ∑ n ∈ range (K+1), term n)
    (hp₂ : (∑ n ∈ range (K+1), term n) ≤ ((315718402914283244:ℝ)+70205835)/10^18) :
    let x : ℝ := Real.eulerMascheroniConstant + ∑' p : Nat.Primes, (Real.log (1-1/(p:ℝ))+1/(p:ℝ))
    0.261497 ≤ x ∧ x ≤ 0.261498 := by
  have he : (fun i => term (i+(K+1))) = after K := by
    funext i
    simp [term,correction,after,add_comm,add_left_comm]
  have hfull : Summable term := (summable_nat_add_iff (K+1)).1 (he ▸ (tail_sum (K:=K) (by decide)).1)
  have hsplit := hfull.sum_add_tsum_nat_add (K+1)
  rw [he] at hsplit
  have hpr : (∑' p : Nat.Primes, correction p) = ∑' n, term n :=
    Nat.Primes.tsum_eq_tsum_ite correction
  have hneg : (∑' p : Nat.Primes, (Real.log (1-1/(p:ℝ))+1/(p:ℝ))) = -(∑' n, term n) := by
    rw [← hpr, ← tsum_neg]
    congr 1; funext p; simp [correction]
  dsimp only
  rw [hneg, ← hsplit]
  have hp0 : 0 ≤ ∑' i, after K i := tsum_nonneg pos
  have hg := GammaCertificate.gamma_bounds
  constructor <;> linarith [hg.1,hg.2,tailSix]

end MertensSix

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem Conjectures.Cuts.Taskb182870585b8412c8aff946c : (have x1 : ℝ := Real.eulerMascheroniConstant + ∑' (x1 : Nat.Primes), (Real.log ((1 : ℝ) - (1 : ℝ) / ↑↑x1) + (1 : ℝ) / ↑↑x1); 0.261497 ≤ x1 ∧ x1 ≤ 0.261498) := by
  have h := @MertensFold.bounds 706244 315718402914283244 70205835 MertensCertificate.checked
  have term_eq : MertensFold.term = MertensAssembly.term := by
    funext p
    rfl
  simp only [term_eq, MertensPrefix.scale, Nat.cast_pow, Nat.cast_ofNat] at h
  exact MertensSix.of_prefix h.1 h.2


theorem Conjectures.Cuts.Taskcefe2059e65427cfde299eb2 :
have x1 : ℝ := Real.eulerMascheroniConstant + ∑' (x1 : Nat.Primes), (Real.log ((1 : ℝ) - (1 : ℝ) / (↑(↑x1 : ℕ) : ℝ)) + (1 : ℝ) / (↑(↑x1 : ℕ) : ℝ)); ∀ (x2 : ℝ), (2 : ℝ) ≤ x2 → x2 ≤ Real.exp (10 : ℝ) → Real.log (Real.log x2) + x1 - 2964e-9 / Real.log x2 ≤ ∑ x5 ∈ Finset.range ⌈x2⌉₊ with Nat.Prime x5, (1 : ℝ) / (↑x5 : ℝ) ∧ ∑ x5 ∈ Finset.range ⌈x2⌉₊ with Nat.Prime x5, (1 : ℝ) / (↑x5 : ℝ) ≤ Real.log (Real.log x2) + x1 + if Real.log x2 > 8.9 then 1614e-6 else (1 : ℝ) := by
  exact (Conjectures.Cuts.Cutdde1e7ef243203eb1faa06c9
    Conjectures.Cuts.Taskb182870585b8412c8aff946c
    Conjectures.Cuts.Task8f9f08650abf4d04bfa7122e
    Conjectures.Cuts.Taskabc64269ad130e923b36a98e).2
