import Conjectures.Goldbach.EstermannAlmostAllPolylog
import Conjectures.Goldbach.ThreeQuartersExceptionalDirichletWindows

/-! A polynomial exceptional-set bound for the minor-arc term of the
binary Goldbach problem, uniform in the lower endpoint of the prime sum.
The argument is the Vaughan–Bessel estimate of Pintz, arXiv:1804.09084,
§2, equation (2.6). The reduced-approximant and prime-power comparisons
are adapted from the repository's EstermannAlmostAllPolylog (Apache-2.0). -/

namespace Conjectures.Goldbach.PolynomialArcExceptionalCount

open Finset Filter MeasureTheory
open Conjectures.Goldbach.EstermannAlmostAllPolylog_aux
open GoldbachMovingWindows (primeLog primeLog_energy)
open scoped BigOperators Topology

noncomputable section

def wave (z : ℝ) := Complex.exp (((2*Real.pi*z : ℝ) : ℂ)*Complex.I)
def series (n : ℕ) (u : ℕ → ℝ) (t : ℝ) := ∑ k ∈ range (n+1), (u k : ℂ)*wave ((k : ℝ)*t)
def tailWeight (Y k : ℕ) := if Y < k then primeLog k else 0
def arcs (n P : ℕ) := {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ P ∧ a ≤ q ∧ a.Coprime q ∧
  |t-(a : ℝ)/q| ≤ (P : ℝ)/((q : ℝ)*n)}
def coeff (n Y m : ℕ) (A : Set ℝ) := intervalIntegral (A.indicator
  (fun t => (series n (tailWeight Y) t)^2 * wave (-(m : ℝ)*t))) 0 1 volume

private theorem vaughan_denominator_terms {x q P T : ℝ} (hx : 0 < x) (hT : 0 < T)
    (hP : 0 < P) (hTsize : T ≤ Real.sqrt P) (hlow : P ≤ q) (hhigh : q ≤ x/P) :
    x / Real.sqrt q ≤ x/T ∧ Real.sqrt (x*q) ≤ x/T := by
  have hq := hP.trans_le hlow
  have hT2 : T^2 ≤ P := (Real.le_sqrt (by positivity) hP.le).mp hTsize
  constructor
  · exact div_le_div_of_nonneg_left hx.le hT (hTsize.trans (Real.sqrt_le_sqrt hlow))
  · apply (Real.sqrt_le_iff).mpr
    refine ⟨by positivity, ?_⟩
    rw [div_pow, le_div_iff₀ (by positivity)]
    have hprod := (le_div_iff₀ hP).mp hhigh
    nlinarith only [mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hT2 hq.le) hx.le,
      mul_le_mul_of_nonneg_left hprod hx.le]

private theorem minor_approximant (Q n : ℕ) (t : ℝ) (hQ : 1 ≤ Q) (hQn : Q ≤ n)
    (ht : t ∈ Set.Icc (0:ℝ) 1)
    (hminor : t ∉ {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Q ∧ a ≤ q ∧ a.Coprime q ∧
      |t - a/(q:ℝ)| ≤ (Q:ℝ)/(q*n)}) :
    ∃ q a : ℕ, Q < q ∧ q ≤ n / Q ∧ a ≤ q ∧ a.Coprime q ∧
      |t - a/(q:ℝ)| ≤ 1 / ((q:ℝ)*((n/Q : ℕ)+1 : ℝ)) := by
  let B := n / Q
  have hB : 0 < B := Nat.div_pos hQn hQ
  obtain ⟨s,hs,hd⟩ := Real.exists_rat_abs_sub_le_and_den_le t hB
  have hdpos : (0 : ℝ) < s.den := Nat.cast_pos.mpr s.pos
  have hBpos : (0 : ℝ) < B := Nat.cast_pos.mpr hB
  have hQB : (0 : ℝ) < Q := Nat.cast_pos.mpr hQ
  have hnp : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  rw [Rat.cast_def, mul_comm ((B : ℝ) + 1) (s.den : ℝ)] at hs
  have hclose : |t * s.den - s.num| < 1 := by
    have h := (mul_le_mul_of_nonneg_right hs hdpos.le)
    rw [← abs_of_pos hdpos, ← abs_mul, abs_of_pos hdpos] at h
    rw [sub_mul, div_mul_cancel₀ _ hdpos.ne'] at h
    refine h.trans_lt ?_
    rw [div_mul_eq_mul_div, one_mul, div_lt_one (by positivity)]
    nlinarith
  obtain ⟨hl,hu⟩ := abs_lt.mp hclose
  have ht0 : 0 ≤ t * s.den := mul_nonneg ht.1 hdpos.le
  have ht1 : t * s.den ≤ s.den := by simpa using mul_le_mul_of_nonneg_right ht.2 hdpos.le
  have hnlo : (-1 : ℤ) < s.num := by exact_mod_cast (show (-1 : ℝ) < s.num by linarith)
  have hnhi : s.num < (s.den : ℤ) + 1 := by exact_mod_cast (show (s.num : ℝ) < s.den + 1 by linarith)
  have hcast : (s.num.natAbs : ℤ) = s.num := by rw [Int.natCast_natAbs, abs_of_nonneg (by omega)]
  have hcast' : (s.num.natAbs : ℝ) = s.num := by
    calc (s.num.natAbs : ℝ) = ((s.num.natAbs : ℤ) : ℝ) := by simp
         _ = _ := congrArg (fun z : ℤ => (z : ℝ)) hcast
  have hle : s.num.natAbs ≤ s.den := by exact_mod_cast (show (s.num.natAbs : ℤ) ≤ s.den by omega)
  rw [← hcast'] at hs
  refine ⟨s.den, s.num.natAbs, ?_, hd, hle, s.reduced, hs⟩
  by_contra! hsmall
  apply hminor
  refine ⟨s.den, s.num.natAbs, s.pos, hsmall, hle, s.reduced, hs.trans ?_⟩
  have hbound : (n : ℝ) < Q * ((B : ℝ) + 1) := by exact_mod_cast Nat.lt_mul_div_succ n hQ
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith only [mul_le_mul_of_nonneg_left hbound.le hdpos.le]

private theorem mangoldt_pointwise_bridge (n : ℕ) (hn : 1 ≤ n) (t : ℝ) :
    let w := fun k : ℕ => if k.Prime then Real.log (k : ℝ) else 0
    let e := fun x : ℝ => Complex.exp (((2*Real.pi*x : ℝ):ℂ)*Complex.I)
    ‖∑ k ∈ Finset.range (n+1), ((ArithmeticFunction.vonMangoldt k - w k : ℝ):ℂ) * e ((k:ℝ)*t)‖ ≤
      2 * Real.sqrt n * Real.log n := by
  intro w e
  have hnon (k : ℕ) : 0 ≤ ArithmeticFunction.vonMangoldt k - w k := by
    by_cases hk : k.Prime <;> simp [w,hk,ArithmeticFunction.vonMangoldt_apply_prime]
  calc
    _ ≤ ∑ k ∈ Finset.range (n+1), ‖((ArithmeticFunction.vonMangoldt k - w k : ℝ):ℂ) * e ((k:ℝ)*t)‖ := norm_sum_le _ _
    _ = ∑ k ∈ Finset.range (n+1), (ArithmeticFunction.vonMangoldt k - w k) := by
      simp only [norm_mul,e,Complex.norm_exp_ofReal_mul_I,mul_one,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hnon _)]
    _ = Chebyshev.psi n - Chebyshev.theta n := by
      rw [Nat.range_succ_eq_Icc_zero, ← Finset.add_sum_Ioc_eq_sum_Icc (Nat.zero_le n)]
      simp [Chebyshev.psi,Chebyshev.theta,w,Finset.sum_filter,Finset.sum_sub_distrib]
    _ ≤ _ := Chebyshev.psi_sub_theta_le (by exact_mod_cast hn)

private theorem prime_mass (Y : ℕ) (t : ℝ) :
    ‖series Y primeLog t‖ ≤ 2*(Y : ℝ) := by
  have hnon (k : ℕ) : |primeLog k| = primeLog k := abs_of_nonneg (by
    by_cases hk : k.Prime <;> simp [GoldbachMovingWindows.primeLog,hk,Real.log_natCast_nonneg])
  have h4 : Real.log 4 ≤ 2 := by
    rw [show (4 : ℝ) = 2^2 by norm_num, Real.log_pow]
    norm_num1
    linarith [Real.log_two_lt_d9]
  calc
  _ ≤ ∑ k ∈ range (Y+1), ‖(primeLog k : ℂ)*wave ((k : ℝ)*t)‖ := norm_sum_le _ _
  _ = Chebyshev.theta Y := by
    simp only [wave, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, hnon]
    unfold GoldbachMovingWindows.primeLog
    rw [← Finset.sum_filter, Chebyshev.theta_eq_sum_primesLE_log]
    congr 1
  _ ≤ _ := (Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg Y)).trans
    (mul_le_mul_of_nonneg_right h4 (Nat.cast_nonneg Y))

private theorem prime_approx (Y q : ℕ) (t : ℝ) (hY : 1 ≤ Y)
    (h : ‖OAI.Problem337.Vaughan.weightedSum (Ioc 0 Y)
      (fun k => OAI.Problem337.VaughanBilinear.phase (t*k)) ArithmeticFunction.vonMangoldt‖ ≤
      16200*(Real.log Y)^4*OAI.Problem337.Vaughan.approximationEnvelope Y q) :
    ‖series Y primeLog t‖ ≤ 16200*(Real.log Y)^4*OAI.Problem337.Vaughan.approximationEnvelope Y q
      + 2*Real.sqrt Y*Real.log Y := by
  have heq : series Y ArithmeticFunction.vonMangoldt t =
      OAI.Problem337.Vaughan.weightedSum (Ioc 0 Y)
        (fun k => OAI.Problem337.VaughanBilinear.phase (t*k)) ArithmeticFunction.vonMangoldt := by
    dsimp [series,wave,OAI.Problem337.Vaughan.weightedSum,OAI.Problem337.VaughanBilinear.phase]
    rw [Nat.range_succ_eq_Icc_zero, ← Finset.add_sum_Ioc_eq_sum_Icc (Nat.zero_le Y)]
    simp only [ArithmeticFunction.map_zero,Complex.ofReal_zero,zero_mul,zero_add,Real.fourierChar_apply]
    apply Finset.sum_congr rfl
    intro k _; rw [mul_comm t (k : ℝ)]
  have herr : ‖series Y ArithmeticFunction.vonMangoldt t-series Y primeLog t‖ ≤
      2*Real.sqrt Y*Real.log Y := by
    simpa only [series, wave, GoldbachMovingWindows.primeLog, ← sum_sub_distrib, ← sub_mul,
      ← Complex.ofReal_sub] using mangoldt_pointwise_bridge Y hY t
  have htr := norm_sub_le (series Y ArithmeticFunction.vonMangoldt t)
    (series Y ArithmeticFunction.vonMangoldt t-series Y primeLog t)
  rw [sub_sub_cancel] at htr
  exact htr.trans (add_le_add (heq ▸ h) herr)

def scale (n P : ℕ) : ℝ := (n : ℝ)/Real.sqrt P+(n : ℝ)^(4/5 : ℝ)

/-- One reduced approximation controls all prefix lengths, including those
shorter than its denominator. This permits the lower cutoff in Pintz's sum. -/
theorem prefix_bound : ∀ᶠ n : ℕ in atTop, ∀ P : ℕ, 1 ≤ P → P ≤ n →
    ∀ t ∈ Set.Icc (0 : ℝ) 1, t ∉ arcs n P → ∀ Y ≤ n,
    ‖series Y primeLog t‖ ≤ 50000*(Real.log n)^4*scale n P := by
  obtain ⟨N,hN⟩ := eventually_atTop.1 OAI.Problem337.Vaughan.eventually_vonMangoldt_sum_log_bound
  have ht := tendsto_natCast_atTop_atTop (R := ℝ)
  filter_upwards [eventually_ge_atTop ((max N 1)^2),
    (Real.tendsto_log_atTop.comp ht).eventually_ge_atTop 1] with n hn hL
  intro P hP hPn t ht' hminor Y hYn
  have hpr : (0 : ℝ) < P := Nat.cast_pos.mpr hP
  have hnr : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hsr : 0 < Real.sqrt (P : ℝ) := Real.sqrt_pos.2 hpr
  have hs1 : 1 ≤ Real.sqrt (P : ℝ) := (Real.le_sqrt (by norm_num) hpr.le).2 (by exact_mod_cast hP)
  have hsP : Real.sqrt (P : ℝ) ≤ P := by
    nlinarith only [Real.sq_sqrt hpr.le, mul_nonneg (sub_nonneg.mpr hs1) hsr.le]
  have hns := Real.sqrt_le_sqrt (by exact_mod_cast hPn : (P : ℝ) ≤ n)
  have hroot : Real.sqrt (n : ℝ) ≤ (n : ℝ)/Real.sqrt P := by
    apply (le_div_iff₀ hsr).2
    exact (mul_le_mul_of_nonneg_left hns (Real.sqrt_nonneg _)).trans_eq (Real.mul_self_sqrt hnr.le)
  have hNn : (N : ℝ) ≤ Real.sqrt (n : ℝ) := by
    apply (Real.le_sqrt (Nat.cast_nonneg N) hnr.le).2
    exact_mod_cast (Nat.pow_le_pow_left (le_max_left N 1) 2).trans hn
  obtain ⟨q,a,hPq,hqB,_,hcop,happ⟩ := minor_approximant P n t hP hPn ht' hminor
  have hq : 0 < q := by omega
  have hqr : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hhigh : (q : ℝ) ≤ (n : ℝ)/P := (le_div_iff₀ hpr).2
    (by exact_mod_cast (Nat.le_div_iff_mul_le hP).1 hqB)
  have hcut : (n : ℝ)/Real.sqrt P ≤ scale n P := le_add_of_nonneg_right (Real.rpow_nonneg hnr.le _)
  have hB := div_le_div_of_nonneg_left hnr.le hsr hsP
  have hscale : 0 ≤ scale n P := by dsimp [scale]; positivity
  have hL' : 1 ≤ Real.log (n : ℝ) := hL
  have hl4 : 1 ≤ (Real.log n)^4 := one_le_pow₀ hL'
  by_cases hsmall : Y ≤ q ∨ Y ≤ N
  · have hY : (Y : ℝ) ≤ scale n P := hsmall.elim
      (fun h => (Nat.cast_le.mpr h).trans (hhigh.trans (hB.trans hcut)))
      (fun h => (Nat.cast_le.mpr h).trans (hNn.trans (hroot.trans hcut)))
    exact (prime_mass Y t).trans ((mul_le_mul_of_nonneg_left hY (by norm_num)).trans
      (mul_le_mul_of_nonneg_right (by linarith only [hl4]) hscale))
  push Not at hsmall
  have happrox : |t-(a:ℝ)/q| ≤ 1/(q:ℝ)^2 := by
    apply happ.trans
    apply one_div_le_one_div_of_le (by positivity)
    rw [sq]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.le_succ_of_le hqB) hqr.le
  have hval := hN Y hsmall.2.le t (a:ℤ) q hq hcop.isCoprime (by simpa using happrox) hsmall.1.le
  have hYp : 0 < Y := by omega
  have hYr : (0 : ℝ) < Y := Nat.cast_pos.mpr hYp
  have hYn' : (Y : ℝ) ≤ n := by exact_mod_cast hYn
  obtain ⟨hu,hv⟩ := vaughan_denominator_terms hnr hsr hpr le_rfl (by exact_mod_cast hPq.le) hhigh
  have hen : OAI.Problem337.Vaughan.approximationEnvelope Y q ≤ 2*scale n P := by
    dsimp [OAI.Problem337.Vaughan.approximationEnvelope,scale]
    have h₁ := (div_le_div_of_nonneg_right hYn' (Real.sqrt_nonneg _)).trans hu
    have h₂ := Real.rpow_le_rpow hYr.le hYn' (by norm_num : (0 : ℝ) ≤ 4/5)
    have h₃ := (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hYn' hqr.le)).trans hv
    linarith only [h₁,h₂,h₃,Real.rpow_nonneg hnr.le (4/5)]
  have hlY := Real.log_le_log hYr hYn'
  have hlog4 := pow_le_pow_left₀ (Real.log_natCast_nonneg Y) hlY 4
  have ham := mul_le_mul (mul_le_mul_of_nonneg_left hlog4 (by norm_num : (0:ℝ)≤16200))
    hen (OAI.Problem337.Vaughan.approximationEnvelope_nonneg _ _ hYr.le) (by positivity)
  have hlogpow : Real.log (n : ℝ) ≤ (Real.log n)^4 := by
    simpa using pow_le_pow_right₀ hL' (by decide : 1 ≤ 4)
  have hres := mul_le_mul (mul_le_mul_of_nonneg_left
    ((Real.sqrt_le_sqrt hYn').trans (hroot.trans hcut)) (by norm_num : (0:ℝ)≤2))
    (hlY.trans hlogpow) (Real.log_natCast_nonneg Y) (by positivity)
  apply (prime_approx Y q t hYp hval).trans
  nlinarith only [add_le_add ham hres, mul_nonneg (pow_nonneg (Real.log_natCast_nonneg n) 4) hscale]

private theorem tail_series (n Y : ℕ) (hYn : Y ≤ n) (t : ℝ) :
    series n (tailWeight Y) t = series n primeLog t-series Y primeLog t := by
  classical
  let f (k : ℕ) := (primeLog k : ℂ)*wave ((k : ℝ)*t)
  have hfilters : (range (n+1)).filter (fun k => ¬ Y < k) = range (Y+1) := by
    ext k
    simp only [mem_filter,mem_range,not_lt]
    omega
  have hs := sum_filter_add_sum_filter_not (range (n+1)) (fun k => Y < k) f
  rw [hfilters] at hs
  have ht : series n (tailWeight Y) t = ∑ k ∈ (range (n+1)).filter (fun k => Y < k), f k := by
    rw [sum_filter]
    unfold series
    apply sum_congr rfl
    intro k _
    by_cases h : Y < k <;> simp [f,tailWeight,h]
  exact (eq_sub_iff_add_eq).2 (by rw [ht]; exact hs)

private theorem tail_energy (n Y : ℕ) :
    (∑ k ∈ range (n+1), (tailWeight Y k)^2) ≤ Real.log 4*(n : ℝ)*Real.log n := by
  refine (sum_le_sum (g := fun k => (primeLog k)^2) (fun k _ => ?_)).trans (primeLog_energy n)
  by_cases h : Y < k <;> simp [tailWeight,h, sq_nonneg]

private theorem scale_sq_le {n P : ℕ} (hn : 0 < (n : ℝ)) (hP : 0 < (P : ℝ)) :
    (scale n P)^2 ≤ 2*((n : ℝ)*((n : ℝ)/P+(n : ℝ)^(3/5 : ℝ))) := by
  let u := (n : ℝ)/Real.sqrt P
  let v := (n : ℝ)^(4/5 : ℝ)
  have hu : u^2 = (n : ℝ)*((n : ℝ)/P) := by
    dsimp [u]; rw [div_pow,Real.sq_sqrt hP.le]; ring
  have hv : v^2 = (n : ℝ)*(n : ℝ)^(3/5 : ℝ) := by
    dsimp [v]; rw [← Real.rpow_mul_natCast hn.le, ← Real.rpow_one_add' hn.le (by norm_num)]
    norm_num
  change (u+v)^2 ≤ _
  calc (u+v)^2 ≤ 2*(u^2+v^2) := by nlinarith only [sq_nonneg (u-v)]
       _ = _ := by rw [hu,hv]; ring

noncomputable def largeMinor (n P Y M : ℕ) : Finset ℕ :=
  @Finset.filter ℕ (fun m => (n : ℝ)/Real.sqrt (Real.log n) ≤ ‖coeff n Y m (arcs n P)ᶜ‖)
    (Classical.decPred _) (range M)

/-- The exceptional frequencies are counted with the same cutoff for every
prime interval (Y,n]. The dyadic block may be replaced by any frequency prefix. -/
theorem count_bound : ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, ∀ P Y M : ℕ,
    1 ≤ P → P ≤ n → Y ≤ n → ((largeMinor n P Y M).card : ℝ) ≤
      C*((n : ℝ)/P+(n : ℝ)^(3/5 : ℝ))*(Real.log n)^10 := by
  classical
  let C : ℝ := 2*100000^2*Real.log 4
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  filter_upwards [prefix_bound,eventually_ge_atTop (2 : ℕ)] with n hsup hn
  intro P Y M hP hPn hYn
  let L := Real.log (n : ℝ)
  have hnr : 0 < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hpr : 0 < (P : ℝ) := Nat.cast_pos.mpr hP
  have hL : 0 < L := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hT : 0 ≤ scale n P := by dsimp [scale]; positivity
  let U := 100000*L^4*scale n P
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hts : ∀ t ∈ Set.Icc (0:ℝ) 1, t ∉ arcs n P → ‖series n (tailWeight Y) t‖ ≤ U := by
    intro t ht ha
    rw [tail_series n Y hYn t]
    have ha' := hsup P hP hPn t ht ha
    have h := (norm_sub_le _ _).trans (add_le_add (ha' n le_rfl) (ha' Y hYn))
    refine h.trans_eq ?_
    dsimp only [U,L]; ring
  have hmoment : (∑ m ∈ range M, ‖coeff n Y m (arcs n P)ᶜ‖^2) ≤ U^2*(Real.log 4*(n : ℝ)*L) :=
    (WindowBessel.minorFourthMoment n M (tailWeight Y) (arcs n P) U
      (GoldbachEstermann.measurable_block_arcs P n) hU hts).trans
      (mul_le_mul_of_nonneg_left (tail_energy n Y) (sq_nonneg U))
  let B := largeMinor n P Y M
  have hcount : (B.card : ℝ)*((n : ℝ)/Real.sqrt L)^2 ≤ U^2*(Real.log 4*(n : ℝ)*L) := calc
    _ = ∑ _m ∈ B, ((n : ℝ)/Real.sqrt L)^2 := by simp
    _ ≤ ∑ m ∈ B, ‖coeff n Y m (arcs n P)ᶜ‖^2 := by
      apply sum_le_sum
      intro m hm
      exact pow_le_pow_left₀ (by positivity) (mem_filter.mp hm).2 2
    _ ≤ ∑ m ∈ range M, ‖coeff n Y m (arcs n P)ᶜ‖^2 :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => sq_nonneg _)
    _ ≤ _ := hmoment
  rw [div_pow,Real.sq_sqrt hL.le,mul_div_assoc'] at hcount
  have hc := (div_le_iff₀ hL).1 hcount
  let A := (n : ℝ)/P+(n : ℝ)^(3/5 : ℝ)
  have hkey : U^2*(Real.log 4*(n : ℝ)*L)*L ≤ (C*A*L^10)*(n : ℝ)^2 := calc
    _ = (100000^2*L^10*Real.log 4*(n : ℝ))*(scale n P)^2 := by dsimp [U]; ring
    _ ≤ (100000^2*L^10*Real.log 4*(n : ℝ))*(2*((n : ℝ)*A)) :=
      mul_le_mul_of_nonneg_left (scale_sq_le hnr hpr) (by positivity)
    _ = _ := by dsimp [C]; ring
  exact le_of_mul_le_mul_right (hc.trans hkey) (sq_pos_of_pos hnr)

def exponents (X : ℕ) := Icc 1 (Nat.log 2 X/2)

noncomputable def shiftedMinor (X P Y : ℕ) : Finset ℕ := by
  classical
  exact (Ico X (2*X)).filter (fun n => Even n ∧ ∃ e ∈ exponents X,
    n-2^e ∈ largeMinor (2*X) P Y (2*X+1))

private theorem shifted_card (X P Y : ℕ) (hX : 1 ≤ X) :
    (shiftedMinor X P Y).card ≤ (Nat.log 2 X/2)*(largeMinor (2*X) P Y (2*X+1)).card := by
  classical
  let B := largeMinor (2*X) P Y (2*X+1)
  have hsub : shiftedMinor X P Y ⊆ (exponents X).biUnion (fun e => B.image (fun m => m+2^e)) := by
    intro n hn
    obtain ⟨hI,_,e,he,hm⟩ := mem_filter.mp hn
    have hlim : e ≤ Nat.log 2 X := (mem_Icc.mp he).2.trans (Nat.div_le_self _ _)
    have hpow := (Nat.pow_le_pow_right (by decide : 0 < 2) hlim).trans
      (Nat.pow_log_le_self 2 (by omega : X ≠ 0))
    exact mem_biUnion.mpr ⟨e,he,mem_image.mpr ⟨n-2^e,hm,Nat.sub_add_cancel
      (hpow.trans (mem_Ico.mp hI).1)⟩⟩
  calc
    _ ≤ _ := card_le_card hsub
    _ ≤ ∑ e ∈ exponents X, (B.image (fun m => m+2^e)).card := card_biUnion_le
    _ ≤ ∑ _e ∈ exponents X, B.card := sum_le_sum (fun _ _ => card_image_le)
    _ = _ := by simp [exponents,B]

/-- One polynomial bound simultaneously discards large minor coefficients
at *all* the binary shifts in the frozen research task. -/
theorem shifted_power : ∀ᶠ X : ℕ in atTop, ∀ P Y : ℕ, 1 ≤ P → P ≤ 2*X → Y ≤ 2*X →
    ((2*X : ℕ) : ℝ)^(1/4 : ℝ) ≤ 2*P →
    ((shiftedMinor X P Y).card : ℝ) ≤ (X : ℝ)^(31/40 : ℝ) := by
  obtain ⟨C,hC,hcnt⟩ := count_bound
  obtain ⟨N,hN⟩ := eventually_atTop.1 hcnt
  let K := 3*C*(2 : ℝ)^(3/4 : ℝ)*2^10/Real.log 2
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hK : 0 < K := by dsimp [K]; positivity
  have hsmall := ((isLittleO_log_rpow_rpow_atTop (11 : ℝ) (by norm_num : (0 : ℝ) < 1/40)).comp_tendsto
    (tendsto_natCast_atTop_atTop (R := ℝ))).bound (inv_pos.mpr hK)
  filter_upwards [eventually_ge_atTop (max N 2),hsmall] with X hX hs
  intro P Y hP hPn hYn hcut
  have hx : 1 < (X : ℝ) := by exact_mod_cast (show 1 < X by omega)
  have hx0 : 0 < (X : ℝ) := by linarith
  have hlog : 0 < Real.log X := Real.log_pos hx
  let Z : ℝ := (2*X : ℕ)
  have hZ : Z = 2*(X : ℝ) := by simp [Z]
  have hZ1 : 1 ≤ Z := by rw [hZ]; linarith
  have hZ0 : 0 < Z := zero_lt_one.trans_le hZ1
  have hp0 : (0 : ℝ) < P := Nat.cast_pos.mpr hP
  have hq : Z / P ≤ 2*Z^(3/4 : ℝ) := by
    apply (div_le_iff₀ hp0).2
    have h := mul_le_mul_of_nonneg_left hcut (Real.rpow_nonneg hZ0.le (3/4 : ℝ))
    change Z^(3/4 : ℝ)*Z^(1/4 : ℝ) ≤ _ at h
    rw [← Real.rpow_add hZ0] at h
    norm_num at h
    linarith only [h]
  have hterms : Z/P+Z^(3/5 : ℝ) ≤ 3*Z^(3/4 : ℝ) := by
    linarith only [hq,Real.rpow_le_rpow_of_exponent_le hZ1 (by norm_num : (3/5 : ℝ) ≤ 3/4)]
  have hlZ : Real.log Z ≤ 2 * Real.log X := by
    rw [hZ,Real.log_mul (by norm_num) hx0.ne']
    linarith only [Real.log_le_log (by norm_num : (0:ℝ)<2)
      (by exact_mod_cast (show 2 ≤ X by omega) : (2:ℝ)≤X)]
  have hL : ((Nat.log 2 X/2 : ℕ) : ℝ) ≤ Real.log X/Real.log 2 :=
    (Nat.cast_le.mpr (Nat.div_le_self _ _)).trans (Real.natLog_le_logb X 2)
  have hb := hN (2*X) (by omega) P Y (2*X+1) hP hPn hYn
  change _ ≤ C*(Z/P+Z^(3/5 : ℝ))*(Real.log Z)^10 at hb
  have hlogZ := Real.log_nonneg hZ1
  have hb' := hb.trans (mul_le_mul (mul_le_mul_of_nonneg_left hterms hC.le)
    (pow_le_pow_left₀ hlogZ hlZ 10) (pow_nonneg hlogZ _) (by positivity))
  have hc : ((shiftedMinor X P Y).card : ℝ) ≤
    ((Nat.log 2 X/2 : ℕ) : ℝ)*(largeMinor (2*X) P Y (2*X+1)).card := by
    exact_mod_cast shifted_card X P Y (by omega)
  have hr := hc.trans (mul_le_mul hL hb' (Nat.cast_nonneg _) (by positivity))
  have hid : Real.log X/Real.log 2*(C*(3*Z^(3/4 : ℝ))*(2*Real.log X)^10) =
      K*(Real.log X)^11*(X : ℝ)^(3/4 : ℝ) := by
    rw [hZ,Real.mul_rpow (by norm_num) hx0.le]
    dsimp [K]; ring
  rw [hid] at hr
  have hs' : (Real.log X)^11 ≤ K⁻¹*(X : ℝ)^(1/40 : ℝ) := by
    simpa only [Function.comp_apply,Real.rpow_natCast,Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hx0.le _),abs_of_nonneg (Real.rpow_nonneg hlog.le _),
      Real.rpow_ofNat,abs_of_nonneg (pow_nonneg hlog.le _)] using hs
  have hfinal : K*(Real.log X)^11 ≤ (X : ℝ)^(1/40 : ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hs' hK.le
    rwa [← mul_assoc,mul_inv_cancel₀ hK.ne',one_mul] at hh
  refine hr.trans ((mul_le_mul_of_nonneg_right hfinal (Real.rpow_nonneg hx0.le _)).trans_eq ?_)
  rw [← Real.rpow_add hx0]
  norm_num

def representations (m : ℕ) :=
  ((range (m+1)).filter (fun p => p.Prime ∧ (m-p).Prime)).card

def failedShifts (X : ℕ) :=
  (Ico X (2*X)).filter (fun n => Even n ∧
    0 < ((exponents X).filter (fun e => representations (n-2^e)=0)).card)

noncomputable def deficientMajor (X P Y : ℕ) : Finset ℕ :=
  @Finset.filter ℕ (fun n => Even n ∧ ∃ e ∈ exponents X,
    (coeff (2*X) Y (n-2^e) (arcs (2*X) P)).re <
      ((2*X : ℕ) : ℝ)/Real.sqrt (Real.log ((2*X : ℕ) : ℝ))) (Classical.decPred _) (Ico X (2*X))

private theorem coeffs_cancel (n P Y m : ℕ) (hrep : representations m = 0) :
    (coeff n Y m (arcs n P)).re+(coeff n Y m (arcs n P)ᶜ).re=0 := by
  have hpairs (i j : ℕ) (he : i+j=m) : tailWeight Y i*tailWeight Y j=0 := by
    have hn : ¬ (i.Prime ∧ j.Prime) := by
      intro h
      have hf : i ∈ (range (m+1)).filter (fun p => p.Prime ∧ (m-p).Prime) := by
        refine mem_filter.mpr ⟨mem_range.mpr (by omega),h.1,?_⟩
        rw [show m-i=j by omega]
        exact h.2
      exact (Nat.ne_of_gt (card_pos.mpr ⟨i,hf⟩)) hrep
    by_cases hi : i.Prime
    · have hj : ¬ j.Prime := fun h => hn ⟨hi,h⟩
      simp [tailWeight,GoldbachMovingWindows.primeLog,hj]
    · simp [tailWeight,GoldbachMovingWindows.primeLog,hi]
  let f := fun t => (series n (tailWeight Y) t)^2*wave (-(m : ℝ)*t)
  have hz : (∫ t in (0 : ℝ)..1,f t)=0 := WindowBessel.ExceptionalCoefficients.zero_from_pairs
    (tailWeight Y) m n hpairs
  have hc : Continuous f := by dsimp [f,series,wave]; fun_prop
  have h := (WindowBessel.ExceptionalCoefficients.indicator_integral_split
    (GoldbachEstermann.measurable_block_arcs P n) (hc.intervalIntegrable 0 1)).trans hz
  exact congrArg Complex.re h

/-- Remove the targets with a genuinely small major-arc coefficient. All
remaining failures of the published simultaneous-shift test fit a strict
sub-4/5 power budget, uniformly for polynomial denominator cutoffs. -/
theorem residual_bound : ∀ᶠ X : ℕ in atTop, ∀ P Y : ℕ, 1 ≤ P → P ≤ 2*X → Y ≤ 2*X →
    ((2*X : ℕ) : ℝ)^(1/4 : ℝ) ≤ 2*P →
    (((failedShifts X \ deficientMajor X P Y).card : ℕ) : ℝ) ≤ (X : ℝ)^(31/40 : ℝ) := by
  classical
  filter_upwards [shifted_power] with X hpower
  intro P Y hP hPn hYn hcut
  apply (Nat.cast_le.mpr (card_le_card (show failedShifts X \ deficientMajor X P Y ⊆
    shiftedMinor X P Y from ?_))).trans (hpower P Y hP hPn hYn hcut)
  intro n hn
  obtain ⟨hbad,hnot⟩ := mem_sdiff.mp hn
  obtain ⟨hI,heven,hcount⟩ := mem_filter.mp hbad
  obtain ⟨e,he⟩ := card_pos.mp hcount
  obtain ⟨heb,hrep⟩ := mem_filter.mp he
  simp only [deficientMajor,mem_filter] at hnot
  have hmaj : ((2*X : ℕ) : ℝ)/Real.sqrt (Real.log ((2*X : ℕ) : ℝ)) ≤
      (coeff (2*X) Y (n-2^e) (arcs (2*X) P)).re := le_of_not_gt (fun h =>
    hnot ⟨hI,heven,e,heb,h⟩)
  refine mem_filter.mpr ⟨hI,heven,e,heb,mem_filter.mpr ⟨mem_range.mpr ?_,?_⟩⟩
  · exact lt_of_le_of_lt (Nat.sub_le n _) (lt_trans
      (show n < 2*X from (mem_Ico.mp hI).2) (Nat.lt_succ_self _))
  · have h := coeffs_cancel (2*X) P Y (n-2^e) hrep
    have hnorm := (abs_le.mp (Complex.abs_re_le_norm (coeff (2*X) Y (n-2^e)
      (arcs (2*X) P)ᶜ))).1
    linarith only [h,hnorm,hmaj]

noncomputable def bulkMajor (X P Y : ℕ) : Finset ℕ :=
  @Finset.filter ℕ (fun m => Even m ∧ (coeff (2*X) Y m (arcs (2*X) P)).re <
    ((2*X : ℕ) : ℝ)/Real.sqrt (Real.log ((2*X : ℕ) : ℝ))) (Classical.decPred _) (Ico X (2*X))

private theorem major_card {X P Y : ℕ} (hX : 8 ≤ X) :
    (deficientMajor X P Y).card ≤ Nat.sqrt X+(Nat.log 2 X/2)*(bulkMajor X P Y).card := by
  classical
  let I := exponents X
  let B := bulkMajor X P Y
  let E := Ico X (X+Nat.sqrt X)
  have hsub : deficientMajor X P Y ⊆ E ∪ I.biUnion (fun e => B.image (fun m => m+2^e)) := by
    intro n hn
    simp only [deficientMajor,mem_filter] at hn
    obtain ⟨hI,hEven,e,he,hlow⟩ := hn
    by_cases hedge : n < X+Nat.sqrt X
    · exact mem_union_left _ (mem_Ico.mpr ⟨(mem_Ico.mp hI).1,hedge⟩)
    have hband : 1 ≤ e ∧ e ≤ Nat.log 2 X/2 := mem_Icc.mp he
    have hpow := (Nat.pow_le_pow_right (by decide : 0 < 2)
      (show e*2 ≤ Nat.log 2 X by omega)).trans (Nat.pow_log_le_self 2 (by omega : X ≠ 0))
    rw [pow_mul] at hpow
    have hsh : 2^e ≤ Nat.sqrt X := Nat.le_sqrt.mpr (by simpa only [sq] using hpow)
    have hev : Even (2^e) := Even.pow_of_ne_zero (by decide : Even (2 : ℕ)) (by omega)
    have hle : 2^e ≤ n := by omega
    apply mem_union_right
    refine mem_biUnion.mpr ⟨e,he,mem_image.mpr ⟨n-2^e,?_,Nat.sub_add_cancel hle⟩⟩
    change n-2^e ∈ bulkMajor X P Y
    simp only [bulkMajor,mem_filter]
    have hni : X ≤ n ∧ n < 2*X := mem_Ico.mp hI
    exact ⟨mem_Ico.mpr ⟨by omega,lt_of_le_of_lt (Nat.sub_le n _) hni.2⟩,
      (Nat.even_sub hle).2 (iff_of_true hEven hev),hlow⟩
  have hu : (I.biUnion (fun e => B.image (fun m => m+2^e))).card ≤ I.card*B.card := calc
    _ ≤ ∑ e ∈ I, (B.image (fun m => m+2^e)).card := card_biUnion_le
    _ ≤ ∑ _e ∈ I, B.card := sum_le_sum (fun _ _ => card_image_le)
    _ = _ := by simp
  have h := (card_le_card hsub).trans (card_union_le _ _)
  apply h.trans
  simpa [E,I,exponents,B] using Nat.add_le_add_left hu E.card

/-- The analytic premise now only inspects *ordinary* even frequencies
in a single dyadic block. It needs one common cutoff and one common
interval of primes for the block. -/
theorem of_bulk_major (H : ∀ᶠ X : ℕ in atTop, ∃ P Y : ℕ, 1 ≤ P ∧ P^5 ≤ (2*X)^2 ∧ Y ≤ 2*X ∧
    ((2*X : ℕ) : ℝ)^(1/4 : ℝ) ≤ 2*P ∧ ((bulkMajor X P Y).card : ℝ) ≤ (X : ℝ)^(3/4 : ℝ)) :
    ∃ N : ℕ, ∀ X ≥ N, (failedShifts X).card^5 ≤ X^4 := by
  classical
  have ht := tendsto_natCast_atTop_atTop (R := ℝ)
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hs := ((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1/40)).comp_tendsto ht).bound h2
  have hp := ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/40)).comp ht).eventually_ge_atTop 3
  apply eventually_atTop.1
  filter_upwards [H,residual_bound,hs,hp,eventually_ge_atTop (8:ℕ)] with X h hx hlog hgap hX
  obtain ⟨P,Y,hP,hpow,hYn,hcut,hbulk⟩ := h
  have hPn : P ≤ 2*X := by
    by_contra! hgt
    exact (not_lt_of_ge (hpow.trans' (Nat.pow_le_pow_right hP (by decide : 2 ≤ 5))))
      (Nat.pow_lt_pow_left hgt (by decide : 2 ≠ 0))
  have hr := hx P Y hP hPn hYn hcut
  have h1 : 1 ≤ (X : ℝ) := by exact_mod_cast (show 1 ≤ X by omega)
  have hx0 : 0 < (X : ℝ) := zero_lt_one.trans_le h1
  have hlog' : Real.log X ≤ Real.log 2*(X : ℝ)^(1/40 : ℝ) := by
    simpa only [Function.comp_apply,Real.norm_eq_abs,abs_of_nonneg (Real.log_natCast_nonneg X),
      abs_of_nonneg (Real.rpow_nonneg hx0.le _)] using hlog
  have hL : ((Nat.log 2 X/2 : ℕ) : ℝ) ≤ (X : ℝ)^(1/40 : ℝ) := calc
    _ ≤ Real.log X / Real.log 2 :=
      (Nat.cast_le.mpr (Nat.div_le_self _ _)).trans (Real.natLog_le_logb X 2)
    _ ≤ _ := (div_le_iff₀ h2).2 (by simpa only [mul_comm] using hlog')
  have hed : ((Nat.sqrt X : ℕ) : ℝ) ≤ (X : ℝ)^(31/40 : ℝ) := calc
    _ ≤ Real.sqrt (X : ℝ) := (Real.le_sqrt (Nat.cast_nonneg _) hx0.le).2
      (by exact_mod_cast Nat.sqrt_le' X)
    _ ≤ _ := by rw [Real.sqrt_eq_rpow]; exact Real.rpow_le_rpow_of_exponent_le h1 (by norm_num)
  have hpair := mul_le_mul hL hbulk (Nat.cast_nonneg _) (Real.rpow_nonneg hx0.le _)
  rw [← Real.rpow_add hx0,show (1/40 : ℝ)+3/4=31/40 by norm_num] at hpair
  have hm : ((deficientMajor X P Y).card : ℝ) ≤ (Nat.sqrt X:ℕ)+
      ((Nat.log 2 X/2 : ℕ) : ℝ)*(bulkMajor X P Y).card := by exact_mod_cast major_card hX
  have hsub : failedShifts X ⊆ (failedShifts X \ deficientMajor X P Y) ∪ deficientMajor X P Y := by
    intro n hn
    by_cases h : n ∈ deficientMajor X P Y <;> simp [h,hn]
  have hnat := (card_le_card hsub).trans (card_union_le _ _)
  have hreal : ((failedShifts X).card : ℝ) ≤ ((failedShifts X \ deficientMajor X P Y).card : ℝ)
      +(deficientMajor X P Y).card := by exact_mod_cast hnat
  have hval : ((failedShifts X).card : ℝ) ≤ (X : ℝ)^(4/5 : ℝ) := calc
    _ ≤ 3*(X : ℝ)^(31/40 : ℝ) := by linarith only [hreal,hr,hm,hed,hpair]
    _ ≤ (X : ℝ)^(1/40 : ℝ)*(X : ℝ)^(31/40 : ℝ) :=
      mul_le_mul_of_nonneg_right hgap (Real.rpow_nonneg hx0.le _)
    _ = _ := by rw [← Real.rpow_add hx0]; norm_num
  have h5 := pow_le_pow_left₀ (Nat.cast_nonneg _) hval 5
  rw [← Real.rpow_mul_natCast hx0.le] at h5
  norm_num at h5
  exact_mod_cast h5

end
end Conjectures.Goldbach.PolynomialArcExceptionalCount

open Conjectures.Goldbach.PolynomialArcExceptionalCount in
/-- Polynomial estimate for the common minor arcs and the residual set in
the binary-shift problem, after excluding its explicitly defined major holes. -/
theorem Conjectures.Goldbach.PolynomialArcExceptionalCount :
    (∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in Filter.atTop, ∀ P Y M : ℕ,
      1 ≤ P → P ≤ n → Y ≤ n → ((largeMinor n P Y M).card : ℝ) ≤
        C*((n : ℝ)/P+(n : ℝ)^(3/5 : ℝ))*(Real.log n)^10) ∧
    (∀ᶠ X : ℕ in Filter.atTop, ∀ P Y : ℕ, 1 ≤ P → P ≤ 2*X → Y ≤ 2*X →
      ((2*X : ℕ) : ℝ)^(1/4 : ℝ) ≤ 2*P →
      (((failedShifts X \ deficientMajor X P Y).card : ℕ) : ℝ) ≤ (X : ℝ)^(31/40 : ℝ)) ∧
    ((∀ᶠ X : ℕ in Filter.atTop, ∃ P Y : ℕ, 1 ≤ P ∧ P^5 ≤ (2*X)^2 ∧ Y ≤ 2*X ∧
      ((2*X : ℕ) : ℝ)^(1/4 : ℝ) ≤ 2*P ∧ ((bulkMajor X P Y).card : ℝ) ≤ (X : ℝ)^(3/4 : ℝ)) →
      ∃ N : ℕ, ∀ X ≥ N, (failedShifts X).card^5 ≤ X^4) :=
  ⟨count_bound,residual_bound,of_bulk_major⟩

