import Mathlib
import Conjectures.Goldbach.FareyLateFirstHitFactorSwitch
import Conjectures.Goldbach.FareyLatePrimeSquareLoss
import Conjectures.Goldbach.FareyCubeSqrtDensityRatio
open Finset

private theorem least_of_pair {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hle : p ≤ q) :
    (p*q).minFac = p := by
  have hn : p*q ≠ 1 := by have := hp.two_le; have := hq.two_le; nlinarith
  have h := Nat.minFac_prime hn
  have d := Nat.minFac_dvd (p*q)
  have u := Nat.minFac_le_of_dvd hp.two_le (dvd_mul_right p q)
  rcases h.dvd_mul.mp d with d | d
  · exact (Nat.prime_dvd_prime_iff_eq h hp).mp d
  · have e := (Nat.prime_dvd_prime_iff_eq h hq).mp d
    omega

private theorem single_side_pairs (z : ℕ) (I : Finset ℕ) (P : Finset (ℕ × ℕ))
    (good : ∀ x ∈ P, x.1.Prime ∧ x.2.Prime ∧ z < x.1 ∧ x.1 ≤ x.2 ∧ x.1*x.2 ∈ I) :
    P.card ≤ (I.filter (fun u => z < u.minFac ∧ u.minFac.Prime ∧ (u/u.minFac).Prime)).card := by
  apply Finset.card_le_card_of_injOn (fun x => x.1*x.2)
  · intro x hx
    obtain ⟨hp,hq,hz,hle,hi⟩ := good x hx
    apply Finset.mem_filter.mpr
    rw [least_of_pair hp hq hle, Nat.mul_div_cancel_left _ hp.pos]
    exact ⟨hi,hz,hp,hq⟩
  · intro x hx y hy e
    obtain ⟨hp,hq,_,hle,_⟩ := good x hx
    obtain ⟨hp',hq',_,hle',_⟩ := good y hy
    change x.1*x.2 = y.1*y.2 at e
    have h := congrArg Nat.minFac e
    rw [least_of_pair hp hq hle,least_of_pair hp' hq' hle'] at h
    apply Prod.ext h
    rw [←h] at e
    exact Nat.eq_of_mul_eq_mul_left hp.pos e


private theorem sieve_product_exp (P : Finset ℕ) (hp : ∀ p ∈ P, 2 ≤ p) :
    (∏ p ∈ P, (1-2/(p:ℝ))) ≤ Real.exp (-2 * ∑ p ∈ P, (p:ℝ)⁻¹) := by
  rw [Finset.mul_sum,Real.exp_sum]
  apply Finset.prod_le_prod₀
  · intro p h
    have hh : (2:ℝ) ≤ p := by exact_mod_cast hp p h
    exact sub_nonneg.mpr ((div_le_one (by linarith)).mpr hh)
  · intro p _
    have h := Real.add_one_le_exp (-2*(p:ℝ)⁻¹)
    simpa only [div_eq_mul_inv, sub_eq_add_neg, neg_mul, add_comm] using h

private theorem sieve_product_log_bound (P : Finset ℕ) (hp : ∀ p ∈ P, 2 ≤ p)
    (x C : ℝ) (hx : 1 < x) (h : Real.log (Real.log x) - C ≤ ∑ p ∈ P, (p:ℝ)⁻¹) :
    (∏ p ∈ P, (1-2/(p:ℝ))) ≤ Real.exp (2*C)/(Real.log x)^2 := by
  apply (sieve_product_exp P hp).trans
  calc
    _ ≤ Real.exp (2*C - 2*Real.log (Real.log x)) := Real.exp_le_exp.mpr (by linarith)
    _ = _ := by
      rw [Real.exp_sub,show 2*Real.log (Real.log x) = Real.log (Real.log x)+Real.log (Real.log x) by ring,
        Real.exp_add,Real.exp_log (Real.log_pos hx),sq]


open ErdosStraus.PrimeEstimates.Mertens in
private theorem odd_prime_product_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ z : ℕ, 3 ≤ z →
      (∏ p ∈ (primesUpTo z).erase 2, (1-2/(p:ℝ))) ≤ K/(Real.log z)^2 := by
  obtain ⟨C,hC,h⟩ := mertensSecond
  let B := C / Real.log 2 + 1/2 - mertensSecondConstant
  refine ⟨Real.exp (2*B),Real.exp_pos _,?_⟩
  intro z hz
  have hz' : (2:ℝ) ≤ z := by exact_mod_cast (by omega : 2 ≤ z)
  have hlog := Real.log_le_log (by norm_num : (0:ℝ)<2) hz'
  have hc := div_le_div_of_nonneg_left hC.le (Real.log_pos (by norm_num : (1:ℝ)<2)) hlog
  have he := (abs_le.mp (h z hz')).1
  rw [Nat.floor_natCast] at he
  have h2 : 2 ∈ primesUpTo z := mem_primesUpTo.mpr ⟨Nat.prime_two,by omega⟩
  have hsum := Finset.sum_erase_add (primesUpTo z) (fun p : ℕ => (p:ℝ)⁻¹) h2
  simp only [primeReciprocalSum,one_div] at he
  apply sieve_product_log_bound _ (fun p hp => (mem_primesUpTo.mp (Finset.mem_of_mem_erase hp)).1.two_le)
    z B (by linarith)
  dsimp [B]
  norm_num at hsum
  linarith


open Filter Topology in
private theorem dyadic_prime_card_lower :
    ∀ᶠ x : ℝ in atTop, x/2 ≤
      (((⌊2*x⌋₊).primesLE \ (⌊x⌋₊).primesLE).card:ℝ) * Real.log (2*x) := by
  have h₂ : Tendsto (fun x : ℝ => Chebyshev.theta (2*x)/(2*x)) atTop (𝓝 1) :=
    Chebyshev.tendsto_theta_div_atTop.comp (tendsto_id.const_mul_atTop (by norm_num : (0:ℝ)<2))
  have ha := h₂.eventually (lt_mem_nhds (by norm_num : (7/8:ℝ) < 1))
  have hb := Chebyshev.tendsto_theta_div_atTop.eventually (gt_mem_nhds (by norm_num : (1:ℝ)<5/4))
  filter_upwards [ha,hb,eventually_gt_atTop (1:ℝ)] with x hx₂ hx₁ hx
  have h0 : 0<x := by linarith
  have hdiff : x/2 ≤ Chebyshev.theta (2*x) - Chebyshev.theta x := by
    have a := (lt_div_iff₀ (show 0<2*x by positivity)).mp hx₂
    have b := (div_lt_iff₀ h0).mp hx₁
    linarith
  refine hdiff.trans ?_
  have hsub := Nat.primesLE_mono (Nat.floor_mono (show x ≤ 2*x by linarith))
  rw [Chebyshev.theta_eq_sum_primesLE,Chebyshev.theta_eq_sum_primesLE,←Finset.sum_sdiff_eq_sub hsub]
  calc
    _ ≤ ∑ _p ∈ (⌊2*x⌋₊).primesLE \ (⌊x⌋₊).primesLE, Real.log (2*x) := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨hpx,hpr⟩ := Nat.mem_primesLE.mp (Finset.mem_sdiff.mp hp).1
      exact Real.log_le_log (by exact_mod_cast hpr.pos)
        ((by exact_mod_cast hpx : (p:ℝ) ≤ (⌊2*x⌋₊:ℕ)).trans (Nat.floor_le (by positivity)))
    _ = _ := by simp


private theorem sum_partner_counts (z : ℕ) (I P : Finset ℕ) (Q : ℕ → Finset ℕ)
    (small : ∀ p ∈ P, p.Prime ∧ z < p)
    (large : ∀ p ∈ P, ∀ q ∈ Q p, q.Prime ∧ p ≤ q ∧ p*q ∈ I) :
    (∑ p ∈ P, (Q p).card) ≤
      (I.filter (fun u => z < u.minFac ∧ u.minFac.Prime ∧ (u/u.minFac).Prime)).card := by
  rw [← Finset.card_sigma]
  apply Finset.card_le_card_of_injOn (fun x : Σ _ : ℕ, ℕ => x.1*x.2)
  · rintro ⟨p,q⟩ hx
    obtain ⟨hp,hq⟩ := Finset.mem_sigma.mp hx
    obtain ⟨pp,hz⟩ := small p hp
    obtain ⟨qp,hle,hi⟩ := large p hp q hq
    apply Finset.mem_filter.mpr
    simpa [least_of_pair pp qp hle, Nat.mul_div_cancel_left _ pp.pos] using
      (show p*q ∈ I ∧ z < p ∧ p.Prime ∧ q.Prime from ⟨hi,hz,pp,qp⟩)
  · rintro ⟨p,q⟩ hx ⟨r,s⟩ hy he
    obtain ⟨hp,hq⟩ := Finset.mem_sigma.mp hx
    obtain ⟨hr,hs⟩ := Finset.mem_sigma.mp hy
    obtain ⟨pp,_⟩ := small p hp
    obtain ⟨rp,_⟩ := small r hr
    obtain ⟨qp,hpq,_⟩ := large p hp q hq
    obtain ⟨sp,hrs,_⟩ := large r hr s hs
    change p*q = r*s at he
    have eq := congrArg Nat.minFac he
    rw [least_of_pair pp qp hpq,least_of_pair rp sp hrs] at eq
    subst r
    exact congrArg (Sigma.mk p) (Nat.eq_of_mul_eq_mul_left pp.pos he)

private theorem sum_partner_lower (z : ℕ) (I P : Finset ℕ) (Q : ℕ → Finset ℕ)
    (small : ∀ p ∈ P, p.Prime ∧ z < p)
    (large : ∀ p ∈ P, ∀ q ∈ Q p, q.Prime ∧ p ≤ q ∧ p*q ∈ I)
    (K : ℝ) (hk : ∀ p ∈ P, K*(p:ℝ)⁻¹ ≤ ((Q p).card:ℝ)) :
    K * (∑ p ∈ P, (p:ℝ)⁻¹) ≤
      ((I.filter (fun u => z < u.minFac ∧ u.minFac.Prime ∧ (u/u.minFac).Prime)).card:ℝ) := by
  rw [Finset.mul_sum]
  refine (Finset.sum_le_sum hk).trans ?_
  exact_mod_cast sum_partner_counts z I P Q small large


open ErdosStraus.PrimeEstimates.Mertens Filter Topology in
private theorem smaller_prime_mass :
    ∀ᶠ t : ℕ in atTop, Real.log (5/4:ℝ)/2 ≤
      ∑ p ∈ primesUpTo (t^5) \ primesUpTo (t^4), (p:ℝ)⁻¹ := by
  obtain ⟨C,hC,h⟩ := mertensSecond
  have hpos : 0 < Real.log (5/4:ℝ) := Real.log_pos (by norm_num)
  obtain ⟨T,hT⟩ := exists_nat_ge (Real.exp (4*C / Real.log (5/4:ℝ)))
  filter_upwards [eventually_ge_atTop (max 2 T)] with t ht
  have ht2 : 2 ≤ t := (le_max_left ..).trans ht
  have htr : (2:ℝ) ≤ t := by exact_mod_cast ht2
  have hlt : 0 < Real.log (t:ℝ) := Real.log_pos (by linarith)
  have hle := Real.log_le_log (Real.exp_pos _) (hT.trans
    (show (T:ℝ) ≤ (t:ℝ) by exact_mod_cast (show T ≤ t from (le_max_right ..).trans ht)))
  rw [Real.log_exp] at hle
  have hh := (div_le_iff₀ hpos).mp hle
  have est (k : ℕ) (hk : k = 4 ∨ k = 5) :
      |primeReciprocalSum (t^k) - (Real.log (k:ℝ) + Real.log (Real.log t) + mertensSecondConstant)| ≤
      C / ((k:ℝ)*Real.log t) := by
    have kn : 1 ≤ k := by omega
    have hu : 2 ≤ t^k := ht2.trans (by simpa using Nat.pow_le_pow_right (by omega : 0<t) kn)
    have he := h ((t^k:ℕ):ℝ) (by exact_mod_cast hu)
    rw [Nat.floor_natCast,Nat.cast_pow,Real.log_pow,Real.log_mul (by exact_mod_cast (by omega : k ≠ 0)) hlt.ne'] at he
    exact he
  have e4 := (abs_le.mp (est 4 (Or.inl rfl))).2
  have e5 := (abs_le.mp (est 5 (Or.inr rfl))).1
  norm_num only [Nat.cast_ofNat] at e4 e5
  have sub : primesUpTo (t^4) ⊆ primesUpTo (t^5) := by
    intro p hp
    obtain ⟨hpp,hle⟩ := mem_primesUpTo.mp hp
    exact mem_primesUpTo.mpr ⟨hpp,hle.trans (Nat.pow_le_pow_right (by omega) (by decide))⟩
  rw [Finset.sum_sdiff_eq_sub sub]
  simp only [← one_div]
  change _ ≤ primeReciprocalSum (t^5) - primeReciprocalSum (t^4)
  have small (k : ℝ) (hk : 1 ≤ k) : C/(k*Real.log t) ≤ Real.log (5/4:ℝ)/4 := by
    apply (div_le_div_of_nonneg_left hC.le hlt (by nlinarith)).trans
    apply (div_le_iff₀ hlt).mpr
    linarith only [hh]
  have diff := Real.log_div (by norm_num : (5:ℝ) ≠ 0) (by norm_num : (4:ℝ) ≠ 0)
  linarith only [e4,e5,small 4 (by norm_num),small 5 (by norm_num),diff]


private noncomputable def partnerSet (n p : ℕ) :=
  let x := (n:ℝ)/(3*p)
  (⌊2*x⌋₊).primesLE \ (⌊x⌋₊).primesLE

private theorem partnerSet_mem {n p q : ℕ} (hp : 0<p) (hsize : 3*p*p ≤ n)
    (hq : q ∈ partnerSet n p) :
    q.Prime ∧ p ≤ q ∧ p*q ∈ Finset.Icc ((n+2)/3) (2*n/3) := by
  obtain ⟨hi,lo⟩ := Finset.mem_sdiff.mp hq
  obtain ⟨high,hprime⟩ := Nat.mem_primesLE.mp hi
  have low : ⌊(n:ℝ)/(3*p)⌋₊ < q := by
    by_contra! h
    exact lo (Nat.mem_primesLE.mpr ⟨h,hprime⟩)
  have hpos : 0 < (3:ℝ)*p := by positivity
  have lower := (div_lt_iff₀ hpos).mp ((Nat.floor_lt (by positivity)).mp low)
  have upper := (Nat.le_floor_iff (by positivity)).mp high
  have rearr : 2*((n:ℝ)/(3*p)) = (2*n)/(3*p) := by ring
  rw [rearr] at upper
  have upper' := (le_div_iff₀ hpos).mp upper
  have h₁ : n < 3*(p*q) := by exact_mod_cast (by linarith only [lower] : (n:ℝ)<3*(p*q))
  have h₂ : 3*(p*q) ≤ 2*n := by exact_mod_cast (by linarith only [upper'] : (3:ℝ)*(p*q)≤2*n)
  refine ⟨hprime,?_,Finset.mem_Icc.mpr ⟨by omega,by omega⟩⟩
  by_contra! h
  have hlt := Nat.mul_lt_mul_of_pos_left h hp
  nlinarith


private theorem partner_count_from_dyadic (n p : ℕ) (hn : 2 ≤ n) (hp : 0 < p)
    (h : ((n:ℝ)/(3*p))/2 ≤ ((partnerSet n p).card:ℝ)*Real.log (2*((n:ℝ)/(3*p)))) :
    ((n:ℝ)/(6*Real.log n))*(p:ℝ)⁻¹ ≤ ((partnerSet n p).card:ℝ) := by
  have hpr : (1:ℝ) ≤ p := by exact_mod_cast hp
  have hnr : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hl := Real.log_pos (by linarith : 1 < (n:ℝ))
  have hpos : 0 < (3:ℝ)*p := by positivity
  have hsize : 2*((n:ℝ)/(3*p)) ≤ n := by
    rw [mul_div_assoc',div_le_iff₀ hpos]
    nlinarith only [mul_le_mul_of_nonneg_left hpr (by positivity : 0 ≤ (3:ℝ)*n),hnr]
  have hlog := Real.log_le_log (by positivity) hsize
  have est := h.trans (mul_le_mul_of_nonneg_left hlog (by positivity))
  field_simp at est ⊢
  nlinarith only [est]


open ErdosStraus.PrimeEstimates.Mertens Filter Topology in
private theorem eventual_one_side_lower :
    ∀ᶠ t : ℕ in atTop, let n := t^12
      (n:ℝ)/(6*Real.log n) * (Real.log (5/4:ℝ)/2) ≤
      (((Finset.Icc ((n+2)/3) (2*n/3)).filter (fun u => t^4 < u.minFac ∧
          u.minFac.Prime ∧ (u/u.minFac).Prime)).card:ℝ) := by
  obtain ⟨X,hX⟩ := eventually_atTop.mp dyadic_prime_card_lower
  obtain ⟨T,hT⟩ := exists_nat_ge X
  filter_upwards [smaller_prime_mass,eventually_ge_atTop (max 3 T)] with t hmass ht
  dsimp only
  let P := primesUpTo (t^5) \ primesUpTo (t^4)
  have ht3 : 3 ≤ t := (le_max_left ..).trans ht
  have ht0 : 0 < t := by omega
  have prop (p : ℕ) (h : p ∈ P) : p.Prime ∧ t^4 < p ∧ p ≤ t^5 := by
    obtain ⟨hu,hl⟩ := Finset.mem_sdiff.mp h
    obtain ⟨hp,hi⟩ := mem_primesUpTo.mp hu
    exact ⟨hp,lt_of_not_ge (fun hh => hl (mem_primesUpTo.mpr ⟨hp,hh⟩)),hi⟩
  have sq (p : ℕ) (h : p ∈ P) : 3*p*p ≤ t^12 := by
    have h1 := (prop p h).2.2
    calc
      _ ≤ t*(t^5)*(t^5) := by gcongr
      _ = t^11 := by ring
      _ ≤ _ := Nat.pow_le_pow_right ht0 (by decide)
  have hn : 2 ≤ t^12 := by
    exact (by omega : 2 ≤ t).trans (by simpa using Nat.pow_le_pow_right ht0 (by decide : 1 ≤ 12))
  have small (p : ℕ) (h : p ∈ P) := (prop p h).1.pos
  refine (mul_le_mul_of_nonneg_left hmass (by positivity)).trans
    (sum_partner_lower (t^4) _ P (partnerSet (t^12)) (fun p h => ⟨(prop p h).1,(prop p h).2.1⟩)
      (fun p h q hq => partnerSet_mem (small p h) (sq p h) hq) _ ?_)
  intro p h
  apply partner_count_from_dyadic _ _ hn (small p h)
  apply hX
  have hp := (prop p h).2.2
  have hn' : t*(3*p) ≤ t^12 := calc
    _ ≤ t*(t*t^5) := by gcongr
    _ = t^7 := by ring
    _ ≤ _ := Nat.pow_le_pow_right ht0 (by decide)
  have hreal : (t:ℝ) ≤ ((t^12:ℕ):ℝ)/(3*p) := by
    apply (le_div_iff₀ (by have := small p h; positivity)).mpr
    exact_mod_cast hn'
  exact hT.trans ((show (T:ℝ) ≤ (t:ℝ) by exact_mod_cast (show T ≤ t from (le_max_right ..).trans ht)).trans hreal)


private theorem exact_root_cutoffs (t : ℕ) :
    ⌊((t^12 : ℕ):ℝ)^(1/3:ℝ)⌋₊ = t^4 ∧ (t^12).sqrt = t^6 := by
  constructor
  · rw [Nat.cast_pow,←Real.rpow_natCast_mul (Nat.cast_nonneg _)]
    norm_num
    exact_mod_cast Nat.floor_natCast (R := ℝ) (t^4)
  · rw [show t^12 = (t^6)^2 by ring, Nat.sqrt_eq']

open ErdosStraus.PrimeEstimates.Mertens in
private theorem dyadic_sieve_factors (z k : ℕ) (hk : 0 < k) :
    (((Finset.Icc 2 z).filter Nat.Prime).filter (fun p => ¬p ∣ (2^k:ℕ)^12)) =
      (primesUpTo z).erase 2 := by
  ext p
  simp only [Finset.mem_filter,Finset.mem_Icc,Finset.mem_erase,mem_primesUpTo]
  constructor
  · rintro ⟨⟨⟨_,hz⟩,hp⟩,h⟩
    refine ⟨?_,hp,hz⟩
    rintro rfl
    exact h ((dvd_pow_self 2 hk.ne').trans (dvd_pow_self _ (by decide : 12 ≠ 0)))
  · rintro ⟨hne,hp,hz⟩
    refine ⟨⟨⟨hp.two_le,hz⟩,hp⟩,fun hd => ?_⟩
    exact hne ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow (hp.dvd_of_dvd_pow hd)))

theorem Conjectures.Cuts.Refute25dd470ddb6f861c24eaee19 : ¬ (have x1 : ℕ → Finset ℕ := fun (x1 : ℕ) => Finset.Icc ((x1 + (2 : ℕ)) / (3 : ℕ)) ((2 : ℕ) * x1 / (3 : ℕ)); have x2 : ℕ → ℕ := fun (x2 : ℕ) => ⌊(↑x2 : ℝ) ^ (1 / 3 : ℝ)⌋₊; have x3 : ℕ → Finset ℕ := fun (x3 : ℕ) => {x4 ∈ x1 x3 | x2 x3 < x4.minFac ∧ Nat.Prime x4.minFac ∧ Nat.Prime (x4 / x4.minFac)}; have x4 : ℕ → ℝ := fun (x4 : ℕ) => (↑(x1 x4).card : ℝ) * (↑x4.totient : ℝ) / (↑x4 : ℝ) * ∏ x5 ∈ Finset.filter Nat.Prime (Finset.Icc (2 : ℕ) x4.sqrt) with ¬x5 ∣ x4, ((1 : ℝ) - (2 : ℝ) / (↑x5 : ℝ)); ∃ (x5 : ℕ), ∀ (x6 : ℕ), x5 ≤ x6 → Even x6 → (↑(x3 x6).card : ℝ) ≤ (23 / 50 : ℝ) * x4 x6) := by
  classical
  dsimp only
  rintro ⟨N,hN⟩
  obtain ⟨K,hK,hprod⟩ := odd_prime_product_bound
  obtain ⟨T,hT⟩ := Filter.eventually_atTop.mp eventual_one_side_lower
  let c := Real.log (5/4:ℝ)/2
  have hc : 0<c := by dsimp [c]; positivity
  obtain ⟨A,hA⟩ := exists_nat_ge (Real.exp (24*K/c+1))
  let k := max (max N T) (max A 3) + 1
  let t := 2^k
  have hkt : k ≤ t := (Nat.lt_two_pow_self).le
  have htN : N ≤ t := by dsimp [k] at hkt; omega
  have htT : T ≤ t := by dsimp [k] at hkt; omega
  have htA : A ≤ t := by dsimp [k] at hkt; omega
  have ht3 : 3 ≤ t := by dsimp [k] at hkt; omega
  have ht0 : 0 < t := by omega
  have hn : t ≤ t^12 := by simpa using Nat.pow_le_pow_right ht0 (by decide : 1 ≤ 12)
  have heven : Even (t^12) := by
    have h : 2 ∣ t := dvd_pow_self 2 (by dsimp [k]; omega)
    exact even_iff_two_dvd.mpr (h.trans (dvd_pow_self _ (by decide : 12 ≠ 0)))
  have up := hN (t^12) (htN.trans hn) heven
  obtain ⟨root,sqrt⟩ := exact_root_cutoffs t
  simp only [root,sqrt] at up
  rw [dyadic_sieve_factors _ k (by dsimp [k]; omega)] at up
  have down := hT t htT
  dsimp only at down
  have hvol : ((Finset.Icc ((t^12+2)/3) (2*t^12/3)).card:ℝ) ≤ (t^12:ℕ) := by
    exact_mod_cast (show (Finset.Icc ((t^12+2)/3) (2*t^12/3)).card ≤ t^12 by rw [Nat.card_Icc]; omega)
  have htot : ((t^12).totient:ℝ) ≤ (t^12:ℕ) := by exact_mod_cast Nat.totient_le _
  have hpos : (0:ℝ)<(t^12:ℕ) := by positivity
  have pref : ((Finset.Icc ((t^12+2)/3) (2*t^12/3)).card:ℝ)*(t^12).totient/(t^12:ℕ) ≤ (t^12:ℕ) := by
    apply (div_le_iff₀ hpos).mpr
    exact mul_le_mul hvol htot (by positivity) hpos.le
  have prod := hprod (t^6) (ht3.trans (by simpa using Nat.pow_le_pow_right ht0 (by decide : 1 ≤ 6)))
  have L : 0 < Real.log (t:ℝ) := Real.log_pos (by exact_mod_cast (show 1<t by omega))
  have hlog := Real.log_le_log (Real.exp_pos _) (hA.trans (show (A:ℝ) ≤ t by exact_mod_cast htA))
  rw [Real.log_exp] at hlog
  have strict : 24*K < c * Real.log (t:ℝ) := by
    have := (div_lt_iff₀ hc).mp (show 24*K/c < Real.log (t:ℝ) by linarith)
    linarith
  have ub := mul_le_mul_of_nonneg_left prod (by positivity : 0 ≤ ((Finset.Icc ((t^12+2)/3) (2*t^12/3)).card:ℝ)*(t^12).totient/(t^12:ℕ))
  have ub' := mul_le_mul_of_nonneg_right pref (by positivity : 0 ≤ K/(Real.log ((t^6:ℕ):ℝ))^2)
  have all := down.trans (up.trans (mul_le_mul_of_nonneg_left (ub.trans ub') (by norm_num : (0:ℝ)≤23/50)))
  change ((t^12:ℕ):ℝ)/(6*Real.log ((t^12:ℕ):ℝ))*c ≤ _ at all
  push_cast at all
  rw [Real.log_pow,Real.log_pow] at all
  norm_num only [Nat.cast_ofNat] at all
  field_simp at all
  nlinarith only [all,strict,hK]

