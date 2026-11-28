import Conjectures.Goldbach.FareyCubeSqrtDensityRatio
import Mathlib
set_option maxRecDepth 8192 in
open Filter Topology in
theorem sharp_dyadic_prime_card :
    ∀ᶠ x : ℝ in atTop, 997/1000*x ≤
      (((⌊2*x⌋₊).primesLE \ (⌊x⌋₊).primesLE).card:ℝ) * Real.log (2*x) := by
  have h₂ : Tendsto (fun x : ℝ => Chebyshev.theta (2*x)/(2*x)) atTop (𝓝 1) :=
    Chebyshev.tendsto_theta_div_atTop.comp (tendsto_id.const_mul_atTop (by norm_num : (0:ℝ)<2))
  have ha := h₂.eventually (lt_mem_nhds (by norm_num : (999/1000:ℝ) < 1))
  have hb := Chebyshev.tendsto_theta_div_atTop.eventually (gt_mem_nhds (by norm_num : (1:ℝ)<1001/1000))
  filter_upwards [ha,hb,eventually_gt_atTop (1:ℝ)] with x hx₂ hx₁ hx
  have h0 : 0<x := by linarith
  have hdiff : 997/1000*x ≤ Chebyshev.theta (2*x) - Chebyshev.theta x := by
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


private noncomputable def partners (t p : ℕ) :=
  let x : ℝ := (t:ℝ)^120/p
  (⌊2*x⌋₊).primesLE \ (⌊x⌋₊).primesLE

set_option maxRecDepth 8192 in
open Filter Topology in
theorem eventual_band_partners :
    ∀ᶠ t : ℕ in atTop, ∀ (j : ℕ), j < 19 → ∀ p : ℕ, t^(41+j) ≤ p → p ≤ t^60 →
      98/100 * ((t:ℝ)^120/(p:ℝ)) ≤
        ((partners t p).card:ℝ)*((79-(j:ℝ))*Real.log t) := by
  obtain ⟨Y,hY⟩ := eventually_atTop.mp sharp_dyadic_prime_card
  obtain ⟨N,hN⟩ := exists_nat_ge Y
  filter_upwards [eventually_ge_atTop (max 2 N)] with t ht
  have h2 : 2 ≤ t := (le_max_left ..).trans ht
  have tr : (2:ℝ) ≤ t := by exact_mod_cast h2
  have L := Real.log_pos (by linarith : (1:ℝ)<t)
  intro j hj p hlo hhi
  have pp : 0 < p := (pow_pos (by omega : 0<t) _).trans_le hlo
  let x : ℝ := (t:ℝ)^120/p
  have pr : (0:ℝ)<p := by exact_mod_cast pp
  have lo : (t:ℝ)^(41+j) ≤ p := by exact_mod_cast hlo
  have hi : (p:ℝ) ≤ (t:ℝ)^60 := by exact_mod_cast hhi
  have tx : (t:ℝ) ≤ x := by
    apply (le_div_iff₀ pr).mpr
    calc
      _ ≤ (t:ℝ)*(t:ℝ)^60 := mul_le_mul_of_nonneg_left hi (by positivity)
      _ = (t:ℝ)^61 := by ring
      _ ≤ _ := pow_le_pow_right₀ (by linarith) (by decide : 61≤120)
  have big := hY x (hN.trans ((by exact_mod_cast (le_max_right 2 N).trans ht : (N:ℝ) ≤ t).trans tx))
  change 997/1000*x ≤ ((partners t p).card:ℝ)*Real.log (2*x) at big
  have lp := Real.log_le_log (by positivity) lo
  rw [Real.log_pow] at lp
  have eq : Real.log (2*x) = Real.log 2 + 120*Real.log t - Real.log p := by
    dsimp [x]; rw [Real.log_mul (by norm_num) (by positivity : (t:ℝ)^120/(p:ℝ) ≠ 0),
      Real.log_div (by positivity) pr.ne',Real.log_pow]; push_cast; ring
  have l2 := Real.log_le_log (by norm_num : (0:ℝ)<2) tr
  have jr : (j:ℝ) ≤ 18 := by exact_mod_cast (show j ≤ 18 by omega)
  push_cast at lp
  have bound : Real.log (2*x) ≤ (61/60)*((79-(j:ℝ))*Real.log t) := by
    rw [eq]; nlinarith [mul_nonneg (sub_nonneg.mpr jr) L.le]
  have final := big.trans (mul_le_mul_of_nonneg_left bound (Nat.cast_nonneg _))
  change 98/100*x ≤ _
  nlinarith only [final,show 0≤x by dsimp [x]; positivity]



open Finset

theorem bilateral_pair_average (X : ℕ) (S : Finset ℕ) (A : ℕ → Finset ℕ)
    (hS : ∀ u ∈ S, Odd u ∧ X ≤ u ∧ u ≤ 2*X)
    (admit : ∀ u ∈ S, ∀ v ∈ S, u ∈ A (u+v)) :
    S.card^2 ≤ ∑ n ∈ (Icc (2*X) (4*X)).filter Even,
      ((A n).filter (fun u => n-u ∈ A n)).card := by
  classical
  let T := (Icc (2*X) (4*X)).filter Even
  have lands : ((S.product S : Finset _) : Set (ℕ × ℕ)).MapsTo (fun w => w.1+w.2) T := by
    rintro ⟨u,v⟩ hw
    obtain ⟨hu,hv⟩ := mem_product.mp hw
    obtain ⟨⟨i,hi⟩,hul,huu⟩ := hS _ hu
    obtain ⟨⟨j,hj⟩,hvl,hvu⟩ := hS _ hv
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨by dsimp; omega,by dsimp; omega⟩,⟨i+j+1,by dsimp; omega⟩⟩
  calc
    _ = (S.product S).card := by simp [pow_two]
    _ = _ := card_eq_sum_card_fiberwise lands
    _ ≤ _ := by
      apply sum_le_sum
      intro n _
      apply card_le_card_of_injOn Prod.fst
      · rintro ⟨u,v⟩ h
        obtain ⟨h,hs⟩ := mem_filter.mp h
        obtain ⟨hu,hv⟩ := mem_product.mp h
        change u+v=n at hs
        subst n
        exact mem_filter.mpr ⟨admit _ hu _ hv,by simpa [Nat.add_sub_cancel_left, Nat.add_comm u v] using admit _ hv _ hu⟩
      · rintro ⟨u,v⟩ h ⟨a,b⟩ g eq
        obtain ⟨_,hh⟩ := mem_filter.mp h
        obtain ⟨_,gg⟩ := mem_filter.mp g
        change u+v=n at hh
        change a+b=n at gg
        change u=a at eq
        exact Prod.ext eq (by dsimp; omega)


private noncomputable def cubeCut (n : ℕ) := ⌊(n:ℝ)^(1/3:ℝ)⌋₊
private def semi (u : ℕ) := u.minFac.Prime ∧ (u/u.minFac).Prime
open Classical in
private noncomputable def acceptedSide (n : ℕ) :=
  (Icc ((n+2)/3) (2*n/3)).filter fun u => cubeCut n < u.minFac ∧ semi u

open Classical in
private noncomputable def commonSemiprimes (X : ℕ) :=
  (Icc X (2*X)).filter fun u => Odd u ∧ cubeCut (4*X) < u.minFac ∧ semi u

open Classical in
theorem farey_bilateral_common_set (X : ℕ) :
    (commonSemiprimes X).card^2 ≤ ∑ n ∈ (Icc (2*X) (4*X)).filter Even,
      ((acceptedSide n).filter (fun u => n-u ∈ acceptedSide n)).card := by
  classical
  apply bilateral_pair_average
  · intro u hu
    obtain ⟨hi,hodd,_,_⟩ := mem_filter.mp hu
    exact ⟨hodd,mem_Icc.mp hi⟩
  · intro u hu v hv
    obtain ⟨hi,_,hcut,hsemi⟩ := mem_filter.mp hu
    obtain ⟨hj,_⟩ := mem_filter.mp hv
    obtain ⟨ul,uu⟩ := mem_Icc.mp hi
    obtain ⟨vl,vu⟩ := mem_Icc.mp hj
    have mono : cubeCut (u+v) ≤ cubeCut (4*X) := by
      apply Nat.floor_mono
      apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
      exact_mod_cast (show u+v ≤ 4*X by omega)
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega,by omega⟩,mono.trans_lt hcut,hsemi⟩


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


set_option maxRecDepth 8192 in
private theorem partner_facts {t p q : ℕ} (ht : 4 ≤ t) (hp : p.Prime)
    (lo : t^41 < p) (hi : p ≤ t^60) (hq : q ∈ partners t p) :
    (p*q).minFac = p ∧ p*q ∈ commonSemiprimes (t^120) := by
  classical
  let x := (t:ℝ)^120 / p
  obtain ⟨upper,lower⟩ := mem_sdiff.mp hq
  obtain ⟨uq,qp⟩ := Nat.mem_primesLE.mp upper
  have lq : ⌊x⌋₊ < q := by
    by_contra! h
    exact lower (Nat.mem_primesLE.mpr ⟨h,qp⟩)
  have pr : (0:ℝ) < p := by exact_mod_cast hp.pos
  have hlow := (div_lt_iff₀ pr).mp ((Nat.floor_lt (show 0≤x by dsimp [x]; positivity)).mp lq)
  have hu : (q:ℝ) ≤ (2*(t:ℝ)^120)/p := by
    rw [mul_div_assoc]
    exact (Nat.le_floor_iff (by positivity)).mp uq
  have hh := (le_div_iff₀ pr).mp hu
  have bot : t^120 < p*q := by exact_mod_cast (by linarith only [hlow] : (t:ℝ)^120 < p*q)
  have top : p*q ≤ 2*t^120 := by exact_mod_cast (by linarith only [hh] : (p:ℝ)*q ≤ 2*(t:ℝ)^120)
  have sq : p*p ≤ t^120 := by calc p*p ≤ t^60*t^60 := Nat.mul_le_mul hi hi
                           _ = t^120 := by ring
  have pq : p ≤ q := by by_contra! h; have := Nat.mul_le_mul_left p h.le; omega
  have least := least_of_pair hp qp pq
  have powbound : 4*t^120 ≤ t^123 := by
    rw [show t^123 = t^3*t^120 by ring]
    exact Nat.mul_le_mul_right _ (by have h := Nat.pow_le_pow_right (by omega : 0<t) (by decide : 1 ≤ 3); simp only [pow_one] at h; omega)
  have cutoff : cubeCut (4*t^120) ≤ t^41 := by
    unfold cubeCut
    have raw := Real.rpow_le_rpow (by positivity : (0:ℝ) ≤ ((4*t^120:ℕ):ℝ))
      (by exact_mod_cast powbound : ((4*t^120:ℕ):ℝ) ≤ ((t^123:ℕ):ℝ)) (by norm_num : (0:ℝ) ≤ 1/3)
    have hf := Nat.floor_mono raw
    rw [Nat.cast_pow,←Real.rpow_natCast_mul (Nat.cast_nonneg _)] at hf
    norm_num at hf
    simpa only [←Nat.cast_pow,Nat.floor_natCast,Nat.cast_mul,Nat.cast_ofNat] using hf
  have gt : 2 < p := by
    have := Nat.pow_le_pow_right (by omega : 0<t) (by decide : 1 ≤ 41)
    simp only [pow_one] at this; omega
  refine ⟨least,mem_filter.mpr ⟨mem_Icc.mpr ⟨bot.le,top⟩,
    (hp.odd_of_ne_two (by omega)).mul (qp.odd_of_ne_two (by omega)),?_,?_⟩⟩
  · rw [least]; exact cutoff.trans_lt lo
  · unfold semi
    rw [least,Nat.mul_div_cancel_left _ hp.pos]
    exact ⟨hp,qp⟩


theorem common_partner_total (t : ℕ) (ht : 4 ≤ t) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ t^41 < p ∧ p ≤ t^60) :
    (∑ p ∈ P, (partners t p).card) ≤ (commonSemiprimes (t^120)).card := by
  classical
  rw [←card_sigma]
  apply card_le_card_of_injOn (fun x : Sigma (fun _ : ℕ => ℕ) => x.1*x.2)
  · rintro ⟨p,q⟩ hx
    obtain ⟨pp,hq⟩ := mem_sigma.mp hx
    obtain ⟨pr,lo,hi⟩ := hP _ pp
    exact (partner_facts ht pr lo hi hq).2
  · rintro ⟨p,q⟩ hx ⟨a,b⟩ hy eq
    obtain ⟨pp,hq⟩ := mem_sigma.mp hx
    obtain ⟨aa,hb⟩ := mem_sigma.mp hy
    obtain ⟨pr,lo,hi⟩ := hP _ pp
    obtain ⟨ar,alo,ahi⟩ := hP _ aa
    have l := (partner_facts ht pr lo hi hq).1
    have r := (partner_facts ht ar alo ahi hb).1
    change p*q=a*b at eq
    have same : p=a := l.symm.trans ((congrArg Nat.minFac eq).trans r)
    subst a
    obtain rfl := Nat.eq_of_mul_eq_mul_left pr.pos eq
    rfl


open ErdosStraus.PrimeEstimates.Mertens Filter Topology Finset

noncomputable def bandMass (t a b : ℕ) : ℝ :=
  ∑ p ∈ primesUpTo (t^b) \ primesUpTo (t^a), (p:ℝ)⁻¹

theorem uniform_band_error (ε : ℝ) (he : 0 < ε) :
    ∀ᶠ t : ℕ in atTop, ∀ a b : ℕ, 0 < a → a ≤ b →
      |bandMass t a b - Real.log ((b:ℝ)/a)| < ε := by
  obtain ⟨C,hC,h⟩ := mertensSecond
  have lim := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop (2:ℕ),lim.eventually_ge_atTop (4*C/ε)] with t ht hlarge
  change 4*C/ε ≤ Real.log t at hlarge
  have L := Real.log_pos (by exact_mod_cast (show 1<t by omega) : (1:ℝ)<t)
  have cb : C/Real.log t ≤ ε/4 := (div_le_iff₀ L).mpr (by linarith [(div_le_iff₀ he).mp hlarge])
  have est (k : ℕ) (hk : 0<k) :
      |primeReciprocalSum (t^k) - (Real.log k + Real.log (Real.log t) + mertensSecondConstant)| ≤ ε/4 := by
    have hu : 2 ≤ t^k := ht.trans (by simpa using Nat.pow_le_pow_right (by omega : 0<t) hk)
    have raw := h ((t^k:ℕ):ℝ) (by exact_mod_cast hu)
    rw [Nat.floor_natCast,Nat.cast_pow,Real.log_pow,Real.log_mul (by exact_mod_cast hk.ne') L.ne'] at raw
    have kr : (1:ℝ) ≤ k := by exact_mod_cast hk
    exact raw.trans ((div_le_div_of_nonneg_left hC.le L (by nlinarith [mul_nonneg (sub_nonneg.mpr kr) L.le])).trans cb)
  intro a b ha hab
  have hb := ha.trans_le hab
  have sub : primesUpTo (t^a) ⊆ primesUpTo (t^b) := by
    intro p hp
    obtain ⟨pr,le⟩ := mem_primesUpTo.mp hp
    exact mem_primesUpTo.mpr ⟨pr,le.trans (Nat.pow_le_pow_right (by omega) hab)⟩
  rw [bandMass,sum_sdiff_eq_sub sub,Real.log_div (by exact_mod_cast hb.ne') (by exact_mod_cast ha.ne')]
  simp only [←one_div]
  change |primeReciprocalSum (t^b)-primeReciprocalSum (t^a) - _| < ε
  have ea := abs_le.mp (est a ha)
  have eb := abs_le.mp (est b hb)
  rw [abs_lt]; constructor <;> linarith

theorem bandMass_limit (a b : ℕ) (ha : 0<a) (hab : a≤b) :
    Tendsto (fun t => bandMass t a b) atTop (𝓝 (Real.log ((b:ℝ)/a))) := by
  rw [Metric.tendsto_nhds]
  intro ε he
  filter_upwards [uniform_band_error ε he] with t ht
  simpa [Real.dist_eq] using ht a b ha hab



open Finset

theorem smooth_band_constant :
    91 < 120 - ∑ j ∈ range 6, (60-10*(j:ℝ))*Real.log ((70+10*(j:ℝ))/(60+10*(j:ℝ))) := by
  have h : ∀ j ∈ range 6, (60-10*(j:ℝ))*Real.log ((70+10*(j:ℝ))/(60+10*(j:ℝ))) ≤
      (60-10*(j:ℝ))*(10/(60+10*(j:ℝ))) := by
    intro j hj
    have b : (j:ℝ) < 6 := by exact_mod_cast mem_range.mp hj
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    apply (Real.log_le_sub_one_of_pos (by positivity)).trans_eq
    field_simp; ring
  have e := sum_le_sum h
  norm_num [sum_range_succ] at e ⊢
  linarith

theorem semiprime_band_constant :
    63/100 < ∑ j ∈ range 19, (120/(79-(j:ℝ)))*Real.log ((42+(j:ℝ))/(41+(j:ℝ))) := by
  have h : ∀ j ∈ range 19, (120/(79-(j:ℝ)))*(1/(42+(j:ℝ))) ≤
      (120/(79-(j:ℝ)))*Real.log ((42+(j:ℝ))/(41+(j:ℝ))) := by
    intro j hj
    have b : (j:ℝ) < 19 := by exact_mod_cast mem_range.mp hj
    apply mul_le_mul_of_nonneg_left _ (div_nonneg (by norm_num) (by linarith))
    apply le_trans _ (Real.one_sub_inv_le_log_of_pos (by positivity))
    apply le_of_eq; field_simp; ring
  have e := sum_le_sum h
  refine lt_of_lt_of_le ?_ e
  norm_num [sum_range_succ]

theorem farey_constants_strict :
    (2/25:ℝ)*(2/3)*(8/3)^2 < (63/100:ℝ)^2 := by norm_num


theorem eventual_actual_band_constants :
    ∀ᶠ t : ℕ in atTop,
      91 < 120 - ∑ j ∈ range 6, (60-10*(j:ℝ))*bandMass t (60+10*j) (70+10*j) ∧
      63/100 < ∑ j ∈ range 19, (120/(79-(j:ℝ)))*bandMass t (41+j) (42+j) := by
  have sm := tendsto_finsetSum (range 6) (fun j _ =>
    (bandMass_limit (60+10*j) (70+10*j) (by omega) (by omega)).const_mul (60-10*(j:ℝ)))
  have se := tendsto_finsetSum (range 19) (fun j _ =>
    (bandMass_limit (41+j) (42+j) (by omega) (by omega)).const_mul (120/(79-(j:ℝ))))
  have hs := (tendsto_const_nhds (x := (120:ℝ))).sub sm
  apply Filter.Eventually.and
  · apply hs.eventually_const_lt
    push_cast
    exact smooth_band_constant
  · apply se.eventually_const_lt
    push_cast
    exact semiprime_band_constant



open Finset

theorem smooth_harmonic_product_bound (z : ℕ) (s : Finset ℕ)
    (hs : ∀ k ∈ s, k ∈ z.smoothNumbers) :
    (∑ k ∈ s, (k:ℝ)⁻¹) * (∏ p ∈ z.primesBelow, (1-(p:ℝ)⁻¹)) ≤ 1 := by
  classical
  let f : ℕ →* ℝ := { toFun := fun k => (k:ℝ)⁻¹,
                       map_one' := by simp,
                       map_mul' := by intros; simp [mul_comm] }
  have hp {p : ℕ} (h : p.Prime) : ‖f p‖ < 1 := by
    change ‖(p:ℝ)⁻¹‖ < 1
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast h.one_lt)
  have hsum := (EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric hp z).2
  have pos : 0 < ∏ p ∈ z.primesBelow, (1-(p:ℝ)⁻¹) := by
    apply prod_pos
    intro p h
    apply sub_pos.mpr
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Nat.prime_of_mem_primesBelow h).one_lt)
  apply (le_div_iff₀ pos).mp
  rw [one_div,←Finset.prod_inv_distrib]
  change _ ≤ ∏ p ∈ z.primesBelow, (1-f p)⁻¹
  rw [← hsum.tsum_eq]
  rw [← Finset.sum_subtype_of_mem (fun k : ℕ => (k:ℝ)⁻¹) hs]
  exact hsum.summable.sum_le_tsum _ (fun k _ => by change 0 ≤ ((k.val:ℝ)⁻¹); positivity)


private noncomputable def harmonicTo (N : ℕ) := ∑ n ∈ Icc 1 N, (n:ℝ)⁻¹

private theorem multiples_harmonic (p N : ℕ) (hp : 0 < p) :
    (∑ n ∈ (Icc 1 N).filter (p ∣ ·), (n:ℝ)⁻¹) = (p:ℝ)⁻¹ * harmonicTo (N/p) := by
  unfold harmonicTo
  rw [mul_sum]
  apply sum_bij (fun n _ => n/p)
  · intro n hn
    obtain ⟨hi,hd⟩ := mem_filter.mp hn
    have npos := (mem_Icc.mp hi).1
    exact mem_Icc.mpr ⟨(Nat.le_div_iff_mul_le hp).mpr (by simpa using Nat.le_of_dvd npos hd),
      Nat.div_le_div_right (mem_Icc.mp hi).2⟩
  · intro a ha b hb heq
    have h := congrArg (· * p) heq
    simpa only [Nat.div_mul_cancel (mem_filter.mp ha).2,Nat.div_mul_cancel (mem_filter.mp hb).2] using h
  · intro k hk
    obtain ⟨hl,hu⟩ := mem_Icc.mp hk
    refine ⟨k*p,mem_filter.mpr ⟨mem_Icc.mpr ⟨by nlinarith, (Nat.le_div_iff_mul_le hp).mp hu⟩,
      dvd_mul_left _ _⟩,Nat.mul_div_cancel _ hp⟩
  · intro n hn
    have eq := Nat.div_mul_cancel (mem_filter.mp hn).2
    have realEq : ((n/p:ℕ):ℝ)*p = n := by exact_mod_cast eq
    rw [←realEq,mul_inv_rev]

open Classical in
theorem smooth_harmonic_loss (z N : ℕ) :
    harmonicTo N ≤ (∑ n ∈ (Icc 1 N).filter (· ∈ z.smoothNumbers), (n:ℝ)⁻¹) +
      ∑ p ∈ (Icc z N).filter Nat.Prime, (p:ℝ)⁻¹ * harmonicTo (N/p) := by
  classical
  let I := Icc 1 N
  let P := (Icc z N).filter Nat.Prime
  have each (n : ℕ) (hn : n ∈ I) :
      (n:ℝ)⁻¹ ≤ (if n ∈ z.smoothNumbers then (n:ℝ)⁻¹ else 0) +
        ∑ p ∈ P, (if p ∣ n then (n:ℝ)⁻¹ else 0) := by
    by_cases h : n ∈ z.smoothNumbers
    · simp only [if_pos h,le_add_iff_nonneg_right]; apply sum_nonneg; intros; positivity
    · rw [if_neg h,zero_add]
      rw [Nat.mem_smoothNumbers'] at h
      push_neg at h
      obtain ⟨p,hp,hd,hl⟩ := h
      have mem : p ∈ P := mem_filter.mpr ⟨mem_Icc.mpr ⟨hl,(Nat.le_of_dvd (mem_Icc.mp hn).1 hd).trans (mem_Icc.mp hn).2⟩,hp⟩
      have ub := single_le_sum (f := fun q : ℕ => if q ∣ n then (n:ℝ)⁻¹ else 0)
        (s := P) (fun q _ => by split_ifs <;> positivity) mem
      simpa [hd] using ub
  have H := sum_le_sum each
  simp only [sum_add_distrib] at H
  rw [sum_comm (s := I) (t := P)] at H
  simp_rw [←sum_filter] at H
  apply H.trans_eq
  congr 1
  exact sum_congr rfl (fun p h => multiples_harmonic p N (mem_filter.mp h).2.pos)


private def band (t j : ℕ) := primesUpTo (t^(70+10*j)) \ primesUpTo (t^(60+10*j))

private theorem bands_sum (t : ℕ) (ht : 1≤t) (k : ℕ) (F : ℕ → ℝ) :
    (∑ j ∈ range k, ∑ p ∈ band t j, F p) =
      (∑ p ∈ primesUpTo (t^(60+10*k)), F p) - ∑ p ∈ primesUpTo (t^60), F p := by
  induction k with
  | zero => simp
  | succ k ih =>
    have sub : primesUpTo (t^(60+10*k)) ⊆ primesUpTo (t^(70+10*k)) := by
      intro p hp
      obtain ⟨pr,hh⟩ := mem_primesUpTo.mp hp
      exact mem_primesUpTo.mpr ⟨pr,hh.trans (Nat.pow_le_pow_right ht (by omega))⟩
    rw [sum_range_succ,ih,band,sum_sdiff_eq_sub sub,show 60+10*(k+1)=70+10*k by omega]
    ring

private theorem harmonic_cast (n : ℕ) : harmonicTo n = (harmonic n : ℝ) := by
  simp [harmonicTo,harmonic_eq_sum_Icc]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
theorem six_band_harmonic_loss (t : ℕ) (ht : 2≤t) :
    (∑ p ∈ (Icc (t^60+1) (t^120)).filter Nat.Prime,
      (p:ℝ)⁻¹*harmonicTo (t^120/p)) ≤
    ∑ j ∈ range 6, (1+(60-10*(j:ℝ))*Real.log t)*bandMass t (60+10*j) (70+10*j) := by
  classical
  let F := fun p : ℕ => (p:ℝ)⁻¹ * harmonicTo (t^120/p)
  have eq : (Icc (t^60+1) (t^120)).filter Nat.Prime =
      primesUpTo (t^120) \ primesUpTo (t^60) := by
    ext p
    constructor
    · intro h
      obtain ⟨hm,pr⟩ := mem_filter.mp h
      obtain ⟨l,u⟩ := mem_Icc.mp hm
      exact mem_sdiff.mpr ⟨mem_primesUpTo.mpr ⟨pr,u⟩,fun h => (Nat.not_le_of_lt l) (mem_primesUpTo.mp h).2⟩
    · intro h
      obtain ⟨hi,lo⟩ := mem_sdiff.mp h
      obtain ⟨pr,u⟩ := mem_primesUpTo.mp hi
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨lt_of_not_ge (fun hh => lo (mem_primesUpTo.mpr ⟨pr,hh⟩)),u⟩,pr⟩
  have sub : primesUpTo (t^60) ⊆ primesUpTo (t^120) := by
    intro p hp
    obtain ⟨pr,hh⟩ := mem_primesUpTo.mp hp
    exact mem_primesUpTo.mpr ⟨pr,hh.trans (Nat.pow_le_pow_right (by omega) (by decide))⟩
  rw [eq,sum_sdiff_eq_sub sub]
  change (∑ p ∈ primesUpTo (t^(60+10*6)), F p) - _ ≤ _
  rw [←bands_sum t (by omega) 6 F]
  apply sum_le_sum
  intro j hj
  have hj6 := mem_range.mp hj
  unfold bandMass; rw [mul_sum]
  apply sum_le_sum
  intro p hp
  obtain ⟨hi,lo⟩ := mem_sdiff.mp hp
  obtain ⟨pr,up⟩ := mem_primesUpTo.mp hi
  have lower : t^(60+10*j) < p := by by_contra! h; exact lo (mem_primesUpTo.mpr ⟨pr,h⟩)
  have ple : p ≤ t^120 := up.trans (Nat.pow_le_pow_right (by omega) (by omega))
  have poweq : t^(60-10*j)*t^(60+10*j)=t^120 := by rw [←pow_add]; congr 1; omega
  have du : t^120/p ≤ t^(60-10*j) := by
    have h1 : t^120/p ≤ t^120 / t^(60+10*j) := Nat.div_le_div_left lower.le (pow_pos (by omega : 0<t) _)
    apply h1.trans_eq; rw [←poweq,Nat.mul_div_cancel _ (pow_pos (by omega : 0<t) _)]
  have dp : 0 < t^120/p := Nat.div_pos ple pr.pos
  have logle := Real.log_le_log (by exact_mod_cast dp : (0:ℝ)<(t^120/p:ℕ))
    (by exact_mod_cast du : ((t^120/p:ℕ):ℝ) ≤ (t:ℝ)^(60-10*j))
  rw [Real.log_pow,Nat.cast_sub (by omega : 10*j≤60)] at logle
  push_cast at logle
  have hh : (harmonic (t^120/p):ℝ) ≤ 1+(60-10*(j:ℝ))*Real.log t := by linarith [harmonic_le_one_add_log (t^120/p)]
  dsimp [F]; rw [harmonic_cast,mul_comm (p:ℝ)⁻¹]
  exact mul_le_mul_of_nonneg_right hh (by positivity)


set_option maxRecDepth 8192 in
theorem eventual_smooth_product :
    ∀ᶠ t : ℕ in atTop, (90*Real.log t) *
      (((t^60+1).primesBelow).prod (fun p : ℕ => (1-(p:ℝ)⁻¹))) ≤ 1 := by
  classical
  let c := ∑ j ∈ range 6, Real.log (((70+10*j:ℕ):ℝ)/(60+10*j:ℕ))
  have sm := tendsto_finsetSum (range 6) (fun j _ =>
    bandMass_limit (60+10*j) (70+10*j) (by omega) (by omega))
  have ub := sm.eventually_lt_const (show c<c+1 by linarith)
  have lim := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventual_actual_band_constants,ub,lim.eventually_ge_atTop (c+1),
    eventually_ge_atTop (2:ℕ)] with t hb hsum hlog ht
  change c+1 ≤ Real.log t at hlog
  let B := fun j => bandMass t (60+10*j) (70+10*j)
  change (∑ j ∈ range 6, B j) < c+1 at hsum
  have hcoef := hb.1
  change 91 < 120-(∑ j ∈ range 6,(60-10*(j:ℝ))*B j) at hcoef
  have L := Real.log_pos (by exact_mod_cast (show 1<t by omega) : (1:ℝ)<t)
  have loss := six_band_harmonic_loss t ht
  have whole := smooth_harmonic_loss (t^60+1) (t^120)
  let S := (Icc 1 (t^120)).filter (· ∈ (t^60+1).smoothNumbers)
  let mass := ∑ n ∈ S, (n:ℝ)⁻¹
  have hlower : 120*Real.log t ≤ harmonicTo (t^120) := by
    rw [harmonic_cast]
    have logup := log_add_one_le_harmonic (t^120)
    apply le_trans _ logup
    change (120:ℕ) * Real.log (t:ℝ) ≤ _
    rw [←Real.log_pow]
    apply Real.log_le_log (by positivity)
    push_cast; linarith
  have e : harmonicTo (t^120) ≤ mass + ∑ j ∈ range 6, (1+(60-10*(j:ℝ))*Real.log t)*B j :=
    whole.trans (add_le_add_right loss _)
  simp_rw [add_mul,one_mul,mul_right_comm (60-10*(_ : ℝ)) (Real.log t)] at e
  rw [sum_add_distrib,←sum_mul] at e
  have good : 90*Real.log t ≤ mass := by
    nlinarith only [hlower,e,hsum,hlog,mul_lt_mul_of_pos_right hcoef L]
  have prodNN : 0 ≤ ((t^60+1).primesBelow).prod (fun p : ℕ => (1-(p:ℝ)⁻¹)) := by
    apply prod_nonneg
    intro p hp
    exact sub_nonneg.mpr (inv_le_one_of_one_le₀ (by exact_mod_cast (Nat.prime_of_mem_primesBelow hp).one_le))
  exact (mul_le_mul_of_nonneg_right good prodNN).trans
    (smooth_harmonic_product_bound _ S (fun k hk => (mem_filter.mp hk).2))


set_option maxRecDepth 8192 in
theorem actual_semiprime_lower :
    ∀ᶠ t : ℕ in atTop, (98/100:ℝ)*(63/100)*(t:ℝ)^120 ≤
      ((commonSemiprimes (t^120)).card:ℝ)*(120*Real.log t) := by
  classical
  filter_upwards [eventual_actual_band_constants,eventual_band_partners,eventually_ge_atTop (4:ℕ)]
    with t hbands hpart ht
  let B := fun j : ℕ => primesUpTo (t^(42+j)) \ primesUpTo (t^(41+j))
  let J := range 19
  have memB (j p : ℕ) (h : p ∈ B j) : p.Prime ∧ t^(41+j)<p ∧ p≤t^(42+j) := by
    obtain ⟨up,lo⟩ := mem_sdiff.mp h
    obtain ⟨pr,upper⟩ := mem_primesUpTo.mp up
    exact ⟨pr,lt_of_not_ge (fun hh => lo (mem_primesUpTo.mpr ⟨pr,hh⟩)),upper⟩
  have order (a b : ℕ) (h : a≤b) := Nat.pow_le_pow_right (by omega : 0<t) h
  have separated (i j : ℕ) (h : i<j) : Disjoint (B i) (B j) := by
    apply disjoint_left.mpr
    intro p hi hj
    have e := order (42+i) (41+j) (by omega)
    exact (not_lt_of_ge ((memB i p hi).2.2.trans e)) (memB j p hj).2.1
  have disj : (J : Set ℕ).PairwiseDisjoint B := by
    intro i _ j _ hij
    rcases lt_or_gt_of_ne hij with hh|hh
    · exact separated i j hh
    · exact (separated j i hh).symm
  have total := common_partner_total t ht (J.biUnion B) (by
    intro p hp
    obtain ⟨j,hj,hp⟩ := mem_biUnion.mp hp
    have bound := mem_range.mp hj
    obtain ⟨pr,lo,hi⟩ := memB j p hp
    exact ⟨pr,(order 41 _ (by omega)).trans_lt lo,hi.trans (order _ 60 (by omega))⟩)
  rw [sum_biUnion disj] at total
  have totalR : (∑ j ∈ J, ∑ p ∈ B j, ((partners t p).card:ℝ)) ≤
      ((commonSemiprimes (t^120)).card:ℝ) := by exact_mod_cast total
  let C : ℝ := (98/100)*(t:ℝ)^120
  have byband (j : ℕ) (hj : j ∈ J) :
      C*((120/(79-(j:ℝ)))*bandMass t (41+j) (42+j)) ≤
        (∑ p ∈ B j, ((partners t p).card:ℝ))*(120*Real.log t) := by
    have jlt := mem_range.mp hj
    have den : 0 < 79-(j:ℝ) := by
      have hjr : (j:ℝ)<19 := by exact_mod_cast jlt
      linarith
    unfold bandMass
    change C*(120/(79-(j:ℝ))*(∑ p ∈ B j,(p:ℝ)⁻¹)) ≤ _
    rw [←mul_assoc,mul_sum,sum_mul]
    apply sum_le_sum
    intro p hp
    obtain ⟨pr,lo,hi⟩ := memB j p hp
    have h := hpart j jlt p lo.le (hi.trans (order _ 60 (by omega)))
    have pp : (0:ℝ)<p := by exact_mod_cast pr.pos
    dsimp [C]; field_simp at h ⊢
    nlinarith only [h]
  have sumB := sum_le_sum byband
  rw [←mul_sum,←sum_mul] at sumB
  have lower := mul_le_mul_of_nonneg_left hbands.2.le (by dsimp [C]; positivity : 0≤C)
  have L : 0 ≤ 120*Real.log (t:ℝ) := by positivity
  exact (by linarith only [show C*(63/100)=(98/100:ℝ)*(63/100)*(t:ℝ)^120 by dsimp [C]; ring] :
    (98/100:ℝ)*(63/100)*(t:ℝ)^120 ≤ C*(63/100)).trans (lower.trans (sumB.trans
    (mul_le_mul_of_nonneg_right totalR L)))


open Finset

theorem multiples_window_bound (X d : ℕ) (hd : 0 < d) :
    (((Icc X (2*X)).filter (d ∣ ·)).card : ℝ) ≤ X/(d:ℝ)+1 := by
  let S := (Icc X (2*X)).filter (d ∣ ·)
  by_cases h : S.Nonempty
  · let a := S.min' h
    have ha : a ∈ S := min'_mem _ _
    have sa := mem_filter.mp ha
    have bound : S.card ≤ (range (X/d+1)).card := by
      apply card_le_card_of_injOn (fun n => (n-a)/d)
      · intro n hn
        obtain ⟨hi,_⟩ := mem_filter.mp hn
        exact mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right
          (by have := (mem_Icc.mp hi).2; have := (mem_Icc.mp sa.1).1; omega)))
      · intro n hn m hm eq
        have hn' : a ≤ n := min'_le _ _ hn
        have hm' : a ≤ m := min'_le _ _ hm
        have dn := Nat.dvd_sub (mem_filter.mp hn).2 sa.2
        have dm := Nat.dvd_sub (mem_filter.mp hm).2 sa.2
        have e := congrArg (· * d) eq
        change (n-a)/d*d = (m-a)/d*d at e
        rw [Nat.div_mul_cancel dn,Nat.div_mul_cancel dm] at e
        omega
    simp only [card_range] at bound
    have frac : ((X/d : ℕ):ℝ) ≤ X/(d:ℝ) := (le_div_iff₀ (by exact_mod_cast hd)).mpr
      (by exact_mod_cast Nat.div_mul_le_self X d)
    change (S.card:ℝ) ≤ _
    have cb : (S.card:ℝ) ≤ (X/d:ℕ)+1 := by exact_mod_cast bound
    linarith
  · change (S.card:ℝ) ≤ _
    rw [not_nonempty_iff_eq_empty.mp h]; simp; positivity


theorem sieve_expansion_bound (P : Finset ℕ) (hP : ∀ p ∈ P, 2 ≤ p)
    (X : ℝ) (g : Finset ℕ → ℝ)
    (h : ∀ T ∈ P.powerset, g T ≤ X*(∏ p ∈ T, (1/(p:ℝ)))+1) :
    (∑ T ∈ P.powerset, ((∏ p ∈ T, 1/(p:ℝ)) *
        ∏ p ∈ P \ T, (1-2/(p:ℝ))) * g T)
      ≤ X*(∏ p ∈ P, (1-1/(p:ℝ))^2) + ∏ p ∈ P, (1-1/(p:ℝ)) := by
  classical
  let a := fun p : ℕ => 1/(p:ℝ)
  let b := fun p : ℕ => 1-2/(p:ℝ)
  have pos (T : Finset ℕ) : 0 ≤ (∏ p ∈ T, a p)*(∏ p ∈ P \ T, b p) := by
    apply mul_nonneg (prod_nonneg (fun _ _ => by dsimp [a]; positivity))
    apply prod_nonneg
    intro p hp
    have hh : (2:ℝ) ≤ p := by exact_mod_cast hP p (mem_sdiff.mp hp).1
    dsimp [b]; have hp' : (0:ℝ)<p := by linarith
    exact sub_nonneg.mpr ((div_le_one hp').mpr hh)
  apply (sum_le_sum (fun T hT => mul_le_mul_of_nonneg_left (h T hT) (pos T))).trans_eq
  change (∑ T ∈ P.powerset, ((∏ p ∈ T, a p)*(∏ p ∈ P \ T, b p)) *
    (X*(∏ p ∈ T, a p)+1)) = _
  simp_rw [show ∀ u v : ℝ, u*v*(X*u+1)=X*(u^2*v)+u*v by intros; ring]
  rw [sum_add_distrib,←mul_sum]
  simp_rw [←prod_pow]
  rw [←prod_add,←prod_add]
  congr 1
  · congr 1
    apply prod_congr rfl
    intro p hp
    dsimp [a,b]; ring
  · apply prod_congr rfl
    intro p hp
    dsimp [a,b]; ring


theorem interval_sieve_mean (X : ℕ) (P : Finset ℕ) (hp : ∀ p ∈ P, p.Prime) :
    (∑ n ∈ Icc X (2*X), ∏ p ∈ P, ((if p ∣ n then 1/(p:ℝ) else 0)+(1-2/(p:ℝ)))) ≤
      X*(∏ p ∈ P, (1-1/(p:ℝ))^2) + ∏ p ∈ P, (1-1/(p:ℝ)) := by
  classical
  let I := Icc X (2*X)
  let g := fun T : Finset ℕ => ((I.filter (fun n => ∀ p ∈ T, p ∣ n)).card:ℝ)
  have hg (T : Finset ℕ) (hT : T ∈ P.powerset) :
      g T ≤ X*(∏ p ∈ T, 1/(p:ℝ))+1 := by
    have ht := mem_powerset.mp hT
    let d := ∏ p ∈ T, p
    have hd : 0 < d := prod_pos fun p h => (hp p (ht h)).pos
    have sub : I.filter (fun n => ∀ p ∈ T, p ∣ n) ⊆ I.filter (d ∣ ·) := by
      intro n hn
      obtain ⟨hi,hh⟩ := mem_filter.mp hn
      refine mem_filter.mpr ⟨hi,Finset.prod_dvd_of_isRelPrime ?_ hh⟩
      intro a ha b hb hab
      exact Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes (hp a (ht ha)) (hp b (ht hb))).mpr hab)
    have H := multiples_window_bound X d hd
    have hcast : (d:ℝ) = ∏ p ∈ T, (p:ℝ) := by simp [d]
    apply le_trans (show g T ≤ ((I.filter (d ∣ ·)).card:ℝ) by dsimp only [g]; exact_mod_cast card_le_card sub)
    simpa [hcast,div_eq_mul_inv] using H
  apply le_trans _ (sieve_expansion_bound P (fun p h => (hp p h).two_le) X g hg)
  apply le_of_eq
  simp_rw [prod_add,prod_ite_zero]
  rw [sum_comm]
  apply sum_congr rfl
  intro T hT
  simp_rw [ite_mul,zero_mul]
  rw [← sum_filter]
  simp [g,I,mul_comm]


theorem terminal_multiplier_le (n : ℕ) (hn : 0 < n) (P : Finset ℕ)
    (hP : P ⊆ (Icc 2 n.sqrt).filter Nat.Prime) :
    (n.totient:ℝ)/n * (∏ p ∈ ((Icc 2 n.sqrt).filter Nat.Prime).filter (fun p => ¬ p ∣ n),
      (1-2/(p:ℝ))) ≤ ∏ p ∈ P, ((if p ∣ n then 1/(p:ℝ) else 0)+(1-2/(p:ℝ))) := by
  classical
  let F := (Icc 2 n.sqrt).filter Nat.Prime
  have ht : (n.totient:ℝ) = n * ∏ p ∈ n.primeFactors, (1-(p:ℝ)⁻¹) := by
    simpa using congrArg (fun x : ℚ => (x:ℝ)) (Nat.totient_eq_mul_prod_factors n)
  have ge (p : ℕ) (hp : p ∈ F) : (2:ℝ) ≤ p := by exact_mod_cast (mem_Icc.mp (mem_filter.mp hp).1).1
  have nn (p : ℕ) (hp : p ∈ F) : 0 ≤ 1-2/(p:ℝ) := by
    have g := ge p hp
    exact sub_nonneg.mpr ((div_le_one (by linarith)).mpr g)
  have sub : P.filter (· ∣ n) ⊆ n.primeFactors := by
    intro p hp
    obtain ⟨hm,hd⟩ := mem_filter.mp hp
    exact Nat.mem_primeFactors.mpr ⟨(mem_filter.mp (hP hm)).2,hd,hn.ne'⟩
  have pos1 (p : ℕ) (hp : p ∈ n.primeFactors) : 0 ≤ 1-(p:ℝ)⁻¹ := by
    have g : (1:ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_le
    exact sub_nonneg.mpr (inv_le_one_of_one_le₀ g)
  have H := prod_le_prod_of_subset_of_le_one₀ sub pos1
    (fun p _ _ => sub_le_self 1 (by positivity))
  have G := prod_le_prod_of_subset_of_le_one₀ (Finset.filter_subset_filter (fun p => ¬p ∣ n) hP)
    (fun p h => nn p (mem_filter.mp h).1) (fun p _ _ => sub_le_self 1 (by positivity))
  have eq (p : ℕ) : ((if p ∣ n then 1/(p:ℝ) else 0)+(1-2/(p:ℝ))) =
      (if p ∣ n then 1-(p:ℝ)⁻¹ else 1-2/(p:ℝ)) := by split_ifs <;> ring
  simp_rw [eq]
  rw [prod_ite,ht,mul_div_cancel_left₀ _ (by exact_mod_cast hn.ne' : (n:ℝ) ≠ 0)]
  exact mul_le_mul H G (prod_nonneg (fun p h => nn p (mem_filter.mp h).1))
    (prod_nonneg (fun p h => pos1 p (sub h)))


private noncomputable def localFactor (p n : ℕ) : ℝ :=
  (if p ∣ n then 1/(p:ℝ) else 0)+(1-2/(p:ℝ))

private noncomputable def terminalVolume (n : ℕ) : ℝ :=
  ((Icc ((n+2)/3) (2*n/3)).card:ℝ)*n.totient/n *
    ∏ p ∈ ((Icc 2 n.sqrt).filter Nat.Prime).filter (fun p => ¬p ∣ n), (1-2/(p:ℝ))

theorem even_volume_sum (X : ℕ) (hX : 2 ≤ X) (P : Finset ℕ)
    (hp : ∀ p ∈ P, p.Prime ∧ 2 < p ∧ p ≤ (2*X).sqrt) :
    (∑ m ∈ Icc X (2*X), terminalVolume (2*m)) ≤
      ((4*(X:ℝ)/3+1)/2) *
        (X*(∏ p ∈ P, (1-1/(p:ℝ))^2) + ∏ p ∈ P, (1-1/(p:ℝ))) := by
  classical
  let K := (4*(X:ℝ)/3+1)/2
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have each (m : ℕ) (hm : m ∈ Icc X (2*X)) :
      terminalVolume (2*m) ≤ K * ∏ p ∈ P, localFactor p m := by
    obtain ⟨hm1,hm2⟩ := mem_Icc.mp hm
    have hn : 0 < 2*m := by omega
    have hs : insert 2 P ⊆ (Icc 2 (2*m).sqrt).filter Nat.Prime := by
      intro p h
      rcases mem_insert.mp h with h|h
      · subst p
        exact mem_filter.mpr ⟨mem_Icc.mpr ⟨le_rfl,Nat.le_sqrt.mpr (by omega)⟩,Nat.prime_two⟩
      · obtain ⟨pr,gt,up⟩ := hp p h
        exact mem_filter.mpr ⟨mem_Icc.mpr ⟨gt.le,up.trans (Nat.sqrt_le_sqrt (by omega))⟩,pr⟩
    have ht := terminal_multiplier_le (2*m) hn (insert 2 P) hs
    change _ ≤ ∏ p ∈ insert 2 P, localFactor p (2*m) at ht
    rw [prod_insert (by intro h; have := (hp 2 h).2.1; omega)] at ht
    have factor : localFactor 2 (2*m) = 1/2 := by simp [localFactor]
    have oddfactor (p : ℕ) (h : p ∈ P) : localFactor p (2*m) = localFactor p m := by
      obtain ⟨pr,gt,_⟩ := hp p h
      have nd : ¬p ∣ 2 := by intro hd; have := Nat.le_of_dvd (by decide : 0<2) hd; omega
      simp [localFactor,pr.dvd_mul,nd]
    rw [factor,prod_congr rfl oddfactor] at ht
    have width : ((Icc ((2*m+2)/3) (2*(2*m)/3)).card:ℝ) ≤ 4*(X:ℝ)/3+1 := by
      have H : 3*(Icc ((2*m+2)/3) (2*(2*m)/3)).card ≤ 4*X+3 := by rw [Nat.card_Icc]; omega
      have H' : 3*((Icc ((2*m+2)/3) (2*(2*m)/3)).card:ℝ) ≤ 4*X+3 := by exact_mod_cast H
      linarith
    have pos : 0 ≤ ∏ p ∈ P, localFactor p m := by
      apply prod_nonneg
      intro p h
      have hh : (2:ℝ) ≤ p := by exact_mod_cast (hp p h).1.two_le
      have nn : 0 ≤ 1-2/(p:ℝ) := sub_nonneg.mpr ((div_le_one (by linarith)).mpr hh)
      unfold localFactor; split_ifs <;> positivity
    unfold terminalVolume
    calc
      _ = ((Icc ((2*m+2)/3) (2*(2*m)/3)).card:ℝ) * _ := by ring
      _ ≤ _ := (mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg _)).trans
        ((mul_le_mul_of_nonneg_right width (mul_nonneg (by norm_num) pos)).trans_eq (by dsimp [K]; ring))
  exact (sum_le_sum each).trans (by rw [←mul_sum]; exact mul_le_mul_of_nonneg_left (interval_sieve_mean X P (fun p h => (hp p h).1)) hK)


theorem farey_pointwise_sum (X : ℕ)
    (h : ∀ n ≥ 2*X, Even n →
      (((acceptedSide n).filter (fun u => n-u ∈ acceptedSide n)).card:ℝ) ≤
        (2/25:ℝ)*terminalVolume n) :
    ((commonSemiprimes X).card:ℝ)^2 ≤ (2/25:ℝ)*
      ∑ m ∈ Icc X (2*X), terminalVolume (2*m) := by
  classical
  have he : (Icc (2*X) (4*X)).filter Even = (Icc X (2*X)).image (2*·) := by
    ext n
    simp only [mem_filter,mem_Icc,mem_image,even_iff_two_dvd]
    constructor
    · rintro ⟨⟨hl,hu⟩,k,hk⟩
      exact ⟨k,by omega,by omega⟩
    · rintro ⟨k,hk,rfl⟩
      exact ⟨by omega,⟨k,rfl⟩⟩
  have lower := farey_bilateral_common_set X
  rw [he, sum_image (by intro a ha b hb eq; change 2*a=2*b at eq; omega)] at lower
  push_cast
  rw [Finset.mul_sum]
  apply le_trans _ (Finset.sum_le_sum (fun m hm => h (2*m) (by have := (mem_Icc.mp hm).1; omega) ⟨m,by omega⟩))
  exact_mod_cast lower

theorem farey_constant_contradiction (x L A s : ℝ) (hx : 10000 ≤ x)
    (hL : 0 ≤ L) (hA : 0 ≤ A) (ha : A ≤ 1) (hs : 0 ≤ s)
    (herr : 10000*L^2 ≤ x) (hprod : A*L ≤ 8/3)
    (hlo : (98/100)*(63/100)*x ≤ s*L)
    (hhi : s^2 ≤ (2/25)*((4*x/3+1)/2)*(x*A^2+A)) : False := by
  have xNN : 0 ≤ x := by linarith
  have H := mul_self_le_mul_self (by positivity : 0 ≤ (98/100:ℝ)*(63/100)*x) hlo
  have J := mul_self_le_mul_self (mul_nonneg hA hL) hprod
  have e : (x*A^2+A)*L^2 ≤ x*((8/3:ℝ)^2+1/10000) := by
    nlinarith only [mul_le_mul_of_nonneg_left J xNN,
      mul_le_mul_of_nonneg_right ha (sq_nonneg L), herr]
  have k : (4*x/3+1)/2 ≤ x*(2/3+1/10000) := by linarith
  have u := mul_le_mul_of_nonneg_right hhi (sq_nonneg L)
  have v := mul_le_mul_of_nonneg_left e (by positivity : 0 ≤ (2/25:ℝ)*((4*x/3+1)/2))
  have w := mul_le_mul_of_nonneg_right k (by positivity : 0 ≤ (2/25:ℝ)*(x*((8/3:ℝ)^2+1/10000)))
  nlinarith only [H,u,v,w,sq_pos_of_pos (by linarith : 0 < x)]

theorem farey_odd_product (t : ℕ) (ht : 2 ≤ t)
    (h : 90*Real.log t * ((t^60+1).primesBelow).prod (fun p : ℕ => 1-(p:ℝ)⁻¹) ≤ 1) :
    (((t^60+1).primesBelow.erase 2).prod (fun p : ℕ => 1-1/(p:ℝ))) *
      (120*Real.log t) ≤ 8/3 := by
  have ht' : t ≤ t^60 := Nat.le_self_pow (by decide) t
  have htwo : 2 ∈ (t^60+1).primesBelow :=
    Nat.mem_primesBelow.mpr ⟨by omega, Nat.prime_two⟩
  have e := Finset.mul_prod_erase (t^60+1).primesBelow (fun p : ℕ => 1-(p:ℝ)⁻¹) htwo
  rw [←e] at h
  norm_num at h
  simp only [one_div]
  linarith only [h]

theorem Conjectures.Cuts.Refute381823bab84c203ff962aeb2 : ¬ (have x1 : ℕ → Finset ℕ := fun (x1 : ℕ) => Finset.Icc ((x1 + (2 : ℕ)) / (3 : ℕ)) ((2 : ℕ) * x1 / (3 : ℕ)); have x2 : ℕ → Finset ℕ := fun (x2 : ℕ) => Finset.filter Nat.Prime (Finset.Icc (2 : ℕ) x2); have x3 : ℕ → Finset ℕ := fun (x3 : ℕ) => {x4 ∈ x1 x3 | ⌊(↑x3 : ℝ) ^ (1 / 3 : ℝ)⌋₊ < x4.minFac ∧ Nat.Prime x4.minFac ∧ Nat.Prime (x4 / x4.minFac)}; have x4 : ℕ → ℝ := fun (x4 : ℕ) => (↑(x1 x4).card : ℝ) * (↑x4.totient : ℝ) / (↑x4 : ℝ) * ∏ x5 ∈ x2 x4.sqrt with ¬x5 ∣ x4, ((1 : ℝ) - (2 : ℝ) / (↑x5 : ℝ)); have x5 : ℕ → Finset ℕ := fun (x5 : ℕ) => {x6 ∈ x3 x5 | x5 - x6 ∈ x3 x5}; have x6 : ℕ → ℕ := fun (x6 : ℕ) => ⌊(↑x6 : ℝ) ^ (2 / 5 : ℝ)⌋₊; ∃ (x7 : ℕ), ∀ (x8 : ℕ), x7 ≤ x8 → Even x8 → (↑(x5 x8).card : ℝ) ≤ (2 / 25 : ℝ) * x4 x8) := by

  classical
  rintro ⟨N,hN⟩
  have ev := eventual_smooth_product.and actual_semiprime_lower
  obtain ⟨t,ht,h⟩ := (ev.and (eventually_ge_atTop (max N 144000000))).exists
  have htN : N ≤ t := (le_max_left ..).trans h
  have htbig : 144000000 ≤ t := (le_max_right ..).trans h
  let X := t^120
  have htX : t ≤ X := Nat.le_self_pow (by decide) t
  let P := (t^60+1).primesBelow.erase 2
  let A := P.prod (fun p : ℕ => 1-1/(p:ℝ))
  have pm (p : ℕ) (hp : p ∈ P) : p.Prime ∧ 2 < p ∧ p ≤ (2*X).sqrt := by
    obtain ⟨hne,hp'⟩ := Finset.mem_erase.mp hp
    obtain ⟨hpt,hprime⟩ := Nat.mem_primesBelow.mp hp'
    refine ⟨hprime,by have := hprime.two_le; omega,Nat.le_sqrt.mpr ?_⟩
    have e : t^60*t^60 = X := by dsimp [X]; ring
    have := Nat.mul_self_le_mul_self (show p ≤ t^60 by omega)
    omega
  have nn (p : ℕ) (hp : p ∈ P) : 0 ≤ 1-1/(p:ℝ) := by
    have o : (1:ℝ) ≤ p := by exact_mod_cast (pm p hp).1.one_le
    simpa [one_div] using sub_nonneg.mpr (inv_le_one_of_one_le₀ o)
  have vol := even_volume_sum X (by omega) P pm
  rw [Finset.prod_pow] at vol
  have summed := farey_pointwise_sum X (by
    intro n hn he
    have orig := hN n (by omega) he
    convert orig using 1 <;> simp only [acceptedSide,cubeCut,semi,terminalVolume] <;> congr! 4 <;> ext u <;> simp)
  have hi := summed.trans (mul_le_mul_of_nonneg_left vol (by norm_num))
  have ap := farey_odd_product t (by omega) ht.1
  have rt : (144000000:ℝ) ≤ t := by exact_mod_cast htbig
  have rone : (1:ℝ) ≤ t := by linarith
  have logs := Real.log_le_sub_one_of_pos (by linarith : (0:ℝ) < t)
  have lnn := Real.log_nonneg rone
  have l2 := mul_self_le_mul_self lnn (by linarith : Real.log t ≤ t)
  have pw : (t:ℝ)^3 ≤ (t:ℝ)^120 := pow_le_pow_right₀ rone (by decide)
  have err : 10000*(120*Real.log t)^2 ≤ (X:ℝ) := by
    dsimp [X]; push_cast
    nlinarith only [pw,l2,mul_le_mul_of_nonneg_right rt (sq_nonneg (t:ℝ))]
  apply farey_constant_contradiction (X:ℝ) (120*Real.log t) A ((commonSemiprimes X).card:ℝ)
  · exact_mod_cast (show 10000 ≤ X by omega)
  · positivity
  · exact Finset.prod_nonneg nn
  · exact Finset.prod_le_one₀ nn (fun p hp => by exact sub_le_self _ (by positivity))
  · positivity
  · exact err
  · exact ap
  · simpa [X] using ht.2
  · simpa only [A, mul_assoc] using hi

