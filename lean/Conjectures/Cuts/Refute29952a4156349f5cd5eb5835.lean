import Mathlib
import Conjectures.Goldbach.FareyCubeSqrtDensityRatio
import Conjectures.Cuts.Refute381823bab84c203ff962aeb2

-- Prime-band asymptotics use FareyCubeSqrtDensityRatio. The sharp product
-- estimate uses the Mertens development and volume limit verified in PR 4560.
namespace FareySharpPairing
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

private def bandStart (j : ℕ) := 2000001+2499*j

private def bandCertificate (j : ℕ) : ℕ :=
  (1000000000*6000000*2499)/((bandStart j+2499)*(6000000-bandStart j))

private def certificateTotal : ℕ → ℕ
  | 0 => 0
  | n+1 => certificateTotal n + bandCertificate n

private theorem sum_certificate (n : ℕ) :
    ∑ j ∈ range n, bandCertificate j = certificateTotal n := by
  induction n with
  | zero => simp [certificateTotal]
  | succ n ih => rw [sum_range_succ,ih,certificateTotal]

set_option maxRecDepth 8192 in
private theorem certificate_floor : 692270000 ≤ certificateTotal 400 := by decide +kernel

theorem sharp_semiprime_band_constant :
    (69227/100000:ℝ) ≤ ∑ j ∈ range 400,
      (6000000 / (6000000-(bandStart j:ℝ))) *
        Real.log (((bandStart j:ℝ)+2499)/bandStart j) := by
  have term (j : ℕ) (hj : j ∈ range 400) :
      (bandCertificate j:ℝ)/1000000000 ≤
        (6000000 / (6000000-(bandStart j:ℝ))) *
          Real.log (((bandStart j:ℝ)+2499)/bandStart j) := by
    have jlt := mem_range.mp hj
    have h₁ : 0 < bandStart j := by unfold bandStart; omega
    have h₂ : bandStart j < 6000000 := by unfold bandStart; omega
    have a : 0 < (bandStart j:ℝ) := by exact_mod_cast h₁
    have b : (bandStart j:ℝ) < 6000000 := by exact_mod_cast h₂
    have raw := Nat.div_mul_le_self (1000000000*6000000*2499) ((bandStart j+2499)*(6000000-bandStart j))
    change bandCertificate j * _ ≤ _ at raw
    have castRaw := (show ((bandCertificate j * ((bandStart j+2499)*(6000000-bandStart j)):ℕ):ℝ) ≤ ((1000000000*6000000*2499:ℕ):ℝ) by exact_mod_cast raw)
    push_cast [Nat.cast_sub h₂.le] at castRaw
    have hl := Real.log_le_sub_one_of_pos (show 0 < (bandStart j:ℝ)/((bandStart j:ℝ)+2499) by positivity)
    rw [Real.log_div a.ne' (by positivity)] at hl
    rw [Real.log_div (by positivity) a.ne']
    have step : 2499/((bandStart j:ℝ)+2499) ≤ Real.log ((bandStart j:ℝ)+2499)-Real.log (bandStart j) := by
      have eq : 2499/((bandStart j:ℝ)+2499) = 1-(bandStart j:ℝ)/((bandStart j:ℝ)+2499) := by field_simp; ring
      linarith
    apply le_trans _ (mul_le_mul_of_nonneg_left step (by positivity))
    field_simp
    nlinarith only [castRaw]
  have s := Finset.sum_le_sum term
  rw [←Finset.sum_div,←Nat.cast_sum,sum_certificate] at s
  have h : (692270000:ℝ) ≤ certificateTotal 400 := by exact_mod_cast certificate_floor
  linarith


set_option maxRecDepth 8192 in
theorem farey_sharp_band_mass_eventual :
    ∀ᶠ t : ℕ in atTop, (69226/100000:ℝ) ≤
      ∑ j ∈ range 400, 6000000/(6000000-(bandStart j:ℝ)) *
        bandMass t (bandStart j) (bandStart j+2499) := by
  let W := fun j : ℕ => (6000000:ℝ)/(6000000-(bandStart j:ℝ))
  have h := tendsto_finsetSum (range 400) (fun j _ =>
    (bandMass_limit (bandStart j) (bandStart j+2499) (by unfold bandStart; omega) (by omega)).const_mul (W j))
  have margins : (69226/100000:ℝ) < ∑ j ∈ range 400, W j * Real.log (((bandStart j+2499:ℕ):ℝ)/bandStart j) := by
    exact lt_of_lt_of_le (by norm_num : (69226/100000:ℝ) < 69227/100000)
      (by simpa only [W,Nat.cast_add,Nat.cast_ofNat] using sharp_semiprime_band_constant)
  exact (h.eventually_const_lt margins).mono (fun _ hx => hx.le)


open Filter Topology Finset

theorem farey_prime_interval_lower (a b η : ℝ) (ha : 0 < a) (hab : a < b)
    (hη : η < 1) :
    ∀ᶠ x : ℝ in atTop, η*(b-a)*x ≤
      (((⌊b*x⌋₊).primesLE \ (⌊a*x⌋₊).primesLE).card:ℝ) * Real.log (b*x) := by
  have hl (k : ℝ) (hk : 0 < k) :
      Tendsto (fun x : ℝ => Chebyshev.theta (k*x)/x) atTop (𝓝 k) := by
    have lim := Chebyshev.tendsto_theta_div_atTop.comp (tendsto_id.const_mul_atTop hk)
    have sc := lim.mul_const k
    simp only [one_mul] at sc
    refine sc.congr' ?_
    filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
    change Chebyshev.theta (k*x)/(k*x)*k = _
    field_simp
  have hd := (hl b (ha.trans hab)).sub (hl a ha)
  have small : η*(b-a) < b-a := by nlinarith [mul_pos (sub_pos.mpr hη) (sub_pos.mpr hab)]
  filter_upwards [hd.eventually_lt_const (show b-a < b-a+1 by linarith),
    hd.eventually_const_lt small,eventually_gt_atTop (0:ℝ)] with x _ h hx
  change η*(b-a) < Chebyshev.theta (b*x)/x-Chebyshev.theta (a*x)/x at h
  rw [←sub_div] at h
  refine ((lt_div_iff₀ hx).mp h).le.trans ?_
  have hb := ha.trans hab
  have sub := Nat.primesLE_mono (Nat.floor_mono (mul_le_mul_of_nonneg_right hab.le hx.le))
  rw [Chebyshev.theta_eq_sum_primesLE,Chebyshev.theta_eq_sum_primesLE,←sum_sdiff_eq_sub sub]
  calc
    _ ≤ ∑ p ∈ (⌊b*x⌋₊).primesLE \ (⌊a*x⌋₊).primesLE, Real.log (b*x) := by
      apply sum_le_sum
      intro p hp
      obtain ⟨hle,hprime⟩ := Nat.mem_primesLE.mp (mem_sdiff.mp hp).1
      exact Real.log_le_log (by exact_mod_cast hprime.pos)
        ((by exact_mod_cast hle : (p:ℝ) ≤ (⌊b*x⌋₊:ℕ)).trans (Nat.floor_le (by positivity)))
    _ = _ := by simp


theorem farey_interval_uniform (a b : ℝ) (ha : 0<a) (hab : a<b)
    (K : ℕ) (hK : 1 ≤ K) (η : ℝ) (hη : η<1) :
    ∀ᶠ t : ℕ in atTop, ∀ p : ℕ, 0 < p → p ≤ t^(K-1) →
    let x := (t:ℝ)^K / p
    η*(b-a)*x ≤ (((⌊b*x⌋₊).primesLE \ (⌊a*x⌋₊).primesLE).card:ℝ) *
      Real.log (b*x) := by
  obtain ⟨T,hT⟩ := eventually_atTop.mp (farey_prime_interval_lower a b η ha hab hη)
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop T,
    eventually_ge_atTop (1:ℕ)] with t ht ht₁
  intro p hp hpt
  apply hT
  apply le_trans ht
  apply (le_div_iff₀ (by exact_mod_cast hp : (0:ℝ)<p)).mpr
  have hle : (p:ℝ) ≤ (t:ℝ)^(K-1) := by exact_mod_cast hpt
  have e : K=K-1+1 := by omega
  calc
    (t:ℝ)*p ≤ t*(t:ℝ)^(K-1) := mul_le_mul_of_nonneg_left hle (by positivity)
    _ = (t:ℝ)^K := by conv_rhs => rw [e, pow_succ, mul_comm]


private noncomputable def fareyPartners (a b x : ℝ) : Finset ℕ :=
  (⌊b*x⌋₊).primesLE \ (⌊a*x⌋₊).primesLE

set_option maxRecDepth 8192 in
theorem farey_weighted_partners (K : ℕ) (hK : 1≤K) (a b : ℝ) (ha : 0<a) (hab : a<b) :
    ∀ᶠ t : ℕ in atTop, ∀ s p : ℕ, s + 100000 ≤ K → t^s ≤ p → p ≤ t^(K-1) →
    (99995/100000:ℝ)*(b-a)*((t:ℝ)^K/p) ≤
      ((fareyPartners a b ((t:ℝ)^K/p)).card:ℝ) *
        (((K:ℝ)-(s:ℝ))*Real.log t) := by
  have z := farey_interval_uniform a b ha hab K hK (99999/100000) (by norm_num)
  filter_upwards [z, eventually_ge_atTop (2:ℕ),
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop b] with t ht h₂ hbt
  intro s p hs hlo hhi
  have hpos : 0<t := by omega
  have pp : 0<p := (pow_pos hpos _).trans_le hlo
  have pr : (0:ℝ)<p := by exact_mod_cast pp
  have tr : (0:ℝ)<t := by exact_mod_cast hpos
  have tl := Real.log_nonneg (show (1:ℝ) ≤ t by exact_mod_cast (show 1≤t by omega))
  have sr : (s:ℝ)+100000 ≤ K := by exact_mod_cast hs
  have lp := Real.log_le_log (pow_pos tr s) (show (t:ℝ)^s ≤ p by exact_mod_cast hlo)
  rw [Real.log_pow] at lp
  have hb := ha.trans hab
  have lb := Real.log_le_log hb hbt
  let x := (t:ℝ)^K/p
  have xp : 0<x := by dsimp [x]; positivity
  have raw := ht p pp hhi
  change (99999/100000:ℝ)*(b-a)*x ≤ ((fareyPartners a b x).card:ℝ)*Real.log (b*x) at raw
  have lelog : Real.log (b*x) ≤ (100001/100000)*(((K:ℝ)-(s:ℝ))*Real.log t) := by
    rw [Real.log_mul hb.ne' xp.ne']
    dsimp [x]
    rw [Real.log_div (pow_pos tr _).ne' pr.ne',Real.log_pow]
    push_cast
    nlinarith only [lp,lb,mul_nonneg (sub_nonneg.mpr sr) tl,tl]
  have bound := raw.trans (mul_le_mul_of_nonneg_left lelog (Nat.cast_nonneg _))
  change (99995/100000:ℝ)*(b-a)*x ≤ _
  nlinarith only [bound,mul_nonneg (sub_nonneg.mpr hab.le) xp.le]


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



private noncomputable def intervalSemis (a b X z : ℕ) :=
  (Ioc (a*X) (b*X)).filter fun u =>
    Odd u ∧ z < u.minFac ∧ u.minFac.Prime ∧ (u/u.minFac).Prime

private theorem interval_pair_membership {a b X z p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hz : 2 ≤ z) (hzp : z<p)
    (hbot : a*X < p*q) (htop : p*q ≤ b*X) (hsq : p*p ≤ a*X) :
    (p*q).minFac=p ∧ p*q ∈ intervalSemis a b X z := by
  have pq : p ≤ q := by by_contra! h; have := Nat.mul_le_mul_left p h.le; omega
  have hmin := least_of_pair hp hq pq
  refine ⟨hmin,mem_filter.mpr ⟨mem_Ioc.mpr ⟨hbot,htop⟩,?_,?_⟩⟩
  · exact (hp.odd_of_ne_two (by omega)).mul (hq.odd_of_ne_two (by omega))
  · rw [hmin,Nat.mul_div_cancel_left _ hp.pos]
    exact ⟨hzp,hp,hq⟩

theorem farey_summed_partner_count (P : Finset ℕ) (Q : ℕ → Finset ℕ) (a b X z : ℕ)
    (hz : 2≤z)
    (hp : ∀ p ∈ P, p.Prime ∧ z<p ∧ p*p≤a*X)
    (hq : ∀ p ∈ P, ∀ q ∈ Q p, q.Prime ∧ a*X<p*q ∧ p*q≤b*X) :
    ∑ p ∈ P, (Q p).card ≤ (intervalSemis a b X z).card := by
  classical
  have fact {p q} (h : p ∈ P) (k : q ∈ Q p) := interval_pair_membership
    (hp _ h).1 (hq _ h _ k).1 hz (hp _ h).2.1 (hq _ h _ k).2.1 (hq _ h _ k).2.2 (hp _ h).2.2
  rw [←card_sigma]
  apply card_le_card_of_injOn (fun x : Sigma (fun _ : ℕ => ℕ) => x.1*x.2)
  · rintro ⟨p,q⟩ h
    obtain ⟨i,j⟩ := mem_sigma.mp h
    exact (fact i j).2
  · rintro ⟨p,q⟩ h ⟨u,v⟩ k eq
    obtain ⟨i,j⟩ := mem_sigma.mp h
    obtain ⟨m,n⟩ := mem_sigma.mp k
    change p*q=u*v at eq
    have same : p=u := (fact i j).1.symm.trans ((congrArg Nat.minFac eq).trans (fact m n).1)
    subst u
    obtain rfl := Nat.eq_of_mul_eq_mul_left (hp _ i).1.pos eq
    rfl


private theorem sharp_partner_range (a b X p q : ℕ) (hp : 0 < p)
    (hq : q ∈ fareyPartners a b ((X:ℝ)/p)) :
    q.Prime ∧ a*X < p*q ∧ p*q ≤ b*X := by
  obtain ⟨upper,lower⟩ := mem_sdiff.mp hq
  obtain ⟨hu,pr⟩ := Nat.mem_primesLE.mp upper
  have lo : ⌊(a:ℝ)*(X/p : ℝ)⌋₊ < q := lt_of_not_ge (fun h => lower (Nat.mem_primesLE.mpr ⟨h,pr⟩))
  have l := (Nat.floor_lt (by positivity)).mp lo
  have u := (Nat.le_floor_iff (by positivity)).mp hu
  have pp : (0:ℝ)<p := by exact_mod_cast hp
  rw [←mul_div_assoc] at l u
  have ll := (div_lt_iff₀ pp).mp l
  have uu := (le_div_iff₀ pp).mp u
  exact ⟨pr,by exact_mod_cast (by linarith only [ll] : (a:ℝ)*X < p*q),
    by exact_mod_cast (by linarith only [uu] : (p:ℝ)*q ≤ b*X)⟩

private theorem sharp_reweight {c x p d L k m : ℝ} (hp : 0<p) (hd : 0<d) (hk : 0≤k)
    (h : c*(x/p) ≤ m*(d*L)) : c*x*(k/d)*p⁻¹ ≤ m*(k*L) := by
  have h1 := mul_le_mul_of_nonneg_right h (div_nonneg hk hd.le)
  convert h1 using 1 <;> field_simp <;> ring

set_option maxRecDepth 8192 in
theorem sharp_interval_semiprime_lower (a b : ℕ) (ha : 1≤a) (hab : a<b) :
    ∀ᶠ t : ℕ in atTop, (99995/100000:ℝ)*((b:ℝ)-a)*(t:ℝ)^6000000*(69226/100000) ≤
      ((intervalSemis a b (t^6000000) (t^2000001)).card:ℝ)*(6000000*Real.log t) := by
  classical
  have ar : (0:ℝ)<a := by exact_mod_cast (show 0<a by omega)
  have abr : (a:ℝ)<b := by exact_mod_cast hab
  filter_upwards [farey_sharp_band_mass_eventual,
    farey_weighted_partners 6000000 (by decide) a b ar abr,eventually_ge_atTop (2:ℕ)]
    with t hb ht ht₂
  let J := range 400
  let B := fun j => primesUpTo (t^(bandStart j+2499)) \ primesUpTo (t^(bandStart j))
  let X := t^6000000
  let Q := fun p : ℕ => fareyPartners a b ((t:ℝ)^6000000/p)
  have memB {j p : ℕ} (h : p∈B j) : p.Prime ∧ t^(bandStart j)<p ∧ p≤t^(bandStart j+2499) := by
    obtain ⟨u,l⟩ := mem_sdiff.mp h
    obtain ⟨pr,le⟩ := mem_primesUpTo.mp u
    exact ⟨pr,lt_of_not_ge (fun hh => l (mem_primesUpTo.mpr ⟨pr,hh⟩)),le⟩
  have order {i k : ℕ} (h : i≤k) := Nat.pow_le_pow_right (by omega : 0<t) h
  have sep {i j : ℕ} (h : i<j) : Disjoint (B i) (B j) := by
    apply disjoint_left.mpr
    intro p hi hj
    exact (not_lt_of_ge ((memB hi).2.2.trans (order (show bandStart i+2499 ≤ bandStart j by unfold bandStart; omega)))) (memB hj).2.1
  have disj : (J : Set ℕ).PairwiseDisjoint B := by
    intro i _ j _ h
    rcases lt_or_gt_of_ne h with h|h
    · exact sep h
    · exact (sep h).symm
  have htop {j p : ℕ} (hj : j∈J) (hm : p∈B j) : p≤t^3000000 := by
    have hj' := mem_range.mp hj
    exact (memB hm).2.2.trans (order (by unfold bandStart; omega))
  have total := farey_summed_partner_count (J.biUnion B) Q a b X (t^2000001)
    (ht₂.trans (Nat.le_self_pow (by decide) _)) (by
      intro p hp
      obtain ⟨j,hj,hm⟩ := mem_biUnion.mp hp
      have hi := htop hj hm
      have sq := Nat.mul_le_mul hi hi
      have eq : t^3000000*t^3000000=X := (pow_add t 3000000 3000000).symm
      exact ⟨(memB hm).1,(order (by unfold bandStart; omega)).trans_lt (memB hm).2.1,
        (sq.trans_eq eq).trans (by simpa using Nat.mul_le_mul_right X ha)⟩) (by
      intro p hp q hq
      obtain ⟨j,_,hm⟩ := mem_biUnion.mp hp
      exact sharp_partner_range a b X p q (memB hm).1.pos (by simpa only [X,Nat.cast_pow] using hq))
  rw [sum_biUnion disj] at total
  have totalR : (∑ j ∈ J, ∑ p ∈ B j, ((Q p).card:ℝ)) ≤ ((intervalSemis a b X (t^2000001)).card:ℝ) := by exact_mod_cast total
  let C : ℝ := (99995/100000)*((b:ℝ)-a)*(t:ℝ)^6000000
  have byband (j : ℕ) (hj : j∈J) :
      C*(6000000/(6000000-(bandStart j:ℝ))*bandMass t (bandStart j) (bandStart j+2499)) ≤
        (∑ p ∈ B j, ((Q p).card:ℝ))*(6000000*Real.log t) := by
    have jl := mem_range.mp hj
    have js : bandStart j+100000 ≤ 6000000 := by unfold bandStart; omega
    have den : 0 < 6000000-(bandStart j:ℝ) := by
      have : bandStart j < 6000000 := by omega
      exact sub_pos.mpr (by exact_mod_cast this)
    unfold bandMass
    rw [←mul_assoc,mul_sum,sum_mul]
    apply sum_le_sum
    intro p hp
    have h := ht (bandStart j) p js (memB hp).2.1.le ((htop hj hp).trans (order (by omega)))
    have pp : (0:ℝ)<p := by exact_mod_cast (memB hp).1.pos
    change _ ≤ ((Q p).card:ℝ)*_ at h
    exact sharp_reweight pp den (by norm_num) h
  have sumB := sum_le_sum byband
  rw [←mul_sum,←sum_mul] at sumB
  have cNN : 0≤C := by dsimp only [C]; positivity
  have L : 0≤6000000*Real.log (t:ℝ) := by positivity
  exact (mul_le_mul_of_nonneg_left hb cNN).trans (sumB.trans (mul_le_mul_of_nonneg_right totalR L))


open Finset

theorem farey_rectangle_count {ι : Type*} [DecidableEq ι]
    (J : Finset ι) (U V : ι → Finset ℕ) (T : Finset ℕ) (A : ℕ → Finset ℕ)
    (hsep : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → Disjoint (U i) (U j))
    (hpair : ∀ i ∈ J, ∀ u ∈ U i, ∀ v ∈ V i,
      u+v ∈ T ∧ u ∈ A (u+v) ∧ v ∈ A (u+v)) :
    ∑ i ∈ J, (U i).card*(V i).card ≤
      ∑ n ∈ T, ((A n).filter (fun u => n-u ∈ A n)).card := by
  classical
  let R := fun i => (U i).product (V i)
  have disj : Set.PairwiseDisjoint (↑J) R := by
    intro i hi j hj hij
    apply Finset.disjoint_left.mpr
    intro w hw hw'
    exact Finset.disjoint_left.mp (hsep i hi j hj hij) (mem_product.mp hw).1 (mem_product.mp hw').1
  have point (w : ℕ × ℕ) (hw : w ∈ J.biUnion R) :
      w.1+w.2 ∈ T ∧ w.1 ∈ A (w.1+w.2) ∧ w.2 ∈ A (w.1+w.2) := by
    obtain ⟨i,hi,hw⟩ := mem_biUnion.mp hw
    exact hpair i hi _ (mem_product.mp hw).1 _ (mem_product.mp hw).2
  have lands : ((J.biUnion R : Finset _) : Set (ℕ × ℕ)).MapsTo (fun w => w.1+w.2) T :=
    fun w hw => (point w hw).1
  calc
    _ = (J.biUnion R).card := by rw [card_biUnion disj]; simp [R]
    _ = _ := card_eq_sum_card_fiberwise lands
    _ ≤ _ := by
      apply sum_le_sum
      intro n _
      apply card_le_card_of_injOn Prod.fst
      · rintro ⟨u,v⟩ hw
        obtain ⟨hw,eq⟩ := mem_filter.mp hw
        obtain ⟨_,hu,hv⟩ := point (u,v) hw
        change u+v=n at eq
        subst n
        exact mem_filter.mpr ⟨hu,by simpa using hv⟩
      · rintro ⟨u,v⟩ hw ⟨a,b⟩ hz eq
        have h := (mem_filter.mp hw).2
        have g := (mem_filter.mp hz).2
        change u+v=n at h
        change a+b=n at g
        change u=a at eq
        exact Prod.ext eq (by dsimp; omega)


theorem farey_strip_geometry (X i u v : ℕ)
    (hi : i ∈ Ico 1001000 2000000)
    (hu : u ∈ Ioc (i*X) ((i+1)*X))
    (hv : v ∈ Ioc ((3000000-i)*X) ((3000999-i)*X)) :
    u+v ∈ Ioc (3000000*X) (3001000*X) ∧
    u ∈ Icc ((u+v+2)/3) (2*(u+v)/3) ∧
    v ∈ Icc ((u+v+2)/3) (2*(u+v)/3) := by
  obtain ⟨il,iu⟩ := mem_Ico.mp hi
  obtain ⟨ul,uu⟩ := mem_Ioc.mp hu
  obtain ⟨vl,vu⟩ := mem_Ioc.mp hv
  rw [Nat.sub_mul] at vl vu
  rw [Nat.add_mul,one_mul] at uu
  have low := Nat.mul_le_mul_right X il
  have high := Nat.mul_le_mul_right X (show i+1≤2000000 by omega)
  rw [Nat.add_mul,one_mul] at high
  simp only [mem_Ioc,mem_Icc]
  omega


private noncomputable def sharpSide (n : ℕ) :=
  (Icc ((n+2)/3) (2*n/3)).filter fun u =>
    ⌊(n:ℝ)^(1/3:ℝ)⌋₊ < u.minFac ∧ u.minFac.Prime ∧ (u/u.minFac).Prime

private theorem sharp_cube_floor {n z : ℕ} (h : n≤z^3) :
    ⌊(n:ℝ)^(1/3:ℝ)⌋₊ ≤ z := by
  have hh := Real.rpow_le_rpow (Nat.cast_nonneg n)
    (show (n:ℝ) ≤ (z:ℝ)^3 by exact_mod_cast h) (by norm_num : (0:ℝ)≤1/3)
  rw [←Real.rpow_natCast_mul (Nat.cast_nonneg z)] at hh
  norm_num at hh
  simpa only [Nat.floor_natCast] using Nat.floor_mono hh

private def stripJ := Ico 1001000 2000000

theorem sharp_strip_count (t : ℕ) (ht : 3001000 ≤ t) :
    let X := t^6000000
    let z := t^2000001
    ∑ i ∈ stripJ, (intervalSemis i (i+1) X z).card *
      (intervalSemis (3000000-i) (3000999-i) X z).card ≤
      ∑ n ∈ (Ioc (3000000*X) (3001000*X)).filter Even,
        ((sharpSide n).filter (fun u => n-u ∈ sharpSide n)).card := by
  classical
  dsimp only
  apply farey_rectangle_count
  · intro i hi j hj ne
    apply disjoint_left.mpr
    intro u ui uj
    obtain ⟨l,r⟩ := mem_Ioc.mp (mem_filter.mp ui).1
    obtain ⟨m,n⟩ := mem_Ioc.mp (mem_filter.mp uj).1
    rcases lt_or_gt_of_ne ne with lt|lt
    · exact (not_lt_of_ge (r.trans (Nat.mul_le_mul_right _ lt))) m
    · exact (not_lt_of_ge (n.trans (Nat.mul_le_mul_right _ lt))) l
  · intro i hi u hu v hv
    obtain ⟨ui,uo,uz,uprime⟩ := mem_filter.mp hu
    obtain ⟨vi,vo,vz,vprime⟩ := mem_filter.mp hv
    obtain ⟨sum,us,vs⟩ := farey_strip_geometry _ _ _ _ hi ui vi
    have cube : u+v ≤ (t^2000001)^3 := by
      have e : (t^2000001)^3 = t^3*t^6000000 := by rw [←pow_mul,←pow_add]
      rw [e]
      exact (mem_Ioc.mp sum).2.trans (Nat.mul_le_mul_right _ (ht.trans (Nat.le_self_pow (by decide) _)))
    have zbound := sharp_cube_floor cube
    exact ⟨mem_filter.mpr ⟨sum,uo.add_odd vo⟩,
      mem_filter.mpr ⟨us,zbound.trans_lt uz,uprime⟩,mem_filter.mpr ⟨vs,zbound.trans_lt vz,vprime⟩⟩


private noncomputable def sharpDensity : ℝ := (99995/100000)*(69226/100000)

private theorem sharp_count_product {c x L U V : ℝ} (hc : 0≤c) (hx : 0≤x) (hU : 0≤U)
    (hL : 0≤L) (u : c*x ≤ U*L) (v : 999*(c*x) ≤ V*L) :
    999*(c*x)^2 ≤ U*V*L^2 := by
  nlinarith only [mul_le_mul u v (by positivity) (mul_nonneg hU hL)]

set_option maxRecDepth 8192 in
theorem sharp_strip_mass :
    ∀ᶠ t : ℕ in atTop, let X := t^6000000
    let L := 6000000*Real.log t
    (999000:ℝ)*999*(sharpDensity*(X:ℝ))^2 ≤
      (∑ n ∈ (Ioc (3000000*X) (3001000*X)).filter Even,
        (((sharpSide n).filter (fun u => n-u ∈ sharpSide n)).card:ℝ))*L^2 := by
  classical
  let U := fun t i => intervalSemis i (i+1) (t^6000000) (t^2000001)
  let V := fun t i => intervalSemis (3000000-i) (3000999-i) (t^6000000) (t^2000001)
  let X := fun t : ℕ => t^6000000
  let L := fun t : ℕ => 6000000*Real.log t
  have each (i : ℕ) (hi : i∈stripJ) : ∀ᶠ t : ℕ in atTop,
      sharpDensity*(X t:ℝ) ≤ ((U t i).card:ℝ)*L t ∧
      999*(sharpDensity*(X t:ℝ)) ≤ ((V t i).card:ℝ)*L t := by
    obtain ⟨il,iu⟩ := mem_Ico.mp hi
    filter_upwards [sharp_interval_semiprime_lower i (i+1) (by omega) (by omega),
      sharp_interval_semiprime_lower (3000000-i) (3000999-i) (by omega) (by omega)]
      with t h k
    have diff : ((3000999-i:ℕ):ℝ)-((3000000-i:ℕ):ℝ)=999 := by
      rw [Nat.cast_sub (by omega),Nat.cast_sub (by omega)]; push_cast; ring
    rw [diff] at k
    push_cast at h
    have eqx : (X t:ℝ)=(t:ℝ)^6000000 := Nat.cast_pow ..
    dsimp only [sharpDensity]
    rw [eqx]
    constructor
    · convert h using 1 <;> ring
    · convert k using 1 <;> ring
  filter_upwards [(eventually_all_finset stripJ).2 each,eventually_ge_atTop (3001000:ℕ)] with t hall ht
  have Lnn : 0≤L t := by dsimp [L]; positivity
  have counted := sharp_strip_count t ht
  have castCount : (∑ i ∈ stripJ, ((U t i).card:ℝ)*((V t i).card:ℝ)) ≤
      ∑ n ∈ (Ioc (3000000*X t) (3001000*X t)).filter Even,
        (((sharpSide n).filter (fun u => n-u ∈ sharpSide n)).card:ℝ) := by exact_mod_cast counted
  have per (i : ℕ) (hi : i∈stripJ) :=

    sharp_count_product (by norm_num [sharpDensity]) (Nat.cast_nonneg (X t))
      (Nat.cast_nonneg (U t i).card) Lnn (hall i hi).1 (hall i hi).2
  have s := Finset.sum_le_sum per
  rw [←sum_mul] at s
  have ncard : stripJ.card=999000 := by rw [stripJ,Nat.card_Ico]
  simp only [sum_const,nsmul_eq_mul,ncard,Nat.cast_ofNat] at s
  dsimp only

  have rhs := mul_le_mul_of_nonneg_right castCount (sq_nonneg (L t))
  rw [sum_mul] at rhs
  exact s.trans rhs


open Finset

theorem multiples_window_bound (lo hi d : ℕ) (hd : 0 < d) :
    (((Icc lo hi).filter (d ∣ ·)).card : ℝ) ≤ ((hi-lo:ℕ):ℝ)/(d:ℝ)+1 := by
  let S := (Icc lo hi).filter (d ∣ ·)
  by_cases h : S.Nonempty
  · let a := S.min' h
    have ha : a ∈ S := min'_mem _ _
    have sa := mem_filter.mp ha
    have bound : S.card ≤ (range ((hi-lo)/d+1)).card := by
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
    have frac : (((hi-lo)/d : ℕ):ℝ) ≤ ((hi-lo:ℕ):ℝ)/(d:ℝ) := (le_div_iff₀ (by exact_mod_cast hd)).mpr
      (by exact_mod_cast Nat.div_mul_le_self (hi-lo) d)
    change (S.card:ℝ) ≤ _
    have cb : (S.card:ℝ) ≤ ((hi-lo)/d:ℕ)+1 := by exact_mod_cast bound
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


theorem interval_sieve_mean (lo hi : ℕ) (P : Finset ℕ) (hp : ∀ p ∈ P, p.Prime) :
    (∑ n ∈ Icc lo hi, ∏ p ∈ P, ((if p ∣ n then 1/(p:ℝ) else 0)+(1-2/(p:ℝ)))) ≤
      ((hi-lo:ℕ):ℝ)*(∏ p ∈ P, (1-1/(p:ℝ))^2) + ∏ p ∈ P, (1-1/(p:ℝ)) := by
  classical
  let I := Icc lo hi
  let g := fun T : Finset ℕ => ((I.filter (fun n => ∀ p ∈ T, p ∣ n)).card:ℝ)
  have hg (T : Finset ℕ) (hT : T ∈ P.powerset) :
      g T ≤ ((hi-lo:ℕ):ℝ)*(∏ p ∈ T, 1/(p:ℝ))+1 := by
    have ht := mem_powerset.mp hT
    let d := ∏ p ∈ T, p
    have hd : 0 < d := prod_pos fun p h => (hp p (ht h)).pos
    have sub : I.filter (fun n => ∀ p ∈ T, p ∣ n) ⊆ I.filter (d ∣ ·) := by
      intro n hn
      obtain ⟨hi,hh⟩ := mem_filter.mp hn
      refine mem_filter.mpr ⟨hi,Finset.prod_dvd_of_isRelPrime ?_ hh⟩
      intro a ha b hb hab
      exact Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes (hp a (ht ha)) (hp b (ht hb))).mpr hab)
    have H := multiples_window_bound lo hi d hd
    have hcast : (d:ℝ) = ∏ p ∈ T, (p:ℝ) := by simp [d]
    apply le_trans (show g T ≤ ((I.filter (d ∣ ·)).card:ℝ) by dsimp only [g]; exact_mod_cast card_le_card sub)
    simpa [hcast,div_eq_mul_inv] using H
  apply le_trans _ (sieve_expansion_bound P (fun p h => (hp p h).two_le) ((hi-lo:ℕ):ℝ) g hg)
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

theorem even_volume_sum_Icc (a b : ℕ) (ha : 2 ≤ a) (hab : a ≤ b) (P : Finset ℕ)
    (hp : ∀ p ∈ P, p.Prime ∧ 2 < p ∧ p ≤ (2*a).sqrt) :
    (∑ m ∈ Icc a b, terminalVolume (2*m)) ≤
      ((2*(b:ℝ)/3+1)/2) *
        (((b:ℝ)-a)*(∏ p ∈ P, (1-1/(p:ℝ))^2) + ∏ p ∈ P, (1-1/(p:ℝ))) := by
  classical
  let K := (2*(b:ℝ)/3+1)/2
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have each (m : ℕ) (hm : m ∈ Icc a b) :
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
    have width : ((Icc ((2*m+2)/3) (2*(2*m)/3)).card:ℝ) ≤ 2*(b:ℝ)/3+1 := by
      have H : 3*(Icc ((2*m+2)/3) (2*(2*m)/3)).card ≤ 2*b+3 := by rw [Nat.card_Icc]; omega
      have H' : 3*((Icc ((2*m+2)/3) (2*(2*m)/3)).card:ℝ) ≤ 2*b+3 := by exact_mod_cast H
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
  exact (sum_le_sum each).trans (by rw [←mul_sum]; apply mul_le_mul_of_nonneg_left _ hK; simpa only [Nat.cast_sub hab, localFactor] using (interval_sieve_mean a b P (fun p h => (hp p h).1)))


open Finset

theorem farey_sum_to_even (X : ℕ) (F V : ℕ → ℝ)
    (hF : ∀ n, 0≤F n) (h : ∀ n ≥ 3000000*X, Even n → F n ≤ (189/500:ℝ)*V n) :
    (∑ n ∈ (Ioc (3000000*X) (3001000*X)).filter Even, F n) ≤
      (189/500:ℝ)* ∑ m ∈ Icc (1500000*X) (1500500*X), V (2*m) := by
  classical
  let B := (Icc (3000000*X) (3001000*X)).filter Even
  have he : B = (Icc (1500000*X) (1500500*X)).image (2*·) := by
    ext n
    simp only [B,mem_filter,mem_Icc,mem_image,even_iff_two_dvd]
    constructor
    · rintro ⟨⟨hl,hu⟩,k,hk⟩
      exact ⟨k,by omega,by omega⟩
    · rintro ⟨k,hk,rfl⟩
      exact ⟨by omega,⟨k,rfl⟩⟩
  have sub : (Ioc (3000000*X) (3001000*X)).filter Even ⊆ B := by
    intro n hn
    obtain ⟨i,e⟩ := mem_filter.mp hn
    obtain ⟨l,u⟩ := mem_Ioc.mp i
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨l.le,u⟩,e⟩
  apply le_trans (sum_le_sum_of_subset_of_nonneg sub (fun n _ _ => hF n))
  rw [he,sum_image (by intro a ha b hb eq; change 2*a=2*b at eq; omega),mul_sum]
  exact sum_le_sum (fun m hm => h _ (by have := (mem_Icc.mp hm).1; omega) ⟨m,by omega⟩)



open Filter Finset
open scoped Topology
namespace FareySharpMertens

def primes (t : ℕ) := ((t ^ 3000000 + 1).primesBelow).erase 2
noncomputable def A (t : ℕ) : ℝ := ∏ p ∈ primes t, (1 - 1 / (p : ℝ))
noncomputable def L (t : ℕ) : ℝ := 6000000 * Real.log (t : ℝ)

private theorem primes_eq (t : ℕ) : RoughRefuteVolume.P (t ^ 6000000) = primes t := by
  have hs : (t ^ 6000000).sqrt = t ^ 3000000 := by
    calc
      _ = ((t ^ 3000000) * (t ^ 3000000)).sqrt := by rw [← pow_add]
      _ = _ := Nat.sqrt_eq _
  ext p
  simp only [RoughRefuteVolume.P, mem_filter, mem_Icc, hs, primes, mem_erase, Nat.mem_primesBelow]
  constructor
  · rintro ⟨⟨hl, hu⟩, hp⟩
    exact ⟨by omega, by omega, hp⟩
  · rintro ⟨hn, hu, hp⟩
    have := hp.two_le
    exact ⟨⟨by omega, by omega⟩, hp⟩

private theorem limit_aux (k : ℕ) (hk : k ≠ 0) :
    Tendsto (fun t : ℕ => ((k : ℝ) * Real.log (t : ℝ)) * RoughRefuteVolume.U (t ^ k)) atTop
      (𝓝 (4 * Real.exp (-Real.eulerMascheroniConstant))) := by
  apply (RoughRefuteVolume.U_limit.comp (tendsto_pow_atTop (α := ℕ) hk)).congr
  intro t
  change RoughRefuteVolume.U (t ^ k) * Real.log ((t ^ k : ℕ) : ℝ) = _
  rw [Nat.cast_pow, Real.log_pow, mul_comm]

private theorem U_eq_A (t : ℕ) : RoughRefuteVolume.U (t ^ 6000000) = A t := by
  rw [RoughRefuteVolume.U, primes_eq]
  rfl

theorem scaled_product_limit : Tendsto (fun t => L t * A t) atTop
    (𝓝 (4 * Real.exp (-Real.eulerMascheroniConstant))) := by
  have h := limit_aux 6000000 (by decide)
  have hc : ((6000000 : ℕ) : ℝ) = (6000000 : ℝ) := by norm_num1
  simp only [hc, U_eq_A] at h
  exact h
theorem scaled_product_eventually_le : ∀ᶠ t in atTop, L t * A t ≤
    4 * Real.exp (-Real.eulerMascheroniConstant) * (100001 / 100000) := by
  have h : 4 * Real.exp (-Real.eulerMascheroniConstant) <
      4 * Real.exp (-Real.eulerMascheroniConstant) * (100001 / 100000) := by
    nlinarith [Real.exp_pos (-Real.eulerMascheroniConstant)]
  exact (scaled_product_limit.eventually (gt_mem_nhds h)).mono (fun _ h => h.le)

end FareySharpMertens


set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem farey_gamma_lower : 5761/10000 < Real.eulerMascheroniConstant := by
  have h := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant 511
  have rat : (68145/10000 : ℚ) < harmonic 511 := by norm_num [harmonic, Finset.sum_range_succ]
  have hr : (68145/10000 : ℝ) < (harmonic 511 : ℝ) := by simpa using (Rat.cast_lt (K := ℝ)).mpr rat
  have hp := Real.log_pow (2:ℝ) 9
  norm_num at hp
  unfold Real.eulerMascheroniSeq at h
  norm_num only [Nat.cast_ofNat, Nat.reduceAdd] at h
  have he : (511:ℝ)+1 = 512 := by norm_num
  linarith [Real.log_two_lt_d9]



theorem sharp_normalized_contradiction (x L A S : ℝ) (hx : 1≤x)
    (hL : 0≤L) (hA : 0≤A) (ha : A≤1) (herr : 10000*L^2≤x)
    (hprod : A*L ≤ (4*100001/100000)/(1779/1000))
    (hlo : 999000*999*((99995/100000*(69226/100000))*x)^2 ≤ S*L^2)
    (hhi : S ≤ 189/500*((3001000*x/3+1)/2)*(500*x*A^2+A)) : False := by
  have xx : 0≤x := by linarith
  have j := mul_self_le_mul_self (mul_nonneg hA hL) hprod
  have inner : (500*x*A^2+A)*L^2 ≤ x*(500*((4*100001/100000)/(1779/1000))^2+1/10000) := by
    nlinarith only [mul_le_mul_of_nonneg_left j xx,mul_le_mul_of_nonneg_right ha (sq_nonneg L),herr]
  have outer : (3001000*x/3+1)/2 ≤ 500168*x := by linarith
  have v := mul_le_mul_of_nonneg_left inner (by positivity : 0 ≤ (189/500:ℝ)*((3001000*x/3+1)/2))
  have w := mul_le_mul_of_nonneg_right outer
    (by positivity : 0 ≤ (189/500:ℝ)*(x*(500*((4*100001/100000)/(1779/1000))^2+1/10000)))
  nlinarith only [hlo,mul_le_mul_of_nonneg_right hhi (sq_nonneg L),v,w,sq_pos_of_pos (by linarith : 0<x)]


end FareySharpPairing
open FareySharpPairing Finset Filter
set_option maxRecDepth 8192 in
theorem Conjectures.Cuts.Refute29952a4156349f5cd5eb5835 : ¬ (have x1 : ℕ → Finset ℕ := fun (x1 : ℕ) => Finset.Icc ((x1 + (2 : ℕ)) / (3 : ℕ)) ((2 : ℕ) * x1 / (3 : ℕ)); have x2 : ℕ → Finset ℕ := fun (x2 : ℕ) => Finset.filter Nat.Prime (Finset.Icc (2 : ℕ) x2); have x3 : ℕ → Finset ℕ := fun (x3 : ℕ) => {x4 ∈ x1 x3 | ⌊(↑x3 : ℝ) ^ (1 / 3 : ℝ)⌋₊ < x4.minFac ∧ Nat.Prime x4.minFac ∧ Nat.Prime (x4 / x4.minFac)}; have x4 : ℕ → ℝ := fun (x4 : ℕ) => (↑(x1 x4).card : ℝ) * (↑x4.totient : ℝ) / (↑x4 : ℝ) * ∏ x5 ∈ x2 x4.sqrt with ¬x5 ∣ x4, ((1 : ℝ) - (2 : ℝ) / (↑x5 : ℝ)); have x5 : ℕ → Finset ℕ := fun (x5 : ℕ) => {x6 ∈ x3 x5 | x5 - x6 ∈ x3 x5}; have x6 : ℕ → ℕ := fun (x6 : ℕ) => ⌊Real.exp (Real.log (↑x6 : ℝ) / (2 : ℝ) - (2 : ℝ) * Real.log (↑x6 : ℝ) ^ (2 / 3 : ℝ))⌋₊; have x7 : ℕ → ℕ := fun (x7 : ℕ) => ⌊(↑x7 : ℝ) ^ (2 / 5 : ℝ)⌋₊; ∃ (x8 : ℕ), ∀ (x9 : ℕ), x8 ≤ x9 → Even x9 → (↑(x5 x9).card : ℝ) ≤ (189 / 500 : ℝ) * x4 x9) := by
  classical
  rintro ⟨N,hN⟩
  obtain ⟨t,⟨lower,mert⟩,ht⟩ :=
    ((sharp_strip_mass.and FareySharpMertens.scaled_product_eventually_le).and
      (eventually_ge_atTop (max N 360000000000000000))).exists
  have htN := (le_max_left N 360000000000000000).trans ht
  have hbig := (le_max_right N 360000000000000000).trans ht
  let X := t^6000000
  let L : ℝ := 6000000*Real.log t
  let A := FareySharpMertens.A t
  let P := FareySharpMertens.primes t
  let F := fun n => (((sharpSide n).filter (fun u => n-u ∈ sharpSide n)).card:ℝ)
  have tx : t≤X := Nat.le_self_pow (by decide) t
  have pm (p : ℕ) (hp : p∈P) : p.Prime ∧ 2<p ∧ p≤(2*(1500000*X)).sqrt := by
    obtain ⟨ne,h⟩ := mem_erase.mp hp
    obtain ⟨lt,pr⟩ := Nat.mem_primesBelow.mp h
    refine ⟨pr,by have := pr.two_le; omega,Nat.le_sqrt.mpr ?_⟩
    have sq := Nat.mul_self_le_mul_self (show p≤t^3000000 by omega)
    have e : t^3000000*t^3000000 = X := (pow_add t 3000000 3000000).symm
    omega
  have nn (p : ℕ) (hp : p∈P) : 0 ≤ 1-1/(p:ℝ) := by
    have o : (1:ℝ) ≤ p := by exact_mod_cast (pm p hp).1.one_le
    simpa [one_div] using sub_nonneg.mpr (inv_le_one_of_one_le₀ o)
  have vol := even_volume_sum_Icc (1500000*X) (1500500*X) (by omega) (by omega) P pm
  rw [Finset.prod_pow] at vol
  have summed := farey_sum_to_even X F terminalVolume (fun n => Nat.cast_nonneg _) (by
    intro n hn he
    have raw := hN n (by omega) he
    convert raw using 1 <;> simp only [F,sharpSide,terminalVolume] <;> congr! 4 <;> ext u <;> simp)
  have hi := summed.trans (mul_le_mul_of_nonneg_left vol (by norm_num))
  have tr : (360000000000000000:ℝ)≤t := by exact_mod_cast hbig
  have lnn := Real.log_nonneg (by linarith : (1:ℝ)≤t)
  have logle := Real.log_le_sub_one_of_pos (by linarith : (0:ℝ)<t)
  have l2 := mul_self_le_mul_self lnn (by linarith : Real.log t ≤ t)
  have pw : (t:ℝ)^3 ≤ (t:ℝ)^6000000 := pow_le_pow_right₀ (by linarith) (by omega)
  have err : 10000*L^2 ≤ (X:ℝ) := by
    dsimp only [X,L]; rw [Nat.cast_pow]
    nlinarith only [pw,l2,mul_le_mul_of_nonneg_right tr (sq_nonneg (t:ℝ))]
  have e := Real.sum_le_exp_of_nonneg (by norm_num : 0 ≤ (5761/10000:ℝ)) 8
  norm_num [Finset.sum_range_succ,Nat.factorial_succ] at e
  have eg := Real.exp_lt_exp.mpr farey_gamma_lower
  have g : (1779/1000:ℝ) ≤ Real.exp Real.eulerMascheroniConstant := by linarith
  change L*A ≤ _ at mert
  rw [Real.exp_neg] at mert
  have ap : A*L ≤ (4*100001/100000)/(1779/1000) := by
    have inv := one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1779/1000) g
    rw [one_div] at inv
    nlinarith only [mert,inv]
  apply sharp_normalized_contradiction (X:ℝ) L A _
  · exact_mod_cast (show 1≤X by omega)
  · dsimp [L]; positivity
  · exact Finset.prod_nonneg nn
  · exact Finset.prod_le_one₀ nn (fun _ _ => sub_le_self _ (by positivity))
  · exact err
  · exact ap
  · exact lower
  · change _ ≤ (189/500:ℝ)*((3001000*(X:ℝ)/3+1)/2)*(500*(X:ℝ)*A^2+A)
    push_cast at hi
    convert hi using 1 <;> dsimp only [A,FareySharpMertens.A,P] <;> ring