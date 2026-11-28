import Conjectures.Goldbach.TwistedGoldbachConductorValue
import Conjectures.Goldbach.BinaryShiftOrderTail

/-! A modulus-uniform off-diagonal estimate. The loss depends only on
the reduced additive denominator and is of double logarithmic size.
The Mertens estimate is imported from the existing Goldbach order-tail
module. See Pintz I, (1.21)–(1.22). -/

namespace Conjectures.Goldbach.TwistedGoldbachConductorSuppression

open Finset Real DirichletCharacter ErdosStraus.PrimeEstimates.Mertens
open TwistedGoldbachConductorValue TwistedGoldbachMixedPrincipal TwistedGoldbachLocalProduct
open scoped BigOperators Classical

noncomputable def totRatio (q : ℕ) : ℝ := (q:ℝ)/q.totient
noncomputable def primeRatio (p : ℕ) : ℝ := (p:ℝ)/((p:ℝ)-1)
noncomputable def doubleLog (q : ℕ) : ℝ := 1+Real.log (1+Real.log q)

theorem totient_euler (q : ℕ) (hq : 0 < q) :
    totRatio q = ∏ p ∈ q.primeFactors, primeRatio p := by
  have pos : 0 < ∏ p ∈ q.primeFactors, ((p:ℝ)-1) := prod_pos (fun p hp =>
    sub_pos.mpr (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt))
  have H := congrArg (fun n : ℕ => (n:ℝ)) (Nat.totient_mul_prod_primeFactors q)
  simp only [Nat.cast_mul,Nat.cast_prod] at H
  have each : ∏ p ∈ q.primeFactors, ((p-1:ℕ):ℝ) = ∏ p ∈ q.primeFactors, ((p:ℝ)-1) :=
    prod_congr rfl (fun p hp => by rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_le]; norm_num)
  rw [each] at H
  unfold totRatio primeRatio
  rw [prod_div_distrib,div_eq_div_iff (by exact_mod_cast (Nat.totient_pos.mpr hq).ne') pos.ne']
  linarith

private theorem count_factors (q : ℕ) (hq : 0 < q) : (q.primeFactors.card:ℝ) ≤ 2*log q := by
  have bound : 2^q.primeFactors.card ≤ q := (Finset.pow_card_le_prod _ _ _
    (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)).trans (Nat.le_of_dvd hq (Nat.prod_primeFactors_dvd q))
  have logs : (q.primeFactors.card:ℝ)*log 2 ≤ log q := by
    rw [← log_pow]
    apply log_le_log (by positivity)
    exact_mod_cast bound
  have half := Real.one_sub_inv_le_log_of_pos (x := 2) (by norm_num)
  norm_num at half
  nlinarith [mul_nonneg (Nat.cast_nonneg (α:=ℝ) q.primeFactors.card) (show 0 ≤ log 2-1/2 by linarith)]

theorem doubleLog_one_le (q : ℕ) (hq : 0 < q) : 1 ≤ doubleLog q := by
  have hlog : 0 ≤ log q := log_nonneg (by exact_mod_cast hq)
  exact le_add_of_nonneg_right (log_nonneg (by linarith))

theorem totient_double_log :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, 0 < q → totRatio q ≤ C * doubleLog q := by
  obtain ⟨A,hA,HM⟩ := mertensSecond
  let z := ∑' n : ℕ, (1:ℝ)/(n:ℝ)^2
  let K := mertensSecondConstant+A/log 2+1+2*z
  refine ⟨exp K,exp_pos K,?_⟩
  intro q hq
  let S := q.primeFactors
  let x := 2*(1+log q)
  have hlog : 0 ≤ log q := log_nonneg (by exact_mod_cast hq)
  have hx : 2 ≤ x := by dsimp [x]; linarith
  have hp (p : ℕ) (h : p ∈ S) : p.Prime := Nat.prime_of_mem_primeFactors h
  have small : ∑ p ∈ S.filter (fun p : ℕ => (p:ℝ) ≤ x), 1/(p:ℝ) ≤ primeReciprocalSum ⌊x⌋₊ := by
    apply sum_le_sum_of_subset_of_nonneg
    · intro p hh
      exact mem_primesUpTo.mpr ⟨hp p (mem_filter.mp hh).1,Nat.le_floor (mem_filter.mp hh).2⟩
    · intro _ _ _; positivity
  have large : ∑ p ∈ S.filter (fun p : ℕ => ¬(p:ℝ) ≤ x), 1/(p:ℝ) ≤ 1 := by
    let B := S.filter (fun p : ℕ => ¬(p:ℝ) ≤ x)
    have hc : (B.card:ℝ) ≤ x := by
      have bnd : (B.card:ℝ) ≤ S.card := by exact_mod_cast card_filter_le S (fun p : ℕ => ¬(p:ℝ) ≤ x)
      dsimp [x]
      linarith [count_factors q hq]
    calc
      _ ≤ ∑ _p ∈ B, 1/x := sum_le_sum (fun p hh =>
        one_div_le_one_div_of_le (by linarith) (le_of_not_ge (mem_filter.mp hh).2))
      _ ≤ 1 := by simpa only [sum_const,nsmul_eq_mul,mul_one_div] using (div_le_one (by linarith : 0<x)).mpr hc
  have recip : ∑ p ∈ S, 1/(p:ℝ) ≤ log (log x)+mertensSecondConstant+A/log 2+1 := by
    have H := (abs_le.mp (HM x hx)).2
    have Adiv := div_le_div_of_nonneg_left hA.le (log_pos (by norm_num : (1:ℝ)<2)) (log_le_log (by norm_num) hx)
    linarith [sum_filter_add_sum_filter_not S (fun p => (p:ℝ)≤x) (fun p => 1/(p:ℝ))]
  have zbound : ∑ p ∈ S, 1/(p:ℝ)^2 ≤ z :=
    (Real.summable_one_div_nat_pow.mpr (by decide : 1<2)).sum_le_tsum S (fun _ _ => by positivity)
  have terms : ∑ p ∈ S, 1/((p:ℝ)-1) ≤ log (log x)+K := by
    have point (p : ℕ) (hh : p ∈ S) : 1/((p:ℝ)-1) ≤ 1/(p:ℝ) + 2*(1/(p:ℝ)^2) := by
      have h : (2:ℝ)≤p := by exact_mod_cast (hp p hh).two_le
      have h0 : 0 < (p:ℝ) := by linarith
      have h1 : 0 < (p:ℝ)-1 := by linarith
      field_simp [h0.ne',h1.ne']
      nlinarith
    have sum := sum_le_sum point
    rw [sum_add_distrib,← mul_sum] at sum
    dsimp only [K]
    linarith
  rw [totient_euler q hq]
  calc
    _ ≤ ∏ p ∈ S, exp (1/((p:ℝ)-1)) := by
      apply prod_le_prod₀
      · intro p h
        have h1 : 1 < (p:ℝ) := by exact_mod_cast (hp p h).one_lt
        exact div_nonneg (Nat.cast_nonneg p) (by linarith)
      · intro p h
        have h1 : 1 < (p:ℝ) := by exact_mod_cast (hp p h).one_lt
        have eqn : primeRatio p = 1/((p:ℝ)-1)+1 := by unfold primeRatio; field_simp; ring
        rw [eqn]
        exact add_one_le_exp _
    _ = exp (∑ p ∈ S, 1/((p:ℝ)-1)) := (exp_sum ..).symm
    _ ≤ exp (log (log x)+K) := exp_le_exp.mpr terms
    _ ≤ _ := by
      rw [exp_add,exp_log (log_pos (by linarith : 1<x)),mul_comm]
      apply mul_le_mul_of_nonneg_left _ (exp_pos K).le
      dsimp [x,doubleLog]
      rw [log_mul (by norm_num) (by positivity)]
      linarith [log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]

private theorem primeRatio_ge_one {p : ℕ} (hp : p.Prime) : 1 ≤ primeRatio p := by
  have h : (1:ℝ)<p := by exact_mod_cast hp.one_lt
  exact (le_div_iff₀ (by linarith : 0 < (p:ℝ)-1)).mpr (by linarith)

/-- The large ordinary Euler factors at primes shared with the target
cancel before any bound on the totient is used. -/
theorem cancel_common_primes (L m : ℕ) [NeZero L] (he : Even m) :
    totRatio L ≤ 2*ordinaryWeight L m * totRatio (L/(m.gcd L)) := by
  let g := m.gcd L
  let j := L/g
  have hg : g ∣ L := Nat.gcd_dvd_right m L
  have hj : 0 < j := Nat.div_pos (Nat.le_of_dvd (NeZero.pos L) hg) (Nat.gcd_pos_of_pos_right m (NeZero.pos L))
  let A := L.primeFactors.filter (fun p => p ∣ m)
  let B := L.primeFactors.filter (fun p => ¬p ∣ m)
  have primeB (p : ℕ) (hp : p ∈ B) := Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1
  have primeA (p : ℕ) (hp : p ∈ A) := Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1
  have splitφ : (∏ p ∈ A, primeRatio p)*(∏ p ∈ B, primeRatio p) = totRatio L := by
    rw [totient_euler L (NeZero.pos L)]
    exact prod_filter_mul_prod_filter_not L.primeFactors _ primeRatio
  have splitW : (∏ p ∈ A, primeRatio p)*(∏ p ∈ B, localWeight m p) = ordinaryWeight L m := by
    rw [ordinary_product]
    have same : ∏ p ∈ A, primeRatio p = ∏ p ∈ A, localWeight m p := by
      exact prod_congr rfl (fun p hp => by simp only [localWeight,ite_eq_left (mem_filter.mp hp).2,primeRatio])
    rw [same]
    exact prod_filter_mul_prod_filter_not L.primeFactors _ _
  let Q := ∏ p ∈ B, p
  let _ : NeZero Q := ⟨(prod_pos (fun p hp => (primeB p hp).pos)).ne'⟩
  have lower := uniform_weight Q m he
  have half : (1/2:ℝ) ≤ ∏ p ∈ B, localWeight m p := by
    have factors : Q.primeFactors=B := Nat.primeFactors_prod primeB
    rw [ordinary_product,factors] at lower
    apply le_trans _ lower
    split <;> norm_num
  have cover : B ⊆ j.primeFactors := by
    intro p hp
    obtain ⟨mem,off⟩ := mem_filter.mp hp
    have hprod : p ∣ g*j := (Nat.mul_div_cancel' hg).symm ▸ Nat.dvd_of_mem_primeFactors mem
    have hd : p ∣ j := ((primeB p hp).dvd_mul.mp hprod).resolve_left
      (fun h => off (h.trans (Nat.gcd_dvd_left m L)))
    exact Nat.mem_primeFactors.mpr ⟨primeB p hp,hd,hj.ne'⟩
  have more : (∏ p ∈ B, primeRatio p) ≤ totRatio j := by
    rw [totient_euler j hj]
    exact prod_le_prod_of_subset_of_one_le₀ cover (fun p h => zero_le_one.trans (primeRatio_ge_one (primeB p h)))
      (fun p hp _ => primeRatio_ge_one (Nat.prime_of_mem_primeFactors hp))
  have a0 : 0 ≤ ∏ p ∈ A, primeRatio p := prod_nonneg (fun p h => zero_le_one.trans (primeRatio_ge_one (primeA p h)))
  have b0 : 0 ≤ ∏ p ∈ B, primeRatio p := prod_nonneg (fun p h => zero_le_one.trans (primeRatio_ge_one (primeB p h)))
  have agrow : (∏ p ∈ A, primeRatio p) ≤ 2*ordinaryWeight L m := by
    rw [← splitW]
    nlinarith [mul_nonneg a0 (sub_nonneg.mpr half)]
  rw [← splitφ]
  exact mul_le_mul agrow more b0 (a0.trans agrow)

theorem conductor_triangle {r s : ℕ} [NeZero r] [NeZero s] {α : DirichletCharacter ℂ r}
    {β : DirichletCharacter ℂ s} (hα : α.IsPrimitive) (hβ : β.IsPrimitive) :
    let d := (inversePair α β).conductor
    r ∣ Nat.lcm d s ∧ s ∣ Nat.lcm d r := by
  intro d
  let L := Nat.lcm r s
  let _ : NeZero L := ⟨(Nat.lcm_pos (NeZero.pos r) (NeZero.pos s)).ne'⟩
  let A := changeLevel (Nat.dvd_lcm_left r s) α
  let B := changeLevel (Nat.dvd_lcm_right r s) β
  let Z := inversePair α β
  have a : A.conductor=r := (conductor_changeLevel ..).trans hα
  have b : B.conductor=s := (conductor_changeLevel ..).trans hβ
  have az : Z*B=A⁻¹ := by
    change (A*B)⁻¹*B=A⁻¹
    rw [mul_comm A B]
    group
  have bz : Z*A=B⁻¹ := by change (A*B)⁻¹*A=B⁻¹; group
  have ar := conductor_mul_dvd_lcm_conductor Z B
  have br := conductor_mul_dvd_lcm_conductor Z A
  rw [az,conductor_inv,a,b] at ar
  rw [bz,conductor_inv,b,a] at br
  exact ⟨ar,br⟩

theorem conductor_saving {r s : ℕ} [NeZero r] [NeZero s] {α : DirichletCharacter ℂ r}
    {β : DirichletCharacter ℂ s} (hα : α.IsPrimitive) (hβ : β.IsPrimitive)
    (m : ℕ) (hm : 0 < m) (he : Even m) :
    let L := Nat.lcm r s
    let j := L/(m.gcd L)
    ‖series α β m‖ * sqrt (((L/r)*(L/s)*j:ℕ):ℝ) ≤
      2*‖series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m‖*(totRatio j)^2 := by
  intro L j
  let _ : NeZero L := ⟨(Nat.lcm_pos (NeZero.pos r) (NeZero.pos s)).ne'⟩
  let a := L/r
  let b := L/s
  let d := (inversePair α β).conductor
  let O := ‖series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m‖
  let T := ‖series α β m‖
  let W := ordinaryWeight L m
  have hw : 0 < W := lt_of_lt_of_le (by split <;> norm_num) (uniform_weight L m he)
  have hj : 0 < j := Nat.div_pos (Nat.le_of_dvd (NeZero.pos L) (Nat.gcd_dvd_right m L))
    (Nat.gcd_pos_of_pos_right m (NeZero.pos L))
  have hO : 0 ≤ O := norm_nonneg _
  have hjφ : 0 < (j.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr hj
  have hLφ : 0 < (L.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos L)
  by_cases good : supported r s L d j
  · have H := full_base hα hβ m hm
    dsimp only at H
    rw [base_norm hα hβ m] at H
    change T*W=O*(if supported r s L d j then _ else 0) at H
    rw [ite_eq_left good] at H
    have ra : sqrt r * sqrt a = sqrt L := by
      rw [← sqrt_mul (Nat.cast_nonneg r),← Nat.cast_mul,Nat.mul_div_cancel' (Nat.dvd_lcm_left r s)]
    have sb : sqrt s * sqrt b = sqrt L := by
      rw [← sqrt_mul (Nat.cast_nonneg s),← Nat.cast_mul,Nat.mul_div_cancel' (Nat.dvd_lcm_right r s)]
    have dj : sqrt d*sqrt j ≤ (j:ℝ) := by
      have h : d ≤ j := Nat.le_of_dvd hj good.2.2.1
      calc
        _ ≤ sqrt j*sqrt j := mul_le_mul_of_nonneg_right (sqrt_le_sqrt (by exact_mod_cast h)) (sqrt_nonneg _)
        _ = _ := Real.mul_self_sqrt (Nat.cast_nonneg _)
    have size : (sqrt r*sqrt s*sqrt d)*sqrt ((a*b*j:ℕ):ℝ) ≤ (L:ℝ)*j := by
      push_cast
      rw [sqrt_mul (mul_nonneg (Nat.cast_nonneg a) (Nat.cast_nonneg b)),sqrt_mul (Nat.cast_nonneg a)]
      calc
        _ = (sqrt r*sqrt a)*(sqrt s*sqrt b)*(sqrt d*sqrt j) := by ring
        _ ≤ _ := by rw [ra,sb,Real.mul_self_sqrt (Nat.cast_nonneg L)]; exact mul_le_mul_of_nonneg_left dj (Nat.cast_nonneg _)
    have clean := cancel_common_primes L m he
    change totRatio L ≤ 2*W*totRatio j at clean
    change T*sqrt ((a*b*j:ℕ):ℝ) ≤ 2*O*(totRatio j)^2
    apply (le_of_mul_le_mul_left _ hw)
    calc
      W*(T*sqrt ((a*b*j:ℕ):ℝ)) = (T*W)*sqrt ((a*b*j:ℕ):ℝ) := by ring
      _ = O*((sqrt r*sqrt s*sqrt d)*sqrt ((a*b*j:ℕ):ℝ)/((L.totient:ℝ)*j.totient)) := by rw [H]; ring
      _ ≤ O*((L:ℝ)*j/((L.totient:ℝ)*j.totient)) := mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right size (mul_pos hLφ hjφ).le) hO
      _ = O*(totRatio L*totRatio j) := by unfold totRatio; ring
      _ ≤ O*((2*W*totRatio j)*totRatio j) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right clean (div_nonneg (Nat.cast_nonneg j) hjφ.le)) hO
      _ = _ := by ring
  · have zero := not_ne_iff.mp (mt (full_support hα hβ m hm he).mp good)
    rw [zero,norm_zero,zero_mul]
    positivity

private theorem reduced_dvd (m k t : ℕ) (hk : 0 < k) : k/(m.gcd k) ∣ t ↔ k ∣ m*t := by
  let g := m.gcd k
  let v := k/g
  let u := m/g
  have hg : 0 < g := Nat.gcd_pos_of_pos_right m hk
  have gm : g*u=m := Nat.mul_div_cancel' (Nat.gcd_dvd_left m k)
  have gk : g*v=k := Nat.mul_div_cancel' (Nat.gcd_dvd_right m k)
  have cop : u.Coprime v := Nat.coprime_div_gcd_div_gcd hg
  change v ∣ t ↔ k ∣ m*t
  rw [← gk,← gm,mul_assoc,Nat.mul_dvd_mul_iff_left hg]
  exact ⟨fun h => h.trans (dvd_mul_left t u),cop.symm.dvd_of_dvd_mul_left⟩

theorem reduced_lcm {r s : ℕ} [NeZero r] [NeZero s] (m : ℕ) :
    (Nat.lcm r s)/(m.gcd (Nat.lcm r s)) = Nat.lcm (r/(m.gcd r)) (s/(m.gcd s)) := by
  let L := Nat.lcm r s
  have equiv (t : ℕ) : L/(m.gcd L) ∣ t ↔ Nat.lcm (r/(m.gcd r)) (s/(m.gcd s)) ∣ t := by
    rw [reduced_dvd m L t (Nat.lcm_pos (NeZero.pos r) (NeZero.pos s)),Nat.lcm_dvd_iff,Nat.lcm_dvd_iff,
      reduced_dvd m r t (NeZero.pos r),reduced_dvd m s t (NeZero.pos s)]
  exact Nat.dvd_antisymm ((equiv _).mpr (dvd_refl _)) ((equiv _).mp (dvd_refl _))

theorem complementary_dvd {r s : ℕ} [NeZero r] [NeZero s] {α : DirichletCharacter ℂ r}
    {β : DirichletCharacter ℂ s} (hα : α.IsPrimitive) (hβ : β.IsPrimitive) {m : ℕ}
    (good : supported r s (Nat.lcm r s) (inversePair α β).conductor (Nat.lcm r s / (m.gcd (Nat.lcm r s)))) :
    let L := Nat.lcm r s
    let d := (inversePair α β).conductor
    L/r ∣ d ∧ L/s ∣ d := by
  intro L d
  have hr : r ∣ L := Nat.dvd_lcm_left ..
  have hs : s ∣ L := Nat.dvd_lcm_right ..
  have ar : L/r ∣ s := Nat.dvd_of_mul_dvd_mul_left (NeZero.pos r) (by rw [Nat.mul_div_cancel' hr]; exact Nat.lcm_dvd_mul r s)
  have bs : L/s ∣ r := Nat.dvd_of_mul_dvd_mul_left (NeZero.pos s) (by rw [Nat.mul_div_cancel' hs,mul_comm]; exact Nat.lcm_dvd_mul r s)
  obtain ⟨A,B⟩ := conductor_triangle hα hβ
  exact ⟨good.1.2.dvd_of_dvd_mul_right (ar.trans (B.trans (Nat.lcm_dvd_mul d r))),
    good.2.1.2.dvd_of_dvd_mul_right (bs.trans (A.trans (Nat.lcm_dvd_mul d s)))⟩

/-- The five quantities in Pintz I (1.22). The denominator of each of
the first two quotients is the gcd of the source conductors. -/
def complexity (r s d m : ℕ) : ℕ :=
  max (max ((s/(r.gcd s))^2) ((r/(r.gcd s))^2)) (max (max (r/(m.gcd r)) (s/(m.gcd s))) d)

private theorem doubleLog_compare {j U : ℕ} (hj : 0 < j) (hU : 0 < U) (upper : j ≤ U^2) :
    doubleLog j ≤ 2 * doubleLog U := by
  have logU : 0 ≤ log U := log_nonneg (by exact_mod_cast hU)
  have lelog : log j ≤ 2*log U := by
    have H := log_le_log (by exact_mod_cast hj : (0:ℝ)<j) (by exact_mod_cast upper : (j:ℝ)≤(U:ℝ)^2)
    simpa only [log_pow,Nat.cast_ofNat] using H
  have le' : log (1+log j) ≤ log (2*(1+log U)) := log_le_log
    (by linarith [log_nonneg (by exact_mod_cast hj : (1:ℝ)≤j)]) (by linarith)
  rw [log_mul (by norm_num) (by positivity)] at le'
  unfold doubleLog
  linarith [log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2),log_nonneg (by linarith : (1:ℝ)≤1+log U)]

/-- The off-diagonal comparison, with its double logarithmic loss and one
constant uniform in every conductor and positive even target. -/
theorem pintz_comparison :
    ∃ C : ℝ, 0 < C ∧ ∀ (r s : ℕ) [NeZero r] [NeZero s] (α : DirichletCharacter ℂ r)
    (β : DirichletCharacter ℂ s), α.IsPrimitive → β.IsPrimitive → ∀ m : ℕ, 0 < m → Even m →
    let U := complexity r s (inversePair α β).conductor m
    ‖series α β m‖ * sqrt U ≤ C * ‖series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m‖*(doubleLog U)^2 := by
  obtain ⟨C,hC,phi⟩ := totient_double_log
  refine ⟨8*C^2,by positivity,?_⟩
  intro r s _ _ α β hα hβ m hm he U
  let L := Nat.lcm r s
  let k := r.gcd s
  let a := L/r
  let b := L/s
  let v := r/(m.gcd r)
  let w := s/(m.gcd s)
  let j := L/(m.gcd L)
  let d := (inversePair α β).conductor
  let T := ‖series α β m‖
  let O := ‖series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m‖
  have Lp : 0 < L := Nat.lcm_pos (NeZero.pos r) (NeZero.pos s)
  have hj : 0 < j := Nat.div_pos (Nat.le_of_dvd Lp (Nat.gcd_dvd_right m L)) (Nat.gcd_pos_of_pos_right m Lp)
  have ap : 0 < a := Nat.div_pos (Nat.le_of_dvd Lp (Nat.dvd_lcm_left ..)) (NeZero.pos r)
  have bp : 0 < b := Nat.div_pos (Nat.le_of_dvd Lp (Nat.dvd_lcm_right ..)) (NeZero.pos s)
  have aeq : a=s/k := by
    change Nat.lcm r s/r=s/r.gcd s
    rw [Nat.lcm_eq_mul_div,Nat.mul_div_assoc _ (Nat.gcd_dvd_right r s),Nat.mul_div_cancel_left _ (NeZero.pos r)]
  have beq : b=r/k := by
    change Nat.lcm r s/s=r/r.gcd s
    rw [Nat.lcm_comm,Nat.lcm_eq_mul_div,Nat.mul_div_assoc _ (Nat.gcd_dvd_right s r),Nat.mul_div_cancel_left _ (NeZero.pos s),Nat.gcd_comm]
  have Ueq : U=max (max (a^2) (b^2)) (max (max v w) d) := by rw [aeq,beq]; rfl
  have vu : v ≤ U := Ueq ▸ (le_max_left v w).trans ((le_max_left _ d).trans (le_max_right ..))
  have wu : w ≤ U := Ueq ▸ (le_max_right v w).trans ((le_max_left _ d).trans (le_max_right ..))
  have au : a^2 ≤ U := Ueq ▸ (le_max_left _ _).trans (le_max_left ..)
  have up : 0 < U := (pow_pos ap 2).trans_le au
  have jeq : j = Nat.lcm v w := reduced_lcm m
  have ju : j ≤ U^2 := by
    rw [jeq,pow_two]
    exact (Nat.le_of_dvd (Nat.mul_pos (Nat.div_pos (Nat.le_of_dvd (NeZero.pos r) (Nat.gcd_dvd_right m r))
        (Nat.gcd_pos_of_pos_right m (NeZero.pos r))) (Nat.div_pos (Nat.le_of_dvd (NeZero.pos s) (Nat.gcd_dvd_right m s))
        (Nat.gcd_pos_of_pos_right m (NeZero.pos s)))) (Nat.lcm_dvd_mul v w)).trans (Nat.mul_le_mul vu wu)
  by_cases good : supported r s L d j
  · obtain ⟨ad,bd⟩ := complementary_dvd hα hβ (m := m) good
    have dj := Nat.le_of_dvd hj good.2.2.1
    have aj := Nat.le_of_dvd hj (ad.trans good.2.2.1)
    have bj := Nat.le_of_dvd hj (bd.trans good.2.2.1)
    have top : U ≤ a*b*j := by
      rw [Ueq,max_le_iff,max_le_iff,max_le_iff,max_le_iff]
      have jtop : j ≤ a*b*j := Nat.le_mul_of_pos_left j (Nat.mul_pos ap bp)
      have vj : v ≤ j := Nat.le_of_dvd hj (jeq ▸ Nat.dvd_lcm_left v w)
      have wj : w ≤ j := Nat.le_of_dvd hj (jeq ▸ Nat.dvd_lcm_right v w)
      refine ⟨⟨?_,?_⟩,⟨⟨vj.trans jtop,wj.trans jtop⟩,dj.trans jtop⟩⟩
      · rw [pow_two]
        exact Nat.mul_le_mul (Nat.le_mul_of_pos_right a bp) aj
      · rw [pow_two]
        exact Nat.mul_le_mul (Nat.le_mul_of_pos_left b ap) bj
    have upper := (phi j hj).trans (mul_le_mul_of_nonneg_left (doubleLog_compare hj up ju) hC.le)
    have nonneg : 0 ≤ totRatio j := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    have hO : 0 ≤ O := norm_nonneg _
    calc
      T*sqrt U ≤ T*sqrt ((a*b*j:ℕ):ℝ) := mul_le_mul_of_nonneg_left (sqrt_le_sqrt (by exact_mod_cast top)) (norm_nonneg _)
      _ ≤ 2*O*(totRatio j)^2 := conductor_saving hα hβ m hm he
      _ ≤ 2*O*(C*(2*doubleLog U))^2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ nonneg upper 2) (by positivity)
      _ = _ := by ring
  · have zero := not_ne_iff.mp (mt (full_support hα hβ m hm he).mp good)
    rw [zero,norm_zero,zero_mul]
    positivity

end Conjectures.Goldbach.TwistedGoldbachConductorSuppression

set_option maxHeartbeats 1500000 in
open Conjectures.Goldbach.TwistedGoldbachConductorSuppression in
theorem Conjectures.Goldbach.TwistedGoldbachConductorSuppression :
by
  classical
  let S := fun {r s : ℕ} (α : DirichletCharacter ℂ r) (β : DirichletCharacter ℂ s) (m : ℕ) =>
    ∑' q : ℕ, if hq : q ≠ 0 then
      let _ : NeZero q := ⟨hq⟩
      if h : r ∣ q ∧ s ∣ q then
        let A := DirichletCharacter.changeLevel h.1 α
        let B := DirichletCharacter.changeLevel h.2 β
        gaussSum A ZMod.stdAddChar * gaussSum B ZMod.stdAddChar *
          gaussSum (A*B)⁻¹ (ZMod.stdAddChar.mulShift (-(m : ZMod q))) / (q.totient : ℂ)^2
      else 0
    else 0
  let O := S (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1)
  let hlog := fun q : ℕ => 1+Real.log (1+Real.log q)
  exact
    (∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, 0 < q → (q:ℝ)/q.totient ≤ C*hlog q) ∧
    (∀ (r s : ℕ) [NeZero r] [NeZero s] (α : DirichletCharacter ℂ r) (β : DirichletCharacter ℂ s),
      α.IsPrimitive → β.IsPrimitive → ∀ m : ℕ, 0 < m → Even m →
      let L := Nat.lcm r s
      let j := L/(m.gcd L)
      ‖S α β m‖*Real.sqrt (((L/r)*(L/s)*j:ℕ):ℝ) ≤
        2*‖O m‖*((j:ℝ)/j.totient)^2) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ (r s : ℕ) [NeZero r] [NeZero s]
      (α : DirichletCharacter ℂ r) (β : DirichletCharacter ℂ s), α.IsPrimitive → β.IsPrimitive →
      ∀ m : ℕ, 0 < m → Even m →
      let θ := (DirichletCharacter.changeLevel (Nat.dvd_lcm_left r s) α)*
        (DirichletCharacter.changeLevel (Nat.dvd_lcm_right r s) β)
      let U := max (max ((s/(r.gcd s))^2) ((r/(r.gcd s))^2))
        (max (max (r/(m.gcd r)) (s/(m.gcd s))) θ.conductor)
      ‖S α β m‖ * Real.sqrt U ≤ C*‖O m‖*(hlog U)^2) := by
  refine ⟨totient_double_log,fun _ _ _ _ _ _ hα hβ m hm he => conductor_saving hα hβ m hm he,?_⟩
  obtain ⟨C,hC,H⟩ := pintz_comparison
  refine ⟨C,hC,?_⟩
  intro r s _ _ α β hα hβ m hm he θ U
  have h := H r s α β hα hβ m hm he
  let D := (Conjectures.Goldbach.TwistedGoldbachConductorValue.inversePair α β).conductor
  have eU : complexity r s D m = U := by
    unfold D Conjectures.Goldbach.TwistedGoldbachConductorValue.inversePair
    rw [DirichletCharacter.conductor_inv]
    rfl
  change ‖Conjectures.Goldbach.TwistedGoldbachLocalProduct.series α β m‖ * Real.sqrt (complexity r s D m) ≤
    C * ‖Conjectures.Goldbach.TwistedGoldbachLocalProduct.series (1 : DirichletCharacter ℂ 1) 1 m‖ *
      (doubleLog (complexity r s D m))^2 at h
  rw [eU] at h
  exact h
