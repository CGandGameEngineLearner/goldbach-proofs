import Mathlib
import Conjectures.Goldbach.ReflectedMajorSharpFloor

open Finset
namespace EnvelopeEuler
open ArithmeticFunction
noncomputable section

def H : ArithmeticFunction ℝ :=
  ⟨fun n => if Squarefree n then 1/(n.totient:ℝ) else 0,by simp⟩
theorem H_apply (n:ℕ) : H n=if Squarefree n then 1/(n.totient:ℝ) else 0 := rfl
def K : ArithmeticFunction ℝ := ⟨fun n=>1/(n:ℝ),by simp⟩
def J : ArithmeticFunction ℝ := ⟨fun n=>((moebius n:ℤ):ℝ)/(n:ℝ),by simp⟩
def G : ArithmeticFunction ℝ := H*J

private theorem H_mult : H.IsMultiplicative := by
  refine ⟨by simp [H], fun {a b} hab=>?_⟩
  simp only [H_apply,Nat.squarefree_mul hab,Nat.totient_mul hab,Nat.cast_mul]
  by_cases ha:Squarefree a <;> by_cases hb:Squarefree b <;> simp [ha,hb,mul_inv_rev,mul_comm]
private theorem J_mult : J.IsMultiplicative := by
  refine ⟨by simp [J], fun {a b} hab=>?_⟩
  simp only [J,coe_mk,isMultiplicative_moebius.map_mul_of_coprime hab,Int.cast_mul,Nat.cast_mul]
  ring
theorem G_mult : G.IsMultiplicative := H_mult.mul J_mult

private theorem JK : J*K=1 := by
  ext n
  by_cases hn:n=0
  · simp [hn]
  have pos:0<(n:ℝ):=by exact_mod_cast (Nat.pos_of_ne_zero hn)
  rw [ArithmeticFunction.mul_apply]
  change (∑z∈n.divisorsAntidiagonal,(((moebius z.1:ℤ):ℝ)/(z.1:ℝ))*(1/(z.2:ℝ)))=_
  have E:(∑z∈n.divisorsAntidiagonal,(((moebius z.1:ℤ):ℝ)/(z.1:ℝ))*(1/(z.2:ℝ))) =
      (∑z∈n.divisorsAntidiagonal,((moebius z.1:ℤ):ℝ))/(n:ℝ):=by
    rw [sum_div];apply sum_congr rfl;intro z hz
    have prod:((z.1:ℝ)*z.2)=n:=by exact_mod_cast (Nat.mem_divisorsAntidiagonal.mp hz).1
    rw [←prod];ring
  rw [E,Nat.sum_divisorsAntidiagonal (fun x _=>((moebius x:ℤ):ℝ))]
  have mu:(∑d∈n.divisors,moebius d)=(1:ArithmeticFunction ℤ) n:=by
    rw [←ArithmeticFunction.coe_mul_zeta_apply,ArithmeticFunction.moebius_mul_coe_zeta]
  rw [←Int.cast_sum,mu]
  by_cases n1:n=1 <;> simp [n1,ArithmeticFunction.one_apply_ne]

theorem convolution (n:ℕ) : H n=∑z∈n.divisorsAntidiagonal,G z.1/(z.2:ℝ) := by
  have eq:G*K=H:=by rw [G,mul_assoc,JK,mul_one]
  rw [←eq,ArithmeticFunction.mul_apply]
  apply sum_congr rfl;intro z _
  change G z.1*(1/(z.2:ℝ)) = _
  ring

def delta (p:ℕ) : ℝ := 1/((p:ℝ)*(p-1:ℝ))
private theorem H_high {p:ℕ} (hp:p.Prime) (k:ℕ) : H (p^(k+2))=0 := by
  rw [H_apply,ite_eq_right];simp [Nat.squarefree_pow_iff hp.ne_one (by omega : k+2≠0)]
private theorem H_prime {p:ℕ} (hp:p.Prime) : H p=1/((p:ℝ)-1):=by
  simp [H_apply,hp.squarefree,Nat.totient_prime hp,Nat.cast_sub hp.one_le]
private theorem J_prime {p:ℕ} (hp:p.Prime) : J p= -(1/(p:ℝ)) := by
  simp [J,moebius_apply_prime hp,neg_div]
private theorem J_high {p:ℕ} (hp:p.Prime) (k:ℕ) : J (p^(k+2))=0 := by
  simp [J,moebius_apply_prime_pow hp (by omega : k+2 ≠ 0)]
private theorem G_succ {p:ℕ} (hp:p.Prime) (k:ℕ) : G (p^(k+1))=J (p^(k+1))+H p*J (p^k) := by
  rw [G,ArithmeticFunction.mul_apply,Nat.sum_divisorsAntidiagonal (fun x y=>H x*J y),Nat.sum_divisors_prime_pow hp]
  rw [sum_range_succ',sum_range_succ']
  simp only [Nat.add_assoc,Nat.reduceAdd,H_high hp,zero_mul,sum_const_zero,zero_add,pow_zero,Nat.div_one,pow_one,H_mult.1,one_mul]
  have eq:p^(k+1)/p=p^k:=by rw [pow_succ,Nat.mul_div_left _ hp.pos]
  rw [eq];ring

theorem G_one : G 1=1 := G_mult.1
theorem G_prime {p:ℕ} (hp:p.Prime): G p=delta p := by
  have eq:=G_succ hp 0
  norm_num [J_mult.1] at eq
  rw [eq,J_prime hp,H_prime hp]
  unfold delta
  have p1:1<(p:ℝ):=by exact_mod_cast hp.one_lt
  field_simp;ring
theorem G_square {p:ℕ} (hp:p.Prime) : G (p^2) = -delta p := by
  rw [G_succ hp 1,J_high hp 0,pow_one,H_prime hp,J_prime hp];simp only [delta,one_div,mul_inv_rev];ring
theorem G_high {p:ℕ} (hp:p.Prime) (k:ℕ): G (p^(k+3))=0 := by
  rw [G_succ hp (k+2),J_high hp (k+1),J_high hp k,mul_zero,add_zero]


private theorem G_off_three {p:ℕ} (hp:p.Prime) {k:ℕ} (hk:k∉range 3) : G (p^k)=0 := by
  have big:3≤k:=by simpa using hk
  have eq:k=k-3+3:=by omega
  exact eq ▸ G_high hp (k-3)

private theorem local_sum {p:ℕ} (hp:p.Prime) : (∑' k:ℕ,G (p^k))=1 := by
  rw [tsum_eq_sum (s:=range 3) (fun _ h=>G_off_three hp h)]
  simp only [sum_range_succ,sum_range_zero,zero_add,pow_zero,pow_one,G_one,G_prime hp,G_square hp];ring

private theorem local_abs {p:ℕ} (hp:p.Prime) : (∑' k:ℕ,|G (p^k)|)=1+2*delta p := by
  rw [tsum_eq_sum (s:=range 3) (fun _ h=>by rw [G_off_three hp h,abs_zero])]
  have ppos:1<(p:ℝ):=by exact_mod_cast hp.one_lt
  have pos:0≤delta p:=div_nonneg zero_le_one (mul_nonneg (Nat.cast_nonneg _) (by linarith only [ppos]))
  simp only [sum_range_succ,sum_range_zero,zero_add,pow_zero,pow_one,G_one,G_prime hp,G_square hp,abs_neg,abs_one,abs_of_nonneg pos];ring

theorem abs_summable : Summable (fun n:ℕ=>|G n|) := by
  let f:=fun n:ℕ=>|G n|
  let major:=fun n:ℕ=>(4:ℝ)*(1/(n:ℝ)^2)
  have ms:Summable major := (Real.summable_one_div_nat_pow.mpr (by decide : 1<2)).mul_left 4
  have mz(n:ℕ):0 ≤ major n := by dsimp [major];positivity
  have f1:f 1=1:=by simp [f,G_one]
  have fm {m n:ℕ} (h:m.Coprime n): f (m*n)=f m*f n:=by simp only [f,G_mult.map_mul_of_coprime h,abs_mul]
  have fs {p:ℕ} (hp:p.Prime):Summable (fun k:ℕ=>‖f (p^k)‖):=
    summable_of_ne_finset_zero (s:=range 3) (fun k hk=>by simp [f,G_off_three hp hk])
  apply summable_of_sum_range_le (c:=Real.exp (∑' n,major n)) (fun n=>abs_nonneg _)
  intro N
  have total:= (EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum (f:=f) f1 (fun h=>fm h) (fun hp=>fs hp) N).2
  have ind : HasSum (N.smoothNumbers.indicator f) (∏p∈N.primesBelow,∑' k,f (p^k)) :=
    hasSum_subtype_iff_indicator.mp total
  calc
    _ = ∑n∈range N,N.smoothNumbers.indicator f n:=by
      apply sum_congr rfl;intro n hn
      rcases Nat.eq_zero_or_pos n with rfl|np
      · simp [f,Set.indicator]
      · exact (Set.indicator_of_mem (Nat.mem_smoothNumbers'.mpr (fun p _ dv=>(Nat.le_of_dvd np dv).trans_lt (mem_range.mp hn))) f).symm
    _ ≤ ∑' n,N.smoothNumbers.indicator f n := ind.summable.sum_le_tsum _ (fun n _=>Set.indicator_nonneg (fun m _=>abs_nonneg _) n)
    _ = _ := ind.tsum_eq
    _ ≤ ∏p∈N.primesBelow,(1+major p):=by
      apply prod_le_prod₀ (fun p _=>tsum_nonneg (fun k=>abs_nonneg _))
      intro p hp
      rw [show (∑' k,f (p^k))=1+2*delta p from local_abs (Nat.mem_primesBelow.mp hp).2]
      apply add_le_add_right
      have pr:2≤(p:ℝ):=by exact_mod_cast (Nat.mem_primesBelow.mp hp).2.two_le
      dsimp only [major,delta]
      have pp:0<(p:ℝ):=by linarith only [pr]
      have po:(0:ℝ)<p-1:=by linarith only [pr]
      field_simp
      linarith only [pr]
    _ ≤ Real.exp (∑p∈N.primesBelow,major p):=Real.prod_one_add_le_exp_sum _ mz
    _ ≤ _ := Real.exp_le_exp.mpr (ms.sum_le_tsum _ (fun x _=>mz x))

theorem tsum_G : (∑' n:ℕ,G n)=1 := by
  have ps := G_mult.eulerProduct_hasProd (by simpa only [Real.norm_eq_abs] using abs_summable)
  have eq : (fun p:Nat.Primes=>∑' k:ℕ,G ((p:ℕ)^k))=fun _=>1 := funext (fun p=>local_sum p.2)
  rw [eq] at ps
  exact ps.unique hasProd_one

end
end EnvelopeEuler

namespace EnvelopeHarmonic
open Finset Filter
open scoped Topology

noncomputable section

def ratio (B d : ℕ) : ℝ :=
  if d=0 ∨ B<d then 0 else (harmonic (B/d):ℝ) / Real.log B

theorem log_ge_one (B:ℕ) (hB:4≤B) : 1≤Real.log B := by
  have h4 : (4:ℝ)≤B := by exact_mod_cast hB
  have h := Real.log_le_log (by norm_num : (0:ℝ)<4) h4
  have log4 : Real.log (4:ℝ)=2*Real.log 2 := by
    rw [show (4:ℝ)=2^2 by norm_num, Real.log_pow]
    ring
  rw [log4] at h
  linarith only [h, Real.log_two_gt_d9]

theorem ratio_bound (B d:ℕ) (hB:4≤B) : 0≤ratio B d ∧ ratio B d≤2 := by
  have logB:=log_ge_one B hB
  by_cases h0:d=0
  · simp [ratio,h0]
  by_cases h:d≤B
  · have kpos : 0<B/d := Nat.div_pos h (Nat.pos_of_ne_zero h0)
    have kle : B/d≤B:=Nat.div_le_self ..
    have hk : (1:ℝ)≤((B/d:ℕ):ℝ) := by exact_mod_cast kpos
    have hkle : ((B/d:ℕ):ℝ)≤B := by exact_mod_cast kle
    have upper := harmonic_le_one_add_log (B/d)
    have logkle := Real.log_le_log (by linarith only [hk] : (0:ℝ)<((B/d:ℕ):ℝ)) hkle
    have hnonneg : (0:ℝ)≤(harmonic (B/d):ℝ) :=
      (Real.log_nonneg (by exact_mod_cast (Nat.le_add_left 1 (B/d)) :
        (1:ℝ)≤((B/d+1:ℕ):ℝ))).trans
        (log_add_one_le_harmonic (B/d))
    simp only [ratio, h0, false_or, not_lt.mpr h, ite_false]
    constructor
    · exact div_nonneg hnonneg (by linarith only [logB])
    · apply (div_le_iff₀ (by linarith only [logB])).mpr
      linarith only [upper,logkle,logB]
  · have high:B<d:=Nat.lt_of_not_ge h
    simp [ratio,h0,high]

private theorem harmonic_between (B d:ℕ) (hd:0<d) (h:d≤B) :
    Real.log B - Real.log d ≤ (harmonic (B/d):ℝ) ∧
      (harmonic (B/d):ℝ) ≤ 1 + Real.log B := by
  have kp:0<B/d:=Nat.div_pos h hd
  have kplus : (0:ℝ)<((B/d+1:ℕ):ℝ) := by exact_mod_cast (Nat.succ_pos (B/d))
  have castB : (0:ℝ)<B := by exact_mod_cast (hd.trans_le h)
  have castd : (0:ℝ)<d := by exact_mod_cast hd
  have upperNat : B/d≤B:=Nat.div_le_self ..
  have upperReal : ((B/d:ℕ):ℝ)≤B := by exact_mod_cast upperNat
  have lowerNat := Nat.lt_mul_div_succ B hd
  have lowerReal : (B:ℝ) ≤ (d:ℝ)*((B/d+1:ℕ):ℝ) := by
    exact_mod_cast lowerNat.le
  have logLower := Real.log_le_log castB lowerReal
  rw [Real.log_mul castd.ne' kplus.ne'] at logLower
  have harmonicLower := log_add_one_le_harmonic (B/d)
  have harmonicUpper := harmonic_le_one_add_log (B/d)
  have logUpper := Real.log_le_log (by exact_mod_cast kp : (0:ℝ)<((B/d:ℕ):ℝ)) upperReal
  constructor <;> linarith only [logLower,harmonicLower,harmonicUpper,logUpper]

theorem ratio_tendsto_one (d:ℕ) (hd:0<d) :
    Tendsto (fun B:ℕ=>ratio B d) atTop (𝓝 1) := by
  have logtop : Tendsto (fun B:ℕ=>Real.log (B:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have invlog : Tendsto (fun B:ℕ=>(Real.log (B:ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp logtop
  have ll : Tendsto (fun B:ℕ=>1-Real.log (d:ℝ)*(Real.log (B:ℝ))⁻¹)
      atTop (𝓝 1) := by
    convert tendsto_const_nhds.sub ((tendsto_const_nhds.mul invlog)) using 1
    simp
  have uu : Tendsto (fun B:ℕ=>1+(Real.log (B:ℝ))⁻¹)
      atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add invlog
  apply Filter.Tendsto.squeeze' ll uu
  · filter_upwards [eventually_ge_atTop (max 4 d)] with B hB
    have dB:d≤B:=le_trans (le_max_right ..) hB
    have four:4≤B:=le_trans (le_max_left ..) hB
    have logpos:0<Real.log B:=lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (log_ge_one B four)
    have h:= (harmonic_between B d hd dB).1
    have eq:1-Real.log (d:ℝ)*(Real.log (B:ℝ))⁻¹ =
        (Real.log B-Real.log d)/Real.log B := by field_simp
    rw [eq,ratio]
    simp only [hd.ne', false_or, not_lt.mpr dB, ite_false]
    exact div_le_div_of_nonneg_right h logpos.le
  · filter_upwards [eventually_ge_atTop (max 4 d)] with B hB
    have dB:d≤B:=le_trans (le_max_right ..) hB
    have four:4≤B:=le_trans (le_max_left ..) hB
    have logpos:0<Real.log B:=lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (log_ge_one B four)
    have h:= (harmonic_between B d hd dB).2
    have eq:1+(Real.log (B:ℝ))⁻¹ =
        (1+Real.log B)/Real.log B := by field_simp; ring
    rw [eq,ratio]
    simp only [hd.ne', false_or, not_lt.mpr dB, ite_false]
    exact div_le_div_of_nonneg_right h logpos.le

theorem weighted_ratio_tendsto (G:ℕ→ℝ)
    (hG:Summable (fun d=>|G d|)) (g0:G 0=0) :
    Tendsto (fun B:ℕ=>∑' d,G d*ratio B d) atTop (𝓝 (∑' d,G d)) := by
  apply tendsto_tsum_of_dominated_convergence (bound:=fun d=>2*|G d|)
  · exact hG.mul_left 2
  · intro d
    by_cases hd:d=0
    · subst d
      simp [g0]
    · have pos:0<d:=Nat.pos_of_ne_zero hd
      have lim := (tendsto_const_nhds (x:=G d)).mul (ratio_tendsto_one d pos)
      simpa only [mul_one] using lim
  · filter_upwards [eventually_ge_atTop (4:ℕ)] with B hB d
    obtain ⟨r0,r2⟩:=ratio_bound B d hB
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg r0]
    have h:=mul_le_mul_of_nonneg_left r2 (abs_nonneg (G d))
    nlinarith only [h]


end
end EnvelopeHarmonic

open Finset
namespace EnvelopeEuler
noncomputable section

theorem finite_reindex (B:ℕ) :
    (∑q∈Icc 1 B,H q)/Real.log B =
      ∑'d:ℕ,G d*(if d=0 ∨ B<d then 0 else (harmonic (B/d):ℝ)/Real.log B) := by
  have iv (t:ℕ):Icc 1 t=Ioc 0 t:=by ext j;simp [Nat.one_le_iff_ne_zero,Nat.pos_iff_ne_zero]
  have mult:G*K=H:=by
    ext n;rw [convolution,ArithmeticFunction.mul_apply];apply sum_congr rfl;intro z _
    change G z.1*(1/(z.2:ℝ))=G z.1/(z.2:ℝ);ring
  have har (t:ℕ):(∑m∈Ioc 0 t,K m)=(harmonic t:ℝ):=by
    rw [←iv,harmonic_eq_sum_Icc];simp [K]
  rw [iv,←mult,ArithmeticFunction.sum_Ioc_mul_eq_sum_sum,sum_div,tsum_eq_sum (s:=Ioc 0 B)]
  · apply sum_congr rfl;intro d hd
    have off:¬(d=0 ∨ B<d):=by have := mem_Ioc.mp hd;omega
    rw [ite_eq_right off,har];ring
  · intro d hd
    have off:d=0 ∨ B<d:=by by_contra! z;exact hd (mem_Ioc.mpr ⟨Nat.pos_of_ne_zero z.1,z.2⟩)
    rw [ite_eq_left off,mul_zero]

end
end EnvelopeEuler

open Filter
namespace EnvelopePrimorial

theorem prime_dvd {p S m : ℕ} (hp:p.Prime) (ps:p≤S) (div:primorial S∣m) : p∣m :=
  (hp.dvd_primorial_iff.mpr ps).trans div

theorem squarefree_dvd {q S m : ℕ} (sq:Squarefree q) (qs:q≤S) (div:primorial S∣m) : q∣m :=
  sq.dvd_primorial.trans ((primorial_dvd_primorial qs).trans div)

theorem fits {N : ℕ} (large:2^32≤N) :
    12*primorial (Nat.log 2 (N+2)/16) ≤ N ∧ 2 ≤ Nat.log 2 (N+2)/16 := by
  let B:=Nat.log 2 (N+2)
  let S:=B/16
  have b32 : 32≤B := Nat.le_log_of_pow_le (by decide) (large.trans (by omega))
  have shift : 2*S+4≤B :=by dsimp [S]; omega
  have hp : 2^(2*S+4)≤2^B := Nat.pow_le_pow_right (by decide) shift
  have hn : 2^B ≤ N+2 := Nat.pow_log_le_self _ (by omega)
  have hfour : 16*4^S≤N+2 := by
    calc
      _ = 2^(2*S+4) := by rw [pow_add,pow_mul]; norm_num; omega
      _ ≤ _ := hp.trans hn
  have pp := primorial_le_four_pow S
  have pos := primorial_pos S
  change 12*primorial S≤N ∧ 2≤S
  dsimp [S] at *
  omega

theorem close_multiple {N S : ℕ} (small:12*primorial S≤N) (hS:2≤S) :
    ∃m:ℕ, N≤ m ∧ m≤2*N ∧ 4*N≤3*m ∧ 2*m≤3*N ∧ Even m ∧
      3*m≤4*N+3*primorial S ∧ primorial S∣m := by
  let P:=primorial S
  let d:=3*P
  let k:=4*N/d
  let m:=(k+1)*P
  have pp : 0<P := primorial_pos S
  have dp : 0<d := by dsimp [d]; omega
  have rem := Nat.mod_lt (4*N) dp
  have split : d*k + 4*N % d=4*N := Nat.div_add_mod (4*N) d
  have triple : 3*m=d*k+d := by dsimp [m,d];ring
  have close : 3*m≤4*N+3*P := by change 3*m≤4*N+d;omega
  have md : P∣m := dvd_mul_left _ _
  have even : Even m := even_iff_two_dvd.mpr (prime_dvd Nat.prime_two hS md)
  change 12*P≤N at small
  refine ⟨m,?_,?_,?_,?_,even,close,md⟩ <;> dsimp [d] at * <;> omega

theorem eventual_target : ∀ᶠ N:ℕ in atTop, ∃m:ℕ, N≤ m ∧ m≤2*N ∧ 4*N≤3*m ∧
    2*m≤3*N ∧ Even m ∧ primorial (Nat.log 2 (N+2)/16)∣m := by
  filter_upwards [eventually_ge_atTop (2^32:ℕ)] with N hN
  obtain ⟨small,hS⟩:=fits hN
  obtain ⟨m,l,h,bl,bh,ev,_,div⟩:=close_multiple small hS
  exact ⟨m,l,h,bl,bh,ev,div⟩

end EnvelopePrimorial

open Filter Topology
namespace EnvelopeScales

def B (N:ℕ) := Nat.log 2 (N+2)
def S (N:ℕ) := B N/16

theorem B_top : Tendsto B atTop atTop := by
  refine tendsto_atTop.2 fun k => ?_
  filter_upwards [eventually_ge_atTop (2^k:ℕ)] with n hn
  exact Nat.le_log_of_pow_le (by decide) (hn.trans (Nat.le_add_right _ _))

theorem S_top : Tendsto S atTop atTop := by
  refine tendsto_atTop.2 fun k => ?_
  filter_upwards [B_top.eventually_ge_atTop (16*k)] with n hn
  dsimp [S]
  omega

private theorem B_bounds {N:ℕ} (hn:2≤N) :
    Real.log (N:ℝ) ≤ (B N:ℝ)+1 ∧ (B N:ℝ) ≤ 4*Real.log (N:ℝ) := by
  have hnR : (2:ℝ)≤N := by exact_mod_cast hn
  have hnP : (0:ℝ)<N := by linarith
  have large : (N:ℝ) ≤ (2:ℝ)^(B N+1) := by
    exact_mod_cast (Nat.le_add_right N 2).trans (Nat.lt_pow_succ_log_self (by decide : 1<2) (N+2)).le
  have lo := Real.log_le_log hnP large
  rw [Real.log_pow, Nat.cast_add, Nat.cast_one] at lo
  have Bz := Nat.cast_nonneg (α:=ℝ) (B N)
  have bp : (2:ℝ)^(B N) ≤ N+2 := by exact_mod_cast (Nat.pow_log_le_self 2 (show N+2≠0 by omega))
  have hi := Real.log_le_log (pow_pos (by norm_num : (0:ℝ)<2) _) (bp.trans (show (N:ℝ)+2≤2*N by linarith))
  rw [Real.log_pow,Real.log_mul (by norm_num) hnP.ne'] at hi
  have hlog := Real.log_le_log (by norm_num : (0:ℝ)<2) hnR
  constructor
  · exact lo.trans (by nlinarith only [mul_nonneg (show 0≤(B N:ℝ)+1 by linarith) (show 0≤1-Real.log 2 by linarith only [Real.log_two_lt_d9])])
  · nlinarith only [hi,hlog,mul_nonneg Bz (show 0≤Real.log 2-1/2 by linarith only [Real.log_two_gt_d9])]

private theorem comparables : ∀ᶠ N:ℕ in atTop,
    (Real.log (N:ℝ) ≤ 64*(B N:ℝ) ∧ (B N:ℝ)≤64*Real.log (N:ℝ)) ∧
    (Real.log (N:ℝ) ≤ 64*(S N:ℝ) ∧ (S N:ℝ)≤64*Real.log (N:ℝ)) := by
  filter_upwards [B_top.eventually_ge_atTop 32,eventually_ge_atTop (2:ℕ)] with N b32 hn
  obtain ⟨lo,hi⟩:=B_bounds hn
  have positive:=Real.log_natCast_nonneg N
  have bR : (32:ℝ)≤B N := by exact_mod_cast b32
  have bS : B N+1≤64*S N := by dsimp [S];omega
  have bsR : (B N:ℝ)+1≤64*(S N:ℝ) := by exact_mod_cast bS
  have sB : (S N:ℝ)≤B N := by exact_mod_cast Nat.div_le_self (B N) 16
  exact ⟨⟨by linarith,by linarith⟩,⟨lo.trans bsR,by linarith⟩⟩

private theorem log_ratio (T : ℕ→ℕ) (comp:∀ᶠ N:ℕ in atTop,
    Real.log (N:ℝ) ≤ 64*(T N:ℝ) ∧ (T N:ℝ)≤64*Real.log (N:ℝ)) :
    Tendsto (fun N:ℕ => Real.log (T N:ℝ)/Real.log (Real.log (N:ℝ))) atTop (𝓝 1) := by
  let L := fun N:ℕ => Real.log (Real.log (N:ℝ))
  have tL : Tendsto L atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have err : Tendsto (fun N:ℕ => Real.log 64/L N) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tL
  have minus : Tendsto (fun N:ℕ => 1-Real.log 64/L N) atTop (𝓝 1) := by simpa using (tendsto_const_nhds (x:=(1:ℝ))).sub err
  have plus : Tendsto (fun N:ℕ => 1+Real.log 64/L N) atTop (𝓝 1) := by simpa using (tendsto_const_nhds (x:=(1:ℝ))).add err
  have both : ∀ᶠ N:ℕ in atTop, 1-Real.log 64/L N ≤ Real.log (T N:ℝ)/L N ∧
       Real.log (T N:ℝ)/L N ≤ 1+Real.log 64/L N := by
    filter_upwards [comp,tL.eventually_gt_atTop 0,eventually_ge_atTop (2:ℕ)] with N h hL hn
    have nr : (1:ℝ)<N := by exact_mod_cast (show 1<N by omega)
    have lp := Real.log_pos nr
    have tp : (0:ℝ)<T N := by linarith only [lp,h.1]
    have l1 := Real.log_le_log lp h.1
    have l2 := Real.log_le_log tp h.2
    rw [Real.log_mul (by norm_num) tp.ne'] at l1
    rw [Real.log_mul (by norm_num) lp.ne'] at l2
    change L N≤_ at l1
    change _≤Real.log 64 + L N at l2
    constructor
    · field_simp [hL]; linarith only [l1]
    · field_simp [hL]; linarith only [l2]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' minus plus (both.mono fun _ h=>h.1) (both.mono fun _ h=>h.2)

theorem B_ratio : Tendsto (fun N:ℕ => Real.log (B N:ℝ)/Real.log (Real.log (N:ℝ))) atTop (𝓝 1) :=
  log_ratio B (comparables.mono fun _ h=>h.1)
theorem S_ratio : Tendsto (fun N:ℕ => Real.log (S N:ℝ)/Real.log (Real.log (N:ℝ))) atTop (𝓝 1) :=
  log_ratio S (comparables.mono fun _ h=>h.2)
end EnvelopeScales

namespace EnvelopeComparison
open Finset Conjectures.Goldbach.EstermannAlmostAllPolylog_aux.GoldbachMajorArc
open scoped BigOperators Classical
noncomputable section

def H (q : ℕ) : ℝ := if Squarefree q then 1/(q.totient:ℝ) else 0

private theorem H_nonneg (q : ℕ) : 0 ≤ H q := by
  unfold H; split <;> positivity

private theorem Hmul {a b : ℕ} (h : a.Coprime b) : H (a*b) = H a * H b := by
  unfold H
  simp only [Nat.squarefree_mul h, Nat.totient_mul h, Nat.cast_mul]
  by_cases ha : Squarefree a <;> by_cases hb : Squarefree b <;> simp [ha,hb,div_eq_mul_inv,mul_comm]

theorem coefficient_bound {q : ℕ} (hq : 0 < q) (m : ℕ) :
    ‖coefficient q m‖ ≤ H q ∧ (q ∣ m → coefficient q m = ((H q : ℝ):ℂ)) := by
  induction q using Nat.recOnPosPrimePosCoprime with
  | zero => omega
  | one => simp [coefficient_one,H]
  | prime_pow p k hp hk =>
    cases k with
    | zero => simp [coefficient_one,H]
    | succ k =>
      cases k with
      | zero =>
        simp only [zero_add, pow_one, coefficient_prime hp]
        have p1 : (1:ℝ) ≤ (p:ℝ)-1 := by have := (show (2:ℝ) ≤ p by exact_mod_cast hp.two_le); linarith
        have pv : H p = 1/((p:ℝ)-1) := by simp [H,hp.squarefree,Nat.totient_prime hp,Nat.cast_sub hp.one_le]
        rw [pv]
        constructor
        · rw [Complex.norm_real, Real.norm_eq_abs]
          unfold localCoefficient
          by_cases div : p ∣ m
          · simp only [if_pos div, abs_of_nonneg (by positivity : 0 ≤ 1/((p:ℝ)-1)), le_refl]
          · simp only [div, ite_false, abs_neg, abs_of_nonneg (by positivity : (0:ℝ) ≤ 1/((p:ℝ)-1)^2)]
            exact one_div_le_one_div_of_le (by linarith) (by nlinarith [sq_nonneg ((p:ℝ)-2)])
        · intro h; simp [localCoefficient, h]
      | succ j =>
        have ns : ¬Squarefree (p^(j+2)) := by
          rw [Nat.squarefree_pow_iff hp.ne_one (by omega)]
          omega
        simp [coefficient_higher_power hp, H, ns]
  | coprime a b ha hb hc ia ib =>
    obtain ⟨aa,ae⟩ := ia (by omega)
    obtain ⟨ba,be⟩ := ib (by omega)
    rw [coefficient_mul (by omega) (by omega) hc, Hmul hc, norm_mul, Complex.ofReal_mul]
    exact ⟨mul_le_mul aa ba (norm_nonneg _) (H_nonneg _), fun d => by
      rw [ae ((dvd_mul_right a b).trans d), be ((dvd_mul_left b a).trans d)]⟩

def mass (L : ℕ) := ∑ q ∈ Icc 1 L, H q

theorem upper (L m : ℕ) : SharpAssembly.row L m ≤ mass L := by
  apply sum_le_sum
  intro q h
  exact (Complex.re_le_norm _).trans (coefficient_bound (mem_Icc.mp h).1 m).1

theorem lower {L S m : ℕ} (hs : S ≤ L) (div : ∀ q ≤ S, Squarefree q → q ∣ m) :
    2 * mass S - mass L ≤ SharpAssembly.row L m := by
  classical
  have each (q : ℕ) (hq : q ∈ Icc 1 S) : (coefficient q m).re = H q := by
    have bd := coefficient_bound (mem_Icc.mp hq).1 m
    by_cases sq : Squarefree q
    · simp [bd.2 (div _ (mem_Icc.mp hq).2 sq)]
    · have z : H q = 0 := by simp [H, sq]
      have c : coefficient q m = 0 := norm_le_zero_iff.mp (z ▸ bd.1)
      simp [c,z]
  have split := Finset.sum_le_sum_of_subset_of_nonneg (s:=Icc 1 S) (t:=Icc 1 L)
    (f:=fun q => (coefficient q m).re+H q) (Finset.Icc_subset_Icc_right hs)
    (fun q hq _ => by
      have lo := (abs_le.mp ((Complex.abs_re_le_norm (coefficient q m)).trans (coefficient_bound (mem_Icc.mp hq).1 m).1)).1
      linarith)
  have small : ∑ q ∈ Icc 1 S, ((coefficient q m).re+H q) = 2*mass S := by
    calc
      _ = ∑ q ∈ Icc 1 S, (2:ℝ)*H q := sum_congr rfl fun q hq => by rw [each q hq];ring
      _ = _ := (mul_sum ..).symm
  rw [small, sum_add_distrib] at split
  change 2*mass S ≤ SharpAssembly.row L m + mass L at split
  linarith

end
end EnvelopeComparison

namespace EnvelopeAssembly
open Finset Filter Real Conjectures.Goldbach.EstermannAlmostAllPolylog_aux
open scoped Topology BigOperators Classical
noncomputable section

def B (N : ℕ) := Nat.log 2 (N+2)
def Y (N : ℕ) := Real.log (Real.log (N:ℝ))
def actual (N m : ℕ) := (GoldbachBa08Approx.coefficient N m (B N) ((B N)^3)).re
def inside (N : ℕ) := (Finset.Icc N (2*N)).filter (SharpAssembly.band N)
def length (N m : ℕ) : ℝ := 2*(N:ℝ)-(m:ℝ)

theorem approximation : ∀ᶠ N : ℕ in atTop, ∀ m ∈ inside N,
    |actual N m - (length N m+1)*SharpAssembly.row (B N) m| ≤ (N:ℝ) := by
  filter_upwards [SharpArcTransfer.transfer 1 (by norm_num)] with N hN
  intro m hit
  have hm := Finset.mem_Icc.mp (Finset.mem_filter.mp hit).1
  let k := B N
  let z := ((2*N-m:ℕ):ℂ)+1
  let s := ∑ q ∈ Icc 1 k, GoldbachMajorArc.coefficient q m
  have err : |(GoldbachBa08Approx.coefficient N m k (k^3)-z*s).re| ≤ (N:ℝ) :=
    (Complex.abs_re_le_norm _).trans (by simpa only [one_mul, B, k, z, s] using hN m hm.1 hm.2)
  have hv : z = ((2*(N:ℝ)-(m:ℝ)+1 : ℝ) : ℂ) := by
    dsimp [z]; push_cast [hm.2]; ring
  rw [hv, Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] at err
  simpa only [actual, length, k, SharpAssembly.row, s, Complex.re_sum] using err

private theorem numerical {A r n x y a : ℝ} (ha : 0<a) (cap : a≤1/16)
    (xp : 0<x) (bigX : 1 ≤ a*x) (bigY : 2 ≤ a*y) (band : n≤2*x)
    (err : |A-(x+1)*r| ≤ n) :
    (r ≤ (1+a)*y → A/x ≤ (1+4*a)*y) ∧
    ((1-3*a)*y ≤ r → (1-4*a)*y ≤ A/x) := by
  have yp : 0 < y := by by_contra! hy; linarith [mul_nonpos_of_nonneg_of_nonpos ha.le hy]
  have ny : n ≤ (a*y)*x := by nlinarith only [band,mul_le_mul_of_nonneg_right bigY xp.le]
  have spare : (1+a)*y ≤ 2*((a*x)*y) := by
    nlinarith only [mul_le_mul_of_nonneg_right bigX yp.le,
      mul_le_mul_of_nonneg_right (show a≤1 by linarith) yp.le]
  obtain ⟨al,au⟩ := abs_le.mp err
  constructor
  · intro h
    apply (div_le_iff₀ xp).mpr
    have hm := mul_le_mul_of_nonneg_left h (show 0≤x+1 by linarith)
    nlinarith only [au, hm, spare, ny]
  · intro h
    apply (le_div_iff₀ xp).mpr
    have hm := mul_le_mul_of_nonneg_left h (show 0≤x+1 by linarith)
    have pos := mul_nonneg (show 0 ≤ 1-3*a by linarith) yp.le
    nlinarith only [al,hm,pos,ny]

theorem result (M : ℕ → ℝ)
    (hi : ∀ L m, SharpAssembly.row L m ≤ M L)
    (choose : ∀ᶠ N : ℕ in atTop, ∃ m ∈ inside N,
      2*M (B N/16) - M (B N) ≤ SharpAssembly.row (B N) m)
    (long : Tendsto (fun N => M (B N)/Y N) atTop (𝓝 1))
    (short : Tendsto (fun N => M (B N/16)/Y N) atTop (𝓝 1)) :
    ∀ ε : ℝ, 0 < ε → ∃ T : ℕ, ∀ N ≥ T,
      (∀ m ∈ inside N, actual N m/length N m ≤ (1+ε)*Y N) ∧
      (∃ m ∈ inside N, (1-ε)*Y N ≤ actual N m/length N m) := by
  intro ε hε
  let a := min (ε/16) (1/16)
  have ha : 0 < a := lt_min (by positivity) (by norm_num)
  have cap : a ≤ 1/16 := min_le_right _ _
  have capε : 4*a ≤ ε := by have h : a≤ε/16 := min_le_left _ _; linarith
  have yTop : Tendsto Y atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ)))
  have nTop := (tendsto_atTop.1 (tendsto_natCast_atTop_atTop (R:=ℝ))) (2/a)
  have yc := (tendsto_atTop.1 yTop) (2/a)
  have hlong := (Metric.tendsto_nhds.mp long) a ha
  have hshort := (Metric.tendsto_nhds.mp short) a ha
  apply eventually_atTop.mp
  filter_upwards [nTop,yc,hlong,hshort,choose,approximation] with N nx yx ml ms pick err
  have yn : 2 ≤ a*Y N := by simpa only [mul_comm] using (div_le_iff₀ ha).mp yx
  have nn : 2 ≤ a*(N:ℝ) := by simpa only [mul_comm] using (div_le_iff₀ ha).mp nx
  have yp : 0 < Y N := by by_contra! hy; linarith [mul_nonpos_of_nonneg_of_nonpos ha.le hy]
  have upper : M (B N) ≤ (1+a)*Y N := by
    have h := (abs_lt.mp (show |M (B N)/Y N - 1| < a by simpa [Real.dist_eq] using ml)).2
    apply (div_le_iff₀ yp).mp; linarith
  have lower : (1-a)*Y N ≤ M (B N/16) := by
    have h := (abs_lt.mp (show |M (B N/16)/Y N - 1| < a by simpa [Real.dist_eq] using ms)).1
    apply (le_div_iff₀ yp).mp; linarith
  have num (m : ℕ) (hit : m∈inside N) := by
    have hb : SharpAssembly.band N m := (Finset.mem_filter.mp hit).2
    have band := hb.2.1
    have h2 : 2*(m:ℝ) ≤ 3*(N:ℝ) := by exact_mod_cast band
    have hh : (N:ℝ) ≤ 2*length N m := by unfold length; linarith
    have nx2 := mul_le_mul_of_nonneg_left hh ha.le
    have bx : 1 ≤ a*length N m := by nlinarith only [nn,nx2]
    have xp : 0 < length N m := by by_contra! hx; linarith [mul_nonpos_of_nonneg_of_nonpos ha.le hx]
    exact numerical ha cap xp bx yn hh (err m hit)
  constructor
  · intro m hit
    exact ((num m hit).1 ((hi _ _).trans upper)).trans
      (mul_le_mul_of_nonneg_right (by linarith) yp.le)
  · obtain ⟨m,hit,h⟩ := pick
    refine ⟨m,hit, (mul_le_mul_of_nonneg_right (by linarith : 1-ε≤1-4*a) yp.le).trans ((num m hit).2 ?_)⟩
    linarith
end
end EnvelopeAssembly

open Filter in
open scoped Topology in
private theorem envelopeMassLimit : Tendsto (fun t => EnvelopeComparison.mass t / Real.log (t:ℝ)) atTop (𝓝 1) := by
  have limit := EnvelopeHarmonic.weighted_ratio_tendsto (fun n => EnvelopeEuler.G n)
    EnvelopeEuler.abs_summable (by simp)
  rw [EnvelopeEuler.tsum_G] at limit
  apply limit.congr
  intro t
  exact (EnvelopeEuler.finite_reindex t).symm

namespace EnvelopeAssembly
open Filter Finset Real Conjectures.Goldbach.EstermannAlmostAllPolylog_aux
open scoped Topology BigOperators Classical
noncomputable section

private theorem scaled (M : ℕ → ℝ) (hM : Tendsto (fun t => M t / Real.log (t:ℝ)) atTop (𝓝 1))
    (f : ℕ → ℕ) (ft : Tendsto f atTop atTop)
    (scale : Tendsto (fun N => Real.log (f N:ℝ)/Y N) atTop (𝓝 1)) :
    Tendsto (fun N => M (f N)/Y N) atTop (𝓝 1) := by
  have prod := (hM.comp ft).mul scale
  rw [one_mul] at prod
  apply prod.congr'
  filter_upwards [(tendsto_atTop.1 ft) 2] with N hn
  have hl : Real.log (f N:ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast (show 1 < f N by omega))).ne'
  change M (f N) / Real.log (f N:ℝ) * (Real.log (f N:ℝ)/Y N) = M (f N)/Y N
  rw [div_mul_div_comm, mul_comm (Real.log (f N:ℝ)) (Y N)]
  exact mul_div_mul_right _ _ hl

private theorem selected : ∀ᶠ N : ℕ in atTop, ∃ m ∈ inside N,
      2*EnvelopeComparison.mass (B N/16) - EnvelopeComparison.mass (B N) ≤ SharpAssembly.row (B N) m := by
  filter_upwards [EnvelopePrimorial.eventual_target] with N target
  obtain ⟨m,low,high,bl,bh,even,div⟩ := target
  refine ⟨m,mem_filter.mpr ⟨mem_Icc.mpr ⟨low,high⟩,bl,bh,even⟩,?_⟩
  exact EnvelopeComparison.lower (Nat.div_le_self ..) (fun _ qs sq => EnvelopePrimorial.squarefree_dvd sq qs div)

theorem conclusion (hM : Tendsto (fun t => EnvelopeComparison.mass t / Real.log (t:ℝ)) atTop (𝓝 1)) :
    ∀ ε : ℝ, 0 < ε → ∃ T : ℕ, ∀ N ≥ T,
      (∀ m ∈ inside N, actual N m/length N m ≤ (1+ε)*Y N) ∧
      (∃ m ∈ inside N, (1-ε)*Y N ≤ actual N m/length N m) :=
  result EnvelopeComparison.mass EnvelopeComparison.upper selected
    (scaled _ hM _ EnvelopeScales.B_top EnvelopeScales.B_ratio)
    (scaled _ hM _ EnvelopeScales.S_top EnvelopeScales.S_ratio)

end
end EnvelopeAssembly

theorem Conjectures.Goldbach.ReflectedUpperEnvelope : (by
  classical
  let e := fun t : ℝ => Complex.exp (((2*Real.pi*t : ℝ) : ℂ)*Complex.I)
  let S := fun (N : ℕ) (t : ℝ) => ∑ p ∈ (Finset.range (N+1)).filter Nat.Prime, (Real.log (p : ℝ) : ℂ) * e ((p : ℝ)*t)
  let arcs := fun N : ℕ => let k := Nat.log 2 (N+2); {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ k ∧ a ≤ q ∧ Nat.Coprime a q ∧ |t-(a : ℝ)/(q : ℝ)| ≤ ((k^3 : ℕ) : ℝ)/((q : ℝ)*(N : ℝ))}
  let A := fun N m : ℕ => (intervalIntegral ((arcs N).indicator (fun t : ℝ => (S N t)^2 * e (-(m : ℝ)*t))) (0 : ℝ) 1 MeasureTheory.volume).re
  let C₂ := ∏' p : ℕ, if Nat.Prime p ∧ 2 < p then 1 - 1/((p : ℝ)-1)^2 else 1
  let band := fun N m : ℕ => 4*N ≤ 3*m ∧ 2*m ≤ 3*N ∧ Even m
  let R := fun N m : ℕ => A N m / (2*(N:ℝ)-(m:ℝ))
  let B := fun N : ℕ => (Finset.Icc N (2*N)).filter (band N)
  exact ∀ ε : ℝ, 0 < ε → ∃ T : ℕ, ∀ N : ℕ, T ≤ N →
    (∀ m ∈ B N, R N m ≤ (1+ε)*Real.log (Real.log (N:ℝ))) ∧
    (∃ m ∈ B N, (1-ε)*Real.log (Real.log (N:ℝ)) ≤ R N m)) := by
  classical
  dsimp only
  simpa only [EnvelopeAssembly.inside, Finset.mem_filter, Finset.mem_Icc, SharpAssembly.band, EnvelopeAssembly.actual, EnvelopeAssembly.B,
    EnvelopeAssembly.length, EnvelopeAssembly.Y, GoldbachBa08Approx.coefficient, GoldbachBa08Approx.arcs,
    Conjectures.Goldbach.EstermannAlmostAllPolylog_aux.GoldbachBlockGeometry.width,
    GoldbachBa08Approx.primeSum_eq, Conjectures.Goldbach.EstermannAlmostAllPolylog_aux.GoldbachMajorArc.phase]
    using EnvelopeAssembly.conclusion envelopeMassLimit
