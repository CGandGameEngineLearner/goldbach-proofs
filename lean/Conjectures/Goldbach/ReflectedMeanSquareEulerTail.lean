import Mathlib
import Conjectures.Cuts.Taskba08eb3c3998330911d98843

/- The major-arc transfer used below is from Goldbach PR #4275. The underlying approximation is the verified module in #4198. -/

namespace SharpArcTransfer
open Finset Filter MeasureTheory Conjectures.Goldbach.EstermannAlmostAllPolylog_aux
open GoldbachEstermannKernel
noncomputable section

theorem model_tail (N B m:ℕ) (np:0<N) (bp:1≤B) (half:2*B^3≤N) (ml:N ≤ m) (mu:m≤2*N):
    ‖GoldbachBa08Approx.scaledModel N m B (B^3)-
      (((2*N-m:ℕ):ℂ)+1)*∑q∈Icc 1 B,GoldbachMajorArc.coefficient q m‖≤8*(N:ℝ)/B:=by
  let v:ℂ:=((2*N-m:ℕ):ℂ)+1
  let C (q:ℕ):=GoldbachMajorArc.coefficient q m
  let w (q:ℕ):ℝ:=(B:ℝ)^3/((q:ℝ)*N)
  let J (q:ℕ):ℂ:=∫t in -(w q)..w q,twisted N m t
  have br:0<(B:ℝ):=by exact_mod_cast bp
  have nn:0<(N:ℝ):=by exact_mod_cast np
  have each (q:ℕ) (hq:q∈Icc 1 B):‖J q-v‖≤2*(N:ℝ)/((B:ℝ)^2):=by
    have q1:(1:ℝ)≤q:=by exact_mod_cast (mem_Icc.mp hq).1
    have qb:(q:ℝ)≤B:=by exact_mod_cast (mem_Icc.mp hq).2
    have wp:0<w q:=by dsimp [w];positivity
    have wh:w q≤1/2:=by
      dsimp [w];apply (div_le_iff₀ (by positivity)).mpr
      have hh:(2:ℝ)*(B:ℝ)^3≤N:=by exact_mod_cast half
      nlinarith only [hh,mul_le_mul_of_nonneg_right q1 nn.le]
    apply (GoldbachBa08Kernel.norm_twisted_tail_upper N m wp wh ml mu).trans
    calc
      2/w q = 2*((q:ℝ)*N)/(B:ℝ)^3:=by dsimp [w];rw [div_div_eq_mul_div]
      _ ≤ 2*((B:ℝ)*N)/(B:ℝ)^3:=by gcongr
      _ = _:=by field_simp
  have shape:GoldbachBa08Approx.scaledModel N m B (B^3)=∑q∈Icc 1 B,C q*J q:=by
    simp only [GoldbachBa08Approx.scaledModel,GoldbachBlockGeometry.width,Nat.cast_pow,C,J,w]
  rw [shape]
  change ‖(∑q∈Icc 1 B,C q*J q)-v*∑q∈Icc 1 B,C q‖≤_
  rw [mul_sum,←sum_sub_distrib]
  apply (norm_sum_le ..).trans
  calc
    _ ≤ ∑q∈Icc 1 B,‖C q‖*(2*(N:ℝ)/(B:ℝ)^2):=by
      apply sum_le_sum;intro q hq
      rw [show C q*J q-v*C q=C q*(J q-v) by ring,norm_mul]
      exact mul_le_mul_of_nonneg_left (each q hq) (norm_nonneg _)
    _ = (∑q∈Icc 1 B,‖C q‖)*(2*(N:ℝ)/(B:ℝ)^2):=by rw [sum_mul]
    _ ≤ (4*(B:ℝ))*(2*(N:ℝ)/(B:ℝ)^2):=by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact (GoldbachMajorArc.sum_norm_coefficient_le_sqrt B m).trans
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_self_iff.mpr (Or.inr (by exact_mod_cast bp))) (by norm_num))
    _ = _:=by field_simp;ring

theorem transfer (ε:ℝ) (he:0<ε) :
    ∀ᶠ N:ℕ in atTop,∀m:ℕ,N ≤ m → m≤2*N →
    let B:=Nat.log 2 (N+2)
    ‖GoldbachBa08Approx.coefficient N m B (B^3)-(((2*N-m:ℕ):ℂ)+1)*
      ∑q∈Icc 1 B,GoldbachMajorArc.coefficient q m‖≤ε*N:=by
  let k:ℕ:=⌈16/ε⌉₊
  filter_upwards [GoldbachBa08Approx.eventually_approx (show 0<ε/2 by positivity),
    GoldbachBa08Approx.eventually_geometry,eventually_ge_atTop (2^k),eventually_ge_atTop (1:ℕ)] with N approx geom huge np
  intro m ml mu B
  obtain ⟨bp,_,sep⟩:=geom
  have half:2*B^3≤N:=by
    have one:1≤B^3:=Nat.one_le_pow 3 B bp
    nlinarith only [Nat.mul_le_mul_left (2*B^3) one,sep]
  have top:16/ε≤(B:ℝ):=(Nat.le_ceil _).trans (Nat.cast_le.mpr
    (Nat.le_log_of_pow_le (by decide : 1<2) (huge.trans (Nat.le_add_right N 2))))
  have bpos:0<(B:ℝ):=by exact_mod_cast bp
  have scalar:8/(B:ℝ)≤ε/2:=by
    apply (div_le_iff₀ bpos).mpr
    have :=(div_le_iff₀ he).mp top
    linarith only [this]
  apply (norm_sub_le_norm_sub_add_norm_sub _ (GoldbachBa08Approx.scaledModel N m B (B^3)) _).trans
  apply (add_le_add (approx m) (model_tail N B m np bp half ml mu)).trans
  have right:8*(N:ℝ)/B≤ε/2*N:=by rw [show 8*(N:ℝ)/B=(8/(B:ℝ))*N by ring];exact mul_le_mul_of_nonneg_right scalar (Nat.cast_nonneg _)
  linarith only [right]

end
end SharpArcTransfer

namespace SharpAssembly
open Finset Conjectures.Goldbach.EstermannAlmostAllPolylog_aux
noncomputable def row (L m : ℕ) : ℝ := ∑ q ∈ Icc 1 L, (GoldbachMajorArc.coefficient q m).re
def band (N m : ℕ) : Prop := 4*N ≤ 3*m ∧ 2*m ≤ 3*N ∧ Even m
end SharpAssembly

open Finset
namespace ProgressionWindow

def window (d a x H:ℕ) := (Icc x (x+H)).filter (fun m=>Even m ∧ m % d=a)

private theorem next_residue {P r:ℕ} (pp:0<P) (rp:r<P) (x:ℕ) :
    ∃b:ℕ, x≤b ∧ b<x+P ∧ b % P=r := by
  let u:=P*(x/P)+r
  have ua : u % P=r :=by simp [u,Nat.add_mod,Nat.mod_eq_of_lt rp]
  have xm:=Nat.div_add_mod x P
  have rem:=Nat.mod_lt x pp
  by_cases good:x≤u
  · exact ⟨u,good,by dsimp [u];omega,ua⟩
  · exact ⟨u+P,by dsimp [u];omega,by omega,by simpa using ua⟩

private theorem one_class {P r b x H:ℕ} (pp:0<P) (xl:x≤b) (bx:b<x+P) (br:b % P=r) :
    let T := (Icc x (x+H)).filter (fun m=>m % P=r)
    H≤P*(T.card+1) ∧ T=(range T.card).image (fun t=>b+P*t) := by
  intro T
  let K:=if b≤x+H then (x+H-b)/P+1 else 0
  have image : T=(range K).image (fun t=>b+P*t) := by
    ext m
    simp only [T,mem_filter,mem_Icc,mem_image,mem_range]
    constructor
    · rintro ⟨⟨xm,mH⟩,mr⟩
      have eq:m≡b [MOD P]:=mr.trans br.symm
      have bm:b ≤ m:=by
        by_contra! lt
        have dv: P∣b-m := (Nat.modEq_iff_dvd' lt.le).mp eq
        have lower:=Nat.le_of_dvd (by omega : 0<b-m) dv
        omega
      have good:b≤x+H:=bm.trans mH
      have div:P∣m-b:=(Nat.modEq_iff_dvd' bm).mp eq.symm
      refine ⟨(m-b)/P,?_,?_⟩
      · dsimp only [K];rw [ite_eq_left good];exact Nat.lt_succ_of_le (Nat.div_le_div_right (by omega))
      · have prod:=Nat.mul_div_cancel' div;omega
    · rintro ⟨t,ht,rfl⟩
      have good:b≤x+H:=by by_contra hn;simp [K,hn] at ht
      have le:t≤(x+H-b)/P:=by simpa [K,good] using ht
      have bound: t*P ≤ x+H-b := (Nat.le_div_iff_mul_le pp).mp le
      rw [mul_comm t P] at bound
      exact ⟨⟨by omega,by omega⟩,by simpa [Nat.add_mod] using br⟩
  have card:T.card=K:=by
    rw [image,card_image_of_injective _ (fun i j eq=>Nat.eq_of_mul_eq_mul_left pp (Nat.add_left_cancel eq)),card_range]
  rw [card]
  refine ⟨?_,image⟩
  by_cases good:b≤x+H
  · have dx:=Nat.div_add_mod (x+H-b) P
    have rem:=Nat.mod_lt (x+H-b) pp
    dsimp only [K];rw [ite_eq_left good,Nat.mul_succ,Nat.mul_succ];omega
  · dsimp only [K];rw [ite_eq_right good];simp;omega

theorem enumerate {d a:ℕ} (od:Odd d) (ad:a<d) (x H:ℕ) :
    ∃ b:ℕ, x≤b ∧ b<x+2*d ∧ Even b ∧ b % d=a ∧
      H≤2*d*((window d a x H).card+1) ∧
      window d a x H=(range (window d a x H).card).image (fun t=>b+2*d*t) := by
  let r:=if Even a then a else a+d
  have dp:0<d:=by omega
  have Pp:0<2*d:=by omega
  have rp:r<2*d:=by dsimp [r];split <;> omega
  have ra:r % d=a:=by dsimp [r];split <;> simp [Nat.mod_eq_of_lt ad]
  have ev:Even r:=by
    dsimp [r];split
    · assumption
    · rename_i h;exact (Nat.not_even_iff_odd.mp h).add_odd od
  have equiv (m:ℕ): Even m ∧ m % d=a ↔ m % (2*d)=r := by
    have er := (even_iff_two_dvd.mp ev).modEq_zero_nat
    constructor
    · rintro ⟨em,md⟩
      have m2: m≡r [MOD 2] := (even_iff_two_dvd.mp em).modEq_zero_nat.trans er.symm
      have md':m≡r [MOD d]:=md.trans ra.symm
      have all := Nat.mod_lcm m2 md'
      rw [od.coprime_two_left.lcm_eq_mul] at all
      exact (show m % (2*d)=r % (2*d) from all).trans (Nat.mod_eq_of_lt rp)
    · intro mr
      have all:m≡r [MOD 2*d]:=mr.trans (Nat.mod_eq_of_lt rp).symm
      have m2:=all.of_dvd (dvd_mul_right 2 d)
      have md:=all.of_dvd (dvd_mul_left d 2)
      exact ⟨even_iff_two_dvd.mpr (Nat.modEq_zero_iff_dvd.mp (m2.trans er)),(show m % d=r % d from md).trans ra⟩
  obtain ⟨b,xl,bx,br⟩:=next_residue Pp rp x
  have shape:window d a x H=(Icc x (x+H)).filter (fun m=>m % (2*d)=r) :=by
    unfold window;exact filter_congr fun m _=>equiv m
  have bcond:=(equiv b).mpr br
  refine ⟨b,xl,bx,bcond.1,bcond.2,?_⟩
  rw [shape]
  exact one_class Pp xl bx br

theorem sum_of_image {M:Type*} [AddCommMonoid M] {d a x H b:ℕ} (dp:0<d)
    (im:window d a x H=(range (window d a x H).card).image (fun t=>b+2*d*t)) (f:ℕ→M) :
    (∑m∈window d a x H,f m) = ∑t∈range (window d a x H).card,f (b+2*d*t) := by
  conv_lhs => rw [im]
  exact sum_image (fun i _ j _ eq=>Nat.eq_of_mul_eq_mul_left (by omega : 0<2*d) (Nat.add_left_cancel eq))

end ProgressionWindow

open Filter
open scoped Topology
namespace ProgressionScales
def cutoff (N:ℕ) := Nat.log 2 (N+2)

private theorem log_cap {N:ℕ} (hn:2≤N) : (cutoff N:ℝ)≤4*Real.log N := by
  have l2:(1:ℝ)/2≤Real.log 2:=by
    have h:=Real.one_sub_inv_le_log_of_pos (x:=2) (by norm_num)
    norm_num at h;linarith
  have n2:(2:ℝ)≤N:=by exact_mod_cast hn
  have q:(2:ℝ)^(cutoff N)≤(N:ℝ)+2:=by
    exact_mod_cast Nat.pow_log_le_self 2 (by omega : N+2≠0)
  have add:(N:ℝ)+2≤(N:ℝ)^2:=by nlinarith only [sq_nonneg ((N:ℝ)-2),n2]
  have v:=Real.log_le_log (by positivity : 0<(2:ℝ)^(cutoff N)) (q.trans add)
  rw [Real.log_pow,Real.log_pow] at v
  have nn:0≤(cutoff N:ℝ):=Nat.cast_nonneg _
  norm_num at v
  nlinarith only [mul_le_mul_of_nonneg_left l2 nn,v]

theorem polylog_small (k:ℕ) (θ ε:ℝ) (ht:0<θ) (ep:0<ε) :
    ∀ᶠ N:ℕ in atTop,(cutoff N:ℝ)^k ≤ ε*(N:ℝ)^θ := by
  have little := (isLittleO_log_rpow_rpow_atTop (k:ℝ) ht).comp_tendsto tendsto_natCast_atTop_atTop
  have c:0<ε/(4:ℝ)^k:=by positivity
  filter_upwards [little.bound c,eventually_ge_atTop (2:ℕ)] with N sm hn
  change ‖Real.log (N:ℝ)^(k:ℝ)‖≤(ε/4^k)*‖(N:ℝ)^θ‖ at sm
  have lg:0≤Real.log (N:ℝ):=Real.log_nonneg (by exact_mod_cast (show 1≤N by omega))
  have ex:0≤(N:ℝ)^θ:=Real.rpow_nonneg (Nat.cast_nonneg _) _
  rw [Real.rpow_natCast,Real.norm_of_nonneg (pow_nonneg lg _),Real.norm_of_nonneg ex] at sm
  apply (pow_le_pow_left₀ (Nat.cast_nonneg _) (log_cap hn) k).trans
  rw [mul_pow]
  exact (mul_le_mul_of_nonneg_left sm (by positivity : 0≤(4:ℝ)^k)).trans_eq (by field_simp)

theorem scales (d:ℕ) (ε θ:ℝ) (ep:0<ε) (ht:0<θ):
    ∀ᶠ N:ℕ in atTop, 2*d≤cutoff N ∧ (cutoff N:ℝ)/(N:ℝ)≤ε ∧
      ∀H K:ℕ,(N:ℝ)^θ≤H → H≤2*d*(K+1) → 0<K ∧ (cutoff N:ℝ)^2≤ε*K := by
  have divp:0<ε/(4*((d:ℝ)+1)):=by positivity
  have growth:Tendsto (fun N:ℕ=>(N:ℝ)^θ) atTop atTop:=(tendsto_rpow_atTop ht).comp tendsto_natCast_atTop_atTop
  filter_upwards [polylog_small 2 θ _ ht divp,polylog_small 1 1 ε (by norm_num) ep,
    growth.eventually (eventually_gt_atTop (2*(d:ℝ))),eventually_ge_atTop (2^(2*d):ℕ),eventually_ge_atTop (1:ℕ)] with N sq lin large ltN np
  have dcut:2*d≤cutoff N:=Nat.le_log_of_pow_le (by decide) (ltN.trans (by omega))
  have nn:0<(N:ℝ):=by exact_mod_cast np
  have a: (cutoff N:ℝ)/(N:ℝ)≤ε:=by
    apply (div_le_iff₀ nn).mpr
    simpa only [pow_one,Real.rpow_one] using lin
  refine ⟨dcut,a,?_⟩
  intro H K hH hK
  have up:(H:ℝ)≤2*(d:ℝ)*((K:ℝ)+1):=by exact_mod_cast hK
  have kp:0<K:=by
    by_contra! z;have e:K=0:=by omega
    rw [e] at up;push_cast at up
    linarith only [large,hH,up]
  have kk:(1:ℝ)≤K:=by exact_mod_cast kp
  have nnk:0≤(K:ℝ):=Nat.cast_nonneg _
  have sz:(N:ℝ)^θ ≤ (4*((d:ℝ)+1))*K:=by
    apply hH.trans (up.trans _)
    nlinarith only [mul_le_mul_of_nonneg_left kk (Nat.cast_nonneg d),nnk]
  refine ⟨kp,sq.trans <| (mul_le_mul_of_nonneg_left sz divp.le).trans_eq ?_⟩
  have hnzero: 4*((d:ℝ)+1)≠0:=by positivity
  field_simp

end ProgressionScales

open Finset
namespace ProgressionLocal
open Conjectures.Goldbach.EstermannAlmostAllPolylog_aux.GoldbachMajorArc
open ArithmeticFunction
noncomputable section

private def c (b:ℕ) : ArithmeticFunction ℝ := ⟨fun q=>(coefficient q b).re, by simp [coefficient]⟩
private theorem cmult (b:ℕ) : (c b).IsMultiplicative := by
  apply ArithmeticFunction.IsMultiplicative.iff_ne_zero.mpr
  refine ⟨by simp [c,coefficient_one],?_⟩
  intro q r hq hr sep
  change (coefficient (q*r) b).re=_
  simp only [coefficient_mul (Nat.pos_of_ne_zero hq) (Nat.pos_of_ne_zero hr) sep,Complex.mul_re,
    coefficient_im_zero b (Nat.pos_of_ne_zero hq),zero_mul,sub_zero]
  rfl

private def F (b:ℕ) : ArithmeticFunction ℝ := (c b)*(ArithmeticFunction.zeta:ArithmeticFunction ℝ)
private theorem Fmult (b:ℕ) :(F b).IsMultiplicative := (cmult b).mul isMultiplicative_zeta.natCast
private theorem F_eq (b q:ℕ) : F b q=∑d∈q.divisors,(coefficient d b).re := coe_mul_zeta_apply
private theorem F_pow (b:ℕ) {p:ℕ} (hp:p.Prime) (k:ℕ) :
    F b (p^(k+1))=1+localCoefficient p b := by
  rw [F_eq,Nat.sum_divisors_prime_pow hp,sum_range_succ',sum_range_succ']
  simp only [Nat.add_assoc,Nat.reduceAdd,coefficient_higher_power hp,Complex.zero_re,sum_const_zero,zero_add,pow_zero,pow_one,coefficient_one,Complex.one_re,coefficient_prime hp,Complex.ofReal_re]
  ring

theorem divisor_product (b:ℕ) {q:ℕ} (hq:q≠0) :
    ∑d∈q.divisors,(coefficient d b).re=∏p∈q.primeFactors,(1+localCoefficient p b) := by
  rw [←F_eq,(Fmult b).multiplicative_factorization (F b) hq]
  apply prod_congr rfl;intro p hp
  have pos:0<q.factorization p:=Finsupp.mem_support_iff.mp hp |> Nat.pos_of_ne_zero
  obtain ⟨k,hk⟩:=Nat.exists_eq_succ_of_ne_zero pos.ne'
  exact hk ▸ F_pow b (p:=p) (Nat.prime_of_mem_primeFactors hp) k

private theorem prime_dvd_residue {p d a b:ℕ} (pd:p∣d) (hb:b % d=a) : p∣b ↔ p∣a := by
  rw [←hb,Nat.dvd_iff_mod_eq_zero,Nat.dvd_iff_mod_eq_zero,Nat.mod_mod_of_dvd _ pd]

def localRatio (p a:ℕ) : ℝ :=
  (if p∣a then 1+1/((p:ℝ)-2) else 1)/(1+1/((p:ℝ)*((p:ℝ)-2)))

private theorem ratio_eq {p d a b:ℕ} (gt:2<p) (pd:p∣d) (hb:b % d=a) :
    1+localCoefficient p b=localRatio p a := by
  have eq:=prime_dvd_residue pd hb
  have rp:2<(p:ℝ):=by exact_mod_cast gt
  have p0:(p:ℝ)≠0:=by linarith
  have p1:(p:ℝ)-1≠0:=by linarith
  have p2:(p:ℝ)-2≠0:=by linarith
  have D:0<(p:ℝ)*(p-2)+1:=by positivity
  by_cases h:p∣a <;>simp only [localCoefficient,localRatio,eq,h,ite_true,ite_false] <;> field_simp <;> ring

theorem fixed_sum {d a b:ℕ} (hd:Odd d) (hb:Even b) (res:b % d=a) :
    ∑q∈(2*d).divisors,(coefficient q b).re =
      2*∏p∈d.primeFactors,((if p∣a then 1+1/((p:ℝ)-2) else 1)/(1+1/((p:ℝ)*((p:ℝ)-2)))) := by
  have dz:d≠0:=by obtain ⟨k,h⟩:=hd;omega
  have nt:2∉d.primeFactors:=fun h => by
    obtain ⟨k,hk⟩:=hd
    have dv:=Nat.dvd_of_mem_primeFactors h
    omega
  rw [divisor_product b (Nat.mul_ne_zero (by decide) dz),Nat.primeFactors_mul (by decide : 2≠0) dz,
    Nat.prime_two.primeFactors,singleton_union,prod_insert nt]
  have two:1+localCoefficient 2 b=2:=by norm_num [localCoefficient,even_iff_two_dvd.mp hb]
  rw [two]
  congr 1;apply prod_congr rfl;intro p hp
  have pr:=Nat.prime_of_mem_primeFactors hp
  have gt:2<p:=by have h:=pr.two_le;have : p≠2:=fun e=>nt (e ▸ hp);omega
  exact ratio_eq gt (Nat.dvd_of_mem_primeFactors hp) res

private theorem coeff_eq {q b c:ℕ} (matchD:∀p,p.Prime → p∣q → (p∣b ↔ p∣c)) :
    coefficient q b=coefficient q c := by
  induction q using Nat.recOnPosPrimePosCoprime with
  | zero => simp [coefficient]
  | one => simp [coefficient_one]
  | prime_pow p k hp hk =>
    rcases k with _|_|k
    · omega
    · rw [pow_one] at matchD ⊢;rw [coefficient_prime hp,coefficient_prime hp];simp only [localCoefficient,matchD p hp (dvd_refl p)]
    · rw [coefficient_higher_power hp,coefficient_higher_power hp]
  | coprime u v hu hv sep iu iv =>
    simp only [coefficient_mul (by omega : 0<u) (by omega : 0<v) sep]
    rw [iu (fun p pr hit=>matchD p pr (hit.trans (dvd_mul_right ..))),iv (fun p pr hit=>matchD p pr (hit.trans (dvd_mul_left ..)))]

theorem coefficient_residue {q d a b c:ℕ} (qd:q∣2*d) (bb:Even b) (cc:Even c) (br:b % d=a) (cr:c % d=a) :
    coefficient q b=coefficient q c := by
  apply coeff_eq;intro p pr pq
  rcases pr.dvd_mul.mp (pq.trans qd) with two|pd
  · have eq:p=2:=((Nat.dvd_prime Nat.prime_two).mp two).resolve_left pr.ne_one
    subst p;exact iff_of_true (even_iff_two_dvd.mp bb) (even_iff_two_dvd.mp cc)
  · exact (prime_dvd_residue pd br).trans (prime_dvd_residue pd cr).symm

end
end ProgressionLocal

namespace ProgressionZero
open Finset Conjectures.Goldbach.EstermannAlmostAllPolylog_aux.GoldbachMajorArc
open scoped ComplexConjugate
noncomputable section

private theorem phase_add (x y:ℝ): phase (x+y)=phase x*phase y := by
  unfold phase
  rw [←Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem phase_mul_nat (x:ℝ) (k:ℕ) : phase ((k:ℝ)*x)=phase x^k := by
  unfold phase
  rw [←Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

private theorem phase_nat (k : ℕ) : phase (k : ℝ) = 1 := by
  unfold phase
  convert Complex.exp_nat_mul_two_pi_mul_I k using 2
  push_cast
  ring

theorem ram_period_mul (q m t : ℕ) (hq : 0 < q) :
    ram q (m + q*t) = ram q m := by
  unfold ram
  apply sum_congr rfl
  intro a ha
  have arg : (((m+q*t:ℕ):ℝ)*a/q) = ((m:ℝ)*a/q) + (t*a:ℕ) := by
    have hqr : (q:ℝ) ≠ 0 := by exact_mod_cast hq.ne'
    push_cast
    field_simp
  rw [arg,phase_add,phase_nat,mul_one]

theorem coefficient_period_mul (q m t : ℕ) (hq : 0 < q) :
    coefficient q (m+q*t) = coefficient q m := by
  unfold coefficient
  rw [ram_period_mul q m t hq]

theorem phase_sum_zero (q c:ℕ) (hq:0<q) (notDvd:¬q∣c) :
    (∑k∈range q,phase (((c*k:ℕ):ℝ)/q))=0 := by
  let z:ℂ:=phase ((c:ℝ)/q)
  have zform:z=Complex.exp (2*Real.pi*Complex.I*(c:ℂ)/(q:ℂ)):=by
    unfold z phase
    congr 1
    push_cast
    ring
  have zne:z≠1:=by
    intro eq
    apply notDvd
    exact (Complex.exp_two_pi_mul_I_mul_div_eq_one_iff hq.ne').mp (zform ▸ eq)
  have zpow:z^q=1:=by
    rw [zform,←Complex.exp_nat_mul]
    have expEq:(q:ℂ)*(2*Real.pi*Complex.I*(c:ℂ)/(q:ℂ))=
        (c:ℂ)*(2*Real.pi*Complex.I):=by
      field_simp [Nat.cast_ne_zero.mpr hq.ne']
    rw [expEq]
    simpa only [Int.cast_natCast] using Complex.exp_int_mul_two_pi_mul_I (c:ℤ)
  have each (k:ℕ):phase (((c*k:ℕ):ℝ)/q)=z^k:=by
    have arg:(((c*k:ℕ):ℝ)/q)=(k:ℝ)*((c:ℝ)/q):=by push_cast;ring
    rw [arg,phase_mul_nat]
  simp_rw [each]
  have geom:=geom_sum_mul z q
  rw [zpow,sub_self] at geom
  exact (mul_eq_zero.mp geom).resolve_right (sub_ne_zero.mpr zne)

theorem ram_sum_zero (q b D:ℕ) (hq:0<q) (hD:¬q∣D) :
    (∑k∈range q,ram q (b+D*k))=0 := by
  change (∑k∈range q,∑a∈(range q).filter (fun a=>a.Coprime q),
    phase (((b+D*k:ℕ):ℝ)*a/q))=0
  rw [sum_comm]
  apply sum_eq_zero
  intro a ha
  have cop:a.Coprime q:=(mem_filter.mp ha).2
  have ndiv:¬q∣D*a:=by
    intro v
    exact hD (cop.symm.dvd_of_dvd_mul_left (by simpa only [mul_comm] using v))
  have each (k:ℕ):phase (((b+D*k:ℕ):ℝ)*a/q)=
      phase (((b*a:ℕ):ℝ)/q)*phase (((D*a*k:ℕ):ℝ)/q):=by
    rw [←phase_add]
    congr 1
    push_cast
    ring
  simp_rw [each]
  rw [←mul_sum,phase_sum_zero q (D*a) hq ndiv,mul_zero]

theorem coefficient_sum_zero (q b D:ℕ) (hq:0<q) (hD:¬q∣D) :
    (∑k∈range q,coefficient q (b+D*k))=0 := by
  have hsum := ram_sum_zero q b D hq hD
  have hconj : (∑ k ∈ range q, conj (ram q (b + D * k))) = 0 := by
    simpa only [map_sum, map_zero] using congrArg conj hsum
  unfold coefficient
  rw [← Finset.mul_sum]
  exact mul_eq_zero_of_right _ hconj

end
end ProgressionZero

open Finset Filter Conjectures.Goldbach.EstermannAlmostAllPolylog_aux
open scoped Classical
namespace ProgressionSums
open GoldbachMajorArc
noncomputable section

theorem coefficient_norm (q m : ℕ) (hq : 0 < q) : ‖coefficient q m‖ ≤ 1 := by
  induction q using Nat.recOnPosPrimePosCoprime with
  | zero => omega
  | one => simp [coefficient_one]
  | prime_pow p k hp hk =>
    cases k with
    | zero => simp [coefficient_one]
    | succ k =>
      cases k with
      | zero =>
        simp only [zero_add,pow_one,coefficient_prime hp m, Complex.norm_real,Real.norm_eq_abs]
        have two : (2:ℝ)≤p := by exact_mod_cast hp.two_le
        have base : 0 < (p:ℝ)-1 := by linarith
        unfold localCoefficient
        split
        · rw [abs_of_nonneg (by positivity)]
          exact (div_le_one (by linarith)).mpr (by linarith)
        · rw [abs_neg,abs_of_nonneg (by positivity)]
          exact (div_le_one (by positivity)).mpr (by nlinarith [sq_nonneg ((p:ℝ)-2)])
      | succ k => simp [coefficient_higher_power hp]
  | coprime a b ha hb cp ia ib =>
    rw [coefficient_mul (by omega) (by omega) cp,norm_mul]
    simpa using mul_le_mul (ia (by omega)) (ib (by omega)) (norm_nonneg _) zero_le_one

end
end ProgressionSums

open Finset Filter
open Conjectures.Goldbach.EstermannAlmostAllPolylog_aux
namespace ProgressionTransfer

private theorem scalar {ε X w:ℝ} (A C:ℂ) (he:0<ε) (wp:0<w) (half:X≤2*w)
    (approx:‖A-((w:ℂ)+1)*C‖≤ε/4*X) (small:‖C‖≤ε/4*X) : |A.re/w-C.re|≤ε := by
  have err := (Complex.abs_re_le_norm (A-((w:ℂ)+1)*C)).trans approx
  simp only [Complex.sub_re,Complex.mul_re,Complex.add_re,Complex.ofReal_re,Complex.one_re,
    Complex.add_im,Complex.ofReal_im,Complex.one_im,zero_add,zero_mul,sub_zero] at err
  have cr := (Complex.abs_re_le_norm C).trans small
  rw [show A.re/w-C.re=(A.re-(w+1)*C.re+C.re)/w by field_simp;ring,abs_div,abs_of_pos wp]
  apply (div_le_iff₀ wp).mpr
  apply (abs_add_le ..).trans
  linarith only [err,cr,mul_le_mul_of_nonneg_left half he.le]

private theorem sqrt_small {ε b x:ℝ} (he:0<ε) (h:32/ε≤Real.sqrt x)
    (bb:0≤b) (bx:b≤x+2) (xx:2≤x) : 4*Real.sqrt b≤ε/4*x := by
  have sq : Real.sqrt b≤2*Real.sqrt x := by
    nlinarith only [Real.sq_sqrt bb,Real.sq_sqrt (by linarith : 0≤x),bx,xx,Real.sqrt_nonneg x,Real.sqrt_nonneg b]
  have e:32≤Real.sqrt x*ε := (div_le_iff₀ he).mp h
  have e':=mul_le_mul_of_nonneg_left e (Real.sqrt_nonneg x)
  rw [←mul_assoc,←pow_two,Real.sq_sqrt (by linarith : 0≤x)] at e'
  linarith only [sq,e']

theorem normalized (ε:ℝ) (he:0<ε) : ∀ᶠ N:ℕ in atTop, ∀ m:ℕ,
    4*N≤3*m → 2*m≤3*N →
    let B:=Nat.log 2 (N+2)
    |(GoldbachBa08Approx.coefficient N m B (B^3)).re/((2*N-m:ℕ):ℝ) - SharpAssembly.row B m|≤ε := by
  have big : ∀ᶠ N:ℕ in atTop,32/ε≤Real.sqrt (N:ℝ) :=
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  filter_upwards [SharpArcTransfer.transfer (ε/4) (by positivity),big,eventually_ge_atTop (2:ℕ)] with N trans hn nlo
  intro m lo hi B
  have ml:N≤ m:=by omega
  have mu:m≤2*N:=by omega
  have wp:(0:ℝ)<((2*N-m:ℕ):ℝ):=by exact_mod_cast (show 0<2*N-m by omega)
  have half:(N:ℝ)≤2*((2*N-m:ℕ):ℝ):=by exact_mod_cast (show N≤2*(2*N-m) by omega)
  have cre : SharpAssembly.row B m = (∑q∈Icc 1 B,GoldbachMajorArc.coefficient q m).re := by simp only [SharpAssembly.row,Complex.re_sum]
  rw [cre]
  apply scalar _ _ he wp half
  · simpa only [Complex.ofReal_natCast] using trans m ml mu
  · apply (norm_sum_le ..).trans
    apply (GoldbachMajorArc.sum_norm_coefficient_le_sqrt B m).trans
    exact sqrt_small he hn (Nat.cast_nonneg _) (by exact_mod_cast Nat.log_le_self 2 (N+2)) (by exact_mod_cast nlo)

end ProgressionTransfer

open Finset Filter
namespace MeanSquareEulerBounds
noncomputable section
open scoped Classical Topology

def w (p:ℕ) : ℝ := 1/((p:ℝ)-1)^3
def u (p:ℕ) : ℝ := 1/((p:ℝ)-1)^2

private theorem tele (f:ℕ→ℝ) (y k:ℕ) :
    ∑p∈Ioc y (y+k),(f (p-1)-f p)=f y-f (y+k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.add_succ,sum_Ioc_succ_top (by omega : y≤y+k),ih,Nat.succ_sub_one];ring

private theorem telescope_bound {a f:ℕ→ℝ} {y:ℕ} (s:Finset ℕ)
    (support:∀p∈s,y<p) (pos:∀p,0≤f p)
    (step:∀p,y<p→0≤f (p-1)-f p ∧ a p≤f (p-1)-f p) :
    ∑p∈s,a p≤f y := by
  let M:=s.sup id
  have sub:s⊆Ioc y (y+M):=fun p h=>mem_Ioc.mpr ⟨support p h,(le_sup (f:=id) h).trans (Nat.le_add_left ..)⟩
  apply (sum_le_sum (fun p hp=>(step p (support p hp)).2)).trans
  apply (sum_le_sum_of_subset_of_nonneg sub (fun p hp _=>(step p (mem_Ioc.mp hp).1).1)).trans
  exact (tele f y M).le.trans (sub_le_self _ (pos _))

theorem w_nonneg {p:ℕ} (hp:1≤p) : 0≤w p:=by
  unfold w;exact one_div_nonneg.mpr (pow_nonneg (sub_nonneg.mpr (by exact_mod_cast hp)) _)

theorem sum_w {y:ℕ} (hy:1≤y) (s:Finset ℕ) (high:∀p∈s,y<p) :
    ∑p∈s,w p ≤ 2/(y:ℝ)^2 := by
  apply telescope_bound (f:=fun i=>2/(i:ℝ)^2) s high (fun _=>by positivity)
  intro p h
  have p2:2≤p:=by omega
  have pr:(2:ℝ)≤p:=by exact_mod_cast p2
  have hp:(0:ℝ)<p:=by linarith
  have hp1:(0:ℝ)<p-1:=by linarith
  rw [Nat.cast_sub (by omega : 1≤p),Nat.cast_one]
  have dom : w p≤2/((p:ℝ)-1)^2-2/(p:ℝ)^2 := by
    unfold w;field_simp
    nlinarith only [sq_nonneg ((p:ℝ)-2),pr]
  exact ⟨(w_nonneg (by omega)).trans dom,dom⟩

theorem sum_u {y:ℕ} (hy:1≤y) (s:Finset ℕ) (high:∀p∈s,y<p) :
    ∑p∈s,u p ≤ 2/(y:ℝ) := by
  apply telescope_bound (f:=fun i=>2/(i:ℝ)) s high (fun _=>by positivity)
  intro p h
  have p2:2≤p:=by omega
  have pr:(2:ℝ)≤p:=by exact_mod_cast p2
  have hp:(0:ℝ)<p:=by linarith
  have hp1:(0:ℝ)<p-1:=by linarith
  rw [Nat.cast_sub (by omega : 1≤p),Nat.cast_one]
  have dom:u p≤2/((p:ℝ)-1)-2/(p:ℝ):=by unfold u;field_simp;linarith
  exact ⟨(by unfold u;positivity : 0≤u p).trans dom,dom⟩

private theorem prod_bound (P:Finset ℕ) (ok:∀p∈P,1<p) :
    ∏p∈P,(1+w p) ≤ Real.exp 2 := by
  let g:=fun p=>max 0 (w p)
  have eq {p:ℕ}:p∈P → g p=w p:=fun h=>max_eq_right (w_nonneg (ok _ h).le)
  calc
    _ = ∏p∈P,(1+g p):=prod_congr rfl (fun _ h=>by rw [eq h])
    _ ≤ _:=Real.prod_one_add_le_exp_sum P (fun _=>le_max_left ..)
    _ ≤ _:=Real.exp_le_exp.mpr (by rw [sum_congr rfl (fun p hp=>eq hp)];simpa using sum_w (y:=1) (by decide) P ok)

private theorem sub_products (P:Finset ℕ) (ok:∀p∈P,1<p) (y:ℕ) :
    (∏p∈P,(1+w p))-(∏p∈P.filter (·≤y),(1+w p)) ≤
      (∑p∈P.filter (y<·),w p)*(∏p∈P,(1+w p)) := by
  induction P using Finset.induction_on with
  | empty => simp
  | @insert p P np ih =>
    have h:=ih (fun q hq=>ok q (mem_insert_of_mem hq))
    have pos:=w_nonneg (ok p (mem_insert_self ..)).le
    have total:0≤∏q∈P,(1+w q):=prod_nonneg (fun q hq=>add_nonneg zero_le_one (w_nonneg (ok q (mem_insert_of_mem hq)).le))
    have sumz:0≤∑q∈P.filter (y<·),w q:=sum_nonneg (fun q hq=>w_nonneg (ok q (mem_insert_of_mem (mem_filter.mp hq).1)).le)
    have nf (b:ℕ→Prop) [DecidablePred b]:p∉P.filter b:=fun hh=>np (mem_filter.mp hh).1
    by_cases small:p≤y
    · simp only [filter_insert,small,not_lt_of_ge small,ite_true,ite_false,prod_insert np,prod_insert (nf _)]
      nlinarith only [mul_le_mul_of_nonneg_left h (add_nonneg zero_le_one pos)]
    · simp only [filter_insert,small,lt_of_not_ge small,ite_true,ite_false,prod_insert np,sum_insert (nf _)]
      nlinarith only [h,mul_nonneg (mul_nonneg pos total) sumz,mul_nonneg (sq_nonneg (w p)) total]

private theorem powerset_tail (P:Finset ℕ) (y:ℕ) :
    ∑t∈P.powerset.filter (fun t=>∃p∈t,y<p),(∏p∈t,w p)=
    (∏p∈P,(1+w p))-(∏p∈P.filter (·≤y),(1+w p)) := by
  let lo:=P.filter (·≤y)
  have eq:P.powerset.filter (fun t=>¬∃p∈t,y<p)=lo.powerset:=by
    ext t;simp only [mem_filter,mem_powerset,lo];constructor
    · rintro ⟨ht,no⟩ p hp;exact mem_filter.mpr ⟨ht hp,le_of_not_gt (fun high=>no ⟨p,hp,high⟩)⟩
    · intro ht;exact ⟨fun p hp=>(mem_filter.mp (ht hp)).1,fun ⟨p,hp,high⟩=>high.not_ge (mem_filter.mp (ht hp)).2⟩
  rw [eq_sub_iff_add_eq,Finset.prod_one_add,Finset.prod_one_add,←eq,sum_filter_add_sum_filter_not]

private theorem phi_weight {q:ℕ} (hs:Squarefree q) :
    1/(q.totient:ℝ)^3 = ∏p∈q.primeFactors,w p := by
  have mul:=Nat.totient_mul_prod_primeFactors q
  rw [Nat.prod_primeFactors_of_squarefree hs] at mul
  have val:q.totient=(∏p∈q.primeFactors,(p-1)):=Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hs.ne_zero) (by simpa [mul_comm] using mul)
  rw [val,Nat.cast_prod,←Finset.prod_pow]
  simp only [one_div,←Finset.prod_inv_distrib]
  apply prod_congr rfl;intro p hp
  have pr:=Nat.prime_of_mem_primeFactors hp
  simp [w,Nat.cast_sub pr.one_le]

private theorem image_id (T:Finset ℕ) (sf:∀q∈T,Squarefree q) :
    (∑q∈T,1/(q.totient:ℝ)^3)=∑t∈T.image Nat.primeFactors,∏p∈t,w p := by
  rw [sum_image]
  · exact sum_congr rfl (fun q hq=>phi_weight (sf q hq))
  · intro a ha b hb eq
    rw [←Nat.prod_primeFactors_of_squarefree (sf a ha),←Nat.prod_primeFactors_of_squarefree (sf b hb),eq]

theorem total_sum (T:Finset ℕ) (sf:∀q∈T,Squarefree q) :
    ∑q∈T,1/(q.totient:ℝ)^3 ≤ Real.exp 2 := by
  let P:=T.biUnion Nat.primeFactors
  have good:∀p∈P,1<p:=by intro p hp;obtain ⟨q,_,hq⟩:=mem_biUnion.mp hp;exact (Nat.prime_of_mem_primeFactors hq).one_lt
  have sub:T.image Nat.primeFactors⊆P.powerset:=by
    intro t ht;obtain ⟨q,hq,rfl⟩:=mem_image.mp ht;exact mem_powerset.mpr (fun p hp=>mem_biUnion.mpr ⟨q,hq,hp⟩)
  rw [image_id T sf]
  apply (sum_le_sum_of_subset_of_nonneg sub (fun t ht _=>prod_nonneg (fun p hp=>w_nonneg (good p (mem_powerset.mp ht hp)).le))).trans
  rw [←Finset.prod_one_add];exact prod_bound P good

theorem bad_sum (T:Finset ℕ) {y:ℕ} (hy:1≤y) (sf:∀q∈T,Squarefree q) (bad:∀q∈T,∃p∈q.primeFactors,y<p) :
    ∑q∈T,1/(q.totient:ℝ)^3 ≤ (2*Real.exp 2)/(y:ℝ)^2 := by
  let P:=T.biUnion Nat.primeFactors
  have good:∀p∈P,1<p:=by intro p hp;obtain ⟨q,_,hq⟩:=mem_biUnion.mp hp;exact (Nat.prime_of_mem_primeFactors hq).one_lt
  have sub:T.image Nat.primeFactors⊆P.powerset.filter (fun t=>∃p∈t,y<p):=by
    intro t ht;obtain ⟨q,hq,rfl⟩:=mem_image.mp ht;exact mem_filter.mpr ⟨mem_powerset.mpr (fun p hp=>mem_biUnion.mpr ⟨q,hq,hp⟩),bad q hq⟩
  rw [image_id T sf]
  apply (sum_le_sum_of_subset_of_nonneg sub (fun t ht _=>prod_nonneg (fun p hp=>w_nonneg (good p (mem_powerset.mp (mem_filter.mp ht).1 hp)).le))).trans
  rw [powerset_tail]
  apply (sub_products P good y).trans
  apply (mul_le_mul (sum_w hy _ (fun p h=>(mem_filter.mp h).2)) (prod_bound P good)
    (prod_nonneg (fun p h=>add_nonneg zero_le_one (w_nonneg (good p h).le))) (by positivity)).trans_eq
  ring


def tailWeight (y p:ℕ) : ℝ := if p.Prime ∧ y<p then u p else 0
def alpha (y:ℕ) : ℝ := ∏'p:ℕ,(1-tailWeight y p)
def lowPrimes (y:ℕ) := (range (y+1)).filter (fun p=>p.Prime ∧ 2<p)

private theorem tw_nonneg (y p:ℕ) : 0≤tailWeight y p := by unfold tailWeight u;split_ifs <;>positivity

private theorem tw_sum {y:ℕ} (hy:1≤y) (T:Finset ℕ) :
    (∑p∈T,tailWeight y p)≤2/(y:ℝ):=by
  unfold tailWeight;rw [←sum_filter]
  exact sum_u hy _ (fun p hp=>(mem_filter.mp hp).2.2)

theorem tail_mult {y:ℕ} (hy:1≤y) : Multipliable (fun p=>1-tailWeight y p) := by
  have h:Summable (fun p=>tailWeight y p):=summable_of_sum_le (fun _=>tw_nonneg ..) (tw_sum hy)
  have hab:Summable (fun p=>‖-tailWeight y p‖):=by simp only [norm_neg,Real.norm_eq_abs,abs_of_nonneg (tw_nonneg ..)];exact h
  simpa only [sub_eq_add_neg] using multipliable_one_add_of_summable hab

private theorem product_lower {y:ℕ} (_hy:1≤y) (T:Finset ℕ):
    0≤∏p∈T,(1-tailWeight y p) ∧ (∏p∈T,(1-tailWeight y p))≤1 ∧
    1-(∏p∈T,(1-tailWeight y p))≤∑p∈T,tailWeight y p:=by
  have small (p:ℕ):tailWeight y p≤1 := by
    unfold tailWeight
    split_ifs with h
    · have pr:(2:ℝ)≤p:=by exact_mod_cast h.1.two_le
      unfold u
      apply (div_le_iff₀ (sq_pos_of_pos (by linarith only [pr]))).mpr
      nlinarith only [sq_nonneg ((p:ℝ)-2),pr]
    · norm_num
  induction T using Finset.induction_on with
  | empty => simp
  | @insert p T hp ih =>
    rw [prod_insert hp,sum_insert hp]
    have v:=tw_nonneg y p
    have lc:=small p
    exact ⟨mul_nonneg (by linarith only [lc]) ih.1,
      (mul_le_mul (show 1-tailWeight y p≤1 by linarith only [v]) ih.2.1 ih.1 (by norm_num)).trans_eq (by ring),
      by nlinarith only [ih.2.2,mul_le_mul_of_nonneg_left ih.2.1 v]⟩

theorem alpha_bounds {y:ℕ} (hy:1≤y) :
    0≤alpha y ∧ alpha y≤1 ∧ |1-alpha y|≤2/(y:ℝ) := by
  have lim:Tendsto (fun T:Finset ℕ=>∏p∈T,(1-tailWeight y p)) atTop (𝓝 (alpha y)):=(tail_mult hy).hasProd
  have pos:=ge_of_tendsto' lim (fun T=>(product_lower hy T).1)
  have one:=le_of_tendsto' lim (fun T=>(product_lower hy T).2.1)
  refine ⟨pos,one,?_⟩
  rw [abs_of_nonneg (sub_nonneg.mpr one)]
  exact le_of_tendsto' (tendsto_const_nhds.sub lim) (fun T=>(product_lower hy T).2.2.trans (tw_sum hy T))

theorem factor_C2 {y:ℕ} (hy:2≤y) :
    (∏'p:ℕ, if p.Prime ∧ 2<p then 1-1/((p:ℝ)-1)^2 else 1) =
      (∏p∈lowPrimes y,(1-u p))*alpha y := by
  let P:=lowPrimes y
  let F:=fun p=>if p∈P then 1-u p else 1
  have low:HasProd F (∏p∈P,(1-u p)):=by
    have eq:(∏p∈P,F p)=∏p∈P,(1-u p):=prod_congr rfl (fun p hp=>ite_eq_left hp)
    rw [←eq]
    exact hasProd_prod_of_ne_finset_one (s:=P) (fun p hp=>ite_eq_right hp)
  have high:= (tail_mult (show 1≤y by omega)).hasProd
  have prod:=low.mul high
  change HasProd (fun p:ℕ=>F p*(1-tailWeight y p)) ((∏p∈P,(1-u p))*alpha y) at prod
  have eq:(fun p:ℕ=>F p*(1-tailWeight y p))=(fun p:ℕ=>if p.Prime ∧ 2<p then 1-1/((p:ℝ)-1)^2 else 1):=by
    funext p
    simp only [F,P,lowPrimes,mem_filter,mem_range,Nat.lt_succ_iff,tailWeight,u]
    by_cases pr:p.Prime
    · by_cases cut:p≤y
      · have nh:¬y<p:=Nat.not_lt.mpr cut
        by_cases large:2<p <;>simp [pr,cut,nh,large]
      · have highp:y<p:=lt_of_not_ge cut
        have large:2<p:=hy.trans_lt highp
        simp [pr,cut,highp,large]
    · simp [pr]
  rw [eq] at prod
  exact prod.tprod_eq

end
end MeanSquareEulerBounds

open Finset Filter
namespace MeanSquareGeometry
noncomputable section

def B (N:ℕ) := (Icc N (2*N)).filter (fun m=>4*N≤3*m ∧ 2*m≤3*N ∧ Even m)

theorem geometry {N:ℕ} (hn:100≤N) : ∃ b:ℕ, Even b ∧
    B N=(range (B N).card).image (fun t=>b+2*t) ∧ 0<(B N).card ∧ N≤24*(B N).card := by
  let x:=(4*N+2)/3
  let H:=3*N/2-x
  have eq:B N=ProgressionWindow.window 1 0 x H:=by
    ext m;simp only [B,ProgressionWindow.window,mem_filter,mem_Icc,Nat.mod_one,and_true,x,H]
    constructor
    · rintro ⟨⟨_,_⟩,lo,up,ev⟩
      exact ⟨⟨by omega,by omega⟩,ev⟩
    · rintro ⟨⟨lo,up⟩,ev⟩
      exact ⟨⟨by omega,by omega⟩,by omega,by omega,ev⟩
  obtain ⟨b,_,_,ev,_,hh,imageEq⟩ := ProgressionWindow.enumerate (d:=1) (a:=0) (by decide) (by decide) x H
  rw [←eq] at hh imageEq
  have length:H≤2*((B N).card+1):=by simpa only [Nat.mul_one] using hh
  dsimp only [H,x] at length
  exact ⟨b,ev,by simpa only [Nat.mul_one] using imageEq,by omega,by omega⟩

theorem scales (e:ℝ) (ep:0<e) :
    ∀ᶠ N:ℕ in atTop, ∃b:ℕ, Even b ∧ B N=(range (B N).card).image (fun t=>b+2*t) ∧
      0<(B N).card ∧ N≤24*(B N).card ∧ 8*(ProgressionScales.cutoff N:ℝ)^4 ≤ e*(B N).card := by
  filter_upwards [ProgressionScales.polylog_small 4 1 (e/192) (by norm_num) (by positivity),
    eventually_ge_atTop (100:ℕ)] with N small big
  obtain ⟨b,ev,eq,kp,nk⟩:=geometry big
  have size: (N:ℝ)≤24*((B N).card:ℝ):=by exact_mod_cast nk
  rw [Real.rpow_one] at small
  refine ⟨b,ev,eq,kp,nk,?_⟩
  nlinarith only [small,mul_le_mul_of_nonneg_left size ep.le]

end
end MeanSquareGeometry

open Finset
namespace MeanSquareWindow

private theorem incomplete {P:ℕ} (pp:0<P) (K v:ℕ) (f:ℕ→ℝ)
    (full:∀a:ℕ,(∑t∈range P,f (a+t))=0) (bd:∀t,|f t|≤2) :
    |∑t∈range K,f (v+t)|≤2*P := by
  have block (k:ℕ) : (∑t∈range (P*k),f (v+t))=0 := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.mul_succ,sum_range_add,ih,zero_add]
      simpa only [Nat.add_assoc] using full (v+P*k)
  have split:=sum_range_add (fun t=>f (v+t)) (P*(K/P)) (K % P)
  rw [Nat.div_add_mod,block,zero_add] at split
  rw [split]
  apply (abs_sum_le_sum_abs ..).trans
  calc
    _ ≤ ∑_t∈range (K % P),(2:ℝ):=sum_le_sum fun _ _=>bd _
    _ ≤ _:=by simpa [mul_comm] using mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Nat.mod_lt K pp).le) (by norm_num : (0:ℝ)≤2)

private theorem transpose (T:Finset ℕ) (K:ℕ) (f:ℕ→ℕ→ℕ→ℝ):
    (∑t∈range K,∑q∈T,∑r∈T,f t q r) = ∑q∈T,∑r∈T,∑t∈range K,f t q r:=by
  rw [sum_comm];apply sum_congr rfl;intro q _;rw [sum_comm]

theorem bilinear_error {L:ℕ} (T:Finset ℕ) (sub:T⊆Icc 1 L) (K v:ℕ)
    (w z H:ℕ→ℝ) (c b:ℕ→ℕ→ℝ)
    (hw:∀q∈T,|w q|≤2) (hz:∀q∈T,|z q|≤2) (hH:∀q∈T,|H q|≤1)
    (hc:∀q∈T,∀t,|c q t|≤1) (hb:∀q∈T,∀t,|b q t|≤1)
    (block:∀q∈T,∀r∈T,∀a:ℕ, (∑t∈range (q*r),c q (a+t)*b r (a+t)) =
      ((q*r:ℕ):ℝ)*(if q=r then H q else 0)) :
    |(∑t∈range K,(∑q∈T,w q*c q (v+t))*(∑r∈T,z r*b r (v+t))) -
       K*(∑q∈T,w q*z q*H q)|≤8*(L:ℝ)^4 := by
  let D (q r:ℕ):ℝ:=if q=r then H q else 0
  let U (q r t:ℕ):ℝ:=c q t*b r t-D q r
  have di(q r:ℕ)(hq:q∈T):|D q r|≤1:=by dsimp [D];split;exact hH q hq;norm_num
  have bound (q r:ℕ)(hq:q∈T)(hr:r∈T):
      |∑t∈range K,U q r (v+t)| ≤ 2* ((q*r:ℕ):ℝ) :=by
    have qp:0<q := (mem_Icc.mp (sub hq)).1
    have rp:0<r := (mem_Icc.mp (sub hr)).1
    apply incomplete (Nat.mul_pos qp rp)
    · intro a;dsimp only [U];rw [sum_sub_distrib,block q hq r hr a];simp [D]
    · intro t;apply (abs_sub ..).trans
      rw [abs_mul]
      have p:|c q t| * |b r t|≤1 :=by simpa using mul_le_mul (hc q hq t) (hb r hr t) (abs_nonneg _) zero_le_one
      linarith only [p,di q r hq]
  have exp (t:ℕ) : (∑q∈T,w q*c q t)*(∑r∈T,z r*b r t) =
      ∑q∈T,∑r∈T,w q*z r*(c q t*b r t) :=by
    rw [sum_mul];apply sum_congr rfl;intro q _;rw [mul_sum]
    apply sum_congr rfl;intro r _;ring
  have main : (∑q∈T,w q*z q*H q)=∑q∈T,∑r∈T,w q*z r*D q r :=by
    apply sum_congr rfl;intro q hq;simp [D,mul_ite,hq]
  have eq : (∑t∈range K,(∑q∈T,w q*c q (v+t))*(∑r∈T,z r*b r (v+t))) -
       K*(∑q∈T,w q*z q*H q) = ∑q∈T,∑r∈T,w q*z r*(∑t∈range K,U q r (v+t)) :=by
    calc
      _ = ∑t∈range K, ((∑q∈T,w q*c q (v+t))*(∑r∈T,z r*b r (v+t))-(∑q∈T,w q*z q*H q)) :=by rw [sum_sub_distrib];simp
      _ = ∑t∈range K,∑q∈T,∑r∈T,w q*z r*U q r (v+t) :=by
        apply sum_congr rfl;intro t _
        rw [exp,main,←sum_sub_distrib];apply sum_congr rfl;intro q _
        rw [←sum_sub_distrib];apply sum_congr rfl;intro r _;dsimp [U];ring
      _ = _ :=by rw [transpose];simp_rw [mul_sum]
  rw [eq]
  have card : (T.card:ℝ)≤L:=by exact_mod_cast (card_le_card sub).trans_eq (by simp : (Icc 1 L).card=L)
  apply (abs_sum_le_sum_abs ..).trans
  calc
    _ ≤ ∑_q∈T,∑_r∈T, 8*(L:ℝ)^2 :=by
      apply sum_le_sum;intro q hq;apply (abs_sum_le_sum_abs ..).trans
      apply sum_le_sum;intro r hr
      rw [abs_mul,abs_mul]
      have co : |w q| * |z r|≤4:= (mul_le_mul (hw q hq) (hz r hr) (abs_nonneg _) (by norm_num)).trans_eq (by norm_num)
      have qr:(q:ℝ)*r≤(L:ℝ)^2:=by rw [pow_two];exact_mod_cast Nat.mul_le_mul (mem_Icc.mp (sub hq)).2 (mem_Icc.mp (sub hr)).2
      have bb:=mul_le_mul co (bound q r hq hr) (abs_nonneg _) (by norm_num : (0:ℝ)≤4)
      push_cast at bb
      linarith only [bb,qr]
    _ ≤ _ :=by
      simp only [sum_const,nsmul_eq_mul]
      calc
        _ ≤ (L:ℝ)*(L*(8*(L:ℝ)^2)) :=by gcongr
        _ = _ :=by ring

theorem square_upper {L:ℕ} (T:Finset ℕ) (sub:T⊆Icc 1 L) (K v:ℕ)
    (w H:ℕ→ℝ) (c:ℕ→ℕ→ℝ) (hw:∀q∈T,|w q|≤2) (hH:∀q∈T,|H q|≤1) (hc:∀q∈T,∀t,|c q t|≤1)
    (block:∀q∈T,∀r∈T,∀a:ℕ, (∑t∈range (q*r),c q (a+t)*c r (a+t)) =
      ((q*r:ℕ):ℝ)*(if q=r then H q else 0)) :
    (∑t∈range K,(∑q∈T,w q*c q (v+t))^2) ≤ K*(∑q∈T,(w q)^2*H q)+8*(L:ℝ)^4 := by
  have e:=(abs_le.mp (bilinear_error T sub K v w w H c c hw hw hH hc hc block)).2
  simp only [pow_two];linarith only [e]

theorem square_bound {L:ℕ} (T:Finset ℕ) (sub:T⊆Icc 1 L) (K v:ℕ)
    (w H:ℕ→ℝ) (c:ℕ→ℕ→ℝ) (hw:∀q∈T,|w q|≤2) (hh:∀q∈T,0≤H q) (hH:∀q∈T,|H q|≤1) (hc:∀q∈T,∀t,|c q t|≤1)
    (block:∀q∈T,∀r∈T,∀a:ℕ, (∑t∈range (q*r),c q (a+t)*c r (a+t)) =
      ((q*r:ℕ):ℝ)*(if q=r then H q else 0)) :
    (∑t∈range K,(∑q∈T,w q*c q (v+t))^2) ≤ 4*K*(∑q∈T,H q)+8*(L:ℝ)^4 := by
  apply (square_upper T sub K v w H c hw hH hc block).trans
  apply add_le_add_left
  rw [show 4*(K:ℝ)*(∑q∈T,H q)=K*(∑q∈T,4*H q) by rw [←mul_sum];ring]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply sum_le_sum;intro q hq
  have e:=pow_le_pow_left₀ (abs_nonneg (w q)) (hw q hq) 2
  rw [sq_abs] at e
  exact mul_le_mul_of_nonneg_right (e.trans_eq (by norm_num)) (hh q hq)

end MeanSquareWindow

open Finset
open Conjectures.Goldbach.EstermannAlmostAllPolylog_aux
namespace MeanSquareRows
open GoldbachMajorArc
open scoped Classical
noncomputable section

def c (q m : ℕ) : ℝ := (coefficient q m).re

def odds (L : ℕ) := (Icc 1 L).filter (fun q => Odd q ∧ Squarefree q)

def weight (L q : ℕ) : ℝ := 1 + if 2*q ≤ L then 1 else 0

private theorem noSquare {q : ℕ} (n : ℕ) (hq : 0 < q) (hs : ¬Squarefree q) : c q n = 0 := by
  induction q using Nat.recOnPosPrimePosCoprime with
  | zero => omega
  | one => exact (hs squarefree_one).elim
  | prime_pow p k hp hk =>
    rcases k with _|_|k
    · omega
    · exact (hs (by simpa using hp.squarefree)).elim
    · simp [c,coefficient_higher_power hp]
  | coprime a b ha hb hab ia ib =>
    simp only [c,coefficient_mul (by omega : 0<a) (by omega : 0<b) hab,Complex.mul_re,
      coefficient_im_zero n (by omega : 0<a),zero_mul,sub_zero]
    by_cases h : Squarefree a
    · exact mul_eq_zero_of_right _ (ib (by omega) (fun h' => hs ((Nat.squarefree_mul hab).mpr ⟨h,h'⟩)))
    · exact mul_eq_zero_of_left (ia (by omega) h) _

private theorem double_eq {q m : ℕ} (qp : 0 < q) (qo : Odd q) (me : Even m) : c (2*q) m = c q m := by
  have cp : Nat.Coprime 2 q := Nat.coprime_two_left.mpr qo
  have at2 : coefficient 2 m = 1 := by
    rw [coefficient_prime Nat.prime_two]
    norm_num [localCoefficient, even_iff_two_dvd.mp me]
  simp [c,coefficient_mul (by decide : 0<2) qp cp,at2]

theorem expand (L m : ℕ) (me : Even m) :
    SharpAssembly.row L m = ∑ q ∈ odds L, weight L q * c q m := by
  let A := Icc 1 L
  have split := sum_filter_add_sum_filter_not A (fun q => Odd q ∧ Squarefree q) (fun q => c q m)
  have evenpart : (∑ q ∈ odds L, if 2*q≤L then c q m else 0) =
      ∑ s ∈ A.filter (fun s => ¬(Odd s ∧ Squarefree s)), c s m := by
    apply sum_bij_ne_zero (fun q _ _ => 2*q)
    · intro q hq hn
      have qL : 2*q≤L := by by_contra h; exact hn (ite_eq_right h)
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨by have := (mem_Icc.mp (mem_filter.mp hq).1).1; omega,qL⟩,
        fun h => by obtain ⟨k,hk⟩ := h.1; omega⟩
    · intro a _ _ b _ _ eq
      omega
    · intro s hs nz
      obtain ⟨hI,hns⟩ := mem_filter.mp hs
      obtain ⟨sp,sL⟩ := mem_Icc.mp hI
      have sf : Squarefree s := by_contra fun h => nz (noSquare _ sp h)
      have notodd : ¬Odd s := fun h => hns ⟨h,sf⟩
      obtain ⟨q,hq⟩ := (Nat.not_odd_iff_even.mp notodd)
      have sq : s=2*q := by omega
      clear hq
      subst s
      have cp := Nat.coprime_of_squarefree_mul sf
      have qo := Nat.coprime_two_left.mp cp
      have good : q∈odds L := mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega,by omega⟩,qo,((Nat.squarefree_mul cp).mp sf).2⟩
      refine ⟨q,good,?_,rfl⟩
      rw [ite_eq_left sL,← double_eq (by omega) qo me]
      exact nz
    · intro q hq hn
      have good := (mem_filter.mp hq).2
      have qL : 2*q≤L := by by_contra h; exact hn (ite_eq_right h)
      rw [ite_eq_left qL, double_eq (mem_Icc.mp (mem_filter.mp hq).1).1 good.1 me]
  change (∑ q ∈ A, c q m) = _
  rw [←split, ←evenpart]
  change (∑ q ∈ odds L, c q m) + (∑ q ∈ odds L, if 2*q≤L then c q m else 0) = _
  rw [←sum_add_distrib]
  apply sum_congr rfl
  intro q _
  by_cases h : 2*q≤L <;> simp [weight,h]
  ring

def primes (y : ℕ) := ((range (y+1)).filter Nat.Prime).erase 2
def W (y : ℕ) := ∏ p ∈ primes y, p

theorem mem_primes {p y : ℕ} : p∈primes y ↔ p.Prime ∧ 2<p ∧ p≤y := by
  simp only [primes,mem_erase,mem_filter,mem_range]
  constructor
  · rintro ⟨ne,le,pr⟩
    exact ⟨pr,by have := pr.two_le;omega,by omega⟩
  · rintro ⟨pr,lt,le⟩
    exact ⟨by omega,by omega,pr⟩

theorem wpos (y : ℕ) : 0 < W y := prod_pos (fun _ hp => (mem_primes.mp hp).1.pos)

theorem wFactors (y : ℕ) : (W y).primeFactors = primes y := Nat.primeFactors_prod (fun _ hp => (mem_primes.mp hp).1)

theorem wOdd (y : ℕ) : Odd (W y) := by
  apply Nat.coprime_two_left.mp
  apply Nat.coprime_prod_right_iff.mpr
  intro p hp
  exact (Nat.coprime_primes Nat.prime_two (mem_primes.mp hp).1).mpr (by have := (mem_primes.mp hp).2.1; omega)

theorem wSquarefree (y : ℕ) : Squarefree (W y) := by
  have h := Nat.squarefree_prod_primeFactors (W y)
  rwa [wFactors] at h

theorem bad_prime {q y : ℕ} (qo : Odd q) (qs : Squarefree q) (hw : ¬q∣W y) :
    ∃ p, p.Prime ∧ y<p ∧ p∣q := by
  by_contra! h
  apply hw
  rw [←Nat.prod_primeFactors_of_squarefree qs]
  apply Finset.prod_dvd_prod_of_subset
  intro p hp
  have pp := Nat.prime_of_mem_primeFactors hp
  have pq := Nat.dvd_of_mem_primeFactors hp
  have pt : 2<p := by
    have z := pp.two_le
    have ne : p≠2 := by
      intro eq
      subst p
      obtain ⟨j,hj⟩ := pq
      obtain ⟨k,hk⟩ := qo
      omega
    omega
  exact mem_primes.mpr ⟨pp,pt,le_of_not_gt (fun yp => h p pp yp pq)⟩

def localRow (y m : ℕ) : ℝ := 2 * ∑ q ∈ (W y).divisors, c q m
def tail (L y : ℕ) := (odds L).filter (fun q => ¬q∣W y)

theorem localSet {y L : ℕ} (large : 2*W y≤L) :
    (odds L).filter (fun q => q∣W y) = (W y).divisors := by
  ext q
  constructor
  · exact fun h => Nat.mem_divisors.mpr ⟨(mem_filter.mp h).2,(wpos y).ne'⟩
  · intro h
    obtain ⟨hit,_⟩ := Nat.mem_divisors.mp h
    have lw := Nat.le_of_dvd (wpos y) hit
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.pos_of_dvd_of_pos hit (wpos y),by omega⟩,
      (wOdd y).of_dvd_nat hit,(wSquarefree y).squarefree_of_dvd hit⟩,hit⟩

theorem localDiff {L y m : ℕ} (me : Even m) (large : 2*W y≤L) :
    SharpAssembly.row L m - localRow y m = ∑ q ∈ tail L y, weight L q*c q m := by
  rw [expand L m me]
  have sp := sum_filter_add_sum_filter_not (odds L) (fun q => q∣W y) (fun q => weight L q*c q m)
  rw [localSet large] at sp
  have first : (∑ q ∈ (W y).divisors, weight L q*c q m) = localRow y m := by
    rw [localRow,Finset.mul_sum]
    apply sum_congr rfl
    intro q hq
    have hw := Nat.le_of_dvd (wpos y) (Nat.mem_divisors.mp hq).1
    norm_num [weight,show 2*q≤L by omega]
  rw [first] at sp
  change _ - _ = ∑ q ∈ (odds L).filter (fun q => ¬q∣W y), _
  linarith

theorem local_prod (y m : ℕ) :
    localRow y m = 2*∏ p ∈ primes y, (1+localCoefficient p m) := by
  rw [localRow]
  change 2*(∑ q ∈ (W y).divisors, (coefficient q m).re) = _
  rw [ProgressionLocal.divisor_product m (wpos y).ne', wFactors]


theorem prod_split (y m : ℕ) (mz : m≠0) :
    (∏ p ∈ primes y, (1+localCoefficient p m)) =
      (∏ p ∈ primes y, (1-1/((p:ℝ)-1)^2)) *
      (∏ p ∈ m.primeFactors.filter (fun p => 2<p ∧ p≤y), (1+1/((p:ℝ)-2))) := by
  have eq : (primes y).filter (fun p => p∣m) = m.primeFactors.filter (fun p => 2<p ∧ p≤y) := by
    ext p
    simp only [mem_filter,mem_primes,Nat.mem_primeFactors,mz,ne_eq,not_false_eq_true,and_true]
    tauto
  rw [←eq, Finset.prod_filter, ←Finset.prod_mul_distrib]
  apply prod_congr rfl
  intro p hp
  have gt : (2:ℝ)<p := by exact_mod_cast (mem_primes.mp hp).2.1
  have a : (p:ℝ)-1≠0 := by linarith
  have b : (p:ℝ)-2≠0 := by linarith
  by_cases hit : p∣m <;> simp [localCoefficient,hit] <;> field_simp <;> ring

end
end MeanSquareRows

open Finset Filter Conjectures.Goldbach.EstermannAlmostAllPolylog_aux
open scoped Classical
namespace MeanSquareEnergy
open MeanSquareRows MeanSquareEulerBounds
noncomputable section

def H (q : ℕ) : ℝ := 1/(q.totient:ℝ)^3

def Orth : Prop := ∀ q r : ℕ, 0<q → 0<r → Odd q → Odd r → Squarefree q → Squarefree r →
    ∀ b a : ℕ, Even b →
      (∑ t ∈ range (q*r), c q (b+2*(a+t))*c r (b+2*(a+t))) =
        ((q*r:ℕ):ℝ)*(if q=r then H q else 0)

private theorem bound (orth : Orth) {L : ℕ} (T : Finset ℕ) (inc : T⊆odds L)
    (b K : ℕ) (even : Even b) (w : ℕ→ℝ) (wb : ∀q∈T, |w q|≤2) :
    (∑t∈range K,(∑q∈T,w q*c q (b+2*t))^2) ≤ 4*K*(∑q∈T,H q)+8*(L:ℝ)^4 := by
  have prop {q} (hq:q∈T) := mem_filter.mp (inc hq)
  have sub : T ⊆ Icc 1 L := fun _ h => (prop h).1
  have hh (q) (_ : q∈T) : 0≤H q := by unfold H;positivity
  have maxH (q) (hq : q∈T) : |H q|≤1 := by
    rw [abs_of_nonneg (hh _ hq)]
    have tp : 0<q.totient := Nat.totient_pos.mpr (mem_Icc.mp (sub hq)).1
    have tr : (1:ℝ)≤(q.totient:ℝ) := by exact_mod_cast tp
    unfold H
    exact (div_le_one (by positivity)).mpr (one_le_pow₀ tr)
  have hc (q) (hq : q∈T) (t:ℕ) : |c q (b+2*t)|≤1 :=
    (Complex.abs_re_le_norm _).trans (ProgressionSums.coefficient_norm _ _ (mem_Icc.mp (sub hq)).1)
  have blk (q) (hq:q∈T) (r) (hr:r∈T) (a:ℕ) := orth q r
    (mem_Icc.mp (sub hq)).1 (mem_Icc.mp (sub hr)).1 (prop hq).2.1 (prop hr).2.1
    (prop hq).2.2 (prop hr).2.2 b a even
  simpa only [zero_add] using MeanSquareWindow.square_bound T sub K 0 w H
    (fun q t => c q (b+2*t)) wb hh maxH hc blk

theorem residual (orth : Orth) {y L : ℕ} (hy:1≤y) (large : 2*W y≤L)
    (b K : ℕ) (even : Even b) :
    (∑t∈range K,(SharpAssembly.row L (b+2*t)-localRow y (b+2*t))^2)
      ≤ 4*K*(2*Real.exp 2/(y:ℝ)^2)+8*(L:ℝ)^4 := by
  let T := tail L y
  have inc : T⊆odds L := fun _ h => (mem_filter.mp h).1
  have sf : ∀ q∈T, Squarefree q := fun q h => (mem_filter.mp (inc h)).2.2
  have bad : ∀ q∈T, ∃p∈q.primeFactors,y<p := by
    intro q h
    obtain ⟨p,pp,yp,pq⟩ := bad_prime (mem_filter.mp (inc h)).2.1 (sf _ h) (mem_filter.mp h).2
    exact ⟨p,Nat.mem_primeFactors.mpr ⟨pp,pq,(by have := (mem_Icc.mp (mem_filter.mp (inc h)).1).1; omega)⟩,yp⟩
  have ww (q) (_ : q∈T) : |weight L q|≤2 := by unfold weight;split <;> norm_num
  have ev (t : ℕ) : Even (b+2*t) := even.add (even_two_mul t)
  simp_rw [localDiff (ev _) large]
  exact (bound orth T inc b K even _ ww).trans (by
    apply add_le_add_left
    exact mul_le_mul_of_nonneg_left (bad_sum T hy sf bad) (by positivity))

theorem local_energy (orth : Orth) {y L : ℕ} (large : 2*W y≤L)
    (b K : ℕ) (even : Even b) :
    (∑t∈range K,(localRow y (b+2*t))^2) ≤ 4*K*Real.exp 2+8*(L:ℝ)^4 := by
  let T := (W y).divisors
  have inc : T⊆odds L := by
    intro q hq
    change q∈(W y).divisors at hq
    rw [←localSet large] at hq
    exact (mem_filter.mp hq).1
  have sf : ∀q∈T,Squarefree q := fun q h => (mem_filter.mp (inc h)).2.2
  have w (q) (_:q∈T) : |(2:ℝ)|≤2 := by norm_num
  simp only [localRow,mul_sum]
  exact (bound orth T inc b K even (fun _=>2) w).trans (by
    apply add_le_add_left
    exact mul_le_mul_of_nonneg_left (total_sum T sf) (by positivity))

def model (y m : ℕ) : ℝ :=
  2*(∏'p:ℕ, if p.Prime ∧ 2<p then 1-1/((p:ℝ)-1)^2 else 1) *
  ∏ p ∈ m.primeFactors.filter (fun p=>2<p ∧ p≤y), (1+1/((p:ℝ)-2))

theorem model_eq {y m : ℕ} (hy : 2≤y) (hm : m≠0) :
    model y m = alpha y * localRow y m := by
  have eq : primes y=lowPrimes y := by
    ext p
    simp only [mem_primes,lowPrimes,mem_filter,mem_range,Nat.lt_succ_iff]
    tauto
  rw [model,factor_C2 hy,local_prod,prod_split y m hm,eq]
  unfold u
  ring

end
end MeanSquareEnergy

namespace ReflectedCovariance
open Finset ProgressionZero
open Conjectures.Goldbach.EstermannAlmostAllPolylog_aux.GoldbachMajorArc
open scoped ComplexConjugate
noncomputable section


private theorem range_mul_sum {M : Type*} [AddCommMonoid M] (q r : ℕ) (f : ℕ → M) :
    (∑ t ∈ range (q*r), f t) = ∑ j ∈ range r, ∑ i ∈ range q, f (j+r*i) := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.succ_mul, sum_range_add, ih]
    simp_rw [sum_range_succ]
    rw [← sum_add_distrib]
    congr 1
    funext j
    congr 1
    ac_rfl

theorem offdiag_shift_one (q r b v : ℕ) (hq : 0 < q) (hr : 0 < r)
    (hodd : Odd q) (hqr : ¬ q ∣ r) :
    (∑ t ∈ range (q*r), coefficient q (b+2*(v+t)) *
      coefficient r (b+2*(v+t))) = 0 := by
  rw [range_mul_sum]
  apply sum_eq_zero
  intro j hj
  have hper (i : ℕ) : coefficient r (b+2*(v+(j+r*i))) =
      coefficient r (b+2*(v+j)) := by
    calc
      coefficient r (b+2*(v+(j+r*i))) = coefficient r ((b+2*(v+j))+r*(2*i)) := by
        congr 1
        ring
      _ = coefficient r (b+2*(v+j)) := coefficient_period_mul r (b+2*(v+j)) (2*i) hr
  have harg (i : ℕ) : b+2*(v+(j+r*i)) = (b+2*(v+j))+(2*r)*i := by ring
  simp_rw [hper, harg]
  rw [←sum_mul]
  have hD : ¬ q ∣ 2*r := by
    intro h
    exact hqr (hodd.coprime_two_right.dvd_of_dvd_mul_left h)
  rw [coefficient_sum_zero q (b+2*(v+j)) (2*r) hq hD]
  simp

theorem offdiag_one (q r : ℕ) (hq : 0 < q) (hr : 0 < r)
    (hodd : Odd q) (hqr : ¬ q ∣ r) :
    (∑ t ∈ range (q*r), coefficient q (2*t) * coefficient r (2*t)) = 0 := by
  simpa using offdiag_shift_one q r 0 0 hq hr hodd hqr

theorem offdiag_shift (q r b v : ℕ) (hq : 0 < q) (hr : 0 < r)
    (hoddq : Odd q) (hoddr : Odd r) (hne : q ≠ r) :
    (∑ t ∈ range (q*r), coefficient q (b+2*(v+t)) *
      coefficient r (b+2*(v+t))) = 0 := by
  by_cases hqr : q ∣ r
  · have hrq : ¬ r ∣ q := by
      intro h
      exact hne (Nat.dvd_antisymm hqr h)
    have h := offdiag_shift_one r q b v hr hq hoddr hrq
    rw [Nat.mul_comm r q] at h
    calc
      (∑ t ∈ range (q*r), coefficient q (b+2*(v+t)) *
        coefficient r (b+2*(v+t))) =
          ∑ t ∈ range (q*r), coefficient r (b+2*(v+t)) *
            coefficient q (b+2*(v+t)) := by
              apply sum_congr rfl
              intro t ht
              ring
      _ = 0 := h
  · exact offdiag_shift_one q r b v hq hr hoddq hqr

theorem offdiag_shift_real (q r b v : ℕ) (hq : 0 < q) (hr : 0 < r)
    (hoddq : Odd q) (hoddr : Odd r) (hne : q ≠ r) :
    (∑ t ∈ range (q*r), (coefficient q (b+2*(v+t))).re *
      (coefficient r (b+2*(v+t))).re) = 0 := by
  have h := congrArg Complex.re (offdiag_shift q r b v hq hr hoddq hoddr hne)
  simp only [Complex.re_sum, Complex.mul_re, coefficient_im_zero _ hq,
    coefficient_im_zero _ hr, mul_zero, sub_zero, Complex.zero_re] at h
  exact h

theorem offdiag_two_starts_one (q r bq br v : ℕ) (hq : 0 < q) (hr : 0 < r)
    (hodd : Odd q) (hqr : ¬ q ∣ r) :
    (∑ t ∈ range (q*r), coefficient q (bq+2*(v+t)) *
      coefficient r (br+2*(v+t))) = 0 := by
  rw [range_mul_sum]
  apply sum_eq_zero
  intro j hj
  have hper (i : ℕ) : coefficient r (br+2*(v+(j+r*i))) =
      coefficient r (br+2*(v+j)) := by
    calc
      coefficient r (br+2*(v+(j+r*i))) =
          coefficient r ((br+2*(v+j))+r*(2*i)) := by congr 1; ring
      _ = coefficient r (br+2*(v+j)) :=
        coefficient_period_mul r (br+2*(v+j)) (2*i) hr
  have harg (i : ℕ) : bq+2*(v+(j+r*i)) = (bq+2*(v+j))+(2*r)*i := by ring
  simp_rw [hper, harg]
  rw [←sum_mul]
  have hD : ¬ q ∣ 2*r := by
    intro h
    exact hqr (hodd.coprime_two_right.dvd_of_dvd_mul_left h)
  rw [coefficient_sum_zero q (bq+2*(v+j)) (2*r) hq hD]
  simp

theorem offdiag_two_starts (q r bq br v : ℕ) (hq : 0 < q) (hr : 0 < r)
    (hoddq : Odd q) (hoddr : Odd r) (hne : q ≠ r) :
    (∑ t ∈ range (q*r), coefficient q (bq+2*(v+t)) *
      coefficient r (br+2*(v+t))) = 0 := by
  by_cases hqr : q ∣ r
  · have hrq : ¬ r ∣ q := by
      intro h
      exact hne (Nat.dvd_antisymm hqr h)
    have h := offdiag_two_starts_one r q br bq v hr hq hoddr hrq
    rw [Nat.mul_comm r q] at h
    calc
      (∑ t ∈ range (q*r), coefficient q (bq+2*(v+t)) *
        coefficient r (br+2*(v+t))) =
          ∑ t ∈ range (q*r), coefficient r (br+2*(v+t)) *
            coefficient q (bq+2*(v+t)) := by
              apply sum_congr rfl
              intro t ht
              ring
      _ = 0 := h
  · exact offdiag_two_starts_one q r bq br v hq hr hoddq hqr

theorem offdiag_two_starts_real (q r bq br v : ℕ) (hq : 0 < q) (hr : 0 < r)
    (hoddq : Odd q) (hoddr : Odd r) (hne : q ≠ r) :
    (∑ t ∈ range (q*r), (coefficient q (bq+2*(v+t))).re *
      (coefficient r (br+2*(v+t))).re) = 0 := by
  have h := congrArg Complex.re (offdiag_two_starts q r bq br v hq hr hoddq hoddr hne)
  simp only [Complex.re_sum, Complex.mul_re, coefficient_im_zero _ hq,
    coefficient_im_zero _ hr, mul_zero, sub_zero, Complex.zero_re] at h
  exact h

theorem diagonal_repeat (q b v : ℕ) (hq : 0 < q) :
    (∑ t ∈ range (q*q), ((coefficient q (b+2*(v+t))).re)^2) =
      (q:ℝ) * ∑ t ∈ range q, ((coefficient q (b+2*(v+t))).re)^2 := by
  have hsplit := range_mul_sum q q
    (fun t => (coefficient q (b+2*(v+t))).re^2)
  rw [hsplit]
  have hper (j i : ℕ) : coefficient q (b+2*(v+(j+q*i))) =
      coefficient q (b+2*(v+j)) := by
    calc
      coefficient q (b+2*(v+(j+q*i))) =
          coefficient q ((b+2*(v+j))+q*(2*i)) := by congr 1; ring
      _ = coefficient q (b+2*(v+j)) :=
        coefficient_period_mul q (b+2*(v+j)) (2*i) hq
  simp_rw [hper]
  simp only [sum_const, card_range, nsmul_eq_mul]
  rw [mul_sum]


end
end ReflectedCovariance

open Finset
namespace MeanSquareCRTDiagonal
open Conjectures.Goldbach.EstermannAlmostAllPolylog_aux.GoldbachMajorArc
open ProgressionZero
noncomputable section

def c (q m:ℕ):ℝ := (coefficient q m).re
def localCov (p h:ℕ) : ℝ := if p∣h then 1/((p:ℝ)-1)^3 else -(1/((p:ℝ)-1)^4)
def cov (q h:ℕ) : ℝ := ∏p∈q.primeFactors,localCov p h

private theorem c_mult {u v:ℕ} (up:0<u) (vp:0<v) (sep:u.Coprime v) (m:ℕ):
    c (u*v) m=c u m*c v m:=by
  simp [c,coefficient_mul up vp sep,Complex.mul_re,coefficient_im_zero m up]

private theorem c_shift {q:ℕ} (qp:0<q) (m i:ℕ):c q (m+q*i)=c q m:=by
  rw [c,c,coefficient_period_mul q m i qp]

private theorem c_zero {p D:ℕ} (hp:p.Prime) (sep:D.Coprime p) (b:ℕ):
    ∑t∈range p,c p (b+D*t)=0:=by
  have no:¬p∣D:=hp.coprime_iff_not_dvd.mp sep.symm
  simpa only [c,Complex.re_sum,Complex.zero_re] using congrArg Complex.re (coefficient_sum_zero p b D hp.pos no)

private theorem cross_prime {p D:ℕ} (hp:p.Prime) (sep:D.Coprime p) (b h:ℕ):
    ∑t∈range p,c p (b+D*t)*c p (b+D*t+h)=(p:ℝ)*localCov p h:=by
  let A:ℝ:=1/((p:ℝ)-1)
  let B:ℝ:= -(1/((p:ℝ)-1)^2)
  have val(i:ℕ): c p i=if p∣i then A else B:=by simp only [c,coefficient_prime hp,Complex.ofReal_re,localCoefficient,A,B]
  have first:=c_zero hp sep b
  have second: (∑t∈range p,c p (b+D*t+h))=0:=by
    have eq(t:ℕ):b+D*t+h=b+h+D*t:=by omega
    simp_rw [eq];exact c_zero hp sep _
  have ne:(p:ℝ)-1≠0:=sub_ne_zero.mpr (by exact_mod_cast hp.ne_one)
  by_cases ph:p∣h
  · have pw(t:ℕ):c p (b+D*t)*c p (b+D*t+h)=(A+B)*c p (b+D*t)-A*B:=by
      have ar:p∣b+D*t+h ↔ p∣b+D*t:=Nat.dvd_add_left ph
      simp only [val,ar];by_cases hit:p∣b+D*t <;>simp [hit] <;>ring
    simp_rw [pw];rw [sum_sub_distrib,←mul_sum,first,sum_const,card_range,nsmul_eq_mul,localCov,ite_eq_left ph]
    dsimp only [A,B];field_simp;ring
  · have pw(t:ℕ):c p (b+D*t)*c p (b+D*t+h)=B*(c p (b+D*t)+c p (b+D*t+h))-B^2:=by
      simp only [val]
      by_cases a:p∣b+D*t
      · have no:¬p∣b+D*t+h:=fun dv=>ph ((Nat.dvd_add_right a).mp dv)
        simp [a,no];ring
      · by_cases ds:p∣b+D*t+h <;>simp [a,ds] <;>ring
    simp_rw [pw];rw [sum_sub_distrib,←mul_sum,sum_add_distrib,first,second,sum_const,card_range,nsmul_eq_mul,localCov,ite_eq_right ph]
    dsimp only [B];field_simp;ring

private theorem range_product (u v:ℕ) (f:ℕ→ℝ):
    (∑t∈range (u*v),f t)=∑j∈range v,∑i∈range u,f (j+v*i) := by
  induction u with
  | zero => simp
  | succ u ih =>
    rw [Nat.succ_mul,sum_range_add,ih];simp_rw [sum_range_succ];rw [←sum_add_distrib]
    congr 1;funext j;congr 1;ac_rfl

theorem progression (q:ℕ) (sq:Squarefree q) (D b h:ℕ) (sep:D.Coprime q):
    (∑t∈range q,c q (b+D*t)*c q (b+D*t+h))=(q:ℝ)*cov q h := by
  induction q using Nat.recOnPosPrimePosCoprime generalizing D b with
  | zero => exact (sq.ne_zero rfl).elim
  | one => simp [c,cov,coefficient_one]
  | prime_pow p k pp kp =>
    have eq:k=1:=((Nat.squarefree_pow_iff pp.ne_one kp.ne').mp sq).2
    subst k;simp only [pow_one,Nat.Prime.primeFactors pp,cov,prod_singleton] at sep ⊢
    exact cross_prime pp sep b h
  | coprime u v up vp uv iu iv =>
    have usp:=Nat.pos_of_ne_zero (by omega : u≠0)
    have vsp:=Nat.pos_of_ne_zero (by omega : v≠0)
    obtain ⟨su,sv⟩:=(Nat.squarefree_mul uv).mp sq
    have du:=sep.coprime_dvd_right (dvd_mul_right u v)
    have dv:=sep.coprime_dvd_right (dvd_mul_left v u)
    have dvu:(D*v).Coprime u:=du.mul_left uv.symm
    have cm:cov (u*v) h=cov u h*cov v h:=by
      simp only [cov,Nat.primeFactors_mul usp.ne' vsp.ne',prod_union uv.disjoint_primeFactors]
    rw [range_product];simp only [c_mult usp vsp uv]
    have block(j i:ℕ):c u (b+D*(j+v*i))*c v (b+D*(j+v*i))*(c u (b+D*(j+v*i)+h)*c v (b+D*(j+v*i)+h))=
        (c u ((b+D*j)+(D*v)*i)*c u ((b+D*j)+(D*v)*i+h))*(c v (b+D*j)*c v (b+D*j+h)):=by
      have e:b+D*(j+v*i)=b+D*j+v*(D*i):=by ring
      have f:b+D*(j+v*i)+h=b+D*j+h+v*(D*i):=by ring
      have vu:c v (b+D*(j+v*i))=c v (b+D*j):=e ▸ c_shift vsp _ _
      have vu':c v (b+D*(j+v*i)+h)=c v (b+D*j+h):=f ▸ c_shift vsp _ _
      rw [vu,vu',show b+D*(j+v*i)=b+D*j+D*v*i by ring];ring
    simp_rw [block,←sum_mul,iu su (D*v) _ dvu,←mul_sum,iv sv D b dv]
    rw [cm,Nat.cast_mul];ring

theorem diagonal {q:ℕ} (oq:Odd q) (sq:Squarefree q) (b:ℕ):
    (∑t∈range q,((coefficient q (b+2*t)).re)^2)=(q:ℝ)/(q.totient:ℝ)^3:=by
  have C:=progression q sq 2 b 0 oq.coprime_two_left
  simp only [Nat.add_zero,←pow_two] at C
  have phiEq:1/(q.totient:ℝ)^3=cov q 0:=by
    have eq:=Nat.totient_mul_prod_primeFactors q
    rw [Nat.prod_primeFactors_of_squarefree sq] at eq
    have f:q.totient=(∏p∈q.primeFactors,(p-1)):=Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero sq.ne_zero) (by simpa [mul_comm] using eq)
    rw [f,Nat.cast_prod,←prod_pow]
    simp only [cov,localCov,dvd_zero,ite_true,one_div,←prod_inv_distrib]
    apply prod_congr rfl;intro p hp
    rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_le,Nat.cast_one]
  rw [←phiEq] at C
  simpa only [c,mul_one_div] using C

end
end MeanSquareCRTDiagonal

namespace MeanSquareOrth
open Finset Conjectures.Goldbach.EstermannAlmostAllPolylog_aux.GoldbachMajorArc
noncomputable section

theorem orth : MeanSquareEnergy.Orth := by
  intro q r hq hr oq or sq sr b a even
  by_cases hqr : q = r
  · subst r
    have hrepeat := ReflectedCovariance.diagonal_repeat q b a hq
    have hdiag := MeanSquareCRTDiagonal.diagonal oq sq (b+2*a)
    have harg (t : ℕ) : b+2*(a+t) = (b+2*a)+2*t := by ring
    have hbase : (∑ t ∈ range q, ((coefficient q (b+2*(a+t))).re)^2) =
        (q:ℝ)/(q.totient:ℝ)^3 := by
      simpa only [harg] using hdiag
    simp only [MeanSquareRows.c]
    calc
      (∑ t ∈ range (q*q), (coefficient q (b+2*(a+t))).re *
        (coefficient q (b+2*(a+t))).re) =
          ∑ t ∈ range (q*q), ((coefficient q (b+2*(a+t))).re)^2 := by
            apply sum_congr rfl
            intro t ht
            ring
      _ = (q:ℝ) * ∑ t ∈ range q, ((coefficient q (b+2*(a+t))).re)^2 := hrepeat
      _ = (q:ℝ) * ((q:ℝ)/(q.totient:ℝ)^3) := by rw [hbase]
      _ = ((q*q:ℕ):ℝ) * MeanSquareEnergy.H q := by
        unfold MeanSquareEnergy.H
        push_cast
        ring
  · have h := ReflectedCovariance.offdiag_two_starts_real q r b b a hq hr oq or hqr
    change (∑ t ∈ range (q*r), (coefficient q (b+2*(a+t))).re *
      (coefficient r (b+2*(a+t))).re) =
      (((q*r:ℕ):ℝ)) * (if q=r then MeanSquareEnergy.H q else 0)
    simp only [hqr, ite_false, mul_zero]
    exact h

end
end MeanSquareOrth

open Finset Filter Conjectures.Goldbach.EstermannAlmostAllPolylog_aux
namespace MeanSquareConclusion
open MeanSquareRows MeanSquareEnergy MeanSquareGeometry MeanSquareEulerBounds
open scoped Classical
noncomputable section

def R (N m : ℕ) : ℝ :=
  let L := ProgressionScales.cutoff N
  (GoldbachBa08Approx.coefficient N m L (L^3)).re/(2*(N:ℝ)-(m:ℝ))

private theorem normalized (e:ℝ) (ep : 0<e) : ∀ᶠ N:ℕ in atTop, ∀ m∈B N,
    |R N m - SharpAssembly.row (ProgressionScales.cutoff N) m|≤e := by
  filter_upwards [ProgressionTransfer.normalized e ep] with N tr
  intro m hm
  obtain ⟨lo,hi,_⟩ := (mem_filter.mp hm).2
  have mu : m ≤ 2*N := by omega
  simpa only [R,ProgressionScales.cutoff,Nat.cast_sub mu,Nat.cast_mul,Nat.cast_ofNat] using tr m lo hi

private theorem three_sq (x z v A s : ℝ) (rx : |x-z|≤ s) (ra : |1-A|≤2*s) :
    (x-A*v)^2 ≤ 3*(s^2+(z-v)^2+(2*s)^2*v^2) := by
  have first := pow_le_pow_left₀ (abs_nonneg (x-z)) rx 2
  have last := pow_le_pow_left₀ (abs_nonneg (1-A)) ra 2
  rw [sq_abs] at first last
  have h : (x-A*v)^2 ≤ 3*((x-z)^2+(z-v)^2+((1-A)*v)^2) := by
    nlinarith only [sq_nonneg ((x-z)-(z-v)),sq_nonneg ((x-z)-(1-A)*v),sq_nonneg ((z-v)-(1-A)*v)]
  rw [mul_pow] at h
  exact h.trans (by linarith only [first,mul_le_mul_of_nonneg_right last (sq_nonneg v)])

theorem main (orth : Orth) : ∃C:ℝ,0<C ∧ ∀y:ℕ,3≤y → ∀ᶠ N:ℕ in atTop,
    (∑ m∈B N,(R N m-model y m)^2)/((B N).card:ℝ) ≤ C/(y:ℝ)^2 := by
  let M := Real.exp 2
  refine ⟨3*(6+24*M),by dsimp [M];positivity,?_⟩
  intro y hy
  let s : ℝ := 1/y
  have yp : (0:ℝ)<y := by exact_mod_cast (show 0<y by omega)
  have y1 : (1:ℝ)≤y := by exact_mod_cast (show 1≤y by omega)
  have sp : 0<s := by dsimp [s];positivity
  have sl : s≤1 := (div_le_one yp).mpr y1
  have sa : s^2≤1 := (pow_le_one₀ sp.le sl)
  have smod : 2*Real.exp 2/(y:ℝ)^2 = 2*M*s^2 := by dsimp [M,s];ring
  have err := (alpha_bounds (show 1≤y by omega)).2.2
  have alphaError : |1-alpha y|≤2*s := by simpa only [s,div_eq_mul_inv,one_mul] using err
  filter_upwards [normalized s sp,MeanSquareGeometry.scales (s^2) (by positivity),
    eventually_ge_atTop (2^(2*W y):ℕ),eventually_ge_atTop (1:ℕ)] with N tr geom large np
  let K := (B N).card
  let L := ProgressionScales.cutoff N
  obtain ⟨b,ev,im,kp,_,cap⟩ := geom
  change 8*(L:ℝ)^4≤ s^2*(K:ℝ) at cap
  have kl : (0:ℝ)<K := by exact_mod_cast kp
  have size : 2*W y≤L := Nat.le_log_of_pow_le (by decide) (large.trans (by omega))
  let m := fun t : ℕ => b+2*t
  have memB (t) (ht:t∈range K) : m t ∈ B N := by
    rw [im];exact mem_image.mpr ⟨t,ht,rfl⟩
  have values (t) (ht:t∈range K) :
      (R N (m t)-model y (m t))^2 ≤ 3*(s^2+(SharpAssembly.row L (m t)-localRow y (m t))^2+
        (2*s)^2*(localRow y (m t))^2) := by
    have mem := memB t ht
    have mn := (mem_Icc.mp (mem_filter.mp mem).1).1
    rw [model_eq (by omega) (by omega)]
    exact three_sq _ _ _ _ _ (tr _ mem) alphaError
  have sr := residual orth (show 1≤y by omega) size b K ev
  rw [smod] at sr
  have sz := local_energy orth size b K ev
  change (∑t∈range K,(SharpAssembly.row L (m t)-localRow y (m t))^2) ≤ _ at sr
  change (∑t∈range K,(localRow y (m t))^2) ≤ 4*K*M+8*(L:ℝ)^4 at sz
  have residualBound := sr.trans (add_le_add_right cap _)
  have localBound : (∑t∈range K,(localRow y (m t))^2) ≤ (4*M+1)*K := by
    linarith only [sz,cap,mul_le_mul_of_nonneg_right sa kl.le]
  have total := sum_le_sum values
  simp only [←mul_sum, sum_add_distrib,sum_const,card_range,nsmul_eq_mul] at total
  have sw : (∑ m∈B N,(R N m-model y m)^2) = ∑t∈range K,(R N (m t)-model y (m t))^2 := by
    conv_lhs => rw [im]
    apply sum_image
    intro i _ j _ eq
    dsimp only [m] at eq
    omega
  rw [sw]
  apply (div_le_iff₀ kl).mpr
  calc
    _ ≤ _ := total
    _ ≤ 3*((K:ℝ)*s^2+(4*K*(2*M*s^2)+s^2*K)+(2*s)^2*((4*M+1)*K)) := by
      gcongr
    _ = 3*(6+24*M)/(y:ℝ)^2*K := by dsimp [s];ring

end
end MeanSquareConclusion

open Filter Finset Conjectures.Goldbach.EstermannAlmostAllPolylog_aux in
theorem Conjectures.Goldbach.ReflectedMeanSquareEulerTail : (by
  classical
  let e := fun t : ℝ => Complex.exp (((2*Real.pi*t : ℝ) : ℂ)*Complex.I)
  let S := fun (N : ℕ) (t : ℝ) => ∑ p ∈ (Finset.range (N+1)).filter Nat.Prime, (Real.log (p : ℝ) : ℂ) * e ((p : ℝ)*t)
  let arcs := fun N : ℕ => let k := Nat.log 2 (N+2); {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ k ∧ a ≤ q ∧ Nat.Coprime a q ∧ |t-(a : ℝ)/(q : ℝ)| ≤ ((k^3 : ℕ) : ℝ)/((q : ℝ)*(N : ℝ))}
  let A := fun N m : ℕ => (intervalIntegral ((arcs N).indicator (fun t : ℝ => (S N t)^2 * e (-(m : ℝ)*t))) (0 : ℝ) 1 MeasureTheory.volume).re
  let C₂ := ∏' p : ℕ, if Nat.Prime p ∧ 2 < p then 1 - 1/((p : ℝ)-1)^2 else 1
  let band := fun N m : ℕ => 4*N ≤ 3*m ∧ 2*m ≤ 3*N ∧ Even m
  let R := fun N m : ℕ => A N m / (2*(N:ℝ)-(m:ℝ))
  let B := fun N : ℕ => (Finset.Icc N (2*N)).filter (band N)
  let avg := fun (F : Finset ℕ) (f : ℕ → ℝ) => (∑ m ∈ F, f m)/(F.card:ℝ)
  exact ∃ C : ℝ, 0 < C ∧ ∀ y : ℕ, 3 ≤ y → ∃ T : ℕ, ∀ N : ℕ, T ≤ N →
    let P := fun m : ℕ => 2*C₂ * ∏ p ∈ m.primeFactors.filter (fun p => 2 < p ∧ p ≤ y), (1+1/((p:ℝ)-2))
    avg (B N) (fun m => (R N m-P m)^2) ≤ C/(y:ℝ)^2) := by
  have orth : MeanSquareEnergy.Orth := MeanSquareOrth.orth
  classical
  dsimp only
  obtain ⟨C,cp,main⟩ := MeanSquareConclusion.main orth
  refine ⟨C,cp,?_⟩
  intro y hy
  obtain ⟨T,hT⟩ := Filter.eventually_atTop.mp (main y hy)
  refine ⟨T,?_⟩
  intro N hn
  simpa only [MeanSquareConclusion.R,MeanSquareEnergy.model,MeanSquareGeometry.B,ProgressionScales.cutoff,
    GoldbachBa08Approx.coefficient,GoldbachBa08Approx.arcs,GoldbachBlockGeometry.width,GoldbachBa08Approx.primeSum_eq,
    GoldbachMajorArc.phase] using hT N hn
