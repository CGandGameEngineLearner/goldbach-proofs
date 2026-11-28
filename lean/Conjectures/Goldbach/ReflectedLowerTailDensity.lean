import Mathlib
import Conjectures.Cuts.Taskba08eb3c3998330911d98843

section
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

/- The mean-square estimate above reuses the verified proof and arithmetic row from Goldbach PR #4435. The concentration argument follows below. -/

noncomputable section
open Finset
namespace ReflectedAntichain

open scoped Classical
variable {ι : Type*} [Fintype ι]

/-- Subsets whose value lies within a fixed distance of a given center. -/
def window (F : Finset ι → ℝ) (z δ : ℝ) : Finset (Finset ι) :=
  univ.filter fun A => |F A - z| ≤ δ

theorem window_antichain (F : Finset ι → ℝ) (z δ gap : ℝ)
    (gain : ∀ A B : Finset ι, A ⊂ B → F A + gap ≤ F B)
    (narrow : 2 * δ < gap) :
    IsAntichain (· ⊆ ·) (↑(window F z δ) : Set (Finset ι)) := by
  intro A hA B hB hne hab
  have a := abs_le.mp ((mem_filter.mp hA).2)
  have b := abs_le.mp ((mem_filter.mp hB).2)
  have g := gain A B (ssubset_of_subset_of_ne hab hne)
  linarith

theorem window_card (F : Finset ι → ℝ) (z δ gap : ℝ)
    (gain : ∀ A B : Finset ι, A ⊂ B → F A + gap ≤ F B)
    (narrow : 2 * δ < gap) :
    (window F z δ).card ≤ (Fintype.card ι).choose (Fintype.card ι / 2) :=
  (window_antichain F z δ gap gain narrow).sperner

theorem window_mass (F w : Finset ι → ℝ) (z δ gap c : ℝ)
    (gain : ∀ A B : Finset ι, A ⊂ B → F A + gap ≤ F B)
    (narrow : 2 * δ < gap) (hc : 0 ≤ c)
    (hw : ∀ A ∈ window F z δ, w A ≤ c) :
    ∑ A ∈ window F z δ, w A ≤ ((Fintype.card ι).choose (Fintype.card ι / 2) : ℝ) * c := by
  calc
    ∑ A ∈ window F z δ, w A ≤ ∑ _A ∈ window F z δ, c := Finset.sum_le_sum hw
    _ = ((window F z δ).card : ℝ) * c := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast window_card F z δ gap gain narrow) hc
/-- Normalized size of the largest layer in a cube of even dimension. -/
def centralRatio (n : ℕ) : ℝ := n.centralBinom / 4^n

theorem central_square (n : ℕ) : (n+1:ℝ) * (centralRatio n)^2 ≤ 1 := by
  induction n with
  | zero => norm_num [centralRatio]
  | succ n ih =>
    have hrec : ((n:ℝ)+1) * ((n+1).centralBinom:ℝ) =
        2 * (2*(n:ℝ)+1) * (n.centralBinom:ℝ) := by
      exact_mod_cast Nat.succ_mul_centralBinom_succ n
    have rat : centralRatio (n+1) = (2*(n:ℝ)+1)/(2*((n:ℝ)+1))*centralRatio n := by
      dsimp [centralRatio]
      rw [pow_succ]
      field_simp
      nlinarith only [hrec]
    have aux : ((n:ℝ)+2)*(2*(n:ℝ)+1)^2 ≤ 4*((n:ℝ)+1)^3 := by
      nlinarith only [Nat.cast_nonneg (α:=ℝ) n]
    have x := mul_le_mul_of_nonneg_right aux (sq_nonneg (centralRatio n))
    have y := mul_le_mul_of_nonneg_left ih (by positivity : 0≤4*((n:ℝ)+1)^2)
    rw [Nat.cast_succ,rat]
    field_simp
    nlinarith only [x,y]

theorem small_layer {ε : ℝ} (ep : 0<ε) :
    ∃ K : ℕ, 0<K ∧ ((K.choose (K/2) : ℝ)/2^K)< ε := by
  obtain ⟨n,hn⟩ := exists_nat_gt (1/ε^2)
  have np : 0<n := by
    by_contra! h
    have : n=0 := by omega
    simp [this] at hn
    linarith [sq_nonneg ε, show 0≤1/ε^2 by positivity]
  refine ⟨2*n,by omega,?_⟩
  rw [Nat.mul_div_cancel_left n zero_lt_two,pow_mul]
  rw [show (2:ℝ)^2=4 by norm_num]
  change centralRatio n < ε
  by_contra! h
  have a := central_square n
  have b := (div_lt_iff₀ (by positivity : 0< ε^2)).mp hn
  have g : ε^2 ≤ (centralRatio n)^2 := by nlinarith only [mul_self_le_mul_self ep.le h]
  nlinarith only [a,b,mul_le_mul_of_nonneg_left g (Nat.cast_nonneg (α:=ℝ) n),sq_nonneg (centralRatio n)]

/-- Both the block count and the precision of their balance can be selected
before the primes themselves. -/
theorem balanced_parameters {ε : ℝ} (ep : 0<ε) :
    ∃ K M : ℕ, 0<K ∧ 0<M ∧ (K.choose (K/2):ℝ)*(1/2+1/(M:ℝ))^K < ε := by
  obtain ⟨K,kp,hK⟩ := small_layer ep
  have hlim : Filter.Tendsto (fun M:ℕ => (K.choose (K/2):ℝ)*(1/2+1/(M:ℝ))^K)
      Filter.atTop (nhds ((K.choose (K/2):ℝ)*(1/2)^K)) := by
    simpa using (Filter.Tendsto.const_mul (K.choose (K/2):ℝ)
      ((tendsto_const_nhds (x:=(1/2:ℝ))).add tendsto_one_div_atTop_nhds_zero_nat |>.pow K))
  have h : (K.choose (K/2):ℝ)*(1/2)^K < ε := by
    simpa [div_pow,div_eq_mul_inv] using hK
  obtain ⟨M,hp,hm⟩ := ((Filter.eventually_gt_atTop 0).and
    (hlim.eventually_lt_const h)).exists
  exact ⟨K,M,kp,hp,hm⟩

end ReflectedAntichain

noncomputable section
open Finset Filter
namespace ReflectedPrimeBlocks

def off (s : Finset ℕ) : ℝ := ∏ p ∈ s, (1 - 1 / (p : ℝ))

private def v (b p : ℕ) : ℝ := if p.Prime ∧ b < p then 1 / (p : ℝ) else 0

private theorem val_nonneg (b p : ℕ) : 0 ≤ v b p := by
  unfold v; split_ifs <;> positivity

private theorem val_le {M b : ℕ} (hm : 0 < M) (mb : M ≤ b) (p : ℕ) :
    v b p ≤ 1 / (M:ℝ) := by
  unfold v
  split_ifs with h
  · exact one_div_le_one_div_of_le (by exact_mod_cast hm) (by exact_mod_cast mb.trans h.2.le)
  · positivity

private theorem divergent (b : ℕ) : ¬Summable (v b) := by
  intro h
  apply not_summable_one_div_on_primes
  rw [← summable_nat_add_iff (b + 1)] at h ⊢
  convert h using 2 with n
  by_cases hp : (n + (b+1)).Prime <;> simp [Set.indicator,v,hp,show b<n+(b+1) by omega]

/-- A finite block strictly above the requested floor whose all-off probability
first crosses one half. The reciprocal of M bounds the size of that last step. -/
theorem single {M : ℕ} (hm : 0 < M) (floor : ℕ) :
    ∃ s : Finset ℕ, (∀ p ∈ s, p.Prime ∧ floor < p) ∧
      1/2-1/(M:ℝ) ≤ off s ∧ off s ≤ 1/2 := by
  classical
  let b := max floor M
  let w (n : ℕ) := ∏ p ∈ range n, (1 - v b p)
  have vb (p:ℕ) : v b p ≤ 1 := by
    apply (val_le hm (le_max_right floor M) p).trans
    exact one_div_le_one_div_of_le zero_lt_one (by exact_mod_cast hm) |>.trans (by norm_num)
  have cross : ∃ n, w n ≤ 1/2 := by
    have divg := (not_summable_iff_tendsto_nat_atTop_of_nonneg (val_nonneg b)).mp (divergent b)
    obtain ⟨n, _, hn⟩ := exists_lt_of_tendsto_atTop divg 0 (Real.log 2)
    refine ⟨n, ?_⟩
    calc
      w n ≤ ∏ p ∈ range n, Real.exp (-(v b p)) :=
        Finset.prod_le_prod₀ (fun p _ => sub_nonneg.mpr (vb p)) (fun p _ => Real.one_sub_le_exp_neg _)
      _ = Real.exp (-(∑ p ∈ range n, v b p)) := by rw [← Real.exp_sum, sum_neg_distrib]
      _ ≤ Real.exp (-Real.log 2) := Real.exp_le_exp.mpr (neg_le_neg hn.le)
      _ = 1/2 := by rw [Real.exp_neg,Real.exp_log (by norm_num)];norm_num
  let n := Nat.find cross
  have hit : w n ≤ 1/2 := Nat.find_spec cross
  have npos : 0 < n := by
    by_contra! bad
    have zn : n = 0 := by omega
    norm_num [zn,w] at hit
  let t := n-1
  have tn : t<n := by dsimp [t];omega
  have nt : n=t+1 := by dsimp [t];omega
  have old : 1/2 < w t := lt_of_not_ge (Nat.find_min cross tn)
  have dec : w n = w t * (1-v b t) := by rw [nt]; exact prod_range_succ ..
  have wt : w t ≤ 1 := by
    apply Finset.prod_le_one₀ (fun p _ => sub_nonneg.mpr (vb p))
    intro p _; linarith [val_nonneg b p]
  have small := val_le hm (le_max_right floor M) t
  have drop : w t * v b t ≤ 1/(M:ℝ) :=
    (mul_le_of_le_one_left (val_nonneg b t) wt).trans small
  have low : 1/2-1/(M:ℝ) ≤ w n := by rw [dec]; linarith
  let s := (range n).filter (fun p : ℕ => p.Prime ∧ b<p)
  have eq : off s = w n := by
    dsimp [off,s,w,v]
    rw [Finset.prod_filter]
    apply prod_congr rfl
    intro p _
    split_ifs <;> ring
  refine ⟨s,fun p hp => ?_,eq.symm ▸ low, eq.symm ▸ hit⟩
  exact ⟨(mem_filter.mp hp).2.1, (le_max_left ..).trans_lt (mem_filter.mp hp).2.2⟩

/-- Any prescribed number of pairwise disjoint prime blocks. Both the floor
and the allowed deviation from one half are independent of the block count. -/
theorem blocks (K M floor : ℕ) (hm : 0 < M) :
    ∃ S : Fin K → Finset ℕ, (Pairwise fun i j => Disjoint (S i) (S j)) ∧
      (∀ i p, p∈S i → p.Prime ∧ floor<p) ∧
      ∀ i, 1/2-1/(M:ℝ) ≤ off (S i) ∧ off (S i) ≤ 1/2 := by
  induction K generalizing floor with
  | zero => exact ⟨Fin.elim0,fun i => i.elim0,fun i => i.elim0,fun i => i.elim0⟩
  | succ k ih =>
    obtain ⟨s,sp,sl,su⟩ := single hm floor
    let b := max floor (s.sup id)
    obtain ⟨S,dis,ps,bd⟩ := ih b
    have apart (i : Fin k) : Disjoint s (S i) := by
      refine disjoint_left.mpr fun p hp hq => ?_
      have m : p ≤ s.sup id := Finset.le_sup (f:=id) hp
      exact (ps i p hq).2.not_ge (m.trans (le_max_right ..))
    let T : Fin (k+1) → Finset ℕ := Fin.cons s S
    refine ⟨T,?_,?_,?_⟩
    · apply (pairwise_fin_succ_iff (R := fun i j : Fin (k+1) => Disjoint (T i) (T j))).mpr
      simpa only [T,Fin.cons_zero, Fin.cons_succ] using
        And.intro (fun i => (apart i).symm) (And.intro apart dis)
    · intro i
      refine Fin.cases sp (fun j p hp => ?_) i
      exact ⟨(ps j p hp).1, (le_max_left ..).trans_lt (ps j p hp).2⟩
    · intro i
      exact Fin.cases ⟨sl,su⟩ bd i

end ReflectedPrimeBlocks

open Finset
noncomputable section
namespace ReflectedBlockLaw

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {Ω : ι → Type*} [∀ i, Fintype (Ω i)] [∀ i, DecidableEq (Ω i)]

def mask (z : ∀ i, Ω i) (S : Finset ι) (i : ι) : Option (Ω i) :=
  if i ∈ S then some (z i) else none

def active (x : ∀ i, Option (Ω i)) := univ.filter fun i => (x i).isSome

omit [∀ i, Fintype (Ω i)] [∀ i, DecidableEq (Ω i)] in
private theorem active_mask (z : ∀ i, Ω i) (S : Finset ι) : active (mask z S) = S := by
  ext i
  by_cases hi : i ∈ S <;> simp [active,mask,hi]

def switch (a : ι → ℝ) (S : Finset ι) : ℝ := ∏ i, if i ∈ S then 1-a i else a i

def base (u : ∀ i, Ω i → ℝ) (z : ∀ i, Ω i) : ℝ := ∏ i, u i (z i)

def point (a : ι → ℝ) (u : ∀ i, Ω i → ℝ) (i : ι) (x : Option (Ω i)) : ℝ :=
  match x with
  | none => a i
  | some y => (1-a i)*u i y

omit [∀ i, Fintype (Ω i)] in
private theorem site_prod (u : ∀ i, Ω i → ℝ) (z : ∀ i, Ω i)
    (S : Finset ι) (x : ∀ i, Option (Ω i)) :
    (if mask z S = x then base u z else 0) =
      ∏ i, if mask z S i = x i then u i (z i) else 0 := by
  classical
  by_cases he : mask z S = x
  · simp [he,base]
  · obtain ⟨i,hi⟩ : ∃ i, mask z S i ≠ x i := by
      by_contra! h
      exact he (funext h)
    rw [ite_eq_right he]
    exact (prod_eq_zero (mem_univ i) (ite_eq_right hi)).symm

set_option maxHeartbeats 1600000 in
theorem law (a : ι → ℝ) (u : ∀ i, Ω i → ℝ) (unorm : ∀ i, ∑ y, u i y = 1)
    (x : ∀ i, Option (Ω i)) :
    (∑ S : Finset ι, switch a S * ∑ z : ∀ i, Ω i,
      if mask z S = x then base u z else 0) = ∏ i, point a u i (x i) := by
  classical
  rw [Finset.sum_eq_single (active x)]
  · simp_rw [site_prod]
    let v (i : ι) (y : Ω i) : ℝ := if (if i ∈ active x then some y else none) = x i then u i y else 0
    have eqv (z : ∀ i, Ω i) (i : ι) : (if mask z (active x) i = x i then u i (z i) else 0) = v i (z i) := by
      by_cases hi : i ∈ active x <;> simp [mask,v,hi]
    simp_rw [eqv]
    rw [← Fintype.prod_sum v]
    dsimp only [v]
    unfold switch
    rw [← prod_mul_distrib]
    apply prod_congr rfl
    intro i hi
    cases h : x i with
    | none => simp [point,active,h,unorm]
    | some y => simp [point,active,h]
  · intro S hS hne
    have ne (z : ∀ i, Ω i) : mask z S ≠ x := by
      rintro rfl
      exact hne (active_mask z S).symm
    simp [ne]
  · simp

theorem expectation (a : ι → ℝ) (u : ∀ i, Ω i → ℝ)
    (unorm : ∀ i, ∑ y, u i y = 1) (f : (∀ i, Option (Ω i)) → ℝ) :
    (∑ x, (∏ i, point a u i (x i))*f x) =
       ∑ z, base u z * ∑ S, switch a S * f (mask z S) := by
  classical
  calc
    _ = ∑ S, ∑ z, ∑ x, switch a S * ((if mask z S = x then base u z else 0)*f x) := by
      simp_rw [← law a u unorm, sum_mul, mul_assoc]
      rw [sum_comm]
      apply sum_congr rfl
      intro S hS
      rw [sum_comm]
      apply sum_congr rfl
      intro z hz
      rw [← mul_sum]
      apply congrArg
      simp_rw [sum_mul]
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro z hz
      rw [mul_sum]
      apply sum_congr rfl
      intro S hS
      simp [ite_mul]
      ring

theorem concentration (a : ι → ℝ) (u : ∀ i, Ω i → ℝ)
    (unorm : ∀ i, ∑ y, u i y = 1) (upos : ∀ i y, 0 ≤ u i y)
    (p : ℝ) (pp : 0 ≤ p) (ab : ∀ i, 0 ≤ a i ∧ a i ≤ 1 ∧ a i ≤ p ∧ 1-a i ≤ p)
    (F : (∀ i, Option (Ω i)) → ℝ) (z δ gap : ℝ)
    (gain : ∀ y A B, A ⊂ B → F (mask y A)+gap ≤ F (mask y B)) (narrow : 2*δ < gap) :
    (∑ x, if |F x-z| ≤ δ then ∏ i, point a u i (x i) else 0) ≤
      (Fintype.card ι).choose (Fintype.card ι / 2) * p^(Fintype.card ι) := by
  classical
  have bs : ∑ y, base u y = 1 := by
    simp only [base,← Fintype.prod_sum,unorm,prod_const_one]
  let C : ℝ := (Fintype.card ι).choose (Fintype.card ι / 2) * p^(Fintype.card ι)
  have swcap (S : Finset ι) : switch a S ≤ p^(Fintype.card ι) := by
    calc
      _ ≤ ∏ _i : ι, p := by
        apply prod_le_prod₀
        · intro i _
          split <;> linarith [(ab i).1,(ab i).2.1]
        · intro i _
          split <;> linarith [(ab i).2.2.1,(ab i).2.2.2]
      _ = _ := by simp
  have hb (y : ∀ i, Ω i) :
      (∑ S, switch a S * (if |F (mask y S)-z| ≤ δ then (1:ℝ) else 0)) ≤ C := by
    simpa [ReflectedAntichain.window,Finset.sum_filter,mul_ite,C] using
      ReflectedAntichain.window_mass (fun S => F (mask y S)) (switch a) z δ gap
        (p^(Fintype.card ι)) (gain y) narrow (pow_nonneg pp _) (fun S _ => swcap S)
  have he := expectation a u unorm (fun x => if |F x-z| ≤ δ then (1:ℝ) else 0)
  simp only [mul_ite,mul_one,mul_zero] at he
  rw [he]
  calc
    _ ≤ ∑ y, base u y*C := by
      apply sum_le_sum
      intro y _
      apply mul_le_mul_of_nonneg_left _ (prod_nonneg (fun i _ => upos i (y i)))
      simpa [mul_ite] using hb y
    _ = _ := by rw [← sum_mul,bs,one_mul]

/-- Each independent finite state space has one distinguished all-off configuration. -/
theorem finite_blocks (off : ∀ i, Ω i) (W : ∀ i, Ω i → ℝ)
    (wn : ∀ i, ∑ y, W i y = 1) (wp : ∀ i y, 0 ≤ W i y)
    (p : ℝ) (pp : 0 ≤ p)
    (balance : ∀ i, W i (off i) < 1 ∧ W i (off i) ≤ p ∧ 1-W i (off i) ≤ p)
    (F : (∀ i, Ω i) → ℝ) (z δ gap : ℝ)
    (gain : ∀ (y : ∀ i, {v : Ω i // v ≠ off i}) (A B : Finset ι), A ⊂ B →
      F (fun i => if i ∈ A then (y i).val else off i) + gap ≤
      F (fun i => if i ∈ B then (y i).val else off i)) (narrow : 2*δ < gap) :
    (∑ x, if |F x-z| ≤ δ then ∏ i, W i (x i) else 0) ≤
      (Fintype.card ι).choose (Fintype.card ι / 2) * p^(Fintype.card ι) := by
  classical
  let a := fun i => W i (off i)
  let u := fun i (y : {v : Ω i // v ≠ off i}) => W i y.val/(1-a i)
  have pos (i) : 0 < 1-a i := sub_pos.mpr (balance i).1
  have un (i) : ∑ y, u i y = 1 := by
    rw [show (∑ y, u i y) = (∑ y : {v : Ω i // v ≠ off i}, W i y.val)/(1-a i) by
      simp only [u,sum_div], div_eq_one_iff_eq (pos i).ne']
    have H := Fintype.sum_eq_add_sum_subtype_ne (W i) (off i)
    rw [wn i] at H
    dsimp [a]
    linarith
  let e := Equiv.piCongrRight (fun i => Equiv.optionSubtypeNe (off i))
  have ep (y : ∀ i, Option {v : Ω i // v ≠ off i}) (i : ι) :
      point a u i (y i) = W i (e y i) := by
    change _ = W i (Equiv.optionSubtypeNe (off i) (y i))
    cases y i with
    | none => rfl
    | some v =>
      simp [point,u, (pos i).ne', mul_div_cancel₀, mul_comm (1-a i)]
  have maskE (y : ∀ i, {v : Ω i // v ≠ off i}) (A : Finset ι) :
      e (mask y A) = fun i => if i ∈ A then (y i).val else off i := by
    funext i
    change Equiv.optionSubtypeNe (off i) (mask y A i) = _
    by_cases hi : i ∈ A <;> simp [mask,hi]
  have bound := concentration a u un (fun i y => div_nonneg (wp i _) (pos i).le)
    p pp (fun i => ⟨wp i _,(balance i).1.le,(balance i).2⟩)
    (fun y => F (e y)) z δ gap (by
      intro y A B h
      simp only [maskE]
      exact gain y A B h) narrow
  simpa only [ep,e.sum_comp (fun x => if |F x-z| ≤ δ then ∏ i, W i (x i) else 0)] using bound

end ReflectedBlockLaw

noncomputable section
open Finset
open scoped Classical
namespace ReflectedModelGain

def C2 : ℝ := ∏' p : ℕ, if p.Prime ∧ 2 < p then 1 - 1/((p:ℝ)-1)^2 else 1

theorem C2_lower : 1/4 ≤ C2 := by
  change (1/4:ℝ) ≤ ∏' p : ℕ, if p.Prime ∧ 2 < p then 1 - 1/((p:ℝ)-1)^2 else 1
  rw [MeanSquareEulerBounds.factor_C2 (y:=3) (by decide)]
  have eq : MeanSquareEulerBounds.lowPrimes 3 = {3} := by decide
  rw [eq,prod_singleton]
  have bound := (MeanSquareEulerBounds.alpha_bounds (y:=3) (by decide)).2.2
  have lower := (abs_le.mp bound).2
  norm_num [MeanSquareEulerBounds.u] at lower ⊢
  linarith

def factor (p : ℕ) : ℝ := 1 + 1/((p:ℝ)-2)

theorem factor_ge {p : ℕ} (hp : 2 < p) : 1 ≤ factor p := by
  have pos : (0:ℝ) < (p:ℝ)-2 := by exact sub_pos.mpr (by exact_mod_cast hp)
  unfold factor
  linarith [one_div_nonneg.mpr pos.le]

private theorem singleton_le {ι : Type*} (f : ι → ℝ) (s : Finset ι)
    (h : ∀ i∈s, 1 ≤ f i) {i : ι} (hi : i∈s) :
    f i ≤ ∏ j∈s, f j := by
  have sub : {i} ⊆ s := singleton_subset_iff.mpr hi
  simpa using Finset.prod_le_prod_of_subset_of_one_le₀ (f:=f) sub
    (fun j hj => zero_le_one.trans (h j (sub hj))) (fun j hj _ => h j hj)

variable {ι : Type*} [Fintype ι]

def site (P : Finset ℕ) (x : Finset P) : ℝ := ∏ p∈x, factor p.val

def model (P : ι→Finset ℕ) (extra : ℝ) (x : ∀ i, Finset (P i)) : ℝ :=
  (2*C2*extra) * ∏ i, site (P i) (x i)

/-- The outside primes need only contribute a multiplier at least one. -/
theorem gain (P : ι→Finset ℕ) (M : ℕ) (mp : 0<M)
    (pr : ∀ i p, p∈P i → 2<p ∧ p≤M) (extra : ℝ) (he : 1 ≤ extra)
    (y : ∀ i, {v : Finset (P i) // v ≠ ∅}) (A B : Finset ι) (hAB : A ⊂ B) :
    model P extra (fun i => if i∈A then (y i).val else ∅) + 2*C2/(M:ℝ) ≤
    model P extra (fun i => if i∈B then (y i).val else ∅) := by
  classical
  have apos : 0≤C2 := by linarith [C2_lower]
  have mr : 0<(M:ℝ) := by exact_mod_cast mp
  let g (i : ι) := site (P i) (y i).val
  have localgap (i : ι) : 1+1/(M:ℝ) ≤ g i := by
    obtain ⟨p,hp⟩ := nonempty_iff_ne_empty.mpr (y i).property
    have h := pr i p.val p.property
    have prr : (2:ℝ)<p.val := by exact_mod_cast h.1
    have prM : (p.val:ℝ)≤M := by exact_mod_cast h.2
    have fg : 1+1/(M:ℝ) ≤ factor p.val := by
      apply add_le_add_right
      exact one_div_le_one_div_of_le (by linarith) (by linarith)
    exact fg.trans (singleton_le (fun q : P i => factor q.val) (y i).val
      (fun q _ => factor_ge (pr i q.val q.property).1) hp)
  have ge1 (i : ι) : 1 ≤ g i := by linarith [localgap i,one_div_nonneg.mpr mr.le]
  have eval (S : Finset ι) :
      model P extra (fun i => if i∈S then (y i).val else ∅) = (2*C2*extra)*(∏ i∈S,g i) := by
    unfold model
    congr 1
    calc
      _ = ∏ i : ι, if i∈S then g i else 1 := by
        apply prod_congr rfl
        intro i _
        by_cases hi : i∈S <;> simp [hi,g,site]
      _ = ∏ i∈S,g i := by rw [←Finset.prod_filter];simp
  obtain ⟨j,hjB,hjA⟩ := Finset.exists_of_ssubset hAB
  have hj : j∈ B \ A := mem_sdiff.mpr ⟨hjB,hjA⟩
  have r := (localgap j).trans (singleton_le g (B \ A) (fun i _ => ge1 i) hj)
  have atleast : 1≤∏ i∈A, g i := one_le_prod₀ (fun i _ => ge1 i)
  have c : 2*C2 ≤ (2*C2*extra)*(∏i∈A,g i) := by
    have h : 2*C2 ≤ 2*C2*extra := le_mul_of_one_le_right (by positivity) he
    exact h.trans (le_mul_of_one_le_right (by positivity) atleast)
  have basepos := (by positivity : 0≤2*C2).trans c
  rw [eval,eval,←Finset.prod_sdiff hAB.subset]
  have mul := mul_le_mul_of_nonneg_left r basepos
  have fac := mul_le_mul_of_nonneg_right c (one_div_nonneg.mpr mr.le)
  simp only [div_eq_mul_inv,one_mul] at mul fac ⊢
  linarith only [mul,fac]

end ReflectedModelGain

open Finset
noncomputable section
namespace ReflectedBlockLaw

def siteMass (P : Finset ℕ) (S : Finset (↥P)) : ℝ :=
  (∏ p ∈ S, (1:ℝ)/p.val) * ∏ p ∈ Sᶜ, (1-(1:ℝ)/p.val)

theorem siteMass_sum (P : Finset ℕ) : ∑ S, siteMass P S = 1 := by
  trans ∏ p : ↥P, ((1:ℝ)/p.val+(1-(1:ℝ)/p.val))
  · exact (Fintype.prod_add _ _).symm
  · simp

theorem siteMass_nonneg (P : Finset ℕ) (hP : ∀ p ∈ P, 0 < p) (S : Finset (↥P)) :
    0 ≤ siteMass P S := by
  refine mul_nonneg (prod_nonneg fun p _ => by positivity) (prod_nonneg fun p _ => ?_)
  have h : (1 : ℝ) ≤ p.val := by exact_mod_cast hP p.val p.property
  exact sub_nonneg.mpr (one_div_le_one_div_of_le zero_lt_one h |>.trans (by norm_num))

theorem siteMass_off (P : Finset ℕ) : siteMass P ∅ = ReflectedPrimeBlocks.off P := by
  simp only [siteMass,prod_empty,compl_empty,one_mul,ReflectedPrimeBlocks.off]
  exact Finset.prod_coe_sort P (fun p : ℕ => 1 - (1:ℝ)/p)

theorem prime_blocks {K : ℕ} (P : Fin K → Finset ℕ)
    (prime : ∀ i p, p ∈ P i → p.Prime)
    {e : ℝ} (e0 : 0 ≤ e)
    (balance : ∀ i, 1/2-e ≤ ReflectedPrimeBlocks.off (P i) ∧ ReflectedPrimeBlocks.off (P i) ≤ 1/2)
    (F : (∀ i, Finset (↥(P i))) → ℝ) (z δ gap : ℝ)
    (gain : ∀ (y : ∀ i, {v : Finset (↥(P i)) // v ≠ ∅}) (A B : Finset (Fin K)), A ⊂ B →
      F (fun i => if i ∈ A then (y i).val else ∅) + gap ≤
      F (fun i => if i ∈ B then (y i).val else ∅))
    (narrow : 2*δ < gap) :
    (∑ x, if |F x-z| ≤ δ then ∏ i, siteMass (P i) (x i) else 0) ≤
      (K.choose (K/2):ℝ)*(1/2+e)^K := by
  have out := finite_blocks (fun _ => ∅) (fun i => siteMass (P i))
    (fun i => siteMass_sum (P i)) (fun i => siteMass_nonneg (P i) (fun p hp => (prime i p hp).pos))
    (1/2+e) (by positivity) (by
      intro i
      rw [siteMass_off]
      obtain ⟨hl,hr⟩ := balance i
      exact ⟨by linarith, by linarith, by linarith⟩)
    F z δ gap gain narrow
  simpa only [Fintype.card_fin] using out

end ReflectedBlockLaw

open Finset
noncomputable section
namespace ReflectedGrouping
variable {α ι : Type*} [Fintype α] [DecidableEq α] [Fintype ι] [DecidableEq ι]
variable {Ω : ι → Type*} [∀ i, Fintype (Ω i)] [∀ i, DecidableEq (Ω i)]

def parts (e : (Σ i, Ω i) ≃ α) (S : Finset α) (i : ι) : Finset (Ω i) :=
  univ.filter (fun p => e ⟨i,p⟩ ∈ S)

def joinParts (e : (Σ i, Ω i) ≃ α) (z : ∀ i, Finset (Ω i)) : Finset α :=
  univ.filter fun a => (e.symm a).snd ∈ z (e.symm a).fst

omit [Fintype ι] [DecidableEq ι] in
theorem parts_join (e : (Σ i, Ω i) ≃ α) (z : ∀ i, Finset (Ω i)) : parts e (joinParts e z) = z := by
  funext i
  ext p
  simp only [parts,joinParts,mem_filter,mem_univ,true_and]
  exact congrArg (fun z1 : Σ i, Ω i => z1.snd ∈ z z1.fst) (e.symm_apply_apply ⟨i,p⟩) |>.to_iff

omit [Fintype ι] [DecidableEq ι] in
theorem join_parts (e : (Σ i, Ω i) ≃ α) (S : Finset α) : joinParts e (parts e S) = S := by
  ext a
  obtain ⟨⟨i,p⟩,rfl⟩ := e.surjective a
  simp [parts,joinParts]

def equiv (e : (Σ i, Ω i) ≃ α) : Finset α ≃ (∀ i, Finset (Ω i)) :=
  ⟨parts e, joinParts e, join_parts e, parts_join e⟩

def bernoulli (w : α → ℝ) (S : Finset α) : ℝ := ∏ a, if a ∈ S then w a else 1 - w a

omit [DecidableEq ι] in
theorem bernoulli_parts (e : (Σ i, Ω i) ≃ α) (w : α → ℝ) (S : Finset α) :
    bernoulli w S = ∏ i, bernoulli (fun j => w (e ⟨i,j⟩)) (parts e S i) := by
  unfold bernoulli
  rw [← e.prod_comp (fun a => if a ∈ S then w a else 1 - w a), Fintype.prod_sigma]
  simp [parts]

theorem split (e : (Σ i, Ω i) ≃ α) (w : α → ℝ) (f : Finset α → ℝ) :
    (∑ S, bernoulli w S * f S) = ∑ z, (∏ i, bernoulli (fun j => w (e ⟨i,j⟩)) (z i)) * f (joinParts e z) := by
  rw [← (equiv e).sum_comp (fun z => (∏ i, bernoulli (fun j => w (e ⟨i,j⟩)) (z i)) * f (joinParts e z))]
  apply sum_congr rfl
  intro S hS
  change _ = (∏ i, bernoulli (fun j => w (e ⟨i,j⟩)) (parts e S i))*f (joinParts e (parts e S))
  rw [join_parts,bernoulli_parts e]

theorem site_eq (P : Finset ℕ) (S : Finset (↥P)) :
    bernoulli (fun p : ↥P => (1:ℝ)/p.val) S = ReflectedBlockLaw.siteMass P S := by
  classical
  unfold bernoulli ReflectedBlockLaw.siteMass
  rw [show (univ:Finset (↥P)) = S ∪ Sᶜ by simp, prod_union disjoint_compl_right]
  rw [prod_congr rfl (fun p hp => ite_eq_left hp),prod_congr rfl (fun p hp => ite_eq_right (Finset.mem_compl.mp hp))]

/-- Split a finite set of primes into named blocks and the remaining primes. -/
def rest (T : Finset ℕ) (P : ι → Finset ℕ) := T \ univ.biUnion P

def block (T : Finset ℕ) (P : ι → Finset ℕ) : Option ι → Finset ℕ
  | none => rest T P
  | some i => P i

theorem partition_equiv (T : Finset ℕ) (P : ι → Finset ℕ)
    (sub : ∀ i, P i ⊆ T) (dis : Pairwise fun i j => Disjoint (P i) (P j)) :
    ∃ e : (Σ k : Option ι, ↥(block T P k)) ≃ ↥T, ∀ k p, (e ⟨k,p⟩).val = p.val := by
  classical
  have covered (k : Option ι) : block T P k ⊆ T := by
    cases k with
    | none => exact sdiff_subset
    | some i => exact sub i
  have unique (a b : Option ι) (v : ℕ) (h1 : v ∈ block T P a) (h2 : v ∈ block T P b) : a = b := by
    cases a with
    | none =>
      cases b with
      | none => rfl
      | some j => exact ((mem_sdiff.mp h1).2 (mem_biUnion.mpr ⟨j,mem_univ _,h2⟩)).elim
    | some i =>
      cases b with
      | none => exact ((mem_sdiff.mp h2).2 (mem_biUnion.mpr ⟨i,mem_univ _,h1⟩)).elim
      | some j =>
        by_contra ne
        exact Finset.disjoint_left.mp (dis (fun h => ne (congrArg some h))) h1 h2
  let assign : (Σ k : Option ι, ↥(block T P k)) → ↥T := fun ⟨k,p⟩ => ⟨p.val,covered k p.property⟩
  have inject : Function.Injective assign := by
    rintro ⟨i,⟨p,hp⟩⟩ ⟨j,⟨q,hq⟩⟩ he
    obtain rfl : p = q := congrArg Subtype.val he
    obtain rfl : i = j := unique i j p hp hq
    rfl
  have onto : Function.Surjective assign := by
    intro p
    by_cases has : ∃ i, p.val ∈ P i
    · obtain ⟨i,hi⟩ := has
      exact ⟨⟨some i,⟨p.val,hi⟩⟩,Subtype.ext rfl⟩
    · refine ⟨⟨none,⟨p.val,mem_sdiff.mpr ⟨p.property,?_⟩⟩⟩,Subtype.ext rfl⟩
      rintro h
      obtain ⟨i,_,hi⟩ := mem_biUnion.mp h
      exact has ⟨i,hi⟩
  exact ⟨Equiv.ofBijective assign ⟨inject,onto⟩,fun _ _ => rfl⟩

/-- The per-prime law factors across the specified blocks and the complementary block. -/
theorem split_prime (T : Finset ℕ) (P : ι → Finset ℕ)
    (sub : ∀ i, P i ⊆ T) (dis : Pairwise fun i j => Disjoint (P i) (P j)) :
    ∃ e : (Σ k : Option ι, ↥(block T P k)) ≃ ↥T,
      (∀ k p, (e ⟨k,p⟩).val = p.val) ∧
      ∀ f : Finset (↥T) → ℝ, (∑ S, ReflectedBlockLaw.siteMass T S*f S) =
        ∑ z, (∏ i, ReflectedBlockLaw.siteMass (block T P i) (z i))*f (joinParts e z) := by
  obtain ⟨e,he⟩ := partition_equiv T P sub dis
  refine ⟨e,he,?_⟩
  intro f
  have a := split e (fun p => (1:ℝ)/p.val) f
  simpa only [he,site_eq] using a

end ReflectedGrouping

open Finset
noncomputable section
namespace ReflectedGrouping

private theorem site_form (T : Finset ℕ) (x : Finset (↥T)) :
    ReflectedModelGain.site T x = ∏ p : ↥T, if p ∈ x then ReflectedModelGain.factor p.val else 1 :=
  (Fintype.prod_ite_mem x (fun p => ReflectedModelGain.factor p.val)).symm

private theorem site_join {ι : Type*} [Fintype ι] [DecidableEq ι] (P : ι → Finset ℕ)
    (T : Finset ℕ) (e : (Σ i, ↥(P i)) ≃ ↥T) (he : ∀ i p, (e ⟨i,p⟩).val = p.val)
    (x : ∀ i, Finset (↥(P i))) :
    ReflectedModelGain.site T (joinParts e x) = ∏ i, ReflectedModelGain.site (P i) (x i) := by
  classical
  simp only [site_form]
  rw [← e.prod_comp (fun p => if p ∈ joinParts e x then ReflectedModelGain.factor p.val else 1), Fintype.prod_sigma]
  apply prod_congr rfl
  intro i hi
  apply prod_congr rfl
  intro p hp
  have at_site : e ⟨i,p⟩ ∈ joinParts e x ↔ p ∈ x i := by
    have a : p ∈ parts e (joinParts e x) i ↔ p ∈ x i := by rw [parts_join]
    simpa only [parts,mem_filter,mem_univ,true_and] using a
  simp only [at_site,he]

/-- A full finite prime model with an arbitrary complementary set of primes;
the bound does not depend on that complement. -/
theorem finite_model_bound {K M : ℕ} (mp : 0 < M) (T : Finset ℕ)
    (P : Fin K → Finset ℕ) (sub : ∀ i, P i ⊆ T)
    (dis : Pairwise fun i j => Disjoint (P i) (P j))
    (Tgood : ∀ p ∈ T, p.Prime ∧ 2 < p)
    (upper : ∀ i p, p ∈ P i → p ≤ M)
    {d : ℝ} (dp : 0 ≤ d)
    (balance : ∀ i, 1/2-d ≤ ReflectedPrimeBlocks.off (P i) ∧ ReflectedPrimeBlocks.off (P i) ≤ 1/2)
    (z δ : ℝ) (narrow : 2*δ < 2*ReflectedModelGain.C2/(M:ℝ)) :
    (∑ x, if |2*ReflectedModelGain.C2*ReflectedModelGain.site T x-z| ≤ δ
      then ReflectedBlockLaw.siteMass T x else 0) ≤ (K.choose (K/2):ℝ)*(1/2+d)^K := by
  classical
  obtain ⟨e,he,hs⟩ := split_prime T P sub dis
  let V := fun x => if |2*ReflectedModelGain.C2*ReflectedModelGain.site T x-z| ≤ δ then (1:ℝ) else 0
  let W := fun (i : Option (Fin K)) => ReflectedBlockLaw.siteMass (block T P i)
  let C : ℝ := (K.choose (K/2):ℝ)*(1/2+d)^K
  have cap (y : Finset (↥(rest T P))) :
      (∑ x, (∏ i, ReflectedBlockLaw.siteMass (P i) (x i)) *
        (if |ReflectedModelGain.model P (ReflectedModelGain.site (rest T P) y) x-z| ≤ δ then (1:ℝ) else 0)) ≤ C := by
    have extra : 1 ≤ ReflectedModelGain.site (rest T P) y :=
      one_le_prod₀ (fun p _ => ReflectedModelGain.factor_ge (Tgood p.val (mem_sdiff.mp p.property).1).2)
    have b := ReflectedBlockLaw.prime_blocks P (fun i p hp => (Tgood p (sub i hp)).1)
      dp balance (ReflectedModelGain.model P (ReflectedModelGain.site (rest T P) y)) z δ _
      (by
        intro y A B hAB
        convert ReflectedModelGain.gain P M mp (fun i p hp => ⟨(Tgood p (sub i hp)).2,upper i p hp⟩)
          _ extra y A B hAB using 1 <;> (congr 2; funext i; split_ifs <;> rfl)) narrow
    simpa only [mul_ite,mul_one,mul_zero] using b
  let family := fun i : Option (Fin K) => Finset (↥(block T P i))
  let E : (∀ i, family i) ≃ family none × (∀ i, family (some i)) := Equiv.piOptionEquivProd
  let G := fun (x : family none × (∀ i, family (some i))) =>
    ReflectedBlockLaw.siteMass (rest T P) x.1 * ((∏ i, ReflectedBlockLaw.siteMass (P i) (x.2 i)) *
      (if |ReflectedModelGain.model P (ReflectedModelGain.site (rest T P) x.1) x.2-z| ≤ δ then (1:ℝ) else 0))
  have pg (x : ∀ i, family i) : (∏ i, W i (x i))*V (joinParts e x) = G (E x) := by
    rw [Fintype.prod_option]
    simp only [V,site_join (block T P) T e he,Fintype.prod_option,G,ReflectedModelGain.model]
    change (W none (x none) * ∏ i, W (some i) (x (some i))) *
      (if |2*ReflectedModelGain.C2*(ReflectedModelGain.site (rest T P) (x none) *
        ∏ i, ReflectedModelGain.site (P i) (x (some i)))-z| ≤ δ then _ else _) = _
    simp only [mul_assoc,W,block,E,Equiv.piOptionEquivProd_apply]
  have hsum := hs V
  change (∑ x, ReflectedBlockLaw.siteMass T x*V x) = ∑ x, (∏ i, W i (x i))*V (joinParts e x) at hsum
  rw [show (∑ x, if |2*ReflectedModelGain.C2*ReflectedModelGain.site T x-z| ≤ δ then ReflectedBlockLaw.siteMass T x else 0) = (∑ x, ReflectedBlockLaw.siteMass T x * V x) by simp [V,mul_ite], hsum]
  simp_rw [pg]
  rw [E.sum_comp G,Fintype.sum_prod_type]
  calc
    _ ≤ ∑ y, ReflectedBlockLaw.siteMass (rest T P) y*C := by
      apply sum_le_sum
      intro y hy
      dsimp only [G]
      rw [← mul_sum]
      exact mul_le_mul_of_nonneg_left (cap y) (ReflectedBlockLaw.siteMass_nonneg _
        (fun p hp => (Tgood p (mem_sdiff.mp hp).1).1.pos) y)
    _ = _ := by rw [← sum_mul,ReflectedBlockLaw.siteMass_sum,one_mul]

end ReflectedGrouping

open Finset MeanSquareEulerBounds ReflectedModelGain
noncomputable section
namespace ReflectedFiniteModel

/-- Uniform concentration over all odd-prime extensions of a fixed finite
initial prime segment, with a common radius for every extension and center. -/
theorem extensions {ε : ℝ} (ep : 0<ε) :
    ∃ δ:ℝ, 0<δ ∧ ∃ Y:ℕ, 3≤Y ∧ ∀ T : Finset ℕ, lowPrimes Y ⊆ T →
      (∀ p∈T,p.Prime ∧ 2<p) → ∀ z:ℝ,
        (∑ x, if |2*C2*site T x-z|≤2*δ then ReflectedBlockLaw.siteMass T x else 0) ≤ ε := by
  obtain ⟨K,H,_kp,hp,cost⟩ := ReflectedAntichain.balanced_parameters ep
  obtain ⟨P,dis,pr,bal⟩ := ReflectedPrimeBlocks.blocks K H 2 hp
  let Y := max 3 ((univ.biUnion P).sup id)
  have y3 : 3 ≤ Y := le_max_left ..
  have ypos : 0<Y := by omega
  have yr : (0:ℝ)<Y := by exact_mod_cast ypos
  have cp : 0<C2 := by linarith [C2_lower]
  have upper (i : Fin K) (p : ℕ) (h:p∈P i) : p≤Y := by
    have allp : p∈univ.biUnion P := mem_biUnion.mpr ⟨i,mem_univ _,h⟩
    exact (Finset.le_sup (f:=id) allp).trans (le_max_right ..)
  let δ := C2/(4*(Y:ℝ))
  have dp : 0<δ := by dsimp [δ];positivity
  have narrow : 2*(2*δ) < 2*C2/(Y:ℝ) := by dsimp [δ];field_simp;linarith
  refine ⟨δ,dp,Y,y3,?_⟩
  intro T inc Tgood z
  have sub (i : Fin K) : P i ⊆ T := by
    intro p h
    exact inc (mem_filter.mpr ⟨mem_range.mpr (by have:=upper i p h;omega),pr i p h⟩)
  exact (ReflectedGrouping.finite_model_bound ypos T P sub dis Tgood upper
    (show 0≤1/(H:ℝ) by positivity) bal z (2*δ) narrow).trans cost.le

theorem uniform {ε : ℝ} (ep : 0<ε) :
    ∃ δ:ℝ, 0<δ ∧ ∃ Y:ℕ, 3≤Y ∧ ∀ y≥Y, ∀ z:ℝ,
      (∑ x, if |2*C2*site (lowPrimes y) x-z|≤2*δ
        then ReflectedBlockLaw.siteMass (lowPrimes y) x else 0) ≤ ε := by
  obtain ⟨δ,dp,Y,yp,ext⟩:=extensions ep
  refine ⟨δ,dp,Y,yp,?_⟩
  intro y hy z
  refine ext _ ?_ (fun p h => (mem_filter.mp h).2) z
  intro p h
  obtain ⟨hp,pr⟩:=mem_filter.mp h
  exact mem_filter.mpr ⟨mem_range.mpr (by have:=mem_range.mp hp;omega),pr⟩

end ReflectedFiniteModel

noncomputable section
open Finset
namespace ReflectedTransfer
variable {α : Type*}

private theorem filter_mul (B : Finset α) (p : α → Prop) [DecidablePred p] (c : ℝ) :
    ((B.filter p).card:ℝ)*c = ∑m∈B, if p m then c else 0 := by
  rw [←sum_filter]
  simp

/-- Deterministic Chebyshev bound comparing a true quantity to its approximation. -/
theorem compare (B : Finset α) (R P : α→ℝ) (z δ : ℝ) (dp : 0<δ) :
    ((B.filter (fun m => |R m-z|≤δ)).card:ℝ)*δ^2 ≤
      ((B.filter (fun m => |P m-z|≤2*δ)).card:ℝ)*δ^2 + ∑m∈B,(R m-P m)^2 := by
  rw [filter_mul,filter_mul,←sum_add_distrib]
  apply sum_le_sum
  intro m _
  by_cases hR : |R m-z|≤δ
  · by_cases hP : |P m-z|≤2*δ
    · simp [hR,hP,sq_nonneg]
    · simp [hR,hP]
      have tri : |P m-z| ≤ |R m-P m| + |R m-z| := by
        calc
          _ = |(P m-R m)+(R m-z)| := by congr 1;ring
          _ ≤ _ := by rw [abs_sub_comm (R m) (P m)];exact abs_add_le ..
      have far : δ ≤ |R m-P m| := by linarith [lt_of_not_ge hP]
      simpa using pow_le_pow_left₀ dp.le far 2
  · by_cases hP : |P m-z|≤2*δ <;> simp [hR,hP,add_nonneg,sq_nonneg]

theorem transfer (B : ℕ→Finset α) (R P : ℕ→α→ℝ)
    (model : ∀ ε:ℝ, 0<ε → ∃ d:ℝ, 0<d ∧ ∃ Y:ℕ, ∀ y≥Y, ∃ T:ℕ, ∀ N≥T, ∀ z:ℝ,
      ((B N).filter (fun m=>|P y m-z|≤d)).card ≤ ε * ((B N).card:ℝ))
    (approx : ∃ C:ℝ, 0<C ∧ ∀ y:ℕ, 3≤y → ∃ T:ℕ, ∀ N≥T,
      (∑m∈B N,(R N m-P y m)^2)/((B N).card:ℝ) ≤ C/(y:ℝ)^2) :
    ∀ ε:ℝ, 0<ε → ∃ δ:ℝ, 0<δ ∧ ∃ T:ℕ, ∀ N≥T, ∀ z:ℝ,
      ((B N).filter (fun m=>|R N m-z|≤δ)).card ≤ ε * ((B N).card:ℝ) := by
  intro ε ep
  obtain ⟨d,dp,Y,modulus⟩:=model (ε/2) (by positivity)
  obtain ⟨C,cp,approximation⟩:=approx
  let δ:=d/2
  have pos : 0<δ := by dsimp [δ];positivity
  obtain ⟨k,hk⟩:=exists_nat_gt (C/((ε/2)*δ^2))
  let y:=max 3 (max k Y)
  have y3 : 3≤y := le_max_left ..
  have Yy : Y≤y := (le_max_right k Y).trans (le_max_right ..)
  have ky : k≤y := (le_max_left k Y).trans (le_max_right ..)
  have yr : (1:ℝ) ≤ y := by exact_mod_cast (by omega : 1≤y)
  have trunc : C/(y:ℝ)^2 ≤ (ε/2)*δ^2 := by
    apply (div_le_iff₀ (by positivity : 0<(y:ℝ)^2)).mpr
    have low : C < (k:ℝ)*((ε/2)*δ^2) := (div_lt_iff₀ (by positivity)).mp hk
    have hi : (k:ℝ) ≤ (y:ℝ)^2 := by
      apply (by exact_mod_cast ky : (k:ℝ)≤y).trans
      nlinarith [sq_nonneg ((y:ℝ)-1)]
    linarith only [mul_le_mul_of_nonneg_right hi (by positivity : 0≤(ε/2)*δ^2),low]
  obtain ⟨T0,hm⟩:=modulus y Yy
  obtain ⟨T1,ha⟩:=approximation y y3
  refine ⟨δ,pos,max T0 T1,?_⟩
  intro N hn z
  by_cases empty : (B N).card=0
  · have be : B N=∅:=card_eq_zero.mp empty
    simp [be]
  have count : (0:ℝ)<(B N).card := by exact_mod_cast Nat.pos_of_ne_zero empty
  have err := (div_le_iff₀ count).mp (ha N ((le_max_right ..).trans hn))
  have main := hm N ((le_max_left ..).trans hn) z
  have cmp := compare (B N) (R N) (P y) z δ pos
  have dd : 2*δ=d := by dsimp [δ];ring
  rw [dd] at cmp
  apply le_of_mul_le_mul_right (a:=δ^2) _ (by positivity)
  linarith only [cmp,err,mul_le_mul_of_nonneg_right trunc count.le,
    mul_le_mul_of_nonneg_right main (sq_nonneg δ)]
end ReflectedTransfer

noncomputable section
open Finset Filter
namespace ReflectedTransfer
open MeanSquareGeometry MeanSquareEnergy MeanSquareConclusion

def ModelBound : Prop := ∀ ε:ℝ, 0<ε → ∃ δ:ℝ, 0<δ ∧ ∃ Y:ℕ, ∀ y≥Y,
  ∀ᶠ N:ℕ in atTop, ∀ z:ℝ,
    ((B N).filter (fun m=>|model y m-z|≤2*δ)).card ≤ ε * ((B N).card:ℝ)

theorem frozen_of_tail (h : ModelBound)
    (tail : ∃ C:ℝ, 0<C ∧ ∀ y:ℕ, 3≤y → ∀ᶠ N:ℕ in atTop,
      (∑m∈B N,(R N m-model y m)^2)/((B N).card:ℝ) ≤ C/(y:ℝ)^2) :
    ∀ ε:ℝ, 0<ε → ∃ δ:ℝ, 0<δ ∧ ∃ T:ℕ, ∀ N≥T, ∀ z:ℝ,
      ((B N).filter (fun m=>|R N m-z|≤δ)).card ≤ ε * ((B N).card:ℝ) := by
  apply transfer B R model
  · intro ε ep
    obtain ⟨δ,dp,Y,hY⟩:=h ε ep
    exact ⟨2*δ,by positivity,Y,fun y hy => eventually_atTop.mp (hY y hy)⟩
  · obtain ⟨C,cp,rest⟩:=tail
    exact ⟨C,cp,fun y hy => eventually_atTop.mp (rest y hy)⟩

theorem frozen (h : ModelBound) :
    ∀ ε:ℝ, 0<ε → ∃ δ:ℝ, 0<δ ∧ ∃ T:ℕ, ∀ N≥T, ∀ z:ℝ,
      ((B N).filter (fun m=>|R N m-z|≤δ)).card ≤ ε * ((B N).card:ℝ) :=
  frozen_of_tail h (MeanSquareConclusion.main MeanSquareOrth.orth)

end ReflectedTransfer

open Finset MeanSquareEulerBounds
noncomputable section
namespace ReflectedModelGain

def hits (T : Finset ℕ) (m : ℕ) : Finset (↥T) := univ.filter (fun p => p.val ∣ m)

theorem hits_image {y m : ℕ} (hm : m ≠ 0) :
    (hits (lowPrimes y) m).image Subtype.val = m.primeFactors.filter (fun p => 2<p ∧ p≤y) := by
  ext p
  simp only [hits,mem_image,mem_filter,mem_univ,true_and, Nat.mem_primeFactors]
  constructor
  · rintro ⟨q,hq,rfl⟩
    have mem := mem_filter.mp q.property
    exact ⟨⟨mem.2.1,hq,hm⟩,mem.2.2,Nat.lt_succ_iff.mp (mem_range.mp mem.1)⟩
  · rintro ⟨⟨pp,dv,_⟩,odd,cut⟩
    have mem : p ∈ lowPrimes y := mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_iff.mpr cut),pp,odd⟩
    exact ⟨⟨p,mem⟩,dv,rfl⟩

theorem true_model {y m : ℕ} (hm : m≠0) :
    MeanSquareEnergy.model y m = 2*C2*site (lowPrimes y) (hits (lowPrimes y) m) := by
  change 2*C2*(∏p∈m.primeFactors.filter (fun p=>2<p ∧ p≤y),factor p) = _
  rw [←hits_image (y:=y) hm,Finset.prod_image]
  · rfl
  · exact fun _ _ _ _ h => Subtype.ext h

end ReflectedModelGain

open Finset Filter
namespace ReflectedModelWindow
open MeanSquareRows ReflectedGrouping
noncomputable section
open scoped Classical

def value (y m:ℕ) : ℝ :=
  2*ReflectedModelGain.C2*∏p∈(primes y).filter (fun p=>p∣m),
    (1+1/((p:ℝ)-2))

theorem positive_value (y m:ℕ) (mp:m≠0) : MeanSquareEnergy.model y m=value y m := by
  have eq : m.primeFactors.filter (fun p => 2<p ∧ p≤y) = (primes y).filter (fun p=>p∣m) := by
    ext p
    simp only [mem_filter,mem_primes,Nat.mem_primeFactors,mp,and_true,ne_eq,not_false_eq_true]
    tauto
  unfold MeanSquareEnergy.model value ReflectedModelGain.C2
  rw [eq]

theorem residue (y m:ℕ) : value y (m % W y) = value y m := by
  have eq : (primes y).filter (fun p=>p ∣ m % W y) = (primes y).filter (fun p=>p∣m) := by
    apply filter_congr
    intro p hp
    have pw : p∣W y := Nat.dvd_of_mem_primeFactors (by simpa only [wFactors] using hp)
    rw [Nat.dvd_iff_mod_eq_zero, Nat.dvd_iff_mod_eq_zero, Nat.mod_mod_of_dvd _ pw]
  simp only [value,eq]

theorem uniform_period {D : ℕ} (dp:0<D) (b:ℕ) (sep:(2:ℕ).Coprime D)
    (f:ℕ→ℝ) : (∑t∈range D,f ((b+2*t) % D))=∑r∈range D,f r := by
  let m (t:ℕ) := (b+2*t) % D
  have inj : Set.InjOn m (↑(range D)) := by
    intro i hi j hj h
    have hmod : (b+2*i)≡(b+2*j) [MOD D] := h
    have h' := Nat.ModEq.cancel_left_of_coprime sep.symm (Nat.ModEq.add_left_cancel' b hmod)
    exact h'.eq_of_lt_of_lt (mem_range.mp hi) (mem_range.mp hj)
  have eq : (range D).image m=range D := by
    apply eq_of_subset_of_card_le
    · intro r hr
      obtain ⟨t,_,rfl⟩ := mem_image.mp hr
      exact mem_range.mpr (Nat.mod_lt _ dp)
    · rw [card_image_of_injOn inj]
  calc
    _ = ∑r∈(range D).image m,f r := (sum_image (fun _ hi _ hj eq=> inj hi hj eq)).symm
    _ = _ := by rw [eq]

private theorem truncate {D:ℕ} (dp:0<D) (f:ℕ→ℝ) (K:ℕ) (e:ℝ) (ep:0≤e)
    (full : ∀u:ℕ,(∑t∈range D, f (u+t))≤D*e) (small:∀k:ℕ,f k≤1) :
    (∑t∈range K,f t) ≤ K*e+D := by
  have blocks (v:ℕ) : (∑t∈range (D*v),f t) ≤ ((D*v:ℕ):ℝ)*e := by
    induction v with
    | zero => simp
    | succ n ih =>
      rw [Nat.mul_succ,sum_range_add,Nat.cast_add,add_mul]
      exact add_le_add ih (full _)
  have h := Nat.div_add_mod K D
  have part := Finset.sum_range_add f (D*(K/D)) (K % D)
  rw [Nat.div_add_mod] at part
  rw [part]
  have rest : (∑i∈range (K % D),f (D*(K/D)+i)) ≤ (K % D:ℕ) := by
    apply (sum_le_sum (fun i _ => (show f (D*(K/D)+i)≤1 from small _))).trans
    simp
  have ltK : D*(K/D)≤K := by omega
  have rem : (K % D:ℕ)≤D := (Nat.mod_lt _ dp).le
  exact (add_le_add (blocks _) rest).trans (add_le_add (mul_le_mul_of_nonneg_right (by exact_mod_cast ltK) ep)
    (by exact_mod_cast rem))

open MeanSquareGeometry in
theorem finite_to_band {y:ℕ} {α δ:ℝ} (ap:0<α)
    (full : ∀ z:ℝ, (∑r∈range (W y), if |value y r-z|≤δ then (1:ℝ) else 0) ≤ W y*α) :
    ∀ᶠ N:ℕ in atTop, ∀ z:ℝ,
      (((B N).filter (fun m=>|MeanSquareEnergy.model y m-z|≤δ)).card:ℝ) ≤ 2*α*(B N).card := by
  have limit : ∀ᶠ N:ℕ in atTop, (24*(W y):ℝ) ≤ N*α := by
    have div : 24*(W y:ℝ)/α>0 := by have := wpos y; positivity
    filter_upwards [tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (24*(W y:ℝ)/α))] with N dd
    exact (div_le_iff₀ ap).mp dd
  filter_upwards [limit,eventually_ge_atTop (100:ℕ)] with N low big
  obtain ⟨b,eb,image,kp,size⟩ := geometry big
  intro z
  let f (t:ℕ) : ℝ := if |value y (b+2*t)-z|≤δ then 1 else 0
  have small (t:ℕ) : f t≤1 := by dsimp only [f]; split <;> norm_num
  have whole (u:ℕ) : (∑i∈range (W y),f (u+i)) ≤ (W y:ℝ)*α := by
    have id (t:ℕ) : f (u+t) = (if |value y (((b+2*u)+2*t) % W y)-z|≤δ then (1:ℝ) else 0) := by
      rw [residue]
      simp only [f,Nat.mul_add,Nat.add_assoc]
    simp_rw [id]
    rw [uniform_period (wpos y) (b+2*u) (wOdd y).coprime_two_left
      (fun r:ℕ => if |value y r-z|≤δ then (1:ℝ) else 0)]
    exact full z
  let K := (B N).card
  have introF (m:ℕ) (hm:m∈B N) : m≠0 := by have h:=(mem_Icc.mp (mem_filter.mp hm).1).1;omega
  have card_eq : (((B N).filter (fun m=>|MeanSquareEnergy.model y m-z|≤δ)).card:ℝ) = ∑t∈range K,f t := by
    calc
      _ = ∑m∈B N,if |MeanSquareEnergy.model y m-z|≤δ then (1:ℝ) else 0 := by
        rw [←Finset.sum_filter];simp
      _ = ∑m∈B N,if |value y m-z|≤δ then (1:ℝ) else 0 := by
        exact sum_congr rfl (fun m hm=>by rw [positive_value y m (introF m hm)])
      _ = _ := by
        conv_lhs => rw [image]
        apply sum_image
        intro i _ j _ eq
        change b+2*i=b+2*j at eq
        omega
  rw [card_eq]
  have estimate := truncate (wpos y) f K (α:ℝ) ap.le whole small
  have nk : (N:ℝ)≤24*(K:ℝ) := by exact_mod_cast size
  change _ ≤ 2*α*(K:ℝ)
  linarith only [estimate,mul_le_mul_of_nonneg_right nk ap.le,low]

end
end ReflectedModelWindow

open Finset Filter MeanSquareRows MeanSquareEulerBounds
namespace ReflectedModelLaw
open ReflectedModelGain ReflectedModelWindow
noncomputable section

theorem primes_eq (y : ℕ) : primes y = lowPrimes y := by
  ext p
  simp only [mem_primes,lowPrimes,mem_filter,mem_range,Nat.lt_succ_iff]
  tauto

theorem wheel_eq (y : ℕ) : W y = ∏p∈lowPrimes y,p := by rw [W,primes_eq]

/-- The residue-value model includes the zero class, where every odd prime in
the finite wheel divides the representative. -/
theorem all_values (y m : ℕ) :
    value y m = 2*C2*site (lowPrimes y) (hits (lowPrimes y) m) := by
  let T := lowPrimes y
  have im : (hits T m).image Subtype.val = T.filter (fun p => p∣m) := by
    ext p
    simp only [hits,mem_image,mem_filter,mem_univ,true_and]
    constructor
    · rintro ⟨q,hq,rfl⟩; exact ⟨q.property,hq⟩
    · rintro ⟨hq,hp⟩; exact ⟨⟨p,hq⟩,hp,rfl⟩
  change 2*C2*(∏p∈(primes y).filter (fun p=>p∣m),factor p) = _
  rw [primes_eq,←im,Finset.prod_image]
  · rfl
  · exact fun _ _ _ _ h => Subtype.ext h

def ResidueLaw : Prop := ∀(T:Finset ℕ), (∀p∈T,p.Prime) → ∀ f:Finset (↥T)→ℝ,
  (∑m∈range (∏p∈T,p), f (hits T m)) = ((∏p∈T,p):ℕ) * ∑x, ReflectedBlockLaw.siteMass T x*f x

theorem model_bound (crt : ResidueLaw) : ReflectedTransfer.ModelBound := by
  intro ε ep
  obtain ⟨δ,dp,Y,_yp,model⟩:=ReflectedFiniteModel.uniform (ε:=ε/2) (by positivity)
  refine ⟨δ,dp,Y,?_⟩
  intro y hy
  let T := lowPrimes y
  have pr : ∀p∈T, p.Prime := fun p hp=>(mem_filter.mp hp).2.1
  have full (z : ℝ) : (∑r∈range (W y), if |value y r-z|≤2*δ then (1:ℝ) else 0) ≤ W y*(ε/2) := by
    let f (x:Finset T) : ℝ := if |2*C2*site T x-z|≤2*δ then 1 else 0
    have eq := crt T pr f
    have ident : (∑r∈range (W y), if |value y r-z|≤2*δ then (1:ℝ) else 0) =
        (W y:ℝ)*∑ x, ReflectedBlockLaw.siteMass T x * f x := by
      simpa only [wheel_eq,all_values,f,T] using eq
    rw [ident]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    simpa only [f,mul_ite,mul_one,mul_zero,T] using model y hy z
  have band := ReflectedModelWindow.finite_to_band (y:=y) (δ:=2*δ) (α:=ε/2) (by positivity) full
  simpa only [show 2*(ε/2)=ε by ring] using band

theorem conclusion (crt : ResidueLaw) :
    ∀ ε:ℝ, 0<ε → ∃ δ:ℝ, 0<δ ∧ ∃ T:ℕ, ∀ N≥T, ∀ z:ℝ,
      ((MeanSquareGeometry.B N).filter (fun m=>|MeanSquareConclusion.R N m-z|≤δ)).card ≤
        ε * ((MeanSquareGeometry.B N).card:ℝ) :=
  ReflectedTransfer.frozen (model_bound crt)
end
end ReflectedModelLaw

namespace ReflectedModelCRT
open Finset
noncomputable section

private theorem range_zmod_sum (n : ℕ) [NeZero n] (g : ℕ → ℝ) :
    (∑ m ∈ range n, g m) = ∑ z : ZMod n, g z.val := by
  rw [← Fin.sum_univ_eq_sum_range g n]
  apply Fintype.sum_equiv (ZMod.finEquiv n).toEquiv
  intro x
  cases n with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n => rfl

abbrev wheel (P : Finset ℕ) : ℕ := ∏ p : P, (p : ℕ)

def crt (P : Finset ℕ) (prime : ∀ p ∈ P, p.Prime) :
    ZMod (wheel P) ≃+* ((p : P) → ZMod (p : ℕ)) := by
  unfold wheel
  apply ZMod.prodEquivPi (fun p : P => (p : ℕ))
  intro p r hne
  apply (Nat.coprime_primes (prime p p.property) (prime r r.property)).mpr
  intro he
  exact hne (Subtype.ext he)

theorem wheel_pos (P : Finset ℕ) (prime : ∀ p ∈ P, p.Prime) :
    0 < wheel P := by
  unfold wheel
  exact Finset.prod_pos fun p _ => (prime p p.property).pos

theorem crt_coord_val (P : Finset ℕ) (prime : ∀ p ∈ P, p.Prime)
    (z : ZMod (wheel P)) (p : P) :
    ((crt P prime z) p).val = z.val % (p : ℕ) := by
  classical
  letI : NeZero (wheel P) := ⟨(wheel_pos P prime).ne'⟩
  letI : NeZero (p : ℕ) := ⟨(prime p p.property).ne_zero⟩
  have cop : Pairwise (Function.onFun Nat.Coprime (fun p : P => (p : ℕ))) := by
    intro a b hne
    apply (Nat.coprime_primes (prime a a.property) (prime b b.property)).mpr
    intro he
    exact hne (Subtype.ext he)
  change ((ZMod.prodEquivPi (fun p : P => (p : ℕ)) cop) z p).val =
    z.val % (p : ℕ)
  rw [ZMod.prodEquivPi_apply]
  have hz := ZMod.natCast_zmod_val z
  conv_lhs => rw [←hz]
  simp only [map_natCast, ZMod.val_natCast]

theorem crt_product (P : Finset ℕ) (prime : ∀ p ∈ P, p.Prime)
    (f : (p : P) → ℕ → ℝ) :
    (∑ m ∈ range (wheel P), ∏ p : P, f p (m % (p:ℕ))) =
      ∏ p : P, ∑ r ∈ range (p:ℕ), f p r := by
  classical
  letI : NeZero (wheel P) := ⟨(wheel_pos P prime).ne'⟩
  letI (p : P) : NeZero (p : ℕ) := ⟨(prime p p.property).ne_zero⟩
  have hCRT :
      (∑ z : ZMod (wheel P), ∏ p : P, f p (((crt P prime) z p).val)) =
        ∏ p : P, ∑ x : ZMod (p : ℕ), f p x.val := by
    let e := (crt P prime).toEquiv
    calc
      (∑ z : ZMod (wheel P), ∏ p : P, f p (((crt P prime) z p).val)) =
        ∑ x : ((p : P) → ZMod (p : ℕ)), ∏ p : P, f p (x p).val := by
          apply Fintype.sum_equiv e
          intro z
          rfl
      _ = _ := by
        simpa only [Fintype.piFinset_univ] using
          (Finset.prod_univ_sum (fun p : P => (Finset.univ : Finset (ZMod (p : ℕ))))
            (fun p x => f p x.val)).symm
  calc
    (∑ m ∈ range (wheel P), ∏ p : P, f p (m % (p:ℕ))) =
        ∑ z : ZMod (wheel P), ∏ p : P, f p (z.val % (p:ℕ)) :=
          range_zmod_sum (wheel P) _
    _ = ∑ z : ZMod (wheel P), ∏ p : P, f p (((crt P prime) z p).val) := by
      apply Finset.sum_congr rfl
      intro z hz
      apply Finset.prod_congr rfl
      intro p hp
      rw [crt_coord_val P prime z p]
    _ = ∏ p : P, ∑ x : ZMod (p : ℕ), f p x.val := hCRT
    _ = ∏ p : P, ∑ r ∈ range (p:ℕ), f p r := by
      apply Finset.prod_congr rfl
      intro p hp
      exact (range_zmod_sum (p:ℕ) (f p)).symm

private theorem local_indicator_sum (p : ℕ) (hp : 0 < p) (a : Prop) [Decidable a] :
    (∑ r ∈ range p, if (r=0 ↔ a) then (1:ℝ) else 0) =
      if a then 1 else (p:ℝ)-1 := by
  by_cases ha : a
  · simp [ha, Finset.sum_ite_eq', hp]
  · simp [ha, Finset.sum_ite, hp]
    rw [show (range p).filter (fun r => ¬r = 0) = (range p).erase 0 by
      ext r; simp [and_comm]]
    simp [hp]

private theorem hit_indicator_prod (P : Finset ℕ) (S : Finset (↥P)) (m : ℕ) :
    (if ReflectedModelGain.hits P m = S then (1:ℝ) else 0) =
      ∏ p : P, if ((m % (p:ℕ) = 0) ↔ p ∈ S) then (1:ℝ) else 0 := by
  classical
  have hmem (p : P) : (m % (p:ℕ) = 0) ↔ p ∈ ReflectedModelGain.hits P m := by
    simp [ReflectedModelGain.hits, Nat.dvd_iff_mod_eq_zero]
  by_cases heq : ReflectedModelGain.hits P m = S
  · rw [if_pos heq]
    have hlocal (p : P) : (m % (p:ℕ) = 0) ↔ p ∈ S := by
      rw [hmem p, heq]
    simp [hlocal]
  · rw [if_neg heq]
    have hw : ∃ p : P, ¬ ((m % (p:ℕ) = 0) ↔ p ∈ S) := by
      by_contra h
      apply heq
      ext p
      have hp := not_not.mp (not_exists.mp h p)
      exact (hmem p).symm.trans hp
    obtain ⟨p,hp⟩ := hw
    exact (Finset.prod_eq_zero (Finset.mem_univ p) (by simp [hp])).symm

theorem hits_count (P : Finset ℕ) (prime : ∀ p ∈ P, p.Prime)
    (S : Finset (↥P)) :
    (∑ m ∈ range (wheel P),
      if ReflectedModelGain.hits P m = S then (1:ℝ) else 0) =
        ∏ p : P, if p ∈ S then (1:ℝ) else (p:ℝ)-1 := by
  classical
  calc
    (∑ m ∈ range (wheel P),
      if ReflectedModelGain.hits P m = S then (1:ℝ) else 0) =
        ∑ m ∈ range (wheel P),
          ∏ p : P, if ((m % (p:ℕ) = 0) ↔ p ∈ S) then (1:ℝ) else 0 := by
            apply sum_congr rfl
            intro m hm
            exact hit_indicator_prod P S m
    _ = ∏ p : P, ∑ r ∈ range (p:ℕ),
          if ((r=0) ↔ p ∈ S) then (1:ℝ) else 0 :=
            crt_product P prime (fun p r =>
              if ((r=0) ↔ p ∈ S) then (1:ℝ) else 0)
    _ = ∏ p : P, if p ∈ S then (1:ℝ) else (p:ℝ)-1 := by
      apply prod_congr rfl
      intro p hp
      exact local_indicator_sum (p:ℕ) (prime p p.property).pos (p∈S)

theorem hits_count_mass (P : Finset ℕ) (prime : ∀ p ∈ P, p.Prime)
    (S : Finset (↥P)) :
    (∑ m ∈ range (wheel P),
      if ReflectedModelGain.hits P m = S then (1:ℝ) else 0) =
        (wheel P:ℝ) * ReflectedBlockLaw.siteMass P S := by
  rw [hits_count P prime S]
  have hfactor (p : P) : (if p∈S then (1:ℝ) else (p:ℝ)-1) =
      (p:ℝ) * (if p∈S then (1:ℝ)/p else 1-(1:ℝ)/p) := by
    have pne : (p:ℝ) ≠ 0 := by
      exact_mod_cast (prime p p.property).ne_zero
    by_cases hp : p∈S <;> simp only [hp, ite_true, ite_false]
    · field_simp
    · field_simp
  simp_rw [hfactor]
  rw [Finset.prod_mul_distrib]
  have hw : (∏ p : P, (p:ℝ)) = (wheel P:ℝ) := by
    simp [wheel]
  rw [hw]
  congr 1
  rw [← ReflectedGrouping.site_eq P S]
  rfl

theorem residue_law (T : Finset ℕ) (prime : ∀ p ∈ T, p.Prime)
    (f : Finset (↥T) → ℝ) :
    (∑ m ∈ range (∏ p ∈ T, p), f (ReflectedModelGain.hits T m)) =
      ((∏ p ∈ T, p : ℕ):ℝ) *
        ∑ S : Finset (↥T), ReflectedBlockLaw.siteMass T S * f S := by
  classical
  have hW : wheel T = ∏ p ∈ T, p := by
    exact Finset.prod_coe_sort T (fun p : ℕ => p)
  rw [←hW]
  have partition (m : ℕ) : f (ReflectedModelGain.hits T m) =
      ∑ S : Finset (↥T), if ReflectedModelGain.hits T m = S then f S else 0 := by
    simp
  calc
    (∑ m ∈ range (wheel T), f (ReflectedModelGain.hits T m)) =
        ∑ m ∈ range (wheel T), ∑ S : Finset (↥T),
          if ReflectedModelGain.hits T m = S then f S else 0 := by
            apply sum_congr rfl
            intro m hm
            exact partition m
    _ = ∑ S : Finset (↥T),
          (∑ m ∈ range (wheel T),
            if ReflectedModelGain.hits T m = S then (1:ℝ) else 0) * f S := by
            rw [sum_comm]
            apply sum_congr rfl
            intro S hS
            rw [sum_mul]
            apply sum_congr rfl
            intro m hm
            split_ifs <;> simp
    _ = ∑ S : Finset (↥T),
          (wheel T:ℝ) * ReflectedBlockLaw.siteMass T S * f S := by
            apply sum_congr rfl
            intro S hS
            rw [hits_count_mass T prime S]
    _ = (wheel T:ℝ) *
          ∑ S : Finset (↥T), ReflectedBlockLaw.siteMass T S * f S := by
            rw [mul_sum]
            apply sum_congr rfl
            intro S hS
            ring

end
end ReflectedModelCRT
end

section
/- The formalization adapts the work of the PrimeNumberTheoremAnd contributors,
PrimeNumberTheoremAnd/IEANTN/Mertens.lean, revision c39a751132c88b6e8080b74c74023fd95b3d8be0.
Source: https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/c39a751132c88b6e8080b74c74023fd95b3d8be0/PrimeNumberTheoremAnd/IEANTN/Mertens.lean
Licensed under the Apache License, Version 2.0. This adaptation uses explicit
measurability arguments, updates proofs for Mathlib 4.36, and omits blueprint
metadata and an Euler-Maclaurin identity unused in the proof. -/
theorem Filter.EventuallyEq.iff_eventually {α : Type _} {β : Type _} {l : Filter α} {f g : α → β} : f =ᶠ[l] g ↔ ∀ᶠ (x : α) in l, f x = g x := by rfl


namespace Real

open Filter Asymptotics

theorem inv_log_eq_o_one : (fun x ↦ 1 / log x) =o[atTop] (fun _ ↦ (1:ℝ)) := by
    rw [isLittleO_one_iff]
    convert tendsto_log_atTop.inv_tendsto_atTop using 1
    ext; simp

theorem one_eq_o_log_log : (fun _ ↦ (1:ℝ)) =o[atTop] (fun x ↦ log (log x)) := by
    simp only [isLittleO_one_left_iff, norm_eq_abs]
    exact tendsto_abs_atTop_atTop.comp (tendsto_log_atTop.comp tendsto_log_atTop)

end Real

section Issue1584
open MeasureTheory Set Filter Topology

/-- The integrand `log v * exp (-v)` is integrable on `Set.Ioi 0`. -/
private lemma integrableOn_log_mul_exp_neg :
    IntegrableOn (fun v : ℝ => Real.log v * Real.exp (-v)) (Set.Ioi 0) := by
  rw [← Set.Ioc_union_Ioi_eq_Ioi (zero_le_one' ℝ), integrableOn_union]
  constructor
  · -- On `Set.Ioc 0 1`: dominate by `|log v|`, which is integrable.
    have hlog : IntegrableOn (fun v : ℝ => Real.log v) (Set.Ioc 0 1) volume := by
      have := (intervalIntegral.intervalIntegrable_log' (a := 0) (b := 1))
      rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le (zero_le_one' ℝ)] at this
    apply Integrable.mono' hlog.norm
    · apply (Measurable.aestronglyMeasurable ?_)
      exact (Real.measurable_log.mul (Real.measurable_exp.comp measurable_neg))
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with v hv
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      have h1 : |Real.exp (-v)| = Real.exp (-v) := abs_of_pos (Real.exp_pos _)
      have h2 : Real.exp (-v) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [hv.1])
      rw [h1]
      nlinarith [abs_nonneg (Real.log v), Real.exp_pos (-v)]
  · -- On `Set.Ioi 1`: dominate by `2 * exp (-v/2)`, integrable.
    have hexp : IntegrableOn (fun v : ℝ => (2 : ℝ) * Real.exp ((-1/2) * v)) (Set.Ioi 1) volume := by
      exact (integrableOn_exp_mul_Ioi (by norm_num : (-1/2 : ℝ) < 0) 1).const_mul 2
    apply Integrable.mono' hexp
    · apply (Measurable.aestronglyMeasurable ?_)
      exact (Real.measurable_log.mul (Real.measurable_exp.comp measurable_neg))
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with v hv
      have hv1 : (1 : ℝ) ≤ v := le_of_lt hv
      have hvpos : (0 : ℝ) < v := by linarith
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      have hlogabs : |Real.log v| = Real.log v :=
        abs_of_nonneg (Real.log_nonneg hv1)
      have hexpabs : |Real.exp (-v)| = Real.exp (-v) := abs_of_pos (Real.exp_pos _)
      rw [hlogabs, hexpabs]
      -- `log v ≤ v`
      have hlogv : Real.log v ≤ v := (Real.log_le_sub_one_of_pos hvpos).trans (by linarith)
      -- `v ≤ 2 * exp (v/2)`
      have hvexp : v ≤ 2 * Real.exp (v/2) := by
        have := Real.add_one_le_exp (v/2)
        nlinarith [Real.exp_pos (v/2)]
      -- combine: log v * exp(-v) ≤ v * exp(-v) ≤ 2 exp(v/2) exp(-v) = 2 exp(-v/2)
      have hstep : Real.log v * Real.exp (-v) ≤ 2 * Real.exp (v/2) * Real.exp (-v) := by
        apply mul_le_mul_of_nonneg_right (hlogv.trans hvexp) (le_of_lt (Real.exp_pos _))
      have heq : 2 * Real.exp (v/2) * Real.exp (-v) = 2 * Real.exp ((-1/2) * v) := by
        rw [mul_assoc, ← Real.exp_add]
        ring_nf
      rw [heq] at hstep
      exact hstep

/-- Helper: `∫_0^∞ log t · e^{-t} dt = Γ'(1)` (real). -/
private lemma integral_log_mul_exp_neg_eq_deriv_Gamma :
    ∫ t in Set.Ioi (0:ℝ), Real.log t * Real.exp (-t) = deriv Real.Gamma 1 := by
  set I : ℝ := ∫ t in Set.Ioi (0:ℝ), Real.log t * Real.exp (-t) with hI
  -- Step 1: derivative of GammaIntegral at 1.
  have h1 := Complex.hasDerivAt_GammaIntegral (s := (1 : ℂ)) (by norm_num)
  -- Step 2: simplify the integrand to `↑(log t * exp (-t))` and pull out `ofReal`.
  have hval : (∫ t : ℝ in Set.Ioi 0, (↑t : ℂ) ^ ((1 : ℂ) - 1) * (↑(Real.log t) * ↑(Real.exp (-t))))
      = (I : ℂ) := by
    have key : ∀ t : ℝ, (↑t : ℂ) ^ ((1 : ℂ) - 1) * (↑(Real.log t) * ↑(Real.exp (-t)))
        = ((Real.log t * Real.exp (-t) : ℝ) : ℂ) := by
      intro t
      rw [sub_self, Complex.cpow_zero, one_mul, Complex.ofReal_mul]
    simp_rw [key]
    rw [integral_complex_ofReal, hI]
  rw [hval] at h1
  -- Step 3: transfer to Complex.Gamma (agrees with GammaIntegral on `{re > 0}`).
  have h2 : HasDerivAt Complex.Gamma (I : ℂ) 1 := by
    apply h1.congr_of_eventuallyEq
    filter_upwards [(isOpen_lt (continuous_const : Continuous (fun _ : ℂ => (0:ℝ))) Complex.continuous_re).mem_nhds
      (show (1:ℂ) ∈ {z : ℂ | (0:ℝ) < z.re} by change (0:ℝ)<(1:ℂ).re; norm_num)] with z hz
    exact Complex.Gamma_eq_integral hz
  -- Step 4: transfer ℂ → ℝ.
  have h3 := h2.real_of_complex
  have h4 : HasDerivAt Real.Gamma I 1 := by
    have hcongr : (fun x : ℝ => (Complex.Gamma ↑x).re) = Real.Gamma := by
      funext x
      rw [Complex.Gamma_ofReal, Complex.ofReal_re]
    rw [hcongr, Complex.ofReal_re] at h3
    exact h3
  rw [← h4.deriv]

/-- Core of #1584, stated with explicit qualifiers (outside `namespace Mertens`,
where `Finset` is open and would clash with `Set.Ioi`). -/
private theorem mul_integ_log_log_eq_aux (s : ℝ) (hs : 1 < s) :
    (s - 1) * ∫ x in Set.Ioi (1:ℝ), Real.log (Real.log x) * x ^ (-s) =
      - Real.log (s - 1) + deriv Real.Gamma 1 := by
  have hs0 : 0 < s - 1 := by linarith
  set f : ℝ → ℝ := fun x => (s - 1) * Real.log x with hf_def
  set f' : ℝ → ℝ := fun x => (s - 1) / x with hf'_def
  set g : ℝ → ℝ := fun u => (Real.log u - Real.log (s - 1)) * Real.exp (-u) with hg_def
  -- f 1 = 0
  have hf1 : f 1 = 0 := by simp [hf_def]
  -- ContinuousOn f (Set.Ici 1)
  have hf_cont : ContinuousOn f (Set.Ici 1) := by
    apply ContinuousOn.mul continuousOn_const
    apply Real.continuousOn_log.mono
    intro x hx
    simp only [Set.mem_Ici] at hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    linarith
  -- Tendsto f atTop atTop
  have hft : Tendsto f atTop atTop := by
    apply Filter.Tendsto.const_mul_atTop hs0
    exact Real.tendsto_log_atTop
  -- HasDerivWithinAt f (f' x) (Set.Ioi x) x for x ∈ Set.Ioi 1
  have hff' : ∀ x ∈ Set.Ioi (1:ℝ), HasDerivWithinAt f (f' x) (Set.Ioi x) x := by
    intro x hx
    simp only [Set.mem_Ioi] at hx
    have hxne : x ≠ 0 := by linarith
    have := (Real.hasDerivAt_log hxne).const_mul (s - 1)
    have h2 : HasDerivAt f ((s - 1) * x⁻¹) x := this
    have : (s - 1) * x⁻¹ = f' x := by rw [hf'_def]; field_simp
    rw [this] at h2
    exact h2.hasDerivWithinAt
  -- image facts: f strictly mono on Set.Ici 1
  have hmono : StrictMonoOn f (Set.Ici 1) := by
    intro a ha b hb hab
    simp only [Set.mem_Ici] at ha hb
    apply mul_lt_mul_of_pos_left _ hs0
    exact Real.log_lt_log (by linarith) hab
  have himg_Ioi : f '' Set.Ioi 1 = Set.Ioi 0 := by
    ext y
    simp only [Set.mem_image, Set.mem_Ioi]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have : 0 < Real.log x := Real.log_pos hx
      positivity
    · intro hy
      refine ⟨Real.exp (y / (s - 1)), ?_, ?_⟩
      · exact Real.one_lt_exp_iff.mpr (div_pos hy hs0)
      · rw [hf_def]
        simp only [Real.log_exp]
        field_simp
  have himg_Ici : f '' Set.Ici 1 = Set.Ici 0 := by
    ext y
    simp only [Set.mem_image, Set.mem_Ici]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have : 0 ≤ Real.log x := Real.log_nonneg hx
      rw [hf_def]; positivity
    · intro hy
      refine ⟨Real.exp (y / (s - 1)), ?_, ?_⟩
      · exact Real.one_le_exp_iff.mpr (div_nonneg hy hs0.le)
      · rw [hf_def]
        simp only [Real.log_exp]
        field_simp
  -- ContinuousOn g (f '' Set.Ioi 1) = ContinuousOn g (Set.Ioi 0)
  have hg_cont : ContinuousOn g (f '' Set.Ioi 1) := by
    rw [himg_Ioi]
    apply ContinuousOn.mul
    · apply ContinuousOn.sub _ continuousOn_const
      apply Real.continuousOn_log.mono
      intro u hu
      simp only [Set.mem_Ioi] at hu
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      linarith
    · exact (Real.continuous_exp.comp continuous_neg).continuousOn
  -- IntegrableOn g (f '' Set.Ici 1) = IntegrableOn g (Set.Ici 0)
  have hg1 : IntegrableOn g (f '' Set.Ici 1) := by
    rw [himg_Ici, integrableOn_Ici_iff_integrableOn_Ioi]
    have e1 : IntegrableOn (fun u => Real.log u * Real.exp (-u)) (Set.Ioi 0) :=
      integrableOn_log_mul_exp_neg
    have e2 : IntegrableOn (fun u => Real.log (s - 1) * Real.exp (-u)) (Set.Ioi 0) :=
      (integrableOn_exp_neg_Ioi 0).const_mul _
    have : g = fun u => Real.log u * Real.exp (-u) - Real.log (s - 1) * Real.exp (-u) := by
      funext u; rw [hg_def]; ring
    rw [this]
    exact e1.sub e2
  -- IntegrableOn (fun x => (g ∘ f) x * f' x) (Set.Ici 1)
  have hg2 : IntegrableOn (fun x => (g ∘ f) x * f' x) (Set.Ici 1) := by
    -- HasDerivWithinAt f (f' x) (Set.Ici 1) x for x ∈ Set.Ici 1.
    have hff'_Ici : ∀ x ∈ Set.Ici (1:ℝ), HasDerivWithinAt f (f' x) (Set.Ici 1) x := by
      intro x hx
      simp only [Set.mem_Ici] at hx
      have hxne : x ≠ 0 := by linarith
      have hd : HasDerivAt f ((s - 1) * x⁻¹) x := (Real.hasDerivAt_log hxne).const_mul (s - 1)
      have heq : (s - 1) * x⁻¹ = f' x := by rw [hf'_def]; field_simp
      rw [heq] at hd
      exact hd.hasDerivWithinAt
    -- f injective on Set.Ici 1.
    have hinj : Set.InjOn f (Set.Ici 1) := hmono.injOn
    -- transfer hg1 through the integrability change of variables.
    have hiff := integrableOn_image_iff_integrableOn_abs_deriv_smul
      (s := Set.Ici (1:ℝ)) (f := f) (f' := f') measurableSet_Ici hff'_Ici hinj g
    rw [hiff] at hg1
    -- relate to our integrand on Set.Ici 1.
    apply hg1.congr
    filter_upwards [self_mem_ae_restrict measurableSet_Ici] with x hx
    simp only [Set.mem_Ici] at hx
    have hxpos : (0:ℝ) < x := by linarith
    have hf'pos : 0 < f' x := by rw [hf'_def]; positivity
    simp only [smul_eq_mul, Function.comp, abs_of_pos hf'pos]
    ring
  -- Apply change of variables.
  have hcov := integral_comp_mul_deriv_Ioi hf_cont hft hff' hg_cont hg1 hg2
  rw [hf1] at hcov
  -- RHS: ∫ u in Set.Ioi 0, g u = deriv Gamma 1 - log (s-1)
  have hrhs : ∫ u in Set.Ioi (0:ℝ), g u = deriv Real.Gamma 1 - Real.log (s - 1) := by
    have e1 : IntegrableOn (fun u => Real.log u * Real.exp (-u)) (Set.Ioi 0) :=
      integrableOn_log_mul_exp_neg
    have e2 : IntegrableOn (fun u => Real.log (s - 1) * Real.exp (-u)) (Set.Ioi 0) :=
      (integrableOn_exp_neg_Ioi 0).const_mul _
    have hsplit : (fun u => g u)
        = fun u => Real.log u * Real.exp (-u) - Real.log (s - 1) * Real.exp (-u) := by
      funext u; rw [hg_def]; ring
    rw [show (∫ u in Set.Ioi (0:ℝ), g u)
        = ∫ u in Set.Ioi (0:ℝ), (Real.log u * Real.exp (-u) - Real.log (s - 1) * Real.exp (-u))
        from by rw [hsplit]]
    rw [integral_sub e1 e2, integral_log_mul_exp_neg_eq_deriv_Gamma]
    rw [integral_const_mul, integral_exp_neg_Ioi_zero, mul_one]
  -- LHS: ∫ x in Set.Ioi 1, (g∘f) x * f' x = (s-1) * ∫ x in Set.Ioi 1, log(log x) * x^(-s)
  have hlhs : ∫ x in Set.Ioi (1:ℝ), (g ∘ f) x * f' x
      = (s - 1) * ∫ x in Set.Ioi (1:ℝ), Real.log (Real.log x) * x ^ (-s) := by
    have hpt : ∀ x ∈ Set.Ioi (1:ℝ), (g ∘ f) x * f' x
        = (s - 1) * (Real.log (Real.log x) * x ^ (-s)) := by
      intro x hx
      simp only [Set.mem_Ioi] at hx
      have hxpos : (0:ℝ) < x := by linarith
      have hlogpos : 0 < Real.log x := Real.log_pos hx
      have hlogne : Real.log x ≠ 0 := ne_of_gt hlogpos
      have hs1ne : s - 1 ≠ 0 := ne_of_gt hs0
      simp only [Function.comp, hf_def, hg_def, hf'_def]
      -- log ((s-1) * log x) - log (s-1) = log (log x)
      rw [Real.log_mul hs1ne hlogne]
      -- exp (-((s-1) * log x)) = x ^ (-(s-1))
      have hexp : Real.exp (-((s - 1) * Real.log x)) = x ^ (-(s - 1)) := by
        rw [Real.rpow_def_of_pos hxpos]
        ring_nf
      rw [hexp]
      -- x ^ (-(s-1)) * ((s-1)/x) = (s-1) * x^(-s)
      have hx1 : x ^ (-(s - 1)) * ((s - 1) / x) = (s - 1) * x ^ (-s) := by
        rw [div_eq_mul_inv, ← Real.rpow_neg_one x]
        rw [show x ^ (-(s - 1)) * ((s - 1) * x ^ (-1 : ℝ))
            = (s - 1) * (x ^ (-(s - 1)) * x ^ (-1 : ℝ)) by ring]
        rw [← Real.rpow_add hxpos]
        ring_nf
      rw [show (Real.log (s - 1) + Real.log (Real.log x) - Real.log (s - 1))
          = Real.log (Real.log x) by ring]
      linear_combination Real.log (Real.log x) * hx1
    rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul]
  rw [hlhs, hrhs] at hcov
  rw [hcov]
  ring

end Issue1584

namespace Mertens

open Real Finset Filter Asymptotics Topology
open ArithmeticFunction hiding log

lemma sum_Ioc_one_eq_sum_Ioc_zero {f : ℕ → ℝ} {x : ℕ} (hx : 1 ≤ x) (hf : f 1 = 0) :
    ∑ n ∈ Ioc 1 x, f n = ∑ n ∈ Ioc 0 x, f n := by
  rw [(by rfl : Ioc 0 x = Icc 1 x), ← add_sum_Ioc_eq_sum_Icc hx]
  simpa

theorem sum_log_le {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log n ≤ x * log x := by
  calc
  _ ≤ ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log x := by
    refine sum_le_sum fun n hn ↦ ?_
    simp only [mem_Ioc] at hn
    exact log_le_log (by exact_mod_cast hn.1) (Nat.le_floor_iff (by linarith)|>.mp hn.2)
  _ = ⌊x⌋₊ * log x := by simp
  _ ≤ _ := by
    gcongr
    · exact log_nonneg hx
    · exact Nat.floor_le (by linarith)


lemma integral_log_le {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    ∫ t in a..b, log t ≤ log b * (b - a) := by
  apply le_of_abs_le
  have : ∀ t ∈ Set.uIoc a b, ‖log t‖ ≤ log b := by
    intro t ht
    rw [Set.uIoc_of_le hab, Set.mem_Ioc] at ht
    rw [norm_of_nonneg <| log_nonneg (by linarith)]
    gcongr <;> linarith
  grw [← norm_eq_abs, intervalIntegral.norm_integral_le_of_norm_le_const this,
    abs_of_nonneg (by linarith)]

theorem sum_log_ge {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log n ≥ x * log x - 2 * x := by
  have one_le_floor : 1 ≤ ⌊x⌋₊ := by simpa
  calc
  _ = ∑ n ∈ Icc 1 ⌊ x ⌋₊, log n := by rfl
  _ = ∑ n ∈ Ico (1 + 1) (⌊ x ⌋₊ + 1), log n := by
    rw [← add_sum_Ioc_eq_sum_Icc one_le_floor]
    simp
    rfl
  _ = ∑ n ∈ Ico 1 ⌊ x ⌋₊, log ((n + 1 : ℕ)) := by
    rw [← Finset.sum_Ico_add']
  _ ≥ ∫ t in 1..⌊x⌋₊, log t := by
    convert MonotoneOn.integral_le_sum_Ico one_le_floor ?_|>.ge
    · norm_cast
    · exact StrictMonoOn.monotoneOn (strictMonoOn_log.mono fun y hy ↦ (by simp_all; linarith))
  _ = (∫ t in 1..x, log t) - ∫ t in ⌊x⌋₊..x, log t := by
    nth_rw 3 [intervalIntegral.integral_symm]
    rw [sub_neg_eq_add, intervalIntegral.integral_add_adjacent_intervals] <;> exact intervalIntegral.intervalIntegrable_log'
  _ ≥ (∫ t in 1..x, log t) - log x := by
    gcongr
    grw [integral_log_le (by simpa) (Nat.floor_le (by linarith))]
    nth_rw 2 [← mul_one (log x)]
    gcongr
    · exact log_nonneg hx
    · linarith [Nat.lt_floor_add_one x]
  _ ≥ x * log x - x - log x := by simp only [integral_log, log_one, mul_zero, sub_zero, ge_iff_le,
    tsub_le_iff_right, sub_add_cancel, le_add_iff_nonneg_right, zero_le_one]
  _ ≥ _ := by linarith [log_le_self (by linarith : 0 ≤ x)]

theorem sum_log_eq_log_factorial (x : ℝ) :
    ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log n = log (Nat.floor x).factorial := by
    rw [←prod_Ico_id_eq_factorial, ←log_prod, prod_natCast]
    · congr
    intro x hx
    simp at hx ⊢; grind

theorem sum_log_eq_sum_mangoldt {x : ℝ} :
    ∑ n ∈ Ioc 0 ⌊x⌋₊, log n = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * ⌊x / d⌋₊ := by
  have : ∀ n : ℕ, log n = (Λ * zeta) n := by simp [vonMangoldt_mul_zeta]
  simp_rw [this, sum_Ioc_mul_zeta_eq_sum, ← Nat.floor_div_natCast]

noncomputable abbrev E₁Λ (x : ℝ) : ℝ := ∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / d - log x

theorem sum_mangoldt_div_eq (x : ℝ) : ∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / d = log x + E₁Λ x := by
    grind

theorem E₁Λ.ge {x : ℝ} (hx : 1 ≤ x) :
    E₁Λ x  ≥ -2 := by
  unfold E₁Λ
  suffices x * ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d  ≥ x * (log x - 2) by
    linarith [le_of_mul_le_mul_left this (by linarith)]
  calc
  _ = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (x / d) := by
    rw [Finset.mul_sum]
    ring_nf
  _ ≥ ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * ⌊x / d⌋₊ := by
    gcongr
    exact Nat.floor_le <| div_nonneg (by linarith) (by linarith)
  _ ≥ x * log x - 2 * x :=
    sum_log_eq_sum_mangoldt ▸ sum_log_ge hx
  _ = _ := by ring



theorem E₁Λ.le {x : ℝ} (hx : 1 ≤ x) :
    E₁Λ x ≤ log 4 + 4 := by
  unfold E₁Λ
  suffices x * ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d ≤ x * (log x + log 4 + 4) by
    linarith [le_of_mul_le_mul_left this (by linarith)]
  calc
  _ = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (x / d) := by
    rw [Finset.mul_sum]
    ring_nf
  _ ≤ ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (⌊x / d⌋₊ + 1) := by
    gcongr
    exact Nat.lt_floor_add_one _|>.le
  _ = (∑ d ∈ Ioc 0 ⌊x⌋₊, log d) + ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d := by
    simp_rw [mul_add, mul_one]
    rw [Finset.sum_add_distrib, sum_log_eq_sum_mangoldt]
  _ ≤ x * log x + (log 4 + 4) * x := by
    gcongr
    · exact sum_log_le hx
    · exact Chebyshev.psi_le_const_mul_self (by linarith)
  _ = _ := by ring

theorem sum_mangoldt_div_eq_log {x : ℝ} (hx : 1 ≤ x) :
    |∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / d - log x| ≤ log 4 + 4 := by
  grind [E₁Λ.le hx, E₁Λ.ge hx, log_nonneg]

theorem E₁Λ.bounded' : ∃ c > 0, ∀ x ≥ 1, |E₁Λ x| ≤ c := by
  exact ⟨log 4 + 4, (by positivity), fun x hx ↦ sum_mangoldt_div_eq_log hx⟩



theorem E₁Λ.bounded : E₁Λ =O[atTop] (fun _ ↦ (1:ℝ)) := by
  simp only [isBigO_iff, norm_eq_abs, norm_one, mul_one,
    eventually_atTop]
  exact ⟨log 4 + 4, 1, fun _ hx ↦ sum_mangoldt_div_eq_log hx⟩

theorem one_eq_o_log : (fun _ ↦ (1:ℝ)) =o[atTop] (fun x ↦ log x) := by
    simp only [isLittleO_one_left_iff, norm_eq_abs]
    exact tendsto_abs_atTop_atTop.comp tendsto_log_atTop

theorem sum_mangoldt_div_eq_log' :
    (fun x ↦ ∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / d) ~[atTop] (fun x ↦ log x) := by
    apply IsLittleO.isEquivalent (IsBigO.trans_isLittleO _ one_eq_o_log)
    convert! E₁Λ.bounded using 1

noncomputable abbrev E₁p (x : ℝ) : ℝ := ∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (log p) / p - log x

theorem sum_log_prime_div_eq (x : ℝ) : ∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (log p) / p = log x + E₁p x := by
    grind

theorem E₁p.le_E₁Λ (x : ℝ) :
    E₁p x ≤ E₁Λ x := by
    unfold E₁p E₁Λ; rw [sum_filter]
    gcongr with p _
    split_ifs with hp
    · simp [vonMangoldt_apply_prime hp]
    have : 0 ≤ Λ p := vonMangoldt_nonneg
    positivity

theorem E₁p.le {x : ℝ} (hx : 1 ≤ x) :
    E₁p x ≤ log 4 + 4 := by
    linarith [E₁Λ.le hx, E₁p.le_E₁Λ x]

noncomputable abbrev E₁ : ℝ := ∑' p : ℕ, if p.Prime then (log p) / (p*(p-1)) else 0

lemma E₁.summand_nonneg (p : ℕ) : 0 ≤ if p.Prime then (log p) / (p*(p-1)) else 0 := by
  split_ifs with h
  · refine div_nonneg (log_natCast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) ?_)
    suffices 1 ≤ (p : ℝ) by linarith
    exact_mod_cast h.one_le
  · rfl

theorem E₁.summable : Summable (fun p : ℕ ↦ if p.Prime then (log p) / (p*(p-1)) else 0) := by
  refine (Real.summable_one_div_nat_rpow.mpr (by norm_num: 1 < (3 : ℝ) / 2)|>.const_div
    4).of_nonneg_of_le E₁.summand_nonneg fun n ↦ ?_
  split_ifs with h
  · grw [Real.log_le_rpow_div (Nat.cast_nonneg _) (by norm_num : 0 < (1 : ℝ) / 2)]
    · have denom : (n : ℝ) * ((n : ℝ) - 1) ≥ n ^ 2/ 2 := by
        rw [sq, mul_div_assoc]
        gcongr
        suffices (n : ℝ) ≥ 2 by linarith
        exact_mod_cast h.two_le
      grw [denom]
      · apply le_of_eq
        rw [← Real.rpow_natCast]
        field_simp
        rw [mul_div_assoc, ← Real.rpow_sub (mod_cast h.pos)]
        norm_num
        rw [Real.rpow_neg (Nat.cast_nonneg _)]
        field
      · exact div_pos (pow_pos (mod_cast h.pos) _) (by norm_num)
    · apply mul_nonneg (Nat.cast_nonneg _)
      suffices 1 ≤ (n : ℝ) by linarith
      exact_mod_cast h.one_le
  · positivity

private lemma antitoneOn_log_div_sq :
    AntitoneOn (fun t ↦ log (t + 2) / (t + 2) ^ 2) (Set.Ici 0) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
  · refine fun t ht ↦ ContinuousAt.continuousWithinAt ?_
    simp at ht
    have : (t + 2) ≠ 0 := by simp; linarith
    fun_prop (disch := grind)
  · refine fun t ht ↦ DifferentiableAt.differentiableWithinAt ?_
    simp at ht
    have : (t + 2) ^ 2 ≠ 0 := by simp; grind
    fun_prop (disch := grind)
  · intro t ht
    simp at ht
    rw [deriv_fun_div (by fun_prop (disch := grind)) (by fun_prop) (by simp; grind), deriv_comp_add_const, deriv_log]
    simp
    field_simp
    simp only [mul_zero, tsub_le_iff_right, zero_add]
    rw [← log_rpow (by linarith), ← log_exp 1, rpow_ofNat]
    gcongr
    nlinarith [exp_one_lt_three]

private lemma log_div_sq_nonneg :
    ∀ t ∈ Set.Ioi 0, 0 ≤ log (t + 2) / (t + 2) ^ 2 := by
  exact fun t ht ↦  div_nonneg (log_nonneg (by simp_all; linarith)) (by positivity)

private lemma log_div_sq_is_deriv :
    ∀ x ∈ Set.Ici 0, HasDerivAt (fun t ↦ (-log (t + 2) - 1) / (t + 2)) (log (x + 2) / (x + 2) ^ 2) x := by
  intro t ht
  simp at ht
  apply HasDerivAt.comp_add_const (f := (fun t ↦ (-log t - 1)/ t)) t 2
  convert! HasDerivAt.fun_div (c' := -1 / (t + 2)) (d' := (1 : ℝ)) _ _  _ using 1
  · field
  · apply HasDerivAt.sub_const
    convert! (hasDerivAt_log (by linarith : t + 2 ≠ 0)).neg using 1
    ring_nf
  · exact hasDerivAt_id _
  · linarith

private lemma tendsto_antideriv_log_div_sq :
    Tendsto (fun t ↦ (-log (t + 2) - 1) / (t + 2)) atTop (nhds 0) := by
  have : Tendsto (fun (t : ℝ) ↦ t + 2) atTop atTop := by exact tendsto_atTop_add_const_right atTop 2 tendsto_id
  apply Tendsto.comp (g := (fun t ↦ (-log t - 1) / t)) _ this
  convert! Tendsto.sub (f := (fun t ↦ -log t / t)) (a := 0) _ tendsto_inv_atTop_zero using 1
  · ring_nf
  · ring_nf
  · convert! (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by linarith)).neg using 1
    · ext; ring

private lemma integrableOn_log_div_sq :
    MeasureTheory.IntegrableOn (fun t ↦ log (t + 2) / (t + 2) ^ 2) (Set.Ioi 0) := by
  exact MeasureTheory.integrableOn_Ioi_deriv_of_nonneg' log_div_sq_is_deriv log_div_sq_nonneg tendsto_antideriv_log_div_sq

private lemma integral_log_div_sq :
    ∫ t in Set.Ioi 0, log (t + 2) / (t + 2) ^ 2 = (log 2 + 1) / 2 := by
  rw [MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg' log_div_sq_is_deriv log_div_sq_nonneg tendsto_antideriv_log_div_sq]
  ring_nf

private lemma summable_log_div_sq :
    Summable (fun (n : ℕ)↦ log (n + 3) / (n + 3) ^ 2) := by
  let g : ℝ → ℝ := (fun n ↦ log (n + 2) / (n + 2) ^ 2)
  suffices Summable (fun (n : ℕ) ↦ g n ) by
    convert! summable_nat_add_iff 1|>.mpr this using 2
    unfold g
    push_cast
    ring_nf
  exact antitoneOn_log_div_sq.summable_of_integrableOn_Ioi_zero integrableOn_log_div_sq log_div_sq_nonneg

private lemma sum_log_div_sq_le :
    ∑' (n : ℕ), log (n + 3) / (n + 3) ^2 ≤ (log 2 + 1) / 2 := by
  let g : ℝ → ℝ := (fun n ↦ log (n + 2) / (n + 2) ^ 2)
  calc
  _ = ∑' (n : ℕ), g (n + 1 : ℕ):= by
    unfold g
    congr
    push_cast
    ring_nf
  _ ≤ ∫ x in Set.Ioi 0, g x := by
    exact antitoneOn_log_div_sq.tsum_add_one_le_integral integrableOn_log_div_sq log_div_sq_nonneg
  _ = _ := by
    exact integral_log_div_sq

theorem E₁.le : E₁ ≤ (5 * log 2 + 3) / 4 := by
  unfold E₁
  calc
  _ = log 2 / 2 + ∑' (n : ℕ), if (n + 3).Prime then log (n + 3) / ((n + 3) * (n + 2)) else 0 := by
    rw [← E₁.summable.sum_add_tsum_nat_add 3, (by rfl : range 3 = {0, 1, 2})]
    simp [Nat.prime_two]
    ring_nf
  _ ≤ log 2 / 2 + ∑' (n : ℕ), (3 / 2) * (log (n + 3) / (n + 3) ^ 2) := by
    gcongr with n
    · convert! summable_nat_add_iff 3|>.mpr E₁.summable using 4
      · norm_cast
      · push_cast; ring
    · exact summable_log_div_sq.mul_left _
    · split_ifs with h
      · grw [(by linarith : (n + 2 : ℝ) ≥ 2 * (n + 3) / 3)]
        · field_simp
          rfl
        · exact log_nonneg (by grind)
      · exact mul_nonneg (by norm_num) (div_nonneg (log_nonneg (by grind)) (by positivity))
  _ = log 2 / 2 + (3 / 2) * ∑' (n : ℕ), log (n + 3) / (n + 3) ^ 2 := by
    rw [tsum_mul_left]
  _ ≤ _ := by
    grw [sum_log_div_sq_le]
    ring_nf
    rfl

theorem E₁.nonneg : E₁ ≥ 0 :=
  tsum_nonneg E₁.summand_nonneg

theorem E₁Λ.le_E₁p_add_E₁ {x : ℝ} (hx : 1 ≤ x) :
    E₁Λ x ≤ E₁p x + E₁ := by
  unfold E₁Λ E₁p
  suffices ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d ≤ ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / p + E₁ by linarith
  simp_rw [vonMangoldt_apply, ite_div, zero_div, ← sum_filter, Chebyshev.sum_PrimePow_eq_sum_sum _ (by linarith)]
  calc
  _ = ∑ k ∈ Icc 1 ⌊log x / log 2⌋₊, ∑ p ∈ Ioc 0 ⌊x ^ (1 / (k : ℝ))⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    refine sum_congr rfl fun k hk ↦ sum_congr rfl fun p hp ↦ ?_
    rw [Nat.Prime.pow_minFac (by simp_all) (by simp_all; linarith)]
  _ ≤ ∑ k ∈ Icc 1 ⌊log x / log 2⌋₊, ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    gcongr with k hk
    apply rpow_le_self_of_one_le hx
    simp only [mem_Icc] at hk
    exact div_le_one₀ (by norm_cast; linarith)|>.mpr (mod_cast hk.1)
  _ ≤ ∑ k ∈ Icc 1 (max 1 ⌊log x / log 2⌋₊), ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    apply sum_le_sum_of_subset_of_nonneg
    · gcongr
      exact le_max_right ..
    · exact fun _ _ _ ↦ sum_nonneg fun _ _ ↦ (by positivity)
  _ = ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, (log p / p) + ∑ k ∈ Ioc 1 (max 1 ⌊log x / log 2⌋₊), ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    rw [← add_sum_Ioc_eq_sum_Icc (le_max_left ..)]
    simp
  _ ≤ _ := by
    gcongr
    rw [sum_comm]
    conv => lhs; arg 2; ext p; arg 2; ext k; rw [← mul_one_div, Nat.cast_pow, ← one_div_pow]
    simp_rw [← mul_sum]
    calc
    _ ≤ ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p * (p - 1)) := by
      gcongr with p hp
      simp only [mem_filter, mem_Ioc] at hp
      conv => rhs; rw [← mul_one_div]
      gcongr
      rw [(by rfl : Ioc 1 (max 1 ⌊log x / log 2⌋₊) = Ico 2 (max 1 ⌊log x / log 2⌋₊  + 1))]
      grw [geom_sum_Ico_le_of_lt_one (by simp)]
      · apply le_of_eq
        have : (p : ℝ) ≠ 0 := by exact_mod_cast hp.1.1.ne.symm
        field
      · simpa using inv_lt_one_of_one_lt₀ (mod_cast hp.2.one_lt)
    _ ≤ _ := by
      rw [sum_filter]
      exact E₁.summable.sum_le_tsum _ fun p hp ↦ E₁.summand_nonneg p

theorem E₁p.ge {x : ℝ} (hx : 1 ≤ x) :
    E₁p x ≥ -2 - E₁ := by
    linarith [E₁Λ.le_E₁p_add_E₁ hx, E₁Λ.ge hx]


theorem sum_log_prime_div_eq_log {x : ℝ} (hx : 1 ≤ x) :
    |∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (log p) / p - log x| ≤ log 4 + 4 := by
    rw [abs_le']
    refine ⟨ E₁p.le hx, ?_ ⟩
    have : log 2 > 0 := by apply log_pos; norm_num
    have : log 4 = 2 * log 2 := by rw [←Real.log_rpow (by norm_num)]; norm_num
    grind [E₁p.ge hx, E₁.le]

theorem E₁p.bounded : ∃ c > 0, ∀ x ≥ 1, |E₁p x| ≤ c := by
  exact ⟨log 4 + 4, (by positivity), fun _ hx ↦ sum_log_prime_div_eq_log  hx⟩

theorem sum_log_prime_div_eq_log' : E₁p =O[atTop] (fun _ ↦ (1:ℝ)) := by
    simp only [isBigO_iff, norm_eq_abs, one_mem, CStarRing.norm_of_mem_unitary, mul_one,
      eventually_atTop, E₁p]
    exact ⟨ log 4 + 4, 1, fun _ ↦ sum_log_prime_div_eq_log ⟩

theorem sum_log_prime_div_eq_log'' : (fun x ↦ ∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (log p) / p) ~[atTop] (fun x ↦ log x) := by
    apply IsLittleO.isEquivalent (IsBigO.trans_isLittleO _ one_eq_o_log)
    convert! sum_log_prime_div_eq_log' using 1

noncomputable abbrev γ : ℝ := (∫ t in Set.Ioi 2, E₁Λ t / (t * log t^2)) + 1 - log (log 2)

noncomputable abbrev E₂Λ (x : ℝ) : ℝ := ∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / (d * log d) - log (log x) - γ

lemma sum_Ioc_one_eq_sum_Icc_zero {f : ℕ → ℝ} {x : ℕ} (hx : 1 ≤ x) (hf1 : f 1 = 0) (hf0 : f 0 = 0) :
    ∑ n ∈ Ioc 1 x, f n = ∑ n ∈ Icc 0 x, f n := by
  rw [sum_Ioc_one_eq_sum_Ioc_zero hx hf1, ← add_sum_Ioc_eq_sum_Icc (by linarith)]
  simpa

private theorem sum_div_log_eq {x : ℝ} (hx : 2 ≤ x) (f : ℕ → ℝ) :
    ∑ n ∈ Ioc 1 ⌊ x ⌋₊, f n / log n =
      (∑ n ∈ Ioc 1 ⌊ x ⌋₊, f n) / log x + ∫ t in 2..x, (∑ n ∈ Ioc 1 ⌊ t ⌋₊, f n) / (t * log t^2) := by
  let g : ℕ → ℝ := (fun n ↦ if n < 2 then 0 else f n)
  trans ∑ n ∈ Icc 0 ⌊ x ⌋₊, (log n)⁻¹ * g n
  · rw [← sum_Ioc_one_eq_sum_Icc_zero (Nat.le_floor (by grind)) (by simp) (by simp)]
    refine sum_congr rfl fun n hn ↦ ?_
    have : ¬(n ≤ 1) := by simp_all
    simp [g, this]
    field
  rw [sum_mul_eq_sub_integral_mul₁ g (f := (fun n ↦ (log n)⁻¹)) (by simp [g]) (by simp [g])]
  · rw [intervalIntegral.integral_of_le hx, mul_comm, ← div_eq_mul_inv, ← sub_neg_eq_add]
    simp_rw [deriv_inv_log]
    congr 1
    · rw [← sum_Ioc_one_eq_sum_Icc_zero (Nat.le_floor (by grind)) (by simp [g]) (by simp [g])]
      congr 1
      refine sum_congr rfl fun n hn ↦ ?_
      simp only [mem_Ioc] at hn
      have : ¬(n ≤ 1) := by linarith
      simp [g, this]
    · rw [← MeasureTheory.integral_neg]
      refine  MeasureTheory.setIntegral_congr_fun (by measurability) fun t ht ↦ ?_
      simp only [Set.mem_Ioc] at ht
      rw [← sum_Ioc_one_eq_sum_Icc_zero (Nat.le_floor (by grind)) (by simp [g]) (by simp [g])]
      field_simp
      congr 2
      refine sum_congr rfl fun n hn ↦ ?_
      simp only [mem_Ioc] at hn
      have : ¬(n ≤ 1) := by linarith
      simp [g, this]
  · intro t ht
    simp only [Set.mem_Icc] at ht
    have : log t ≠ 0 := by simp; grind
    fun_prop (disch := grind)
  · refine ContinuousOn.integrableOn_Icc fun t ht ↦ ContinuousAt.continuousWithinAt ?_
    simp only [Set.mem_Icc] at ht
    conv => arg 1; ext x; rw [deriv_inv_log]
    have : log t ^2 ≠ 0 := by simp; grind
    fun_prop (disch := grind)

private theorem integrable_const_div_mul_log_sq {x : ℝ} (c : ℝ) (hx : 2 ≤ x) :
    MeasureTheory.IntegrableOn (fun x ↦ c / (x * log x ^ 2)) (Set.Ioi x) MeasureTheory.volume := by
  conv => arg 1; ext t; rw [← mul_one_div]
  apply MeasureTheory.Integrable.const_mul
  refine MeasureTheory.integrableOn_Ioi_deriv_of_nonneg' ?_ ?_ tendsto_log_atTop.inv_tendsto_atTop.neg
  · intro t ht
    simp only [Set.mem_Ici] at ht
    have : log t ≠ 0 := by simp; grind
    have : DifferentiableAt ℝ (fun t ↦ -(log t)⁻¹) t := by
      fun_prop (disch := grind)
    convert! this.hasDerivAt using 1
    simp [deriv_inv_log]
    field
  · intro t ht
    simp only [Set.mem_Ioi] at ht
    exact one_div_nonneg.mpr <| mul_nonneg (by linarith) (sq_nonneg _)

private theorem floor_measurable (f : ℕ → ℝ) : Measurable (fun x : ℝ => f ⌊x⌋₊) :=
  (show Measurable f from measurable_from_top).comp Nat.measurable_floor

private theorem m1_measurable : Measurable E₁Λ :=
  (floor_measurable (fun n => ∑ d ∈ Ioc 0 n, (Λ d) / d)).sub Real.measurable_log

private theorem p1_measurable : Measurable E₁p :=
  (floor_measurable (fun n => ∑ p ∈ Ioc 0 n with p.Prime, (log p) / p)).sub Real.measurable_log

private theorem m2_measurable : Measurable E₂Λ :=
  (((floor_measurable (fun n => ∑ d ∈ Ioc 0 n, (Λ d) / (d * log d))).sub
    (Real.measurable_log.comp Real.measurable_log)).sub measurable_const)

private theorem integrable_E₁Λ_div_mul_log_sq {x : ℝ} (hx : 2 ≤ x) :
    MeasureTheory.IntegrableOn (fun x ↦ E₁Λ x / (x * log x ^ 2)) (Set.Ioi x) MeasureTheory.volume := by
  obtain ⟨c, hc1, hc2⟩ := E₁Λ.bounded'
  apply MeasureTheory.Integrable.mono (integrable_const_div_mul_log_sq c hx)
  · exact (m1_measurable.div (measurable_id.mul (Real.measurable_log.pow_const 2))).aestronglyMeasurable
  · filter_upwards [MeasureTheory.ae_restrict_mem (by measurability)] with t ht
    simp only [Set.mem_Ioi] at ht
    simp only [norm_div, norm_eq_abs, norm_mul, norm_pow, sq_abs, abs_of_pos hc1]
    gcongr
    exact hc2 t (by linarith)

private theorem integrable_E₁p_div_mul_log_sq {x : ℝ} (hx : 2 ≤ x) :
    MeasureTheory.IntegrableOn (fun x ↦ E₁p x / (x * log x ^ 2)) (Set.Ioi x) MeasureTheory.volume := by
  obtain ⟨c, hc1, hc2⟩ := E₁p.bounded
  apply MeasureTheory.Integrable.mono (integrable_const_div_mul_log_sq c hx)
  · exact (p1_measurable.div (measurable_id.mul (Real.measurable_log.pow_const 2))).aestronglyMeasurable
  · filter_upwards [MeasureTheory.ae_restrict_mem (by measurability)] with t ht
    simp only [Set.mem_Ioi] at ht
    simp only [norm_div, norm_eq_abs, norm_mul, norm_pow, sq_abs, abs_of_pos hc1]
    gcongr
    exact hc2 t (by linarith)

lemma deriv_log_log {x : ℝ} (hx : 1 < x) :
    deriv (fun t ↦ log (log t)) x = 1 / (x * log x) := by
  rw [deriv.log (differentiableAt_log (by linarith)) (by simp; grind), deriv_log]
  field

lemma integral_one_div_mul_log {x : ℝ} (hx : 2 ≤ x) :
    ∫ t in 2..x, 1 / (t * log t) = log (log x) - log (log 2) := by
  rw [← intervalIntegral.integral_deriv_eq_sub (f := fun t ↦ log (log t))]
  · refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [deriv_log_log]
    rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
    linarith
  · intro t ht
    rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
    have : log t ≠ 0 := by simp; grind
    fun_prop (disch := grind)
  · refine ContinuousOn.intervalIntegrable ?_
    apply ContinuousOn.congr (f := (fun t ↦ 1 / (t * log t)))
    · refine fun t ht ↦ ContinuousAt.continuousWithinAt ?_
      rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
      have : log t ≠ 0 := by simp; grind
      fun_prop (disch := grind)
    · intro t ht
      rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
      exact deriv_log_log (by linarith)

lemma intervalIntegrable_one_div_mul_log {x : ℝ} (hx : 2 ≤ x) :
    IntervalIntegrable (fun t ↦ 1 / (t * log t)) MeasureTheory.volume 2 x := by
  refine ContinuousOn.intervalIntegrable fun t ht ↦ ContinuousAt.continuousWithinAt ?_
  rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
  have : log t ≠ 0 := by simp; grind
  fun_prop (disch := grind)

theorem E₂Λ.eq {x : ℝ} (hx : 2 ≤ x) :
    E₂Λ x = E₁Λ x / log x - ∫ t in Set.Ioi x, E₁Λ t / (t * log t^2) := by
  unfold E₂Λ
  rw [← sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp)]
  conv => lhs; arg 1; arg 1; arg 2; ext n; rw [(by field : Λ n / (n * log n) = (Λ n / n) / log n)]
  rw [sum_div_log_eq hx]
  rw [sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp), sum_mangoldt_div_eq]
  have : ∫ t in 2..x, (∑ n ∈ Ioc 1 ⌊t⌋₊, Λ n / n) / (t * log t ^ 2) = ∫ t in 2..x, (1 / (t * log t) + E₁Λ t / (t * log t ^ 2)) := by
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
    rw [sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp), sum_mangoldt_div_eq]
    field
  rw [this, intervalIntegral.integral_add]
  · rw [integral_one_div_mul_log hx, add_div, div_self (by simp; grind)]
    unfold γ
    calc
    _ = E₁Λ x / log x + (∫ (x : ℝ) in 2..x, E₁Λ x / (x * log x ^ 2)) -
      ((∫ (t : ℝ) in Set.Ioi 2, E₁Λ t / (t * log t ^ 2))) := by ring
    _ = _ := by
      rw [← intervalIntegral.integral_interval_add_Ioi (integrable_E₁Λ_div_mul_log_sq (by rfl)) (integrable_E₁Λ_div_mul_log_sq hx)]
      ring
  · exact intervalIntegrable_one_div_mul_log hx
  · rw [intervalIntegrable_iff, Set.uIoc_of_le hx]
    exact integrable_E₁Λ_div_mul_log_sq (x := 2) (by rfl)|>.mono (by grind) (by rfl)

private theorem integ_div_mul_log_sq {x : ℝ} (c : ℝ) (hx : 2 ≤ x) :
    ∫ t in Set.Ioi x, c / (t * log t^2) = c / log x := by
    convert! MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto' (m := 0) (f := fun x ↦ - c / log x) ?_
      (integrable_const_div_mul_log_sq c hx) ?_ using 1
    · grind
    · intro t ht; simp at ht
      convert! HasDerivAt.fun_div (hasDerivAt_const _ (-c)) (hasDerivAt_log (by linarith)) ?_ using 1
      · grind
      simp; grind
    convert! tendsto_log_atTop.inv_tendsto_atTop.const_mul (-c) using 1
    simp

theorem E₂Λ.abs_le {x : ℝ} (hx : 2 ≤ x) :
    |E₂Λ x| ≤ (log 4 + 6) / log x := by
    have : 0 < log x := by apply log_pos; linarith
    rw [E₂Λ.eq hx, abs_le']
    constructor
    · grw [E₁Λ.le (by linarith)]
      have : ∫ t in Set.Ioi x, E₁Λ t / (t * log t^2) ≥ - 2 / log x := calc
        _ ≥ ∫ t in Set.Ioi x, (-2) / (t * log t^2) := by
          apply MeasureTheory.setIntegral_mono_on (integrable_const_div_mul_log_sq (-2) hx)
            (integrable_E₁Λ_div_mul_log_sq hx) (by measurability)
          intro y hy; simp at hy
          have : 1 < y := by linarith
          have : 0 < log y := log_pos this
          gcongr; exact E₁Λ.ge (by linarith)
        _ = _ := integ_div_mul_log_sq (-2) hx
      grw [this]
      grind
    grw [E₁Λ.ge (by linarith)]
    have : ∫ t in Set.Ioi x, E₁Λ t / (t * log t^2) ≤ (log 4 + 4) / log x := calc
        _ ≤ ∫ t in Set.Ioi x, (log 4 + 4) / (t * log t^2) := by
          apply MeasureTheory.setIntegral_mono_on (integrable_E₁Λ_div_mul_log_sq hx)
            (integrable_const_div_mul_log_sq (log 4 + 4) hx) (by measurability)
          intro y hy; simp at hy
          have : 1 < y := by linarith
          have : 0 < log y := log_pos this
          gcongr; exact E₁Λ.le (by linarith)
        _ = _ := integ_div_mul_log_sq (log 4 + 4) hx
    grw [this]
    grind


theorem E₂Λ.bound : E₂Λ =O[atTop] (fun x ↦ 1 / log x) := by
    simp only [one_div, isBigO_iff, norm_eq_abs, norm_inv, eventually_atTop]
    use log 4 + 6, 2
    intro x hx
    convert E₂Λ.abs_le hx using 1
    have : 0 < log x := by apply log_pos; linarith
    grind [abs_of_pos this]

theorem E₂Λ.bound' : E₂Λ =o[atTop] (fun _ ↦ (1:ℝ)) := E₂Λ.bound.trans_isLittleO inv_log_eq_o_one

theorem log_zeta_eq_sum (s : ℝ) (hs : 1 < s) :
    log (riemannZeta (s:ℂ)).re = ∑' n, Λ n / (n^s * log n) := by
  have hsc : (1 : ℝ) < ((s : ℂ)).re := by simpa using hs
  -- (II) Euler log product
  have hep := riemannZeta_eulerProduct_exp_log (s := (s : ℂ)) hsc
  set S : ℂ := ∑' p : Nat.Primes, -Complex.log (1 - (p : ℂ) ^ (-(s : ℂ))) with hS
  -- bridge: prime cpow equals real rpow
  have hcpow : ∀ p : Nat.Primes, (p : ℂ) ^ (-(s : ℂ)) = (((p : ℝ) ^ (-s) : ℝ) : ℂ) := by
    intro p
    rw [Complex.ofReal_cpow (by positivity)]
    push_cast; ring_nf
  -- the real value of each prime term
  set z : Nat.Primes → ℝ := fun p => (p : ℝ) ^ (-s) with hz
  -- z p ∈ (0,1)
  have hz_pos : ∀ p : Nat.Primes, 0 < z p := fun p => by
    have : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.pos
    positivity
  have hz_lt_one : ∀ p : Nat.Primes, z p < 1 := by
    intro p
    have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.one_lt
    change (p : ℝ) ^ (-s) < 1
    rw [Real.rpow_neg (by positivity), inv_lt_one_iff₀]
    right
    exact (Real.one_lt_rpow_iff_of_pos (by positivity)).mpr (Or.inl ⟨hp1, by linarith⟩)
  -- each summand is the ofReal of a real number
  have hterm : ∀ p : Nat.Primes,
      -Complex.log (1 - (p : ℂ) ^ (-(s : ℂ))) = ((-Real.log (1 - z p) : ℝ) : ℂ) := by
    intro p
    rw [hcpow p]
    have h1z : (0 : ℝ) < 1 - z p := by have := hz_lt_one p; linarith
    rw [show (1 : ℂ) - ((z p : ℝ) : ℂ) = (((1 - z p : ℝ)) : ℂ) by push_cast; ring]
    rw [← Complex.ofReal_log h1z.le]
    push_cast; ring
  -- (III) S is real: S = (Sr : ℂ) with Sr the real sum
  set Sr : ℝ := ∑' p : Nat.Primes, -Real.log (1 - z p) with hSr
  have hSeq : S = (Sr : ℂ) := by
    rw [hS, hSr, Complex.ofReal_tsum]
    exact tsum_congr hterm
  have hSim : S.im = 0 := by rw [hSeq]; exact Complex.ofReal_im _
  have hSre : S.re = Sr := by rw [hSeq]; exact Complex.ofReal_re _
  -- (IV) invert exp: log ζ = S
  have hlog_zeta : Complex.log (riemannZeta (s : ℂ)) = S := by
    rw [← hep, Complex.log_exp (by rw [hSim]; exact neg_lt_zero.mpr Real.pi_pos)
      (by rw [hSim]; exact Real.pi_pos.le)]
  -- relate Real.log ζ.re to S.re = Sr
  have hkey : Real.log (riemannZeta (s : ℂ)).re = Sr := by
    have hζim : (riemannZeta (s : ℂ)).im = 0 := riemannZeta_im_eq_zero_of_one_lt hs
    have hζeq : riemannZeta (s : ℂ) = ((riemannZeta (s : ℂ)).re : ℂ) := by
      apply Complex.ext <;> simp [hζim]
    have : Real.log (riemannZeta (s : ℂ)).re
        = (Complex.log (riemannZeta (s : ℂ))).re := by
      conv_rhs => rw [hζeq]
      rw [Complex.log_ofReal_re]
    rw [this, hlog_zeta, hSre]
  rw [hkey]
  -- now goal: Sr = ∑' n, Λ n / (n^s * log n)
  -- (V) expand each prime term via real Taylor series
  have habs : ∀ p : Nat.Primes, |z p| < 1 := by
    intro p
    rw [abs_of_pos (hz_pos p)]; exact hz_lt_one p
  have htaylor : ∀ p : Nat.Primes,
      HasSum (fun n : ℕ => (z p) ^ (n + 1) / (n + 1)) (-Real.log (1 - z p)) :=
    fun p => hasSum_pow_div_log_of_abs_lt_one (habs p)
  have hSr_double : Sr = ∑' (p : Nat.Primes) (n : ℕ), (z p) ^ (n + 1) / (n + 1) := by
    rw [hSr]
    exact tsum_congr fun p => ((htaylor p).tsum_eq).symm
  -- summability of the prime sum ∑ z p
  have hsummable_z : Summable z := Nat.Primes.summable_rpow.mpr (by linarith)
  -- summability of ∑ p, -log(1 - z p)
  have hsummable_prime : Summable (fun p : Nat.Primes => -Real.log (1 - z p)) := by
    have := Real.summable_log_one_add_of_summable hsummable_z.neg
    convert! this.neg using 1
  -- summability of g over the product
  have hg_nonneg : ∀ pk : Nat.Primes × ℕ, 0 ≤ (z pk.1) ^ (pk.2 + 1) / (pk.2 + 1) := by
    intro pk; positivity [hz_pos pk.1]
  have hsummable_g : Summable (fun pk : Nat.Primes × ℕ => (z pk.1) ^ (pk.2 + 1) / (pk.2 + 1)) := by
    rw [summable_prod_of_nonneg hg_nonneg]
    refine ⟨fun p => (htaylor p).summable, ?_⟩
    refine hsummable_prime.congr (fun p => ?_)
    exact ((htaylor p).tsum_eq).symm
  -- pointwise: F (p^(n+1)) = g (p, n)
  have hpoint : ∀ (p : Nat.Primes) (n : ℕ),
      Λ ((p : ℕ) ^ (n + 1)) /
        ((((p : ℕ) ^ (n + 1) : ℕ) : ℝ) ^ s * Real.log (((p : ℕ) ^ (n + 1) : ℕ) : ℝ))
      = (z p) ^ (n + 1) / (n + 1) := by
    intro p n
    have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.one_lt
    have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos hp1
    rw [vonMangoldt_apply_pow (Nat.succ_ne_zero n), vonMangoldt_apply_prime p.prop]
    have hcast : (((p : ℕ) ^ (n + 1) : ℕ) : ℝ) = (p : ℝ) ^ (n + 1) := by push_cast; ring
    rw [hcast, Real.log_pow]
    rw [show (z p) ^ (n + 1) = ((p : ℝ) ^ (n + 1)) ^ (-s) by
      rw [hz]; rw [← Real.rpow_natCast ((p : ℝ) ^ (-s)) (n + 1),
        ← Real.rpow_natCast ((p : ℝ)) (n + 1), ← Real.rpow_mul (by positivity),
        ← Real.rpow_mul (by positivity)]; ring_nf]
    rw [Real.rpow_neg (by positivity)]
    field_simp
    push_cast
    ring
  -- (VI) reindex via the prime-power equivalence
  set F : ℕ → ℝ := fun n => Λ n / ((n : ℝ) ^ s * Real.log n) with hF
  -- support of F is contained in prime powers
  have hsupp : Function.support F ⊆ {n : ℕ | IsPrimePow n} := by
    intro n hn
    rw [Function.mem_support] at hn
    simp only [Set.mem_ofPred_eq]
    by_contra hpp
    apply hn
    simp only [hF, vonMangoldt_eq_zero_iff.mpr hpp, zero_div]
  -- the product sum equals the subtype sum
  have hprod_eq : (∑' pk : Nat.Primes × ℕ, (z pk.1) ^ (pk.2 + 1) / (pk.2 + 1))
      = ∑' m : {n : ℕ // IsPrimePow n}, F m.val := by
    rw [← Equiv.tsum_eq Nat.Primes.prodNatEquiv (fun m : {n : ℕ // IsPrimePow n} => F m.val)]
    apply tsum_congr
    intro pk
    rw [Nat.Primes.coe_prodNatEquiv_apply, hF]
    exact (hpoint pk.1 pk.2).symm
  -- assemble
  rw [hSr_double, ← hsummable_g.tsum_prod' (fun p => (htaylor p).summable), hprod_eq]
  exact tsum_subtype_eq_of_support_subset hsupp

section
open MeasureTheory Set

-- Helpers for `log_zeta_eq_integ` (#1583): Abel summation / sum-integral interchange.
namespace LogZetaInteg

/-- The summatory coefficient `Λ d / (d log d)`. -/
private noncomputable def c (d : ℕ) : ℝ := Λ d / (d * Real.log d)

/-- The per-index integrand: `c d` times the rpow restricted to `Ici (d:ℝ)`. -/
private noncomputable def f (s : ℝ) (d : ℕ) (x : ℝ) : ℝ :=
    c d * (Set.Ici (d:ℝ)).indicator (fun x => x ^ (-s)) x

@[simp] private lemma c_zero : c 0 = 0 := by simp [c]
@[simp] private lemma c_one : c 1 = 0 := by simp [c, vonMangoldt_apply_one]

/-- `c d ≥ 0` for all `d`. -/
private lemma c_nonneg (d : ℕ) : 0 ≤ c d := by
  unfold c
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd; simp
  · apply div_nonneg vonMangoldt_nonneg
    have : (0:ℝ) ≤ (d:ℝ) := Nat.cast_nonneg d
    have hlog : 0 ≤ Real.log d := Real.log_natCast_nonneg d
    positivity

/-- General comparison majorant: `(log n)^a / n^s` is summable for any real `a` and `s > 1`,
since `(log x)^a = o(x^ε)` for every `ε > 0`. All the summability conditions below reduce to
this by domination. -/
private lemma summable_log_rpow_div_rpow (a : ℝ) {s : ℝ} (hs : 1 < s) :
    Summable (fun n : ℕ => (Real.log n) ^ a / (n:ℝ) ^ s) := by
  have hε : (0:ℝ) < (s - 1) / 2 := by linarith
  refine summable_of_isBigO_nat (g := fun n : ℕ => (n:ℝ) ^ ((s - 1) / 2 - s)) ?_ ?_
  · rw [Real.summable_nat_rpow]; linarith
  · have ho : (fun x : ℝ => (Real.log x) ^ a) =O[atTop] (fun x : ℝ => x ^ ((s - 1) / 2)) :=
      (isLittleO_log_rpow_rpow_atTop a hε).isBigO
    have hmul : (fun x : ℝ => (Real.log x) ^ a / x ^ s)
        =O[atTop] (fun x : ℝ => x ^ ((s - 1) / 2) / x ^ s) := by
      simpa only [div_eq_mul_inv] using ho.mul (isBigO_refl (fun x : ℝ => (x ^ s)⁻¹) atTop)
    have heq : (fun x : ℝ => x ^ ((s - 1) / 2) / x ^ s)
        =ᶠ[atTop] (fun x : ℝ => x ^ ((s - 1) / 2 - s)) := by
      filter_upwards [eventually_gt_atTop 0] with x hx
      rw [← Real.rpow_sub hx]
    exact (hmul.trans_eventuallyEq heq).natCast_atTop

/-- Real summability of `Λ n / n^s` for `s > 1`: dominated by `log n / n^s` via `Λ n ≤ log n`. -/
private lemma summable_vonMangoldt_div_rpow (s : ℝ) (hs : 1 < s) :
    Summable (fun n : ℕ => (Λ n : ℝ) / (n:ℝ) ^ s) := by
  refine Summable.of_nonneg_of_le (fun n => div_nonneg vonMangoldt_nonneg (by positivity)) ?_
    (summable_log_rpow_div_rpow 1 hs)
  intro n
  rw [Real.rpow_one]
  gcongr
  exact vonMangoldt_le_log

/-- Real summability of `Λ n / (n^s * log n)` for `s > 1` (compare with the previous lemma). -/
private lemma summable_c_term (s : ℝ) (hs : 1 < s) :
    Summable (fun d : ℕ => c d * ((d:ℝ) ^ (1 - s) / (s - 1))) := by
  have hs1 : (0:ℝ) < s - 1 := by linarith
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  -- Majorise by `(1/(log 2·(s-1)))·(Λ d/d^s)`, summable by `summable_vonMangoldt_div_rpow`.
  refine Summable.of_nonneg_of_le (fun d => ?_) (fun d => ?_)
    ((summable_vonMangoldt_div_rpow s hs).mul_left (1 / (Real.log 2 * (s - 1))))
  · -- `0 ≤ c d * (d^(1-s)/(s-1))`
    refine mul_nonneg (c_nonneg d) (div_nonneg ?_ hs1.le)
    rcases eq_or_ne (d:ℝ) 0 with hd | hd
    · rw [hd, Real.zero_rpow (by linarith : (1 - s) ≠ 0)]
    · positivity
  · -- `c d * (d^(1-s)/(s-1)) ≤ (1/(log 2·(s-1)))·(Λ d/d^s)`
    rcases lt_or_ge d 2 with hd | hd
    · have hc : c d = 0 := by interval_cases d <;> simp
      rw [hc, zero_mul]
      exact mul_nonneg (by positivity) (div_nonneg vonMangoldt_nonneg (by positivity))
    · have hd2 : (2:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
      have hd0 : (0:ℝ) < (d:ℝ) := by linarith
      have hlogge : Real.log 2 ≤ Real.log d := Real.log_le_log (by norm_num) hd2
      have hds : (0:ℝ) < (d:ℝ) ^ s := Real.rpow_pos_of_pos hd0 s
      have hkey : c d * ((d:ℝ) ^ (1 - s) / (s - 1)) = Λ d / ((d:ℝ) ^ s * Real.log d * (s - 1)) := by
        unfold c
        rw [show (1 - s : ℝ) = -s + 1 by ring, Real.rpow_add hd0, Real.rpow_one, Real.rpow_neg hd0.le]
        field_simp
      -- `Λ d / (d^s·log d·(s-1)) ≤ Λ d / (d^s·log 2·(s-1))` since `log 2 ≤ log d`.
      have hcb : (d:ℝ) ^ s * Real.log 2 * (s - 1) ≤ (d:ℝ) ^ s * Real.log d * (s - 1) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlogge hds.le) hs1.le
      rw [hkey, show (1 / (Real.log 2 * (s - 1))) * ((Λ d : ℝ) / (d:ℝ) ^ s)
          = Λ d / ((d:ℝ) ^ s * Real.log 2 * (s - 1)) from by field_simp]
      exact div_le_div_of_nonneg_left vonMangoldt_nonneg (by positivity) hcb

/-- The integration-by-parts identity (#1583), with explicit qualifiers. -/
theorem log_zeta_eq_integ_aux (s : ℝ) (hs : 1 < s) :
    Real.log (riemannZeta (s:ℂ)).re =
      (s - 1) * ∫ x in Set.Ioi 1, (Real.log (Real.log x) + γ + E₂Λ x) * x ^ (-s) := by
  rw [Mertens.log_zeta_eq_sum s hs]
  symm
  have hstep1 : ∀ x ∈ Set.Ioi (1:ℝ),
      (Real.log (Real.log x) + γ + E₂Λ x) * x ^ (-s)
        = (∑ d ∈ Finset.Ioc 0 ⌊x⌋₊, c d) * x ^ (-s) := by
    intro x hx
    simp only [Mertens.E₂Λ, c]
    ring
  have hstep2 : ∀ x ∈ Set.Ioi (1:ℝ),
      (Real.log (Real.log x) + γ + E₂Λ x) * x ^ (-s) = ∑' d : ℕ, f s d x := by
    intro x hx
    rw [hstep1 x hx]
    simp only [f]
    rw [Finset.sum_mul]
    have hx0 : (0:ℝ) ≤ x := by have := hx; simp only [Set.mem_Ioi] at this; linarith
    rw [tsum_eq_sum (s := Finset.Ioc 0 ⌊x⌋₊) ?_]
    · apply Finset.sum_congr rfl
      intro d hd
      simp only [Finset.mem_Ioc] at hd
      have hdx : (d:ℝ) ≤ x := by
        rw [← Nat.le_floor_iff hx0]; exact hd.2
      rw [Set.indicator_of_mem (by simpa using hdx)]
    · intro d hd
      simp only [Finset.mem_Ioc, not_and, not_le] at hd
      rcases Nat.eq_zero_or_pos d with hd0 | hd0
      · subst hd0; simp
      · have hfloor : ⌊x⌋₊ < d := hd hd0
        have hdx : x < (d:ℝ) := by
          rw [← Nat.floor_lt hx0]; exact hfloor
        rw [Set.indicator_of_notMem (by simpa using not_le.mpr hdx)]
        ring
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hstep2]
  have hperterm : ∀ d : ℕ, ∫ x in Set.Ioi (1:ℝ), f s d x = c d * ((d:ℝ) ^ (1 - s) / (s - 1)) := by
    intro d
    rcases Nat.eq_zero_or_pos d with hd0 | hd0
    · subst hd0; simp [f]
    simp only [f]
    rw [MeasureTheory.integral_const_mul, MeasureTheory.setIntegral_indicator measurableSet_Ici]
    congr 1
    have hdR : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd0
    have hdR0 : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd0
    set A : Set ℝ := Set.Ioi (1:ℝ) ∩ Set.Ici (d:ℝ) with hA
    have hae : A =ᵐ[volume] Set.Ioi (d:ℝ) := by
      have h1 : A =ᵐ[volume] (Set.Ici (1:ℝ) ∩ Set.Ici (d:ℝ) : Set ℝ) :=
        MeasureTheory.ae_eq_set_inter MeasureTheory.Ioi_ae_eq_Ici (by rfl)
      rw [Set.Ici_inter_Ici, max_eq_right hdR] at h1
      exact h1.trans MeasureTheory.Ioi_ae_eq_Ici.symm
    rw [MeasureTheory.setIntegral_congr_set hae]
    rw [integral_Ioi_rpow_of_lt (by linarith : (-s:ℝ) < -1) hdR0,
      show (-s + 1 : ℝ) = 1 - s by ring]
    have hs1 : (1 - s) ≠ 0 := by linarith
    have hs2 : (s - 1) ≠ 0 := by linarith
    field_simp
    ring
  have hint : ∀ d : ℕ, MeasureTheory.IntegrableOn (f s d) (Set.Ioi (1:ℝ)) := by
    intro d
    unfold f
    apply MeasureTheory.Integrable.const_mul
    rw [show MeasureTheory.Integrable ((Set.Ici (d:ℝ)).indicator fun x => x ^ (-s))
        (volume.restrict (Set.Ioi (1:ℝ)))
      ↔ MeasureTheory.IntegrableOn ((Set.Ici (d:ℝ)).indicator fun x => x ^ (-s))
          (Set.Ioi (1:ℝ)) volume from Iff.rfl,
      MeasureTheory.integrableOn_indicator_iff measurableSet_Ici.nullMeasurableSet]
    apply MeasureTheory.IntegrableOn.mono_set
      (integrableOn_Ioi_rpow_of_lt (by linarith : (-s:ℝ) < -1) (by norm_num : (0:ℝ) < 1/2))
    intro x hx
    simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Ioi] at hx ⊢
    linarith [hx.2]
  have hnorm_int : ∀ d : ℕ,
      ∫ x in Set.Ioi (1:ℝ), ‖f s d x‖ = c d * ((d:ℝ) ^ (1 - s) / (s - 1)) := by
    intro d
    rw [← hperterm d]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    simp only [Set.mem_Ioi] at hx
    have hfnn : 0 ≤ f s d x := by
      simp only [f]
      apply mul_nonneg (c_nonneg d)
      by_cases hxd : (d:ℝ) ≤ x
      · rw [Set.indicator_of_mem (by simpa using hxd)]
        exact le_of_lt (Real.rpow_pos_of_pos (by linarith) _)
      · rw [Set.indicator_of_notMem (by simpa using hxd)]
    change ‖f s d x‖ = f s d x
    rw [Real.norm_eq_abs, abs_of_nonneg hfnn]
  have hinterchange : ∫ x in Set.Ioi (1:ℝ), ∑' d : ℕ, f s d x
      = ∑' d : ℕ, ∫ x in Set.Ioi (1:ℝ), f s d x := by
    refine (MeasureTheory.integral_tsum_of_summable_integral_norm hint ?_).symm
    apply (summable_c_term s hs).congr
    intro d
    exact (hnorm_int d).symm
  rw [hinterchange]
  simp_rw [hperterm]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro d
  rcases Nat.eq_zero_or_pos d with hd0 | hd0
  · subst hd0; simp
  · have hdR : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd0
    have hsub : (d:ℝ) ^ (1 - s) = (d:ℝ) ^ (-s) * (d:ℝ) := by
      rw [show (1 - s : ℝ) = -s + 1 by ring, Real.rpow_add hdR, Real.rpow_one]
    have hs1 : s - 1 ≠ 0 := by linarith
    have hneg : (d:ℝ) ^ (-s) = ((d:ℝ) ^ s)⁻¹ := by
      rw [Real.rpow_neg (le_of_lt hdR)]
    unfold c
    rw [hsub, hneg]
    field_simp

end LogZetaInteg
end

private theorem log_zeta_eq_integ (s : ℝ) (hs : 1 < s) :
    log (riemannZeta (s:ℂ)).re = (s - 1) * ∫ x in .Ioi 1, (log (log x) + γ + E₂Λ x) * x^(-s) :=
  LogZetaInteg.log_zeta_eq_integ_aux s hs

private theorem mul_integ_log_log_eq (s : ℝ) (hs : 1 < s) :
    (s - 1) * ∫ x in .Ioi 1, log (log x) * x^(-s) = - log (s - 1) + deriv Gamma 1 :=
  mul_integ_log_log_eq_aux s hs

private theorem mul_integ_gamma_eq (s) (hs : 1 < s) : (s - 1) * ∫ x in .Ioi 1, γ * x^(-s) = γ := by
  rw [MeasureTheory.integral_const_mul γ (· ^ (-s)), @integral_Ioi_rpow_of_lt (-s), one_rpow] <;>
    grind

-- Integrability helpers for the integral splitting in `log_zeta_eq` (#1319).
-- Each summand of `(log (log x) + γ + E₂Λ x) * x^(-s)` is separately integrable on `Ioi 1`.

/-- Comparison test for `x ^ (-s)` decay: if `f` is measurable and dominated by `B * x ^ a` on
`Set.Ioi c` (with `0 < c` and `a + 1 < s`), then `fun x ↦ f x * x ^ (-s)` is integrable there.
This is the integral analogue of the summability of `O(x ^ a / x ^ s)` series and packages the
decay estimate reused for each tail in `log_zeta_eq`. -/
private theorem integrableOn_Ioi_mul_rpow_neg_of_abs_le
    {c B a s : ℝ} (hc : 0 < c) (has : a + 1 < s) {f : ℝ → ℝ} (hf : Measurable f)
    (hbound : ∀ x ∈ Set.Ioi c, |f x| ≤ B * x ^ a) :
    MeasureTheory.IntegrableOn (fun x => f x * x ^ (-s)) (Set.Ioi c) := by
  have hg : MeasureTheory.IntegrableOn (fun x => B * x ^ (a - s)) (Set.Ioi c) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith : a - s < -1) hc).const_mul B
  refine MeasureTheory.Integrable.mono' hg
    (hf.mul (measurable_id.pow_const (-s))).aestronglyMeasurable ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
  have hxpos : (0:ℝ) < x := hc.trans hx
  have hxs : (0:ℝ) < x ^ (-s) := Real.rpow_pos_of_pos hxpos _
  rw [norm_mul, norm_eq_abs, norm_eq_abs, abs_of_pos hxs]
  calc |f x| * x ^ (-s) ≤ B * x ^ a * x ^ (-s) :=
        mul_le_mul_of_nonneg_right (hbound x hx) hxs.le
    _ = B * x ^ (a - s) := by rw [mul_assoc, ← Real.rpow_add hxpos, sub_eq_add_neg]

/-- `log (log x) * x ^ (-s)` is integrable on `Ioi 1` for `s > 1`
(log-log singularity at `1` is integrable; `x^(-s)` gives decay). -/
private theorem integrableOn_log_log_mul_rpow (s : ℝ) (hs : 1 < s) :
    MeasureTheory.IntegrableOn (fun x => log (log x) * x ^ (-s)) (Set.Ioi 1) := by
  rw [← Set.Ioc_union_Ioi_eq_Ioi (by norm_num : (1:ℝ) ≤ 2)]
  apply MeasureTheory.IntegrableOn.union
  · -- Near `1`: `log (log x)` is integrable (log-log singularity) and `x^(-s) ≤ 1`.
    have hll : MeasureTheory.IntegrableOn (fun x => log (log x)) (Set.Ioc 1 2) := by
      have h : IntervalIntegrable (log ∘ log) MeasureTheory.volume 1 2 := by
        apply MeromorphicOn.intervalIntegrable_log
        intro x hx
        rw [Set.uIcc_of_le (by norm_num : (1:ℝ) ≤ 2)] at hx
        exact (analyticAt_log (by linarith [hx.1] : 0 < x)).meromorphicAt
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp h
    have hmul : MeasureTheory.IntegrableOn (fun x => x ^ (-s) * log (log x)) (Set.Ioc 1 2) := by
      apply hll.bdd_mul (c := 1)
      · fun_prop
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with x hx
        rw [norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by linarith [hx.1] : (0:ℝ) ≤ x) _)]
        calc x ^ (-s) ≤ (1:ℝ) ^ (-s) :=
              Real.rpow_le_rpow_of_nonpos (by norm_num) hx.1.le (by linarith)
          _ = 1 := Real.one_rpow _
    simpa [mul_comm] using hmul
  · -- Tail (`Ioi 2`): `|log (log x)| ≤ (1/ε + |log (log 2)|)·x^ε` with `ε = (s-1)/2`, `ε + 1 < s`.
    set ε := (s - 1) / 2 with hε
    have hεpos : 0 < ε := by rw [hε]; linarith
    refine integrableOn_Ioi_mul_rpow_neg_of_abs_le (a := ε) (B := 1 / ε + |log (log 2)|)
      (by norm_num) (by rw [hε]; linarith) (Real.measurable_log.comp Real.measurable_log) ?_
    intro x hx
    simp only [Set.mem_Ioi] at hx
    have hx1 : (1:ℝ) ≤ x ^ ε := Real.one_le_rpow (by linarith) hεpos.le
    have hlogx : 0 < log x := Real.log_pos (by linarith)
    have hlog2 : 0 < log 2 := Real.log_pos (by norm_num)
    have hmono : log 2 ≤ log x := Real.log_le_log (by norm_num) (by linarith)
    have hub : log (log x) ≤ x ^ ε / ε :=
      calc log (log x) ≤ log x := (Real.log_le_sub_one_of_pos hlogx).trans (by linarith)
        _ ≤ x ^ ε / ε := Real.log_le_rpow_div (by linarith) hεpos
    have hlb : log (log 2) ≤ log (log x) := Real.log_le_log hlog2 hmono
    have hxε : 0 ≤ x ^ ε / ε := by positivity
    calc |log (log x)| ≤ x ^ ε / ε + |log (log 2)| := by
          rw [abs_le]
          exact ⟨by linarith [neg_abs_le (log (log 2))],
            by linarith [abs_nonneg (log (log 2))]⟩
      _ ≤ (1 / ε + |log (log 2)|) * x ^ ε := by
          have h2 : |log (log 2)| ≤ |log (log 2)| * x ^ ε := le_mul_of_one_le_right (abs_nonneg _) hx1
          have h1 : x ^ ε / ε = 1 / ε * x ^ ε := by ring
          rw [add_mul]; linarith

/-- `γ * x ^ (-s)` is integrable on `Ioi 1` for `s > 1`. -/
private theorem integrableOn_γ_mul_rpow (s : ℝ) (hs : 1 < s) :
    MeasureTheory.IntegrableOn (fun x => γ * x ^ (-s)) (Set.Ioi 1) := by
  exact (integrableOn_Ioi_rpow_of_lt (by linarith : -s < -1) one_pos).const_mul γ

/-- `E₂Λ x * x ^ (-s)` is integrable on `Ioi 1` for `s > 1`
(`E₂Λ ~ -log(log x)` near `1`, and `E₂Λ = O(1/log x)` at `∞`). -/
private theorem integrableOn_E₂Λ_mul_rpow (s : ℝ) (hs : 1 < s) :
    MeasureTheory.IntegrableOn (fun x => E₂Λ x * x ^ (-s)) (Set.Ioi 1) := by
  rw [← Set.Ioo_union_Ici_eq_Ioi (by norm_num : (1:ℝ) < 2)]
  apply MeasureTheory.IntegrableOn.union
  · -- Near `1`: `⌊x⌋₊ = 1`, the sum is `0`, so `E₂Λ x = -log (log x) - γ`.
    have hsub : Set.Ioo (1:ℝ) 2 ⊆ Set.Ioi 1 := fun x hx => hx.1
    have h1 := (integrableOn_γ_mul_rpow s hs).mono_set hsub
    have h2 := (integrableOn_log_log_mul_rpow s hs).mono_set hsub
    have hb : MeasureTheory.IntegrableOn
        (fun x => -(log (log x) * x ^ (-s)) - γ * x ^ (-s)) (Set.Ioo 1 2) :=
      h2.neg.sub h1
    apply hb.congr_fun _ measurableSet_Ioo
    intro x hx
    simp only [Set.mem_Ioo] at hx
    have hfloor : ⌊ x ⌋₊ = 1 := by
      rw [Nat.floor_eq_iff (by linarith)]
      exact ⟨by push_cast; linarith [hx.1], by push_cast; linarith [hx.2]⟩
    have hsum : (∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / ((d:ℝ) * log d)) = 0 := by rw [hfloor]; norm_num
    change -(log (log x) * x ^ (-s)) - γ * x ^ (-s)
        = (∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / (d * log d) - log (log x) - γ) * x ^ (-s)
    rw [hsum]; ring
  · -- Tail: `|E₂Λ x| ≤ (log 4 + 6)/log x ≤ (log 4 + 6)/log 2` is bounded (`a = 0`), times decay.
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    refine integrableOn_Ioi_mul_rpow_neg_of_abs_le (a := 0) (B := (log 4 + 6) / log 2)
      (by norm_num) (by linarith) m2_measurable ?_
    intro x hx
    simp only [Set.mem_Ioi] at hx
    have hlog2 : 0 < log 2 := Real.log_pos (by norm_num)
    have hc : 0 ≤ log 4 + 6 := by positivity
    rw [Real.rpow_zero, mul_one]
    have hb2 : (log 4 + 6) / log x ≤ (log 4 + 6) / log 2 :=
      div_le_div_of_nonneg_left hc hlog2 (Real.log_le_log (by norm_num) (le_of_lt hx))
    exact (E₂Λ.abs_le (le_of_lt hx)).trans hb2

private theorem log_zeta_eq (s : ℝ) (hs : 1 < s) :
    log (riemannZeta (s:ℂ)).re = - log (s - 1) + deriv Gamma 1 + γ + (s - 1) * ∫ x in Set.Ioi 1, E₂Λ x * x^(-s) := by
  -- Start from the integration-by-parts identity (#1583).
  rw [log_zeta_eq_integ s hs]
  -- Linearity of the integral: split into the three summands (uses the integrability helpers).
  have key : (∫ x in Set.Ioi 1, (log (log x) + γ + E₂Λ x) * x ^ (-s))
      = (∫ x in Set.Ioi 1, log (log x) * x ^ (-s))
        + (∫ x in Set.Ioi 1, γ * x ^ (-s))
        + (∫ x in Set.Ioi 1, E₂Λ x * x ^ (-s)) := by
    rw [← MeasureTheory.integral_add (integrableOn_log_log_mul_rpow s hs)
      (integrableOn_γ_mul_rpow s hs)]
    rw [← MeasureTheory.integral_add (f := fun x => log (log x) * x ^ (-s) + γ * x ^ (-s))
      (g := fun x => E₂Λ x * x ^ (-s))
      ((integrableOn_log_log_mul_rpow s hs).add (integrableOn_γ_mul_rpow s hs))
      (integrableOn_E₂Λ_mul_rpow s hs)]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro x _
    ring
  -- Apply sublemmas #1584 and #1585, then finish algebraically.
  rw [key, mul_add, mul_add, mul_integ_log_log_eq s hs, mul_integ_gamma_eq s hs]

private lemma zeta_pole_mul_re_tendsto_one :
    Filter.Tendsto (fun s : ℝ => (s - 1) * (riemannZeta (s : ℂ)).re)
      (nhdsWithin 1 (Set.Ioi 1)) (nhds 1) := by
  have hofReal :
      Filter.Tendsto (fun s : ℝ => (s : ℂ)) (nhdsWithin 1 (Set.Ioi 1))
        (nhdsWithin (1 : ℂ) ({1} : Set ℂ)ᶜ) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · exact (Complex.continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact Set.mem_compl_singleton_iff.mpr (by
        norm_num
        exact ne_of_gt (Set.mem_Ioi.mp hs))
  have hcomplex :
      Filter.Tendsto (fun s : ℝ => ((s : ℂ) - 1) * riemannZeta (s : ℂ))
        (nhdsWithin 1 (Set.Ioi 1)) (nhds 1) :=
    riemannZeta_residue_one.comp hofReal
  have hreal :
      Filter.Tendsto
        (fun s : ℝ => (((s : ℂ) - 1) * riemannZeta (s : ℂ)).re)
        (nhdsWithin 1 (Set.Ioi 1)) (nhds (1 : ℝ)) :=
    (Complex.continuous_re.tendsto (1 : ℂ)).comp hcomplex
  simpa [Complex.ofReal_sub, Complex.ofReal_mul] using hreal

private theorem log_zeta_limit :
    Filter.Tendsto
      (fun s : ℝ => Real.log (riemannZeta (s : ℂ)).re + Real.log (s - 1))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds 0) := by
  have hlog :
      Filter.Tendsto
        (fun s : ℝ => Real.log ((s - 1) * (riemannZeta (s : ℂ)).re))
        (nhdsWithin 1 (Set.Ioi 1)) (nhds (Real.log 1)) :=
    (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp
      zeta_pole_mul_re_tendsto_one
  have hEq :
      (fun s : ℝ => Real.log (riemannZeta (s : ℂ)).re + Real.log (s - 1))
        =ᶠ[nhdsWithin 1 (Set.Ioi 1)]
      fun s : ℝ => Real.log ((s - 1) * (riemannZeta (s : ℂ)).re) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hspos : 0 < s - 1 := sub_pos.mpr (Set.mem_Ioi.mp hs)
    have hzpos : 0 < (riemannZeta (s : ℂ)).re :=
      riemannZeta_re_pos_of_one_lt (Set.mem_Ioi.mp hs)
    rw [Real.log_mul hspos.ne' hzpos.ne']
    ring
  simpa using hlog.congr' (hEq.mono fun s hs => hs.symm)

-- Helpers for `deriv_gamma_add_γ_eq_zero` (#1320): take `s → 1⁺` in `log_zeta_eq`.
section
open MeasureTheory Set

/-- `E₂Λ` is measurable: its Mangoldt-sum part factors through `⌊·⌋₊` and the rest is
continuous/measurable. -/
private lemma measurable_E₂Λ : Measurable E₂Λ := m2_measurable

/-- On `(1,2)` the Mangoldt sum is empty (`⌊x⌋₊ = 1`), so `E₂Λ x = - log (log x) - γ`. -/
private lemma E₂Λ_eq_on_Ioo {x : ℝ} (hx : x ∈ Set.Ioo (1 : ℝ) 2) :
    E₂Λ x = - log (log x) - γ := by
  obtain ⟨h1, h2⟩ := hx
  have hf : ⌊x⌋₊ = 1 := by
    rw [Nat.floor_eq_iff (by linarith)]
    exact ⟨by exact_mod_cast h1.le, by exact_mod_cast h2⟩
  unfold E₂Λ
  rw [hf]
  simp

/-- Domination of `|E₂Λ|` near `1`: for `x ∈ (1,2)`, `|E₂Λ x| ≤ |log (x-1)| + log 2 + |γ|`,
the RHS being integrable on `(1,2)` (the `log (x-1)` is integrable across the singularity at `1`). -/
private lemma abs_E₂Λ_le_on_Ioo {x : ℝ} (hx : x ∈ Set.Ioo (1 : ℝ) 2) :
    |E₂Λ x| ≤ |log (x - 1)| + log 2 + |γ| := by
  obtain ⟨hx1, hx2⟩ := hx
  have hloglog : |log (log x)| ≤ |log (x - 1)| + log 2 := by
    have hxpos : (0:ℝ) < x := by linarith
    have hlogx_pos : 0 < log x := Real.log_pos hx1
    have hxm1 : 0 < x - 1 := by linarith
    have hub : log x ≤ x - 1 := by have := Real.log_le_sub_one_of_pos hxpos; linarith
    have hlb2 : (x - 1) / 2 ≤ log x := by
      have h := Real.log_le_sub_one_of_pos (x := 1 / x) (by positivity)
      rw [Real.log_div one_ne_zero (by positivity), Real.log_one] at h
      simp only [zero_sub] at h
      have h12 : (x - 1) / 2 ≤ 1 - 1 / x := by
        rw [← sub_nonneg]
        have e : (1 - 1 / x) - (x - 1) / 2 = (3 * x - 2 - x ^ 2) / (2 * x) := by field_simp; ring
        rw [e]; exact div_nonneg (by nlinarith [hx1, hx2]) (by positivity)
      linarith
    have hupper : log (log x) ≤ log (x - 1) := Real.log_le_log hlogx_pos hub
    have hlower : log (x - 1) - log 2 ≤ log (log x) := by
      have := Real.log_le_log (show (0:ℝ) < (x - 1) / 2 by positivity) hlb2
      rwa [Real.log_div (by linarith) (by norm_num)] at this
    have h2 : (0:ℝ) ≤ log 2 := Real.log_nonneg (by norm_num)
    rw [abs_le]
    exact ⟨by have := neg_abs_le (log (x - 1)); linarith,
          by have := le_abs_self (log (x - 1)); linarith⟩
  rw [E₂Λ_eq_on_Ioo ⟨hx1, hx2⟩]
  have htri : |(- log (log x) - γ)| ≤ |log (log x)| + |γ| := by
    have h := abs_sub (-log (log x)) γ
    rwa [abs_neg] at h
  linarith

/-- Constant bound on `|E₂Λ|` for `2 ≤ x`, sharpening `E₂Λ.abs_le` via `log 2 ≤ log x`. -/
private lemma abs_E₂Λ_le_const {x : ℝ} (hx : 2 ≤ x) :
    |E₂Λ x| ≤ (log 4 + 6) / log 2 :=
  (E₂Λ.abs_le hx).trans <| div_le_div_of_nonneg_left (by positivity)
    (Real.log_pos (by norm_num)) (Real.log_le_log (by norm_num) hx)

/-- The near-1 dominating function `|log (x-1)| + log 2 + |γ|` is integrable on `(1,2)`
(it dominates `|E₂Λ|` there, handling the log-log singularity at `1`). -/
private lemma integrableOn_log_sub_one_bound :
    IntegrableOn (fun x => |log (x - 1)| + log 2 + |γ|) (Set.Ioo 1 2) volume := by
  have hlog : IntegrableOn (fun x => |log (x - 1)|) (Set.Ioo 1 2) volume := by
    have h0 : IntervalIntegrable (fun x => log x) volume 0 1 :=
      intervalIntegral.intervalIntegrable_log'
    have h1 : IntervalIntegrable (fun x => log (x - 1)) volume (0 + 1) (1 + 1) :=
      h0.comp_sub_right 1
    norm_num at h1
    exact (h1.1.mono_set Set.Ioo_subset_Ioc_self).abs
  have hc : IntegrableOn (fun _ : ℝ => log 2 + |γ|) (Set.Ioo (1 : ℝ) 2) volume :=
    integrableOn_const (measure_Ioo_lt_top).ne (by finiteness)
  have hsum : IntegrableOn (fun x => |log (x - 1)| + (log 2 + |γ|)) (Set.Ioo 1 2) volume :=
    hlog.add hc
  exact hsum.congr_fun (fun x _ => by ring) measurableSet_Ioo

/-- `E₂Λ` is integrable on every bounded interval `(1, X)` (`X ≥ 2`): log-log singularity near
`1` plus boundedness on `[2, X]`. -/
private lemma integrableOn_E₂Λ_Ioo {X : ℝ} (_hX : 2 ≤ X) :
    IntegrableOn E₂Λ (Set.Ioo 1 X) volume := by
  have hsub : Set.Ioo (1 : ℝ) X ⊆ Set.Ioo 1 2 ∪ Set.Icc 2 X := by
    intro x hx; simp only [Set.mem_Ioo, Set.mem_union, Set.mem_Icc] at *
    rcases lt_or_ge x 2 with h | h
    · exact Or.inl ⟨hx.1, h⟩
    · exact Or.inr ⟨h, hx.2.le⟩
  apply IntegrableOn.mono_set _ hsub
  apply IntegrableOn.union
  · have hg := integrableOn_log_sub_one_bound
    refine Integrable.mono' hg measurable_E₂Λ.aestronglyMeasurable ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with x hx
    rw [Real.norm_eq_abs]; exact abs_E₂Λ_le_on_Ioo hx
  · refine Integrable.mono' (g := fun _ => (log 4 + 6) / log 2) ?_
      measurable_E₂Λ.aestronglyMeasurable ?_
    · exact integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top) (by finiteness)
    · filter_upwards [self_mem_ae_restrict measurableSet_Icc] with x hx
      rw [Real.norm_eq_abs]; exact abs_E₂Λ_le_const hx.1

/-- The error integral, scaled by `(s-1)`, vanishes as `s → 1⁺` (uses `E₂Λ =o(1)`). -/
private lemma sub_one_mul_integral_E₂Λ_tendsto :
    Filter.Tendsto (fun s : ℝ => (s - 1) * ∫ x in Set.Ioi 1, E₂Λ x * x ^ (-s))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds 0) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  -- Choose `X ≥ 2` so that `|E₂Λ x| ≤ ε/2` for `x ≥ X` (from `E₂Λ =o(1)`).
  obtain ⟨X₀, hX₀⟩ : ∃ X, ∀ x ≥ X, |E₂Λ x| ≤ ε / 2 := by
    have := E₂Λ.bound'.def (by positivity : (0:ℝ) < ε / 2)
    simp only [Real.norm_eq_abs, abs_one, mul_one] at this
    rw [Filter.eventually_atTop] at this; exact this
  set X := max X₀ 2 with hXdef
  have hX2 : 2 ≤ X := le_max_right _ _
  have hXge : ∀ x ≥ X, |E₂Λ x| ≤ ε / 2 := fun x hx => hX₀ x (le_trans (le_max_left _ _) hx)
  -- `B` is the (finite) mass of `|E₂Λ|` on `(1, X)`.
  set B := ∫ x in Set.Ioo 1 X, |E₂Λ x| with hBdef
  have hB0 : 0 ≤ B := setIntegral_nonneg measurableSet_Ioo (fun x _ => abs_nonneg _)
  refine ⟨min 1 (ε / 2 / (B + 1)), by positivity, ?_⟩
  intro s hs hdist
  simp only [Set.mem_Ioi] at hs
  rw [Real.dist_eq] at hdist
  have hs1 : s - 1 < min 1 (ε / 2 / (B + 1)) := by
    rw [abs_of_pos (by linarith)] at hdist; exact hdist
  have hsm1 : 0 < s - 1 := by linarith
  -- `|E₂Λ|·x^(-s)` is integrable on `(1,∞)` and its subintervals.
  have hintAbs : IntegrableOn (fun x => |E₂Λ x| * x ^ (-s)) (Set.Ioi 1) volume := by
    have h2 : IntegrableOn (fun x => |E₂Λ x * x ^ (-s)|) (Set.Ioi 1) volume :=
      (integrableOn_E₂Λ_mul_rpow s hs).abs
    refine h2.congr_fun ?_ measurableSet_Ioi
    intro x hx; simp only [Set.mem_Ioi] at hx
    change |E₂Λ x * x ^ (-s)| = |E₂Λ x| * x ^ (-s)
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (by linarith) _)]
  have hintAbsIoc : IntegrableOn (fun x => |E₂Λ x| * x ^ (-s)) (Set.Ioc 1 X) volume :=
    hintAbs.mono_set Set.Ioc_subset_Ioi_self
  have hintAbsIoiX : IntegrableOn (fun x => |E₂Λ x| * x ^ (-s)) (Set.Ioi X) volume :=
    hintAbs.mono_set (Set.Ioi_subset_Ioi (by linarith))
  -- Split `∫_{(1,∞)} = ∫_{(1,X]} + ∫_{(X,∞)}`.
  have hsplit : ∫ x in Set.Ioi 1, |E₂Λ x| * x ^ (-s) =
      (∫ x in Set.Ioc 1 X, |E₂Λ x| * x ^ (-s)) + ∫ x in Set.Ioi X, |E₂Λ x| * x ^ (-s) := by
    have hu : Set.Ioi (1:ℝ) = Set.Ioc 1 X ∪ Set.Ioi X :=
      (Set.Ioc_union_Ioi_eq_Ioi (by linarith)).symm
    rw [hu, setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hintAbs.mono_set (by rw [hu]; exact Set.subset_union_left))
      (hintAbs.mono_set (by rw [hu]; exact Set.subset_union_right))]
  -- Piece 1: on `(1,X]`, `x^(-s) ≤ 1`, so the integral is `≤ B`.
  have hp1 : ∫ x in Set.Ioc 1 X, |E₂Λ x| * x ^ (-s) ≤ B := by
    rw [hBdef]
    have ha : IntegrableOn (fun x => |E₂Λ x|) (Set.Ioo 1 X) volume := (integrableOn_E₂Λ_Ioo hX2).abs
    have habsIoc : IntegrableOn (fun x => |E₂Λ x|) (Set.Ioc 1 X) volume :=
      ha.congr_set_ae (Ioo_ae_eq_Ioc).symm
    rw [← integral_Ioc_eq_integral_Ioo]
    apply setIntegral_mono_on hintAbsIoc habsIoc measurableSet_Ioc
    intro x hx
    have hx1 : (1:ℝ) ≤ x := by have := hx.1; linarith
    have hle1 : x ^ (-s) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1 (by linarith)
    calc |E₂Λ x| * x ^ (-s) ≤ |E₂Λ x| * 1 := by gcongr
      _ = |E₂Λ x| := mul_one _
  -- Piece 2: on `(X,∞)`, `|E₂Λ| ≤ ε/2`, and `∫_{(X,∞)} x^(-s) = X^(1-s)/(s-1)`.
  have hp2 : ∫ x in Set.Ioi X, |E₂Λ x| * x ^ (-s) ≤ (ε / 2) * (X ^ (1 - s) / (s - 1)) := by
    have hrpow_int : IntegrableOn (fun x : ℝ => x ^ (-s)) (Set.Ioi X) volume :=
      integrableOn_Ioi_rpow_of_lt (by linarith) (by linarith : (0:ℝ) < X)
    have hval : ∫ x in Set.Ioi X, x ^ (-s) = X ^ (1 - s) / (s - 1) := by
      rw [integral_Ioi_rpow_of_lt (by linarith) (by linarith : (0:ℝ) < X),
        show -s + 1 = 1 - s by ring, show (1:ℝ) - s = -(s - 1) by ring]
      rw [div_neg, neg_div, neg_neg]
    rw [← hval, ← integral_const_mul]
    apply setIntegral_mono_on hintAbsIoiX (hrpow_int.const_mul (ε / 2)) measurableSet_Ioi
    intro x hx
    have hxpos : (0:ℝ) < x := by simp only [Set.mem_Ioi] at hx; linarith
    have hnn : 0 ≤ x ^ (-s) := Real.rpow_nonneg hxpos.le _
    have hb : |E₂Λ x| ≤ ε / 2 := hXge x (by simp only [Set.mem_Ioi] at hx; linarith)
    gcongr
  have hXpow : X ^ (1 - s) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
  -- Assemble: `(s-1)·∫|E₂Λ|·x^(-s) ≤ (s-1)·B + ε/2`.
  have hbound : (s - 1) * ∫ x in Set.Ioi 1, |E₂Λ x| * x ^ (-s) ≤ (s - 1) * B + ε / 2 := by
    rw [hsplit, mul_add]
    have ht2 : (s - 1) * ∫ x in Set.Ioi X, |E₂Λ x| * x ^ (-s) ≤ ε / 2 := by
      calc (s - 1) * ∫ x in Set.Ioi X, |E₂Λ x| * x ^ (-s)
          ≤ (s - 1) * ((ε / 2) * (X ^ (1 - s) / (s - 1))) :=
            mul_le_mul_of_nonneg_left hp2 hsm1.le
        _ = (ε / 2) * X ^ (1 - s) := by
              have hne : s - 1 ≠ 0 := by linarith
              field_simp
        _ ≤ (ε / 2) * 1 := by gcongr
        _ = ε / 2 := mul_one _
    have ht1 : (s - 1) * ∫ x in Set.Ioc 1 X, |E₂Λ x| * x ^ (-s) ≤ (s - 1) * B :=
      mul_le_mul_of_nonneg_left hp1 hsm1.le
    linarith
  -- `|(s-1)·∫ E₂Λ·x^(-s)| ≤ (s-1)·∫|E₂Λ|·x^(-s)`.
  have habs_le : |(s - 1) * ∫ x in Set.Ioi 1, E₂Λ x * x ^ (-s)|
      ≤ (s - 1) * ∫ x in Set.Ioi 1, |E₂Λ x| * x ^ (-s) := by
    rw [abs_mul, abs_of_pos hsm1]
    gcongr
    rw [← Real.norm_eq_abs]
    refine (norm_integral_le_integral_norm _).trans_eq ?_
    refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    simp only [Set.mem_Ioi] at hx
    change ‖E₂Λ x * x ^ (-s)‖ = |E₂Λ x| * x ^ (-s)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (by linarith) _)]
  rw [Real.dist_eq, sub_zero]
  -- `(s-1)·B + ε/2 < ε` since `s - 1 < ε/2/(B+1)`.
  have hfin : (s - 1) * B + ε / 2 < ε := by
    have hlt : s - 1 < ε / 2 / (B + 1) := lt_of_lt_of_le hs1 (min_le_right _ _)
    have hBp : 0 < B + 1 := by linarith
    have h1 : (s - 1) * B ≤ (s - 1) * (B + 1) := by nlinarith
    have h2 : (s - 1) * (B + 1) < (ε / 2 / (B + 1)) * (B + 1) := mul_lt_mul_of_pos_right hlt hBp
    have h3 : (ε / 2 / (B + 1)) * (B + 1) = ε / 2 := by field_simp
    linarith
  calc |(s - 1) * ∫ x in Set.Ioi 1, E₂Λ x * x ^ (-s)|
      ≤ (s - 1) * ∫ x in Set.Ioi 1, |E₂Λ x| * x ^ (-s) := habs_le
    _ ≤ (s - 1) * B + ε / 2 := hbound
    _ < ε := hfin

end

theorem deriv_gamma_add_γ_eq_zero : deriv Gamma 1 + γ = 0 := by
  -- For `s > 1`, `log_zeta_eq` rearranges to a constant identity.
  have key : ∀ s : ℝ, 1 < s →
      (Real.log (riemannZeta (s:ℂ)).re + Real.log (s - 1))
        - (s - 1) * ∫ x in Set.Ioi 1, E₂Λ x * x ^ (-s) = deriv Gamma 1 + γ := by
    intro s hs
    have h := log_zeta_eq s hs
    linarith
  -- The LHS is eventually constant, so its limit is that constant.
  have hconst : Filter.Tendsto
      (fun s : ℝ => (Real.log (riemannZeta (s:ℂ)).re + Real.log (s - 1))
        - (s - 1) * ∫ x in Set.Ioi 1, E₂Λ x * x ^ (-s))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds (deriv Gamma 1 + γ)) := by
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (key s hs).symm
  -- But the same function tends to `0 - 0` by the two limit lemmas.
  have hlim := log_zeta_limit.sub sub_one_mul_integral_E₂Λ_tendsto
  rw [sub_zero] at hlim
  exact tendsto_nhds_unique hconst hlim

theorem γ.eq_eulerMascheroni : γ = eulerMascheroniConstant := by
  linarith [Real.eulerMascheroniConstant_eq_neg_deriv, deriv_gamma_add_γ_eq_zero]

theorem sum_mangoldt_div_log_eq (x : ℝ) : ∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / (d * log d) = log (log x) + eulerMascheroniConstant + E₂Λ x := by
    grind [γ.eq_eulerMascheroni]

theorem sum_mangoldt_div_log_eq_log_log : ∃ C, ∀ x, 2 ≤ x →
    |∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / (d * log d) - log (log x)| ≤ C := by
    use (log 4 + 6)/log 2 + |eulerMascheroniConstant|
    intro x hx
    rw [sum_mangoldt_div_log_eq]
    calc
      _ = |E₂Λ x + eulerMascheroniConstant| := by ring_nf
      _ ≤ (log 4 + 6)/log x + |eulerMascheroniConstant| := by grw [abs_add_le, E₂Λ.abs_le hx]
      _ ≤ _ := by gcongr

theorem sum_mangoldt_div_log_eq_log_log' : (fun x ↦ ∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / (d * log d) - log (log x)) =O[atTop] (fun _ ↦ (1:ℝ)) := by
    simp only [isBigO_iff, norm_eq_abs, one_mem, CStarRing.norm_of_mem_unitary, mul_one,
      eventually_atTop]
    obtain ⟨ C, _ ⟩ := sum_mangoldt_div_log_eq_log_log
    use C, 2


theorem sum_mangoldt_div_log_eq_log_log'' : (fun x ↦ ∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / (d * log d)) ~[atTop] (fun x ↦ log (log x)) := by
    apply IsLittleO.isEquivalent (IsBigO.trans_isLittleO _ one_eq_o_log_log)
    convert! sum_mangoldt_div_log_eq_log_log' using 1

noncomputable def M : ℝ := (∫ t in Set.Ioi 2, E₁p t / (t * log t^2)) + 1 - log (log 2)

theorem M.le : M ≤ (log 4 + 4) / log 2 + 1 - log (log 2) := calc
    _ ≤ (∫ t in Set.Ioi 2, (log 4 + 4) / (t * log t^2)) + 1 - log (log 2) := by
      unfold M; gcongr with x hx
      · exact integrable_E₁p_div_mul_log_sq (by norm_num)
      · exact integrable_const_div_mul_log_sq _ (by norm_num)
      · measurability
      · simp at hx; positivity
      simp at hx; exact E₁p.le (by linarith)
    _ = _ := by rw [integ_div_mul_log_sq _ (by norm_num)]

theorem M.ge : M ≥ (-2 - E₁) / log 2 + 1 - log (log 2) := calc
    _ ≥ (∫ t in Set.Ioi 2, (-2 - E₁) / (t * log t^2)) + 1 - log (log 2) := by
      unfold M; gcongr with x hx
      · exact integrable_const_div_mul_log_sq _ (by norm_num)
      · exact integrable_E₁p_div_mul_log_sq (by norm_num)
      · measurability
      · simp at hx; positivity
      simp at hx; exact E₁p.ge (by linarith)
    _ = _ := by rw [integ_div_mul_log_sq _ (by norm_num)]

noncomputable abbrev E₂p (x : ℝ) : ℝ := ∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (1:ℝ) / p - log (log x) - M

theorem sum_prime_div_eq (x : ℝ) : ∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (1:ℝ) / p = log (log x) + M + E₂p x := by
    ring

theorem E₂p.eq {x : ℝ} (hx : 2 ≤ x) :
    E₂p x = E₁p x / log x - ∫ t in Set.Ioi x, E₁p t / (t * log t^2) := by
  unfold E₂p
  rw [sum_filter, ← sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp [Nat.not_prime_one])]
  have (n : ℕ) : (if Nat.Prime n then (1 : ℝ) / n else 0) = (if Nat.Prime n then log n / n else 0) / log n := by
    split_ifs with h
    · have : log n ≠ 0 := by simp; grind [h.two_le]
      field
    · simp
  simp_rw [this]
  rw [sum_div_log_eq hx, sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp), ← sum_filter]
  rw [sum_log_prime_div_eq]
  have : ∫ t in 2..x, (∑ n ∈ Ioc 1 ⌊t⌋₊, if Nat.Prime n then log ↑n / ↑n else 0) / (t * log t ^ 2) = ∫ t in 2..x, (1 / (t * log t) + E₁p t / (t * log t ^2)) := by
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
    rw [sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp), ← sum_filter, sum_log_prime_div_eq]
    field
  rw [this, intervalIntegral.integral_add]
  · rw [integral_one_div_mul_log hx, add_div, div_self (by simp; grind)]
    unfold M
    calc
    _ = E₁p x / log x + (∫ (x : ℝ) in 2..x, E₁p x / (x * log x ^ 2)) -
      ((∫ (t : ℝ) in Set.Ioi 2, E₁p t / (t * log t ^ 2))) := by ring
    _ = _ := by
      rw [← intervalIntegral.integral_interval_add_Ioi (integrable_E₁p_div_mul_log_sq (by rfl)) (integrable_E₁p_div_mul_log_sq hx)]
      ring
  · exact intervalIntegrable_one_div_mul_log hx
  · rw [intervalIntegrable_iff, Set.uIoc_of_le hx]
    exact integrable_E₁p_div_mul_log_sq (x := 2) (by rfl)|>.mono (by grind) (by rfl)

theorem E₂p.abs_le {x : ℝ} (hx : 2 ≤ x) :
    |E₂p x| ≤ (log 4 + 6 + E₁) / log x := by
    have : 0 < log x := by apply log_pos; linarith
    rw [E₂p.eq hx, abs_le']
    constructor
    · grw [E₁p.le (by linarith)]
      have : ∫ t in Set.Ioi x, E₁p t / (t * log t^2) ≥ (- 2 - E₁) / log x := calc
        _ ≥ ∫ t in Set.Ioi x, (-2 - E₁) / (t * log t^2) := by
          apply MeasureTheory.setIntegral_mono_on (integrable_const_div_mul_log_sq (-2 - E₁) hx)
            (integrable_E₁p_div_mul_log_sq hx) (by measurability)
          intro y hy; simp at hy
          have : 1 < y := by linarith
          have : 0 < log y := log_pos this
          gcongr; exact E₁p.ge (by linarith)
        _ = _ := integ_div_mul_log_sq (-2 - E₁) hx
      grw [this]
      grind
    grw [E₁p.ge (by linarith)]
    have : ∫ t in Set.Ioi x, E₁p t / (t * log t^2) ≤ (log 4 + 4) / log x := calc
        _ ≤ ∫ t in Set.Ioi x, (log 4 + 4) / (t * log t^2) := by
          apply MeasureTheory.setIntegral_mono_on (integrable_E₁p_div_mul_log_sq hx)
            (integrable_const_div_mul_log_sq (log 4 + 4) hx) (by measurability)
          intro y hy; simp at hy
          have : 1 < y := by linarith
          have : 0 < log y := log_pos this
          gcongr; exact E₁p.le (by linarith)
        _ = _ := integ_div_mul_log_sq (log 4 + 4) hx
    grw [this]
    grind

theorem E₂p.bound : E₂p =O[atTop] (fun x ↦ 1 / log x) := by
    simp only [one_div, isBigO_iff, norm_eq_abs, norm_inv, eventually_atTop]
    use log 4 + 6 + E₁, 2
    intro x hx
    convert E₂p.abs_le hx using 1
    have : 0 < log x := by apply log_pos; linarith
    grind [abs_of_pos this]

theorem E₂p.bound' : E₂p =o[atTop] (fun _ ↦ (1:ℝ)) := E₂p.bound.trans_isLittleO inv_log_eq_o_one

theorem sum_prime_div_eq_log_log : ∃ C, ∀ x, 2 ≤ x →
    |∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, (1:ℝ) / p - log (log x)| ≤ C := by
    use |M| + (log 4 + 6 + E₁) / log 2
    intro x hx
    rw [sum_prime_div_eq]
    calc
      _ = |M + E₂p x| := by ring_nf
      _ ≤ |M| + (log 4 + 6 + E₁) / log x := by grw [abs_add_le, E₂p.abs_le hx]
      _ ≤ _ := by
        gcongr
        have : 0 < log 4 := by apply log_pos; norm_num
        linarith [E₁.nonneg]

theorem sum_prime_div_eq_log_log' : (fun x ↦ ∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, (1:ℝ) / p - log (log x)) =O[atTop] (fun _ ↦ (1:ℝ)) := by
    simp only [isBigO_iff, norm_eq_abs, one_mem, CStarRing.norm_of_mem_unitary, mul_one,
      eventually_atTop]
    obtain ⟨ C, hC ⟩ := sum_prime_div_eq_log_log
    use C, 2

theorem sum_prime_div_eq_log_log'' : (fun x ↦ ∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, (1:ℝ) / p) ~[atTop] (fun x ↦ log (log x)) := by
    apply IsLittleO.isEquivalent (IsBigO.trans_isLittleO _ one_eq_o_log_log)
    convert! sum_prime_div_eq_log_log' using 1

lemma HasSum_log_one_sub_one_div_prime {p : ℕ} (hp : p.Prime) :
    HasSum (fun n : ℕ ↦ (-1 : ℝ) / (( n + 1) * p ^ (n + 1))) (log (1 - 1 / p)) := by
  convert! Real.hasSum_pow_div_log_of_abs_lt_one (x := 1 / p) _|>.neg using 1
  · ext
    rw [div_pow, one_pow, div_div]
    ring
  · ring
  · simp only [one_div, abs_inv, Nat.abs_cast]
    exact inv_lt_one_of_one_lt₀ (mod_cast hp.one_lt)

lemma E₂Λ_sub_E₂p_tendsto :
    Tendsto (E₂Λ - E₂p) atTop (nhds 0) := by
  exact isLittleO_one_iff ℝ|>.mp <| E₂Λ.bound'.sub E₂p.bound'

/-- Function used in the proof of `M.eq`, `Λ n / n * log n` restricted to not primes. -/
noncomputable abbrev M_eq_f (n : ℕ) :=
    if ¬n.Prime then Λ n /(n * log n) else 0

lemma E₂Λ_sub_E₂p_eq (x : ℝ) :
    E₂Λ x - E₂p x = ∑ n ∈ Ioc 0 ⌊x⌋₊, M_eq_f n - (γ - M) := by
  calc
  _ = ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / (n * log n) - ∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, (1 : ℝ) / p - (γ - M) := by ring
  _ = _ := by
    rw [sum_filter, ← sum_sub_distrib]
    congr
    ext n
    split_ifs with hn
    · rw [vonMangoldt_apply_prime hn]
      have : log n ≠ 0 := by simp; grind [hn.two_le]
      field
    · ring

lemma M_eq_f.sum_tendsto :
    Tendsto (fun (x : ℝ) ↦ ∑ n ∈ Ioc 0 ⌊x⌋₊, M_eq_f n) atTop (nhds (γ - M)) := by
  apply tendsto_sub_nhds_zero_iff.mp
  convert E₂Λ_sub_E₂p_tendsto using 1
  ext
  rw [← E₂Λ_sub_E₂p_eq]
  simp

lemma M_eq_f.sum_tendsto' :
    Tendsto (fun (N : ℕ) ↦ ∑ n ∈ range N, M_eq_f n) atTop (nhds (γ - M)) := by
  have : Tendsto (fun (N : ℕ) ↦ (∑ n ∈ Ioc 0 ⌊(N : ℝ)⌋₊, M_eq_f n)) atTop (nhds (γ - M)) := M_eq_f.sum_tendsto.comp tendsto_natCast_atTop_atTop
  simp_rw [Nat.floor_natCast] at this
  apply (this.comp (tendsto_sub_atTop_nat 1)).congr'
  filter_upwards [eventually_ge_atTop 1] with N hn
  rw [Nat.range_eq_Icc_zero_sub_one, ← add_sum_Ioc_eq_sum_Icc] <;> grind

lemma M_eq_f.HasSum :
    HasSum M_eq_f (γ - M) := by
  refine hasSum_iff_tendsto_nat_of_nonneg (fun n ↦ ?_) _|>.mpr M_eq_f.sum_tendsto'
  unfold M_eq_f
  split_ifs with hn
  · rfl
  · exact div_nonneg vonMangoldt_nonneg (by positivity)

lemma M_eq_f.sum_primes :
    ∑' (p : Nat.Primes), M_eq_f p = 0 := by
  convert! tsum_zero with p
  grind

lemma tsum_primes_eq_tsum_ite (f : ℕ → ℝ) :
    ∑' (n : Nat.Primes), f n = ∑' (n : ℕ), if n.Prime then f n else 0 := by
  convert! tsum_subtype {n:ℕ | n.Prime} f using 2
  ext
  simp [Set.indicator]


lemma tsum_M_eq_f_eq_tsum :
    -∑' (n : ℕ), M_eq_f n = ∑' p : ℕ, if p.Prime then log (1 - 1 / p) + 1 / p else 0 := by
  rw [tsum_eq_tsum_primes_add_tsum_primes_of_support_subset_prime_powers M_eq_f.HasSum.summable
    (fun n hn ↦ (by simp_all [vonMangoldt_ne_zero_iff])), M_eq_f.sum_primes, zero_add,
    tsum_primes_eq_tsum_ite (fun p ↦ ∑' (k : ℕ), M_eq_f (p ^ (k + 2))), ← tsum_neg]
  refine tsum_congr fun n ↦ ?_
  split_ifs with hn
  · rw [← HasSum_log_one_sub_one_div_prime hn|>.tsum_eq, HasSum_log_one_sub_one_div_prime hn|>.summable.tsum_eq_zero_add]
    simp only [ite_not, Nat.cast_pow, log_pow, Nat.cast_add, Nat.cast_ofNat, CharP.cast_eq_zero,
      zero_add, pow_one, one_mul, Nat.cast_one, one_div]
    trans -∑' (k : ℕ), (1 : ℝ) / ((k + 2) * n ^ (k + 2))
    · congr
      ext k
      have : ¬(Nat.Prime (n ^ (k + 2))) := by exact Nat.Prime.not_prime_pow (by grind)
      simp only [this, ↓reduceIte, one_div, mul_inv_rev]
      rw [vonMangoldt_apply_pow (by grind), vonMangoldt_apply_prime hn]
      have : log n ≠ 0 := by simp; grind [hn.two_le]
      field
    · rw [← tsum_neg]
      ring_nf
      congr
      ext
      ring_nf
  · ring

theorem M.eq : M = γ + ∑' p : ℕ, if p.Prime then log (1 - 1 / p) + 1 / p else 0 := by
  rw [← tsum_M_eq_f_eq_tsum, M_eq_f.HasSum.tsum_eq]
  ring

noncomputable def E₃ (x : ℝ) : ℝ := ∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, log (1 - (1:ℝ) / p) + log (log x) + eulerMascheroniConstant

theorem prod_one_minus_div_prime_eq {x : ℝ} (hx : 1 < x) :
    ∏ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, (1 - (1 : ℝ) / p) =
      exp (-eulerMascheroniConstant) * exp (E₃ x) / log x := by
  have hlog : 0 < log x := log_pos hx
  have hpos : ∀ {p : ℕ}, p.Prime → (0 : ℝ) < 1 - 1 / p := fun {p} hp ↦ by
    have : (2 : ℝ) ≤ p := mod_cast hp.two_le
    grind [one_div_le_one_div_of_le two_pos this]
  rw [E₃, exp_add, exp_add, exp_sum, exp_log hlog, exp_neg,
    prod_congr rfl fun p hp ↦ exp_log (hpos (mem_filter.mp hp).2)]
  field_simp

noncomputable abbrev M_eq_summand (p : ℕ) := if p.Prime then log (1 - 1 / p) + 1 / p else 0

lemma M_eq_summand_bound (n : ℕ) :
    |M_eq_summand n| ≤ 2 / n ^ 2 := by
  unfold M_eq_summand
  split_ifs with h
  · trans 1 / n ^ 2 / (1 - 1 / n)
    · convert abs_log_sub_add_sum_range_le (x := 1 / n) _ 1 using 1
      · rw [add_comm]
        simp
      · rw [abs_of_nonneg (by simp)]
        ring
      · simpa using inv_lt_one_of_one_lt₀ (mod_cast h.one_lt)
    rw [(by ring : (2 : ℝ) / n ^ 2 = 1 / n ^ 2 / (1 / 2))]
    gcongr
    suffices (1 : ℝ) / n ≤ 1 / 2 by linarith
    gcongr
    exact_mod_cast h.two_le
  · rw [abs_zero]
    positivity

lemma M_eq_summable : Summable M_eq_summand := by
  apply Summable.of_abs
  exact Summable.of_nonneg_of_le (by simp) M_eq_summand_bound (Summable.const_div (by simp) _)

lemma tsum_M_eq_summand_eq :
    ∑' (n : ℕ), M_eq_summand n = M - γ := by
  rw [M.eq]
  grind

lemma sum_one_div_sq_le {N : ℝ} (hN : 1 ≤ N) :
    ∑' (n : ℕ), (1 : ℝ) / (n + N) ^ 2 ≤ 2 / N := by
  grw [AntitoneOn.tsum_le_integral (f := (fun t ↦ 1 / (t + N) ^ 2))]
  · have hd : ∀ x ∈ Set.Ici 0, HasDerivAt (fun t ↦ -1 / (t + N)) (1 / (x + N) ^ 2) x := by
      intro t ht
      convert! HasDerivAt.fun_div (d' := (1 : ℝ)) (hasDerivAt_const ..) _ _ using 1
      · ring
      · simpa using hasDerivAt_id' t
      · simp at ht
        linarith
    have lim : Tendsto (fun t ↦ -1 / (t + N)) atTop (nhds 0) := by
      exact (tendsto_atTop_add_const_right atTop N tendsto_id).const_div_atTop _
    rw [MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg' hd (fun _ _ ↦ (by positivity)) lim]
    ring_nf
    rw [mul_two]
    gcongr
    field_simp
    exact hN
  · unfold AntitoneOn
    intro a ha b hb h
    beta_reduce
    simp at ha hb
    gcongr
  · convert! integrableOn_add_rpow_Ioi_of_lt (by norm_num : (-2 : ℝ) < -1) (by linarith : -N < 0) using 2
    simp
  · exact fun _ _ ↦ (by positivity)

lemma sum_M_eq_summand_le {N : ℕ} (hN : 0 < N) :
    |∑ n ∈ range N, M_eq_summand n - (M - γ)| ≤ 4 / N := by
  rw [← tsum_M_eq_summand_eq, ← M_eq_summable.sum_add_tsum_nat_add N]
  simp only [sub_add_cancel_left, abs_neg]
  rw [← norm_eq_abs]
  have summable := summable_nat_add_iff N|>.mpr M_eq_summable.norm
  apply norm_tsum_le_tsum_norm summable|>.trans
  apply Summable.tsum_le_tsum (fun _ ↦ M_eq_summand_bound _) summable _|>.trans
  · conv => lhs; arg 1; ext; rw [← mul_one_div]
    rw [tsum_mul_left]
    push_cast
    grw [sum_one_div_sq_le (mod_cast hN)]
    ring_nf
    rfl
  · exact (summable_nat_add_iff N|>.mpr (summable_one_div_nat_pow.mpr one_lt_two))|>.const_div _

lemma sum_M_eq_summand_le' {x : ℝ} (hx : 2 ≤ x) :
    |∑ n ∈ Ioc 0 ⌊x⌋₊, M_eq_summand n - (M - γ)| ≤ 4 / x := by
  have := sum_M_eq_summand_le (by grind : 0 < ⌊x⌋₊ + 1)
  rw [Nat.range_eq_Icc_zero_sub_one _ (by grind), ← add_sum_Ioc_eq_sum_Icc (by grind),
    (by simp : M_eq_summand 0 = 0), zero_add] at this
  simp only [add_tsub_cancel_right, Nat.cast_add, Nat.cast_one] at this
  grw [this]
  gcongr
  exact Nat.lt_floor_add_one _|>.le

theorem E₃.abs_le : ∃ C, ∀ x, 2 ≤ x → |E₃ x| ≤ C / log x := by
  unfold E₃
  refine ⟨4 + (log 4 + 6 + E₁), fun x hx ↦ ?_⟩
  calc
  _ = |(∑ n ∈ Ioc 0 ⌊x⌋₊, M_eq_summand n - (M - γ)) - E₂p x| := by
    unfold E₂p
    have (n : ℕ) : M_eq_summand n = (if n.Prime then log (1 - 1 / n) else 0) + (if n.Prime then (1 : ℝ) / n else 0) := by
      unfold M_eq_summand
      split_ifs
      · rfl
      · ring
    simp_rw [this]
    rw [sum_filter, sum_filter, sum_add_distrib, γ.eq_eulerMascheroni]
    ring_nf
  _ ≤ _ := by
    grw [abs_sub, E₂p.abs_le hx, sum_M_eq_summand_le' hx]
    have : 4 / x ≤ 4 / log x := by
      gcongr
      · exact log_pos (by linarith)
      · exact log_le_self (by linarith)
    grw [this]
    rw [← add_div]

theorem E₃.bound : E₃ =O[atTop] (fun x ↦ 1 / log x) := by
    simp only [isBigO_iff, norm_eq_abs, eventually_atTop]
    obtain ⟨ C, hC ⟩ := E₃.abs_le
    use C, 2
    convert hC using 3 with x hx
    have : 0 < log x := by apply log_pos; linarith
    have : 0 < 1 / log x := by positivity
    grind [abs_of_pos this]

theorem E₃.bound' : E₃ =o[atTop] (fun _ ↦ (1:ℝ)) := E₃.bound.trans_isLittleO inv_log_eq_o_one

theorem E₃.bound'' : (fun x ↦ ∏ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (1 - (1:ℝ) / p)) ~[atTop] (fun x ↦ exp (-eulerMascheroniConstant) / log x) := by
   rw [isEquivalent_iff_tendsto_one]
   · convert Tendsto.congr' ?_ (Tendsto.rexp ((isLittleO_one_iff ℝ).mp E₃.bound')) using 2 with x
     · simp
     simp only [EventuallyEq.iff_eventually, Pi.div_apply, eventually_atTop]; use 2; intro x hx
     rw [prod_one_minus_div_prime_eq (by linarith)]
     have : 0 < log x := by apply log_pos; linarith
     field_simp
   simp only [ne_eq, div_eq_zero_iff, exp_ne_zero, log_eq_zero, eventually_atTop]; use 2
   grind

end Mertens
end

section
open Finset Filter Real
open scoped Topology
noncomputable section
namespace ReflectedMertens
open MeanSquareEulerBounds ReflectedPrimeBlocks

def constant : ℝ := 2*Real.exp (-Real.eulerMascheroniConstant)

theorem odd_identity {x : ℝ} (hx : 2≤x) :
    off (lowPrimes ⌊x⌋₊) = 2*Real.exp (-Real.eulerMascheroniConstant)*Real.exp (Mertens.E₃ x)/Real.log x := by
  let T := lowPrimes ⌊x⌋₊
  have two : 2≤⌊x⌋₊ := Nat.le_floor hx
  have eq : ((Ioc 0 ⌊x⌋₊).filter Nat.Prime) = insert 2 T := by
    ext p
    simp only [T,lowPrimes,mem_filter,mem_insert,mem_range,Nat.lt_succ_iff,mem_Ioc]
    constructor
    · rintro ⟨⟨_,cut⟩,pr⟩
      by_cases e : p=2
      · exact Or.inl e
      · exact Or.inr ⟨cut,pr,lt_of_le_of_ne pr.two_le (Ne.symm e)⟩
    · rintro (rfl|⟨cut,pr,big⟩)
      · exact ⟨⟨by decide,two⟩,Nat.prime_two⟩
      · exact ⟨⟨by omega,cut⟩,pr⟩
  have n2 : 2∉T := fun h => (mem_filter.mp h).2.2.false
  have allp := Mertens.prod_one_minus_div_prime_eq (show 1<x by linarith)
  rw [eq,prod_insert n2] at allp
  change _ = _ at allp
  change (∏p∈T,(1-1/(p:ℝ)))=_
  push_cast at allp
  simp only [div_eq_mul_inv] at allp ⊢
  linarith only [allp]

theorem odd_real : Tendsto (fun x:ℝ => Real.log x * off (lowPrimes ⌊x⌋₊)) atTop (𝓝 constant) := by
  have small : Tendsto Mertens.E₃ atTop (𝓝 0) := (Asymptotics.isLittleO_one_iff ℝ).mp Mertens.E₃.bound'
  have lim : Tendsto (fun x:ℝ=>constant*Real.exp (Mertens.E₃ x)) atTop (𝓝 constant) := by
    simpa using small.rexp.const_mul constant
  apply lim.congr'
  filter_upwards [eventually_ge_atTop (2:ℝ)] with x hx
  rw [odd_identity hx]
  have hlog : Real.log x ≠ 0 := (Real.log_pos (by linarith : 1<x)).ne'
  unfold constant
  field_simp

theorem odd_nat : Tendsto (fun n:ℕ => Real.log n * off (lowPrimes n)) atTop (𝓝 constant) := by
  simpa [Function.comp_def] using odd_real.comp (tendsto_natCast_atTop_atTop (R:=ℝ))

end ReflectedMertens
end

section
open Filter Real Finset
open scoped Topology
noncomputable section
namespace ReflectedLowerScales
open ReflectedMertens ReflectedPrimeBlocks MeanSquareEulerBounds

def low (s : ℝ) : ℕ := ⌊s/8⌋₊
def highArg (s : ℝ) : ℝ := s*(Real.log s)^2
def high (s : ℝ) : ℕ := ⌊highArg s⌋₊

theorem low_atTop : Tendsto (fun s:ℝ=>s/8) atTop atTop := by
  simpa [div_eq_mul_inv] using (tendsto_id.atTop_mul_const (by norm_num : (0:ℝ)<(8:ℝ)⁻¹))

theorem high_atTop : Tendsto highArg atTop atTop := by
  apply tendsto_atTop_mono' atTop _ (tendsto_id (α:=ℝ))
  filter_upwards [eventually_ge_atTop (Real.exp 1)] with s large
  have l : 1≤Real.log s := by simpa using (log_le_log (exp_pos _) large)
  have hs := (exp_pos 1).trans_le large
  change s ≤ s *(Real.log s)^2
  exact le_mul_of_one_le_right hs.le (one_le_pow₀ l)

private theorem common {arg : ℝ→ℝ} (atop : Tendsto arg atTop atTop)
    (ratio : Tendsto (fun s:ℝ=>Real.log (arg s)/Real.log s) atTop (𝓝 1)) :
    Tendsto (fun s:ℝ=>Real.log s*off (lowPrimes ⌊arg s⌋₊)) atTop (𝓝 constant) := by
  have lim := (odd_real.comp atop).div ratio (by norm_num : (1:ℝ)≠0)
  apply (show Tendsto (fun s:ℝ=>(Real.log (arg s)*off (lowPrimes ⌊arg s⌋₊))/(Real.log (arg s)/Real.log s))
      atTop (𝓝 constant) by simpa [Function.comp_def,Pi.div_def] using lim).congr'
  filter_upwards [atop.eventually (eventually_gt_atTop (1:ℝ)),eventually_gt_atTop (1:ℝ)] with s larg hs
  have l := (log_pos hs).ne'
  have la := (log_pos larg).ne'
  field_simp

theorem low_limit : Tendsto (fun s:ℝ=>Real.log s*off (lowPrimes (low s))) atTop (𝓝 constant) := by
  apply common low_atTop
  have lim := (tendsto_const_nhds (x:=(1:ℝ))).sub (Real.tendsto_log_atTop.const_div_atTop (Real.log 8))
  apply (show Tendsto (fun s:ℝ=> 1-Real.log 8/Real.log s) atTop (𝓝 1) by simpa using lim).congr'
  filter_upwards [eventually_gt_atTop (1:ℝ)] with s hs
  rw [Real.log_div (by linarith : s ≠ 0) (by norm_num : (8:ℝ)≠0)]
  field_simp [(log_pos hs).ne']

theorem high_limit : Tendsto (fun s:ℝ=>Real.log s*off (lowPrimes (high s))) atTop (𝓝 constant) := by
  apply common high_atTop
  have small : Tendsto (fun s:ℝ => log (log s)/log s) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp Real.tendsto_log_atTop
  have lim := (tendsto_const_nhds (x:=(1:ℝ))).add (small.const_mul 2)
  apply (show Tendsto (fun s:ℝ=>1+2*(log (log s)/log s)) atTop (𝓝 1) by simpa using lim).congr'
  filter_upwards [eventually_gt_atTop (1:ℝ)] with s hs
  have l := (log_pos hs).ne'
  rw [highArg,Real.log_mul (by linarith : s≠0) (pow_ne_zero 2 l),Real.log_pow]
  push_cast
  field_simp

theorem lost_mass : Tendsto (fun s:ℝ=>log s*(s/(high s:ℝ))) atTop (𝓝 0) := by
  have floorRatio : Tendsto (fun s:ℝ=>(high s:ℝ)/highArg s) atTop (𝓝 1) := tendsto_nat_floor_div_atTop.comp high_atTop
  have lim := (Real.tendsto_log_atTop.const_div_atTop (1:ℝ)).div floorRatio (by norm_num : (1:ℝ)≠0)
  apply (show Tendsto (fun s:ℝ=>(1/log s)/((high s:ℝ)/highArg s)) atTop (𝓝 0) by simpa [Pi.div_def] using lim).congr'
  filter_upwards [eventually_gt_atTop (1:ℝ)] with s hs
  have l := (log_pos hs).ne'
  unfold highArg
  by_cases bad : (high s:ℝ)=0
  · simp [bad]
  · field_simp [l,bad,show s≠0 by linarith]


end ReflectedLowerScales
end

section
open Finset
open MeanSquareRows
open ReflectedModelGain ReflectedBlockLaw ReflectedModelWindow MeanSquareEulerBounds
namespace ReflectedLowerModel
noncomputable section

def clear {T : Finset ℕ} (X : ℕ) (S : Finset (↥T)) : Prop := ∀ p ∈ S, X < p.val
instance {T : Finset ℕ} (X : ℕ) (S : Finset (↥T)) : Decidable (clear X S) :=
  inferInstanceAs (Decidable (∀ p ∈ S, X < p.val))

def off (T : Finset ℕ) (X : ℕ) := ∏ p ∈ T.filter (·≤X), (1-1/(p:ℝ))
def high (T : Finset ℕ) (X : ℕ) := ∏ p ∈ T.filter (X<·), (1+1/((p:ℝ)*(p-2)))

theorem mixed (T : Finset ℕ) (X : ℕ) (f : ℕ → ℝ) :
    (∑ S, if clear X S then siteMass T S * (∏p∈S,f p.val) else 0) =
      off T X * ∏ p ∈ T.filter (X<·), (1-1/(p:ℝ)+(1/(p:ℝ))*f p) := by
  classical
  let on := fun p : ↥T => if X<p.val then (1/(p.val:ℝ))*f p.val else 0
  let notOn := fun p : ↥T => 1-1/(p.val:ℝ)
  have row (S : Finset (↥T)) : (if clear X S then siteMass T S*(∏p∈S,f p.val) else 0) =
      (∏ p∈S,on p)*(∏ p∈Sᶜ,notOn p) := by
    by_cases hit : clear X S
    · rw [ite_eq_left hit]
      have hitvals : (∏p∈S,on p) = (∏p∈S,(1/(p.val:ℝ)) * f p.val) :=
        prod_congr rfl (fun p hp => ite_eq_left (hit p hp))
      rw [hitvals,prod_mul_distrib]
      unfold siteMass
      ring
    · rw [ite_eq_right hit]
      obtain ⟨p,hp,bad⟩ : ∃ p ∈ S, ¬ X < p.val := by
        by_contra! h
        exact hit h
      rw [prod_eq_zero hp (show on p=0 by simp [on,bad]),zero_mul]
  simp_rw [row]
  rw [← Fintype.prod_add]
  let t := fun p : ℕ => (if X<p then 1/(p:ℝ)*f p else 0) + (1-1/(p:ℝ))
  change (∏ p : ↥T, t p.val) = _
  rw [Finset.prod_coe_sort]
  rw [← prod_filter_mul_prod_filter_not T (fun p => p≤X) t]
  unfold off
  apply congrArg₂ (·*·)
  · apply prod_congr rfl
    intro p hp
    simp [t,not_lt.mpr (mem_filter.mp hp).2]
  · simp only [not_le]
    apply prod_congr rfl
    intro p hp
    simp only [t,ite_eq_left (mem_filter.mp hp).2,add_comm]

theorem clear_mass (T : Finset ℕ) (X : ℕ) :
    (∑ S : Finset (↥T), if clear X S then siteMass T S else 0) = off T X := by
  simpa using mixed T X (fun _ => 1)

theorem clear_moment (T : Finset ℕ) (X : ℕ) :
    (∑ S : Finset (↥T), if clear X S then siteMass T S*site T S else 0) = off T X*high T X := by
  rw [show (∑ S : Finset (↥T), if clear X S then siteMass T S*site T S else 0) = _ from mixed T X factor]
  unfold high
  congr 1
  apply prod_congr rfl
  intro p hp
  unfold factor
  simp only [one_div,mul_inv_rev]
  ring

theorem site_one (T : Finset ℕ) (ok : ∀p∈T,2<p) (S : Finset (↥T)) : 1 ≤ site T S :=
  one_le_prod₀ (fun p _ => factor_ge (ok p.val p.property))

def prob (T : Finset ℕ) (δ : ℝ) : ℝ :=
  ∑ S, if 2*C2*site T S ≤ 2*C2+δ then siteMass T S else 0

theorem lower (T : Finset ℕ) (ok : ∀p∈T,2<p) (X : ℕ) {δ : ℝ} (dp : 0 < δ) :
    off T X*(1-(2*C2/δ)*(high T X-1)) ≤ prob T δ := by
  have cp : 0 ≤ 2*C2 := by linarith [C2_lower]
  have wpos (S : Finset (↥T)) : 0 ≤ siteMass T S :=
    siteMass_nonneg T (fun p hp => by have := ok p hp;omega) S
  have each (S : Finset (↥T)) :
      (if clear X S then siteMass T S else 0) -
      (2*C2/δ)*((if clear X S then siteMass T S*site T S else 0) -
        (if clear X S then siteMass T S else 0)) ≤
      (if 2*C2*site T S ≤ 2*C2+δ then siteMass T S else 0) := by
    by_cases hc : clear X S
    · simp only [hc,ite_true]
      have nz := mul_nonneg (div_nonneg cp dp.le) (mul_nonneg (wpos S) (sub_nonneg.mpr (site_one T ok S)))
      split_ifs with h
      · nlinarith only [nz]
      · have bad : 1 ≤ (2*C2/δ)*(site T S-1) := by
          rw [div_mul_eq_mul_div,le_div_iff₀ dp];push Not at h
          linarith
        nlinarith only [mul_le_mul_of_nonneg_left bad (wpos S)]
    · simp only [hc,ite_false,sub_zero,mul_zero]
      split <;> first | exact wpos S | rfl
  have h := sum_le_sum (s:=univ) (fun S _ => each S)
  simp only [sum_sub_distrib,← mul_sum,clear_mass,clear_moment] at h
  unfold prob
  linarith only [h]

theorem upper (T : Finset ℕ) (ok : ∀p∈T,2<p) (X : ℕ) (δ : ℝ)
    (gap : ∀ p∈T, p≤X → δ < 2*C2/((p:ℝ)-2)) :
    prob T δ ≤ off T X := by
  rw [← clear_mass T X]
  apply sum_le_sum
  intro S _
  by_cases small : clear X S
  · simp only [small,ite_true]
    split <;> first | rfl | exact siteMass_nonneg T (fun p hp => by have := ok p hp;omega) S
  · have not_hit : ¬ 2*C2*site T S ≤ 2*C2+δ := by
      obtain ⟨p,hp,bad⟩ : ∃ p∈S, ¬ X < p.val := by
        by_contra! h;exact small h
      have fg : factor p.val ≤ site T S := by
        have sub : {p} ⊆ S := singleton_subset_iff.mpr hp
        simpa [site] using Finset.prod_le_prod_of_subset_of_one_le₀ (f:=fun q:↥T=>factor q.val) sub
          (fun j _ => zero_le_one.trans (factor_ge (ok j.val j.property))) (fun j _ _ => factor_ge (ok j.val j.property))
      have cp : 0 ≤ 2*C2 := by linarith [C2_lower]
      have win := gap p.val p.property (le_of_not_gt bad)
      have lower := mul_le_mul_of_nonneg_left fg cp
      unfold factor at lower
      rw [div_eq_mul_inv] at win
      simp only [one_div] at lower
      linarith
    simp [small,not_hit]

theorem low_off {X y : ℕ} (xy : X ≤ y) :
    off (lowPrimes y) X = ReflectedPrimeBlocks.off (lowPrimes X) := by
  have eq : (lowPrimes y).filter (·≤X) = lowPrimes X := by
    ext p
    simp only [lowPrimes,mem_filter,mem_range,Nat.lt_succ_iff]
    constructor
    · rintro ⟨⟨_,h⟩,hX⟩; exact ⟨hX,h⟩
    · rintro ⟨hX,h⟩;exact ⟨⟨hX.trans xy,h⟩,hX⟩
  rw [off,eq]
  rfl

def periodHits (y : ℕ) (δ : ℝ) : ℝ :=
  ∑ r∈range (W y), if value y r ≤ 2*C2+δ then (1:ℝ) else 0

theorem period_law (y : ℕ) (δ : ℝ) : periodHits y δ = (W y:ℝ)*prob (lowPrimes y) δ := by
  let T := lowPrimes y
  have pr : ∀p∈T,p.Prime := fun p hp => (mem_filter.mp hp).2.1
  let f := fun x : Finset (↥T) => if 2*C2*site T x ≤ 2*C2+δ then (1:ℝ) else 0
  have eq := ReflectedModelCRT.residue_law T pr f
  simpa only [periodHits,ReflectedModelLaw.wheel_eq,ReflectedModelLaw.all_values,prob,f,T,mul_ite,mul_one,mul_zero] using eq

theorem period_lower {y X : ℕ} (xy : X ≤ y) {δ : ℝ} (dp : 0<δ) :
    (W y:ℝ)*(ReflectedPrimeBlocks.off (lowPrimes X)*
      (1-(2*C2/δ)*(high (lowPrimes y) X-1))) ≤ periodHits y δ := by
  rw [period_law,← low_off xy]
  exact mul_le_mul_of_nonneg_left (lower _ (fun p hp => (mem_filter.mp hp).2.2) _ dp) (Nat.cast_nonneg _)

theorem period_upper {y X : ℕ} (xy : X ≤ y) (δ : ℝ)
    (gap : ∀p∈lowPrimes X, δ < 2*C2/((p:ℝ)-2)) :
    periodHits y δ ≤ (W y:ℝ)*ReflectedPrimeBlocks.off (lowPrimes X) := by
  rw [period_law,← low_off xy]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply upper _ (fun p hp => (mem_filter.mp hp).2.2)
  intro p hp px
  exact gap p (mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_iff.mpr px),(mem_filter.mp hp).2⟩)

end
end ReflectedLowerModel
end

section
namespace ReflectedHighBound
open Finset

noncomputable def factor (p:ℕ) : ℝ := 1+1/((p:ℝ)*(p-2))

theorem exact_product {X:ℕ} (hx:2≤X) (k:ℕ) :
   (∏p∈Ioc X (X+k),factor p) =
     ((X:ℝ)/((X:ℝ)-1))*(((X:ℝ)+k-1)/((X:ℝ)+k)) := by
  have a : (1:ℝ)<X := by exact_mod_cast (show 1<X by omega)
  induction k with
  | zero =>
    simp only [Nat.cast_zero,add_zero,Ioc_self,prod_empty]
    have x : (0:ℝ)<X := by positivity
    have x0 : (X:ℝ)-1 ≠ 0 := (sub_pos.mpr a).ne'
    field_simp
  | succ k ih =>
    rw [Nat.add_succ,prod_Ioc_succ_top (by omega), ih]
    unfold factor
    push_cast
    have p : (0:ℝ)<(X:ℝ)+k := by exact add_pos_of_pos_of_nonneg (by positivity) (Nat.cast_nonneg _)
    have xp : (0:ℝ)<(X:ℝ)-1 := sub_pos.mpr a
    have z : 0<(X:ℝ)+(k:ℝ)+1-2 := by linarith [Nat.cast_nonneg (α:=ℝ) k]
    have d : 0<(X:ℝ)+(k:ℝ)+1 := by linarith
    have e : 0<(X:ℝ)+((k:ℝ)+1) := by linarith
    field_simp
    ring

theorem bound {X:ℕ} (hx:2≤X) (S:Finset ℕ) (high:∀p∈S,X<p) :
    (∏p∈S,factor p)≤1+2/(X:ℝ) := by
  let k:=S.sup id
  have sub : S⊆Ioc X (X+k) := by
    intro p hp
    have s : p≤k := le_sup (f:=id) hp
    exact mem_Ioc.mpr ⟨high p hp,by omega⟩
  have g (p:ℕ) (hp:X<p) : 1≤factor p := by
    have t : 2<p := by omega
    have u : 0<(p:ℝ)-2 := sub_pos.mpr (by exact_mod_cast t)
    unfold factor
    linarith [one_div_nonneg.mpr (mul_nonneg (Nat.cast_nonneg p) u.le)]
  have up := prod_le_prod_of_subset_of_one_le₀ sub
    (fun p hp => (show 0≤(1:ℝ) by norm_num).trans (g p (high p hp)))
    (fun p hp _ => g p (mem_Ioc.mp hp).1)
  rw [exact_product hx] at up
  have x : (0:ℝ)<X := by exact_mod_cast (show 0<X by omega)
  have xp : (0:ℝ)<(X:ℝ)-1 := sub_pos.mpr (by exact_mod_cast (show 1<X by omega))
  have x2 : (2:ℝ)≤X := by exact_mod_cast hx
  apply up.trans
  calc
    _ ≤ (X:ℝ)/((X:ℝ)-1) := mul_le_of_le_one_right (by positivity)
      ((div_le_one (add_pos_of_pos_of_nonneg x (Nat.cast_nonneg _))).mpr (by linarith))
    _ ≤ 1+2/(X:ℝ) := by
      apply (div_le_iff₀ xp).mpr
      field_simp
      linarith

theorem actual {X y:ℕ} (hx:2≤X) : ReflectedLowerModel.high (MeanSquareEulerBounds.lowPrimes y) X ≤ 1+2/(X:ℝ) := by
  apply bound hx
  intro p hp
  exact (Finset.mem_filter.mp hp).2

end ReflectedHighBound
end

section
open Filter Finset MeanSquareRows MeanSquareEulerBounds ReflectedModelGain
namespace ReflectedLowerThresholds
noncomputable section

theorem off_unit (X : ℕ) : 0 ≤ ReflectedPrimeBlocks.off (lowPrimes X) ∧
    ReflectedPrimeBlocks.off (lowPrimes X) ≤ 1 := by
  have pos (p : ℕ) (hp : p∈lowPrimes X) : 0≤1-1/(p:ℝ) := by
    have pr : (1:ℝ) ≤ p := by exact_mod_cast (mem_filter.mp hp).2.1.one_le
    exact sub_nonneg.mpr ((one_div_le_one_div_of_le zero_lt_one pr).trans (by norm_num))
  exact ⟨prod_nonneg pos,prod_le_one₀ pos (fun p _ => sub_le_self _ (by positivity))⟩

theorem small_prime_gap {s : ℝ} (sp : 0<s) {p : ℕ}
    (mem : p∈lowPrimes (ReflectedLowerScales.low s)) : 2/s < 2*C2/((p:ℝ)-2) := by
  have p2 := (mem_filter.mp mem).2.2
  have px : p ≤ ReflectedLowerScales.low s := Nat.lt_succ_iff.mp (mem_range.mp (mem_filter.mp mem).1)
  have pr : (2:ℝ) < p := by exact_mod_cast p2
  have ps : (p:ℝ) ≤ s/8 := (by exact_mod_cast px : (p:ℝ) ≤ (ReflectedLowerScales.low s:ℝ)).trans
    (Nat.floor_le (by positivity : (0:ℝ) ≤ s/8))
  apply (div_lt_div_iff₀ sp (sub_pos.mpr pr)).mpr
  nlinarith only [ps,sp,mul_le_mul_of_nonneg_right C2_lower sp.le]

theorem scale_order : ∀ᶠ s:ℝ in atTop, 0<s ∧ 2≤ReflectedLowerScales.high s ∧
    ReflectedLowerScales.low s ≤ ReflectedLowerScales.high s := by
  have htop : Tendsto ReflectedLowerScales.high atTop atTop :=
    tendsto_nat_floor_atTop.comp ReflectedLowerScales.high_atTop
  filter_upwards [eventually_ge_atTop (Real.exp 1),htop.eventually_ge_atTop 2] with s hs high
  have sp := (Real.exp_pos 1).trans_le hs
  have l : 1≤Real.log s := by simpa using Real.log_le_log (Real.exp_pos _) hs
  have h : s ≤ ReflectedLowerScales.highArg s :=
    le_mul_of_one_le_right sp.le (one_le_pow₀ l)
  exact ⟨sp,high,Nat.floor_mono ((by linarith : s/8 ≤ s).trans h)⟩

theorem uniform : ∀ᶠ s:ℝ in atTop, ∀ y≥ReflectedLowerScales.high s,
    (W y:ℝ)*(ReflectedPrimeBlocks.off (lowPrimes (ReflectedLowerScales.high s)) -
        8*C2*(s/(ReflectedLowerScales.high s:ℝ))) ≤ ReflectedLowerModel.periodHits y (1/(2*s)) ∧
    ReflectedLowerModel.periodHits y (2/s) ≤
      (W y:ℝ)*ReflectedPrimeBlocks.off (lowPrimes (ReflectedLowerScales.low s)) := by
  filter_upwards [scale_order] with s lord
  obtain ⟨sp,h2,lh⟩ := lord
  intro y hy
  let X := ReflectedLowerScales.high s
  have xr : (0:ℝ)<X := by exact_mod_cast (by omega : 0 < ReflectedLowerScales.high s)
  let b := ReflectedPrimeBlocks.off (lowPrimes X)
  have ob := off_unit X
  have op : 0≤b := ob.1
  have ou : b≤1 := ob.2
  have cp : 0≤C2 := by linarith [C2_lower]
  have dp : (0:ℝ)<1/(2*s) := by positivity
  refine ⟨?_, ReflectedLowerModel.period_upper (lh.trans hy) (2/s) (fun _ hp => small_prime_gap sp hp)⟩
  apply le_trans _ (ReflectedLowerModel.period_lower hy dp)
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  let tail := ReflectedLowerModel.high (lowPrimes y) X
  have tb : tail - 1 ≤ 2/(X:ℝ) := by linarith only [ReflectedHighBound.actual (y:=y) h2]
  have ratio : (2*C2/(1/(2*s)))*(2/(X:ℝ))=8*C2*(s/(X:ℝ)) := by field_simp;ring
  have loss : (2*C2/(1/(2*s)))*(tail-1) ≤ 8*C2*(s/(X:ℝ)) :=
    (mul_le_mul_of_nonneg_left tb (by positivity)).trans_eq ratio
  have cp' : 0 ≤ 8*C2*(s/(X:ℝ)) := by positivity
  have cap := (mul_le_mul_of_nonneg_left loss op).trans (mul_le_of_le_one_left cp' ou)
  change b-8*C2*(s/(X:ℝ)) ≤ b*(1-(2*C2/(1/(2*s)))*(tail-1))
  linarith only [cap]
end
end ReflectedLowerThresholds
end

section
open Finset Filter
open scoped Topology
noncomputable section
namespace ReflectedLowerFinish
open MeanSquareGeometry MeanSquareEnergy MeanSquareConclusion ReflectedModelGain
open MeanSquareEulerBounds ReflectedPrimeBlocks ReflectedLowerScales ReflectedMertens

def cdf {α : Type*} (F : Finset α) (f : α→ℝ) (t : ℝ) : ℝ :=
  ((F.filter (fun m=>f m≤t)).card:ℝ)/F.card

theorem cdf_mono {α : Type*} (F : Finset α) (f : α→ℝ) {t u : ℝ} (tu : t≤u) :
    cdf F f t ≤ cdf F f u := by
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have inc : F.filter (fun m=>f m≤t) ⊆ F.filter (fun m=>f m≤u) := by
    intro m hm
    exact mem_filter.mpr ⟨(mem_filter.mp hm).1, (mem_filter.mp hm).2.trans tu⟩
  exact_mod_cast Finset.card_le_card inc

private theorem filter_mul {α : Type*} (F : Finset α) (f : α→ℝ) (t h : ℝ) :
    ((F.filter (fun m=>f m≤t)).card:ℝ)*h^2 = ∑m∈F, if f m≤t then h^2 else 0 := by
  rw [←sum_filter];simp

theorem cdf_transfer {α : Type*} (F : Finset α) (f g : α→ℝ) (t h : ℝ) (hp : 0<h) :
    cdf F f t ≤ cdf F g (t+h) +
      ((∑m∈F,(f m - g m)^2)/F.card)/h^2 := by
  have cap : ((F.filter (fun m=>f m≤t)).card:ℝ)*h^2 ≤
      ((F.filter (fun m=>g m≤t+h)).card:ℝ)*h^2 + ∑m∈F,(f m-g m)^2 := by
    rw [filter_mul,filter_mul,←sum_add_distrib]
    apply sum_le_sum
    intro m _
    by_cases hf : f m≤t
    · by_cases hg : g m≤t+h
      · simp [hf,hg,sq_nonneg]
      · simp [hf,hg]
        have far : h≤g m-f m := by linarith [lt_of_not_ge hg]
        simpa only [show (g m-f m)^2=(f m-g m)^2 by ring] using pow_le_pow_left₀ hp.le far 2
    · by_cases hg : g m≤t+h <;> simp [hf,hg,add_nonneg,sq_nonneg]
  by_cases empty : F.card=0
  · simp [cdf,empty]
  have fp : (0:ℝ)<F.card := by exact_mod_cast Nat.pos_of_ne_zero empty
  unfold cdf
  field_simp
  linarith only [cap]

def ModelTails (C : ℝ) : Prop :=
  ∀ᶠ s : ℝ in atTop, ∀ η:ℝ, 0<η → ∃ Y:ℕ, ∀ y≥Y, ∀ᶠ N:ℕ in atTop,
    off (lowPrimes (high s))-C*(s/(high s:ℝ))-η ≤ cdf (B N) (model y) (2*C2+1/(2*s)) ∧
    cdf (B N) (model y) (2*C2+2/s) ≤ off (lowPrimes (low s))+η

def TrueTails (C : ℝ) : Prop :=
  ∀ᶠ s : ℝ in atTop, ∀ᶠ N:ℕ in atTop,
    off (lowPrimes (high s))-C*(s/(high s:ℝ))-2/s ≤ cdf (B N) (R N) (2*C2+1/s) ∧
    cdf (B N) (R N) (2*C2+1/s) ≤ off (lowPrimes (low s))+2/s

private theorem large_cut (Y:ℕ) (C θ:ℝ) (_cp:0<C) (tp:0<θ) :
    ∃ y:ℕ, Y≤y ∧ 3≤y ∧ C/(y:ℝ)^2 ≤ θ := by
  obtain ⟨k,hk⟩:=exists_nat_gt (C/θ)
  let y:=max 3 (max k Y)
  have Yy : Y≤y := (le_max_right k Y).trans (le_max_right ..)
  have ky : k≤y := (le_max_left k Y).trans (le_max_right ..)
  have y3 : 3≤y := le_max_left ..
  have yr : (1:ℝ)≤y := by exact_mod_cast (by omega : 1≤y)
  refine ⟨y,Yy,y3,(div_le_iff₀ (by positivity)).mpr ?_⟩
  have l: C < (k:ℝ)*θ := (div_lt_iff₀ tp).mp hk
  have kr:(k:ℝ)≤y := by exact_mod_cast ky
  have hi : (k:ℝ)≤(y:ℝ)^2 := kr.trans (by nlinarith [sq_nonneg ((y:ℝ)-1)])
  linarith only [mul_le_mul_of_nonneg_right hi tp.le,l]

theorem from_models {C:ℝ} (models : ModelTails C) : TrueTails C := by
  obtain ⟨D,dp,tail⟩:=MeanSquareConclusion.main MeanSquareOrth.orth
  filter_upwards [models,eventually_gt_atTop (0:ℝ)] with s models hs
  let h := 1/(2*s)
  have hp : 0<h := by dsimp [h];positivity
  let η:=1/s
  have ep : 0<η := by dsimp [η];positivity
  obtain ⟨Y,good⟩:= models η ep
  obtain ⟨y,yY,y3,yc⟩:=large_cut Y D (η*h^2) dp (by positivity)
  filter_upwards [good y yY,tail y y3] with N modB err
  let A := R N
  let P := model y
  let v := 2*C2+1/s
  have main : ((∑m∈B N,(A m-P m)^2)/(B N).card)/h^2 ≤ η := by
    apply (div_le_iff₀ (by positivity)).mpr
    exact err.trans yc
  have rev : (∑m∈B N,(P m-A m)^2) = ∑m∈B N,(A m-P m)^2 := by
    apply sum_congr rfl;intro m _;ring
  have upper := cdf_transfer (B N) A P v h hp
  have lower := cdf_transfer (B N) P A (v-h) h hp
  rw [rev,sub_add_cancel] at lower
  have old : v-h=2*C2+1/(2*s) := by dsimp [v,h];field_simp;ring
  rw [old] at lower
  have widen : v+h ≤ 2*C2+2/s := by dsimp [v,h];field_simp;linarith
  have ubd := (cdf_mono (B N) P widen).trans modB.2
  change _ ≤ cdf (B N) A v ∧ cdf (B N) A v ≤ _
  dsimp [η] at main modB ubd
  have lb : off (lowPrimes (high s))-C*(s/(high s:ℝ))-1/s ≤ cdf (B N) A v+((∑m∈B N,(A m-P m)^2)/(B N).card)/h^2 := modB.1.trans lower
  have ub := upper.trans (add_le_add ubd main)
  simp only [div_eq_mul_inv,one_mul] at lb ub main ⊢
  exact ⟨by linarith only [lb,main],by linarith only [ub]⟩

theorem squeeze {C:ℝ} (tails : TrueTails C) :
    ∀ ε:ℝ, 0<ε → ∃ δ0:ℝ, 0<δ0 ∧ ∀ δ:ℝ, 0<δ → δ<δ0 → ∃ T:ℕ, ∀ N≥T,
      |Real.log (1/δ)*cdf (B N) (R N) (2*C2+δ)-constant|≤ε := by
  have loss : Tendsto (fun s:ℝ=>Real.log s/s) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have lo : Tendsto (fun s:ℝ => Real.log s*(off (lowPrimes (high s))-C*(s/(high s:ℝ))-2/s))
      atTop (𝓝 constant) := by
    have lim := (high_limit.sub (lost_mass.const_mul C)).sub (loss.const_mul 2)
    apply (show Tendsto (fun s:ℝ=>Real.log s*off (lowPrimes (high s))-C*(Real.log s*(s/(high s:ℝ)))-2*(Real.log s/s))
      atTop (𝓝 constant) by simpa using lim).congr'
    filter_upwards with s
    ring
  have hi : Tendsto (fun s:ℝ => Real.log s*(off (lowPrimes (low s))+2/s)) atTop (𝓝 constant) := by
    have lim := low_limit.add (loss.const_mul 2)
    apply (show Tendsto (fun s:ℝ=>Real.log s*off (lowPrimes (low s))+2*(Real.log s/s)) atTop (𝓝 constant)
      by simpa using lim).congr'
    filter_upwards with s
    ring
  intro ε ep
  have eps : ∀ᶠ s:ℝ in atTop, ∀ᶠ N:ℕ in atTop,
      |Real.log s*cdf (B N) (R N) (2*C2+1/s)-constant|≤ε := by
    filter_upwards [tails,lo.eventually_const_lt (sub_lt_self _ ep),
      hi.eventually_lt_const (lt_add_of_pos_right _ ep),eventually_gt_atTop (1:ℝ)]
      with s t lower upper sp
    filter_upwards [t] with N b
    have pos := (Real.log_pos sp).le
    rw [abs_le]
    constructor
    · linarith only [lower,mul_le_mul_of_nonneg_left b.1 pos]
    · linarith only [upper,mul_le_mul_of_nonneg_left b.2 pos]
  obtain ⟨S,hS⟩:=eventually_atTop.mp eps
  let q:=max 1 S+1
  have qp:0<q := by dsimp [q];linarith [le_max_left (1:ℝ) S]
  refine ⟨1/q,by positivity,?_⟩
  intro δ dp dsmall
  have big : S ≤ 1/δ := by
    have lt : q < 1/δ := (lt_div_iff₀ dp).mpr (by
      have := (lt_div_iff₀ qp).mp dsmall
      linarith only [this])
    exact (show S≤q by dsimp [q];linarith [le_max_right (1:ℝ) S]).trans lt.le
  simpa only [one_div_one_div] using eventually_atTop.mp (hS (1/δ) big)

theorem conclusion {C:ℝ} (models : ModelTails C) :
    ∀ ε:ℝ, 0<ε → ∃ δ0:ℝ, 0<δ0 ∧ ∀ δ:ℝ, 0<δ → δ<δ0 → ∃ T:ℕ, ∀ N≥T,
      |Real.log (1/δ)*cdf (B N) (R N) (2*C2+δ)-constant|≤ε :=
  squeeze (from_models models)
end ReflectedLowerFinish
end

section
namespace ReflectedLowerTransfer
open Finset Filter MeanSquareGeometry
noncomputable section
open scoped Classical

private theorem filter_indicator {α : Type*} (B : Finset α) (p : α → Prop)
    [DecidablePred p] :
    ((B.filter p).card:ℝ) = ∑ m ∈ B, if p m then (1:ℝ) else 0 := by
  rw [←Finset.sum_filter]
  simp

theorem lower_compare {α : Type*} (B : Finset α) (R P : α → ℝ)
    (z η : ℝ) (hη : 0 < η) :
    ((B.filter (fun m => P m ≤ z-η)).card:ℝ)*η^2 ≤
      ((B.filter (fun m => R m ≤ z)).card:ℝ)*η^2 +
        ∑ m ∈ B, (R m-P m)^2 := by
  rw [filter_indicator,filter_indicator,sum_mul,sum_mul,←sum_add_distrib]
  apply sum_le_sum
  intro m hm
  by_cases hP : P m ≤ z-η
  · by_cases hR : R m ≤ z
    · simp [hP,hR,sq_nonneg]
    · simp only [hP,hR,ite_true,ite_false,one_mul,zero_mul,zero_add]
      nlinarith [sq_nonneg (R m-P m-η)]
  · by_cases hR : R m ≤ z <;> simp [hP,hR] <;> positivity

theorem upper_compare {α : Type*} (B : Finset α) (R P : α → ℝ)
    (z η : ℝ) (hη : 0 < η) :
    ((B.filter (fun m => R m ≤ z)).card:ℝ)*η^2 ≤
      ((B.filter (fun m => P m ≤ z+η)).card:ℝ)*η^2 +
        ∑ m ∈ B, (R m-P m)^2 := by
  rw [filter_indicator,filter_indicator,sum_mul,sum_mul,←sum_add_distrib]
  apply sum_le_sum
  intro m hm
  by_cases hR : R m ≤ z
  · by_cases hP : P m ≤ z+η
    · simp [hR,hP,sq_nonneg]
    · simp only [hR,hP,ite_true,ite_false,one_mul,zero_mul,zero_add]
      nlinarith [sq_nonneg (P m-R m-η)]
  · by_cases hP : P m ≤ z+η <;> simp [hR,hP] <;> positivity

private theorem periodic_upper {D : ℕ} (dp : 0 < D) (f : ℕ → ℝ)
    (K : ℕ) (e : ℝ) (ep : 0 ≤ e)
    (full : ∀ u : ℕ, (∑ t ∈ range D, f (u+t)) = (D:ℝ)*e)
    (small : ∀ k, f k ≤ 1) :
    (∑ t ∈ range K, f t) ≤ (K:ℝ)*e + D := by
  have blocks (v : ℕ) : (∑ t ∈ range (D*v), f t) ≤ ((D*v:ℕ):ℝ)*e := by
    induction v with
    | zero => simp
    | succ n ih =>
      rw [Nat.mul_succ,sum_range_add,Nat.cast_add,add_mul]
      exact add_le_add ih (full _).le
  have h := Nat.div_add_mod K D
  have part := Finset.sum_range_add f (D*(K/D)) (K % D)
  rw [Nat.div_add_mod] at part
  rw [part]
  have rest : (∑ i ∈ range (K % D), f (D*(K/D)+i)) ≤ (K % D:ℕ) := by
    apply (sum_le_sum (fun i _ => small _)).trans
    simp
  have ltK : D*(K/D) ≤ K := by omega
  have rem : (K % D:ℕ) ≤ D := (Nat.mod_lt _ dp).le
  exact (add_le_add (blocks _) rest).trans
    (add_le_add (mul_le_mul_of_nonneg_right (by exact_mod_cast ltK) ep)
      (by exact_mod_cast rem))

private theorem periodic_lower {D : ℕ} (dp : 0 < D) (f : ℕ → ℝ)
    (K : ℕ) (e : ℝ) (ee : e ≤ 1)
    (full : ∀ u : ℕ, (∑ t ∈ range D, f (u+t)) = (D:ℝ)*e)
    (nonneg : ∀ k, 0 ≤ f k) :
    (K:ℝ)*e - D ≤ ∑ t ∈ range K, f t := by
  have fullComp (u : ℕ) : (∑ t ∈ range D, (1-f (u+t))) =
      (D:ℝ)*(1-e) := by
    rw [sum_sub_distrib]
    simp only [sum_const, card_range, nsmul_eq_mul, mul_one]
    rw [full u]
    ring
  have upper := periodic_upper dp (fun t => 1-f t) K (1-e) (by linarith)
    fullComp (fun k => by linarith [nonneg k])
  simp only [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul, mul_one] at upper
  linarith

private theorem periodic_error {D : ℕ} (dp : 0 < D) (f : ℕ → ℝ)
    (K : ℕ) (e : ℝ) (ep : 0 ≤ e) (ee : e ≤ 1)
    (full : ∀ u : ℕ, (∑ t ∈ range D, f (u+t)) = (D:ℝ)*e)
    (bounds : ∀ k, 0 ≤ f k ∧ f k ≤ 1) :
    |(∑ t ∈ range K, f t) - (K:ℝ)*e| ≤ D := by
  apply abs_le.mpr
  constructor
  · have lower := periodic_lower dp f K e ee full (fun k => (bounds k).1)
    linarith
  · have upper := periodic_upper dp f K e ep full (fun k => (bounds k).2)
    linarith

def wheelCDF (y : ℕ) (z : ℝ) : ℝ :=
  (∑ r ∈ range (MeanSquareRows.W y),
    if ReflectedModelWindow.value y r ≤ z then (1:ℝ) else 0) /
      (MeanSquareRows.W y:ℝ)

private theorem wheelCDF_nonneg (y : ℕ) (z : ℝ) : 0 ≤ wheelCDF y z := by
  unfold wheelCDF
  exact div_nonneg (sum_nonneg fun _ _ => by split <;> norm_num)
    (Nat.cast_nonneg _)

private theorem wheelCDF_le_one (y : ℕ) (z : ℝ) : wheelCDF y z ≤ 1 := by
  unfold wheelCDF
  have hp : (0:ℝ) < MeanSquareRows.W y := by
    exact_mod_cast MeanSquareRows.wpos y
  apply (div_le_iff₀ hp).mpr
  convert sum_le_sum (s:=range (MeanSquareRows.W y))
    (fun r _ => show (if ReflectedModelWindow.value y r ≤ z then (1:ℝ) else 0) ≤ 1 by
      split <;> norm_num) using 1
  simp

private theorem model_period (y b : ℕ) (z : ℝ) (u : ℕ) :
    (∑ t ∈ range (MeanSquareRows.W y),
      if ReflectedModelWindow.value y (b+2*(u+t)) ≤ z then (1:ℝ) else 0) =
        (MeanSquareRows.W y:ℝ)*wheelCDF y z := by
  have harg (t : ℕ) : b+2*(u+t) = (b+2*u)+2*t := by ring
  simp_rw [harg]
  have heq (t : ℕ) :
      (if ReflectedModelWindow.value y ((b+2*u)+2*t) ≤ z then (1:ℝ) else 0) =
        (if ReflectedModelWindow.value y (((b+2*u)+2*t) % MeanSquareRows.W y) ≤ z
          then (1:ℝ) else 0) := by
    rw [ReflectedModelWindow.residue]
  simp_rw [heq]
  rw [ReflectedModelWindow.uniform_period (MeanSquareRows.wpos y)
    (b+2*u) (MeanSquareRows.wOdd y).coprime_two_left
    (fun r : ℕ => if ReflectedModelWindow.value y r ≤ z then (1:ℝ) else 0)]
  unfold wheelCDF
  have hne : (MeanSquareRows.W y:ℝ) ≠ 0 := by
    exact_mod_cast (MeanSquareRows.wpos y).ne'
  field_simp

theorem model_band_error (y N : ℕ) (hn : 100 ≤ N) (z : ℝ) :
    |(((B N).filter (fun m => MeanSquareEnergy.model y m ≤ z)).card:ℝ) -
      ((B N).card:ℝ)*wheelCDF y z| ≤ MeanSquareRows.W y := by
  obtain ⟨b,eb,image,kp,size⟩ := MeanSquareGeometry.geometry hn
  let K := (B N).card
  let f (t : ℕ) : ℝ :=
    if ReflectedModelWindow.value y (b+2*t) ≤ z then 1 else 0
  have bounds (t : ℕ) : 0 ≤ f t ∧ f t ≤ 1 := by
    dsimp only [f]
    split <;> norm_num
  have full (u : ℕ) : (∑ t ∈ range (MeanSquareRows.W y), f (u+t)) =
      (MeanSquareRows.W y:ℝ)*wheelCDF y z := by
    simpa only [f] using model_period y b z u
  have estimate := periodic_error (MeanSquareRows.wpos y) f K (wheelCDF y z)
    (wheelCDF_nonneg y z) (wheelCDF_le_one y z) full bounds
  have introF (m : ℕ) (hm : m ∈ B N) : m ≠ 0 := by
    have h := (mem_Icc.mp (mem_filter.mp hm).1).1
    omega
  have count_eq :
      (((B N).filter (fun m => MeanSquareEnergy.model y m ≤ z)).card:ℝ) =
        ∑ t ∈ range K, f t := by
    calc
      _ = ∑ m ∈ B N, if MeanSquareEnergy.model y m ≤ z then (1:ℝ) else 0 :=
        filter_indicator (B N) _
      _ = ∑ m ∈ B N, if ReflectedModelWindow.value y m ≤ z then (1:ℝ) else 0 := by
        apply sum_congr rfl
        intro m hm
        rw [ReflectedModelWindow.positive_value y m (introF m hm)]
      _ = ∑ t ∈ range K, f t := by
        conv_lhs => rw [image]
        apply sum_image
        intro i _ j _ eq
        change b+2*i=b+2*j at eq
        omega
  rw [count_eq]
  exact estimate

theorem wheelCDF_eq_site (y : ℕ) (z : ℝ) :
    wheelCDF y z =
      ∑ S : Finset (↥(MeanSquareEulerBounds.lowPrimes y)),
        ReflectedBlockLaw.siteMass (MeanSquareEulerBounds.lowPrimes y) S *
          (if 2*ReflectedModelGain.C2*
            ReflectedModelGain.site (MeanSquareEulerBounds.lowPrimes y) S ≤ z
            then (1:ℝ) else 0) := by
  let T := MeanSquareEulerBounds.lowPrimes y
  have pr : ∀ p ∈ T, p.Prime := by
    intro p hp
    exact (mem_filter.mp hp).2.1
  let f (S : Finset T) : ℝ :=
    if 2*ReflectedModelGain.C2*ReflectedModelGain.site T S ≤ z then 1 else 0
  have law := ReflectedModelCRT.residue_law T pr f
  have hW : MeanSquareRows.W y = ∏ p ∈ T, p := by
    simpa only [T] using ReflectedModelLaw.wheel_eq y
  have hsum :
      (∑ r ∈ range (MeanSquareRows.W y),
        if ReflectedModelWindow.value y r ≤ z then (1:ℝ) else 0) =
          (MeanSquareRows.W y:ℝ) *
            ∑ S : Finset T, ReflectedBlockLaw.siteMass T S * f S := by
    rw [hW]
    simpa only [f, T, ReflectedModelLaw.all_values] using law
  unfold wheelCDF
  rw [hsum]
  have hne : (MeanSquareRows.W y:ℝ) ≠ 0 := by
    exact_mod_cast (MeanSquareRows.wpos y).ne'
  field_simp
  rfl

end
end ReflectedLowerTransfer
end

section
open Filter Finset
open scoped Topology
noncomputable section
namespace LowerOrthAssembly
open MeanSquareGeometry MeanSquareRows MeanSquareEnergy ReflectedModelGain
open ReflectedLowerTransfer ReflectedLowerFinish ReflectedLowerScales
open ReflectedPrimeBlocks MeanSquareEulerBounds

private theorem wheel_period (y : ℕ) (a : ℝ) :
    wheelCDF y (2*C2+a) = ReflectedLowerModel.periodHits y a/(W y:ℝ) := rfl

private theorem close_in_band (y : ℕ) (η : ℝ) (ep : 0<η) :
    ∀ᶠ N : ℕ in atTop, ∀ z:ℝ, |cdf (B N) (MeanSquareEnergy.model y) z-wheelCDF y z|≤η := by
  have lim : ∀ᶠ N : ℕ in atTop, 24*(W y:ℝ)≤N*η := by
    filter_upwards [tendsto_natCast_atTop_atTop (R:=ℝ) |>.eventually_ge_atTop (24*(W y:ℝ)/η)] with N large
    exact (div_le_iff₀ ep).mp large
  filter_upwards [eventually_ge_atTop (100:ℕ),lim] with N big large
  obtain ⟨_,_,_,kp,size⟩:=MeanSquareGeometry.geometry big
  have kpos : (0:ℝ)<(B N).card := by exact_mod_cast kp
  have nsize : (N:ℝ)≤24*((B N).card:ℝ) := by exact_mod_cast size
  have cap : (W y:ℝ)≤η*((B N).card:ℝ) := by
    linarith only [large,mul_le_mul_of_nonneg_right nsize ep.le]
  intro z
  have err := model_band_error y N big z
  have diff (r w k : ℝ) (h : k≠0) : r/k-w = (r-k*w)/k := by field_simp
  unfold cdf
  rw [show (((B N).filter (fun m => MeanSquareEnergy.model y m≤z)).card:ℝ)/(B N).card-wheelCDF y z =
      ((((B N).filter (fun m => MeanSquareEnergy.model y m≤z)).card:ℝ) - (B N).card*wheelCDF y z)/(B N).card
      by exact diff _ _ _ kpos.ne',abs_div, abs_of_pos kpos]
  exact (div_le_iff₀ kpos).mpr (err.trans cap)

theorem models : ReflectedLowerFinish.ModelTails (8*ReflectedModelGain.C2) := by
  filter_upwards [ReflectedLowerThresholds.uniform] with s bounds
  intro η ep
  refine ⟨high s,?_⟩
  intro y hy
  have ll := (bounds y hy).1
  have uu := (bounds y hy).2
  have pos : (0:ℝ) < W y := by exact_mod_cast wpos y
  let l := off (lowPrimes (high s)) - 8*C2*(s/(high s:ℝ))
  let u := off (lowPrimes (low s))
  have left : l ≤ wheelCDF y (2*C2+1/(2*s)) := by
    rw [wheel_period]
    exact (le_div_iff₀ pos).mpr (by simpa only [l,mul_comm (W y:ℝ)] using ll)
  have right : wheelCDF y (2*C2+2/s) ≤ u := by
    rw [wheel_period]
    exact (div_le_iff₀ pos).mpr (by simpa only [u,mul_comm (W y:ℝ)] using uu)
  filter_upwards [close_in_band y η ep] with N near
  have lbd := (abs_le.mp (near (2*C2+1/(2*s)))).1
  have ubd := (abs_le.mp (near (2*C2+2/s))).2
  change l-η≤_ ∧ _≤u+η
  exact ⟨by linarith only [left,lbd],by linarith only [right,ubd]⟩
end LowerOrthAssembly
end

section
open Finset Filter Conjectures.Goldbach.EstermannAlmostAllPolylog_aux in
theorem Conjectures.Goldbach.ReflectedLowerTailDensity : (by
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
  exact ∀ ε : ℝ, 0 < ε → ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∃ T : ℕ, ∀ N : ℕ, T ≤ N →
    let P := (((B N).filter (fun m => R N m ≤ 2*C₂+δ)).card:ℝ)/((B N).card:ℝ)
    |Real.log (1/δ)*P - 2*Real.exp (-Real.eulerMascheroniConstant)| ≤ ε) := by
  have models : ReflectedLowerFinish.ModelTails (8*ReflectedModelGain.C2) := LowerOrthAssembly.models
  classical
  dsimp only
  simpa only [MeanSquareGeometry.B,MeanSquareConclusion.R,ReflectedLowerFinish.cdf,
    ReflectedMertens.constant,ReflectedModelGain.C2,ProgressionScales.cutoff,GoldbachBa08Approx.coefficient,
    GoldbachBa08Approx.arcs,GoldbachBlockGeometry.width,GoldbachBa08Approx.primeSum_eq,GoldbachMajorArc.phase]
    using ReflectedLowerFinish.conclusion models
end
