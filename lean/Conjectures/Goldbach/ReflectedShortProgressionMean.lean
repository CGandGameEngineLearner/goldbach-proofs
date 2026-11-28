import Mathlib
import Conjectures.Cuts.Taskba08eb3c3998330911d98843

/- The uniform major-arc transfer and the arithmetic row definitions below are from Goldbach PR #4275. -/

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

private theorem prime_dvd_residue {p d a b:ℕ} (pd:p∣d) (hb:b%d=a) : p∣b ↔ p∣a := by
  rw [←hb,Nat.dvd_iff_mod_eq_zero,Nat.dvd_iff_mod_eq_zero,Nat.mod_mod_of_dvd _ pd]

def localRatio (p a:ℕ) : ℝ :=
  (if p∣a then 1+1/((p:ℝ)-2) else 1)/(1+1/((p:ℝ)*((p:ℝ)-2)))

private theorem ratio_eq {p d a b:ℕ} (gt:2<p) (pd:p∣d) (hb:b%d=a) :
    1+localCoefficient p b=localRatio p a := by
  have eq:=prime_dvd_residue pd hb
  have rp:2<(p:ℝ):=by exact_mod_cast gt
  have p0:(p:ℝ)≠0:=by linarith
  have p1:(p:ℝ)-1≠0:=by linarith
  have p2:(p:ℝ)-2≠0:=by linarith
  have D:0<(p:ℝ)*(p-2)+1:=by positivity
  by_cases h:p∣a <;>simp only [localCoefficient,localRatio,eq,h,ite_true,ite_false] <;> field_simp <;> ring

theorem fixed_sum {d a b:ℕ} (hd:Odd d) (hb:Even b) (res:b%d=a) :
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

theorem coefficient_residue {q d a b c:ℕ} (qd:q∣2*d) (bb:Even b) (cc:Even c) (br:b%d=a) (cr:c%d=a) :
    coefficient q b=coefficient q c := by
  apply coeff_eq;intro p pr pq
  rcases pr.dvd_mul.mp (pq.trans qd) with two|pd
  · have eq:p=2:=((Nat.dvd_prime Nat.prime_two).mp two).resolve_left pr.ne_one
    subst p;exact iff_of_true (even_iff_two_dvd.mp bb) (even_iff_two_dvd.mp cc)
  · exact (prime_dvd_residue pd br).trans (prime_dvd_residue pd cr).symm

end
end ProgressionLocal

open Finset
namespace ProgressionWindow

def window (d a x H:ℕ) := (Icc x (x+H)).filter (fun m=>Even m ∧ m%d=a)

private theorem next_residue {P r:ℕ} (pp:0<P) (rp:r<P) (x:ℕ) :
    ∃b:ℕ, x≤b ∧ b<x+P ∧ b%P=r := by
  let u:=P*(x/P)+r
  have ua : u%P=r :=by simp [u,Nat.add_mod,Nat.mod_eq_of_lt rp]
  have xm:=Nat.div_add_mod x P
  have rem:=Nat.mod_lt x pp
  by_cases good:x≤u
  · exact ⟨u,good,by dsimp [u];omega,ua⟩
  · exact ⟨u+P,by dsimp [u];omega,by omega,by simpa using ua⟩

private theorem one_class {P r b x H:ℕ} (pp:0<P) (xl:x≤b) (bx:b<x+P) (br:b%P=r) :
    let T := (Icc x (x+H)).filter (fun m=>m%P=r)
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
    ∃ b:ℕ, x≤b ∧ b<x+2*d ∧ Even b ∧ b%d=a ∧
      H≤2*d*((window d a x H).card+1) ∧
      window d a x H=(range (window d a x H).card).image (fun t=>b+2*d*t) := by
  let r:=if Even a then a else a+d
  have dp:0<d:=by omega
  have Pp:0<2*d:=by omega
  have rp:r<2*d:=by dsimp [r];split <;> omega
  have ra:r%d=a:=by dsimp [r];split <;> simp [Nat.mod_eq_of_lt ad]
  have ev:Even r:=by
    dsimp [r];split
    · assumption
    · rename_i h;exact (Nat.not_even_iff_odd.mp h).add_odd od
  have equiv (m:ℕ): Even m ∧ m%d=a ↔ m%(2*d)=r := by
    have er := (even_iff_two_dvd.mp ev).modEq_zero_nat
    constructor
    · rintro ⟨em,md⟩
      have m2: m≡r [MOD 2] := (even_iff_two_dvd.mp em).modEq_zero_nat.trans er.symm
      have md':m≡r [MOD d]:=md.trans ra.symm
      have all := Nat.mod_lcm m2 md'
      rw [od.coprime_two_left.lcm_eq_mul] at all
      exact (show m%(2*d)=r%(2*d) from all).trans (Nat.mod_eq_of_lt rp)
    · intro mr
      have all:m≡r [MOD 2*d]:=mr.trans (Nat.mod_eq_of_lt rp).symm
      have m2:=all.of_dvd (dvd_mul_right 2 d)
      have md:=all.of_dvd (dvd_mul_left d 2)
      exact ⟨even_iff_two_dvd.mpr (Nat.modEq_zero_iff_dvd.mp (m2.trans er)),(show m%d=r%d from md).trans ra⟩
  obtain ⟨b,xl,bx,br⟩:=next_residue Pp rp x
  have shape:window d a x H=(Icc x (x+H)).filter (fun m=>m%(2*d)=r) :=by
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

private theorem incomplete {q K : ℕ} (qp : 0 < q) (g : ℕ → ℝ)
    (zero : ∀ v, (∑ t ∈ range q, g (v+t)) = 0)
    (bd : ∀ t, |g t| ≤ 1) : |∑ t ∈ range K, g t| ≤ (q:ℝ) := by
  have full (k : ℕ) : (∑ t ∈ range (q*k), g t) = 0 := by
    induction k with
    | zero => simp
    | succ k ih => rw [Nat.mul_succ, sum_range_add, ih, zero, add_zero]
  have eq := Finset.sum_range_add g (q*(K/q)) (K%q)
  rw [Nat.div_add_mod, full, zero_add] at eq
  rw [eq]
  refine (abs_sum_le_sum_abs ..).trans ?_
  calc
    _ ≤ ∑ _t ∈ range (K%q), (1:ℝ) := sum_le_sum (fun t _ => bd _)
    _ ≤ (q:ℝ) := by simpa using (show (K%q:ℕ) ≤ q from (Nat.mod_lt K qp).le)

theorem residue_error (B D b K : ℕ) (dp : 0 < D) (inc : D ≤ B) (E : ℝ)
    (localSum : ∀ t, (∑ q ∈ D.divisors, (coefficient q (b+D*t)).re) = E)
    (vanish : ∀ q > 0, ¬ q ∣ D → ∀ v : ℕ,
       (∑ t ∈ range q, (coefficient q (v+D*t)).re) = 0) :
    |(∑ t ∈ range K, SharpAssembly.row B (b+D*t)) - K*E| ≤ (B:ℝ)^2 := by
  let A := Icc 1 B
  let c (q t : ℕ) := (coefficient q (b+D*t)).re
  have eq : A.filter (fun q => q ∣ D) = D.divisors := by
    ext q
    simp only [A, mem_filter, mem_Icc, Nat.mem_divisors]
    exact ⟨fun h => ⟨h.2, dp.ne'⟩, fun h => ⟨⟨Nat.pos_of_dvd_of_pos h.1 dp,(Nat.le_of_dvd dp h.1).trans inc⟩,h.1⟩⟩
  have split (t : ℕ) : SharpAssembly.row B (b+D*t) - E =
      ∑ q ∈ A, if q ∣ D then 0 else c q t := by
    have fixed : (∑ q ∈ A, if q ∣ D then c q t else 0) = E := by
      rw [← Finset.sum_filter, eq]; exact localSum t
    rw [←fixed, SharpAssembly.row, ←Finset.sum_sub_distrib]
    apply sum_congr rfl
    intro q _
    by_cases h : q ∣ D <;> simp [h,c]
  have both : (∑ t ∈ range K, SharpAssembly.row B (b+D*t))-K*E =
      ∑ q ∈ A, ∑ t ∈ range K, if q ∣ D then 0 else c q t := by
    calc
      _ = ∑ t ∈ range K, (SharpAssembly.row B (b+D*t)-E) := by rw [sum_sub_distrib];simp
      _ = _ := by simp_rw [split]; rw [sum_comm]
  rw [both]
  refine (abs_sum_le_sum_abs ..).trans ?_
  calc
    _ ≤ ∑ _q ∈ A,(B:ℝ) := by
      apply sum_le_sum
      intro q hq
      obtain ⟨qp,qB⟩ := mem_Icc.mp hq
      by_cases h : q ∣ D
      · simp [h]
      · simp only [h, ite_false]
        refine (incomplete (K:=K) qp (c q) ?_ ?_).trans (by exact_mod_cast qB)
        · intro v
          simpa only [c, Nat.mul_add, ← Nat.add_assoc] using vanish q qp h (b+D*v)
        · intro t
          exact (Complex.abs_re_le_norm _).trans (coefficient_norm _ _ qp)
    _ = _ := by simp [A, Nat.card_Icc, pow_two]

end
end ProgressionSums

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

namespace ProgressionConclusion
open Finset Filter Conjectures.Goldbach.EstermannAlmostAllPolylog_aux
open scoped Classical BigOperators
noncomputable section

def R (N m : ℕ) : ℝ :=
  let B := ProgressionScales.cutoff N
  (GoldbachBa08Approx.coefficient N m B (B^3)).re/(2*(N:ℝ)-(m:ℝ))

def E (d a : ℕ) : ℝ := 2 * ∏ p ∈ d.primeFactors,
    ((if p ∣ a then 1+1/((p:ℝ)-2) else 1)/(1+1/((p:ℝ)*((p:ℝ)-2))))

def F (N d a x H : ℕ) := (((Icc N (2*N)).filter (SharpAssembly.band N)) ∩ Icc x (x+H)).filter
    (fun m => m%d=a)

theorem F_window {N d a x H : ℕ} (lo : 4*N≤3*x) (hi : 2*(x+H)≤3*N) :
    F N d a x H = ProgressionWindow.window d a x H := by
  ext m
  simp only [F, ProgressionWindow.window, mem_filter, mem_inter, mem_Icc, SharpAssembly.band]
  constructor
  · rintro ⟨⟨⟨_,_,_,ev⟩,seq⟩,res⟩
    exact ⟨seq,ev,res⟩
  · rintro ⟨⟨a1,a2⟩,ev,res⟩
    exact ⟨⟨⟨⟨by omega,by omega⟩,by omega,by omega,ev⟩,a1,a2⟩,res⟩

theorem mean
    (orth : ∀ D q : ℕ, 0 < q → ¬ q ∣ D → ∀ v : ℕ,
       (∑ t ∈ range q, (GoldbachMajorArc.coefficient q (v+D*t)).re) = 0)
    (transfer : ∀ e : ℝ, 0 < e → ∀ᶠ N : ℕ in atTop, ∀ m,
      4*N≤3*m → 2*m≤3*N → |R N m - SharpAssembly.row (ProgressionScales.cutoff N) m| ≤ e) :
    ∀ d a : ℕ, Odd d → a < d → ∀ θ : ℝ, 0 < θ → θ < 1 → ∀ ε : ℝ, 0 < ε →
    ∃ T : ℕ, ∀ N x H : ℕ, T ≤ N → 4*N ≤ 3*x → 2*(x+H) ≤ 3*N → (N:ℝ)^θ ≤ (H:ℝ) →
      |(∑ m ∈ F N d a x H, R N m)/((F N d a x H).card:ℝ) - E d a| ≤ ε := by
  intro d a od ad θ ht _ ε he
  let e := ε/3
  have ep : 0 < e := by dsimp [e]; positivity
  have dp : 0 < d := by omega
  obtain ⟨T,hT⟩ := eventually_atTop.mp ((ProgressionScales.scales d e θ ep ht).and (transfer e ep))
  refine ⟨T, ?_⟩
  intro N x H nT lo hi long
  obtain ⟨⟨inc,_,scale⟩,tr⟩ := hT N nT
  rw [F_window lo hi]
  let W := ProgressionWindow.window d a x H
  let K := W.card
  let L := ProgressionScales.cutoff N
  obtain ⟨b,bx,bt,be,ba,hH,im⟩ := ProgressionWindow.enumerate od ad x H
  obtain ⟨kpos,small⟩ := scale H K long hH
  have kp : (0:ℝ) < K := by exact_mod_cast kpos
  have fixed (t : ℕ) :
      (∑ q ∈ (2*d).divisors, (GoldbachMajorArc.coefficient q (b+2*d*t)).re) = E d a := by
    apply ProgressionLocal.fixed_sum od (be.add ((even_two.mul_right d).mul_right t))
    have v : b+2*d*t = b+d*(2*t) := by ring
    rw [v, Nat.add_mul_mod_self_left, ba]
  have rerr := ProgressionSums.residue_error L (2*d) b K (by omega) inc (E d a) fixed (orth (2*d))
  have sw := ProgressionWindow.sum_of_image dp im (SharpAssembly.row L)
  change (∑ m ∈ W, SharpAssembly.row L m) = _ at sw
  rw [←sw] at rerr
  let sr := ∑ m ∈ W, R N m
  let sc := ∑ m ∈ W, SharpAssembly.row L m
  have e1 : |sr - sc| ≤ K*e := by
    dsimp only [sr,sc]
    rw [←sum_sub_distrib]
    refine (abs_sum_le_sum_abs ..).trans ?_
    calc
      _ ≤ ∑ _m ∈ W, e := by
        apply sum_le_sum
        intro m hm
        have hw : m ∈ ProgressionWindow.window d a x H := hm
        have lr := mem_Icc.mp (mem_filter.mp hw).1
        apply tr <;> omega
      _ = _ := by simp [K, nsmul_eq_mul]
  have e2 : |sc-(K:ℝ)*E d a| ≤ e*K := rerr.trans small
  have join := (abs_sub_le sr sc ((K:ℝ)*E d a)).trans (add_le_add e1 e2)
  change |sr/(K:ℝ)-E d a| ≤ ε
  rw [show sr/(K:ℝ)-E d a = (sr-K*E d a)/K by field_simp, abs_div, abs_of_pos kp]
  apply (div_le_iff₀ kp).mpr
  refine join.trans ?_
  dsimp [e]
  nlinarith only [mul_nonneg he.le kp.le]

end
end ProgressionConclusion

open Filter Finset Conjectures.Goldbach.EstermannAlmostAllPolylog_aux in
theorem Conjectures.Goldbach.ReflectedShortProgressionMean : (by
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
  exact ∀ d a : ℕ, Odd d → a < d → ∀ θ : ℝ, 0 < θ → θ < 1 → ∀ ε : ℝ, 0 < ε → ∃ T : ℕ, ∀ N x H : ℕ, T ≤ N → 4*N ≤ 3*x → 2*(x+H) ≤ 3*N → (N:ℝ)^θ ≤ (H:ℝ) →
    let F := ((B N) ∩ Finset.Icc x (x+H)).filter (fun m => m%d=a)
    let E := 2 * ∏ p ∈ d.primeFactors, ((if p ∣ a then 1+1/((p:ℝ)-2) else 1)/(1+1/((p:ℝ)*((p:ℝ)-2))))
    |avg F (R N) - E| ≤ ε) := by
  classical
  have vanish : ∀ D q : ℕ, 0 < q → ¬q∣D → ∀ v : ℕ,
      (∑ t ∈ range q,(GoldbachMajorArc.coefficient q (v+D*t)).re)=0 := by
    intro D q qp h v
    simpa only [Complex.re_sum, Complex.zero_re] using
      congrArg Complex.re (ProgressionZero.coefficient_sum_zero q v D qp h)
  have tr : ∀ e:ℝ, 0<e → ∀ᶠ N:ℕ in atTop, ∀ m,
      4*N≤3*m → 2*m≤3*N → |ProgressionConclusion.R N m - SharpAssembly.row (ProgressionScales.cutoff N) m| ≤ e := by
    intro e ep
    filter_upwards [ProgressionTransfer.normalized e ep] with N hN
    intro m l h
    have mu : m≤2*N := by omega
    simpa only [ProgressionConclusion.R, ProgressionScales.cutoff, Nat.cast_sub mu, Nat.cast_mul, Nat.cast_ofNat]
      using hN m l h
  have eqF (N d a x H : ℕ) : ProgressionConclusion.F N d a x H =
      (((Icc N (2*N)).filter (fun m => 4*N≤3*m ∧ 2*m≤3*N ∧ Even m)) ∩ Icc x (x+H)).filter
        (fun m => m%d=a) := by
    ext m
    simp only [ProgressionConclusion.F, mem_filter, mem_inter, SharpAssembly.band]
  dsimp only
  simpa only [eqF, ProgressionConclusion.R, ProgressionConclusion.E,
    ProgressionScales.cutoff, GoldbachBa08Approx.coefficient, GoldbachBa08Approx.arcs,
    GoldbachBlockGeometry.width, GoldbachBa08Approx.primeSum_eq, GoldbachMajorArc.phase]
    using ProgressionConclusion.mean vanish tr
