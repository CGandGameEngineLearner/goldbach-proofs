import Mathlib
import Conjectures.Goldbach.ExceptionFourSeventhsCountingBridge
import Conjectures.Goldbach.EstermannAlmostAllPolylog

/- The centered kernel reflection follows the Apache-2.0 proof of DFQDZZ (goldbach-proofs PR 316), as reused by EstermannAlmostAllPolylog. -/

open Finset Filter MeasureTheory
open scoped Classical
noncomputable section
namespace OddMinorFull
open Conjectures.Goldbach.EstermannAlmostAllPolylog_aux
open GoldbachMajorArc

def cutoff (n:ℕ) := Polylog.cutoff 2 n
def f (n:ℕ) (t:ℝ) := primeSum n t ^ 2 * phase (-(n:ℝ)*t)
def major (n:ℕ) := GoldbachBlockGeometry.majorContribution (cutoff n) n (f n)
def minor (n:ℕ) : ℝ := (∫t in (0:ℝ)..1, (GoldbachBlockGeometry.arcs (cutoff n) n)ᶜ.indicator (f n) t).re

theorem split (n:ℕ) :
    (major n).re + minor n = ∑k∈range (n+1),primeWeight k*primeWeight (n-k) := by
  exact congrArg Complex.re (Conjectures.Goldbach.FourSevenths.Coefficient n)

theorem odd_convolution (n:ℕ) (hn:5≤n) (od:Odd n) :
    (major n).re+minor n = 2*primeWeight 2*primeWeight (n-2) := by
  rw [split]
  let J:=range (n+1)
  let B:Finset ℕ:={2,n-2}
  have sub:B⊆J := by
    intro k hk
    simp only [B,mem_insert,mem_singleton] at hk
    exact mem_range.mpr (by omega)
  have zero (k:ℕ) (hk:k∈J) (nb:k∉B) : primeWeight k * primeWeight (n-k)=0 := by
    by_cases p:k.Prime
    · by_cases q:(n-k).Prime
      · have two : k=2 ∨ n-k=2 := by
          rcases p.eq_two_or_odd with h|h
          · exact Or.inl h
          rcases q.eq_two_or_odd with h'|h'
          · exact Or.inr h'
          have kn:=mem_range.mp hk
          obtain ⟨c,hc⟩:=od
          omega
        exfalso
        apply nb
        simp only [B,mem_insert,mem_singleton]
        omega
      · simp [primeWeight,q]
    · simp [primeWeight,p]
  calc
    _ = ∑k∈B,primeWeight k*primeWeight (n-k) := (sum_subset sub zero).symm
    _ = _ := by
      simp only [B,sum_insert (by simp;omega : 2∉({n-2}:Finset ℕ)),sum_singleton,show n-(n-2)=2 by omega]
      ring

theorem odd_upper (n:ℕ) (hn:5≤n) (od:Odd n) :
    (major n).re + minor n ≤ 2*Real.log 2*Real.log n := by
  rw [odd_convolution n hn od]
  have cap : primeWeight (n-2) ≤ Real.log n := by
    by_cases p:(n-2).Prime
    · simp only [primeWeight,ite_eq_left p]
      exact Real.log_le_log (by exact_mod_cast p.pos) (by exact_mod_cast Nat.sub_le n 2)
    · simp only [primeWeight,ite_eq_right p]
      exact Real.log_nonneg (by exact_mod_cast (show 1≤n by omega))
  simpa [primeWeight,Nat.prime_two] using mul_le_mul_of_nonneg_left cap (by positivity : 0≤2*Real.log 2)

def base (k:ℕ) : ℕ := 2^k
def point (k i:ℕ) := 4*base k+2*i+1
theorem base_pos (k:ℕ) : 0<base k := by unfold base;positivity
theorem point_props {k i:ℕ} (hi:i<base k) : Odd (point k i) ∧
    4*base k≤point k i ∧ point k i≤6*base k ∧ cutoff (point k i)=(k+2)^2 := by
  have bp:=base_pos k
  have pos:0<point k i+2 := by unfold point;omega
  have l : 2^(k+2)≤point k i+2 := by simp [pow_add,point,base];omega
  have u : point k i+2<2^(k+2+1) := by
    have h: i<2^k := hi
    simp only [point,base,pow_add]
    norm_num
    omega
  refine ⟨⟨2*base k+i,by unfold point;omega⟩,by unfold point;omega,by unfold point;omega,?_⟩
  have hlog : Nat.log 2 (point k i+2)=k+2 := Nat.log_eq_of_pow_le_of_lt_pow l u
  simp [cutoff,Polylog.cutoff,hlog]

theorem residual_square_subsum (k:ℕ) :
    (∑i∈range (base k),(minor (point k i))^2) ≤
      ∑n∈Icc (4*base k) (2*(4*base k)),(minor n)^2 := by
  let P:Finset ℕ := (range (base k)).image (point k)
  have inj:Function.Injective (point k) := by intro i j h;unfold point at h;omega
  have sub:P⊆Icc (4*base k) (2*(4*base k)) := by
    intro n hn
    obtain ⟨i,hi,rfl⟩:=mem_image.mp hn
    have h:=point_props (mem_range.mp hi)
    exact mem_Icc.mpr ⟨h.2.1,by omega⟩
  calc
    _ = ∑n∈P,(minor n)^2 := (sum_image (f:=fun n=>(minor n)^2) (fun _ _ _ _ h=>inj h)).symm
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg sub (by intros;positivity)
end OddMinorFull

open MeasureTheory Finset
noncomputable section
namespace OddMinorKernel
open Conjectures.Goldbach.EstermannAlmostAllPolylog_aux
open GoldbachMajorArc

def density (x:ℝ) := Real.sinc (Real.pi*x)^2
def K (T:ℝ) := ∫ x in -T..T,density x

theorem cont_density : Continuous density := by
  exact (Real.continuous_sinc.comp (continuous_const.mul continuous_id)).pow _

theorem K_nonneg {T:ℝ} (h:0≤T) : 0≤K T := intervalIntegral.integral_nonneg (by linarith) (fun x _=>sq_nonneg _)

theorem K_le {T:ℝ} (h:0≤T) : K T≤2*T := by
  have up:=intervalIntegral.integral_mono_on (μ:=volume) (a:=-T) (b:=T) (f:=density) (g:=fun _=>(1:ℝ)) (by linarith)
    (cont_density.intervalIntegrable ..) (continuous_const.intervalIntegrable ..) (fun x _=>by
      dsimp [density]
      simpa using (sq_le_sq' (abs_le.mp (Real.abs_sinc_le_one _)).1 (abs_le.mp (Real.abs_sinc_le_one _)).2 :
        (Real.sinc (Real.pi*x))^2≤(1:ℝ)^2))
  simp only [intervalIntegral.integral_const,smul_eq_mul,mul_one] at up
  change (∫x in -T..T,density x) ≤ 2*T
  linarith only [up]

theorem wing_sine (Q:ℕ) :
    (∫x in (Q:ℝ)/2..(Q:ℝ), Real.sin (Real.pi*x)^2)=(Q:ℝ)/4 := by
  rw [intervalIntegral.integral_comp_mul_left (fun x:ℝ=>Real.sin x^2) Real.pi_ne_zero,smul_eq_mul,integral_sin_sq]
  have s:Real.sin (Real.pi*Q)=0 := by simpa [mul_comm] using Real.sin_nat_mul_pi Q
  have prod:Real.sin (Real.pi*((Q:ℝ)/2))*Real.cos (Real.pi*((Q:ℝ)/2))=0 := by
    have d:=Real.sin_two_mul (Real.pi*((Q:ℝ)/2))
    rw [show 2*(Real.pi*((Q:ℝ)/2))=Real.pi*Q by ring,s] at d
    linarith
  rw [prod,s]
  field_simp
  ring

theorem gap {Q:ℕ} (hq:0<Q) :
    1/(4*Real.pi^2*(Q:ℝ)) ≤ K Q - K ((Q:ℝ)/2) := by
  have qp:(0:ℝ)<Q:=by exact_mod_cast hq
  let H:=(Q:ℝ)/2
  have h:0≤H:=by dsimp [H];positivity
  have hQ:H≤Q:=by dsimp [H];linarith
  have e1:=intervalIntegral.integral_add_adjacent_intervals
    (cont_density.intervalIntegrable (μ:=volume) (-(Q:ℝ)) (-H)) (cont_density.intervalIntegrable (μ:=volume) (-H) H)
  have e2:=intervalIntegral.integral_add_adjacent_intervals
    (cont_density.intervalIntegrable (μ:=volume) (-(Q:ℝ)) H) (cont_density.intervalIntegrable (μ:=volume) H Q)
  have nn : 0≤∫x in -(Q:ℝ)..-H,density x := intervalIntegral.integral_nonneg (by linarith) (fun x _=>sq_nonneg _)
  have pos:0<(Real.pi*(Q:ℝ))^2:=by positivity
  have lower: (∫x in H..(Q:ℝ),Real.sin (Real.pi*x)^2) ≤ (Real.pi*(Q:ℝ))^2*∫x in H..(Q:ℝ),density x := by
    rw [←intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hQ (by exact ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).pow _).intervalIntegrable ..)
      ((continuous_const.mul cont_density).intervalIntegrable ..)
    intro x hx
    have xp:0<x:=(by dsimp [H];positivity : 0<H).trans_le hx.1
    have x0:Real.pi*x≠0:=by positivity
    change _ ≤ _*Real.sinc (Real.pi*x)^2
    rw [Real.sinc_of_ne_zero x0,div_pow]
    have m: (Real.pi*x)^2 ≤ (Real.pi*(Q:ℝ))^2:=by gcongr;exact hx.2
    calc
      _ = (Real.pi*x)^2*(Real.sin (Real.pi*x)^2/(Real.pi*x)^2) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right m (by positivity)
  change (∫x in (Q:ℝ)/2..(Q:ℝ),_)≤_ at lower
  rw [wing_sine] at lower
  have num: (1/(4*Real.pi^2*(Q:ℝ)))*((Real.pi*Q)^2)=(Q:ℝ)/4 := by field_simp
  have hmain:1/(4*Real.pi^2*(Q:ℝ)) ≤ ∫ x in H..(Q:ℝ),density x := by
    apply le_of_mul_le_mul_right (a:=((Real.pi*Q)^2)) _ pos
    rw [num,mul_comm (∫x in H..(Q:ℝ),density x)]
    exact lower
  unfold K
  change _≤(∫x in -(Q:ℝ)..(Q:ℝ),density x)-(∫x in -H..H,density x)
  linarith only [e1,e2,nn,hmain]

end OddMinorKernel

open Finset MeasureTheory
open Conjectures.Goldbach.EstermannAlmostAllPolylog_aux.GoldbachMajorArc
noncomputable section
namespace OddMinorKernel

theorem close_sinc (x:ℝ) : 1-|Real.sinc x|≤|x| := by
  by_cases h:|x|<1
  · have c:=Real.cos_le_sinc (h.trans (by linarith only [Real.pi_gt_three] : (1:ℝ)<Real.pi/2))
    have l:=Real.abs_cos_sub_cos_le 0 x
    simp only [Real.cos_zero,zero_sub,abs_neg] at l
    linarith only [c,le_abs_self (1-Real.cos x),l,le_abs_self (Real.sinc x)]
  · linarith only [le_of_not_gt h,abs_nonneg (Real.sinc x)]

private theorem phase_pow (h:ℝ) (k:ℕ) : phase h ^k=phase ((k:ℝ)*h) := by
  unfold phase
  rw [←Complex.exp_nat_mul]
  congr 1;push_cast;ring

private theorem chord (x:ℝ) : ‖phase x-1‖=2*|Real.sin (Real.pi*x)| := by
  unfold phase
  rw [mul_comm _ Complex.I,Complex.norm_exp_I_mul_ofReal_sub_one,Real.norm_eq_abs,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
  rw [show 2*Real.pi*x/2=Real.pi*x by ring]

def geom (n:ℕ) (h:ℝ) := ∑k∈range n,(phase h)^k

theorem geom_cap (n:ℕ) (h:ℝ) : ‖geom n h‖≤n := by
  apply (norm_sum_le ..).trans
  simp [norm_pow,show ‖phase h‖=1 from Complex.norm_exp_ofReal_mul_I _]

theorem geom_identity (n:ℕ) (h:ℝ) :
    ‖geom n h‖*|Real.sin (Real.pi*h)|=|Real.sin (Real.pi*((n:ℝ)*h))| := by
  have eq:=congrArg norm (geom_sum_mul (phase h) n)
  rw [norm_mul,phase_pow,chord,chord] at eq
  change ‖geom n h‖*(2*|Real.sin (Real.pi*h)|)=2*|Real.sin (Real.pi*((n:ℝ)*h))| at eq
  linarith only [eq]

theorem rescale {n:ℕ} (np:0<n) (x:ℝ) :
    ‖geom n (x/n)‖ * |Real.sinc (Real.pi*(x/n))| = (n:ℝ)*|Real.sinc (Real.pi*x)| := by
  have n0:(0:ℝ)<n:=by exact_mod_cast np
  by_cases zero:x=0
  · simp [geom,zero,phase]
  have hx:Real.pi*x≠0:=mul_ne_zero Real.pi_ne_zero zero
  have hn:Real.pi*(x/(n:ℝ))≠0:=mul_ne_zero Real.pi_ne_zero (div_ne_zero zero n0.ne')
  rw [Real.sinc_of_ne_zero hn,Real.sinc_of_ne_zero hx,abs_div,abs_div]
  rw [←mul_div_assoc (‖geom n (x/n)‖) _ _,geom_identity,show (n:ℝ)*(x/n)=x by field_simp,←mul_div_assoc Real.pi x (n:ℝ),
    abs_div,abs_of_pos n0]
  field_simp

theorem kernel_close {n:ℕ} (np:0<n) (x:ℝ) :
    |‖kernel n (x/n)‖-(n:ℝ)*(|Real.sinc (Real.pi*x)|)|≤1+Real.pi*|x| := by
  let h:=x/(n:ℝ)
  have n0:(0:ℝ)<n:=by exact_mod_cast np
  have eq:=rescale np x
  have cap:=geom_cap n h
  have fe:=Real.abs_sinc_le_one (Real.pi*h)
  have geom_low:0≤‖geom n h‖-(n:ℝ)*|Real.sinc (Real.pi*x)|:=by
    rw [←eq]
    exact sub_nonneg.mpr (by simpa only [mul_one] using mul_le_mul_of_nonneg_left fe (norm_nonneg (geom n h)))
  have loss:=mul_le_mul cap (close_sinc (Real.pi*h)) (by linarith only [fe]) n0.le
  have na:(n:ℝ)*|Real.pi*h|=Real.pi*|x| := by
    rw [abs_mul,abs_of_pos Real.pi_pos,show |h|=|x|/(n:ℝ) by simp [h,abs_div,abs_of_pos n0]]
    field_simp
  rw [na] at loss
  have err:|‖geom n h‖-(n:ℝ)*(|Real.sinc (Real.pi*x)|)|≤Real.pi*|x|:=by
    rw [abs_of_nonneg geom_low]
    change ‖geom n h‖*|Real.sinc (Real.pi*h)|=_ at eq
    linarith only [loss,eq]
  have k:kernel n h=geom n h+(phase h)^n:=by
    unfold kernel geom
    rw [sum_range_succ]
    simp only [phase_pow]
  have d:=abs_norm_sub_norm_le (kernel n h) (geom n h)
  rw [k,add_sub_cancel_left,norm_pow,show ‖phase h‖=1 from Complex.norm_exp_ofReal_mul_I _,one_pow] at d
  change |‖kernel n h‖ - ((n:ℝ)*|Real.sinc (Real.pi*x)|)| ≤ 1+Real.pi*|x|
  have tri:=abs_sub_le (‖kernel n h‖) (‖geom n h‖) ((n:ℝ)*|Real.sinc (Real.pi*x)|)
  rw [k] at tri
  rw [k]
  exact tri.trans (add_le_add d err)

end OddMinorKernel

open Finset MeasureTheory
open Conjectures.Goldbach.EstermannAlmostAllPolylog_aux.GoldbachMajorArc
noncomputable section
namespace OddMinorKernel

theorem kernel_cap (n:ℕ) (x:ℝ): ‖kernel n x‖≤(n:ℝ)+1 := by
  apply (norm_sum_le ..).trans
  simp only [show ∀t:ℝ,‖phase t‖=1 from fun _=>Complex.norm_exp_ofReal_mul_I _,sum_const,card_range,nsmul_eq_mul,mul_one,Nat.cast_add,Nat.cast_one,le_refl]

theorem square_close {n:ℕ} (np:0<n) {T x:ℝ} (hx:|x|≤T) :
    |‖kernel n (x/n)‖^2-(n:ℝ)^2*density x| ≤ (2*(n:ℝ)+1)*(1+Real.pi*T) := by
  let s:=|Real.sinc (Real.pi*x)|
  let k:=‖kernel n (x/n)‖
  have n0:=Nat.cast_nonneg (α:=ℝ) n
  have ss: 0 ≤ s:=abs_nonneg _
  have h1:k≤(n:ℝ)+1:=kernel_cap .. 
  have h2:(n:ℝ)*s≤n:=by simpa only [mul_one] using mul_le_mul_of_nonneg_left (Real.abs_sinc_le_one (Real.pi*x)) n0
  have h3:|k-(n:ℝ)*s|≤1+Real.pi*T:= (kernel_close np x).trans (by gcongr)
  have h4: k+(n:ℝ)*s≤2*(n:ℝ)+1:=by linarith only [h1,h2]
  have h5:0≤k+(n:ℝ)*s:=add_nonneg (norm_nonneg _) (mul_nonneg n0 ss)
  have e:(n:ℝ)^2*density x=((n:ℝ)*s)^2:=by dsimp only [s,density];rw [mul_pow,sq_abs]
  rw [e]
  change |k^2-_ ^2|≤_
  rw [sq_sub_sq,abs_mul,abs_of_nonneg h5]
  exact mul_le_mul h4 h3 (abs_nonneg _) (by positivity)

theorem mass_compare {n:ℕ} (np:0<n) {T:ℝ} (hT:0≤T) :
    |kernelMass n (T/(n:ℝ))-(n:ℝ)*K T| ≤ 6*T*(1+Real.pi*T) := by
  have n0:(0:ℝ)<n:=by exact_mod_cast np
  have n1:(1:ℝ)≤n:=by exact_mod_cast np
  have ord:-T≤T:=by linarith
  let u := fun x:ℝ=>‖kernel n (x/n)‖^2
  let v := fun x:ℝ=>(n:ℝ)^2*density x
  have cu: Continuous u := by unfold u kernel phase;fun_prop
  have cv: Continuous v := continuous_const.mul cont_density
  have est:=intervalIntegral.norm_integral_le_of_norm_le_const (a:=-T) (b:=T)
    (f:=fun x=>u x-v x) (C:=(2*(n:ℝ)+1)*(1+Real.pi*T)) (fun x hx=>by
      rw [Set.uIoc_of_le ord] at hx
      rw [Real.norm_eq_abs]
      exact square_close np (abs_le.mpr ⟨hx.1.le,hx.2⟩))
  have utrans:(∫x in -T..T,u x)=(n:ℝ)*kernelMass n (T/(n:ℝ)):=by
    dsimp only [u,kernelMass]
    rw [intervalIntegral.integral_comp_div (fun x=>‖kernel n x‖^2) n0.ne',smul_eq_mul,neg_div]
  have vtrans:(∫x in -T..T,v x)=(n:ℝ)^2*K T:=intervalIntegral.integral_const_mul ..
  rw [Real.norm_eq_abs,intervalIntegral.integral_sub (cu.intervalIntegrable ..) (cv.intervalIntegrable ..),utrans,vtrans,
    show (n:ℝ)*kernelMass n (T/(n:ℝ))-(n:ℝ)^2*K T=(n:ℝ)*(kernelMass n (T/(n:ℝ))-(n:ℝ)*K T) by ring,abs_mul,abs_of_pos n0,
    abs_of_nonneg (by linarith : 0≤T- -T)] at est
  have pos:0≤2*T*(1+Real.pi*T):=by positivity
  apply le_of_mul_le_mul_left (a:=(n:ℝ)) _ n0
  nlinarith only [est,mul_le_mul_of_nonneg_right n1 pos]

end OddMinorKernel

namespace OddMinorMajor
open Finset Filter MeasureTheory Conjectures.Goldbach.EstermannAlmostAllPolylog_aux
open scoped ComplexConjugate
noncomputable section

abbrev Q (n : ℕ) := GoldbachMajorArc.Polylog.cutoff 2 n

def major (n : ℕ) : ℂ := GoldbachBlockGeometry.majorContribution (Q n) n (fun t=>GoldbachMajorArc.primeSum n t ^ 2 * GoldbachMajorArc.phase (-(n:ℝ)*t))

def mass (n q : ℕ) : ℝ := GoldbachMajorArc.kernelMass n (GoldbachMajorArc.Polylog.width (Q n) n q)

def model (n : ℕ) : ℝ := ∑ q ∈ Icc 1 (Q n), (GoldbachMajorArc.coefficient q n).re * mass n q

private theorem centered (n : ℕ) (t:ℝ) :
    GoldbachEstermannKernel.twisted n n t = ((‖GoldbachMajorArc.kernel n t‖^2 : ℝ):ℂ) := by
  let E := GoldbachMajorArc.phase
  have add (x y:ℝ) : E (x+y)=E x*E y := by
    unfold E GoldbachMajorArc.phase;rw [←Complex.exp_add];congr 1;push_cast;ring
  have cc (x : ℝ) : conj (E x)=E (-x) := by
    unfold E GoldbachMajorArc.phase;rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
    congr 1; push_cast; ring
  have hsym : GoldbachMajorArc.kernel n t * E (-(n:ℝ)*t) = conj (GoldbachMajorArc.kernel n t) := by
    unfold GoldbachMajorArc.kernel
    rw [sum_mul,map_sum]
    change (∑k∈range (n+1),E ((k:ℝ)*t)*E (-(n:ℝ)*t))=∑k∈range (n+1),conj (E ((k:ℝ)*t))
    calc
      _ = ∑k∈range (n+1),conj (E (((n-k:ℕ):ℝ)*t)) := by
        apply sum_congr rfl
        intro k hk
        rw [cc,←add,Nat.cast_sub (Nat.lt_succ_iff.mp (mem_range.mp hk))]
        congr 1;ring
      _ = _ := by simpa only [Nat.add_sub_cancel] using
        sum_range_reflect (fun k=>conj (E ((k:ℝ)*t))) (n+1)
  change (GoldbachMajorArc.kernel n t)^2 * E (-(n:ℝ)*t) = _
  rw [sq,mul_assoc,hsym,Complex.mul_conj,Complex.normSq_eq_norm_sq]

def complexModel (n:ℕ) := ∑q∈Icc 1 (Q n),GoldbachMajorArc.coefficient q n * ∫t in -(GoldbachBlockGeometry.width (Q n) n q)..(GoldbachBlockGeometry.width (Q n) n q), GoldbachEstermannKernel.twisted n n t

theorem model_identity (n : ℕ) : complexModel n = (model n:ℂ) := by
  unfold complexModel model
  push_cast
  apply sum_congr rfl
  intro q hq
  simp_rw [centered]
  rw [intervalIntegral.integral_ofReal]
  have hi := GoldbachMajorArc.coefficient_im_zero n (mem_Icc.mp hq).1
  have realC : ((GoldbachMajorArc.coefficient q n).re:ℂ)=GoldbachMajorArc.coefficient q n := by
    apply Complex.ext <;> simp [hi]
  rw [realC]
  rfl

open GoldbachMajorArc

private theorem bound {n:ℕ} (hn:2*(Q n)^2<n) :
    ‖major n - complexModel n‖ ≤ Polylog.totalArcError (Q n) n (n:ℝ) := by
  let F (t:ℝ) := primeSum n t ^ 2 * phase (-(n:ℝ)*t)
  let K := GoldbachEstermannKernel.twisted n n
  let C (q a : ℕ) := (unitMean q a)^2 * phase (-(n:ℝ)*((a:ℝ)/q))
  have fc : Continuous F := by unfold F primeSum phase;fun_prop
  have kc : Continuous K := by unfold K GoldbachEstermannKernel.twisted GoldbachEstermannKernel.kernel GoldbachEstermannKernel.phase;fun_prop
  have endpoints : C 1 0 = C 1 1 := by
    have um (a:ℕ):unitMean 1 a=1:=by rw [unitMean_eq_ram (by simp),ram_one];simp
    have ph:phase (-(n:ℝ))=1:=by
      unfold phase
      convert Complex.exp_int_mul_two_pi_mul_I (-(n:ℤ)) using 2
      push_cast
      ring
    simp only [C,um,one_pow,one_mul,Nat.cast_zero,Nat.cast_one,zero_div,one_div_one,mul_zero,mul_one,ph]
    simp [phase]
  have h := GoldbachBlockGeometry.major_error F K fc kc C endpoints hn
  have coef (q:ℕ) : (∑a∈(range q).filter (fun a=>a.Coprime q), C q a)=coefficient q n := sum_centers_eq_coefficient q n
  simp_rw [coef] at h
  apply h.trans_eq
  unfold Polylog.totalArcError
  apply sum_congr rfl;intro q _
  apply sum_congr rfl;intro a _
  apply intervalIntegral.integral_congr;intro t _
  let c := (a:ℝ)/q
  let k := kernel n t
  let u := unitMean q a
  change ‖primeSum n (c+t)^2*phase (-(n:ℝ)*(c+t)) - (u^2*phase (-(n:ℝ)*c))*(k^2*phase (-(n:ℝ)*t))‖ =
    ‖primeSum n (c+t)^2*phase (-(n:ℝ)*(c+t)) - (u*k)^2*phase (-(n:ℝ)*(c+t))‖
  have add (x y:ℝ) : phase (x+y)=phase x*phase y := by
    unfold phase;rw [←Complex.exp_add];congr 1;push_cast;ring
  rw [mul_add,add]
  congr 1;ring

theorem transfer : ∀ᶠ n : ℕ in atTop, ‖major n - (model n:ℂ)‖ ≤ (n:ℝ)/(Real.log n)^4 := by
  have small := ((isLittleO_log_rpow_rpow_atTop (4:ℝ) (by norm_num : (0:ℝ)<1)).comp_tendsto
      (tendsto_natCast_atTop_atTop (R:=ℝ))).bound (by norm_num : (0:ℝ)<1/1024)
  filter_upwards [small,Polylog.eventually_totalArcError_lt 2 4 (by decide) (by norm_num : (0:ℝ)<1),
    eventually_ge_atTop (2:ℕ)] with n geo err hn
  have pos := Real.log_pos (by exact_mod_cast hn : (1:ℝ)<n)
  change ‖Real.log (n:ℝ)^(4:ℝ)‖ ≤ (1/1024)*‖(n:ℝ)^(1:ℝ)‖ at geo
  rw [show (4:ℝ)=(4:ℕ) by norm_num,Real.rpow_natCast,Real.rpow_one,Real.norm_eq_abs,
    abs_of_nonneg (by positivity),Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg n)] at geo
  have qq := Polylog.cutoff_le_log 4 hn
  have idn : (Q n)^2=Polylog.cutoff 4 n := by unfold Q Polylog.cutoff;ring
  have dis : 2*(Q n)^2<n := by
    rw [idn]
    apply (Nat.cast_lt (α:=ℝ)).mp
    push_cast
    nlinarith only [qq,geo,show (0:ℝ)<n by exact_mod_cast (by omega:0<n)]
  rw [←model_identity]
  apply (bound dis).trans
  apply (le_div_iff₀ (pow_pos pos 4)).mpr
  simpa only [Q,mul_comm,one_mul,mul_one] using (err (n:ℝ)).le

theorem transfer_real : ∀ᶠ n : ℕ in atTop, |(major n).re - model n| ≤ (n:ℝ)/(Real.log n)^4 := by
  filter_upwards [transfer] with n hn
  exact (Complex.abs_re_le_norm (major n - model n)).trans hn

end
end OddMinorMajor

open Finset Filter
namespace OddMinorFixed
open Conjectures.Goldbach.EstermannAlmostAllPolylog_aux.GoldbachMajorArc
open OddMinorMajor
noncomputable section

def fixed (n:ℕ) : ℝ :=
  ∑q∈Icc 1 (Q n),(coefficient q n).re*((n:ℝ)*OddMinorKernel.K ((Q n:ℝ)/q))

theorem bound {n:ℕ}
    (compare : ∀ {T:ℝ}, 0≤T → |kernelMass n (T/n) - n*OddMinorKernel.K T| ≤ 6*T*(1+Real.pi*T)) :
    |model n - fixed n| ≤ 24*(1+Real.pi)*((Q n:ℝ)+1)^3 := by
  let A : ℝ := Q n
  have az : 0≤A := Nat.cast_nonneg _
  have each (q:ℕ) (hq:q∈Icc 1 (Q n)) :
      |mass n q - (n:ℝ)*OddMinorKernel.K (A/q)| ≤ 6*A*(1+Real.pi*A) := by
    have h1 : (1:ℝ) ≤ q := by exact_mod_cast (mem_Icc.mp hq).1
    have qr := zero_lt_one.trans_le h1
    have small : A/q ≤ A := div_le_self az h1
    have h := compare (T:=A/q) (by positivity)
    rw [mass,Polylog.width]
    change |kernelMass n (A/((q:ℝ)*n)) - n*OddMinorKernel.K (A/q)| ≤ _
    rw [←div_div]
    exact h.trans (mul_le_mul (mul_le_mul_of_nonneg_left small (by norm_num))
      (add_le_add (le_refl 1) (mul_le_mul_of_nonneg_left small Real.pi_pos.le)) (by positivity) (by positivity))
  have top : Real.sqrt A ≤ A+1 := by nlinarith only [Real.sq_sqrt az,sq_nonneg (Real.sqrt A-1),az]
  unfold model fixed
  rw [←sum_sub_distrib]
  apply (abs_sum_le_sum_abs ..).trans
  calc
    _ ≤ ∑q∈Icc 1 (Q n),‖coefficient q n‖*(6*A*(1+Real.pi*A)) := by
      apply sum_le_sum
      intro q hq
      rw [←mul_sub,abs_mul]
      exact mul_le_mul (Complex.abs_re_le_norm _) (each q hq) (abs_nonneg _) (norm_nonneg _)
    _ = (∑q∈Icc 1 (Q n),‖coefficient q n‖)*(6*A*(1+Real.pi*A)) := (sum_mul ..).symm
    _ ≤ (4*(A+1))*(6*A*(1+Real.pi*A)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact (sum_norm_coefficient_le_sqrt (Q n) n).trans (mul_le_mul_of_nonneg_left top (by norm_num))
    _ ≤ _ := by
      change 4*(A+1)*(6*A*(1+Real.pi*A)) ≤ 24*(1+Real.pi)*(A+1)^3
      nlinarith only [az,sq_nonneg A,Real.pi_pos.le,mul_nonneg Real.pi_pos.le az,mul_nonneg Real.pi_pos.le (sq_nonneg A)]

theorem factor (n:ℕ) : fixed n = (n:ℝ)*∑q∈Icc 1 (Q n),(coefficient q n).re*OddMinorKernel.K ((Q n:ℝ)/q) := by
  unfold fixed
  rw [mul_sum]
  exact sum_congr rfl (fun _ _=>by ring)

theorem transfer : ∀ᶠ n:ℕ in atTop,
    |(major n).re-fixed n| ≤ (n:ℝ)/(Real.log n)^4+24*(1+Real.pi)*((Q n:ℝ)+1)^3 := by
  filter_upwards [transfer_real,eventually_ge_atTop (1:ℕ)] with n hd np
  exact (abs_sub_le (major n).re (model n) (fixed n)).trans
    (add_le_add hd (bound (fun hT=>OddMinorKernel.mass_compare np hT)))

end
end OddMinorFixed

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

open Finset Filter
namespace OddMinorRam
open Conjectures.Goldbach.EstermannAlmostAllPolylog_aux.GoldbachMajorArc
noncomputable section

private theorem phase_norm (x : ℝ) : ‖phase x‖ = 1 := by
  unfold phase
  exact Complex.norm_exp_ofReal_mul_I _

theorem ram_norm_le (q n : ℕ) : ‖ram q n‖ ≤ (q : ℝ) := by
  unfold ram
  calc
    _ ≤ ∑ a ∈ (range q).filter (fun a => a.Coprime q),
        ‖phase ((n : ℝ) * a / q)‖ := norm_sum_le _ _
    _ = ((range q).filter (fun a => a.Coprime q)).card := by
      simp [phase_norm]
    _ ≤ q := by
      exact_mod_cast (Finset.card_filter_le (range q) (fun a => a.Coprime q)).trans_eq
        (Finset.card_range q)

theorem coefficient_norm_le_cube {q : ℕ} (hq : 0 < q) (n : ℕ) :
    ‖coefficient q n‖ ≤ (q : ℝ)^3 := by
  have tp : (0 : ℝ) < q.totient := by
    exact_mod_cast Nat.totient_pos.mpr hq
  have tone : (1 : ℝ) ≤ q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  have qr : (0 : ℝ) ≤ q := by positivity
  have ratio : ‖ram q 1‖ / (q.totient : ℝ) ≤ q := by
    apply (div_le_iff₀ tp).mpr
    nlinarith only [ram_norm_le q 1, tone, qr]
  calc
    ‖coefficient q n‖ =
        (‖ram q 1‖ / (q.totient : ℝ))^2 * ‖ram q n‖ := by
      simp [coefficient, norm_pow]
    _ ≤ (q : ℝ)^2 * q := by
      gcongr
      exact ram_norm_le q n
    _ = (q : ℝ)^3 := by ring

def oddPartial (q A t : ℕ) : ℂ :=
  ∑ i ∈ range t, coefficient q (A + 2*i)

theorem odd_period {q : ℕ} (hq : 0 < q) (A i : ℕ) :
    coefficient q (A + 2*(i+q)) = coefficient q (A + 2*i) := by
  have arith : A + 2*(i+q) = (A+2*i)+q*2 := by omega
  rw [arith, ProgressionZero.coefficient_period_mul q (A+2*i) 2 hq]

theorem odd_zero {q : ℕ} (qbig : 3 ≤ q) (A : ℕ) : oddPartial q A q = 0 := by
  have qn : ¬q ∣ 2 := by
    intro d
    have le := Nat.le_of_dvd (by decide : 0 < 2) d
    omega
  exact ProgressionZero.coefficient_sum_zero q A 2 (by omega) qn

theorem oddPartial_mod {q : ℕ} (qbig : 3 ≤ q) (A t : ℕ) :
    oddPartial q A t = oddPartial q A (t % q) := by
  induction t using Nat.strong_induction_on with
  | ind t ih =>
    by_cases h : t < q
    · rw [Nat.mod_eq_of_lt h]
    · have qt : q ≤ t := by omega
      have tk : t = q + (t-q) := by omega
      conv_lhs => rw [tk]
      unfold oddPartial
      rw [Finset.sum_range_add]
      have zero := odd_zero qbig A
      change (∑ i ∈ range q, coefficient q (A+2*i)) = 0 at zero
      rw [zero, zero_add]
      have per : (∑ i ∈ range (t-q), coefficient q (A+2*(q+i))) =
          ∑ i ∈ range (t-q), coefficient q (A+2*i) := by
        apply Finset.sum_congr rfl
        intro i hi
        simpa only [Nat.add_comm q i] using odd_period (by omega : 0 < q) A i
      rw [per]
      have hrec := ih (t-q) (by omega)
      change (∑ i ∈ range (t-q), coefficient q (A+2*i)) =
        ∑ i ∈ range ((t-q) % q), coefficient q (A+2*i) at hrec
      rw [hrec]
      have modEq : t % q=(t-q) % q := by
        conv_lhs => rw [tk]
        simp
      rw [modEq]

theorem oddPartial_bound {q : ℕ} (qbig : 3 ≤ q) (A t : ℕ) :
    ‖oddPartial q A t‖ ≤ (q : ℝ)^4 := by
  have qp : 0 < q := by omega
  rw [oddPartial_mod qbig]
  unfold oddPartial
  calc
    _ ≤ ∑ i ∈ range (t % q), ‖coefficient q (A+2*i)‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ range (t % q), (q : ℝ)^3 := by
      apply Finset.sum_le_sum
      intro i hi
      exact coefficient_norm_le_cube qp _
    _ = ((t % q:ℕ) : ℝ) * (q : ℝ)^3 := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ (q : ℝ)^4 := by
      have rem : t % q ≤ q := (Nat.mod_lt t qp).le
      have cast : ((t % q:ℕ) : ℝ) ≤ q := by exact_mod_cast rem
      nlinarith only [mul_le_mul_of_nonneg_right cast (by positivity : 0 ≤ (q:ℝ)^3)]

def oddWeighted (q A t : ℕ) : ℂ :=
  ∑ i ∈ range t, ((A+2*i : ℕ) : ℂ) * coefficient q (A+2*i)

private theorem oddPartial_succ (q A t : ℕ) :
    oddPartial q A (t+1) = oddPartial q A t + coefficient q (A+2*t) := by
  simp [oddPartial, Finset.sum_range_succ]

theorem oddWeighted_Abel (q A t : ℕ) :
    oddWeighted q A t = ((A+2*t : ℕ) : ℂ) * oddPartial q A t -
      2 * ∑ k ∈ range t, oddPartial q A (k+1) := by
  induction t with
  | zero => simp [oddWeighted, oddPartial]
  | succ t ih =>
    calc
      oddWeighted q A (t+1) = oddWeighted q A t +
          ((A+2*t : ℕ) : ℂ) * coefficient q (A+2*t) := by
        simp [oddWeighted, Finset.sum_range_succ]
      _ = ((A+2*t : ℕ) : ℂ) * oddPartial q A t -
          2 * ∑ k ∈ range t, oddPartial q A (k+1) +
            ((A+2*t : ℕ) : ℂ) * coefficient q (A+2*t) := by rw [ih]
      _ = ((A+2*(t+1) : ℕ) : ℂ) * oddPartial q A (t+1) -
          2 * ∑ k ∈ range (t+1), oddPartial q A (k+1) := by
        rw [Finset.sum_range_succ, oddPartial_succ]
        push_cast
        ring

theorem oddWeighted_bound {q : ℕ} (qbig : 3 ≤ q) (A t : ℕ) :
    ‖oddWeighted q A t‖ ≤ ((A+4*t : ℕ) : ℝ) * (q : ℝ)^4 := by
  rw [oddWeighted_Abel]
  have sumBound :
      ‖∑ k ∈ range t, oddPartial q A (k+1)‖ ≤ (t : ℝ) * (q : ℝ)^4 := by
    calc
      _ ≤ ∑ k ∈ range t, ‖oddPartial q A (k+1)‖ := norm_sum_le _ _
      _ ≤ ∑ _k ∈ range t, (q : ℝ)^4 := by
        apply Finset.sum_le_sum
        intro k hk
        exact oddPartial_bound qbig A (k+1)
      _ = (t : ℝ) * (q : ℝ)^4 := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  calc
    _ ≤ ‖((A+2*t : ℕ) : ℂ) * oddPartial q A t‖ +
          ‖(2 : ℂ) * ∑ k ∈ range t, oddPartial q A (k+1)‖ := norm_sub_le _ _
    _ = ((A+2*t : ℕ) : ℝ) * ‖oddPartial q A t‖ +
          2 * ‖∑ k ∈ range t, oddPartial q A (k+1)‖ := by
      simp only [norm_mul, Complex.norm_natCast]
      norm_num
    _ ≤ ((A+2*t : ℕ) : ℝ) * (q : ℝ)^4 + 2*(t : ℝ)*(q : ℝ)^4 := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left (oddPartial_bound qbig A t) (by positivity)
      · nlinarith only [mul_le_mul_of_nonneg_left sumBound (by norm_num : (0 : ℝ) ≤ 2)]
    _ = ((A+4*t : ℕ) : ℝ) * (q : ℝ)^4 := by
      push_cast
      ring

end
end OddMinorRam

open Finset
open Conjectures.Goldbach.EstermannAlmostAllPolylog_aux.GoldbachMajorArc
noncomputable section
namespace OddMinorFirstTwo
open OddMinorFull OddMinorKernel

theorem values {n:ℕ} (odd:Odd n) :
    (coefficient 1 n).re=1 ∧ (coefficient 2 n).re= -1 := by
  have nd:¬2∣n:=by obtain ⟨k,hk⟩:=odd;omega
  rw [coefficient_one,coefficient_prime Nat.prime_two]
  norm_num [localCoefficient,nd]

theorem split {Q:ℕ} (q2:2≤Q) (f:ℕ→ℝ) :
    ∑q∈Icc 1 Q,f q=f 1+f 2+∑q∈Icc 3 Q,f q := by
  have eq:Icc 1 Q=insert 1 (insert 2 (Icc 3 Q)):=by ext q;simp only [mem_Icc,mem_insert];omega
  rw [eq,sum_insert (by simp),sum_insert (by simp)]
  ring

theorem row {n Q:ℕ} (od:Odd n) (qp:0<Q) :
    (n:ℝ)/(4*Real.pi^2*Q) ≤
      (coefficient 1 n).re*((n:ℝ)*K ((Q:ℝ)/(1:ℕ)))+
      (coefficient 2 n).re*((n:ℝ)*K ((Q:ℝ)/(2:ℕ))) := by
  obtain ⟨v1,v2⟩:=values od
  rw [v1,v2]
  push_cast
  simp only [div_one,one_mul,neg_one_mul]
  have h:=mul_le_mul_of_nonneg_left (gap qp) (Nat.cast_nonneg (α:=ℝ) n)
  convert h using 1 <;> ring

theorem main (k:ℕ) :
    (1/Real.pi^2)*(base k:ℝ)^2/((k:ℝ)+2)^2 ≤
      ∑i∈range (base k),
        ((coefficient 1 (point k i)).re*((point k i:ℝ)*K (((k+2)^2:ℕ):ℝ))+
        (coefficient 2 (point k i)).re*((point k i:ℝ)*K ((((k+2)^2:ℕ):ℝ)/2))) := by
  let Q:=(k+2)^2
  have qp:0<Q:=by dsimp [Q];positivity
  have den:0<4*Real.pi^2*(Q:ℝ):=by positivity
  have each (i:ℕ) (hi:i∈range (base k)) :
      4*(base k:ℝ)/(4*Real.pi^2*(Q:ℝ)) ≤
      (coefficient 1 (point k i)).re*((point k i:ℝ)*K (Q:ℝ))+
      (coefficient 2 (point k i)).re*((point k i:ℝ)*K ((Q:ℝ)/2)) := by
    have pt:=point_props (mem_range.mp hi)
    have ptle:4*(base k:ℝ)≤(point k i:ℝ):=by exact_mod_cast pt.2.1
    apply (div_le_div_of_nonneg_right ptle den.le).trans
    simpa only [Nat.cast_one,Nat.cast_ofNat,div_one] using row pt.1 qp
  have all:=sum_le_sum each
  rw [sum_const,card_range,nsmul_eq_mul] at all
  refine le_trans ?_ all
  dsimp [Q]
  push_cast
  have pn:Real.pi≠0:=Real.pi_ne_zero
  have kn:(k:ℝ)+2≠0:=by positivity
  apply le_of_eq
  field_simp

end OddMinorFirstTwo

open Filter Finset
open scoped Classical
noncomputable section
namespace OddMinorContra
open OddMinorFull

theorem geometric_dominates (s:ℝ) (sp:0<s) (d:ℕ) (C:ℝ) (cp:0<C) :
    ∀ᶠ k:ℕ in atTop, ((k:ℝ)+2)^d < C*(base k:ℝ)^s := by
  let r:ℝ:=(2:ℝ)^s
  have rp:1<r := Real.one_lt_rpow (by norm_num) sp
  have lim:=tendsto_pow_const_div_const_pow_of_one_lt d rp
  have pos : 0<C/2^d := by positivity
  filter_upwards [lim.eventually_lt_const pos,eventually_ge_atTop 2] with k hk big
  have kp : (2:ℝ)≤k := by exact_mod_cast big
  have le : (k:ℝ)+2≤2*k := by linarith
  have ar : (base k:ℝ)^s=r^k := by
    simp only [base,Nat.cast_pow,Nat.cast_ofNat,r]
    rw [←Real.rpow_natCast,←Real.rpow_mul (by norm_num),mul_comm,Real.rpow_mul (by norm_num)]
    simp
  rw [ar]
  have hk' := (div_lt_iff₀ (pow_pos (lt_trans zero_lt_one rp) k)).mp hk
  calc
    _ ≤ (2*(k:ℝ))^d := pow_le_pow_left₀ (by positivity) le d
    _ = (2:ℝ)^d*(k:ℝ)^d := mul_pow .. 
    _ < 2^d*(C/2^d*r^k) := mul_lt_mul_of_pos_left hk' (by positivity)
    _ = _ := by field_simp

theorem contradiction {c:ℝ} (cp:0<c) (bias:∀ᶠ k:ℕ in atTop,
    c*(base k:ℝ)^2/((k:ℝ)+2)^2 ≤ -∑i∈range (base k),minor (point k i)) :
    ¬(∀ e:ℝ, 0<e → ∃ C:ℝ, ∃N:ℕ, 0<C ∧ ∀X:ℕ, N≤X →
        (∑n∈Icc X (2*X),(minor n)^2) ≤ C*(X:ℝ)^(18/7+e)) := by
  intro claimed
  obtain ⟨C,N,cp',upper⟩:=claimed (5/28) (by norm_num)
  let D:=C*(4:ℝ)^(11/4:ℝ)
  have dd:0<D := by dsimp [D];positivity
  have gt:=geometric_dominates (1/4) (by norm_num) 4 (c^2/D) (by positivity)
  obtain ⟨k,lb,small,large⟩:=
    (bias.and (gt.and (eventually_ge_atTop N))).exists
  let m:ℝ:=base k
  let P:ℝ:=(k:ℝ)+2
  let S:=∑i∈range (base k),minor (point k i)
  have mp:0 < m := by dsimp [m];exact_mod_cast base_pos k
  have pp:0 < P := by dsimp [P];positivity
  have nx:N≤4*base k := by have : k<2^k := Nat.lt_two_pow_self;dsimp [base];omega
  have hu := (residual_square_subsum k).trans (upper (4*base k) nx)
  have ur : (∑i∈range (base k),(minor (point k i))^2) ≤ D*m^(11/4:ℝ) := by
    norm_num only [show (18/7+5/28:ℝ)=11/4 by norm_num,Nat.cast_mul,Nat.cast_ofNat] at hu
    simpa only [D,m,Real.mul_rpow (by norm_num : (0:ℝ)≤4) mp.le,mul_assoc] using hu
  have cs := sq_sum_le_card_mul_sum_sq (s:=range (base k)) (f:=fun i=>minor (point k i))
  have su : S^2≤D*m^(15/4:ℝ) := by
    simp only [card_range] at cs
    apply cs.trans
    have le:=mul_le_mul_of_nonneg_left ur mp.le
    apply le.trans_eq
    rw [show (15/4:ℝ)=1+11/4 by norm_num,Real.rpow_add mp,Real.rpow_one]
    ring
  have lb' : c*m^2/P^2 ≤ -S := lb
  have ss:=pow_le_pow_left₀ (by positivity : 0≤c*m^2/P^2) lb' 2
  rw [div_pow,mul_pow,neg_sq] at ss
  have product := (div_le_iff₀ (by positivity : 0<(P^2)^2)).mp (ss.trans su)
  have ps : P^4 < c^2/D*m^(1/4:ℝ) := small
  have smaller:=mul_lt_mul_of_pos_left ps (mul_pos dd (Real.rpow_pos_of_pos mp (15/4:ℝ)))
  have eq : D*m^(15/4:ℝ)*(c^2/D*m^(1/4:ℝ))=c^2*(m^2)^2 := by
    have ex : m^(15/4:ℝ)*m^(1/4:ℝ)=m^4 := by
      rw [←Real.rpow_add mp,show (15/4+1/4:ℝ)=4 by norm_num];norm_cast
    calc
      _ = c^2*(m^(15/4:ℝ)*m^(1/4:ℝ)) := by field_simp [dd.ne']
      _ = _ := by rw [ex];ring
  rw [eq] at smaller
  linarith only [product,smaller,show (P^2)^2=P^4 by ring,
    show D*m^(15/4:ℝ)*(P^2)^2=D*m^(15/4:ℝ)*P^4 by ring]
theorem absorb {A C:ℝ} (ap:0<A) (cp:0≤C) (d:ℕ) (raw:∀ᶠ k:ℕ in atTop,
    A*(base k:ℝ)^2/((k:ℝ)+2)^2 ≤ -(∑i∈range (base k),minor (point k i)) +
      C*(base k:ℝ)*((k:ℝ)+2)^d + C*(base k:ℝ)^2/((k:ℝ)+2)^4) :
    ∀ᶠ k:ℕ in atTop, (A/2)*(base k:ℝ)^2/((k:ℝ)+2)^2 ≤ -∑i∈range (base k),minor (point k i) := by
  have geo:=geometric_dominates 1 (by norm_num) (d+2) (A/(4*(C+1))) (by positivity)
  have big : ∀ᶠ k:ℕ in atTop, 4*C/A < k :=
    tendsto_natCast_atTop_atTop.eventually_gt_atTop _
  filter_upwards [raw,geo,big] with k h poly huge
  let m:ℝ:=base k
  let P:ℝ:=(k:ℝ)+2
  have mp:0 < m := by dsimp [m];exact_mod_cast base_pos k
  have pp:0 < P := by dsimp [P];positivity
  have pl:P^d*P^2 < A/(4*(C+1))*m := by simpa [P,m,pow_add] using poly
  have a1 : C*m*P^d ≤ (A/4)*m^2/P^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos pp)).mpr
    have pc : 4*(C+1)*(P^d*P^2) < A*m := by
      have l : P^d*P^2 < A*m/(4*(C+1)) := by convert pl using 1; ring
      have z := (lt_div_iff₀ (by positivity : 0<4*(C+1))).mp l
      linarith only [z,show P^d*P^2*(4*(C+1))=4*(C+1)*(P^d*P^2) by ring]
    have r:=mul_le_mul_of_nonneg_right pc.le mp.le
    nlinarith only [r,mul_nonneg (mul_nonneg (pow_nonneg pp.le d) (sq_nonneg P)) mp.le]
  have ca : 4*C ≤ A*P^2 := by
    have z := (div_lt_iff₀ ap).mp huge
    have zz : (k:ℝ)≤P^2 := by dsimp [P]; nlinarith [sq_nonneg (k:ℝ),Nat.cast_nonneg k (α:=ℝ)]
    nlinarith only [z,mul_le_mul_of_nonneg_left zz ap.le]
  have a2 : C*m^2/P^4 ≤ (A/4)*m^2/P^2 := by
    rw [div_le_div_iff₀ (pow_pos pp 4) (sq_pos_of_pos pp)]
    have z := mul_le_mul_of_nonneg_right ca (mul_nonneg (sq_nonneg m) (sq_nonneg P))
    nlinarith only [z]
  change A*m^2/P^2 ≤ _ + C*m*P^d+C*m^2/P^4 at h
  change (A/2)*m^2/P^2 ≤ _
  linarith only [h,a1,a2,show A*m^2/P^2 = (A/2)*m^2/P^2+2*((A/4)*m^2/P^2) by ring]
end OddMinorContra

open Filter Finset
open scoped Classical
noncomputable section
namespace OddMinorBlock
open OddMinorFull OddMinorContra

abbrev P (k:ℕ) : ℝ := (k:ℝ)+2

theorem log_bounds {k i:ℕ} (hi:i<base k) :
    P k*Real.log 2 ≤ Real.log (point k i) ∧ Real.log (point k i) ≤ 2*P k := by
  have mpos:=base_pos k
  have pt:=point_props hi
  have lower : (2:ℝ)^(k+2) ≤ point k i := by
    exact_mod_cast (show 2^(k+2)≤point k i by rw [pow_add];change 2^k*4 ≤ _; simp [point,base];omega)
  have upper : (point k i:ℝ) ≤ (2:ℝ)^(k+3) := by
    exact_mod_cast (show point k i≤2^(k+3) by rw [pow_add];change _≤2^k*8;change i<2^k at hi;simp only [point,base];omega)
  have pos:0<(point k i:ℝ) := by exact_mod_cast (show 0<point k i by omega)
  have l:=Real.log_le_log (by positivity) lower
  have r:=Real.log_le_log pos upper
  rw [Real.log_pow] at l r
  push_cast at l r
  refine ⟨l,?_⟩
  apply r.trans
  have le:=Real.log_le_sub_one_of_pos (by norm_num : 0<(2:ℝ))
  dsimp [P]
  nlinarith [mul_le_mul_of_nonneg_left le (show 0≤(k:ℝ)+3 by positivity),Nat.cast_nonneg k (α:=ℝ)]

theorem fixed_to_bias (F:ℕ→ℝ) (E:ℝ) (ep:0≤E)
    (err:∀ᶠ n:ℕ in atTop, |(OddMinorMajor.major n).re-F n| ≤
        (n:ℝ)/(Real.log n)^4+E*((OddMinorMajor.Q n:ℝ)+1)^3)
    (A C:ℝ) (ap:0<A) (cp:0≤C) (d:ℕ) (main:∀ᶠ k:ℕ in atTop,
      A*(base k:ℝ)^2/(P k)^2 ≤ (∑i∈range (base k),F (point k i))+C*(base k:ℝ)*(P k)^d) :
    ∀ᶠ k:ℕ in atTop, (A/2)*(base k:ℝ)^2/(P k)^2 ≤ -∑i∈range (base k),minor (point k i) := by
  let B:ℝ:=4+8*E+6/(Real.log 2)^4
  have L:0<Real.log 2 := Real.log_pos (by norm_num)
  have bp : 0≤B := by dsimp [B];positivity
  obtain ⟨N,beyond⟩:=eventually_atTop.mp err
  apply absorb ap (add_nonneg bp cp) (d+6)
  filter_upwards [main,eventually_ge_atTop N] with k hm kn
  let m:ℝ:=base k
  let v:=P k
  have mpos:=base_pos k
  have mp:0 < m := by dsimp [m];exact_mod_cast mpos
  have v1:1≤v := by dsimp [v,P];linarith [Nat.cast_nonneg k (α:=ℝ)]
  have vp:=lt_of_lt_of_le zero_lt_one v1
  have ptBound (i:ℕ) (hi:i∈range (base k)) : F (point k i) ≤
      -minor (point k i)+B*v^6+B*m/v^4 := by
    let n:=point k i
    have props:=point_props (mem_range.mp hi)
    have np:5≤n := by dsimp [n,point];omega
    have nn:N≤n := by have : k<2^k := Nat.lt_two_pow_self;change k<base k at this;dsimp [n];omega
    have qeq : (OddMinorMajor.Q n:ℝ)=v^2 := by
      change (cutoff (point k i):ℝ)=((k:ℝ)+2)^2
      rw [props.2.2.2];push_cast;rfl
    have ct : (n:ℝ)≤6*m := by dsimp [n,m];exact_mod_cast props.2.2.1
    obtain ⟨logl,logr⟩:=log_bounds (mem_range.mp hi)
    change v*Real.log 2≤Real.log n at logl
    change Real.log n≤2*v at logr
    have io:=odd_upper n np props.1
    have log2le:Real.log 2≤1 := by linarith only [Real.log_le_sub_one_of_pos (by norm_num : 0<(2:ℝ))]
    have full : (OddMinorMajor.major n).re+minor n≤4*v := by
      apply io.trans
      calc
        _ ≤ 2*1*(2*v) := mul_le_mul (by linarith only [log2le]) logr (Real.log_nonneg (by exact_mod_cast (show 1≤n by omega))) (by norm_num)
        _ = _ := by ring
    have e:=beyond n nn
    rw [qeq] at e
    have den : (n:ℝ)/(Real.log n)^4≤(6/(Real.log 2)^4)*m/v^4 := by
      calc
        _ ≤ 6*m/(v*Real.log 2)^4 := div_le_div₀ (by positivity) ct (pow_pos (mul_pos vp L) _) (pow_le_pow_left₀ (mul_nonneg vp.le L.le) logl _)
        _ = _ := by ring
    have vc : (v^2+1)^3≤8*v^6 := by
      have a: v^2+1≤2*v^2 := by linarith [one_le_pow₀ v1 (n:=2)]
      calc
        _ ≤ (2*v^2)^3 := pow_le_pow_left₀ (by positivity) a 3
        _ = _ := by ring
    have le6 : v≤v^6 := by simpa using (pow_le_pow_right₀ v1 (by decide : 1≤6))
    have on := (abs_le.mp e).1
    have B1:4+8*E≤B := by dsimp [B];exact le_add_of_nonneg_right (by positivity)
    have B2:6/(Real.log 2)^4≤B := by dsimp [B];linarith
    have x1:=mul_le_mul_of_nonneg_right B1 (pow_nonneg vp.le 6)
    have x2:=div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right B2 mp.le) (pow_nonneg vp.le 4)
    change F n ≤ -minor n+_+_
    linarith only [full,on,den,mul_le_mul_of_nonneg_left vc ep,le6,x1,x2]
  have allrows:=sum_le_sum ptBound
  simp only [sum_add_distrib,sum_neg_distrib,sum_const,card_range,nsmul_eq_mul] at allrows
  have vd : v^d≤v^(d+6) := pow_le_pow_right₀ v1 (by omega)
  have v6 : v^6≤v^(d+6) := pow_le_pow_right₀ v1 (by omega)
  change A*m^2/v^2 ≤ _ + (B+C)*m*v^(d+6)+(B+C)*m^2/v^4
  change A*m^2/v^2 ≤ _+C*m*v^d at hm
  change _ ≤ _+m*(B*v^6)+m*(B*m/v^4) at allrows
  have z1:=mul_le_mul_of_nonneg_left v6 (mul_nonneg bp mp.le)
  have z2:=mul_le_mul_of_nonneg_left vd (mul_nonneg cp mp.le)
  have z3 : 0≤C*m^2/v^4 := by positivity
  calc
    _ ≤ (∑i∈range (base k), F (point k i))+C*m*v^d := hm
    _ ≤ (-∑i∈range (base k),minor (point k i))+m*(B*v^6)+m*(B*m/v^4)+C*m*v^d :=
      by exact add_le_add_left allrows _
    _ = (-∑i∈range (base k),minor (point k i))+(B*m*v^6+C*m*v^d)+B*m^2/v^4 := by ring
    _ ≤ (-∑i∈range (base k),minor (point k i))+(B*m*v^(d+6)+C*m*v^(d+6))+
      (B*m^2/v^4+C*m^2/v^4) :=
      by exact add_le_add (add_le_add_right (add_le_add z1 z2) _) (le_add_of_nonneg_right z3)
    _ = _ := by ring
end OddMinorBlock

open Finset Filter
open scoped Classical
noncomputable section
namespace OddMinorEnd
open OddMinorFull OddMinorKernel
open Conjectures.Goldbach.EstermannAlmostAllPolylog_aux.GoldbachMajorArc

private def row (k q i:ℕ) : ℝ := (coefficient q (point k i)).re *
    ((point k i:ℝ)*K ((((k+2)^2:ℕ):ℝ)/q))

private theorem tail_bound (k:ℕ) : let Q:=(k+2)^2
    |∑i∈range (base k),∑q∈Icc 3 Q,row k q i| ≤ 1200*(base k:ℝ)*((k:ℝ)+2)^12 := by
  let Q:=(k+2)^2
  let m:=base k
  let A:=4*m+1
  let P:ℝ:=(k:ℝ)+2
  have p1 : 1≤P := by dsimp [P];linarith [Nat.cast_nonneg k (α:=ℝ)]
  have pc : (Q:ℝ)=P^2 := by simp [Q,P]
  have mc : 1≤(m:ℝ) := by exact_mod_cast base_pos k
  have capA : ((A+4*m:ℕ):ℝ) ≤ 9*(m:ℝ) := by dsimp [A]; push_cast;linarith only [mc]
  have each (q:ℕ) (hq:q∈Icc 3 Q) : |∑i∈range m,row k q i| ≤
      18*(m:ℝ)*((Q:ℝ)+1)^5 := by
    let z := OddMinorRam.oddWeighted q A m
    let w := K ((Q:ℝ)/q)
    have aeq : ∑i∈range m,row k q i = z.re*w := by
      dsimp only [row,z,OddMinorRam.oddWeighted,w]
      rw [Complex.re_sum,sum_mul]
      apply sum_congr rfl
      intro i _
      have id : A+2*i=point k i := by dsimp [A,m,point];omega
      rw [id]
      simp only [Complex.mul_re,Complex.natCast_re,Complex.natCast_im,zero_mul,sub_zero]
      dsimp [Q]
      ring
    have wp : 0≤w := K_nonneg (by positivity)
    have q1 : 1≤(q:ℝ) := by exact_mod_cast ((show 1≤3 by decide).trans (mem_Icc.mp hq).1)
    have wcap : w≤2*((Q:ℝ)+1) := (K_le (by positivity)).trans (by
      linarith only [div_le_self (Nat.cast_nonneg Q (α:=ℝ)) q1])
    have zcap : |z.re| ≤ 9*(m:ℝ)*((Q:ℝ)+1)^4 := by
      apply (Complex.abs_re_le_norm z).trans
      apply (OddMinorRam.oddWeighted_bound (mem_Icc.mp hq).1 A m).trans
      have qr:(q:ℝ)≤Q := by exact_mod_cast (mem_Icc.mp hq).2
      gcongr; linarith only [capA,qr]
    rw [aeq,abs_mul,abs_of_nonneg wp]
    calc
      _ ≤ (9*(m:ℝ)*((Q:ℝ)+1)^4)*(2*((Q:ℝ)+1)) :=
        mul_le_mul zcap wcap wp (by positivity)
      _ = _ := by ring
  change |∑i∈range m, ∑q∈Icc 3 Q,row k q i| ≤ _
  rw [sum_comm]
  have cnt : ((Icc 3 Q).card:ℝ)≤(Q:ℝ)+1 := by
    exact_mod_cast (show (Icc 3 Q).card≤Q+1 by simp [Nat.card_Icc];omega)
  have p2:1≤P^2 := one_le_pow₀ p1
  calc
    _ ≤ ∑q∈Icc 3 Q, |∑i∈range m,row k q i| := abs_sum_le_sum_abs .. 
    _ ≤ ∑_q∈Icc 3 Q, 18*(m:ℝ)*((Q:ℝ)+1)^5 := sum_le_sum each
    _ ≤ ((Q:ℝ)+1)*(18*(m:ℝ)*((Q:ℝ)+1)^5) := by
      rw [sum_const,nsmul_eq_mul];gcongr
    _ = 18*(m:ℝ)*(P^2+1)^6 := by rw [pc];ring
    _ ≤ 18*(m:ℝ)*(2*P^2)^6 := by gcongr;linarith only [p2]
    _ ≤ 1200*(m:ℝ)*P^12 := by nlinarith only [mul_nonneg (Nat.cast_nonneg m (α:=ℝ)) (pow_nonneg (zero_le_one.trans p1) 12)]

theorem fixed_lower (k:ℕ) :
    (1/Real.pi^2)*(base k:ℝ)^2/((k:ℝ)+2)^2 ≤
      (∑i∈range (base k),OddMinorFixed.fixed (point k i))+1200*(base k:ℝ)*((k:ℝ)+2)^12 := by
  let Q:=(k+2)^2
  have q2 : 2≤Q := by dsimp [Q];nlinarith [Nat.zero_le k]
  have split : ∑i∈range (base k),OddMinorFixed.fixed (point k i) =
      (∑i∈range (base k),(row k 1 i+row k 2 i))+(∑i∈range (base k),∑q∈Icc 3 Q,row k q i) := by
    rw [←sum_add_distrib]
    apply sum_congr rfl
    intro i hi
    have c : OddMinorMajor.Q (point k i)=Q := (point_props (mem_range.mp hi)).2.2.2
    unfold OddMinorFixed.fixed
    rw [c]
    exact OddMinorFirstTwo.split q2 (fun q=>row k q i)
  have p : (1/Real.pi^2)*(base k:ℝ)^2/((k:ℝ)+2)^2 ≤ ∑ i∈range (base k),(row k 1 i+row k 2 i) := by
    simpa only [row,Nat.cast_one,div_one,Nat.cast_ofNat] using OddMinorFirstTwo.main k
  rw [split]
  have t:= (abs_le.mp (tail_bound k)).1
  linarith only [p,t]

theorem refute : ¬(∀ e:ℝ, 0<e → ∃ C:ℝ, ∃N:ℕ, 0<C ∧ ∀X:ℕ, N≤X →
    (∑n∈Icc X (2*X),(minor n)^2) ≤ C*(X:ℝ)^(18/7+e)) := by
  have b := OddMinorBlock.fixed_to_bias OddMinorFixed.fixed _ (by positivity) OddMinorFixed.transfer
    (1/Real.pi^2) 1200 (by positivity) (by norm_num) 12 (Filter.Eventually.of_forall fixed_lower)
  exact OddMinorContra.contradiction (by positivity : 0<(1/Real.pi^2)/2) b
end OddMinorEnd

theorem Conjectures.Cuts.Refuteb8b4ba21e36f3ce1448331bf : ¬ (have x1 : ℕ → ℝ := fun (x1 : ℕ) => if Nat.Prime x1 then Real.log ↑x1 else (0 : ℝ); have x2 : ℝ → ℂ := fun (x2 : ℝ) => Complex.exp (↑((2 : ℝ) * Real.pi * x2) * Complex.I); have x3 : ℕ → (ℕ → ℝ) → ℝ → ℂ := fun (x3 : ℕ) (x4 : ℕ → ℝ) (x5 : ℝ) => ∑ x6 ∈ Finset.range (x3 + (1 : ℕ)), ↑(x4 x6) * x2 (↑x6 * x5); have x4 : ℕ → ℕ := fun (x4 : ℕ) => Nat.log (2 : ℕ) (x4 + (2 : ℕ)) ^ (2 : ℕ); have x5 : ℕ → Set ℝ := fun (x5 : ℕ) => {x6 : ℝ | ∃ (x7 : ℕ) (x8 : ℕ), (1 : ℕ) ≤ x7 ∧ x7 ≤ x4 x5 ∧ x8 ≤ x7 ∧ x8.Coprime x7 ∧ |x6 - ↑x8 / ↑x7| ≤ ↑(x4 x5) / (↑x7 * ↑x5)}; have x6 : ℕ → ℝ → ℂ := fun (x6 : ℕ) (x7 : ℝ) => x3 x6 x1 x7 ^ (2 : ℕ) * x2 (-↑x6 * x7); have x7 : ℕ → ℂ := fun (x7 : ℕ) => ∫ (x8 : ℝ) in (0 : ℝ)..(1 : ℝ), (x5 x7).indicator (x6 x7) x8; have x8 : ℕ → ℝ := fun (x8 : ℕ) => (∫ (x9 : ℝ) in (0 : ℝ)..(1 : ℝ), (x5 x8)ᶜ.indicator (x6 x8) x9).re; ∀ (x9 : ℝ), (0 : ℝ) < x9 → ∃ (x11 : ℝ) (x12 : ℕ), (0 : ℝ) < x11 ∧ ∀ (x13 : ℕ), x12 ≤ x13 → ∑ x15 ∈ Finset.Icc x13 ((2 : ℕ) * x13), x8 x15 ^ (2 : ℕ) ≤ x11 * ↑x13 ^ ((18 / 7 : ℝ) + x9)) := by
  exact OddMinorEnd.refute
