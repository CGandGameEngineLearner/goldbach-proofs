import Conjectures.Goldbach.ExceptionalZeroCatalogue

/-! Local zero density at scale η near Re s = 1. The right-hand
Dirichlet series is majorized by the logarithmic derivative of zeta,
whose pole has residue one. Taking real parts in the disk partial
fraction expansion retains the sign of every zero contribution. -/

namespace Conjectures.Goldbach.NearOneZeroMultiplicity

open Complex DirichletCharacter Metric Set Filter
open _root_.Goldbach GoldbachSmoothing
open scoped Classical Topology

theorem right_majorant {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    ‖logDeriv (LFunction χ) (⟨σ,t⟩ : ℂ)‖ ≤ (-logDeriv riemannZeta (σ:ℂ)).re := by
  let f : ℕ → ℂ := fun n => (ArithmeticFunction.vonMangoldt n : ℂ)
  let s : ℂ := ⟨σ,t⟩
  have hf : Summable (LSeries.term f (σ:ℂ)) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hσ)
  have hm (n : ℕ) : ‖LSeries.term (twistedCoefficient χ) s n‖ ≤ ‖LSeries.term f (σ:ℂ) n‖ := by
    rw [show ‖LSeries.term f (σ:ℂ) n‖ = ‖LSeries.term f s n‖ by simp [LSeries.norm_term_eq,s]]
    apply LSeries.norm_term_le
    change ‖χ (n:ZMod q)*(ArithmeticFunction.vonMangoldt n:ℂ)‖ ≤ ‖(ArithmeticFunction.vonMangoldt n:ℂ)‖
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one _)
  have hn := hf.norm.of_nonneg_of_le (fun _ => norm_nonneg _) hm
  have real_term (n : ℕ) : (LSeries.term f (σ:ℂ) n).re = ‖LSeries.term f (σ:ℂ) n‖ := by
    open scoped ComplexOrder in
    have nonneg := LSeries.term_nonneg (a:=f) (n:=n)
      (show 0 ≤ f n from Complex.zero_le_real.mpr ArithmeticFunction.vonMangoldt_nonneg) σ
    exact congrArg Complex.re (Complex.eq_coe_norm_of_nonneg nonneg)
  have hzeta : LSeries f (σ:ℂ) = -logDeriv riemannZeta (σ:ℂ) := by
    simpa [logDeriv, neg_div] using
      (ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (s:=(σ:ℂ)) (by simpa using hσ))
  calc
    _ = ‖LSeries (twistedCoefficient χ) s‖ := by
      rw [LSeries_twistedCoefficient_eq χ (show 1<s.re from hσ),norm_neg]
    _ ≤ ∑' n, ‖LSeries.term f (σ:ℂ) n‖ := (norm_tsum_le_tsum_norm hn).trans (hn.tsum_le_tsum hm hf.norm)
    _ = (LSeries f (σ:ℂ)).re := by rw [LSeries,Complex.re_tsum hf]; simp_rw [real_term]
    _ = _ := congrArg Complex.re hzeta

/-- Isolate the pole of zeta on the whole real segment [1,2]. -/
theorem right_edge :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
      (η t : ℝ), 0 < η → η ≤ 1 →
        ‖logDeriv (LFunction χ) (⟨1+η,t⟩ : ℂ)‖ ≤ 1/η + D := by
  let P : DirichletCharacter ℂ 1 := 1
  let f := regularizedL P
  have analytic (z : ℂ) := analytic_regularizedL P z (mem_univ z)
  have cont : ContinuousOn (fun x : ℝ => ‖logDeriv f (x:ℂ)‖) (Icc 1 2) := by
    intro x hx
    have ne : f (x:ℂ) ≠ 0 := ExceptionalZeroCatalogue.regular_ne P _ hx.1
    have c := (analytic _).deriv.continuousAt.div (analytic _).continuousAt ne
    exact (c.comp (Complex.continuous_ofReal.continuousAt)).norm.continuousWithinAt
  obtain ⟨D,hD⟩ := isCompact_Icc.bddAbove_image cont
  refine ⟨max D 0,le_max_right _ _,?_⟩
  intro q _ χ η t hη hη'
  let x := 1+η
  have hx : 1<x := by dsimp [x]; linarith
  have hxc : (x:ℂ) ≠ 1 := by exact_mod_cast hx.ne'
  have hζ : LFunction P (x:ℂ) ≠ 0 := LFunction_ne_zero_of_one_le_re P (Or.inr hxc) hx.le
  have eqn := logDeriv_regularizedL_eq P hxc hζ
  have eqn' : -logDeriv riemannZeta (x:ℂ) = ((1/η:ℝ):ℂ)-logDeriv f (x:ℂ) := by
    rw [LFunction_modOne_eq] at eqn
    have sub : (x:ℂ)-1=(η:ℂ) := by simp [x]
    simpa [f,P,principalFlag,sub] using (show -logDeriv riemannZeta (x:ℂ) =
      principalFlag P / ((x:ℂ)-1)-logDeriv (regularizedL P) (x:ℂ) by rw [eqn]; ring)
  have H := hD (mem_image_of_mem (fun u : ℝ => ‖logDeriv f (u:ℂ)‖)
    (show x ∈ Icc 1 2 from ⟨hx.le,by dsimp [x];linarith⟩))
  refine (right_majorant χ hx t).trans ?_
  rw [eqn',sub_re,ofReal_re]
  linarith [neg_le_abs (logDeriv f (x:ℂ)).re,abs_re_le_norm (logDeriv f (x:ℂ)),le_max_left D 0]

/-- The regularized logarithmic derivative and all zeros in the disk
of radius 33/25 have an error at most 694400 times the log-height. -/
theorem local_expansion {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ) :
    ∃ Z : Finset ℂ, (∀ z, z ∈ Z ↔ z ∈ closedBall (⟨2,t⟩:ℂ) (33/25) ∧
        ExceptionalZeroCatalogue.genuine χ z) ∧
      ∀ η : ℝ, 0 < η → η ≤ 1 → let s : ℂ := ⟨1+η,t⟩
        ‖logDeriv (regularizedL χ) s - ∑ z ∈ Z, (analyticOrderNatAt (regularizedL χ) z : ℂ)/(s-z)‖
          ≤ 694400 * logHeight q t := by
  let f := regularizedL χ
  let c : ℂ := ⟨2,t⟩
  let H := 2*(q:ℝ)*(2+|t|)
  have hq : (1:ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have ht := abs_nonneg t
  have hK : 2+|t| ≤ H := by dsimp [H]; nlinarith [mul_nonneg (sub_nonneg.mpr hq) (by positivity : 0≤2+|t|)]
  have hH : 4 ≤ H := by dsimp [H]; nlinarith [mul_nonneg (by positivity : 0 ≤ (q:ℝ)) ht]
  have hqH : (q:ℝ) ≤ H := by dsimp [H]; nlinarith [mul_nonneg (by positivity : 0 ≤ (q:ℝ)) ht]
  have hpos : 0 < H := by linarith
  have hAnchor : (1/4:ℝ) ≤ ‖f c‖ := norm_regularizedL_anchor χ t
  have hn : f c ≠ 0 := norm_pos_iff.mp (by linarith)
  have growth (w : ℂ) (hw : w ∈ closedBall c (24/25*(3/2))) : ‖f w‖ ≤ H^8 * ‖f c‖ := by
    have dist := mem_closedBall_iff_norm.mp hw
    have hre := abs_le.mp ((abs_re_le_norm (w-c)).trans dist)
    change -_ ≤ w.re-2 ∧ _ at hre
    have hr : (1/8:ℝ) ≤ w.re := by linarith [hre.1]
    have hg := GoldbachGrhGrowth.norm_regularizedLFunction_le χ hr
    have hraw : ‖f w‖ ≤ 25*q*(1+‖w‖)^2 := by
      by_cases hχ : χ=1 <;> simpa [f,regularizedL,hχ] using hg
    have hcn : ‖c‖ ≤ 2+|t| := by simpa [c] using norm_le_abs_re_add_abs_im c
    have hwH : 1+‖w‖ ≤ 3*H := by linarith only [norm_le_norm_sub_add w c,dist,hcn,hK,hH]
    have h5 : (4:ℝ)^5 ≤ H^5 := pow_le_pow_left₀ (by norm_num) hH 5
    calc
      _ ≤ 25*q*(1+‖w‖)^2 := hraw
      _ ≤ 25*H*(3*H)^2 := by gcongr
      _ = 225*H^3 := by ring
      _ ≤ (H^5/4)*H^3 := mul_le_mul_of_nonneg_right (by norm_num at h5;linarith) (by positivity)
      _ = H^8*(1/4) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hAnchor (by positivity)
  obtain ⟨Z,hZ,_,approx⟩ := GoldbachGrhLogDerivative.logDeriv_partial_fraction_disk
    (c:=c) (R:=(3/2:ℝ)) (f:=f) (B:=H^8) (by norm_num)
    ((analytic_regularizedL χ).mono (subset_univ _)) hn
    (le_trans (by norm_num : (2:ℝ)≤4^8) (pow_le_pow_left₀ (by norm_num) hH 8)) growth
  refine ⟨Z,?_,?_⟩
  · intro z
    change z ∈ (↑Z : Set ℂ) ↔ _
    rw [hZ]
    change (_ ∧ f z=0) ↔ _
    rw [show (22/25*(3/2):ℝ)=33/25 by norm_num]
    exact and_congr_right fun _ => ExceptionalZeroCatalogue.regular_zero χ z
  · intro η hη hη'
    let s : ℂ := ⟨1+η,t⟩
    have sub : s-c=((η-1:ℝ):ℂ) := by apply Complex.ext <;> simp [s,c] <;> ring
    have mem : s ∈ closedBall c (83/100*(3/2)) := by
      rw [mem_closedBall_iff_norm,sub,Complex.norm_real,Real.norm_eq_abs,abs_of_nonpos (by linarith)]
      linarith
    have hs : f s ≠ 0 := ExceptionalZeroCatalogue.regular_ne χ s (by change 1≤1+η;linarith)
    have h := approx s mem hs
    rw [Real.log_pow] at h
    change _ ≤ 694400 * Real.log H
    convert h using 1 <;> norm_num <;> ring

noncomputable def kernel (s z : ℂ) : ℝ := (s-z).re / Complex.normSq (s-z)

theorem kernel_eq (s z : ℂ) (n : ℕ) :
    ((n:ℂ)/(s-z)).re = n*kernel s z := by
  simp [kernel,Complex.div_re,mul_div_assoc]

theorem disk_potential :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
      (t η : ℝ), 0 < η → η ≤ 1 → ∀ S : Finset ℂ,
        (∀ z ∈ S, z ∈ closedBall (⟨2,t⟩:ℂ) (33/25) ∧ ExceptionalZeroCatalogue.genuine χ z) →
        let s : ℂ := ⟨1+η,t⟩
        ∑ z ∈ S, (analyticOrderNatAt (regularizedL χ) z : ℝ)*kernel s z ≤
          (logDeriv (LFunction χ) s).re + (principalFlag χ/(s-1)).re + 694400*logHeight q t ∧
        ∑ z ∈ S, (analyticOrderNatAt (regularizedL χ) z : ℝ)*kernel s z ≤
          2/η + D + 694400*logHeight q t := by
  obtain ⟨D,hD,right⟩ := right_edge
  refine ⟨D,hD,?_⟩
  intro q _ χ t η hη hη' S hS s
  obtain ⟨Z,mem,apr⟩ := local_expansion χ t
  have hs : 1<s.re := by change 1<1+η;linarith
  have hn : s ≠ 1 := fun e => (by simpa [e] using hs : False)
  have hL := LFunction_ne_zero_of_one_le_re χ (Or.inr hn) hs.le
  let weight := fun z => (analyticOrderNatAt (regularizedL χ) z : ℝ)*kernel s z
  have sub : S ⊆ Z := fun z hz => (mem z).mpr (hS z hz)
  have hw (z : ℂ) (hz : z ∈ Z) : 0 ≤ weight z := by
    have h := ((mem z).mp hz).2
    have hzre : z.re < 1 := lt_of_not_ge fun e => ExceptionalZeroCatalogue.regular_ne χ z e
      ((ExceptionalZeroCatalogue.regular_zero χ z).mpr h)
    exact mul_nonneg (Nat.cast_nonneg _) (div_nonneg (sub_nonneg.mpr (hzre.trans hs).le) (normSq_nonneg _))
  have cmp : ∑ z ∈ S, weight z ≤ ∑ z ∈ Z, weight z :=
    Finset.sum_le_sum_of_subset_of_nonneg sub fun z hz _ => hw z hz
  let total : ℂ := ∑ z ∈ Z, (analyticOrderNatAt (regularizedL χ) z : ℂ)/(s-z)
  have reTot : total.re = ∑ z ∈ Z, weight z := by simp [total,Complex.re_sum,kernel_eq,weight]
  have major := abs_re_le_norm (logDeriv (regularizedL χ) s-total)
  have below := (abs_le.mp (major.trans (apr η hη hη'))).1
  rw [sub_re,reTot,logDeriv_regularizedL_eq χ hn hL,add_re] at below
  have bound : ∑ z ∈ S, weight z ≤ (logDeriv (LFunction χ) s).re +
      (principalFlag χ/(s-1)).re + 694400*logHeight q t := by linarith
  refine ⟨bound,?_⟩
  have flag : ‖principalFlag χ‖ ≤ 1 := by by_cases e : χ=1 <;> simp [principalFlag,e]
  have dist : η ≤ ‖s-1‖ := by
    have a := (le_abs_self (s-1).re).trans (abs_re_le_norm (s-1))
    simpa [s] using a
  have pf := (re_le_norm (principalFlag χ/(s-1))).trans
    (by rw [norm_div];exact div_le_div₀ zero_le_one flag hη dist : ‖principalFlag χ/(s-1)‖ ≤ 1/η)
  have r := (re_le_norm (logDeriv (LFunction χ) s)).trans (right q χ η t hη hη')
  change ∑ z ∈ S, weight z ≤ _
  linarith [show (2:ℝ)/η = 1/η+1/η by ring]

/-- Each near-one zero contributes almost its full multiplicity to the
Poisson kernel at horizontal distance 8h. -/
theorem near_kernel {t h : ℝ} (hh : 0<h) {z : ℂ}
    (lo : 1-h ≤ z.re) (hi : z.re ≤ 1) (ht : |z.im-t| ≤ h) :
    3 ≤ 32*h*kernel (⟨1+8*h,t⟩:ℂ) z := by
  let a := 1+8*h-z.re
  let b := t-z.im
  have a0 : 8*h ≤ a := by dsimp [a];linarith
  have a1 : a ≤ 9*h := by dsimp [a];linarith
  have ap : 0 < a := by linarith
  have b1 : |b| ≤ h := by simpa [b,abs_sub_comm] using ht
  have sq1 := pow_le_pow_left₀ ap.le a1 2
  have sq2 := (sq_le_sq₀ (abs_nonneg b) hh.le).mpr b1
  rw [sq_abs] at sq2
  change 3 ≤ 32*h*(a/(a*a+b*b))
  rw [← mul_div_assoc,le_div_iff₀ (add_pos_of_pos_of_nonneg (mul_pos ap ap) (mul_self_nonneg b))]
  nlinarith only [sq1,sq2,mul_le_mul_of_nonneg_left a0 hh.le,sq_nonneg h]

theorem rectangle_mass :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
      (t h : ℝ), 0<h → h≤1/8 → ∀ S : Finset ℂ,
      (∀ z ∈ S, 1-h ≤ z.re ∧ |z.im-t| ≤ h ∧ ExceptionalZeroCatalogue.genuine χ z) →
      let M := (∑ z ∈ S, analyticOrderNatAt (regularizedL χ) z : ℕ)
      3*(M:ℝ) ≤ 8+32*h*(D+694400*logHeight q t) ∧
        (χ ≠ 1 → 3*(M:ℝ) ≤ 4+32*h*(D+694400*logHeight q t)) := by
  obtain ⟨D,hD,potential⟩ := disk_potential
  obtain ⟨A,hA,right⟩ := right_edge
  refine ⟨max D A,hD.trans (le_max_left _ _),?_⟩
  intro q _ χ t h hh hh' S hS M
  let s : ℂ := ⟨1+8*h,t⟩
  have upper (z : ℂ) (hz : z ∈ S) : z.re ≤ 1 := le_of_lt (lt_of_not_ge fun e =>
    ExceptionalZeroCatalogue.regular_ne χ z e ((ExceptionalZeroCatalogue.regular_zero χ z).mpr (hS z hz).2.2))
  have inside (z : ℂ) (hz : z ∈ S) :
      z ∈ closedBall (⟨2,t⟩:ℂ) (33/25) ∧ ExceptionalZeroCatalogue.genuine χ z := by
    refine ⟨?_,(hS z hz).2.2⟩
    rw [mem_closedBall_iff_norm]
    have k := norm_le_abs_re_add_abs_im (z-(⟨2,t⟩:ℂ))
    change ‖_‖ ≤ |z.re-2|+|z.im-t| at k
    rw [abs_of_nonpos (by linarith [upper z hz] : z.re-2 ≤ 0)] at k
    linarith [(hS z hz).1,(hS z hz).2.1]
  let W := ∑ z ∈ S, (analyticOrderNatAt (regularizedL χ) z:ℝ)*kernel s z
  have weighted : 3*(M:ℝ) ≤ 32*h*W := by
    dsimp only [M,W]
    push_cast
    rw [Finset.mul_sum,Finset.mul_sum]
    refine Finset.sum_le_sum fun z hz => ?_
    have k := near_kernel hh (hS z hz).1 (upper z hz) (hS z hz).2.1
    calc
      _ ≤ (32*h*kernel s z)*(analyticOrderNatAt (regularizedL χ) z:ℝ) :=
        mul_le_mul_of_nonneg_right k (Nat.cast_nonneg _)
      _ = _ := by ring
  have h8 : 0<8*h := by positivity
  have h8' : 8*h≤1 := by linarith
  obtain ⟨p₁,p₂⟩ := potential q χ t (8*h) h8 h8' S inside
  have simp2 : 32*h*(2/(8*h))=8 := by field_simp;ring
  have simp1 : 32*h*(1/(8*h))=4 := by field_simp;ring
  constructor
  · calc
      _ ≤ 32*h*W := weighted
      _ ≤ 32*h*(2/(8*h)+D+694400*logHeight q t) := mul_le_mul_of_nonneg_left p₂ (by positivity)
      _ = 8+32*h*(D+694400*logHeight q t) := by linarith only [simp2]
      _ ≤ _ := by gcongr; exact le_max_left _ _
  · intro hn
    have P := (re_le_norm (logDeriv (LFunction χ) s)).trans (right q χ (8*h) t h8 h8')
    change W ≤ (logDeriv (LFunction χ) s).re + (principalFlag χ/(s-1)).re + _ at p₁
    simp [principalFlag,hn] at p₁
    have p : W ≤ 1/(8*h)+A+694400*logHeight q t := by linarith
    calc
      _ ≤ 32*h*W := weighted
      _ ≤ 32*h*(1/(8*h)+A+694400*logHeight q t) := mul_le_mul_of_nonneg_left p (by positivity)
      _ = 4+32*h*(A+694400*logHeight q t) := by linarith only [simp1]
      _ ≤ _ := by gcongr; exact le_max_right _ _

/-- In a logarithmically shrinking box every nonprincipal character
has at most one zero counted with multiplicity, uniformly in height. -/
theorem isolated :
    ∃ c : ℝ, 0<c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
      (t : ℝ) (S : Finset ℂ), let h := c/logHeight q t
      (∀ z ∈ S, 1-h ≤ z.re ∧ |z.im-t| ≤ h ∧ ExceptionalZeroCatalogue.genuine χ z) →
      let M := ∑ z ∈ S, analyticOrderNatAt (regularizedL χ) z
      M ≤ 2 ∧ (χ ≠ 1 → M ≤ 1) := by
  obtain ⟨D,hD,rect⟩ := rectangle_mass
  let A := D+694401
  have hA : 1 ≤ A := by dsimp [A];linarith
  have hAp : 0<A := by linarith
  let c := 1/(64*A)
  have hc : 0<c := by dsimp [c];positivity
  refine ⟨c,hc,?_⟩
  intro q _ χ t S h hS M
  let L := logHeight q t
  have hL : 1 ≤ L := logHeight_ge_one q t
  have hLp : 0<L := by linarith
  have hh : 0<h := div_pos hc hLp
  have hh' : h≤1/8 := by
    change 1/(64*A)/L ≤ 1/8
    rw [div_div]
    apply one_div_le_one_div_of_le (by norm_num)
    nlinarith [one_le_mul_of_one_le_of_one_le hA hL]
  have bound : D+694400*L ≤ A*L := by
    dsimp [A];nlinarith [mul_nonneg hD (sub_nonneg.mpr hL)]
  have cost : 32*h*(D+694400*L) ≤ 1/2 := calc
    _ ≤ 32*h*(A*L) := mul_le_mul_of_nonneg_left bound (by positivity)
    _ = 1/2 := by change 32*(1/(64*A)/L)*(A*L)=_;field_simp;ring
  have ⟨p₁,p₂⟩ := rect q χ t h hh hh' S hS
  change 3*(M:ℝ) ≤ 8+32*h*(D+694400*L) at p₁
  constructor
  · by_contra! H
    have H' : (3:ℝ) ≤ M := by exact_mod_cast (show 3≤M by omega)
    linarith
  · intro hn
    have p : 3*(M:ℝ) ≤ 4+32*h*(D+694400*L) := p₂ hn
    by_contra! H
    have H' : (2:ℝ) ≤ M := by exact_mod_cast (show 2≤M by omega)
    linarith

end Conjectures.Goldbach.NearOneZeroMultiplicity

open Conjectures.Goldbach.NearOneZeroMultiplicity in
theorem Conjectures.Goldbach.NearOneZeroMultiplicity :
by
  classical
  let L := fun (q : ℕ) (t : ℝ) => Real.log (2*(q:ℝ)*(2+|t|))
  let genuine := fun {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (z : ℂ) =>
    (χ ≠ 1 ∨ z ≠ 1) ∧ DirichletCharacter.LFunction χ z=0
  let f := fun {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) =>
    if χ=1 then DirichletCharacter.LFunctionTrivChar₁ q else DirichletCharacter.LFunction χ
  let M := fun {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (S : Finset ℂ) =>
    ∑ z ∈ S, analyticOrderNatAt (f χ) z
  let box := fun {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (t h : ℝ) (S : Finset ℂ) =>
    ∀ z ∈ S, 1-h ≤ z.re ∧ |z.im-t| ≤ h ∧ genuine χ z
  exact
    (∃ D : ℝ, 0 ≤ D ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
      (η t : ℝ), 0 < η → η ≤ 1 →
        ‖logDeriv (DirichletCharacter.LFunction χ) (⟨1+η,t⟩ : ℂ)‖ ≤ 1/η+D) ∧
    (∃ D : ℝ, 0 ≤ D ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
      (t h : ℝ), 0<h → h≤1/8 → ∀ S : Finset ℂ, box χ t h S →
        3*(M χ S:ℝ) ≤ 8+32*h*(D+694400*L q t) ∧
        (χ ≠ 1 → 3*(M χ S:ℝ) ≤ 4+32*h*(D+694400*L q t))) ∧
    (∃ c : ℝ, 0<c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ)
      (S : Finset ℂ), box χ t (c/L q t) S → M χ S ≤ 2 ∧ (χ ≠ 1 → M χ S ≤ 1)) := by
  exact ⟨right_edge,rectangle_mass,isolated⟩
