import Conjectures.Goldbach.ExceptionalQuadraticUniqueness

/-! A uniform zero-free strip with one possible real quadratic zero.
The coefficients of the derivative version of the classical 3,4,1
inequality retain their sign for every Euler factor. -/

namespace Conjectures.Goldbach.DirichletExceptionalZeroRegion

open Complex DirichletCharacter Metric Set
open _root_.Goldbach GoldbachSmoothing
open ExceptionalZeroCatalogue NearOneZeroMultiplicity
open scoped Classical

private theorem positive_polynomial (z : ℂ) (hz : ‖z‖ ≤ 1) :
    0 ≤ 3+4*z.re+(z*z).re := by
  have sq := pow_le_pow_left₀ (norm_nonneg z) hz 2
  rw [Complex.sq_norm,Complex.normSq_apply] at sq
  rw [Complex.mul_re]
  nlinarith [sq_nonneg (1+z.re)]

private theorem three_terms {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (x t : ℝ) (n : ℕ) :
    let f : ℕ → ℂ := fun k => (ArithmeticFunction.vonMangoldt k:ℂ)
    0 ≤ 3*(LSeries.term f (x:ℂ) n).re +
      4*(LSeries.term (twistedCoefficient χ) (⟨x,t⟩:ℂ) n).re +
      (LSeries.term (twistedCoefficient (χ*χ)) (⟨x,2*t⟩:ℂ) n).re := by
  intro f
  by_cases hn : n=0
  · subst n; simp
  have nc : (n:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  let l := Real.log (n:ℝ)
  let a := Real.exp (-(l*x))
  let phase := fun u : ℝ => Complex.exp (((-(l*u):ℝ):ℂ)*I)
  have factor (u : ℝ) : ((n:ℂ)^(⟨x,u⟩:ℂ))⁻¹ = (a:ℂ)*phase u := by
    rw [cpow_def_of_ne_zero nc,← Complex.exp_neg]
    dsimp only [a,phase]
    rw [Complex.ofReal_exp,← Complex.exp_add,← Complex.natCast_log]
    congr 1
    apply Complex.ext <;> simp [l,mul_re,mul_im]
    all_goals ring
  have ph2 : phase (2*t) = phase t*phase t := by
    dsimp only [phase];rw [← Complex.exp_add];congr 1;push_cast;ring
  have ph0 : phase 0=1 := by simp [phase]
  let d : ℝ := ArithmeticFunction.vonMangoldt n*a
  let u : ℂ := χ (n:ZMod q)*phase t
  have ud : ‖u‖ ≤ 1 := by
    dsimp only [u]
    rw [norm_mul,show ‖phase t‖=1 by simp [phase,Complex.norm_exp],mul_one]
    exact χ.norm_le_one _
  have e0 : LSeries.term f (x:ℂ) n = (d:ℂ) := by
    rw [LSeries.term_of_ne_zero hn,div_eq_mul_inv,show (x:ℂ)=(⟨x,0⟩:ℂ) from rfl,factor,ph0,mul_one]
    simp [d,f]
  have e1 : LSeries.term (twistedCoefficient χ) (⟨x,t⟩:ℂ) n = (d:ℂ)*u := by
    rw [LSeries.term_of_ne_zero hn,div_eq_mul_inv,factor]
    simp [twistedCoefficient,d,u];ring
  have e2 : LSeries.term (twistedCoefficient (χ*χ)) (⟨x,2*t⟩:ℂ) n = (d:ℂ)*(u*u) := by
    rw [LSeries.term_of_ne_zero hn,div_eq_mul_inv,factor,ph2]
    simp [twistedCoefficient,d,u,MulChar.mul_apply];ring
  rw [e0,e1,e2]
  have scale (v : ℂ) : ((d:ℂ)*v).re=d*v.re := by simp [Complex.mul_re]
  simp only [ofReal_re,scale]
  have dn : 0 ≤ d := mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.exp_pos _).le
  linarith only [mul_nonneg dn (positive_polynomial u ud)]

theorem three_four_one {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {x : ℝ} (hx : 1 < x) (t : ℝ) :
    3*(logDeriv riemannZeta (x:ℂ)).re + 4*(logDeriv (LFunction χ) (⟨x,t⟩:ℂ)).re +
      (logDeriv (LFunction (χ*χ)) (⟨x,2*t⟩:ℂ)).re ≤ 0 := by
  let f : ℕ → ℂ := fun n => (ArithmeticFunction.vonMangoldt n:ℂ)
  have h0 : LSeriesSummable f (x:ℂ) := ArithmeticFunction.LSeriesSummable_vonMangoldt hx
  have h1 : LSeriesSummable (twistedCoefficient χ) (⟨x,t⟩:ℂ) := χ.LSeriesSummable_twist_vonMangoldt hx
  have h2 : LSeriesSummable (twistedCoefficient (χ*χ)) (⟨x,2*t⟩:ℂ) :=
    (χ*χ).LSeriesSummable_twist_vonMangoldt hx
  have hzeta : LSeries f (x:ℂ) = -logDeriv riemannZeta (x:ℂ) := by
    simpa [logDeriv,neg_div] using ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div
      (s:=(x:ℂ)) (by simpa using hx)
  have total := ((((Complex.hasSum_re h0.hasSum).mul_left 3).add
    ((Complex.hasSum_re h1.hasSum).mul_left 4)).add (Complex.hasSum_re h2.hasSum)).tsum_eq
  have pos := (tsum_nonneg (fun n => three_terms χ x t n)).trans_eq total
  change 0 ≤ 3*(LSeries f (x:ℂ)).re + 4*(LSeries (twistedCoefficient χ) (⟨x,t⟩:ℂ)).re +
    (LSeries (twistedCoefficient (χ*χ)) (⟨x,2*t⟩:ℂ)).re at pos
  rw [hzeta,LSeries_twistedCoefficient_eq χ hx,LSeries_twistedCoefficient_eq (χ*χ) hx] at pos
  simp only [neg_re] at pos
  linarith

private theorem log_double (q : ℕ) [NeZero q] (t : ℝ) :
    logHeight q (2*t) ≤ 2*logHeight q t := by
  let H := 2*(q:ℝ)*(2+|t|)
  have Q1 : (1:ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have H2 : 2 ≤ H := by
    dsimp [H]
    nlinarith [mul_nonneg (Nat.cast_nonneg q) (abs_nonneg t)]
  change Real.log (2*(q:ℝ)*(2+|2*t|)) ≤ 2*Real.log H
  apply le_trans _ (show Real.log (H^2) = 2*Real.log H by simp).le
  apply Real.log_le_log (by positivity)
  rw [abs_mul,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  calc
    _ ≤ 2*H := by dsimp [H]; linarith only [Nat.cast_nonneg (α:=ℝ) q]
    _ ≤ H^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr H2) (show 0 ≤ H by linarith)]

private theorem imaginary_pole {h t : ℝ} (hp : 0 < h) (large : 64*h ≤ |t|) :
    (1/((⟨1+16*h,t⟩:ℂ)-1)).re ≤ 1/(256*h) := by
  have square := (sq_le_sq₀ (show 0 ≤ 64*h by positivity) (abs_nonneg t)).mpr large
  rw [sq_abs] at square
  rw [Complex.div_re,Complex.normSq_apply]
  simp only [sub_re,sub_im,one_re,one_im,add_sub_cancel_left,sub_zero,one_mul,zero_mul,
    zero_div,add_zero]
  apply (div_le_div_iff₀ (add_pos_of_pos_of_nonneg (mul_pos (by positivity) (by positivity))
    (mul_self_nonneg _)) (by positivity)).mpr
  nlinarith only [square,sq_nonneg h]

/-- A near-one zero of any character has quadratic character and
has very small height. Both conclusions hold in the same strip. -/
theorem zero_characteristics :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      ∀ (z : ℂ) (h : ℝ), 0 < h → h ≤ c/logHeight q z.im →
      1-h ≤ z.re → genuine χ z → χ.IsQuadratic ∧ |z.im| < 64*h := by
  obtain ⟨_,_,pot⟩ := disk_potential
  obtain ⟨D,hD,right⟩ := right_edge
  let A := 3*D+6*694400+1
  have A1 : 1 ≤ A := by dsimp [A];linarith
  have Ap : 0 < A := by linarith
  let c := 1/(128*A)
  refine ⟨c,by dsimp [c];positivity,?_⟩
  intro q _ χ z h hp small near zero
  let t := z.im
  let L := logHeight q t
  let s : ℂ := ⟨1+16*h,t⟩
  let s₂ : ℂ := ⟨1+16*h,2*t⟩
  have L1 : 1 ≤ L := logHeight_ge_one q t
  have Lp : 0 < L := by linarith
  have bound : h ≤ 1/(128*(A*L)) := by
    convert small using 1
    dsimp [c,L,t];rw [div_div];ring
  have budget : h*(128*(A*L)) ≤ 1 := (le_div_iff₀ (by positivity)).mp bound
  have smallH : h ≤ 1/16 := by
    apply bound.trans
    apply one_div_le_one_div_of_le (by norm_num)
    linarith [one_le_mul_of_one_le_of_one_le A1 L1]
  have ep : 0 < 16*h := by positivity
  have e1 : 16*h ≤ 1 := by linarith
  have zhi : z.re ≤ 1 := le_of_lt (lt_of_not_ge fun hz => regular_ne χ z hz ((regular_zero χ z).mpr zero))
  have mem : z ∈ closedBall (⟨2,t⟩:ℂ) (33/25) := by
    rw [mem_closedBall_iff_norm]
    have k := norm_le_abs_re_add_abs_im (z-(⟨2,t⟩:ℂ))
    change ‖_‖ ≤ |z.re-2|+|z.im-z.im| at k
    rw [sub_self,abs_zero,add_zero,abs_of_nonpos (by linarith : z.re-2 ≤ 0)] at k
    linarith
  have ab : 0 < 1+16*h-z.re := by linarith
  have k : 1 ≤ 17*h*kernel s z := by
    change 1 ≤ 17*h*((1+16*h-z.re)/((1+16*h-z.re)*(1+16*h-z.re)+(t-z.im)*(t-z.im)))
    rw [show t-z.im=0 from sub_self _,zero_mul,add_zero,← mul_div_assoc,
      le_div_iff₀ (mul_pos ab ab)]
    nlinarith only [mul_nonneg (show 0 ≤ 17*h-(1+16*h-z.re) by linarith) ab.le]
  have kn : 0 ≤ kernel s z := div_nonneg ab.le (normSq_nonneg _)
  have multiplicity : (1:ℝ) ≤ analyticOrderNatAt (regularizedL χ) z := by
    exact_mod_cast (order_positive χ zero).1
  have p1 := (pot q χ t (16*h) ep e1 {z} (by
    intro u hu;obtain rfl := Finset.mem_singleton.mp hu;exact ⟨mem,zero⟩)).1
  change _ ≤ (logDeriv (LFunction χ) s).re + (principalFlag χ/(s-1)).re + 694400*L at p1
  simp only [Finset.sum_singleton] at p1
  have single := k.trans (mul_le_mul_of_nonneg_left ((le_mul_of_one_le_left kn multiplicity).trans p1)
    (by positivity : 0 ≤ 17*h))
  by_contra absent
  have big (quad : χ.IsQuadratic) : 64*h ≤ |t| := le_of_not_gt fun hi => absent ⟨quad,hi⟩
  have pole1 : (principalFlag χ/(s-1)).re ≤ 1/(256*h) := by
    by_cases principal : χ=1
    · have quad : χ.IsQuadratic := MulChar.isQuadratic_iff_sq_eq_one.mpr (by simp [principal])
      simpa [principalFlag,principal,s] using imaginary_pole hp (big quad)
    · simp [principalFlag,principal]
      positivity
  have pole2 : (principalFlag (χ*χ)/(s₂-1)).re ≤ 1/(256*h) := by
    by_cases pair : χ*χ=1
    · have quad : χ.IsQuadratic := MulChar.isQuadratic_iff_sq_eq_one.mpr (by simpa [pow_two] using pair)
      have twice : 64*h ≤ |2*t| := by
        rw [abs_mul,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
        linarith [big quad,abs_nonneg t]
      simpa [principalFlag,pair,s₂] using imaginary_pole hp twice
    · simp [principalFlag,pair]
      positivity
  have p2 := (pot q (χ*χ) (2*t) (16*h) ep e1 ∅ (by simp)).1
  change _ ≤ (logDeriv (LFunction (χ*χ)) s₂).re + (principalFlag (χ*χ)/(s₂-1)).re +
    694400*logHeight q (2*t) at p2
  simp only [Finset.sum_empty] at p2
  let x := 1+16*h
  have hx : 1 < x := by dsimp [x];linarith
  have tri : 3*(logDeriv riemannZeta (x:ℂ)).re+4*(logDeriv (LFunction χ) s).re+
    (logDeriv (LFunction (χ*χ)) s₂).re ≤ 0 := three_four_one χ hx t
  have R := right 1 (1 : DirichletCharacter ℂ 1) (16*h) 0 ep e1
  rw [LFunction_modOne_eq] at R
  have pole : -(logDeriv riemannZeta (x:ℂ)).re ≤ 1/(16*h)+D :=
    ((neg_le_abs _).trans (abs_re_le_norm _)).trans R
  have log2 : logHeight q (2*t) ≤ 2*L := log_double q t
  have cost : 3*D+6*694400*L ≤ A*L := by
    dsimp [A];nlinarith [mul_nonneg hD (sub_nonneg.mpr L1)]
  have total : 4*((logDeriv (LFunction χ) s).re+(principalFlag χ/(s-1)).re+694400*L) ≤
      3*(1/(16*h))+5*(1/(256*h))+A*L := by
    linarith only [pole,p2,pole1,pole2,tri,log2,cost]
  have fees := mul_le_mul_of_nonneg_left total (by positivity : 0 ≤ 17*h)
  have factor : (17*h)*(3*(1/(16*h))+5*(1/(256*h)))=901/256 := by field_simp;ring
  linarith only [single,budget,fees,factor]

private theorem logHeight_le {r Q : ℕ} [NeZero r] {u T : ℝ}
    (leQ : r ≤ Q) (ht : |u| ≤ T) : logHeight r u ≤ logHeight Q T := by
  have rp : (0:ℝ) < r := by exact_mod_cast NeZero.pos r
  have rq : (r:ℝ) ≤ Q := by exact_mod_cast leQ
  have hT := (abs_nonneg u).trans ht
  unfold logHeight
  rw [abs_of_nonneg hT]
  exact Real.log_le_log (by positivity) (by gcongr)

/-- Across every primitive conductor up to Q and at all heights up to T,
the classical logarithmic strip contains at most one genuine zero, and
its character, ordinate, and analytic multiplicity are determined. -/
theorem full_page :
    ∃ c : ℝ, 0 < c ∧ ∀ (Q r s : ℕ) [NeZero r] [NeZero s],
      r ≤ Q → s ≤ Q → ∀ (T : ℝ), 0 ≤ T →
      ∀ (χ : DirichletCharacter ℂ r) (ψ : DirichletCharacter ℂ s),
      χ.IsPrimitive → ψ.IsPrimitive → ∀ z w : ℂ, let h := c/logHeight Q T
        1-h ≤ z.re → |z.im| ≤ T → genuine χ z →
        1-h ≤ w.re → |w.im| ≤ T → genuine ψ w →
        χ.IsQuadratic ∧ χ ≠ 1 ∧ r=s ∧ HEq χ ψ ∧ z=w ∧ z.im=0 ∧
          analyticOrderNatAt (LFunction χ) z=1 := by
  obtain ⟨a,ha,profile⟩ := zero_characteristics
  obtain ⟨b,hb,page⟩ := ExceptionalQuadraticUniqueness.landau_page
  obtain ⟨δ,hδ,compact⟩ := bounded_strip 1 1
  let c := min a (min (b/64) (min δ (1/64)))
  have hc : 0 < c := lt_min ha (lt_min (by positivity) (lt_min hδ (by norm_num)))
  have ca : c ≤ a := min_le_left _ _
  have cb : c ≤ b/64 := (min_le_right _ _).trans (min_le_left _ _)
  have cd : c ≤ δ := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have c1 : c ≤ 1/64 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨c,hc,?_⟩
  intro Q r s _ _ hr hs T hT χ ψ pr ps z w h hz hiz zz hw hiw zw
  haveI : NeZero Q := ⟨((NeZero.pos r).trans_le hr).ne'⟩
  let L := logHeight Q T
  have L1 : 1 ≤ L := logHeight_ge_one Q T
  have Lp : 0 < L := zero_lt_one.trans_le L1
  have hp : 0 < h := div_pos hc Lp
  have hmax : h ≤ c := div_le_self hc.le L1
  have info (n : ℕ) [NeZero n] (hn : n ≤ Q) (θ : DirichletCharacter ℂ n) (prim : θ.IsPrimitive)
      (u : ℂ) (hu : 1-h ≤ u.re) (ht : |u.im| ≤ T) (zu : genuine θ u) :
      θ.IsQuadratic ∧ θ ≠ 1 ∧ |u.im| ≤ 64*h := by
    have pos : 0 < logHeight n u.im := zero_lt_one.trans_le (logHeight_ge_one n u.im)
    have localWidth : h ≤ a/logHeight n u.im := by
      change c/L ≤ _
      calc
        _ ≤ c/logHeight n u.im := div_le_div_of_nonneg_left hc.le pos (logHeight_le hn ht)
        _ ≤ _ := div_le_div_of_nonneg_right ca pos.le
    obtain ⟨quad,low⟩ := profile n θ u h hp localWidth hu zu
    refine ⟨quad,?_,low.le⟩
    intro principal
    have level : 1 = n := by simpa only [principal,IsPrimitive,conductor_one] using prim
    have smallT : |u.im| ≤ 1 := by linarith [hmax.trans c1]
    exact compact n level.symm.le θ u smallT (by linarith [hmax.trans cd]) zu
  obtain ⟨qr,nχ,zt⟩ := info r hr χ pr z hz hiz zz
  obtain ⟨qs,nψ,wt⟩ := info s hs ψ ps w hw hiw zw
  have ln : Real.log (4*(Q:ℝ)) = logHeight Q 0 := by
    simp only [logHeight,abs_zero,add_zero];congr 1;ring
  have lp : 0 < Real.log (4*(Q:ℝ)) := ln ▸ zero_lt_one.trans_le (logHeight_ge_one Q 0)
  have sup : Real.log (4*(Q:ℝ)) ≤ L := by
    rw [ln];exact logHeight_le (le_refl Q) (by simpa using hT)
  have width : 64*h ≤ b/Real.log (4*(Q:ℝ)) := by
    change 64*(c/L) ≤ _
    rw [← mul_div_assoc]
    calc
      _ ≤ b/L := div_le_div_of_nonneg_right (by linarith only [cb]) Lp.le
      _ ≤ _ := div_le_div_of_nonneg_left hb.le lp sup
  have hw' : h ≤ b/Real.log (4*(Q:ℝ)) := by linarith
  exact ⟨qr,nχ,page Q r s hr hs χ ψ pr ps qr qs nχ nψ z w
    (by linarith) (zt.trans width) zz (by linarith) (wt.trans width) zw⟩

end Conjectures.Goldbach.DirichletExceptionalZeroRegion

theorem Conjectures.Goldbach.DirichletExceptionalZeroRegion :
by
  classical
  let Z := fun {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r) (z : ℂ) =>
    (χ ≠ 1 ∨ z ≠ 1) ∧ DirichletCharacter.LFunction χ z=0
  exact ∃ c : ℝ, 0<c ∧ ∀ (Q r s : ℕ) [NeZero r] [NeZero s],
    r≤Q → s≤Q → ∀ (T : ℝ), 0≤T →
    ∀ (χ : DirichletCharacter ℂ r) (ψ : DirichletCharacter ℂ s),
    χ.IsPrimitive → ψ.IsPrimitive → ∀ z w : ℂ,
      let h := c/Real.log (2*(Q:ℝ)*(2+|T|))
      1-h≤z.re → |z.im|≤T → Z χ z → 1-h≤w.re → |w.im|≤T → Z ψ w →
      χ.IsQuadratic ∧ χ ≠ 1 ∧ r=s ∧ HEq χ ψ ∧ z=w ∧ z.im=0 ∧
        analyticOrderNatAt (DirichletCharacter.LFunction χ) z=1 :=
  DirichletExceptionalZeroRegion.full_page
