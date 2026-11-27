import Conjectures.Goldbach.ExceptionalZeroTwistedWindow
import Conjectures.Goldbach.EstermannAlmostAllPolylog

/-! A character-uniform estimate for the first Riesz mean. The integration
line on the right is allowed to approach one with x. This keeps the tails
proportional to x^(1+η); the common possible exceptional residue is explicit. -/

namespace Conjectures.Goldbach.ExceptionalZeroRieszEstimate

open Complex DirichletCharacter MeasureTheory Set Filter
open _root_.Goldbach GoldbachSmoothing GoldbachTwistedMellin
open ExceptionalZeroCatalogue ExceptionalZeroInducedLevels ExceptionalZeroContour ExceptionalZeroTwistedWindow
open Conjectures.Goldbach.EstermannAlmostAllPolylog_aux.OAI.LargePrimeGaps (rieszSum rieszSum_mellinInv)
open scoped Classical Topology Interval

noncomputable def weight (x : ℝ) (s : ℂ) := (x:ℂ)^s/(s*(s+1))

noncomputable def integrand {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (x : ℝ) (s : ℂ) :=
  contourLog χ s*weight x s

private theorem weight_analytic {x : ℝ} (hx : 0<x) {s : ℂ} (hs : 0<s.re) :
    AnalyticAt ℂ (weight x) s := by
  have : NeZero (x:ℂ) := ⟨ofReal_ne_zero.mpr hx.ne'⟩
  have n0 : s ≠ 0 := fun e => (by simp [e] at hs)
  have n1 : s+1 ≠ 0 := by
    intro e
    have := congrArg Complex.re e
    simp at this
    linarith
  exact ((differentiable_const_cpow_of_neZero (x:ℂ)).analyticAt _).div
    (by fun_prop) (mul_ne_zero n0 n1)

theorem weight_bound {x : ℝ} (hx : 0<x) {s : ℂ} (hs : 1/2 ≤ s.re) :
    ‖weight x s‖ ≤ 8*x^s.re/(1+s.im^2) := by
  have s0 : 1/2 ≤ ‖s‖ := hs.trans (re_le_norm _)
  have s1 : 1/2 ≤ ‖s+1‖ := by
    have re := re_le_norm (s+1);simp only [add_re,one_re] at re;linarith
  have p0 : (1/2:ℝ)*(1/2) ≤ ‖s‖*‖s+1‖ := mul_le_mul s0 s1 (by norm_num) (norm_nonneg _)
  have p1 : s.im^2 ≤ ‖s‖*‖s+1‖ := by
    have i1 : |s.im| ≤ ‖s+1‖ := by simpa using abs_im_le_norm (s+1)
    simpa only [←sq,sq_abs] using mul_le_mul (abs_im_le_norm s) i1 (abs_nonneg _) (norm_nonneg _)
  have pos : 0<‖s‖*‖s+1‖ := by linarith
  rw [weight,norm_div,norm_mul,norm_cpow_eq_rpow_re_of_pos hx]
  apply (div_le_div_iff₀ pos (by positivity)).mpr
  have den : 1+s.im^2 ≤ 8*(‖s‖*‖s+1‖) := by linarith only [p0,p1]
  nlinarith only [mul_nonneg (Real.rpow_nonneg hx.le s.re) (sub_nonneg.mpr den)]

private theorem contour_right_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1<s.re) :
    contourLog χ s = LSeries (twistedCoefficient χ) s := by
  have off : s ≠ 1 := fun e => (by simp [e] at hs)
  have ne := LFunction_ne_zero_of_one_le_re χ (Or.inr off) hs.le
  rw [contourLog,logDeriv_regularizedL_eq χ off ne,LSeries_twistedCoefficient_eq χ hs]
  ring

private theorem right_inverse {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x k : ℝ} (hx : 0<x)
    (hk : 1<k) :
    rieszSum (twistedCoefficient χ) x = (1/(2*Real.pi)) • ∫ t : ℝ, integrand χ x (line k t) := by
  rw [← rieszSum_mellinInv hk.le hx (twistedCoefficient χ) (χ.LSeriesSummable_twist_vonMangoldt hk)]
  unfold mellinInv
  apply congrArg (fun v : ℂ => (1/(2*Real.pi):ℝ) • v)
  apply integral_congr_ae
  filter_upwards with t
  have hz : 1<(line k t).re := by simpa using hk
  dsimp only [integrand,weight]
  rw [contour_right_eq χ hz]
  change (((1/x:ℝ):ℂ)^(-line k t))*(LSeries (twistedCoefficient χ) (line k t)/_) = _
  rw [one_div,Complex.ofReal_inv,inv_cpow_ofReal_nonneg hx.le,cpow_neg,inv_inv]
  unfold line
  ring

private theorem right_integrable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x k : ℝ} (hx : 0<x)
    (hk : 1<k) : Integrable (fun t : ℝ => integrand χ x (line k t)) := by
  have eqn (t : ℝ) : integrand χ x (line k t) = LSeries (twistedCoefficient χ) (line k t)*weight x (line k t) := by
    rw [integrand,contour_right_eq χ (by simpa using hk)]
  simp_rw [eqn]
  apply integrable_series_transform _ _ _ (χ.LSeriesSummable_twist_vonMangoldt hk).norm
  have hc : Continuous (fun t : ℝ => weight x (line k t)) := continuous_iff_continuousAt.mpr
    (fun t => (weight_analytic hx (s:=line k t) (by simp;linarith)).continuousAt.comp
      (by unfold line;fun_prop))
  apply (integrable_inv_one_add_sq.const_mul (8*x^k)).mono' hc.aestronglyMeasurable
  filter_upwards with t
  simpa only [re_line,im_line,div_eq_mul_inv] using weight_bound hx (s:=line k t) (by simp;linarith)

private theorem edge_point {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {x σ T A : ℝ} (hx : 0<x) (hs : 1/2≤σ) (hA : 0≤A)
    (control : ∀ u : ℂ, edge σ T u → ‖contourLog χ u‖ ≤ A)
    {r t : ℝ} (hu : edge σ T (line r t)) :
    ‖integrand χ x (line r t)‖ ≤ 8*A*x^r/(1+t^2) := by
  have low : 1/2≤(line r t).re := hs.trans hu.1
  have wt := weight_bound hx low
  simp only [re_line,im_line] at wt
  rw [integrand,norm_mul]
  exact (mul_le_mul (control _ hu) wt (norm_nonneg _) hA).trans_eq (by ring)

private theorem vertical_bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {x σ T A : ℝ} (hx : 0<x) (hs : 1/2≤σ) (hs2 : σ≤2) (hT : 0<T) (hA : 0≤A)
    (control : ∀ u : ℂ, edge σ T u → ‖contourLog χ u‖ ≤ A) :
    ‖∫ t in (-T)..T, integrand χ x (line σ t)‖ ≤ 8*A*x^σ*Real.pi := by
  let M := 8*A*x^σ
  have bound (t : ℝ) (ht : t ∈ Ioc (-T) T) : ‖integrand χ x (line σ t)‖ ≤ M*(1+t^2)⁻¹ := by
    have onEdge : edge σ T (line σ t) := ⟨by simp,by simpa using hs2,
      by simpa using abs_le.mpr ⟨ht.1.le,ht.2⟩,Or.inl (re_line ..)⟩
    simpa [M,div_eq_mul_inv] using edge_point χ hx hs hA control onEdge
  have integral := intervalIntegral.norm_integral_le_of_norm_le (by linarith : -T≤T)
    (Filter.Eventually.of_forall bound) (integrable_inv_one_add_sq.intervalIntegrable.const_mul M)
  rw [intervalIntegral.integral_const_mul,integral_inv_one_add_sq] at integral
  exact integral.trans (mul_le_mul_of_nonneg_left (by
    linarith only [Real.arctan_lt_pi_div_two T,Real.neg_pi_div_two_lt_arctan (-T)])
    (by dsimp [M];positivity))

private theorem horizontal_bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {x σ k T t A : ℝ} (hx : 1≤x) (hs : 1/2≤σ) (hsk : σ≤k) (hk : k≤2)
    (hT : 0<T) (ht : |t|=T) (hA : 0≤A) (control : ∀ u : ℂ, edge σ T u → ‖contourLog χ u‖ ≤ A) :
    ‖∫ u in σ..k, integrand χ x (line u t)‖ ≤ 16*A*x^k/T^2 := by
  have point (u : ℝ) (hu : u ∈ Ι σ k) : ‖integrand χ x (line u t)‖ ≤ 8*A*x^k/T^2 := by
    rw [uIoc_of_le hsk] at hu
    have side : edge σ T (line u t) := ⟨by simpa using hu.1.le,by simpa using hu.2.trans hk,
      by simpa using ht.le,Or.inr (by simpa using ht)⟩
    apply (edge_point χ (zero_lt_one.trans_le hx) hs hA control side).trans
    have sq : t^2=T^2 := by rw [←sq_abs,ht]
    rw [sq]
    exact div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hx hu.2) (by positivity)) (by positivity) (by linarith)
  have int := intervalIntegral.norm_integral_le_of_norm_le_const point
  have len : |k-σ| ≤ 2 := by rw [abs_of_nonneg (sub_nonneg.mpr hsk)];linarith
  exact int.trans ((mul_le_mul_of_nonneg_left len (by positivity : 0≤8*A*x^k/T^2)).trans_eq (by ring))

private theorem tail_bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {x η T D : ℝ} (hx : 0<x) (hp : 0<η) (hT : 0<T) (hD : 0≤D)
    (control : ∀ t : ℝ, ‖logDeriv (LFunction χ) (line (1+η) t)‖ ≤ 1/η+D) :
    let k := 1+η
    ‖(∫ t : ℝ, integrand χ x (line k t)) - ∫ t in (-T)..T, integrand χ x (line k t)‖ ≤
      16*(1/η+D)*x^k/T := by
  intro k
  have hk : 1<k := by dsimp [k];linarith
  let M := 8*(1/η+D)*x^k
  have bound (t : ℝ) (ht : T < |t|) : ‖integrand χ x (line k t)‖ ≤ M/t^2 := by
    have sk : 1<(line k t).re := by simpa using hk
    have lg : ‖contourLog χ (line k t)‖ ≤ 1/η+D := by
      rw [contour_right_eq χ sk,LSeries_twistedCoefficient_eq χ sk,norm_neg]
      exact control t
    have wt := weight_bound hx (s:=line k t) (by simp;linarith)
    simp only [re_line,im_line] at wt
    have tp : 0<t^2 := sq_pos_of_ne_zero ((abs_pos.mp (hT.trans ht)))
    rw [integrand,norm_mul]
    calc
      _ ≤ (1/η+D)*(8*x^k/(1+t^2)) := mul_le_mul lg wt (norm_nonneg _) (by positivity)
      _ = M/(1+t^2) := by dsimp [M];ring
      _ ≤ _ := div_le_div_of_nonneg_left (by dsimp [M];positivity) tp (by linarith)
  exact (tails_bound (right_integrable χ hx hk) hT (by dsimp [M];positivity) bound).trans_eq
    (by dsimp [M];ring)

noncomputable def model {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (x σ b : ℝ) : ℂ :=
  principalFlag χ*weight x 1 - (if active χ σ b then weight x (b:ℂ) else 0)

/-- Shifting the moving right edge still encloses precisely the same zeros,
since no genuine zero lies in the closed half-plane to the right of one. -/
private theorem shift {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x σ k T b : ℝ}
    (hx : 0<x) (hs : 1/2≤σ) (hs1 : σ<1) (hk : 1<k) (hk2 : k≤2) (ht : 0<T)
    (inside : ∀ w ∈ boxZeros χ σ 2 (-T) T, σ<w.re ∧ w.re<2 ∧ -T<w.im ∧ w.im<T)
    (residue : ∀ K : ℂ → ℂ, ∑ w ∈ boxZeros χ σ 2 (-T) T,(analyticOrderNatAt (regularizedL χ) w:ℂ)*K w =
      if active χ σ b then K (b:ℂ) else 0) :
    let F := integrand χ x
    (∫ t in (-T)..T, F (line k t)) =
      (∫ t in (-T)..T, F (line σ t)) + 2*(Real.pi:ℂ)*model χ x σ b +
      I*((∫ u in σ..k, F (line u (-T))) - ∫ u in σ..k, F (line u T)) := by
  let S := boxZeros χ σ 2 (-T) T
  let U := Icc σ k ×ℂ Icc (-T) T
  have zero (w : ℂ) (hw : w ∈ U) : regularizedL χ w = 0 ↔ w ∈ S := by
    obtain ⟨r,i⟩ := mem_reProdIm.mp hw
    rw [show S=boxZeros χ σ 2 (-T) T from rfl,mem_boxZeros]
    exact ⟨fun zw => ⟨mem_reProdIm.mpr ⟨⟨r.1,r.2.trans hk2⟩,i⟩,zw⟩,And.right⟩
  have interior (w : ℂ) (hw : w ∈ S) : σ<w.re ∧ w.re<k ∧ -T<w.im ∧ w.im<T := by
    obtain ⟨lo,_,im⟩ := inside w hw
    have zw := ((mem_boxZeros χ σ 2 (-T) T w).mp hw).2
    have above : w.re < 1 := lt_of_not_ge fun e => regular_ne χ w e zw
    exact ⟨lo,above.trans hk,im⟩
  have kw (w : ℂ) (hw : w ∈ U) : AnalyticAt ℂ (weight x) w :=
    weight_analytic hx (lt_of_lt_of_le (by linarith : 0<σ) (mem_reProdIm.mp hw).1.1)
  have rect := rectBoundaryIntegral_neg_logDeriv_add_pole_mul (regularizedL χ) (weight x) S (principalFlag χ)
    hs1 hk (neg_lt_zero.mpr ht) ht ((analytic_regularizedL χ).mono (subset_univ _)) kw zero interior
    (fun w _ => regularizedL_analyticOrder_ne_top χ w) (regularizedL_ne_zero_at_one χ)
  dsimp only [S] at rect
  rw [residue (weight x)] at rect
  exact right_vertical_integral_of_rect rect

theorem finite_estimate :
    ∃ c A D : ℝ, 0<c ∧ c≤1/4 ∧ 0<A ∧ 0≤D ∧ ∀ (Q : ℕ) [NeZero Q] (T : ℝ), 1≤T →
      let L := logHeight Q (T+1)
      let h := c/L
      ∃ σ b : ℝ, 1-h/2≤σ ∧ σ≤1-h/4 ∧
      ∀ (q : ℕ) [NeZero q], q≤Q → ∀ (χ : DirichletCharacter ℂ q) (x η : ℝ),
        1≤x → 0<η → η≤1 →
        ‖rieszSum (twistedCoefficient χ) x - model χ x σ b‖ ≤
        8*(A*L^2)*x^σ*Real.pi + 32*(A*L^2)*x^(1+η)/T^2 + 16*(1/η+D)*x^(1+η)/T := by
  obtain ⟨c,A,hc,c1,hA,box⟩ := common_box
  obtain ⟨D,hD,right⟩ := NearOneZeroMultiplicity.right_edge
  refine ⟨c,A,D,hc,c1,hA,hD,?_⟩
  intro Q _ T hT L h
  obtain ⟨σ,b,left,upper,family⟩ := box Q T hT
  have L1 : 1≤L := logHeight_ge_one Q (T+1)
  have hp : 0<h := div_pos hc (zero_lt_one.trans_le L1)
  have cap : h≤1/4 := (div_le_self hc.le L1).trans c1
  have hs : 1/2≤σ := by change 1-h/2≤σ at left;linarith
  have hs1 : σ<1 := by change σ≤1-h/4 at upper;linarith
  have tp : 0<T := zero_lt_one.trans_le hT
  refine ⟨σ,b,left,upper,?_⟩
  intro q _ leQ χ x η hx ep e1
  obtain ⟨edgeControl,inside,residue⟩ := family q leQ χ
  let B := A*L^2
  let k := 1+η
  let cπ := 1/(2*Real.pi)
  let R := model χ x σ b
  let F := integrand χ x
  let full := ∫ t : ℝ, F (line k t)
  let trunc := ∫ t in (-T)..T, F (line k t)
  let v := ∫ t in (-T)..T, F (line σ t)
  let bottom := ∫ u in σ..k, F (line u (-T))
  let top := ∫ u in σ..k, F (line u T)
  have xp := zero_lt_one.trans_le hx
  have kp : 1<k := by dsimp [k];linarith
  have k2 : k≤2 := by dsimp [k];linarith
  have bp : 0≤B := by dsimp [B];positivity
  have inverse : rieszSum (twistedCoefficient χ) x = cπ • full := right_inverse χ xp kp
  have rect : trunc = v + 2*(Real.pi:ℂ)*R + I*(bottom-top) :=
    shift χ xp hs hs1 kp k2 tp inside residue
  have normV : ‖v‖ ≤ 8*B*x^σ*Real.pi :=
    vertical_bound χ xp hs (by linarith) tp bp edgeControl
  have normH (t : ℝ) (ht : |t|=T) := horizontal_bound χ hx hs (hs1.trans kp).le k2 tp ht bp edgeControl
  have nB : ‖bottom‖ ≤ 16*B*x^k/T^2 := normH (-T) (by simp [abs_of_pos tp])
  have nT : ‖top‖ ≤ 16*B*x^k/T^2 := normH T (abs_of_pos tp)
  have onLine (t : ℝ) : line (1+η) t = (⟨1+η,t⟩:ℂ) := Complex.ext (re_line ..) (im_line ..)
  have nF : ‖full-trunc‖ ≤ 16*(1/η+D)*x^k/T :=
    tail_bound χ xp ep tp hD (fun t => by rw [onLine];exact right q χ η t ep e1)
  have cancel : cπ • (2*(Real.pi:ℂ)*R) = R := by
    rw [Complex.real_smul];dsimp [cπ];push_cast;field_simp [Real.pi_ne_zero]
  have ident : rieszSum (twistedCoefficient χ) x - R = cπ • ((full-trunc)+v+I*(bottom-top)) := by
    have eqv := congrArg (fun z : ℂ => cπ • z) rect
    simp only [smul_add,cancel] at eqv
    rw [inverse]
    simp only [smul_add,smul_sub,eqv]
    abel
  have ps : ‖cπ‖≤1 := by
    rw [Real.norm_eq_abs,abs_of_pos (by dsimp [cπ];positivity)]
    dsimp [cπ]
    apply (div_le_one (by positivity : 0<2*Real.pi)).mpr
    linarith [Real.pi_gt_three]
  have nI : ‖I*(bottom-top)‖ ≤ ‖bottom‖+‖top‖ := by
    rw [norm_mul,norm_I,one_mul]
    exact norm_sub_le ..
  change ‖rieszSum (twistedCoefficient χ) x - R‖ ≤ _
  rw [ident,norm_smul]
  apply (mul_le_of_le_one_left (norm_nonneg _) ps).trans
  have triangle := (norm_add_le ((full-trunc)+v) (I*(bottom-top))).trans
    (add_le_add (norm_add_le (full-trunc) v) nI)
  change _ ≤ 8*B*x^σ*Real.pi + 32*B*x^k/T^2 + 16*(1/η+D)*x^k/T
  exact (triangle.trans (add_le_add (add_le_add nF normV) (add_le_add nB nT))).trans_eq (by ring)

end Conjectures.Goldbach.ExceptionalZeroRieszEstimate

set_option maxHeartbeats 1800000 in
theorem Conjectures.Goldbach.ExceptionalZeroRieszEstimate :
by
  classical
  let wt := fun (x : ℝ) (s : ℂ) => (x:ℂ)^s/(s*(s+1))
  exact ∃ c A D : ℝ, 0<c ∧ c≤1/4 ∧ 0<A ∧ 0≤D ∧
    ∀ (Q : ℕ) [NeZero Q] (T : ℝ), 1≤T →
    let L := Real.log (2*(Q:ℝ)*(2+|T+1|))
    let h := c/L
    ∃ σ b : ℝ, 1-h/2≤σ ∧ σ≤1-h/4 ∧ ∀ (q : ℕ) [NeZero q], q≤Q →
    ∀ (χ : DirichletCharacter ℂ q) (x η : ℝ), 1≤x → 0<η → η≤1 →
      let P := ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
        χ (n:ZMod q)*(ArithmeticFunction.vonMangoldt n:ℂ)*(1-(n:ℂ)/(x:ℂ))
      let R := (@ite ℂ (χ=1) (Classical.propDecidable _) 1 0)*wt x 1 -
        (@ite ℂ (σ<b ∧ b<1 ∧ (χ ≠ 1 ∨ (b:ℂ) ≠ 1) ∧ DirichletCharacter.LFunction χ (b:ℂ)=0)
          (Classical.propDecidable _) (wt x (b:ℂ)) 0)
      ‖P-R‖ ≤ 8*(A*L^2)*x^σ*Real.pi + 32*(A*L^2)*x^(1+η)/T^2 + 16*(1/η+D)*x^(1+η)/T :=
by
  with_unfolding_all exact ExceptionalZeroRieszEstimate.finite_estimate
