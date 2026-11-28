import Conjectures.Goldbach.ExceptionalZeroRieszDecay

/-! Removing the first Riesz weight with a common possible exceptional zero.
The real primitive of x^β/β has second derivative x^(β−1), bounded by one
throughout the summation window whenever 1/2 ≤ β < 1. -/

namespace Conjectures.Goldbach.ExceptionalZeroPrimePrefix

open Set Real Complex DirichletCharacter
open _root_.Goldbach GoldbachSmoothing ExceptionalZeroTwistedWindow ExceptionalZeroRieszEstimate
open Conjectures.Goldbach.EstermannAlmostAllPolylog_aux.OAI.LargePrimeGaps
  (weightedPrefix weightedPrefix_eq_mul_rieszSum weightedPrefix_difference weightedPrefix_tail_bound
   primeCoefficients_norm_le characterMain_norm_le)
open scoped Classical

private noncomputable def primitive (b x : ℝ) : ℝ := x^(b+1)/(b*(b+1))
private noncomputable def density (b x : ℝ) : ℝ := x^b/b

private theorem primitive_derivative {x b : ℝ} (hx : 0<x) (hb : 0<b) :
    HasDerivAt (primitive b) (density b x) x := by
  have der := (Real.hasDerivAt_rpow_const (p:=b+1) (Or.inl hx.ne')).div_const (b*(b+1))
  have eqn : density b x = (b+1)*x^(b+1-1)/(b*(b+1)) := by
    rw [density,add_sub_cancel_right]
    field_simp
  rw [eqn]
  exact der

private theorem density_derivative {x b : ℝ} (hx : 0<x) (hb : 0<b) :
    HasDerivAt (density b) (x^(b-1)) x := by
  have der := (Real.hasDerivAt_rpow_const (p:=b) (Or.inl hx.ne')).div_const b
  have eqn : x^(b-1)=b*x^(b-1)/b := by field_simp
  rw [eqn]
  exact der

private theorem primitive_increment {x b h : ℝ} (hx : 1≤x) (hh : 0<h) (hb : 0<b) (hb1 : b≤1) :
    |primitive b (x+h) - primitive b x - h*density b x| ≤ h^2 := by
  have xp := zero_lt_one.trans_le hx
  have dF (t : ℝ) (ht : t ∈ Icc x (x+h)) := primitive_derivative (xp.trans_le ht.1) hb
  obtain ⟨z,hz,slope⟩ := exists_hasDerivAt_eq_slope (primitive b) (density b) (by linarith : x<x+h)
    (fun t ht => (dF t ht).continuousAt.continuousWithinAt)
    (fun t ht => dF t (Ioo_subset_Icc_self ht))
  rw [add_sub_cancel_left] at slope
  have lip := norm_image_sub_le_of_norm_deriv_le_segment' (f:=density b)
    (fun (t : ℝ) (ht : t ∈ Icc x (x+h)) =>
      (density_derivative (xp.trans_le ht.1) hb).hasDerivWithinAt)
    (fun (t : ℝ) (ht : t ∈ Ico x (x+h)) => (show ‖t^(b-1)‖≤(1:ℝ) by
      rw [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (xp.trans_le ht.1).le _)]
      exact Real.rpow_le_one_of_one_le_of_nonpos (hx.trans ht.1) (by linarith))) z (Ioo_subset_Icc_self hz)
  have ident : primitive b (x+h)-primitive b x-h*density b x = h*(density b z-density b x) := by
    have s := (eq_div_iff hh.ne').mp slope
    linarith only [s]
  rw [ident,abs_mul,abs_of_pos hh]
  calc
    _ ≤ h*(z-x) := mul_le_mul_of_nonneg_left (by simpa [Real.norm_eq_abs] using lip) hh.le
    _ ≤ h^2 := by nlinarith only [mul_le_mul_of_nonneg_left hz.2.le hh.le]

noncomputable def integrated {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (x σ b : ℝ) : ℂ :=
  principalFlag χ*(x:ℂ)^2/2 - (if active χ σ b then (primitive b x:ℂ) else 0)

noncomputable def sharp {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (x σ b : ℝ) : ℂ :=
  principalFlag χ*(x:ℂ) - (if active χ σ b then (density b x:ℂ) else 0)

private theorem integrated_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x σ b : ℝ}
    (hx : 0<x) : integrated χ x σ b = (x:ℂ)*model χ x σ b := by
  have one : weight x 1=(x:ℂ)/2 := by unfold weight;norm_num
  unfold integrated model
  rw [one]
  by_cases use : active χ σ b
  · rw [ite_eq_left use,ite_eq_left use]
    have power : (primitive b x:ℂ) = (x:ℂ)*weight x (b:ℂ) := by
      unfold primitive weight
      rw [Real.rpow_add hx,Real.rpow_one]
      push_cast
      rw [Complex.ofReal_cpow hx.le]
      ring
    rw [power];ring
  · rw [ite_eq_right use,ite_eq_right use];ring

private theorem integrated_increment {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {x σ b h : ℝ} (hx : 1≤x) (hs : 1/2≤σ) (hh : 0<h) :
    ‖integrated χ (x+h) σ b - integrated χ x σ b - (h:ℂ)*sharp χ x σ b‖ ≤ 2*h^2 := by
  have nδ : ‖principalFlag χ‖≤1 := characterMain_norm_le χ
  let δ := principalFlag χ
  have principal : ‖δ*(h:ℂ)^2/2‖≤h^2 := by
    rw [norm_div,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hh]
    norm_num
    nlinarith only [mul_le_mul_of_nonneg_right nδ (sq_nonneg h),sq_nonneg h]
  unfold integrated sharp
  by_cases use : active χ σ b
  · simp only [ite_eq_left use]
    have er := primitive_increment hx hh (by linarith only [hs,use.1] : 0<b) use.2.1.le
    let r := primitive b (x+h)-primitive b x-h*density b x
    have iden : principalFlag χ*((x+h:ℝ):ℂ)^2/2 - (primitive b (x+h):ℂ) -
        (principalFlag χ*(x:ℂ)^2/2-(primitive b x:ℂ))-(h:ℂ)*(principalFlag χ*x-(density b x:ℂ)) =
        δ*(h:ℂ)^2/2 - (r:ℂ) := by dsimp [δ,r];push_cast;ring
    rw [iden]
    have small : ‖(r:ℂ)‖≤h^2 := by simpa only [Complex.norm_real,Real.norm_eq_abs] using er
    linarith only [norm_sub_le (δ*(h:ℂ)^2/2) (r:ℂ),principal,small]
  · simp only [ite_eq_right use,sub_zero]
    have iden : principalFlag χ*((x+h:ℝ):ℂ)^2/2 -principalFlag χ*(x:ℂ)^2/2 -(h:ℂ)*(principalFlag χ*x) =
        δ*(h:ℂ)^2/2 := by dsimp [δ];push_cast;ring
    rw [iden]
    linarith only [principal,sq_nonneg h]

/-- Moving the endpoint by h costs the sum of two integrated errors, the
short interval's elementary Mangoldt bound, and the model's curvature. -/
theorem unsmooth {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x σ b h : ℝ}
    (hx : 1≤x) (hs : 1/2≤σ) (hh : 0<h) :
    let a := twistedCoefficient χ
    let E := fun y => ‖weightedPrefix a y - integrated χ y σ b‖
    ‖(∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, a n) - sharp χ x σ b‖ ≤
      (E (x+h)+E x)/h + (h+1)*Real.log (x+h)+2*h := by
  intro a E
  let p := ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, a n
  let F := fun t => weightedPrefix a t - integrated χ t σ b
  let tail := ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x+h⌋₊, ((x+h-(n:ℝ):ℝ):ℂ)*a n
  let curv := integrated χ (x+h) σ b - integrated χ x σ b - (h:ℂ)*sharp χ x σ b
  have xp := zero_lt_one.trans_le hx
  have lp := Real.log_nonneg (show 1≤x+h by linarith)
  have coef (n : ℕ) (hn : n∈Finset.Ioc ⌊x⌋₊ ⌊x+h⌋₊) : ‖a n‖≤Real.log (x+h) := by
    have hn0 : 0<n := lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.mp hn).1
    have hn1 := (Nat.le_floor_iff (show 0≤x+h by linarith)).mp (Finset.mem_Ioc.mp hn).2
    exact (primeCoefficients_norm_le χ n).trans (Real.log_le_log (by exact_mod_cast hn0) hn1)
  have tail_le : ‖tail‖ ≤ (h+1)*(h*Real.log (x+h)) := weightedPrefix_tail_bound xp.le hh.le lp a coef
  have inc : weightedPrefix a (x+h)-weightedPrefix a x=(h:ℂ)*p+tail :=
    weightedPrefix_difference hh.le a
  have full : (h:ℂ)*(p-sharp χ x σ b) = ((F (x+h)-F x)-tail)+curv := by
    dsimp [F,curv]
    linear_combination -inc
  have tri := (norm_add_le (F (x+h)-F x-tail) curv).trans
    (add_le_add ((norm_sub_le (F (x+h)-F x) tail).trans
      (add_le_add (norm_sub_le (F (x+h)) (F x)) (le_refl ‖tail‖))) le_rfl)
  rw [←full,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hh] at tri
  change ‖p-sharp χ x σ b‖ ≤ _
  calc
    _ ≤ ((E (x+h)+E x)+((h+1)*Real.log (x+h)+2*h)*h)/h := by
      apply (le_div_iff₀ hh).mpr
      have cv : ‖curv‖≤2*h^2 := integrated_increment χ hx hs hh
      change h*‖p-sharp χ x σ b‖ ≤ E (x+h)+E x+‖tail‖+‖curv‖ at tri
      nlinarith only [tri,tail_le,cv]
    _ = _ := by field_simp;ring

/-- Up to exp(sqrt(log x)) in modulus the ordinary, unsmoothed prefix
has an exponentially decaying relative error after its single possible
exceptional term is retained. The correction and the contour are common
to every level in the family at this length. -/
theorem prime_prefix :
    ∃ k C : ℝ, 0<k ∧ 0<C ∧ ∀ (x : ℝ), Real.exp 64≤x →
      let u := Real.sqrt (Real.log x)
      ∀ (Q : ℕ) [NeZero Q], (Q:ℝ)≤Real.exp u → ∃ σ b : ℝ, 1/2≤σ ∧ σ≤1-8*k/u ∧
      ∀ (q : ℕ) [NeZero q], q≤Q → ∀ χ : DirichletCharacter ℂ q,
        ‖(∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, twistedCoefficient χ n) - sharp χ x σ b‖ ≤
        C*x*Real.exp (-(k*u)) := by
  obtain ⟨a,A,ap,ac,Ap,estimate⟩ := ExceptionalZeroRieszDecay.uniform_estimate
  let k := a/4
  have kp : 0<k := by dsimp [k];positivity
  let C := 5*A+8/k^2+2
  refine ⟨k,C,kp,by dsimp [C];positivity,?_⟩
  intro x hx u Q _ hQ
  have x1 : 1≤x := (Real.one_le_exp (by norm_num : (0:ℝ)≤64)).trans hx
  have xp := zero_lt_one.trans_le x1
  have lx : 64≤Real.log x := by simpa using Real.log_le_log (Real.exp_pos _) hx
  have usq : u^2=Real.log x := Real.sq_sqrt (by linarith)
  have up : 0<u := Real.sqrt_pos.mpr (by linarith)
  have u8 : 8≤u := by nlinarith only [usq,lx,up]
  obtain ⟨σ,b,lo,hi,fam⟩ := estimate u u8 Q hQ
  have ku : 8*k=2*a := by dsimp [k];ring
  refine ⟨σ,b,lo,by simpa only [ku] using hi,?_⟩
  intro q _ leQ χ
  let H := Real.exp (-(2*k*u))
  let h := x*H
  have Hp : 0<H := Real.exp_pos _
  have H1 : H≤1 := Real.exp_le_one_iff.mpr (by nlinarith only [mul_nonneg kp.le up.le])
  have hp : 0<h := mul_pos xp Hp
  have h1 : 1≤h := by
    change 1≤x*Real.exp _
    rw [←Real.exp_log xp,←Real.exp_add,Real.one_le_exp_iff]
    have := mul_le_mul_of_nonneg_right ac up.le
    dsimp [k]
    nlinarith only [usq,this,u8,sq_nonneg (u-8)]
  have hle : h≤x := mul_le_of_le_one_right xp.le H1
  have v1 : 1≤x+h := by linarith
  have vlo : u^2≤Real.log (x+h) := usq.le.trans (Real.log_le_log xp (by linarith))
  have vhi : Real.log (x+h)≤2*u^2 := by
    apply (Real.log_le_log (by positivity) (show x+h≤2*x by linarith)).trans
    rw [Real.log_mul (by norm_num) xp.ne']
    linarith only [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2),usq,lx]
  have decay : Real.exp (-(a*u))=H^2 := by
    change _ = (Real.exp _)^2
    rw [sq,←Real.exp_add]
    congr 1;dsimp [k];ring
  let E := fun y => ‖weightedPrefix (twistedCoefficient χ) y - integrated χ y σ b‖
  have err (y : ℝ) (hy : 1≤y) (yl : u^2≤Real.log y) (yu : Real.log y≤2*u^2) : E y≤A*y^2*H^2 := by
    have yp := zero_lt_one.trans_le hy
    dsimp [E]
    rw [weightedPrefix_eq_mul_rieszSum _ yp,integrated_eq χ yp,←mul_sub,norm_mul,
      Complex.norm_real,Real.norm_eq_abs,abs_of_pos yp]
    have r := fam q leQ χ y hy yl yu
    rw [decay] at r
    exact (mul_le_mul_of_nonneg_left r yp.le).trans_eq (by ring)
  have el := err x x1 usq.le (by rw [←usq];nlinarith only [sq_nonneg u])
  have er := err (x+h) v1 vlo vhi
  have both : (E (x+h)+E x)/h ≤ 5*A*x*H := by
    apply (div_le_iff₀ hp).mpr
    have bound : (x+h)^2≤(2*x)^2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    have outer : A*(x+h)^2*H^2≤A*(2*x)^2*H^2 := by gcongr
    change _ ≤ 5*A*x*H*(x*H)
    nlinarith only [el,er,outer]
  have short : (h+1)*Real.log (x+h) ≤ (2*h)*(2*u^2) := by
    apply mul_le_mul (by linarith) vhi (Real.log_nonneg v1) (by positivity)
  have raw := unsmooth (b:=b) χ x1 lo hp
  change _ ≤ (E (x+h)+E x)/h+(h+1)*Real.log (x+h)+2*h at raw
  have loss : u^2*H ≤ (2/k^2)*Real.exp (-(k*u)) :=
    ExceptionalZeroRieszDecay.square_exp_bound kp up.le
  have weak : H≤Real.exp (-(k*u)) := Real.exp_le_exp.mpr (by nlinarith only [mul_nonneg kp.le up.le])
  have K0 : 0≤5*A+2 := by positivity
  calc
    _ ≤ 5*A*x*H+(2*h)*(2*u^2)+2*h := raw.trans (add_le_add (add_le_add both short) le_rfl)
    _ = x*((5*A+2)*H+4*(u^2*H)) := by dsimp [h];ring
    _ ≤ x*((5*A+2)*Real.exp (-(k*u))+4*((2/k^2)*Real.exp (-(k*u)))) := by gcongr
    _ = _ := by dsimp [C];ring

end Conjectures.Goldbach.ExceptionalZeroPrimePrefix

set_option maxHeartbeats 1800000 in
theorem Conjectures.Goldbach.ExceptionalZeroPrimePrefix :
by
  classical
  exact ∃ k C : ℝ, 0<k ∧ 0<C ∧ ∀ (x : ℝ), Real.exp 64≤x →
    let u := Real.sqrt (Real.log x)
    ∀ (Q : ℕ) [NeZero Q], (Q:ℝ)≤Real.exp u → ∃ σ b : ℝ, 1/2≤σ ∧ σ≤1-8*k/u ∧
    ∀ (q : ℕ) [NeZero q], q≤Q → ∀ χ : DirichletCharacter ℂ q,
      let P := ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, χ (n:ZMod q)*(ArithmeticFunction.vonMangoldt n:ℂ)
      let R := (@ite ℂ (χ=1) (Classical.propDecidable _) 1 0)*(x:ℂ) -
        (@ite ℂ (σ<b ∧ b<1 ∧ (χ ≠ 1 ∨ (b:ℂ) ≠ 1) ∧ DirichletCharacter.LFunction χ (b:ℂ)=0)
          (Classical.propDecidable _) ((x^b/b:ℝ):ℂ) 0)
      ‖P-R‖ ≤ C*x*Real.exp (-(k*u)) :=
by
  with_unfolding_all exact ExceptionalZeroPrimePrefix.prime_prefix
