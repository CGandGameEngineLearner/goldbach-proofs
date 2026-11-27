import Conjectures.Goldbach.ExceptionalZeroPrimeFamily

/-! Prime Fourier sums at reduced rational frequencies, with the signed
exceptional coefficient retained through Fourier inversion. Prime powers
are removed once, after summing over characters. -/

namespace Conjectures.Goldbach.ExceptionalZeroRationalCenters

open Real Complex DirichletCharacter
open _root_.Goldbach GoldbachSmoothing GoldbachGRHWindow GoldbachTwistedMellin
open ExceptionalZeroTwistedWindow ExceptionalZeroPrimePrefix ExceptionalZeroPrimeFamily
open scoped Classical

noncomputable def primeCenter (N q a : ℕ) [NeZero q] : ℂ :=
  ∑ j ∈ Finset.Ioc 0 N, primeLog j * ZMod.stdAddChar ((a:ZMod q)*(j:ZMod q))

noncomputable def gaussWeight (q a : ℕ) [NeZero q] (s b : ℝ) : ℂ :=
  ∑ χ ∈ carriers q s b, additiveWeight (a:ZMod q) χ

noncomputable def mainTerm (q a : ℕ) [NeZero q] (x s b : ℝ) : ℂ :=
  ((ArithmeticFunction.moebius q:ℂ)/(q.totient:ℂ))*(x:ℂ) - gaussWeight q a s b*((x^b/b:ℝ):ℂ)

/-- The absolute prime-power loss is independent of the modulus. -/
theorem center_transfer (N q a : ℕ) [NeZero q] (hN : 1≤N) (cop : a.Coprime q)
    {x s b M : ℝ} (hM : 0≤M) (hver : ∀ χ : DirichletCharacter ℂ q,
      ‖(∑ j ∈ Finset.Ioc 0 N, twistedCoefficient χ j)-sharp χ x s b‖≤M) :
    ‖primeCenter N q a-mainTerm q a x s b‖ ≤ Real.sqrt q*M+2*Real.sqrt N*Real.log N+Real.log q := by
  classical
  let I := Finset.Ioc 0 N
  let e (j : ℕ) : ℂ := ZMod.stdAddChar ((a:ZMod q)*(j:ZMod q))
  let w (χ : DirichletCharacter ℂ q) := additiveWeight (a:ZMod q) χ
  let P (χ : DirichletCharacter ℂ q) := ∑ j ∈ I, twistedCoefficient χ j
  let U := ∑ j ∈ I, (primeLog j*e j)*(1:DirichletCharacter ℂ q) (j:ZMod q)
  let W := ∑ j ∈ I, twistedCoefficient (1:DirichletCharacter ℂ q) j*e j
  let D := ∑ j ∈ I.filter (fun j : ℕ => ¬IsUnit (j:ZMod q)), primeLog j*e j
  have splitP : primeCenter N q a=U+D := by
    dsimp only [primeCenter,U,D]
    rw [Finset.sum_filter,←Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : IsUnit (j:ZMod q)
    · simp [e,MulChar.one_apply,hj]
    · simp [e,MulChar.map_nonunit _ hj,hj]
  have dnorm : ‖D‖≤Real.log q := by
    apply (norm_sum_le ..).trans
    simpa [e,norm_mul,ZMod.stdAddChar_apply] using primeLog_nonunit_mass_le (q:=q) I
  have rot (j : ℕ) : GoldbachTwistedMellin.phase (2*Real.pi*a/q) j=e j := by
    dsimp only [e]
    rw [GoldbachGRHWindow.stdAddChar_nat_pair,GoldbachTwistedMellin.phase,
      show (2*Real.pi*(a:ℝ)/q)*j=2*Real.pi*((a:ℝ)*j/q) by ring]
  have loss : ‖U-W‖≤2*Real.sqrt N*Real.log N := by
    have raw := prime_removal (1:DirichletCharacter ℂ q) 0 N N le_rfl hN (2*Real.pi*a/q)
    simpa only [rot] using raw
  have invert : W=∑ χ, w χ*P χ := by
    dsimp only [W,P]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    have eqn : (∑ χ, w χ * twistedCoefficient χ j) =
        (∑ χ, w χ*χ (j:ZMod q))*(ArithmeticFunction.vonMangoldt j:ℂ) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro χ _
      simp [twistedCoefficient,mul_assoc]
    rw [eqn,show (∑ χ, w χ*χ (j:ZMod q))=_ from additiveWeight_inversion (a:ZMod q) (j:ZMod q)]
    by_cases hj : IsUnit (j:ZMod q)
    · simp [e,twistedCoefficient,MulChar.one_apply,hj,mul_comm]
    · simp [e,twistedCoefficient,MulChar.map_nonunit _ hj,hj]
  have principal : (∑ χ, w χ*(principalFlag χ*(x:ℂ)))=additiveModel q (a:ZMod q)*(x:ℂ) := by
    simp [principalFlag,ite_mul,mul_ite,w,additiveWeight_one]
  have corrected : (∑ χ, w χ*(if active χ s b then ((x^b/b:ℝ):ℂ) else 0)) =
      gaussWeight q a s b*((x^b/b:ℝ):ℂ) := by
    rw [gaussWeight,Finset.sum_mul,carriers,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro χ _
    by_cases h : active χ s b <;> simp [w,h]
  have model : (∑ χ, w χ*sharp χ x s b)=mainTerm q a x s b := by
    change (∑ χ, w χ*(principalFlag χ*(x:ℂ)-(if active χ s b then ((x^b/b:ℝ):ℂ) else 0)))=_
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib,principal,corrected,mainTerm,
      additiveModel_eq_moebius _ ((ZMod.isUnit_iff_coprime a q).mpr cop)]
  have analytic : ‖W-mainTerm q a x s b‖≤Real.sqrt q*M := by
    rw [invert,←model,←Finset.sum_sub_distrib]
    simp_rw [←mul_sub]
    apply (norm_sum_le ..).trans
    calc
      _ ≤ ∑ χ, ‖w χ‖*M := by
        apply Finset.sum_le_sum
        intro χ _
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hver χ) (norm_nonneg _)
      _ = (∑ χ, ‖w χ‖)*M := (Finset.sum_mul ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right (sum_norm_additiveWeight_le (a:ZMod q)) hM
  calc
    _ = ‖((W-mainTerm q a x s b)+(U-W))+D‖ := by rw [splitP];congr 1;abel
    _ ≤ _ := (norm_add_le ..).trans (add_le_add ((norm_add_le ..).trans (add_le_add analytic loss)) dnorm)

/-- The prime-power and nonunit errors fit below the same exponential
scale as the character estimates on the smaller modulus range. -/
private theorem elementary_loss {x u : ℝ} {q : ℕ} [NeZero q] (u8 : 8≤u)
    (lx : Real.log x=u^2) (xp : 0<x) (hq : (q:ℝ)≤Real.exp u) :
    2*Real.sqrt x*Real.log x + Real.log q ≤ 5*x*Real.exp (-u) := by
  have up : 0≤u := by linarith
  have ex : x=Real.exp (u^2) := by rw [←lx,Real.exp_log xp]
  have sq : u^2≤2*Real.exp u := by
    have h := Real.pow_div_factorial_le_exp u up 2
    norm_num at h
    linarith
  have ss : Real.sqrt x=Real.exp (u^2/2) := by rw [ex,Real.exp_half]
  have smooth : Real.exp (u^2/2)*Real.exp u ≤ x*Real.exp (-u) := by
    rw [ex,←Real.exp_add,←Real.exp_add,Real.exp_le_exp]
    nlinarith only [u8,mul_nonneg (sub_nonneg.mpr u8) up]
  have prime : 2*Real.sqrt x*Real.log x≤4*(x*Real.exp (-u)) := by
    rw [ss,lx]
    nlinarith only [mul_le_mul_of_nonneg_left sq (Real.exp_pos (u^2/2)).le,smooth]
  have qp : 0<(q:ℝ) := by exact_mod_cast NeZero.pos q
  have small := Real.log_le_log qp hq
  rw [Real.log_exp] at small
  have low : Real.exp u≤x*Real.exp (-u) := by
    rw [ex,←Real.exp_add,Real.exp_le_exp]
    nlinarith only [u8,mul_nonneg (sub_nonneg.mpr u8) up]
  linarith only [prime,small,Real.add_one_le_exp u,low]

theorem rational_centers :
    ∃ k t C : ℝ, 0<k ∧ 0<t ∧ t≤k/2 ∧ 0<C ∧ ∀ N : ℕ, Real.exp 64≤(N:ℝ) →
    let u := Real.sqrt (Real.log N)
    let s := 1-k/u
    ∀ (Q : ℕ) [NeZero Q], (Q:ℝ)≤Real.exp u → ∃ (b : ℝ) (d : ℕ), d≤Q ∧
    ∀ (q : ℕ) [NeZero q], q≤Q →
      (carriers q s b).card=(if d∣q then 1 else 0) ∧
      (∀ χ ∈ carriers q s b, χ.IsQuadratic ∧ χ ≠ 1 ∧ χ.conductor=d ∧ analyticOrderNatAt (LFunction χ) (b:ℂ)=1) ∧
      ∀ a : ℕ, a.Coprime q →
        let R := ‖primeCenter N q a-mainTerm q a N s b‖
        (¬d∣q → gaussWeight q a s b=0) ∧
        R≤Real.sqrt q*(C*N*Real.exp (-(k*u)))+2*Real.sqrt N*Real.log N+Real.log q ∧
        ((q:ℝ)≤Real.exp (2*t*u) → R≤C*N*Real.exp (-(t*u))) := by
  obtain ⟨k,A,kp,Ap,family⟩ := uniform_family
  let t := min (k/2) (1/4)
  have tp : 0<t := lt_min (by positivity) (by norm_num)
  have tk : t≤k/2 := min_le_left ..
  have t1 : t≤1 := (min_le_right .. : t≤1/4).trans (by norm_num)
  refine ⟨k,t,A+5,kp,tp,tk,by positivity,?_⟩
  intro N hN u s Q _ hQ
  have N1 : 1≤(N:ℝ) := (Real.one_le_exp (by norm_num : 0≤(64:ℝ))).trans hN
  have npos : 0<(N:ℝ) := zero_lt_one.trans_le N1
  have lg := Real.log_le_log (Real.exp_pos _) hN
  rw [Real.log_exp] at lg
  have lu : Real.log N=u^2 := (Real.sq_sqrt (by linarith)).symm
  have up : 0≤u := Real.sqrt_nonneg _
  have u8 : 8≤u := by nlinarith only [lg,lu,up]
  obtain ⟨b,d,dQ,all⟩ := family N hN Q hQ
  refine ⟨b,d,dQ,?_⟩
  intro q _ qQ
  obtain ⟨count,types,err⟩ := all q qQ
  refine ⟨count,types,?_⟩
  intro a cop R
  have vanish (nv : ¬d∣q) : gaussWeight q a s b=0 := by
    rw [ite_eq_right nv,Finset.card_eq_zero] at count
    change carriers q s b=∅ at count
    simp [gaussWeight,count]
  have qsmall : (q:ℝ)≤Real.exp u := (Nat.cast_le.mpr qQ).trans hQ
  have raw := center_transfer N q a (by exact_mod_cast N1) cop (x:=N) (s:=s) (b:=b)
    (M:=A*N*Real.exp (-(k*u))) (by positivity) (by simpa only [Nat.floor_natCast] using err)
  refine ⟨vanish,raw.trans ?_,?_⟩
  · gcongr
    linarith
  · intro hq
    have sr : Real.sqrt q≤Real.exp (t*u) := by
      have bound := Real.sqrt_le_sqrt hq
      rw [←Real.exp_half,show 2*t*u/2=t*u by ring] at bound
      exact bound
    have analytic : Real.sqrt q*(A*N*Real.exp (-(k*u)))≤A*N*Real.exp (-(t*u)) := by
      calc
        _ ≤ Real.exp (t*u)*(A*N*Real.exp (-(k*u))) := mul_le_mul_of_nonneg_right sr (by positivity)
        _ = A*N*Real.exp (t*u+ -(k*u)) := by rw [Real.exp_add];ring
        _ ≤ _ := by
          gcongr
          nlinarith only [mul_le_mul_of_nonneg_right tk up]
    have elementary := elementary_loss u8 lu npos qsmall
    have decrease : Real.exp (-u)≤Real.exp (-(t*u)) := by
      apply Real.exp_le_exp.mpr
      linarith only [mul_le_mul_of_nonneg_right t1 up]
    linarith only [raw,analytic,elementary,mul_le_mul_of_nonneg_left decrease (by positivity : 0≤5*(N:ℝ))]

end Conjectures.Goldbach.ExceptionalZeroRationalCenters

set_option maxHeartbeats 1800000 in
theorem Conjectures.Goldbach.ExceptionalZeroRationalCenters :
by
  classical
  let hit := fun {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s b : ℝ) =>
    s<b ∧ b<1 ∧ (χ ≠ 1 ∨ (b:ℂ) ≠ 1) ∧ DirichletCharacter.LFunction χ (b:ℂ)=0
  exact ∃ k t C : ℝ, 0<k ∧ 0<t ∧ t≤k/2 ∧ 0<C ∧ ∀ N : ℕ, Real.exp 64≤(N:ℝ) →
    let u := Real.sqrt (Real.log N)
    let s := 1-k/u
    ∀ (Q : ℕ) [NeZero Q], (Q:ℝ)≤Real.exp u → ∃ (b : ℝ) (d : ℕ), d≤Q ∧
    ∀ (q : ℕ) [NeZero q], q≤Q →
      let S := @Finset.filter (DirichletCharacter ℂ q) (fun χ => hit χ s b)
        (fun _ => Classical.propDecidable _) Finset.univ
      S.card=(if d∣q then 1 else 0) ∧
      (∀ χ ∈ S, χ.IsQuadratic ∧ χ ≠ 1 ∧ χ.conductor=d ∧
        analyticOrderNatAt (DirichletCharacter.LFunction χ) (b:ℂ)=1) ∧
      ∀ a : ℕ, a.Coprime q →
        let E := fun j : ℕ => ZMod.stdAddChar ((a:ZMod q)*(j:ZMod q))
        let P := ∑ j ∈ Finset.Ioc 0 N, ((if j.Prime then Real.log (j:ℝ) else 0:ℝ):ℂ)*E j
        let G := ∑ χ ∈ S, (starRingEnd ℂ) (∑ r : ZMod q,
          (starRingEnd ℂ) (ZMod.stdAddChar ((a:ZMod q)*r))*χ r)/(q.totient:ℂ)
        let R := ‖P-(((ArithmeticFunction.moebius q:ℂ)/(q.totient:ℂ))*(N:ℂ)-G*((((N:ℝ)^b/b):ℝ):ℂ))‖
        (¬d∣q → G=0) ∧
        R≤Real.sqrt q*(C*N*Real.exp (-(k*u)))+2*Real.sqrt N*Real.log N+Real.log q ∧
        ((q:ℝ)≤Real.exp (2*t*u) → R≤C*N*Real.exp (-(t*u))) :=
by
  with_unfolding_all exact ExceptionalZeroRationalCenters.rational_centers
