import Conjectures.Goldbach.ExceptionalZeroPrimePrefix

/-! Put the exceptional cutoff at 1−k/sqrt(log x) and identify exactly
which characters carry the correction. The exponent k is absolute and
every positive level divisible by the selected conductor has one carrier. -/

namespace Conjectures.Goldbach.ExceptionalZeroPrimeFamily

open Real Complex DirichletCharacter
open _root_.Goldbach GoldbachSmoothing ExceptionalZeroCatalogue ExceptionalZeroInducedLevels
open ExceptionalZeroTwistedWindow ExceptionalZeroPrimePrefix
open scoped Classical

noncomputable def carriers (q : ℕ) [NeZero q] (s b : ℝ) : Finset (DirichletCharacter ℂ q) :=
  Finset.univ.filter (fun χ => active χ s b)

@[simp] theorem mem_carriers {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} {s b : ℝ} :
    χ ∈ carriers q s b ↔ active χ s b := by simp [carriers]

private theorem induced_ext {q : ℕ} (χ ψ : DirichletCharacter ℂ q)
    (hc : χ.conductor=ψ.conductor) (hχ : HEq χ.primitiveCharacter ψ.primitiveCharacter) : χ=ψ := by
  have lift {r t : ℕ} (d : r∣q) (e : t∣q) (φ : DirichletCharacter ℂ r) (θ : DirichletCharacter ℂ t)
      (same : r=t) (eqn : HEq φ θ) : changeLevel d φ=changeLevel e θ := by
    subst t
    cases eq_of_heq eqn
    rfl
  simpa only [changeLevel_primitiveCharacter] using
    lift χ.conductor_dvd_level ψ.conductor_dvd_level χ.primitiveCharacter ψ.primitiveCharacter hc hχ

/-- The shift of the cutoff from σ up to s loses at most a real-power
term of size 2 x exp(-ku). -/
private theorem cutoff_error {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {x u k σ b : ℝ} (hx : 1≤x) (up : 0<u) (kp : 0<k) (lu : Real.log x=u^2)
    (hs : 1/2≤σ) (hsc : σ≤1-k/u) :
    ‖sharp χ x σ b - sharp χ x (1-k/u) b‖ ≤ 2*x*Real.exp (-(k*u)) := by
  let s := 1-k/u
  have xp := zero_lt_one.trans_le hx
  by_cases old : active χ σ b
  · by_cases new : active χ s b
    · simp only [sharp,show 1-k/u=s from rfl,ite_eq_left old,ite_eq_left new,sub_self,norm_zero]
      positivity
    · have lo : 1/2<b := hs.trans_lt old.1
      have bs : b≤ s := le_of_not_gt (fun h => new ⟨h,old.2⟩)
      have pow : x^b≤x*Real.exp (-(k*u)) := by
        rw [Real.rpow_def_of_pos xp,←Real.exp_log xp,Real.log_exp,←Real.exp_add,Real.exp_le_exp,lu]
        have prod := mul_le_mul_of_nonneg_left bs (sq_nonneg u)
        have iden : u^2*s=u^2-k*u := by dsimp [s];field_simp
        linarith only [prod,iden]
      have dens : |x^b/b| ≤ 2*(x*Real.exp (-(k*u))) := by
        rw [abs_of_nonneg (by positivity)]
        apply (div_le_iff₀ (by linarith : 0<b)).mpr
        nlinarith only [pow,mul_le_mul_of_nonneg_right lo.le (by positivity : 0≤x*Real.exp (-(k*u)))]
      simp only [sharp,show 1-k/u=s from rfl,ite_eq_left old,ite_eq_right new,sub_zero,sub_sub_cancel_left,
        norm_neg,Complex.norm_real,Real.norm_eq_abs]
      exact dens.trans_eq (by ring)
  · have new : ¬active χ s b := fun h => old ⟨hsc.trans_lt h.1,h.2⟩
    simp only [sharp,show 1-k/u=s from rfl,ite_eq_right old,ite_eq_right new,sub_self,norm_zero]
    positivity

private theorem select_conductor {Q : ℕ} [NeZero Q] {s b : ℝ} (hs : 1/2≤ s)
    (family : ∀ (q r : ℕ) [NeZero q] [NeZero r], q≤Q → r≤Q →
      ∀ (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r), active χ s b → active ψ s b →
      χ.IsQuadratic ∧ χ ≠ 1 ∧ χ.conductor=ψ.conductor ∧ HEq χ.primitiveCharacter ψ.primitiveCharacter ∧
      analyticOrderNatAt (LFunction χ) (b:ℂ)=1) :
    ∃ d : ℕ, d≤Q ∧ ∀ (q : ℕ) [NeZero q], q≤Q →
      (carriers q s b).card=(if d∣q then 1 else 0) ∧
      ∀ χ ∈ carriers q s b, χ.IsQuadratic ∧ χ ≠ 1 ∧ χ.conductor=d ∧ analyticOrderNatAt (LFunction χ) (b:ℂ)=1 := by
  classical
  by_cases ex : ∃ r : ℕ, ∃ nz : NeZero r, r≤Q ∧ ∃ ψ : DirichletCharacter ℂ r, @active r nz ψ s b
  · obtain ⟨r,nz,rQ,ψ,hψ⟩ := ex
    let d := ψ.conductor
    haveI : NeZero d := ⟨ψ.conductor_ne_zero⟩
    have pos : 0<(b:ℂ).re := by change 0<b;linarith only [hs,hψ.1]
    have off : (b:ℂ)≠1 := fun eqn => (by have e := congrArg Complex.re eqn;simp at e;linarith only [e,hψ.2.1])
    have back := (lift_zero_order ψ.conductor_dvd_level ψ.primitiveCharacter pos off).1
    rw [changeLevel_primitiveCharacter] at back
    have root := back.mp hψ.2.2
    refine ⟨d,(Nat.le_of_dvd (NeZero.pos r) ψ.conductor_dvd_level).trans rQ,?_⟩
    intro q _ qQ
    have char (χ : DirichletCharacter ℂ q) (hχ : active χ s b) :=
      family q r qQ rQ χ ψ hχ hψ
    refine ⟨?_,fun χ hχ => ?_⟩
    · by_cases dv : d∣q
      · rw [ite_eq_left dv,Finset.card_eq_one_iff_existsUnique]
        let φ := changeLevel dv ψ.primitiveCharacter
        have hφ : active φ s b := ⟨hψ.1,hψ.2.1,(lift_zero_order dv ψ.primitiveCharacter pos off).1.mpr root⟩
        refine ⟨φ,mem_carriers.mpr hφ,?_⟩
        intro χ hχ
        obtain ⟨_,_,levels,chars,_⟩ := family q q qQ qQ χ φ (mem_carriers.mp hχ) hφ
        exact induced_ext χ φ levels chars
      · rw [ite_eq_right dv,Finset.card_eq_zero,Finset.eq_empty_iff_forall_notMem]
        intro χ hχ
        have level : χ.conductor=d := (char χ (mem_carriers.mp hχ)).2.2.1
        exact dv (level ▸ χ.conductor_dvd_level)
    · obtain ⟨quad,non',level,_,order⟩ := char χ (mem_carriers.mp hχ)
      exact ⟨quad,non',level,order⟩
  · refine ⟨0,Nat.zero_le Q,?_⟩
    intro q nz qQ
    have empty : carriers q s b=∅ := Finset.eq_empty_iff_forall_notMem.mpr (fun χ hχ =>
      ex ⟨q,nz,qQ,χ,mem_carriers.mp hχ⟩)
    simp [empty,NeZero.ne q]

theorem uniform_family :
    ∃ k C : ℝ, 0<k ∧ 0<C ∧ ∀ x : ℝ, Real.exp 64≤x →
    let u := Real.sqrt (Real.log x)
    let s := 1-k/u
    ∀ (Q : ℕ) [NeZero Q], (Q:ℝ)≤Real.exp u → ∃ (b : ℝ) (d : ℕ), d≤Q ∧
    ∀ (q : ℕ) [NeZero q], q≤Q →
      (carriers q s b).card=(if d∣q then 1 else 0) ∧
      (∀ χ ∈ carriers q s b, χ.IsQuadratic ∧ χ ≠ 1 ∧ χ.conductor=d ∧ analyticOrderNatAt (LFunction χ) (b:ℂ)=1) ∧
      ∀ χ : DirichletCharacter ℂ q,
        ‖(∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, twistedCoefficient χ n)-sharp χ x s b‖≤C*x*Real.exp (-(k*u)) := by
  obtain ⟨a,A,ap,Ap,estimate⟩ := prime_prefix
  obtain ⟨c,cp,cap,page⟩ := ExceptionalZeroInducedLevels.all_characters
  let k := min a (c/2)
  have kp : 0<k := lt_min ap (by positivity)
  have ka : k≤a := min_le_left ..
  have kc : k≤c/2 := min_le_right ..
  refine ⟨k,A+2,kp,by positivity,?_⟩
  intro x hx u s Q _ hQ
  have x1 := (Real.one_le_exp (by norm_num : (0:ℝ)≤64)).trans hx
  have xp := zero_lt_one.trans_le x1
  have lx : 64≤Real.log x := by simpa using Real.log_le_log (Real.exp_pos _) hx
  have lu : Real.log x=u^2 := (Real.sq_sqrt (by linarith)).symm
  have up : 0<u := Real.sqrt_pos.mpr (by linarith)
  have u8 : 8≤u := by nlinarith only [lu,lx,up]
  have L1 := logHeight_ge_one Q 0
  have lp : 0<logHeight Q 0 := zero_lt_one.trans_le L1
  have qp : 0<(Q:ℝ) := by exact_mod_cast NeZero.pos Q
  have lbound : logHeight Q 0≤2*u := by
    rw [logHeight,abs_zero,add_zero,show 2*(Q:ℝ)*2=4*Q by ring,Real.log_mul (by norm_num) qp.ne']
    have qlog := Real.log_le_log qp hQ
    rw [Real.log_exp] at qlog
    linarith only [qlog,u8,Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4)]
  have cut : k/u≤c/logHeight Q 0 := by
    have bound := div_le_div_of_nonneg_left cp.le lp lbound
    apply (div_le_div_of_nonneg_right kc up.le).trans
    calc
      _ = c/(2*u) := by ring
      _ ≤ _ := bound
  obtain ⟨σ,b,σ0,σ1,f⟩ := estimate x hx Q hQ
  have sc : σ≤ s := by
    change σ≤1-8*a/u at σ1
    dsimp [s]
    linarith only [σ1,div_le_div_of_nonneg_right (by linarith only [ka,ap] : k≤8*a) up.le]
  have region (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : active χ s b) :
      inStrip χ (c/logHeight Q 0) 0 (b:ℂ) := by
    refine ⟨?_,by simp,hχ.2.2⟩
    change 1-c/logHeight Q 0≤b
    have gt := hχ.1
    change 1-k/u<b at gt
    linarith
  obtain ⟨d,dQ,conductor⟩ := select_conductor (Q:=Q) (s:=s) (b:=b) (σ0.trans sc) (by
    intro q r _ _ qQ rQ χ ψ hχ hψ
    obtain ⟨qq,nn,level,char,_,_,order⟩ := page Q q r qQ rQ 0 le_rfl χ ψ (b:ℂ) (b:ℂ) (region _ _ hχ) (region _ _ hψ)
    exact ⟨qq,nn,level,char,order⟩)
  refine ⟨b,d,dQ,?_⟩
  intro q _ qQ
  obtain ⟨count,types⟩ := conductor q qQ
  refine ⟨count,types,?_⟩
  intro χ
  let P := ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, twistedCoefficient χ n
  have old := f q qQ χ
  have cuterr := cutoff_error (x:=x) (u:=u) (k:=k) (b:=b) χ x1 up kp lu σ0 sc
  have less : Real.exp (-(a*u)) ≤ Real.exp (-(k*u)) :=
    Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_right ka up.le))
  calc
    _ = ‖(P-sharp χ x σ b)+(sharp χ x σ b-sharp χ x s b)‖ := by congr 1;abel
    _ ≤ ‖P-sharp χ x σ b‖+‖sharp χ x σ b-sharp χ x s b‖ := norm_add_le ..
    _ ≤ A*x*Real.exp (-(k*u))+2*x*Real.exp (-(k*u)) :=
      add_le_add (old.trans (mul_le_mul_of_nonneg_left less (mul_nonneg Ap.le xp.le))) cuterr
    _ = _ := by ring

end Conjectures.Goldbach.ExceptionalZeroPrimeFamily

set_option maxHeartbeats 1800000 in
theorem Conjectures.Goldbach.ExceptionalZeroPrimeFamily :
by
  classical
  let hit := fun {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s b : ℝ) =>
    s<b ∧ b<1 ∧ (χ ≠ 1 ∨ (b:ℂ) ≠ 1) ∧ DirichletCharacter.LFunction χ (b:ℂ)=0
  exact ∃ k C : ℝ, 0<k ∧ 0<C ∧ ∀ x : ℝ, Real.exp 64≤x →
    let u := Real.sqrt (Real.log x)
    let s := 1-k/u
    ∀ (Q : ℕ) [NeZero Q], (Q:ℝ)≤Real.exp u → ∃ (b : ℝ) (d : ℕ), d≤Q ∧
    ∀ (q : ℕ) [NeZero q], q≤Q →
      let S := @Finset.filter (DirichletCharacter ℂ q) (fun χ => hit χ s b)
        (fun _ => Classical.propDecidable _) Finset.univ
      S.card=(if d∣q then 1 else 0) ∧
      (∀ χ ∈ S, χ.IsQuadratic ∧ χ ≠ 1 ∧ χ.conductor=d ∧
        analyticOrderNatAt (DirichletCharacter.LFunction χ) (b:ℂ)=1) ∧
      ∀ χ : DirichletCharacter ℂ q,
        let P := ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, χ (n:ZMod q)*(ArithmeticFunction.vonMangoldt n:ℂ)
        let R := (@ite ℂ (χ=1) (Classical.propDecidable _) 1 0)*(x:ℂ) -
          (@ite ℂ (hit χ s b) (Classical.propDecidable _) ((x^b/b:ℝ):ℂ) 0)
        ‖P-R‖ ≤ C*x*Real.exp (-(k*u)) :=
by
  with_unfolding_all exact ExceptionalZeroPrimeFamily.uniform_family
