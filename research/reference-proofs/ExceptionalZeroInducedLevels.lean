import Conjectures.Goldbach.DirichletExceptionalZeroRegion

/-! Genuine zeros in the Landau–Page region at imprimitive levels.
The omitted Euler factors preserve analytic order in the open right half-plane.
Thus a primitive exceptional conductor d occurs at precisely floor(Q/d) levels. -/

namespace Conjectures.Goldbach.ExceptionalZeroInducedLevels

open Complex DirichletCharacter Set Metric
open _root_.Goldbach GoldbachSmoothing
open ExceptionalZeroCatalogue
open scoped Classical Topology

private noncomputable def factors {r : ℕ} (χ : DirichletCharacter ℂ r) (n : ℕ) (z : ℂ) : ℂ :=
  ∏ p ∈ n.primeFactors, (1-χ p*(p:ℂ)^(-z))

private theorem factors_ne {r : ℕ} (χ : DirichletCharacter ℂ r) (n : ℕ) {z : ℂ}
    (right : 0 < z.re) : factors χ n z ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  have prime := Nat.prime_of_mem_primeFactors hp
  have normp : ‖(p:ℂ)^(-z)‖ < 1 := by
    rw [norm_natCast_cpow_of_pos prime.pos,neg_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast prime.one_lt) (neg_lt_zero.mpr right)
  have normlt : ‖χ p*(p:ℂ)^(-z)‖ < 1 := by
    rw [norm_mul]
    calc
      _ ≤ 1*‖(p:ℂ)^(-z)‖ := mul_le_mul_of_nonneg_right (χ.norm_le_one _) (norm_nonneg _)
      _ < _ := by simpa using normp
  intro zero
  simp only [← sub_eq_zero.mp zero,norm_one,lt_self_iff_false] at normlt

private theorem analytic_factors {r : ℕ} (χ : DirichletCharacter ℂ r) (n : ℕ) (z : ℂ) :
    AnalyticAt ℂ (factors χ n) z := by
  have diff : Differentiable ℂ (factors χ n) := by
    unfold factors
    apply Differentiable.fun_finsetProd
    intro p hp
    have : NeZero p := ⟨(Nat.prime_of_mem_primeFactors hp).ne_zero⟩
    fun_prop
  exact diff.analyticAt z

/-- The equality holds for analytic orders themselves, including order zero.
The pole of the principal character at one is excluded. -/
theorem lift_zero_order {r n : ℕ} [NeZero r] [NeZero n] (d : r ∣ n)
    (χ : DirichletCharacter ℂ r) {z : ℂ} (right : 0 < z.re) (off : z ≠ 1) :
    (genuine (changeLevel d χ) z ↔ genuine χ z) ∧
    analyticOrderAt (LFunction (changeLevel d χ)) z = analyticOrderAt (LFunction χ) z := by
  have fn := factors_ne χ n right
  have g : LFunction (changeLevel d χ) =ᶠ[𝓝 z] (LFunction χ * factors χ n) := by
    filter_upwards [isOpen_compl_singleton.mem_nhds (x:=z) off] with u hu
    exact LFunction_changeLevel d χ (Or.inr hu)
  have ag := analytic_factors χ n z
  have af : AnalyticAt ℂ (LFunction χ) z := by
    apply DifferentiableOn.analyticOnNhd (s:=({1}ᶜ:Set ℂ)) _ isOpen_compl_singleton z off
    exact fun u hu => (differentiableAt_LFunction χ u (Or.inl hu)).differentiableWithinAt
  constructor
  · change ((_ ∨ _) ∧ _ = 0) ↔ ((_ ∨ _) ∧ _ = 0)
    rw [show LFunction (changeLevel d χ) z = LFunction χ z*factors χ n z from g.self_of_nhds]
    simp [off,fn]
  · rw [analyticOrderAt_congr g,analyticOrderAt_mul af ag,ag.analyticOrderAt_eq_zero.mpr fn,add_zero]

def inStrip {n : ℕ} [NeZero n] (χ : DirichletCharacter ℂ n) (h T : ℝ) (z : ℂ) : Prop :=
  1-h ≤ z.re ∧ |z.im| ≤ T ∧ genuine χ z

private theorem lift_heq {r s n : ℕ} (dr : r ∣ n) (ds : s ∣ n)
    (χ : DirichletCharacter ℂ r) (ψ : DirichletCharacter ℂ s) (same : r=s) (eqv : HEq χ ψ) :
    changeLevel dr χ = changeLevel ds ψ := by
  subst s
  cases eq_of_heq eqv
  rfl

theorem all_characters :
    ∃ c : ℝ, 0<c ∧ c≤1/4 ∧ ∀ (Q r s : ℕ) [NeZero r] [NeZero s],
      r≤Q → s≤Q → ∀ (T : ℝ), 0≤T → ∀ (χ : DirichletCharacter ℂ r) (ψ : DirichletCharacter ℂ s)
      (z w : ℂ), let h := c/logHeight Q T
      inStrip χ h T z → inStrip ψ h T w →
      χ.IsQuadratic ∧ χ ≠ 1 ∧ χ.conductor=ψ.conductor ∧ HEq χ.primitiveCharacter ψ.primitiveCharacter ∧
      z=w ∧ z.im=0 ∧ analyticOrderNatAt (LFunction χ) z=1 := by
  obtain ⟨a,ha,page⟩ := DirichletExceptionalZeroRegion.full_page
  let c := min a (1/4)
  have hc : 0<c := lt_min ha (by norm_num)
  have c1 : c ≤ 1/4 := min_le_right _ _
  refine ⟨c,hc,c1,?_⟩
  intro Q r s _ _ hr hs T hT χ ψ z w h hχ hψ
  have : NeZero Q := ⟨((NeZero.pos r).trans_le hr).ne'⟩
  have L1 := logHeight_ge_one Q T
  have Lp : 0<logHeight Q T := zero_lt_one.trans_le L1
  have cap : h ≤ 1/4 := (div_le_self hc.le L1).trans c1
  have width : h ≤ a/logHeight Q T := div_le_div_of_nonneg_right (min_le_left _ _) Lp.le
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have : NeZero ψ.conductor := ⟨ψ.conductor_ne_zero⟩
  have lift (n : ℕ) [NeZero n] (θ : DirichletCharacter ℂ n) (v : ℂ) (hv : inStrip θ h T v)
      [NeZero θ.conductor] : genuine θ.primitiveCharacter v ∧
      analyticOrderAt (LFunction θ) v = analyticOrderAt (LFunction θ.primitiveCharacter) v := by
    have low := hv.1
    have hi : v.re < 1 := lt_of_not_ge fun e => regular_ne θ v e ((regular_zero θ v).mpr hv.2.2)
    have off : v ≠ 1 := fun e => (by simp [e] at hi)
    have L := lift_zero_order θ.conductor_dvd_level θ.primitiveCharacter (by linarith : 0<v.re) off
    rw [changeLevel_primitiveCharacter] at L
    exact ⟨L.1.mp hv.2.2,L.2⟩
  obtain ⟨uz,order⟩ := lift r χ z hχ
  obtain ⟨uw,_⟩ := lift s ψ w hψ
  have rd := (Nat.le_of_dvd (NeZero.pos r) χ.conductor_dvd_level).trans hr
  have sd := (Nat.le_of_dvd (NeZero.pos s) ψ.conductor_dvd_level).trans hs
  obtain ⟨quad,nontrivial,levels,characters,eqv,real',simple⟩ :=
    page Q χ.conductor ψ.conductor rd sd T hT χ.primitiveCharacter ψ.primitiveCharacter
      χ.primitiveCharacter_isPrimitive ψ.primitiveCharacter_isPrimitive z w
      (by linarith only [hχ.1,width]) hχ.2.1 uz (by linarith only [hψ.1,width]) hψ.2.1 uw
  have quad' : χ.IsQuadratic := by
    rw [← χ.changeLevel_primitiveCharacter,MulChar.isQuadratic_iff_sq_eq_one,← map_pow,quad.sq_eq_one,map_one]
  have non' : χ ≠ 1 := fun e => nontrivial ((changeLevel_eq_one_iff χ.conductor_dvd_level).mp
    (χ.changeLevel_primitiveCharacter.trans e))
  exact ⟨quad',non',levels,characters,eqv,real',(congrArg ENat.toNat order).trans simple⟩

def occurs (n : ℕ) (h T : ℝ) (z : ℂ) : Prop :=
  ∃ hn : NeZero n, ∃ χ : DirichletCharacter ℂ n, @inStrip n hn χ h T z

/-- At each multiple of its primitive conductor exactly one induced
character has the exceptional zero. This counts all levels carrying it. -/
theorem level_count :
    ∃ c : ℝ, 0<c ∧ ∀ (Q r : ℕ) [NeZero r], r≤Q → ∀ (T : ℝ), 0≤T →
    ∀ (χ : DirichletCharacter ℂ r), χ.IsPrimitive → ∀ (z : ℂ),
    let h := c/logHeight Q T
    inStrip χ h T z →
      (∀ (n : ℕ) [NeZero n], n≤Q →
        ((∃! ψ : DirichletCharacter ℂ n, inStrip ψ h T z) ↔ r ∣ n)) ∧
      ((Finset.Ioc 0 Q).filter (fun n => occurs n h T z)).card = Q/r := by
  obtain ⟨c,hc,c1,all⟩ := all_characters
  refine ⟨c,hc,?_⟩
  intro Q r _ hr T hT χ prim z h hz
  have : NeZero Q := ⟨((NeZero.pos r).trans_le hr).ne'⟩
  have cap : h ≤ 1/4 := (div_le_self hc.le (logHeight_ge_one Q T)).trans c1
  have right : 0<z.re := by linarith only [hz.1,cap]
  have hi : z.re<1 := lt_of_not_ge fun e => regular_ne χ z e ((regular_zero χ z).mpr hz.2.2)
  have off : z ≠ 1 := fun e => (by simp [e] at hi)
  have necessary (n : ℕ) [NeZero n] (hn : n ≤ Q) (ψ : DirichletCharacter ℂ n)
      (hw : inStrip ψ h T z) : r ∣ n := by
    have eqn := (all Q r n hr hn T hT χ ψ z z hz hw).2.2.1
    rw [show r=ψ.conductor from prim.symm.trans eqn]
    exact ψ.conductor_dvd_level
  have induced (n : ℕ) [NeZero n] (hn : n ≤ Q) (d : r ∣ n) :
      ∃! ψ : DirichletCharacter ℂ n, inStrip ψ h T z := by
    let φ := changeLevel d χ
    have hv : inStrip φ h T z := ⟨hz.1,hz.2.1,(lift_zero_order d χ right off).1.mpr hz.2.2⟩
    refine ⟨φ,hv,?_⟩
    intro ψ hw
    obtain ⟨_,_,leq,ceq,_⟩ := all Q n n hn hn T hT ψ φ z z hw hv
    simpa only [changeLevel_primitiveCharacter] using
      lift_heq ψ.conductor_dvd_level φ.conductor_dvd_level ψ.primitiveCharacter φ.primitiveCharacter leq ceq
  constructor
  · intro n _ hn
    exact ⟨fun ⟨ψ,hw,_⟩ => necessary n hn ψ hw,induced n hn⟩
  · have seteq : (Finset.Ioc 0 Q).filter (fun n => occurs n h T z) =
        (Finset.Ioc 0 Q).filter (fun n => r ∣ n) := by
      apply Finset.filter_congr
      intro n hn
      obtain ⟨hp,leQ⟩ := Finset.mem_Ioc.mp hn
      have nz : NeZero n := ⟨hp.ne'⟩
      constructor
      · rintro ⟨_,ψ,hw⟩
        exact necessary n leQ ψ hw
      · intro d
        obtain ⟨θ,hw,_⟩ := induced n leQ d
        exact ⟨nz,θ,hw⟩
    rw [seteq,Nat.Ioc_filter_dvd_card_eq_div]

end Conjectures.Goldbach.ExceptionalZeroInducedLevels

theorem Conjectures.Goldbach.ExceptionalZeroInducedLevels :
by
  classical
  let Z := fun {n : ℕ} [NeZero n] (χ : DirichletCharacter ℂ n) (h T : ℝ) (z : ℂ) =>
    1-h ≤ z.re ∧ |z.im| ≤ T ∧ (χ ≠ 1 ∨ z ≠ 1) ∧ DirichletCharacter.LFunction χ z=0
  exact ∃ c : ℝ, 0<c ∧ ∀ (Q r : ℕ) [NeZero r], r≤Q → ∀ (T : ℝ), 0≤T →
    ∀ (χ : DirichletCharacter ℂ r), χ.IsPrimitive → ∀ (z : ℂ),
    let h := c/Real.log (2*(Q:ℝ)*(2+|T|))
    Z χ h T z →
      (∀ (n : ℕ) [NeZero n], n≤Q → ((∃! ψ : DirichletCharacter ℂ n, Z ψ h T z) ↔ r ∣ n)) ∧
      ((Finset.Ioc 0 Q).filter (fun n => ∃ hn : NeZero n, ∃ ψ : DirichletCharacter ℂ n,
        @Z n hn ψ h T z)).card = Q/r :=
by
  classical
  obtain ⟨c,hc,levels⟩ := ExceptionalZeroInducedLevels.level_count
  refine ⟨c,hc,?_⟩
  intro Q r _ hr T hT χ prim z h hz
  obtain ⟨each,total⟩ := levels Q r hr T hT χ prim z hz
  refine ⟨each,?_⟩
  convert total using 2
  ext n
  simp [ExceptionalZeroInducedLevels.occurs,ExceptionalZeroInducedLevels.inStrip,
    ExceptionalZeroCatalogue.genuine,h,_root_.Goldbach.logHeight]
