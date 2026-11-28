import Conjectures.Goldbach.ExceptionalZeroContour

/-! The exact twisted prime-power window with a common possible residue.
All levels, windows, and additive frequencies use the same contour and zero.
The horizontal, left vertical, and infinite right-tail errors retain their signs. -/

namespace Conjectures.Goldbach.ExceptionalZeroTwistedWindow

open Complex DirichletCharacter Set Metric
open _root_.Goldbach GoldbachSmoothing GoldbachTwistedMellin
open ExceptionalZeroCatalogue ExceptionalZeroInducedLevels ExceptionalZeroContour
open scoped Classical Topology

def active {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (σ b : ℝ) : Prop :=
  σ < b ∧ b < 1 ∧ genuine χ (b:ℂ)

theorem common_box :
    ∃ c C : ℝ, 0<c ∧ c≤1/4 ∧ 0<C ∧ ∀ (Q : ℕ) [NeZero Q] (T : ℝ), 1≤T →
      let L := logHeight Q (T+1)
      let h := c/L
      ∃ σ b : ℝ, 1-h/2≤σ ∧ σ≤1-h/4 ∧
      ∀ (q : ℕ) [NeZero q], q≤Q → ∀ χ : DirichletCharacter ℂ q,
        (∀ u : ℂ, edge σ T u → ‖contourLog χ u‖ ≤ C*L^2) ∧
        (∀ w ∈ boxZeros χ σ 2 (-T) T, σ < w.re ∧ w.re < 2 ∧ -T < w.im ∧ w.im < T) ∧
        (∀ K : ℂ → ℂ, ∑ w ∈ boxZeros χ σ 2 (-T) T, (analyticOrderNatAt (regularizedL χ) w : ℂ)*K w =
          if active χ σ b then K (b:ℂ) else 0) := by
  obtain ⟨c,C,hc,c1,hC,contour⟩ := ExceptionalZeroContour.contour
  refine ⟨c,C,hc,c1,hC,?_⟩
  intro Q _ T hT L h
  obtain ⟨σ,b,left,right,label,avoid⟩ := contour Q T hT
  have hp : 0<h := div_pos hc (zero_lt_one.trans_le (logHeight_ge_one Q (T+1)))
  refine ⟨σ,b,left,right,?_⟩
  intro q _ leQ χ
  let S := boxZeros χ σ 2 (-T) T
  have info (w : ℂ) (hw : w ∈ S) : w=(b:ℂ) ∧ σ<w.re ∧ w.re<1 ∧ w.im=0 ∧
      genuine χ w ∧ analyticOrderNatAt (regularizedL χ) w=1 := by
    obtain ⟨inside,zero⟩ := (mem_boxZeros χ σ 2 (-T) T w).mp hw
    obtain ⟨re,im⟩ := mem_reProdIm.mp inside
    have low := re.1
    have up := re.2
    have imag := abs_le.mpr im
    have gw := (regular_zero χ w).mp zero
    have strip : inStrip χ h (T+1) w := ⟨by linarith only [low,left,hp],by linarith,gw⟩
    obtain ⟨wb,real',non',simple⟩ := label q leQ χ w strip
    have eqn : w=(b:ℂ) := Complex.ext wb real'
    have strict : σ < w.re := by
      by_contra! le
      have e := le_antisymm le low
      have d := (avoid q leQ χ w ⟨low,up,imag,Or.inl e⟩).1 w gw
      change h/8 ≤ ‖w-w‖ at d
      simp only [sub_self,norm_zero] at d
      linarith
    have below : w.re < 1 := lt_of_not_ge (fun e => regular_ne χ w e zero)
    exact ⟨eqn,strict,below,real',gw,by simpa only [regularizedL,ite_eq_right non'] using simple⟩
  refine ⟨fun u hu => (avoid q leQ χ u hu).2,?_,?_⟩
  · intro w hw
    obtain ⟨_,hs,hu,real',_,_⟩ := info w hw
    exact ⟨hs,by linarith,by linarith,by linarith⟩
  · intro K
    by_cases selected : active χ σ b
    · have member : (b:ℂ) ∈ S := by
        apply (mem_boxZeros χ σ 2 (-T) T _).mpr
        exact ⟨mem_reProdIm.mpr ⟨⟨selected.1.le,by change b≤2;linarith only [selected.2.1]⟩,
          by change -T≤0 ∧ 0≤T; constructor <;> linarith⟩,(regular_zero χ _).mpr selected.2.2⟩
      have one : S = {(b:ℂ)} := Finset.ext (fun w => by
        rw [Finset.mem_singleton];exact ⟨fun hw => (info w hw).1,fun eqn => eqn ▸ member⟩)
      have simple := (info _ member).2.2.2.2.2
      change ∑ w ∈ S, _ = _
      rw [one,Finset.sum_singleton,simple,ite_eq_left selected]
      simp
    · have empty : S = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (by
        intro w hw
        obtain ⟨eqn,lo,hi,_,gw,_⟩ := info w hw
        subst w
        exact selected ⟨lo,hi,gw⟩)
      change ∑ w ∈ S, _ = _
      rw [empty,Finset.sum_empty,ite_eq_right selected]

/-- An exact decomposition for actual von Mangoldt coefficients and any
additive twist in the native dyadic window, using one common real ordinate. -/
theorem windows :
    ∃ c C : ℝ, 0<c ∧ 0<C ∧ ∀ (Q : ℕ) [NeZero Q] (T : ℝ), 1≤T →
      let L := logHeight Q (T+1)
      let h := c/L
      ∃ σ b : ℝ, 1-h/2≤σ ∧ σ≤1-h/4 ∧
      ∀ (q : ℕ) [NeZero q], q≤Q → ∀ χ : DirichletCharacter ℂ q,
        (∀ u : ℂ, edge σ T u → ‖contourLog χ u‖ ≤ C*L^2) ∧
        ∀ (l r : ℕ) (X θ : ℝ), 1≤X → X≤(l:ℝ) → (l:ℝ)+1≤r → (r:ℝ)+1≤2*X → |θ|≤1 →
        (∑ n ∈ Finset.Ioc l r, twistedCoefficient χ n*phase θ n) =
          principalFlag χ*transform l r θ 1 - (if active χ σ b then transform l r θ (b:ℂ) else 0) +
          contourRemainder χ l r θ σ T + truncationRemainder χ l r θ T := by
  obtain ⟨c,C,hc,_,hC,box⟩ := common_box
  refine ⟨c,C,hc,hC,?_⟩
  intro Q _ T hT L h
  have hp : 0<h := div_pos hc (zero_lt_one.trans_le (logHeight_ge_one Q (T+1)))
  obtain ⟨σ,b,left,right,family⟩ := box Q T hT
  refine ⟨σ,b,left,right,?_⟩
  intro q _ leQ χ
  obtain ⟨side,inside,residue⟩ := family q leQ χ
  refine ⟨side,?_⟩
  intro l r X θ X1 leL lr leR freq
  have σ1 : σ < 1 := by change σ≤1-h/4 at right;linarith
  have eqn := exact_twisted_box χ X1 leL lr leR freq σ1 (by linarith : 0<T) inside
  simpa only [zeroContribution,residue] using eqn

end Conjectures.Goldbach.ExceptionalZeroTwistedWindow

set_option maxHeartbeats 1800000 in
theorem Conjectures.Goldbach.ExceptionalZeroTwistedWindow :
by
  classical
  let phase := fun (θ x : ℝ) => Complex.exp (((θ*x:ℝ):ℂ)*Complex.I)
  let K := fun (l r θ : ℝ) => mellin (fun x : ℝ =>
    ((max 0 (min (x-l) (min 1 (r+1-x))) : ℝ):ℂ)*phase θ x)
  let flag := fun {q : ℕ} (χ : DirichletCharacter ℂ q) => if χ=1 then (1:ℂ) else 0
  let F := fun {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (l r θ u t : ℝ) =>
    let s := (u:ℂ)+(t:ℂ)*Complex.I
    let G := if χ=1 then DirichletCharacter.LFunctionTrivChar₁ q else DirichletCharacter.LFunction χ
    (-logDeriv G s+flag χ/(s-1))*K l r θ s
  let J := fun (f : ℝ → ℂ) (a b : ℝ) => intervalIntegral f a b MeasureTheory.volume
  let scale := 1/(2*Real.pi)
  exact ∃ c : ℝ, 0<c ∧ ∀ (Q : ℕ) [NeZero Q] (T : ℝ), 1≤T →
    let h := c/Real.log (2*(Q:ℝ)*(2+|T+1|))
    ∃ σ b : ℝ, 1-h/2≤σ ∧ σ≤1-h/4 ∧ ∀ (q : ℕ) [NeZero q], q≤Q →
    ∀ (χ : DirichletCharacter ℂ q) (l r : ℕ) (X θ : ℝ), 1≤X → X≤(l:ℝ) →
      (l:ℝ)+1≤r → (r:ℝ)+1≤2*X → |θ|≤1 →
      let W := F χ l r θ
      (∑ n ∈ Finset.Ioc l r, χ (n:ZMod q)*(ArithmeticFunction.vonMangoldt n:ℂ)*phase θ n) =
      flag χ*K l r θ 1 -
        (if σ<b ∧ b<1 ∧ (χ ≠ 1 ∨ (b:ℂ) ≠ 1) ∧ DirichletCharacter.LFunction χ (b:ℂ)=0
         then K l r θ (b:ℂ) else 0) +
      scale • (J (W σ) (-T) T + Complex.I*(J (fun u => W u (-T)) σ 2 - J (fun u => W u T) σ 2)) +
      scale • (MeasureTheory.integral MeasureTheory.volume (W 2) - J (W 2) (-T) T) :=
by
  obtain ⟨c,_,hc,_,windows⟩ := ExceptionalZeroTwistedWindow.windows
  refine ⟨c,hc,?_⟩
  intro Q _ T ht h
  obtain ⟨σ,b,lo,hi,f⟩ := windows Q T ht
  refine ⟨σ,b,lo,hi,?_⟩
  intro q _ leQ χ l r X θ X1 leL lr leR freq
  have formula := (f q leQ χ).2 l r X θ X1 leL lr leR freq
  have testEq (a d θ' : ℝ) : GoldbachTwistedMellin.test a d θ' =
      (fun x : ℝ => ((max 0 (min (x-a) (min 1 (d+1-x))) : ℝ):ℂ)*
        Complex.exp (((θ'*x:ℝ):ℂ)*Complex.I)) := rfl
  dsimp only at ⊢
  by_cases e : σ<b ∧ b<1 ∧ (χ ≠ 1 ∨ (b:ℂ) ≠ 1) ∧ DirichletCharacter.LFunction χ (b:ℂ)=0
  all_goals by_cases principal : χ=1
  all_goals
    simp only [ExceptionalZeroTwistedWindow.active,ExceptionalZeroCatalogue.genuine,
      GoldbachTwistedMellin.contourRemainder,GoldbachTwistedMellin.truncationRemainder,
      GoldbachTwistedMellin.integrand,GoldbachTwistedMellin.line,_root_.Goldbach.contourLog,
      _root_.Goldbach.regularizedL,_root_.Goldbach.principalFlag,GoldbachTwistedMellin.transform,
      testEq,GoldbachTwistedMellin.phase,
      GoldbachSmoothing.twistedCoefficient,Pi.mul_apply] at formula
    simpa only [e,principal,true_and,and_true,ite_true,ite_false] using formula
