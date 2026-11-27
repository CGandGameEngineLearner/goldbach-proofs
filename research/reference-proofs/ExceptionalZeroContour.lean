import Conjectures.Goldbach.ExceptionalZeroInducedLevels

/-! A single zero-avoiding contour for every character of level at most Q.
The possible exceptional zero is real. Two candidate abscissae suffice to
separate the contour from it without knowing the zero in advance. -/

namespace Conjectures.Goldbach.ExceptionalZeroContour

open Complex DirichletCharacter Set Metric
open _root_.Goldbach GoldbachSmoothing GoldbachTwistedMellin
open ExceptionalZeroCatalogue ExceptionalZeroInducedLevels
open scoped Classical Topology

def edge (σ T : ℝ) (u : ℂ) : Prop :=
  σ ≤ u.re ∧ u.re ≤ 2 ∧ |u.im| ≤ T ∧ (u.re=σ ∨ |u.im|=T)

private theorem candidate (b h : ℝ) (hp : 0<h) :
    ∃ σ : ℝ, 1-h/2 ≤ σ ∧ σ ≤ 1-h/4 ∧ h/8 ≤ |σ-b| := by
  by_cases low : b ≤ 1-3*h/8
  · exact ⟨1-h/4,by linarith,le_refl _,(by linarith : h/8 ≤ 1-h/4-b).trans (le_abs_self _)⟩
  · exact ⟨1-h/2,le_refl _,by linarith,(by linarith : h/8 ≤ -(1-h/2-b)).trans (neg_le_abs _)⟩

/-- Keep the same logarithmic width, ordinate, and simple residue throughout
the whole family. The bound applies on the left and both horizontal edges. -/
theorem contour :
    ∃ c C : ℝ, 0<c ∧ c≤1/4 ∧ 0<C ∧ ∀ (Q : ℕ) [NeZero Q] (T : ℝ), 1≤T →
      let L := logHeight Q (T+1)
      let h := c/L
      ∃ σ b : ℝ, 1-h/2≤σ ∧ σ≤1-h/4 ∧
        (∀ (q : ℕ) [NeZero q], q≤Q → ∀ (χ : DirichletCharacter ℂ q) (w : ℂ),
          inStrip χ h (T+1) w → w.re=b ∧ w.im=0 ∧ χ ≠ 1 ∧ analyticOrderNatAt (LFunction χ) w=1) ∧
        (∀ (q : ℕ) [NeZero q], q≤Q → ∀ (χ : DirichletCharacter ℂ q) (u : ℂ),
          edge σ T u →
          (∀ w : ℂ, genuine χ w → h/8 ≤ ‖u-w‖) ∧
          ‖contourLog χ u‖ ≤ C*L^2) := by
  obtain ⟨c,hc,c1,family⟩ := all_characters
  obtain ⟨D,hD,logBound⟩ := norm_logDeriv_regularizedL_le
  let C := D*(1+8/c)+8/c
  refine ⟨c,C,hc,c1,by dsimp [C]; positivity,?_⟩
  intro Q _ T hT L h
  have L1 : 1 ≤ L := logHeight_ge_one Q (T+1)
  have Lp : 0 < L := zero_lt_one.trans_le L1
  have hp : 0 < h := div_pos hc Lp
  have cap : h ≤ 1/4 := (div_le_self hc.le L1).trans c1
  have hr : logHeight Q (T+1) = L := rfl
  have positive : 0 ≤ T+1 := by linarith
  have label : ∃ b : ℝ, ∀ (q : ℕ) [NeZero q], q≤Q →
      ∀ (χ : DirichletCharacter ℂ q) (w : ℂ), inStrip χ h (T+1) w →
        w.re=b ∧ w.im=0 ∧ χ ≠ 1 ∧ analyticOrderNatAt (LFunction χ) w=1 := by
    by_cases hasZero : ∃ (r : ℕ) (nz : NeZero r), r≤Q ∧
        ∃ (ψ : DirichletCharacter ℂ r) (z : ℂ), @inStrip r nz ψ h (T+1) z
    · obtain ⟨r,nz,leQ,ψ,z,hz⟩ := hasZero
      refine ⟨z.re,?_⟩
      intro q _ qQ χ w hw
      obtain ⟨_,non',_,_,equal,real',simple⟩ := family Q q r qQ leQ (T+1) positive χ ψ w z hw hz
      exact ⟨congrArg Complex.re equal,real',non',simple⟩
    · exact ⟨0,fun q i qQ χ w hw => (hasZero ⟨q,i,qQ,χ,w,hw⟩).elim⟩
  obtain ⟨b,label⟩ := label
  obtain ⟨σ,left,right,gap⟩ := candidate b h hp
  refine ⟨σ,b,left,right,label,?_⟩
  intro q _ leQ χ u hu
  obtain ⟨lo,hi,ht,side⟩ := hu
  let d := h/8
  have dp : 0 < d := by dsimp [d];positivity
  have sep (w : ℂ) (zero : genuine χ w) : d ≤ ‖u-w‖ := by
    by_contra! small
    have re := (abs_re_le_norm (u-w)).trans_lt small
    have im := (abs_im_le_norm (u-w)).trans_lt small
    simp only [sub_re,sub_im] at re im
    have wre : 1-h ≤ w.re := by dsimp [d] at re;linarith [(abs_lt.mp re).2]
    have wim : |w.im| ≤ T+1 := by
      have hwi := abs_sub_abs_le_abs_sub w.im u.im
      rw [abs_sub_comm w.im u.im] at hwi
      dsimp [d] at im
      linarith
    obtain ⟨wb,real',_⟩ := label q leQ χ w ⟨wre,wim,zero⟩
    rcases side with es|et
    · rw [es,wb] at re
      exact (not_lt_of_ge gap) re
    · rw [real',sub_zero,et] at im
      dsimp [d] at im
      linarith
  refine ⟨sep,?_⟩
  have Qpos : (0:ℝ) < q := by exact_mod_cast NeZero.pos q
  have qr : (q:ℝ) ≤ Q := by exact_mod_cast leQ
  have LH : logHeight q u.im ≤ L := by
    change Real.log (2*(q:ℝ)*(2+|u.im|)) ≤ Real.log (2*(Q:ℝ)*(2+|T+1|))
    rw [abs_of_nonneg positive]
    apply Real.log_le_log (by positivity)
    gcongr
    linarith
  have reg := logBound q χ u.im u.re d (by linarith) hi dp
    (fun w _ zero => sep w ((regular_zero χ w).mp zero))
  change ‖logDeriv (regularizedL χ) u‖ ≤ D*logHeight q u.im*(1+d⁻¹) at reg
  have poleDist : d ≤ ‖u-1‖ := by
    rcases side with es|et
    · have A := (neg_le_abs (u-1).re).trans (abs_re_le_norm _)
      simp only [sub_re,one_re,es] at A
      dsimp [d];linarith
    · have A := abs_im_le_norm (u-1)
      simp only [sub_im,one_im,sub_zero,et] at A
      dsimp [d];linarith
  have flag : ‖principalFlag χ‖ ≤ 1 := by by_cases e : χ=1 <;> simp [principalFlag,e]
  have pole : ‖principalFlag χ/(u-1)‖ ≤ 1/d := by
    rw [norm_div]
    exact div_le_div₀ zero_le_one flag dp poleDist
  have inv : 1/d=(8/c)*L := by change 1/(c/L/8)=_;field_simp
  have top := norm_add_le (-logDeriv (regularizedL χ) u) (principalFlag χ/(u-1))
  rw [norm_neg] at top
  change ‖-logDeriv (regularizedL χ) u + principalFlag χ/(u-1)‖ ≤ _
  have up : D*logHeight q u.im*(1+d⁻¹) ≤ D*L*(1+d⁻¹) := by gcongr
  rw [← one_div,inv] at up
  rw [← one_div,inv] at reg
  rw [inv] at pole
  have ls : (8/c)*L ≤ (8/c)*L^2 := by
    gcongr; nlinarith [mul_nonneg Lp.le (sub_nonneg.mpr L1)]
  have cost : D*L*(1+(8/c)*L) ≤ D*(1+8/c)*L^2 := by
    calc
      _ ≤ D*L*((1+8/c)*L) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = _ := by ring
  dsimp only [C]
  linarith only [top,reg,up,pole,ls,cost]

end Conjectures.Goldbach.ExceptionalZeroContour

theorem Conjectures.Goldbach.ExceptionalZeroContour :
by
  classical
  exact ∃ c C : ℝ, 0<c ∧ 0<C ∧ ∀ (Q : ℕ) [NeZero Q] (T : ℝ), 1≤T →
    let L := Real.log (2*(Q:ℝ)*(2+|T+1|))
    let h := c/L
    ∃ σ : ℝ, 1-h/2≤σ ∧ σ≤1-h/4 ∧ ∀ (q : ℕ) [NeZero q], q≤Q →
      ∀ (χ : DirichletCharacter ℂ q) (u : ℂ), σ≤u.re → u.re≤2 → |u.im|≤T →
      (u.re=σ ∨ |u.im|=T) →
      (∀ w : ℂ, (χ ≠ 1 ∨ w ≠ 1) → DirichletCharacter.LFunction χ w=0 → h/8≤‖u-w‖) ∧
      ‖logDeriv (DirichletCharacter.LFunction χ) u‖ ≤ C*L^2 :=
by
  obtain ⟨c,C,hc,_,hC,contour⟩ := ExceptionalZeroContour.contour
  refine ⟨c,C,hc,hC,?_⟩
  intro Q _ T hT L h
  obtain ⟨σ,_,lo,hi,_,edges⟩ := contour Q T hT
  have Lp : 0<L := zero_lt_one.trans_le (_root_.Goldbach.logHeight_ge_one Q (T+1))
  have hp : 0<h := div_pos hc Lp
  refine ⟨σ,lo,hi,?_⟩
  intro q _ leQ χ u left right ht side
  obtain ⟨sep,up⟩ := edges q leQ χ u ⟨left,right,ht,side⟩
  have off : u ≠ 1 := by
    intro eu
    rcases side with e|e
    · change σ ≤ 1-h/4 at hi
      rw [eu,Complex.one_re] at e
      linarith
    · rw [eu,Complex.one_im,abs_zero] at e
      linarith
  have ne : DirichletCharacter.LFunction χ u ≠ 0 := by
    intro zero
    have bound := sep u ⟨Or.inr off,zero⟩
    change h/8 ≤ ‖u-u‖ at bound
    simp only [sub_self,norm_zero] at bound
    linarith
  have same : _root_.Goldbach.contourLog χ u = -logDeriv (DirichletCharacter.LFunction χ) u := by
    rw [_root_.Goldbach.contourLog,_root_.Goldbach.logDeriv_regularizedL_eq χ off ne]
    ring
  exact ⟨fun w hw zw => sep w ⟨hw,zw⟩,by simpa only [same,norm_neg,L,_root_.Goldbach.logHeight] using up⟩
