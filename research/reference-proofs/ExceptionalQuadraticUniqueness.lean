import Conjectures.Goldbach.NearOneZeroMultiplicity

/-! A Landau–Page bound for quadratic characters at low height. The
Dirichlet coefficients in the four-character argument are nonnegative.
The uniform disk estimate then compares the two candidate zero terms
against the single pole of zeta. -/

namespace Conjectures.Goldbach.ExceptionalQuadraticUniqueness

open Complex DirichletCharacter Metric Set Filter
open _root_.Goldbach GoldbachSmoothing
open ExceptionalZeroCatalogue NearOneZeroMultiplicity
open scoped Classical Topology ComplexConjugate

private theorem four_character {q : ℕ} [NeZero q] (χ ψ : DirichletCharacter ℂ q)
    (hχ : χ.IsQuadratic) (hψ : ψ.IsQuadratic) {x : ℝ} (hx : 1<x) :
    (logDeriv riemannZeta (x:ℂ)).re + (logDeriv (LFunction χ) (x:ℂ)).re +
      (logDeriv (LFunction ψ) (x:ℂ)).re + (logDeriv (LFunction (χ*ψ)) (x:ℂ)).re ≤ 0 := by
  let f : ℕ → ℂ := fun n => (ArithmeticFunction.vonMangoldt n : ℂ)
  let g := f + twistedCoefficient χ + twistedCoefficient ψ + twistedCoefficient (χ*ψ)
  have hs : 1<(x:ℂ).re := hx
  have hf : LSeriesSummable f (x:ℂ) := ArithmeticFunction.LSeriesSummable_vonMangoldt hs
  have hsum (θ : DirichletCharacter ℂ q) : LSeriesSummable (twistedCoefficient θ) (x:ℂ) :=
    θ.LSeriesSummable_twist_vonMangoldt hs
  have summ : LSeriesSummable g (x:ℂ) := ((hf.add (hsum χ)).add (hsum ψ)).add (hsum _)
  have pos : 0 ≤ (LSeries g (x:ℂ)).re := by
    open scoped ComplexOrder in
    have coeff (n : ℕ) : 0 ≤ g n := by
      have oneplus (θ : DirichletCharacter ℂ q) (hθ : θ.IsQuadratic) : 0≤1+θ (n:ZMod q) := by
        rcases hθ (n:ZMod q) with e|e|e <;> rw [e] <;> norm_num
      have fac : g n = ((1+χ (n:ZMod q))*(1+ψ (n:ZMod q)))*f n := by
        simp [g,twistedCoefficient,f,MulChar.mul_apply];ring
      rw [fac]
      exact mul_nonneg (mul_nonneg (oneplus χ hχ) (oneplus ψ hψ))
        (Complex.zero_le_real.mpr ArithmeticFunction.vonMangoldt_nonneg)
    rw [LSeries,Complex.re_tsum summ]
    exact tsum_nonneg fun n => (LSeries.term_nonneg (coeff n) x).1
  have zeta : LSeries f (x:ℂ) = -logDeriv riemannZeta (x:ℂ) := by
    simpa [logDeriv,neg_div] using ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs
  dsimp only [g] at pos
  rw [LSeries_add ((hf.add (hsum χ)).add (hsum ψ)) (hsum _),
    LSeries_add (hf.add (hsum χ)) (hsum ψ),LSeries_add hf (hsum χ),zeta,
    LSeries_twistedCoefficient_eq χ hs,LSeries_twistedCoefficient_eq ψ hs,
    LSeries_twistedCoefficient_eq (χ*ψ) hs] at pos
  simp only [add_re,neg_re] at pos
  linarith

private theorem disk_at_zero {h : ℝ} {z : ℂ} (hh : h≤1/8)
    (lo : 1-h ≤ z.re) (hi : z.re ≤ 1) (ht : |z.im|≤h) :
    z ∈ closedBall (⟨2,0⟩:ℂ) (33/25) := by
  rw [mem_closedBall_iff_norm]
  have k := norm_le_abs_re_add_abs_im (z-(⟨2,0⟩:ℂ))
  change ‖_‖ ≤ |z.re-2|+|z.im-0| at k
  rw [sub_zero,abs_of_nonpos (by linarith : z.re-2 ≤ 0)] at k
  linarith

/-- Two distinct quadratic nonprincipal characters at the same modulus
cannot each contribute a zero to the same small box about 1. -/
theorem one_character_at_level :
    ∃ c : ℝ, 0<c ∧ ∀ (q : ℕ) [NeZero q] (χ ψ : DirichletCharacter ℂ q),
      χ.IsQuadratic → ψ.IsQuadratic → χ ≠ 1 → ψ ≠ 1 →
      ∀ (h : ℝ) (z w : ℂ), 0<h → h≤c/logHeight q 0 →
        1-h≤z.re → |z.im|≤h → genuine χ z → 1-h≤w.re → |w.im|≤h → genuine ψ w → χ=ψ := by
  obtain ⟨_,_,potential⟩ := disk_potential
  obtain ⟨D,hD,right⟩ := right_edge
  let C := D+3*694400+1
  have hC : 1 ≤ C := by dsimp [C];linarith
  have Cp : 0<C := by linarith
  let c := 1/(64*C)
  have hc : 0<c := by dsimp [c];positivity
  refine ⟨c,hc,?_⟩
  intro q _ χ ψ hχ hψ nχ nψ h z w hp hsmall hz hiz zz hw hiw zw
  by_contra diff
  have nprod : χ*ψ ≠ 1 := by
    intro e
    exact diff ((eq_inv_of_mul_eq_one_left e).trans hψ.inv)
  let L := logHeight q 0
  have hL : 1 ≤ L := logHeight_ge_one q 0
  have Lp : 0<L := by linarith
  have cap : h ≤ 1/(64*(C*L)) := by
    convert hsmall using 1
    dsimp [c,L];rw [div_div];ring
  have limit : 64*(C*L)*h ≤ 1 := by
    rw [mul_comm];exact (le_div_iff₀ (by positivity)).mp cap
  have h8 : 0<8*h := by positivity
  have h' : h≤1/8 := by
    apply cap.trans
    apply one_div_le_one_div_of_le (by norm_num)
    linarith [one_le_mul_of_one_le_of_one_le hC hL]
  have h8' : 8*h≤1 := by linarith
  let s : ℂ := ⟨1+8*h,0⟩
  let LD := fun (θ : DirichletCharacter ℂ q) => (logDeriv (LFunction θ) s).re
  let E := 694400*L
  have single (θ : DirichletCharacter ℂ q) (nθ : θ ≠ 1) (v : ℂ) (lo : 1-h≤v.re)
      (ti : |v.im|≤h) (zero : genuine θ v) : 3 ≤ 32*h*(LD θ+E) := by
    have upper : v.re ≤ 1 := le_of_lt (lt_of_not_ge fun e => regular_ne θ v e ((regular_zero θ v).mpr zero))
    have k := near_kernel hp lo upper (by simpa using ti : |v.im-0|≤h)
    have pot := (potential q θ 0 (8*h) h8 h8' {v} (by
      intro v' hv; obtain rfl := Finset.mem_singleton.mp hv;exact ⟨disk_at_zero h' lo upper ti,zero⟩)).1
    change _ ≤ LD θ + (principalFlag θ/(s-1)).re + E at pot
    simp [principalFlag,nθ] at pot
    have m : (1:ℝ) ≤ (analyticOrderNatAt (regularizedL θ) v:ℝ) := by
      exact_mod_cast (order_positive θ zero).1
    have kn : 0 ≤ kernel s v := by
      change 0 ≤ (1+8*h-v.re)/_
      exact div_nonneg (by linarith) (normSq_nonneg _)
    exact k.trans (mul_le_mul_of_nonneg_left
      ((le_mul_of_one_le_left kn m).trans pot) (by positivity))
  have empty := (potential q (χ*ψ) 0 (8*h) h8 h8' ∅ (by simp)).1
  change _ ≤ LD (χ*ψ) + (principalFlag (χ*ψ)/(s-1)).re + E at empty
  simp [principalFlag,nprod] at empty
  have comb := four_character χ ψ hχ hψ (show 1<1+8*h by linarith)
  have tot : (logDeriv riemannZeta s).re + LD χ + LD ψ + LD (χ*ψ) ≤ 0 := comb
  have eqn : LFunction (1 : DirichletCharacter ℂ 1) = riemannZeta := LFunction_modOne_eq
  have r := right 1 (1 : DirichletCharacter ℂ 1) (8*h) 0 h8 h8'
  rw [eqn] at r
  have pole : -(logDeriv riemannZeta s).re ≤ 1/(8*h)+D :=
    ((neg_le_abs _).trans (abs_re_le_norm _)).trans r
  have inv : 32*h*(1/(8*h))=4 := by field_simp;ring
  have sum : LD χ+LD ψ+2*E ≤ 1/(8*h)+D+3*E := by linarith
  have both := add_le_add (single χ nχ z hz hiz zz) (single ψ nψ w hw hiw zw)
  have mul := mul_le_mul_of_nonneg_left sum (by positivity : 0≤32*h)
  have cost : D+3*E ≤ C*L := by
    dsimp [C,E];nlinarith [mul_nonneg hD (sub_nonneg.mpr hL)]
  have saving := mul_le_mul_of_nonneg_left cost (by positivity : 0≤32*h)
  linarith only [both,mul,inv,limit,saving]

/- The continuation argument follows the conjugation identity for
primitive real characters in the verified DyadicCellShortPrimeFloor.
Here the quadratic character may have any positive modulus. -/
theorem conjugate_value {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsQuadratic) (hn : χ ≠ 1) (s : ℂ) : LFunction χ (conj s) = conj (LFunction χ s) := by
  let f := LFunction χ
  let g := conj ∘ f ∘ conj
  have hf := differentiable_LFunction hn
  have hg : Differentiable ℂ g := fun z => by
    simpa only [g,Complex.conj_conj] using (hf (conj z)).conj_conj
  have hr (z : ℂ) (hz : 1<z.re) : f (conj z) = conj (f z) := by
    dsimp [f]
    rw [χ.LFunction_eq_LSeries (by simpa using hz),χ.LFunction_eq_LSeries hz]
    change (∑' n, LSeries.term _ (conj z) n) = conj (∑' n, LSeries.term _ z n)
    rw [Complex.conj_tsum]
    apply tsum_congr
    intro n
    by_cases e : n=0
    · subst n;simp
    rw [LSeries.term_of_ne_zero e,LSeries.term_of_ne_zero e]
    have arg : (n:ℂ).arg ≠ Real.pi := by
      rw [show (n:ℂ)=((n:ℝ):ℂ) from rfl,Complex.arg_ofReal_of_nonneg (Nat.cast_nonneg n)]
      exact Real.pi_pos.ne
    rw [Complex.cpow_conj _ _ arg,map_div₀]
    change χ (n:ZMod q) / _ = conj (χ (n:ZMod q)) / _
    rcases hχ (n:ZMod q) with a|a|a <;> simp [a]
  have same : g =ᶠ[𝓝 (2:ℂ)] f := by
    filter_upwards [(show IsOpen {u : ℂ | (1:ℝ)<u.re} from
      isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (1:ℝ)<(2:ℂ).re by norm_num)] with z hz
    simp only [g,Function.comp_apply,hr z hz,Complex.conj_conj]
  have all : g = f := (hg.differentiableOn.analyticOnNhd isOpen_univ).eq_of_eventuallyEq
    (hf.differentiableOn.analyticOnNhd isOpen_univ) same
  have eqn := congrFun all s
  change conj (f (conj s))=f s at eqn
  simpa [f] using congrArg conj eqn

theorem simple_real_at_level :
    ∃ c : ℝ, 0<c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsQuadratic → χ ≠ 1 → ∀ (h : ℝ), h≤c/logHeight q 0 →
      ∀ z w : ℂ, 1-h≤z.re → |z.im|≤h → genuine χ z →
        1-h≤w.re → |w.im|≤h → genuine χ w →
        z=w ∧ z.im=0 ∧ analyticOrderNatAt (LFunction χ) z=1 := by
  obtain ⟨c,hc,unique⟩ := isolated
  refine ⟨c,hc,?_⟩
  intro q _ χ qr hn h hsmall z w hz hiz zz hw hiw zw
  have hfit (v : ℂ) (lo : 1-h≤v.re) (ht : |v.im|≤h) (zero : genuine χ v) :
      1-c/logHeight q 0 ≤ v.re ∧ |v.im-0|≤c/logHeight q 0 ∧ genuine χ v :=
    ⟨by linarith,by simpa using ht.trans hsmall,zero⟩
  have eqv (u : ℂ) (lo : 1-h≤u.re) (ht : |u.im|≤h) (zero : genuine χ u) : z=u := by
    by_contra e
    have b := (unique q χ 0 {z,u} (by
      intro v hv
      simp only [Finset.mem_insert,Finset.mem_singleton] at hv
      rcases hv with rfl|rfl
      · exact hfit _ hz hiz zz
      · exact hfit _ lo ht zero)).2 hn
    simp only [Finset.sum_insert (by simpa using e : z ∉ ({u}:Finset ℂ)),Finset.sum_singleton] at b
    have pz : 0<analyticOrderNatAt (regularizedL χ) z := (order_positive χ zz).1
    have pu : 0<analyticOrderNatAt (regularizedL χ) u := (order_positive χ zero).1
    omega
  have conjz : genuine χ (conj z) := ⟨Or.inl hn,by rw [conjugate_value χ qr hn,zz.2,map_zero]⟩
  have real' := congrArg Complex.im (eqv (conj z) (by simpa using hz) (by simpa using hiz) conjz)
  have b := (unique q χ 0 {z} (by
    intro v hv; obtain rfl := Finset.mem_singleton.mp hv;exact hfit _ hz hiz zz)).2 hn
  simp only [Finset.sum_singleton] at b
  have pz : 0<analyticOrderNatAt (regularizedL χ) z := (order_positive χ zz).1
  have f : regularizedL χ = LFunction χ := by simp [regularizedL,hn]
  rw [f] at pz b
  simp only [Complex.conj_im] at real'
  exact ⟨eqv w hw hiw zw,by linarith,by omega⟩

private theorem quadratic_lift {r m : ℕ} [NeZero m] (hr : r ∣ m) (χ : DirichletCharacter ℂ r)
    (qr : χ.IsQuadratic) : (changeLevel hr χ).IsQuadratic := by
  rw [MulChar.isQuadratic_iff_sq_eq_one,← map_pow,qr.sq_eq_one,map_one]

/-- Compare the two primitive characters at their least common multiple.
Its logarithm costs at most a factor of two. -/
theorem landau_page :
    ∃ c : ℝ, 0<c ∧ ∀ (Q r s : ℕ) [NeZero r] [NeZero s],
      r≤Q → s≤Q → ∀ (χ : DirichletCharacter ℂ r) (ψ : DirichletCharacter ℂ s),
      χ.IsPrimitive → ψ.IsPrimitive → χ.IsQuadratic → ψ.IsQuadratic → χ ≠ 1 → ψ ≠ 1 →
      ∀ z w : ℂ, let h := c/Real.log (4*(Q:ℝ))
        1-h≤z.re → |z.im|≤h → genuine χ z → 1-h≤w.re → |w.im|≤h → genuine ψ w →
        r=s ∧ HEq χ ψ ∧ z=w ∧ z.im=0 ∧ analyticOrderNatAt (LFunction χ) z=1 := by
  obtain ⟨a,ha,chars⟩ := one_character_at_level
  obtain ⟨b,hb,zeros⟩ := simple_real_at_level
  let c := min a b/2
  have hc : 0<c := div_pos (lt_min ha hb) (by norm_num)
  refine ⟨c,hc,?_⟩
  intro Q r s _ _ hr hs χ ψ pr ps qr qs nχ nψ z w h hz hiz zz hw hiw zw
  let m := Nat.lcm r s
  haveI : NeZero m := ⟨(Nat.lcm_pos (NeZero.pos r) (NeZero.pos s)).ne'⟩
  let L := Real.log (4*(Q:ℝ))
  have Qpos : 0<Q := (NeZero.pos r).trans_le hr
  have Qone : 1≤(Q:ℝ) := by exact_mod_cast Qpos
  have Lpos : 0<L := Real.log_pos (by linarith)
  have height (n : ℕ) [NeZero n] (hn : n≤Q*Q) : logHeight n 0 ≤ 2*L := by
    have np : 0 < (n:ℝ) := by exact_mod_cast NeZero.pos n
    have H : (n:ℝ)≤(Q:ℝ)*(Q:ℝ) := by exact_mod_cast hn
    have H' : 2*(n:ℝ)*(2+|(0:ℝ)|)≤(4*(Q:ℝ))^2 := by simp only [abs_zero,add_zero];nlinarith [sq_nonneg (Q:ℝ)]
    exact (Real.log_le_log (by positivity) H').trans_eq (Real.log_pow _ _)
  have width (n : ℕ) [NeZero n] (hn : n≤Q*Q) (u : ℝ) (hu : min a b ≤ u) : h ≤ u/logHeight n 0 := by
    have A := height n hn
    have Lp : 0<logHeight n 0 := zero_lt_one.trans_le (logHeight_ge_one n 0)
    change c/L ≤ _
    rw [div_le_div_iff₀ Lpos Lp]
    calc
      _ ≤ c*(2*L) := mul_le_mul_of_nonneg_left A hc.le
      _ = min a b*L := by dsimp [c];ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hu Lpos.le
  have hm : m ≤ Q*Q := (Nat.le_of_dvd (Nat.mul_pos (NeZero.pos r) (NeZero.pos s))
    (Nat.lcm_dvd (Nat.dvd_mul_right r s) (Nat.dvd_mul_left s r))).trans (Nat.mul_le_mul hr hs)
  let dr := Nat.dvd_lcm_left r s
  let ds := Nat.dvd_lcm_right r s
  have gn {u : ℕ} [NeZero u] (d : u∣m) (θ : DirichletCharacter ℂ u) (v : ℂ)
      (nt : θ ≠ 1) (zv : genuine θ v) : genuine (changeLevel d θ) v := by
    refine ⟨Or.inl (nt ∘ (changeLevel_eq_one_iff d).mp),?_⟩
    rw [LFunction_changeLevel d θ zv.1,zv.2,zero_mul]
  have eqn := chars m (changeLevel dr χ) (changeLevel ds ψ) (quadratic_lift dr χ qr)
    (quadratic_lift ds ψ qs) (nχ ∘ (changeLevel_eq_one_iff dr).mp) (nψ ∘ (changeLevel_eq_one_iff ds).mp)
    h z w (div_pos hc Lpos) (width m hm a (min_le_left _ _))
    hz hiz (gn dr χ z nχ zz) hw hiw (gn ds ψ w nψ zw)
  have levels : r=s := by
    have e := congrArg DirichletCharacter.conductor eqn
    rwa [conductor_changeLevel,conductor_changeLevel,pr,ps] at e
  subst s
  have equal : χ=ψ := changeLevel_injective dr eqn
  subst ψ
  have hr2 : r≤Q*Q := hr.trans (Nat.le_mul_of_pos_right Q Qpos)
  exact ⟨rfl,HEq.rfl,zeros r χ qr nχ h (width r hr2 b (min_le_right _ _)) z w hz hiz zz hw hiw zw⟩

end Conjectures.Goldbach.ExceptionalQuadraticUniqueness

theorem Conjectures.Goldbach.ExceptionalQuadraticUniqueness :
by
  classical
  let Z := fun {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r) (z : ℂ) =>
    (χ ≠ 1 ∨ z ≠ 1) ∧ DirichletCharacter.LFunction χ z=0
  exact ∃ c : ℝ, 0<c ∧ ∀ (Q r s : ℕ) [NeZero r] [NeZero s],
    r≤Q → s≤Q → ∀ (χ : DirichletCharacter ℂ r) (ψ : DirichletCharacter ℂ s),
    χ.IsPrimitive → ψ.IsPrimitive → χ.IsQuadratic → ψ.IsQuadratic → χ ≠ 1 → ψ ≠ 1 →
    ∀ z w : ℂ, let h := c/Real.log (4*(Q:ℝ))
      1-h≤z.re → |z.im|≤h → Z χ z → 1-h≤w.re → |w.im|≤h → Z ψ w →
      r=s ∧ HEq χ ψ ∧ z=w ∧ z.im=0 ∧ analyticOrderNatAt (DirichletCharacter.LFunction χ) z=1 :=
  ExceptionalQuadraticUniqueness.landau_page
