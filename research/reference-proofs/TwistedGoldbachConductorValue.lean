import Conjectures.Goldbach.TwistedGoldbachCoefficientProduct

/-! Exact arithmetic support and size of the common-conductor coefficient in
the generalized Goldbach singular series. The additive frequency need not
be a unit. Its reduced denominator selects the primitive character and the
remaining Möbius factor. See Pintz I, (7.3)–(7.5).
https://arxiv.org/abs/1804.05561 -/

namespace Conjectures.Goldbach.TwistedGoldbachConductorValue

open Finset DirichletCharacter TwistedGoldbachSingularSeries TwistedGoldbachCoefficientProduct
open TwistedGoldbachLocalProduct
open B13BilateralVaughanReductionProof
open DyadicMixedB4MoebiusGauss DyadicMixedB4GaussLift DyadicMixedB4ImprimitiveBound
open scoped BigOperators Classical

/-- The exact phase of an induced Gauss sum at an unramified additive
frequency. A shared prime or a square in the conductor quotient kills it. -/
theorem induced_standard {r q : ℕ} [NeZero r] [NeZero q] (hr : r ∣ q)
    (χ : DirichletCharacter ℂ r) (hχ : χ.IsPrimitive) :
    gaussSum (changeLevel hr χ) ZMod.stdAddChar =
      (ArithmeticFunction.moebius (q/r):ℂ) * χ (↑(q/r):ZMod r) * gaussSum χ ZMod.stdAddChar := by
  have h := sum_inducedGauss_moebius hr χ 1
  simp only [Nat.cast_one,AddChar.mulShift_one] at h
  rw [h,sum_eq_single_of_mem (q/r) (Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd hr,NeZero.ne q⟩)]
  · rw [Nat.div_div_self hr (NeZero.ne q)]
    have a := gaussSum_as_fraction_sum χ 1
    simpa only [Nat.cast_one,AddChar.mulShift_one,one_mul,moebiusComplex] using
      congrArg (fun z : ℂ => (ArithmeticFunction.moebius (q/r):ℂ)*χ (↑(q/r):ZMod r)*z) a.symm
  · intro e he hne
    have bad : ¬(e.Coprime r ∧ (q/e/r) ∣ 1) := by
      intro ⟨hc,hf⟩
      have one := Nat.eq_one_of_dvd_one hf
      obtain ⟨_,_,eqn⟩ := conductor_cofactor hr he hc
      rw [one,mul_one] at eqn
      exact hne (by rw [← eqn,Nat.mul_div_cancel _ (NeZero.pos r)])
    have zero := norm_induced_gauss_term hr he 1 hχ
    rw [ite_eq_right bad] at zero
    exact norm_le_zero_iff.mp zero

def admissible (r q : ℕ) : Prop := Squarefree (q/r) ∧ (q/r).Coprime r

theorem induced_standard_norm {r q : ℕ} [NeZero r] [NeZero q] (hr : r ∣ q)
    (χ : DirichletCharacter ℂ r) (hχ : χ.IsPrimitive) :
    ‖gaussSum (changeLevel hr χ) ZMod.stdAddChar‖ =
      if admissible r q then Real.sqrt r else 0 := by
  rw [induced_standard hr χ hχ,norm_mul,norm_mul,DirichletCharacter.norm_gaussSum_stdAddChar hχ]
  by_cases hs : Squarefree (q/r)
  · have mu : ‖(ArithmeticFunction.moebius (q/r):ℂ)‖ = 1 := by
      rcases ArithmeticFunction.moebius_ne_zero_iff_eq_or.mp (ArithmeticFunction.moebius_ne_zero_iff_squarefree.mpr hs) with H | H <;> rw [H] <;> norm_num
    rw [mu,one_mul]
    by_cases hc : (q/r).Coprime r
    · have hu := (ZMod.isUnit_iff_coprime (q/r) r).mpr hc
      have hn := χ.unit_norm_eq_one hu.unit
      rw [ite_eq_left (show admissible r q from ⟨hs,hc⟩)]
      simpa only [hu.unit_spec,one_mul] using congrArg (fun z : ℝ => z*Real.sqrt r) hn
    · rw [χ.map_nonunit (fun h => hc ((ZMod.isUnit_iff_coprime _ _).mp h)),norm_zero,zero_mul]
      simp [admissible,hc]
  · simp [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hs,admissible,hs]

/-- The Fourier frequency g*k has reduced denominator j, where g=q/j and
k is a unit modulo j. This gives its exact norm at the original level. -/
theorem amplitude_norm {q j : ℕ} [NeZero q] [NeZero j] (hj : j ∣ q)
    (χ : DirichletCharacter ℂ q) (k : ℕ) (hk : k.Coprime j) :
    ‖amplitude χ (q/j*k)‖ = if χ.conductor ∣ j ∧ admissible χ.conductor j then
      Real.sqrt χ.conductor/(j.totient:ℝ) else 0 := by
  let d := χ.conductor
  let _ : NeZero d := ⟨fun h => NeZero.ne q (conductor_eq_zero_iff_level_eq_zero.mp h)⟩
  rw [amplitude_at_divisor hj]
  by_cases hd : d ∣ j
  · let θ := χ.primitiveCharacter
    let θj := changeLevel hd θ
    have eqn : χ = changeLevel hj θj := by
      dsimp only [θj,θ]
      rw [← changeLevel_trans,changeLevel_primitiveCharacter]
    have H : χ.FactorsThrough j := ⟨hj,θj,eqn⟩
    have eqj : H.χ₀=θj := changeLevel_injective hj (H.eq_changeLevel.symm.trans eqn)
    rw [dite_eq_left H,eqj]
    let hu : (ZMod j)ˣ := ZMod.unitOfCoprime k hk
    have HS := gaussSum_mulShift_eq θj ZMod.stdAddChar hu
    have val : (hu:ZMod j)=(k:ZMod j) := ZMod.coe_unitOfCoprime k hk
    unfold amplitude
    rw [← val,HS,norm_div,norm_mul,(θj⁻¹).unit_norm_eq_one hu,one_mul,Complex.norm_natCast,
      induced_standard_norm hd θ χ.primitiveCharacter_isPrimitive]
    change (if admissible d j then Real.sqrt d else 0)/(j.totient:ℝ) = _
    change (if admissible d j then Real.sqrt d else 0)/(j.totient:ℝ) =
      (if d ∣ j ∧ admissible d j then Real.sqrt d/(j.totient:ℝ) else 0)
    by_cases good : admissible d j <;> simp [good,hd]
  · have H : ¬χ.FactorsThrough j := fun h => hd (χ.conductor_dvd_of_mem_conductorSet h)
    rw [dite_eq_right H,norm_zero,ite_eq_right (not_and_of_not_left _ hd)]

theorem shifted_norm {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (m : ℕ) :
    let j := q/(m.gcd q)
    ‖gaussSum χ (ZMod.stdAddChar.mulShift (m:ZMod q))‖ =
      if χ.conductor ∣ j ∧ admissible χ.conductor j then
        (q.totient:ℝ)/j.totient * Real.sqrt χ.conductor else 0 := by
  intro j
  let g := m.gcd q
  have hg : 0 < g := Nat.gcd_pos_of_pos_right m (NeZero.pos q)
  have hd : g ∣ q := Nat.gcd_dvd_right m q
  have hj : j ∣ q := Nat.div_dvd_of_dvd hd
  let _ : NeZero j := ⟨(Nat.div_pos (Nat.le_of_dvd (NeZero.pos q) hd) hg).ne'⟩
  have eqn : q/j*(m/g)=m := by
    dsimp [j,g]
    rw [Nat.div_div_self hd (NeZero.ne q),Nat.mul_div_cancel' (Nat.gcd_dvd_left m q)]
  have A := amplitude_norm hj χ (m/g) (Nat.coprime_div_gcd_div_gcd hg)
  rw [eqn,amplitude,norm_div,Complex.norm_natCast] at A
  have hφ : (q.totient:ℝ) ≠ 0 := by exact_mod_cast NeZero.ne q.totient
  have val := (div_eq_iff hφ).mp A
  rw [val]
  split_ifs <;> ring

noncomputable def inversePair {r s : ℕ} (α : DirichletCharacter ℂ r) (β : DirichletCharacter ℂ s) :
    DirichletCharacter ℂ (Nat.lcm r s) :=
  ((changeLevel (Nat.dvd_lcm_left r s) α)*(changeLevel (Nat.dvd_lcm_right r s) β))⁻¹

def supported (r s L d j : ℕ) : Prop :=
  admissible r L ∧ admissible s L ∧ d ∣ j ∧ admissible d j

/-- The three primitive conductors determine the exact magnitude at the
base denominator, without factoring either of the source moduli. -/
theorem base_norm {r s : ℕ} [NeZero r] [NeZero s] {α : DirichletCharacter ℂ r}
    {β : DirichletCharacter ℂ s} (hα : α.IsPrimitive) (hβ : β.IsPrimitive) (m : ℕ) :
    let L := Nat.lcm r s
    let d := (inversePair α β).conductor
    let j := L/(m.gcd L)
    ‖coefficient α β m L‖ = if supported r s L d j then
      Real.sqrt r * Real.sqrt s * Real.sqrt d / ((L.totient:ℝ)*(j.totient:ℝ)) else 0 := by
  intro L d j
  have hL : L ≠ 0 := (Nat.lcm_pos (NeZero.pos r) (NeZero.pos s)).ne'
  let _ : NeZero L := ⟨hL⟩
  have hr : r ∣ L := Nat.dvd_lcm_left ..
  have hs : s ∣ L := Nat.dvd_lcm_right ..
  let θ := inversePair α β
  have neg_eq : ‖gaussSum θ (ZMod.stdAddChar.mulShift (-(m:ZMod L)))‖ =
      ‖gaussSum θ (ZMod.stdAddChar.mulShift (m:ZMod L))‖ := by
    exact le_antisymm (DyadicMixedB4CharacterFactorBound.norm_gauss_neg_shift_le _ _)
      (by simpa using DyadicMixedB4CharacterFactorBound.norm_gauss_neg_shift_le θ (-(m:ZMod L)))
  rw [coefficient,dite_eq_left hL,dite_eq_left (And.intro hr hs)]
  unfold gaussCoefficient
  rw [norm_div,norm_pow,Complex.norm_natCast,norm_mul,norm_mul,
    induced_standard_norm hr α hα,induced_standard_norm hs β hβ]
  change (if admissible r L then _ else 0)*(if admissible s L then _ else 0)*
    ‖gaussSum θ (ZMod.stdAddChar.mulShift (-(m:ZMod L)))‖/(L.totient:ℝ)^2 = _
  rw [neg_eq,shifted_norm]
  change _ * _ * (if d ∣ j ∧ admissible d j then (L.totient:ℝ)/j.totient*Real.sqrt d else 0)/(L.totient:ℝ)^2 = _
  have hφ : (L.totient:ℝ) ≠ 0 := by exact_mod_cast NeZero.ne L.totient
  unfold supported
  by_cases h1 : admissible r L <;> by_cases h2 : admissible s L <;> by_cases h3 : d ∣ j ∧ admissible d j <;>
    simp only [h1,h2,h3,and_true,and_false,ite_true,ite_false,mul_zero,zero_mul,zero_div]
  field_simp [hφ]

theorem full_base {r s : ℕ} [NeZero r] [NeZero s] {α : DirichletCharacter ℂ r}
    {β : DirichletCharacter ℂ s} (hα : α.IsPrimitive) (hβ : β.IsPrimitive) (m : ℕ) (hm : 0 < m) :
    let L := Nat.lcm r s
    let _ : NeZero L := ⟨(Nat.lcm_pos (NeZero.pos r) (NeZero.pos s)).ne'⟩
    ‖series α β m‖ * TwistedGoldbachMixedPrincipal.ordinaryWeight L m =
      ‖series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m‖ * ‖coefficient α β m L‖ := by
  intro L inst
  let _ : NeZero L := inst
  have hr : r ∣ L := Nat.dvd_lcm_left ..
  have hs : s ∣ L := Nat.dvd_lcm_right ..
  have E := ambient_sum hα hβ hr hs m
  rw [sum_eq_single_of_mem L (Nat.mem_divisors_self L (NeZero.ne L))] at E
  · have N := congrArg (fun z : ℂ => ‖z‖) E
    simp only [normalized,norm_div,norm_mul,norm_pow,Complex.norm_natCast] at N
    have J := congrArg (fun z : ℂ => ‖z‖) (TwistedGoldbachConductorRatio.conductor_identity hα hβ hr hs m hm)
    simp only [norm_mul] at J
    rw [← N]
    unfold TwistedGoldbachMixedPrincipal.ordinaryWeight
    change ‖series α β m‖*((L:ℝ)*_/(L.totient:ℝ)^2)=_ * ((L:ℝ)*_/(L.totient:ℝ)^2)
    simp only [series,TwistedGoldbachConductorRatio.J] at J ⊢
    linear_combination ((L:ℝ)/(L.totient:ℝ)^2)*J
  · intro d hd ne
    exact off_level α β m d (fun h => ne (Nat.dvd_antisymm (Nat.dvd_of_mem_divisors hd) h))

/-- Nonvanishing of the infinite series is equivalent to four finite
arithmetic conditions on the conductors and the reduced denominator. -/
theorem full_support {r s : ℕ} [NeZero r] [NeZero s] {α : DirichletCharacter ℂ r}
    {β : DirichletCharacter ℂ s} (hα : α.IsPrimitive) (hβ : β.IsPrimitive)
    (m : ℕ) (hm : 0 < m) (he : Even m) :
    let L := Nat.lcm r s
    let d := (inversePair α β).conductor
    series α β m ≠ 0 ↔ supported r s L d (L/(m.gcd L)) := by
  intro L d
  let j := L/(m.gcd L)
  let _ : NeZero L := ⟨(Nat.lcm_pos (NeZero.pos r) (NeZero.pos s)).ne'⟩
  let _ : NeZero j := ⟨(Nat.div_pos (Nat.le_of_dvd (NeZero.pos L) (Nat.gcd_dvd_right m L))
    (Nat.gcd_pos_of_pos_right m (NeZero.pos L))).ne'⟩
  have hd : 0 < d := Nat.pos_of_ne_zero (fun h => NeZero.ne L (conductor_eq_zero_iff_level_eq_zero.mp h))
  let O := series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m
  have hO : 0 < ‖O‖ := lt_of_lt_of_le (by norm_num : (0:ℝ)<1)
    ((TwistedGoldbachMixedPrincipal.ordinary_at_least_one m hm he).trans (Complex.re_le_norm O))
  have W := TwistedGoldbachMixedPrincipal.uniform_weight L m he
  have hw : 0 < TwistedGoldbachMixedPrincipal.ordinaryWeight L m := lt_of_lt_of_le (by split <;> norm_num) W
  have H := full_base hα hβ m hm
  dsimp only at H
  rw [base_norm hα hβ m] at H
  change ‖series α β m‖ * TwistedGoldbachMixedPrincipal.ordinaryWeight L m = ‖O‖ *
    (if supported r s L d j then Real.sqrt r * Real.sqrt s * Real.sqrt d/((L.totient:ℝ)*(j.totient:ℝ)) else 0) at H
  by_cases good : supported r s L d j
  · rw [ite_eq_left good] at H
    refine ⟨fun _ => good, fun _ hzero => ?_⟩
    rw [hzero,norm_zero,zero_mul] at H
    have hrp : (0:ℝ)<r := by exact_mod_cast NeZero.pos r
    have hsp : (0:ℝ)<s := by exact_mod_cast NeZero.pos s
    have hdp : (0:ℝ)<d := by exact_mod_cast hd
    have hLφ : 0 < (L.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos L)
    have hjφ : 0 < (j.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos j)
    exact (ne_of_lt (mul_pos hO (div_pos (mul_pos (mul_pos (Real.sqrt_pos.mpr hrp)
      (Real.sqrt_pos.mpr hsp)) (Real.sqrt_pos.mpr hdp)) (mul_pos hLφ hjφ)))) H
  · rw [ite_eq_right good,mul_zero] at H
    have zero := norm_eq_zero.mp ((mul_eq_zero.mp H).resolve_right hw.ne')
    exact ⟨fun hn => False.elim (hn zero),fun h => False.elim (good h)⟩

end Conjectures.Goldbach.TwistedGoldbachConductorValue

set_option maxHeartbeats 1200000 in
open Conjectures.Goldbach.TwistedGoldbachConductorValue in
theorem Conjectures.Goldbach.TwistedGoldbachConductorValue :
by
  classical
  let good := fun (r q : ℕ) => Squarefree (q/r) ∧ (q/r).Coprime r
  let c := fun {r s : ℕ} (α : DirichletCharacter ℂ r) (β : DirichletCharacter ℂ s) (m d : ℕ) =>
    if hd : d ≠ 0 then
      let _ : NeZero d := ⟨hd⟩
      if h : r ∣ d ∧ s ∣ d then
        let A := DirichletCharacter.changeLevel h.1 α
        let B := DirichletCharacter.changeLevel h.2 β
        gaussSum A ZMod.stdAddChar * gaussSum B ZMod.stdAddChar *
          gaussSum (A*B)⁻¹ (ZMod.stdAddChar.mulShift (-(m : ZMod d))) / (d.totient : ℂ)^2
      else 0
    else 0
  exact
    (∀ (r q : ℕ) [NeZero r] [NeZero q] (h : r ∣ q) (χ : DirichletCharacter ℂ r), χ.IsPrimitive →
      gaussSum (DirichletCharacter.changeLevel h χ) ZMod.stdAddChar =
        (ArithmeticFunction.moebius (q/r):ℂ)*χ (↑(q/r):ZMod r)*gaussSum χ ZMod.stdAddChar) ∧
    (∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (m : ℕ), let j := q/(m.gcd q)
      ‖gaussSum χ (ZMod.stdAddChar.mulShift (m:ZMod q))‖ =
        if χ.conductor ∣ j ∧ good χ.conductor j then
          (q.totient:ℝ)/j.totient * Real.sqrt χ.conductor else 0) ∧
    (∀ (r s : ℕ) [NeZero r] [NeZero s] (α : DirichletCharacter ℂ r) (β : DirichletCharacter ℂ s),
      α.IsPrimitive → β.IsPrimitive → ∀ m : ℕ,
      let L := Nat.lcm r s
      let θ := ((DirichletCharacter.changeLevel (Nat.dvd_lcm_left r s) α)*
                (DirichletCharacter.changeLevel (Nat.dvd_lcm_right r s) β))⁻¹
      let d := θ.conductor
      let j := L/(m.gcd L)
      let P := good r L ∧ good s L ∧ d ∣ j ∧ good d j
      let S := ∑' k : ℕ, c α β m k
      (‖c α β m L‖ = if P then Real.sqrt r*Real.sqrt s*Real.sqrt d/((L.totient:ℝ)*(j.totient:ℝ)) else 0) ∧
      (0 < m →
        let _ : NeZero L := ⟨(Nat.lcm_pos (NeZero.pos r) (NeZero.pos s)).ne'⟩
        let W := (L:ℝ)*‖∑ x : ZMod L, (1 : DirichletCharacter ℂ L) x * (1 : DirichletCharacter ℂ L) ((m:ZMod L)-x)‖/(L.totient:ℝ)^2
        ‖S‖ * W = ‖∑' k : ℕ, c (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m k‖ * ‖c α β m L‖) ∧
      (0 < m → Even m → (S ≠ 0 ↔ P))) := by
  classical
  refine ⟨fun _ _ _ _ h χ hχ => induced_standard h χ hχ,?_,?_⟩
  · intro q _ χ m
    let j := q/(m.gcd q)
    by_cases h : χ.conductor ∣ j ∧ Squarefree (j/χ.conductor) ∧ (j/χ.conductor).Coprime χ.conductor <;>
      simpa only [admissible,← show j=q/(m.gcd q) from rfl,h,ite_true,ite_false] using shifted_norm χ m
  · intro r s _ _ α β hα hβ m L θ d j P S
    refine ⟨?_,full_base hα hβ m,full_support hα hβ m⟩
    have value := base_norm hα hβ m
    change ‖TwistedGoldbachSingularSeries.coefficient α β m L‖ =
      (if supported r s L d j then _ else 0) at value
    by_cases h : P
    · rw [ite_eq_left h]
      rwa [ite_eq_left (show supported r s L d j from h)] at value
    · rw [ite_eq_right h]
      rwa [ite_eq_right (show ¬supported r s L d j from h)] at value
