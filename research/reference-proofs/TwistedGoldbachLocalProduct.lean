import Conjectures.Goldbach.TwistedGoldbachConductorRatio
import Conjectures.Goldbach.SquarefreeTwistedGoldbachDensity
import Conjectures.Goldbach.PrimePowerTwistedGoldbachDensity

/-! Factor the full complex singular series of two primitive source characters
through the local components of their actual common-level characters. -/

namespace Conjectures.Goldbach.TwistedGoldbachLocalProduct

open Finset DirichletCharacter TwistedGoldbachConductorRatio
open scoped BigOperators Classical

noncomputable def series {r s : ℕ} (α : DirichletCharacter ℂ r)
    (β : DirichletCharacter ℂ s) (m : ℕ) : ℂ :=
  ∑' d : ℕ, TwistedGoldbachSingularSeries.coefficient α β m d

section Coordinates
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ι → ℕ} [∀ i, NeZero (q i)]
  {L : ℕ} [NeZero L] (e : ZMod L ≃+* ∀ i, ZMod (q i))

/-- Restrict a common-level character to the units at one CRT coordinate.
The same formula extends it by zero on nonunits. -/
noncomputable def component (χ : DirichletCharacter ℂ L) (i : ι) : DirichletCharacter ℂ (q i) where
  toFun x := χ (e.symm (Pi.mulSingle i x))
  map_one' := by simp
  map_mul' x y := by simp only [Pi.mulSingle_mul,map_mul]
  map_nonunit' x hx := χ.map_nonunit (by
    intro hu
    have h := (hu.map e).map (Pi.evalRingHom (fun j => ZMod (q j)) i)
    exact hx (by simpa using h))

omit [Fintype ι] [∀ i, NeZero (q i)] [NeZero L] in
theorem component_one (i : ι) : component e (1 : DirichletCharacter ℂ L) i = 1 := by
  apply MulChar.ext
  intro u
  have hu := (u.isUnit.map (MonoidHom.mulSingle (fun j => ZMod (q j)) i)).map e.symm
  simp only [MonoidHom.mulSingle_apply] at hu
  change (1 : DirichletCharacter ℂ L) (e.symm (Pi.mulSingle i (u:ZMod (q i)))) = _
  rw [MulChar.one_apply hu,MulChar.one_apply u.isUnit]

omit [∀ i, NeZero (q i)] [NeZero L] in
theorem reassemble (χ : DirichletCharacter ℂ L) (x : ZMod L) :
    χ x = ∏ i, component e χ i (e x i) := by
  change χ x = ∏ i, χ (e.symm (Pi.mulSingle i (e x i)))
  rw [← map_prod,← map_prod,Finset.univ_prod_mulSingle,e.symm_apply_apply]

/-- Factor the convolution itself, including every phase. -/
theorem local_factors (A B : DirichletCharacter ℂ L) (m : ℕ) :
    J A B (m:ZMod L) = ∏ i, J (component e A i) (component e B i) (m:ZMod (q i)) := by
  let f (i : ι) (x : ZMod (q i)) := component e A i x * component e B i ((m:ZMod (q i))-x)
  have step (x : ZMod L) : A x * B ((m:ZMod L)-x) = ∏ i, f i (e x i) := by
    rw [reassemble e A x,reassemble e B ((m:ZMod L)-x),← prod_mul_distrib,map_sub,map_natCast]
    rfl
  calc
    _ = ∑ x : ZMod L, ∏ i, f i (e x i) := sum_congr rfl (fun x _ => step x)
    _ = ∑ x : ∀ i, ZMod (q i), ∏ i, f i (x i) :=
      Equiv.sum_comp e.toEquiv (fun x => ∏ i, f i (x i))
    _ = _ := (Fintype.prod_sum f).symm

theorem principal_ne_zero (d m : ℕ) [NeZero d] (he : Even m) :
    J (1 : DirichletCharacter ℂ d) 1 (m:ZMod d) ≠ 0 := by
  obtain ⟨x,hx⟩ := admissible_even d m he
  rw [principal_card]
  exact Nat.cast_ne_zero.mpr (card_pos.mpr ⟨x,mem_filter.mpr ⟨mem_univ _,hx⟩⟩).ne'

/-- Exact Euler product for the correction to the ordinary singular series,
over any CRT decomposition, including prime powers with unequal conductors. -/
theorem full_product {r s : ℕ} [NeZero r] [NeZero s] {α : DirichletCharacter ℂ r}
    {β : DirichletCharacter ℂ s} (hα : α.IsPrimitive) (hβ : β.IsPrimitive)
    (hr : r ∣ L) (hs : s ∣ L) (m : ℕ) (hm : 0 < m) (he : Even m) :
    series α β m = series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m *
      ∏ i, (J (component e (changeLevel hr α) i) (component e (changeLevel hs β) i) (m:ZMod (q i)) /
        J (1 : DirichletCharacter ℂ (q i)) 1 (m:ZMod (q i))) := by
  have h := conductor_identity hα hβ hr hs m hm
  rw [local_factors e (1 : DirichletCharacter ℂ L) 1,local_factors e (changeLevel hr α) (changeLevel hs β)] at h
  simp only [component_one] at h
  rw [prod_div_distrib,← mul_div_assoc,eq_div_iff (prod_ne_zero_iff.mpr (fun i _ => principal_ne_zero (q i) m he))]
  exact h

/-- A noninverse pair at any single CRT factor dividing the target kills the
entire series, even if all the other conductor factors are coprime to it. -/
theorem vanished_factor {r s : ℕ} [NeZero r] [NeZero s] {α : DirichletCharacter ℂ r}
    {β : DirichletCharacter ℂ s} (hα : α.IsPrimitive) (hβ : β.IsPrimitive)
    (hr : r ∣ L) (hs : s ∣ L) (m : ℕ) (hm : 0 < m) (he : Even m) (i : ι)
    (hdiv : q i ∣ m)
    (hne : component e (changeLevel hr α) i * component e (changeLevel hs β) i ≠ 1) :
    series α β m = 0 := by
  rw [full_product e hα hβ hr hs m hm he]
  apply mul_eq_zero_of_right
  apply prod_eq_zero (mem_univ i)
  rw [(ZMod.natCast_eq_zero_iff m (q i)).mpr hdiv,zero_jacobi,ite_eq_right hne,zero_div]

private theorem ratio_le_one {d : ℕ} [NeZero d] (A B : DirichletCharacter ℂ d)
    (m : ℕ) (he : Even m) :
    ‖J A B (m:ZMod d) / J (1 : DirichletCharacter ℂ d) 1 (m:ZMod d)‖ ≤ 1 := by
  rw [norm_div,div_le_one (norm_pos_iff.mpr (principal_ne_zero d m he))]
  exact TwistedGoldbachSingularSeries.chars_le_units A B _

private theorem simple_saving {p : ℕ} [hp : Fact p.Prime] (A B : DirichletCharacter ℂ p)
    (m : ℕ) (hmp : ¬ p ∣ m) (hab : A ≠ 1 ∨ B ≠ 1) :
    ‖J A B (m:ZMod p) / J (1 : DirichletCharacter ℂ p) 1 (m:ZMod p)‖ ≤
      Real.sqrt p / ((p:ℝ)-2) := by
  have hm0 : (m:ZMod p) ≠ 0 := fun h => hmp ((ZMod.natCast_eq_zero_iff m p).mp h)
  have hn : ¬(A=1 ∧ B=1) := by tauto
  have ht := SquarefreeTwistedGoldbachDensity.local_norm A B (m:ZMod p)
  have ht0 := SquarefreeTwistedGoldbachDensity.local_norm (1 : DirichletCharacter ℂ p) 1 (m:ZMod p)
  simp only [hm0,ite_false,hn] at ht
  simp only [hm0,ite_false,and_self,ite_true] at ht0
  change ‖SquarefreeTwistedGoldbachDensity.localSum A B (m:ZMod p) /
    SquarefreeTwistedGoldbachDensity.localSum (1 : DirichletCharacter ℂ p) 1 (m:ZMod p)‖ ≤ _
  rw [norm_div,ht,ht0]
  apply div_le_div_of_nonneg_right _ (sub_nonneg.mpr (by exact_mod_cast hp.out.two_le))
  split_ifs
  · exact (Real.one_le_sqrt.mpr (by exact_mod_cast hp.out.one_le))
  · exact le_rfl

/-- Multiplicative saving from any collection of distinct prime CRT
coordinates away from the target with a nontrivial character component. The
complementary factors may be prime powers or arbitrary composite factors. -/
theorem prime_suppression {r s : ℕ} [NeZero r] [NeZero s] {α : DirichletCharacter ℂ r}
    {β : DirichletCharacter ℂ s} (hα : α.IsPrimitive) (hβ : β.IsPrimitive)
    (hr : r ∣ L) (hs : s ∣ L) (m : ℕ) (hm : 0 < m) (he : Even m)
    (T : Finset ι) (good : ∀ i ∈ T, (q i).Prime ∧ 5 ≤ q i ∧ ¬q i ∣ m ∧
      (component e (changeLevel hr α) i ≠ 1 ∨ component e (changeLevel hs β) i ≠ 1)) :
    ‖series α β m‖ ≤ ‖series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m‖ *
      ∏ i ∈ T, Real.sqrt (q i) / ((q i:ℝ)-2) := by
  let w (i : ι) : ℝ := if i ∈ T then Real.sqrt (q i) / ((q i:ℝ)-2) else 1
  have weights : (∏ i, w i) = ∏ i ∈ T, Real.sqrt (q i) / ((q i:ℝ)-2) := by
    simp [w,prod_ite_mem]
  rw [full_product e hα hβ hr hs m hm he,norm_mul,norm_prod,← weights]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply prod_le_prod₀ (fun _ _ => norm_nonneg _)
  intro i _
  by_cases hi : i ∈ T
  · obtain ⟨hp,_,hd,hn⟩ := good i hi
    let _ : Fact (q i).Prime := ⟨hp⟩
    rw [show w i = _ from ite_eq_left hi]
    exact simple_saving _ _ m hd hn
  · rw [show w i = 1 from ite_eq_right hi]
    exact ratio_le_one _ _ m he

end Coordinates

theorem ordinary_prime_power {p : ℕ} [hp : Fact p.Prime] (j m : ℕ) :
    ‖J (1 : DirichletCharacter ℂ (p*p^j)) 1 (m:ZMod (p*p^j))‖ =
      ((p^j:ℕ):ℝ) * (if p ∣ m then (p:ℝ)-1 else (p:ℝ)-2) := by
  have h := PrimePowerTwistedGoldbachDensity.both_lifted (d := p) (f := p^j)
    (fun a (ha : a.Coprime p) => ha.pow_right j) (1 : DirichletCharacter ℂ p) 1 (m:ZMod (p*p^j))
  simp only [map_one,map_natCast] at h
  have here := SquarefreeTwistedGoldbachDensity.local_norm (1 : DirichletCharacter ℂ p) 1 (m:ZMod p)
  simp only [one_mul,and_self,ite_true,ZMod.natCast_eq_zero_iff] at here
  change ‖PrimePowerTwistedGoldbachDensity.density (1 : DirichletCharacter ℂ p) 1 (m:ZMod p)‖ = _ at here
  change ‖PrimePowerTwistedGoldbachDensity.density (1 : DirichletCharacter ℂ (p*p^j)) 1 (m:ZMod (p*p^j))‖ = _
  rw [h,norm_mul,Complex.norm_natCast,here]

/-- Complete norm table for the infinite twisted series at a pair of
primitive prime-power conductors. Clearing the ordinary local count makes
the formula valid even at odd targets and at the prime two. -/
theorem prime_power_shell {p : ℕ} [hp : Fact p.Prime] (j : ℕ)
    (A B : DirichletCharacter ℂ (p*p^j)) (hA : A.IsPrimitive) (hB : B.IsPrimitive)
    (m : ℕ) (hm : 0 < m) :
    let d := ((A*B)⁻¹).conductor
    let f := (p*p^j)/d
    ‖series A B m‖ * (((p^j:ℕ):ℝ) * (if p ∣ m then (p:ℝ)-1 else (p:ℝ)-2)) =
      ‖series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m‖ *
        (if A*B=1 then
          (if p^j ∣ m then ((p^j:ℕ):ℝ) * (if p ∣ m/p^j then (p:ℝ)-1 else 1) else 0)
         else if f ∣ m ∧ (m/f).Coprime d then (f:ℝ)*Real.sqrt d else 0) := by
  have h := congrArg (fun z : ℂ => ‖z‖)
    (conductor_identity hA hB (dvd_refl _) (dvd_refl _) m hm)
  simp only [norm_mul,changeLevel_self,ordinary_prime_power] at h
  have table := PrimePowerTwistedGoldbachDensity.prime_power_table j A B hA hB m
  change ‖J A B (m:ZMod (p*p^j))‖ = _ at table
  rw [table] at h
  exact h

/-- At a unit target and a repeated prime, only a primitive product can
survive. Its magnitude has an extra square-root saving with each level. -/
theorem unit_prime_power {p : ℕ} [hp : Fact p.Prime] (j : ℕ) (hj : 0 < j)
    (A B : DirichletCharacter ℂ (p*p^j)) (hA : A.IsPrimitive) (hB : B.IsPrimitive)
    (m : ℕ) (hm : 0 < m) (hmp : ¬p ∣ m) :
    ‖series A B m‖ * (((p^j:ℕ):ℝ) * ((p:ℝ)-2)) =
      ‖series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m‖ *
        (if ((A*B)⁻¹).conductor = p*p^j then Real.sqrt (p*p^j:ℕ) else 0) := by
  let Q := p*p^j
  let d := ((A*B)⁻¹).conductor
  have hd : d ∣ Q := ((A*B)⁻¹).conductor_dvd_level
  have hpQ : p ∣ Q := dvd_mul_right p (p^j)
  have hQ : 0 < Q := Nat.mul_pos hp.out.pos (pow_pos hp.out.pos _)
  have mp : m.Coprime p := (hp.out.coprime_iff_not_dvd.mpr hmp).symm
  have mQ := mp.mul_right (mp.pow_right j)
  have nf : Q/d ∣ m → d=Q := by
    intro h
    have one := Nat.eq_one_of_dvd_coprimes mQ h (Nat.div_dvd_of_dvd hd)
    have cancel := Nat.div_mul_cancel hd
    simpa only [one,one_mul] using cancel
  have table := prime_power_shell j A B hA hB m hm
  dsimp only at table
  rw [ite_eq_right hmp] at table
  rw [table]
  congr 1
  change (if A*B=1 then _ else if Q/d ∣ m ∧ (m/(Q/d)).Coprime d then _ else 0) =
    (if d=Q then _ else 0)
  by_cases invpair : A*B=1
  · have d1 : d=1 := (eq_one_iff_conductor_eq_one (χ := (A*B)⁻¹)).mp (by rw [invpair,inv_one])
    have neq : d ≠ Q := by
      intro h
      have h1 : p ∣ 1 := by simpa only [← h,d1] using hpQ
      exact hp.out.not_dvd_one h1
    have nopow : ¬p^j ∣ m := fun h => hmp ((dvd_pow_self p hj.ne').trans h)
    simp only [invpair,ite_true,neq,ite_false,nopow]
  rw [ite_eq_right invpair]
  by_cases same : d=Q
  · have red : Q/d=1 := by rw [same,Nat.div_self hQ]
    have hc : m.Coprime d := by rw [same]; exact mQ
    have hs : Q/d ∣ m ∧ (m/(Q/d)).Coprime d := by simpa only [red,one_dvd,Nat.div_one,true_and] using hc
    rw [ite_eq_left hs,ite_eq_left same,red,Nat.cast_one,one_mul]
    exact congrArg (fun a : ℕ => Real.sqrt a) same
  · have cannot : ¬(Q/d ∣ m ∧ (m/(Q/d)).Coprime d) := fun h => same (nf h.1)
    simp only [cannot,ite_false,same]

end Conjectures.Goldbach.TwistedGoldbachLocalProduct

set_option maxHeartbeats 1200000 in
open Conjectures.Goldbach.TwistedGoldbachLocalProduct in
theorem Conjectures.Goldbach.TwistedGoldbachLocalProduct :
by
  classical
  let S := fun {r s : ℕ} (α : DirichletCharacter ℂ r) (β : DirichletCharacter ℂ s) (m : ℕ) =>
    ∑' d : ℕ, if hd : d ≠ 0 then
      let _ : NeZero d := ⟨hd⟩
      if h : r ∣ d ∧ s ∣ d then
        let A := DirichletCharacter.changeLevel h.1 α
        let B := DirichletCharacter.changeLevel h.2 β
        gaussSum A ZMod.stdAddChar * gaussSum B ZMod.stdAddChar *
          gaussSum (A*B)⁻¹ (ZMod.stdAddChar.mulShift (-(m : ZMod d))) / (d.totient : ℂ)^2
      else 0
    else 0
  let O := S (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1)
  exact
    (∀ (k L r s : ℕ) [NeZero L] [NeZero r] [NeZero s] (q : Fin k → ℕ) [∀ i, NeZero (q i)]
      (e : ZMod L ≃+* (∀ i, ZMod (q i))) (α : DirichletCharacter ℂ r) (β : DirichletCharacter ℂ s),
      α.IsPrimitive → β.IsPrimitive → ∀ (hr : r ∣ L) (hs : s ∣ L) (m : ℕ), 0 < m → Even m →
      let A := fun (i : Fin k) (x : ZMod (q i)) => DirichletCharacter.changeLevel hr α (e.symm (Pi.mulSingle i x))
      let B := fun (i : Fin k) (x : ZMod (q i)) => DirichletCharacter.changeLevel hs β (e.symm (Pi.mulSingle i x))
      (S α β m = O m * ∏ i, ((∑ x : ZMod (q i), A i x * B i ((m:ZMod (q i))-x)) /
        (∑ x : ZMod (q i), (1 : DirichletCharacter ℂ (q i)) x * (1 : DirichletCharacter ℂ (q i)) ((m:ZMod (q i))-x)))) ∧
      (∀ i, q i ∣ m → (∃ u : (ZMod (q i))ˣ, A i u * B i u ≠ 1) → S α β m = 0) ∧
      (∀ T : Finset (Fin k), (∀ i ∈ T, (q i).Prime ∧ 5 ≤ q i ∧ ¬q i ∣ m ∧
        (∃ u : (ZMod (q i))ˣ, A i u ≠ 1 ∨ B i u ≠ 1)) →
        ‖S α β m‖ ≤ ‖O m‖ * ∏ i ∈ T, Real.sqrt (q i) / ((q i:ℝ)-2))) ∧
    (∀ (p : ℕ) [Fact p.Prime] (j : ℕ) (A B : DirichletCharacter ℂ (p*p^j)),
      A.IsPrimitive → B.IsPrimitive → ∀ m : ℕ, 0 < m →
      let d := ((A*B)⁻¹).conductor
      let f := (p*p^j)/d
      ‖S A B m‖ * (((p^j:ℕ):ℝ) * (if p ∣ m then (p:ℝ)-1 else (p:ℝ)-2)) =
        ‖O m‖ * (if A*B=1 then
          (if p^j ∣ m then ((p^j:ℕ):ℝ) * (if p ∣ m/p^j then (p:ℝ)-1 else 1) else 0)
          else if f ∣ m ∧ (m/f).Coprime d then (f:ℝ)*Real.sqrt d else 0)) ∧
    (∀ (p : ℕ) [Fact p.Prime] (j : ℕ), 0 < j →
      ∀ (A B : DirichletCharacter ℂ (p*p^j)), A.IsPrimitive → B.IsPrimitive →
      ∀ m : ℕ, 0 < m → ¬p ∣ m →
      ‖S A B m‖ * (((p^j:ℕ):ℝ)*((p:ℝ)-2)) =
        ‖O m‖ * (if ((A*B)⁻¹).conductor = p*p^j then Real.sqrt (p*p^j:ℕ) else 0)) := by
  classical
  refine ⟨?_,fun _ _ j A B hA hB m hm => prime_power_shell j A B hA hB m hm,
    fun _ _ j hj A B hA hB m hm hd => unit_prime_power j hj A B hA hB m hm hd⟩
  intro k L r s _ _ _ q _ e α β hα hβ hr hs m hm he A B
  refine ⟨full_product e hα hβ hr hs m hm he,?_,?_⟩
  · rintro i hd ⟨u,hu⟩
    apply vanished_factor e hα hβ hr hs m hm he i hd
    intro triv
    have H := DFunLike.congr_fun triv (u : ZMod (q i))
    rw [MulChar.mul_apply,MulChar.one_apply u.isUnit] at H
    exact hu H
  · intro T good
    apply prime_suppression e hα hβ hr hs m hm he T
    intro i hi
    obtain ⟨hp,hp5,hdiv,u,hn⟩ := good i hi
    refine ⟨hp,hp5,hdiv,?_⟩
    rcases hn with h | h
    · left
      intro triv
      have H := DFunLike.congr_fun triv (u : ZMod (q i))
      rw [MulChar.one_apply u.isUnit] at H
      exact h H
    · right
      intro triv
      have H := DFunLike.congr_fun triv (u : ZMod (q i))
      rw [MulChar.one_apply u.isUnit] at H
      exact h H
