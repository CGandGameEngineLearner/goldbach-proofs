import Conjectures.Goldbach.ExceptionalZeroRationalCenters
import Conjectures.Goldbach.TwistedGoldbachConductorValue

/-! Determine the exact support, magnitude and quadratic phase of the
exceptional term in a rational-center prime Fourier sum. Its coefficient
may vanish even at a multiple of the exceptional conductor. -/

namespace Conjectures.Goldbach.ExceptionalZeroArcAmplitude

open Complex DirichletCharacter GoldbachTwistedMellin
open ExceptionalZeroPrimeFamily ExceptionalZeroRationalCenters
open TwistedGoldbachSingularSeries TwistedGoldbachConductorValue
open scoped Classical ComplexConjugate

private theorem weight_gauss {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (quad : χ.IsQuadratic)
    (a : ℕ) : additiveWeight (a:ZMod q) χ=amplitude χ a := by
  rw [weight_expansion,amplitude,gaussSum]
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  have realval : conj (χ r)=χ r := by
    rcases quad r with z | z | z <;> simp [z]
  rw [realval,AddChar.mulShift_apply,mul_comm]

private theorem unit_rotation {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (quad : χ.IsQuadratic)
    (a : ℕ) (cop : a.Coprime q) : amplitude χ a=χ (a:ZMod q)*amplitude χ 1 := by
  unfold amplitude
  let unit := ZMod.unitOfCoprime a cop
  have hs := gaussSum_mulShift_eq χ ZMod.stdAddChar unit
  simp only [Nat.cast_one,AddChar.mulShift_one,quad.inv,unit,ZMod.coe_unitOfCoprime] at hs ⊢
  rw [hs]
  ring

private theorem signed_square {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (quad : χ.IsQuadratic)
    (a : ℕ) : (amplitude χ a)^2=χ (-1)*(‖amplitude χ a‖:ℂ)^2 := by
  let w := amplitude χ a
  have parity : w=χ (-1)*conj w := by
    have hs := gaussSum_inv_eq_conj χ (ZMod.stdAddChar.mulShift (a:ZMod q))
    rw [quad.inv] at hs
    dsimp only [w,amplitude]
    rw [map_div₀,Complex.conj_natCast,←mul_div_assoc,←hs]
  calc
    w^2 = w*w := sq w
    _ = (χ (-1)*conj w)*w := congrArg (·*w) parity
    _ = _ := by rw [mul_assoc,Complex.conj_mul']

theorem conductor_profile {q d : ℕ} [NeZero q] {s b : ℝ}
    (count : (carriers q s b).card=(if d∣q then 1 else 0))
    (family : ∀ χ ∈ carriers q s b, χ.IsQuadratic ∧ χ.conductor=d)
    (a : ℕ) (cop : a.Coprime q) :
    ‖gaussWeight q a s b‖=(if d∣q ∧ Squarefree (q/d) ∧ (q/d).Coprime d then
      Real.sqrt d/(q.totient:ℝ) else 0) ∧
    ∀ χ ∈ carriers q s b,
      gaussWeight q a s b=χ (a:ZMod q)*gaussWeight q 1 s b ∧
      (gaussWeight q a s b)^2=χ (-1)*(‖gaussWeight q a s b‖:ℂ)^2 := by
  classical
  by_cases dv : d∣q
  · rw [ite_eq_left dv] at count
    obtain ⟨χ,single⟩ := Finset.card_eq_one.mp count
    have hχ : χ ∈ carriers q s b := by simp [single]
    obtain ⟨quad,lev⟩ := family χ hχ
    have exactW (j : ℕ) : gaussWeight q j s b=amplitude χ j := by
      simp only [gaussWeight,single,Finset.sum_singleton,weight_gauss χ quad j]
    refine ⟨?_,?_⟩
    · have size := amplitude_norm (q:=q) (j:=q) (dvd_refl q) χ a cop
      simpa only [Nat.div_self (NeZero.pos q),one_mul,lev,admissible,exactW] using size
    · intro ψ hψ
      have eqn : ψ=χ := by simpa only [single,Finset.mem_singleton] using hψ
      subst ψ
      simp only [exactW]
      exact ⟨unit_rotation χ quad a cop,signed_square χ quad a⟩
  · rw [ite_eq_right dv,Finset.card_eq_zero] at count
    simp [gaussWeight,count,dv]

end Conjectures.Goldbach.ExceptionalZeroArcAmplitude

set_option maxHeartbeats 1800000 in
theorem Conjectures.Goldbach.ExceptionalZeroArcAmplitude :
by
  classical
  let hit := fun {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s b : ℝ) =>
    s<b ∧ b<1 ∧ (χ ≠ 1 ∨ (b:ℂ) ≠ 1) ∧ DirichletCharacter.LFunction χ (b:ℂ)=0
  exact ∀ (q d : ℕ) [NeZero q] (s b : ℝ),
    let S := @Finset.filter (DirichletCharacter ℂ q) (fun χ => hit χ s b)
      (fun _ => Classical.propDecidable _) Finset.univ
    let G := fun j : ℕ => ∑ χ ∈ S, (starRingEnd ℂ) (∑ r : ZMod q,
      (starRingEnd ℂ) (ZMod.stdAddChar ((j:ZMod q)*r))*χ r)/(q.totient:ℂ)
    S.card=(if d∣q then 1 else 0) →
    (∀ χ ∈ S, χ.IsQuadratic ∧ χ.conductor=d) →
    ∀ a : ℕ, a.Coprime q →
      ‖G a‖=(if d∣q ∧ Squarefree (q/d) ∧ (q/d).Coprime d then Real.sqrt d/(q.totient:ℝ) else 0) ∧
      ∀ χ ∈ S, G a=χ (a:ZMod q)*G 1 ∧ (G a)^2=χ (-1)*(‖G a‖:ℂ)^2 :=
by
  intro hit q d nz s b S G count family a cop
  with_unfolding_all exact ExceptionalZeroArcAmplitude.conductor_profile (q:=q) (d:=d) (s:=s) (b:=b) count family a cop
