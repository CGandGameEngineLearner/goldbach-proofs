import Conjectures.Goldbach.ExceptionalZeroPrimeFamily

/-! The prime number theorem in reduced residue classes with one common
exceptional conductor. Its normalized error decays throughout the smaller
subexponential range q ≤ exp(k sqrt(log x)/2). -/

namespace Conjectures.Goldbach.ExceptionalZeroProgressions

open Set Real Complex DirichletCharacter
open _root_.Goldbach GoldbachSmoothing ExceptionalZeroTwistedWindow ExceptionalZeroPrimeFamily
open ExceptionalZeroPrimePrefix
open Conjectures.Goldbach.EstermannAlmostAllPolylog_aux.OAI.LargePrimeGaps
  (primeCharacterPrefix primeCharacterError residuePrefix character_error_orthogonality)
open scoped Classical

noncomputable def amplitude (q : ℕ) [NeZero q] (a : ℕ) (s b : ℝ) : ℂ :=
  ∑ χ ∈ carriers q s b, χ (a:ZMod q)⁻¹

private theorem character_card (q : ℕ) [NeZero q] :
    Fintype.card (DirichletCharacter ℂ q)=q.totient := by
  simpa only [Nat.card_eq_fintype_card] using DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q

private theorem sign {q a d : ℕ} [NeZero q] {s b : ℝ} (cop : a.Coprime q)
    (count : (carriers q s b).card=(if d∣q then 1 else 0))
    (quad : ∀ χ ∈ carriers q s b, χ.IsQuadratic) :
    (if d∣q then amplitude q a s b=1 ∨ amplitude q a s b= -1 else amplitude q a s b=0) := by
  by_cases dv : d∣q
  · rw [ite_eq_left dv] at count ⊢
    obtain ⟨χ,only⟩ := Finset.card_eq_one.mp count
    have mem : χ∈carriers q s b := by simp [only]
    have unit : IsUnit (a:ZMod q)⁻¹ := by
      obtain ⟨z,hz⟩ := (ZMod.isUnit_iff_coprime a q).mpr cop
      rw [←hz,ZMod.inv_coe_unit]
      exact (z⁻¹).isUnit
    have nonzero := (unit.map χ.toMonoidHom).ne_zero
    rw [amplitude,only,Finset.sum_singleton]
    exact (quad χ mem _).resolve_left nonzero
  · rw [ite_eq_right dv] at count ⊢
    simp [amplitude,Finset.card_eq_zero.mp count]

private theorem average {q : ℕ} [NeZero q] {a : ℕ} (ha : a<q) (cop : a.Coprime q)
    (x s b M : ℝ)
    (all : ∀ χ : DirichletCharacter ℂ q,
      ‖primeCharacterPrefix x χ - sharp χ x s b‖ ≤ M) :
    ‖(residuePrefix ArithmeticFunction.vonMangoldt ⌊x⌋₊ q a:ℂ) -
      ((x:ℂ) - amplitude q a s b*((x^b/b:ℝ):ℂ))/(q.totient:ℂ)‖ ≤ M := by
  classical
  let P : ℂ := (residuePrefix ArithmeticFunction.vonMangoldt ⌊x⌋₊ q a:ℝ)
  let t : ℂ := q.totient
  let g : ℂ := (x^b/b:ℝ)
  let w := fun (χ : DirichletCharacter ℂ q) => χ (a:ZMod q)⁻¹
  let E := fun χ : DirichletCharacter ℂ q => primeCharacterPrefix x χ - sharp χ x s b
  have tn : t≠0 := by dsimp [t];exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  have normsum : ‖∑ χ, w χ*E χ‖ ≤ (q.totient:ℝ)*M := by
    apply (norm_sum_le ..).trans
    calc
      _ ≤ ∑ _χ : DirichletCharacter ℂ q, M := by
        apply Finset.sum_le_sum
        intro χ _
        rw [norm_mul]
        exact (mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one _)).trans (all χ)
      _ = _ := by simp [character_card]
  have base := character_error_orthogonality x (NeZero.pos q) ha cop
  change (∑ χ, w χ*primeCharacterError x χ)=_ at base
  have identity (χ : DirichletCharacter ℂ q) :
      E χ = primeCharacterError x χ + (if active χ s b then g else 0) := by
    unfold E sharp primeCharacterError principalFlag
    by_cases h : χ=1
    · simp only [ite_eq_left h,one_mul]
      abel
    · simp only [ite_eq_right h,zero_mul,sub_zero]
      abel
  have correction : (∑ χ, w χ*(if active χ s b then g else 0))=amplitude q a s b*g := by
    rw [amplitude,Finset.sum_mul,carriers,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro χ _
    by_cases hit : active χ s b <;> simp [hit,w]
  have iden : (∑ χ, w χ*E χ)=t*(P-((x:ℂ)-amplitude q a s b*g)/t) := by
    simp_rw [identity,mul_add]
    rw [Finset.sum_add_distrib,base,correction]
    change t*((residuePrefix ArithmeticFunction.vonMangoldt ⌊x⌋₊ q a-x/q.totient:ℝ):ℂ)+_ = _
    push_cast
    dsimp only [P,t,g] at *
    field_simp
    ring
  rw [iden,norm_mul] at normsum
  have tp : (0:ℝ)<q.totient := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  change ‖(q.totient:ℂ)‖*_≤_ at normsum
  rw [Complex.norm_natCast] at normsum
  exact (le_of_mul_le_mul_left normsum tp)

theorem progressions :
    ∃ k C : ℝ, 0<k ∧ 0<C ∧ ∀ x : ℝ, Real.exp 64≤x →
    let u := Real.sqrt (Real.log x)
    let s := 1-k/u
    ∀ (Q : ℕ) [NeZero Q], (Q:ℝ)≤Real.exp u → ∃ (b : ℝ) (d : ℕ), d≤Q ∧
    ∀ (q : ℕ) [NeZero q], q≤Q →
      (carriers q s b).card=(if d∣q then 1 else 0) ∧
      (∀ χ ∈ carriers q s b, χ.IsQuadratic ∧ χ ≠ 1 ∧ χ.conductor=d ∧ analyticOrderNatAt (LFunction χ) (b:ℂ)=1) ∧
      ∀ (a : ℕ), a<q → a.Coprime q →
      let ε := (amplitude q a s b).re
      let R := |residuePrefix ArithmeticFunction.vonMangoldt ⌊x⌋₊ q a-(x-ε*(x^b/b))/q.totient|
      (if d∣q then ε=1 ∨ ε= -1 else ε=0) ∧ R≤C*x*Real.exp (-(k*u)) ∧
      ((q:ℝ)≤Real.exp (k*u/2) → R≤C*(x/q.totient)*Real.exp (-(k*u/2))) := by
  obtain ⟨k,C,kp,Cp,raw⟩ := uniform_family
  refine ⟨k,C,kp,Cp,?_⟩
  intro x hx u s Q _ hQ
  obtain ⟨b,d,dQ,family⟩ := raw x hx Q hQ
  refine ⟨b,d,dQ,?_⟩
  intro q _ qQ
  obtain ⟨count,types,error⟩ := family q qQ
  refine ⟨count,types,?_⟩
  intro a ha cop ε R
  have signs := sign cop (s:=s) (b:=b) count (fun χ hχ => (types χ hχ).1)
  have realpart : (if d∣q then ε=1 ∨ ε= -1 else ε=0) ∧ ((ε:ℂ)=amplitude q a s b) := by
    dsimp only [ε]
    by_cases dv : d∣q
    · rw [ite_eq_left dv] at signs ⊢
      rcases signs with plus | minus
      · simp [plus]
      · simp [minus]
    · rw [ite_eq_right dv] at signs ⊢
      simp [signs]
  have xp := (Real.exp_pos _).trans_le hx
  let M := C*x*Real.exp (-(k*u))
  have bound := average ha cop x s b M (fun χ => error χ)
  rw [←realpart.2] at bound
  have exactR : R≤M := by
    change |residuePrefix ArithmeticFunction.vonMangoldt ⌊x⌋₊ q a-(x-ε*(x^b/b))/q.totient|≤M
    rw [←Real.norm_eq_abs,←Complex.norm_real]
    push_cast
    simpa only [Complex.ofReal_div] using bound
  refine ⟨realpart.1,exactR,?_⟩
  intro qrange
  apply exactR.trans
  have tp : (0:ℝ)<q.totient := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  have tot : (q.totient:ℝ)≤Real.exp (k*u/2) :=
    (show (q.totient:ℝ)≤q by exact_mod_cast Nat.totient_le q).trans qrange
  have exp : (q.totient:ℝ)*Real.exp (-(k*u))≤Real.exp (-(k*u/2)) := by
    apply (mul_le_mul_of_nonneg_right tot (Real.exp_pos _).le).trans_eq
    rw [←Real.exp_add];congr 1;ring
  calc
    M = (C*(x/q.totient))*((q.totient:ℝ)*Real.exp (-(k*u))) := by dsimp [M];field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left exp (by positivity)

end Conjectures.Goldbach.ExceptionalZeroProgressions

set_option maxHeartbeats 1800000 in
theorem Conjectures.Goldbach.ExceptionalZeroProgressions :
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
      ∀ a : ℕ, a<q → a.Coprime q →
        let ε := (∑ χ ∈ S, χ (a:ZMod q)⁻¹).re
        let ψ := ∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun n => n%q=a), ArithmeticFunction.vonMangoldt n
        let R := |ψ-(x-ε*(x^b/b))/q.totient|
        (if d∣q then ε=1 ∨ ε= -1 else ε=0) ∧ R≤C*x*Real.exp (-(k*u)) ∧
        ((q:ℝ)≤Real.exp (k*u/2) → R≤C*(x/q.totient)*Real.exp (-(k*u/2))) :=
by
  with_unfolding_all exact ExceptionalZeroProgressions.progressions
