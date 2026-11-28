import Mathlib
import Conjectures.Goldbach.SharpSingularSeriesRatios

open Finset DirichletCharacter
open Conjectures.Goldbach.SharpSingularSeriesRatiosProof
open TwistedGoldbachConductorRatio TwistedGoldbachLocalProduct
open TwistedGoldbachMixedPrincipal SquarefreeTwistedGoldbachDensity

private theorem prime_count (p m : ℕ) [Fact p.Prime] (hp : ¬ p ∣ m) :
    J (1 : DirichletCharacter ℂ p) 1 (m : ZMod p) = (p : ℂ) - 2 := by
  have hn : (m : ZMod p) ≠ 0 := fun h => hp ((ZMod.natCast_eq_zero_iff m p).mp h)
  have h : ‖J (1 : DirichletCharacter ℂ p) 1 (m : ZMod p)‖ = (p : ℝ) - 2 := by
    change ‖localSum (1 : DirichletCharacter ℂ p) 1 _‖ = _
    simpa [hn] using local_norm (1 : DirichletCharacter ℂ p) 1 (m : ZMod p)
  rw [principal_card, Complex.norm_natCast] at h
  rw [principal_card]
  exact_mod_cast congrArg Complex.ofReal h

private theorem squarefree_count {s m : ℕ} [NeZero s] (hs : Squarefree s) (hc : s.Coprime m) :
    J (1 : DirichletCharacter ℂ s) 1 (m : ZMod s) = ∏ p ∈ s.primeFactors, ((p : ℂ) - 2) := by
  classical
  let q (p : s.primeFactors) : ℕ := p.val
  have prime (p : s.primeFactors) : (q p).Prime := Nat.prime_of_mem_primeFactors p.property
  let (p : s.primeFactors) : Fact (q p).Prime := ⟨prime p⟩
  have hprod : (∏ p, q p) = s := by
    change (∏ p : s.primeFactors, (p : ℕ)) = s
    rw [Finset.prod_coe_sort s.primeFactors (fun p : ℕ => p)]
    exact Nat.prod_primeFactors_of_squarefree hs
  have pair : Pairwise (fun a b : s.primeFactors => (q a).Coprime (q b)) := by
    intro a b hab
    exact (Nat.coprime_primes (prime a) (prime b)).mpr (fun h => hab (Subtype.ext h))
  let e := (ZMod.ringEquivCongr hprod.symm).trans (ZMod.prodEquivPi q pair)
  rw [local_factors e]
  simp only [component_one]
  rw [← Finset.prod_coe_sort s.primeFactors]
  apply prod_congr rfl
  intro p _
  exact prime_count (q p) m (fun hd => (prime p).not_dvd_one (hc ▸ Nat.dvd_gcd (Nat.dvd_of_mem_primeFactors p.property) hd))

theorem Conjectures.Goldbach.PartnerPrincipalRowPhase : (by
  classical
  let S := fun {r s : ℕ} (α : DirichletCharacter ℂ r) (β : DirichletCharacter ℂ s) (m : ℕ) =>
    ∑' q : ℕ, if hq : q ≠ 0 then
      let _ : NeZero q := ⟨hq⟩
      if h : r ∣ q ∧ s ∣ q then
        let A := DirichletCharacter.changeLevel h.1 α
        let B := DirichletCharacter.changeLevel h.2 β
        gaussSum A ZMod.stdAddChar * gaussSum B ZMod.stdAddChar *
          gaussSum (A*B)⁻¹ (ZMod.stdAddChar.mulShift (-(m:ZMod q))) / (q.totient:ℂ)^2
      else 0
    else 0
  let O := S (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1)
  let P := (1 : DirichletCharacter ℂ 1)
  let B := Σ s : ℕ, DirichletCharacter ℂ s
  let valid := fun b : B => b.1 ≠ 0 ∧ b.2.IsPrimitive
  exact ∀ (s : ℕ) [NeZero s] (β : DirichletCharacter ℂ s), β.IsPrimitive → ∀ m : ℕ, 0 < m → Even m → S P β m = if Squarefree s ∧ s.Coprime m then O m * ((-1:ℂ)^s.primeFactors.card) * β (m:ZMod s) / (∏ p ∈ s.primeFactors, ((p:ℂ)-2)) else 0) := by
  classical
  dsimp only
  intro s _ β hβ m hm he
  change series (1 : DirichletCharacter ℂ 1) β m = _
  have ratio := exact_ratio isPrimitive_one_level_one hβ (one_dvd s) (dvd_refl s) m hm he
  rw [map_one, changeLevel_self, ← principal_card] at ratio
  have swap : J (1 : DirichletCharacter ℂ s) β (m : ZMod s) = J β 1 (m : ZMod s) := by
    unfold J
    rw [← Equiv.sum_comp (Equiv.subLeft (m : ZMod s))
      (fun x : ZMod s => (1 : DirichletCharacter ℂ s) x * β (m-x))]
    simp [mul_comm]
  rw [swap, mixed_jacobi β hβ] at ratio
  rw [show series (1 : DirichletCharacter ℂ 1) β m = _ from ratio]
  by_cases good : Squarefree s ∧ s.Coprime m
  · rw [ite_eq_left good, squarefree_count good.1 good.2,
      ArithmeticFunction.moebius_apply_of_squarefree good.1,
      ← (ArithmeticFunction.cardDistinctFactors_eq_cardFactors_iff_squarefree (NeZero.ne s)).mpr good.1,
      ArithmeticFunction.cardDistinctFactors_eq_card_primeFactors]
    push_cast
    change _ = series _ _ _ * _ * _ / _
    unfold series
    ring
  · rw [ite_eq_right good]
    by_cases hs : Squarefree s
    · have hunit : ¬ IsUnit (m : ZMod s) :=
        fun hu => good ⟨hs, ((ZMod.isUnit_iff_coprime m s).mp hu).symm⟩
      simp [β.map_nonunit hunit]
    · simp [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hs]
