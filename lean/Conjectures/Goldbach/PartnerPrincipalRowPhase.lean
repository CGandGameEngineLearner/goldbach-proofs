import Mathlib
import Conjectures.Goldbach.SharpSingularSeriesRatios

open Finset DirichletCharacter
open Conjectures.Goldbach.SharpSingularSeriesRatiosProof
open TwistedGoldbachLocalProduct TwistedGoldbachConductorRatio TwistedGoldbachMixedPrincipal
open scoped BigOperators Classical

private theorem principal_product {s : ℕ} [NeZero s] (m : ℕ)
    (hs : Squarefree s) (hc : s.Coprime m) :
    J (1 : DirichletCharacter ℂ s) 1 (m : ZMod s) = ∏ p ∈ s.primeFactors, ((p:ℂ)-2) := by
  let F (p : s.primeFactors) := (p:ℕ) ^ s.factorization p
  have hp (p : s.primeFactors) := Nat.prime_of_mem_primeFactors p.property
  let _ : ∀ p : s.primeFactors, NeZero (F p) := fun p => ⟨pow_ne_zero _ (hp p).ne_zero⟩
  let e : ZMod s ≃+* ∀ p : s.primeFactors, ZMod (F p) := ZMod.equivPi s (NeZero.ne s)
  rw [local_factors e, ← Finset.prod_coe_sort s.primeFactors]
  apply prod_congr rfl
  intro p _
  simp only [component_one]
  have eq : F p = p.val := by
    dsimp [F]
    rw [Nat.factorization_eq_one_of_squarefree hs (hp p) (Nat.dvd_of_mem_primeFactors p.property), pow_one]
  have calcPrime (q : ℕ) [NeZero q] (hq : q = p.val) :
      J (1 : DirichletCharacter ℂ q) 1 (m:ZMod q) = (p.val:ℂ)-2 := by
    subst q
    let _ : Fact p.val.Prime := ⟨hp p⟩
    have hu := (ZMod.isUnit_iff_coprime m p.val).mpr
      (hc.symm.coprime_dvd_right (Nat.dvd_of_mem_primeFactors p.property))
    have h := Equiv.sum_comp (Equiv.mulLeft₀ (m:ZMod p.val) hu.ne_zero)
      (fun a : ZMod p.val => (1 : DirichletCharacter ℂ p.val) a * (1 : DirichletCharacter ℂ p.val) ((m:ZMod p.val)-a))
    calc
      _ = _ := h.symm
      _ = jacobiSum (1 : DirichletCharacter ℂ p.val) 1 := by
        unfold jacobiSum
        apply sum_congr rfl
        intro a _
        simp [← mul_one_sub, map_mul, MulChar.one_apply hu]
      _ = _ := by rw [jacobiSum_one_one,ZMod.card]
  exact calcPrime _ eq

private theorem swap {r s : ℕ} (a : DirichletCharacter ℂ r) (b : DirichletCharacter ℂ s) (m : ℕ) :
    series a b m = series b a m := by
  unfold series
  apply tsum_congr
  intro q
  unfold TwistedGoldbachSingularSeries.coefficient
  by_cases hq : q ≠ 0
  · letI : NeZero q := ⟨hq⟩
    simp only [dif_pos hq]
    by_cases h : r ∣ q ∧ s ∣ q
    · rw [dif_pos h, dif_pos h.symm]
      unfold TwistedGoldbachSingularSeries.gaussCoefficient
      rw [mul_comm (changeLevel h.1 a) (changeLevel h.2 b),
        mul_comm (gaussSum (changeLevel h.1 a) _) (gaussSum (changeLevel h.2 b) _)]
    · simp [h, show ¬(s ∣ q ∧ r ∣ q) from fun h' => h h'.symm]
  · simp [hq]

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
  dsimp only
  intro s _ β hβ m hm he
  change series (1 : DirichletCharacter ℂ 1) β m = if Squarefree s ∧ s.Coprime m then
    series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m *
    (-1:ℂ)^s.primeFactors.card * β (m:ZMod s) / _ else 0
  rw [swap]
  split_ifs with hs
  · have hJ := principal_product m hs.1 hs.2
    apply (eq_div_iff (hJ ▸ principal_ne_zero s m he)).mpr
    have h := mixed_exact β hβ m hm
    rw [hJ, ArithmeticFunction.moebius_apply_of_squarefree hs.1,
      ← (ArithmeticFunction.cardDistinctFactors_eq_cardFactors_iff_squarefree (NeZero.ne s)).mpr hs.1,
      ArithmeticFunction.cardDistinctFactors_eq_card_primeFactors] at h
    push_cast at h
    simpa only [mul_assoc] using h
  · apply mixed_zero β hβ m hm he
    by_cases hf : Squarefree s
    · exact Or.inr (fun hc => hs ⟨hf,hc.symm⟩)
    · exact Or.inl hf
