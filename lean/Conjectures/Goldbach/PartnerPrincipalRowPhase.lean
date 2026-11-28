import Mathlib
import Conjectures.Goldbach.SharpSingularSeriesRatios

/-!
The full complex principal row of the twisted Goldbach singular series: the
principal character of level one paired with an arbitrary primitive partner.

The mixed principal identity of `Conjectures.Goldbach.SharpSingularSeriesRatios`
evaluates the pair at any common level; symmetry of the series in its two
arguments turns it into the row with the principal character in the first slot.
The surviving case is a squarefree conductor coprime to the target, where the
ordinary local count is the product of `p - 2` over the prime factors and the
Moebius value is the parity of the number of prime factors.

Adapted from `Conjectures.Goldbach.SharpSingularSeriesRatios` (mixed principal
identities `mixed_exact`, `mixed_zero`, `principal_card`, `local_factors`).
-/

namespace Conjectures.Goldbach.PartnerPrincipalRowPhase_aux

open Finset DirichletCharacter
open Conjectures.Goldbach.SharpSingularSeriesRatiosProof
open TwistedGoldbachSingularSeries TwistedGoldbachConductorRatio TwistedGoldbachLocalProduct

/-! ### Symmetry of the two twisted arguments -/

private theorem coefficient_symm {r s : ℕ} (α : DirichletCharacter ℂ r) (β : DirichletCharacter ℂ s)
    (m d : ℕ) : coefficient α β m d = coefficient β α m d := by
  classical
  by_cases hd : d = 0
  · simp [coefficient, hd]
  · let _ : NeZero d := ⟨hd⟩
    by_cases h : r ∣ d ∧ s ∣ d
    · have h2 : s ∣ d ∧ r ∣ d := ⟨h.2, h.1⟩
      simp only [coefficient, dite_eq_left hd, dite_eq_left h, dite_eq_left h2]
      unfold gaussCoefficient
      rw [mul_comm (changeLevel h.1 α) (changeLevel h.2 β)]
      ring
    · have h2 : ¬(s ∣ d ∧ r ∣ d) := fun hh => h ⟨hh.2, hh.1⟩
      simp [coefficient, hd, h, h2]

private theorem series_symm {r s : ℕ} (α : DirichletCharacter ℂ r) (β : DirichletCharacter ℂ s)
    (m : ℕ) : series α β m = series β α m := by
  unfold series
  exact tsum_congr fun d => coefficient_symm α β m d

/-! ### The ordinary local count at a prime away from the target -/

private theorem local_principal {p : ℕ} [Fact p.Prime] (m : ℕ) (hpm : ¬ p ∣ m) :
    J (1 : DirichletCharacter ℂ p) 1 (m : ZMod p) = ((p : ℂ) - 2) := by
  classical
  have hp : p.Prime := Fact.out
  let _ : NeZero p := ⟨hp.ne_zero⟩
  have hm0 : (m : ZMod p) ≠ 0 := fun h => hpm ((ZMod.natCast_eq_zero_iff m p).mp h)
  rw [principal_card]
  have hset : (univ.filter (admissible (m : ZMod p))) =
      (univ.erase (0 : ZMod p)).erase (m : ZMod p) := by
    ext x
    simp only [mem_filter, mem_erase, mem_univ, true_and, admissible, isUnit_iff_ne_zero]
    constructor
    · rintro ⟨h0, h1⟩
      exact ⟨fun h => h1 (sub_eq_zero.mpr h.symm), h0, trivial⟩
    · rintro ⟨h1, h0, _⟩
      exact ⟨h0, fun h => h1 (sub_eq_zero.mp h).symm⟩
  rw [hset, card_erase_of_mem (mem_erase.mpr ⟨hm0, mem_univ _⟩), card_erase_of_mem (mem_univ _),
    card_univ, ZMod.card p]
  have h2 : 2 ≤ p := hp.two_le
  have hsub : p - 1 - 1 = p - 2 := by omega
  rw [hsub, Nat.cast_sub h2, Nat.cast_ofNat]

/-! ### The ordinary count at a squarefree level coprime to the target -/

private theorem principal_product {s m : ℕ} [NeZero s] (hs : Squarefree s) (hcop : s.Coprime m) :
    J (1 : DirichletCharacter ℂ s) 1 (m : ZMod s) = ∏ p ∈ s.primeFactors, ((p : ℂ) - 2) := by
  let a : s.primeFactors → ℕ := fun p => (p : ℕ)
  have aprime (i : s.primeFactors) : (a i).Prime := Nat.prime_of_mem_primeFactors i.property
  let _ : ∀ i, NeZero (a i) := fun i => ⟨(aprime i).ne_zero⟩
  have copr : Pairwise (fun i j : s.primeFactors => (a i).Coprime (a j)) := by
    intro i j hij
    refine ((aprime i).coprime_iff_not_dvd).mpr (fun h => hij (Subtype.ext ?_))
    exact (((aprime j).dvd_iff_eq (aprime i).ne_one).mp h).symm
  have hprod : (∏ i, a i) = s :=
    (Finset.prod_coe_sort s.primeFactors (fun p : ℕ => p)).trans
      (Nat.prod_primeFactors_of_squarefree hs)
  let e : ZMod s ≃+* ∀ i, ZMod (a i) :=
    (ZMod.ringEquivCongr hprod.symm).trans (ZMod.prodEquivPi a copr)
  have hJ := local_factors e (1 : DirichletCharacter ℂ s) 1 m
  simp only [component_one] at hJ
  rw [hJ]
  rw [← Finset.prod_coe_sort s.primeFactors (fun p : ℕ => ((p : ℂ) - 2))]
  apply Finset.prod_congr rfl
  intro p _
  let _ : Fact (a p).Prime := ⟨aprime p⟩
  have hpm : ¬ (a p) ∣ m :=
    ((aprime p).coprime_iff_not_dvd).mp
      (hcop.of_dvd_left (Nat.dvd_of_mem_primeFactors p.property))
  exact local_principal m hpm

private theorem principal_product_ne_zero {s m : ℕ} [NeZero s] (_hs : Squarefree s)
    (hcop : s.Coprime m) (he : Even m) :
    (∏ p ∈ s.primeFactors, ((p : ℂ) - 2)) ≠ 0 := by
  refine prod_ne_zero_iff.mpr (fun p hp => ?_)
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hp2 : (p : ℂ) ≠ 2 := by
    intro h
    have hpe : p = 2 := by exact_mod_cast h
    subst hpe
    have hd : (2 : ℕ) ∣ s := Nat.dvd_of_mem_primeFactors hp
    have hm2 : (2 : ℕ) ∣ m := even_iff_two_dvd.mp he
    exact (Nat.prime_two.coprime_iff_not_dvd.mp (hcop.of_dvd_left hd)) hm2
  intro h
  apply hp2
  linear_combination h

private theorem moebius_parity {s : ℕ} (hs : Squarefree s) :
    (ArithmeticFunction.moebius s : ℂ) = (-1 : ℂ) ^ s.primeFactors.card := by
  rw [ArithmeticFunction.moebius_apply_of_squarefree hs]
  have hcard : s.primeFactors.card = s.primeFactorsList.length := by
    rw [← Nat.toFinset_factors s, List.toFinset_card_of_nodup hs.nodup_primeFactorsList]
  rw [ArithmeticFunction.cardFactors_apply, hcard]
  push_cast
  ring

end Conjectures.Goldbach.PartnerPrincipalRowPhase_aux

theorem Conjectures.Goldbach.PartnerPrincipalRowPhase :
by
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
  exact ∀ (s : ℕ) [NeZero s] (β : DirichletCharacter ℂ s), β.IsPrimitive → ∀ m : ℕ, 0 < m → Even m → S P β m = if Squarefree s ∧ s.Coprime m then O m * ((-1:ℂ)^s.primeFactors.card) * β (m:ZMod s) / (∏ p ∈ s.primeFactors, ((p:ℂ)-2)) else 0
:= by
  classical
  dsimp only
  intro s _ β hβ m hm he
  change Conjectures.Goldbach.SharpSingularSeriesRatiosProof.TwistedGoldbachLocalProduct.series
      (1 : DirichletCharacter ℂ 1) β m =
    if Squarefree s ∧ s.Coprime m then
      Conjectures.Goldbach.SharpSingularSeriesRatiosProof.TwistedGoldbachLocalProduct.series
        (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m *
        ((-1 : ℂ) ^ s.primeFactors.card) * β (m : ZMod s) /
          (∏ p ∈ s.primeFactors, ((p : ℂ) - 2))
    else 0
  rw [Conjectures.Goldbach.PartnerPrincipalRowPhase_aux.series_symm]
  by_cases h : Squarefree s ∧ s.Coprime m
  · rw [ite_eq_left h]
    obtain ⟨hsq, hcop⟩ := h
    have hmix := Conjectures.Goldbach.SharpSingularSeriesRatiosProof.TwistedGoldbachMixedPrincipal.mixed_exact β hβ m hm
    rw [Conjectures.Goldbach.PartnerPrincipalRowPhase_aux.principal_product hsq hcop,
      Conjectures.Goldbach.PartnerPrincipalRowPhase_aux.moebius_parity hsq] at hmix
    rw [eq_div_iff
      (Conjectures.Goldbach.PartnerPrincipalRowPhase_aux.principal_product_ne_zero hsq hcop he)]
    rw [hmix]
    ring
  · rw [ite_eq_right h]
    refine Conjectures.Goldbach.SharpSingularSeriesRatiosProof.TwistedGoldbachMixedPrincipal.mixed_zero β hβ m hm he ?_
    by_cases hsq : Squarefree s
    · exact Or.inr (fun hc => h ⟨hsq, hc.symm⟩)
    · exact Or.inl hsq
