import Mathlib
import Conjectures.Goldbach.SharpSingularSeriesRatios

/-! Unbounded normalized quadratic mass on squarefree partners at a fixed target.
The local Jacobi tables and the exact Euler product come from
`Conjectures.Goldbach.SharpSingularSeriesRatios`. -/

namespace Conjectures.Goldbach.PartnerQuadraticObstruction_aux

open Finset DirichletCharacter
open Conjectures.Goldbach.SharpSingularSeriesRatiosProof
open Conjectures.Goldbach.SharpSingularSeriesRatiosProof.TwistedGoldbachSingularSeries
open Conjectures.Goldbach.SharpSingularSeriesRatiosProof.TwistedGoldbachConductorRatio
open Conjectures.Goldbach.SharpSingularSeriesRatiosProof.TwistedGoldbachLocalProduct
open Conjectures.Goldbach.SharpSingularSeriesRatiosProof.TwistedGoldbachMixedPrincipal
open Conjectures.Goldbach.SharpSingularSeriesRatiosProof.SquarefreeTwistedGoldbachDensity
open scoped BigOperators Classical

/-- The nontrivial characters at a given level. -/
noncomputable def nontriv (p : ℕ) : Finset (DirichletCharacter ℂ p) :=
  (univ : Finset (DirichletCharacter ℂ p)).filter (fun β => β ≠ 1)

theorem mem_nontriv {p : ℕ} {β : DirichletCharacter ℂ p} : β ∈ nontriv p ↔ β ≠ 1 := by
  simp [nontriv]

private theorem two_ne_zero {p : ℕ} (hp : 3 ≤ p) : (2 : ZMod p) ≠ 0 := by
  intro h
  have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
  have := Nat.le_of_dvd (by decide) hd
  omega

private theorem local_nontrivial {p : ℕ} [NeZero p] (hp : p.Prime) (hp3 : 3 ≤ p)
    (β : DirichletCharacter ℂ p) (hβ : β ≠ 1) :
    ‖J (1 : DirichletCharacter ℂ p) β (2 : ZMod p)‖ = 1 := by
  let _ : Fact p.Prime := ⟨hp⟩
  have t := local_norm (1 : DirichletCharacter ℂ p) β (2 : ZMod p)
  change ‖J (1 : DirichletCharacter ℂ p) β (2 : ZMod p)‖ = _ at t
  simpa [two_ne_zero hp3, hβ] using t

private theorem local_principal {p : ℕ} [NeZero p] (hp : p.Prime) (hp3 : 3 ≤ p) :
    ‖J (1 : DirichletCharacter ℂ p) 1 (2 : ZMod p)‖ = (p:ℝ) - 2 := by
  let _ : Fact p.Prime := ⟨hp⟩
  have t := local_norm (1 : DirichletCharacter ℂ p) (1 : DirichletCharacter ℂ p) (2 : ZMod p)
  change ‖J (1 : DirichletCharacter ℂ p) 1 (2 : ZMod p)‖ = _ at t
  simpa [two_ne_zero hp3] using t

private theorem isPrimitive_of_ne_one {p : ℕ} [NeZero p] (hp : p.Prime)
    (β : DirichletCharacter ℂ p) (hβ : β ≠ 1) : β.IsPrimitive := by
  rw [isPrimitive_def]
  have h1 : β.conductor ≠ 1 := (eq_one_iff_conductor_eq_one).not.mp hβ
  have hd := (Nat.dvd_prime hp).mp β.conductor_dvd_level
  omega

private theorem card_nontrivial {p : ℕ} [NeZero p] (hp : p.Prime) :
    (nontriv p).card = p - 2 := by
  have h1 : nontriv p = (univ : Finset (DirichletCharacter ℂ p)).erase 1 := by
    ext x; simp [nontriv]
  rw [h1, card_erase_of_mem (mem_univ 1), card_univ, ← Nat.card_eq_fintype_card,
    card_eq_totient_of_hasEnoughRootsOfUnity ℂ p, Nat.totient_prime hp]
  omega

private theorem series_ratio {p : ℕ} [NeZero p] (β : DirichletCharacter ℂ p)
    (hβ : β.IsPrimitive) :
    series (1 : DirichletCharacter ℂ 1) β 2 =
      series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) 2 *
      (J (1 : DirichletCharacter ℂ p) β (2 : ZMod p) /
        J (1 : DirichletCharacter ℂ p) 1 (2 : ZMod p)) := by
  have h := conductor_identity (α := (1 : DirichletCharacter ℂ 1)) (β := β) (L := p)
    isPrimitive_one_level_one hβ (one_dvd p) (dvd_refl p) 2 (by decide)
  simp only [changeLevel_self, map_one] at h
  have hJ : J (1 : DirichletCharacter ℂ p) 1 (2 : ZMod p) ≠ 0 := principal_ne_zero p 2 (by decide)
  apply mul_right_cancel₀ hJ
  rw [mul_assoc, div_mul_cancel₀ _ hJ]
  exact h

private theorem prime_mass {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) :
    (∑ β ∈ nontriv p, ‖series (1 : DirichletCharacter ℂ 1) β 2‖ ^ 2) =
      ‖series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) 2‖ ^ 2 / ((p:ℝ) - 2) := by
  let _ : NeZero p := ⟨hp.ne_zero⟩
  let _ : Fact p.Prime := ⟨hp⟩
  have hpr := local_principal hp hp3
  have hpos : (0:ℝ) < (p:ℝ) - 2 := by
    have : (3:ℝ) ≤ p := by exact_mod_cast hp3
    linarith
  have term : ∀ β ∈ nontriv p,
      ‖series (1 : DirichletCharacter ℂ 1) β 2‖ ^ 2 =
        ‖series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) 2‖ ^ 2 /
          ((p:ℝ) - 2) ^ 2 := by
    intro β hβ
    have hne : β ≠ 1 := mem_nontriv.mp hβ
    have hprim := isPrimitive_of_ne_one hp β hne
    rw [series_ratio β hprim, norm_mul, norm_div, local_nontrivial hp hp3 β hne, hpr]
    have hne' : ((p:ℝ) - 2) ≠ 0 := hpos.ne'
    field_simp [hne']
  have hcard : ((p - 2 : ℕ) : ℝ) = (p:ℝ) - 2 := by
    have h2 : (2:ℕ) ≤ p := by omega
    have h := Nat.cast_sub h2 (R := ℝ)
    rwa [Nat.cast_ofNat] at h
  refine (Finset.sum_congr rfl (fun β hβ => term β hβ)).trans ?_
  rw [sum_const, nsmul_eq_mul, card_nontrivial hp, hcard]
  have hne' : ((p:ℝ) - 2) ≠ 0 := hpos.ne'
  field_simp [hne']

/-- The mass of the odd primes, weighted by `1/(p-2)`, is unbounded. -/
private theorem mass_unbounded : ∀ K : ℝ, ∃ N : ℕ,
    K < ∑ p ∈ (range N).filter (fun p : ℕ => p.Prime ∧ 3 ≤ p), (1:ℝ) / ((p:ℝ) - 2) := by
  intro K
  have ind : ∀ n : ℕ, 0 ≤ (Set.indicator {p : ℕ | p.Prime} (fun n : ℕ => (1:ℝ)/n)) n :=
    fun n => Set.indicator_nonneg (fun _ _ => by positivity) n
  have hdiv : ∀ M : ℝ, ∃ N : ℕ, M < ∑ n ∈ range N,
      (Set.indicator {p : ℕ | p.Prime} (fun n : ℕ => (1:ℝ)/n)) n := by
    by_contra! h
    obtain ⟨M, hM⟩ := h
    apply not_summable_one_div_on_primes
    refine ⟨⨆ N : ℕ, ∑ n ∈ range N,
      (Set.indicator {p : ℕ | p.Prime} (fun n : ℕ => (1:ℝ)/n)) n, ?_⟩
    refine (hasSum_iff_tendsto_nat_of_nonneg ind _).mpr ?_
    refine tendsto_atTop_ciSup (monotone_nat_of_le_succ fun N => ?_) ⟨M, ?_⟩
    · rw [sum_range_succ]
      linarith [ind N]
    · rintro _ ⟨N, rfl⟩
      exact hM N
  obtain ⟨N, hN⟩ := hdiv (K + 1/2)
  have hT : (∑ n ∈ range N, (Set.indicator {p : ℕ | p.Prime} (fun n : ℕ => (1:ℝ)/n)) n) =
      ∑ p ∈ (range N).filter (fun p : ℕ => p.Prime), (1:ℝ)/(p:ℝ) := by
    symm
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp [Set.indicator_apply]
  rw [hT] at hN
  have hsub : (range N).filter (fun p : ℕ => p.Prime) ⊆
      insert 2 ((range N).filter (fun p : ℕ => p.Prime ∧ 3 ≤ p)) := by
    intro p hp
    have hp' := mem_filter.mp hp
    rcases Nat.lt_or_ge p 3 with h | h
    · have h2 : p = 2 := by
        have := hp'.2.two_le
        omega
      subst h2
      exact mem_insert_self 2 _
    · exact mem_insert_of_mem (mem_filter.mpr ⟨hp'.1, hp'.2, h⟩)
  have htwo : (2:ℕ) ∉ (range N).filter (fun p : ℕ => p.Prime ∧ 3 ≤ p) := by
    intro hmem
    have := (mem_filter.mp hmem).2.2
    omega
  have hstep : (∑ p ∈ (range N).filter (fun p : ℕ => p.Prime), (1:ℝ)/(p:ℝ)) ≤
      (∑ p ∈ (range N).filter (fun p : ℕ => p.Prime ∧ 3 ≤ p), (1:ℝ)/(p:ℝ)) + 1/2 := by
    have h1 := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun p _ _ => by positivity : ∀ p ∈ insert 2 ((range N).filter (fun p : ℕ => p.Prime ∧ 3 ≤ p)),
        p ∉ (range N).filter (fun p : ℕ => p.Prime) → (0:ℝ) ≤ 1/(p:ℝ))
    rw [sum_insert htwo] at h1
    push_cast at h1
    linarith
  have hstep2 : (∑ p ∈ (range N).filter (fun p : ℕ => p.Prime ∧ 3 ≤ p), (1:ℝ)/(p:ℝ)) ≤
      ∑ p ∈ (range N).filter (fun p : ℕ => p.Prime ∧ 3 ≤ p), (1:ℝ)/((p:ℝ)-2) := by
    refine Finset.sum_le_sum fun p hp => ?_
    have hpm := (mem_filter.mp hp).2
    have hp3 : (3:ℝ) ≤ p := by exact_mod_cast hpm.2
    have hpos : (0:ℝ) < (p:ℝ) - 2 := by linarith
    exact one_div_le_one_div_of_le hpos (by linarith)
  have hmid : K < ∑ p ∈ (range N).filter (fun p : ℕ => p.Prime ∧ 3 ≤ p), (1:ℝ)/(p:ℝ) := by
    linarith [hN, hstep]
  exact ⟨N, lt_of_lt_of_le hmid hstep2⟩

theorem unbounded_mass : ∀ K : ℝ, ∃ F : Finset (Σ s : ℕ, DirichletCharacter ℂ s),
    (∀ b ∈ F, b.1 ≠ 0 ∧ b.2.IsPrimitive ∧ Squarefree b.1) ∧
    K * ‖series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) 2‖ ^ 2 <
      ∑ b ∈ F, ‖series (1 : DirichletCharacter ℂ 1) b.2 2‖ ^ 2 := by
  intro K
  obtain ⟨N, hN⟩ := mass_unbounded K
  let T := (range N).filter (fun p : ℕ => p.Prime ∧ 3 ≤ p)
  refine ⟨T.sigma (fun p => nontriv p), ?_, ?_⟩
  · intro b hb
    obtain ⟨hp, hβ⟩ := Finset.mem_sigma.mp hb
    have hpm := mem_filter.mp hp
    have hprime : b.1.Prime := hpm.2.1
    have hne : b.2 ≠ 1 := mem_nontriv.mp hβ
    let _ : NeZero b.1 := ⟨hprime.ne_zero⟩
    exact ⟨hprime.ne_zero, isPrimitive_of_ne_one hprime b.2 hne, hprime.squarefree⟩
  · have hsum : (∑ b ∈ T.sigma (fun p => nontriv p),
        ‖series (1 : DirichletCharacter ℂ 1) b.2 2‖ ^ 2) =
        ‖series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) 2‖ ^ 2 *
          ∑ p ∈ T, (1:ℝ) / ((p:ℝ) - 2) := by
      calc
        (∑ b ∈ T.sigma (fun p => nontriv p),
            ‖series (1 : DirichletCharacter ℂ 1) b.2 2‖ ^ 2)
            = ∑ p ∈ T, ∑ β ∈ nontriv p,
                ‖series (1 : DirichletCharacter ℂ 1) β 2‖ ^ 2 := by
              rw [Finset.sum_sigma]
        _ = ∑ p ∈ T, ‖series (1 : DirichletCharacter ℂ 1)
              (1 : DirichletCharacter ℂ 1) 2‖ ^ 2 * ((1:ℝ) / ((p:ℝ) - 2)) := by
              refine Finset.sum_congr rfl fun p hp => ?_
              have hpm := mem_filter.mp hp
              rw [prime_mass hpm.2.1 hpm.2.2, div_eq_mul_one_div]
        _ = ‖series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) 2‖ ^ 2 *
              ∑ p ∈ T, (1:ℝ) / ((p:ℝ) - 2) := (Finset.mul_sum _ _ _).symm
    rw [hsum]
    have hO : 0 < ‖series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) 2‖ ^ 2 := by
      have h1 := ordinary_at_least_one 2 (by decide) (by decide)
      have h2 : 1 ≤ ‖series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) 2‖ :=
        h1.trans (Complex.re_le_norm _)
      positivity
    calc
      K * ‖series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) 2‖ ^ 2
          < (∑ p ∈ T, (1:ℝ) / ((p:ℝ) - 2)) *
              ‖series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) 2‖ ^ 2 :=
        mul_lt_mul_of_pos_right hN hO
      _ = ‖series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) 2‖ ^ 2 *
            ∑ p ∈ T, (1:ℝ) / ((p:ℝ) - 2) := mul_comm _ _

end Conjectures.Goldbach.PartnerQuadraticObstruction_aux

theorem Conjectures.Goldbach.PartnerQuadraticObstruction :
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
  exact ∀ K : ℝ, ∃ F : Finset (Σ s : ℕ, DirichletCharacter ℂ s), (∀ b ∈ F, b.1 ≠ 0 ∧ b.2.IsPrimitive ∧ Squarefree b.1) ∧ K * ‖O 2‖ ^ 2 < ∑ b ∈ F, ‖S (1 : DirichletCharacter ℂ 1) b.2 2‖ ^ 2 := by
  classical
  dsimp only
  exact Conjectures.Goldbach.PartnerQuadraticObstruction_aux.unbounded_mass
