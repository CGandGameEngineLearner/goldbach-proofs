import Mathlib
import Conjectures.Goldbach.PrimitivePartnerCubicMass

/-! Exact squared mass of all primitive origins at a fixed level.
The row Parseval identity and the common-level injection are from Goldbach PR 4245;
the conductor identity and the prime-power Jacobi formulas are from PR 4023.
The CRT calculation below adapts the proof of ordinary_product in that module.
-/

namespace PartnerOrigins

open DirichletCharacter Finset
open scoped Classical BigOperators

abbrev Partner := Σ s : ℕ, DirichletCharacter ℂ s

private noncomputable def origin {D : ℕ} (χ : DirichletCharacter ℂ D) : Partner :=
  ⟨χ.conductor, χ.primitiveCharacter⟩

private theorem origin_injective (D : ℕ) : Function.Injective (@origin D) := by
  classical
  let lift (b : Partner) : DirichletCharacter ℂ D :=
    if h : b.1 ∣ D then changeLevel h b.2 else 1
  have hl (χ : DirichletCharacter ℂ D) : lift (origin χ) = χ := by
    simpa only [lift, origin, dif_pos χ.conductor_dvd_level] using χ.changeLevel_primitiveCharacter
  intro χ ψ h
  simpa only [hl] using congrArg lift h

private theorem same_origin_of_equal_lifts {D s t : ℕ} [NeZero D]
    (a : DirichletCharacter ℂ s) (b : DirichletCharacter ℂ t)
    (hs : s ∣ D) (ht : t ∣ D) (ha : a.IsPrimitive) (hb : b.IsPrimitive)
    (h : changeLevel hs a = changeLevel ht b) :
    (⟨s, a⟩ : Partner) = ⟨t, b⟩ := by
  have eqst := congrArg DirichletCharacter.conductor h
  rw [conductor_changeLevel, conductor_changeLevel, ha, hb] at eqst
  subst t
  exact congrArg (Sigma.mk s) (changeLevel_injective hs h)

noncomputable def partners (D : ℕ) [NeZero D] : Finset Partner :=
  univ.image (@origin D)

theorem mem_partners (D : ℕ) [NeZero D] (b : Partner) :
    b ∈ partners D ↔ b.1 ≠ 0 ∧ b.1 ∣ D ∧ b.2.IsPrimitive := by
  classical
  rcases b with ⟨s, ψ⟩
  constructor
  · intro h
    obtain ⟨χ, _, eq⟩ := mem_image.mp h
    have hgood : (origin χ).1 ≠ 0 ∧ (origin χ).1 ∣ D ∧ (origin χ).2.IsPrimitive :=
      ⟨χ.conductor_ne_zero, χ.conductor_dvd_level, χ.primitiveCharacter_isPrimitive⟩
    exact eq ▸ hgood
  · rintro ⟨_, hs, hψ⟩
    let χ := changeLevel hs ψ
    apply mem_image.mpr
    refine ⟨χ, mem_univ _, ?_⟩
    exact same_origin_of_equal_lifts χ.primitiveCharacter ψ χ.conductor_dvd_level hs
      χ.primitiveCharacter_isPrimitive hψ χ.changeLevel_primitiveCharacter

theorem sum_partners (D : ℕ) [NeZero D] (f : Partner → ℝ) :
    (∑ b ∈ partners D, f b) =
      ∑ χ : DirichletCharacter ℂ D, f ⟨χ.conductor, χ.primitiveCharacter⟩ := by
  classical
  unfold partners
  rw [sum_image (fun _ _ _ _ h => origin_injective D h)] <;> rfl

end PartnerOrigins

namespace PartnerLevelLocal

open Finset DirichletCharacter
open Conjectures.Goldbach.SharpSingularSeriesRatiosProof
open TwistedGoldbachConductorRatio TwistedGoldbachLocalProduct
open scoped BigOperators Classical

private theorem prime_power_ratio {p : ℕ} [hp : Fact p.Prime] (a m : ℕ) (ha : 0 < a) :
    (((p ^ a).totient : ℕ) : ℝ) /
        ‖J (1 : DirichletCharacter ℂ (p ^ a)) 1 (m : ZMod (p ^ a))‖ =
      if ¬p ∣ m then ((p : ℝ) - 1) / ((p : ℝ) - 2) else 1 := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero ha.ne'
  have hf : (0 : ℝ) < ((p ^ j : ℕ) : ℝ) := by exact_mod_cast pow_pos hp.out.pos j
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := sub_pos.mpr (by exact_mod_cast hp.out.one_lt)
  have form (d : ℕ) [NeZero d] (hd : d = p * p ^ j) :
      (d.totient : ℝ) / ‖J (1 : DirichletCharacter ℂ d) 1 (m : ZMod d)‖ =
        if ¬p ∣ m then ((p : ℝ) - 1) / ((p : ℝ) - 2) else 1 := by
    subst d
    have ht : (p * p ^ j).totient = p ^ j * (p - 1) := by
      rw [← pow_succ', Nat.totient_prime_pow_succ hp.out]
    rw [ht, ordinary_prime_power, Nat.cast_mul, Nat.cast_sub hp.out.one_le, Nat.cast_one]
    by_cases h : p ∣ m
    · simp only [h, if_true, not_true_eq_false, if_false, div_self (mul_ne_zero hf.ne' hp1.ne')]
    · simp only [h, if_false, not_false_eq_true, if_true]
      exact mul_div_mul_left _ _ hf.ne'
  exact form _ (pow_succ' p j)

-- CRT decomposition as in TwistedGoldbachMixedPrincipal.ordinary_product.
theorem totient_ratio (D m : ℕ) [NeZero D] (_he : Even m) :
    (D.totient : ℝ) / ‖J (1 : DirichletCharacter ℂ D) 1 (m : ZMod D)‖ =
      ∏ p ∈ D.primeFactors.filter (fun p => ¬p ∣ m),
        (((p : ℝ) - 1) / ((p : ℝ) - 2)) := by
  classical
  let F (p : D.primeFactors) := (p : ℕ) ^ (D.factorization p)
  have pp (p : D.primeFactors) : (p : ℕ).Prime := Nat.prime_of_mem_primeFactors p.property
  let _ : ∀ p : D.primeFactors, Fact (p : ℕ).Prime := fun p => ⟨pp p⟩
  let _ : ∀ p : D.primeFactors, NeZero (F p) := fun p => ⟨pow_ne_zero _ (pp p).ne_zero⟩
  have expo (p : D.primeFactors) : 0 < D.factorization (p : ℕ) :=
    (pp p).factorization_pos_of_dvd (NeZero.ne D) (Nat.dvd_of_mem_primeFactors p.property)
  let e : ZMod D ≃+* ∀ p : D.primeFactors, ZMod (F p) := ZMod.equivPi D (NeZero.ne D)
  have hJ := local_factors e (1 : DirichletCharacter ℂ D) 1 m
  simp only [component_one] at hJ
  have hφ : D.totient = ∏ p : D.primeFactors, (F p).totient := by
    rw [Nat.totient_eq_prod_factorization (NeZero.ne D), Nat.prod_factorization_eq_prod_primeFactors]
    simp only [F, Nat.totient_prime_pow (pp _) (expo _)]
    exact (Finset.prod_coe_sort D.primeFactors (fun p : ℕ => p ^ (D.factorization p - 1) * (p - 1))).symm
  have hφr : (D.totient : ℝ) = ∏ p : D.primeFactors, ((F p).totient : ℝ) := by exact_mod_cast hφ
  rw [hφr, hJ, norm_prod, ← prod_div_distrib, Finset.prod_filter]
  let g (p : ℕ) : ℝ := if ¬p ∣ m then ((p : ℝ) - 1) / ((p : ℝ) - 2) else 1
  change _ = ∏ p ∈ D.primeFactors, g p
  rw [← Finset.prod_coe_sort D.primeFactors g]
  apply prod_congr rfl
  intro p _
  exact prime_power_ratio (p := (p : ℕ)) (D.factorization p) m (expo p)

end PartnerLevelLocal

namespace PartnerLevelAssembly
open Finset DirichletCharacter
open Conjectures.Goldbach.SharpSingularSeriesRatiosProof
open TwistedGoldbachLocalProduct TwistedGoldbachConductorRatio
open scoped BigOperators Classical

theorem mass (D r : ℕ) [NeZero D] [NeZero r] (hr : r ∣ D)
    (α : DirichletCharacter ℂ r) (hα : α.IsPrimitive) (m : ℕ)
    (hm : 0 < m) (he : Even m) :
    ∃ F : Finset (Σ s : ℕ, DirichletCharacter ℂ s),
      (∀ b, b ∈ F ↔ b.1 ≠ 0 ∧ b.1 ∣ D ∧ b.2.IsPrimitive) ∧
      (∑ b ∈ F, ‖series α b.2 m‖ ^ 2) =
        ‖series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m‖ ^ 2 *
        ∏ p ∈ D.primeFactors.filter (fun p => ¬ p ∣ m), ((p : ℝ)-1)/((p : ℝ)-2) := by
  classical
  refine ⟨PartnerOrigins.partners D, PartnerOrigins.mem_partners D, ?_⟩
  let A := changeLevel hr α
  let ordinary := series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m
  let principal := J (1 : DirichletCharacter ℂ D) 1 (m : ZMod D)
  have hn : principal ≠ 0 := principal_ne_zero D m he
  have hnorm : ‖principal‖ ≠ 0 := (norm_pos_iff.mpr hn).ne'
  have term (χ : DirichletCharacter ℂ D) :
      ‖series α χ.primitiveCharacter m‖ ^ 2 =
        (‖ordinary‖ ^ 2 / ‖principal‖ ^ 2) * ‖J A χ (m : ZMod D)‖ ^ 2 := by
    letI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    have hid : series α χ.primitiveCharacter m * principal =
        ordinary * J A χ (m : ZMod D) := by
      simpa only [series, principal, ordinary, A, changeLevel_primitiveCharacter] using
        (conductor_identity hα χ.primitiveCharacter_isPrimitive hr χ.conductor_dvd_level m hm)
    rw [(eq_div_iff hn).2 hid, norm_div, norm_mul, div_pow, mul_pow]
    ring
  rw [PartnerOrigins.sum_partners D (fun b => ‖series α b.2 m‖ ^ 2)]
  change (∑ χ : DirichletCharacter ℂ D, ‖series α χ.primitiveCharacter m‖ ^ 2) = _
  simp_rw [term]
  rw [← Finset.mul_sum, CubicPartnerResearch.row_plancherel,
    ← PartnerLevelLocal.totient_ratio D m he]
  change (‖ordinary‖ ^ 2 / ‖principal‖ ^ 2) * ((D.totient : ℝ) * ‖principal‖) =
    ‖ordinary‖ ^ 2 * ((D.totient : ℝ) / ‖principal‖)
  field_simp [hnorm] <;> ring

end PartnerLevelAssembly

theorem Conjectures.Goldbach.PartnerLevelParseval : (by
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
  exact ∀ (D r : ℕ) [NeZero D] [NeZero r], r ∣ D → ∀ α : DirichletCharacter ℂ r, α.IsPrimitive → ∀ m : ℕ, 0 < m → Even m → ∃ F : Finset (Σ s : ℕ, DirichletCharacter ℂ s), (∀ b, b ∈ F ↔ b.1 ≠ 0 ∧ b.1 ∣ D ∧ b.2.IsPrimitive) ∧ (∑ b ∈ F, ‖S α b.2 m‖ ^ 2) = ‖O m‖ ^ 2 * ∏ p ∈ D.primeFactors.filter (fun p => ¬ p ∣ m), (((p:ℝ)-1)/((p:ℝ)-2))) := by
  classical
  dsimp only
  intro D r instD instr hr α hα m hm he
  exact PartnerLevelAssembly.mass D r hr α hα m hm he
