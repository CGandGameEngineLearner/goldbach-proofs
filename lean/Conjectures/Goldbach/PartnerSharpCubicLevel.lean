import Mathlib
import Conjectures.Goldbach.SharpSingularSeriesRatios

/-! Sharp cubic row constant at every odd squarefree level D, with attainment at
the principal row and target m = 2.

Reuses the local Jacobi-sum norm table (`SquarefreeTwistedGoldbachDensity.local_norm`)
and global CRT factorization (`TwistedGoldbachLocalProduct.full_product`) from
`Conjectures.Goldbach.SharpSingularSeriesRatios` (PR #4023). -/

namespace PartnerSharpCubicLevelProof

open Finset DirichletCharacter
open Conjectures.Goldbach.SharpSingularSeriesRatiosProof
open TwistedGoldbachConductorRatio TwistedGoldbachLocalProduct
open SquarefreeTwistedGoldbachDensity
open scoped BigOperators Classical

private theorem card_dirichletCharacter_prime (p : ℕ) [hp : Fact p.Prime] :
    Fintype.card (DirichletCharacter ℂ p) = p - 1 := by
  rw [← Nat.card_eq_fintype_card,
    DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ p,
    Nat.totient_prime hp.out]

private theorem prime_cubic_principal {p : ℕ} [hp : Fact p.Prime] (hp3 : 3 ≤ p)
    (m : ℕ) (hm : ¬ p ∣ m) :
    (∑ B : DirichletCharacter ℂ p,
      ‖J (1 : DirichletCharacter ℂ p) B (m : ZMod p) /
        J (1 : DirichletCharacter ℂ p) 1 (m : ZMod p)‖ ^ 3) =
      1 + 1 / ((p : ℝ) - 2) ^ 2 := by
  classical
  have hm0 : (m : ZMod p) ≠ 0 := mt (ZMod.natCast_eq_zero_iff m p).mp hm
  have hdpos : (0 : ℝ) < (p : ℝ) - 2 := by
    have : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
    linarith
  have h11 : ‖J (1 : DirichletCharacter ℂ p) 1 (m : ZMod p)‖ = (p : ℝ) - 2 := by
    change ‖localSum (1 : DirichletCharacter ℂ p) 1 (m : ZMod p)‖ = _
    rw [local_norm]
    simp [hm0]
  have h1B (B : DirichletCharacter ℂ p) (hB : B ≠ 1) :
      ‖J (1 : DirichletCharacter ℂ p) B (m : ZMod p)‖ = 1 := by
    change ‖localSum (1 : DirichletCharacter ℂ p) B (m : ZMod p)‖ = _
    rw [local_norm]
    simp [hm0, hB]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : DirichletCharacter ℂ p))]
  have hterm1 :
      ‖J (1 : DirichletCharacter ℂ p) 1 (m : ZMod p) /
        J (1 : DirichletCharacter ℂ p) 1 (m : ZMod p)‖ ^ 3 = 1 := by
    rw [norm_div, h11, div_self hdpos.ne', one_pow]
  have hrest :
      (∑ B ∈ Finset.univ.erase (1 : DirichletCharacter ℂ p),
        ‖J (1 : DirichletCharacter ℂ p) B (m : ZMod p) /
          J (1 : DirichletCharacter ℂ p) 1 (m : ZMod p)‖ ^ 3) =
        ∑ _B ∈ Finset.univ.erase (1 : DirichletCharacter ℂ p), (1 / ((p : ℝ) - 2)) ^ 3 := by
    apply Finset.sum_congr rfl
    intro B hB
    rw [norm_div, h1B B (Finset.ne_of_mem_erase hB), h11]
  have hcard : (Finset.univ.erase (1 : DirichletCharacter ℂ p)).card = p - 2 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      card_dirichletCharacter_prime p]
    omega
  rw [hterm1, hrest, Finset.sum_const, hcard, nsmul_eq_mul]
  have hcast : ((p - 2 : ℕ) : ℝ) = (p : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega : 2 ≤ p)]
    norm_num
  rw [hcast]
  field_simp [hdpos.ne']

private theorem nonprincipal_arith {p : ℕ} (hp5 : 5 ≤ p) :
    2 + ((p : ℝ) - 3) * (Real.sqrt p) ^ 3 ≤
      ((p : ℝ) - 2) ^ 3 + ((p : ℝ) - 2) := by
  have hp_real : (5 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp5
  have hp_nn : (0 : ℝ) ≤ (p : ℝ) := by linarith
  have hsqrt_le : Real.sqrt p ≤ ((p : ℝ) + 4) / 4 := by
    nlinarith [Real.sq_sqrt hp_nn, sq_nonneg (Real.sqrt p - 2)]
  have hcube : (Real.sqrt p) ^ 3 = (p : ℝ) * Real.sqrt p := by
    rw [pow_succ, Real.sq_sqrt hp_nn]
  rw [hcube]
  have hmul : ((p : ℝ) - 3) * ((p : ℝ) * Real.sqrt p) ≤
      ((p : ℝ) - 3) * ((p : ℝ) * (((p : ℝ) + 4) / 4)) := by
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    exact mul_le_mul_of_nonneg_left hsqrt_le hp_nn
  have hpoly : 2 + ((p : ℝ) - 3) * ((p : ℝ) * (((p : ℝ) + 4) / 4)) ≤
      ((p : ℝ) - 2) ^ 3 + ((p : ℝ) - 2) := by
    let t : ℝ := (p : ℝ) - 5
    have ht : 0 ≤ t := by dsimp [t]; linarith
    have hid : (((p : ℝ) - 2) ^ 3 + ((p : ℝ) - 2)) -
        (2 + ((p : ℝ) - 3) * ((p : ℝ) * (((p : ℝ) + 4) / 4))) =
        (3 * t ^ 3 + 20 * t ^ 2 + 39 * t + 22) / 4 := by
      dsimp [t]; ring
    nlinarith [sq_nonneg t, mul_nonneg (sq_nonneg t) ht]
  linarith

private theorem prime_cubic_bound {p : ℕ} [hp : Fact p.Prime] (hp3 : 3 ≤ p)
    (A : DirichletCharacter ℂ p) (m : ℕ) :
    (∑ B : DirichletCharacter ℂ p,
      ‖J A B (m : ZMod p) / J (1 : DirichletCharacter ℂ p) 1 (m : ZMod p)‖ ^ 3) ≤
      1 + 1 / ((p : ℝ) - 2) ^ 2 := by
  classical
  have hdpos : (0 : ℝ) < (p : ℝ) - 2 := by
    have : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
    linarith
  by_cases hm : p ∣ m
  · have hm0 : (m : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff m p).mpr hm
    have h11 : ‖J (1 : DirichletCharacter ℂ p) 1 (m : ZMod p)‖ = (p : ℝ) - 1 := by
      change ‖localSum (1 : DirichletCharacter ℂ p) 1 (m : ZMod p)‖ = _
      rw [local_norm]
      simp [hm0]
    have hden : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    have hsum :
        (∑ B : DirichletCharacter ℂ p,
          ‖J A B (m : ZMod p) / J (1 : DirichletCharacter ℂ p) 1 (m : ZMod p)‖ ^ 3) = 1 := by
      rw [Finset.sum_eq_single A⁻¹]
      · have hAA : ‖J A A⁻¹ (m : ZMod p)‖ = (p : ℝ) - 1 := by
          change ‖localSum A A⁻¹ (m : ZMod p)‖ = _
          rw [local_norm]
          simp [hm0]
        rw [norm_div, hAA, h11, div_self hden.ne', one_pow]
      · intro B _ hB
        have hne : A * B ≠ 1 := by
          intro h
          apply hB
          calc B = A⁻¹ * (A * B) := by group
            _ = A⁻¹ * 1 := by rw [h]
            _ = A⁻¹ := mul_one _
        have h0 : ‖J A B (m : ZMod p)‖ = 0 := by
          change ‖localSum A B (m : ZMod p)‖ = _
          rw [local_norm]
          simp [hm0, hne]
        rw [norm_div, h0, zero_div, zero_pow (by norm_num)]
      · intro h
        exact (h (Finset.mem_univ _)).elim
    rw [hsum]
    linarith [one_div_nonneg.mpr (sq_nonneg ((p : ℝ) - 2))]
  · by_cases hA : A = 1
    · subst hA
      exact (prime_cubic_principal hp3 m hm).le
    · have hm0 : (m : ZMod p) ≠ 0 := mt (ZMod.natCast_eq_zero_iff m p).mp hm
      have h11 : ‖J (1 : DirichletCharacter ℂ p) 1 (m : ZMod p)‖ = (p : ℝ) - 2 := by
        change ‖localSum (1 : DirichletCharacter ℂ p) 1 (m : ZMod p)‖ = _
        rw [local_norm]
        simp [hm0]
      have hAinv_ne : A⁻¹ ≠ 1 := by
        intro h
        exact hA (inv_eq_one.mp h)
      have hterm_one :
          ‖J A 1 (m : ZMod p) / J (1 : DirichletCharacter ℂ p) 1 (m : ZMod p)‖ ^ 3 =
            (1 / ((p : ℝ) - 2)) ^ 3 := by
        have hJ : ‖J A 1 (m : ZMod p)‖ = 1 := by
          change ‖localSum A 1 (m : ZMod p)‖ = _
          rw [local_norm]
          simp [hm0, hA]
        rw [norm_div, hJ, h11]
      have hterm_inv :
          ‖J A A⁻¹ (m : ZMod p) / J (1 : DirichletCharacter ℂ p) 1 (m : ZMod p)‖ ^ 3 =
            (1 / ((p : ℝ) - 2)) ^ 3 := by
        have hJ : ‖J A A⁻¹ (m : ZMod p)‖ = 1 := by
          change ‖localSum A A⁻¹ (m : ZMod p)‖ = _
          rw [local_norm]
          simp [hm0, hA]
        rw [norm_div, hJ, h11]
      let S := (Finset.univ.erase (1 : DirichletCharacter ℂ p)).erase A⁻¹
      have hmem_inv : A⁻¹ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ p) :=
        Finset.mem_erase.mpr ⟨hAinv_ne, Finset.mem_univ _⟩
      have hsplit :
          (∑ B : DirichletCharacter ℂ p,
            ‖J A B (m : ZMod p) / J (1 : DirichletCharacter ℂ p) 1 (m : ZMod p)‖ ^ 3) =
            (1 / ((p : ℝ) - 2)) ^ 3 + (1 / ((p : ℝ) - 2)) ^ 3 +
              ∑ B ∈ S, ‖J A B (m : ZMod p) / J (1 : DirichletCharacter ℂ p) 1 (m : ZMod p)‖ ^ 3 := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : DirichletCharacter ℂ p)),
          ← Finset.add_sum_erase _ _ hmem_inv, hterm_one, hterm_inv]
        ring
      have hS_sum :
          (∑ B ∈ S, ‖J A B (m : ZMod p) / J (1 : DirichletCharacter ℂ p) 1 (m : ZMod p)‖ ^ 3) =
            (S.card : ℝ) * (Real.sqrt p / ((p : ℝ) - 2)) ^ 3 := by
        rw [← nsmul_eq_mul, ← Finset.sum_const]
        apply Finset.sum_congr rfl
        intro B hB
        have hB_inv : B ≠ A⁻¹ := (Finset.mem_erase.mp hB).1
        have hB_one : B ≠ 1 := (Finset.mem_erase.mp (Finset.mem_erase.mp hB).2).1
        have hAB : A * B ≠ 1 := by
          intro h
          apply hB_inv
          calc B = A⁻¹ * (A * B) := by group
            _ = A⁻¹ * 1 := by rw [h]
            _ = A⁻¹ := mul_one _
        have hJ : ‖J A B (m : ZMod p)‖ = Real.sqrt p := by
          change ‖localSum A B (m : ZMod p)‖ = _
          rw [local_norm]
          simp [hm0, hA, hB_one, hAB]
        rw [norm_div, hJ, h11]
      have hcardS : S.card = p - 3 := by
        dsimp only [S]
        rw [Finset.card_erase_of_mem hmem_inv, Finset.card_erase_of_mem (Finset.mem_univ _),
          Finset.card_univ, card_dirichletCharacter_prime p]
        omega
      have hcastS : (S.card : ℝ) = (p : ℝ) - 3 := by
        rw [hcardS, Nat.cast_sub hp3]
        norm_num
      rw [hsplit, hS_sum, hcastS]
      have hcomb :
          (1 / ((p : ℝ) - 2)) ^ 3 + (1 / ((p : ℝ) - 2)) ^ 3 +
              ((p : ℝ) - 3) * (Real.sqrt p / ((p : ℝ) - 2)) ^ 3 =
            (2 + ((p : ℝ) - 3) * (Real.sqrt p) ^ 3) / ((p : ℝ) - 2) ^ 3 := by
        field_simp [hdpos.ne']
        ring
      have hrhs :
          1 + 1 / ((p : ℝ) - 2) ^ 2 =
            (((p : ℝ) - 2) ^ 3 + ((p : ℝ) - 2)) / ((p : ℝ) - 2) ^ 3 := by
        field_simp [hdpos.ne']
      rw [hcomb, hrhs]
      apply div_le_div_of_nonneg_right _ (pow_nonneg hdpos.le 3)
      rcases eq_or_ne p 3 with rfl | hpne3
      · norm_num
      · have hp5 : 5 ≤ p := by
          by_contra! hlt
          have : p = 4 := by omega
          subst this
          exact (by decide : ¬ Nat.Prime 4) hp.out
        exact nonprincipal_arith hp5

private theorem squarefree_factorization_eq_one {D p : ℕ} (hsq : Squarefree D)
    (hp : p ∈ D.primeFactors) : D.factorization p = 1 := by
  have hDne : D ≠ 0 := hsq.ne_zero
  have hmem := Nat.mem_primeFactors.mp hp
  have hge : 1 ≤ D.factorization p := (hmem.1.dvd_iff_one_le_factorization hDne).mp hmem.2.1
  have hle : D.factorization p ≤ 1 :=
    (Nat.squarefree_iff_factorization_le_one hDne).mp hsq p
  omega

private theorem changeLevel_eq_of_sigma_eq {D s₁ s₂ : ℕ}
    {ψ₁ : DirichletCharacter ℂ s₁} {ψ₂ : DirichletCharacter ℂ s₂}
    (h₁ : s₁ ∣ D) (h₂ : s₂ ∣ D)
    (heq : (⟨s₁, ψ₁⟩ : Σ s : ℕ, DirichletCharacter ℂ s) = ⟨s₂, ψ₂⟩) :
    changeLevel h₁ ψ₁ = changeLevel h₂ ψ₂ := by
  cases heq
  rfl

private theorem sigma_eq_of_changeLevel_eq {D s₁ s₂ : ℕ} [NeZero D]
    {ψ₁ : DirichletCharacter ℂ s₁} {ψ₂ : DirichletCharacter ℂ s₂}
    (h₁ : s₁ ∣ D) (h₂ : s₂ ∣ D) (heq : s₁ = s₂)
    (hlift : changeLevel h₁ ψ₁ = changeLevel h₂ ψ₂) :
    (⟨s₁, ψ₁⟩ : Σ s : ℕ, DirichletCharacter ℂ s) = ⟨s₂, ψ₂⟩ := by
  subst heq
  exact congrArg (Sigma.mk s₁) (changeLevel_injective h₁ hlift)

private theorem prim_injective {D : ℕ} [NeZero D] :
    Function.Injective (fun χ : DirichletCharacter ℂ D =>
      (⟨χ.conductor, χ.primitiveCharacter⟩ : Σ s : ℕ, DirichletCharacter ℂ s)) := by
  intro χ₁ χ₂ h
  rw [← χ₁.changeLevel_primitiveCharacter, ← χ₂.changeLevel_primitiveCharacter]
  exact changeLevel_eq_of_sigma_eq χ₁.conductor_dvd_level χ₂.conductor_dvd_level h

private theorem mem_prim_image {D : ℕ} [NeZero D] (b : Σ s : ℕ, DirichletCharacter ℂ s) :
    b ∈ Finset.univ.image (fun χ : DirichletCharacter ℂ D =>
      (⟨χ.conductor, χ.primitiveCharacter⟩ : Σ s : ℕ, DirichletCharacter ℂ s)) ↔
      b.1 ≠ 0 ∧ b.1 ∣ D ∧ b.2.IsPrimitive := by
  constructor
  · intro hb
    obtain ⟨χ, _, rfl⟩ := Finset.mem_image.mp hb
    exact ⟨ne_zero_of_dvd_ne_zero (NeZero.ne D) χ.conductor_dvd_level,
      χ.conductor_dvd_level, χ.primitiveCharacter_isPrimitive⟩
  · rintro ⟨hne, hdvd, hprim⟩
    rcases b with ⟨s, β⟩
    dsimp only at hne hdvd hprim
    let χ : DirichletCharacter ℂ D := changeLevel hdvd β
    refine Finset.mem_image.mpr ⟨χ, Finset.mem_univ _, ?_⟩
    have hcond : χ.conductor = s := by
      dsimp only [χ]
      rw [conductor_changeLevel, hprim]
    exact sigma_eq_of_changeLevel_eq χ.conductor_dvd_level hdvd hcond
      χ.changeLevel_primitiveCharacter

private theorem coord_bijective {D : ℕ} [NeZero D]
    {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ι → ℕ} [∀ i, NeZero (q i)]
    (e : ZMod D ≃+* ∀ i, ZMod (q i)) :
    Function.Bijective (fun χ : DirichletCharacter ℂ D => fun i => component e χ i) := by
  have hinj : Function.Injective (fun χ : DirichletCharacter ℂ D => fun i => component e χ i) := by
    intro χ₁ χ₂ h
    apply MulChar.ext
    intro u
    rw [reassemble e χ₁ (u : ZMod D), reassemble e χ₂ (u : ZMod D)]
    exact Finset.prod_congr rfl (fun i _ =>
      congrArg (fun ψ : DirichletCharacter ℂ (q i) => ψ (e u i)) (congrFun h i))
  refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨hinj, ?_⟩
  have hunit : (ZMod D)ˣ ≃* ∀ i, (ZMod (q i))ˣ :=
    (Units.mapEquiv e.toMulEquiv).trans MulEquiv.piUnits
  have htot : D.totient = ∏ i, (q i).totient := by
    have hc := Fintype.card_congr hunit.toEquiv
    rw [ZMod.card_units_eq_totient, Fintype.card_pi] at hc
    simpa only [ZMod.card_units_eq_totient] using hc
  rw [Fintype.card_pi, ← Nat.card_eq_fintype_card,
    DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ D, htot]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Nat.card_eq_fintype_card,
    DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ (q i)]

private theorem row_cubic_sum {D r : ℕ} [NeZero D] [NeZero r]
    {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ι → ℕ} [∀ i, NeZero (q i)]
    (e : ZMod D ≃+* ∀ i, ZMod (q i))
    (hr : r ∣ D) (α : DirichletCharacter ℂ r) (hα : α.IsPrimitive)
    (m : ℕ) (hm : 0 < m) (he : Even m) :
    let F : Finset (Σ s : ℕ, DirichletCharacter ℂ s) :=
      Finset.univ.image (fun χ : DirichletCharacter ℂ D => ⟨χ.conductor, χ.primitiveCharacter⟩)
    (∑ b ∈ F, ‖series α b.2 m‖ ^ 3) =
      ‖series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m‖ ^ 3 *
        ∏ i : ι, ∑ c : DirichletCharacter ℂ (q i),
          ‖J (component e (changeLevel hr α) i) c (m : ZMod (q i)) /
            J (1 : DirichletCharacter ℂ (q i)) 1 (m : ZMod (q i))‖ ^ 3 := by
  classical
  intro F
  let loc : DirichletCharacter ℂ D → ∀ i : ι, DirichletCharacter ℂ (q i) :=
    fun χ i => component e χ i
  have hloc : Function.Bijective loc := coord_bijective e
  let A (i : ι) : DirichletCharacter ℂ (q i) := component e (changeLevel hr α) i
  let W (i : ι) (c : DirichletCharacter ℂ (q i)) : ℝ :=
    ‖J (A i) c (m : ZMod (q i)) /
      J (1 : DirichletCharacter ℂ (q i)) 1 (m : ZMod (q i))‖ ^ 3
  have hterm (χ : DirichletCharacter ℂ D) :
      ‖series α χ.primitiveCharacter m‖ ^ 3 =
        ‖series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m‖ ^ 3 *
          ∏ i : ι, W i (loc χ i) := by
    haveI : NeZero χ.conductor :=
      ⟨ne_zero_of_dvd_ne_zero (NeZero.ne D) χ.conductor_dvd_level⟩
    have hfp := full_product e hα χ.primitiveCharacter_isPrimitive hr χ.conductor_dvd_level
      m hm he
    rw [χ.changeLevel_primitiveCharacter] at hfp
    rw [hfp, norm_mul, norm_prod, mul_pow, Finset.prod_pow]
  calc
    (∑ b ∈ F, ‖series α b.2 m‖ ^ 3)
        = ∑ χ : DirichletCharacter ℂ D, ‖series α χ.primitiveCharacter m‖ ^ 3 := by
          dsimp only [F]
          rw [Finset.sum_image (fun x _ y _ h => prim_injective h)]
    _ = ‖series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m‖ ^ 3 *
          ∑ χ : DirichletCharacter ℂ D, ∏ i : ι, W i (loc χ i) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun χ _ => hterm χ
    _ = ‖series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m‖ ^ 3 *
          ∑ f : (∀ i : ι, DirichletCharacter ℂ (q i)), ∏ i : ι, W i (f i) := by
          congr 1
          exact Fintype.sum_bijective loc hloc _ _ (fun _ => rfl)
    _ = ‖series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m‖ ^ 3 *
          ∏ i : ι, ∑ c : DirichletCharacter ℂ (q i), W i c := by
          rw [Fintype.prod_sum]

theorem main_theorem :
    ∀ D : ℕ, 0 < D → Odd D → Squarefree D →
      ∃ F : Finset (Σ s : ℕ, DirichletCharacter ℂ s),
        (∀ b, b ∈ F ↔ b.1 ≠ 0 ∧ b.1 ∣ D ∧ b.2.IsPrimitive) ∧
        (∑ b ∈ F, ‖series (1 : DirichletCharacter ℂ 1) b.2 2‖ ^ 3) =
          ‖series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) 2‖ ^ 3 *
            (∏ p ∈ D.primeFactors, (1 + 1 / ((p : ℝ) - 2) ^ 2)) ∧
        ∀ (r : ℕ) [NeZero r], r ∣ D → ∀ α : DirichletCharacter ℂ r, α.IsPrimitive →
          ∀ m : ℕ, 0 < m → Even m →
            (∑ b ∈ F, ‖series α b.2 m‖ ^ 3) ≤
              ‖series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m‖ ^ 3 *
                (∏ p ∈ D.primeFactors, (1 + 1 / ((p : ℝ) - 2) ^ 2)) := by
  classical
  intro D hDpos hDodd hDsq
  haveI : NeZero D := ⟨hDpos.ne'⟩
  let prim : DirichletCharacter ℂ D → Σ s : ℕ, DirichletCharacter ℂ s :=
    fun χ => ⟨χ.conductor, χ.primitiveCharacter⟩
  let F : Finset (Σ s : ℕ, DirichletCharacter ℂ s) := Finset.univ.image prim
  let I := ↥D.primeFactors
  haveI (i : I) : Fact (i : ℕ).Prime := ⟨(Nat.mem_primeFactors.mp i.property).1⟩
  haveI (i : I) : NeZero (i : ℕ) := ⟨(Nat.mem_primeFactors.mp i.property).1.ne_zero⟩
  have hfac (i : I) : (i : ℕ) ^ D.factorization i = (i : ℕ) := by
    rw [squarefree_factorization_eq_one hDsq i.property, pow_one]
  let e : ZMod D ≃+* ∀ i : I, ZMod (i : ℕ) :=
    (ZMod.equivPi D hDpos.ne').trans
      (RingEquiv.piCongrRight fun i => ZMod.ringEquivCongr (hfac i))
  have hp3 (i : I) : 3 ≤ (i : ℕ) := by
    have hp_mem := Nat.mem_primeFactors.mp i.property
    have hp_prime : (i : ℕ).Prime := hp_mem.1
    have hp_odd : Odd (i : ℕ) := hDodd.of_dvd_nat hp_mem.2.1
    have h2 := hp_prime.two_le
    have hne2 : (i : ℕ) ≠ 2 := by
      rintro heq
      rw [heq] at hp_odd
      exact (by decide : ¬ Odd 2) hp_odd
    omega
  refine ⟨F, fun b => mem_prim_image b, ?_, ?_⟩
  · have hrow := row_cubic_sum e (one_dvd D) (1 : DirichletCharacter ℂ 1)
      (show (1 : DirichletCharacter ℂ 1).IsPrimitive from DirichletCharacter.conductor_one)
      2 (by omega) (by decide : Even 2)
    rw [hrow]
    congr 1
    calc
      (∏ i : I, ∑ c : DirichletCharacter ℂ (i : ℕ),
          ‖J (component e (changeLevel (one_dvd D) (1 : DirichletCharacter ℂ 1)) i) c (2 : ZMod (i : ℕ)) /
            J (1 : DirichletCharacter ℂ (i : ℕ)) 1 (2 : ZMod (i : ℕ))‖ ^ 3)
          = ∏ i : I, (1 + 1 / (((i : ℕ) : ℝ) - 2) ^ 2) := by
            refine Finset.prod_congr rfl fun i _ => ?_
            rw [changeLevel_one, component_one]
            have hnot2 : ¬ (i : ℕ) ∣ 2 := by
              intro hd
              have := Nat.le_of_dvd (by omega) hd
              have := hp3 i
              omega
            exact prime_cubic_principal (hp3 i) 2 hnot2
      _ = ∏ p ∈ D.primeFactors, (1 + 1 / ((p : ℝ) - 2) ^ 2) :=
            Finset.prod_coe_sort D.primeFactors (fun p => 1 + 1 / ((p : ℝ) - 2) ^ 2)
  · intro r _ hr α hα m hm he
    have hrow := row_cubic_sum e hr α hα m hm he
    rw [hrow]
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg (norm_nonneg _) 3)
    calc
      (∏ i : I, ∑ c : DirichletCharacter ℂ (i : ℕ),
          ‖J (component e (changeLevel hr α) i) c (m : ZMod (i : ℕ)) /
            J (1 : DirichletCharacter ℂ (i : ℕ)) 1 (m : ZMod (i : ℕ))‖ ^ 3)
          ≤ ∏ i : I, (1 + 1 / (((i : ℕ) : ℝ) - 2) ^ 2) := by
            apply Finset.prod_le_prod₀
            · intro i _
              exact Finset.sum_nonneg fun _ _ => pow_nonneg (norm_nonneg _) 3
            · intro i _
              exact prime_cubic_bound (hp3 i) (component e (changeLevel hr α) i) m
      _ = ∏ p ∈ D.primeFactors, (1 + 1 / ((p : ℝ) - 2) ^ 2) :=
            Finset.prod_coe_sort D.primeFactors (fun p => 1 + 1 / ((p : ℝ) - 2) ^ 2)

end PartnerSharpCubicLevelProof

theorem Conjectures.Goldbach.PartnerSharpCubicLevel :
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
  exact ∀ D : ℕ, 0 < D → Odd D → Squarefree D → ∃ F : Finset (Σ s : ℕ, DirichletCharacter ℂ s), (∀ b, b ∈ F ↔ b.1 ≠ 0 ∧ b.1 ∣ D ∧ b.2.IsPrimitive) ∧ (∑ b ∈ F, ‖S (1 : DirichletCharacter ℂ 1) b.2 2‖ ^ 3) = ‖O 2‖ ^ 3 * (∏ p ∈ D.primeFactors, (1+1/((p:ℝ)-2)^2)) ∧ ∀ (r : ℕ) [NeZero r], r ∣ D → ∀ α : DirichletCharacter ℂ r, α.IsPrimitive → ∀ m : ℕ, 0 < m → Even m → (∑ b ∈ F, ‖S α b.2 m‖ ^ 3) ≤ ‖O m‖ ^ 3 * (∏ p ∈ D.primeFactors, (1+1/((p:ℝ)-2)^2)) := by
  classical
  dsimp only
  exact PartnerSharpCubicLevelProof.main_theorem
