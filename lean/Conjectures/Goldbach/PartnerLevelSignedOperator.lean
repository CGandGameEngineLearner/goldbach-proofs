import Mathlib
import Conjectures.Goldbach.SharpSingularSeriesRatios

/-!
# Exact ℓ² Operator Norm of the Signed Full-Level Twisted Singular-Series Matrix
(`L-goldbach-partner-level-signed-operator`)

For any positive level `D` and positive even target `m`, let `F` be the finite set of
primitive Dirichlet characters `(s, β)` (`s ≠ 0`, `s ∣ D`, `β.IsPrimitive`). We determine
the exact `ℓ²` operator norm of `(applyRow w)(a) = ∑ b ∈ F, S a.2 b.2 m * w b`, namely
`scale = ‖O m‖ * φ(D) / H`, where `O = S 1 1` is the ordinary singular series and
`H = #{0 ≤ x < D : gcd(x, D) = gcd(m - x, D) = 1}`, and construct an explicit nonzero
attainment vector.

## Proof outline and sources
1. Biject `DirichletCharacter ℂ D` onto `F` via `B ↦ ⟨B.conductor, B.primitiveCharacter⟩`
   (following `@Qmhou` PR #4164 and `@SaladDay` PR #4316).
2. By `TwistedGoldbachConductorRatio.conductor_identity` at level `D`,
   `S A.primitiveCharacter B.primitiveCharacter m = (O m / H) * J A B (m : ZMod D)` where
   `H = J 1 1 (m : ZMod D) > 0` (`principal_ne_zero` for `Even m`).
3. Transform `u B = w (g B)` on `(ZMod D)ˣ` via `uHat y = ∑ B, B y * u B`. Using character
   orthogonality (`DirichletCharacter.sum_char_inv_mul_char_eq`) and residue orthogonality
   (`MulChar.sum_eq_zero_of_ne_one`, `MulChar.sum_one_eq_card_units`), the kernel `J A B m`
   acts on `uHat` as the partial reflection `y ↦ m - y` restricted to admissible units,
   giving `∑ A, ‖∑ B, J A B m * u B‖² = φ(D) * ∑_{x ∈ Adm(m)} ‖uHat(m - x)‖² ≤ φ(D)² * ∑ B, ‖u B‖²`.
4. Choosing one admissible unit `x₀ ∈ Adm(m)` (`admissible_even`) and setting
   `u₀ B = conj (B (m - x₀))` concentrates `uHat` on `m - x₀`, yielding `0 < ∑ B, ‖u₀ B‖² = φ(D)`
   and exact equality `normSq (applyRow w₀) = scale² * normSq w₀`.

## Attribution
* Builds on `Conjectures.Goldbach.PrimitivePartnerCubicMass` and
  `Conjectures.Goldbach.SharpSingularSeriesRatios` in `CGandGameEngineLearner/goldbach-proofs`
  (Apache-2.0; citing `@zxg0623` PR #4023, `@Qmhou` PR #4164, `@JiangZhexin` PR #4206, and
  `@SaladDay` PR #4316).
-/

namespace Conjectures.Goldbach.PartnerLevelSignedOperatorAux

open Finset DirichletCharacter MulChar
open Conjectures.Goldbach.SharpSingularSeriesRatiosProof
open TwistedGoldbachConductorRatio TwistedGoldbachLocalProduct
open scoped ComplexConjugate BigOperators Classical

private theorem admissible_card_eq {D : ℕ} [NeZero D] (m : ℕ) :
    ((Finset.range D).filter (fun x => x.Coprime D ∧ (m + D - (x % D)).Coprime D)).card =
      ((Finset.univ : Finset (ZMod D)).filter (admissible (m : ZMod D))).card := by
  apply Finset.card_bij (fun (x : ℕ) _ => (x : ZMod D))
  · intro x hx
    obtain ⟨hxr, hc1, hc2⟩ := mem_filter.mp hx
    have hlt : x < D := mem_range.mp hxr
    have hmod : x % D = x := Nat.mod_eq_of_lt hlt
    rw [hmod] at hc2
    have hcast : ((m + D - x : ℕ) : ZMod D) = (m : ZMod D) - (x : ZMod D) := by
      rw [Nat.cast_sub (by omega : x ≤ m + D), Nat.cast_add, ZMod.natCast_self, add_zero]
    refine mem_filter.mpr ⟨mem_univ _, ⟨(ZMod.isUnit_iff_coprime x D).mpr hc1, ?_⟩⟩
    rw [← hcast]
    exact (ZMod.isUnit_iff_coprime (m + D - x) D).mpr hc2
  · intro x₁ hx₁ x₂ hx₂ h
    have h1 : x₁ < D := mem_range.mp (mem_filter.mp hx₁).1
    have h2 : x₂ < D := mem_range.mp (mem_filter.mp hx₂).1
    have hv := congrArg ZMod.val h
    rwa [ZMod.val_natCast_of_lt h1, ZMod.val_natCast_of_lt h2] at hv
  · intro z hz
    obtain ⟨_, hu1, hu2⟩ := mem_filter.mp hz
    refine ⟨z.val, mem_filter.mpr ⟨mem_range.mpr (ZMod.val_lt z), ?_, ?_⟩, ZMod.natCast_zmod_val z⟩
    · exact (ZMod.isUnit_iff_coprime z.val D).mp (by simpa [ZMod.natCast_zmod_val] using hu1)
    · rw [Nat.mod_eq_of_lt (ZMod.val_lt z)]
      have hlt : z.val < D := ZMod.val_lt z
      have hcast : ((m + D - z.val : ℕ) : ZMod D) = (m : ZMod D) - z := by
        rw [Nat.cast_sub (by omega : z.val ≤ m + D), Nat.cast_add, ZMod.natCast_self,
          add_zero, ZMod.natCast_zmod_val]
      exact (ZMod.isUnit_iff_coprime (m + D - z.val) D).mp (hcast.symm ▸ hu2)

private theorem conj_char_apply {D : ℕ} (B : DirichletCharacter ℂ D) (z : ZMod D) :
    conj (B z) = B⁻¹ z := by
  change star (B z) = B⁻¹ z
  exact MulChar.star_apply' B z

private theorem conj_at_unit {D : ℕ} (χ : DirichletCharacter ℂ D) {x : ZMod D} (hx : IsUnit x) :
    conj (χ x) = χ x⁻¹ := by
  obtain ⟨u, rfl⟩ := hx
  rw [ZMod.inv_coe_unit]
  change star (χ (u : ZMod D)) = _
  rw [MulChar.star_apply', MulChar.inv_apply, Ring.inverse_unit]

private theorem sum_conj_mul_zmod {D : ℕ} [NeZero D] (B C : DirichletCharacter ℂ D) :
    (∑ z : ZMod D, conj (B z) * C z) = if B = C then (D.totient : ℂ) else 0 := by
  have hstep : ∀ z : ZMod D, conj (B z) * C z = (B⁻¹ * C) z := by
    intro z
    rw [conj_char_apply, MulChar.mul_apply]
  simp_rw [hstep]
  by_cases hBC : B = C
  · subst hBC
    rw [if_pos rfl, inv_mul_cancel, MulChar.sum_one_eq_card_units, ZMod.card_units_eq_totient]
  · rw [if_neg hBC]
    have hne : B⁻¹ * C ≠ 1 := fun h => hBC (inv_mul_eq_one.mp h)
    exact MulChar.sum_eq_zero_of_ne_one hne

private theorem uHat_plancherel {D : ℕ} [NeZero D] (u : DirichletCharacter ℂ D → ℂ) :
    (∑ y : ZMod D, ‖∑ B : DirichletCharacter ℂ D, B y * u B‖ ^ 2) =
      (D.totient : ℝ) * ∑ B : DirichletCharacter ℂ D, ‖u B‖ ^ 2 := by
  let uHat (y : ZMod D) : ℂ := ∑ B : DirichletCharacter ℂ D, B y * u B
  change (∑ y : ZMod D, ‖uHat y‖ ^ 2) = _
  apply Complex.ofReal_injective
  push_cast
  calc
    (∑ y : ZMod D, (‖uHat y‖ : ℂ) ^ 2)
        = ∑ y : ZMod D, conj (uHat y) * uHat y := by
          apply sum_congr rfl; intro y _; exact (Complex.conj_mul' (uHat y)).symm
    _ = ∑ y : ZMod D, (∑ B, conj (B y) * conj (u B)) * (∑ C, C y * u C) := by
          apply sum_congr rfl; intro y _; simp [uHat, map_sum, map_mul]
    _ = ∑ B, ∑ C, (conj (u B) * u C) * (∑ y : ZMod D, conj (B y) * C y) := by
          simp_rw [sum_mul, mul_sum]
          rw [sum_comm]
          apply sum_congr rfl; intro B _
          rw [sum_comm]
          apply sum_congr rfl; intro C _
          apply sum_congr rfl; intro y _; ring
    _ = ∑ B, ∑ C, (conj (u B) * u C) * (if B = C then (D.totient : ℂ) else 0) := by
          apply sum_congr rfl; intro B _; apply sum_congr rfl; intro C _
          rw [sum_conj_mul_zmod]
    _ = ∑ B : DirichletCharacter ℂ D, (conj (u B) * u B) * (D.totient : ℂ) := by
          apply sum_congr rfl; intro B _; simp
    _ = (D.totient : ℂ) * ∑ B : DirichletCharacter ℂ D, (‖u B‖ : ℂ) ^ 2 := by
          rw [mul_sum]
          apply sum_congr rfl; intro B _
          rw [Complex.conj_mul']; ring

private theorem kernel_apply {D : ℕ} [NeZero D] (u : DirichletCharacter ℂ D → ℂ)
    (m : ZMod D) (A : DirichletCharacter ℂ D) :
    (∑ B : DirichletCharacter ℂ D, J A B m * u B) =
      ∑ x ∈ (univ : Finset (ZMod D)).filter (admissible m),
        A x * (∑ B : DirichletCharacter ℂ D, B (m - x) * u B) := by
  have hJ : ∀ B : DirichletCharacter ℂ D,
      J A B m = ∑ x ∈ (univ : Finset (ZMod D)).filter (admissible m), A x * B (m - x) := by
    intro B
    symm
    apply sum_subset (filter_subset ..)
    intro x _ hno
    by_cases hx : IsUnit x
    · have hy : ¬ IsUnit (m - x) := fun hy => hno (mem_filter.mpr ⟨mem_univ _, hx, hy⟩)
      simp [B.map_nonunit hy]
    · simp [A.map_nonunit hx]
  simp_rw [hJ, sum_mul]
  rw [sum_comm]
  apply sum_congr rfl; intro x _
  rw [mul_sum]
  apply sum_congr rfl; intro B _; ring

private theorem dual_ortho_energy {D : ℕ} [NeZero D] (Adm : Finset (ZMod D))
    (hAdm : ∀ x ∈ Adm, IsUnit x) (v : ZMod D → ℂ) :
    (∑ A : DirichletCharacter ℂ D, ‖∑ x ∈ Adm, A x * v x‖ ^ 2) =
      (D.totient : ℝ) * ∑ x ∈ Adm, ‖v x‖ ^ 2 := by
  apply Complex.ofReal_injective
  push_cast
  have ortho : ∀ x ∈ Adm, ∀ y ∈ Adm,
      (∑ A : DirichletCharacter ℂ D, conj (A x) * A y) =
        if x = y then (D.totient : ℂ) else 0 := by
    intro x hx y _
    have hux : IsUnit x := hAdm x hx
    simp_rw [conj_at_unit _ hux]
    exact DirichletCharacter.sum_char_inv_mul_char_eq ℂ hux y
  calc
    (∑ A : DirichletCharacter ℂ D, (‖∑ x ∈ Adm, A x * v x‖ : ℂ) ^ 2)
        = ∑ A : DirichletCharacter ℂ D,
            (∑ x ∈ Adm, conj (A x) * conj (v x)) * (∑ y ∈ Adm, A y * v y) := by
          apply sum_congr rfl; intro A _
          rw [← Complex.conj_mul', map_sum]
          simp only [map_mul]
    _ = ∑ x ∈ Adm, ∑ y ∈ Adm,
          (conj (v x) * v y) * (∑ A : DirichletCharacter ℂ D, conj (A x) * A y) := by
          simp_rw [sum_mul, mul_sum]
          rw [sum_comm]
          apply sum_congr rfl; intro x _
          rw [sum_comm]
          apply sum_congr rfl; intro y _
          apply sum_congr rfl; intro A _; ring
    _ = ∑ x ∈ Adm, ∑ y ∈ Adm,
          (conj (v x) * v y) * (if x = y then (D.totient : ℂ) else 0) := by
          apply sum_congr rfl; intro x hx; apply sum_congr rfl; intro y hy
          rw [ortho x hx y hy]
    _ = ∑ x ∈ Adm, (conj (v x) * v x) * (D.totient : ℂ) := by
          apply sum_congr rfl; intro x hx
          rw [sum_eq_single x]
          · simp
          · intro y _ hyx; simp [Ne.symm hyx]
          · intro hnot; exact absurd hx hnot
    _ = (D.totient : ℂ) * ∑ x ∈ Adm, (‖v x‖ : ℂ) ^ 2 := by
          rw [mul_sum]
          apply sum_congr rfl; intro x _
          rw [Complex.conj_mul']; ring

private theorem kernel_energy {D : ℕ} [NeZero D] (u : DirichletCharacter ℂ D → ℂ) (m : ZMod D) :
    (∑ A : DirichletCharacter ℂ D, ‖∑ B : DirichletCharacter ℂ D, J A B m * u B‖ ^ 2) =
      (D.totient : ℝ) * ∑ x ∈ (univ : Finset (ZMod D)).filter (admissible m),
        ‖∑ B : DirichletCharacter ℂ D, B (m - x) * u B‖ ^ 2 := by
  simp_rw [kernel_apply u m]
  exact dual_ortho_energy ((univ : Finset (ZMod D)).filter (admissible m))
    (fun x hx => (mem_filter.mp hx).2.1)
    (fun x => ∑ B : DirichletCharacter ℂ D, B (m - x) * u B)

private theorem kernel_le {D : ℕ} [NeZero D] (u : DirichletCharacter ℂ D → ℂ) (m : ZMod D) :
    (∑ A : DirichletCharacter ℂ D, ‖∑ B : DirichletCharacter ℂ D, J A B m * u B‖ ^ 2) ≤
      (D.totient : ℝ) ^ 2 * ∑ B : DirichletCharacter ℂ D, ‖u B‖ ^ 2 := by
  rw [kernel_energy]
  let uHat (y : ZMod D) : ℂ := ∑ B : DirichletCharacter ℂ D, B y * u B
  have hsub : (∑ x ∈ (univ : Finset (ZMod D)).filter (admissible m), ‖uHat (m - x)‖ ^ 2) ≤
      ∑ x : ZMod D, ‖uHat (m - x)‖ ^ 2 :=
    sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => sq_nonneg _)
  have hshift : (∑ x : ZMod D, ‖uHat (m - x)‖ ^ 2) = ∑ y : ZMod D, ‖uHat y‖ ^ 2 :=
    Equiv.sum_comp (Equiv.subLeft m) (fun y => ‖uHat y‖ ^ 2)
  have hplan : (∑ y : ZMod D, ‖uHat y‖ ^ 2) =
      (D.totient : ℝ) * ∑ B : DirichletCharacter ℂ D, ‖u B‖ ^ 2 :=
    uHat_plancherel u
  calc
    (D.totient : ℝ) * ∑ x ∈ (univ : Finset (ZMod D)).filter (admissible m), ‖uHat (m - x)‖ ^ 2
        ≤ (D.totient : ℝ) * ((D.totient : ℝ) * ∑ B : DirichletCharacter ℂ D, ‖u B‖ ^ 2) := by
          apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
          calc _ ≤ ∑ x : ZMod D, ‖uHat (m - x)‖ ^ 2 := hsub
            _ = ∑ y : ZMod D, ‖uHat y‖ ^ 2 := hshift
            _ = _ := hplan
    _ = (D.totient : ℝ) ^ 2 * ∑ B : DirichletCharacter ℂ D, ‖u B‖ ^ 2 := by ring

private theorem core {s t L : ℕ} [NeZero L] (a : DirichletCharacter ℂ s) (b : DirichletCharacter ℂ t)
    (hs : s ∣ L) (ht : t ∣ L) (ha : a.IsPrimitive) (hb : b.IsPrimitive)
    (h : changeLevel hs a = changeLevel ht b) :
    (⟨s, a⟩ : Σ n : ℕ, DirichletCharacter ℂ n) = ⟨t, b⟩ := by
  have eqst := congrArg DirichletCharacter.conductor h
  rw [conductor_changeLevel, conductor_changeLevel, ha, hb] at eqst
  subst t
  exact congrArg (Sigma.mk s) (changeLevel_injective hs h)

private theorem lift_congr {s t L : ℕ} (hs : s ∣ L) (ht : t ∣ L)
    (a : DirichletCharacter ℂ s) (b : DirichletCharacter ℂ t)
    (h : (⟨s, a⟩ : Σ n : ℕ, DirichletCharacter ℂ n) = ⟨t, b⟩) :
    changeLevel hs a = changeLevel ht b := by
  cases h
  rfl

theorem main (D m : ℕ) (hD : 0 < D) (hm : 0 < m) (he : Even m) :
    let O := series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1)
    let B := Σ s : ℕ, DirichletCharacter ℂ s
    let valid := fun b : B => b.1 ≠ 0 ∧ b.2.IsPrimitive
    ∃ F : Finset B, (∀ b, b ∈ F ↔ valid b ∧ b.1 ∣ D) ∧
      (let H := ((Finset.range D).filter (fun x => x.Coprime D ∧ (m + D - (x % D)).Coprime D)).card
       let scale := ‖O m‖ * (D.totient : ℝ) / (H : ℝ)
       let normSq := fun w : B → ℂ => ∑ a ∈ F, ‖w a‖ ^ 2
       let applyRow := fun (w : B → ℂ) (a : B) => ∑ b ∈ F, series a.2 b.2 m * w b
       (∀ w : B → ℂ, normSq (applyRow w) ≤ scale ^ 2 * normSq w) ∧
       ∃ w : B → ℂ, 0 < normSq w ∧ normSq (applyRow w) = scale ^ 2 * normSq w) := by
  dsimp only
  let _ : NeZero D := ⟨hD.ne'⟩
  let g : DirichletCharacter ℂ D → Σ s : ℕ, DirichletCharacter ℂ s :=
    fun B => ⟨B.conductor, B.primitiveCharacter⟩
  have ginj : Function.Injective g := by
    intro B C hBC
    have h1 := lift_congr B.conductor_dvd_level C.conductor_dvd_level
      B.primitiveCharacter C.primitiveCharacter hBC
    rwa [changeLevel_primitiveCharacter, changeLevel_primitiveCharacter] at h1
  let F := univ.image g
  refine ⟨F, ?_, ?_⟩
  · intro b
    simp only [F, mem_image, mem_univ, true_and]
    constructor
    · rintro ⟨B, rfl⟩
      exact ⟨⟨B.conductor_ne_zero, B.primitiveCharacter_isPrimitive⟩, B.conductor_dvd_level⟩
    · rintro ⟨⟨hb0, hbprim⟩, hbd⟩
      obtain ⟨s, β⟩ := b
      let _ : NeZero s := ⟨hb0⟩
      refine ⟨changeLevel hbd β, ?_⟩
      dsimp only [g]
      exact core _ _ _ _ (primitiveCharacter_isPrimitive _) hbprim (changeLevel_primitiveCharacter _)
  · let H := ((Finset.range D).filter (fun x => x.Coprime D ∧ (m + D - (x % D)).Coprime D)).card
    let O := series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1)
    let scale := ‖O m‖ * (D.totient : ℝ) / (H : ℝ)
    let normSq := fun w : (Σ s : ℕ, DirichletCharacter ℂ s) → ℂ => ∑ a ∈ F, ‖w a‖ ^ 2
    let applyRow := fun (w : (Σ s : ℕ, DirichletCharacter ℂ s) → ℂ)
        (a : Σ s : ℕ, DirichletCharacter ℂ s) => ∑ b ∈ F, series a.2 b.2 m * w b
    change (∀ w, normSq (applyRow w) ≤ scale ^ 2 * normSq w) ∧
      ∃ w, 0 < normSq w ∧ normSq (applyRow w) = scale ^ 2 * normSq w
    have hH_adm : H = ((univ : Finset (ZMod D)).filter (admissible (m : ZMod D))).card :=
      admissible_card_eq m
    have hJ0 : J (1 : DirichletCharacter ℂ D) 1 (m : ZMod D) = (H : ℂ) := by
      rw [principal_card, hH_adm]
    have hJ0_ne : J (1 : DirichletCharacter ℂ D) 1 (m : ZMod D) ≠ 0 :=
      principal_ne_zero D m he
    have hHC_ne : (H : ℂ) ≠ 0 := hJ0 ▸ hJ0_ne
    have hHR_ne : (H : ℝ) ≠ 0 := by
      intro h0
      apply hHC_ne
      exact_mod_cast h0
    have hS : ∀ A B : DirichletCharacter ℂ D,
        series A.primitiveCharacter B.primitiveCharacter m =
          (O m / (H : ℂ)) * J A B (m : ZMod D) := by
      intro A B
      let _ : NeZero A.conductor := ⟨A.conductor_ne_zero⟩
      let _ : NeZero B.conductor := ⟨B.conductor_ne_zero⟩
      have hcid := conductor_identity A.primitiveCharacter_isPrimitive
        B.primitiveCharacter_isPrimitive A.conductor_dvd_level B.conductor_dvd_level m hm
      rw [changeLevel_primitiveCharacter, changeLevel_primitiveCharacter, hJ0] at hcid
      rw [div_mul_eq_mul_div, eq_div_iff hHC_ne]
      exact hcid
    have hnormSq : ∀ w : (Σ s : ℕ, DirichletCharacter ℂ s) → ℂ,
        normSq w = ∑ B : DirichletCharacter ℂ D, ‖w (g B)‖ ^ 2 := by
      intro w
      dsimp only [normSq, F]
      exact sum_image (fun x _ y _ h => ginj h)
    have happlySq : ∀ w : (Σ s : ℕ, DirichletCharacter ℂ s) → ℂ,
        normSq (applyRow w) =
          (‖O m‖ / (H : ℝ)) ^ 2 *
            ∑ A : DirichletCharacter ℂ D,
              ‖∑ B : DirichletCharacter ℂ D, J A B (m : ZMod D) * w (g B)‖ ^ 2 := by
      intro w
      rw [hnormSq (applyRow w)]
      have hrow : ∀ A : DirichletCharacter ℂ D,
          applyRow w (g A) =
            (O m / (H : ℂ)) * ∑ B : DirichletCharacter ℂ D, J A B (m : ZMod D) * w (g B) := by
        intro A
        dsimp only [applyRow, F]
        rw [sum_image (fun x _ y _ h => ginj h)]
        dsimp only [g]
        simp_rw [hS A _, mul_assoc, ← mul_sum]
      simp_rw [hrow, norm_mul, norm_div, Complex.norm_natCast, mul_pow, ← mul_sum]
    constructor
    · intro w
      rw [happlySq w, hnormSq w]
      calc
        (‖O m‖ / (H : ℝ)) ^ 2 *
            ∑ A : DirichletCharacter ℂ D,
              ‖∑ B : DirichletCharacter ℂ D, J A B (m : ZMod D) * w (g B)‖ ^ 2
            ≤ (‖O m‖ / (H : ℝ)) ^ 2 *
                ((D.totient : ℝ) ^ 2 * ∑ B : DirichletCharacter ℂ D, ‖w (g B)‖ ^ 2) :=
              mul_le_mul_of_nonneg_left (kernel_le (fun B => w (g B)) (m : ZMod D)) (sq_nonneg _)
        _ = scale ^ 2 * ∑ B : DirichletCharacter ℂ D, ‖w (g B)‖ ^ 2 := by
              dsimp only [scale]; ring
    · obtain ⟨x₀, hx₀⟩ := admissible_even D m he
      let u₀ (B : DirichletCharacter ℂ D) : ℂ := conj (B ((m : ZMod D) - x₀))
      let w₀ : (Σ s : ℕ, DirichletCharacter ℂ s) → ℂ := fun b =>
        if h : ∃ B : DirichletCharacter ℂ D, g B = b then u₀ (Classical.choose h) else 0
      have hw₀ : ∀ B : DirichletCharacter ℂ D, w₀ (g B) = u₀ B := by
        intro B
        have hex : ∃ C : DirichletCharacter ℂ D, g C = g B := ⟨B, rfl⟩
        dsimp only [w₀]
        rw [dif_pos hex, ginj (Classical.choose_spec hex)]
      have hcardD : Fintype.card (DirichletCharacter ℂ D) = D.totient := by
        rw [← Nat.card_eq_fintype_card,
          DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity]
      have hu₀_norm : ∀ B : DirichletCharacter ℂ D, ‖u₀ B‖ = 1 := by
        intro B
        dsimp only [u₀]
        rw [Complex.norm_conj]
        exact B.unit_norm_eq_one hx₀.2.unit
      have hnorm_w₀ : normSq w₀ = (D.totient : ℝ) := by
        rw [hnormSq w₀]
        simp_rw [hw₀, hu₀_norm, one_pow, sum_const, card_univ, hcardD, nsmul_eq_mul, mul_one]
      refine ⟨w₀, ?_, ?_⟩
      · rw [hnorm_w₀]
        exact_mod_cast Nat.totient_pos.mpr hD
      · rw [happlySq w₀, hnorm_w₀]
        simp_rw [hw₀]
        rw [kernel_energy u₀ (m : ZMod D)]
        let Adm := (univ : Finset (ZMod D)).filter (admissible (m : ZMod D))
        have hx₀_mem : x₀ ∈ Adm := mem_filter.mpr ⟨mem_univ _, hx₀⟩
        have hpeak : ∀ x : ZMod D,
            (∑ B : DirichletCharacter ℂ D, B ((m : ZMod D) - x) * u₀ B) =
              if x = x₀ then (D.totient : ℂ) else 0 := by
          intro x
          have hterm : ∀ B : DirichletCharacter ℂ D,
              B ((m : ZMod D) - x) * u₀ B =
                B ((m : ZMod D) - x₀)⁻¹ * B ((m : ZMod D) - x) := by
            intro B
            dsimp only [u₀]
            rw [conj_at_unit B hx₀.2, mul_comm]
          simp_rw [hterm]
          rw [DirichletCharacter.sum_char_inv_mul_char_eq ℂ hx₀.2 ((m : ZMod D) - x)]
          have hinj : ((m : ZMod D) - x₀ = (m : ZMod D) - x) ↔ x = x₀ := by
            rw [sub_right_inj, eq_comm]
          simp only [hinj]
        have hsum_adm : (∑ x ∈ Adm,
            ‖∑ B : DirichletCharacter ℂ D, B ((m : ZMod D) - x) * u₀ B‖ ^ 2) =
              (D.totient : ℝ) ^ 2 := by
          simp_rw [hpeak]
          rw [sum_eq_single x₀]
          · simp [Complex.norm_natCast]
          · intro x _ hne; simp [hne]
          · intro hnot; exact absurd hx₀_mem hnot
        change (‖O m‖ / (H : ℝ)) ^ 2 *
            ((D.totient : ℝ) * ∑ x ∈ Adm,
              ‖∑ B : DirichletCharacter ℂ D, B ((m : ZMod D) - x) * u₀ B‖ ^ 2) =
          scale ^ 2 * (D.totient : ℝ)
        rw [hsum_adm]
        dsimp only [scale]
        ring

end Conjectures.Goldbach.PartnerLevelSignedOperatorAux

theorem Conjectures.Goldbach.PartnerLevelSignedOperator :
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
  exact ∀ D m : ℕ, 0 < D → 0 < m → Even m → ∃ F : Finset B, (∀ b, b ∈ F ↔ valid b ∧ b.1 ∣ D) ∧ (let H := ((Finset.range D).filter (fun x => x.Coprime D ∧ (m+D-(x%D)).Coprime D)).card; let scale := ‖O m‖*(D.totient:ℝ)/(H:ℝ); let normSq := fun w : B → ℂ => ∑ a ∈ F, ‖w a‖^2; let applyRow := fun (w : B → ℂ) (a : B) => ∑ b ∈ F, S a.2 b.2 m * w b; (∀ w : B → ℂ, normSq (applyRow w) ≤ scale^2 * normSq w) ∧ ∃ w : B → ℂ, 0 < normSq w ∧ normSq (applyRow w) = scale^2 * normSq w)
:= by
  classical
  dsimp only
  intro D m hD hm he
  exact Conjectures.Goldbach.PartnerLevelSignedOperatorAux.main D m hD hm he
