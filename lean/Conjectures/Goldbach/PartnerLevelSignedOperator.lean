import Mathlib
import Conjectures.Goldbach.SharpSingularSeriesRatios

/-! Exact ℓ² operator norm of the signed full-level singular-series matrix at level D,
together with an explicit maximizing vector.

Reuses `TwistedGoldbachConductorRatio.conductor_identity`, `principal_card`,
`admissible_even`, and `principal_ne_zero` from
`Conjectures.Goldbach.SharpSingularSeriesRatios` (PR #4023). -/

namespace PartnerLevelSignedOperatorProof

open Finset DirichletCharacter
open Conjectures.Goldbach.SharpSingularSeriesRatiosProof
open TwistedGoldbachConductorRatio TwistedGoldbachLocalProduct
open scoped ComplexConjugate BigOperators Classical

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
      (b.1 ≠ 0 ∧ b.2.IsPrimitive) ∧ b.1 ∣ D := by
  constructor
  · intro hb
    obtain ⟨χ, _, rfl⟩ := Finset.mem_image.mp hb
    exact ⟨⟨ne_zero_of_dvd_ne_zero (NeZero.ne D) χ.conductor_dvd_level,
      χ.primitiveCharacter_isPrimitive⟩, χ.conductor_dvd_level⟩
  · rintro ⟨⟨hne, hprim⟩, hdvd⟩
    rcases b with ⟨s, β⟩
    dsimp only at hne hdvd hprim
    let χ : DirichletCharacter ℂ D := changeLevel hdvd β
    refine Finset.mem_image.mpr ⟨χ, Finset.mem_univ _, ?_⟩
    have hcond : χ.conductor = s := by
      dsimp only [χ]
      rw [conductor_changeLevel, hprim]
    exact sigma_eq_of_changeLevel_eq χ.conductor_dvd_level hdvd hcond
      χ.changeLevel_primitiveCharacter

private theorem conj_at_unit {q : ℕ} (χ : DirichletCharacter ℂ q) {x : ZMod q} (hx : IsUnit x) :
    conj (χ x) = χ x⁻¹ := by
  obtain ⟨u, rfl⟩ := hx
  rw [ZMod.inv_coe_unit]
  change star (χ (u : ZMod q)) = _
  rw [MulChar.star_apply', MulChar.inv_apply, Ring.inverse_unit]

private theorem H_eq_admissible_card (D m : ℕ) [NeZero D] :
    ((Finset.range D).filter (fun x => x.Coprime D ∧ (m + D - x % D).Coprime D)).card =
      (Finset.univ.filter (admissible (m : ZMod D))).card := by
  classical
  refine Finset.card_bij (fun x _ => (x : ZMod D)) ?_ ?_ ?_
  · intro x hx
    obtain ⟨hxlt, hcop1, hcop2⟩ := Finset.mem_filter.mp hx
    have hlt : x < D := Finset.mem_range.mp hxlt
    have hmod : x % D = x := Nat.mod_eq_of_lt hlt
    rw [hmod] at hcop2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
    · exact (ZMod.isUnit_iff_coprime x D).mpr hcop1
    · have hcast : ((m + D - x : ℕ) : ZMod D) = (m : ZMod D) - (x : ZMod D) := by
        rw [Nat.cast_sub (by omega : x ≤ m + D), Nat.cast_add, ZMod.natCast_self, add_zero]
      rw [← hcast]
      exact (ZMod.isUnit_iff_coprime (m + D - x) D).mpr hcop2
  · intro x₁ hx₁ x₂ hx₂ heq
    have h1 : x₁ < D := Finset.mem_range.mp (Finset.mem_filter.mp hx₁).1
    have h2 : x₂ < D := Finset.mem_range.mp (Finset.mem_filter.mp hx₂).1
    have hv := congrArg ZMod.val heq
    rwa [ZMod.val_natCast_of_lt h1, ZMod.val_natCast_of_lt h2] at hv
  · intro z hz
    obtain ⟨_, hu1, hu2⟩ := Finset.mem_filter.mp hz
    refine ⟨z.val, ?_, ZMod.natCast_zmod_val z⟩
    have hlt : z.val < D := ZMod.val_lt z
    have hmod : z.val % D = z.val := Nat.mod_eq_of_lt hlt
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlt, ?_, ?_⟩
    · rw [← ZMod.isUnit_iff_coprime, ZMod.natCast_zmod_val]
      exact hu1
    · rw [hmod, ← ZMod.isUnit_iff_coprime]
      have hcast : ((m + D - z.val : ℕ) : ZMod D) = (m : ZMod D) - z := by
        rw [Nat.cast_sub (by omega : z.val ≤ m + D), Nat.cast_add, ZMod.natCast_self,
          add_zero, ZMod.natCast_zmod_val]
      rw [hcast]
      exact hu2

private theorem sum_char_normSq {D : ℕ} [NeZero D] (g : ZMod D → ℂ) :
    (∑ A : DirichletCharacter ℂ D, ‖∑ x : ZMod D, A x * g x‖ ^ 2) =
      (D.totient : ℝ) * ∑ x ∈ Finset.univ.filter (fun x : ZMod D => IsUnit x), ‖g x‖ ^ 2 := by
  classical
  let U := Finset.univ.filter (fun x : ZMod D => IsUnit x)
  have hrestr (A : DirichletCharacter ℂ D) :
      (∑ x : ZMod D, A x * g x) = ∑ x ∈ U, A x * g x := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro x _ hx
    have hnu : ¬ IsUnit x := by simpa [U] using hx
    rw [MulChar.map_nonunit A hnu, zero_mul]
  have hortho (x y : ZMod D) (hx : x ∈ U) :
      (∑ A : DirichletCharacter ℂ D, conj (A x * g x) * (A y * g y)) =
        if x = y then (D.totient : ℂ) * (‖g x‖ ^ 2 : ℝ) else 0 := by
    have hu : IsUnit x := (Finset.mem_filter.mp hx).2
    have hfact :
        (∑ A : DirichletCharacter ℂ D, conj (A x * g x) * (A y * g y)) =
          (conj (g x) * g y) * (∑ A : DirichletCharacter ℂ D, A x⁻¹ * A y) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro A _
      rw [map_mul, conj_at_unit A hu]
      ring
    rw [hfact, DirichletCharacter.sum_char_inv_mul_char_eq ℂ hu y]
    by_cases hxy : x = y
    · subst hxy
      rw [ite_eq_left rfl, ite_eq_left rfl, Complex.conj_mul']
      push_cast
      ring
    · simp [hxy]
  apply Complex.ofReal_injective
  push_cast
  calc
    (∑ A : DirichletCharacter ℂ D, ((‖∑ x : ZMod D, A x * g x‖ : ℂ) ^ 2))
        = ∑ A : DirichletCharacter ℂ D,
            (∑ x ∈ U, conj (A x * g x)) * (∑ y ∈ U, A y * g y) := by
          apply Finset.sum_congr rfl
          intro A _
          rw [← Complex.conj_mul', hrestr A, map_sum]
    _ = ∑ x ∈ U, ∑ y ∈ U, ∑ A : DirichletCharacter ℂ D, conj (A x * g x) * (A y * g y) := by
          simp_rw [Finset.sum_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro x _
          rw [Finset.sum_comm]
    _ = ∑ x ∈ U, ∑ y ∈ U, if x = y then (D.totient : ℂ) * ((‖g x‖ : ℂ) ^ 2) else 0 := by
          apply Finset.sum_congr rfl
          intro x hx
          apply Finset.sum_congr rfl
          intro y _
          simpa using hortho x y hx
    _ = ∑ x ∈ U, (D.totient : ℂ) * ((‖g x‖ : ℂ) ^ 2) := by
          apply Finset.sum_congr rfl
          intro x hx
          simp [hx]
    _ = (D.totient : ℂ) * ∑ x ∈ U, ((‖g x‖ : ℂ) ^ 2) := (Finset.mul_sum _ _ _).symm

private theorem sum_unit_fourier_normSq {D : ℕ} [NeZero D] (u : DirichletCharacter ℂ D → ℂ) :
    (∑ y ∈ Finset.univ.filter (fun y : ZMod D => IsUnit y),
        ‖∑ B : DirichletCharacter ℂ D, B y * u B‖ ^ 2) =
      (D.totient : ℝ) * ∑ B : DirichletCharacter ℂ D, ‖u B‖ ^ 2 := by
  classical
  let U := Finset.univ.filter (fun y : ZMod D => IsUnit y)
  have hchar_ortho (B₁ B₂ : DirichletCharacter ℂ D) :
      (∑ y ∈ U, conj (B₁ y) * B₂ y) = if B₁ = B₂ then (D.totient : ℂ) else 0 := by
    have hsum : (∑ y ∈ U, conj (B₁ y) * B₂ y) = ∑ y : ZMod D, (B₁⁻¹ * B₂) y := by
      have hsub : (∑ y ∈ U, (B₁⁻¹ * B₂) y) = ∑ y : ZMod D, (B₁⁻¹ * B₂) y := by
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro y _ hy
        have hnu : ¬ IsUnit y := by simpa [U] using hy
        exact MulChar.map_nonunit _ hnu
      rw [← hsub]
      apply Finset.sum_congr rfl
      intro y hy
      have hu : IsUnit y := (Finset.mem_filter.mp hy).2
      rw [MulChar.mul_apply]
      congr 1
      obtain ⟨v, rfl⟩ := hu
      change star (B₁ (v : ZMod D)) = B₁⁻¹ (v : ZMod D)
      rw [MulChar.star_apply']
    rw [hsum]
    by_cases heq : B₁ = B₂
    · subst heq
      rw [if_pos rfl, inv_mul_cancel, MulChar.sum_one_eq_card_units, ZMod.card_units_eq_totient]
    · have hne : B₁⁻¹ * B₂ ≠ 1 := by
        intro h
        apply heq
        calc B₁ = B₁ * 1 := (mul_one _).symm
          _ = B₁ * (B₁⁻¹ * B₂) := by rw [h]
          _ = B₂ := by group
      rw [if_neg heq, MulChar.sum_eq_zero_of_ne_one hne]
  apply Complex.ofReal_injective
  push_cast
  calc
    (∑ y ∈ U, ((‖∑ B : DirichletCharacter ℂ D, B y * u B‖ : ℂ) ^ 2))
        = ∑ y ∈ U,
            (∑ B₁ : DirichletCharacter ℂ D, conj (B₁ y * u B₁)) *
              (∑ B₂ : DirichletCharacter ℂ D, B₂ y * u B₂) := by
          apply Finset.sum_congr rfl
          intro y _
          rw [← Complex.conj_mul', map_sum]
    _ = ∑ B₁ : DirichletCharacter ℂ D, ∑ B₂ : DirichletCharacter ℂ D,
          (conj (u B₁) * u B₂) * (∑ y ∈ U, conj (B₁ y) * B₂ y) := by
          simp_rw [Finset.sum_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro B₁ _
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro B₂ _
          apply Finset.sum_congr rfl
          intro y _
          rw [map_mul]
          ring
    _ = ∑ B₁ : DirichletCharacter ℂ D, ∑ B₂ : DirichletCharacter ℂ D,
          if B₁ = B₂ then (D.totient : ℂ) * ((‖u B₁‖ : ℂ) ^ 2) else 0 := by
          apply Finset.sum_congr rfl
          intro B₁ _
          apply Finset.sum_congr rfl
          intro B₂ _
          rw [hchar_ortho B₁ B₂]
          by_cases heq : B₁ = B₂
          · subst heq
            rw [if_pos rfl, if_pos rfl, Complex.conj_mul']
            ring
          · simp [heq]
    _ = ∑ B₁ : DirichletCharacter ℂ D, (D.totient : ℂ) * ((‖u B₁‖ : ℂ) ^ 2) := by
          apply Finset.sum_congr rfl
          intro B₁ _
          simp
    _ = (D.totient : ℂ) * ∑ B₁ : DirichletCharacter ℂ D, ((‖u B₁‖ : ℂ) ^ 2) :=
          (Finset.mul_sum _ _ _).symm

theorem main_theorem :
    ∀ D m : ℕ, 0 < D → 0 < m → Even m →
      ∃ F : Finset (Σ s : ℕ, DirichletCharacter ℂ s),
        (∀ b, b ∈ F ↔ (b.1 ≠ 0 ∧ b.2.IsPrimitive) ∧ b.1 ∣ D) ∧
        (let H := ((Finset.range D).filter (fun x => x.Coprime D ∧ (m + D - (x % D)).Coprime D)).card
         let scale := ‖series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m‖ *
           (D.totient : ℝ) / (H : ℝ)
         let normSq := fun w : (Σ s : ℕ, DirichletCharacter ℂ s) → ℂ => ∑ a ∈ F, ‖w a‖ ^ 2
         let applyRow := fun (w : (Σ s : ℕ, DirichletCharacter ℂ s) → ℂ)
           (a : Σ s : ℕ, DirichletCharacter ℂ s) => ∑ b ∈ F, series a.2 b.2 m * w b
         (∀ w : (Σ s : ℕ, DirichletCharacter ℂ s) → ℂ,
           normSq (applyRow w) ≤ scale ^ 2 * normSq w) ∧
         ∃ w : (Σ s : ℕ, DirichletCharacter ℂ s) → ℂ,
           0 < normSq w ∧ normSq (applyRow w) = scale ^ 2 * normSq w) := by
  classical
  intro D m hDpos hm he
  haveI : NeZero D := ⟨hDpos.ne'⟩
  let prim : DirichletCharacter ℂ D → Σ s : ℕ, DirichletCharacter ℂ s :=
    fun χ => ⟨χ.conductor, χ.primitiveCharacter⟩
  let F : Finset (Σ s : ℕ, DirichletCharacter ℂ s) := Finset.univ.image prim
  refine ⟨F, fun b => mem_prim_image b, ?_⟩
  dsimp only
  let H := ((Finset.range D).filter (fun x => x.Coprime D ∧ (m + D - (x % D)).Coprime D)).card
  let O := series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m
  let scale := ‖O‖ * (D.totient : ℝ) / (H : ℝ)
  let U := Finset.univ.filter (fun x : ZMod D => IsUnit x)
  let Uadm := Finset.univ.filter (admissible (m : ZMod D))
  have hJ11 : J (1 : DirichletCharacter ℂ D) 1 (m : ZMod D) = (H : ℂ) := by
    rw [principal_card, ← H_eq_admissible_card D m]
  have hHne : (H : ℂ) ≠ 0 := by
    rw [← hJ11]
    exact principal_ne_zero D m he
  have hHreal : (H : ℝ) ≠ 0 := by exact_mod_cast hHne
  have hS_eq (A B : DirichletCharacter ℂ D) :
      series A.primitiveCharacter B.primitiveCharacter m =
        (O / (H : ℂ)) * J A B (m : ZMod D) := by
    haveI : NeZero A.conductor :=
      ⟨ne_zero_of_dvd_ne_zero hDpos.ne' A.conductor_dvd_level⟩
    haveI : NeZero B.conductor :=
      ⟨ne_zero_of_dvd_ne_zero hDpos.ne' B.conductor_dvd_level⟩
    have hid := conductor_identity A.primitiveCharacter_isPrimitive
      B.primitiveCharacter_isPrimitive A.conductor_dvd_level B.conductor_dvd_level m hm
    rw [A.changeLevel_primitiveCharacter, B.changeLevel_primitiveCharacter, hJ11] at hid
    change series A.primitiveCharacter B.primitiveCharacter m * (H : ℂ) = O * J A B (m : ZMod D) at hid
    calc
      series A.primitiveCharacter B.primitiveCharacter m
          = (series A.primitiveCharacter B.primitiveCharacter m * (H : ℂ)) / (H : ℂ) :=
            (mul_div_cancel_right₀ _ hHne).symm
      _ = (O * J A B (m : ZMod D)) / (H : ℂ) := by rw [hid]
      _ = (O / (H : ℂ)) * J A B (m : ZMod D) := by ring
  have h_energy (w : (Σ s : ℕ, DirichletCharacter ℂ s) → ℂ) :
      let u : DirichletCharacter ℂ D → ℂ := fun χ => w (prim χ)
      let f : ZMod D → ℂ := fun y => ∑ B : DirichletCharacter ℂ D, B y * u B
      (∑ a ∈ F, ‖∑ b ∈ F, series a.2 b.2 m * w b‖ ^ 2) =
        (‖O‖ / (H : ℝ)) ^ 2 * (D.totient : ℝ) * ∑ y ∈ Uadm, ‖f y‖ ^ 2 := by
    intro u f
    have hrow (A : DirichletCharacter ℂ D) :
        (∑ b ∈ F, series A.primitiveCharacter b.2 m * w b) =
          (O / (H : ℂ)) * ∑ x : ZMod D, A x * f ((m : ZMod D) - x) := by
      dsimp only [F]
      rw [Finset.sum_image (fun x _ y _ h => prim_injective h)]
      calc
        (∑ B : DirichletCharacter ℂ D, series A.primitiveCharacter B.primitiveCharacter m * u B)
            = ∑ B : DirichletCharacter ℂ D, ((O / (H : ℂ)) * J A B (m : ZMod D)) * u B :=
              Finset.sum_congr rfl fun B _ => by rw [hS_eq A B]
        _ = (O / (H : ℂ)) * ∑ B : DirichletCharacter ℂ D, J A B (m : ZMod D) * u B := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun B _ => by ring
        _ = (O / (H : ℂ)) * ∑ x : ZMod D, A x * f ((m : ZMod D) - x) := by
              congr 1
              simp_rw [J, Finset.sum_mul]
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro x _
              dsimp only [f]
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun B _ => by ring
    have hnorm :
        (∑ a ∈ F, ‖∑ b ∈ F, series a.2 b.2 m * w b‖ ^ 2) =
          (‖O‖ / (H : ℝ)) ^ 2 *
            ∑ A : DirichletCharacter ℂ D, ‖∑ x : ZMod D, A x * f ((m : ZMod D) - x)‖ ^ 2 := by
      dsimp only [F]
      rw [Finset.sum_image (fun x _ y _ h => prim_injective h), Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro A _
      rw [hrow A, norm_mul, mul_pow, norm_div, Complex.norm_natCast]
    rw [hnorm, sum_char_normSq (fun x => f ((m : ZMod D) - x))]
    have hsub : (∑ x ∈ U, ‖f ((m : ZMod D) - x)‖ ^ 2) = ∑ y ∈ Uadm, ‖f y‖ ^ 2 := by
      have hzero : (∑ x ∈ U, ‖f ((m : ZMod D) - x)‖ ^ 2) = ∑ x ∈ Uadm, ‖f ((m : ZMod D) - x)‖ ^ 2 := by
        symm
        apply Finset.sum_subset
        · intro x hx
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2.1⟩
        · intro x hxU hxadm
          have hu1 : IsUnit x := (Finset.mem_filter.mp hxU).2
          have hnu2 : ¬ IsUnit ((m : ZMod D) - x) := fun hu2 =>
            hxadm (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu1, hu2⟩)
          have hf0 : f ((m : ZMod D) - x) = 0 := by
            dsimp only [f]
            exact Finset.sum_eq_zero fun B _ => by rw [MulChar.map_nonunit B hnu2, zero_mul]
          rw [hf0, norm_zero, zero_pow (by norm_num)]
      rw [hzero]
      refine Finset.sum_bij (fun x _ => (m : ZMod D) - x) ?_ ?_ ?_ ?_
      · intro x hx
        obtain ⟨_, hu1, hu2⟩ := Finset.mem_filter.mp hx
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu2, ?_⟩
        simpa [sub_sub_cancel] using hu1
      · intro x₁ _ x₂ _ heq
        exact sub_right_injective heq
      · intro y hy
        obtain ⟨_, hu1, hu2⟩ := Finset.mem_filter.mp hy
        refine ⟨(m : ZMod D) - y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu2, ?_⟩,
          sub_sub_cancel (m : ZMod D) y⟩
        simpa [sub_sub_cancel] using hu1
      · intro _ _
        rfl
    rw [hsub]
    ring
  constructor
  · intro w
    let u : DirichletCharacter ℂ D → ℂ := fun χ => w (prim χ)
    let f : ZMod D → ℂ := fun y => ∑ B : DirichletCharacter ℂ D, B y * u B
    have hnormSq_w : (∑ a ∈ F, ‖w a‖ ^ 2) = ∑ B : DirichletCharacter ℂ D, ‖u B‖ ^ 2 := by
      dsimp only [F]
      rw [Finset.sum_image (fun x _ y _ h => prim_injective h)]
    have hle : (∑ y ∈ Uadm, ‖f y‖ ^ 2) ≤ ∑ y ∈ U, ‖f y‖ ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro y hy
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hy).2.1⟩
      · intro _ _ _
        exact sq_nonneg _
    calc
      (∑ a ∈ F, ‖∑ b ∈ F, series a.2 b.2 m * w b‖ ^ 2)
          = (‖O‖ / (H : ℝ)) ^ 2 * (D.totient : ℝ) * ∑ y ∈ Uadm, ‖f y‖ ^ 2 := h_energy w
      _ ≤ (‖O‖ / (H : ℝ)) ^ 2 * (D.totient : ℝ) * ∑ y ∈ U, ‖f y‖ ^ 2 :=
            mul_le_mul_of_nonneg_left hle (by positivity)
      _ = (‖O‖ / (H : ℝ)) ^ 2 * (D.totient : ℝ) *
            ((D.totient : ℝ) * ∑ B : DirichletCharacter ℂ D, ‖u B‖ ^ 2) := by
            rw [sum_unit_fourier_normSq u]
      _ = scale ^ 2 * ∑ a ∈ F, ‖w a‖ ^ 2 := by
            rw [hnormSq_w]
            dsimp only [scale]
            ring
  · obtain ⟨x₀, hx₀⟩ := admissible_even D m he
    let y₀ : ZMod D := (m : ZMod D) - x₀
    have hy₀_unit : IsUnit y₀ := hx₀.2
    have hy₀_adm : y₀ ∈ Uadm := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy₀_unit, ?_⟩
      simpa [y₀, sub_sub_cancel] using hx₀.1
    let w : (Σ s : ℕ, DirichletCharacter ℂ s) → ℂ :=
      fun b => if h : b.1 ∣ D then (changeLevel h b.2) y₀⁻¹ else 0
    have hu_eq (χ : DirichletCharacter ℂ D) : w (prim χ) = χ y₀⁻¹ := by
      dsimp only [w, prim]
      rw [dif_pos χ.conductor_dvd_level, χ.changeLevel_primitiveCharacter]
    refine ⟨w, ?_, ?_⟩
    · have hnormSq_w : (∑ a ∈ F, ‖w a‖ ^ 2) = (D.totient : ℝ) := by
        dsimp only [F]
        rw [Finset.sum_image (fun x _ y _ h => prim_injective h)]
        have h1 (χ : DirichletCharacter ℂ D) : ‖w (prim χ)‖ ^ 2 = 1 := by
          rw [hu_eq χ]
          obtain ⟨u₀, hu₀⟩ := hy₀_unit
          have hinv : y₀⁻¹ = ((u₀⁻¹ : (ZMod D)ˣ) : ZMod D) := by
            rw [← hu₀, ZMod.inv_coe_unit]
          rw [hinv, χ.unit_norm_eq_one u₀⁻¹, one_pow]
        calc
          (∑ χ : DirichletCharacter ℂ D, ‖w (prim χ)‖ ^ 2)
              = ∑ _χ : DirichletCharacter ℂ D, (1 : ℝ) := Finset.sum_congr rfl fun χ _ => h1 χ
          _ = (Fintype.card (DirichletCharacter ℂ D) : ℝ) := by simp
          _ = (D.totient : ℝ) := by
                rw [← Nat.card_eq_fintype_card,
                  DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ D]
      rw [hnormSq_w]
      exact_mod_cast Nat.totient_pos.mpr hDpos
    · let u : DirichletCharacter ℂ D → ℂ := fun χ => w (prim χ)
      let f : ZMod D → ℂ := fun y => ∑ B : DirichletCharacter ℂ D, B y * u B
      have hf_eq (y : ZMod D) : f y = if y₀ = y then (D.totient : ℂ) else 0 := by
        dsimp only [f, u]
        have hswap : (∑ B : DirichletCharacter ℂ D, B y * w (prim B)) =
            ∑ B : DirichletCharacter ℂ D, B y₀⁻¹ * B y := by
          apply Finset.sum_congr rfl
          intro B _
          rw [hu_eq B, mul_comm]
        rw [hswap]
        exact DirichletCharacter.sum_char_inv_mul_char_eq ℂ hy₀_unit y
      have hnormSq_w : (∑ a ∈ F, ‖w a‖ ^ 2) = ∑ B : DirichletCharacter ℂ D, ‖u B‖ ^ 2 := by
        dsimp only [F]
        rw [Finset.sum_image (fun x _ y _ h => prim_injective h)]
      have heq_sum : (∑ y ∈ Uadm, ‖f y‖ ^ 2) = ∑ y ∈ U, ‖f y‖ ^ 2 := by
        apply Finset.sum_subset
        · intro y hy
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hy).2.1⟩
        · intro y _ hy_not
          have hne : y₀ ≠ y := fun h => hy_not (h ▸ hy₀_adm)
          rw [hf_eq y, if_neg hne, norm_zero, zero_pow (by norm_num)]
      calc
        (∑ a ∈ F, ‖∑ b ∈ F, series a.2 b.2 m * w b‖ ^ 2)
            = (‖O‖ / (H : ℝ)) ^ 2 * (D.totient : ℝ) * ∑ y ∈ Uadm, ‖f y‖ ^ 2 := h_energy w
        _ = (‖O‖ / (H : ℝ)) ^ 2 * (D.totient : ℝ) * ∑ y ∈ U, ‖f y‖ ^ 2 := by rw [heq_sum]
        _ = (‖O‖ / (H : ℝ)) ^ 2 * (D.totient : ℝ) *
              ((D.totient : ℝ) * ∑ B : DirichletCharacter ℂ D, ‖u B‖ ^ 2) := by
              rw [sum_unit_fourier_normSq u]
        _ = scale ^ 2 * ∑ a ∈ F, ‖w a‖ ^ 2 := by
              rw [hnormSq_w]
              dsimp only [scale]
              ring

end PartnerLevelSignedOperatorProof

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
  exact ∀ D m : ℕ, 0 < D → 0 < m → Even m → ∃ F : Finset B, (∀ b, b ∈ F ↔ valid b ∧ b.1 ∣ D) ∧ (let H := ((Finset.range D).filter (fun x => x.Coprime D ∧ (m+D-(x%D)).Coprime D)).card; let scale := ‖O m‖*(D.totient:ℝ)/(H:ℝ); let normSq := fun w : B → ℂ => ∑ a ∈ F, ‖w a‖^2; let applyRow := fun (w : B → ℂ) (a : B) => ∑ b ∈ F, S a.2 b.2 m * w b; (∀ w : B → ℂ, normSq (applyRow w) ≤ scale^2 * normSq w) ∧ ∃ w : B → ℂ, 0 < normSq w ∧ normSq (applyRow w) = scale^2 * normSq w) := by
  classical
  dsimp only
  exact PartnerLevelSignedOperatorProof.main_theorem
