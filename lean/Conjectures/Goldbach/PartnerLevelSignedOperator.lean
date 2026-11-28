import Mathlib
import Conjectures.Goldbach.PrimitivePartnerCubicMass
import Conjectures.Goldbach.SharpSingularSeriesRatios

/-! Exact ℓ² operator norm and extremal attainment for the signed twisted singular series
matrix across all primitive characters whose conductors divide a common level `D`. -/

namespace Conjectures.Goldbach.PartnerLevelSignedOperator_aux

open Finset DirichletCharacter MulChar
open Conjectures.Goldbach.SharpSingularSeriesRatiosProof
open TwistedGoldbachConductorRatio TwistedGoldbachLocalProduct
open scoped BigOperators Classical

private theorem star_eq_inv_of_isUnit {D : ℕ} [NeZero D] (χ : DirichletCharacter ℂ D)
    {x : ZMod D} (hx : IsUnit x) :
    (starRingEnd ℂ) (χ x) = χ x⁻¹ := by
  obtain ⟨u, rfl⟩ := hx
  have hu : (χ (u : ZMod D)) ^ Fintype.card (ZMod D)ˣ = 1 := by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, pow_card_eq_one, Units.val_one, map_one]
  have hnormPow : ‖χ (u : ZMod D)‖ ^ Fintype.card (ZMod D)ˣ = 1 := by
    rw [← norm_pow, hu, norm_one]
  have hnorm : ‖χ (u : ZMod D)‖ = 1 := by
    have hc : 0 < Fintype.card (ZMod D)ˣ := Fintype.card_pos
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hc.ne').mp hnormPow
  have hmul : (starRingEnd ℂ) (χ (u : ZMod D)) * χ (u : ZMod D) = 1 := by
    rw [mul_comm, Complex.mul_conj', hnorm]
    norm_num
  have hinv : χ (u : ZMod D)⁻¹ * χ (u : ZMod D) = 1 := by
    rw [← map_mul, (ZMod.inv_mul_eq_one_of_isUnit (⟨u, rfl⟩ : IsUnit (u : ZMod D)) (u : ZMod D)).mpr rfl, map_one]
  have hne : χ (u : ZMod D) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hmul
    exact zero_ne_one hmul
  exact mul_right_cancel₀ hne (hmul.trans hinv.symm)

private theorem component_one {ι : Type*} [DecidableEq ι] {q : ι → ℕ} {L : ℕ}
    (e : ZMod L ≃+* ∀ i, ZMod (q i)) (i : ι) :
    component e (1 : DirichletCharacter ℂ L) i = 1 := by
  apply MulChar.ext'
  intro x
  by_cases hx : IsUnit x
  · rw [MulChar.one_apply hx]
    have hunit : IsUnit (e.symm (Pi.mulSingle i x : ∀ j, ZMod (q j))) := by
      have hp : IsUnit (Pi.mulSingle i x : ∀ j, ZMod (q j)) := by
        refine Pi.isUnit_iff.mpr fun j => ?_
        by_cases hj : j = i
        · subst hj; simpa [Pi.mulSingle_eq_same] using hx
        · simp [Pi.mulSingle_eq_of_ne hj]
      simpa using hp.map e.symm
    change (1 : DirichletCharacter ℂ L) (e.symm (Pi.mulSingle i x : ∀ j, ZMod (q j))) = 1
    exact MulChar.one_apply hunit
  · rw [MulChar.map_nonunit (1 : DirichletCharacter ℂ (q i)) hx]
    have hnunit : ¬ IsUnit (e.symm (Pi.mulSingle i x : ∀ j, ZMod (q j))) := by
      intro hu
      have hp : IsUnit (Pi.mulSingle i x : ∀ j, ZMod (q j)) := by
        simpa using hu.map e
      have hi : IsUnit ((Pi.mulSingle i x : ∀ j, ZMod (q j)) i) := (Pi.isUnit_iff.mp hp) i
      rw [Pi.mulSingle_eq_same] at hi
      exact hx hi
    change (1 : DirichletCharacter ℂ L) (e.symm (Pi.mulSingle i x : ∀ j, ZMod (q j))) = 0
    exact MulChar.map_nonunit 1 hnunit

private theorem crt_J {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ι → ℕ} [∀ i, NeZero (q i)]
    {D : ℕ} [NeZero D] (e : ZMod D ≃+* ∀ i, ZMod (q i)) (m : ℕ)
    (A B : DirichletCharacter ℂ D) :
    (∏ i : ι, J (component e A i) (component e B i) (m : ZMod (q i))) =
      J A B (m : ZMod D) := by
  simp only [J]
  rw [Fintype.prod_sum]
  symm
  rw [← Equiv.sum_comp e.symm.toEquiv (fun x : ZMod D => A x * B ((m : ZMod D) - x))]
  apply Finset.sum_congr rfl
  intro y _
  have hm : ∀ i : ι, e ((m : ZMod D) - e.symm y) i = (m : ZMod (q i)) - y i := by
    intro i
    rw [map_sub, map_natCast, e.apply_symm_apply, Pi.sub_apply, Pi.natCast_apply]
  have hA : A (e.symm y) = ∏ i : ι, component e A i (y i) := by
    simpa [e.apply_symm_apply] using reassemble e A (e.symm y)
  have hB : B ((m : ZMod D) - e.symm y) =
      ∏ i : ι, component e B i ((m : ZMod (q i)) - y i) := by
    have hr := reassemble e B ((m : ZMod D) - e.symm y)
    refine hr.trans (Finset.prod_congr rfl fun i _ => ?_)
    rw [hm i]
  change A (e.symm y) * B ((m : ZMod D) - e.symm y) = _
  rw [hA, hB, ← Finset.prod_mul_distrib]

private theorem H_eq_admissible_card (D m : ℕ) [NeZero D] :
    ((Finset.range D).filter (fun x => x.Coprime D ∧ (m + D - (x % D)).Coprime D)).card =
      ((Finset.univ : Finset (ZMod D)).filter (admissible (m : ZMod D))).card := by
  refine Finset.card_bij (fun x _ => (x : ZMod D)) ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_univ, true_and, admissible] at hx ⊢
    rcases hx with ⟨hxD, h1, h2⟩
    have hmod : x % D = x := Nat.mod_eq_of_lt hxD
    rw [hmod] at h2
    have hsub : ((m + D - x : ℕ) : ZMod D) = (m : ZMod D) - (x : ZMod D) := by
      have hle : x ≤ m + D := by omega
      apply eq_sub_of_add_eq
      rw [← Nat.cast_add, Nat.sub_add_cancel hle, Nat.cast_add, ZMod.natCast_self, add_zero]
    refine ⟨(ZMod.isUnit_iff_coprime x D).mpr h1, ?_⟩
    rw [← hsub]
    exact (ZMod.isUnit_iff_coprime (m + D - x) D).mpr h2
  · intro x hx y hy hxy
    simp only [Finset.mem_filter, Finset.mem_range] at hx hy
    have hv := congrArg ZMod.val hxy
    rwa [ZMod.val_natCast_of_lt hx.1, ZMod.val_natCast_of_lt hy.1] at hv
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, admissible] at ha
    refine ⟨a.val, ?_, ZMod.natCast_zmod_val a⟩
    have hv : a.val < D := ZMod.val_lt a
    have h1 : a.val.Coprime D := by
      apply (ZMod.isUnit_iff_coprime a.val D).mp
      simpa [ZMod.natCast_zmod_val] using ha.1
    have hsub : ((m + D - a.val : ℕ) : ZMod D) = (m : ZMod D) - a := by
      have hle : a.val ≤ m + D := by omega
      apply eq_sub_of_add_eq
      conv_lhs => rhs; rw [← ZMod.natCast_zmod_val a]
      rw [← Nat.cast_add, Nat.sub_add_cancel hle, Nat.cast_add, ZMod.natCast_self, add_zero]
    have h2 : (m + D - a.val % D).Coprime D := by
      rw [Nat.mod_eq_of_lt hv]
      apply (ZMod.isUnit_iff_coprime (m + D - a.val) D).mp
      rw [hsub]
      exact ha.2
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hv, h1, h2⟩

private theorem series_eq_mul_J {D : ℕ} [NeZero D] (m : ℕ) (hm : 0 < m) (he : Even m)
    (A B : DirichletCharacter ℂ D) :
    series A.primitiveCharacter B.primitiveCharacter m =
      (series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m /
        (((Finset.univ : Finset (ZMod D)).filter (admissible (m : ZMod D))).card : ℂ)) *
        J A B (m : ZMod D) := by
  let I := ↥D.primeFactors
  let Q (i : I) := (i : ℕ) ^ D.factorization (i : ℕ)
  have (i : I) : NeZero (Q i) :=
    ⟨pow_ne_zero _ (Nat.Prime.ne_zero (Nat.mem_primeFactors.mp i.property).1)⟩
  let e := ZMod.equivPi D (NeZero.ne D)
  have : NeZero A.conductor := ⟨A.conductor_ne_zero⟩
  have : NeZero B.conductor := ⟨B.conductor_ne_zero⟩
  have hfp := full_product e A.primitiveCharacter_isPrimitive B.primitiveCharacter_isPrimitive
    A.conductor_dvd_level B.conductor_dvd_level m hm he
  rw [changeLevel_primitiveCharacter A, changeLevel_primitiveCharacter B] at hfp
  rw [hfp, Finset.prod_div_distrib, crt_J e m A B]
  have h1 : (∏ i : I, J (1 : DirichletCharacter ℂ (Q i)) 1 (m : ZMod (Q i))) =
      J (1 : DirichletCharacter ℂ D) 1 (m : ZMod D) := by
    have hc : ∀ i : I, component e (1 : DirichletCharacter ℂ D) i = 1 := component_one e
    simpa only [hc] using crt_J e m (1 : DirichletCharacter ℂ D) (1 : DirichletCharacter ℂ D)
  rw [h1, principal_card (m : ZMod D)]
  ring

private theorem parseval_admissible {D : ℕ} [NeZero D] (m : ZMod D) (z : ZMod D → ℂ) :
    (∑ A : DirichletCharacter ℂ D,
      ‖∑ x ∈ (Finset.univ : Finset (ZMod D)).filter (admissible m), A x * z x‖ ^ 2) =
      (D.totient : ℝ) * ∑ x ∈ (Finset.univ : Finset (ZMod D)).filter (admissible m), ‖z x‖ ^ 2 := by
  let U := (Finset.univ : Finset (ZMod D)).filter (admissible m)
  apply Complex.ofReal_injective
  push_cast
  have h1 : ∀ c : ℂ, (‖c‖ : ℂ) ^ 2 = (starRingEnd ℂ) c * c := fun c => by
    rw [mul_comm, Complex.mul_conj']
  simp_rw [h1, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hswap : (∑ x ∈ U, ∑ A : DirichletCharacter ℂ D, ∑ y ∈ U,
      (starRingEnd ℂ (A x) * starRingEnd ℂ (z x)) * (A y * z y)) =
      ∑ x ∈ U, ∑ y ∈ U, (∑ A : DirichletCharacter ℂ D, A x⁻¹ * A y) *
        (starRingEnd ℂ (z x) * z y) := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _
    have hux : IsUnit x := (Finset.mem_filter.mp hx).2.1
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro A _
    rw [star_eq_inv_of_isUnit A hux]
    ring
  rw [hswap]
  apply Finset.sum_congr rfl
  intro x hx
  have hux : IsUnit x := (Finset.mem_filter.mp hx).2.1
  have hsub : (∑ y ∈ U, (∑ A : DirichletCharacter ℂ D, A x⁻¹ * A y) *
      (starRingEnd ℂ (z x) * z y)) =
      ∑ y ∈ U, if y = x then (D.totient : ℂ) * (starRingEnd ℂ (z x) * z y) else 0 := by
    apply Finset.sum_congr rfl
    intro y _
    rw [DirichletCharacter.sum_char_inv_mul_char_eq ℂ hux y]
    by_cases hxy : x = y
    · subst hxy; simp
    · rw [ite_eq_right hxy, ite_eq_right (Ne.symm hxy), zero_mul]
  rw [hsub, Finset.sum_ite_eq', ite_eq_left hx]

private theorem parseval_chars {D : ℕ} [NeZero D] (v : DirichletCharacter ℂ D → ℂ) :
    (∑ y ∈ (Finset.univ : Finset (ZMod D)).filter (fun y => IsUnit y),
      ‖∑ B : DirichletCharacter ℂ D, B y * v B‖ ^ 2) =
      (D.totient : ℝ) * ∑ B : DirichletCharacter ℂ D, ‖v B‖ ^ 2 := by
  let UD := (Finset.univ : Finset (ZMod D)).filter (fun y => IsUnit y)
  apply Complex.ofReal_injective
  push_cast
  have h1 : ∀ c : ℂ, (‖c‖ : ℂ) ^ 2 = (starRingEnd ℂ) c * c := fun c => by
    rw [mul_comm, Complex.mul_conj']
  simp_rw [h1, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hswap : (∑ B : DirichletCharacter ℂ D, ∑ y ∈ UD, ∑ B' : DirichletCharacter ℂ D,
      (starRingEnd ℂ (B y) * starRingEnd ℂ (v B)) * (B' y * v B')) =
      ∑ B : DirichletCharacter ℂ D, ∑ B' : DirichletCharacter ℂ D,
        (∑ y ∈ UD, starRingEnd ℂ (B y) * B' y) * (starRingEnd ℂ (v B) * v B') := by
    apply Finset.sum_congr rfl
    intro B _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro B' _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro y _
    ring
  rw [hswap]
  apply Finset.sum_congr rfl
  intro B _
  have hsub : (∑ B' : DirichletCharacter ℂ D,
      (∑ y ∈ UD, starRingEnd ℂ (B y) * B' y) * (starRingEnd ℂ (v B) * v B')) =
      ∑ B' : DirichletCharacter ℂ D,
        if B' = B then (D.totient : ℂ) * (starRingEnd ℂ (v B) * v B') else 0 := by
    apply Finset.sum_congr rfl
    intro B' _
    have hsum : (∑ y ∈ UD, starRingEnd ℂ (B y) * B' y) = ∑ y : ZMod D, (B⁻¹ * B') y := by
      have hsub1 : (∑ y ∈ UD, starRingEnd ℂ (B y) * B' y) = ∑ y ∈ UD, (B⁻¹ * B') y := by
        apply Finset.sum_congr rfl
        intro y hy
        have huy : IsUnit y := (Finset.mem_filter.mp hy).2
        obtain ⟨u, rfl⟩ := huy
        rw [star_eq_inv_of_isUnit B ⟨u, rfl⟩, MulChar.mul_apply, MulChar.inv_apply, Ring.inverse_unit u]
        congr 1
        have hmul : B (u : ZMod D)⁻¹ * B (u : ZMod D) = 1 := by
          rw [← map_mul, (ZMod.inv_mul_eq_one_of_isUnit (⟨u, rfl⟩ : IsUnit (u : ZMod D)) (u : ZMod D)).mpr rfl, map_one]
        have hmul2 : B ((u⁻¹ : (ZMod D)ˣ) : ZMod D) * B (u : ZMod D) = 1 := by
          rw [← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one]
        have hne : B (u : ZMod D) ≠ 0 := by
          intro h0
          rw [h0, mul_zero] at hmul
          exact zero_ne_one hmul
        exact mul_right_cancel₀ hne (hmul.trans hmul2.symm)
      rw [hsub1]
      symm
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun y : ZMod D => IsUnit y)]
      have h0 : ∑ y ∈ Finset.univ.filter (fun y : ZMod D => ¬ IsUnit y), (B⁻¹ * B') y = 0 := by
        apply Finset.sum_eq_zero
        intro y hy
        exact MulChar.map_nonunit _ (Finset.mem_filter.mp hy).2
      rw [h0, add_zero]
    rw [hsum]
    by_cases hBB : B = B'
    · subst hBB
      rw [ite_eq_left rfl, inv_mul_cancel, MulChar.sum_one_eq_card_units, ZMod.card_units_eq_totient]
    · have hne1 : B⁻¹ * B' ≠ 1 := by
        intro h1
        apply hBB
        calc B = B * 1 := (mul_one B).symm
          _ = B * (B⁻¹ * B') := by rw [h1]
          _ = B' := by rw [← mul_assoc, mul_inv_cancel, one_mul]
      rw [ite_eq_right (Ne.symm hBB), MulChar.sum_eq_zero_of_ne_one hne1, zero_mul]
  rw [hsub, Finset.sum_ite_eq', ite_eq_left (Finset.mem_univ B)]

private theorem sum_admissible_sub {D : ℕ} [NeZero D] (m : ZMod D) (f : ZMod D → ℝ) :
    (∑ x ∈ (Finset.univ : Finset (ZMod D)).filter (admissible m), f (m - x)) =
      ∑ y ∈ (Finset.univ : Finset (ZMod D)).filter (admissible m), f y := by
  apply Finset.sum_bij (fun x _ => m - x)
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, admissible] at hx ⊢
    exact ⟨hx.2, by simpa only [sub_sub_cancel] using hx.1⟩
  · intro x _ y _ hxy
    have h := congrArg (fun t => m - t) hxy
    simpa only [sub_sub_cancel] using h
  · intro y hy
    refine ⟨m - y, ?_, sub_sub_cancel m y⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, admissible] at hy ⊢
    exact ⟨hy.2, by simpa only [sub_sub_cancel] using hy.1⟩
  · intro _ _; rfl

private theorem sigma_eq_of_changeLevel {s t L : ℕ} [NeZero L]
    (a : DirichletCharacter ℂ s) (b : DirichletCharacter ℂ t)
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
    let B := Σ s : ℕ, DirichletCharacter ℂ s
    let valid := fun b : B => b.1 ≠ 0 ∧ b.2.IsPrimitive
    let O := series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1)
    ∃ F : Finset B, (∀ b, b ∈ F ↔ valid b ∧ b.1 ∣ D) ∧
      (let H := ((Finset.range D).filter (fun x => x.Coprime D ∧ (m + D - (x % D)).Coprime D)).card
       let scale := ‖O m‖ * (D.totient : ℝ) / (H : ℝ)
       let normSq := fun w : B → ℂ => ∑ a ∈ F, ‖w a‖ ^ 2
       let applyRow := fun (w : B → ℂ) (a : B) => ∑ b ∈ F, series a.2 b.2 m * w b
       (∀ w : B → ℂ, normSq (applyRow w) ≤ scale ^ 2 * normSq w) ∧
       ∃ w : B → ℂ, 0 < normSq w ∧ normSq (applyRow w) = scale ^ 2 * normSq w) := by
  classical
  have : NeZero D := ⟨hD.ne'⟩
  let B := Σ s : ℕ, DirichletCharacter ℂ s
  let valid : B → Prop := fun b => b.1 ≠ 0 ∧ b.2.IsPrimitive
  let g : DirichletCharacter ℂ D → B := fun χ => ⟨χ.conductor, χ.primitiveCharacter⟩
  let F : Finset B := Finset.univ.image g
  have hF : ∀ b : B, b ∈ F ↔ valid b ∧ b.1 ∣ D := by
    intro b
    simp only [F, Finset.mem_image, Finset.mem_univ, true_and, valid]
    constructor
    · rintro ⟨χ, rfl⟩
      exact ⟨⟨χ.conductor_ne_zero, χ.primitiveCharacter_isPrimitive⟩, χ.conductor_dvd_level⟩
    · rintro ⟨⟨hb0, hbprim⟩, hbd⟩
      rcases b with ⟨s, β⟩
      have : NeZero s := ⟨hb0⟩
      refine ⟨changeLevel hbd β, sigma_eq_of_changeLevel _ _ _ _
        (primitiveCharacter_isPrimitive _) hbprim (changeLevel_primitiveCharacter _)⟩
  have ginj : Function.Injective g := by
    intro χ₁ χ₂ h
    have h1 := lift_congr χ₁.conductor_dvd_level χ₂.conductor_dvd_level
      χ₁.primitiveCharacter χ₂.primitiveCharacter h
    rwa [changeLevel_primitiveCharacter, changeLevel_primitiveCharacter] at h1
  let U := (Finset.univ : Finset (ZMod D)).filter (admissible (m : ZMod D))
  let UD := (Finset.univ : Finset (ZMod D)).filter (fun x => IsUnit x)
  have hHU : ((Finset.range D).filter (fun x => x.Coprime D ∧ (m + D - (x % D)).Coprime D)).card = U.card :=
    H_eq_admissible_card D m
  have hUpos : 0 < U.card := by
    have hnz := principal_ne_zero D m he
    rw [principal_card (m : ZMod D)] at hnz
    exact Nat.pos_of_ne_zero (by exact_mod_cast hnz)
  have hUsub : U ⊆ UD := fun x hx => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2.1⟩
  let c₀ : ℂ := series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m / (U.card : ℂ)
  have hc₀norm : ‖c₀‖ = ‖series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m‖ / (U.card : ℝ) := by
    rw [norm_div, Complex.norm_natCast]
  have hsumF : ∀ f : B → ℝ, (∑ a ∈ F, f a) = ∑ A : DirichletCharacter ℂ D, f (g A) := by
    intro f
    exact Finset.sum_image (fun x _ y _ h => ginj h)
  have hsumFC : ∀ f : B → ℂ, (∑ a ∈ F, f a) = ∑ A : DirichletCharacter ℂ D, f (g A) := by
    intro f
    exact Finset.sum_image (fun x _ y _ h => ginj h)
  have happly : ∀ (w : B → ℂ) (A : DirichletCharacter ℂ D),
      (∑ b ∈ F, series (g A).2 b.2 m * w b) =
        c₀ * ∑ x ∈ U, A x * (∑ χ : DirichletCharacter ℂ D, χ ((m : ZMod D) - x) * w (g χ)) := by
    intro w A
    rw [hsumFC (fun b => series (g A).2 b.2 m * w b)]
    have hterm : ∀ χ : DirichletCharacter ℂ D,
        series (g A).2 (g χ).2 m * w (g χ) =
          c₀ * ∑ x ∈ U, A x * χ ((m : ZMod D) - x) * w (g χ) := by
      intro χ
      dsimp only [g]
      rw [series_eq_mul_J m hm he A χ]
      change c₀ * J A χ (m : ZMod D) * w (g χ) = _
      have hJ : J A χ (m : ZMod D) = ∑ x ∈ U, A x * χ ((m : ZMod D) - x) := by
        simp only [J]
        rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (admissible (m : ZMod D))]
        have h0 : ∑ x ∈ Finset.univ.filter (fun x => ¬ admissible (m : ZMod D) x),
            A x * χ ((m : ZMod D) - x) = 0 := by
          apply Finset.sum_eq_zero
          intro x hx
          have hna : ¬ (IsUnit x ∧ IsUnit ((m : ZMod D) - x)) := (Finset.mem_filter.mp hx).2
          by_cases h1 : IsUnit x
          · have h2 : ¬ IsUnit ((m : ZMod D) - x) := fun h => hna ⟨h1, h⟩
            rw [MulChar.map_nonunit χ h2, mul_zero]
          · rw [MulChar.map_nonunit A h1, zero_mul]
        rw [h0, add_zero]
      rw [hJ, mul_assoc, ← Finset.sum_mul]
    simp_rw [hterm, ← Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    simp_rw [mul_assoc, ← Finset.mul_sum]
  have hnormApply : ∀ w : B → ℂ,
      (∑ a ∈ F, ‖∑ b ∈ F, series a.2 b.2 m * w b‖ ^ 2) =
        ‖c₀‖ ^ 2 * (D.totient : ℝ) *
          ∑ y ∈ U, ‖∑ χ : DirichletCharacter ℂ D, χ y * w (g χ)‖ ^ 2 := by
    intro w
    rw [hsumF (fun a => ‖∑ b ∈ F, series a.2 b.2 m * w b‖ ^ 2)]
    simp_rw [happly w, norm_mul, mul_pow, ← Finset.mul_sum]
    rw [parseval_admissible (m : ZMod D) (fun x => ∑ χ : DirichletCharacter ℂ D, χ ((m : ZMod D) - x) * w (g χ))]
    rw [sum_admissible_sub (m : ZMod D) (fun y => ‖∑ χ : DirichletCharacter ℂ D, χ y * w (g χ)‖ ^ 2)]
    ring
  refine ⟨F, hF, ?_⟩
  dsimp only
  rw [hHU]
  have hscale : (‖series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m‖ *
      (D.totient : ℝ) / (U.card : ℝ)) ^ 2 = ‖c₀‖ ^ 2 * (D.totient : ℝ) ^ 2 := by
    rw [hc₀norm]
    ring
  constructor
  · intro w
    rw [hnormApply w, hscale, hsumF (fun a => ‖w a‖ ^ 2)]
    have hsub : (∑ y ∈ U, ‖∑ χ : DirichletCharacter ℂ D, χ y * w (g χ)‖ ^ 2) ≤
        ∑ y ∈ UD, ‖∑ χ : DirichletCharacter ℂ D, χ y * w (g χ)‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hUsub (fun _ _ _ => sq_nonneg _)
    have hpc := parseval_chars (fun χ => w (g χ))
    have hcpos : 0 ≤ ‖c₀‖ ^ 2 * (D.totient : ℝ) := by positivity
    calc
      ‖c₀‖ ^ 2 * (D.totient : ℝ) * ∑ y ∈ U, ‖∑ χ : DirichletCharacter ℂ D, χ y * w (g χ)‖ ^ 2
          ≤ ‖c₀‖ ^ 2 * (D.totient : ℝ) * ∑ y ∈ UD, ‖∑ χ : DirichletCharacter ℂ D, χ y * w (g χ)‖ ^ 2 :=
        mul_le_mul_of_nonneg_left hsub hcpos
      _ = ‖c₀‖ ^ 2 * (D.totient : ℝ) * ((D.totient : ℝ) * ∑ χ : DirichletCharacter ℂ D, ‖w (g χ)‖ ^ 2) := by
        rw [hpc]
      _ = ‖c₀‖ ^ 2 * (D.totient : ℝ) ^ 2 * ∑ χ : DirichletCharacter ℂ D, ‖w (g χ)‖ ^ 2 := by
        ring
  · let w : B → ℂ := fun b =>
      if h : b.1 ∣ D then ∑ x ∈ U, (starRingEnd ℂ) ((changeLevel h b.2) x) else 0
    have hw : ∀ χ : DirichletCharacter ℂ D, w (g χ) = ∑ x ∈ U, (starRingEnd ℂ) (χ x) := by
      intro χ
      dsimp only [w, g]
      rw [dite_eq_left χ.conductor_dvd_level, changeLevel_primitiveCharacter χ]
    have hW : ∀ y ∈ UD, (∑ χ : DirichletCharacter ℂ D, χ y * w (g χ)) =
        if y ∈ U then (D.totient : ℂ) else 0 := by
      intro y hy
      simp_rw [hw, Finset.mul_sum]
      rw [Finset.sum_comm]
      have hterm : ∀ x ∈ U, (∑ χ : DirichletCharacter ℂ D, χ y * (starRingEnd ℂ) (χ x)) =
          if x = y then (D.totient : ℂ) else 0 := by
        intro x hx
        have hux : IsUnit x := (Finset.mem_filter.mp hx).2.1
        have hsum : (∑ χ : DirichletCharacter ℂ D, χ y * (starRingEnd ℂ) (χ x)) =
            ∑ χ : DirichletCharacter ℂ D, χ x⁻¹ * χ y := by
          apply Finset.sum_congr rfl
          intro χ _
          rw [star_eq_inv_of_isUnit χ hux, mul_comm]
        rw [hsum, DirichletCharacter.sum_char_inv_mul_char_eq ℂ hux y]
      rw [Finset.sum_congr rfl hterm]
      by_cases hyU : y ∈ U
      · rw [ite_eq_left hyU, Finset.sum_ite_eq', ite_eq_left hyU]
      · rw [ite_eq_right hyU]
        apply Finset.sum_eq_zero
        intro x hx
        exact ite_eq_right (fun (h : x = y) => hyU (h ▸ hx))
    have hUeq : (∑ y ∈ U, ‖∑ χ : DirichletCharacter ℂ D, χ y * w (g χ)‖ ^ 2) =
        ∑ y ∈ UD, ‖∑ χ : DirichletCharacter ℂ D, χ y * w (g χ)‖ ^ 2 := by
      symm
      rw [← Finset.sum_sdiff hUsub]
      have h0 : ∑ y ∈ UD \ U, ‖∑ χ : DirichletCharacter ℂ D, χ y * w (g χ)‖ ^ 2 = 0 := by
        apply Finset.sum_eq_zero
        intro y hy
        obtain ⟨hyD, hyU⟩ := Finset.mem_sdiff.mp hy
        rw [hW y hyD, ite_eq_right hyU, norm_zero, sq, mul_zero]
      rw [h0, zero_add]
    have htotpos : 0 < (D.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hD
    have hnormSq : 0 < ∑ a ∈ F, ‖w a‖ ^ 2 := by
      have hpc := parseval_chars (fun χ => w (g χ))
      rw [hsumF (fun a => ‖w a‖ ^ 2)]
      have hval : (∑ y ∈ UD, ‖∑ χ : DirichletCharacter ℂ D, χ y * w (g χ)‖ ^ 2) =
          (U.card : ℝ) * (D.totient : ℝ) ^ 2 := by
        rw [← hUeq]
        have hterm : ∀ y ∈ U, ‖∑ χ : DirichletCharacter ℂ D, χ y * w (g χ)‖ ^ 2 = (D.totient : ℝ) ^ 2 := by
          intro y hy
          rw [hW y (hUsub hy), ite_eq_left hy, Complex.norm_natCast]
        rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
      have hlhs : 0 < (D.totient : ℝ) * ∑ χ : DirichletCharacter ℂ D, ‖w (g χ)‖ ^ 2 := by
        rw [← hpc, hval]
        positivity
      exact (mul_pos_iff_of_pos_left htotpos).mp hlhs
    refine ⟨w, hnormSq, ?_⟩
    rw [hnormApply w, hUeq, hscale, parseval_chars (fun χ => w (g χ)), hsumF (fun a => ‖w a‖ ^ 2)]
    ring

end Conjectures.Goldbach.PartnerLevelSignedOperator_aux

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
  exact ∀ D m : ℕ, 0 < D → 0 < m → Even m → ∃ F : Finset B, (∀ b, b ∈ F ↔ valid b ∧ b.1 ∣ D) ∧ (let H := ((Finset.range D).filter (fun x => x.Coprime D ∧ (m+D-(x % D)).Coprime D)).card; let scale := ‖O m‖*(D.totient:ℝ)/(H:ℝ); let normSq := fun w : B → ℂ => ∑ a ∈ F, ‖w a‖^2; let applyRow := fun (w : B → ℂ) (a : B) => ∑ b ∈ F, S a.2 b.2 m * w b; (∀ w : B → ℂ, normSq (applyRow w) ≤ scale^2 * normSq w) ∧ ∃ w : B → ℂ, 0 < normSq w ∧ normSq (applyRow w) = scale^2 * normSq w)
:= by
  classical
  dsimp only
  intro D m hD hm he
  exact Conjectures.Goldbach.PartnerLevelSignedOperator_aux.main D m hD hm he
