import Mathlib
import Conjectures.Goldbach.PartnerLevelParseval

/-!
Character orthogonality identifies the Jacobi-sum matrix with the transform
of reflection restricted to admissible units. A point mass on one such unit
attains the norm. Reindexing by primitive origins transfers both assertions
to the matrix of singular series.

The conductor ratio is from zxg0623's PR #4023. The character parametrization
by primitive origins follows PR #4316. The local energy calculation also uses
the character orthogonality underlying PR #4245.
-/

namespace PartnerOperatorCount

open Finset
open Conjectures.Goldbach.SharpSingularSeriesRatiosProof
open TwistedGoldbachConductorRatio
open scoped Classical

theorem count_eq (D m : ℕ) [NeZero D] :
    ((Finset.range D).filter (fun x => x.Coprime D ∧ (m+D-(Nat.mod x D)).Coprime D)).card =
      (Finset.univ.filter (admissible (m : ZMod D))).card := by
  classical
  have bridge (x : ℕ) (hx : x < D) :
      (x.Coprime D ∧ (m+D-(Nat.mod x D)).Coprime D) ↔ admissible (m : ZMod D) (x : ZMod D) := by
    change _ ↔ IsUnit (x : ZMod D) ∧ IsUnit ((m:ZMod D) - x)
    rw [show Nat.mod x D = x from Nat.mod_eq_of_lt hx, ← ZMod.isUnit_iff_coprime, ← ZMod.isUnit_iff_coprime,
      Nat.cast_sub (by omega : x ≤ m+D), Nat.cast_add, ZMod.natCast_self, add_zero]
  apply Finset.card_bij (fun (x : ℕ) _ => (x : ZMod D))
  · intro x hx
    obtain ⟨hr,h⟩ := mem_filter.mp hx
    exact mem_filter.mpr ⟨mem_univ _, (bridge x (mem_range.mp hr)).mp h⟩
  · intro a ha b hb he
    have h := congrArg ZMod.val he
    simpa only [ZMod.val_natCast_of_lt (mem_range.mp (mem_filter.mp ha).1),
      ZMod.val_natCast_of_lt (mem_range.mp (mem_filter.mp hb).1)] using h
  · intro b hb
    refine ⟨b.val, mem_filter.mpr ⟨mem_range.mpr b.val_lt, (bridge b.val b.val_lt).mpr ?_⟩,
      ZMod.natCast_zmod_val b⟩
    rw [ZMod.natCast_zmod_val]
    exact (mem_filter.mp hb).2

theorem norm_eq_count (D m : ℕ) [NeZero D] :
    ‖J (1 : DirichletCharacter ℂ D) 1 (m:ZMod D)‖ =
      (((Finset.range D).filter (fun x => x.Coprime D ∧ (m+D-(Nat.mod x D)).Coprime D)).card:ℝ) := by
  rw [principal_card, Complex.norm_natCast, count_eq]

theorem count_pos (D m : ℕ) [NeZero D] (he : Even m) :
    0 < ((Finset.range D).filter (fun x => x.Coprime D ∧ (m+D-(Nat.mod x D)).Coprime D)).card := by
  rw [count_eq]
  obtain ⟨x,hx⟩ := admissible_even D m he
  exact card_pos.mpr ⟨x, mem_filter.mpr ⟨mem_univ _, hx⟩⟩

end PartnerOperatorCount

namespace SignedLevel
open Finset DirichletCharacter
open Conjectures.Goldbach.SharpSingularSeriesRatiosProof.TwistedGoldbachConductorRatio
open scoped ComplexConjugate Classical

private theorem gram_energy {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (M : ι → κ → ℂ) (d : κ → ℝ)
    (h : ∀ x y, (∑ i, conj (M i x) * M i y) = if x = y then (d x : ℂ) else 0)
    (v : κ → ℂ) :
    (∑ i, ‖∑ x, M i x * v x‖^2) = ∑ x, d x * ‖v x‖^2 := by
  apply Complex.ofReal_injective
  push_cast
  simp only [← Complex.conj_mul']
  calc
    _ = ∑ i, ∑ x, ∑ y, (conj (v x)*v y) * (conj (M i x)*M i y) := by
      apply sum_congr rfl
      intro i _
      rw [map_sum, sum_mul]
      apply sum_congr rfl
      intro x _
      rw [mul_sum]
      apply sum_congr rfl
      intro y _
      rw [map_mul]
      ring
    _ = ∑ x, ∑ y, (conj (v x)*v y) * ∑ i, conj (M i x)*M i y := by
      rw [sum_comm]
      apply sum_congr rfl
      intro x _
      rw [sum_comm]
      simp only [mul_sum]
    _ = _ := by
      simp_rw [h]
      simp [mul_comm]

theorem char_orthogonal {q : ℕ} [NeZero q] (x y : ZMod q) (hx : IsUnit x) :
    (∑ A : DirichletCharacter ℂ q, conj (A x) * A y) = if x=y then (q.totient:ℂ) else 0 := by
  have hc (A : DirichletCharacter ℂ q) : conj (A x) = A x⁻¹ := by
    obtain ⟨u,rfl⟩ := hx
    rw [ZMod.inv_coe_unit]
    change star (A (u:ZMod q)) = _
    rw [MulChar.star_apply', MulChar.inv_apply, Ring.inverse_unit]
  simpa only [hc] using DirichletCharacter.sum_char_inv_mul_char_eq ℂ hx y

private theorem residue_orthogonal {q : ℕ} [NeZero q] (A B : DirichletCharacter ℂ q) :
    (∑ x : ZMod q, conj (A x) * B x) = if A=B then (q.totient:ℂ) else 0 := by
  change (∑ x : ZMod q, star (A x) * B x) = _
  simp only [MulChar.star_apply', ← MulChar.mul_apply]
  by_cases h : A=B
  · subst B
    simp [MulChar.sum_one_eq_card_units, ZMod.card_units_eq_totient]
  · rw [ite_eq_right h, MulChar.sum_eq_zero_of_ne_one]
    exact fun he => h (inv_mul_eq_one.mp he)

theorem local_operator_le {q : ℕ} [NeZero q] (m : ZMod q) (w : DirichletCharacter ℂ q → ℂ) :
    (∑ A : DirichletCharacter ℂ q, ‖∑ B, J A B m * w B‖^2) ≤
      (q.totient : ℝ)^2 * ∑ B, ‖w B‖^2 := by
  let f (x : ZMod q) := ∑ B : DirichletCharacter ℂ q, B x * w B
  let d (x : ZMod q) : ℝ := if IsUnit x then q.totient else 0
  have hd (x y : ZMod q) :
      (∑ A : DirichletCharacter ℂ q, conj (A x) * A y) = if x=y then (d x:ℂ) else 0 := by
    by_cases hx : IsUnit x
    · simpa [d,hx] using char_orthogonal x y hx
    · simp [d,hx,MulChar.map_nonunit _ hx]
  have inner : (∑ x, ‖f x‖^2) = (q.totient:ℝ) * ∑ B, ‖w B‖^2 := by
    rw [mul_sum]
    exact gram_energy (fun (x : ZMod q) (B : DirichletCharacter ℂ q) => B x)
      (fun _ => (q.totient:ℝ)) residue_orthogonal w
  have transform (A : DirichletCharacter ℂ q) : (∑ B, J A B m * w B) = ∑ x, A x * f (m-x) := by
    simp only [J,f,sum_mul,mul_sum,mul_assoc]
    rw [sum_comm]
  have flip : (∑ x : ZMod q, ‖f (m-x)‖^2) = ∑ y, ‖f y‖^2 := by
    exact Fintype.sum_equiv ((Equiv.neg (ZMod q)).trans (Equiv.addLeft m)) _ _
      (fun x => by simp [sub_eq_add_neg])
  simp_rw [transform]
  rw [gram_energy (fun (A : DirichletCharacter ℂ q) (x : ZMod q) => A x) d hd]
  calc
    _ ≤ ∑ x : ZMod q, (q.totient:ℝ) * ‖f (m-x)‖^2 := by
      apply sum_le_sum
      intro x _
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      by_cases hx : IsUnit x <;> simp [d,hx]
    _ = _ := by rw [← mul_sum,flip,inner]; ring

end SignedLevel

namespace SignedLevel
open Finset DirichletCharacter
open Conjectures.Goldbach.SharpSingularSeriesRatiosProof.TwistedGoldbachConductorRatio

/-- Inverse evaluation at one admissible residue picks out its reflected residue
by character orthogonality, attaining the upper bound for the Jacobi matrix. -/
theorem local_operator_attained (D m : ℕ) [NeZero D] (he : Even m) :
    ∃ w : DirichletCharacter ℂ D → ℂ,
      0 < ∑ B, ‖w B‖^2 ∧
      (∑ A, ‖∑ B, J A B (m:ZMod D) * w B‖^2) =
        (D.totient:ℝ)^2 * ∑ B, ‖w B‖^2 := by
  classical
  obtain ⟨x,hx⟩ := admissible_even D m he
  let y := (m : ZMod D)-x
  have hy : IsUnit y := hx.2
  let w (B : DirichletCharacter ℂ D) := B y⁻¹
  have wn (B : DirichletCharacter ℂ D) : ‖w B‖ = 1 := by
    obtain ⟨u, hu⟩ := hy
    simp only [w, ← hu, ZMod.inv_coe_unit, B.unit_norm_eq_one]
  have row (A : DirichletCharacter ℂ D) :
      (∑ B, J A B (m:ZMod D) * w B) = A x * (D.totient:ℂ) := by
    calc
      _ = ∑ z : ZMod D, A z * (∑ B : DirichletCharacter ℂ D, B y⁻¹ * B ((m:ZMod D)-z)) := by
        simp only [J, sum_mul, w, mul_sum]
        rw [sum_comm]
        apply sum_congr rfl
        intro z _
        apply sum_congr rfl
        intro B _
        ring
      _ = _ := by
        simp_rw [DirichletCharacter.sum_char_inv_mul_char_eq ℂ hy]
        simp [y, mul_ite]
  refine ⟨w, ?_, ?_⟩
  · simp_rw [wn]
    simp
    exact Fintype.card_pos
  · have xn (A : DirichletCharacter ℂ D) : ‖A x‖ = 1 := A.unit_norm_eq_one hx.1.unit
    calc
      _ = ∑ A : DirichletCharacter ℂ D, (D.totient : ℝ)^2 * ‖w A‖^2 := by
        apply sum_congr rfl
        intro A _
        rw [row, norm_mul, xn, wn]
        simp
      _ = _ := (mul_sum _ _ _).symm

end SignedLevel

namespace SignedLevel
open Finset DirichletCharacter
open Conjectures.Goldbach.SharpSingularSeriesRatiosProof
open TwistedGoldbachConductorRatio TwistedGoldbachLocalProduct
open scoped Classical

private abbrev Partner := Σ s : ℕ, DirichletCharacter ℂ s

private noncomputable def origin {D : ℕ} (A : DirichletCharacter ℂ D) : Partner :=
  ⟨A.conductor, A.primitiveCharacter⟩

private theorem lift_eq {s t D : ℕ} (hs : s ∣ D) (ht : t ∣ D)
    (A : DirichletCharacter ℂ s) (B : DirichletCharacter ℂ t)
    (h : (⟨s,A⟩ : Partner) = ⟨t,B⟩) : changeLevel hs A = changeLevel ht B := by
  cases h
  rfl

private theorem origin_inj (D : ℕ) [NeZero D] :
    Function.Injective (origin (D := D)) := by
  intro A B h
  have e := lift_eq A.conductor_dvd_level B.conductor_dvd_level _ _ h
  simpa only [changeLevel_primitiveCharacter] using e

private theorem same_primitive {s t D : ℕ} [NeZero D] (a : DirichletCharacter ℂ s)
    (b : DirichletCharacter ℂ t) (hs : s ∣ D) (ht : t ∣ D)
    (ha : a.IsPrimitive) (hb : b.IsPrimitive) (h : changeLevel hs a = changeLevel ht b) :
    (⟨s,a⟩ : Partner) = ⟨t,b⟩ := by
  have e := congrArg DirichletCharacter.conductor h
  rw [conductor_changeLevel, conductor_changeLevel, ha, hb] at e
  subst t
  exact congrArg (Sigma.mk s) (changeLevel_injective hs h)

private theorem origin_mem (D : ℕ) [NeZero D] (b : Partner) :
    b ∈ (univ.image (origin (D := D))) ↔
      (b.1 ≠ 0 ∧ b.2.IsPrimitive) ∧ b.1 ∣ D := by
  simp only [mem_image, mem_univ, true_and]
  constructor
  · rintro ⟨A, rfl⟩
    exact ⟨⟨A.conductor_ne_zero,A.primitiveCharacter_isPrimitive⟩,A.conductor_dvd_level⟩
  · rcases b with ⟨s, χ⟩
    rintro ⟨⟨hs, prim⟩, hd⟩
    let _ : NeZero s := ⟨hs⟩
    let A := changeLevel hd χ
    exact ⟨A, same_primitive _ _ A.conductor_dvd_level hd A.primitiveCharacter_isPrimitive
      prim (changeLevel_primitiveCharacter A)⟩

private theorem scaled_operator {I B : Type*} [Fintype I] [Nonempty I] [DecidableEq B]
    (g : I → B) (hg : Function.Injective g) (K : B → B → ℂ) (J : I → I → ℂ)
    (c : ℂ) (t : ℝ) (hK : ∀ i j, K (g i) (g j) = c * J i j)
    (hu : ∀ u : I → ℂ, (∑ i, ‖∑ j, J i j * u j‖^2) ≤ t^2 * ∑ j, ‖u j‖^2)
    (hl : ∃ u : I → ℂ, 0 < ∑ j, ‖u j‖^2 ∧
      (∑ i, ‖∑ j, J i j * u j‖^2) = t^2 * ∑ j, ‖u j‖^2) :
    let F := univ.image g
    let mass (w : B → ℂ) := ∑ b ∈ F, ‖w b‖^2
    let applyRow (w : B → ℂ) (a : B) := ∑ b ∈ F, K a b * w b
    (∀ w : B → ℂ, mass (applyRow w) ≤ (‖c‖ * t)^2 * mass w) ∧
    ∃ w : B → ℂ, 0 < mass w ∧ mass (applyRow w) = (‖c‖ * t)^2 * mass w := by
  classical
  intro F mass applyRow
  have reindex (f : B → ℝ) : ∑ b ∈ F, f b = ∑ j : I, f (g j) :=
    sum_image hg.injOn
  have mass_eq (w : B → ℂ) : mass w = ∑ j : I, ‖w (g j)‖^2 := reindex _
  have row_eq (w : B → ℂ) (i : I) : applyRow w (g i) = c * ∑ j, J i j * w (g j) := by
    dsimp only [applyRow, F]
    rw [sum_image hg.injOn, mul_sum]
    apply sum_congr rfl
    intro j _
    rw [hK, mul_assoc]
  have lhs (w : B → ℂ) :
      mass (applyRow w) = ‖c‖^2 * ∑ i, ‖∑ j, J i j * w (g j)‖^2 := by
    rw [mass_eq, mul_sum]
    apply sum_congr rfl
    intro i _
    rw [row_eq, norm_mul, mul_pow]
  constructor
  · intro w
    rw [lhs, mass_eq, mul_pow, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hu (fun j => w (g j))) (sq_nonneg _)
  · obtain ⟨u, hpos, heq⟩ := hl
    let w (b : B) := u (Function.invFun g b)
    have hw (i : I) : w (g i) = u i := congrArg u (Function.leftInverse_invFun hg i)
    refine ⟨w, ?_, ?_⟩
    · simpa only [mass_eq, hw] using hpos
    · rw [lhs, mass_eq, mul_pow, mul_assoc]
      simp only [hw, heq]

end SignedLevel

open Finset DirichletCharacter SignedLevel
open Conjectures.Goldbach.SharpSingularSeriesRatiosProof
open TwistedGoldbachConductorRatio TwistedGoldbachLocalProduct

theorem Conjectures.Goldbach.PartnerLevelSignedOperator : (
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
  exact ∀ D m : ℕ, 0 < D → 0 < m → Even m → ∃ F : Finset B, (∀ b, b ∈ F ↔ valid b ∧ b.1 ∣ D) ∧ (let H := ((Finset.range D).filter (fun x => x.Coprime D ∧ (m+D-(Nat.mod x D)).Coprime D)).card; let scale := ‖O m‖*(D.totient:ℝ)/(H:ℝ); let normSq := fun w : B → ℂ => ∑ a ∈ F, ‖w a‖^2; let applyRow := fun (w : B → ℂ) (a : B) => ∑ b ∈ F, S a.2 b.2 m * w b; (∀ w : B → ℂ, normSq (applyRow w) ≤ scale^2 * normSq w) ∧ ∃ w : B → ℂ, 0 < normSq w ∧ normSq (applyRow w) = scale^2 * normSq w)
) := by
  classical
  dsimp only
  intro D m hD hm he
  let _ : NeZero D := ⟨hD.ne'⟩
  let H := ((Finset.range D).filter fun x => x.Coprime D ∧ (m+D-(Nat.mod x D)).Coprime D).card
  let O := series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m
  let c := O / (H : ℂ)
  let g := origin (D := D)
  let K := fun a b : Partner => series a.2 b.2 m
  have coefficient (A B : DirichletCharacter ℂ D) :
      K (g A) (g B) = c * J A B (m : ZMod D) := by
    let _ : NeZero A.conductor := ⟨A.conductor_ne_zero⟩
    let _ : NeZero B.conductor := ⟨B.conductor_ne_zero⟩
    have h := exact_ratio A.primitiveCharacter_isPrimitive B.primitiveCharacter_isPrimitive
      A.conductor_dvd_level B.conductor_dvd_level m hm he
    rw [changeLevel_primitiveCharacter, changeLevel_primitiveCharacter,
      ← PartnerOperatorCount.count_eq D m] at h
    change K (g A) (g B) = O * (J A B (m : ZMod D) / (H : ℂ)) at h
    rw [h]
    dsimp only [c]
    ring
  have scale : ‖c‖ * (D.totient : ℝ) = ‖O‖ * (D.totient : ℝ) / (H : ℝ) := by
    dsimp only [c]
    rw [norm_div, Complex.norm_natCast]
    ring
  refine ⟨Finset.univ.image g, origin_mem D, ?_⟩
  have bound := scaled_operator g (origin_inj D) K
    (fun A B => J A B (m : ZMod D)) c (D.totient : ℝ) coefficient
    (local_operator_le (m : ZMod D)) (local_operator_attained D m he)
  dsimp only at bound
  rw [scale] at bound
  exact bound
