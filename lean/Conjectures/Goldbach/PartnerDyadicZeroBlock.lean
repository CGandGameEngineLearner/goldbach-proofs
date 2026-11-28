import Mathlib
import Conjectures.Goldbach.PrimitivePartnerCubicMass

/-! All-conductor bilinear l^{6/5} singular-series bound and uniform dyadic-block
Beta-kernel estimate for the Pintz explicit-formula kernel.

Reuses `Conjectures.Goldbach.PrimitivePartnerCubicMass` (PR #4245) for the uniform
cubic row bound, and applies finite Holder interpolation together with stationary-phase
integration by parts on `Complex.betaIntegral`. -/

namespace PartnerDyadicZeroBlockProof

open Finset MeasureTheory intervalIntegral
open scoped BigOperators Classical

private noncomputable def Sfun {r s : ℕ} (α : DirichletCharacter ℂ r)
    (β : DirichletCharacter ℂ s) (m : ℕ) : ℂ :=
  ∑' q : ℕ, if hq : q ≠ 0 then
    let _ : NeZero q := ⟨hq⟩
    if h : r ∣ q ∧ s ∣ q then
      let A := DirichletCharacter.changeLevel h.1 α
      let B := DirichletCharacter.changeLevel h.2 β
      gaussSum A ZMod.stdAddChar * gaussSum B ZMod.stdAddChar *
        gaussSum (A * B)⁻¹ (ZMod.stdAddChar.mulShift (-(m : ZMod q))) / (q.totient : ℂ) ^ 2
    else 0
  else 0

private noncomputable def Ofun (m : ℕ) : ℂ :=
  Sfun (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m

private theorem Sfun_symm {r s : ℕ} (α : DirichletCharacter ℂ r)
    (β : DirichletCharacter ℂ s) (m : ℕ) :
    Sfun α β m = Sfun β α m := by
  unfold Sfun
  congr 1
  funext q
  by_cases hq : q ≠ 0
  · rw [dite_eq_left hq, dite_eq_left hq]
    haveI : NeZero q := ⟨hq⟩
    by_cases h : r ∣ q ∧ s ∣ q
    · have h' : s ∣ q ∧ r ∣ q := ⟨h.2, h.1⟩
      rw [dite_eq_left h, dite_eq_left h']
      dsimp only
      rw [mul_comm (DirichletCharacter.changeLevel h.1 α) (DirichletCharacter.changeLevel h.2 β),
        mul_comm (gaussSum (DirichletCharacter.changeLevel h.1 α) ZMod.stdAddChar)]
    · have h' : ¬ (s ∣ q ∧ r ∣ q) := fun ⟨hs, hr⟩ => h ⟨hr, hs⟩
      rw [dite_eq_right h, dite_eq_right h']
  · rw [dite_eq_right hq, dite_eq_right hq]

private theorem row_cubic_bound (m : ℕ) (hm : 0 < m) (he : Even m)
    (F : Finset (Σ s : ℕ, DirichletCharacter ℂ s))
    (hF : ∀ b ∈ F, b.1 ≠ 0 ∧ b.2.IsPrimitive)
    (a : Σ s : ℕ, DirichletCharacter ℂ s) (ha : a.1 ≠ 0 ∧ a.2.IsPrimitive) :
    (∑ b ∈ F, ‖Sfun a.2 b.2 m‖ ^ 3) ≤ 3 * ‖Ofun m‖ ^ 3 := by
  have : NeZero a.1 := ⟨ha.1⟩
  exact Conjectures.Goldbach.PrimitivePartnerCubicMass a.1 a.2 ha.2 m hm he F hF

private theorem col_cubic_bound (m : ℕ) (hm : 0 < m) (he : Even m)
    (F : Finset (Σ s : ℕ, DirichletCharacter ℂ s))
    (hF : ∀ b ∈ F, b.1 ≠ 0 ∧ b.2.IsPrimitive)
    (b : Σ s : ℕ, DirichletCharacter ℂ s) (hb : b.1 ≠ 0 ∧ b.2.IsPrimitive) :
    (∑ a ∈ F, ‖Sfun a.2 b.2 m‖ ^ 3) ≤ 3 * ‖Ofun m‖ ^ 3 := by
  calc
    (∑ a ∈ F, ‖Sfun a.2 b.2 m‖ ^ 3)
        = ∑ a ∈ F, ‖Sfun b.2 a.2 m‖ ^ 3 :=
          Finset.sum_congr rfl fun a _ => by rw [Sfun_symm]
    _ ≤ 3 * ‖Ofun m‖ ^ 3 := row_cubic_bound m hm he F hF b hb

private theorem rpow_split_nonneg {x : ℝ} (hx : 0 ≤ x) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    x ^ a * x ^ b = x ^ (a + b) := by
  rcases eq_or_lt_of_le hx with rfl | hpos
  · rw [Real.zero_rpow ha.ne', Real.zero_rpow hb.ne', Real.zero_rpow (by linarith), mul_zero]
  · exact (Real.rpow_add hpos a b).symm

private theorem bilinear_bound (m : ℕ) (hm : 0 < m) (he : Even m)
    (F : Finset (Σ s : ℕ, DirichletCharacter ℂ s))
    (hF : ∀ b ∈ F, b.1 ≠ 0 ∧ b.2.IsPrimitive)
    (u v : (Σ s : ℕ, DirichletCharacter ℂ s) → ℝ) :
    (∑ a ∈ F, ∑ b ∈ F, |u a| * ‖Sfun a.2 b.2 m‖ * |v b|) ≤
      (3 : ℝ) ^ (1 / 3 : ℝ) * ‖Ofun m‖ *
        (∑ a ∈ F, |u a| ^ (6 / 5 : ℝ)) ^ (5 / 6 : ℝ) *
        (∑ b ∈ F, |v b| ^ (6 / 5 : ℝ)) ^ (5 / 6 : ℝ) := by
  let B := Σ s : ℕ, DirichletCharacter ℂ s
  let s : Finset (B × B) := F ×ˢ F
  let p : B × B → ℝ := fun z => |u z.1| ^ (1 / 5 : ℝ) * ‖Sfun z.1.2 z.2.2 m‖ ^ (1 / 2 : ℝ)
  let q : B × B → ℝ := fun z => |v z.2| ^ (1 / 5 : ℝ) * ‖Sfun z.1.2 z.2.2 m‖ ^ (1 / 2 : ℝ)
  let r : B × B → ℝ := fun z => |u z.1| ^ (4 / 5 : ℝ) * |v z.2| ^ (4 / 5 : ℝ)
  have hp_nn (z : B × B) : 0 ≤ p z := mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _)
    (Real.rpow_nonneg (norm_nonneg _) _)
  have hq_nn (z : B × B) : 0 ≤ q z := mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _)
    (Real.rpow_nonneg (norm_nonneg _) _)
  have hr_nn (z : B × B) : 0 ≤ r z := mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _)
    (Real.rpow_nonneg (abs_nonneg _) _)
  have hfactor (z : B × B) :
      |u z.1| * ‖Sfun z.1.2 z.2.2 m‖ * |v z.2| = (p z * q z) * r z := by
    dsimp only [p, q, r]
    have hu : |u z.1| ^ (1 / 5 : ℝ) * |u z.1| ^ (4 / 5 : ℝ) = |u z.1| := by
      rw [rpow_split_nonneg (abs_nonneg _) (by norm_num) (by norm_num)]
      norm_num
    have hv : |v z.2| ^ (1 / 5 : ℝ) * |v z.2| ^ (4 / 5 : ℝ) = |v z.2| := by
      rw [rpow_split_nonneg (abs_nonneg _) (by norm_num) (by norm_num)]
      norm_num
    have hS : ‖Sfun z.1.2 z.2.2 m‖ ^ (1 / 2 : ℝ) * ‖Sfun z.1.2 z.2.2 m‖ ^ (1 / 2 : ℝ) =
        ‖Sfun z.1.2 z.2.2 m‖ := by
      rw [rpow_split_nonneg (norm_nonneg _) (by norm_num) (by norm_num)]
      norm_num
    calc
      |u z.1| * ‖Sfun z.1.2 z.2.2 m‖ * |v z.2|
          = (|u z.1| ^ (1 / 5 : ℝ) * |u z.1| ^ (4 / 5 : ℝ)) *
              (‖Sfun z.1.2 z.2.2 m‖ ^ (1 / 2 : ℝ) * ‖Sfun z.1.2 z.2.2 m‖ ^ (1 / 2 : ℝ)) *
              (|v z.2| ^ (1 / 5 : ℝ) * |v z.2| ^ (4 / 5 : ℝ)) := by rw [hu, hv, hS]
      _ = (|u z.1| ^ (1 / 5 : ℝ) * ‖Sfun z.1.2 z.2.2 m‖ ^ (1 / 2 : ℝ) *
            (|v z.2| ^ (1 / 5 : ℝ) * ‖Sfun z.1.2 z.2.2 m‖ ^ (1 / 2 : ℝ))) *
            (|u z.1| ^ (4 / 5 : ℝ) * |v z.2| ^ (4 / 5 : ℝ)) := by ring
  have hconj1 : Real.HolderConjugate (3 : ℝ) (3 / 2 : ℝ) := by
    constructor <;> norm_num
  have hconj2 : Real.HolderConjugate (2 : ℝ) (2 : ℝ) := by
    constructor <;> norm_num
  have h1 : (∑ z ∈ s, (p z * q z) * r z) ≤
      (∑ z ∈ s, (p z * q z) ^ (3 : ℝ)) ^ (1 / 3 : ℝ) *
        (∑ z ∈ s, r z ^ (3 / 2 : ℝ)) ^ (1 / (3 / 2 : ℝ)) :=
    Real.inner_le_Lp_mul_Lq_of_nonneg s hconj1
      (fun z _ => mul_nonneg (hp_nn z) (hq_nn z)) (fun z _ => hr_nn z)
  have h2 : (∑ z ∈ s, (p z * q z) ^ (3 : ℝ)) ≤
      (∑ z ∈ s, (p z ^ (3 : ℝ)) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) *
        (∑ z ∈ s, (q z ^ (3 : ℝ)) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
    have heq : (∑ z ∈ s, (p z * q z) ^ (3 : ℝ)) = ∑ z ∈ s, p z ^ (3 : ℝ) * q z ^ (3 : ℝ) :=
      Finset.sum_congr rfl fun z _ => Real.mul_rpow (hp_nn z) (hq_nn z)
    rw [heq]
    exact Real.inner_le_Lp_mul_Lq_of_nonneg s hconj2
      (fun z _ => Real.rpow_nonneg (hp_nn z) _) (fun z _ => Real.rpow_nonneg (hq_nn z) _)
  let U : ℝ := ∑ a ∈ F, |u a| ^ (6 / 5 : ℝ)
  let V : ℝ := ∑ b ∈ F, |v b| ^ (6 / 5 : ℝ)
  have hU_nn : 0 ≤ U := Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (abs_nonneg _) _
  have hV_nn : 0 ≤ V := Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (abs_nonneg _) _
  let M : ℝ := 3 * ‖Ofun m‖ ^ 3
  have hM_nn : 0 ≤ M := by positivity
  have hP : (∑ z ∈ s, (p z ^ (3 : ℝ)) ^ (2 : ℝ)) ≤ M * U := by
    have hterm (z : B × B) :
        (p z ^ (3 : ℝ)) ^ (2 : ℝ) = |u z.1| ^ (6 / 5 : ℝ) * ‖Sfun z.1.2 z.2.2 m‖ ^ 3 := by
      dsimp only [p]
      rw [← Real.rpow_mul (mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _)
        (Real.rpow_nonneg (norm_nonneg _) _)), show (3 : ℝ) * 2 = 6 by norm_num,
        Real.mul_rpow (Real.rpow_nonneg (abs_nonneg _) _) (Real.rpow_nonneg (norm_nonneg _) _),
        ← Real.rpow_mul (abs_nonneg _), ← Real.rpow_mul (norm_nonneg _)]
      norm_num
    calc
      (∑ z ∈ s, (p z ^ (3 : ℝ)) ^ (2 : ℝ))
          = ∑ a ∈ F, ∑ b ∈ F, |u a| ^ (6 / 5 : ℝ) * ‖Sfun a.2 b.2 m‖ ^ 3 := by
            rw [Finset.sum_product]
            exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => hterm (a, b)
      _ = ∑ a ∈ F, |u a| ^ (6 / 5 : ℝ) * ∑ b ∈ F, ‖Sfun a.2 b.2 m‖ ^ 3 :=
            Finset.sum_congr rfl fun a _ => (Finset.mul_sum _ _ _).symm
      _ ≤ ∑ a ∈ F, |u a| ^ (6 / 5 : ℝ) * M :=
            Finset.sum_le_sum fun a ha => mul_le_mul_of_nonneg_left
              (row_cubic_bound m hm he F hF a (hF a ha)) (Real.rpow_nonneg (abs_nonneg _) _)
      _ = M * U := by rw [← Finset.sum_mul, mul_comm]
  have hQ : (∑ z ∈ s, (q z ^ (3 : ℝ)) ^ (2 : ℝ)) ≤ M * V := by
    have hterm (z : B × B) :
        (q z ^ (3 : ℝ)) ^ (2 : ℝ) = |v z.2| ^ (6 / 5 : ℝ) * ‖Sfun z.1.2 z.2.2 m‖ ^ 3 := by
      dsimp only [q]
      rw [← Real.rpow_mul (mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _)
        (Real.rpow_nonneg (norm_nonneg _) _)), show (3 : ℝ) * 2 = 6 by norm_num,
        Real.mul_rpow (Real.rpow_nonneg (abs_nonneg _) _) (Real.rpow_nonneg (norm_nonneg _) _),
        ← Real.rpow_mul (abs_nonneg _), ← Real.rpow_mul (norm_nonneg _)]
      norm_num
    calc
      (∑ z ∈ s, (q z ^ (3 : ℝ)) ^ (2 : ℝ))
          = ∑ b ∈ F, ∑ a ∈ F, |v b| ^ (6 / 5 : ℝ) * ‖Sfun a.2 b.2 m‖ ^ 3 := by
            rw [Finset.sum_product_right]
            exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => hterm (a, b)
      _ = ∑ b ∈ F, |v b| ^ (6 / 5 : ℝ) * ∑ a ∈ F, ‖Sfun a.2 b.2 m‖ ^ 3 :=
            Finset.sum_congr rfl fun b _ => (Finset.mul_sum _ _ _).symm
      _ ≤ ∑ b ∈ F, |v b| ^ (6 / 5 : ℝ) * M :=
            Finset.sum_le_sum fun b hb => mul_le_mul_of_nonneg_left
              (col_cubic_bound m hm he F hF b (hF b hb)) (Real.rpow_nonneg (abs_nonneg _) _)
      _ = M * V := by rw [← Finset.sum_mul, mul_comm]
  have hR : (∑ z ∈ s, r z ^ (3 / 2 : ℝ)) = U * V := by
    have hterm (z : B × B) :
        r z ^ (3 / 2 : ℝ) = |u z.1| ^ (6 / 5 : ℝ) * |v z.2| ^ (6 / 5 : ℝ) := by
      dsimp only [r]
      rw [Real.mul_rpow (Real.rpow_nonneg (abs_nonneg _) _) (Real.rpow_nonneg (abs_nonneg _) _),
        ← Real.rpow_mul (abs_nonneg _), ← Real.rpow_mul (abs_nonneg _)]
      norm_num
    calc
      (∑ z ∈ s, r z ^ (3 / 2 : ℝ))
          = ∑ a ∈ F, ∑ b ∈ F, |u a| ^ (6 / 5 : ℝ) * |v b| ^ (6 / 5 : ℝ) := by
            rw [Finset.sum_product]
            exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => hterm (a, b)
      _ = U * V := by
            dsimp only [U, V]
            rw [Finset.sum_mul]
            exact Finset.sum_congr rfl fun a _ => (Finset.mul_sum _ _ _).symm
  have h2' : (∑ z ∈ s, (p z * q z) ^ (3 : ℝ)) ≤ (M * U) ^ (1 / 2 : ℝ) * (M * V) ^ (1 / 2 : ℝ) := by
    refine h2.trans (mul_le_mul ?_ ?_ (Real.rpow_nonneg (Finset.sum_nonneg fun _ _ =>
      Real.rpow_nonneg (Real.rpow_nonneg (hq_nn _) _) _) _) (Real.rpow_nonneg (mul_nonneg hM_nn hU_nn) _))
    · exact Real.rpow_le_rpow (Finset.sum_nonneg fun _ _ =>
        Real.rpow_nonneg (Real.rpow_nonneg (hp_nn _) _) _) hP (by norm_num)
    · exact Real.rpow_le_rpow (Finset.sum_nonneg fun _ _ =>
        Real.rpow_nonneg (Real.rpow_nonneg (hq_nn _) _) _) hQ (by norm_num)
  have h1' : (∑ z ∈ s, (p z * q z) ^ (3 : ℝ)) ^ (1 / 3 : ℝ) ≤
      ((M * U) ^ (1 / 2 : ℝ) * (M * V) ^ (1 / 2 : ℝ)) ^ (1 / 3 : ℝ) :=
    Real.rpow_le_rpow (Finset.sum_nonneg fun _ _ =>
      Real.rpow_nonneg (mul_nonneg (hp_nn _) (hq_nn _)) _) h2' (by norm_num)
  have hsum_eq : (∑ a ∈ F, ∑ b ∈ F, |u a| * ‖Sfun a.2 b.2 m‖ * |v b|) =
      ∑ z ∈ s, (p z * q z) * r z := by
    rw [Finset.sum_product]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => hfactor (a, b)
  rw [hsum_eq]
  calc
    (∑ z ∈ s, (p z * q z) * r z)
        ≤ (∑ z ∈ s, (p z * q z) ^ (3 : ℝ)) ^ (1 / 3 : ℝ) *
            (U * V) ^ (2 / 3 : ℝ) := by
          rw [hR, show (1 : ℝ) / (3 / 2 : ℝ) = 2 / 3 by norm_num] at h1
          exact h1
    _ ≤ ((M * U) ^ (1 / 2 : ℝ) * (M * V) ^ (1 / 2 : ℝ)) ^ (1 / 3 : ℝ) *
          (U * V) ^ (2 / 3 : ℝ) :=
          mul_le_mul_of_nonneg_right h1' (Real.rpow_nonneg (mul_nonneg hU_nn hV_nn) _)
    _ = (3 : ℝ) ^ (1 / 3 : ℝ) * ‖Ofun m‖ * U ^ (5 / 6 : ℝ) * V ^ (5 / 6 : ℝ) := by
          rw [Real.mul_rpow (Real.rpow_nonneg (mul_nonneg hM_nn hU_nn) _)
              (Real.rpow_nonneg (mul_nonneg hM_nn hV_nn) _),
            ← Real.rpow_mul (mul_nonneg hM_nn hU_nn),
            ← Real.rpow_mul (mul_nonneg hM_nn hV_nn),
            show (1 / 2 : ℝ) * (1 / 3 : ℝ) = 1 / 6 by norm_num,
            Real.mul_rpow hM_nn hU_nn, Real.mul_rpow hM_nn hV_nn,
            Real.mul_rpow hU_nn hV_nn]
          have hMpow : M ^ (1 / 6 : ℝ) * M ^ (1 / 6 : ℝ) = (3 : ℝ) ^ (1 / 3 : ℝ) * ‖Ofun m‖ := by
            rw [rpow_split_nonneg hM_nn (by norm_num) (by norm_num),
              show (1 / 6 : ℝ) + 1 / 6 = 1 / 3 by norm_num]
            dsimp only [M]
            rw [Real.mul_rpow (by norm_num) (pow_nonneg (norm_nonneg _) 3),
              ← Real.rpow_natCast ‖Ofun m‖ 3, ← Real.rpow_mul (norm_nonneg _)]
            norm_num
          have hUpow : U ^ (1 / 6 : ℝ) * U ^ (2 / 3 : ℝ) = U ^ (5 / 6 : ℝ) := by
            rw [rpow_split_nonneg hU_nn (by norm_num) (by norm_num)]
            norm_num
          have hVpow : V ^ (1 / 6 : ℝ) * V ^ (2 / 3 : ℝ) = V ^ (5 / 6 : ℝ) := by
            rw [rpow_split_nonneg hV_nn (by norm_num) (by norm_num)]
            norm_num
          calc
            M ^ (1 / 6 : ℝ) * U ^ (1 / 6 : ℝ) * (M ^ (1 / 6 : ℝ) * V ^ (1 / 6 : ℝ)) *
                (U ^ (2 / 3 : ℝ) * V ^ (2 / 3 : ℝ))
                = (M ^ (1 / 6 : ℝ) * M ^ (1 / 6 : ℝ)) * (U ^ (1 / 6 : ℝ) * U ^ (2 / 3 : ℝ)) *
                    (V ^ (1 / 6 : ℝ) * V ^ (2 / 3 : ℝ)) := by ring
            _ = (3 : ℝ) ^ (1 / 3 : ℝ) * ‖Ofun m‖ * U ^ (5 / 6 : ℝ) * V ^ (5 / 6 : ℝ) := by
                  rw [hMpow, hUpow, hVpow]

/-! ## Uniform Beta-integral estimate on the dyadic height block -/

private theorem mono_uIcc {E : Type*} [NormedAddCommGroup E] {f : ℝ → E} {a b c d : ℝ}
    (h : IntervalIntegrable f volume a b) (hab : a ≤ b) (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b) :
    IntervalIntegrable f volume c d :=
  h.mono_set (by rw [Set.uIcc_of_le hab, Set.uIcc_of_le hcd]; exact Set.Icc_subset_Icc hac hdb)

private theorem cont_rpow_x (p : ℝ) {u v : ℝ} (hu : 0 < u) :
    ContinuousOn (fun x : ℝ => x ^ p) (Set.Icc u v) :=
  ContinuousOn.rpow_const (f := fun x : ℝ => x) continuousOn_id
    (fun x hx => Or.inl (lt_of_lt_of_le hu hx.1).ne')

private theorem cont_rpow_one_sub (p : ℝ) {u v : ℝ} (hv : v < 1) :
    ContinuousOn (fun x : ℝ => (1 - x) ^ p) (Set.Icc u v) :=
  ContinuousOn.rpow_const (f := fun x : ℝ => 1 - x) (continuousOn_const.sub continuousOn_id)
    (fun x hx => Or.inl (sub_pos.mpr (lt_of_le_of_lt hx.2 hv)).ne')

private theorem rpow_neg_half_mul_self {x : ℝ} (hx : 0 < x) :
    x ^ (-(1 / 2 : ℝ)) * x = Real.sqrt x := by
  rw [Real.sqrt_eq_rpow]
  nth_rw 2 [← Real.rpow_one x]
  rw [← Real.rpow_add hx]
  norm_num

private theorem betaIntegrand_eq_polar (z₁ z₂ : ℂ) {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    (x : ℂ) ^ (z₁ - 1) * (1 - (x : ℂ)) ^ (z₂ - 1) =
      ((x ^ (z₁.re - 1) * (1 - x) ^ (z₂.re - 1) : ℝ) : ℂ) *
        Complex.exp (((z₁.im * Real.log x + z₂.im * Real.log (1 - x) : ℝ) : ℂ) * Complex.I) := by
  have hx1' : 0 < 1 - x := by linarith
  have h1 : (x : ℂ) ^ (z₁ - 1) =
      ((x ^ (z₁.re - 1) : ℝ) : ℂ) * Complex.exp (((z₁.im * Real.log x : ℝ) : ℂ) * Complex.I) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx0.ne'),
      ← Complex.ofReal_log hx0.le, Real.rpow_def_of_pos hx0, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    apply Complex.ext <;> simp [mul_comm]
  have h2 : (1 - (x : ℂ)) ^ (z₂ - 1) =
      (((1 - x) ^ (z₂.re - 1) : ℝ) : ℂ) *
        Complex.exp (((z₂.im * Real.log (1 - x) : ℝ) : ℂ) * Complex.I) := by
    have hsub : (1 : ℂ) - (x : ℂ) = ((1 - x : ℝ) : ℂ) := by push_cast; ring
    rw [hsub, Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx1'.ne'),
      ← Complex.ofReal_log hx1'.le, Real.rpow_def_of_pos hx1', Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    apply Complex.ext <;> simp [mul_comm]
  rw [h1, h2]
  have hexp :
      Complex.exp (((z₁.im * Real.log x : ℝ) : ℂ) * Complex.I) *
        Complex.exp (((z₂.im * Real.log (1 - x) : ℝ) : ℂ) * Complex.I) =
      Complex.exp (((z₁.im * Real.log x + z₂.im * Real.log (1 - x) : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  calc
    ((x ^ (z₁.re - 1) : ℝ) : ℂ) * Complex.exp (((z₁.im * Real.log x : ℝ) : ℂ) * Complex.I) *
        ((((1 - x) ^ (z₂.re - 1) : ℝ) : ℂ) *
          Complex.exp (((z₂.im * Real.log (1 - x) : ℝ) : ℂ) * Complex.I))
        = (((x ^ (z₁.re - 1) * (1 - x) ^ (z₂.re - 1) : ℝ) : ℂ)) *
            (Complex.exp (((z₁.im * Real.log x : ℝ) : ℂ) * Complex.I) *
              Complex.exp (((z₂.im * Real.log (1 - x) : ℝ) : ℂ) * Complex.I)) := by
          push_cast; ring
    _ = _ := by rw [hexp]

private theorem norm_betaIntegrand_le (z₁ z₂ : ℂ)
    (hre1 : 1 / 2 ≤ z₁.re ∧ z₁.re ≤ 1) (hre2 : 1 / 2 ≤ z₂.re ∧ z₂.re ≤ 1)
    {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    ‖(x : ℂ) ^ (z₁ - 1) * (1 - (x : ℂ)) ^ (z₂ - 1)‖ ≤
      x ^ (-(1 / 2 : ℝ)) * (1 - x) ^ (-(1 / 2 : ℝ)) := by
  have hx1' : 0 < 1 - x := by linarith
  rw [betaIntegrand_eq_polar z₁ z₂ hx0 hx1, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
    Complex.norm_real, Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg hx0.le _)
      (Real.rpow_nonneg hx1'.le _))]
  apply mul_le_mul
  · exact Real.rpow_le_rpow_of_exponent_ge hx0 hx1.le (by linarith)
  · exact Real.rpow_le_rpow_of_exponent_ge hx1' (by linarith) (by linarith)
  · exact Real.rpow_nonneg hx1'.le _
  · exact Real.rpow_nonneg hx0.le _

private theorem g_le_weight (z₁ z₂ : ℂ)
    (hre1 : 1 / 2 ≤ z₁.re ∧ z₁.re ≤ 1) (hre2 : 1 / 2 ≤ z₂.re ∧ z₂.re ≤ 1)
    {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    x ^ (z₁.re - 1) * (1 - x) ^ (z₂.re - 1) ≤ x ^ (-(1 / 2 : ℝ)) * (1 - x) ^ (-(1 / 2 : ℝ)) := by
  have hx1' : 0 < 1 - x := by linarith
  exact mul_le_mul (Real.rpow_le_rpow_of_exponent_ge hx0 hx1.le (by linarith))
    (Real.rpow_le_rpow_of_exponent_ge hx1' (by linarith) (by linarith))
    (Real.rpow_nonneg hx1'.le _) (Real.rpow_nonneg hx0.le _)

private theorem inv_sqrt_half_le_two : (1 / 2 : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 2 := by
  rw [Real.rpow_neg (by norm_num), ← Real.sqrt_eq_rpow]
  have hs : (1 / 2 : ℝ) ≤ Real.sqrt (1 / 2) := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 2), Real.sqrt_nonneg (1 / 2 : ℝ)]
  rw [inv_le_comm₀ (Real.sqrt_pos.mpr (by norm_num)) (by norm_num)]
  linarith

private theorem integral_inv_sqrt (a b : ℝ) :
    ∫ x in a..b, x ^ (-(1 / 2 : ℝ)) = 2 * Real.sqrt b - 2 * Real.sqrt a := by
  rw [integral_rpow (Or.inl (by norm_num : -(1 : ℝ) < -(1 / 2 : ℝ)))]
  have h1 : (-(1 / 2 : ℝ) + 1) = (1 / 2 : ℝ) := by norm_num
  rw [h1, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
  ring

private theorem integral_beta_weight_le (u v : ℝ) (hu : 0 < u) (huv : u ≤ v) (hv : v < 1) :
    ∫ x in u..v, x ^ (-(1 / 2 : ℝ)) * (1 - x) ^ (-(1 / 2 : ℝ)) ≤ 8 := by
  have hcont_l : ContinuousOn (fun x : ℝ => x ^ (-(1 / 2 : ℝ)) * (1 - x) ^ (-(1 / 2 : ℝ)))
      (Set.uIcc u v) := by
    rw [Set.uIcc_of_le huv]
    exact (cont_rpow_x _ hu).mul (cont_rpow_one_sub _ hv)
  have hcont_r1 : ContinuousOn (fun x : ℝ => 2 * x ^ (-(1 / 2 : ℝ))) (Set.uIcc u v) := by
    rw [Set.uIcc_of_le huv]
    exact continuousOn_const.mul (cont_rpow_x _ hu)
  have hcont_r2 : ContinuousOn (fun x : ℝ => 2 * (1 - x) ^ (-(1 / 2 : ℝ))) (Set.uIcc u v) := by
    rw [Set.uIcc_of_le huv]
    exact continuousOn_const.mul (cont_rpow_one_sub _ hv)
  have hdom : ∀ x ∈ Set.Icc u v,
      x ^ (-(1 / 2 : ℝ)) * (1 - x) ^ (-(1 / 2 : ℝ)) ≤
        2 * x ^ (-(1 / 2 : ℝ)) + 2 * (1 - x) ^ (-(1 / 2 : ℝ)) := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le hu hx.1
    have hx1 : 0 < 1 - x := sub_pos.mpr (lt_of_le_of_lt hx.2 hv)
    have hnn1 : 0 ≤ x ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hx0.le _
    have hnn2 : 0 ≤ (1 - x) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hx1.le _
    by_cases hhalf : x ≤ 1 / 2
    · have hpow : (1 - x) ^ (-(1 / 2 : ℝ)) ≤ 2 :=
        (Real.rpow_le_rpow_of_nonpos (by norm_num) (by linarith) (by norm_num)).trans
          inv_sqrt_half_le_two
      have hm := mul_le_mul_of_nonneg_left hpow hnn1
      linarith
    · have hpow : x ^ (-(1 / 2 : ℝ)) ≤ 2 :=
        (Real.rpow_le_rpow_of_nonpos (by norm_num) (by linarith) (by norm_num)).trans
          inv_sqrt_half_le_two
      have hm := mul_le_mul_of_nonneg_right hpow hnn2
      linarith
  have hle := intervalIntegral.integral_mono_on huv (hcont_l.intervalIntegrable (μ := MeasureTheory.volume))
    ((hcont_r1.add hcont_r2).intervalIntegrable (μ := MeasureTheory.volume)) hdom
  dsimp only [Pi.add_apply] at hle
  rw [intervalIntegral.integral_add (hcont_r1.intervalIntegrable (μ := MeasureTheory.volume))
      (hcont_r2.intervalIntegrable (μ := MeasureTheory.volume)),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_inv_sqrt u v,
    intervalIntegral.integral_comp_sub_left (fun y : ℝ => y ^ (-(1 / 2 : ℝ))) (1 : ℝ),
    integral_inv_sqrt (1 - v) (1 - u)] at hle
  have hsqv : Real.sqrt v ≤ 1 := by
    rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hv.le
  have hsq1u : Real.sqrt (1 - u) ≤ 1 := by
    calc Real.sqrt (1 - u) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt (by linarith)
      _ = 1 := Real.sqrt_one
  linarith [Real.sqrt_nonneg u, Real.sqrt_nonneg (1 - v)]

private theorem tail_left_bound (z₁ z₂ : ℂ)
    (hre1 : 1 / 2 ≤ z₁.re ∧ z₁.re ≤ 1) (hre2 : 1 / 2 ≤ z₂.re ∧ z₂.re ≤ 1)
    {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1 / 2) :
    ‖∫ x in (0 : ℝ)..a, (x : ℂ) ^ (z₁ - 1) * (1 - (x : ℂ)) ^ (z₂ - 1)‖ ≤ 4 * Real.sqrt a := by
  have hint : IntervalIntegrable (fun x : ℝ => (x : ℂ) ^ (z₁ - 1) * (1 - (x : ℂ)) ^ (z₂ - 1))
      volume 0 a :=
    mono_uIcc (Complex.betaIntegral_convergent (by linarith) (by linarith))
      (by norm_num) le_rfl ha0.le (by linarith)
  have hrhs : IntervalIntegrable (fun x : ℝ => 2 * x ^ (-(1 / 2 : ℝ))) volume 0 a :=
    (intervalIntegral.intervalIntegrable_rpow' (by norm_num)).const_mul 2
  have hdom : ∀ x ∈ Set.Ioo (0 : ℝ) a,
      ‖(x : ℂ) ^ (z₁ - 1) * (1 - (x : ℂ)) ^ (z₂ - 1)‖ ≤ 2 * x ^ (-(1 / 2 : ℝ)) := by
    intro x hx
    have h1 := norm_betaIntegrand_le z₁ z₂ hre1 hre2 hx.1 (by linarith [hx.2])
    have hpow : (1 - x) ^ (-(1 / 2 : ℝ)) ≤ 2 :=
      (Real.rpow_le_rpow_of_nonpos (by norm_num) (by linarith [hx.2]) (by norm_num)).trans
        inv_sqrt_half_le_two
    calc
      ‖(x : ℂ) ^ (z₁ - 1) * (1 - (x : ℂ)) ^ (z₂ - 1)‖
          ≤ x ^ (-(1 / 2 : ℝ)) * (1 - x) ^ (-(1 / 2 : ℝ)) := h1
      _ ≤ x ^ (-(1 / 2 : ℝ)) * 2 :=
            mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hx.1.le _)
      _ = 2 * x ^ (-(1 / 2 : ℝ)) := mul_comm _ _
  calc
    ‖∫ x in (0 : ℝ)..a, (x : ℂ) ^ (z₁ - 1) * (1 - (x : ℂ)) ^ (z₂ - 1)‖
        ≤ ∫ x in (0 : ℝ)..a, ‖(x : ℂ) ^ (z₁ - 1) * (1 - (x : ℂ)) ^ (z₂ - 1)‖ :=
          intervalIntegral.norm_integral_le_integral_norm ha0.le
    _ ≤ ∫ x in (0 : ℝ)..a, 2 * x ^ (-(1 / 2 : ℝ)) :=
          intervalIntegral.integral_mono_on_of_le_Ioo ha0.le hint.norm hrhs hdom
    _ = 4 * Real.sqrt a := by
          rw [intervalIntegral.integral_const_mul, integral_inv_sqrt 0 a, Real.sqrt_zero]
          ring

private theorem beta_sub_left_symm (z₁ z₂ : ℂ) (a b : ℝ) :
    (∫ x in a..b, (x : ℂ) ^ (z₁ - 1) * (1 - (x : ℂ)) ^ (z₂ - 1)) =
      ∫ y in (1 - b)..(1 - a), (y : ℂ) ^ (z₂ - 1) * (1 - (y : ℂ)) ^ (z₁ - 1) := by
  have hc := intervalIntegral.integral_comp_sub_left
    (fun y : ℝ => (y : ℂ) ^ (z₂ - 1) * (1 - (y : ℂ)) ^ (z₁ - 1)) (1 : ℝ) (a := a) (b := b)
  rw [← hc]
  apply intervalIntegral.integral_congr
  intro x _
  dsimp only
  simp only [Complex.ofReal_sub, Complex.ofReal_one, sub_sub_cancel]
  rw [mul_comm]

private theorem tail_right_bound (z₁ z₂ : ℂ)
    (hre1 : 1 / 2 ≤ z₁.re ∧ z₁.re ≤ 1) (hre2 : 1 / 2 ≤ z₂.re ∧ z₂.re ≤ 1)
    {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1 / 2) :
    ‖∫ x in (1 - a)..(1 : ℝ), (x : ℂ) ^ (z₁ - 1) * (1 - (x : ℂ)) ^ (z₂ - 1)‖ ≤ 4 * Real.sqrt a := by
  rw [beta_sub_left_symm z₁ z₂ (1 - a) 1]
  norm_num
  exact tail_left_bound z₂ z₁ hre2 hre1 ha0 ha1

private theorem g_deriv_bound (z₁ z₂ : ℂ)
    (hre1 : 1 / 2 ≤ z₁.re ∧ z₁.re ≤ 1) (hre2 : 1 / 2 ≤ z₂.re ∧ z₂.re ≤ 1)
    {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    |((z₁.re - 1) * x ^ (z₁.re - 2)) * (1 - x) ^ (z₂.re - 1) +
        x ^ (z₁.re - 1) * (-(z₂.re - 1) * (1 - x) ^ (z₂.re - 2))| ≤
      (x ^ (z₁.re - 1) * (1 - x) ^ (z₂.re - 1)) / (2 * x * (1 - x)) := by
  have hx1' : 0 < 1 - x := by linarith
  have h1 : x ^ (z₁.re - 2) = x ^ (z₁.re - 1) / x := by
    rw [show z₁.re - 2 = (z₁.re - 1) - 1 by ring, Real.rpow_sub_one hx0.ne']
  have h2 : (1 - x) ^ (z₂.re - 2) = (1 - x) ^ (z₂.re - 1) / (1 - x) := by
    rw [show z₂.re - 2 = (z₂.re - 1) - 1 by ring, Real.rpow_sub_one hx1'.ne']
  rw [h1, h2]
  let g := x ^ (z₁.re - 1) * (1 - x) ^ (z₂.re - 1)
  have hg_nn : 0 ≤ g := mul_nonneg (Real.rpow_nonneg hx0.le _) (Real.rpow_nonneg hx1'.le _)
  have hrew : ((z₁.re - 1) * (x ^ (z₁.re - 1) / x)) * (1 - x) ^ (z₂.re - 1) +
      x ^ (z₁.re - 1) * (-(z₂.re - 1) * ((1 - x) ^ (z₂.re - 1) / (1 - x))) =
      g * ((z₁.re - 1) / x - (z₂.re - 1) / (1 - x)) := by
    dsimp only [g]; field_simp [hx0.ne', hx1'.ne']; ring
  rw [hrew, abs_mul, abs_of_nonneg hg_nn]
  have habs : |(z₁.re - 1) / x - (z₂.re - 1) / (1 - x)| ≤ 1 / (2 * x * (1 - x)) := by
    have ha1 : |z₁.re - 1| ≤ 1 / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
    have ha2 : |z₂.re - 1| ≤ 1 / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
    have hsum := add_le_add (div_le_div_of_nonneg_right ha1 hx0.le)
      (div_le_div_of_nonneg_right ha2 hx1'.le)
    calc
      |(z₁.re - 1) / x - (z₂.re - 1) / (1 - x)|
          ≤ |(z₁.re - 1) / x| + |(z₂.re - 1) / (1 - x)| := abs_sub _ _
      _ = |z₁.re - 1| / x + |z₂.re - 1| / (1 - x) := by
            rw [abs_div, abs_div, abs_of_pos hx0, abs_of_pos hx1']
      _ ≤ (1 / 2) / x + (1 / 2) / (1 - x) := hsum
      _ = 1 / (2 * x * (1 - x)) := by field_simp [hx0.ne', hx1'.ne']; ring
  calc
    g * |(z₁.re - 1) / x - (z₂.re - 1) / (1 - x)|
        ≤ g * (1 / (2 * x * (1 - x))) := mul_le_mul_of_nonneg_left habs hg_nn
    _ = g / (2 * x * (1 - x)) := by ring

private theorem ibp_oscillatory_bound (z₁ z₂ : ℂ) {u v : ℝ}
    (hu0 : 0 < u) (huv : u ≤ v) (hv1 : v < 1)
    (hφ' : ∀ x ∈ Set.Icc u v, z₁.im / x - z₂.im / (1 - x) ≠ 0) :
    let g := fun x : ℝ => x ^ (z₁.re - 1) * (1 - x) ^ (z₂.re - 1)
    let g' := fun x : ℝ =>
      ((z₁.re - 1) * x ^ (z₁.re - 2)) * (1 - x) ^ (z₂.re - 1) +
        x ^ (z₁.re - 1) * (-(z₂.re - 1) * (1 - x) ^ (z₂.re - 2))
    let φ' := fun x : ℝ => z₁.im / x - z₂.im / (1 - x)
    let φ'' := fun x : ℝ => -(z₁.im / x ^ 2) - z₂.im / (1 - x) ^ 2
    ‖∫ x in u..v, (x : ℂ) ^ (z₁ - 1) * (1 - (x : ℂ)) ^ (z₂ - 1)‖ ≤
      |g v / φ' v| + |g u / φ' u| +
        ∫ x in u..v, (|g' x| / |φ' x| + g x * |φ'' x| / (φ' x) ^ 2) := by
  intro g g' φ' φ''
  let φ : ℝ → ℝ := fun x => z₁.im * Real.log x + z₂.im * Real.log (1 - x)
  let h : ℝ → ℝ := fun x => g x / φ' x
  let h' : ℝ → ℝ := fun x => (g' x * φ' x - g x * φ'' x) / (φ' x) ^ 2
  let U : ℝ → ℂ := fun x => ((h x : ℝ) : ℂ) / Complex.I
  let U' : ℝ → ℂ := fun x => ((h' x : ℝ) : ℂ) / Complex.I
  let V : ℝ → ℂ := fun x => Complex.exp ((φ x : ℂ) * Complex.I)
  let V' : ℝ → ℂ := fun x => (((φ' x : ℝ) : ℂ) * Complex.I) * Complex.exp ((φ x : ℂ) * Complex.I)
  have hsub1 (x : ℝ) : HasDerivAt (fun t : ℝ => 1 - t) (-1) x :=
    (hasDerivAt_id x).const_sub (1 : ℝ)
  have hdg (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) : HasDerivAt g (g' x) x := by
    have hx1' : 0 < 1 - x := by linarith
    have h1 : HasDerivAt (fun t : ℝ => t ^ (z₁.re - 1)) ((z₁.re - 1) * x ^ (z₁.re - 2)) x := by
      have ha := Real.hasDerivAt_rpow_const (Or.inl hx0.ne') (p := z₁.re - 1)
      have heq : (z₁.re - 1) * x ^ (z₁.re - 1 - 1) = (z₁.re - 1) * x ^ (z₁.re - 2) := by
        congr 2; ring
      rwa [heq] at ha
    have h2 : HasDerivAt (fun t : ℝ => (1 - t) ^ (z₂.re - 1))
        (-(z₂.re - 1) * (1 - x) ^ (z₂.re - 2)) x := by
      have hb : HasDerivAt (fun y : ℝ => y ^ (z₂.re - 1))
          ((z₂.re - 1) * (1 - x) ^ (z₂.re - 1 - 1)) (1 - x) :=
        Real.hasDerivAt_rpow_const (Or.inl hx1'.ne') (p := z₂.re - 1)
      have hc := hb.comp x (hsub1 x)
      have heq : (z₂.re - 1) * (1 - x) ^ (z₂.re - 1 - 1) * -1 =
          -(z₂.re - 1) * (1 - x) ^ (z₂.re - 2) := by
        rw [show z₂.re - 1 - 1 = z₂.re - 2 by ring]; ring
      rwa [heq] at hc
    exact h1.mul h2
  have hdφ (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) : HasDerivAt φ (φ' x) x := by
    have hx1' : 0 < 1 - x := by linarith
    have h1 : HasDerivAt (fun t : ℝ => z₁.im * Real.log t) (z₁.im / x) x := by
      have ha := (Real.hasDerivAt_log hx0.ne').const_mul z₁.im
      have heq : z₁.im * x⁻¹ = z₁.im / x := by ring
      rwa [heq] at ha
    have h2 : HasDerivAt (fun t : ℝ => z₂.im * Real.log (1 - t)) (-(z₂.im / (1 - x))) x := by
      have hb := ((Real.hasDerivAt_log hx1'.ne').comp x (hsub1 x)).const_mul z₂.im
      have heq : z₂.im * ((1 - x)⁻¹ * -1) = -(z₂.im / (1 - x)) := by ring
      rwa [heq] at hb
    have hadd := h1.add h2
    have heq : z₁.im / x + -(z₂.im / (1 - x)) = φ' x := by dsimp only [φ']; ring
    rwa [heq] at hadd
  have hdφ' (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) : HasDerivAt φ' (φ'' x) x := by
    have hx1' : 0 < 1 - x := by linarith
    have h1 : HasDerivAt (fun t : ℝ => z₁.im / t) (-(z₁.im / x ^ 2)) x := by
      have hi := (hasDerivAt_inv hx0.ne').const_mul z₁.im
      have hfun : (fun t : ℝ => z₁.im * t⁻¹) = (fun t : ℝ => z₁.im / t) := by funext t; ring
      rw [hfun] at hi
      have heq : z₁.im * -(x ^ 2)⁻¹ = -(z₁.im / x ^ 2) := by ring
      rwa [heq] at hi
    have h2 : HasDerivAt (fun t : ℝ => z₂.im / (1 - t)) (z₂.im / (1 - x) ^ 2) x := by
      have hi := ((hasDerivAt_inv hx1'.ne').comp x (hsub1 x)).const_mul z₂.im
      have hfun : (fun t : ℝ => z₂.im * ((fun y : ℝ => y⁻¹) ∘ fun s : ℝ => 1 - s) t) =
          (fun t : ℝ => z₂.im / (1 - t)) := by funext t; simp [div_eq_mul_inv]
      rw [hfun] at hi
      have heq : z₂.im * (-((1 - x) ^ 2)⁻¹ * -1) = z₂.im / (1 - x) ^ 2 := by ring
      rwa [heq] at hi
    exact h1.sub h2
  have hdU (x : ℝ) (hx : x ∈ Set.uIcc u v) : HasDerivAt U (U' x) x := by
    rw [Set.uIcc_of_le huv] at hx
    have hx0 : 0 < x := lt_of_lt_of_le hu0 hx.1
    have hx1 : x < 1 := lt_of_le_of_lt hx.2 hv1
    have hdh : HasDerivAt h (h' x) x := (hdg x hx0 hx1).div (hdφ' x hx0 hx1) (hφ' x hx)
    exact (hdh.ofReal_comp).div_const Complex.I
  have hdV (x : ℝ) (hx : x ∈ Set.uIcc u v) : HasDerivAt V (V' x) x := by
    rw [Set.uIcc_of_le huv] at hx
    have hx0 : 0 < x := lt_of_lt_of_le hu0 hx.1
    have hx1 : x < 1 := lt_of_le_of_lt hx.2 hv1
    have hmul : HasDerivAt (fun t : ℝ => ((φ t : ℝ) : ℂ) * Complex.I)
        (((φ' x : ℝ) : ℂ) * Complex.I) x :=
      (hdφ x hx0 hx1).ofReal_comp.mul_const Complex.I
    have hc := (Complex.hasDerivAt_exp _).comp x hmul
    have heq : Complex.exp ((φ x : ℂ) * Complex.I) * (((φ' x : ℝ) : ℂ) * Complex.I) = V' x := by
      dsimp only [V']; ring
    rwa [heq] at hc
  have hcont_g : ContinuousOn g (Set.Icc u v) := fun x hx =>
    (hdg x (lt_of_lt_of_le hu0 hx.1) (lt_of_le_of_lt hx.2 hv1)).continuousAt.continuousWithinAt
  have hcont_g' : ContinuousOn g' (Set.Icc u v) :=
    ((continuousOn_const.mul (cont_rpow_x _ hu0)).mul (cont_rpow_one_sub _ hv1)).add
      ((cont_rpow_x _ hu0).mul (continuousOn_const.mul (cont_rpow_one_sub _ hv1)))
  have hcont_φ' : ContinuousOn φ' (Set.Icc u v) := fun x hx =>
    (hdφ' x (lt_of_lt_of_le hu0 hx.1) (lt_of_le_of_lt hx.2 hv1)).continuousAt.continuousWithinAt
  have hcont_φ'' : ContinuousOn φ'' (Set.Icc u v) := by
    have h1 : ContinuousOn (fun x : ℝ => z₁.im / x ^ 2) (Set.Icc u v) :=
      continuousOn_const.div (continuousOn_id.pow 2) fun x hx =>
        pow_ne_zero 2 (lt_of_lt_of_le hu0 hx.1).ne'
    have h2 : ContinuousOn (fun x : ℝ => z₂.im / (1 - x) ^ 2) (Set.Icc u v) :=
      continuousOn_const.div ((continuousOn_const.sub continuousOn_id).pow 2) fun x hx =>
        pow_ne_zero 2 (sub_pos.mpr (lt_of_le_of_lt hx.2 hv1)).ne'
    exact h1.neg.sub h2
  have hcont_h' : ContinuousOn h' (Set.Icc u v) :=
    ((hcont_g'.mul hcont_φ').sub (hcont_g.mul hcont_φ'')).div (hcont_φ'.pow 2)
      fun x hx => pow_ne_zero 2 (hφ' x hx)
  have hcont_U' : ContinuousOn U' (Set.uIcc u v) := by
    rw [Set.uIcc_of_le huv]
    exact (Complex.continuous_ofReal.comp_continuousOn hcont_h').div_const Complex.I
  have hcont_V' : ContinuousOn V' (Set.uIcc u v) := by
    rw [Set.uIcc_of_le huv]
    have hcont_φ : ContinuousOn φ (Set.Icc u v) := fun x hx =>
      (hdφ x (lt_of_lt_of_le hu0 hx.1) (lt_of_le_of_lt hx.2 hv1)).continuousAt.continuousWithinAt
    exact ((Complex.continuous_ofReal.comp_continuousOn hcont_φ').mul continuousOn_const).mul
      (Complex.continuous_exp.comp_continuousOn
        ((Complex.continuous_ofReal.comp_continuousOn hcont_φ).mul continuousOn_const))
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hdU hdV
    hcont_U'.intervalIntegrable hcont_V'.intervalIntegrable
  have heq_int :
      (∫ x in u..v, (x : ℂ) ^ (z₁ - 1) * (1 - (x : ℂ)) ^ (z₂ - 1)) =
        ∫ x in u..v, U x * V' x := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le huv] at hx
    have hx0 : 0 < x := lt_of_lt_of_le hu0 hx.1
    have hx1 : x < 1 := lt_of_le_of_lt hx.2 hv1
    dsimp only
    rw [betaIntegrand_eq_polar z₁ z₂ hx0 hx1]
    dsimp only [U, V', h, g, φ]
    have hφne : ((φ' x : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hφ' x hx)
    have hIne : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
    push_cast
    field_simp [hφne, hIne]
  rw [heq_int, hibp]
  have hUV_norm (x : ℝ) : ‖U x * V x‖ = |h x| := by
    dsimp only [U, V]
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, norm_div, Complex.norm_I, div_one,
      Complex.norm_real, Real.norm_eq_abs]
  have hU'V_norm (x : ℝ) (hx : x ∈ Set.Icc u v) :
      ‖U' x * V x‖ ≤ |g' x| / |φ' x| + g x * |φ'' x| / (φ' x) ^ 2 := by
    dsimp only [U', V]
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, norm_div, Complex.norm_I, div_one,
      Complex.norm_real, Real.norm_eq_abs]
    have hx0 : 0 < x := lt_of_lt_of_le hu0 hx.1
    have hx1 : x < 1 := lt_of_le_of_lt hx.2 hv1
    have hg_nn : 0 ≤ g x := mul_nonneg (Real.rpow_nonneg hx0.le _) (Real.rpow_nonneg (by linarith) _)
    have hφne : φ' x ≠ 0 := hφ' x hx
    have hrew : h' x = g' x / φ' x - g x * φ'' x / (φ' x) ^ 2 := by
      dsimp only [h']
      field_simp [hφne]
    rw [hrew]
    calc
      |g' x / φ' x - g x * φ'' x / (φ' x) ^ 2|
          ≤ |g' x / φ' x| + |g x * φ'' x / (φ' x) ^ 2| := abs_sub _ _
      _ = |g' x| / |φ' x| + g x * |φ'' x| / (φ' x) ^ 2 := by
            rw [abs_div, abs_div, abs_mul, abs_of_nonneg hg_nn, abs_of_nonneg (sq_nonneg (φ' x))]
  have hcont_rhs : ContinuousOn (fun x => |g' x| / |φ' x| + g x * |φ'' x| / (φ' x) ^ 2)
      (Set.uIcc u v) := by
    rw [Set.uIcc_of_le huv]
    exact (hcont_g'.abs.div hcont_φ'.abs fun x hx => abs_ne_zero.mpr (hφ' x hx)).add
      ((hcont_g.mul hcont_φ''.abs).div (hcont_φ'.pow 2) fun x hx => pow_ne_zero 2 (hφ' x hx))
  have hcont_U'V : ContinuousOn (fun x => U' x * V x) (Set.uIcc u v) := by
    have hcont_V : ContinuousOn V (Set.uIcc u v) := by
      rw [Set.uIcc_of_le huv]
      have hcont_φ : ContinuousOn φ (Set.Icc u v) := fun x hx =>
        (hdφ x (lt_of_lt_of_le hu0 hx.1) (lt_of_le_of_lt hx.2 hv1)).continuousAt.continuousWithinAt
      exact Complex.continuous_exp.comp_continuousOn
        ((Complex.continuous_ofReal.comp_continuousOn hcont_φ).mul continuousOn_const)
    exact hcont_U'.mul hcont_V
  have htri : ‖U v * V v - U u * V u - ∫ x in u..v, U' x * V x‖ ≤
      ‖U v * V v‖ + ‖U u * V u‖ + ‖∫ x in u..v, U' x * V x‖ := by
    have t1 := norm_sub_le (U v * V v - U u * V u) (∫ x in u..v, U' x * V x)
    have t2 := norm_sub_le (U v * V v) (U u * V u)
    linarith
  have hint_le : ‖∫ x in u..v, U' x * V x‖ ≤
      ∫ x in u..v, (|g' x| / |φ' x| + g x * |φ'' x| / (φ' x) ^ 2) := by
    calc
      ‖∫ x in u..v, U' x * V x‖
          ≤ ∫ x in u..v, ‖U' x * V x‖ := intervalIntegral.norm_integral_le_integral_norm huv
      _ ≤ ∫ x in u..v, (|g' x| / |φ' x| + g x * |φ'' x| / (φ' x) ^ 2) :=
            intervalIntegral.integral_mono_on huv hcont_U'V.norm.intervalIntegrable
              hcont_rhs.intervalIntegrable fun x hx => hU'V_norm x hx
  rw [hUV_norm v, hUV_norm u] at htri
  exact htri.trans (by linarith)

private theorem beta_opposite_sign_bound (z₁ z₂ : ℂ) {T : ℝ} (hT : 1 ≤ T)
    (hre1 : 1 / 2 ≤ z₁.re ∧ z₁.re ≤ 1) (hre2 : 1 / 2 ≤ z₂.re ∧ z₂.re ≤ 1)
    (him1 : T ≤ z₁.im ∧ z₁.im ≤ 2 * T) (him2 : -2 * T ≤ z₂.im ∧ z₂.im ≤ -T) :
    ‖Complex.betaIntegral z₁ z₂‖ ≤ 40 / Real.sqrt T := by
  have hTpos : 0 < T := by linarith
  have hsqTpos : 0 < Real.sqrt T := Real.sqrt_pos.mpr hTpos
  have hsqT_le_T : Real.sqrt T ≤ T := by
    nlinarith [Real.sq_sqrt hTpos.le, sq_nonneg (Real.sqrt T - 1)]
  let a : ℝ := 1 / (8 * T)
  have ha0 : 0 < a := by dsimp [a]; positivity
  have ha_le : a ≤ 1 / 8 := by
    dsimp [a]; rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hsqa : 4 * Real.sqrt a ≤ 2 / Real.sqrt T := by
    have hsq : Real.sqrt a = 1 / (Real.sqrt 8 * Real.sqrt T) := by
      dsimp only [a]; rw [Real.sqrt_div (by norm_num), Real.sqrt_one, Real.sqrt_mul (by norm_num)]
    rw [hsq]
    have h8 : (2 : ℝ) ≤ Real.sqrt 8 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 8), Real.sqrt_nonneg 8]
    rw [show 4 * (1 / (Real.sqrt 8 * Real.sqrt T)) = (4 / Real.sqrt 8) / Real.sqrt T by ring]
    apply div_le_div_of_nonneg_right _ hsqTpos.le
    rw [div_le_iff₀ (by linarith)]; linarith
  have hconv := Complex.betaIntegral_convergent (u := z₁) (v := z₂) (by linarith) (by linarith)
  have h0a : IntervalIntegrable (fun x : ℝ => (x : ℂ) ^ (z₁ - 1) * (1 - (x : ℂ)) ^ (z₂ - 1))
      volume 0 a := mono_uIcc hconv (by norm_num) le_rfl ha0.le (by linarith)
  have ham : IntervalIntegrable (fun x : ℝ => (x : ℂ) ^ (z₁ - 1) * (1 - (x : ℂ)) ^ (z₂ - 1))
      volume a (1 - a) := mono_uIcc hconv (by norm_num) ha0.le (by linarith) (by linarith)
  have ha1 : IntervalIntegrable (fun x : ℝ => (x : ℂ) ^ (z₁ - 1) * (1 - (x : ℂ)) ^ (z₂ - 1))
      volume (1 - a) 1 := mono_uIcc hconv (by norm_num) (by linarith) (by linarith) le_rfl
  have hsplit : Complex.betaIntegral z₁ z₂ =
      (∫ x in (0 : ℝ)..a, (x : ℂ) ^ (z₁ - 1) * (1 - (x : ℂ)) ^ (z₂ - 1)) +
      (∫ x in a..(1 - a), (x : ℂ) ^ (z₁ - 1) * (1 - (x : ℂ)) ^ (z₂ - 1)) +
      (∫ x in (1 - a)..(1 : ℝ), (x : ℂ) ^ (z₁ - 1) * (1 - (x : ℂ)) ^ (z₂ - 1)) := by
    unfold Complex.betaIntegral
    rw [← intervalIntegral.integral_add_adjacent_intervals (h0a.trans ham) ha1,
      ← intervalIntegral.integral_add_adjacent_intervals h0a ham]
  have hleft := (tail_left_bound z₁ z₂ hre1 hre2 ha0 (by linarith)).trans hsqa
  have hright := (tail_right_bound z₁ z₂ hre1 hre2 ha0 (by linarith)).trans hsqa
  have hφ'_lb : ∀ x ∈ Set.Icc a (1 - a), T / (x * (1 - x)) ≤ z₁.im / x - z₂.im / (1 - x) := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le ha0 hx.1
    have hx1 : 0 < 1 - x := by linarith [hx.2]
    have h1 : T / x ≤ z₁.im / x := div_le_div_of_nonneg_right him1.1 hx0.le
    have h2 : T / (1 - x) ≤ -z₂.im / (1 - x) := div_le_div_of_nonneg_right (by linarith) hx1.le
    have hid : T / (x * (1 - x)) = T / x + T / (1 - x) := by field_simp [hx0.ne', hx1.ne']; ring
    linarith [show -z₂.im / (1 - x) = -(z₂.im / (1 - x)) by ring]
  have hφ'_ne : ∀ x ∈ Set.Icc a (1 - a), z₁.im / x - z₂.im / (1 - x) ≠ 0 := fun x hx => by
    have hx0 : 0 < x := lt_of_lt_of_le ha0 hx.1
    have hx1 : 0 < 1 - x := by linarith [hx.2]
    have hpos : 0 < T / (x * (1 - x)) := by positivity
    linarith [hφ'_lb x hx]
  have hibp := ibp_oscillatory_bound z₁ z₂ ha0 (by linarith) (by linarith) hφ'_ne
  dsimp only at hibp
  have hbdy (x : ℝ) (hx : x ∈ Set.Icc a (1 - a)) :
      |x ^ (z₁.re - 1) * (1 - x) ^ (z₂.re - 1) / (z₁.im / x - z₂.im / (1 - x))| ≤ 1 / Real.sqrt T := by
    have hx0 : 0 < x := lt_of_lt_of_le ha0 hx.1
    have hx1 : 0 < 1 - x := by linarith [hx.2]
    have hφpos : 0 < z₁.im / x - z₂.im / (1 - x) := lt_of_lt_of_le (by positivity) (hφ'_lb x hx)
    rw [abs_of_nonneg (div_nonneg (mul_nonneg (Real.rpow_nonneg hx0.le _)
      (Real.rpow_nonneg hx1.le _)) hφpos.le)]
    have hg := g_le_weight z₁ z₂ hre1 hre2 hx0 (by linarith)
    have hinv : x ^ (-(1 / 2 : ℝ)) * (1 - x) ^ (-(1 / 2 : ℝ)) / (T / (x * (1 - x))) ≤ 1 / T := by
      have hrew : x ^ (-(1 / 2 : ℝ)) * (1 - x) ^ (-(1 / 2 : ℝ)) / (T / (x * (1 - x))) =
          (Real.sqrt x * Real.sqrt (1 - x)) / T := by
        rw [div_div_eq_mul_div, ← rpow_neg_half_mul_self hx0, ← rpow_neg_half_mul_self hx1]; ring
      rw [hrew]
      apply div_le_div_of_nonneg_right _ hTpos.le
      have hs1 : Real.sqrt x ≤ 1 := by
        calc Real.sqrt x ≤ Real.sqrt 1 := Real.sqrt_le_sqrt (by linarith)
          _ = 1 := Real.sqrt_one
      have hs2 : Real.sqrt (1 - x) ≤ 1 := by
        calc Real.sqrt (1 - x) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt (by linarith)
          _ = 1 := Real.sqrt_one
      nlinarith [Real.sqrt_nonneg x, Real.sqrt_nonneg (1 - x)]
    have hstep1 : x ^ (z₁.re - 1) * (1 - x) ^ (z₂.re - 1) / (z₁.im / x - z₂.im / (1 - x)) ≤
        x ^ (-(1 / 2 : ℝ)) * (1 - x) ^ (-(1 / 2 : ℝ)) / (T / (x * (1 - x))) :=
      div_le_div₀ (mul_nonneg (Real.rpow_nonneg hx0.le _) (Real.rpow_nonneg hx1.le _))
        hg (by positivity) (hφ'_lb x hx)
    exact (hstep1.trans hinv).trans (one_div_le_one_div_of_le hsqTpos hsqT_le_T)
  have hmid_int :
      (∫ x in a..(1 - a),
        (|((z₁.re - 1) * x ^ (z₁.re - 2)) * (1 - x) ^ (z₂.re - 1) +
            x ^ (z₁.re - 1) * (-(z₂.re - 1) * (1 - x) ^ (z₂.re - 2))| /
          |z₁.im / x - z₂.im / (1 - x)| +
          x ^ (z₁.re - 1) * (1 - x) ^ (z₂.re - 1) *
            |-(z₁.im / x ^ 2) - z₂.im / (1 - x) ^ 2| / (z₁.im / x - z₂.im / (1 - x)) ^ 2)) ≤
        20 / Real.sqrt T := by
    have hpt : ∀ x ∈ Set.Icc a (1 - a),
        |((z₁.re - 1) * x ^ (z₁.re - 2)) * (1 - x) ^ (z₂.re - 1) +
            x ^ (z₁.re - 1) * (-(z₂.re - 1) * (1 - x) ^ (z₂.re - 2))| /
          |z₁.im / x - z₂.im / (1 - x)| +
          x ^ (z₁.re - 1) * (1 - x) ^ (z₂.re - 1) *
            |-(z₁.im / x ^ 2) - z₂.im / (1 - x) ^ 2| / (z₁.im / x - z₂.im / (1 - x)) ^ 2 ≤
          (5 / (2 * T)) * (x ^ (-(1 / 2 : ℝ)) * (1 - x) ^ (-(1 / 2 : ℝ))) := by
      intro x hx
      have hx0 : 0 < x := lt_of_lt_of_le ha0 hx.1
      have hx1 : 0 < 1 - x := by linarith [hx.2]
      have hφlb := hφ'_lb x hx
      have hφpos : 0 < z₁.im / x - z₂.im / (1 - x) := lt_of_lt_of_le (by positivity) hφlb
      have hg := g_le_weight z₁ z₂ hre1 hre2 hx0 (by linarith)
      have hterm1 :
          |((z₁.re - 1) * x ^ (z₁.re - 2)) * (1 - x) ^ (z₂.re - 1) +
              x ^ (z₁.re - 1) * (-(z₂.re - 1) * (1 - x) ^ (z₂.re - 2))| /
            |z₁.im / x - z₂.im / (1 - x)| ≤
            (1 / (2 * T)) * (x ^ (-(1 / 2 : ℝ)) * (1 - x) ^ (-(1 / 2 : ℝ))) := by
        rw [abs_of_pos hφpos]
        have hd := g_deriv_bound z₁ z₂ hre1 hre2 hx0 (by linarith)
        have hstep := div_le_div₀ (by positivity) hd (by positivity) hφlb
        have hsimp : (x ^ (z₁.re - 1) * (1 - x) ^ (z₂.re - 1)) / (2 * x * (1 - x)) /
            (T / (x * (1 - x))) =
            (1 / (2 * T)) * (x ^ (z₁.re - 1) * (1 - x) ^ (z₂.re - 1)) := by
          field_simp [hx0.ne', hx1.ne', hTpos.ne']
        rw [hsimp] at hstep
        exact hstep.trans (mul_le_mul_of_nonneg_left hg (by positivity))
      have hterm2 :
          x ^ (z₁.re - 1) * (1 - x) ^ (z₂.re - 1) *
              |-(z₁.im / x ^ 2) - z₂.im / (1 - x) ^ 2| / (z₁.im / x - z₂.im / (1 - x)) ^ 2 ≤
            (2 / T) * (x ^ (-(1 / 2 : ℝ)) * (1 - x) ^ (-(1 / 2 : ℝ))) := by
        have hφ''_le : |-(z₁.im / x ^ 2) - z₂.im / (1 - x) ^ 2| ≤
            2 * T / (x ^ 2 * (1 - x) ^ 2) := by
          have ha1 : |z₁.im / x ^ 2| ≤ 2 * T / x ^ 2 := by
            rw [abs_div, abs_of_pos (sq_pos_of_pos hx0), abs_of_pos (by linarith)]
            exact div_le_div_of_nonneg_right him1.2 (sq_nonneg x)
          have ha2 : |z₂.im / (1 - x) ^ 2| ≤ 2 * T / (1 - x) ^ 2 := by
            rw [abs_div, abs_of_pos (sq_pos_of_pos hx1), abs_of_neg (by linarith)]
            exact div_le_div_of_nonneg_right (by linarith) (sq_nonneg _)
          have hsum_le : 2 * T / x ^ 2 + 2 * T / (1 - x) ^ 2 ≤ 2 * T / (x ^ 2 * (1 - x) ^ 2) := by
            have hid : 2 * T / x ^ 2 + 2 * T / (1 - x) ^ 2 =
                2 * T * ((1 - x) ^ 2 + x ^ 2) / (x ^ 2 * (1 - x) ^ 2) := by
              field_simp [hx0.ne', hx1.ne']
            rw [hid]
            apply div_le_div_of_nonneg_right _ (by positivity)
            have h1 : (1 - x) ^ 2 + x ^ 2 ≤ 1 := by nlinarith
            nlinarith
          calc
            |-(z₁.im / x ^ 2) - z₂.im / (1 - x) ^ 2|
                ≤ |-(z₁.im / x ^ 2)| + |z₂.im / (1 - x) ^ 2| := abs_sub _ _
            _ = |z₁.im / x ^ 2| + |z₂.im / (1 - x) ^ 2| := by rw [abs_neg]
            _ ≤ 2 * T / x ^ 2 + 2 * T / (1 - x) ^ 2 := add_le_add ha1 ha2
            _ ≤ 2 * T / (x ^ 2 * (1 - x) ^ 2) := hsum_le
        have hsq_lb : (T / (x * (1 - x))) ^ 2 ≤ (z₁.im / x - z₂.im / (1 - x)) ^ 2 :=
          pow_le_pow_left₀ (by positivity) hφlb 2
        have hquot : |-(z₁.im / x ^ 2) - z₂.im / (1 - x) ^ 2| /
            (z₁.im / x - z₂.im / (1 - x)) ^ 2 ≤ 2 / T := by
          have h1 := div_le_div₀ (by positivity) hφ''_le (by positivity) hsq_lb
          have hsimp : (2 * T / (x ^ 2 * (1 - x) ^ 2)) / (T / (x * (1 - x))) ^ 2 = 2 / T := by
            field_simp [hx0.ne', hx1.ne', hTpos.ne']
          rwa [hsimp] at h1
        calc
          x ^ (z₁.re - 1) * (1 - x) ^ (z₂.re - 1) *
              |-(z₁.im / x ^ 2) - z₂.im / (1 - x) ^ 2| / (z₁.im / x - z₂.im / (1 - x)) ^ 2
              = (x ^ (z₁.re - 1) * (1 - x) ^ (z₂.re - 1)) *
                  (|-(z₁.im / x ^ 2) - z₂.im / (1 - x) ^ 2| /
                    (z₁.im / x - z₂.im / (1 - x)) ^ 2) := by ring
          _ ≤ (x ^ (-(1 / 2 : ℝ)) * (1 - x) ^ (-(1 / 2 : ℝ))) * (2 / T) :=
                mul_le_mul hg hquot (by positivity) (by positivity)
          _ = (2 / T) * (x ^ (-(1 / 2 : ℝ)) * (1 - x) ^ (-(1 / 2 : ℝ))) := mul_comm _ _
      linarith [hterm1, hterm2, show (1 / (2 * T)) * (x ^ (-(1 / 2 : ℝ)) * (1 - x) ^ (-(1 / 2 : ℝ))) +
        (2 / T) * (x ^ (-(1 / 2 : ℝ)) * (1 - x) ^ (-(1 / 2 : ℝ))) =
        (5 / (2 * T)) * (x ^ (-(1 / 2 : ℝ)) * (1 - x) ^ (-(1 / 2 : ℝ))) by ring]
    have hcont_l : ContinuousOn (fun x : ℝ =>
        |((z₁.re - 1) * x ^ (z₁.re - 2)) * (1 - x) ^ (z₂.re - 1) +
            x ^ (z₁.re - 1) * (-(z₂.re - 1) * (1 - x) ^ (z₂.re - 2))| /
          |z₁.im / x - z₂.im / (1 - x)| +
          x ^ (z₁.re - 1) * (1 - x) ^ (z₂.re - 1) *
            |-(z₁.im / x ^ 2) - z₂.im / (1 - x) ^ 2| / (z₁.im / x - z₂.im / (1 - x)) ^ 2)
        (Set.uIcc a (1 - a)) := by
      rw [Set.uIcc_of_le (by linarith)]
      have hc_g' : ContinuousOn (fun x : ℝ =>
          ((z₁.re - 1) * x ^ (z₁.re - 2)) * (1 - x) ^ (z₂.re - 1) +
            x ^ (z₁.re - 1) * (-(z₂.re - 1) * (1 - x) ^ (z₂.re - 2))) (Set.Icc a (1 - a)) :=
        ((continuousOn_const.mul (cont_rpow_x _ ha0)).mul (cont_rpow_one_sub _ (by linarith))).add
          ((cont_rpow_x _ ha0).mul (continuousOn_const.mul (cont_rpow_one_sub _ (by linarith))))
      have hc_φ' : ContinuousOn (fun x : ℝ => z₁.im / x - z₂.im / (1 - x)) (Set.Icc a (1 - a)) := by
        have hc1 : ContinuousOn (fun x : ℝ => z₁.im / x) (Set.Icc a (1 - a)) :=
          continuousOn_const.div continuousOn_id fun x hx => (lt_of_lt_of_le ha0 hx.1).ne'
        have hc2 : ContinuousOn (fun x : ℝ => z₂.im / (1 - x)) (Set.Icc a (1 - a)) :=
          continuousOn_const.div (continuousOn_const.sub continuousOn_id) fun x hx =>
            ne_of_gt (by linarith [hx.2, ha0] : (0 : ℝ) < 1 - x)
        exact hc1.sub hc2
      have hc_φ'' : ContinuousOn (fun x : ℝ => -(z₁.im / x ^ 2) - z₂.im / (1 - x) ^ 2)
          (Set.Icc a (1 - a)) := by
        have hc1' : ContinuousOn (fun x : ℝ => z₁.im / x ^ 2) (Set.Icc a (1 - a)) :=
          continuousOn_const.div (continuousOn_id.pow 2) fun x hx =>
            pow_ne_zero 2 (lt_of_lt_of_le ha0 hx.1).ne'
        have hc2 : ContinuousOn (fun x : ℝ => z₂.im / (1 - x) ^ 2) (Set.Icc a (1 - a)) :=
          continuousOn_const.div ((continuousOn_const.sub continuousOn_id).pow 2) fun x hx =>
            pow_ne_zero 2 (ne_of_gt (by linarith [hx.2, ha0] : (0 : ℝ) < 1 - x))
        exact hc1'.neg.sub hc2
      exact (hc_g'.abs.div hc_φ'.abs fun x hx => abs_ne_zero.mpr (hφ'_ne x hx)).add
        ((((cont_rpow_x _ ha0).mul (cont_rpow_one_sub _ (by linarith))).mul hc_φ''.abs).div
          (hc_φ'.pow 2) fun x hx => pow_ne_zero 2 (hφ'_ne x hx))
    have hcont_r : ContinuousOn (fun x : ℝ => (5 / (2 * T)) *
        (x ^ (-(1 / 2 : ℝ)) * (1 - x) ^ (-(1 / 2 : ℝ)))) (Set.uIcc a (1 - a)) := by
      rw [Set.uIcc_of_le (by linarith)]
      exact continuousOn_const.mul ((cont_rpow_x _ ha0).mul (cont_rpow_one_sub _ (by linarith)))
    have hle := intervalIntegral.integral_mono_on (by linarith)
      (hcont_l.intervalIntegrable (μ := MeasureTheory.volume))
      (hcont_r.intervalIntegrable (μ := MeasureTheory.volume)) hpt
    rw [intervalIntegral.integral_const_mul] at hle
    have hw := integral_beta_weight_le a (1 - a) ha0 (by linarith) (by linarith)
    have h1 : (5 / (2 * T)) * 8 = 20 / T := by ring
    have h2 : 20 / T ≤ 20 / Real.sqrt T := div_le_div_of_nonneg_left (by norm_num) hsqTpos hsqT_le_T
    exact hle.trans ((mul_le_mul_of_nonneg_left hw (by positivity)).trans (h1.le.trans h2))
  have hmid : ‖∫ x in a..(1 - a), (x : ℂ) ^ (z₁ - 1) * (1 - (x : ℂ)) ^ (z₂ - 1)‖ ≤
      22 / Real.sqrt T := by
    have hb1 := hbdy (1 - a) ⟨by linarith, le_rfl⟩
    have hb2 := hbdy a ⟨le_rfl, by linarith⟩
    have hsum : 1 / Real.sqrt T + 1 / Real.sqrt T + 20 / Real.sqrt T = 22 / Real.sqrt T := by ring
    linarith [hibp, hb1, hb2, hmid_int, hsum]
  rw [hsplit]
  have t1 := norm_add_le
    ((∫ x in (0 : ℝ)..a, (x : ℂ) ^ (z₁ - 1) * (1 - (x : ℂ)) ^ (z₂ - 1)) +
      (∫ x in a..(1 - a), (x : ℂ) ^ (z₁ - 1) * (1 - (x : ℂ)) ^ (z₂ - 1)))
    (∫ x in (1 - a)..(1 : ℝ), (x : ℂ) ^ (z₁ - 1) * (1 - (x : ℂ)) ^ (z₂ - 1))
  have t2 := norm_add_le
    (∫ x in (0 : ℝ)..a, (x : ℂ) ^ (z₁ - 1) * (1 - (x : ℂ)) ^ (z₂ - 1))
    (∫ x in a..(1 - a), (x : ℂ) ^ (z₁ - 1) * (1 - (x : ℂ)) ^ (z₂ - 1))
  have hsum : 2 / Real.sqrt T + 22 / Real.sqrt T + 2 / Real.sqrt T ≤ 40 / Real.sqrt T := by
    rw [show 2 / Real.sqrt T + 22 / Real.sqrt T + 2 / Real.sqrt T = 26 / Real.sqrt T by ring]
    exact div_le_div_of_nonneg_right (by norm_num) hsqTpos.le
  linarith [t1, t2, hleft, hmid, hright, hsum]

set_option maxHeartbeats 800000 in
private theorem beta_same_sign_left_piece (z₁ z₂ : ℂ) {T : ℝ} (hT : 1 ≤ T)
    (hre1 : 1 / 2 ≤ z₁.re ∧ z₁.re ≤ 1) (hre2 : 1 / 2 ≤ z₂.re ∧ z₂.re ≤ 1)
    (him1 : T ≤ z₁.im ∧ z₁.im ≤ 2 * T) (him2 : T ≤ z₂.im ∧ z₂.im ≤ 2 * T) :
    let a : ℝ := 1 / (8 * T)
    let x₀ : ℝ := z₁.im / (z₁.im + z₂.im)
    let δ : ℝ := 1 / (8 * Real.sqrt T)
    ‖∫ x in a..(x₀ - δ), (x : ℂ) ^ (z₁ - 1) * (1 - (x : ℂ)) ^ (z₂ - 1)‖ ≤ 800 / Real.sqrt T := by
  intro a x₀ δ
  have hTpos : 0 < T := by linarith
  have hsqTpos : 0 < Real.sqrt T := Real.sqrt_pos.mpr hTpos
  have hsqT_ge1 : 1 ≤ Real.sqrt T := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hT
  have hsqT_le_T : Real.sqrt T ≤ T := by
    nlinarith [Real.sq_sqrt hTpos.le, sq_nonneg (Real.sqrt T - 1)]
  have ha0 : 0 < a := by dsimp [a]; positivity
  have ha_le : a ≤ 1 / 8 := by
    dsimp [a]; rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hδ0 : 0 < δ := by dsimp [δ]; positivity
  have hδ_le : δ ≤ 1 / 8 := by
    dsimp [δ]; rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hx₀_lo : 1 / 3 ≤ x₀ := by dsimp [x₀]; rw [le_div_iff₀ (by linarith)]; linarith
  have hx₀_hi : x₀ ≤ 2 / 3 := by dsimp [x₀]; rw [div_le_iff₀ (by linarith)]; linarith
  have hφ'_eq : ∀ x : ℝ, x ≠ 0 → 1 - x ≠ 0 →
      z₁.im / x - z₂.im / (1 - x) = (z₁.im + z₂.im) * (x₀ - x) / (x * (1 - x)) := by
    intro x hx0 hx1
    dsimp only [x₀]
    have hsum_ne : z₁.im + z₂.im ≠ 0 := by linarith
    field_simp [hx0, hx1, hsum_ne]; ring
  have hφ'_lb : ∀ x ∈ Set.Icc a (x₀ - δ),
      2 * T * (x₀ - x) / (x * (1 - x)) ≤ z₁.im / x - z₂.im / (1 - x) := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le ha0 hx.1
    have hx1 : 0 < 1 - x := by linarith [hx.2, hx₀_hi, hδ0]
    rw [hφ'_eq x hx0.ne' hx1.ne']
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_right (by linarith) (by linarith [hx.2, hδ0])
  have hφ'_ne : ∀ x ∈ Set.Icc a (x₀ - δ), z₁.im / x - z₂.im / (1 - x) ≠ 0 := fun x hx => by
    have hx0 : 0 < x := lt_of_lt_of_le ha0 hx.1
    have hx1 : 0 < 1 - x := by linarith [hx.2, hx₀_hi, hδ0]
    have hpos : 0 < 2 * T * (x₀ - x) / (x * (1 - x)) := by
      have : 0 < x₀ - x := by linarith [hx.2, hδ0]
      positivity
    linarith [hφ'_lb x hx]
  have hibp := ibp_oscillatory_bound z₁ z₂ ha0 (by linarith) (by linarith) hφ'_ne
  dsimp only at hibp
  have hbdy_a : |a ^ (z₁.re - 1) * (1 - a) ^ (z₂.re - 1) / (z₁.im / a - z₂.im / (1 - a))| ≤
      5 / Real.sqrt T := by
    have ha1 : 0 < 1 - a := by linarith
    have hxa : 0 < x₀ - a := by linarith
    have hφpos : 0 < z₁.im / a - z₂.im / (1 - a) :=
      lt_of_lt_of_le (by positivity) (hφ'_lb a ⟨le_rfl, by linarith⟩)
    rw [abs_of_nonneg (div_nonneg (mul_nonneg (Real.rpow_nonneg ha0.le _)
      (Real.rpow_nonneg ha1.le _)) hφpos.le)]
    have hg := g_le_weight z₁ z₂ hre1 hre2 ha0 (by linarith)
    have hlb : 2 * T * (1 / 5) / (a * (1 - a)) ≤ z₁.im / a - z₂.im / (1 - a) := by
      refine le_trans ?_ (hφ'_lb a ⟨le_rfl, by linarith⟩)
      apply div_le_div_of_nonneg_right _ (by positivity)
      have : (1 / 5 : ℝ) ≤ x₀ - a := by linarith
      nlinarith
    have hstep := div_le_div₀ (mul_nonneg (Real.rpow_nonneg ha0.le _) (Real.rpow_nonneg ha1.le _))
      hg (by positivity) hlb
    have hsimp : a ^ (-(1 / 2 : ℝ)) * (1 - a) ^ (-(1 / 2 : ℝ)) / (2 * T * (1 / 5) / (a * (1 - a))) =
        5 * (Real.sqrt a * Real.sqrt (1 - a)) / (2 * T) := by
      rw [div_div_eq_mul_div, ← rpow_neg_half_mul_self ha0, ← rpow_neg_half_mul_self ha1]; ring
    rw [hsimp] at hstep
    have hs1 : Real.sqrt a ≤ 1 := by
      calc Real.sqrt a ≤ Real.sqrt 1 := Real.sqrt_le_sqrt (by linarith)
        _ = 1 := Real.sqrt_one
    have hs2 : Real.sqrt (1 - a) ≤ 1 := by
      calc Real.sqrt (1 - a) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt (by linarith)
        _ = 1 := Real.sqrt_one
    have hnum : 5 * (Real.sqrt a * Real.sqrt (1 - a)) ≤ 5 := by
      nlinarith [Real.sqrt_nonneg a, Real.sqrt_nonneg (1 - a)]
    have hdiv : 5 * (Real.sqrt a * Real.sqrt (1 - a)) / (2 * T) ≤ 5 / T := by
      rw [div_le_div_iff₀ (by positivity) hTpos]; nlinarith
    exact (hstep.trans hdiv).trans (div_le_div_of_nonneg_left (by norm_num) hsqTpos hsqT_le_T)
  have hφ'_end : Real.sqrt T / 4 ≤ z₁.im / (x₀ - δ) - z₂.im / (1 - (x₀ - δ)) := by
    have h1 := hφ'_lb (x₀ - δ) ⟨by linarith, le_rfl⟩
    have hx0 : 0 < x₀ - δ := by linarith
    have hx1 : 0 < 1 - (x₀ - δ) := by linarith
    have hprod_le : (x₀ - δ) * (1 - (x₀ - δ)) ≤ 1 := by nlinarith
    have h2 : 2 * T * δ ≤ 2 * T * (x₀ - (x₀ - δ)) / ((x₀ - δ) * (1 - (x₀ - δ))) := by
      rw [sub_sub_cancel, le_div_iff₀ (by positivity)]
      have h2td : 0 < 2 * T * δ := by positivity
      nlinarith
    have h3 : 2 * T * δ = Real.sqrt T / 4 := by
      dsimp only [δ]
      rw [show 2 * T * (1 / (8 * Real.sqrt T)) = (T / Real.sqrt T) / 4 by ring, Real.div_sqrt]
    linarith
  have hg_mid_le : ∀ x ∈ Set.Icc (1 / 6 : ℝ) (x₀ - δ),
      x ^ (z₁.re - 1) * (1 - x) ^ (z₂.re - 1) ≤ 6 := by
    intro x hx
    have hx0 : 0 < x := by linarith [hx.1]
    have hx1 : 0 < 1 - x := by linarith [hx.2, hx₀_hi, hδ0]
    have h1 : x ^ (z₁.re - 1) ≤ x ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_ge hx0 (by linarith) (by linarith)
    have h2 : (1 - x) ^ (z₂.re - 1) ≤ (1 - x) ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_ge hx1 (by linarith) (by linarith)
    have h2' : (1 - x) ^ (-(1 / 2 : ℝ)) ≤ 2 := by
      have : (1 / 3 : ℝ) ≤ 1 - x := by linarith [hx.2, hx₀_hi, hδ0]
      have hsq : (1 / 2 : ℝ) ≤ Real.sqrt (1 - x) := by
        nlinarith [Real.sq_sqrt hx1.le, Real.sqrt_nonneg (1 - x)]
      rw [Real.rpow_neg hx1.le, ← Real.sqrt_eq_rpow,
        inv_le_comm₀ (Real.sqrt_pos.mpr hx1) (by norm_num)]
      linarith
    have h3 : x ^ (-(1 / 2 : ℝ)) ≤ 3 := by
      have hsq : (1 / 3 : ℝ) ≤ Real.sqrt x := by
        nlinarith [Real.sq_sqrt hx0.le, Real.sqrt_nonneg x, hx.1]
      rw [Real.rpow_neg hx0.le, ← Real.sqrt_eq_rpow,
        inv_le_comm₀ (Real.sqrt_pos.mpr hx0) (by norm_num)]
      linarith
    calc
      x ^ (z₁.re - 1) * (1 - x) ^ (z₂.re - 1)
          ≤ 3 * 2 := mul_le_mul (h1.trans h3) (h2.trans h2') (Real.rpow_nonneg hx1.le _) (by norm_num)
      _ = 6 := by norm_num
  have hbdy_end :
      |(x₀ - δ) ^ (z₁.re - 1) * (1 - (x₀ - δ)) ^ (z₂.re - 1) /
        (z₁.im / (x₀ - δ) - z₂.im / (1 - (x₀ - δ)))| ≤ 24 / Real.sqrt T := by
    have hφpos : 0 < z₁.im / (x₀ - δ) - z₂.im / (1 - (x₀ - δ)) := by linarith [hφ'_end, hsqTpos]
    have hx0_nn : 0 ≤ x₀ - δ := by linarith [hx₀_lo, hδ_le]
    have hx1_nn : 0 ≤ 1 - (x₀ - δ) := by linarith [hx₀_hi, hδ0]
    rw [abs_of_nonneg (div_nonneg (mul_nonneg (Real.rpow_nonneg hx0_nn _)
      (Real.rpow_nonneg hx1_nn _)) hφpos.le)]
    have hg6 := hg_mid_le (x₀ - δ) ⟨by linarith [hx₀_lo, hδ_le], le_rfl⟩
    have hstep := div_le_div₀ (by norm_num) hg6 (by positivity) hφ'_end
    have hrew : (6 : ℝ) / (Real.sqrt T / 4) = 24 / Real.sqrt T := by ring
    rwa [hrew] at hstep
  have hcont_g' : ContinuousOn (fun x : ℝ =>
      |((z₁.re - 1) * x ^ (z₁.re - 2)) * (1 - x) ^ (z₂.re - 1) +
          x ^ (z₁.re - 1) * (-(z₂.re - 1) * (1 - x) ^ (z₂.re - 2))| /
        |z₁.im / x - z₂.im / (1 - x)|) (Set.uIcc a (x₀ - δ)) := by
    rw [Set.uIcc_of_le (by linarith)]
    have h1 : ContinuousOn (fun x : ℝ =>
        ((z₁.re - 1) * x ^ (z₁.re - 2)) * (1 - x) ^ (z₂.re - 1) +
          x ^ (z₁.re - 1) * (-(z₂.re - 1) * (1 - x) ^ (z₂.re - 2))) (Set.Icc a (x₀ - δ)) :=
      ((continuousOn_const.mul (cont_rpow_x _ ha0)).mul (cont_rpow_one_sub _ (by linarith))).add
        ((cont_rpow_x _ ha0).mul (continuousOn_const.mul (cont_rpow_one_sub _ (by linarith))))
    have h2 : ContinuousOn (fun x : ℝ => z₁.im / x - z₂.im / (1 - x)) (Set.Icc a (x₀ - δ)) := by
      have hc1 : ContinuousOn (fun x : ℝ => z₁.im / x) (Set.Icc a (x₀ - δ)) :=
        continuousOn_const.div continuousOn_id fun x hx => (lt_of_lt_of_le ha0 hx.1).ne'
      have hc2 : ContinuousOn (fun x : ℝ => z₂.im / (1 - x)) (Set.Icc a (x₀ - δ)) :=
        continuousOn_const.div (continuousOn_const.sub continuousOn_id) fun x hx =>
          ne_of_gt (by linarith [hx.2, hx₀_hi, hδ0] : (0 : ℝ) < 1 - x)
      exact hc1.sub hc2
    exact h1.abs.div h2.abs fun x hx => abs_ne_zero.mpr (hφ'_ne x hx)
  have hcont_φ''_term : ContinuousOn (fun x : ℝ =>
      x ^ (z₁.re - 1) * (1 - x) ^ (z₂.re - 1) *
        |-(z₁.im / x ^ 2) - z₂.im / (1 - x) ^ 2| / (z₁.im / x - z₂.im / (1 - x)) ^ 2)
      (Set.uIcc a (x₀ - δ)) := by
    rw [Set.uIcc_of_le (by linarith)]
    have hφ'c : ContinuousOn (fun x : ℝ => z₁.im / x - z₂.im / (1 - x)) (Set.Icc a (x₀ - δ)) := by
      have hc1 : ContinuousOn (fun x : ℝ => z₁.im / x) (Set.Icc a (x₀ - δ)) :=
        continuousOn_const.div continuousOn_id fun x hx => (lt_of_lt_of_le ha0 hx.1).ne'
      have hc2 : ContinuousOn (fun x : ℝ => z₂.im / (1 - x)) (Set.Icc a (x₀ - δ)) :=
        continuousOn_const.div (continuousOn_const.sub continuousOn_id) fun x hx =>
          ne_of_gt (by linarith [hx.2, hx₀_hi, hδ0] : (0 : ℝ) < 1 - x)
      exact hc1.sub hc2
    have hφ''c : ContinuousOn (fun x : ℝ => -(z₁.im / x ^ 2) - z₂.im / (1 - x) ^ 2)
        (Set.Icc a (x₀ - δ)) := by
      have hc1' : ContinuousOn (fun x : ℝ => z₁.im / x ^ 2) (Set.Icc a (x₀ - δ)) :=
        continuousOn_const.div (continuousOn_id.pow 2) fun x hx =>
          pow_ne_zero 2 (lt_of_lt_of_le ha0 hx.1).ne'
      have hc2 : ContinuousOn (fun x : ℝ => z₂.im / (1 - x) ^ 2) (Set.Icc a (x₀ - δ)) :=
        continuousOn_const.div ((continuousOn_const.sub continuousOn_id).pow 2) fun x hx =>
          pow_ne_zero 2 (ne_of_gt (by linarith [hx.2, hx₀_hi, hδ0] : (0 : ℝ) < 1 - x))
      exact hc1'.neg.sub hc2
    exact (((cont_rpow_x _ ha0).mul (cont_rpow_one_sub _ (by linarith))).mul hφ''c.abs).div
      (hφ'c.pow 2) fun x hx => pow_ne_zero 2 (hφ'_ne x hx)
  have hint1 :
      (∫ x in a..(x₀ - δ),
        |((z₁.re - 1) * x ^ (z₁.re - 2)) * (1 - x) ^ (z₂.re - 1) +
            x ^ (z₁.re - 1) * (-(z₂.re - 1) * (1 - x) ^ (z₂.re - 2))| /
          |z₁.im / x - z₂.im / (1 - x)|) ≤ 16 / Real.sqrt T := by
    have hpt : ∀ x ∈ Set.Icc a (x₀ - δ),
        |((z₁.re - 1) * x ^ (z₁.re - 2)) * (1 - x) ^ (z₂.re - 1) +
            x ^ (z₁.re - 1) * (-(z₂.re - 1) * (1 - x) ^ (z₂.re - 2))| /
          |z₁.im / x - z₂.im / (1 - x)| ≤
          (2 / Real.sqrt T) * (x ^ (-(1 / 2 : ℝ)) * (1 - x) ^ (-(1 / 2 : ℝ))) := by
      intro x hx
      have hx0 : 0 < x := lt_of_lt_of_le ha0 hx.1
      have hx1 : 0 < 1 - x := by linarith [hx.2, hx₀_hi, hδ0]
      have hφlb : 2 * T * δ / (x * (1 - x)) ≤ z₁.im / x - z₂.im / (1 - x) := by
        refine le_trans ?_ (hφ'_lb x hx)
        apply div_le_div_of_nonneg_right _ (by positivity)
        have : δ ≤ x₀ - x := by linarith [hx.2]
        nlinarith
      have hφpos : 0 < z₁.im / x - z₂.im / (1 - x) := lt_of_lt_of_le (by positivity) hφlb
      rw [abs_of_pos hφpos]
      have hd := g_deriv_bound z₁ z₂ hre1 hre2 hx0 (by linarith)
      have hstep := div_le_div₀ (by positivity) hd (by positivity) hφlb
      have hsimp : (x ^ (z₁.re - 1) * (1 - x) ^ (z₂.re - 1)) / (2 * x * (1 - x)) /
          (2 * T * δ / (x * (1 - x))) =
          (2 / Real.sqrt T) * (x ^ (z₁.re - 1) * (1 - x) ^ (z₂.re - 1)) := by
        dsimp only [δ]
        have hdivsq : Real.sqrt T / T = 1 / Real.sqrt T := by
          rw [div_eq_div_iff hTpos.ne' hsqTpos.ne']
          linarith [Real.mul_self_sqrt hTpos.le]
        calc
          (x ^ (z₁.re - 1) * (1 - x) ^ (z₂.re - 1)) / (2 * x * (1 - x)) /
              (2 * T * (1 / (8 * Real.sqrt T)) / (x * (1 - x)))
              = (2 * (Real.sqrt T / T)) * (x ^ (z₁.re - 1) * (1 - x) ^ (z₂.re - 1)) := by
                field_simp [hx0.ne', hx1.ne', hTpos.ne', hsqTpos.ne']; ring
          _ = (2 / Real.sqrt T) * (x ^ (z₁.re - 1) * (1 - x) ^ (z₂.re - 1)) := by
                rw [hdivsq]; ring
      rw [hsimp] at hstep
      exact hstep.trans (mul_le_mul_of_nonneg_left (g_le_weight z₁ z₂ hre1 hre2 hx0 (by linarith))
        (by positivity))
    have hcont_r : ContinuousOn (fun x : ℝ => (2 / Real.sqrt T) *
        (x ^ (-(1 / 2 : ℝ)) * (1 - x) ^ (-(1 / 2 : ℝ)))) (Set.uIcc a (x₀ - δ)) := by
      rw [Set.uIcc_of_le (by linarith)]
      exact continuousOn_const.mul ((cont_rpow_x _ ha0).mul (cont_rpow_one_sub _ (by linarith)))
    have hle := intervalIntegral.integral_mono_on (by linarith)
      (hcont_g'.intervalIntegrable (μ := MeasureTheory.volume))
      (hcont_r.intervalIntegrable (μ := MeasureTheory.volume)) hpt
    rw [intervalIntegral.integral_const_mul] at hle
    have hw := integral_beta_weight_le a (x₀ - δ) ha0 (by linarith) (by linarith)
    exact hle.trans (by
      have h1 := mul_le_mul_of_nonneg_left hw (by positivity : 0 ≤ 2 / Real.sqrt T)
      linarith [show (2 / Real.sqrt T) * 8 = 16 / Real.sqrt T by ring])
  have hint2_left :
      (∫ x in a..(1 / 6 : ℝ),
        x ^ (z₁.re - 1) * (1 - x) ^ (z₂.re - 1) *
          |-(z₁.im / x ^ 2) - z₂.im / (1 - x) ^ 2| / (z₁.im / x - z₂.im / (1 - x)) ^ 2) ≤
        720 / Real.sqrt T := by
    have hsub_int : IntervalIntegrable (fun x : ℝ =>
        x ^ (z₁.re - 1) * (1 - x) ^ (z₂.re - 1) *
          |-(z₁.im / x ^ 2) - z₂.im / (1 - x) ^ 2| / (z₁.im / x - z₂.im / (1 - x)) ^ 2)
        volume a (1 / 6) :=
      mono_uIcc hcont_φ''_term.intervalIntegrable (by linarith) le_rfl (by linarith) (by linarith)
    have hpt : ∀ x ∈ Set.Icc a (1 / 6 : ℝ),
        x ^ (z₁.re - 1) * (1 - x) ^ (z₂.re - 1) *
          |-(z₁.im / x ^ 2) - z₂.im / (1 - x) ^ 2| / (z₁.im / x - z₂.im / (1 - x)) ^ 2 ≤
          (90 / T) * (x ^ (-(1 / 2 : ℝ)) * (1 - x) ^ (-(1 / 2 : ℝ))) := by
      intro x hx
      have hx0 : 0 < x := lt_of_lt_of_le ha0 hx.1
      have hx1 : 0 < 1 - x := by linarith [hx.2]
      have hφ''_le : |-(z₁.im / x ^ 2) - z₂.im / (1 - x) ^ 2| ≤ 10 * T / x ^ 2 := by
        have hz1 : 0 < z₁.im := by linarith
        have hz2 : 0 < z₂.im := by linarith
        have hpos : 0 < z₁.im / x ^ 2 + z₂.im / (1 - x) ^ 2 := by positivity
        rw [show -(z₁.im / x ^ 2) - z₂.im / (1 - x) ^ 2 = -(z₁.im / x ^ 2 + z₂.im / (1 - x) ^ 2) by ring,
          abs_neg, abs_of_pos hpos]
        have h1 : z₁.im / x ^ 2 ≤ 2 * T / x ^ 2 := div_le_div_of_nonneg_right him1.2 (sq_nonneg x)
        have h2 : z₂.im / (1 - x) ^ 2 ≤ 8 * T / x ^ 2 := by
          have hsq : x ^ 2 ≤ 4 * (1 - x) ^ 2 := by nlinarith [hx.2]
          rw [div_le_div_iff₀ (sq_pos_of_pos hx1) (sq_pos_of_pos hx0)]
          nlinarith [him2.2]
        linarith [show 2 * T / x ^ 2 + 8 * T / x ^ 2 = 10 * T / x ^ 2 by ring]
      have hφ_lb : T / (3 * x) ≤ z₁.im / x - z₂.im / (1 - x) := by
        refine le_trans ?_ (hφ'_lb x ⟨hx.1, by linarith [hx.2]⟩)
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have hdiff : (1 / 6 : ℝ) ≤ x₀ - x := by linarith [hx.2]
        have hTx : 0 < T * x := by positivity
        nlinarith [hx.2, hTx, hdiff]
      have hsq_lb : (T / (3 * x)) ^ 2 ≤ (z₁.im / x - z₂.im / (1 - x)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hφ_lb 2
      have hquot : |-(z₁.im / x ^ 2) - z₂.im / (1 - x) ^ 2| /
          (z₁.im / x - z₂.im / (1 - x)) ^ 2 ≤ 90 / T := by
        have h1 := div_le_div₀ (by positivity) hφ''_le (by positivity) hsq_lb
        have hsimp : (10 * T / x ^ 2) / (T / (3 * x)) ^ 2 = 90 / T := by
          field_simp [hx0.ne', hTpos.ne']; ring
        rwa [hsimp] at h1
      calc
        x ^ (z₁.re - 1) * (1 - x) ^ (z₂.re - 1) *
            |-(z₁.im / x ^ 2) - z₂.im / (1 - x) ^ 2| / (z₁.im / x - z₂.im / (1 - x)) ^ 2
            = (x ^ (z₁.re - 1) * (1 - x) ^ (z₂.re - 1)) *
                (|-(z₁.im / x ^ 2) - z₂.im / (1 - x) ^ 2| /
                  (z₁.im / x - z₂.im / (1 - x)) ^ 2) := by ring
        _ ≤ (x ^ (-(1 / 2 : ℝ)) * (1 - x) ^ (-(1 / 2 : ℝ))) * (90 / T) :=
              mul_le_mul (g_le_weight z₁ z₂ hre1 hre2 hx0 (by linarith [hx.2])) hquot
                (by positivity) (by positivity)
        _ = (90 / T) * (x ^ (-(1 / 2 : ℝ)) * (1 - x) ^ (-(1 / 2 : ℝ))) := mul_comm _ _
    have hcont_r : ContinuousOn (fun x : ℝ => (90 / T) *
        (x ^ (-(1 / 2 : ℝ)) * (1 - x) ^ (-(1 / 2 : ℝ)))) (Set.uIcc a (1 / 6)) := by
      rw [Set.uIcc_of_le (by linarith)]
      exact continuousOn_const.mul ((cont_rpow_x _ ha0).mul (cont_rpow_one_sub _ (by norm_num)))
    have hle := intervalIntegral.integral_mono_on (by linarith) hsub_int
      hcont_r.intervalIntegrable hpt
    rw [intervalIntegral.integral_const_mul] at hle
    have hw := integral_beta_weight_le a (1 / 6) ha0 (by linarith) (by norm_num)
    have h1 : (90 / T) * 8 = 720 / T := by ring
    have h2 : 720 / T ≤ 720 / Real.sqrt T := div_le_div_of_nonneg_left (by norm_num) hsqTpos hsqT_le_T
    exact hle.trans ((mul_le_mul_of_nonneg_left hw (by positivity)).trans (h1.le.trans h2))
  have hint2_right :
      (∫ x in (1 / 6 : ℝ)..(x₀ - δ),
        x ^ (z₁.re - 1) * (1 - x) ^ (z₂.re - 1) *
          |-(z₁.im / x ^ 2) - z₂.im / (1 - x) ^ 2| / (z₁.im / x - z₂.im / (1 - x)) ^ 2) ≤
        24 / Real.sqrt T := by
    have hsub_int : IntervalIntegrable (fun x : ℝ =>
        x ^ (z₁.re - 1) * (1 - x) ^ (z₂.re - 1) *
          |-(z₁.im / x ^ 2) - z₂.im / (1 - x) ^ 2| / (z₁.im / x - z₂.im / (1 - x)) ^ 2)
        volume (1 / 6) (x₀ - δ) :=
      mono_uIcc hcont_φ''_term.intervalIntegrable (by linarith) (by linarith) (by linarith) le_rfl
    let F : ℝ → ℝ := fun x => 6 / (z₁.im / x - z₂.im / (1 - x))
    let F' : ℝ → ℝ := fun x =>
      6 * (z₁.im / x ^ 2 + z₂.im / (1 - x) ^ 2) / (z₁.im / x - z₂.im / (1 - x)) ^ 2
    have hsub1 (x : ℝ) : HasDerivAt (fun t : ℝ => 1 - t) (-1) x :=
      (hasDerivAt_id x).const_sub (1 : ℝ)
    have hdF (x : ℝ) (hx : x ∈ Set.uIcc (1 / 6 : ℝ) (x₀ - δ)) : HasDerivAt F (F' x) x := by
      rw [Set.uIcc_of_le (by linarith)] at hx
      have hx0 : 0 < x := by linarith [hx.1]
      have hx1 : 0 < 1 - x := by linarith [hx.2, hx₀_hi, hδ0]
      have hφne := hφ'_ne x ⟨by linarith [hx.1], hx.2⟩
      have hd1 : HasDerivAt (fun t : ℝ => z₁.im / t) (-(z₁.im / x ^ 2)) x := by
        have hi := (hasDerivAt_inv hx0.ne').const_mul z₁.im
        have hfun : (fun t : ℝ => z₁.im * t⁻¹) = (fun t : ℝ => z₁.im / t) := by funext t; ring
        rw [hfun] at hi
        have heq : z₁.im * -(x ^ 2)⁻¹ = -(z₁.im / x ^ 2) := by ring
        rwa [heq] at hi
      have hd2 : HasDerivAt (fun t : ℝ => z₂.im / (1 - t)) (z₂.im / (1 - x) ^ 2) x := by
        have hi := ((hasDerivAt_inv hx1.ne').comp x (hsub1 x)).const_mul z₂.im
        have hfun : (fun t : ℝ => z₂.im * ((fun y : ℝ => y⁻¹) ∘ fun s : ℝ => 1 - s) t) =
            (fun t : ℝ => z₂.im / (1 - t)) := by funext t; simp [div_eq_mul_inv]
        rw [hfun] at hi
        have heq : z₂.im * (-((1 - x) ^ 2)⁻¹ * -1) = z₂.im / (1 - x) ^ 2 := by ring
        rwa [heq] at hi
      have hdi := (hd1.sub hd2).inv hφne
      have hmul := hdi.const_mul (6 : ℝ)
      have hfun : (fun y : ℝ => (6 : ℝ) * ((fun t : ℝ => z₁.im / t) - fun t : ℝ => z₂.im / (1 - t))⁻¹ y) = F := by
        funext t; simp [F, div_eq_mul_inv]
      rw [hfun] at hmul
      have heq : (6 : ℝ) * (-( -(z₁.im / x ^ 2) - z₂.im / (1 - x) ^ 2 ) /
          ((fun t : ℝ => z₁.im / t) - fun t : ℝ => z₂.im / (1 - t)) x ^ 2) = F' x := by
        dsimp only [F', Pi.sub_apply]; ring
      rwa [heq] at hmul
    have hcont_F' : ContinuousOn F' (Set.uIcc (1 / 6 : ℝ) (x₀ - δ)) := by
      rw [Set.uIcc_of_le (by linarith)]
      have h1 : ContinuousOn (fun x : ℝ => z₁.im / x ^ 2 + z₂.im / (1 - x) ^ 2)
          (Set.Icc (1 / 6 : ℝ) (x₀ - δ)) := by
        have hc1 : ContinuousOn (fun x : ℝ => z₁.im / x ^ 2) (Set.Icc (1 / 6 : ℝ) (x₀ - δ)) :=
          continuousOn_const.div (continuousOn_id.pow 2) fun x hx =>
            pow_ne_zero 2 (ne_of_gt (by linarith [hx.1] : (0 : ℝ) < x))
        have hc2 : ContinuousOn (fun x : ℝ => z₂.im / (1 - x) ^ 2) (Set.Icc (1 / 6 : ℝ) (x₀ - δ)) :=
          continuousOn_const.div ((continuousOn_const.sub continuousOn_id).pow 2) fun x hx =>
            pow_ne_zero 2 (ne_of_gt (by linarith [hx.2, hx₀_hi, hδ0] : (0 : ℝ) < 1 - x))
        exact hc1.add hc2
      have h2 : ContinuousOn (fun x : ℝ => z₁.im / x - z₂.im / (1 - x))
          (Set.Icc (1 / 6 : ℝ) (x₀ - δ)) := by
        have hc1 : ContinuousOn (fun x : ℝ => z₁.im / x) (Set.Icc (1 / 6 : ℝ) (x₀ - δ)) :=
          continuousOn_const.div continuousOn_id fun x hx =>
            ne_of_gt (by linarith [hx.1] : (0 : ℝ) < x)
        have hc2 : ContinuousOn (fun x : ℝ => z₂.im / (1 - x)) (Set.Icc (1 / 6 : ℝ) (x₀ - δ)) :=
          continuousOn_const.div (continuousOn_const.sub continuousOn_id) fun x hx =>
            ne_of_gt (by linarith [hx.2, hx₀_hi, hδ0] : (0 : ℝ) < 1 - x)
        exact hc1.sub hc2
      exact (continuousOn_const.mul h1).div (h2.pow 2) fun x hx =>
        pow_ne_zero 2 (hφ'_ne x ⟨by linarith [hx.1], hx.2⟩)
    have hpt : ∀ x ∈ Set.Icc (1 / 6 : ℝ) (x₀ - δ),
        x ^ (z₁.re - 1) * (1 - x) ^ (z₂.re - 1) *
          |-(z₁.im / x ^ 2) - z₂.im / (1 - x) ^ 2| / (z₁.im / x - z₂.im / (1 - x)) ^ 2 ≤
          F' x := by
      intro x hx
      have hx0 : 0 < x := by linarith [hx.1]
      have hx1 : 0 < 1 - x := by linarith [hx.2, hx₀_hi, hδ0]
      have hz1 : 0 < z₁.im := by linarith
      have hz2 : 0 < z₂.im := by linarith
      have hpos : 0 < z₁.im / x ^ 2 + z₂.im / (1 - x) ^ 2 := by positivity
      rw [show -(z₁.im / x ^ 2) - z₂.im / (1 - x) ^ 2 = -(z₁.im / x ^ 2 + z₂.im / (1 - x) ^ 2) by ring,
        abs_neg, abs_of_pos hpos]
      dsimp only [F']
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      exact mul_le_mul_of_nonneg_right (hg_mid_le x hx) hpos.le
    have hle := intervalIntegral.integral_mono_on (by linarith) hsub_int
      hcont_F'.intervalIntegrable hpt
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hdF hcont_F'.intervalIntegrable] at hle
    have hF16 : 0 ≤ F (1 / 6) := by
      dsimp only [F]
      have hxa : 0 < x₀ - (1 / 6 : ℝ) := by linarith
      have hφpos : 0 < z₁.im / (1 / 6 : ℝ) - z₂.im / (1 - 1 / 6) :=
        lt_of_lt_of_le (by positivity) (hφ'_lb (1 / 6) ⟨by linarith, by linarith⟩)
      positivity
    have hFend : F (x₀ - δ) ≤ 24 / Real.sqrt T := by
      dsimp only [F]
      have h1 := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 6) (by positivity) hφ'_end
      have h2 : (6 : ℝ) / (Real.sqrt T / 4) = 24 / Real.sqrt T := by ring
      rwa [h2] at h1
    linarith
  have hint2 :
      (∫ x in a..(x₀ - δ),
        x ^ (z₁.re - 1) * (1 - x) ^ (z₂.re - 1) *
          |-(z₁.im / x ^ 2) - z₂.im / (1 - x) ^ 2| / (z₁.im / x - z₂.im / (1 - x)) ^ 2) ≤
        744 / Real.sqrt T := by
    have hl : IntervalIntegrable (fun x : ℝ =>
        x ^ (z₁.re - 1) * (1 - x) ^ (z₂.re - 1) *
          |-(z₁.im / x ^ 2) - z₂.im / (1 - x) ^ 2| / (z₁.im / x - z₂.im / (1 - x)) ^ 2)
        volume a (1 / 6) :=
      mono_uIcc hcont_φ''_term.intervalIntegrable (by linarith) le_rfl (by linarith) (by linarith)
    have hr : IntervalIntegrable (fun x : ℝ =>
        x ^ (z₁.re - 1) * (1 - x) ^ (z₂.re - 1) *
          |-(z₁.im / x ^ 2) - z₂.im / (1 - x) ^ 2| / (z₁.im / x - z₂.im / (1 - x)) ^ 2)
        volume (1 / 6) (x₀ - δ) :=
      mono_uIcc hcont_φ''_term.intervalIntegrable (by linarith) (by linarith) (by linarith) le_rfl
    rw [← intervalIntegral.integral_add_adjacent_intervals hl hr]
    have hsum : 720 / Real.sqrt T + 24 / Real.sqrt T = 744 / Real.sqrt T := by ring
    linarith [hint2_left, hint2_right, hsum]
  have hint_total :
      (∫ x in a..(x₀ - δ),
        (|((z₁.re - 1) * x ^ (z₁.re - 2)) * (1 - x) ^ (z₂.re - 1) +
            x ^ (z₁.re - 1) * (-(z₂.re - 1) * (1 - x) ^ (z₂.re - 2))| /
          |z₁.im / x - z₂.im / (1 - x)| +
          x ^ (z₁.re - 1) * (1 - x) ^ (z₂.re - 1) *
            |-(z₁.im / x ^ 2) - z₂.im / (1 - x) ^ 2| / (z₁.im / x - z₂.im / (1 - x)) ^ 2)) ≤
        760 / Real.sqrt T := by
    rw [intervalIntegral.integral_add hcont_g'.intervalIntegrable hcont_φ''_term.intervalIntegrable]
    have hsum : 16 / Real.sqrt T + 744 / Real.sqrt T = 760 / Real.sqrt T := by ring
    linarith [hint1, hint2, hsum]
  have hsum : 24 / Real.sqrt T + 5 / Real.sqrt T + 760 / Real.sqrt T ≤ 800 / Real.sqrt T := by
    rw [show 24 / Real.sqrt T + 5 / Real.sqrt T + 760 / Real.sqrt T = 789 / Real.sqrt T by ring]
    exact div_le_div_of_nonneg_right (by norm_num) hsqTpos.le
  linarith [hibp, hbdy_a, hbdy_end, hint_total, hsum]

private theorem beta_same_sign_bound (z₁ z₂ : ℂ) {T : ℝ} (hT : 1 ≤ T)
    (hre1 : 1 / 2 ≤ z₁.re ∧ z₁.re ≤ 1) (hre2 : 1 / 2 ≤ z₂.re ∧ z₂.re ≤ 1)
    (him1 : T ≤ z₁.im ∧ z₁.im ≤ 2 * T) (him2 : T ≤ z₂.im ∧ z₂.im ≤ 2 * T) :
    ‖Complex.betaIntegral z₁ z₂‖ ≤ 1610 / Real.sqrt T := by
  have hTpos : 0 < T := by linarith
  have hsqTpos : 0 < Real.sqrt T := Real.sqrt_pos.mpr hTpos
  have hsqT_ge1 : 1 ≤ Real.sqrt T := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hT
  let a : ℝ := 1 / (8 * T)
  let x₀ : ℝ := z₁.im / (z₁.im + z₂.im)
  let δ : ℝ := 1 / (8 * Real.sqrt T)
  have ha0 : 0 < a := by dsimp [a]; positivity
  have ha_le : a ≤ 1 / 8 := by
    dsimp [a]; rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hδ0 : 0 < δ := by dsimp [δ]; positivity
  have hδ_le : δ ≤ 1 / 8 := by
    dsimp [δ]; rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hx₀_lo : 1 / 3 ≤ x₀ := by dsimp [x₀]; rw [le_div_iff₀ (by linarith)]; linarith
  have hx₀_hi : x₀ ≤ 2 / 3 := by dsimp [x₀]; rw [div_le_iff₀ (by linarith)]; linarith
  have hsqa : 4 * Real.sqrt a ≤ 2 / Real.sqrt T := by
    have hsq : Real.sqrt a = 1 / (Real.sqrt 8 * Real.sqrt T) := by
      dsimp only [a]; rw [Real.sqrt_div (by norm_num), Real.sqrt_one, Real.sqrt_mul (by norm_num)]
    rw [hsq]
    have h8 : (2 : ℝ) ≤ Real.sqrt 8 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 8), Real.sqrt_nonneg 8]
    rw [show 4 * (1 / (Real.sqrt 8 * Real.sqrt T)) = (4 / Real.sqrt 8) / Real.sqrt T by ring]
    apply div_le_div_of_nonneg_right _ hsqTpos.le
    rw [div_le_iff₀ (by linarith)]; linarith
  have hconv := Complex.betaIntegral_convergent (u := z₁) (v := z₂) (by linarith) (by linarith)
  have hi1 : IntervalIntegrable (fun x : ℝ => (x : ℂ) ^ (z₁ - 1) * (1 - (x : ℂ)) ^ (z₂ - 1))
      volume 0 a := mono_uIcc hconv (by norm_num) le_rfl ha0.le (by linarith)
  have hi2 : IntervalIntegrable (fun x : ℝ => (x : ℂ) ^ (z₁ - 1) * (1 - (x : ℂ)) ^ (z₂ - 1))
      volume a (x₀ - δ) := mono_uIcc hconv (by norm_num) ha0.le (by linarith) (by linarith)
  have hi3 : IntervalIntegrable (fun x : ℝ => (x : ℂ) ^ (z₁ - 1) * (1 - (x : ℂ)) ^ (z₂ - 1))
      volume (x₀ - δ) (x₀ + δ) := mono_uIcc hconv (by norm_num) (by linarith) (by linarith) (by linarith)
  have hi4 : IntervalIntegrable (fun x : ℝ => (x : ℂ) ^ (z₁ - 1) * (1 - (x : ℂ)) ^ (z₂ - 1))
      volume (x₀ + δ) (1 - a) := mono_uIcc hconv (by norm_num) (by linarith) (by linarith) (by linarith)
  have hi5 : IntervalIntegrable (fun x : ℝ => (x : ℂ) ^ (z₁ - 1) * (1 - (x : ℂ)) ^ (z₂ - 1))
      volume (1 - a) 1 := mono_uIcc hconv (by norm_num) (by linarith) (by linarith) le_rfl
  have hsplit : Complex.betaIntegral z₁ z₂ =
      (∫ x in (0 : ℝ)..a, (x : ℂ) ^ (z₁ - 1) * (1 - (x : ℂ)) ^ (z₂ - 1)) +
      (∫ x in a..(x₀ - δ), (x : ℂ) ^ (z₁ - 1) * (1 - (x : ℂ)) ^ (z₂ - 1)) +
      (∫ x in (x₀ - δ)..(x₀ + δ), (x : ℂ) ^ (z₁ - 1) * (1 - (x : ℂ)) ^ (z₂ - 1)) +
      (∫ x in (x₀ + δ)..(1 - a), (x : ℂ) ^ (z₁ - 1) * (1 - (x : ℂ)) ^ (z₂ - 1)) +
      (∫ x in (1 - a)..(1 : ℝ), (x : ℂ) ^ (z₁ - 1) * (1 - (x : ℂ)) ^ (z₂ - 1)) := by
    unfold Complex.betaIntegral
    rw [← intervalIntegral.integral_add_adjacent_intervals (((hi1.trans hi2).trans hi3).trans hi4) hi5,
      ← intervalIntegral.integral_add_adjacent_intervals ((hi1.trans hi2).trans hi3) hi4,
      ← intervalIntegral.integral_add_adjacent_intervals (hi1.trans hi2) hi3,
      ← intervalIntegral.integral_add_adjacent_intervals hi1 hi2]
  have hb1 := (tail_left_bound z₁ z₂ hre1 hre2 ha0 (by linarith)).trans hsqa
  have hb5 := (tail_right_bound z₁ z₂ hre1 hre2 ha0 (by linarith)).trans hsqa
  have hb2 : ‖∫ x in a..(x₀ - δ), (x : ℂ) ^ (z₁ - 1) * (1 - (x : ℂ)) ^ (z₂ - 1)‖ ≤
      800 / Real.sqrt T := beta_same_sign_left_piece z₁ z₂ hT hre1 hre2 him1 him2
  have hb4 : ‖∫ x in (x₀ + δ)..(1 - a), (x : ℂ) ^ (z₁ - 1) * (1 - (x : ℂ)) ^ (z₂ - 1)‖ ≤
      800 / Real.sqrt T := by
    rw [beta_sub_left_symm z₁ z₂ (x₀ + δ) (1 - a)]
    have h1a : 1 - (1 - a) = a := by ring
    have h1x : 1 - (x₀ + δ) = z₂.im / (z₂.im + z₁.im) - δ := by
      dsimp only [x₀]
      have hne : z₁.im + z₂.im ≠ 0 := by linarith
      have hne' : z₂.im + z₁.im ≠ 0 := by linarith
      field_simp [hne, hne']; ring
    rw [h1a, h1x]
    exact beta_same_sign_left_piece z₂ z₁ hT hre2 hre1 him2 him1
  have hb3 : ‖∫ x in (x₀ - δ)..(x₀ + δ), (x : ℂ) ^ (z₁ - 1) * (1 - (x : ℂ)) ^ (z₂ - 1)‖ ≤
      2 / Real.sqrt T := by
    have hpt : ∀ x ∈ Set.Icc (x₀ - δ) (x₀ + δ),
        ‖(x : ℂ) ^ (z₁ - 1) * (1 - (x : ℂ)) ^ (z₂ - 1)‖ ≤ 5 := by
      intro x hx
      have hx0 : 0 < x := by linarith [hx.1]
      have hx1 : 0 < 1 - x := by linarith [hx.2]
      have hn := norm_betaIntegrand_le z₁ z₂ hre1 hre2 hx0 (by linarith)
      have h1 : x ^ (-(1 / 2 : ℝ)) ≤ Real.sqrt 5 := by
        have hlo : (1 / 5 : ℝ) ≤ x := by linarith [hx.1]
        have hsq : Real.sqrt (1 / 5 : ℝ) ≤ Real.sqrt x := Real.sqrt_le_sqrt hlo
        rw [Real.rpow_neg hx0.le, ← Real.sqrt_eq_rpow,
          inv_le_comm₀ (Real.sqrt_pos.mpr hx0) (Real.sqrt_pos.mpr (by norm_num))]
        have hi : (Real.sqrt 5)⁻¹ = Real.sqrt (1 / 5 : ℝ) := by
          rw [Real.sqrt_div (by norm_num), Real.sqrt_one, one_div]
        linarith
      have h2 : (1 - x) ^ (-(1 / 2 : ℝ)) ≤ Real.sqrt 5 := by
        have hlo : (1 / 5 : ℝ) ≤ 1 - x := by linarith [hx.2]
        have hsq : Real.sqrt (1 / 5 : ℝ) ≤ Real.sqrt (1 - x) := Real.sqrt_le_sqrt hlo
        rw [Real.rpow_neg hx1.le, ← Real.sqrt_eq_rpow,
          inv_le_comm₀ (Real.sqrt_pos.mpr hx1) (Real.sqrt_pos.mpr (by norm_num))]
        have hi : (Real.sqrt 5)⁻¹ = Real.sqrt (1 / 5 : ℝ) := by
          rw [Real.sqrt_div (by norm_num), Real.sqrt_one, one_div]
        linarith
      calc
        ‖(x : ℂ) ^ (z₁ - 1) * (1 - (x : ℂ)) ^ (z₂ - 1)‖
            ≤ Real.sqrt 5 * Real.sqrt 5 := hn.trans (mul_le_mul h1 h2
              (Real.rpow_nonneg hx1.le _) (Real.sqrt_nonneg 5))
        _ = 5 := Real.mul_self_sqrt (by norm_num)
    calc
      ‖∫ x in (x₀ - δ)..(x₀ + δ), (x : ℂ) ^ (z₁ - 1) * (1 - (x : ℂ)) ^ (z₂ - 1)‖
          ≤ ∫ x in (x₀ - δ)..(x₀ + δ), ‖(x : ℂ) ^ (z₁ - 1) * (1 - (x : ℂ)) ^ (z₂ - 1)‖ :=
            intervalIntegral.norm_integral_le_integral_norm (by linarith)
      _ ≤ ∫ _x in (x₀ - δ)..(x₀ + δ), (5 : ℝ) :=
            intervalIntegral.integral_mono_on (by linarith) hi3.norm intervalIntegrable_const hpt
      _ = 5 * (2 * δ) := by simp; ring
      _ ≤ 2 / Real.sqrt T := by
            dsimp only [δ]
            rw [show 5 * (2 * (1 / (8 * Real.sqrt T))) = (5 / 4) / Real.sqrt T by ring]
            exact div_le_div_of_nonneg_right (by norm_num) hsqTpos.le
  rw [hsplit]
  have t1 := norm_add_le
    ((∫ x in (0 : ℝ)..a, (x : ℂ) ^ (z₁ - 1) * (1 - (x : ℂ)) ^ (z₂ - 1)) +
     (∫ x in a..(x₀ - δ), (x : ℂ) ^ (z₁ - 1) * (1 - (x : ℂ)) ^ (z₂ - 1)) +
     (∫ x in (x₀ - δ)..(x₀ + δ), (x : ℂ) ^ (z₁ - 1) * (1 - (x : ℂ)) ^ (z₂ - 1)) +
     (∫ x in (x₀ + δ)..(1 - a), (x : ℂ) ^ (z₁ - 1) * (1 - (x : ℂ)) ^ (z₂ - 1)))
    (∫ x in (1 - a)..(1 : ℝ), (x : ℂ) ^ (z₁ - 1) * (1 - (x : ℂ)) ^ (z₂ - 1))
  have t2 := norm_add_le
    ((∫ x in (0 : ℝ)..a, (x : ℂ) ^ (z₁ - 1) * (1 - (x : ℂ)) ^ (z₂ - 1)) +
     (∫ x in a..(x₀ - δ), (x : ℂ) ^ (z₁ - 1) * (1 - (x : ℂ)) ^ (z₂ - 1)) +
     (∫ x in (x₀ - δ)..(x₀ + δ), (x : ℂ) ^ (z₁ - 1) * (1 - (x : ℂ)) ^ (z₂ - 1)))
    (∫ x in (x₀ + δ)..(1 - a), (x : ℂ) ^ (z₁ - 1) * (1 - (x : ℂ)) ^ (z₂ - 1))
  have t3 := norm_add_le
    ((∫ x in (0 : ℝ)..a, (x : ℂ) ^ (z₁ - 1) * (1 - (x : ℂ)) ^ (z₂ - 1)) +
     (∫ x in a..(x₀ - δ), (x : ℂ) ^ (z₁ - 1) * (1 - (x : ℂ)) ^ (z₂ - 1)))
    (∫ x in (x₀ - δ)..(x₀ + δ), (x : ℂ) ^ (z₁ - 1) * (1 - (x : ℂ)) ^ (z₂ - 1))
  have t4 := norm_add_le
    (∫ x in (0 : ℝ)..a, (x : ℂ) ^ (z₁ - 1) * (1 - (x : ℂ)) ^ (z₂ - 1))
    (∫ x in a..(x₀ - δ), (x : ℂ) ^ (z₁ - 1) * (1 - (x : ℂ)) ^ (z₂ - 1))
  have hsum : 2 / Real.sqrt T + 800 / Real.sqrt T + 2 / Real.sqrt T + 800 / Real.sqrt T +
      2 / Real.sqrt T ≤ 1610 / Real.sqrt T := by
    rw [show 2 / Real.sqrt T + 800 / Real.sqrt T + 2 / Real.sqrt T + 800 / Real.sqrt T +
      2 / Real.sqrt T = 1606 / Real.sqrt T by ring]
    exact div_le_div_of_nonneg_right (by norm_num) hsqTpos.le
  linarith [t1, t2, t3, t4, hb1, hb2, hb3, hb4, hb5, hsum]

private theorem betaIntegral_conj (z₁ z₂ : ℂ) (hre1 : 0 < z₁.re) (hre2 : 0 < z₂.re) :
    Complex.betaIntegral (starRingEnd ℂ z₁) (starRingEnd ℂ z₂) =
      starRingEnd ℂ (Complex.betaIntegral z₁ z₂) := by
  unfold Complex.betaIntegral
  have hconv := Complex.betaIntegral_convergent hre1 hre2
  have hclm := (Complex.conjCLE.toContinuousLinearMap.intervalIntegral_comp_comm hconv).symm
  simp only [ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply] at hclm
  rw [hclm]
  apply intervalIntegral.integral_congr_ae
  have h0 : ∀ᵐ x : ℝ ∂volume, x ≠ (0 : ℝ) := by rw [MeasureTheory.ae_iff]; simp
  have h1 : ∀ᵐ x : ℝ ∂volume, x ≠ (1 : ℝ) := by rw [MeasureTheory.ae_iff]; simp
  filter_upwards [h0, h1] with x hx0 hx1 hxmem
  rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hxmem
  have hxpos : 0 < x := hxmem.1
  have hxlt : x < 1 := lt_of_le_of_ne hxmem.2 hx1
  rw [betaIntegrand_eq_polar z₁ z₂ hxpos hxlt,
    betaIntegrand_eq_polar (starRingEnd ℂ z₁) (starRingEnd ℂ z₂) hxpos hxlt]
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_re, Complex.conj_im]
  congr 1
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

private theorem beta_dyadic_bound (z₁ z₂ : ℂ) {T : ℝ} (hT : 1 ≤ T)
    (hre1 : 1 / 2 ≤ z₁.re ∧ z₁.re ≤ 1) (hre2 : 1 / 2 ≤ z₂.re ∧ z₂.re ≤ 1)
    (him1 : T ≤ |z₁.im| ∧ |z₁.im| ≤ 2 * T) (him2 : T ≤ |z₂.im| ∧ |z₂.im| ≤ 2 * T) :
    ‖Complex.betaIntegral z₁ z₂‖ ≤ 1610 / Real.sqrt T := by
  have hpos_first : ∀ w₁ w₂ : ℂ,
      (1 / 2 ≤ w₁.re ∧ w₁.re ≤ 1) → (1 / 2 ≤ w₂.re ∧ w₂.re ≤ 1) →
      (T ≤ w₁.im ∧ w₁.im ≤ 2 * T) → (T ≤ |w₂.im| ∧ |w₂.im| ≤ 2 * T) →
      ‖Complex.betaIntegral w₁ w₂‖ ≤ 1610 / Real.sqrt T := by
    intro w₁ w₂ hr1 hr2 hi1 hi2
    rcases le_or_gt 0 w₂.im with hnn | hneg
    · rw [abs_of_nonneg hnn] at hi2
      exact beta_same_sign_bound w₁ w₂ hT hr1 hr2 hi1 hi2
    · rw [abs_of_neg hneg] at hi2
      exact (beta_opposite_sign_bound w₁ w₂ hT hr1 hr2 hi1 ⟨by linarith, by linarith⟩).trans
        (div_le_div_of_nonneg_right (by norm_num) (Real.sqrt_nonneg T))
  rcases le_or_gt 0 z₁.im with hnn | hneg
  · rw [abs_of_nonneg hnn] at him1
    exact hpos_first z₁ z₂ hre1 hre2 him1 him2
  · rw [abs_of_neg hneg] at him1
    have hconj : ‖Complex.betaIntegral z₁ z₂‖ =
        ‖Complex.betaIntegral (starRingEnd ℂ z₁) (starRingEnd ℂ z₂)‖ := by
      rw [betaIntegral_conj z₁ z₂ (by linarith) (by linarith), Complex.norm_conj]
    rw [hconj]
    exact hpos_first (starRingEnd ℂ z₁) (starRingEnd ℂ z₂)
      (by simpa using hre1) (by simpa using hre2)
      (by simp; constructor <;> linarith)
      (by simp; exact him2)

theorem main_theorem :
    let B := Σ s : ℕ, DirichletCharacter ℂ s
    let primitive := fun b : B => b.1 ≠ 0 ∧ b.2.IsPrimitive
    let zeroAt := fun (b : B) (z : ℂ) => if h : b.1 ≠ 0 then
      letI : NeZero b.1 := ⟨h⟩
      DirichletCharacter.LFunction b.2 z = 0
      else False
    let N := fun (F : Finset B) (w : B → ℝ) => (∑ b ∈ F, |w b| ^ (6 / 5 : ℝ)) ^ (5 / 6 : ℝ)
    (∀ m : ℕ, 0 < m → Even m → ∀ F : Finset B, (∀ b ∈ F, primitive b) →
      ∀ u v : B → ℝ, (∑ a ∈ F, ∑ b ∈ F, |u a| * ‖Sfun a.2 b.2 m‖ * |v b|)
        ≤ (3 : ℝ) ^ (1 / 3 : ℝ) * ‖Ofun m‖ * N F u * N F v) ∧
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (T : ℝ), 0 < m → Even m → 1 ≤ T →
      ∀ (n : ℕ) (χ : Fin n → B) (z u v : Fin n → ℂ),
      (∀ i, primitive (χ i) ∧ zeroAt (χ i) (z i) ∧
        1 / 2 ≤ (z i).re ∧ (z i).re ≤ 1 ∧ T ≤ |(z i).im| ∧ |(z i).im| ≤ 2 * T) →
      let F := Finset.univ.image χ
      let W := fun (w : Fin n → ℂ) (b : B) =>
        ∑ i ∈ Finset.univ.filter (fun i => χ i = b), ‖w i‖ * (m : ℝ) ^ ((z i).re - 1)
      let K := fun i j : Fin n => Complex.Gamma (z i) * Complex.Gamma (z j) /
        Complex.Gamma (z i + z j) * (m : ℂ) ^ (z i + z j - 1)
      ‖∑ i : Fin n, ∑ j : Fin n, u i * v j * Sfun (χ i).2 (χ j).2 m * K i j‖
        ≤ C * (m : ℝ) * ‖Ofun m‖ / Real.sqrt T * N F (W u) * N F (W v) := by
  refine ⟨fun m hm he F hF u v => bilinear_bound m hm he F hF u v, ?_⟩
  refine ⟨1610 * (3 : ℝ) ^ (1 / 3 : ℝ), by positivity, ?_⟩
  intro m T hm he hT n χ z u v hcond
  dsimp only
  let B := Σ s : ℕ, DirichletCharacter ℂ s
  let F : Finset B := Finset.univ.image χ
  let W : (Fin n → ℂ) → B → ℝ := fun w b =>
    ∑ i ∈ Finset.univ.filter (fun i => χ i = b), ‖w i‖ * (m : ℝ) ^ ((z i).re - 1)
  let K : Fin n → Fin n → ℂ := fun i j =>
    Complex.Gamma (z i) * Complex.Gamma (z j) / Complex.Gamma (z i + z j) *
      (m : ℂ) ^ (z i + z j - 1)
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hK_bound (i j : Fin n) :
      ‖K i j‖ ≤ 1610 / Real.sqrt T * (m : ℝ) *
        (m : ℝ) ^ ((z i).re - 1) * (m : ℝ) ^ ((z j).re - 1) := by
    dsimp only [K]
    have hre_i := (hcond i).2.2.1
    have hre_i' := (hcond i).2.2.2.1
    have him_i := (hcond i).2.2.2.2
    have hre_j := (hcond j).2.2.1
    have hre_j' := (hcond j).2.2.2.1
    have him_j := (hcond j).2.2.2.2
    have hGne : Complex.Gamma (z i + z j) ≠ 0 :=
      Complex.Gamma_ne_zero_of_re_pos (by simp only [Complex.add_re]; linarith)
    have hbeta : Complex.Gamma (z i) * Complex.Gamma (z j) / Complex.Gamma (z i + z j) =
        Complex.betaIntegral (z i) (z j) := by
      rw [Complex.Gamma_mul_Gamma_eq_betaIntegral (by linarith) (by linarith),
        mul_div_cancel_left₀ _ hGne]
    rw [hbeta, norm_mul, show (m : ℂ) = ((m : ℝ) : ℂ) from (Complex.ofReal_natCast m).symm,
      Complex.norm_cpow_eq_rpow_re_of_pos hm_pos]
    have hmpow : (m : ℝ) ^ (z i + z j - 1).re =
        (m : ℝ) * (m : ℝ) ^ ((z i).re - 1) * (m : ℝ) ^ ((z j).re - 1) := by
      have hexp : (z i + z j - 1).re = 1 + ((z i).re - 1) + ((z j).re - 1) := by
        simp only [Complex.sub_re, Complex.add_re, Complex.one_re]; ring
      rw [hexp, Real.rpow_add hm_pos, Real.rpow_add hm_pos, Real.rpow_one]
    rw [hmpow]
    have hb := beta_dyadic_bound (z i) (z j) hT ⟨hre_i, hre_i'⟩ ⟨hre_j, hre_j'⟩ him_i him_j
    calc
      ‖Complex.betaIntegral (z i) (z j)‖ *
          ((m : ℝ) * (m : ℝ) ^ ((z i).re - 1) * (m : ℝ) ^ ((z j).re - 1))
          ≤ (1610 / Real.sqrt T) *
              ((m : ℝ) * (m : ℝ) ^ ((z i).re - 1) * (m : ℝ) ^ ((z j).re - 1)) :=
            mul_le_mul_of_nonneg_right hb (by positivity)
      _ = 1610 / Real.sqrt T * (m : ℝ) *
            (m : ℝ) ^ ((z i).re - 1) * (m : ℝ) ^ ((z j).re - 1) := by ring
  have hF_prim : ∀ b ∈ F, b.1 ≠ 0 ∧ b.2.IsPrimitive := by
    intro b hb
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hb
    exact (hcond i).1
  have hW_nn (w : Fin n → ℂ) (b : B) : 0 ≤ W w b :=
    Finset.sum_nonneg fun i _ => mul_nonneg (norm_nonneg _) (Real.rpow_nonneg hm_pos.le _)
  have hgroup :
      (∑ i : Fin n, ∑ j : Fin n,
        (‖u i‖ * (m : ℝ) ^ ((z i).re - 1)) * ‖Sfun (χ i).2 (χ j).2 m‖ *
          (‖v j‖ * (m : ℝ) ^ ((z j).re - 1))) =
      ∑ a ∈ F, ∑ b ∈ F, |W u a| * ‖Sfun a.2 b.2 m‖ * |W v b| := by
    have hinner (i : Fin n) :
        (∑ j : Fin n, (‖u i‖ * (m : ℝ) ^ ((z i).re - 1)) * ‖Sfun (χ i).2 (χ j).2 m‖ *
          (‖v j‖ * (m : ℝ) ^ ((z j).re - 1))) =
        ∑ b ∈ F, (‖u i‖ * (m : ℝ) ^ ((z i).re - 1)) * ‖Sfun (χ i).2 b.2 m‖ * W v b := by
      rw [← Finset.sum_fiberwise_of_maps_to (g := χ)
        (fun j _ => Finset.mem_image_of_mem χ (Finset.mem_univ j))]
      apply Finset.sum_congr rfl
      intro b _
      dsimp only [W]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      have hjb : χ j = b := (Finset.mem_filter.mp hj).2
      rw [hjb]
    calc
      (∑ i : Fin n, ∑ j : Fin n,
          (‖u i‖ * (m : ℝ) ^ ((z i).re - 1)) * ‖Sfun (χ i).2 (χ j).2 m‖ *
            (‖v j‖ * (m : ℝ) ^ ((z j).re - 1)))
          = ∑ i : Fin n, ∑ b ∈ F,
              (‖u i‖ * (m : ℝ) ^ ((z i).re - 1)) * ‖Sfun (χ i).2 b.2 m‖ * W v b :=
            Finset.sum_congr rfl fun i _ => hinner i
      _ = ∑ a ∈ F, ∑ i ∈ Finset.univ.filter (fun i => χ i = a), ∑ b ∈ F,
            (‖u i‖ * (m : ℝ) ^ ((z i).re - 1)) * ‖Sfun (χ i).2 b.2 m‖ * W v b :=
            (Finset.sum_fiberwise_of_maps_to (g := χ)
              (fun i _ => Finset.mem_image_of_mem χ (Finset.mem_univ i)) _).symm
      _ = ∑ a ∈ F, ∑ b ∈ F, |W u a| * ‖Sfun a.2 b.2 m‖ * |W v b| := by
            apply Finset.sum_congr rfl
            intro a _
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro b _
            rw [abs_of_nonneg (hW_nn u a), abs_of_nonneg (hW_nn v b)]
            dsimp only [W]
            rw [Finset.sum_mul, Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro i hi
            have hia : χ i = a := (Finset.mem_filter.mp hi).2
            rw [hia]
  have hbil := bilinear_bound m hm he F hF_prim (W u) (W v)
  calc
    ‖∑ i : Fin n, ∑ j : Fin n, u i * v j * Sfun (χ i).2 (χ j).2 m * K i j‖
        ≤ ∑ i : Fin n, ‖∑ j : Fin n, u i * v j * Sfun (χ i).2 (χ j).2 m * K i j‖ :=
          norm_sum_le _ _
    _ ≤ ∑ i : Fin n, ∑ j : Fin n, ‖u i * v j * Sfun (χ i).2 (χ j).2 m * K i j‖ :=
          Finset.sum_le_sum fun i _ => norm_sum_le _ _
    _ ≤ ∑ i : Fin n, ∑ j : Fin n,
          (1610 / Real.sqrt T * (m : ℝ)) *
            ((‖u i‖ * (m : ℝ) ^ ((z i).re - 1)) * ‖Sfun (χ i).2 (χ j).2 m‖ *
              (‖v j‖ * (m : ℝ) ^ ((z j).re - 1))) := by
          apply Finset.sum_le_sum; intro i _
          apply Finset.sum_le_sum; intro j _
          rw [norm_mul, norm_mul, norm_mul]
          calc
            ‖u i‖ * ‖v j‖ * ‖Sfun (χ i).2 (χ j).2 m‖ * ‖K i j‖
                ≤ ‖u i‖ * ‖v j‖ * ‖Sfun (χ i).2 (χ j).2 m‖ *
                    (1610 / Real.sqrt T * (m : ℝ) *
                      (m : ℝ) ^ ((z i).re - 1) * (m : ℝ) ^ ((z j).re - 1)) :=
                  mul_le_mul_of_nonneg_left (hK_bound i j) (by positivity)
            _ = (1610 / Real.sqrt T * (m : ℝ)) *
                  ((‖u i‖ * (m : ℝ) ^ ((z i).re - 1)) * ‖Sfun (χ i).2 (χ j).2 m‖ *
                    (‖v j‖ * (m : ℝ) ^ ((z j).re - 1))) := by ring
    _ = (1610 / Real.sqrt T * (m : ℝ)) *
          ∑ a ∈ F, ∑ b ∈ F, |W u a| * ‖Sfun a.2 b.2 m‖ * |W v b| := by
          rw [← hgroup, Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm
    _ ≤ (1610 / Real.sqrt T * (m : ℝ)) *
          ((3 : ℝ) ^ (1 / 3 : ℝ) * ‖Ofun m‖ *
            (∑ a ∈ F, |W u a| ^ (6 / 5 : ℝ)) ^ (5 / 6 : ℝ) *
            (∑ b ∈ F, |W v b| ^ (6 / 5 : ℝ)) ^ (5 / 6 : ℝ)) :=
          mul_le_mul_of_nonneg_left hbil (by positivity)
    _ = 1610 * (3 : ℝ) ^ (1 / 3 : ℝ) * (m : ℝ) * ‖Ofun m‖ / Real.sqrt T *
          (∑ a ∈ F, |W u a| ^ (6 / 5 : ℝ)) ^ (5 / 6 : ℝ) *
          (∑ b ∈ F, |W v b| ^ (6 / 5 : ℝ)) ^ (5 / 6 : ℝ) := by ring

end PartnerDyadicZeroBlockProof

theorem Conjectures.Goldbach.PartnerDyadicZeroBlock :
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
  let B := Σ s : ℕ, DirichletCharacter ℂ s
  let primitive := fun b : B => b.1 ≠ 0 ∧ b.2.IsPrimitive
  let zeroAt := fun (b : B) (z : ℂ) => if h : b.1 ≠ 0 then
    letI : NeZero b.1 := ⟨h⟩
    DirichletCharacter.LFunction b.2 z = 0
    else False
  let N := fun (F : Finset B) (w : B → ℝ) => (∑ b ∈ F, |w b| ^ (6/5 : ℝ)) ^ (5/6 : ℝ)
  exact
    (∀ m : ℕ, 0 < m → Even m → ∀ F : Finset B, (∀ b ∈ F, primitive b) →
      ∀ u v : B → ℝ, (∑ a ∈ F, ∑ b ∈ F, |u a| * ‖S a.2 b.2 m‖ * |v b|)
        ≤ (3 : ℝ)^(1/3 : ℝ) * ‖O m‖ * N F u * N F v) ∧
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (T : ℝ), 0 < m → Even m → 1 ≤ T →
      ∀ (n : ℕ) (χ : Fin n → B) (z u v : Fin n → ℂ),
      (∀ i, primitive (χ i) ∧ zeroAt (χ i) (z i) ∧
        1/2 ≤ (z i).re ∧ (z i).re ≤ 1 ∧ T ≤ |(z i).im| ∧ |(z i).im| ≤ 2*T) →
      let F := Finset.univ.image χ
      let W := fun (w : Fin n → ℂ) (b : B) =>
        ∑ i ∈ Finset.univ.filter (fun i => χ i = b), ‖w i‖ * (m : ℝ)^((z i).re-1)
      let K := fun i j : Fin n => Complex.Gamma (z i) * Complex.Gamma (z j) /
        Complex.Gamma (z i + z j) * (m : ℂ)^(z i + z j - 1)
      ‖∑ i : Fin n, ∑ j : Fin n, u i * v j * S (χ i).2 (χ j).2 m * K i j‖
        ≤ C * (m : ℝ) * ‖O m‖ / Real.sqrt T * N F (W u) * N F (W v) := by
  classical
  dsimp only
  exact PartnerDyadicZeroBlockProof.main_theorem
