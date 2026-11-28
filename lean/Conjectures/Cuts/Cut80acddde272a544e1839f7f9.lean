import Mathlib
import Conjectures.Goldbach.Type2MovingDiagonalMoment
import Conjectures.Cuts.Taskf7c18a375028fb1ff2783f5b

-- child 1 zh: 控制无共享指标且左右各存在一对下标普通和相等的四元组多项式等和碰撞数。
-- child 1 en: Bound disjoint-index quadruple polynomial collisions that contain a pair on each side with equal ordinary sum.
-- child 2 zh: 控制无共享指标且左右各存在一对下标平方和相等的四元组多项式等和碰撞数。
-- child 2 en: Bound disjoint-index quadruple polynomial collisions that contain a pair on each side with equal sum of squares.
-- child 3 zh: 控制既无共享指标、又无匹配两项普通和及两项平方和的四元组多项式等和碰撞数。
-- child 3 en: Bound disjoint-index quadruple polynomial collisions with neither equal pair sums nor equal pair sums of squares.

namespace GoldbachCutDisjointDecomp

open Finset DyadicMixedB4Fourier
open scoped BigOperators

def tuples (A : Finset ℕ) (k : ℕ) : Finset (Fin k → ℕ) :=
  Fintype.piFinset fun _ : Fin k => A

def score (f : ℕ → ℤ) {k : ℕ} (u : Fin k → ℕ) : ℤ :=
  ∑ i : Fin k, f (u i)

def collisions (A : Finset ℕ) (f : ℕ → ℤ) (k : ℕ) :
    Finset ((Fin k → ℕ) × (Fin k → ℕ)) :=
  ((tuples A k).product (tuples A k)).filter fun p => score f p.1 = score f p.2

def shared (A : Finset ℕ) (f : ℕ → ℤ) (k : ℕ) :
    Finset ((Fin k → ℕ) × (Fin k → ℕ)) := by
  classical
  exact (collisions A f k).filter fun p => ∃ i j : Fin k, p.1 i = p.2 j

def disjoint (A : Finset ℕ) (f : ℕ → ℤ) (k : ℕ) :
    Finset ((Fin k → ℕ) × (Fin k → ℕ)) := by
  classical
  exact (collisions A f k).filter fun p => ∀ i j : Fin k, p.1 i ≠ p.2 j

theorem shared_card_le (A : Finset ℕ) (f : ℕ → ℤ) (k : ℕ) :
    (shared A f (k + 1)).card ≤ (k + 1) ^ 2 * A.card * (collisions A f k).card := by
  classical
  let remove (i : Fin (k + 1)) (u : Fin (k + 1) → ℕ) (j : Fin k) : ℕ :=
    u (i.succAbove j)
  let positions (p : (Fin (k + 1) → ℕ) × (Fin (k + 1) → ℕ)) :
      Fin (k + 1) × Fin (k + 1) :=
    if h : ∃ q : Fin (k + 1) × Fin (k + 1), p.1 q.1 = p.2 q.2 then
      Classical.choose h
    else (0, 0)
  have chosen (p : (Fin (k + 1) → ℕ) × (Fin (k + 1) → ℕ))
      (hp : p ∈ shared A f (k + 1)) :
      p.1 (positions p).1 = p.2 (positions p).2 := by
    have hs : ∃ i j : Fin (k + 1), p.1 i = p.2 j := (Finset.mem_filter.mp hp).2
    have he : ∃ q : Fin (k + 1) × Fin (k + 1), p.1 q.1 = p.2 q.2 := by
      rcases hs with ⟨i, j, hij⟩
      exact ⟨(i, j), hij⟩
    simpa only [positions, dite_eq_left he] using Classical.choose_spec he
  let pack (p : (Fin (k + 1) → ℕ) × (Fin (k + 1) → ℕ)) :
      (Fin (k + 1) × Fin (k + 1)) × (ℕ × ((Fin k → ℕ) × (Fin k → ℕ))) :=
    (positions p, p.1 (positions p).1,
      (remove (positions p).1 p.1, remove (positions p).2 p.2))
  let target := (Finset.univ : Finset (Fin (k + 1) × Fin (k + 1))).product
    (A.product (collisions A f k))
  have sum_remove (i : Fin (k + 1)) (u : Fin (k + 1) → ℕ) :
      score f u = f (u i) + score f (remove i u) :=
    Fin.sum_univ_succAbove (fun j => f (u j)) i
  have pack_mem : Set.MapsTo pack (shared A f (k + 1)) target := by
    intro p hp
    have hcol : p ∈ collisions A f (k + 1) := (Finset.mem_filter.mp hp).1
    have hwords : p ∈ (tuples A (k + 1)).product (tuples A (k + 1)) :=
      (Finset.mem_filter.mp hcol).1
    have heq : score f p.1 = score f p.2 := (Finset.mem_filter.mp hcol).2
    have hL : ∀ a : Fin (k + 1), p.1 a ∈ A :=
      Fintype.mem_piFinset.mp (Finset.mem_product.mp hwords).1
    have hR : ∀ a : Fin (k + 1), p.2 a ∈ A :=
      Fintype.mem_piFinset.mp (Finset.mem_product.mp hwords).2
    have heval := congrArg f (chosen p hp)
    rw [sum_remove (positions p).1 p.1, sum_remove (positions p).2 p.2, heval] at heq
    have hsub : score f (remove (positions p).1 p.1) =
        score f (remove (positions p).2 p.2) := add_left_cancel heq
    have hu : remove (positions p).1 p.1 ∈ tuples A k :=
      Fintype.mem_piFinset.mpr fun a => hL _
    have hv : remove (positions p).2 p.2 ∈ tuples A k :=
      Fintype.mem_piFinset.mpr fun a => hR _
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_product.mpr
      ⟨hL _, Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hu, hv⟩, hsub⟩⟩⟩
  have restore (i : Fin (k + 1)) (u v : Fin (k + 1) → ℕ)
      (h : u i = v i) (hrest : remove i u = remove i v) : u = v := by
    funext j
    by_cases hj : j = i
    · simpa only [hj] using h
    · obtain ⟨m, rfl⟩ := Fin.exists_succAbove_eq hj
      exact congrFun hrest m
  have pack_inj : (shared A f (k + 1) : Set ((Fin (k + 1) → ℕ) × (Fin (k + 1) → ℕ))).InjOn pack := by
    intro p hp p' hp' h
    have hpos : positions p = positions p' := congrArg Prod.fst h
    have hfirst : p.1 (positions p).1 = p'.1 (positions p').1 :=
      congrArg (fun u => u.2.1) h
    have hleft : remove (positions p).1 p.1 = remove (positions p').1 p'.1 :=
      congrArg (fun u => u.2.2.1) h
    have hright : remove (positions p).2 p.2 = remove (positions p').2 p'.2 :=
      congrArg (fun u => u.2.2.2) h
    have hsecond : p.2 (positions p).2 = p'.2 (positions p').2 :=
      (chosen p hp).symm.trans (hfirst.trans (chosen p' hp'))
    rw [← hpos] at hfirst hleft hright hsecond
    exact Prod.ext (restore (positions p).1 p.1 p'.1 hfirst hleft)
      (restore (positions p).2 p.2 p'.2 hsecond hright)
  have hcard : target.card = (k + 1) ^ 2 * A.card * (collisions A f k).card := by
    simp only [target, Finset.card_product, Finset.card_univ, Fintype.card_prod,
      Fintype.card_fin]
    ring
  exact (Finset.card_le_card_of_injOn pack pack_mem pack_inj).trans hcard.le

theorem collision_card_le (A : Finset ℕ) (f : ℕ → ℤ) (k : ℕ) :
    (collisions A f (k + 1)).card ≤
      (disjoint A f (k + 1)).card + (k + 1) ^ 2 * A.card * (collisions A f k).card := by
  classical
  have hcover : collisions A f (k + 1) ⊆ disjoint A f (k + 1) ∪ shared A f (k + 1) := by
    intro p hp
    by_cases h : ∃ i j : Fin (k + 1), p.1 i = p.2 j
    · apply Finset.mem_union_right
      exact Finset.mem_filter.mpr ⟨hp, h⟩
    · apply Finset.mem_union_left
      exact Finset.mem_filter.mpr ⟨hp, fun i j hij => h ⟨i, j, hij⟩⟩
  exact (Finset.card_le_card hcover).trans ((Finset.card_union_le _ _).trans
    (Nat.add_le_add_left (shared_card_le A f k) _))

theorem four_card_le_of_moment_interpolation (A : Finset ℕ) (f : ℕ → ℤ)
    (hCS : ((collisions A f 3).card : ℝ) ^ 2 ≤
      ((collisions A f 2).card : ℝ) * ((collisions A f 4).card : ℝ)) :
    ((collisions A f 4).card : ℝ) ≤
      2 * ((disjoint A f 4).card : ℝ) +
        256 * (A.card : ℝ) ^ 2 * ((collisions A f 2).card : ℝ) := by
  let Z : ℝ := A.card
  let D : ℝ := (disjoint A f 4).card
  let E (s : ℕ) : ℝ := (collisions A f s).card
  change E 4 ≤ 2 * D + 256 * Z ^ 2 * E 2
  change E 3 ^ 2 ≤ E 2 * E 4 at hCS
  have hCountNat : (collisions A f 4).card ≤
      (disjoint A f 4).card + 16 * A.card * (collisions A f 3).card :=
    collision_card_le A f 3
  have hCount : E 4 ≤ D + 16 * Z * E 3 := by
    dsimp only [D, E, Z]
    exact_mod_cast hCountNat
  have hZ : 0 ≤ Z := Nat.cast_nonneg _
  have hE (s : ℕ) : 0 ≤ E s := Nat.cast_nonneg _
  have hSquared : (16 * Z * E 3) ^ 2 ≤ (E 4 / 2 + 128 * Z ^ 2 * E 2) ^ 2 := by
    calc
      (16 * Z * E 3) ^ 2 = (256 * Z ^ 2) * (E 3) ^ 2 := by ring
      _ ≤ (256 * Z ^ 2) * (E 2 * E 4) :=
        mul_le_mul_of_nonneg_left hCS (by positivity)
      _ ≤ (E 4 / 2 + 128 * Z ^ 2 * E 2) ^ 2 := by
        nlinarith only [sq_nonneg (E 4 / 2 - 128 * Z ^ 2 * E 2)]
  have hAbsorb : 16 * Z * E 3 ≤ E 4 / 2 + 128 * Z ^ 2 * E 2 := by
    by_contra! h
    exact (not_lt_of_ge hSquared) (pow_lt_pow_left₀ h (by positivity) (by decide))
  linarith only [hCount, hAbsorb]

noncomputable def expSum (A : Finset ℕ) (f : ℕ → ℤ) (t : ℝ) : ℂ :=
  ∑ n ∈ A, mode (f n) t

theorem continuous_expSum (A : Finset ℕ) (f : ℕ → ℤ) : Continuous (expSum A f) := by
  unfold expSum
  exact continuous_finset_sum A fun n _ => continuous_mode (f n)

theorem collisions_card_eq_integral (A : Finset ℕ) (f : ℕ → ℤ) (k : ℕ) :
    ∫ t in (0 : ℝ)..1, ‖expSum A f t‖ ^ (2 * k) = ((collisions A f k).card : ℝ) := by
  classical
  let K := expSum A f
  let Q := tuples A k
  let F := score f (k := k)
  have hpow (t : ℝ) : K t ^ k = ∑ x ∈ Q, mode (F x) t := by
    dsimp only [K, expSum]
    rw [sum_pow']
    apply sum_congr rfl
    intro x _
    unfold mode frequency
    rw [← Complex.exp_sum]
    congr 1
    dsimp [F, score]
    push_cast
    simp only [mul_sum, sum_mul]
    apply sum_congr rfl
    intro i _
    ring
  let P := Q ×ˢ Q
  let delta (p : (Fin k → ℕ) × (Fin k → ℕ)) := F p.1 - F p.2
  have hpoint (t : ℝ) : ((‖K t‖ ^ (2 * k) : ℝ) : ℂ) = ∑ p ∈ P, mode (delta p) t := by
    rw [show ‖K t‖ ^ (2 * k) = ‖K t ^ k‖ ^ 2 by rw [norm_pow, ← pow_mul, mul_comm],
      Complex.ofReal_pow, ← Complex.mul_conj', hpow]
    change (∑ x ∈ Q, mode (F x) t) * star (∑ x ∈ Q, mode (F x) t) = _
    rw [star_sum, sum_mul_sum, Finset.sum_product]
    exact sum_congr rfl fun x _ => sum_congr rfl fun y _ => mode_mul_conj _ _ _
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  calc
    (∫ t in (0 : ℝ)..1, ((‖K t‖ ^ (2 * k) : ℝ) : ℂ))
      = ∫ t in (0 : ℝ)..1, ∑ p ∈ P, mode (delta p) t :=
          intervalIntegral.integral_congr fun t _ => hpoint t
    _ = ∑ p ∈ P, ∫ t in (0 : ℝ)..1, mode (delta p) t :=
          intervalIntegral.integral_finsetSum fun p _ =>
            (continuous_mode _).intervalIntegrable _ _
    _ = (((collisions A f k).card : ℝ) : ℂ) := by
          simp only [mode_integral, delta, sub_eq_zero, ← sum_filter, sum_const,
            nsmul_eq_mul, mul_one]
          norm_cast

theorem triple_sq_le_pair_mul_quad (A : Finset ℕ) (f : ℕ → ℤ) :
    ((collisions A f 3).card : ℝ) ^ 2 ≤
      ((collisions A f 2).card : ℝ) * ((collisions A f 4).card : ℝ) := by
  classical
  by_cases hA : A.Nonempty
  · obtain ⟨a₀, ha₀⟩ := hA
    let u₀ : Fin 2 → ℕ := fun _ => a₀
    have hu₀ : u₀ ∈ tuples A 2 := Fintype.mem_piFinset.mpr fun _ => ha₀
    have hmem : (u₀, u₀) ∈ collisions A f 2 :=
      Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hu₀, hu₀⟩, rfl⟩
    have hE2pos : (0 : ℝ) < ((collisions A f 2).card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr ⟨(u₀, u₀), hmem⟩
    let E2 : ℝ := ((collisions A f 2).card : ℝ)
    let E3 : ℝ := ((collisions A f 3).card : ℝ)
    let E4 : ℝ := ((collisions A f 4).card : ℝ)
    let K := expSum A f
    have hnonneg : 0 ≤ ∫ t in (0 : ℝ)..1, (E2 * ‖K t‖ ^ 4 - E3 * ‖K t‖ ^ 2) ^ 2 :=
      intervalIntegral.integral_nonneg (by norm_num) fun t _ => sq_nonneg _
    have hI2 : ∫ t in (0 : ℝ)..1, ‖K t‖ ^ 4 = E2 := by
      simpa [K, E2] using collisions_card_eq_integral A f 2
    have hI3 : ∫ t in (0 : ℝ)..1, ‖K t‖ ^ 6 = E3 := by
      simpa [K, E3] using collisions_card_eq_integral A f 3
    have hI4 : ∫ t in (0 : ℝ)..1, ‖K t‖ ^ 8 = E4 := by
      simpa [K, E4] using collisions_card_eq_integral A f 4
    have hcont8 : IntervalIntegrable (fun t : ℝ => ‖K t‖ ^ 8) MeasureTheory.volume 0 1 :=
      ((continuous_expSum A f).norm.pow 8).intervalIntegrable 0 1
    have hcont6 : IntervalIntegrable (fun t : ℝ => ‖K t‖ ^ 6) MeasureTheory.volume 0 1 :=
      ((continuous_expSum A f).norm.pow 6).intervalIntegrable 0 1
    have hcont4 : IntervalIntegrable (fun t : ℝ => ‖K t‖ ^ 4) MeasureTheory.volume 0 1 :=
      ((continuous_expSum A f).norm.pow 4).intervalIntegrable 0 1
    have hexpand :
        (∫ t in (0 : ℝ)..1, (E2 * ‖K t‖ ^ 4 - E3 * ‖K t‖ ^ 2) ^ 2) =
          E2 * (E2 * E4 - E3 ^ 2) := by
      have hfn : ∀ t : ℝ, (E2 * ‖K t‖ ^ 4 - E3 * ‖K t‖ ^ 2) ^ 2 =
          E2 ^ 2 * ‖K t‖ ^ 8 + (-(2 * E2 * E3)) * ‖K t‖ ^ 6 + E3 ^ 2 * ‖K t‖ ^ 4 := by
        intro t
        ring
      simp_rw [hfn]
      rw [intervalIntegral.integral_add ((hcont8.const_mul _).add (hcont6.const_mul _))
        (hcont4.const_mul _)]
      rw [intervalIntegral.integral_add (hcont8.const_mul _) (hcont6.const_mul _)]
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul, hI4, hI3, hI2]
      ring
    rw [hexpand] at hnonneg
    have hdiff : 0 ≤ E2 * E4 - E3 ^ 2 :=
      nonneg_of_mul_nonneg_right hnonneg hE2pos
    linarith only [hdiff]
  · have hEmpty : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hA
    have h3 : (collisions A f 3).card = 0 := by
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_not_mem]
      intro p hp
      have hm := (Finset.mem_filter.mp hp).1
      have hp1 := Fintype.mem_piFinset.mp (Finset.mem_product.mp hm).1 0
      rw [hEmpty] at hp1
      exact Finset.not_mem_empty _ hp1
    rw [h3]
    norm_num
    positivity

theorem pair_collisions_card_eq_subtype (P : Polynomial ℤ) (A : Finset ℕ) :
    (collisions A (fun n => P.eval (n : ℤ)) 2).card =
      ({z ∈ (Finset.univ : Finset ((Fin 2 → ↥A) × (Fin 2 → ↥A))) |
        (∑ i : Fin 2, P.eval ((z.1 i : ℕ) : ℤ)) =
          ∑ i : Fin 2, P.eval ((z.2 i : ℕ) : ℤ)}).card := by
  classical
  let mapFn (z : (Fin 2 → ↥A) × (Fin 2 → ↥A)) : (Fin 2 → ℕ) × (Fin 2 → ℕ) :=
    (fun i => (z.1 i : ℕ), fun i => (z.2 i : ℕ))
  symm
  apply Finset.card_bij (fun z _ => mapFn z)
  · intro z hz
    have hsum := (Finset.mem_filter.mp hz).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, hsum⟩
    · exact Fintype.mem_piFinset.mpr fun i => (z.1 i).property
    · exact Fintype.mem_piFinset.mpr fun i => (z.2 i).property
  · intro z₁ _ z₂ _ heq
    apply Prod.ext
    · funext i
      exact Subtype.ext (congrFun (congrArg Prod.fst heq) i)
    · funext i
      exact Subtype.ext (congrFun (congrArg Prod.snd heq) i)
  · intro p hp
    obtain ⟨hwords, hsum⟩ := Finset.mem_filter.mp hp
    obtain ⟨hleft, hright⟩ := Finset.mem_product.mp hwords
    have hL : ∀ i : Fin 2, p.1 i ∈ A := Fintype.mem_piFinset.mp hleft
    have hR : ∀ i : Fin 2, p.2 i ∈ A := Fintype.mem_piFinset.mp hright
    refine ⟨(fun i => ⟨p.1 i, hL i⟩, fun i => ⟨p.2 i, hR i⟩),
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsum⟩, rfl⟩

end GoldbachCutDisjointDecomp

open Finset GoldbachCutDisjointDecomp

theorem Conjectures.Cuts.Cut80acddde272a544e1839f7f9
  (hPairSum : by
    classical
    exact ∀ P : Polynomial ℤ, 3 ≤ P.natDegree → ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ, 2 ≤ M → ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 M →
        let T := Fintype.piFinset (fun _ : Fin 4 => A)
        let w := fun u : Fin 4 → ℕ => ∑ j : Fin 4, P.eval (u j : ℤ)
        (((T.product T).filter (fun z => w z.1 = w z.2 ∧
          (∀ i j : Fin 4, z.1 i ≠ z.2 j) ∧
          (∃ i₁ i₂ j₁ j₂ : Fin 4, i₁ ≠ i₂ ∧ j₁ ≠ j₂ ∧
            z.1 i₁ + z.1 i₂ = z.2 j₁ + z.2 j₂))).card : ℝ) ≤
          C * (M : ℝ) ^ ε * (A.card : ℝ) ^ 4)
  (hPairSq : by
    classical
    exact ∀ P : Polynomial ℤ, 3 ≤ P.natDegree → ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ, 2 ≤ M → ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 M →
        let T := Fintype.piFinset (fun _ : Fin 4 => A)
        let w := fun u : Fin 4 → ℕ => ∑ j : Fin 4, P.eval (u j : ℤ)
        (((T.product T).filter (fun z => w z.1 = w z.2 ∧
          (∀ i j : Fin 4, z.1 i ≠ z.2 j) ∧
          (∃ i₁ i₂ j₁ j₂ : Fin 4, i₁ ≠ i₂ ∧ j₁ ≠ j₂ ∧
            (z.1 i₁)^2 + (z.1 i₂)^2 = (z.2 j₁)^2 + (z.2 j₂)^2))).card : ℝ) ≤
          C * (M : ℝ) ^ ε * (A.card : ℝ) ^ 4)
  (hResidual : by
    classical
    exact ∀ P : Polynomial ℤ, 3 ≤ P.natDegree → ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ, 2 ≤ M → ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 M →
        let T := Fintype.piFinset (fun _ : Fin 4 => A)
        let w := fun u : Fin 4 → ℕ => ∑ j : Fin 4, P.eval (u j : ℤ)
        (((T.product T).filter (fun z => w z.1 = w z.2 ∧
          (∀ i j : Fin 4, z.1 i ≠ z.2 j) ∧
          ¬(∃ i₁ i₂ j₁ j₂ : Fin 4, i₁ ≠ i₂ ∧ j₁ ≠ j₂ ∧
            z.1 i₁ + z.1 i₂ = z.2 j₁ + z.2 j₂) ∧
          ¬(∃ i₁ i₂ j₁ j₂ : Fin 4, i₁ ≠ i₂ ∧ j₁ ≠ j₂ ∧
            (z.1 i₁)^2 + (z.1 i₂)^2 = (z.2 j₁)^2 + (z.2 j₂)^2))).card : ℝ) ≤
          C * (M : ℝ) ^ ε * (A.card : ℝ) ^ (if P.natDegree = 3 then (5 : ℕ) else 4)) : (∀ (x1 : Polynomial ℤ),   (3 : ℕ) ≤ x1.natDegree →     ∀ (x3 : ℝ),       (0 : ℝ) < x3 →         ∃ (x5 : ℝ),           (0 : ℝ) < x5 ∧             ∀ (x6 : ℕ),               (2 : ℕ) ≤ x6 →                 ∀ x8 ⊆ Finset.Icc (1 : ℕ) x6,                   have x10 : Finset (Fin (4 : ℕ) → ℕ) := Fintype.piFinset fun (x10 : Fin (4 : ℕ)) => x8;                   have x11 : (Fin (4 : ℕ) → ℕ) → ℤ := fun (x11 : Fin (4 : ℕ) → ℕ) => ∑ x12 : Fin (4 : ℕ), Polynomial.eval (↑(x11 x12)) x1;                   ↑{x12 ∈ x10.product x10 | x11 x12.1 = x11 x12.2 ∧ ∀ (x13 : Equiv.Perm (Fin (4 : ℕ))), x12.2 ≠ x12.1 ∘ ⇑x13}.card ≤ x5 * ↑x6 ^ x3 * ↑x8.card ^ if x1.natDegree = (3 : ℕ) then (5 : ℕ) else (4 : ℕ)) := by
  classical
  intro P hP ε hε
  obtain ⟨Csum, hCsum, bSum⟩ := hPairSum P hP ε hε
  obtain ⟨Csq, hCsq, bSq⟩ := hPairSq P hP ε hε
  obtain ⟨Cres, hCres, bRes⟩ := hResidual P hP ε hε
  obtain ⟨C2, hC2, b2⟩ := Conjectures.Cuts.Taskf7c18a375028fb1ff2783f5b P (by omega) ε hε
  refine ⟨2 * Csum + 2 * Csq + 2 * Cres + 256 * C2, by positivity, ?_⟩
  intro M hM A hA
  let f : ℕ → ℤ := fun n => P.eval (n : ℤ)
  let T := tuples A 4
  let w := score f (k := 4)
  let off := (T.product T).filter (fun z => w z.1 = w z.2 ∧ ∀ σ : Equiv.Perm (Fin 4), z.2 ≠ z.1 ∘ σ)
  let pSum (z : (Fin 4 → ℕ) × (Fin 4 → ℕ)) : Prop :=
    ∃ i₁ i₂ j₁ j₂ : Fin 4, i₁ ≠ i₂ ∧ j₁ ≠ j₂ ∧ z.1 i₁ + z.1 i₂ = z.2 j₁ + z.2 j₂
  let pSq (z : (Fin 4 → ℕ) × (Fin 4 → ℕ)) : Prop :=
    ∃ i₁ i₂ j₁ j₂ : Fin 4, i₁ ≠ i₂ ∧ j₁ ≠ j₂ ∧
      (z.1 i₁) ^ 2 + (z.1 i₂) ^ 2 = (z.2 j₁) ^ 2 + (z.2 j₂) ^ 2
  let Ssum := (T.product T).filter (fun z => w z.1 = w z.2 ∧ (∀ i j : Fin 4, z.1 i ≠ z.2 j) ∧ pSum z)
  let Ssq := (T.product T).filter (fun z => w z.1 = w z.2 ∧ (∀ i j : Fin 4, z.1 i ≠ z.2 j) ∧ pSq z)
  let Sres := (T.product T).filter (fun z => w z.1 = w z.2 ∧ (∀ i j : Fin 4, z.1 i ≠ z.2 j) ∧ ¬pSum z ∧ ¬pSq z)
  have hoff : off.card ≤ (collisions A f 4).card := by
    apply Finset.card_le_card
    intro z hz
    obtain ⟨hm, heq, _⟩ := Finset.mem_filter.mp hz
    exact Finset.mem_filter.mpr ⟨hm, heq⟩
  have hcover : disjoint A f 4 ⊆ Ssum ∪ Ssq ∪ Sres := by
    intro z hz
    obtain ⟨hcol, hdisj⟩ := Finset.mem_filter.mp hz
    obtain ⟨hm, heq⟩ := Finset.mem_filter.mp hcol
    by_cases hs : pSum z
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨hm, heq, hdisj, hs⟩))
    · by_cases hq : pSq z
      · exact Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨hm, heq, hdisj, hq⟩))
      · exact Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨hm, heq, hdisj, hs, hq⟩)
  have hdisjCard : ((disjoint A f 4).card : ℝ) ≤ (Ssum.card : ℝ) + (Ssq.card : ℝ) + (Sres.card : ℝ) := by
    have hNat : (disjoint A f 4).card ≤ Ssum.card + Ssq.card + Sres.card :=
      (Finset.card_le_card hcover).trans ((Finset.card_union_le _ _).trans
        (Nat.add_le_add_right (Finset.card_union_le _ _) _))
    exact_mod_cast hNat
  have hInterp : ((collisions A f 4).card : ℝ) ≤
      2 * ((disjoint A f 4).card : ℝ) + 256 * (A.card : ℝ) ^ 2 * ((collisions A f 2).card : ℝ) :=
    four_card_le_of_moment_interpolation A f (triple_sq_le_pair_mul_quad A f)
  have hE2 : ((collisions A f 2).card : ℝ) ≤ C2 * (M : ℝ) ^ ε * (A.card : ℝ) ^ 2 := by
    rw [pair_collisions_card_eq_subtype P A]
    convert b2 M hM A hA
  have hSumBound : (Ssum.card : ℝ) ≤ Csum * (M : ℝ) ^ ε * (A.card : ℝ) ^ 4 := by
    dsimp only [Ssum, T, w, f, pSum, tuples, score]
    convert bSum M hM A hA
  have hSqBound : (Ssq.card : ℝ) ≤ Csq * (M : ℝ) ^ ε * (A.card : ℝ) ^ 4 := by
    dsimp only [Ssq, T, w, f, pSq, tuples, score]
    convert bSq M hM A hA
  have hResBound : (Sres.card : ℝ) ≤
      Cres * (M : ℝ) ^ ε * (A.card : ℝ) ^ (if P.natDegree = 3 then (5 : ℕ) else 4) := by
    dsimp only [Sres, T, w, f, pSum, pSq, tuples, score]
    convert bRes M hM A hA
  let k : ℕ := if P.natDegree = 3 then 5 else 4
  have hpow4 : (A.card : ℝ) ^ 4 ≤ (A.card : ℝ) ^ k := by
    by_cases hz : A.card = 0
    · dsimp [k]
      split_ifs <;> simp [hz]
    · have hone : (1 : ℝ) ≤ A.card := by exact_mod_cast (show 1 ≤ A.card by omega)
      apply pow_le_pow_right₀ hone
      dsimp [k]
      split_ifs <;> decide
  have hm_nonneg : 0 ≤ (M : ℝ) ^ ε := by positivity
  have h4toK : (M : ℝ) ^ ε * (A.card : ℝ) ^ 4 ≤ (M : ℝ) ^ ε * (A.card : ℝ) ^ k :=
    mul_le_mul_of_nonneg_left hpow4 hm_nonneg
  have hStep1 : (off.card : ℝ) ≤
      2 * ((Ssum.card : ℝ) + (Ssq.card : ℝ) + (Sres.card : ℝ)) +
        256 * (A.card : ℝ) ^ 2 * (C2 * (M : ℝ) ^ ε * (A.card : ℝ) ^ 2) := by
    have hoffR : (off.card : ℝ) ≤ ((collisions A f 4).card : ℝ) := by exact_mod_cast hoff
    have h2disj : 2 * ((disjoint A f 4).card : ℝ) ≤
        2 * ((Ssum.card : ℝ) + (Ssq.card : ℝ) + (Sres.card : ℝ)) :=
      mul_le_mul_of_nonneg_left hdisjCard (by positivity)
    have h2e2 : 256 * (A.card : ℝ) ^ 2 * ((collisions A f 2).card : ℝ) ≤
        256 * (A.card : ℝ) ^ 2 * (C2 * (M : ℝ) ^ ε * (A.card : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hE2 (by positivity)
    linarith only [hoffR, hInterp, h2disj, h2e2]
  have h1 : Csum * ((M : ℝ) ^ ε * (A.card : ℝ) ^ 4) ≤ Csum * ((M : ℝ) ^ ε * (A.card : ℝ) ^ k) :=
    mul_le_mul_of_nonneg_left h4toK hCsum.le
  have h2 : Csq * ((M : ℝ) ^ ε * (A.card : ℝ) ^ 4) ≤ Csq * ((M : ℝ) ^ ε * (A.card : ℝ) ^ k) :=
    mul_le_mul_of_nonneg_left h4toK hCsq.le
  have h3 : 256 * C2 * ((M : ℝ) ^ ε * (A.card : ℝ) ^ 4) ≤
      256 * C2 * ((M : ℝ) ^ ε * (A.card : ℝ) ^ k) :=
    mul_le_mul_of_nonneg_left h4toK (by positivity)
  change (off.card : ℝ) ≤
    (2 * Csum + 2 * Csq + 2 * Cres + 256 * C2) * (M : ℝ) ^ ε * (A.card : ℝ) ^ k
  have hmul : 256 * (A.card : ℝ) ^ 2 * (C2 * (M : ℝ) ^ ε * (A.card : ℝ) ^ 2) =
      256 * C2 * ((M : ℝ) ^ ε * (A.card : ℝ) ^ 4) := by ring
  rw [hmul] at hStep1
  linarith only [hStep1, hSumBound, hSqBound, hResBound, h1, h2, h3]
