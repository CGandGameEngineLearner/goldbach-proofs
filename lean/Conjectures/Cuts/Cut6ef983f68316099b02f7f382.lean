import Mathlib
import Conjectures.Cuts.Taskf7c18a375028fb1ff2783f5b

namespace RepeatedTripleCollision
noncomputable section
open Finset

private def equalPairs {α : Type*} [Fintype α] (f g : α → ℤ) : Finset (α × α) :=
  univ.filter fun z => f z.1 = g z.2

private lemma count_equalPairs {α : Type*} [Fintype α] (f g : α → ℤ) (T : Finset ℤ)
    (hf : ∀ a, f a ∈ T) :
    (equalPairs f g).card = ∑ k ∈ T, (univ.filter fun a => f a = k).card *
      (univ.filter fun b => g b = k).card := by
  classical
  rw [card_eq_sum_card_fiberwise (f := fun z : α × α => f z.1)
    (t := T) (s := equalPairs f g) (fun a _ => hf a.1)]
  refine sum_congr rfl (fun k _ => ?_)
  rw [← card_product]
  congr 1
  ext z
  simp [equalPairs]
  omega

private lemma mixed_bound {α : Type*} [Fintype α] (f g : α → ℤ)
    (h : (equalPairs g g).card ≤ (equalPairs f f).card) :
    (equalPairs f g).card ≤ (equalPairs f f).card := by
  classical
  let T := univ.image f ∪ univ.image g
  have hf (a : α) : f a ∈ T := mem_union_left _ (mem_image_of_mem _ (mem_univ a))
  have hg (a : α) : g a ∈ T := mem_union_right _ (mem_image_of_mem _ (mem_univ a))
  have hsum : 2 * (equalPairs f g).card ≤ (equalPairs f f).card + (equalPairs g g).card := by
    rw [count_equalPairs f g T hf, count_equalPairs f f T hf, count_equalPairs g g T hg,
      mul_sum, ← sum_add_distrib]
    apply sum_le_sum
    intro k _
    generalize (univ.filter fun a => f a = k).card = a
    generalize (univ.filter fun a => g a = k).card = b
    zify
    nlinarith [sq_nonneg ((a : ℤ) - (b : ℤ))]
  omega

private abbrev Pair (α : Type*) := Fin 2 → α
private abbrev Triple (α : Type*) := Fin 3 → α
private abbrev Perm := Equiv.Perm (Fin 3)
private def pairSum {α : Type*} (f : α → ℤ) (p : Pair α) := ∑ i, f (p i)
private def shiftedDiff {α : Type*} (f : α → ℤ) (h : ℤ) (p : Pair α) := f (p 0) - f (p 1) + h

private def exchange {α : Type*} (z : Pair α × Pair α) : Pair α × Pair α :=
  (![z.1 0, z.2 1], ![z.2 0, z.1 1])

private lemma exchange_involutive {α : Type*} : Function.Involutive (@exchange α) := by
  intro z
  apply Prod.ext <;> funext i <;> fin_cases i <;> rfl

private lemma uniform_bound {α : Type*} [Fintype α] (f : α → ℤ) (h : ℤ) :
    (equalPairs (pairSum f) (shiftedDiff f h)).card ≤ (equalPairs (pairSum f) (pairSum f)).card := by
  apply mixed_bound
  apply card_le_card_of_injOn exchange _ exchange_involutive.injective.injOn
  intro z hz
  have he := (mem_filter.mp hz).2
  simp only [shiftedDiff] at he
  refine mem_filter.mpr ⟨mem_univ _, ?_⟩
  simp [exchange, pairSum, Fin.sum_univ_two]
  linarith

private lemma reorder {α : Type*} (u : Triple α) (h : ¬ Function.Injective u) :
    ∃ e : Perm, u (e 0) = u (e 1) := by
  classical
  simp only [Function.Injective, not_forall] at h
  obtain ⟨i,j,hij⟩ := h
  obtain ⟨he, hn⟩ := hij
  let t : Perm := Equiv.swap 0 i
  have ht : t 0 = i := Equiv.swap_apply_left _ _
  have hk : t.symm j ≠ 0 := by
    intro hk
    exact hn ((ht.symm.trans (congrArg t hk).symm).trans (t.apply_symm_apply j))
  let e := (Equiv.swap 1 (t.symm j)).trans t
  have he0 : e 0 = i := by
    change t (Equiv.swap 1 (t.symm j) 0) = i
    rw [Equiv.swap_apply_of_ne_of_ne (by decide) (Ne.symm hk), ht]
  have he1 : e 1 = j := by simp [e]
  exact ⟨e, by rwa [he0, he1]⟩

private def leftSet {α : Type*} [Fintype α] (f : α → ℤ) : Finset (Triple α × Triple α) := by
  classical
  exact univ.filter fun z => (∑ i, f (z.1 i)) = (∑ i, f (z.2 i)) ∧ ¬ Function.Injective z.1

private def pool {α : Type*} [Fintype α] (f : α → ℤ) :=
  univ.sigma fun a : α => equalPairs (pairSum f) (shiftedDiff f (2*f a))

private lemma left_bound {α : Type*} [Fintype α] (f : α → ℤ) :
    (leftSet f).card ≤ Fintype.card Perm *
      (Fintype.card α * (equalPairs (pairSum f) (pairSum f)).card) := by
  classical
  let S := leftSet f
  have hs (z : ↥S) := (mem_filter.mp z.property).2
  let tag (z : ↥S) := (reorder z.val.1 (hs z).2).choose
  have htag (z : ↥S) : z.val.1 (tag z 0) = z.val.1 (tag z 1) :=
    (reorder z.val.1 (hs z).2).choose_spec
  let F (z : ↥S) : Perm × (Σ _ : α, Pair α × Pair α) :=
    (tag z, ⟨z.val.1 (tag z 0), (![z.val.2 0,z.val.2 1], ![z.val.1 (tag z 2),z.val.2 2])⟩)
  have hmap (z : ↥S) : F z ∈ (univ : Finset Perm) ×ˢ pool f := by
    refine mem_product.mpr ⟨mem_univ _, mem_sigma.mpr ⟨mem_univ _, mem_filter.mpr ⟨mem_univ _, ?_⟩⟩⟩
    have hperm := Equiv.sum_comp (tag z) (fun i => f (z.val.1 i))
    have htotal := (hs z).1
    rw [Fin.sum_univ_three] at hperm
    rw [← hperm, Fin.sum_univ_three] at htotal
    simp only [htag z] at htotal
    change pairSum f ![z.val.2 0,z.val.2 1] = shiftedDiff f (2*f (z.val.1 (tag z 0))) ![z.val.1 (tag z 2),z.val.2 2]
    simp [pairSum, shiftedDiff, Fin.sum_univ_two, htag z]
    linarith
  have hinj : Function.Injective F := by
    intro a b hab
    have ht : tag a = tag b := congrArg Prod.fst hab
    have h0 : a.val.1 (tag a 0) = b.val.1 (tag b 0) := congrArg (fun z => z.2.1) hab
    have h2 : a.val.1 (tag a 2) = b.val.1 (tag b 2) := congrArg (fun z => z.2.2.2 0) hab
    apply Subtype.ext
    apply Prod.ext
    · funext i
      obtain ⟨k,rfl⟩ := (tag a).surjective i
      have hh : a.val.1 (tag a k) = b.val.1 (tag b k) := by
        fin_cases k
        · exact h0
        · exact (htag a).symm.trans (h0.trans (htag b))
        · exact h2
      simpa only [ht] using hh
    · funext i
      fin_cases i
      · exact congrArg (fun z => z.2.2.1 0) hab
      · exact congrArg (fun z => z.2.2.1 1) hab
      · exact congrArg (fun z => z.2.2.2 1) hab
  have hpool : (pool f).card ≤ Fintype.card α * (equalPairs (pairSum f) (pairSum f)).card := by
    rw [pool, card_sigma]
    calc
      _ ≤ ∑ _a : α, (equalPairs (pairSum f) (pairSum f)).card := sum_le_sum fun a _ => uniform_bound f _
      _ = _ := by simp
  have hcount : S.card ≤ Fintype.card Perm * (pool f).card := by
    simpa only [card_univ, Fintype.card_coe, card_product] using
      (card_le_card_of_injOn (s := (univ : Finset ↥S)) F (fun z _ => hmap z) hinj.injOn)
  exact hcount.trans (Nat.mul_le_mul_left _ hpool)

private lemma both_bound {α : Type*} [Fintype α] (f : α → ℤ) (G : Finset (Triple α × Triple α))
    (hg : ∀ z ∈ G, (∑ i, f (z.1 i)) = (∑ i, f (z.2 i)) ∧
      ¬ (Function.Injective z.1 ∧ Function.Injective z.2)) :
    G.card ≤ (2 * Fintype.card Perm) * (Fintype.card α * (equalPairs (pairSum f) (pairSum f)).card) := by
  classical
  let S := leftSet f
  have cover : G ⊆ S ∪ S.image Prod.swap := by
    intro z hz
    obtain ⟨hs,hbad⟩ := hg z hz
    by_cases hl : Function.Injective z.1
    · apply mem_union_right
      exact mem_image.mpr ⟨z.swap, mem_filter.mpr ⟨mem_univ _, hs.symm, fun hr => hbad ⟨hl, hr⟩⟩, rfl⟩
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _,hs,hl⟩)
  have h := (card_le_card cover).trans (card_union_le _ _)
  have hi : (S.image Prod.swap).card ≤ S.card := card_image_le
  have hb := left_bound f
  change S.card ≤ _ at hb
  rw [Nat.mul_assoc]
  omega

theorem repeated_triples (P : Polynomial ℤ) (hd : 3 ≤ P.natDegree) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ, 2 ≤ M → ∀ A ⊆ Icc 1 M,
    ∀ G : Finset ((Fin 3 → ↥A) × (Fin 3 → ↥A)),
    (∀ z ∈ G, (∑ i, P.eval ((z.1 i : ℕ) : ℤ)) = (∑ i, P.eval ((z.2 i : ℕ) : ℤ)) ∧
      ¬ (Function.Injective z.1 ∧ Function.Injective z.2)) →
    (G.card : ℝ) ≤ C * (M : ℝ)^ε * (A.card : ℝ)^3 := by
  classical
  obtain ⟨C,hC,h⟩ := Conjectures.Cuts.Taskf7c18a375028fb1ff2783f5b P (by omega) ε hε
  let B : ℕ := 2 * Fintype.card Perm
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨(B:ℝ) * C, mul_pos (by exact_mod_cast hB) hC, ?_⟩
  intro M hM A hA G hg
  let f (a : ↥A) := P.eval ((a : ℕ) : ℤ)
  have hnat := both_bound f G hg
  rw [Fintype.card_coe] at hnat
  have he : ((equalPairs (pairSum f) (pairSum f)).card : ℝ) ≤ C * (M : ℝ)^ε * (A.card : ℝ)^2 :=
    h M hM A hA
  calc
    (G.card : ℝ) ≤ (B:ℝ) * ((A.card : ℝ) * ((equalPairs (pairSum f) (pairSum f)).card : ℝ)) := by
      exact_mod_cast hnat
    _ ≤ (B:ℝ) * ((A.card : ℝ) * (C * (M : ℝ)^ε * (A.card : ℝ)^2)) := by gcongr
    _ = _ := by ring

end
end RepeatedTripleCollision

namespace DistinctTripleReduction
open Finset

private def DistinctCount (degrees : ℕ → Prop) : Prop :=
  ∀ P : Polynomial ℤ, degrees P.natDegree → ∀ ε : ℝ, 0 < ε →
  ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ, 2 ≤ M → ∀ A ⊆ Icc 1 M,
    ((univ.filter fun z : (Fin 3 → ↥A) × (Fin 3 → ↥A) =>
      (∑ i, P.eval ((z.1 i : ℕ) : ℤ)) = (∑ i, P.eval ((z.2 i : ℕ) : ℤ)) ∧
      (∀ i j, z.1 i ≠ z.2 j) ∧ Function.Injective z.1 ∧ Function.Injective z.2).card : ℝ)
      ≤ C * (M : ℝ)^ε * (A.card : ℝ)^3

end DistinctTripleReduction

-- child 1 zh: 对三次整系数多项式，控制六个指标两两不同的三元组等和碰撞数。
-- child 1 en: Bound equal triple sums for integer cubic polynomials when all six indices are distinct.
-- child 2 zh: 对次数至少为四的整系数多项式，控制六个指标两两不同的三元组等和碰撞数。
-- child 2 en: Bound equal triple sums for integer polynomials of degree at least four when all six indices are distinct.
open DistinctTripleReduction Finset in
theorem Conjectures.Cuts.Cut6ef983f68316099b02f7f382
    (hcubic : DistinctCount (fun d => d = 3))
    (hhigher : DistinctCount (fun d => 4 ≤ d)) : (
∀ (x1 : Polynomial ℤ),   (3 : ℕ) ≤ x1.natDegree →     ∀ (x3 : ℝ),       (0 : ℝ) < x3 →         ∃ (x5 : ℝ),           (0 : ℝ) < x5 ∧             ∀ (x6 : ℕ),               (2 : ℕ) ≤ x6 →                 ∀ x8 ⊆ Finset.Icc (1 : ℕ) x6,                   have x10 : (Fin (3 : ℕ) → ↥x8) → ℤ := fun (x10 : Fin (3 : ℕ) → ↥x8) => ∑ x11 : Fin (3 : ℕ), Polynomial.eval (↑↑(x10 x11)) x1;                   have x11 : Finset ((Fin (3 : ℕ) → ↥x8) × (Fin (3 : ℕ) → ↥x8)) := Finset.univ;                   have x12 : Finset ((Fin (3 : ℕ) → ↥x8) × (Fin (3 : ℕ) → ↥x8)) := {x12 ∈ x11 | x10 x12.1 = x10 x12.2};                   ↑{x13 ∈ x12 | ∀ (x14 x15 : Fin (3 : ℕ)), x13.1 x14 ≠ x13.2 x15}.card ≤ x5 * ↑x6 ^ x3 * ↑x8.card ^ (3 : ℕ)
) := by
  classical
  intro P hd ε hε
  let f (n : ℕ) := P.eval (n : ℤ)
  have hh : ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ, 2 ≤ M → ∀ A ⊆ Icc 1 M,
      ((univ.filter fun z : (Fin 3 → ↥A) × (Fin 3 → ↥A) =>
        (∑ i, f (z.1 i)) = (∑ i, f (z.2 i)) ∧
        (∀ i j, z.1 i ≠ z.2 j) ∧ Function.Injective z.1 ∧ Function.Injective z.2).card : ℝ)
        ≤ C * (M : ℝ)^ε * (A.card : ℝ)^3 := by
    by_cases he : P.natDegree = 3
    · exact hcubic P he ε hε
    · exact hhigher P (by omega) ε hε
  obtain ⟨C,hC,h⟩ := hh
  obtain ⟨D,hD,d⟩ := RepeatedTripleCollision.repeated_triples P hd ε hε
  refine ⟨C+D,add_pos hC hD,?_⟩
  intro M hM A hA
  let G := ((univ : Finset ((Fin 3 → ↥A) × (Fin 3 → ↥A))).filter fun z =>
    (∑ i, f (z.1 i)) = (∑ i, f (z.2 i))).filter fun z => ∀ i j, z.1 i ≠ z.2 j
  let good (z : (Fin 3 → ↥A) × (Fin 3 → ↥A)) := Function.Injective z.1 ∧ Function.Injective z.2
  have h1 : ((G.filter good).card : ℝ) ≤ C * (M : ℝ)^ε * (A.card : ℝ)^3 := by
    apply le_trans _ (h M hM A hA)
    apply Nat.cast_le.mpr
    apply card_le_card
    intro z hz
    obtain ⟨hz,hinj⟩ := mem_filter.mp hz
    obtain ⟨hz,hdj⟩ := mem_filter.mp hz
    exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hz).2,hdj,hinj⟩
  have h2 : ((G.filter fun z => ¬ good z).card : ℝ) ≤ D * (M : ℝ)^ε * (A.card : ℝ)^3 := by
    apply d M hM A hA
    intro z hz
    obtain ⟨hz,hrep⟩ := mem_filter.mp hz
    exact ⟨(mem_filter.mp (mem_filter.mp hz).1).2,hrep⟩
  change (G.card : ℝ) ≤ _
  have ht := Finset.card_filter_add_card_filter_not (s := G) (p := good)
  have hreal : (G.card : ℝ) = ((G.filter good).card : ℝ) + ((G.filter fun z => ¬ good z).card : ℝ) := by
    exact_mod_cast ht.symm
  rw [hreal]
  calc
    _ ≤ (C * (M : ℝ)^ε * (A.card : ℝ)^3) + (D * (M : ℝ)^ε * (A.card : ℝ)^3) := add_le_add h1 h2
    _ = _ := by ring
