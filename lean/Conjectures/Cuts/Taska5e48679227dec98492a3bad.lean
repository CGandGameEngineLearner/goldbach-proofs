import Mathlib
import Conjectures.Cuts.Taskf7c18a375028fb1ff2783f5b

namespace SquareMatchedCollision
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

/-- Translation of the target difference cannot increase a self-collision count. -/
private lemma shifted_le {α : Type*} [Fintype α] (f : α → ℤ) (h : ℤ) :
    (equalPairs f (fun a => f a + h)).card ≤ (equalPairs f f).card := by
  classical
  let g := fun a => f a + h
  let T := univ.image f ∪ univ.image g
  have hf (a : α) : f a ∈ T := mem_union_left _ (mem_image_of_mem _ (mem_univ a))
  have hg (a : α) : g a ∈ T := mem_union_right _ (mem_image_of_mem _ (mem_univ a))
  have hgg : equalPairs g g = equalPairs f f := by ext z; simp [equalPairs, g]
  have hsum : 2 * (equalPairs f g).card ≤ (equalPairs f f).card + (equalPairs g g).card := by
    rw [count_equalPairs f g T hf, count_equalPairs f f T hf, count_equalPairs g g T hg,
      mul_sum, ← sum_add_distrib]
    apply sum_le_sum
    intro k _
    generalize (univ.filter fun a => f a = k).card = a
    generalize (univ.filter fun a => g a = k).card = b
    zify
    nlinarith [sq_nonneg ((a : ℤ) - (b : ℤ))]
  rw [hgg] at hsum
  change (equalPairs f g).card ≤ _
  omega

private abbrev Pair (A : Finset ℕ) := Fin 2 → ↥A
private abbrev Quad (A : Finset ℕ) := Pair A × Pair A

private def value (P : Polynomial ℤ) {A : Finset ℕ} (a : Pair A) : ℤ :=
  ∑ i, P.eval ((a i : ℕ) : ℤ)

private def sqPoly : Polynomial ℤ := Polynomial.X ^ 2

private def slices (P : Polynomial ℤ) (A : Finset ℕ) :=
  (equalPairs (value (A := A) sqPoly) (value sqPoly)).sigma fun z =>
    equalPairs (value P) (fun a : Pair A => value P a + (value P z.2 - value P z.1))

private lemma slices_bound (P : Polynomial ℤ) (hP : 2 ≤ P.natDegree) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ, 2 ≤ M → ∀ A ⊆ Icc 1 M,
      ((slices P A).card : ℝ) ≤ C * (M : ℝ)^ε * (A.card : ℝ)^4 := by
  classical
  have hs : 2 ≤ sqPoly.natDegree := by simp [sqPoly]
  obtain ⟨C, hC, hc⟩ := Conjectures.Cuts.Taskf7c18a375028fb1ff2783f5b P hP (ε/2) (by positivity)
  obtain ⟨D, hD, hd⟩ := Conjectures.Cuts.Taskf7c18a375028fb1ff2783f5b sqPoly hs (ε/2) (by positivity)
  refine ⟨D*C, mul_pos hD hC, ?_⟩
  intro M hM A hA
  let S := equalPairs (value (A := A) sqPoly) (value sqPoly)
  let E := equalPairs (value (A := A) P) (value P)
  have hcount : (slices P A).card ≤ S.card * E.card := by
    rw [slices, card_sigma]
    calc
      _ ≤ ∑ _z ∈ S, E.card := sum_le_sum fun z _ => shifted_le _ _
      _ = _ := by simp
  have hsplit : (M : ℝ)^(ε/2) * (M : ℝ)^(ε/2) = (M : ℝ)^ε := by
    rw [← Real.rpow_add (by exact_mod_cast (show 0 < M by omega)), add_halves]
  calc
    _ ≤ (S.card : ℝ) * (E.card : ℝ) := by exact_mod_cast hcount
    _ ≤ (D * (M : ℝ)^(ε/2) * (A.card : ℝ)^2) *
      (C * (M : ℝ)^(ε/2) * (A.card : ℝ)^2) :=
        mul_le_mul (hd M hM A hA) (hc M hM A hA) (by positivity) (by positivity)
    _ = _ := by rw [← hsplit]; ring

private abbrev Perm := Equiv.Perm (Fin 4)
private abbrev Slots := Perm × Perm

private lemma place (i j : Fin 4) (h : i ≠ j) :
    ∃ e : Perm, e 0 = i ∧ e 1 = j := by
  let t : Perm := Equiv.swap 0 i
  have ht : t 0 = i := Equiv.swap_apply_left _ _
  have hk : t.symm j ≠ 0 := by
    intro hk
    exact h ((ht.symm.trans (congrArg t hk).symm).trans (t.apply_symm_apply j))
  refine ⟨(Equiv.swap 1 (t.symm j)).trans t, ?_, ?_⟩
  · change t (Equiv.swap 1 (t.symm j) 0) = i
    rw [Equiv.swap_apply_of_ne_of_ne (by decide) (Ne.symm hk), ht]
  · simp

private abbrev Block (A : Finset ℕ) := (_z : Quad A) × Quad A

private def pack {A : Finset ℕ} (u v : Fin 4 → ↥A) : Block A :=
  ⟨(![u 0, u 1], ![v 0, v 1]), (![u 2, u 3], ![v 2, v 3])⟩

private lemma unpack {A : Finset ℕ} {u v u' v' : Fin 4 → ↥A}
    (h : pack u v = pack u' v') : u = u' ∧ v = v' := by
  constructor <;> funext i <;> fin_cases i
  · exact congrArg (fun b => b.1.1 0) h
  · exact congrArg (fun b => b.1.1 1) h
  · exact congrArg (fun b => b.2.1 0) h
  · exact congrArg (fun b => b.2.1 1) h
  · exact congrArg (fun b => b.1.2 0) h
  · exact congrArg (fun b => b.1.2 1) h
  · exact congrArg (fun b => b.2.2 0) h
  · exact congrArg (fun b => b.2.2 1) h

private lemma pack_mem {A : Finset ℕ} (P : Polynomial ℤ) (u v : Fin 4 → ↥A)
    (hs : (u 0 : ℕ)^2 + (u 1 : ℕ)^2 = (v 0 : ℕ)^2 + (v 1 : ℕ)^2)
    (hp : (∑ i, P.eval ((u i : ℕ) : ℤ)) = ∑ i, P.eval ((v i : ℕ) : ℤ)) :
    pack u v ∈ slices P A := by
  simp only [pack, slices, equalPairs, mem_sigma, mem_filter, mem_univ, true_and]
  simp [value, sqPoly, Fin.sum_univ_two]
  rw [Fin.sum_univ_four, Fin.sum_univ_four] at hp
  constructor
  · exact_mod_cast hs
  · linarith

private lemma cover (P : Polynomial ℤ) (A : Finset ℕ)
    (G : Finset ((Fin 4 → ℕ) × (Fin 4 → ℕ)))
    (hg : ∀ z ∈ G, (∀ i, z.1 i ∈ A) ∧ (∀ i, z.2 i ∈ A) ∧
      (∑ i, P.eval (z.1 i : ℤ)) = (∑ i, P.eval (z.2 i : ℤ)) ∧
      ∃ e : Slots, z.1 (e.1 0)^2 + z.1 (e.1 1)^2 = z.2 (e.2 0)^2 + z.2 (e.2 1)^2) :
    G.card ≤ Fintype.card Slots * (slices P A).card := by
  classical
  let tag (z : ↥G) := (hg z.1 z.2).2.2.2.choose
  let u (z : ↥G) (i : Fin 4) : ↥A :=
    ⟨z.val.1 ((tag z).1 i), (hg z.val z.property).1 _⟩
  let v (z : ↥G) (i : Fin 4) : ↥A :=
    ⟨z.val.2 ((tag z).2 i), (hg z.val z.property).2.1 _⟩
  let F (z : ↥G) : Slots × Block A := (tag z, pack (u z) (v z))
  have maps (z : ↥G) : F z ∈ (univ : Finset Slots) ×ˢ slices P A := by
    refine mem_product.mpr ⟨mem_univ _, pack_mem _ _ _ ((hg z.val z.property).2.2.2.choose_spec) ?_⟩
    change (∑ i, P.eval (z.val.1 ((tag z).1 i) : ℤ)) = ∑ i, P.eval (z.val.2 ((tag z).2 i) : ℤ)
    rw [Equiv.sum_comp (tag z).1 (fun i => P.eval (z.val.1 i : ℤ)),
      Equiv.sum_comp (tag z).2 (fun i => P.eval (z.val.2 i : ℤ))]
    exact (hg z.val z.property).2.2.1
  have inj : Function.Injective F := by
    intro a b hab
    have ht : tag a = tag b := congrArg Prod.fst hab
    obtain ⟨hl,hr⟩ := unpack (show pack (u a) (v a) = pack (u b) (v b) from congrArg Prod.snd hab)
    apply Subtype.ext
    apply Prod.ext
    · funext i
      obtain ⟨k,rfl⟩ := (tag a).1.surjective i
      have hh := congrArg Subtype.val (congrFun hl k)
      change a.val.1 ((tag a).1 k) = b.val.1 ((tag b).1 k) at hh
      simpa only [ht] using hh
    · funext i
      obtain ⟨k,rfl⟩ := (tag a).2.surjective i
      have hh := congrArg Subtype.val (congrFun hr k)
      change a.val.2 ((tag a).2 k) = b.val.2 ((tag b).2 k) at hh
      simpa only [ht] using hh
  simpa only [card_univ, Fintype.card_coe, card_product] using
    (card_le_card_of_injOn (s := (univ : Finset ↥G)) F (fun z _ => maps z) inj.injOn)

end
end SquareMatchedCollision
open SquareMatchedCollision Finset in
theorem Conjectures.Cuts.Taska5e48679227dec98492a3bad : (∀ (x1 : Polynomial ℤ),   (3 : ℕ) ≤ x1.natDegree →     ∀ (x3 : ℝ),       (0 : ℝ) < x3 →         ∃ (x5 : ℝ),           (0 : ℝ) < x5 ∧             ∀ (x6 : ℕ),               (2 : ℕ) ≤ x6 →                 ∀ x8 ⊆ Finset.Icc (1 : ℕ) x6,                   have x10 : Finset (Fin (4 : ℕ) → ℕ) := Fintype.piFinset fun (_ : Fin (4 : ℕ)) => x8;                   let x11 : (Fin (4 : ℕ) → ℕ) → ℤ := fun (x11 : Fin (4 : ℕ) → ℕ) => ∑ x12 : Fin (4 : ℕ), Polynomial.eval (↑(x11 x12) : ℤ) x1;                   have x12 : Finset ((Fin (4 : ℕ) → ℕ) × (Fin (4 : ℕ) → ℕ)) := {x12 ∈ x10.product x10 | x11 x12.1 = x11 x12.2 ∧ ∀ (x13 : Fin (4 : ℕ) × Fin (4 : ℕ)), x12.1 x13.1 ≠ x12.2 x13.2};                   (↑{x13 ∈ x12 | ∃ (x14 : Fin (4 : ℕ) × Fin (4 : ℕ)) (x15 : Fin (4 : ℕ) × Fin (4 : ℕ)), x14.1 ≠ x14.2 ∧ x15.1 ≠ x15.2 ∧ x13.1 x14.1 ^ (2 : ℕ) + x13.1 x14.2 ^ (2 : ℕ) = x13.2 x15.1 ^ (2 : ℕ) + x13.2 x15.2 ^ (2 : ℕ)}.card : ℝ) ≤ x5 * (↑x6 : ℝ) ^ x3 * (↑x8.card : ℝ) ^ (4 : ℕ)) := by
  classical
  intro P hP ε hε
  obtain ⟨C,hC,hbound⟩ := slices_bound P (by omega) ε hε
  let B : ℝ := Fintype.card Slots
  have hB : 0 < B := by dsimp [B]; exact_mod_cast Fintype.card_pos
  refine ⟨B*C, mul_pos hB hC, ?_⟩
  intro N hN A hA
  apply le_trans (b := B * ((slices P A).card : ℝ))
  · dsimp only [B]
    rw [← Nat.cast_mul]
    apply Nat.cast_le.mpr
    apply cover
    intro z hz
    obtain ⟨hzw,ij,kl,hij,hkl,hmatch⟩ := mem_filter.mp hz
    obtain ⟨hp,hsum,_⟩ := mem_filter.mp hzw
    obtain ⟨hl,hr⟩ := mem_product.mp hp
    obtain ⟨e,he0,he1⟩ := place _ _ hij
    obtain ⟨f,hf0,hf1⟩ := place _ _ hkl
    refine ⟨Fintype.mem_piFinset.mp hl,Fintype.mem_piFinset.mp hr,hsum,⟨e,f⟩,?_⟩
    simpa only [he0,he1,hf0,hf1] using hmatch
  · calc
      _ ≤ B * (C * (N : ℝ)^ε * (A.card : ℝ)^4) :=
        mul_le_mul_of_nonneg_left (hbound N hN A hA) hB.le
      _ = _ := by ring
