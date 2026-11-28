import Mathlib
import Conjectures.Cuts.Taskf7c18a375028fb1ff2783f5b

namespace SqPair

def two {T : Type*} (f : T → ℤ) (v : Fin 2 → T) : ℤ := f (v 0) + f (v 1)

noncomputable def energy {T : Type*} [Fintype T] [DecidableEq T] (f : T → ℤ) : ℕ :=
  ((Finset.univ : Finset ((Fin 2 → T) × (Fin 2 → T))).filter
    (fun z => two f z.1 = two f z.2)).card

noncomputable def canonical {T : Type*} [Fintype T] [DecidableEq T] (f s : T → ℤ) :
    Finset ((Fin 4 → T) × (Fin 4 → T)) :=
  Finset.univ.filter fun z =>
    (∑ i, f (z.1 i)) = (∑ i, f (z.2 i)) ∧
      s (z.1 0) + s (z.1 1) = s (z.2 0) + s (z.2 1)

noncomputable def witnessed {T : Type*} [Fintype T] [DecidableEq T] (f s : T → ℤ) :
    Finset ((Fin 4 → T) × (Fin 4 → T)) := by
  classical
  exact Finset.univ.filter fun z =>
    (∑ i, f (z.1 i)) = (∑ i, f (z.2 i)) ∧
      ∃ i j : Fin 4 × Fin 4, i.1 ≠ i.2 ∧ j.1 ≠ j.2 ∧
        s (z.1 i.1) + s (z.1 i.2) = s (z.2 j.1) + s (z.2 j.2)

end SqPair

namespace SqPair

/- The finite-distribution shift bound is by DDT666444888, goldbach-proofs PR #4822,
revision 08f52bc72ddd07df8627ac7fe961d304db4d9de6 (Apache-2.0). -/
private theorem shift_le {β : Type*} [Fintype β] [DecidableEq β] (f : β → ℤ) (d : ℤ) :
    ((Finset.univ : Finset (β × β)).filter (fun z => f z.1 = f z.2 + d)).card ≤
    ((Finset.univ : Finset (β × β)).filter (fun z => f z.1 = f z.2)).card := by
  classical
  let g : β → ℤ := fun x => f x + d
  let S := Finset.univ.image f ∪ Finset.univ.image g
  let fiber (h : β → ℤ) (t : ℤ) := (Finset.univ : Finset β).filter (fun x => h x = t)
  let pairs (h k : β → ℤ) := (Finset.univ : Finset (β × β)).filter (fun z => h z.1 = k z.2)
  have formula (h k : β → ℤ) (hh : ∀ x, h x ∈ S) :
      (pairs h k).card = ∑ t ∈ S, (fiber h t).card * (fiber k t).card := by
    refine (Finset.card_eq_sum_card_fiberwise (f := fun z : β × β => h z.1)
      (t := S) (s := pairs h k) (fun z _ => hh z.1)).trans ?_
    apply Finset.sum_congr rfl
    intro t _
    rw [← Finset.card_product]
    apply congrArg Finset.card
    ext z
    simp only [pairs, fiber, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product]
    exact ⟨fun ⟨he, ht⟩ => ⟨ht, he.symm.trans ht⟩,
      fun ⟨h₁, h₂⟩ => ⟨h₁.trans h₂.symm, h₁⟩⟩
  have hf (x : β) : f x ∈ S := Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ x))
  have hg (x : β) : g x ∈ S := Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ x))
  have hdiag : pairs g g = pairs f f := by simp [pairs, g]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq S (fun t => (fiber f t).card)
    (fun t => (fiber g t).card)
  simp only [sq, ← formula f g hf, ← formula f f hf, ← formula g g hg, hdiag] at hcs
  change (pairs f g).card ≤ (pairs f f).card
  nlinarith

private def firstTwo {T : Type*} (u : Fin 4 → T) : Fin 2 → T := ![u 0, u 1]
private def lastTwo {T : Type*} (u : Fin 4 → T) : Fin 2 → T := ![u 2, u 3]

private theorem tuple_ext {T : Type*} {u v : Fin 4 → T}
    (ha : firstTwo u = firstTwo v) (hb : lastTwo u = lastTwo v) : u = v := by
  funext k
  fin_cases k
  · exact congrFun ha 0
  · exact congrFun ha 1
  · exact congrFun hb 0
  · exact congrFun hb 1

private theorem sum_four_parts {T : Type*} (f : T → ℤ) (u : Fin 4 → T) :
    (∑ i, f (u i)) = two f (firstTwo u) + two f (lastTwo u) := by
  simp [Fin.sum_univ_succ, two, firstTwo, lastTwo, add_assoc]

theorem canonical_le {T : Type*} [Fintype T] [DecidableEq T] (f s : T → ℤ) :
    (canonical f s).card ≤ energy s * energy f := by
  classical
  let lefts (z : (Fin 4 → T) × (Fin 4 → T)) := (firstTwo z.1, firstTwo z.2)
  let rights (z : (Fin 4 → T) × (Fin 4 → T)) := (lastTwo z.1, lastTwo z.2)
  let L : Finset ((Fin 2 → T) × (Fin 2 → T)) :=
    Finset.univ.filter fun p => two s p.1 = two s p.2
  have hmem (z) (hz : z ∈ canonical f s) : lefts z ∈ L := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hz).2.2⟩
  have hfiber (p : (Fin 2 → T) × (Fin 2 → T)) :
      ((canonical f s).filter fun z => lefts z = p).card ≤ energy f := by
    let d := two f p.2 - two f p.1
    let R : Finset ((Fin 2 → T) × (Fin 2 → T)) :=
      Finset.univ.filter fun q => two f q.1 = two f q.2 + d
    have hbound : R.card ≤ energy f := shift_le (two f) d
    refine (Finset.card_le_card_of_injOn (t := R) rights ?_ ?_).trans hbound
    · intro z hz
      obtain ⟨hz, he⟩ := Finset.mem_filter.mp hz
      have h := (Finset.mem_filter.mp hz).2.1
      rw [sum_four_parts, sum_four_parts] at h
      have h1 : firstTwo z.1 = p.1 := congrArg Prod.fst he
      have h2 : firstTwo z.2 = p.2 := congrArg Prod.snd he
      rw [h1, h2] at h
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      change two f (lastTwo z.1) = two f (lastTwo z.2) + (two f p.2 - two f p.1)
      omega
    · intro z hz w hw he
      have h : lefts z = lefts w := (Finset.mem_filter.mp hz).2.trans (Finset.mem_filter.mp hw).2.symm
      exact Prod.ext (tuple_ext (congrArg Prod.fst h) (congrArg Prod.fst he))
        (tuple_ext (congrArg Prod.snd h) (congrArg Prod.snd he))
  calc
    (canonical f s).card = ∑ p ∈ L, ((canonical f s).filter fun z => lefts z = p).card :=
      Finset.card_eq_sum_card_fiberwise hmem
    _ ≤ ∑ _ ∈ L, energy f := Finset.sum_le_sum fun p _ => hfiber p
    _ = energy s * energy f := by simp [L, energy]

end SqPair

namespace SqPair

private theorem orderedIndices (a b : Fin 4) (hab : a ≠ b) :
    ∃ p : Equiv.Perm (Fin 4), p 0 = a ∧ p 1 = b := by
  let p := Equiv.swap 0 a
  have hp : p 0 = a := Equiv.swap_apply_left _ _
  have hne : a ≠ p 1 := by
    rw [← hp]
    exact p.injective.ne (by decide)
  refine ⟨p.trans (Equiv.swap (p 1) b), ?_, ?_⟩
  · change Equiv.swap (p 1) b (p 0) = a
    rw [hp, Equiv.swap_apply_of_ne_of_ne hne hab]
  · exact Equiv.swap_apply_left _ _

theorem witnessed_le {T : Type*} [Fintype T] [DecidableEq T] (f s : T → ℤ) :
    (witnessed f s).card ≤ 576 * (canonical f s).card := by
  classical
  let P := Equiv.Perm (Fin 4)
  let source := (Finset.univ : Finset (P × P)) ×ˢ canonical f s
  let restore : (P × P) × ((Fin 4 → T) × (Fin 4 → T)) → ((Fin 4 → T) × (Fin 4 → T)) :=
    fun z => (z.2.1 ∘ z.1.1.symm, z.2.2 ∘ z.1.2.symm)
  have cover : witnessed f s ⊆ source.image restore := by
    intro z hz
    obtain ⟨hsum, i, j, hi, hj, heq⟩ := (Finset.mem_filter.mp hz).2
    obtain ⟨p, hp₀, hp₁⟩ := orderedIndices i.1 i.2 hi
    obtain ⟨q, hq₀, hq₁⟩ := orderedIndices j.1 j.2 hj
    have hcanon : (z.1 ∘ p, z.2 ∘ q) ∈ canonical f s := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_, ?_⟩
      · exact (Equiv.sum_comp p (fun k => f (z.1 k))).trans
          (hsum.trans (Equiv.sum_comp q (fun k => f (z.2 k))).symm)
      · simpa [Function.comp_def, hp₀, hp₁, hq₀, hq₁] using heq
    refine Finset.mem_image.mpr ⟨((p,q),(z.1 ∘ p,z.2 ∘ q)), ?_, ?_⟩
    · exact Finset.mem_product.mpr ⟨Finset.mem_univ _, hcanon⟩
    · exact Prod.ext (funext fun k => congrArg z.1 (p.apply_symm_apply k))
          (funext fun k => congrArg z.2 (q.apply_symm_apply k))
  calc
    _ ≤ (source.image restore).card := Finset.card_le_card cover
    _ ≤ source.card := Finset.card_image_le
    _ = 576 * (canonical f s).card := by
      norm_num [source, P, Finset.card_product, Fintype.card_perm, Nat.factorial]

end SqPair

namespace SqPair

theorem lift_le (P : Polynomial ℤ) (A : Finset ℕ) :
    let tuples : Finset (Fin 4 → ℕ) := Fintype.piFinset fun _ => A
    let total : (Fin 4 → ℕ) → ℤ := fun a => ∑ i : Fin 4, P.eval (a i : ℤ)
    let pairs := (tuples.product tuples).filter fun z =>
      total z.1 = total z.2 ∧ ∀ i : Fin 4 × Fin 4, z.1 i.1 ≠ z.2 i.2
    (pairs.filter fun z => ∃ i j : Fin 4 × Fin 4, i.1 ≠ i.2 ∧ j.1 ≠ j.2 ∧
      z.1 i.1 ^ 2 + z.1 i.2 ^ 2 = z.2 j.1 ^ 2 + z.2 j.2 ^ 2).card ≤
      (witnessed (fun a : A => P.eval (a : ℕ)) (fun a : A => ((a : ℕ) : ℤ) ^ 2)).card := by
  classical
  let forget : ((Fin 4 → A) × (Fin 4 → A)) → ((Fin 4 → ℕ) × (Fin 4 → ℕ)) :=
    fun z => (fun i => (z.1 i).val, fun i => (z.2 i).val)
  refine le_trans (Finset.card_le_card (t := Finset.image forget _) ?_) Finset.card_image_le
  rintro ⟨a, b⟩ hz
  obtain ⟨hpair, i, j, hi, hj, heq⟩ := Finset.mem_filter.mp hz
  obtain ⟨hab, hpol, _⟩ := Finset.mem_filter.mp hpair
  obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
  let x : Fin 4 → A := fun k => ⟨a k, Fintype.mem_piFinset.mp ha k⟩
  let y : Fin 4 → A := fun k => ⟨b k, Fintype.mem_piFinset.mp hb k⟩
  refine Finset.mem_image.mpr ⟨(x, y), ?_, rfl⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, hpol, i, j, hi, hj, ?_⟩
  change (a i.1 : ℤ)^2 + (a i.2 : ℤ)^2 = (b j.1 : ℤ)^2 + (b j.2 : ℤ)^2
  exact_mod_cast heq

end SqPair

namespace SqPair

theorem polynomial_energy (P : Polynomial ℤ) (hP : 2 ≤ P.natDegree)
    (e : ℝ) (he : 0 < e) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ, 2 ≤ M → ∀ A ⊆ Finset.Icc 1 M,
      (energy (fun a : A => P.eval ((a : ℕ) : ℤ)) : ℝ) ≤
        C * (M : ℝ)^e * (A.card : ℝ)^2 := by
  obtain ⟨C, hC, h⟩ := Conjectures.Cuts.Taskf7c18a375028fb1ff2783f5b P hP e he
  refine ⟨C, hC, ?_⟩
  intro M hM A hA
  refine le_trans ?_ (h M hM A hA)
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro z hz
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, two, Fin.sum_univ_two] at hz ⊢
  exact (Finset.mem_filter.mp hz).2

theorem energy_product (P : Polynomial ℤ) (hP : 3 ≤ P.natDegree)
    (e : ℝ) (he : 0 < e) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ, 2 ≤ M → ∀ A ⊆ Finset.Icc 1 M,
      ((576 * (energy (fun a : A => ((a : ℕ) : ℤ)^2) *
              energy (fun a : A => P.eval ((a : ℕ) : ℤ))) : ℕ) : ℝ)
        ≤ C * (M : ℝ)^e * (A.card : ℝ)^4 := by
  obtain ⟨K, hK, h⟩ := polynomial_energy P (by omega) (e/2) (by positivity)
  obtain ⟨L, hL, hsq⟩ := polynomial_energy ((Polynomial.X : Polynomial ℤ)^2)
    (by simp) (e/2) (by positivity)
  refine ⟨576 * (L*K), by positivity, ?_⟩
  intro M hM A hA
  have h₁ := h M hM A hA
  have h₂ := hsq M hM A hA
  simp only [Polynomial.eval_pow, Polynomial.eval_X] at h₂
  push_cast
  have hpow : (M : ℝ)^(e/2) * (M : ℝ)^(e/2) = (M : ℝ)^e := by
    rw [← Real.rpow_add (by exact_mod_cast (show 0 < M by omega))]
    congr 1; ring
  calc
    _ ≤ 576 * ((L * (M : ℝ)^(e/2) * (A.card : ℝ)^2) *
               (K * (M : ℝ)^(e/2) * (A.card : ℝ)^2)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact mul_le_mul h₂ h₁ (by positivity) (by positivity)
    _ = (576 * (L*K)) * ((M : ℝ)^(e/2) * (M : ℝ)^(e/2)) * (A.card : ℝ)^4 := by ring
    _ = _ := by rw [hpow]

end SqPair

theorem Conjectures.Cuts.Taska5e48679227dec98492a3bad : (∀ (x1 : Polynomial ℤ),   (3 : ℕ) ≤ x1.natDegree →     ∀ (x3 : ℝ),       (0 : ℝ) < x3 →         ∃ (x5 : ℝ),           (0 : ℝ) < x5 ∧             ∀ (x6 : ℕ),               (2 : ℕ) ≤ x6 →                 ∀ x8 ⊆ Finset.Icc (1 : ℕ) x6,                   have x10 : Finset (Fin (4 : ℕ) → ℕ) := Fintype.piFinset fun (x10 : Fin (4 : ℕ)) => x8;                   let x11 : (Fin (4 : ℕ) → ℕ) → ℤ := fun (x11 : Fin (4 : ℕ) → ℕ) => ∑ x12 : Fin (4 : ℕ), Polynomial.eval (↑(x11 x12) : ℤ) x1;                   have x12 : Finset ((Fin (4 : ℕ) → ℕ) × (Fin (4 : ℕ) → ℕ)) := {x12 ∈ x10.product x10 | x11 x12.1 = x11 x12.2 ∧ ∀ (x13 : Fin (4 : ℕ) × Fin (4 : ℕ)), x12.1 x13.1 ≠ x12.2 x13.2};                   (↑{x13 ∈ x12 | ∃ (x14 : Fin (4 : ℕ) × Fin (4 : ℕ)) (x15 : Fin (4 : ℕ) × Fin (4 : ℕ)), x14.1 ≠ x14.2 ∧ x15.1 ≠ x15.2 ∧ x13.1 x14.1 ^ (2 : ℕ) + x13.1 x14.2 ^ (2 : ℕ) = x13.2 x15.1 ^ (2 : ℕ) + x13.2 x15.2 ^ (2 : ℕ)}.card : ℝ) ≤ x5 * (↑x6 : ℝ) ^ x3 * (↑x8.card : ℝ) ^ (4 : ℕ)) := by
  classical
  intro P hP e he
  obtain ⟨C, hC, bound⟩ := SqPair.energy_product P hP e he
  refine ⟨C, hC, ?_⟩
  intro M hM A hA
  let f : A → ℤ := fun a => P.eval ((a : ℕ) : ℤ)
  let s : A → ℤ := fun a => ((a : ℕ) : ℤ)^2
  have hcount := (SqPair.lift_le P A).trans ((SqPair.witnessed_le f s).trans
    (Nat.mul_le_mul_left 576 (SqPair.canonical_le f s)))
  exact (Nat.cast_le.mpr hcount).trans (bound M hM A hA)
