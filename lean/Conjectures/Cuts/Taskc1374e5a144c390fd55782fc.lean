import Mathlib
import Conjectures.Cuts.Taskf7c18a375028fb1ff2783f5b

namespace CubicTripleCount

/-- Translating one copy of a finite integer-valued distribution cannot
increase the number of equal-value pairs, by Cauchy–Schwarz on the fibers. -/
theorem shift_le {β : Type*} [Fintype β] [DecidableEq β] (f : β → ℤ) (d : ℤ) :
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

/-- Fix the first index on each side of a triple collision. The remaining
two coordinates on each side give a pair collision with a fixed shift. -/
theorem triple_le (A : Finset ℕ) (v : ℕ → ℤ) :
    let T := Fintype.piFinset fun _ : Fin 3 => A
    let w := fun x : Fin 3 → ℕ => ∑ i, v (x i)
    ((T.product T).filter (fun z => w z.1 = w z.2)).card ≤ A.card ^ 2 *
      ((Finset.univ : Finset ((Fin 2 → ↥A) × (Fin 2 → ↥A))).filter
        (fun z => (∑ i, v (z.1 i)) = ∑ i, v (z.2 i))).card := by
  classical
  intro T w
  let S := (T.product T).filter (fun z => w z.1 = w z.2)
  let first := fun z : (Fin 3 → ℕ) × (Fin 3 → ℕ) => (z.1 0, z.2 0)
  let f := fun x : Fin 2 → ↥A => ∑ i, v (x i)
  let H := (Finset.univ : Finset ((Fin 2 → ↥A) × (Fin 2 → ↥A))).filter (fun z => f z.1 = f z.2)
  have mems {z} (hz : z ∈ S) : (∀ i, z.1 i ∈ A) ∧ (∀ i, z.2 i ∈ A) := by
    obtain ⟨hl, hr⟩ := Finset.mem_product.mp (Finset.mem_filter.mp hz).1
    exact ⟨Fintype.mem_piFinset.mp hl, Fintype.mem_piFinset.mp hr⟩
  have maps : ∀ z ∈ S, first z ∈ A.product A := fun z hz =>
    Finset.mem_product.mpr ⟨(mems hz).1 0, (mems hz).2 0⟩
  have bound (b : ℕ × ℕ) (_ : b ∈ A.product A) :
      (S.filter (fun z => first z = b)).card ≤ H.card := by
    let B := S.filter (fun z => first z = b)
    let D := (Finset.univ : Finset ((Fin 2 → ↥A) × (Fin 2 → ↥A))).filter
      (fun z => f z.1 = f z.2 + (v b.2 - v b.1))
    let tailPair (z : ↥B) : (Fin 2 → ↥A) × (Fin 2 → ↥A) :=
      (fun i => ⟨z.val.1 i.succ, (mems (Finset.mem_filter.mp z.prop).1).1 i.succ⟩,
       fun i => ⟨z.val.2 i.succ, (mems (Finset.mem_filter.mp z.prop).1).2 i.succ⟩)
    have hmem (z : ↥B) : tailPair z ∈ D := by
      obtain ⟨hz, hfix⟩ := Finset.mem_filter.mp z.prop
      have hw := (Finset.mem_filter.mp hz).2
      have h1 : z.val.1 0 = b.1 := congrArg Prod.fst hfix
      have h2 : z.val.2 0 = b.2 := congrArg Prod.snd hfix
      simp only [w, Fin.sum_univ_succ] at hw
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      dsimp [f, tailPair]
      rw [← h1, ← h2]
      simp only [Fin.sum_univ_succ]
      omega
    let pack := fun z : ↥B => (⟨tailPair z, hmem z⟩ : ↥D)
    have hinj : Function.Injective pack := by
      intro x y hxy
      have ht : tailPair x = tailPair y := congrArg Subtype.val hxy
      have hf : first x.val = first y.val :=
        (Finset.mem_filter.mp x.prop).2.trans (Finset.mem_filter.mp y.prop).2.symm
      apply Subtype.ext
      apply Prod.ext
      · funext i
        refine Fin.cases (congrArg Prod.fst hf) (fun j => ?_) i
        exact congrArg (fun z : (Fin 2 → ↥A) × (Fin 2 → ↥A) => (z.1 j : ℕ)) ht
      · funext i
        refine Fin.cases (congrArg Prod.snd hf) (fun j => ?_) i
        exact congrArg (fun z : (Fin 2 → ↥A) × (Fin 2 → ↥A) => (z.2 j : ℕ)) ht
    exact (Finset.card_le_card_of_injective hinj).trans (shift_le f (v b.2 - v b.1))
  have h := Finset.card_le_mul_card_image_of_maps_to maps H.card bound
  have hc : (A.product A).card = A.card * A.card := Finset.card_product A A
  rw [hc, Nat.mul_comm H.card] at h
  simpa only [pow_two] using h

end CubicTripleCount

theorem Conjectures.Cuts.Taskc1374e5a144c390fd55782fc : (∀ (x1 : Polynomial ℤ),   (3 : ℕ) ≤ x1.natDegree →     x1.natDegree = (3 : ℕ) →       ∀ (x4 : ℝ),         (0 : ℝ) < x4 →           ∃ (x6 : ℝ),             (0 : ℝ) < x6 ∧               ∀ (x7 : ℕ),                 (2 : ℕ) ≤ x7 →                   ∀ x9 ⊆ Finset.Icc (1 : ℕ) x7,                     have x11 : Finset (Fin (3 : ℕ) → ℕ) := Fintype.piFinset fun (x11 : Fin (3 : ℕ)) => x9;                     have x12 : (Fin (3 : ℕ) → ℕ) → ℤ := fun (x12 : Fin (3 : ℕ) → ℕ) => ∑ x13 : Fin (3 : ℕ), Polynomial.eval (↑(x12 x13)) x1;                     ↑{x13 ∈ x11.product x11 | x12 x13.1 = x12 x13.2 ∧ ∀ (x14 : Equiv.Perm (Fin (3 : ℕ))), x13.2 ≠ x13.1 ∘ ⇑x14}.card ≤ x6 * ↑x7 ^ x4 * ↑x9.card ^ (4 : ℕ)) := by
  classical
  intro P hdeg _ ε hε
  obtain ⟨C, hC, hpairs⟩ :=
    Conjectures.Cuts.Taskf7c18a375028fb1ff2783f5b P (by omega) ε hε
  refine ⟨C, hC, ?_⟩
  intro M hM A hA
  let v : ℕ → ℤ := fun a => P.eval (a : ℤ)
  let T := Fintype.piFinset (fun _ : Fin 3 => A)
  let w (x : Fin 3 → ℕ) := ∑ i, v (x i)
  let pairs := (Finset.univ : Finset ((Fin 2 → ↥A) × (Fin 2 → ↥A))).filter
    (fun z => (∑ i, v (z.1 i)) = ∑ i, v (z.2 i))
  have hsubset := Finset.card_le_card (Finset.monotone_filter_right
    (T.product T) (fun z _ (h : w z.1 = w z.2 ∧
      ∀ σ : Equiv.Perm (Fin 3), z.2 ≠ z.1 ∘ σ) => h.1))
  have htrip := CubicTripleCount.triple_le A v
  have hcount : ((T.product T).filter (fun z => w z.1 = w z.2 ∧
      ∀ σ : Equiv.Perm (Fin 3), z.2 ≠ z.1 ∘ σ)).card ≤ A.card ^ 2 * pairs.card :=
    hsubset.trans htrip
  have hc : (pairs.card : ℝ) ≤ C * (M : ℝ) ^ ε * (A.card : ℝ) ^ 2 := hpairs M hM A hA
  calc
    _ ≤ ((A.card : ℝ) ^ 2) * pairs.card := by exact_mod_cast hcount
    _ ≤ ((A.card : ℝ) ^ 2) * (C * (M : ℝ) ^ ε * (A.card : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hc (sq_nonneg _)
    _ = _ := by ring
