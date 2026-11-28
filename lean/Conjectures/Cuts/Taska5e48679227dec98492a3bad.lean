import Mathlib
import Conjectures.Cuts.Taskf7c18a375028fb1ff2783f5b

-- The finite-fiber shift lemma is from proof PR #4822.

namespace CubicTripleCount

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

end CubicTripleCount


namespace SquareMatch

noncomputable def energy (A : Finset ℕ) (v : ℕ → ℤ) : ℕ :=
  ((Finset.univ : Finset ((Fin 2 → ↥A) × (Fin 2 → ↥A))).filter
    (fun z => (∑ i, v (z.1 i)) = ∑ i, v (z.2 i))).card

end SquareMatch
namespace SquareMatch

theorem fixed_le (A : Finset ℕ) (v : ℕ → ℤ) :
    let T := Fintype.piFinset fun _ : Fin 4 => A
    let w := fun x : Fin 4 → ℕ => ∑ i, v (x i)
    ((T.product T).filter (fun z => w z.1 = w z.2 ∧
      (z.1 0)^2 + (z.1 1)^2 = (z.2 0)^2 + (z.2 1)^2)).card ≤
      energy A (fun a => (a : ℤ)^2) * energy A v := by
  classical
  intro T w
  let S := (T.product T).filter (fun z => w z.1 = w z.2 ∧
    (z.1 0)^2 + (z.1 1)^2 = (z.2 0)^2 + (z.2 1)^2)
  let B := (Fin 2 → ↥A) × (Fin 2 → ↥A)
  have mems (z : ↥S) : (∀ i, z.val.1 i ∈ A) ∧ (∀ i, z.val.2 i ∈ A) := by
    obtain ⟨hl, hr⟩ := Finset.mem_product.mp (Finset.mem_filter.mp z.prop).1
    exact ⟨Fintype.mem_piFinset.mp hl, Fintype.mem_piFinset.mp hr⟩
  let head (z : ↥S) : B :=
    (fun i => ⟨z.val.1 i.castSucc.castSucc, (mems z).1 _⟩,
     fun i => ⟨z.val.2 i.castSucc.castSucc, (mems z).2 _⟩)
  let tail (z : ↥S) : B :=
    (fun i => ⟨z.val.1 i.succ.succ, (mems z).1 _⟩,
     fun i => ⟨z.val.2 i.succ.succ, (mems z).2 _⟩)
  let G := (Finset.univ : Finset B).filter
    (fun z => (∑ i, ((z.1 i : ℕ) : ℤ)^2) = ∑ i, ((z.2 i : ℕ) : ℤ)^2)
  have into (z : ↥S) (_ : z ∈ Finset.univ) : head z ∈ G := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    simp only [Fin.sum_univ_two]
    exact_mod_cast (Finset.mem_filter.mp z.prop).2.2
  let f := fun x : Fin 2 → ↥A => ∑ i, v (x i)
  have fiber (b : B) (_ : b ∈ G) :
      ((Finset.univ : Finset ↥S).filter (fun z => head z = b)).card ≤ energy A v := by
    let src := (Finset.univ : Finset ↥S).filter (fun z => head z = b)
    let dst := (Finset.univ : Finset B).filter (fun z => f z.1 = f z.2 + (f b.2 - f b.1))
    have maps {z : ↥S} (hz : z ∈ src) : tail z ∈ dst := by
      have hfix := (Finset.mem_filter.mp hz).2
      have hs := (Finset.mem_filter.mp z.prop).2.1
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rw [← hfix]
      simp only [w, Fin.sum_univ_four] at hs
      simp only [f, head, tail, Fin.sum_univ_two]
      change v (z.val.1 2) + v (z.val.1 3) =
        v (z.val.2 2) + v (z.val.2 3) +
          ((v (z.val.2 0) + v (z.val.2 1)) - (v (z.val.1 0) + v (z.val.1 1)))
      omega
    have inj : Set.InjOn tail (↑src : Set ↥S) := by
      intro x hx y hy t
      have h : head x = head y :=
        (Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm
      have hL (i : Fin 2) := congrArg (fun q : B => (q.1 i : ℕ)) h
      have hR (i : Fin 2) := congrArg (fun q : B => (q.2 i : ℕ)) h
      have tL (i : Fin 2) := congrArg (fun q : B => (q.1 i : ℕ)) t
      have tR (i : Fin 2) := congrArg (fun q : B => (q.2 i : ℕ)) t
      apply Subtype.ext
      apply Prod.ext
      · funext i
        fin_cases i
        · exact hL 0
        · exact hL 1
        · exact tL 0
        · exact tL 1
      · funext i
        fin_cases i
        · exact hR 0
        · exact hR 1
        · exact tR 0
        · exact tR 1
    exact (Finset.card_le_card_of_injOn tail (fun _ hz => maps hz) inj).trans
      (CubicTripleCount.shift_le f (f b.2 - f b.1))
  have bound := Finset.card_le_mul_card_image_of_maps_to into (energy A v) fiber
  change S.card ≤ G.card * energy A v
  simpa only [Finset.card_univ, Fintype.card_coe, Nat.mul_comm (energy A v)] using bound

end SquareMatch

namespace SquareMatch

private theorem move_pair (i j : Fin 4) (h : i ≠ j) :
    ∃ σ : Equiv.Perm (Fin 4), σ 0 = i ∧ σ 1 = j := by
  let τ := Equiv.swap 0 i
  have hτ : τ 0 = i := Equiv.swap_apply_left _ _
  have h0 : (0 : Fin 4) ≠ τ.symm j := by
    intro he
    exact h (hτ.symm.trans ((congrArg τ he).trans (τ.apply_symm_apply j)))
  refine ⟨(Equiv.swap 1 (τ.symm j)).trans τ, ?_, ?_⟩
  · change τ (Equiv.swap 1 (τ.symm j) 0) = i
    rw [Equiv.swap_apply_of_ne_of_ne (by decide : (0 : Fin 4) ≠ 1) h0, hτ]
  · change τ (Equiv.swap 1 (τ.symm j) 1) = j
    rw [Equiv.swap_apply_left, τ.apply_symm_apply]

theorem any_le (A : Finset ℕ) (v : ℕ → ℤ) :
    let T := Fintype.piFinset fun _ : Fin 4 => A
    let w := fun x : Fin 4 → ℕ => ∑ i, v (x i)
    let S := (T.product T).filter (fun z => w z.1 = w z.2 ∧
      ∀ ij : Fin 4 × Fin 4, z.1 ij.1 ≠ z.2 ij.2)
    (S.filter (fun z => ∃ ij kl : Fin 4 × Fin 4, ij.1 ≠ ij.2 ∧ kl.1 ≠ kl.2 ∧
      z.1 ij.1 ^ 2 + z.1 ij.2 ^ 2 = z.2 kl.1 ^ 2 + z.2 kl.2 ^ 2)).card ≤
      576 * (energy A (fun a => (a : ℤ)^2) * energy A v) := by
  classical
  intro T w S
  let D := (T.product T).filter (fun z => w z.1 = w z.2 ∧
    z.1 0 ^ 2 + z.1 1 ^ 2 = z.2 0 ^ 2 + z.2 1 ^ 2)
  let perms := (Finset.univ : Finset (Equiv.Perm (Fin 4) × Equiv.Perm (Fin 4)))
  let blocks (p : Equiv.Perm (Fin 4) × Equiv.Perm (Fin 4)) :=
    D.image (fun z => (z.1 ∘ p.1.symm, z.2 ∘ p.2.symm))
  apply le_trans (b := (perms.biUnion blocks).card)
  · apply Finset.card_le_card
    intro z hz
    obtain ⟨hzS, ij, kl, hi, hk, hmatch⟩ := Finset.mem_filter.mp hz
    obtain ⟨hzT, hw, _⟩ := Finset.mem_filter.mp hzS
    obtain ⟨hxT, hyT⟩ := Finset.mem_product.mp hzT
    obtain ⟨σ,hσ₀,hσ₁⟩ := move_pair _ _ hi
    obtain ⟨τ,hτ₀,hτ₁⟩ := move_pair _ _ hk
    apply Finset.mem_biUnion.mpr
    refine ⟨(σ,τ), Finset.mem_univ _, Finset.mem_image.mpr ⟨(z.1 ∘ σ, z.2 ∘ τ), ?_, ?_⟩⟩
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ?_, ?_⟩
      · exact Fintype.mem_piFinset.mpr fun i => Fintype.mem_piFinset.mp hxT (σ i)
      · exact Fintype.mem_piFinset.mpr fun i => Fintype.mem_piFinset.mp hyT (τ i)
      · exact (Equiv.sum_comp σ (fun i => v (z.1 i))).trans (hw.trans (Equiv.sum_comp τ (fun i => v (z.2 i))).symm)
      · simpa only [Function.comp_apply, hσ₀, hσ₁, hτ₀, hτ₁] using hmatch
    · apply Prod.ext <;> funext i <;> simp
  · have h := Finset.card_biUnion_le_card_mul perms blocks D.card (fun _ _ => Finset.card_image_le)
    have hcard : perms.card = 576 := by
      norm_num [perms, Fintype.card_prod, Fintype.card_perm, Nat.factorial]
    rw [hcard] at h
    exact h.trans (Nat.mul_le_mul_left _ (fixed_le A v))

end SquareMatch

theorem Conjectures.Cuts.Taska5e48679227dec98492a3bad : (∀ (x1 : Polynomial ℤ),   (3 : ℕ) ≤ x1.natDegree →     ∀ (x3 : ℝ),       (0 : ℝ) < x3 →         ∃ (x5 : ℝ),           (0 : ℝ) < x5 ∧             ∀ (x6 : ℕ),               (2 : ℕ) ≤ x6 →                 ∀ x8 ⊆ Finset.Icc (1 : ℕ) x6,                   have x10 : Finset (Fin (4 : ℕ) → ℕ) := Fintype.piFinset fun (x10 : Fin (4 : ℕ)) => x8;                   let x11 : (Fin (4 : ℕ) → ℕ) → ℤ := fun (x11 : Fin (4 : ℕ) → ℕ) => ∑ x12 : Fin (4 : ℕ), Polynomial.eval (↑(x11 x12) : ℤ) x1;                   have x12 : Finset ((Fin (4 : ℕ) → ℕ) × (Fin (4 : ℕ) → ℕ)) := {x12 ∈ x10.product x10 | x11 x12.1 = x11 x12.2 ∧ ∀ (x13 : Fin (4 : ℕ) × Fin (4 : ℕ)), x12.1 x13.1 ≠ x12.2 x13.2};                   (↑{x13 ∈ x12 | ∃ (x14 : Fin (4 : ℕ) × Fin (4 : ℕ)) (x15 : Fin (4 : ℕ) × Fin (4 : ℕ)), x14.1 ≠ x14.2 ∧ x15.1 ≠ x15.2 ∧ x13.1 x14.1 ^ (2 : ℕ) + x13.1 x14.2 ^ (2 : ℕ) = x13.2 x15.1 ^ (2 : ℕ) + x13.2 x15.2 ^ (2 : ℕ)}.card : ℝ) ≤ x5 * (↑x6 : ℝ) ^ x3 * (↑x8.card : ℝ) ^ (4 : ℕ)) := by
  classical
  intro P hdeg ε hε
  have hhalf : 0 < ε / 2 := by positivity
  let Q : Polynomial ℤ := Polynomial.X ^ 2
  have hQ : 2 ≤ Q.natDegree := by simp [Q]
  obtain ⟨C, hC, hpair⟩ :=
    Conjectures.Cuts.Taskf7c18a375028fb1ff2783f5b P (by omega) (ε / 2) hhalf
  obtain ⟨D, hD, hsquare⟩ :=
    Conjectures.Cuts.Taskf7c18a375028fb1ff2783f5b Q hQ (ε / 2) hhalf
  refine ⟨576 * (D * C), by positivity, ?_⟩
  intro M hM A hA
  let v (a : ℕ) := P.eval (a : ℤ)
  let s (a : ℕ) := (a : ℤ)^2
  have hp : (SquareMatch.energy A v : ℝ) ≤ C * (M : ℝ)^(ε / 2) * (A.card : ℝ)^2 :=
    hpair M hM A hA
  have hs : (SquareMatch.energy A s : ℝ) ≤ D * (M : ℝ)^(ε / 2) * (A.card : ℝ)^2 := by
    simpa only [Q, Polynomial.eval_pow, Polynomial.eval_X, SquareMatch.energy, s] using
      hsquare M hM A hA
  have count := SquareMatch.any_le A v
  have product := mul_le_mul hs hp (Nat.cast_nonneg _) (by positivity)
  have hrpow : (M : ℝ) ^ (ε / 2) * (M : ℝ) ^ (ε / 2) = (M : ℝ) ^ ε := by
    rw [← Real.rpow_add (by exact_mod_cast (show 0 < M by omega))]
    congr 1
    ring
  calc
    _ ≤ 576 * ((SquareMatch.energy A s : ℝ) * (SquareMatch.energy A v : ℝ)) := by
      exact_mod_cast count
    _ ≤ 576 * ((D * (M : ℝ)^(ε/2) * (A.card : ℝ)^2) *
        (C * (M : ℝ)^(ε/2) * (A.card : ℝ)^2)) := by
      exact mul_le_mul_of_nonneg_left product (by norm_num)
    _ = (576 * (D * C)) * ((M : ℝ)^(ε/2) * (M : ℝ)^(ε/2)) * (A.card : ℝ)^4 := by ring
    _ = _ := by rw [hrpow]
