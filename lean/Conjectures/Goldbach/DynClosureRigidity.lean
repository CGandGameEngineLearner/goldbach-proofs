import Mathlib

/-- A positive and a negative hit confine all candidate shifts to a finite
interval. One failing coordinate per shift would give a single finite window
in which none of those shifts could work. -/
theorem Conjectures.Goldbach.DynClosureRigidity :
    ∀ (A B : Set ℤ), (∀ x ∈ A, 0 < x) → (∀ x ∈ B, x < 0) →
      ∀ (P Q : Set ℤ), P.Nonempty → Q.Nonempty →
        (∀ F : Finset ℤ, ∃ k : ℤ, ∀ i ∈ F,
          (i ∈ P ↔ i+k ∈ A) ∧ (i ∈ Q ↔ i+k ∈ B)) →
        ∃ k : ℤ, ∀ i : ℤ, (i ∈ P ↔ i+k ∈ A) ∧ (i ∈ Q ↔ i+k ∈ B) := by
  classical
  intro A B hA hB P Q hP hQ hlocal
  obtain ⟨p, hp⟩ := hP
  obtain ⟨q, hq⟩ := hQ
  by_contra hglobal
  have fails (k : ℤ) :
      ∃ i : ℤ, ¬ ((i ∈ P ↔ i+k ∈ A) ∧ (i ∈ Q ↔ i+k ∈ B)) :=
    Classical.not_forall.mp (fun h => hglobal ⟨k, h⟩)
  choose witness hw using fails
  let shifts := Finset.Ioo (-p) (-q)
  let window := insert p (insert q (shifts.image witness))
  obtain ⟨k, hk⟩ := hlocal window
  have hpos := hA (p+k) ((hk p (by simp [window])).1.mp hp)
  have hneg := hB (q+k) ((hk q (by simp [window])).2.mp hq)
  have hshift : k ∈ shifts := Finset.mem_Ioo.mpr ⟨by omega, by omega⟩
  have hmem : witness k ∈ window :=
    Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_image_of_mem witness hshift))
  exact hw k (hk (witness k) hmem)
