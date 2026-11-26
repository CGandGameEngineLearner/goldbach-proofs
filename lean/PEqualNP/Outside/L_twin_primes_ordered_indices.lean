import Mathlib

theorem PEqualNP.Outside.L_twin_primes_ordered_indices :
    ∀ m : ℕ, ((Finset.univ : Finset (Fin m × Fin m)).filter (fun z => z.1 ≠ z.2)).card = m*(m-1) := by
  intro m
  have hdiag : (Finset.univ : Finset (Fin m × Fin m)).filter (fun z => z.1 ≠ z.2)
      = (Finset.univ : Finset (Fin m × Fin m)) \ ((Finset.univ : Finset (Fin m)).image (fun i => (i, i))) := by
    ext ⟨i, j⟩
    simp
  have hsub : ((Finset.univ : Finset (Fin m)).image (fun i => (i, i))) ⊆ (Finset.univ : Finset (Fin m × Fin m)) := by
    intro x hx
    simp at hx
    obtain ⟨i, rfl⟩ := hx
    simp
  have hcard : ((Finset.univ : Finset (Fin m)).image (fun i => (i, i))).card = m := by
    rw [Finset.card_image_of_injective]
    · simp
    · intro a b hab
      simpa using congrArg Prod.fst hab
  have htot : ((Finset.univ : Finset (Fin m × Fin m))).card = m * m := by
    simp
  have harith : m * (m - 1) = m * m - m := by
    cases m with
    | zero => simp
    | succ k =>
      simp only [Nat.succ_sub_one, Nat.mul_succ]
      exact (Nat.add_sub_cancel _ _).symm
  rw [hdiag, Finset.card_sdiff_of_subset hsub, htot, hcard, harith]
