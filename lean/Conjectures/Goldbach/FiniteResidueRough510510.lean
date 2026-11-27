import Mathlib

theorem Conjectures.Goldbach.FiniteResidueRough510510 :
    ∀ a : ℕ, a < 510510 → Even a →
      ∃ p ∈ ({3, 5, 7, 11, 41, 61, 79, 149, 167, 769, 1747, 2297, 2311} : Finset ℕ),
        Nat.Coprime ((a + 510510 - p) % 510510) 510510 := by
  have key : (Finset.range 510510).filter
      (fun a => a % 2 = 0 ∧
        (({3, 5, 7, 11, 41, 61, 79, 149, 167, 769, 1747, 2297, 2311} : Finset ℕ).filter
          (fun p => Nat.Coprime ((a + 510510 - p) % 510510) 510510)) = ∅) = ∅ := by
    decide
  intro a ha hev
  by_contra h
  have hinner :
      (({3, 5, 7, 11, 41, 61, 79, 149, 167, 769, 1747, 2297, 2311} : Finset ℕ).filter
        (fun p => Nat.Coprime ((a + 510510 - p) % 510510) 510510)) = ∅ := by
    rw [Finset.eq_empty_iff_forall_not_mem]
    intro p hp hc
    exact h ⟨p, hp, (Finset.mem_filter.mp hc).2⟩
  have hmem : a ∈ (Finset.range 510510).filter
      (fun a => a % 2 = 0 ∧
        (({3, 5, 7, 11, 41, 61, 79, 149, 167, 769, 1747, 2297, 2311} : Finset ℕ).filter
          (fun p => Nat.Coprime ((a + 510510 - p) % 510510) 510510)) = ∅) := by
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨ha, Nat.even_iff.mp hev, hinner⟩
  rw [key] at hmem
  exact absurd hmem (by simp)
