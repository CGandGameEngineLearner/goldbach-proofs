import Mathlib

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace PEqualNP.Outside

/-- Residue roughness modulo `30030 = 2 * 3 * 5 * 7 * 11 * 13`: every even residue class
`a` below `30030` can be shifted by one of `3, 5, 7, 11, 31, 43, 61, 79, 149, 197`
into a class coprime to `30030`. The verification is a finite computation. -/
theorem L_goldbach_finite_residue_rough_30030 :
    ∀ a : ℕ, a < 30030 → Even a →
      ∃ p ∈ ({3, 5, 7, 11, 31, 43, 61, 79, 149, 197} : Finset ℕ),
        Nat.Coprime ((a + 30030 - p) % 30030) 30030 := by
  have key : (Finset.range 30030).filter
      (fun a => a % 2 = 0 ∧
        (({3, 5, 7, 11, 31, 43, 61, 79, 149, 197} : Finset ℕ).filter
          (fun p => Nat.Coprime ((a + 30030 - p) % 30030) 30030)) = ∅) = ∅ := by
    decide
  intro a ha hev
  by_contra h
  have hinner : (({3, 5, 7, 11, 31, 43, 61, 79, 149, 197} : Finset ℕ).filter
      (fun p => Nat.Coprime ((a + 30030 - p) % 30030) 30030)) = ∅ := by
    apply Finset.filter_false_of_mem
    intro p hp hc
    exact h ⟨p, hp, hc⟩
  have hmem : a ∈ (Finset.range 30030).filter
      (fun a => a % 2 = 0 ∧
        (({3, 5, 7, 11, 31, 43, 61, 79, 149, 197} : Finset ℕ).filter
          (fun p => Nat.Coprime ((a + 30030 - p) % 30030) 30030)) = ∅) := by
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨ha, Nat.even_iff.mp hev, hinner⟩
  rw [key] at hmem
  exact absurd hmem (by simp)

end PEqualNP.Outside
