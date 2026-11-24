import Mathlib

theorem PEqualNP.Outside.L_log_rank_survive_deletion :
    ∀ (n : ℕ) (A : Finset (Fin n)) (a : ℤ) (Y D : Finset (Finset (Fin n))), let adj := fun (A B : Finset (Fin n)) (a : ℤ) => ((A ∩ B).card : ℤ) = a ∨ ((A ∩ B).card : ℤ) = a+1; (Y.filter (fun B => ¬ adj A B a)).card > D.card → ∃ B ∈ Y \ D, ¬ adj A B a := by
  intro n A a Y D
  dsimp only
  intro h
  by_contra hcon
  have hcon' : ∀ B, B ∈ Y \ D → (((A ∩ B).card : ℤ) = a ∨ ((A ∩ B).card : ℤ) = a + 1) := by
    intro B hB
    by_contra hB'
    exact hcon ⟨B, hB, hB'⟩
  have hsub : Y.filter (fun B => ¬ (((A ∩ B).card : ℤ) = a ∨ ((A ∩ B).card : ℤ) = a + 1)) ⊆ D := by
    intro B hB
    by_contra hBD
    exact (Finset.mem_filter.mp hB).2 (hcon' B (Finset.mem_sdiff.mpr ⟨(Finset.mem_filter.mp hB).1, hBD⟩))
  have hle := Finset.card_le_card hsub
  omega
