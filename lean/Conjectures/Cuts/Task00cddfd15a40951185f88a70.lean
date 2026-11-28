import Mathlib

namespace Conjectures.Cuts

private def collinearTriples (T : Finset (ℕ × ℕ)) :
    Finset (((ℕ × ℕ) × (ℕ × ℕ)) × (ℕ × ℕ)) :=
  {t ∈ (T ×ˢ T) ×ˢ T |
    (t.1.1.1 < t.1.2.1 ∨ t.1.1.1 = t.1.2.1 ∧ t.1.1.2 < t.1.2.2) ∧
    (t.1.2.1 < t.2.1 ∨ t.1.2.1 = t.2.1 ∧ t.1.2.2 < t.2.2) ∧
    ((t.1.2.1 : ℤ) - (t.1.1.1 : ℤ)) * ((t.2.2 : ℤ) - (t.1.1.2 : ℤ)) =
      ((t.1.2.2 : ℤ) - (t.1.1.2 : ℤ)) * ((t.2.1 : ℤ) - (t.1.1.1 : ℤ))}

private theorem remove_collinear_triples (T : Finset (ℕ × ℕ)) :
    ∃ S ⊆ T, collinearTriples S = ∅ ∧ T.card ≤ S.card + (collinearTriples T).card := by
  classical
  refine Finset.strongInductionOn T ?_
  intro T ih
  by_cases h : collinearTriples T = ∅
  · exact ⟨T, Finset.Subset.rfl, h, by simp [h]⟩
  obtain ⟨t, ht⟩ := Finset.nonempty_iff_ne_empty.mpr h
  have hp : t.1.1 ∈ T :=
    (Finset.mem_product.mp (Finset.mem_product.mp (Finset.mem_filter.mp ht).1).1).1
  let U := T.erase t.1.1
  have hu : U ⊂ T := Finset.erase_ssubset hp
  obtain ⟨S, hSU, hS, hbound⟩ := ih U hu
  -- Deleting a vertex cannot create triples, and the selected triple disappears.
  have htriples : collinearTriples U ⊆ (collinearTriples T).erase t := by
    intro u hu'
    have hfilter := Finset.mem_filter.mp hu'
    have hprod := Finset.mem_product.mp hfilter.1
    have hpair := Finset.mem_product.mp hprod.1
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_filter.mpr ⟨?_, hfilter.2⟩⟩
    · rintro rfl
      simpa [U] using hpair.1
    · exact Finset.mem_product.mpr
        ⟨Finset.mem_product.mpr ⟨hu.subset hpair.1, hu.subset hpair.2⟩,
          hu.subset hprod.2⟩
  have hcard := Finset.card_le_card htriples
  rw [Finset.card_erase_of_mem ht] at hcard
  have hU : U.card = T.card - 1 := Finset.card_erase_of_mem hp
  have hposT : 0 < T.card := Finset.card_pos.mpr ⟨_, hp⟩
  have hposTriples : 0 < (collinearTriples T).card := Finset.card_pos.mpr ⟨_, ht⟩
  exact ⟨S, hSU.trans hu.subset, hS, by omega⟩

end Conjectures.Cuts

theorem Conjectures.Cuts.Task00cddfd15a40951185f88a70 :
    ∀ (x1 : Finset (ℕ × ℕ)), ∃ x2 ⊆ x1, {x3 ∈ (x2 ×ˢ x2) ×ˢ x2 | (x3.1.1.1 < x3.1.2.1 ∨ x3.1.1.1 = x3.1.2.1 ∧ x3.1.1.2 < x3.1.2.2) ∧ (x3.1.2.1 < x3.2.1 ∨ x3.1.2.1 = x3.2.1 ∧ x3.1.2.2 < x3.2.2) ∧ ((↑x3.1.2.1 : ℤ) - (↑x3.1.1.1 : ℤ)) * ((↑x3.2.2 : ℤ) - (↑x3.1.1.2 : ℤ)) = ((↑x3.1.2.2 : ℤ) - (↑x3.1.1.2 : ℤ)) * ((↑x3.2.1 : ℤ) - (↑x3.1.1.1 : ℤ))} = ∅ ∧ x1.card ≤ x2.card + {x3 ∈ (x1 ×ˢ x1) ×ˢ x1 | (x3.1.1.1 < x3.1.2.1 ∨ x3.1.1.1 = x3.1.2.1 ∧ x3.1.1.2 < x3.1.2.2) ∧ (x3.1.2.1 < x3.2.1 ∨ x3.1.2.1 = x3.2.1 ∧ x3.1.2.2 < x3.2.2) ∧ ((↑x3.1.2.1 : ℤ) - (↑x3.1.1.1 : ℤ)) * ((↑x3.2.2 : ℤ) - (↑x3.1.1.2 : ℤ)) = ((↑x3.1.2.2 : ℤ) - (↑x3.1.1.2 : ℤ)) * ((↑x3.2.1 : ℤ) - (↑x3.1.1.1 : ℤ))}.card := by
  exact Conjectures.Cuts.remove_collinear_triples
