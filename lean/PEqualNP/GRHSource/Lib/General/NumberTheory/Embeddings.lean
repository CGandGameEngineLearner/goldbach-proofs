import PEqualNP.GRHSource.Lib.General.NumberTheory.PlaceEmbedding

/-! General lemmas of algebraic number theory (textbook or folklore).

This file: Complex embeddings of a totally complex field come in conjugate pairs. -/

open NumberField Polynomial ComplexEmbedding InfinitePlace Finset IsTotallyComplex


variable {E} [Field E] [IsTotallyComplex E]

@[simp, grind] lemma conjugate_ne_self σ : @conjugate E _ σ ≠ σ := complexEmbedding_not_isReal _

@[to_additive] lemma prod_embeddings_eq_prod_pairs [NumberField E]
  [PlaceEmbedding E] {M} [CommMonoid M] (F : (E →+* ℂ) → M) : ∏ σ, F σ = ∏ v, F (Φ v) * F (conjugate
  (Φ v)) := by
    classical
    rw [← Finset.prod_fiberwise Finset.univ mk F]
    apply Finset.prod_congr rfl
    intro v _
    apply Finset.prod_eq_mul_of_mem (Φ v) (conjugate (Φ v))
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, mk_Φ v⟩
    · apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, (mk_conjugate_eq (Φ v)).trans (mk_Φ v)⟩
    · exact (conjugate_ne_self (Φ v)).symm
    · intro σ hσ hne
      have hm := (Finset.mem_filter.mp hσ).2
      rcases mk_eq_iff.mp ((mk_Φ v).trans hm.symm) with h | h
      · exact (hne.1 h.symm).elim
      · exact (hne.2 h.symm).elim

omit [IsTotallyComplex E] in
lemma roots_map_conjugate (P : E[X]) (σ : E →+* ℂ) :
    (P.map (conjugate σ)).roots = (P.map σ).roots.map star := by
  have h := (IsAlgClosed.splits (P.map σ)).roots_map (starRingEnd ℂ)
  rw [Polynomial.map_map] at h
  exact h
