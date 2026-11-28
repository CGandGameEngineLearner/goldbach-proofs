import Mathlib

/-!
General deletion lemma for the no-three-in-line problem.

For every finite set `T` of lattice points there is a subset `S ⊆ T` containing no
lexicographically ordered collinear triple, with `|T| ≤ |S| + |collinearTriples T|`.

Method: strong induction on `|T|`.  If `T` has no ordered collinear triple, take `S = T`.
Otherwise pick one such triple `t` and delete its last point `c = t.2`.  The triples of
`T.erase c` form a subset of the triples of `T` that misses `t`, so
`|triples (T.erase c)| + 1 ≤ |triples T|`, and the induction hypothesis on `T.erase c`
closes the count.
-/

namespace Conjectures.Cuts.Task00cddfd15a40951185f88a70_aux

/-- Strict lexicographic order on lattice points. -/
def lexLt (a b : ℕ × ℕ) : Prop := a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 < b.2)

/-- Vanishing signed area of three lattice points. -/
def coll (a b c : ℕ × ℕ) : Prop :=
  ((b.1 : ℤ) - (a.1 : ℤ)) * ((c.2 : ℤ) - (a.2 : ℤ)) =
    ((b.2 : ℤ) - (a.2 : ℤ)) * ((c.1 : ℤ) - (a.1 : ℤ))

/-- The lexicographically ordered collinear triples of a point set. -/
def triples (A : Finset (ℕ × ℕ)) : Finset (((ℕ × ℕ) × (ℕ × ℕ)) × (ℕ × ℕ)) :=
  {x3 ∈ (A ×ˢ A) ×ˢ A |
    (x3.1.1.1 < x3.1.2.1 ∨ x3.1.1.1 = x3.1.2.1 ∧ x3.1.1.2 < x3.1.2.2) ∧
    (x3.1.2.1 < x3.2.1 ∨ x3.1.2.1 = x3.2.1 ∧ x3.1.2.2 < x3.2.2) ∧
    ((↑x3.1.2.1 : ℤ) - (↑x3.1.1.1 : ℤ)) * ((↑x3.2.2 : ℤ) - (↑x3.1.1.2 : ℤ)) =
      ((↑x3.1.2.2 : ℤ) - (↑x3.1.1.2 : ℤ)) * ((↑x3.2.1 : ℤ) - (↑x3.1.1.1 : ℤ))}

theorem mem_triples {A : Finset (ℕ × ℕ)} {x3 : ((ℕ × ℕ) × (ℕ × ℕ)) × (ℕ × ℕ)} :
    x3 ∈ triples A ↔ x3.1.1 ∈ A ∧ x3.1.2 ∈ A ∧ x3.2 ∈ A ∧
      lexLt x3.1.1 x3.1.2 ∧ lexLt x3.1.2 x3.2 ∧ coll x3.1.1 x3.1.2 x3.2 := by
  simp only [triples, Finset.mem_filter, Finset.mem_product]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4, h5, h6⟩
    exact ⟨h1, h2, h3, h4, h5, h6⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    exact ⟨⟨⟨h1, h2⟩, h3⟩, h4, h5, h6⟩

theorem triples_mono {A B : Finset (ℕ × ℕ)} (h : A ⊆ B) : triples A ⊆ triples B := by
  intro x3 hx3
  rw [mem_triples] at hx3 ⊢
  exact ⟨h hx3.1, h hx3.2.1, h hx3.2.2.1, hx3.2.2.2.1, hx3.2.2.2.2.1, hx3.2.2.2.2.2⟩

/-- Deletion lemma: a subset with no ordered collinear triple, deleting at most one point
per ordered collinear triple of the ambient set. -/
theorem exists_clean : ∀ (A : Finset (ℕ × ℕ)),
    ∃ S ⊆ A, triples S = ∅ ∧ A.card ≤ S.card + (triples A).card := by
  intro A
  have hmain : ∀ n : ℕ, ∀ B : Finset (ℕ × ℕ), B.card = n →
      ∃ S ⊆ B, triples S = ∅ ∧ B.card ≤ S.card + (triples B).card := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih B hB
    by_cases hT : triples B = ∅
    · refine ⟨B, subset_rfl, hT, ?_⟩
      simp [hT]
    · obtain ⟨t, ht⟩ := Finset.nonempty_iff_ne_empty.mpr hT
      have ht' : t.1.1 ∈ B ∧ t.1.2 ∈ B ∧ t.2 ∈ B ∧
          lexLt t.1.1 t.1.2 ∧ lexLt t.1.2 t.2 ∧ coll t.1.1 t.1.2 t.2 :=
        (mem_triples).mp ht
      have hcB : t.2 ∈ B := ht'.2.2.1
      have hcardB : B.card = (B.erase t.2).card + 1 := by
        rw [Finset.card_erase_of_mem hcB]
        have : 0 < B.card := Finset.card_pos.mpr ⟨t.2, hcB⟩
        omega
      have hlt : (B.erase t.2).card < n := by omega
      obtain ⟨S, hS, hS0, hScard⟩ := ih (B.erase t.2).card hlt (B.erase t.2) rfl
      have hSB : S ⊆ B := hS.trans (Finset.erase_subset _ _)
      have hmono : triples (B.erase t.2) ⊆ triples B := triples_mono (Finset.erase_subset _ _)
      have htn : t ∉ triples (B.erase t.2) := by
        rw [mem_triples]
        rintro ⟨_, _, h3, _⟩
        exact Finset.notMem_erase t.2 B h3
      have hcard : (triples (B.erase t.2)).card + 1 ≤ (triples B).card := by
        have h1 : insert t (triples (B.erase t.2)) ⊆ triples B := Finset.insert_subset ht hmono
        have h2 : (insert t (triples (B.erase t.2))).card = (triples (B.erase t.2)).card + 1 :=
          Finset.card_insert_of_notMem htn
        rw [← h2]
        exact Finset.card_le_card h1
      refine ⟨S, hSB, hS0, ?_⟩
      omega
  exact hmain A.card A rfl

end Conjectures.Cuts.Task00cddfd15a40951185f88a70_aux

theorem Conjectures.Cuts.Task00cddfd15a40951185f88a70 :
∀ (x1 : Finset (ℕ × ℕ)), ∃ x2 ⊆ x1, {x3 ∈ (x2 ×ˢ x2) ×ˢ x2 | (x3.1.1.1 < x3.1.2.1 ∨ x3.1.1.1 = x3.1.2.1 ∧ x3.1.1.2 < x3.1.2.2) ∧ (x3.1.2.1 < x3.2.1 ∨ x3.1.2.1 = x3.2.1 ∧ x3.1.2.2 < x3.2.2) ∧ ((↑x3.1.2.1 : ℤ) - (↑x3.1.1.1 : ℤ)) * ((↑x3.2.2 : ℤ) - (↑x3.1.1.2 : ℤ)) = ((↑x3.1.2.2 : ℤ) - (↑x3.1.1.2 : ℤ)) * ((↑x3.2.1 : ℤ) - (↑x3.1.1.1 : ℤ))} = ∅ ∧ x1.card ≤ x2.card + {x3 ∈ (x1 ×ˢ x1) ×ˢ x1 | (x3.1.1.1 < x3.1.2.1 ∨ x3.1.1.1 = x3.1.2.1 ∧ x3.1.1.2 < x3.1.2.2) ∧ (x3.1.2.1 < x3.2.1 ∨ x3.1.2.1 = x3.2.1 ∧ x3.1.2.2 < x3.2.2) ∧ ((↑x3.1.2.1 : ℤ) - (↑x3.1.1.1 : ℤ)) * ((↑x3.2.2 : ℤ) - (↑x3.1.1.2 : ℤ)) = ((↑x3.1.2.2 : ℤ) - (↑x3.1.1.2 : ℤ)) * ((↑x3.2.1 : ℤ) - (↑x3.1.1.1 : ℤ))}.card := by
  intro x1
  obtain ⟨S, hS, hS0, hScard⟩ :=
    Conjectures.Cuts.Task00cddfd15a40951185f88a70_aux.exists_clean x1
  refine ⟨S, hS, ?_, ?_⟩
  · exact hS0
  · exact hScard
