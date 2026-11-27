import Mathlib

/-- Joshi III, route JA-0025: a quotient-lattice spanning witness set lifts back to the
ambient lattice once the base lattice `L` sits inside the hull `C`.

Given `L ≤ C` and, for every `x`, a representative `y ∈ C` with `x - y ∈ L`, every element
`x = (x - y) + y` lies in `C`; hence `C` is the whole additive group. -/
theorem Conjectures.JoshiAbc.ThreeLift :
    ∀ (G : Type) [AddCommGroup G] (C L : AddSubgroup G), L ≤ C → (∀ x : G, ∃ y ∈ C, x-y ∈ L) → C=⊤ := by
  intro G _ C L hLC hcov
  have hmem : ∀ x : G, x ∈ C := by
    intro x
    obtain ⟨y, hy, hxy⟩ := hcov x
    have hx : x = (x - y) + y := by abel
    rw [hx]
    exact C.add_mem (hLC hxy) hy
  refine le_antisymm le_top ?_
  intro x _
  exact hmem x
