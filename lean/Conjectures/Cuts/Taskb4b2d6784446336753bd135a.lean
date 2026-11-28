import Mathlib

/-!
Cut lemma of the exceptions route: double counting for families of sets of size at most one.

Both sides count the elements `z ∈ x1` whose `x3 z` is a nonempty subset of `x2`: for such `z` the
inner sum over `y ∈ x2` of the indicator `y ∈ x3 z` equals `(x3 z).card`, which by the hypothesis
`card ≤ 1` is the indicator of `(x3 z).Nonempty`.  Self-contained: Mathlib only.
-/

namespace Conjectures.Cuts.Taskb4b2d6784446336753bd135a_aux

lemma inner (x2 s : Finset ℕ) (hs : s ⊆ x2) :
    ∑ y ∈ x2, (if y ∈ s then (1 : ℕ) else 0) = s.card := by
  classical
  rw [Finset.sum_ite_mem]
  have hxs : x2 ∩ s = s := by
    ext y
    simp only [Finset.mem_inter]
    exact ⟨fun hy => hy.2, fun hy => ⟨hs hy, hy⟩⟩
  rw [hxs]
  simp

lemma card_indicator (s : Finset ℕ) (h : s.card ≤ 1) :
    s.card = (if s.Nonempty then (1 : ℕ) else 0) := by
  by_cases hn : s.Nonempty
  · have h1 : 1 ≤ s.card := Finset.one_le_card.mpr hn
    simp [hn]
    omega
  · have h0 : s.card = 0 := Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hn)
    rw [h0, if_neg hn]

end Conjectures.Cuts.Taskb4b2d6784446336753bd135a_aux

open Conjectures.Cuts.Taskb4b2d6784446336753bd135a_aux

theorem Conjectures.Cuts.Taskb4b2d6784446336753bd135a :
    ∀ (x1 x2 : Finset ℕ) (x3 : ℕ → Finset ℕ), (∀ x4 ∈ x1, x3 x4 ⊆ x2 ∧ (x3 x4).card ≤ (1 : ℕ)) → {x5 ∈ x1 | (x3 x5).Nonempty}.card = ∑ x5 ∈ x2, {x6 ∈ x1 | x5 ∈ x3 x6}.card := by
  intro x1 x2 x3 h
  classical
  have hL : {z ∈ x1 | (x3 z).Nonempty}.card =
      ∑ z ∈ x1, (if (x3 z).Nonempty then (1 : ℕ) else 0) := Finset.card_filter _ _
  have hR : (∑ y ∈ x2, {z ∈ x1 | y ∈ x3 z}.card) =
      ∑ z ∈ x1, ∑ y ∈ x2, (if y ∈ x3 z then (1 : ℕ) else 0) := by
    simp_rw [Finset.card_filter]
    rw [Finset.sum_comm]
  rw [hL, hR]
  refine Finset.sum_congr rfl ?_
  intro z hz
  obtain ⟨hsub, hcard⟩ := h z hz
  rw [inner x2 (x3 z) hsub, card_indicator (x3 z) hcard]
