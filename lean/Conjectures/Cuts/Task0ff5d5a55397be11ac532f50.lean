import Mathlib

theorem Conjectures.Cuts.Task0ff5d5a55397be11ac532f50 : (∀ (x1 x2 : Finset ℕ) (x3 : ℕ → Finset ℕ) (x4 : ℕ), (∀ x5 ∈ x1, x3 x5 ⊆ x2) → ∑ x6 ∈ x1, (x3 x6).card.choose x4 = ∑ x6 ∈ Finset.powersetCard x4 x2, {x7 ∈ x1 | x6 ⊆ x3 x7}.card) := by
  classical
  intro A B F k hF
  have row (a : ℕ) (ha : a ∈ A) :
      (F a).card.choose k = ∑ s ∈ B.powersetCard k, if s ⊆ F a then 1 else 0 := by
    have sets : (F a).powersetCard k = (B.powersetCard k).filter (fun s => s ⊆ F a) := by
      ext s
      simp only [Finset.mem_filter, Finset.mem_powersetCard]
      exact ⟨fun h => ⟨⟨h.1.trans (hF a ha), h.2⟩, h.1⟩, fun h => ⟨h.2, h.1.2⟩⟩
    simpa using congrArg Finset.card sets
  calc
    _ = ∑ a ∈ A, ∑ s ∈ B.powersetCard k, if s ⊆ F a then 1 else 0 := Finset.sum_congr rfl row
    _ = ∑ s ∈ B.powersetCard k, ∑ a ∈ A, if s ⊆ F a then 1 else 0 := Finset.sum_comm
    _ = _ := by simp
