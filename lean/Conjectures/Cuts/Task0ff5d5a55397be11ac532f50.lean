import Mathlib

theorem Conjectures.Cuts.Task0ff5d5a55397be11ac532f50 : (∀ (x1 x2 : Finset ℕ) (x3 : ℕ → Finset ℕ) (x4 : ℕ), (∀ x5 ∈ x1, x3 x5 ⊆ x2) → ∑ x6 ∈ x1, (x3 x6).card.choose x4 = ∑ x6 ∈ Finset.powersetCard x4 x2, {x7 ∈ x1 | x6 ⊆ x3 x7}.card) := by
  classical
  intro A U F k hF
  have restrict (a : ℕ) (ha : a ∈ A) :
      ((U.powersetCard k).filter fun T => T ⊆ F a) = (F a).powersetCard k := by
    ext T
    simp only [Finset.mem_filter, Finset.mem_powersetCard]
    constructor
    · rintro ⟨⟨_, hcard⟩, hsub⟩
      exact ⟨hsub, hcard⟩
    · rintro ⟨hsub, hcard⟩
      exact ⟨⟨hsub.trans (hF a ha), hcard⟩, hsub⟩
  calc
    _ = ∑ a ∈ A, ∑ T ∈ U.powersetCard k, (if T ⊆ F a then 1 else 0 : ℕ) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_boole (R := ℕ) (fun T => T ⊆ F a) (U.powersetCard k)]
      simp [restrict a ha]
    _ = ∑ T ∈ U.powersetCard k, ∑ a ∈ A, (if T ⊆ F a then 1 else 0 : ℕ) := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro T _
      exact Finset.sum_boole (R := ℕ) (fun a => T ⊆ F a) A
