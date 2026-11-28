import Mathlib

theorem Conjectures.Cuts.Taskf3d6edc1fd081a479fa48cd1 : (by
  classical
  exact ∀ (U A B : Finset ℕ) (G F : ℕ → Finset ℕ) (i j : ℕ),
    (∀ n ∈ U, G n ⊆ A ∧ F n ⊆ B) →
    (∑ n ∈ U, (G n).card.choose i*(F n).card.choose j) =
      ∑ s ∈ A.powersetCard i, ∑ t ∈ B.powersetCard j, (U.filter (fun n => s ⊆ G n ∧ t ⊆ F n)).card) := by
  classical
  intro U A B G F i j h
  have candidates (n : ℕ) (hn : n ∈ U) :
      (G n).card.choose i*(F n).card.choose j =
      ∑ s ∈ A.powersetCard i, ∑ t ∈ B.powersetCard j, (if s ⊆ G n ∧ t ⊆ F n then 1 else 0 : ℕ) := by
    have split (X Y : Finset ℕ) (k : ℕ) (hxy : X ⊆ Y) :
        ((Y.powersetCard k).filter (fun s => s ⊆ X)) = X.powersetCard k := by
      ext s
      simp only [Finset.mem_filter,Finset.mem_powersetCard]
      exact ⟨fun h => ⟨h.2,h.1.2⟩,fun h => ⟨⟨h.1.trans hxy,h.2⟩,h.1⟩⟩
    have prod (s t : Finset ℕ) :
      (if s ⊆ G n ∧ t ⊆ F n then 1 else 0 : ℕ) =
      (if s ⊆ G n then 1 else 0)*(if t ⊆ F n then 1 else 0) := by
      by_cases hs : s ⊆ G n <;> by_cases ht : t ⊆ F n <;> simp [hs,ht]
    simp_rw [prod,← Finset.mul_sum]
    rw [← Finset.sum_mul]
    simp [Finset.sum_boole,split _ A i (h n hn).1,split _ B j (h n hn).2]
  calc
    _ = ∑ n ∈ U, ∑ s ∈ A.powersetCard i, ∑ t ∈ B.powersetCard j,
          (if s ⊆ G n ∧ t ⊆ F n then 1 else 0 : ℕ) := Finset.sum_congr rfl candidates
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro s _
      rw [Finset.sum_comm]
      simp [Finset.sum_boole]
