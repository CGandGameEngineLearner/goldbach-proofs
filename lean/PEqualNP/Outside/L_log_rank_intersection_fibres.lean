import Mathlib

theorem PEqualNP.Outside.L_log_rank_intersection_fibres :
    ∀ (n k t : ℕ) (A : Finset (Fin n)), t ≤ k → let layer := (Finset.univ : Finset (Fin n)).powersetCard k; (layer.filter (fun B => (A ∩ B).card = t)).card = Nat.choose A.card t * Nat.choose (n-A.card) (k-t) := by
  intro n k t A ht
  dsimp only
  have hU : (Finset.univ : Finset (Fin n)).card = n := by simp
  set S := ((Finset.univ : Finset (Fin n)).powersetCard k).filter (fun B => (A ∩ B).card = t) with hS
  set T := (A.powersetCard t) ×ˢ ((Finset.univ \ A).powersetCard (k - t)) with hT
  have hmain : S.card = T.card := by
    refine Finset.card_bij (s := S) (t := T) (fun B _ => (A ∩ B, B \ A)) ?_ ?_ ?_
    · intro B hB
      rw [hS, Finset.mem_filter, Finset.mem_powersetCard] at hB
      obtain ⟨⟨hBU, hBk⟩, hBt⟩ := hB
      rw [hT, Finset.mem_product, Finset.mem_powersetCard, Finset.mem_powersetCard]
      refine ⟨⟨Finset.inter_subset_left, hBt⟩, ?_, ?_⟩
      · intro x hx
        exact Finset.mem_sdiff.mpr ⟨hBU (Finset.mem_sdiff.mp hx).1, (Finset.mem_sdiff.mp hx).2⟩
      · rw [Finset.card_sdiff, hBk, hBt]
    · intro B1 _ B2 _ h
      have h1 : A ∩ B1 = A ∩ B2 := congrArg Prod.fst h
      have h2 : B1 \ A = B2 \ A := congrArg Prod.snd h
      have e1 : B1 = (B1 \ A) ∪ (B1 ∩ A) := (Finset.sdiff_union_inter B1 A).symm
      have e2 : B2 = (B2 \ A) ∪ (B2 ∩ A) := (Finset.sdiff_union_inter B2 A).symm
      rw [e1, e2, Finset.inter_comm B1 A, Finset.inter_comm B2 A, h2, h1]
    · rintro ⟨S1, T1⟩ hP
      rw [hT, Finset.mem_product, Finset.mem_powersetCard, Finset.mem_powersetCard] at hP
      obtain ⟨⟨hS1A, hS1c⟩, hT1U, hT1c⟩ := hP
      refine ⟨S1 ∪ T1, ?_, ?_⟩
      · rw [hS, Finset.mem_filter, Finset.mem_powersetCard]
        have hdisj : Disjoint S1 T1 := by
          rw [Finset.disjoint_left]
          intro x hxS hxT
          exact (Finset.mem_sdiff.mp (hT1U hxT)).2 (hS1A hxS)
        have hInter : A ∩ (S1 ∪ T1) = S1 := by
          ext x
          simp only [Finset.mem_inter, Finset.mem_union]
          constructor
          · rintro ⟨hxA, hxS | hxT⟩
            · exact hxS
            · exact absurd hxA ((Finset.mem_sdiff.mp (hT1U hxT)).2)
          · intro hx
            exact ⟨hS1A hx, Or.inl hx⟩
        refine ⟨⟨Finset.union_subset (hS1A.trans (Finset.subset_univ A)) (hT1U.trans Finset.sdiff_subset), ?_⟩, ?_⟩
        · rw [Finset.card_union_of_disjoint hdisj, hS1c, hT1c]
          exact Nat.add_sub_of_le ht
        · rw [hInter, hS1c]
      · apply Prod.ext
        · have hInter : A ∩ (S1 ∪ T1) = S1 := by
            ext x
            simp only [Finset.mem_inter, Finset.mem_union]
            constructor
            · rintro ⟨hxA, hxS | hxT⟩
              · exact hxS
              · exact absurd hxA ((Finset.mem_sdiff.mp (hT1U hxT)).2)
            · intro hx
              exact ⟨hS1A hx, Or.inl hx⟩
          exact hInter
        · have hSdiff : (S1 ∪ T1) \ A = T1 := by
            ext x
            simp only [Finset.mem_sdiff, Finset.mem_union]
            constructor
            · rintro ⟨hxS | hxT, hxA⟩
              · exact absurd (hS1A hxS) hxA
              · exact hxT
            · intro hx
              exact ⟨Or.inr hx, (Finset.mem_sdiff.mp (hT1U hx)).2⟩
          exact hSdiff
  rw [hmain, hT, Finset.card_product, Finset.card_powersetCard, Finset.card_powersetCard]
  congr 1
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ A), hU]
