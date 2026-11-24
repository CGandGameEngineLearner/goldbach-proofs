import Mathlib

private def sixLocal (t c : ℕ) (a : ℤ) : ℕ :=
  ∑ j ∈ Finset.range (t + 1),
    (if ((j + c : ℤ) = a ∨ (j + c : ℤ) = a + 1) then 0 else Nat.choose 3 j * Nat.choose 3 (t - j))

private def escLayer (n k : ℕ) (A : Finset (Fin n)) (a : ℤ) : Finset (Finset (Fin n)) :=
  ((Finset.univ : Finset (Fin n)).powersetCard k).filter
    (fun B => ((A ∩ B).card : ℤ) ≠ a ∧ ((A ∩ B).card : ℤ) ≠ a + 1)

private def traceFiber (n k t : ℕ) (A : Finset (Fin n)) (a : ℤ) (D : Finset (Fin n)) :
    Finset (Finset (Fin n)) :=
  (escLayer n k A a).filter (fun B => (B ∩ D).card = t)

private def pairSet (n k t : ℕ) (A : Finset (Fin n)) (a : ℤ) (D D₁ : Finset (Fin n)) :
    Finset (Finset (Fin n) × Finset (Fin n)) :=
  ((D.powersetCard t) ×ˢ ((Finset.univ \ D).powersetCard (k - t))).filter
    (fun p => ((D₁ ∩ p.1).card + (A ∩ p.2).card : ℤ) ≠ a
      ∧ ((D₁ ∩ p.1).card + (A ∩ p.2).card : ℤ) ≠ a + 1)

private lemma pairSet_card_eq_sum {n k t : ℕ} (A D D₁ : Finset (Fin n)) (a : ℤ) :
    (pairSet n k t A a D D₁).card
      = ∑ R ∈ (Finset.univ \ D).powersetCard (k - t),
          ((D.powersetCard t).filter (fun T => ((D₁ ∩ T).card + (A ∩ R).card : ℤ) ≠ a
            ∧ ((D₁ ∩ T).card + (A ∩ R).card : ℤ) ≠ a + 1)).card := by
  have hfiber := Finset.card_eq_sum_card_fiberwise
    (f := fun p : Finset (Fin n) × Finset (Fin n) => p.2)
    (s := pairSet n k t A a D D₁)
    (t := (Finset.univ \ D).powersetCard (k - t))
    (H := by
      intro p hp
      rw [Finset.mem_coe] at hp
      simp only [pairSet, Finset.mem_filter, Finset.mem_product] at hp
      exact hp.1.2)
  rw [hfiber]
  refine Finset.sum_congr rfl (fun R hR => ?_)
  refine Finset.card_bij (fun p _ => p.1) ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_filter] at hp
    obtain ⟨hpPair, hpR⟩ := hp
    simp only [pairSet, Finset.mem_filter, Finset.mem_product] at hpPair
    obtain ⟨⟨hpT, _⟩, he1, he2⟩ := hpPair
    refine Finset.mem_filter.mpr ⟨hpT, ?_, ?_⟩
    · simpa only [hpR] using he1
    · simpa only [hpR] using he2
  · intro p hp q hq hpq
    simp only [Finset.mem_filter] at hp hq
    exact Prod.ext hpq (hp.2.trans hq.2.symm)
  · intro T hT
    simp only [Finset.mem_filter] at hT
    obtain ⟨hTlayer, he1, he2⟩ := hT
    refine ⟨(T, R), ?_, rfl⟩
    refine Finset.mem_filter.mpr ⟨?_, rfl⟩
    refine Finset.mem_filter.mpr ⟨?_, he1, he2⟩
    exact Finset.mem_product.mpr ⟨hTlayer, hR⟩

private lemma pairSet_card_eq_traceFiber {n k t : ℕ} (A D D₁ : Finset (Fin n)) (a : ℤ)
    (hD1 : D₁ ⊆ D) (hAD : A ∩ D = D₁) (htk : t ≤ k) :
    (pairSet n k t A a D D₁).card = (traceFiber n k t A a D).card := by
  have hD1A : D₁ ⊆ A := by rw [← hAD]; exact Finset.inter_subset_left
  refine Finset.card_bij (fun p _ => p.1 ∪ p.2) ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_filter, pairSet, Finset.mem_product] at hp
    obtain ⟨⟨hp1, hp2⟩, he1, he2⟩ := hp
    obtain ⟨hp1D, hp1c⟩ := Finset.mem_powersetCard.mp hp1
    obtain ⟨hp2U, hp2c⟩ := Finset.mem_powersetCard.mp hp2
    have hBD : (p.1 ∪ p.2) ∩ D = p.1 := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_union]
      constructor
      · rintro ⟨hx1 | hx2, hxD⟩
        · exact hx1
        · exact absurd hxD ((Finset.mem_sdiff.mp (hp2U hx2)).2)
      · intro hx1
        exact ⟨Or.inl hx1, hp1D hx1⟩
    have hInterA : A ∩ (p.1 ∪ p.2) = (D₁ ∩ p.1) ∪ (A ∩ p.2) := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_union]
      constructor
      · rintro ⟨hxA, hx1 | hx2⟩
        · exact Or.inl ⟨by rw [← hAD]; exact Finset.mem_inter.mpr ⟨hxA, hp1D hx1⟩, hx1⟩
        · exact Or.inr ⟨hxA, hx2⟩
      · rintro (⟨hxD1, hx1⟩ | ⟨hxA, hx2⟩)
        · exact ⟨hD1A hxD1, Or.inl hx1⟩
        · exact ⟨hxA, Or.inr hx2⟩
    have hdisjA : Disjoint (D₁ ∩ p.1) (A ∩ p.2) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      exact (Finset.mem_sdiff.mp (hp2U (Finset.mem_inter.mp hx2).2)).2 (hD1 (Finset.mem_inter.mp hx1).1)
    have hAcard : (A ∩ (p.1 ∪ p.2)).card = (D₁ ∩ p.1).card + (A ∩ p.2).card := by
      rw [hInterA, Finset.card_union_of_disjoint hdisjA]
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · refine Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨?_, ?_⟩, ?_, ?_⟩
      · intro x hx
        exact Finset.mem_univ x
      · rw [Finset.card_union_of_disjoint (by
          rw [Finset.disjoint_left]
          intro x hx1 hx2
          exact (Finset.mem_sdiff.mp (hp2U hx2)).2 (hp1D hx1)), hp1c, hp2c,
          Nat.add_sub_of_le htk]
      · rw [hAcard]; exact he1
      · rw [hAcard]; exact he2
    · rw [hBD, hp1c]
  · intro p hp q hq hpq
    simp only [Finset.mem_filter, pairSet, Finset.mem_product] at hp hq
    obtain ⟨⟨hp1, hp2⟩, he1, he2⟩ := hp
    obtain ⟨⟨hq1, hq2⟩, he3, he4⟩ := hq
    obtain ⟨hp1D, hp1c⟩ := Finset.mem_powersetCard.mp hp1
    obtain ⟨hp2U, hp2c⟩ := Finset.mem_powersetCard.mp hp2
    obtain ⟨hq1D, hq1c⟩ := Finset.mem_powersetCard.mp hq1
    obtain ⟨hq2U, hq2c⟩ := Finset.mem_powersetCard.mp hq2
    have hBDp : (p.1 ∪ p.2) ∩ D = p.1 := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_union]
      constructor
      · rintro ⟨hx1 | hx2, hxD⟩
        · exact hx1
        · exact absurd hxD ((Finset.mem_sdiff.mp (hp2U hx2)).2)
      · intro hx1
        exact ⟨Or.inl hx1, hp1D hx1⟩
    have hBDq : (q.1 ∪ q.2) ∩ D = q.1 := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_union]
      constructor
      · rintro ⟨hx1 | hx2, hxD⟩
        · exact hx1
        · exact absurd hxD ((Finset.mem_sdiff.mp (hq2U hx2)).2)
      · intro hx1
        exact ⟨Or.inl hx1, hq1D hx1⟩
    have hRSp : (p.1 ∪ p.2) \ D = p.2 := by
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_union]
      constructor
      · rintro ⟨hx1 | hx2, hxD⟩
        · exact absurd (hp1D hx1) hxD
        · exact hx2
      · intro hx2
        exact ⟨Or.inr hx2, (Finset.mem_sdiff.mp (hp2U hx2)).2⟩
    have hRSq : (q.1 ∪ q.2) \ D = q.2 := by
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_union]
      constructor
      · rintro ⟨hx1 | hx2, hxD⟩
        · exact absurd (hq1D hx1) hxD
        · exact hx2
      · intro hx2
        exact ⟨Or.inr hx2, (Finset.mem_sdiff.mp (hq2U hx2)).2⟩
    apply Prod.ext
    · rw [← hBDp, ← hBDq, hpq]
    · rw [← hRSp, ← hRSq, hpq]
  · intro B hB
    simp only [traceFiber, Finset.mem_filter] at hB
    obtain ⟨hBesc, hBDc⟩ := hB
    simp only [escLayer, Finset.mem_filter] at hBesc
    obtain ⟨hBlayer, hBne1, hBne2⟩ := hBesc
    obtain ⟨hBsub, hBc⟩ := Finset.mem_powersetCard.mp hBlayer
    have hBDsub : B ∩ D ⊆ D := Finset.inter_subset_right
    have hKsub : B \ D ⊆ Finset.univ \ D := by
      intro x hx
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, (Finset.mem_sdiff.mp hx).2⟩
    have hKc : (B \ D).card = k - t := by
      rw [Finset.card_sdiff, hBc, Finset.inter_comm, hBDc]
    have hInterA : A ∩ B = (D₁ ∩ (B ∩ D)) ∪ (A ∩ (B \ D)) := by
      ext x
      constructor
      · intro hx
        have hxA : x ∈ A := (Finset.mem_inter.mp hx).1
        have hxB : x ∈ B := (Finset.mem_inter.mp hx).2
        by_cases hxD : x ∈ D
        · have hxD1 : x ∈ D₁ := by
            rw [← hAD]
            exact Finset.mem_inter.mpr ⟨hxA, hxD⟩
          exact Finset.mem_union_left _
            (Finset.mem_inter.mpr ⟨hxD1, Finset.mem_inter.mpr ⟨hxB, hxD⟩⟩)
        · exact Finset.mem_union_right _
            (Finset.mem_inter.mpr ⟨hxA, Finset.mem_sdiff.mpr ⟨hxB, hxD⟩⟩)
      · intro hx
        rcases Finset.mem_union.mp hx with h | h
        · obtain ⟨hxD1, hxBD⟩ := Finset.mem_inter.mp h
          exact Finset.mem_inter.mpr ⟨hD1A hxD1, (Finset.mem_inter.mp hxBD).1⟩
        · obtain ⟨hxA, hxsd⟩ := Finset.mem_inter.mp h
          exact Finset.mem_inter.mpr ⟨hxA, (Finset.mem_sdiff.mp hxsd).1⟩
    have hdisjA : Disjoint (D₁ ∩ (B ∩ D)) (A ∩ (B \ D)) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp hx2).2).2 (hD1 (Finset.mem_inter.mp hx1).1)
    have hAcard : (A ∩ B).card = (D₁ ∩ (B ∩ D)).card + (A ∩ (B \ D)).card := by
      rw [hInterA, Finset.card_union_of_disjoint hdisjA]
    have hUnion : (B ∩ D) ∪ (B \ D) = B := by
      rw [Finset.union_comm, Finset.sdiff_union_inter]
    refine ⟨(B ∩ D, B \ D), ?_, hUnion⟩
    refine Finset.mem_filter.mpr ⟨?_, ?_, ?_⟩
    · exact Finset.mem_product.mpr
        ⟨Finset.mem_powersetCard.mpr ⟨hBDsub, hBDc⟩, Finset.mem_powersetCard.mpr ⟨hKsub, hKc⟩⟩
    · change ((D₁ ∩ (B ∩ D)).card + (A ∩ (B \ D)).card : ℤ) ≠ a
      rw [← Nat.cast_add, ← hAcard]
      exact hBne1
    · change ((D₁ ∩ (B ∩ D)).card + (A ∩ (B \ D)).card : ℤ) ≠ a + 1
      rw [← Nat.cast_add, ← hAcard]
      exact hBne2

private lemma six_fibre_card {n : ℕ} (D D₁ : Finset (Fin n)) (t j : ℕ)
    (hD1 : D₁ ⊆ D) (hD : D.card = 6) (hD1c : D₁.card = 3) (hjt : j ≤ t) :
    ((D.powersetCard t).filter (fun T => (D₁ ∩ T).card = j)).card
      = Nat.choose 3 j * Nat.choose 3 (t - j) := by
  have hDsub : (D \ D₁).card = 3 := by
    rw [Finset.card_sdiff_of_subset hD1, hD, hD1c]
  set W := (D₁.powersetCard j) ×ˢ ((D \ D₁).powersetCard (t - j)) with hW
  have hmain : ((D.powersetCard t).filter (fun T => (D₁ ∩ T).card = j)).card = W.card := by
    refine Finset.card_bij (fun T _ => (D₁ ∩ T, T \ D₁)) ?_ ?_ ?_
    · intro T hT
      rw [Finset.mem_filter, Finset.mem_powersetCard] at hT
      obtain ⟨⟨hTD, hTc⟩, hTj⟩ := hT
      rw [hW, Finset.mem_product, Finset.mem_powersetCard, Finset.mem_powersetCard]
      refine ⟨⟨Finset.inter_subset_left, hTj⟩, ?_, ?_⟩
      · intro x hx
        exact Finset.mem_sdiff.mpr ⟨hTD (Finset.mem_sdiff.mp hx).1, (Finset.mem_sdiff.mp hx).2⟩
      · rw [Finset.card_sdiff, hTc, hTj]
    · intro T1 _ T2 _ h
      have h1 : D₁ ∩ T1 = D₁ ∩ T2 := congrArg Prod.fst h
      have h2 : T1 \ D₁ = T2 \ D₁ := congrArg Prod.snd h
      have e1 : T1 = (T1 \ D₁) ∪ (T1 ∩ D₁) := (Finset.sdiff_union_inter T1 D₁).symm
      have e2 : T2 = (T2 \ D₁) ∪ (T2 ∩ D₁) := (Finset.sdiff_union_inter T2 D₁).symm
      rw [e1, e2, Finset.inter_comm T1 D₁, Finset.inter_comm T2 D₁, h2, h1]
    · rintro ⟨S1, T1⟩ hP
      rw [hW, Finset.mem_product, Finset.mem_powersetCard, Finset.mem_powersetCard] at hP
      obtain ⟨⟨hS1D1, hS1c⟩, hT1U, hT1c⟩ := hP
      have hdisj : Disjoint S1 T1 := by
        rw [Finset.disjoint_left]
        intro x hxS hxT
        exact (Finset.mem_sdiff.mp (hT1U hxT)).2 (hS1D1 hxS)
      have hInter : D₁ ∩ (S1 ∪ T1) = S1 := by
        ext x
        simp only [Finset.mem_inter, Finset.mem_union]
        constructor
        · rintro ⟨hxA, hxS | hxT⟩
          · exact hxS
          · exact absurd hxA ((Finset.mem_sdiff.mp (hT1U hxT)).2)
        · intro hx
          exact ⟨hS1D1 hx, Or.inl hx⟩
      have hSdiff : (S1 ∪ T1) \ D₁ = T1 := by
        ext x
        simp only [Finset.mem_sdiff, Finset.mem_union]
        constructor
        · rintro ⟨hxS | hxT, hxA⟩
          · exact absurd (hS1D1 hxS) hxA
          · exact hxT
        · intro hx
          exact ⟨Or.inr hx, (Finset.mem_sdiff.mp (hT1U hx)).2⟩
      refine ⟨S1 ∪ T1, ?_, ?_⟩
      · rw [Finset.mem_filter, Finset.mem_powersetCard]
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · exact Finset.union_subset (hS1D1.trans hD1) (hT1U.trans Finset.sdiff_subset)
        · rw [Finset.card_union_of_disjoint hdisj, hS1c, hT1c]
          exact Nat.add_sub_of_le hjt
        · rw [hInter, hS1c]
      · apply Prod.ext
        · exact hInter
        · exact hSdiff
  rw [hmain, hW, Finset.card_product, Finset.card_powersetCard, Finset.card_powersetCard, hD1c, hDsub]


private lemma sixLocal_two (c : ℕ) (a : ℤ) : 3 ≤ sixLocal 2 c a := by
  have h : sixLocal 2 c a
      = (if (((0:ℕ) + c : ℤ) = a ∨ ((0:ℕ) + c : ℤ) = a + 1) then 0 else Nat.choose 3 0 * Nat.choose 3 (2 - 0))
      + (if (((1:ℕ) + c : ℤ) = a ∨ ((1:ℕ) + c : ℤ) = a + 1) then 0 else Nat.choose 3 1 * Nat.choose 3 (2 - 1))
      + (if (((2:ℕ) + c : ℤ) = a ∨ ((2:ℕ) + c : ℤ) = a + 1) then 0 else Nat.choose 3 2 * Nat.choose 3 (2 - 2)) := by
    simp only [sixLocal, Finset.sum_range_succ, Finset.sum_range_zero, Nat.zero_add]
  rw [h]
  norm_num
  split_ifs <;> omega

private lemma sixLocal_three (c : ℕ) (a : ℤ) : 2 ≤ sixLocal 3 c a := by
  have h : sixLocal 3 c a
      = (if (((0:ℕ) + c : ℤ) = a ∨ ((0:ℕ) + c : ℤ) = a + 1) then 0 else Nat.choose 3 0 * Nat.choose 3 (3 - 0))
      + (if (((1:ℕ) + c : ℤ) = a ∨ ((1:ℕ) + c : ℤ) = a + 1) then 0 else Nat.choose 3 1 * Nat.choose 3 (3 - 1))
      + (if (((2:ℕ) + c : ℤ) = a ∨ ((2:ℕ) + c : ℤ) = a + 1) then 0 else Nat.choose 3 2 * Nat.choose 3 (3 - 2))
      + (if (((3:ℕ) + c : ℤ) = a ∨ ((3:ℕ) + c : ℤ) = a + 1) then 0 else Nat.choose 3 3 * Nat.choose 3 (3 - 3)) := by
    simp only [sixLocal, Finset.sum_range_succ, Finset.sum_range_zero, Nat.zero_add]
  rw [h]
  norm_num
  split_ifs <;> omega

private lemma sixLocal_four (c : ℕ) (a : ℤ) : 3 ≤ sixLocal 4 c a := by
  have h : sixLocal 4 c a
      = (if (((0:ℕ) + c : ℤ) = a ∨ ((0:ℕ) + c : ℤ) = a + 1) then 0 else Nat.choose 3 0 * Nat.choose 3 (4 - 0))
      + (if (((1:ℕ) + c : ℤ) = a ∨ ((1:ℕ) + c : ℤ) = a + 1) then 0 else Nat.choose 3 1 * Nat.choose 3 (4 - 1))
      + (if (((2:ℕ) + c : ℤ) = a ∨ ((2:ℕ) + c : ℤ) = a + 1) then 0 else Nat.choose 3 2 * Nat.choose 3 (4 - 2))
      + (if (((3:ℕ) + c : ℤ) = a ∨ ((3:ℕ) + c : ℤ) = a + 1) then 0 else Nat.choose 3 3 * Nat.choose 3 (4 - 3))
      + (if (((4:ℕ) + c : ℤ) = a ∨ ((4:ℕ) + c : ℤ) = a + 1) then 0 else Nat.choose 3 4 * Nat.choose 3 (4 - 4)) := by
    simp only [sixLocal, Finset.sum_range_succ, Finset.sum_range_zero, Nat.zero_add]
  rw [h]
  norm_num
  split_ifs <;> omega

private lemma six_local_count {n : ℕ} (D D₁ : Finset (Fin n)) (t c : ℕ) (a : ℤ)
    (hD1 : D₁ ⊆ D) (hD : D.card = 6) (hD1c : D₁.card = 3) :
    ((D.powersetCard t).filter (fun T => ((D₁ ∩ T).card + c : ℤ) ≠ a ∧ ((D₁ ∩ T).card + c : ℤ) ≠ a + 1)).card
      = sixLocal t c a := by
  have hfiber := Finset.card_eq_sum_card_fiberwise
    (f := fun T : Finset (Fin n) => (D₁ ∩ T).card)
    (s := (D.powersetCard t).filter
      (fun T => ((D₁ ∩ T).card + c : ℤ) ≠ a ∧ ((D₁ ∩ T).card + c : ℤ) ≠ a + 1))
    (t := Finset.range (t + 1))
    (H := by
      intro T hT
      rw [Finset.mem_coe] at hT
      rw [Finset.mem_filter, Finset.mem_powersetCard] at hT
      obtain ⟨⟨hTD, hTc⟩, _⟩ := hT
      rw [Finset.mem_coe, Finset.mem_range]
      change (D₁ ∩ T).card < t + 1
      have hle : (D₁ ∩ T).card ≤ T.card := Finset.card_le_card Finset.inter_subset_right
      omega)
  rw [hfiber, sixLocal]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have hjt : j ≤ t := by
    rw [Finset.mem_range] at hj
    omega
  by_cases hes : ((j : ℤ) + c = a ∨ (j : ℤ) + c = a + 1)
  · rw [ite_eq_left hes]
    have hemp : ((D.powersetCard t).filter
        (fun T => ((D₁ ∩ T).card + c : ℤ) ≠ a ∧ ((D₁ ∩ T).card + c : ℤ) ≠ a + 1)).filter
        (fun T => (D₁ ∩ T).card = j) = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro T hT
      simp only [Finset.mem_filter, Finset.mem_powersetCard] at hT
      obtain ⟨⟨⟨_, _⟩, he1, he2⟩, hTj⟩ := hT
      rcases hes with h | h
      · exact he1 (by omega)
      · exact he2 (by omega)
    rw [hemp, Finset.card_empty]
  · rw [ite_eq_right hes]
    have hset : ((D.powersetCard t).filter
        (fun T => ((D₁ ∩ T).card + c : ℤ) ≠ a ∧ ((D₁ ∩ T).card + c : ℤ) ≠ a + 1)).filter
        (fun T => (D₁ ∩ T).card = j)
        = (D.powersetCard t).filter (fun T => (D₁ ∩ T).card = j) := by
      apply Finset.ext
      intro T
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨⟨hTlayer, _, _⟩, hTj⟩
        exact ⟨hTlayer, hTj⟩
      · rintro ⟨hTlayer, hTj⟩
        refine ⟨⟨hTlayer, ?_, ?_⟩, hTj⟩
        · intro h; exact hes (Or.inl (by omega))
        · intro h; exact hes (Or.inr (by omega))
    rw [hset, six_fibre_card D D₁ t j hD1 hD hD1c hjt]

private def sixZetaLower (n k : ℕ) : ℕ :=
  3 * Nat.choose (n - 6) (k - 2)
    + (if 3 ≤ k then 2 * Nat.choose (n - 6) (k - 3) else 0)
    + (if 4 ≤ k then 3 * Nat.choose (n - 6) (k - 4) else 0)

private lemma fiberR_lower {n k t : ℕ} (A D D₁ : Finset (Fin n)) (a : ℤ) (e : ℕ)
    (hD1 : D₁ ⊆ D) (hD : D.card = 6) (hD1c : D₁.card = 3)
    (he : ∀ c : ℕ, e ≤ sixLocal t c a) :
    e * Nat.choose (n - 6) (k - t)
      ≤ ∑ R ∈ (Finset.univ \ D).powersetCard (k - t),
          ((D.powersetCard t).filter (fun T => ((D₁ ∩ T).card + (A ∩ R).card : ℤ) ≠ a
            ∧ ((D₁ ∩ T).card + (A ∩ R).card : ℤ) ≠ a + 1)).card := by
  have hcard : (Finset.univ \ D).card = n - 6 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ D), Finset.card_univ,
      Fintype.card_fin, hD]
  have hsum : ∑ R ∈ (Finset.univ \ D).powersetCard (k - t), e
      ≤ ∑ R ∈ (Finset.univ \ D).powersetCard (k - t),
          ((D.powersetCard t).filter (fun T => ((D₁ ∩ T).card + (A ∩ R).card : ℤ) ≠ a
            ∧ ((D₁ ∩ T).card + (A ∩ R).card : ℤ) ≠ a + 1)).card := by
    apply Finset.sum_le_sum
    intro R _
    rw [six_local_count D D₁ t (A ∩ R).card a hD1 hD hD1c]
    exact he (A ∩ R).card
  calc e * Nat.choose (n - 6) (k - t)
      = Nat.choose (n - 6) (k - t) * e := by ring
    _ = ((Finset.univ \ D).powersetCard (k - t)).card * e := by
        rw [Finset.card_powersetCard, hcard]
    _ = ∑ R ∈ (Finset.univ \ D).powersetCard (k - t), e :=
        (Finset.sum_const_nat (fun R _ => rfl)).symm
    _ ≤ _ := hsum

private lemma stepC_fiber_lower {n k t : ℕ} (A D D₁ : Finset (Fin n)) (a : ℤ) (e : ℕ)
    (hD1 : D₁ ⊆ D) (hAD : A ∩ D = D₁) (hD : D.card = 6) (hD1c : D₁.card = 3)
    (htk : t ≤ k) (he : ∀ c : ℕ, e ≤ sixLocal t c a) :
    e * Nat.choose (n - 6) (k - t) ≤ (traceFiber n k t A a D).card := by
  rw [← pairSet_card_eq_traceFiber A D D₁ a hD1 hAD htk, pairSet_card_eq_sum A D D₁ a]
  exact fiberR_lower A D D₁ a e hD1 hD hD1c he

private lemma six_coord_exists {n : ℕ} (A : Finset (Fin n)) (hA3 : 3 ≤ A.card)
    (hhalf : 2 * A.card ≤ n) :
    ∃ D D₁ D₂ : Finset (Fin n), D₁ ⊆ A ∧ D₂ ⊆ Aᶜ ∧ D₁.card = 3 ∧ D₂.card = 3
      ∧ Disjoint D₁ D₂ ∧ D = D₁ ∪ D₂ := by
  have hcompl : (Aᶜ : Finset (Fin n)).card = n - A.card := by
    rw [Finset.card_compl, Fintype.card_fin]
  have hAc3 : 3 ≤ (Aᶜ : Finset (Fin n)).card := by
    rw [hcompl]; omega
  obtain ⟨D₁, hD1A, hD1c⟩ := Finset.exists_subset_card_eq hA3
  obtain ⟨D₂, hD2Ac, hD2c⟩ := Finset.exists_subset_card_eq hAc3
  refine ⟨D₁ ∪ D₂, D₁, D₂, hD1A, hD2Ac, hD1c, hD2c, ?_, rfl⟩
  rw [Finset.disjoint_left]
  intro x hx1 hx2
  exact (Finset.mem_compl.mp (hD2Ac hx2)) (hD1A hx1)

private lemma stepC_escape_count (n k : ℕ) (A : Finset (Fin n)) (a : ℤ)
    (hk : 2 ≤ k) (hkn : k + 2 ≤ n) (hA3 : 3 ≤ A.card) (hhalf : 2 * A.card ≤ n) :
    sixZetaLower n k ≤ (escLayer n k A a).card := by
  obtain ⟨D, D₁, D₂, hD1A, hD2Ac, hD1c, hD2c, hdisj, rfl⟩ := six_coord_exists A hA3 hhalf
  have hD6 : (D₁ ∪ D₂).card = 6 := by
    rw [Finset.card_union_of_disjoint hdisj, hD1c, hD2c]
  have hD1 : D₁ ⊆ D₁ ∪ D₂ := Finset.subset_union_left
  have hAD : A ∩ (D₁ ∪ D₂) = D₁ := by
    ext x
    constructor
    · intro hx
      rcases Finset.mem_inter.mp hx with ⟨hxA, hxU⟩
      rcases Finset.mem_union.mp hxU with hx1 | hx2
      · exact hx1
      · exact absurd hxA (Finset.mem_compl.mp (hD2Ac hx2))
    · intro hx
      exact Finset.mem_inter.mpr ⟨hD1A hx, Finset.mem_union_left _ hx⟩
  have htraceSub : ∀ t : ℕ, traceFiber n k t A a (D₁ ∪ D₂) ⊆ escLayer n k A a :=
    fun t B hB => (Finset.mem_filter.mp hB).1
  rcases lt_or_ge k 3 with hklt | hkge
  · -- k = 2
    have hk2 : k = 2 := by omega
    subst hk2
    have hz : sixZetaLower n 2 = 3 := by simp [sixZetaLower]
    rw [hz]
    have hb := stepC_fiber_lower (D := D₁ ∪ D₂) (D₁ := D₁) A a 3 hD1 hAD hD6 hD1c
      (by omega) (fun c => sixLocal_two c a)
    have hC : Nat.choose (n - 6) (2 - 2) = 1 := by norm_num
    rw [hC, Nat.mul_one] at hb
    exact le_trans hb (Finset.card_le_card (htraceSub 2))
  · rcases lt_or_ge k 4 with hklt4 | hkge4
    · -- k = 3
      have hk3 : k = 3 := by omega
      subst hk3
      have hz : sixZetaLower n 3 = 3 * Nat.choose (n - 6) (3 - 2) + 2 * Nat.choose (n - 6) (3 - 3) := by
        simp [sixZetaLower]
      rw [hz]
      have hb2 := stepC_fiber_lower (D := D₁ ∪ D₂) (D₁ := D₁) A a 3 hD1 hAD hD6 hD1c
        (by omega) (fun c => sixLocal_two c a)
      have hb3 := stepC_fiber_lower (D := D₁ ∪ D₂) (D₁ := D₁) A a 2 hD1 hAD hD6 hD1c
        (by omega) (fun c => sixLocal_three c a)
      have hdisj23 : Disjoint (traceFiber n 3 2 A a (D₁ ∪ D₂)) (traceFiber n 3 3 A a (D₁ ∪ D₂)) := by
        rw [Finset.disjoint_left]
        intro B h1 h2
        have e1 : (B ∩ (D₁ ∪ D₂)).card = 2 := (Finset.mem_filter.mp h1).2
        have e2 : (B ∩ (D₁ ∪ D₂)).card = 3 := (Finset.mem_filter.mp h2).2
        omega
      have hcardU : (traceFiber n 3 2 A a (D₁ ∪ D₂) ∪ traceFiber n 3 3 A a (D₁ ∪ D₂)).card
          = (traceFiber n 3 2 A a (D₁ ∪ D₂)).card + (traceFiber n 3 3 A a (D₁ ∪ D₂)).card :=
        Finset.card_union_of_disjoint hdisj23
      have hsubU : traceFiber n 3 2 A a (D₁ ∪ D₂) ∪ traceFiber n 3 3 A a (D₁ ∪ D₂)
          ⊆ escLayer n 3 A a := by
        intro B hB
        rcases Finset.mem_union.mp hB with h | h
        · exact htraceSub 2 h
        · exact htraceSub 3 h
      calc 3 * Nat.choose (n - 6) (3 - 2) + 2 * Nat.choose (n - 6) (3 - 3)
          ≤ (traceFiber n 3 2 A a (D₁ ∪ D₂)).card + (traceFiber n 3 3 A a (D₁ ∪ D₂)).card :=
            Nat.add_le_add hb2 hb3
        _ = _ := hcardU.symm
        _ ≤ (escLayer n 3 A a).card := Finset.card_le_card hsubU
    · -- 4 ≤ k
      have h3k : 3 ≤ k := by omega
      have h4k : 4 ≤ k := hkge4
      have hz : sixZetaLower n k = 3 * Nat.choose (n - 6) (k - 2)
          + 2 * Nat.choose (n - 6) (k - 3) + 3 * Nat.choose (n - 6) (k - 4) := by
        simp only [sixZetaLower]
        rw [ite_eq_left h3k, ite_eq_left h4k]
      rw [hz]
      have hb2 := stepC_fiber_lower (D := D₁ ∪ D₂) (D₁ := D₁) A a 3 hD1 hAD hD6 hD1c
        (by omega) (fun c => sixLocal_two c a)
      have hb3 := stepC_fiber_lower (D := D₁ ∪ D₂) (D₁ := D₁) A a 2 hD1 hAD hD6 hD1c
        (by omega) (fun c => sixLocal_three c a)
      have hb4 := stepC_fiber_lower (D := D₁ ∪ D₂) (D₁ := D₁) A a 3 hD1 hAD hD6 hD1c
        (by omega) (fun c => sixLocal_four c a)
      have hd23 : Disjoint (traceFiber n k 2 A a (D₁ ∪ D₂)) (traceFiber n k 3 A a (D₁ ∪ D₂)) := by
        rw [Finset.disjoint_left]
        intro B h1 h2
        have e1 : (B ∩ (D₁ ∪ D₂)).card = 2 := (Finset.mem_filter.mp h1).2
        have e2 : (B ∩ (D₁ ∪ D₂)).card = 3 := (Finset.mem_filter.mp h2).2
        omega
      have hd24 : Disjoint (traceFiber n k 2 A a (D₁ ∪ D₂)) (traceFiber n k 4 A a (D₁ ∪ D₂)) := by
        rw [Finset.disjoint_left]
        intro B h1 h2
        have e1 : (B ∩ (D₁ ∪ D₂)).card = 2 := (Finset.mem_filter.mp h1).2
        have e2 : (B ∩ (D₁ ∪ D₂)).card = 4 := (Finset.mem_filter.mp h2).2
        omega
      have hd34 : Disjoint (traceFiber n k 3 A a (D₁ ∪ D₂)) (traceFiber n k 4 A a (D₁ ∪ D₂)) := by
        rw [Finset.disjoint_left]
        intro B h1 h2
        have e1 : (B ∩ (D₁ ∪ D₂)).card = 3 := (Finset.mem_filter.mp h1).2
        have e2 : (B ∩ (D₁ ∪ D₂)).card = 4 := (Finset.mem_filter.mp h2).2
        omega
      have hdU : Disjoint (traceFiber n k 2 A a (D₁ ∪ D₂) ∪ traceFiber n k 3 A a (D₁ ∪ D₂))
          (traceFiber n k 4 A a (D₁ ∪ D₂)) := by
        rw [Finset.disjoint_left]
        intro B hB h4
        rcases Finset.mem_union.mp hB with h | h
        · exact Finset.disjoint_left.mp hd24 h h4
        · exact Finset.disjoint_left.mp hd34 h h4
      have hcardU : ((traceFiber n k 2 A a (D₁ ∪ D₂) ∪ traceFiber n k 3 A a (D₁ ∪ D₂))
            ∪ traceFiber n k 4 A a (D₁ ∪ D₂)).card
          = (traceFiber n k 2 A a (D₁ ∪ D₂)).card
            + (traceFiber n k 3 A a (D₁ ∪ D₂)).card
            + (traceFiber n k 4 A a (D₁ ∪ D₂)).card := by
        rw [Finset.card_union_of_disjoint hdU, Finset.card_union_of_disjoint hd23,
          Nat.add_assoc]
      have hsubU : (traceFiber n k 2 A a (D₁ ∪ D₂) ∪ traceFiber n k 3 A a (D₁ ∪ D₂))
            ∪ traceFiber n k 4 A a (D₁ ∪ D₂) ⊆ escLayer n k A a := by
        intro B hB
        rcases Finset.mem_union.mp hB with h | h
        · rcases Finset.mem_union.mp h with h' | h'
          · exact htraceSub 2 h'
          · exact htraceSub 3 h'
        · exact htraceSub 4 h
      calc 3 * Nat.choose (n - 6) (k - 2) + 2 * Nat.choose (n - 6) (k - 3)
              + 3 * Nat.choose (n - 6) (k - 4)
          ≤ (traceFiber n k 2 A a (D₁ ∪ D₂)).card
              + (traceFiber n k 3 A a (D₁ ∪ D₂)).card
              + (traceFiber n k 4 A a (D₁ ∪ D₂)).card := Nat.add_le_add (Nat.add_le_add hb2 hb3) hb4
        _ = _ := hcardU.symm
        _ ≤ (escLayer n k A a).card := Finset.card_le_card hsubU


private def sixG (k t : ℝ) : ℝ :=
  16 * k ^ 6 - 60 * k ^ 5 - 80 * k ^ 4 +
  540 * k ^ 3 - 656 * k ^ 2 + 240 * k +
  (120 * k ^ 5 - 660 * k ^ 4 + 1160 * k ^ 3 -
    720 * k ^ 2 + 112 * k) * t +
  (230 * k ^ 4 - 1095 * k ^ 3 + 1760 * k ^ 2 -
    1125 * k + 220) * t ^ 2 +
  (195 * k ^ 3 - 690 * k ^ 2 + 800 * k - 315) * t ^ 3 +
  (80 * k ^ 2 - 180 * k + 110) * t ^ 4 +
  (13 * k - 15) * t ^ 5

private theorem sixG_shift (q t : ℝ) :
    sixG (q + 3) t =
      16 * q ^ 6 + 228 * q ^ 5 + 1180 * q ^ 4 + 2820 * q ^ 3 +
      3124 * q ^ 2 + 1272 * q +
      (120 * q ^ 5 + 1140 * q ^ 4 + 4040 * q ^ 3 +
        6480 * q ^ 2 + 4432 * q + 876) * t +
      (230 * q ^ 4 + 1665 * q ^ 3 + 4325 * q ^ 2 +
        4710 * q + 1750) * t ^ 2 +
      (195 * q ^ 3 + 1065 * q ^ 2 + 1925 * q + 1140) * t ^ 3 +
      (80 * q ^ 2 + 300 * q + 290) * t ^ 4 +
      (13 * q + 24) * t ^ 5 := by
  simp [sixG]
  ring

private theorem sixG_nonneg (k t : ℝ) (hk : 3 ≤ k) (ht : 0 ≤ t) : 0 ≤ sixG k t := by
  obtain ⟨q, rfl⟩ : ∃ q, k = q + 3 := ⟨k - 3, by ring⟩
  have hq : 0 ≤ q := by linarith
  rw [sixG_shift]
  positivity

private theorem sixG_two_pos (t : ℝ) (ht : 2 ≤ t) : 0 < sixG 2 t := by
  let s := t - 2
  have hs : 0 ≤ s := by dsimp [s]; linarith
  have hts : t = s + 2 := by dsimp [s]; ring
  rw [hts]
  have h : sixG 2 (s + 2) =
      11 * s ^ 5 + 180 * s ^ 4 + 1085 * s ^ 3 + 3000 * s ^ 2 + 3764 * s + 1680 := by
    simp [sixG]
    ring
  rw [h]
  positivity

private theorem factorial_six_mul (n : ℕ) (hn : 6 ≤ n) :
    (n - 6).factorial * (n * (n - 1) * (n - 2) * (n - 3) * (n - 4) * (n - 5)) = n.factorial := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
  simp only [Nat.add_sub_cancel]
  simp [Nat.factorial]
  ring

private theorem factorial_two_mul (m : ℕ) (hm : 2 ≤ m) :
    (m - 2).factorial * (m * (m - 1)) = m.factorial := by
  obtain ⟨b, rfl⟩ : ∃ b, m = b + 2 := ⟨m - 2, by omega⟩
  simp only [Nat.add_sub_cancel]
  simp [Nat.factorial]
  ring

private theorem factorial_three_mul (m : ℕ) (hm : 3 ≤ m) :
    (m - 3).factorial * (m * (m - 1) * (m - 2)) = m.factorial := by
  obtain ⟨b, rfl⟩ : ∃ b, m = b + 3 := ⟨m - 3, by omega⟩
  simp only [Nat.add_sub_cancel]
  simp [Nat.factorial]
  ring

private theorem factorial_four_mul (m : ℕ) (hm : 4 ≤ m) :
    (m - 4).factorial * (m * (m - 1) * (m - 2) * (m - 3)) = m.factorial := by
  obtain ⟨b, rfl⟩ : ∃ b, m = b + 4 := ⟨m - 4, by omega⟩
  simp only [Nat.add_sub_cancel]
  simp [Nat.factorial]
  ring

private theorem cast_prod_six (n : ℕ) (hn : 6 ≤ n) :
    ((n * (n - 1) * (n - 2) * (n - 3) * (n - 4) * (n - 5) : ℕ) : ℝ)
      = (n:ℝ) * ((n:ℝ) - 1) * ((n:ℝ) - 2) * ((n:ℝ) - 3) * ((n:ℝ) - 4) * ((n:ℝ) - 5) := by
  have e1 : ((n - 1 : ℕ) : ℝ) = (n:ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : (1:ℕ) ≤ n), Nat.cast_one]
  have e2 : ((n - 2 : ℕ) : ℝ) = (n:ℝ) - 2 := by
    rw [Nat.cast_sub (by omega : (2:ℕ) ≤ n)]
    norm_num
  have e3 : ((n - 3 : ℕ) : ℝ) = (n:ℝ) - 3 := by
    rw [Nat.cast_sub (by omega : (3:ℕ) ≤ n)]
    norm_num
  have e4 : ((n - 4 : ℕ) : ℝ) = (n:ℝ) - 4 := by
    rw [Nat.cast_sub (by omega : (4:ℕ) ≤ n)]
    norm_num
  have e5 : ((n - 5 : ℕ) : ℝ) = (n:ℝ) - 5 := by
    rw [Nat.cast_sub (by omega : (5:ℕ) ≤ n)]
    norm_num
  simp only [Nat.cast_mul, e1, e2, e3, e4, e5]

private theorem cast_prod_k2 (k : ℕ) (hk : 2 ≤ k) :
    ((k * (k - 1) : ℕ) : ℝ) = (k:ℝ) * ((k:ℝ) - 1) := by
  have e1 : ((k - 1 : ℕ) : ℝ) = (k:ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : (1:ℕ) ≤ k), Nat.cast_one]
  simp only [Nat.cast_mul, e1]

private theorem cast_prod_k3 (k : ℕ) (hk : 3 ≤ k) :
    ((k * (k - 1) * (k - 2) : ℕ) : ℝ) = (k:ℝ) * ((k:ℝ) - 1) * ((k:ℝ) - 2) := by
  have e1 : ((k - 1 : ℕ) : ℝ) = (k:ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : (1:ℕ) ≤ k), Nat.cast_one]
  have e2 : ((k - 2 : ℕ) : ℝ) = (k:ℝ) - 2 := by
    rw [Nat.cast_sub (by omega : (2:ℕ) ≤ k), Nat.cast_ofNat]
  simp only [Nat.cast_mul, e1, e2]

private theorem cast_prod_k4 (k : ℕ) (hk : 4 ≤ k) :
    ((k * (k - 1) * (k - 2) * (k - 3) : ℕ) : ℝ) = (k:ℝ) * ((k:ℝ) - 1) * ((k:ℝ) - 2) * ((k:ℝ) - 3) := by
  have e1 : ((k - 1 : ℕ) : ℝ) = (k:ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : (1:ℕ) ≤ k), Nat.cast_one]
  have e2 : ((k - 2 : ℕ) : ℝ) = (k:ℝ) - 2 := by
    rw [Nat.cast_sub (by omega : (2:ℕ) ≤ k), Nat.cast_ofNat]
  have e3 : ((k - 3 : ℕ) : ℝ) = (k:ℝ) - 3 := by
    rw [Nat.cast_sub (by omega : (3:ℕ) ≤ k), Nat.cast_ofNat]
  simp only [Nat.cast_mul, e1, e2, e3]

private theorem cast_prod_nk4 (n k : ℕ) (hkn : k ≤ n) (h : 4 ≤ n - k) :
    (((n - k) * (n - k - 1) * (n - k - 2) * (n - k - 3) : ℕ) : ℝ)
      = ((n:ℝ) - (k:ℝ)) * (((n:ℝ) - (k:ℝ)) - 1) * (((n:ℝ) - (k:ℝ)) - 2) * (((n:ℝ) - (k:ℝ)) - 3) := by
  have e0 : ((n - k : ℕ) : ℝ) = (n:ℝ) - (k:ℝ) := by rw [Nat.cast_sub hkn]
  have e1 : ((n - k - 1 : ℕ) : ℝ) = (n:ℝ) - (k:ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : (1:ℕ) ≤ n - k), e0, Nat.cast_one]
  have e2 : ((n - k - 2 : ℕ) : ℝ) = (n:ℝ) - (k:ℝ) - 2 := by
    rw [Nat.cast_sub (by omega : (2:ℕ) ≤ n - k), e0]
    norm_num
  have e3 : ((n - k - 3 : ℕ) : ℝ) = (n:ℝ) - (k:ℝ) - 3 := by
    rw [Nat.cast_sub (by omega : (3:ℕ) ≤ n - k), e0]
    norm_num
  simp only [Nat.cast_mul, e0, e1, e2, e3]

private theorem cast_prod_nk3 (n k : ℕ) (hkn : k ≤ n) (h : 3 ≤ n - k) :
    (((n - k) * (n - k - 1) * (n - k - 2) : ℕ) : ℝ)
      = ((n:ℝ) - (k:ℝ)) * (((n:ℝ) - (k:ℝ)) - 1) * (((n:ℝ) - (k:ℝ)) - 2) := by
  have e0 : ((n - k : ℕ) : ℝ) = (n:ℝ) - (k:ℝ) := by rw [Nat.cast_sub hkn]
  have e1 : ((n - k - 1 : ℕ) : ℝ) = (n:ℝ) - (k:ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : (1:ℕ) ≤ n - k), e0, Nat.cast_one]
  have e2 : ((n - k - 2 : ℕ) : ℝ) = (n:ℝ) - (k:ℝ) - 2 := by
    rw [Nat.cast_sub (by omega : (2:ℕ) ≤ n - k), e0]
    norm_num
  simp only [Nat.cast_mul, e0, e1, e2]

private theorem cast_prod_nk2 (n k : ℕ) (hkn : k ≤ n) (h : 2 ≤ n - k) :
    (((n - k) * (n - k - 1) : ℕ) : ℝ)
      = ((n:ℝ) - (k:ℝ)) * (((n:ℝ) - (k:ℝ)) - 1) := by
  have e0 : ((n - k : ℕ) : ℝ) = (n:ℝ) - (k:ℝ) := by rw [Nat.cast_sub hkn]
  have e1 : ((n - k - 1 : ℕ) : ℝ) = (n:ℝ) - (k:ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : (1:ℕ) ≤ n - k), e0, Nat.cast_one]
  simp only [Nat.cast_mul, e0, e1]

private theorem factorial_six_mul_real (n : ℕ) (hn : 6 ≤ n) :
    ((n - 6).factorial : ℝ) * ((n:ℝ) * ((n:ℝ) - 1) * ((n:ℝ) - 2) * ((n:ℝ) - 3) * ((n:ℝ) - 4) * ((n:ℝ) - 5))
      = (n.factorial : ℝ) := by
  rw [← cast_prod_six n hn]
  exact_mod_cast factorial_six_mul n hn

private theorem factorial_two_mul_real (m : ℕ) (hm : 2 ≤ m) :
    ((m - 2).factorial : ℝ) * ((m:ℝ) * ((m:ℝ) - 1)) = (m.factorial : ℝ) := by
  rw [← cast_prod_k2 m hm]
  exact_mod_cast factorial_two_mul m hm

private theorem factorial_three_mul_real (m : ℕ) (hm : 3 ≤ m) :
    ((m - 3).factorial : ℝ) * ((m:ℝ) * ((m:ℝ) - 1) * ((m:ℝ) - 2)) = (m.factorial : ℝ) := by
  rw [← cast_prod_k3 m hm]
  exact_mod_cast factorial_three_mul m hm

private theorem factorial_four_mul_real (m : ℕ) (hm : 4 ≤ m) :
    ((m - 4).factorial : ℝ) * ((m:ℝ) * ((m:ℝ) - 1) * ((m:ℝ) - 2) * ((m:ℝ) - 3)) = (m.factorial : ℝ) := by
  rw [← cast_prod_k4 m hm]
  exact_mod_cast factorial_four_mul m hm

private def sixD (n : ℕ) : ℝ :=
  (n:ℝ) * ((n:ℝ) - 1) * ((n:ℝ) - 2) * ((n:ℝ) - 3) * ((n:ℝ) - 4) * ((n:ℝ) - 5)

private def sixP2R (n k : ℕ) : ℝ :=
  (k:ℝ) * ((k:ℝ) - 1) *
    (((n:ℝ) - (k:ℝ)) * (((n:ℝ) - (k:ℝ)) - 1) * (((n:ℝ) - (k:ℝ)) - 2) * (((n:ℝ) - (k:ℝ)) - 3))

private def sixP3R (n k : ℕ) : ℝ :=
  (k:ℝ) * ((k:ℝ) - 1) * ((k:ℝ) - 2) *
    (((n:ℝ) - (k:ℝ)) * (((n:ℝ) - (k:ℝ)) - 1) * (((n:ℝ) - (k:ℝ)) - 2))

private def sixP4R (n k : ℕ) : ℝ :=
  (k:ℝ) * ((k:ℝ) - 1) * ((k:ℝ) - 2) * ((k:ℝ) - 3) *
    (((n:ℝ) - (k:ℝ)) * (((n:ℝ) - (k:ℝ)) - 1))

private theorem sixD_pos (n : ℕ) (hn : 6 ≤ n) : 0 < sixD n := by
  have hnR : (6:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have h1 : (0:ℝ) < (n:ℝ) := by linarith
  have h2 : (0:ℝ) < (n:ℝ) - 1 := by linarith
  have h3 : (0:ℝ) < (n:ℝ) - 2 := by linarith
  have h4 : (0:ℝ) < (n:ℝ) - 3 := by linarith
  have h5 : (0:ℝ) < (n:ℝ) - 4 := by linarith
  have h6 : (0:ℝ) < (n:ℝ) - 5 := by linarith
  simp only [sixD]
  exact mul_pos (mul_pos (mul_pos (mul_pos (mul_pos h1 h2) h3) h4) h5) h6

private theorem choose_ratio_two (n k : ℕ) (hn : 6 ≤ n) (hk : 2 ≤ k) (hkn : k + 4 ≤ n) :
    (Nat.choose (n - 6) (k - 2) : ℝ) * sixD n = (Nat.choose n k : ℝ) * sixP2R n k := by
  have hkn' : k ≤ n := by omega
  have hk2 : k - 2 ≤ n - 6 := by omega
  have hnk4 : 4 ≤ n - k := by omega
  have hd : n - 6 - (k - 2) = n - k - 4 := by omega
  have h1 : (Nat.choose n k : ℝ) = (n.factorial : ℝ) / ((k.factorial : ℝ) * ((n - k).factorial : ℝ)) :=
    Nat.cast_choose ℝ hkn'
  have h2 : (Nat.choose (n - 6) (k - 2) : ℝ) =
      ((n - 6).factorial : ℝ) / (((k - 2).factorial : ℝ) * ((n - k - 4).factorial : ℝ)) := by
    have hh := Nat.cast_choose ℝ hk2
    rwa [hd] at hh
  have hfN := factorial_six_mul_real n hn
  have hfK := factorial_two_mul_real k hk
  have hfNK := factorial_four_mul_real (n - k) hnk4
  rw [Nat.cast_sub hkn'] at hfNK
  have hfNne : ((n - 6).factorial : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_pos (n - 6)).ne'
  have hfKne : ((k - 2).factorial : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_pos (k - 2)).ne'
  have hfNKne : ((n - k - 4).factorial : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_pos (n - k - 4)).ne'
  have hk1 : (0:ℝ) < (k:ℝ) := by
    have : (2:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
    linarith
  have hk2' : (0:ℝ) < (k:ℝ) - 1 := by
    have : (2:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
    linarith
  have hnk : (0:ℝ) < (n:ℝ) - (k:ℝ) := by
    have : (k:ℝ) < (n:ℝ) := by exact_mod_cast (by omega : k < n)
    linarith
  have hnk1 : (0:ℝ) < (n:ℝ) - (k:ℝ) - 1 := by
    have : ((n - k : ℕ) : ℝ) = (n:ℝ) - (k:ℝ) := by rw [Nat.cast_sub hkn']
    have h4 : (4:ℝ) ≤ ((n - k : ℕ) : ℝ) := by exact_mod_cast hnk4
    linarith
  have hnk2 : (0:ℝ) < (n:ℝ) - (k:ℝ) - 2 := by
    have : ((n - k : ℕ) : ℝ) = (n:ℝ) - (k:ℝ) := by rw [Nat.cast_sub hkn']
    have h4 : (4:ℝ) ≤ ((n - k : ℕ) : ℝ) := by exact_mod_cast hnk4
    linarith
  have hnk3 : (0:ℝ) < (n:ℝ) - (k:ℝ) - 3 := by
    have : ((n - k : ℕ) : ℝ) = (n:ℝ) - (k:ℝ) := by rw [Nat.cast_sub hkn']
    have h4 : (4:ℝ) ≤ ((n - k : ℕ) : ℝ) := by exact_mod_cast hnk4
    linarith
  have hDpos := sixD_pos n hn
  simp only [sixP2R, sixD]
  rw [h1, h2, ← hfN, ← hfK, ← hfNK]
  field_simp

private theorem poly_identity (n k : ℕ) (hk : 4 ≤ k) (hhalf : k ≤ n - k) :
    5 * (n:ℝ)^2 * (3 * sixP2R n k + 2 * sixP3R n k + 3 * sixP4R n k) - 2 * (k:ℝ)^2 * sixD n
      = (n:ℝ) * (k:ℝ) * sixG (k:ℝ) ((n:ℝ) - 2 * (k:ℝ)) := by
  simp only [sixP2R, sixP3R, sixP4R, sixD, sixG]
  ring

private theorem stepD_poly_k3 (n : ℕ) (hkn : 3 + 2 ≤ n) (hhalf : 3 ≤ n - 3) :
    2 * (min 3 (n - 3))^2 * Nat.choose n 3 ≤ 5 * n^2 * sixZetaLower n 3 := by
  have hn : 6 ≤ n := by omega
  have hmin : min 3 (n - 3) = 3 := Nat.min_eq_left hhalf
  rw [hmin]
  have hdef : sixZetaLower n 3 = 3 * (n - 6) + 2 := by
    simp only [sixZetaLower]
    norm_num [Nat.choose_one_right]
  have hC : (Nat.choose n 3 : ℝ) = (n:ℝ) * ((n:ℝ) - 1) * ((n:ℝ) - 2) / 6 := by
    have h1 : (Nat.choose n 3 : ℝ) = (n.factorial : ℝ) / (((3:ℕ).factorial : ℝ) * ((n - 3).factorial : ℝ)) :=
      Nat.cast_choose ℝ (by omega : 3 ≤ n)
    have hf := factorial_three_mul_real n (by omega : 3 ≤ n)
    rw [h1, ← hf]
    norm_num
    field_simp
  have hpoly : 3 * ((n:ℝ) * ((n:ℝ) - 1) * ((n:ℝ) - 2)) ≤ 5 * (n:ℝ)^2 * (3 * (n:ℝ) - 16) := by
    have hnR : (6:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    have hp1 : (0:ℝ) ≤ (n:ℝ) := by linarith
    have hp2 : (0:ℝ) ≤ (n:ℝ) - 6 := by linarith
    have hp3 : (0:ℝ) ≤ 12 * (n:ℝ) + 1 := by positivity
    have hprod : (0:ℝ) ≤ (n:ℝ) * ((n:ℝ) - 6) * (12 * (n:ℝ) + 1) :=
      mul_nonneg (mul_nonneg hp1 hp2) hp3
    nlinarith [hprod]
  have hmainR : 2 * (3:ℝ)^2 * (Nat.choose n 3 : ℝ) ≤ 5 * (n:ℝ)^2 * (sixZetaLower n 3 : ℝ) := by
    have hc6 : ((n - 6 : ℕ) : ℝ) = (n:ℝ) - 6 := by
      rw [Nat.cast_sub (by omega : 6 ≤ n)]
      norm_num
    calc 2 * (3:ℝ)^2 * (Nat.choose n 3 : ℝ) = 3 * ((n:ℝ) * ((n:ℝ) - 1) * ((n:ℝ) - 2)) := by
          rw [hC]; ring
      _ ≤ 5 * (n:ℝ)^2 * (3 * (n:ℝ) - 16) := hpoly
      _ = 5 * (n:ℝ)^2 * (sixZetaLower n 3 : ℝ) := by
          rw [hdef]
          push_cast
          rw [hc6]
          ring
  exact_mod_cast hmainR

private theorem stepD_poly_k2 (n : ℕ) (hkn : 2 + 2 ≤ n) :
    2 * (min 2 (n - 2))^2 * Nat.choose n 2 ≤ 5 * n^2 * sixZetaLower n 2 := by
  have hmin : min 2 (n - 2) = 2 := Nat.min_eq_left (by omega)
  rw [hmin]
  have hdef : sixZetaLower n 2 = 3 := by
    simp only [sixZetaLower]
    norm_num
  have hC : (Nat.choose n 2 : ℝ) = (n:ℝ) * ((n:ℝ) - 1) / 2 := by
    have h1 : (Nat.choose n 2 : ℝ) = (n.factorial : ℝ) / (((2:ℕ).factorial : ℝ) * ((n - 2).factorial : ℝ)) :=
      Nat.cast_choose ℝ (by omega : 2 ≤ n)
    have hf := factorial_two_mul_real n (by omega : 2 ≤ n)
    rw [h1, ← hf]
    norm_num
    field_simp
  have hmainR : 2 * (2:ℝ)^2 * (Nat.choose n 2 : ℝ) ≤ 5 * (n:ℝ)^2 * (sixZetaLower n 2 : ℝ) := by
    have hn0 : (0:ℝ) ≤ (n:ℝ) := by positivity
    calc 2 * (2:ℝ)^2 * (Nat.choose n 2 : ℝ) = 4 * ((n:ℝ) * ((n:ℝ) - 1)) := by
          rw [hC]; ring
      _ ≤ 5 * (n:ℝ)^2 * 3 := by nlinarith [hn0]
      _ = 5 * (n:ℝ)^2 * (sixZetaLower n 2 : ℝ) := by
          rw [hdef]
          norm_num
  exact_mod_cast hmainR

private theorem choose_ratio_three (n k : ℕ) (hn : 6 ≤ n) (hk : 4 ≤ k) (hkn : k + 4 ≤ n) :
    (Nat.choose (n - 6) (k - 3) : ℝ) * sixD n = (Nat.choose n k : ℝ) * sixP3R n k := by
  have hkn' : k ≤ n := by omega
  have hnk3 : 3 ≤ n - k := by omega
  have habs_nat : Nat.choose (n - 6) (k - 2) * (k - 2) = Nat.choose (n - 6) (k - 3) * (n - k - 3) := by
    have h := Nat.choose_succ_right_eq (n - 6) (k - 3)
    rwa [show k - 3 + 1 = k - 2 by omega,
         show n - 6 - (k - 3) = n - k - 3 by omega] at h
  have hk2c : ((k - 2 : ℕ) : ℝ) = (k:ℝ) - 2 := by
    rw [Nat.cast_sub (by omega : (2:ℕ) ≤ k)]
    norm_num
  have hnk3c : ((n - k - 3 : ℕ) : ℝ) = (n:ℝ) - (k:ℝ) - 3 := by
    rw [Nat.cast_sub (by omega : (3:ℕ) ≤ n - k), Nat.cast_sub hkn']
    norm_num
  have habs : (Nat.choose (n - 6) (k - 2) : ℝ) * ((k:ℝ) - 2)
      = (Nat.choose (n - 6) (k - 3) : ℝ) * ((n:ℝ) - (k:ℝ) - 3) := by
    have h : ((Nat.choose (n - 6) (k - 2) * (k - 2) : ℕ) : ℝ)
        = ((Nat.choose (n - 6) (k - 3) * (n - k - 3) : ℕ) : ℝ) := by rw [habs_nat]
    push_cast at h
    rwa [hk2c, hnk3c] at h
  have hdpos : (0:ℝ) < (n:ℝ) - (k:ℝ) - 3 := by
    have h4 : (4:ℕ) ≤ n - k := by omega
    have h1 : ((n - k : ℕ) : ℝ) = (n:ℝ) - (k:ℝ) := by rw [Nat.cast_sub hkn']
    have h2 : (4:ℝ) ≤ ((n - k : ℕ) : ℝ) := by exact_mod_cast h4
    linarith
  have hP : sixP2R n k * ((k:ℝ) - 2) = sixP3R n k * ((n:ℝ) - (k:ℝ) - 3) := by
    simp only [sixP2R, sixP3R]
    ring
  have e2 := choose_ratio_two n k hn (by omega : 2 ≤ k) hkn
  have hC3 : (Nat.choose (n - 6) (k - 3) : ℝ)
      = (Nat.choose (n - 6) (k - 2) : ℝ) * ((k:ℝ) - 2) / ((n:ℝ) - (k:ℝ) - 3) := by
    rw [eq_div_iff (ne_of_gt hdpos)]
    exact habs.symm
  calc (Nat.choose (n - 6) (k - 3) : ℝ) * sixD n
      = ((Nat.choose (n - 6) (k - 2) : ℝ) * ((k:ℝ) - 2) / ((n:ℝ) - (k:ℝ) - 3)) * sixD n := by rw [hC3]
    _ = ((Nat.choose (n - 6) (k - 2) : ℝ) * sixD n) * ((k:ℝ) - 2) / ((n:ℝ) - (k:ℝ) - 3) := by ring
    _ = ((Nat.choose n k : ℝ) * sixP2R n k) * ((k:ℝ) - 2) / ((n:ℝ) - (k:ℝ) - 3) := by rw [e2]
    _ = (Nat.choose n k : ℝ) * (sixP2R n k * ((k:ℝ) - 2)) / ((n:ℝ) - (k:ℝ) - 3) := by ring
    _ = (Nat.choose n k : ℝ) * (sixP3R n k * ((n:ℝ) - (k:ℝ) - 3)) / ((n:ℝ) - (k:ℝ) - 3) := by rw [hP]
    _ = (Nat.choose n k : ℝ) * sixP3R n k := by
        field_simp

private theorem choose_ratio_four (n k : ℕ) (hn : 6 ≤ n) (hk : 4 ≤ k) (hkn : k + 4 ≤ n) :
    (Nat.choose (n - 6) (k - 4) : ℝ) * sixD n = (Nat.choose n k : ℝ) * sixP4R n k := by
  have hkn' : k ≤ n := by omega
  have hnk2 : 2 ≤ n - k := by omega
  have habs_nat : Nat.choose (n - 6) (k - 3) * (k - 3) = Nat.choose (n - 6) (k - 4) * (n - k - 2) := by
    have h := Nat.choose_succ_right_eq (n - 6) (k - 4)
    rwa [show k - 4 + 1 = k - 3 by omega,
         show n - 6 - (k - 4) = n - k - 2 by omega] at h
  have hk3c : ((k - 3 : ℕ) : ℝ) = (k:ℝ) - 3 := by
    rw [Nat.cast_sub (by omega : (3:ℕ) ≤ k)]
    norm_num
  have hnk2c : ((n - k - 2 : ℕ) : ℝ) = (n:ℝ) - (k:ℝ) - 2 := by
    rw [Nat.cast_sub (by omega : (2:ℕ) ≤ n - k), Nat.cast_sub hkn']
    norm_num
  have habs : (Nat.choose (n - 6) (k - 3) : ℝ) * ((k:ℝ) - 3)
      = (Nat.choose (n - 6) (k - 4) : ℝ) * ((n:ℝ) - (k:ℝ) - 2) := by
    have h : ((Nat.choose (n - 6) (k - 3) * (k - 3) : ℕ) : ℝ)
        = ((Nat.choose (n - 6) (k - 4) * (n - k - 2) : ℕ) : ℝ) := by rw [habs_nat]
    push_cast at h
    rwa [hk3c, hnk2c] at h
  have hdpos : (0:ℝ) < (n:ℝ) - (k:ℝ) - 2 := by
    have h4 : (4:ℕ) ≤ n - k := by omega
    have h1 : ((n - k : ℕ) : ℝ) = (n:ℝ) - (k:ℝ) := by rw [Nat.cast_sub hkn']
    have h2 : (4:ℝ) ≤ ((n - k : ℕ) : ℝ) := by exact_mod_cast h4
    linarith
  have hP : sixP3R n k * ((k:ℝ) - 3) = sixP4R n k * ((n:ℝ) - (k:ℝ) - 2) := by
    simp only [sixP3R, sixP4R]
    ring
  have e3 := choose_ratio_three n k hn hk hkn
  have hC4 : (Nat.choose (n - 6) (k - 4) : ℝ)
      = (Nat.choose (n - 6) (k - 3) : ℝ) * ((k:ℝ) - 3) / ((n:ℝ) - (k:ℝ) - 2) := by
    rw [eq_div_iff (ne_of_gt hdpos)]
    exact habs.symm
  calc (Nat.choose (n - 6) (k - 4) : ℝ) * sixD n
      = ((Nat.choose (n - 6) (k - 3) : ℝ) * ((k:ℝ) - 3) / ((n:ℝ) - (k:ℝ) - 2)) * sixD n := by rw [hC4]
    _ = ((Nat.choose (n - 6) (k - 3) : ℝ) * sixD n) * ((k:ℝ) - 3) / ((n:ℝ) - (k:ℝ) - 2) := by ring
    _ = ((Nat.choose n k : ℝ) * sixP3R n k) * ((k:ℝ) - 3) / ((n:ℝ) - (k:ℝ) - 2) := by rw [e3]
    _ = (Nat.choose n k : ℝ) * (sixP3R n k * ((k:ℝ) - 3)) / ((n:ℝ) - (k:ℝ) - 2) := by ring
    _ = (Nat.choose n k : ℝ) * (sixP4R n k * ((n:ℝ) - (k:ℝ) - 2)) / ((n:ℝ) - (k:ℝ) - 2) := by rw [hP]
    _ = (Nat.choose n k : ℝ) * sixP4R n k := by
        field_simp

private theorem zeta_ratio (n k : ℕ) (hn : 6 ≤ n) (hk : 4 ≤ k) (hhalf : k ≤ n - k) :
    (sixZetaLower n k : ℝ) * sixD n
      = (Nat.choose n k : ℝ) * (3 * sixP2R n k + 2 * sixP3R n k + 3 * sixP4R n k) := by
  have h3 : 3 ≤ k := by omega
  have hkn4 : k + 4 ≤ n := by omega
  have hdef : sixZetaLower n k
      = 3 * Nat.choose (n - 6) (k - 2) + 2 * Nat.choose (n - 6) (k - 3) + 3 * Nat.choose (n - 6) (k - 4) := by
    simp only [sixZetaLower, if_pos h3, if_pos hk]
  have e2 := choose_ratio_two n k hn (by omega : 2 ≤ k) hkn4
  have e3 := choose_ratio_three n k hn hk hkn4
  have e4 := choose_ratio_four n k hn hk hkn4
  rw [hdef]
  push_cast
  calc (3 * ↑(Nat.choose (n - 6) (k - 2)) + 2 * ↑(Nat.choose (n - 6) (k - 3))
        + 3 * ↑(Nat.choose (n - 6) (k - 4))) * sixD n
      = 3 * (↑(Nat.choose (n - 6) (k - 2)) * sixD n) + 2 * (↑(Nat.choose (n - 6) (k - 3)) * sixD n)
        + 3 * (↑(Nat.choose (n - 6) (k - 4)) * sixD n) := by ring
    _ = 3 * (↑(Nat.choose n k) * sixP2R n k) + 2 * (↑(Nat.choose n k) * sixP3R n k)
        + 3 * (↑(Nat.choose n k) * sixP4R n k) := by rw [e2, e3, e4]
    _ = ↑(Nat.choose n k) * (3 * sixP2R n k + 2 * sixP3R n k + 3 * sixP4R n k) := by ring

private theorem stepD_poly_k4 (n k : ℕ) (hk : 4 ≤ k) (hkn : k + 2 ≤ n) (hhalf : k ≤ n - k) :
    2 * (min k (n - k))^2 * Nat.choose n k ≤ 5 * n^2 * sixZetaLower n k := by
  have hn : 6 ≤ n := by omega
  have hmin : min k (n - k) = k := Nat.min_eq_left hhalf
  rw [hmin]
  have hz := zeta_ratio n k hn hk hhalf
  have hp := poly_identity n k hk hhalf
  have hDpos := sixD_pos n hn
  have hnR : (0:ℝ) < (n:ℝ) := by
    have : (6:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    linarith
  have hkR : (0:ℝ) < (k:ℝ) := by
    have : (4:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
    linarith
  have hG : 0 ≤ sixG (k:ℝ) ((n:ℝ) - 2 * (k:ℝ)) := by
    apply sixG_nonneg
    · have : (3:ℝ) ≤ (k:ℝ) := by exact_mod_cast (by omega : 3 ≤ k)
      linarith
    · have : (2:ℝ) * (k:ℝ) ≤ (n:ℝ) := by exact_mod_cast (by omega : 2 * k ≤ n)
      linarith
  have hCpos : (0:ℝ) < (Nat.choose n k : ℝ) := by
    have : 0 < Nat.choose n k := Nat.choose_pos (by omega : k ≤ n)
    exact_mod_cast this
  have hkey : 2 * (k:ℝ)^2 * sixD n
      ≤ 5 * (n:ℝ)^2 * (3 * sixP2R n k + 2 * sixP3R n k + 3 * sixP4R n k) := by
    have hnkG : 0 ≤ (n:ℝ) * (k:ℝ) * sixG (k:ℝ) ((n:ℝ) - 2 * (k:ℝ)) :=
      mul_nonneg (mul_nonneg hnR.le hkR.le) hG
    nlinarith [hp, hnkG]
  have h1 : 2 * (k:ℝ)^2 * (Nat.choose n k : ℝ) * sixD n
      ≤ 5 * (n:ℝ)^2 * (Nat.choose n k : ℝ) * (3 * sixP2R n k + 2 * sixP3R n k + 3 * sixP4R n k) := by
    have h := mul_le_mul_of_nonneg_right hkey hCpos.le
    calc 2 * (k:ℝ)^2 * (Nat.choose n k : ℝ) * sixD n
        = (2 * (k:ℝ)^2 * sixD n) * (Nat.choose n k : ℝ) := by ring
      _ ≤ (5 * (n:ℝ)^2 * (3 * sixP2R n k + 2 * sixP3R n k + 3 * sixP4R n k)) * (Nat.choose n k : ℝ) := h
      _ = 5 * (n:ℝ)^2 * (Nat.choose n k : ℝ) * (3 * sixP2R n k + 2 * sixP3R n k + 3 * sixP4R n k) := by ring
  have h2 : 2 * (k:ℝ)^2 * (Nat.choose n k : ℝ) * sixD n
      ≤ 5 * (n:ℝ)^2 * (sixZetaLower n k : ℝ) * sixD n := by
    have h1' : 2 * (k:ℝ)^2 * (Nat.choose n k : ℝ) * sixD n
        ≤ 5 * (n:ℝ)^2 * ((Nat.choose n k : ℝ) * (3 * sixP2R n k + 2 * sixP3R n k + 3 * sixP4R n k)) := by
      rw [show 5 * (n:ℝ)^2 * ((Nat.choose n k : ℝ) * (3 * sixP2R n k + 2 * sixP3R n k + 3 * sixP4R n k))
          = 5 * (n:ℝ)^2 * (Nat.choose n k : ℝ) * (3 * sixP2R n k + 2 * sixP3R n k + 3 * sixP4R n k) by ring]
      exact h1
    calc 2 * (k:ℝ)^2 * (Nat.choose n k : ℝ) * sixD n
        ≤ 5 * (n:ℝ)^2 * ((Nat.choose n k : ℝ) * (3 * sixP2R n k + 2 * sixP3R n k + 3 * sixP4R n k)) := h1'
      _ = 5 * (n:ℝ)^2 * ((sixZetaLower n k : ℝ) * sixD n) := by rw [← hz]
      _ = 5 * (n:ℝ)^2 * (sixZetaLower n k : ℝ) * sixD n := by ring
  exact_mod_cast (le_of_mul_le_mul_right h2 hDpos)

private lemma stepD_poly (n k : ℕ) (hk : 2 ≤ k) (hkn : k + 2 ≤ n) (hhalf : k ≤ n - k) :
    2 * (min k (n - k))^2 * Nat.choose n k ≤ 5 * n^2 * sixZetaLower n k := by
  rcases lt_or_ge k 3 with hlt | hge
  · interval_cases k
    exact stepD_poly_k2 n (by omega)
  rcases lt_or_ge k 4 with hlt | hge
  · interval_cases k
    exact stepD_poly_k3 n (by omega) (by omega)
  · exact stepD_poly_k4 n k hge (by omega) hhalf

private lemma escLayer_complA (n k : ℕ) (A : Finset (Fin n)) (a : ℤ) :
    escLayer n k A a = escLayer n k (Aᶜ) ((k : ℤ) - 1 - a) := by
  have hstep : ∀ B : Finset (Fin n), ((Aᶜ ∩ B).card : ℤ) = (B.card : ℤ) - ((A ∩ B).card : ℤ) := by
    intro B
    have e : Aᶜ ∩ B = B \ A := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_compl, Finset.mem_sdiff]
      tauto
    rw [e, Finset.card_sdiff]
    exact Nat.cast_sub (Finset.card_le_card Finset.inter_subset_right)
  ext B
  simp only [escLayer, Finset.mem_filter, Finset.mem_powersetCard]
  constructor
  · rintro ⟨⟨hBsub, hBk⟩, he1, he2⟩
    refine ⟨⟨hBsub, hBk⟩, ?_, ?_⟩
    · intro hcontra
      apply he2
      have h1 : ((Aᶜ ∩ B).card : ℤ) = (k : ℤ) - ((A ∩ B).card : ℤ) := by rw [hstep B, hBk]
      omega
    · intro hcontra
      apply he1
      have h1 : ((Aᶜ ∩ B).card : ℤ) = (k : ℤ) - ((A ∩ B).card : ℤ) := by rw [hstep B, hBk]
      omega
  · rintro ⟨⟨hBsub, hBk⟩, he1, he2⟩
    refine ⟨⟨hBsub, hBk⟩, ?_, ?_⟩
    · intro hcontra
      apply he1
      have h1 : ((Aᶜ ∩ B).card : ℤ) = (k : ℤ) - ((A ∩ B).card : ℤ) := by rw [hstep B, hBk]
      omega
    · intro hcontra
      apply he2
      have h1 : ((Aᶜ ∩ B).card : ℤ) = (k : ℤ) - ((A ∩ B).card : ℤ) := by rw [hstep B, hBk]
      omega

private lemma escLayer_complB (n k : ℕ) (A : Finset (Fin n)) (a : ℤ) (hk : k ≤ n) :
    (escLayer n k A a).card = (escLayer n (n - k) A ((A.card : ℤ) - 1 - a)).card := by
  have hinner : ∀ B : Finset (Fin n), A ∩ ((Finset.univ : Finset (Fin n)) \ B) = A \ B := by
    intro B
    ext x
    simp [Finset.mem_inter, Finset.mem_sdiff]
  have hinter : ∀ B : Finset (Fin n), ((A ∩ ((Finset.univ : Finset (Fin n)) \ B)).card : ℤ)
      = (A.card : ℤ) - ((A ∩ B).card : ℤ) := by
    intro B
    have hcomm : (B ∩ A).card = (A ∩ B).card := by rw [Finset.inter_comm]
    rw [hinner, Finset.card_sdiff, hcomm]
    exact Nat.cast_sub (Finset.card_le_card Finset.inter_subset_left)
  refine Finset.card_bij (fun B _ => (Finset.univ : Finset (Fin n)) \ B) ?_ ?_ ?_
  · intro B hB
    simp only [escLayer, Finset.mem_filter, Finset.mem_powersetCard] at hB
    obtain ⟨⟨hBsub, hBk⟩, he1, he2⟩ := hB
    have hcard : ((Finset.univ : Finset (Fin n)) \ B).card = n - k := by
      rw [Finset.card_sdiff_of_subset hBsub, Finset.card_univ, Fintype.card_fin, hBk]
    refine Finset.mem_filter.mpr
      ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hcard⟩, ?_, ?_⟩
    · intro hcontra
      apply he1
      have h1 : ((A ∩ ((Finset.univ : Finset (Fin n)) \ B)).card : ℤ)
          = (A.card : ℤ) - ((A ∩ B).card : ℤ) := hinter B
      omega
    · intro hcontra
      apply he2
      have h1 : ((A ∩ ((Finset.univ : Finset (Fin n)) \ B)).card : ℤ)
          = (A.card : ℤ) - ((A ∩ B).card : ℤ) := hinter B
      omega
  · intro B1 _ B2 _ hEq
    have h1 : B1 = (Finset.univ : Finset (Fin n)) \ ((Finset.univ : Finset (Fin n)) \ B1) :=
      (Finset.sdiff_sdiff_eq_self (Finset.subset_univ B1)).symm
    have h2 : B2 = (Finset.univ : Finset (Fin n)) \ ((Finset.univ : Finset (Fin n)) \ B2) :=
      (Finset.sdiff_sdiff_eq_self (Finset.subset_univ B2)).symm
    rw [h1, h2, hEq]
  · intro C hC
    simp only [escLayer, Finset.mem_filter, Finset.mem_powersetCard] at hC
    obtain ⟨⟨hCsub, hCk⟩, he1, he2⟩ := hC
    have hBcard : ((Finset.univ : Finset (Fin n)) \ C).card = k := by
      rw [Finset.card_sdiff_of_subset hCsub, Finset.card_univ, Fintype.card_fin]
      omega
    refine ⟨(Finset.univ : Finset (Fin n)) \ C, ?_, ?_⟩
    · refine Finset.mem_filter.mpr
        ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hBcard⟩, ?_, ?_⟩
      · intro hcontra
        apply he2
        have h1 : ((A ∩ ((Finset.univ : Finset (Fin n)) \ C)).card : ℤ)
            = (A.card : ℤ) - ((A ∩ C).card : ℤ) := hinter C
        omega
      · intro hcontra
        apply he1
        have h1 : ((A ∩ ((Finset.univ : Finset (Fin n)) \ C)).card : ℤ)
            = (A.card : ℤ) - ((A ∩ C).card : ℤ) := hinter C
        omega
    · exact Finset.sdiff_sdiff_eq_self hCsub

private lemma stepB_escape_lower {n k : ℕ} (A : Finset (Fin n)) (a : ℤ)
    (hA2 : A.card = 2) (hk : 2 ≤ k) (hkhalf : k ≤ n - k) (hkn : k + 2 ≤ n) :
    Nat.choose (n - 2) (k - 2) ≤ (escLayer n k A a).card := by
  have hk2 : 2 ≤ k := hk
  have hhalf : k ≤ n - k := hkhalf
  classical
  have hAcard : (Aᶜ : Finset (Fin n)).card = n - 2 := by
    rw [Finset.card_compl, Fintype.card_fin, hA2]
  by_cases hgood : ((2 : ℤ) ≠ a ∧ (2 : ℤ) ≠ a + 1)
  · -- 含 A 的类：S ↦ A ∪ S
    set f : Finset (Fin n) → Finset (Fin n) := fun S => A ∪ S with hf
    have hinj : Set.InjOn f ↑((Aᶜ : Finset (Fin n)).powersetCard (k - 2)) := by
      intro S1 hS1 S2 hS2 hEq
      obtain ⟨hS1sub, -⟩ := Finset.mem_powersetCard.mp hS1
      obtain ⟨hS2sub, -⟩ := Finset.mem_powersetCard.mp hS2
      have e1 : (A ∪ S1) ∩ Aᶜ = S1 := by
        ext x
        simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_compl]
        constructor
        · rintro ⟨hxA | hxS, hxAc⟩
          · exact absurd hxA hxAc
          · exact hxS
        · intro hx
          exact ⟨Or.inr hx, Finset.mem_compl.mp (hS1sub hx)⟩
      have e2 : (A ∪ S2) ∩ Aᶜ = S2 := by
        ext x
        simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_compl]
        constructor
        · rintro ⟨hxA | hxS, hxAc⟩
          · exact absurd hxA hxAc
          · exact hxS
        · intro hx
          exact ⟨Or.inr hx, Finset.mem_compl.mp (hS2sub hx)⟩
      have hEq' : A ∪ S1 = A ∪ S2 := hEq
      calc S1 = (A ∪ S1) ∩ Aᶜ := e1.symm
        _ = (A ∪ S2) ∩ Aᶜ := by rw [hEq']
        _ = S2 := e2
    have himgsub : ((Aᶜ : Finset (Fin n)).powersetCard (k - 2)).image f ⊆ escLayer n k A a := by
      intro B hB
      obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hB
      obtain ⟨hSsub, hScard⟩ := Finset.mem_powersetCard.mp hS
      have hdisj : Disjoint A S := by
        rw [Finset.disjoint_left]
        intro x hxA hxS
        exact (Finset.mem_compl.mp (hSsub hxS)) hxA
      have hBcard : (A ∪ S).card = k := by
        rw [Finset.card_union_of_disjoint hdisj, hA2, hScard]
        omega
      have hinter : A ∩ (A ∪ S) = A := Finset.inter_eq_left.mpr (Finset.subset_union_left)
      rw [escLayer, Finset.mem_filter, Finset.mem_powersetCard]
      refine ⟨⟨Finset.subset_univ _, hBcard⟩, ?_, ?_⟩
      · rw [hinter, hA2]; exact hgood.1
      · rw [hinter, hA2]; exact hgood.2
    calc (n - 2).choose (k - 2)
        = (((Aᶜ : Finset (Fin n)).powersetCard (k - 2))).card := by
          rw [Finset.card_powersetCard, hAcard]
      _ = ((((Aᶜ : Finset (Fin n)).powersetCard (k - 2)).image f)).card :=
          (Finset.card_image_of_injOn hinj).symm
      _ ≤ (escLayer n k A a).card := Finset.card_le_card himgsub
  · -- 不含 A 的类：S 本身
    have hone : a = 1 ∨ a = 2 := by omega
    have hID : ((Aᶜ : Finset (Fin n)).powersetCard k) ⊆ escLayer n k A a := by
      intro S hS
      obtain ⟨hSsub, hScard⟩ := Finset.mem_powersetCard.mp hS
      have hemp : A ∩ S = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro x hx
        exact (Finset.mem_compl.mp (hSsub (Finset.mem_inter.mp hx).2)) (Finset.mem_inter.mp hx).1
      have hzero : (A ∩ S).card = 0 := by rw [hemp]; simp
      rw [escLayer, Finset.mem_filter, Finset.mem_powersetCard]
      refine ⟨⟨Finset.subset_univ _, hScard⟩, ?_, ?_⟩
      · rw [hzero]; omega
      · rw [hzero]; omega
    have hE : (n - 2).choose k ≤ (escLayer n k A a).card := by
      calc (n - 2).choose k = ((Aᶜ : Finset (Fin n)).powersetCard k).card := by
            rw [Finset.card_powersetCard, hAcard]
        _ ≤ (escLayer n k A a).card := Finset.card_le_card hID
    -- C(n-2,k-2) ≤ C(n-2,k)
    have hratio : (n - 2).choose k * (k * (k - 1)) = (n - 2).choose (k - 2) * ((n - k) * (n - k - 1)) := by
      have hstep1 : (n - 2).choose k * k = (n - 2).choose (k - 1) * (n - k - 1) := by
        have h := Nat.choose_succ_right_eq (n - 2) (k - 1)
        rw [show k - 1 + 1 = k from by omega] at h
        rw [show n - 2 - (k - 1) = n - k - 1 from by omega] at h
        exact h
      have hstep2 : (n - 2).choose (k - 1) * (k - 1) = (n - 2).choose (k - 2) * (n - k) := by
        have h := Nat.choose_succ_right_eq (n - 2) (k - 2)
        rw [show k - 2 + 1 = k - 1 from by omega] at h
        rw [show n - 2 - (k - 2) = n - k from by omega] at h
        exact h
      calc (n - 2).choose k * (k * (k - 1))
          = ((n - 2).choose k * k) * (k - 1) := by ring
        _ = ((n - 2).choose (k - 1) * (n - k - 1)) * (k - 1) := by rw [hstep1]
        _ = ((n - 2).choose (k - 1) * (k - 1)) * (n - k - 1) := by ring
        _ = ((n - 2).choose (k - 2) * (n - k)) * (n - k - 1) := by rw [hstep2]
        _ = (n - 2).choose (k - 2) * ((n - k) * (n - k - 1)) := by ring
    have hmono : (n - 2).choose (k - 2) ≤ (n - 2).choose k := by
      have hY : k * (k - 1) ≤ (n - k) * (n - k - 1) := by
        have h1 : k ≤ n - k := hhalf
        have h2 : k - 1 ≤ n - k - 1 := by omega
        exact Nat.mul_le_mul h1 h2
      have hXpos : 0 < k * (k - 1) := by
        have : 1 ≤ k - 1 := by omega
        exact Nat.mul_pos (by omega) this
      have h1 : (n - 2).choose (k - 2) * (k * (k - 1)) ≤ (n - 2).choose (k - 2) * ((n - k) * (n - k - 1)) :=
        Nat.mul_le_mul_left _ hY
      rw [← hratio] at h1
      exact Nat.le_of_mul_le_mul_right h1 hXpos
    exact le_trans hmono hE

/-- Step B 的纯算术部分（对所有 k ≥ 2 成立）：2·k²·C(n,k) ≤ 5n²·C(n-2,k-2)。 -/
private lemma stepB_main {n k : ℕ} (hk : 2 ≤ k) (hkn : k + 2 ≤ n) :
    2 * k ^ 2 * Nat.choose n k ≤ 5 * n ^ 2 * Nat.choose (n - 2) (k - 2) := by
  have hk2 : 2 ≤ k := hk
  have hnk : k ≤ n := by omega
  -- Nat 比值恒等式：C(n,k)·k·(k-1) = n(n-1)·C(n-2,k-2)
  have hident : Nat.choose n k * (k * (k - 1)) = n * (n - 1) * (n - 2).choose (k - 2) := by
    have hstep1 : Nat.choose n k * k = n * Nat.choose (n - 1) (k - 1) := by
      have h := Nat.choose_mul (n := n) (k := k) (s := 1) (by omega)
      simpa [Nat.choose_one_right] using h
    have hstep2 : Nat.choose (n - 1) (k - 1) * (k - 1) = (n - 1) * Nat.choose (n - 2) (k - 2) := by
      have h := Nat.choose_mul (n := n - 1) (k := k - 1) (s := 1) (by omega)
      simpa [Nat.choose_one_right, show n - 1 - 1 = n - 2 from by omega,
        show k - 1 - 1 = k - 2 from by omega] using h
    calc Nat.choose n k * (k * (k - 1))
        = (Nat.choose n k * k) * (k - 1) := by ring
      _ = (n * Nat.choose (n - 1) (k - 1)) * (k - 1) := by rw [hstep1]
      _ = n * (Nat.choose (n - 1) (k - 1) * (k - 1)) := by ring
      _ = n * ((n - 1) * Nat.choose (n - 2) (k - 2)) := by rw [hstep2]
      _ = n * (n - 1) * (n - 2).choose (k - 2) := by ring
  -- ℝ 收尾
  have hnR : (0:ℝ) < (n:ℝ) := by
    have : 0 < n := by omega
    exact_mod_cast this
  have hnm1 : (0:ℝ) < (n:ℝ) - 1 := by
    have : 1 < n := by omega
    have h2 : (1:ℝ) < (n:ℝ) := by exact_mod_cast this
    linarith
  have hden : (n:ℝ) * ((n:ℝ) - 1) ≠ 0 := by
    exact mul_ne_zero hnR.ne' hnm1.ne'
  have hidentR : (Nat.choose n k : ℝ) * ((k:ℝ) * ((k:ℝ) - 1))
      = (n:ℝ) * ((n:ℝ) - 1) * ((n - 2).choose (k - 2) : ℝ) := by
    have h := congrArg (fun m : ℕ => (m : ℝ)) hident
    push_cast at h
    have hk1 : ((k - 1 : ℕ) : ℝ) = (k:ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ k)]; norm_num
    have hn1 : ((n - 1 : ℕ) : ℝ) = (n:ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ n)]; norm_num
    rw [hk1, hn1] at h
    exact h
  have key : 2 * (k:ℝ) * ((n:ℝ) - 1) ≤ 5 * (n:ℝ) * ((k:ℝ) - 1) := by
    have hkR2 : (2:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk2
    have hnR4 : (4:ℝ) ≤ (n:ℝ) := by
      have : 4 ≤ n := by omega
      exact_mod_cast this
    nlinarith
  have hApos : (0:ℝ) ≤ (Nat.choose n k : ℝ) := by positivity
  have hkey2 : 2 * (k:ℝ) * ((n:ℝ) - 1) * ((Nat.choose n k : ℝ) * (n:ℝ) * (k:ℝ))
      ≤ 5 * (n:ℝ) * ((k:ℝ) - 1) * ((Nat.choose n k : ℝ) * (n:ℝ) * (k:ℝ)) := by
    apply mul_le_mul_of_nonneg_right key
    positivity
  have hd : (0:ℝ) < (n:ℝ) * ((n:ℝ) - 1) := mul_pos hnR hnm1
  have hgoalR : (2:ℝ) * (k:ℝ)^2 * (Nat.choose n k : ℝ)
      ≤ 5 * (n:ℝ)^2 * ((n - 2).choose (k - 2) : ℝ) := by
    have hmul : ((2:ℝ) * (k:ℝ)^2 * (Nat.choose n k : ℝ)) * ((n:ℝ) * ((n:ℝ) - 1))
        ≤ (5 * (n:ℝ)^2 * ((n - 2).choose (k - 2) : ℝ)) * ((n:ℝ) * ((n:ℝ) - 1)) := by
      nlinarith [hkey2, hidentR]
    nlinarith [hmul, hd]
  exact_mod_cast hgoalR

/-- Step B 的最终形态：|A|=2 分支直接给出主定理的目标不等式（k ≤ n-k 情形）。 -/
private lemma stepB_done {n k : ℕ} (A : Finset (Fin n)) (a : ℤ)
    (hk2 : 2 ≤ k) (hkn : k + 2 ≤ n) (hhalf : k ≤ n - k) (hA2 : A.card = 2) :
    2 * (min k (n - k))^2 * ((Finset.univ : Finset (Fin n)).powersetCard k).card
      ≤ 5 * n^2 * (escLayer n k A a).card := by
  have hlayer : ((Finset.univ : Finset (Fin n)).powersetCard k).card = Nat.choose n k := by
    rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  have hE := stepB_escape_lower A a hA2 hk2 hhalf hkn
  have hpoly0 := stepB_main hk2 hkn
  have hpoly : 2 * (min k (n - k))^2 * Nat.choose n k ≤ 5 * n^2 * (n - 2).choose (k - 2) := by
    rw [Nat.min_eq_left hhalf]
    exact hpoly0
  calc 2 * (min k (n - k))^2 * ((Finset.univ : Finset (Fin n)).powersetCard k).card
      = 2 * (min k (n - k))^2 * Nat.choose n k := by rw [hlayer]
    _ ≤ 5 * n^2 * (n - 2).choose (k - 2) := hpoly
    _ ≤ 5 * n^2 * (escLayer n k A a).card := Nat.mul_le_mul_left (5 * n ^ 2) hE

private lemma main_reduced (n k : ℕ) (A : Finset (Fin n)) (a : ℤ)
    (hk : 2 ≤ k) (hkn : k + 2 ≤ n) (hA2 : 2 ≤ A.card) (hAn : A.card + 2 ≤ n)
    (hkhalf : k ≤ n - k) (hAhalf : A.card ≤ n - A.card) :
    2 * (min k (n - k)) ^ 2 * Nat.choose n k
      ≤ 5 * n ^ 2 * (escLayer n k A a).card := by
  have hm : min k (n - k) = k := Nat.min_eq_left hkhalf
  have hD := stepD_poly n k hk hkn hkhalf
  have hD' : 2 * k ^ 2 * Nat.choose n k ≤ 5 * n ^ 2 * sixZetaLower n k := by
    rwa [hm] at hD
  by_cases h2 : A.card = 2
  · have hB := stepB_escape_lower A a h2 hk hkhalf hkn
    have hBm := stepB_main (n := n) (k := k) hk hkn
    calc 2 * (min k (n - k)) ^ 2 * Nat.choose n k = 2 * k ^ 2 * Nat.choose n k := by rw [hm]
      _ ≤ 5 * n ^ 2 * Nat.choose (n - 2) (k - 2) := hBm
      _ ≤ 5 * n ^ 2 * (escLayer n k A a).card := Nat.mul_le_mul_left _ hB
  · have hA3 : 3 ≤ A.card := by omega
    have hAhalf' : 2 * A.card ≤ n := by omega
    have hC := stepC_escape_count n k A a hk hkn hA3 hAhalf'
    calc 2 * (min k (n - k)) ^ 2 * Nat.choose n k = 2 * k ^ 2 * Nat.choose n k := by rw [hm]
      _ ≤ 5 * n ^ 2 * sixZetaLower n k := hD'
      _ ≤ 5 * n ^ 2 * (escLayer n k A a).card := Nat.mul_le_mul_left _ hC

theorem PEqualNP.Outside.L_log_rank_sharp_layer_escape :
    ∀ (n k : ℕ) (A : Finset (Fin n)) (a : ℤ), 2 ≤ k → k+2 ≤ n → 2 ≤ A.card → A.card+2 ≤ n → let layer := (Finset.univ : Finset (Fin n)).powersetCard k; let esc := layer.filter (fun B => ((A ∩ B).card : ℤ) ≠ a ∧ ((A ∩ B).card : ℤ) ≠ a+1); 2*(min k (n-k))^2*layer.card ≤ 5*n^2*esc.card := by
  intro n k A a hk hkn hA2 hAn
  dsimp only
  rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  change 2 * (min k (n - k)) ^ 2 * Nat.choose n k
      ≤ 5 * n ^ 2 * (escLayer n k A a).card
  have hknle : k ≤ n := by omega
  have hcompl : (Aᶜ : Finset (Fin n)).card = n - A.card := by
    rw [Finset.card_compl, Fintype.card_fin]
  by_cases hkhalf : k ≤ n - k
  · by_cases hAhalf : A.card ≤ n - A.card
    · exact main_reduced n k A a hk hkn hA2 hAn hkhalf hAhalf
    · have hAC2 : 2 ≤ (Aᶜ : Finset (Fin n)).card := by rw [hcompl]; omega
      have hACn : (Aᶜ : Finset (Fin n)).card + 2 ≤ n := by rw [hcompl]; omega
      have hAChalf : (Aᶜ : Finset (Fin n)).card ≤ n - (Aᶜ : Finset (Fin n)).card := by
        rw [hcompl]; omega
      have hred := main_reduced n k Aᶜ ((k : ℤ) - 1 - a) hk hkn hAC2 hACn hkhalf hAChalf
      rwa [← escLayer_complA n k A a] at hred
  · have hk'k : n - k ≤ k := by omega
    have hkn' : (n - k) + 2 ≤ n := by omega
    have hC' : Nat.choose n k = Nat.choose n (n - k) := (Nat.choose_symm hknle).symm
    have hmin' : min k (n - k) = min (n - k) (n - (n - k)) := by
      have hsub : n - (n - k) = k := by omega
      rw [hsub, Nat.min_comm]
    by_cases hAhalf : A.card ≤ n - A.card
    · have hred := main_reduced n (n - k) A ((A.card : ℤ) - 1 - a)
        (by omega) hkn' hA2 hAn (by omega) hAhalf
      rw [hC', hmin', escLayer_complB n k A a hknle]
      exact hred
    · have hAC2 : 2 ≤ (Aᶜ : Finset (Fin n)).card := by rw [hcompl]; omega
      have hACn : (Aᶜ : Finset (Fin n)).card + 2 ≤ n := by rw [hcompl]; omega
      have hAChalf : (Aᶜ : Finset (Fin n)).card ≤ n - (Aᶜ : Finset (Fin n)).card := by
        rw [hcompl]; omega
      have hred := main_reduced n (n - k) Aᶜ
        (((n - k : ℕ) : ℤ) - 1 - ((A.card : ℤ) - 1 - a))
        (by omega) hkn' hAC2 hACn (by omega) hAChalf
      rw [hC', hmin', escLayer_complB n k A a hknle,
        escLayer_complA n (n - k) A ((A.card : ℤ) - 1 - a)]
      exact hred
