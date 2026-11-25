import Mathlib

private theorem countSamplesContainingTriple {n k : ℕ} (e : Finset (Fin n))
    (he : e.card = 3) (h3k : 3 ≤ k) :
    (((Finset.univ : Finset (Fin n)).powersetCard k).filter
      (fun T => e ⊆ T)).card = Nat.choose (n - 3) (k - 3) := by
  classical
  let U : Finset (Fin n) := Finset.univ \ e
  let S : Finset (Finset (Fin n)) :=
    ((Finset.univ : Finset (Fin n)).powersetCard k).filter (fun T => e ⊆ T)
  have hUcard : U.card = n - 3 := by
    dsimp [U]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ e), Finset.card_univ,
      Fintype.card_fin, he]
  have hcount : S.card = (U.powersetCard (k - 3)).card := by
    refine Finset.card_bij (fun T _ => T \ e) ?_ ?_ ?_
    · intro T hT
      rcases Finset.mem_filter.mp hT with ⟨hTk, heT⟩
      rcases Finset.mem_powersetCard.mp hTk with ⟨_, hTcard⟩
      rw [Finset.mem_powersetCard]
      constructor
      · intro x hx
        exact Finset.mem_sdiff.mpr
          ⟨Finset.mem_univ x, fun hxe => (Finset.mem_sdiff.mp hx).2 hxe⟩
      · rw [Finset.card_sdiff_of_subset heT, hTcard, he]
    · intro T hT T' hT' hEq
      apply Finset.ext
      intro x
      by_cases hx : x ∈ e
      · have hsub := (Finset.mem_filter.mp hT).2
        have hsub' := (Finset.mem_filter.mp hT').2
        simp [hsub hx, hsub' hx]
      · simpa [Finset.mem_sdiff, hx] using Finset.ext_iff.mp hEq x
    · intro V hV
      rcases Finset.mem_powersetCard.mp hV with ⟨hVU, hVcard⟩
      have hdis : Disjoint e V := by
        rw [Finset.disjoint_left]
        intro x hxE hxV
        exact (Finset.mem_sdiff.mp (hVU hxV)).2 hxE
      let T : Finset (Fin n) := e ∪ V
      refine ⟨T, Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ?_, ?_⟩, ?_⟩
      · constructor
        · exact Finset.subset_univ T
        · change (e ∪ V).card = k
          rw [Finset.card_union_of_disjoint hdis, he, hVcard]
          omega
      · intro x hx
        exact Finset.mem_union_left _ hx
      · dsimp [T]
        apply Finset.ext
        intro x
        by_cases hxE : x ∈ e
        · have hxV : x ∉ V := by
            intro hxV
            exact (Finset.mem_sdiff.mp (hVU hxV)).2 hxE
          simp [hxE, hxV]
        · simp [Finset.mem_sdiff, hxE]
  rw [hcount, Finset.card_powersetCard, hUcard]

theorem PEqualNP.Outside.L_no_three_in_line_triple_sample_incidence :
    ∀ (n k : ℕ) (E : Finset (Finset (Fin n))), 3 ≤ k → k ≤ n →
      (∀ e ∈ E, e.card = 3) →
      (∑ T ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
        (E.filter (fun e => e ⊆ T)).card) =
        E.card * Nat.choose (n - 3) (k - 3) := by
  intro n k E h3k hkn hE
  classical
  let S : Finset (Finset (Fin n)) :=
    (Finset.univ : Finset (Fin n)).powersetCard k
  calc
    (∑ T ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
        (E.filter (fun e => e ⊆ T)).card) =
        ∑ T ∈ S, (E.filter (fun e => e ⊆ T)).card := rfl
    _ = ∑ T ∈ S, ∑ e ∈ E, if e ⊆ T then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro T hT
      rw [Finset.card_filter]
    _ = ∑ e ∈ E, ∑ T ∈ S, if e ⊆ T then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ e ∈ E, (S.filter (fun T => e ⊆ T)).card := by
      apply Finset.sum_congr rfl
      intro e he
      symm
      rw [Finset.card_filter]
    _ = ∑ e ∈ E, Nat.choose (n - 3) (k - 3) := by
      apply Finset.sum_congr rfl
      intro e he
      exact countSamplesContainingTriple e (hE e he) h3k
    _ = E.card * Nat.choose (n - 3) (k - 3) := by
      simp [Finset.sum_const, nsmul_eq_mul]
