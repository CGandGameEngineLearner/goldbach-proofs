import Mathlib

theorem PEqualNP.Outside.L_no_three_in_line_triple_sample_incidence :
    ∀ (n k : ℕ) (E : Finset (Finset (Fin n))), 3≤k → k≤n → (∀ e∈E, e.card=3) → (∑ T ∈ (Finset.univ : Finset (Fin n)).powersetCard k, (E.filter (fun e => e⊆T)).card) = E.card * Nat.choose (n-3) (k-3) := by
  intro n k E hk hkn hE
  classical
  calc
    (∑ T ∈ (Finset.univ : Finset (Fin n)).powersetCard k, (E.filter (fun e => e ⊆ T)).card)
        = ∑ T ∈ (Finset.univ : Finset (Fin n)).powersetCard k, ∑ e ∈ E, if e ⊆ T then (1:ℕ) else 0 := by
          apply Finset.sum_congr rfl
          intro T hT
          simp
    _ = ∑ e ∈ E, ∑ T ∈ (Finset.univ : Finset (Fin n)).powersetCard k, if e ⊆ T then (1:ℕ) else 0 :=
          Finset.sum_comm
    _ = ∑ e ∈ E, (((Finset.univ : Finset (Fin n)).powersetCard k).filter (fun T => e ⊆ T)).card := by
          apply Finset.sum_congr rfl
          intro e he
          rw [Finset.card_filter]
    _ = ∑ e ∈ E, Nat.choose (n - 3) (k - 3) := by
          apply Finset.sum_congr rfl
          intro e he
          have he3 : e.card = 3 := hE e he
          have hle : e.card ≤ k := by omega
          have h := Finset.card_filter_powersetCard_subset e (Finset.univ : Finset (Fin n)) k (Finset.subset_univ e) hle
          rw [Finset.card_univ, Fintype.card_fin, he3] at h
          exact h
    _ = E.card * Nat.choose (n - 3) (k - 3) := by
          rw [Finset.sum_const, smul_eq_mul]
