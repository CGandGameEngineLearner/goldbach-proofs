import Mathlib

private lemma ntl_incidence :
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

private lemma ntl_alteration :
    ∀ (n : ℕ) (T : Finset (Fin n)) (E : Finset (Finset (Fin n))), (∀ e∈E, e.card=3) → ∃ U ⊆ T, T.card ≤ U.card+(E.filter (fun e => e⊆T)).card ∧ ∀ e∈E, ¬ e⊆U := by
  intro n T E hE
  classical
  set S : Finset (Finset (Fin n)) := E.filter (fun e => e ⊆ T) with hS
  have hchoice : ∀ e ∈ S, ∃ x : Fin n, x ∈ e := by
    intro e he
    have h3 : e.card = 3 := hE e (Finset.mem_filter.mp he).1
    exact Finset.card_pos.mp (by omega)
  let g : {e // e ∈ S} → Fin n := fun e => Classical.choose (hchoice e.1 e.2)
  have hg : ∀ e : {e // e ∈ S}, g e ∈ e.1 := fun e => Classical.choose_spec (hchoice e.1 e.2)
  set H : Finset (Fin n) := S.attach.image g with hH
  have hHsub : H ⊆ T := by
    intro x hx
    rw [hH] at hx
    obtain ⟨e, -, rfl⟩ := Finset.mem_image.mp hx
    exact (Finset.mem_filter.mp e.2).2 (hg e)
  refine ⟨T \ H, Finset.sdiff_subset, ?_, ?_⟩
  · have hcardH : H.card ≤ S.card := by
      rw [hH]
      exact le_trans Finset.card_image_le (by simp)
    have hHT : H.card ≤ T.card := Finset.card_le_card hHsub
    have hcard : (T \ H).card = T.card - H.card := Finset.card_sdiff_of_subset hHsub
    omega
  · intro e he heU
    have heS : e ∈ S := by
      rw [hS]
      exact Finset.mem_filter.mpr ⟨he, heU.trans Finset.sdiff_subset⟩
    have hmem : g ⟨e, heS⟩ ∈ e := hg ⟨e, heS⟩
    have h1 : g ⟨e, heS⟩ ∈ H := by
      rw [hH]
      exact Finset.mem_image.mpr ⟨⟨e, heS⟩, Finset.mem_attach _ _, rfl⟩
    have h2 : g ⟨e, heS⟩ ∈ T \ H := heU hmem
    exact (Finset.mem_sdiff.mp h2).2 h1

theorem PEqualNP.Outside.L_no_three_in_line_sample_conflict_budget :
    ∀ (n k b : ℕ) (E : Finset (Finset (Fin n))), 3≤k → k≤n → (∀ e∈E,e.card=3) → E.card*Nat.choose (n-3) (k-3) ≤ b*Nat.choose n k → ∃ U : Finset (Fin n), k≤U.card+b ∧ ∀ e∈E, ¬ e⊆U := by
  intro n k b E hk hkn hE hbudget
  classical
  have hCcard : ((Finset.univ : Finset (Fin n)).powersetCard k).card = Nat.choose n k := by
    rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  have hCpos : 0 < ((Finset.univ : Finset (Fin n)).powersetCard k).card := by
    rw [hCcard]
    exact Nat.choose_pos hkn
  have hident := ntl_incidence n k E hk hkn hE
  have hT : ∃ T ∈ (Finset.univ : Finset (Fin n)).powersetCard k, (E.filter (fun e => e ⊆ T)).card ≤ b := by
    by_contra h
    have hlt : ∀ T ∈ (Finset.univ : Finset (Fin n)).powersetCard k, b < (E.filter (fun e => e ⊆ T)).card := by
      intro T hT
      by_contra hle
      exact h ⟨T, hT, Nat.not_lt.mp hle⟩
    have h1 : (b + 1) * ((Finset.univ : Finset (Fin n)).powersetCard k).card
        ≤ ∑ T ∈ (Finset.univ : Finset (Fin n)).powersetCard k, (E.filter (fun e => e ⊆ T)).card := by
      calc (b + 1) * ((Finset.univ : Finset (Fin n)).powersetCard k).card
          = ∑ T ∈ (Finset.univ : Finset (Fin n)).powersetCard k, (b + 1) := by
              rw [Finset.sum_const, smul_eq_mul]
              ring
        _ ≤ ∑ T ∈ (Finset.univ : Finset (Fin n)).powersetCard k, (E.filter (fun e => e ⊆ T)).card :=
              Finset.sum_le_sum (fun T hT => Nat.succ_le_of_lt (hlt T hT))
    have h2 : (∑ T ∈ (Finset.univ : Finset (Fin n)).powersetCard k, (E.filter (fun e => e ⊆ T)).card)
        ≤ b * ((Finset.univ : Finset (Fin n)).powersetCard k).card := by
      rw [hident, hCcard]
      exact hbudget
    have h3 : b * ((Finset.univ : Finset (Fin n)).powersetCard k).card
        < (b + 1) * ((Finset.univ : Finset (Fin n)).powersetCard k).card := by
      exact Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self b) hCpos
    exact absurd (le_trans h1 h2) (not_le.mpr h3)
  obtain ⟨T, hTC, hTb⟩ := hT
  have hTcard : T.card = k := (Finset.mem_powersetCard.mp hTC).2
  obtain ⟨U, -, hUcard, hUno⟩ := ntl_alteration n T E hE
  refine ⟨U, ?_, hUno⟩
  have : T.card ≤ U.card + (E.filter (fun e => e ⊆ T)).card := hUcard
  omega
