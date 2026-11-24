import Mathlib

open scoped BigOperators

private lemma sum_zero_of_all_ksubsets (n k : ℕ) (w : Fin n → ℝ)
    (hk1 : 1 ≤ k) (hkn : k + 2 ≤ n)
    (hz : ∀ B : Finset (Fin n), B.card = k → Finset.sum B w = 0) :
    ∀ x, w x = 0 := by
  classical
  have hconst : ∀ e f : Fin n, w e = w f := by
    intro e f
    by_cases hef : e = f
    · rw [hef]
    · have hUcard : ((Finset.univ : Finset (Fin n)) \ ({e, f} : Finset (Fin n))).card = n - 2 := by
        rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
        have h2 : ({e, f} : Finset (Fin n)).card = 2 := by
          rw [Finset.card_insert_of_notMem (by simpa using hef), Finset.card_singleton]
        rw [h2]
        simp
      have hcard : k - 1 ≤ ((Finset.univ : Finset (Fin n)) \ ({e, f} : Finset (Fin n))).card := by
        rw [hUcard]
        omega
      obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hcard
      have he_notT : e ∉ T := by
        intro h
        have h' := hTsub h
        simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, Finset.mem_univ,
          true_and] at h'
        exact h' (by simp)
      have hf_notT : f ∉ T := by
        intro h
        have h' := hTsub h
        simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, Finset.mem_univ,
          true_and] at h'
        exact h' (by simp)
      have hBcard : (insert e T).card = k := by
        rw [Finset.card_insert_of_notMem he_notT]
        omega
      have hB'card : (insert f T).card = k := by
        rw [Finset.card_insert_of_notMem hf_notT]
        omega
      have hzB := hz (insert e T) hBcard
      have hzB' := hz (insert f T) hB'card
      rw [Finset.sum_insert he_notT] at hzB
      rw [Finset.sum_insert hf_notT] at hzB'
      linarith
  have hne : (k : ℝ) ≠ 0 := by
    have hkpos : 0 < k := by omega
    exact_mod_cast (Nat.pos_iff_ne_zero.mp hkpos)
  obtain ⟨B0, hB0card⟩ : ∃ B : Finset (Fin n), B.card = k := by
    have hle : k ≤ (Finset.univ : Finset (Fin n)).card := by
      simp
      omega
    obtain ⟨B, hBsub, hBcard⟩ := Finset.exists_subset_card_eq hle
    exact ⟨B, hBcard⟩
  have hz0 := hz B0 hB0card
  intro x
  have hsum : Finset.sum B0 w = (k : ℝ) * w x := by
    have hstep : ∀ y ∈ B0, w y = w x := fun y _ => hconst y x
    rw [Finset.sum_congr rfl hstep, Finset.sum_const, hB0card]
    simp [nsmul_eq_mul]
  rw [hsum] at hz0
  exact (mul_eq_zero.mp hz0).resolve_left hne



private lemma chi_diff_indep (n k : ℕ) (Y : Finset (Finset (Fin n)))
    (hk1 : 1 ≤ k) (hkn : k + 2 ≤ n)
    (huniq : ∀ (w : Fin n → ℝ) (C : ℝ), (∀ B ∈ Y, Finset.sum B w = C) →
      ∀ B : Finset (Fin n), B.card = k → Finset.sum B w = C)
    (S : Finset (Fin n)) (e0 : Fin n) (c : Fin n → ℝ)
    (hc : ∀ j : ↥Y, (∑ e ∈ S, c e * ((if e ∈ (j:↥Y).val then (1:ℝ) else 0) -
      (if e0 ∈ (j:↥Y).val then (1:ℝ) else 0))) = 0) :
    ∀ e ∈ S, e ≠ e0 → c e = 0 := by
  classical
  have hA : ∀ B : Finset (Fin n),
      (∑ e ∈ S, c e * (if e ∈ B then (1:ℝ) else 0)) = ∑ x ∈ B, (if x ∈ S then c x else 0) := by
    intro B
    simp only [mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_mem, Finset.sum_ite_mem, Finset.inter_comm]
  set T : ℝ := ∑ e ∈ S, c e with hT
  have hBsum : ∀ B : Finset (Fin n),
      (∑ x ∈ B, (if x = e0 then T else 0)) = T * (if e0 ∈ B then (1:ℝ) else 0) := by
    intro B
    rw [Finset.sum_ite_eq']
    by_cases h : e0 ∈ B <;> simp [h]
  let w : Fin n → ℝ := fun x => (if x ∈ S then c x else 0) - (if x = e0 then T else 0)
  have hw : ∀ B ∈ Y, Finset.sum B w = 0 := by
    intro B hBmem
    have hcB := hc ⟨B, hBmem⟩
    have hexp : (∑ e ∈ S, c e * ((if e ∈ B then (1:ℝ) else 0) - (if e0 ∈ B then (1:ℝ) else 0)))
        = (∑ e ∈ S, c e * (if e ∈ B then (1:ℝ) else 0)) -
          (∑ e ∈ S, c e * (if e0 ∈ B then (1:ℝ) else 0)) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro e _
      ring
    have h2 : (∑ e ∈ S, c e * (if e0 ∈ B then (1:ℝ) else 0))
        = T * (if e0 ∈ B then (1:ℝ) else 0) := by
      rw [hT, Finset.sum_mul]
    rw [hexp, h2, hA] at hcB
    have hsplit : Finset.sum B w = (∑ x ∈ B, (if x ∈ S then c x else 0)) -
        (∑ x ∈ B, (if x = e0 then T else 0)) := by
      simp only [w, Finset.sum_sub_distrib]
    rw [hsplit, hBsum]
    linarith
  have hw0 : ∀ B : Finset (Fin n), B.card = k → Finset.sum B w = 0 := by
    intro B hBc
    exact huniq w 0 hw B hBc
  have hwz : ∀ x, w x = 0 := sum_zero_of_all_ksubsets n k w hk1 hkn hw0
  intro e heS hene
  have hwe : w e = c e := by
    simp only [w]
    simp [heS, hene]
  rw [← hwe]
  exact hwz e

theorem PEqualNP.Outside.L_log_rank_rank_sized_protocol :
    ∀ (n k m : ℕ) (A : Fin m → Finset (Fin n)) (Y : Finset (Finset (Fin n))) (a : ℤ), 2 ≤ k → k+2 ≤ n → let layer := (Finset.univ : Finset (Fin n)).powersetCard k; let adj := fun (A B : Finset (Fin n)) (a : ℤ) => ((A ∩ B).card : ℤ) = a ∨ ((A ∩ B).card : ℤ) = a+1; let detects := fun (Y : Finset (Finset (Fin n))) => ∀ A : Finset (Fin n), 2 ≤ A.card → A.card + 2 ≤ n → ∀ a : ℤ, ∃ B ∈ Y, ¬ adj A B a; let lin := fun (w : Fin n → ℝ) (B : Finset (Fin n)) => Finset.sum B w; let uniqueOn := fun (Y : Finset (Finset (Fin n))) => ∀ (w : Fin n → ℝ) (c : ℝ), (∀ B ∈ Y, lin w B = c) → ∀ B ∈ layer, lin w B = c; Y.Nonempty → Y ⊆ layer → detects Y → uniqueOn Y → (∀ i, ∀ B ∈ Y, adj (A i) B a) → let M : Matrix (Fin m) (↥Y) ℝ := fun i j => (((A i ∩ j.val).card : ℝ) - (a : ℝ)); ∃ send : Fin m → Fin (M.rank+1), ∃ reply : Fin (M.rank+1) → ↥Y → Bool, ∃ out : Fin m → Bool → Bool, ∀ i j, (out i (reply (send i) j) = true ↔ M i j = 1) := by
  intro n k m A Y a hk hkn
  classical
  unfold Matrix
  dsimp only
  intro hYne hYsub hdet huniq hrow
  set M : Matrix (Fin m) (↥Y) ℝ := fun i j => ((A i ∩ (j:↥Y).val).card : ℝ) - (a : ℝ) with hM
  have hMval : ∀ (i : Fin m) (j : ↥Y), M i j = ((A i ∩ (j:↥Y).val).card : ℝ) - (a : ℝ) := fun i j => by rw [hM]
  have hYcard : ∀ B ∈ Y, B.card = k := by
    intro B hB
    have h := hYsub hB
    simp only [Finset.mem_powersetCard] at h
    exact h.2
  have hM01 : ∀ (i : Fin m) (j : ↥Y), M i j = 0 ∨ M i j = 1 := by
    intro i j
    have h := hrow i (j:↥Y) j.2
    rcases h with h | h
    · left
      rw [hM]
      have h' : ((A i ∩ (j:↥Y).val).card : ℝ) = (a : ℝ) := by exact_mod_cast h
      linarith
    · right
      rw [hM]
      have h' : ((A i ∩ (j:↥Y).val).card : ℝ) = ((a + 1 : ℤ) : ℝ) := by exact_mod_cast h
      push_cast at h'
      linarith
  have hclass : ∀ i : Fin m, (A i).card ≤ 1 ∨ n - 1 ≤ (A i).card := by
    intro i
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2⟩ := hcon
    have hle : (A i).card + 2 ≤ n := by omega
    obtain ⟨B, hBY, hBadj⟩ := hdet (A i) h1 hle a
    exact hBadj (hrow i B hBY)

  have hAcases : ∀ i : Fin m, A i = ∅ ∨ (∃ e : Fin n, A i = {e}) ∨ (∃ e : Fin n, A i = Finset.univ.erase e) ∨ A i = Finset.univ := by
    intro i
    rcases hclass i with hsmall | hbig
    · have hc : (A i).card = 0 ∨ (A i).card = 1 := by omega
      rcases hc with hc | hc
      · exact Or.inl (Finset.card_eq_zero.mp hc)
      · obtain ⟨e, he⟩ := Finset.card_eq_one.mp hc
        exact Or.inr (Or.inl ⟨e, he⟩)
    · have hle : (A i).card ≤ n := by
        have h2 := Finset.card_le_card (Finset.subset_univ (A i))
        simpa using h2
      have hc : (A i).card = n - 1 ∨ (A i).card = n := by omega
      rcases hc with hc | hc
      · have hcomp : (Finset.univ \ A i).card = 1 := by
          rw [Finset.card_sdiff_of_subset (Finset.subset_univ (A i)), hc, Finset.card_univ,
            Fintype.card_fin]
          omega
        obtain ⟨e, he⟩ := Finset.card_eq_one.mp hcomp
        refine Or.inr (Or.inr (Or.inl ⟨e, ?_⟩))
        ext x
        constructor
        · intro hx
          rw [Finset.mem_erase]
          refine ⟨?_, Finset.mem_univ x⟩
          intro hxe
          have hmem : e ∈ Finset.univ \ A i := by
            rw [he]
            simp
          rw [Finset.mem_sdiff] at hmem
          exact hmem.2 (hxe ▸ hx)
        · intro hx
          by_contra hxA
          have hmem : x ∈ Finset.univ \ A i := by
            rw [Finset.mem_sdiff]
            exact ⟨Finset.mem_univ x, hxA⟩
          rw [he] at hmem
          have hxe : x = e := by simpa using hmem
          have hne : x ≠ e := (Finset.mem_erase.mp hx).1
          exact hne hxe
      · exact Or.inr (Or.inr (Or.inr (Finset.eq_of_subset_of_card_le (Finset.subset_univ (A i)) (by simp [hc]))))
  have hrowkind : ∀ i : Fin m,
      (∃ v : ℝ, ∀ j : ↥Y, M i j = v) ∨
      (∃ e : Fin n, ∀ j : ↥Y, M i j = ((if e ∈ (j:↥Y).val then (1:ℝ) else 0) - (a:ℝ))) ∨
      (∃ e : Fin n, ∀ j : ↥Y, M i j = ((k:ℝ) - (if e ∈ (j:↥Y).val then (1:ℝ) else 0) - (a:ℝ))) := by
    intro i
    rcases hAcases i with hA | hA | hA | hA
    · left
      refine ⟨-(a:ℝ), ?_⟩
      intro j
      rw [hMval, hA]
      simp
    · obtain ⟨e, he⟩ := hA
      refine Or.inr (Or.inl ⟨e, ?_⟩)
      intro j
      rw [hMval, he]
      have hcard : (({e} ∩ (j:↥Y).val).card : ℝ) = (if e ∈ (j:↥Y).val then (1:ℝ) else 0) := by
        by_cases hmem : e ∈ (j:↥Y).val
        · have h1 : ({e} ∩ (j:↥Y).val) = {e} := by
            ext x
            simp only [Finset.mem_inter, Finset.mem_singleton]
            constructor
            · exact fun h => h.1
            · intro hx
              exact ⟨hx, hx ▸ hmem⟩
          rw [h1]
          simp [hmem]
        · have h1 : ({e} ∩ (j:↥Y).val) = ∅ := by
            ext x
            simp only [Finset.mem_inter, Finset.mem_singleton, Finset.notMem_empty, iff_false,
              not_and]
            intro hxe hxb
            exact hmem (hxe ▸ hxb)
          rw [h1]
          simp [hmem]
      rw [hcard]
    · obtain ⟨e, he⟩ := hA
      refine Or.inr (Or.inr ⟨e, ?_⟩)
      intro j
      rw [hMval, he]
      have hinter : ((Finset.univ.erase e) ∩ (j:↥Y).val) = ((j:↥Y).val).erase e := by
        ext x
        simp only [Finset.mem_inter, Finset.mem_erase, Finset.mem_univ]
        tauto
      have hcard : ((((j:↥Y).val).erase e).card : ℝ) = (k:ℝ) - (if e ∈ (j:↥Y).val then (1:ℝ) else 0) := by
        by_cases hmem : e ∈ (j:↥Y).val
        · rw [Finset.card_erase_of_mem hmem, hYcard (j:↥Y) j.2]
          simp only [hmem, ite_true]
          rw [Nat.cast_sub (by omega : (1:ℕ) ≤ k)]
          norm_num
        · rw [Finset.erase_eq_of_notMem hmem, hYcard (j:↥Y) j.2]
          simp [hmem]
      rw [hinter, hcard]
    · left
      refine ⟨(k:ℝ) - (a:ℝ), ?_⟩
      intro j
      rw [hMval, hA]
      have h1 : (Finset.univ ∩ (j:↥Y).val) = (j:↥Y).val := by simp
      rw [h1, hYcard (j:↥Y) j.2]
  have hUa : ∀ (i : Fin m) (e : Fin n), (¬ ∃ v : ℝ, ∀ j : ↥Y, M i j = v) →
      (∀ j : ↥Y, M i j = ((if e ∈ (j:↥Y).val then (1:ℝ) else 0) - (a:ℝ))) → a = 0 := by
    intro i e hnc hrow_
    obtain ⟨B0, hB0⟩ := hYne
    let j0 : ↥Y := ⟨B0, hB0⟩
    obtain ⟨j1, hj1⟩ : ∃ j : ↥Y, M i j ≠ M i j0 := by
      by_contra hcon
      push Not at hcon
      exact hnc ⟨M i j0, fun j => hcon j⟩
    have hχ : (if e ∈ (j1:↥Y).val then (1:ℝ) else 0) ≠
        (if e ∈ (j0:↥Y).val then (1:ℝ) else 0) := by
      intro hh
      exact hj1 (by rw [hrow_ j1, hrow_ j0, hh])
    by_cases he1 : e ∈ (j1:↥Y).val
    · by_cases he0 : e ∈ (j0:↥Y).val
      · exact absurd (by simp [he1, he0]) hχ
      · have h1 := hM01 i j1
        have h2 := hM01 i j0
        rw [hrow_ j1] at h1
        rw [hrow_ j0] at h2
        simp only [he1, he0, if_true, if_false] at h1 h2
        rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
        · exfalso; linarith
        · exfalso; linarith
        · have hz : (a:ℝ) = 0 := by linarith
          exact_mod_cast hz
        · exfalso; linarith
    · by_cases he0 : e ∈ (j0:↥Y).val
      · have h1 := hM01 i j1
        have h2 := hM01 i j0
        rw [hrow_ j1] at h1
        rw [hrow_ j0] at h2
        simp only [he1, he0, if_true, if_false] at h1 h2
        rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
        · exfalso; linarith
        · have hz : (a:ℝ) = 0 := by linarith
          exact_mod_cast hz
        · exfalso; linarith
        · exfalso; linarith
      · exact absurd (by simp [he1, he0]) hχ
  have hWa : ∀ (i : Fin m) (e : Fin n), (¬ ∃ v : ℝ, ∀ j : ↥Y, M i j = v) →
      (∀ j : ↥Y, M i j = ((k:ℝ) - (if e ∈ (j:↥Y).val then (1:ℝ) else 0) - (a:ℝ))) → a = k - 1 := by
    intro i e hnc hrow_
    obtain ⟨B0, hB0⟩ := hYne
    let j0 : ↥Y := ⟨B0, hB0⟩
    obtain ⟨j1, hj1⟩ : ∃ j : ↥Y, M i j ≠ M i j0 := by
      by_contra hcon
      push Not at hcon
      exact hnc ⟨M i j0, fun j => hcon j⟩
    have hχ : (if e ∈ (j1:↥Y).val then (1:ℝ) else 0) ≠
        (if e ∈ (j0:↥Y).val then (1:ℝ) else 0) := by
      intro hh
      exact hj1 (by rw [hrow_ j1, hrow_ j0, hh])
    by_cases he1 : e ∈ (j1:↥Y).val
    · by_cases he0 : e ∈ (j0:↥Y).val
      · exact absurd (by simp [he1, he0]) hχ
      · have h1 := hM01 i j1
        have h2 := hM01 i j0
        rw [hrow_ j1] at h1
        rw [hrow_ j0] at h2
        simp only [he1, he0, if_true, if_false] at h1 h2
        rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
        · exfalso; linarith
        · have hz : (a:ℝ) = (k:ℝ) - 1 := by linarith
          exact_mod_cast hz
        · exfalso; linarith
        · exfalso; linarith
    · by_cases he0 : e ∈ (j0:↥Y).val
      · have h1 := hM01 i j1
        have h2 := hM01 i j0
        rw [hrow_ j1] at h1
        rw [hrow_ j0] at h2
        simp only [he1, he0, if_true, if_false] at h1 h2
        rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
        · exfalso; linarith
        · exfalso; linarith
        · have hz : (a:ℝ) = (k:ℝ) - 1 := by linarith
          exact_mod_cast hz
        · exfalso; linarith
      · exact absurd (by simp [he1, he0]) hχ
  have hexcl : ¬ ((∃ i, (¬ ∃ v : ℝ, ∀ j : ↥Y, M i j = v) ∧
      (∃ e : Fin n, ∀ j : ↥Y, M i j = ((if e ∈ (j:↥Y).val then (1:ℝ) else 0) - (a:ℝ)))) ∧
      (∃ i, (¬ ∃ v : ℝ, ∀ j : ↥Y, M i j = v) ∧
      (∃ e : Fin n, ∀ j : ↥Y, M i j = ((k:ℝ) - (if e ∈ (j:↥Y).val then (1:ℝ) else 0) - (a:ℝ))))) := by
    rintro ⟨⟨i1, h1nc, e1, h1r⟩, ⟨i2, h2nc, e2, h2r⟩⟩
    have ha0 : a = 0 := hUa i1 e1 h1nc h1r
    have hak : a = k - 1 := hWa i2 e2 h2nc h2r
    omega
  have hχ01 : ∀ (e : Fin n) (j : ↥Y), ((if e ∈ (j:↥Y).val then (1:ℝ) else 0) = 1) ∨
      ((if e ∈ (j:↥Y).val then (1:ℝ) else 0) = 0) := by
    intro e j
    by_cases h : e ∈ (j:↥Y).val <;> simp [h]
  have hncdata : ∀ i : Fin m, (¬ ∃ v : ℝ, ∀ j : ↥Y, M i j = v) →
      ∃ (e : Fin n) (jO jZ : ↥Y),
        ((if e ∈ (jO:↥Y).val then (1:ℝ) else 0) = 1) ∧
        ((if e ∈ (jZ:↥Y).val then (1:ℝ) else 0) = 0) ∧
        (∀ j : ↥Y, (if e ∈ (j:↥Y).val then (1:ℝ) else 0) = 1 → M i j = M i jO) ∧
        (∀ j : ↥Y, (if e ∈ (j:↥Y).val then (1:ℝ) else 0) = 0 → M i j = M i jZ) := by
    intro i hnc
    rcases hrowkind i with hC | ⟨e, he⟩ | ⟨e, he⟩
    · exact absurd hC hnc
    · have hrow : ∀ j : ↥Y, M i j = ((if e ∈ (j:↥Y).val then (1:ℝ) else 0) - (a:ℝ)) := he
      have hex1 : ∃ j : ↥Y, (if e ∈ (j:↥Y).val then (1:ℝ) else 0) = 1 := by
        by_contra hcon
        push Not at hcon
        apply hnc
        refine ⟨-(a:ℝ), fun j => ?_⟩
        rw [hrow j]
        have h0 : (if e ∈ (j:↥Y).val then (1:ℝ) else 0) = 0 := by
          rcases hχ01 e j with h | h
          · exact absurd h (hcon j)
          · exact h
        rw [h0]; ring
      obtain ⟨jO, hjO⟩ := hex1
      have hex0 : ∃ j : ↥Y, (if e ∈ (j:↥Y).val then (1:ℝ) else 0) = 0 := by
        by_contra hcon
        push Not at hcon
        apply hnc
        refine ⟨1 - (a:ℝ), fun j => ?_⟩
        rw [hrow j]
        have h1 : (if e ∈ (j:↥Y).val then (1:ℝ) else 0) = 1 := by
          rcases hχ01 e j with h | h
          · exact h
          · exact absurd h (hcon j)
        rw [h1]
      obtain ⟨jZ, hjZ⟩ := hex0
      exact ⟨e, jO, jZ, hjO, hjZ,
        fun j hj => by rw [hrow j, hrow jO, hj, hjO],
        fun j hj => by rw [hrow j, hrow jZ, hj, hjZ]⟩
    · have hrow : ∀ j : ↥Y, M i j = ((k:ℝ) - (if e ∈ (j:↥Y).val then (1:ℝ) else 0) - (a:ℝ)) := he
      have hex1 : ∃ j : ↥Y, (if e ∈ (j:↥Y).val then (1:ℝ) else 0) = 1 := by
        by_contra hcon
        push Not at hcon
        apply hnc
        refine ⟨(k:ℝ) - (a:ℝ), fun j => ?_⟩
        rw [hrow j]
        have h0 : (if e ∈ (j:↥Y).val then (1:ℝ) else 0) = 0 := by
          rcases hχ01 e j with h | h
          · exact absurd h (hcon j)
          · exact h
        rw [h0]; ring
      obtain ⟨jO, hjO⟩ := hex1
      have hex0 : ∃ j : ↥Y, (if e ∈ (j:↥Y).val then (1:ℝ) else 0) = 0 := by
        by_contra hcon
        push Not at hcon
        apply hnc
        refine ⟨(k:ℝ) - 1 - (a:ℝ), fun j => ?_⟩
        rw [hrow j]
        have h1 : (if e ∈ (j:↥Y).val then (1:ℝ) else 0) = 1 := by
          rcases hχ01 e j with h | h
          · exact h
          · exact absurd h (hcon j)
        rw [h1]
      obtain ⟨jZ, hjZ⟩ := hex0
      exact ⟨e, jO, jZ, hjO, hjZ,
        fun j hj => by rw [hrow j, hrow jO, hj, hjO],
        fun j hj => by rw [hrow j, hrow jZ, hj, hjZ]⟩
  have hnpos : 0 < n := by omega
  let dfin : Fin n := ⟨0, hnpos⟩
  have hUformAll : (∃ i : Fin m, (¬ ∃ v : ℝ, ∀ j : ↥Y, M i j = v) ∧
      (∃ e : Fin n, ∀ j : ↥Y, M i j = ((if e ∈ (j:↥Y).val then (1:ℝ) else 0) - (a:ℝ)))) →
      ∀ i, (¬ ∃ v : ℝ, ∀ j : ↥Y, M i j = v) →
      ∃ e : Fin n, ∀ j : ↥Y, M i j = ((if e ∈ (j:↥Y).val then (1:ℝ) else 0) - (a:ℝ)) := by
    intro hU i hnc
    rcases hrowkind i with hC | hU' | hW'
    · exact absurd hC hnc
    · exact hU'
    · exact absurd ⟨hU, ⟨i, hnc, hW'⟩⟩ hexcl
  have hWformAll : (¬ ∃ i : Fin m, (¬ ∃ v : ℝ, ∀ j : ↥Y, M i j = v) ∧
      (∃ e : Fin n, ∀ j : ↥Y, M i j = ((if e ∈ (j:↥Y).val then (1:ℝ) else 0) - (a:ℝ)))) →
      ∀ i, (¬ ∃ v : ℝ, ∀ j : ↥Y, M i j = v) →
      ∃ e : Fin n, ∀ j : ↥Y, M i j = ((k:ℝ) - (if e ∈ (j:↥Y).val then (1:ℝ) else 0) - (a:ℝ)) := by
    intro hU i hnc
    rcases hrowkind i with hC | hU' | hW'
    · exact absurd hC hnc
    · exact absurd ⟨i, hnc, hU'⟩ hU
    · exact hW'
  obtain ⟨sb, cc, hsign, hrowu⟩ : ∃ (sb : Bool) (cc : Fin m → Fin n), (sb = true ∨ sb = false) ∧
      ∀ i, (¬ ∃ v : ℝ, ∀ j : ↥Y, M i j = v) → ∀ j : ↥Y,
        M i j = (if sb then (if cc i ∈ (j:↥Y).val then (1:ℝ) else 0)
          else (if cc i ∈ (j:↥Y).val then (0:ℝ) else 1)) := by
    by_cases hU : ∃ i : Fin m, (¬ ∃ v : ℝ, ∀ j : ↥Y, M i j = v) ∧
        (∃ e : Fin n, ∀ j : ↥Y, M i j = ((if e ∈ (j:↥Y).val then (1:ℝ) else 0) - (a:ℝ)))
    · let cc' : Fin m → Fin n := fun i => if h : (¬ ∃ v : ℝ, ∀ j : ↥Y, M i j = v) then
          Classical.choose (hUformAll hU i h) else dfin
      refine ⟨true, cc', Or.inl rfl, ?_⟩
      intro i hnc j
      have hcc' : cc' i = Classical.choose (hUformAll hU i hnc) := by
        simp only [cc']
        exact dif_pos hnc
      set c : Fin n := Classical.choose (hUformAll hU i hnc) with hc_def
      rw [show cc' i = c from hcc']
      have hspec : M i j = (if c ∈ (j:↥Y).val then (1:ℝ) else 0) - (a:ℝ) := by
        rw [hc_def]
        exact Classical.choose_spec (hUformAll hU i hnc) j
      have ha0 : a = 0 := by
        rw [hc_def] at *
        exact hUa i _ hnc (Classical.choose_spec (hUformAll hU i hnc))
      rw [hspec, ha0]
      simp only [Int.cast_zero, sub_zero]
      by_cases hmem : c ∈ (j:↥Y).val <;> simp [hmem]
    · let cc' : Fin m → Fin n := fun i => if h : (¬ ∃ v : ℝ, ∀ j : ↥Y, M i j = v) then
          Classical.choose (hWformAll hU i h) else dfin
      refine ⟨false, cc', Or.inr rfl, ?_⟩
      intro i hnc j
      have hcc' : cc' i = Classical.choose (hWformAll hU i hnc) := by
        simp only [cc']
        exact dif_pos hnc
      set c : Fin n := Classical.choose (hWformAll hU i hnc) with hc_def
      rw [show cc' i = c from hcc']
      have hspec : M i j = ((k:ℝ) - (if c ∈ (j:↥Y).val then (1:ℝ) else 0)) - (a:ℝ) := by
        rw [hc_def]
        exact Classical.choose_spec (hWformAll hU i hnc) j
      have hak : a = k - 1 := by
        rw [hc_def] at *
        exact hWa i _ hnc (Classical.choose_spec (hWformAll hU i hnc))
      have hk' : ((a:ℝ)) = (k:ℝ) - 1 := by
        have h2 : ((a:ℝ)) = ((((k:ℤ) - 1 : ℤ)) : ℝ) := by rw [hak]
        simpa using h2
      rw [hspec, hk']
      by_cases hmem : c ∈ (j:↥Y).val <;> simp [hmem]
  let S : Finset (Fin n) := (Finset.univ.filter (fun i : Fin m =>
    ¬ ∃ v : ℝ, ∀ j : ↥Y, M i j = v)).image cc
  have hcval : ∀ i, (∃ v : ℝ, ∀ j : ↥Y, M i j = v) → ∀ j : ↥Y, M i j = (if h : (∃ v : ℝ, ∀ j : ↥Y, M i j = v) then Classical.choose h else 0) := by
    intro i h j
    rw [dif_pos h]
    exact Classical.choose_spec h j
  
  have huniq' : ∀ (w : Fin n → ℝ) (C : ℝ), (∀ B ∈ Y, Finset.sum B w = C) →
      ∀ B : Finset (Fin n), B.card = k → Finset.sum B w = C := by
    intro w C hw B hB
    exact huniq w C hw B (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ B, hB⟩)
  have hSrank : S.card ≤ M.rank + 1 := by
    by_cases hzero : S.card = 0
    · omega
    · have hpos : 0 < S.card := by omega
      obtain ⟨e0, he0S⟩ := Finset.card_pos.mp hpos
      have hwit : ∀ e ∈ S, ∃ i : Fin m, (¬ ∃ v : ℝ, ∀ j : ↥Y, M i j = v) ∧ cc i = e := by
        intro e he
        have he' : e ∈ (Finset.univ.filter (fun i : Fin m =>
            ¬ ∃ v : ℝ, ∀ j : ↥Y, M i j = v)).image cc := by
          simpa only [S] using he
        obtain ⟨i, hi, hci⟩ := Finset.mem_image.mp he'
        exact ⟨i, (Finset.mem_filter.mp hi).2, hci⟩
      let iw : (e : Fin n) → e ∈ S → Fin m := fun e he => Classical.choose (hwit e he)
      have hiw : ∀ (e : Fin n) (he : e ∈ S), (¬ ∃ v : ℝ, ∀ j : ↥Y, M (iw e he) j = v) ∧ cc (iw e he) = e := by
        intro e he
        exact Classical.choose_spec (hwit e he)
      let sv : ℝ := if sb then (1:ℝ) else -1
      have hsvne : sv ≠ 0 := by
        simp only [sv]
        split_ifs <;> norm_num
      -- rows at witnesses are affine in the coordinate indicator
      have hform : ∀ (e : Fin n) (he : e ∈ S) (j : ↥Y),
          M (iw e he) j - M (iw e0 he0S) j = sv * ((if e ∈ (j:↥Y).val then (1:ℝ) else 0) -
            (if e0 ∈ (j:↥Y).val then (1:ℝ) else 0)) := by
        intro e he j
        have h1 := hrowu (iw e he) (hiw e he).1 j
        have h2 := hrowu (iw e0 he0S) (hiw e0 he0S).1 j
        rw [h1, h2, (hiw e he).2, (hiw e0 he0S).2]
        simp only [sv]
        by_cases hb : sb
        · simp only [hb, if_true, ite_true]
          by_cases hq : e ∈ (j:↥Y).val <;> by_cases hq2 : e0 ∈ (j:↥Y).val <;> simp [hq, hq2]
        · simp only [hb, Bool.false_eq_true, if_false, ite_true]
          by_cases hq : e ∈ (j:↥Y).val <;> by_cases hq2 : e0 ∈ (j:↥Y).val <;> simp [hq, hq2]
      let u : ↥(S.erase e0) → (↥Y → ℝ) := fun t => fun j =>
        M (iw t.1 (Finset.mem_of_mem_erase t.2)) j - M (iw e0 he0S) j
      have hind : LinearIndependent ℝ u := by
        rw [linearIndependent_iff']
        intro T g hsum t ht
        set c : Fin n → ℝ := fun x => sv * (∑ i ∈ T, if (i.1 : Fin n) = x then g i else 0) with hcdef
        have hchi : ∀ j : ↥Y, (∑ x ∈ S, c x * ((if x ∈ (j:↥Y).val then (1:ℝ) else 0) -
            (if e0 ∈ (j:↥Y).val then (1:ℝ) else 0))) = 0 := by
          intro j
          set F : Fin n → ℝ := fun x => (if x ∈ (j:↥Y).val then (1:ℝ) else 0) -
            (if e0 ∈ (j:↥Y).val then (1:ℝ) else 0) with hF
          have hpt : (∑ i ∈ T, g i * u i j) = 0 := by
            have h2 : (∑ i ∈ T, g i • u i) j = ((0 : ↥Y → ℝ)) j := by rw [hsum]
            simpa [Pi.smul_apply, smul_eq_mul] using h2
          have h1 : (∑ x ∈ S, c x * F x) =
              sv * (∑ x ∈ S, (∑ i ∈ T, if (i.1 : Fin n) = x then g i else 0) * F x) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro x _
            simp only [hcdef]
            ring
          have h2 : (∑ x ∈ S, (∑ i ∈ T, if (i.1 : Fin n) = x then g i else 0) * F x) =
              ∑ i ∈ T, g i * F (i.1) := by
            simp only [Finset.sum_mul]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro i _
            simp only [ite_mul, zero_mul]
            rw [Finset.sum_ite_eq, if_pos (Finset.mem_of_mem_erase i.2)]
          have h3 : (∑ i ∈ T, g i * u i j) = sv * (∑ i ∈ T, g i * F (i.1)) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            have hrow := hform i.1 (Finset.mem_of_mem_erase i.2) j
            simp only [u, hF]
            rw [hrow]
            ring
          calc (∑ x ∈ S, c x * F x) = sv * (∑ x ∈ S, (∑ i ∈ T, if (i.1 : Fin n) = x then g i else 0) * F x) := h1
            _ = sv * (∑ i ∈ T, g i * F (i.1)) := by rw [h2]
            _ = ∑ i ∈ T, g i * u i j := h3.symm
            _ = 0 := hpt
        have hk1 : 1 ≤ k := by omega
        have hcz := chi_diff_indep n k Y hk1 hkn huniq' S e0 c hchi
        have hct : c t.1 = 0 :=
          hcz t.1 (Finset.mem_of_mem_erase t.2) (Finset.ne_of_mem_erase t.2)
        have hsumt : c t.1 = sv * g t := by
          simp only [hcdef]
          congr 1
          rw [Finset.sum_eq_single t]
          · simp
          · intro i hi hit
            by_cases hh : (i.1 : Fin n) = t.1
            · exact absurd (Subtype.ext hh) hit
            · simp [hh]
          · intro ht'; exact absurd ht ht'
        rw [hsumt] at hct
        exact (mul_eq_zero.mp hct).resolve_left hsvne
      have hfin : Module.finrank ℝ (Submodule.span ℝ (Set.range u)) = S.card - 1 := by
        rw [finrank_span_eq_card hind, Fintype.card_coe, Finset.card_erase_of_mem he0S]
      have hle : Submodule.span ℝ (Set.range u) ≤ Submodule.span ℝ (Set.range M.row) := by
        rw [Submodule.span_le]
        rintro _ ⟨t, rfl⟩
        exact Submodule.sub_mem _ (Submodule.subset_span ⟨_, rfl⟩) (Submodule.subset_span ⟨_, rfl⟩)
      have hmono := Submodule.finrank_mono hle
      rw [M.rank_eq_finrank_span_row]
      omega
  let crow : Fin m → ℝ := fun i => if h : (∃ v : ℝ, ∀ j : ↥Y, M i j = v) then Classical.choose h else 0
  have hcrow : ∀ i, (h : ∃ v : ℝ, ∀ j : ↥Y, M i j = v) → ∀ j : ↥Y, M i j = crow i := by
    intro i h j
    simp only [crow]
    rw [dif_pos h]
    exact Classical.choose_spec h j
  by_cases hzero : S.card = 0
  · -- all rows constant
    refine ⟨fun _ => 0, fun _ _ => false, fun i _ => decide (crow i = 1), ?_⟩
    intro i j
    have hPC : (∃ v : ℝ, ∀ j : ↥Y, M i j = v) := by
      by_contra hnc
      have hmem : cc i ∈ S := by
        exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hnc⟩, rfl⟩
      have hempty : S = ∅ := Finset.card_eq_zero.mp hzero
      rw [hempty] at hmem
      exact absurd hmem (Finset.notMem_empty _)
    have h1 := hcrow i hPC j
    rw [decide_eq_true_iff, ← h1]
  · -- nontrivial: build the coding
    have hpos : 0 < S.card := Nat.pos_of_ne_zero hzero
    obtain ⟨e0, he0S⟩ := Finset.card_pos.mp hpos
    have hcardle : Fintype.card ↥S ≤ M.rank + 1 := by
      rwa [Fintype.card_coe]
    let enc : ↥S → Fin (M.rank + 1) := fun a => Fin.castLE hcardle (Fintype.equivFin ↥S a)
    have henc_inj : Function.Injective enc := by
      intro a b hab
      exact (Fintype.equivFin ↥S).injective (Fin.castLE_injective hcardle hab)
    let dec : Fin (M.rank + 1) → Fin n := fun m =>
      if h : ∃ a : ↥S, enc a = m then (Classical.choose h).1 else e0
    have hdec : ∀ a : ↥S, dec (enc a) = a.1 := by
      intro a
      have hex : ∃ b : ↥S, enc b = enc a := ⟨a, rfl⟩
      simp only [dec]
      rw [dif_pos hex]
      exact congrArg Subtype.val (henc_inj (Classical.choose_spec hex))
    let sendF : Fin m → Fin (M.rank + 1) := fun i =>
      if h : (¬ ∃ v : ℝ, ∀ j : ↥Y, M i j = v) then
        enc ⟨cc i, Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩, rfl⟩⟩
      else 0
    let replyF : Fin (M.rank + 1) → ↥Y → Bool := fun m j => decide (dec m ∈ (j:↥Y).val)
    let outF : Fin m → Bool → Bool := fun i b =>
      if h : (¬ ∃ v : ℝ, ∀ j : ↥Y, M i j = v) then (if sb then b else !b)
      else decide (crow i = 1)
    refine ⟨sendF, replyF, outF, ?_⟩
    intro i j
    by_cases hnc : (¬ ∃ v : ℝ, ∀ j : ↥Y, M i j = v)
    · have hrow := hrowu i hnc j
      have hsend : sendF i = enc ⟨cc i, Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hnc⟩, rfl⟩⟩ := by
        simp only [sendF]
        exact dif_pos hnc
      have hrep : replyF (sendF i) j = decide (cc i ∈ (j:↥Y).val) := by
        simp only [replyF]
        rw [hsend, hdec]
      have hout : outF i (replyF (sendF i) j) =
          (if sb then replyF (sendF i) j else !(replyF (sendF i) j)) := by
        simp only [outF]
        exact dif_pos hnc
      change (outF i (replyF (sendF i) j) = true) ↔ M i j = 1
      rw [hout, hrep, hrow]
      by_cases hsb : sb
      · simp only [hsb, if_true, decide_eq_true_iff]
        by_cases hmem : cc i ∈ (j:↥Y).val <;> simp [hmem]
      · simp only [hsb, Bool.false_eq_true, if_false, decide_eq_true_iff]
        by_cases hmem : cc i ∈ (j:↥Y).val <;> simp [hmem]
    · have hPC : (∃ v : ℝ, ∀ j : ↥Y, M i j = v) := by
        by_contra h2
        exact hnc h2
      have hout : outF i (replyF (sendF i) j) = decide (crow i = 1) := by
        simp only [outF]
        exact dif_neg hnc
      change (outF i (replyF (sendF i) j) = true) ↔ M i j = 1
      have h1 := hcrow i hPC j
      rw [hout, decide_eq_true_iff, ← h1]
