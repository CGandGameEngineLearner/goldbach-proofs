import Mathlib

open scoped BigOperators

private lemma row_shape {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k) {Y : Finset (Finset (Fin n))}
    {A : Finset (Fin n)} {a : ℝ} (hYcard : ∀ B ∈ Y, B.card = k)
    (hclass : A.card ≤ 1 ∨ n - 1 ≤ A.card) :
    (A = ∅ ∧ ∀ j : ↥Y, ((A ∩ (j:↥Y).val).card : ℝ) - a = -a) ∨
    (∃ e : Fin n, A = {e} ∧ ∀ j : ↥Y,
        ((A ∩ (j:↥Y).val).card : ℝ) - a = (if e ∈ (j:↥Y).val then 1 else 0) - a) ∨
    (∃ e : Fin n, A = Finset.univ.erase e ∧ ∀ j : ↥Y,
        ((A ∩ (j:↥Y).val).card : ℝ) - a
          = (k : ℝ) - a - (if e ∈ (j:↥Y).val then 1 else 0)) ∨
    (A = Finset.univ ∧ ∀ j : ↥Y, ((A ∩ (j:↥Y).val).card : ℝ) - a = (k : ℝ) - a) := by
  have hAle : A.card ≤ n := by
    simpa [Fintype.card_fin] using Finset.card_le_univ A
  rcases hclass with hsmall | hbig
  · have h01 : A.card = 0 ∨ A.card = 1 := by omega
    rcases h01 with h0 | h1
    · left
      have hA0 : A = ∅ := Finset.card_eq_zero.mp h0
      refine ⟨hA0, ?_⟩
      intro j
      have hz : A ∩ (j:↥Y).val = ∅ := by rw [hA0]; simp
      rw [hz]
      simp
    · right; left
      obtain ⟨e, he⟩ := Finset.card_eq_one.mp h1
      refine ⟨e, he, ?_⟩
      intro j
      rw [he]
      by_cases hmem : e ∈ (j:↥Y).val
      · rw [Finset.singleton_inter_of_mem hmem, Finset.card_singleton]
        simp [hmem]
      · rw [Finset.singleton_inter_of_notMem hmem, Finset.card_empty]
        simp [hmem]
  · have hbig' : A.card = n - 1 ∨ A.card = n := by omega
    rcases hbig' with hnm1 | hcardn
    · right; right; left
      have hcomp : (Finset.univ \ A).card = 1 := by
        rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin, hnm1]
        omega
      obtain ⟨e, he⟩ := Finset.card_eq_one.mp hcomp
      have hmem : e ∉ A := by
        have h1 : e ∈ (Finset.univ \ A) := by rw [he]; simp
        exact (Finset.mem_sdiff.mp h1).2
      have hE : A = Finset.univ.erase e := by
        have hsub : A ⊆ Finset.univ.erase e := by
          intro x hx
          rw [Finset.mem_erase]
          exact ⟨fun hxe => hmem (hxe ▸ hx), Finset.mem_univ x⟩
        have hc : (Finset.univ.erase e).card ≤ A.card := by
          rw [Finset.card_erase_of_mem (Finset.mem_univ e), Finset.card_univ, Fintype.card_fin]
          omega
        exact Finset.eq_of_subset_of_card_le hsub hc
      refine ⟨e, hE, ?_⟩
      intro j
      have hAB : (A ∩ (j:↥Y).val) = (j:↥Y).val.erase e := by
        rw [hE]
        ext x
        simp only [Finset.mem_inter, Finset.mem_erase, Finset.mem_univ]
        tauto
      rw [hAB]
      by_cases hmem2 : e ∈ (j:↥Y).val
      · rw [Finset.card_erase_of_mem hmem2, hYcard (j:↥Y).val j.2, Nat.cast_sub hk]
        simp [hmem2]
        ring
      · rw [Finset.erase_eq_self.mpr hmem2, hYcard (j:↥Y).val j.2]
        simp [hmem2]
    · right; right; right
      have hU : A = Finset.univ := Finset.eq_univ_of_card A (by rw [hcardn, Fintype.card_fin])
      refine ⟨hU, ?_⟩
      intro j
      rw [hU, Finset.univ_inter, hYcard (j:↥Y).val j.2]


/- 辅助：子集求和的内外交换形式 -/
private lemma sum_filter_indicator {α : Type} [DecidableEq α] (S B : Finset α) (f : α → ℝ) :
    Finset.sum S (fun e => f e * (if e ∈ B then (1:ℝ) else 0))
      = Finset.sum (S.filter (fun e => e ∈ B)) f := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e _
  by_cases h : e ∈ B <;> simp [h]

private lemma sum_filter_indicator' {α : Type} [DecidableEq α] (B S : Finset α) (f : α → ℝ) :
    Finset.sum B (fun e => (if e ∈ S then f e else 0))
      = Finset.sum (S.filter (fun e => e ∈ B)) f := by
  conv_lhs => rw [← Finset.sum_filter]
  congr 1
  ext e
  simp only [Finset.mem_filter]
  exact and_comm

/-- 关键引理：单坐标函数之差在列族上的限制线性无关。 -/
private lemma chi_diff_indep {n k : ℕ} (Y : Finset (Finset (Fin n)))
    (hk : 2 ≤ k) (hkn : k + 2 ≤ n)
    (huniq : ∀ (w : Fin n → ℝ) (c : ℝ), (∀ B ∈ Y, Finset.sum B w = c) →
      ∀ B ∈ (Finset.univ : Finset (Fin n)).powersetCard k, Finset.sum B w = c)
    (S : Finset (Fin n)) (e0 : Fin n) (he0 : e0 ∈ S) (lam : Fin n → ℝ)
    (hlam : ∀ e, e ∉ S → lam e = 0)
    (hrel : ∀ (B : Finset (Fin n)) (hB : B ∈ Y),
      (Finset.sum S (fun e => lam e * ((if e ∈ B then (1:ℝ) else 0)
        - (if e0 ∈ B then (1:ℝ) else 0)))) = 0)
    {e : Fin n} (he : e ∈ S) (hne : e ≠ e0) : lam e = 0 := by
  classical
  set T : ℝ := Finset.sum S lam with hT
  set w : Fin n → ℝ := fun x => (if x ∈ S then lam x else 0) - (if x = e0 then T else 0) with hw
  -- w 在 S\{e0} 上等于 lam
  have hwS : ∀ x, x ∈ S → x ≠ e0 → w x = lam x := by
    intro x hx hxe
    simp [hw, hx, hxe]
  -- w 在 S 外（且非 e0）为零
  have hwOut : ∀ x, x ∉ S → x ≠ e0 → w x = 0 := by
    intro x hx hxe
    simp [hw, hx, hxe]
  -- 关键：rel 与 w 的求和关系
  have hkey : ∀ (B : Finset (Fin n)) (hB : B ∈ Y), Finset.sum B w = 0 := by
    intro B hB
    have hrelB := hrel B hB
    -- 展开 LHS 为两个和
    have hexp : Finset.sum S (fun e => lam e * ((if e ∈ B then (1:ℝ) else 0)
        - (if e0 ∈ B then (1:ℝ) else 0)))
        = Finset.sum (S.filter (fun e => e ∈ B)) lam
          - (if e0 ∈ B then (1:ℝ) else 0) * Finset.sum S lam := by
      have hsplit : Finset.sum S (fun e => lam e * ((if e ∈ B then (1:ℝ) else 0)
          - (if e0 ∈ B then (1:ℝ) else 0)))
          = Finset.sum S (fun e => lam e * (if e ∈ B then (1:ℝ) else 0))
            - (if e0 ∈ B then (1:ℝ) else 0) * Finset.sum S lam := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro e _
        ring
      rw [hsplit, sum_filter_indicator]
    -- w 的求和
    have hwExp : Finset.sum B w = Finset.sum (S.filter (fun e => e ∈ B)) lam
          - (if e0 ∈ B then (1:ℝ) else 0) * T := by
      have h1 : Finset.sum B w = Finset.sum B (fun x => (if x ∈ S then lam x else 0))
          - Finset.sum B (fun x => (if x = e0 then T else 0)) := by
        rw [← Finset.sum_sub_distrib]
      have h2 : Finset.sum B (fun x => (if x = e0 then T else 0))
          = (if e0 ∈ B then (1:ℝ) else 0) * T := by
        rw [Finset.sum_ite_eq']
        by_cases h : e0 ∈ B
        · simp [h]
        · simp [h]
      have h3 : Finset.sum B (fun x => (if x ∈ S then lam x else 0))
          = Finset.sum (S.filter (fun e => e ∈ B)) lam := sum_filter_indicator' B S lam
      rw [h1, h2, h3]
    rw [← hT] at hexp
    rw [hexp] at hrelB
    rw [hwExp, hrelB]
  -- 提升到全部 k-子集
  have hlayer : ∀ B ∈ (Finset.univ : Finset (Fin n)).powersetCard k, Finset.sum B w = 0 := by
    refine huniq w 0 ?_
    intro B hB
    exact hkey B hB
  -- 构造 k-子集的辅助
  have hk_sub : ∀ (T' : Finset (Fin n)) (x : Fin n), x ∈ T' → k ≤ T'.card →
      ∃ B, B ⊆ T' ∧ B.card = k ∧ x ∈ B := by
    intro T' x hx hc
    have h1 : k - 1 ≤ (T'.erase x).card := by
      rw [Finset.card_erase_of_mem hx]; omega
    obtain ⟨U, hUsub, hUcard⟩ := Finset.exists_subset_card_eq h1
    refine ⟨insert x U, ?_, ?_, Finset.mem_insert_self x U⟩
    · intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hyU
      · exact hx
      · exact Finset.mem_of_mem_erase (hUsub hyU)
    · have hxU : x ∉ U := by
        intro hcon
        have hmem := hUsub hcon
        simp only [Finset.mem_erase] at hmem
        exact hmem.1 rfl
      rw [Finset.card_insert_of_notMem hxU, hUcard]
      omega
  -- 主论证：分「S 外有元素」与「S = univ」两案
  by_cases hout : ∃ f : Fin n, f ∉ S
  · obtain ⟨f, hfS⟩ := hout
    have hfe0 : f ≠ e0 := fun h => hfS (h ▸ he0)
    -- T' = univ \ {e0, f}
    have hTcard : k ≤ (((Finset.univ : Finset (Fin n)).erase e0).erase f).card := by
      have h1 : ((Finset.univ : Finset (Fin n)).erase e0).card = n - 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ e0), Finset.card_univ, Fintype.card_fin]
      have h2 : f ∈ (Finset.univ : Finset (Fin n)).erase e0 := by
        simp only [Finset.mem_erase, Finset.mem_univ, and_true]
        exact hfe0
      rw [Finset.card_erase_of_mem h2, h1]
      omega
    have heT : e ∈ ((Finset.univ : Finset (Fin n)).erase e0).erase f := by
      simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      exact ⟨fun h => hfS (h ▸ he), hne⟩
    obtain ⟨B, hBsub, hBcard, heB⟩ := hk_sub _ e heT hTcard
    -- B' = insert f (B.erase e)
    have hfe : f ∉ B.erase e := by
      intro hcon
      have h1 : f ∈ B := Finset.mem_of_mem_erase hcon
      have h2 := hBsub h1
      simp only [Finset.mem_erase] at h2
      exact h2.1 rfl
    set B' := insert f (B.erase e) with hB'def
    have hB'card : B'.card = k := by
      rw [hB'def, Finset.card_insert_of_notMem hfe, Finset.card_erase_of_mem heB, hBcard]
      omega
    have hB'mem : B' ∈ (Finset.univ : Finset (Fin n)).powersetCard k := by
      rw [Finset.mem_powersetCard]
      exact ⟨Finset.subset_univ _, hB'card⟩
    have hBmem : B ∈ (Finset.univ : Finset (Fin n)).powersetCard k := by
      rw [Finset.mem_powersetCard]
      exact ⟨Finset.subset_univ _, hBcard⟩
    -- 两个和都为零
    have hsumB : Finset.sum B w = 0 := hlayer B hBmem
    have hsumB' : Finset.sum B' w = 0 := hlayer B' hB'mem
    -- sum B' = w f + sum (B.erase e)
    have hsplitB' : Finset.sum B' w = w f + Finset.sum (B.erase e) w := by
      rw [hB'def, Finset.sum_insert hfe]
    have hsplitB : Finset.sum B w = w e + Finset.sum (B.erase e) w := by
      rw [← Finset.add_sum_erase B w heB]
    have hwe : w e = lam e := hwS e he hne
    have hwf : w f = 0 := hwOut f hfS hfe0
    rw [hsplitB] at hsumB
    rw [hsplitB'] at hsumB'
    rw [hwe] at hsumB
    rw [hwf] at hsumB'
    linarith
  · -- S = univ
    push Not at hout
    have hSuniv : S = Finset.univ := Finset.eq_univ_of_forall hout
    have hwlam : ∀ x, x ≠ e0 → w x = lam x := by
      intro x hx
      exact hwS x (by rw [hSuniv]; exact Finset.mem_univ x) hx
    -- 先证 S\{e0} 上 lam 相等
    have hpair : ∀ e₁ e₂ : Fin n, e₁ ≠ e0 → e₂ ≠ e0 → e₁ ≠ e₂ → lam e₁ = lam e₂ := by
      intro e₁ e₂ h1 h2 h12
      have hTcard : k ≤ (((Finset.univ : Finset (Fin n)).erase e0).erase e₂).card := by
        have h1 : ((Finset.univ : Finset (Fin n)).erase e0).card = n - 1 := by
          rw [Finset.card_erase_of_mem (Finset.mem_univ e0), Finset.card_univ, Fintype.card_fin]
        have h2' : e₂ ∈ (Finset.univ : Finset (Fin n)).erase e0 := by
          simp only [Finset.mem_erase, Finset.mem_univ, and_true]
          exact h2
        rw [Finset.card_erase_of_mem h2', h1]
        omega
      have he1T : e₁ ∈ ((Finset.univ : Finset (Fin n)).erase e0).erase e₂ := by
        simp only [Finset.mem_erase, Finset.mem_univ, and_true]
        exact ⟨h12, h1⟩
      obtain ⟨B, hBsub, hBcard, he1B⟩ := hk_sub _ e₁ he1T hTcard
      have he2B : e₂ ∉ B := by
        intro hcon
        have h2 : e₂ ∈ ((Finset.univ : Finset (Fin n)).erase e0).erase e₂ := hBsub hcon
        exact (Finset.mem_erase.mp h2).1 rfl
      set B' := insert e₂ (B.erase e₁) with hB'def
      have he2not : e₂ ∉ B.erase e₁ := fun h => he2B (Finset.mem_of_mem_erase h)
      have hB'card : B'.card = k := by
        rw [hB'def, Finset.card_insert_of_notMem he2not, Finset.card_erase_of_mem he1B, hBcard]
        omega
      have hB'mem : B' ∈ (Finset.univ : Finset (Fin n)).powersetCard k := by
        rw [Finset.mem_powersetCard]
        exact ⟨Finset.subset_univ _, hB'card⟩
      have hBmem : B ∈ (Finset.univ : Finset (Fin n)).powersetCard k := by
        rw [Finset.mem_powersetCard]
        exact ⟨Finset.subset_univ _, hBcard⟩
      have hsumB : Finset.sum B w = 0 := hlayer B hBmem
      have hsumB' : Finset.sum B' w = 0 := hlayer B' hB'mem
      have hsplitB' : Finset.sum B' w = w e₂ + Finset.sum (B.erase e₁) w := by
        rw [hB'def, Finset.sum_insert he2not]
      have hsplitB : Finset.sum B w = w e₁ + Finset.sum (B.erase e₁) w := by
        rw [← Finset.add_sum_erase B w he1B]
      rw [hsplitB] at hsumB
      rw [hsplitB'] at hsumB'
      rw [hwlam e₁ h1] at hsumB
      rw [hwlam e₂ h2] at hsumB'
      linarith
    -- 取一个大小 k 且不含 e0 的集合算总和
    have hn2 : k ≤ ((Finset.univ : Finset (Fin n)).erase e0).card := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ e0)]
      simp only [Finset.card_univ, Fintype.card_fin]; omega
    obtain ⟨B0, hB0sub, hB0card, heB0⟩ := hk_sub _ e
      (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ e⟩) hn2
    have hB0mem : B0 ∈ (Finset.univ : Finset (Fin n)).powersetCard k := by
      rw [Finset.mem_powersetCard]
      exact ⟨Finset.subset_univ _, hB0card⟩
    have hsum0 : Finset.sum B0 w = 0 := hlayer B0 hB0mem
    -- 每个 B0 中元素的 lam 都等于 lam e
    have hlamEq : ∀ x ∈ B0, lam x = lam e := by
      intro x hx
      have hxne0 : x ≠ e0 := by
        intro hcon
        have := hB0sub hx
        simp only [Finset.mem_erase] at this
        exact this.1 hcon
      by_cases hxe : x = e
      · rw [hxe]
      · exact (hpair x e hxne0 hne hxe).symm ▸ rfl
    have hsumlam : Finset.sum B0 lam = (k : ℝ) * lam e := by
      rw [Finset.sum_congr rfl hlamEq]
      rw [Finset.sum_const, hB0card, nsmul_eq_mul]
    have hsumw : Finset.sum B0 w = Finset.sum B0 lam := by
      apply Finset.sum_congr rfl
      intro x hx
      have hxne0 : x ≠ e0 := by
        intro hcon
        have := hB0sub hx
        simp only [Finset.mem_erase] at this
        exact this.1 hcon
      exact hwlam x hxne0
    rw [hsumw, hsumlam] at hsum0
    have hkpos : (0:ℝ) < (k : ℝ) := by
      have : 0 < k := by omega
      exact_mod_cast this
    nlinarith

/-- (d) 秩下界：若 S 中每个坐标 e 都有一行等于 c*chi_e + d（c≠0），则 |S| ≤ rank+1。 -/
private lemma rank_ge_of_rows {n k m : ℕ} {Y : Finset (Finset (Fin n))}
    (hk : 2 ≤ k) (hkn : k + 2 ≤ n)
    (huniq : ∀ (w : Fin n → ℝ) (c : ℝ), (∀ B ∈ Y, Finset.sum B w = c) →
      ∀ B ∈ (Finset.univ : Finset (Fin n)).powersetCard k, Finset.sum B w = c)
    (M : Matrix (Fin m) (↥Y) ℝ)
    (S : Finset (Fin n)) (e0 : Fin n) (he0 : e0 ∈ S)
    (c d : ℝ) (hc : c ≠ 0)
    (idx : Fin n → Fin m)
    (hrow : ∀ e ∈ S, ∀ j : ↥Y,
      M (idx e) j = c * (if e ∈ (j:↥Y).val then (1:ℝ) else 0) + d) :
    S.card ≤ M.rank + 1 := by
  classical
  set v : ↥(S.erase e0) → (↥Y → ℝ) := fun e => M.row (idx e.val) - M.row (idx e0) with hv
  have hvval : ∀ (e : ↥(S.erase e0)) (j : ↥Y),
      v e j = c * ((if e.val ∈ (j:↥Y).val then (1:ℝ) else 0)
        - (if e0 ∈ (j:↥Y).val then (1:ℝ) else 0)) := by
    intro e j
    have heS : e.val ∈ S := (Finset.mem_erase.mp e.property).2
    have h1 := hrow e.val heS j
    have h2 := hrow e0 he0 j
    simp only [hv, Pi.sub_apply, Matrix.row, h1, h2]
    ring
  have hLI : LinearIndependent ℝ v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    set lam : Fin n → ℝ := fun x =>
      if h : x ∈ S ∧ x ≠ e0 then c * g ⟨x, Finset.mem_erase.mpr ⟨h.2, h.1⟩⟩ else 0
      with hlamdef
    have hlamOut : ∀ x, x ∉ S → lam x = 0 := by
      intro x hx
      simp only [hlamdef]
      exact dif_neg (fun h => hx h.1)
    have he0zero : lam e0 = 0 := by
      simp only [hlamdef]
      exact dif_neg (fun h => h.2 rfl)
    have hlamval : ∀ (e : ↥(S.erase e0)), lam e.val = c * g e := by
      intro e
      have heS : e.val ∈ S := (Finset.mem_erase.mp e.property).2
      have hene : e.val ≠ e0 := (Finset.mem_erase.mp e.property).1
      simp only [hlamdef]
      rw [dif_pos (show e.val ∈ S ∧ e.val ≠ e0 from ⟨heS, hene⟩)]
    have hrel : ∀ (B : Finset (Fin n)) (hB : B ∈ Y),
        (Finset.sum S (fun e => lam e * ((if e ∈ B then (1:ℝ) else 0)
          - (if e0 ∈ B then (1:ℝ) else 0)))) = 0 := by
      intro B hB
      have hpt := congrFun hg ⟨B, hB⟩
      rw [Finset.sum_apply] at hpt
      simp only [Pi.smul_apply, smul_eq_mul] at hpt
      have h1 : Finset.sum S (fun e => lam e * ((if e ∈ B then (1:ℝ) else 0)
          - (if e0 ∈ B then (1:ℝ) else 0)))
          = Finset.sum (S.erase e0) (fun e => lam e * ((if e ∈ B then (1:ℝ) else 0)
            - (if e0 ∈ B then (1:ℝ) else 0))) := by
        rw [← Finset.add_sum_erase S (fun e => lam e * ((if e ∈ B then (1:ℝ) else 0)
          - (if e0 ∈ B then (1:ℝ) else 0))) he0, he0zero, zero_mul, zero_add]
      rw [h1]
      rw [← Finset.sum_coe_sort (S.erase e0) (fun e => lam e * ((if e ∈ B then (1:ℝ) else 0)
            - (if e0 ∈ B then (1:ℝ) else 0)))]
      have h2 : ∀ i : ↥(S.erase e0), lam i.val * ((if (i.val) ∈ B then (1:ℝ) else 0)
            - (if e0 ∈ B then (1:ℝ) else 0)) = g i * v i ⟨B, hB⟩ := by
        intro i
        rw [hlamval i, hvval i ⟨B, hB⟩]
        ring
      rw [Finset.sum_congr rfl (fun i _ => h2 i)]
      exact hpt
    have heS : i.val ∈ S := (Finset.mem_erase.mp i.property).2
    have hene : i.val ≠ e0 := (Finset.mem_erase.mp i.property).1
    have hres := chi_diff_indep Y hk hkn huniq S e0 he0 lam hlamOut hrel heS hene
    rw [hlamval i] at hres
    exact (mul_eq_zero.mp hres).resolve_left hc
  have hcardι : Fintype.card ↥(S.erase e0) = S.card - 1 := by
    rw [Fintype.card_coe, Finset.card_erase_of_mem he0]
  have hfin : Module.finrank ℝ (Submodule.span ℝ (Set.range v)) = Fintype.card ↥(S.erase e0) :=
    finrank_span_eq_card hLI
  have hle : Submodule.span ℝ (Set.range v) ≤ Submodule.span ℝ (Set.range M.row) := by
    rw [Submodule.span_le]
    rintro _ ⟨e, rfl⟩
    exact Submodule.sub_mem _ (Submodule.subset_span ⟨idx e.val, rfl⟩)
      (Submodule.subset_span ⟨idx e0, rfl⟩)
  have hmono : Module.finrank ℝ (Submodule.span ℝ (Set.range v))
      ≤ Module.finrank ℝ (Submodule.span ℝ (Set.range M.row)) :=
    Submodule.finrank_mono hle
  have hrank := Matrix.rank_eq_finrank_span_row M
  rw [hfin, hcardι] at hmono
  rw [hrank]
  omega


/-- a = 0 时每行是常 0、常 1 或 χ_e 型。 -/
private lemma rows_of_a_zero {n k m : ℕ} {Y : Finset (Finset (Fin n))}
    {A : Fin m → Finset (Fin n)} {a : ℤ}
    (hn : 1 ≤ n) (hk : 2 ≤ k) (hYne : Y.Nonempty)
    (hYcard : ∀ B ∈ Y, B.card = k)
    (ha0 : ((a:ℤ):ℝ) = 0)
    (hM01 : ∀ (i : Fin m) (j : ↥Y),
      ((A i ∩ (j:↥Y).val).card : ℝ) - ((a:ℤ):ℝ) = 0 ∨
      ((A i ∩ (j:↥Y).val).card : ℝ) - ((a:ℤ):ℝ) = 1)
    (hclass : ∀ i : Fin m, (A i).card ≤ 1 ∨ n - 1 ≤ (A i).card) :
    ∀ i : Fin m, (∀ j : ↥Y, ((A i ∩ (j:↥Y).val).card : ℝ) - ((a:ℤ):ℝ) = 0) ∨
      (∀ j : ↥Y, ((A i ∩ (j:↥Y).val).card : ℝ) - ((a:ℤ):ℝ) = 1) ∨
      (∃ e : Fin n, ∀ j : ↥Y, ((A i ∩ (j:↥Y).val).card : ℝ) - ((a:ℤ):ℝ)
        = (if e ∈ (j:↥Y).val then (1:ℝ) else 0)) := by
  classical
  intro i
  obtain ⟨j₀, hj₀⟩ := hYne
  have hshape := row_shape hn (by omega : 1 ≤ k) hYcard (hclass i) (a := ((a:ℤ):ℝ))
  rcases hshape with ⟨hA, hval⟩ | ⟨e, hA, hval⟩ | ⟨e, hA, hval⟩ | ⟨hA, hval⟩
  · left
    intro j
    rw [hval j, ha0]; ring
  · right; right
    exact ⟨e, fun j => by rw [hval j, ha0]; ring⟩
  · -- 余单点型：行 = k - χ_e，hM01 迫使 χ_e 恒 1（且 k=2）
    right; left
    have hk2 : (2:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
    have hχall : ∀ j : ↥Y, (if e ∈ (j:↥Y).val then (1:ℝ) else 0) = 1 := by
      intro j
      have p := hM01 i j
      rw [hval j, ha0] at p
      by_contra h
      have h0 : (if e ∈ (j:↥Y).val then (1:ℝ) else 0) = 0 := by
        by_cases hm : e ∈ (j:↥Y).val
        · simp [hm] at h
        · simp [hm]
      rw [h0] at p
      rcases p with p | p <;> linarith
    intro j
    have p := hM01 i j
    rw [hval j, ha0, hχall j] at p
    rw [hval j, ha0, hχall j]
    rcases p with p | p <;> linarith
  · -- 全集型：行 = k，与 hM01 矛盾
    exfalso
    have p := hM01 i ⟨j₀, hj₀⟩
    rw [hval ⟨j₀, hj₀⟩, ha0] at p
    have hk2 : (2:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
    rcases p with p | p <;> linarith

/-- a = k-1 时每行是常 0、常 1 或 1-χ_e 型。 -/
private lemma rows_of_a_km1 {n k m : ℕ} {Y : Finset (Finset (Fin n))}
    {A : Fin m → Finset (Fin n)} {a : ℤ}
    (hn : 1 ≤ n) (hk : 2 ≤ k) (hYne : Y.Nonempty)
    (hYcard : ∀ B ∈ Y, B.card = k)
    (ha : ((a:ℤ):ℝ) = (k:ℝ) - 1)
    (hM01 : ∀ (i : Fin m) (j : ↥Y),
      ((A i ∩ (j:↥Y).val).card : ℝ) - ((a:ℤ):ℝ) = 0 ∨
      ((A i ∩ (j:↥Y).val).card : ℝ) - ((a:ℤ):ℝ) = 1)
    (hclass : ∀ i : Fin m, (A i).card ≤ 1 ∨ n - 1 ≤ (A i).card) :
    ∀ i : Fin m, (∀ j : ↥Y, ((A i ∩ (j:↥Y).val).card : ℝ) - ((a:ℤ):ℝ) = 0) ∨
      (∀ j : ↥Y, ((A i ∩ (j:↥Y).val).card : ℝ) - ((a:ℤ):ℝ) = 1) ∨
      (∃ e : Fin n, ∀ j : ↥Y, ((A i ∩ (j:↥Y).val).card : ℝ) - ((a:ℤ):ℝ)
        = 1 - (if e ∈ (j:↥Y).val then (1:ℝ) else 0)) := by
  classical
  intro i
  obtain ⟨j₀, hj₀⟩ := hYne
  have hshape := row_shape hn (by omega : 1 ≤ k) hYcard (hclass i) (a := ((a:ℤ):ℝ))
  rcases hshape with ⟨hA, hval⟩ | ⟨e, hA, hval⟩ | ⟨e, hA, hval⟩ | ⟨hA, hval⟩
  · -- ∅ 型：行 = -(k-1)，与 hM01 矛盾
    exfalso
    have p := hM01 i ⟨j₀, hj₀⟩
    rw [hval ⟨j₀, hj₀⟩, ha] at p
    have hk2 : (2:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
    rcases p with p | p <;> linarith
  · -- 单点型：行 = χ_e - (k-1)；若 χ_e 恒 1 且 k=2 则为常 0，否则矛盾
    have hk2 : (2:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
    by_cases hcase : ∀ j : ↥Y, (if e ∈ (j:↥Y).val then (1:ℝ) else 0) = 1
    · left
      intro j
      have p := hM01 i j
      rw [hval j, ha, hcase j] at p
      rw [hval j, ha, hcase j]
      rcases p with p | p <;> linarith
    · -- χ_e 不恒 1：取 χ=0 的列，此时行值 = -(k-1) ≤ -1，矛盾
      exfalso
      push Not at hcase
      obtain ⟨j, hj⟩ := hcase
      have h0 : (if e ∈ (j:↥Y).val then (1:ℝ) else 0) = 0 := by
        by_cases hm : e ∈ (j:↥Y).val
        · simp [hm] at hj
        · simp [hm]
      have p := hM01 i j
      rw [hval j, ha, h0] at p
      rcases p with p | p <;> linarith
  · -- 余单点型：行 = 1 - χ_e
    right; right
    exact ⟨e, fun j => by rw [hval j, ha]; ring⟩
  · -- 全集型：行 = 1
    right; left
    intro j
    have p := hM01 i j
    rw [hval j, ha] at p
    rw [hval j, ha]
    rcases p with p | p <;> linarith

private lemma rectangle_counting {n m : ℕ} {Y : Finset (Finset (Fin n))}
    (M : Matrix (Fin m) (↥Y) ℝ) (S : Finset (Fin n)) (chi : Fin n → ↥Y → ℝ)
    (hrank : S.card ≤ M.rank + 1)
    (hconst : ∀ i : Fin m, (∀ j : ↥Y, M i j = 0) ∨ (∀ j : ↥Y, M i j = 1) ∨
      (∃ e : Fin n, e ∈ S ∧ ∀ j : ↥Y, M i j = chi e j))
    (htwo : ∀ e ∈ S, ∃ v₀ v₁ : ℝ, ∀ j : ↥Y, chi e j = v₀ ∨ chi e j = v₁) :
    ∃ R : Finset (Fin m), ∃ C : Finset (↥Y), ∃ v : ℝ,
      (∀ i ∈ R, ∀ j ∈ C, M i j = v) ∧
      m * Y.card ≤ 4 * (M.rank + 1) * R.card * C.card := by
  classical
  rcases Nat.eq_zero_or_pos m with hm0 | hm
  · exact ⟨∅, ∅, 0, by simp, by simp [hm0]⟩
  rcases Nat.eq_zero_or_pos Y.card with hY0 | hY
  · exact ⟨∅, ∅, 0, by simp, by simp [hY0]⟩
  by_cases hrank0 : M.rank = 0
  · have hM0 : M = 0 := by
      have hspan : Submodule.span ℝ (Set.range M.row) = ⊥ := by
        have hfin : Module.finrank ℝ ↥(Submodule.span ℝ (Set.range M.row)) = 0 := by
          have h := Matrix.rank_eq_finrank_span_row M
          rw [hrank0] at h
          exact h.symm
        exact Submodule.finrank_eq_zero.mp hfin
      ext i j
      have hmem : M.row i ∈ Submodule.span ℝ (Set.range M.row) :=
        Submodule.subset_span ⟨i, rfl⟩
      rw [hspan] at hmem
      have hzero : M.row i = 0 := by simpa using hmem
      simpa using congrFun hzero j
    refine ⟨Finset.univ, Finset.univ, 0, ?_, ?_⟩
    · intro i _ j _; rw [hM0]; simp
    · have hle : m * Y.card ≤ 4 * (m * Y.card) := Nat.le_mul_of_pos_left _ (by norm_num)
      calc m * Y.card ≤ 4 * (m * Y.card) := hle
        _ = 4 * (M.rank + 1) * (Finset.univ : Finset (Fin m)).card * (Finset.univ : Finset ↥Y).card := by
            rw [hrank0, Finset.card_univ, Finset.card_univ, Fintype.card_coe, Fintype.card_fin]
            ring
  have hrankpos : 1 ≤ M.rank := Nat.one_le_iff_ne_zero.mpr hrank0
  let good : Fin m → Option (Option (Fin n)) → Prop := fun i l =>
    match l with
    | none => ∀ j : ↥Y, M i j = 0
    | some none => ∀ j : ↥Y, M i j = 1
    | some (some e) => e ∈ S ∧ ∀ j : ↥Y, M i j = chi e j
  have hexists : ∀ i : Fin m, ∃ l, good i l := by
    intro i
    rcases hconst i with h0 | h1 | ⟨e, heS, he⟩
    · exact ⟨none, h0⟩
    · exact ⟨some none, h1⟩
    · exact ⟨some (some e), heS, he⟩
  let lab : Fin m → Option (Option (Fin n)) := fun i => Classical.choose (hexists i)
  have hlab : ∀ i : Fin m, good i (lab i) := fun i => Classical.choose_spec (hexists i)
  let L : Finset (Option (Option (Fin n))) := Finset.univ.image lab
  have hLabmem : ∀ i : Fin m, lab i ∈ L := fun i =>
    Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  let T0 : Finset (Option (Option (Fin n))) :=
    insert none (insert (some none) (S.image (fun e => some (some e))))
  have hLsub : L ⊆ T0 := by
    intro l hl
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hl
    rcases hi : lab i with _ | l1
    · exact Finset.mem_insert_self _ _
    · rcases h1 : l1 with _ | e
      · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
      · have hg := hlab i
        rw [hi, h1] at hg
        change e ∈ S ∧ ∀ j : ↥Y, M i j = chi e j at hg
        exact Finset.mem_insert_of_mem
          (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨e, hg.1, rfl⟩))
  have hLcard : L.card ≤ S.card + 2 := by
    have h1 : L.card ≤ T0.card := Finset.card_le_card hLsub
    have h2 : T0.card = S.card + 2 := by
      have hnone : (none : Option (Option (Fin n))) ∉
          insert (some none) (S.image (fun e => some (some e))) := by simp
      have hsome : (some none : Option (Option (Fin n))) ∉
          S.image (fun e => some (some e)) := by
        intro hmem
        obtain ⟨e, -, he⟩ := Finset.mem_image.mp hmem
        simp at he
      dsimp only [T0]
      rw [Finset.card_insert_of_notMem hnone, Finset.card_insert_of_notMem hsome,
        Finset.card_image_of_injective (f := fun e : Fin n => some (some e)) S
          (fun a b hab => by simpa only [Option.some.injEq] using hab)]
    omega
  have hLrank : L.card ≤ M.rank + 3 := by omega
  have hLne : L.Nonempty := ⟨lab ⟨0, hm⟩, hLabmem _⟩
  let F : Option (Option (Fin n)) → Finset (Fin m) := fun l =>
    Finset.univ.filter (fun i => lab i = l)
  obtain ⟨l, hlL, hlmax⟩ := Finset.exists_max_image L (fun l => (F l).card) hLne
  have hsum : ∑ l' ∈ L, (F l').card = m := by
    have h1 : ∑ l' ∈ L, (F l').card =
        ∑ l' ∈ L, ∑ i ∈ Finset.univ.filter (fun i => lab i = l'), (1:ℕ) := by
      apply Finset.sum_congr rfl
      intro l' _
      exact Finset.card_eq_sum_ones _
    rw [h1, Finset.sum_fiberwise_eq_sum_filter]
    have hfilter : (Finset.univ.filter (fun i : Fin m => lab i ∈ L)) = Finset.univ := by
      apply Finset.filter_true_of_mem
      intro i _
      exact hLabmem i
    rw [hfilter, ← Finset.card_eq_sum_ones, Finset.card_univ, Fintype.card_fin]
  have hm_le : m ≤ L.card * (F l).card := by
    have hle : ∑ l' ∈ L, (F l').card ≤ ∑ l' ∈ L, (F l).card :=
      Finset.sum_le_sum (fun l' hl' => hlmax l' hl')
    have hconst : ∑ l' ∈ L, (F l).card = L.card * (F l).card := by
      rw [Finset.sum_const, nsmul_eq_mul]
      simp
    rw [hsum, hconst] at hle
    exact hle
  rcases l with _ | l1
  · refine ⟨F none, Finset.univ, 0, ?_, ?_⟩
    · intro i hi j hj
      have hi' : lab i = none := by
        have h := (Finset.mem_filter.mp hi).2
        simpa [F] using h
      have hg := hlab i
      rw [hi'] at hg
      exact hg j
    · have hle2 : m * Y.card ≤ (L.card * (F none).card) * Y.card :=
        Nat.mul_le_mul_right _ hm_le
      calc m * Y.card ≤ (L.card * (F none).card) * Y.card := hle2
        _ ≤ ((M.rank + 3) * (F none).card) * Y.card :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hLrank)
        _ ≤ (4 * (M.rank + 1) * (F none).card) * Y.card := by
            have h43 : M.rank + 3 ≤ 4 * (M.rank + 1) := by omega
            exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h43)
        _ = 4 * (M.rank + 1) * (F none).card * (Finset.univ : Finset ↥Y).card := by
            rw [Finset.card_univ, Fintype.card_coe]
  rcases l1 with _ | e
  · refine ⟨F (some none), Finset.univ, 1, ?_, ?_⟩
    · intro i hi j hj
      have hi' : lab i = some none := by
        have h := (Finset.mem_filter.mp hi).2
        simpa [F] using h
      have hg := hlab i
      rw [hi'] at hg
      exact hg j
    · have hle2 : m * Y.card ≤ (L.card * (F (some none)).card) * Y.card :=
        Nat.mul_le_mul_right _ hm_le
      calc m * Y.card ≤ (L.card * (F (some none)).card) * Y.card := hle2
        _ ≤ ((M.rank + 3) * (F (some none)).card) * Y.card :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hLrank)
        _ ≤ (4 * (M.rank + 1) * (F (some none)).card) * Y.card := by
            have h43 : M.rank + 3 ≤ 4 * (M.rank + 1) := by omega
            exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h43)
        _ = 4 * (M.rank + 1) * (F (some none)).card * (Finset.univ : Finset ↥Y).card := by
            rw [Finset.card_univ, Fintype.card_coe]
  · obtain ⟨i0, -, hi0⟩ := Finset.mem_image.mp hlL
    have hg0 := hlab i0
    rw [hi0] at hg0
    change e ∈ S ∧ ∀ j : ↥Y, M i0 j = chi e j at hg0
    obtain ⟨v0, v1, hv⟩ := htwo e hg0.1
    let C0 : Finset ↥Y := Finset.univ.filter (fun j => chi e j = v0)
    let C1 : Finset ↥Y := Finset.univ.filter (fun j => chi e j = v1)
    have hcover : ∀ j : ↥Y, j ∈ C0 ∪ C1 := by
      intro j
      rcases hv j with h | h
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ j, h⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ j, h⟩)
    have hcard : Y.card ≤ C0.card + C1.card := by
      have h1 : (Finset.univ : Finset ↥Y).card ≤ (C0 ∪ C1).card :=
        Finset.card_le_card (fun j _ => hcover j)
      have h2 : (C0 ∪ C1).card ≤ C0.card + C1.card := Finset.card_union_le _ _
      calc Y.card = (Finset.univ : Finset ↥Y).card := by
              rw [Finset.card_univ, Fintype.card_coe]
        _ ≤ C0.card + C1.card := le_trans h1 h2
    have hchoice : Y.card ≤ 2 * C0.card ∨ Y.card ≤ 2 * C1.card := by omega
    have hi_le : ∀ i ∈ F (some (some e)), lab i = some (some e) := by
      intro i hi
      exact (Finset.mem_filter.mp hi).2
    rcases hchoice with hC | hC
    · refine ⟨F (some (some e)), C0, v0, ?_, ?_⟩
      · intro i hi j hj
        have hi' := hi_le i hi
        have hg := hlab i
        rw [hi'] at hg
        change e ∈ S ∧ ∀ j : ↥Y, M i j = chi e j at hg
        have hj' : chi e j = v0 := (Finset.mem_filter.mp hj).2
        rw [hg.2 j, hj']
      · have hle2 : m * Y.card ≤ (L.card * (F (some (some e))).card) * Y.card :=
          Nat.mul_le_mul_right _ hm_le
        calc m * Y.card ≤ (L.card * (F (some (some e))).card) * Y.card := hle2
          _ ≤ ((M.rank + 3) * (F (some (some e))).card) * Y.card :=
              Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hLrank)
          _ ≤ ((M.rank + 3) * (F (some (some e))).card) * (2 * C0.card) :=
              Nat.mul_le_mul_left _ hC
          _ ≤ (4 * (M.rank + 1) * (F (some (some e))).card) * C0.card := by
              have h43 : 2 * (M.rank + 3) ≤ 4 * (M.rank + 1) := by omega
              have hstep := Nat.mul_le_mul_right ((F (some (some e))).card * C0.card) h43
              calc ((M.rank + 3) * (F (some (some e))).card) * (2 * C0.card)
                  = (2 * (M.rank + 3)) * ((F (some (some e))).card * C0.card) := by ring
                _ ≤ (4 * (M.rank + 1)) * ((F (some (some e))).card * C0.card) := hstep
                _ = (4 * (M.rank + 1) * (F (some (some e))).card) * C0.card := by ring
    · refine ⟨F (some (some e)), C1, v1, ?_, ?_⟩
      · intro i hi j hj
        have hi' := hi_le i hi
        have hg := hlab i
        rw [hi'] at hg
        change e ∈ S ∧ ∀ j : ↥Y, M i j = chi e j at hg
        have hj' : chi e j = v1 := (Finset.mem_filter.mp hj).2
        rw [hg.2 j, hj']
      · have hle2 : m * Y.card ≤ (L.card * (F (some (some e))).card) * Y.card :=
          Nat.mul_le_mul_right _ hm_le
        calc m * Y.card ≤ (L.card * (F (some (some e))).card) * Y.card := hle2
          _ ≤ ((M.rank + 3) * (F (some (some e))).card) * Y.card :=
              Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hLrank)
          _ ≤ ((M.rank + 3) * (F (some (some e))).card) * (2 * C1.card) :=
              Nat.mul_le_mul_left _ hC
          _ ≤ (4 * (M.rank + 1) * (F (some (some e))).card) * C1.card := by
              have h43 : 2 * (M.rank + 3) ≤ 4 * (M.rank + 1) := by omega
              have hstep := Nat.mul_le_mul_right ((F (some (some e))).card * C1.card) h43
              calc ((M.rank + 3) * (F (some (some e))).card) * (2 * C1.card)
                  = (2 * (M.rank + 3)) * ((F (some (some e))).card * C1.card) := by ring
                _ ≤ (4 * (M.rank + 1)) * ((F (some (some e))).card * C1.card) := hstep
                _ = (4 * (M.rank + 1) * (F (some (some e))).card) * C1.card := by ring


/-- 由行结构造坐标集 S 并给秩下界。 -/
private lemma rank_and_S {n k m : ℕ} {Y : Finset (Finset (Fin n))}
    (hk : 2 ≤ k) (hkn : k + 2 ≤ n)
    (huniq' : ∀ (w : Fin n → ℝ) (c : ℝ), (∀ B ∈ Y, Finset.sum B w = c) →
      ∀ B ∈ (Finset.univ : Finset (Fin n)).powersetCard k, Finset.sum B w = c)
    (M : Matrix (Fin m) (↥Y) ℝ) (hmpos : 0 < m)
    (c d : ℝ) (hc : c ≠ 0)
    (hrows : ∀ i : Fin m,
      (∀ j : ↥Y, M i j = 0) ∨ (∀ j : ↥Y, M i j = 1) ∨
      (∃ e : Fin n, ∀ j : ↥Y, M i j = c * (if e ∈ (j:↥Y).val then (1:ℝ) else 0) + d)) :
    ∃ S : Finset (Fin n), S.card ≤ M.rank + 1 ∧
      (∀ i : Fin m, (∀ j : ↥Y, M i j = 0) ∨ (∀ j : ↥Y, M i j = 1) ∨
        (∃ e : Fin n, e ∈ S ∧ ∀ j : ↥Y,
          M i j = c * (if e ∈ (j:↥Y).val then (1:ℝ) else 0) + d)) := by
  classical
  set S : Finset (Fin n) := Finset.univ.filter
    (fun e => ∃ i : Fin m, ∀ j : ↥Y, M i j = c * (if e ∈ (j:↥Y).val then (1:ℝ) else 0) + d)
    with hS
  have hconst : ∀ i : Fin m, (∀ j : ↥Y, M i j = 0) ∨ (∀ j : ↥Y, M i j = 1) ∨
      (∃ e : Fin n, e ∈ S ∧ ∀ j : ↥Y,
        M i j = c * (if e ∈ (j:↥Y).val then (1:ℝ) else 0) + d) := by
    intro i
    rcases hrows i with h | h | ⟨e, he⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · refine Or.inr (Or.inr ⟨e, ?_, he⟩)
      rw [hS]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨i, he⟩
  refine ⟨S, ?_, hconst⟩
  by_cases hSne : S = ∅
  · rw [hSne]; simp
  · obtain ⟨e0, he0⟩ := Finset.nonempty_iff_ne_empty.mpr hSne
    set idx : Fin n → Fin m := fun e =>
      if h : ∃ i : Fin m, ∀ j : ↥Y, M i j = c * (if e ∈ (j:↥Y).val then (1:ℝ) else 0) + d
      then Classical.choose h else ⟨0, hmpos⟩ with hidx
    have hidxval : ∀ e ∈ S, ∀ j : ↥Y,
        M (idx e) j = c * (if e ∈ (j:↥Y).val then (1:ℝ) else 0) + d := by
      intro e he j
      have h : ∃ i : Fin m, ∀ j : ↥Y,
          M i j = c * (if e ∈ (j:↥Y).val then (1:ℝ) else 0) + d := by
        rw [hS] at he
        simpa using he
      have hidxe : idx e = Classical.choose h := by
        rw [hidx]
        exact dif_pos h
      rw [hidxe]
      exact Classical.choose_spec h j
    have := rank_ge_of_rows hk hkn huniq' M S e0 he0 c d hc idx hidxval
    exact this


theorem PEqualNP.Outside.L_log_rank_large_rectangle :
    ∀ (n k m : ℕ) (A : Fin m → Finset (Fin n)) (Y : Finset (Finset (Fin n))) (a : ℤ), 2 ≤ k → k+2 ≤ n → let layer := (Finset.univ : Finset (Fin n)).powersetCard k; let adj := fun (A B : Finset (Fin n)) (a : ℤ) => ((A ∩ B).card : ℤ) = a ∨ ((A ∩ B).card : ℤ) = a+1; let detects := fun (Y : Finset (Finset (Fin n))) => ∀ A : Finset (Fin n), 2 ≤ A.card → A.card + 2 ≤ n → ∀ a : ℤ, ∃ B ∈ Y, ¬ adj A B a; let lin := fun (w : Fin n → ℝ) (B : Finset (Fin n)) => Finset.sum B w; let uniqueOn := fun (Y : Finset (Finset (Fin n))) => ∀ (w : Fin n → ℝ) (c : ℝ), (∀ B ∈ Y, lin w B = c) → ∀ B ∈ layer, lin w B = c; Y.Nonempty → Y ⊆ layer → detects Y → uniqueOn Y → (∀ i, ∀ B ∈ Y, adj (A i) B a) → let M : Matrix (Fin m) (↥Y) ℝ := fun i j => (((A i ∩ j.val).card : ℝ) - (a : ℝ)); ∃ R : Finset (Fin m), ∃ C : Finset (↥Y), ∃ v : ℝ, (∀ i ∈ R, ∀ j ∈ C, M i j = v) ∧ m*Y.card ≤ 4*(M.rank+1)*R.card*C.card := by
  intro n k m A Y a hk hkn
  unfold Matrix
  dsimp only
  intro hYne hYsub hdet huniq hrow
  set M : Matrix (Fin m) (↥Y) ℝ :=
    fun i j => ((A i ∩ (j:↥Y).val).card : ℝ) - ((a:ℤ):ℝ) with hM
  classical
  have hn : 1 ≤ n := by omega
  have hYcard : ∀ B ∈ Y, B.card = k := by
    intro B hB
    have h := hYsub hB
    simp only [Finset.mem_powersetCard, Finset.mem_univ, true_and] at h
    exact h.2
  have hMval : ∀ (i : Fin m) (j : ↥Y),
      M i j = ((A i ∩ (j:↥Y).val).card : ℝ) - ((a:ℤ):ℝ) := by
    intro i j
    rw [hM]
  have hM01 : ∀ (i : Fin m) (j : ↥Y), M i j = 0 ∨ M i j = 1 := by
    intro i j
    have h := hrow i (j:↥Y) j.2
    rw [hMval]
    rcases h with h | h
    · left
      have h' : ((A i ∩ (j:↥Y).val).card : ℝ) = ((a:ℤ):ℝ) := by exact_mod_cast h
      linarith
    · right
      have h2 : ((A i ∩ (j:↥Y).val).card : ℤ) = a + 1 := h
      have h' : ((A i ∩ (j:↥Y).val).card : ℝ) = ((a + 1 : ℤ) : ℝ) := by exact_mod_cast h2
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
  have huniq' : ∀ (w : Fin n → ℝ) (c : ℝ), (∀ B ∈ Y, Finset.sum B w = c) →
      ∀ B ∈ (Finset.univ : Finset (Fin n)).powersetCard k, Finset.sum B w = c := by
    intro w c hw B hB
    exact huniq w c hw B hB
  by_cases hm0 : m = 0
  · subst hm0
    refine ⟨∅, ∅, 0, ?_, ?_⟩
    · intro i; exact absurd i.2 (by simp)
    · simp
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
  have hchi_two : ∀ (c d : ℝ) (e : Fin n), ∃ v₀ v₁ : ℝ, ∀ j : ↥Y,
      c * (if e ∈ (j:↥Y).val then (1:ℝ) else 0) + d = v₀ ∨
      c * (if e ∈ (j:↥Y).val then (1:ℝ) else 0) + d = v₁ := by
    intro c d e
    refine ⟨d, c + d, fun j => ?_⟩
    by_cases h : e ∈ (j:↥Y).val <;> simp [h]
  by_cases hex : ∃ i : Fin m, (¬∀ j : ↥Y, M i j = 0) ∧ (¬∀ j : ↥Y, M i j = 1)
  · obtain ⟨i0, hi0⟩ := hex
    have hsh := row_shape hn (by omega : 1 ≤ k) hYcard (hclass i0) (a := ((a:ℤ):ℝ))
    rcases hsh with ⟨hA, hval⟩ | ⟨e, hA, hval⟩ | ⟨e, hA, hval⟩ | ⟨hA, hval⟩
    · -- 空集型
      exfalso
      obtain ⟨j0, hj0⟩ := hYne
      have hconst : ∀ j : ↥Y, M i0 j = M i0 ⟨j0, hj0⟩ := by
        intro j
        rw [hMval, hMval, hval j, hval ⟨j0, hj0⟩]
      rcases hM01 i0 ⟨j0, hj0⟩ with h | h
      · exact hi0.1 (fun j => by rw [hconst j, h])
      · exact hi0.2 (fun j => by rw [hconst j, h])
    · -- 单点型
      have hne : ∃ j1 j2 : ↥Y, M i0 j1 ≠ M i0 j2 := by
        by_contra hcon
        push Not at hcon
        obtain ⟨j0, hj0⟩ := hYne
        rcases hM01 i0 ⟨j0, hj0⟩ with h | h
        · exact hi0.1 (fun j => by rw [hcon j ⟨j0, hj0⟩, h])
        · exact hi0.2 (fun j => by rw [hcon j ⟨j0, hj0⟩, h])
      obtain ⟨j1, j2, hdiff⟩ := hne
      have hchi : (if e ∈ (j1:↥Y).val then (1:ℝ) else 0)
          ≠ (if e ∈ (j2:↥Y).val then (1:ℝ) else 0) := by
        intro hc
        apply hdiff
        rw [hMval, hMval, hval j1, hval j2, hc]
      have hchi1 : (if e ∈ (j1:↥Y).val then (1:ℝ) else 0) = 0 ∨
          (if e ∈ (j1:↥Y).val then (1:ℝ) else 0) = 1 := by
        by_cases h : e ∈ (j1:↥Y).val <;> simp [h]
      have hchi2 : (if e ∈ (j2:↥Y).val then (1:ℝ) else 0) = 0 ∨
          (if e ∈ (j2:↥Y).val then (1:ℝ) else 0) = 1 := by
        by_cases h : e ∈ (j2:↥Y).val <;> simp [h]
      have ha0R : ((a:ℤ):ℝ) = 0 := by
        have p1 := hM01 i0 j1
        have p2 := hM01 i0 j2
        rw [hMval, hval j1] at p1
        rw [hMval, hval j2] at p2
        rcases hchi1 with h1 | h1 <;> rcases hchi2 with h2 | h2
        · exact absurd (h1.trans h2.symm) hchi
        · rw [h1] at p1; rw [h2] at p2
          rcases p1 with p1 | p1 <;> rcases p2 with p2 | p2 <;> linarith
        · rw [h1] at p1; rw [h2] at p2
          rcases p1 with p1 | p1 <;> rcases p2 with p2 | p2 <;> linarith
        · exact absurd (h1.trans h2.symm) hchi
      have hrows0 := rows_of_a_zero hn hk hYne hYcard ha0R hM01 hclass
      have hrows : ∀ i : Fin m, (∀ j : ↥Y, M i j = 0) ∨ (∀ j : ↥Y, M i j = 1) ∨
          (∃ e : Fin n, ∀ j : ↥Y,
            M i j = (1:ℝ) * (if e ∈ (j:↥Y).val then (1:ℝ) else 0) + 0) := by
        intro i
        rcases hrows0 i with h | h | ⟨e, he⟩
        · exact Or.inl (fun j => by rw [hMval, h j])
        · exact Or.inr (Or.inl (fun j => by rw [hMval, h j]))
        · exact Or.inr (Or.inr ⟨e, fun j => by rw [hMval, he j]; ring⟩)
      obtain ⟨S, hrank, hconst⟩ := rank_and_S hk hkn huniq' M hmpos 1 0 (by norm_num) hrows
      exact rectangle_counting M S
        (fun e j => (1:ℝ) * (if e ∈ (j:↥Y).val then (1:ℝ) else 0) + 0)
        hrank hconst (fun e _ => hchi_two 1 0 e)
    · -- 余单点型
      have hne : ∃ j1 j2 : ↥Y, M i0 j1 ≠ M i0 j2 := by
        by_contra hcon
        push Not at hcon
        obtain ⟨j0, hj0⟩ := hYne
        rcases hM01 i0 ⟨j0, hj0⟩ with h | h
        · exact hi0.1 (fun j => by rw [hcon j ⟨j0, hj0⟩, h])
        · exact hi0.2 (fun j => by rw [hcon j ⟨j0, hj0⟩, h])
      obtain ⟨j1, j2, hdiff⟩ := hne
      have hchi : (if e ∈ (j1:↥Y).val then (1:ℝ) else 0)
          ≠ (if e ∈ (j2:↥Y).val then (1:ℝ) else 0) := by
        intro hc
        apply hdiff
        rw [hMval, hMval, hval j1, hval j2, hc]
      have hchi1 : (if e ∈ (j1:↥Y).val then (1:ℝ) else 0) = 0 ∨
          (if e ∈ (j1:↥Y).val then (1:ℝ) else 0) = 1 := by
        by_cases h : e ∈ (j1:↥Y).val <;> simp [h]
      have hchi2 : (if e ∈ (j2:↥Y).val then (1:ℝ) else 0) = 0 ∨
          (if e ∈ (j2:↥Y).val then (1:ℝ) else 0) = 1 := by
        by_cases h : e ∈ (j2:↥Y).val <;> simp [h]
      have haR : ((a:ℤ):ℝ) = (k:ℝ) - 1 := by
        have p1 := hM01 i0 j1
        have p2 := hM01 i0 j2
        rw [hMval, hval j1] at p1
        rw [hMval, hval j2] at p2
        rcases hchi1 with h1 | h1 <;> rcases hchi2 with h2 | h2
        · exact absurd (h1.trans h2.symm) hchi
        · rw [h1] at p1; rw [h2] at p2
          rcases p1 with p1 | p1 <;> rcases p2 with p2 | p2 <;> linarith
        · rw [h1] at p1; rw [h2] at p2
          rcases p1 with p1 | p1 <;> rcases p2 with p2 | p2 <;> linarith
        · exact absurd (h1.trans h2.symm) hchi
      have hrows0 := rows_of_a_km1 hn hk hYne hYcard haR hM01 hclass
      have hrows : ∀ i : Fin m, (∀ j : ↥Y, M i j = 0) ∨ (∀ j : ↥Y, M i j = 1) ∨
          (∃ e : Fin n, ∀ j : ↥Y,
            M i j = (-1:ℝ) * (if e ∈ (j:↥Y).val then (1:ℝ) else 0) + 1) := by
        intro i
        rcases hrows0 i with h | h | ⟨e, he⟩
        · exact Or.inl (fun j => by rw [hMval, h j])
        · exact Or.inr (Or.inl (fun j => by rw [hMval, h j]))
        · exact Or.inr (Or.inr ⟨e, fun j => by rw [hMval, he j]; ring⟩)
      obtain ⟨S, hrank, hconst⟩ := rank_and_S hk hkn huniq' M hmpos (-1) 1 (by norm_num) hrows
      exact rectangle_counting M S
        (fun e j => (-1:ℝ) * (if e ∈ (j:↥Y).val then (1:ℝ) else 0) + 1)
        hrank hconst (fun e _ => hchi_two (-1) 1 e)
    · -- 全集型
      exfalso
      obtain ⟨j0, hj0⟩ := hYne
      have hconst : ∀ j : ↥Y, M i0 j = M i0 ⟨j0, hj0⟩ := by
        intro j
        rw [hMval, hMval, hval j, hval ⟨j0, hj0⟩]
      rcases hM01 i0 ⟨j0, hj0⟩ with h | h
      · exact hi0.1 (fun j => by rw [hconst j, h])
      · exact hi0.2 (fun j => by rw [hconst j, h])
  · have hall : ∀ i : Fin m, (∀ j : ↥Y, M i j = 0) ∨ (∀ j : ↥Y, M i j = 1) := by
      intro i
      by_contra hc
      exact hex ⟨i, (fun h0 => hc (Or.inl h0)), (fun h1 => hc (Or.inr h1))⟩
    exact rectangle_counting M ∅ (fun _ _ => 0) (by simp)
      (fun i => Or.elim (hall i) (fun h => Or.inl h) (fun h => Or.inr (Or.inl h)))
      (fun e he => by simp at he)
