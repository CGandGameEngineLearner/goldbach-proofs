import Mathlib

private def sgn (b : Bool) : ℤ := if b then 1 else -1

private lemma abs_sgn (b : Bool) : |sgn b| = 1 := by
  cases b <;> simp [sgn]

private lemma exists_close_of_sum_pow_two_eq_zero
    {j : Fin 10 → ℕ} {b : Fin 10 → Bool}
    (hsum : ∑ r : Fin 10, sgn (b r) * (2 : ℤ) ^ (j r) = 0) :
    ∀ r : Fin 10, ∃ s : Fin 10, s ≠ r ∧ |(j r : ℤ) - (j s : ℤ)| < 4 := by
  intro r
  by_contra h
  push_neg at h
  let U : Finset (Fin 10) := Finset.univ.filter (fun s => j r + 4 ≤ j s)
  let D : Finset (Fin 10) := Finset.univ.filter (fun s => j s + 4 ≤ j r)
  have hrU : r ∉ U := by simp [U]
  have hrD : r ∉ D := by simp [D]
  have hUD : Disjoint U D := by
    rw [Finset.disjoint_left]
    intro s hsU hsD
    simp only [U, D, Finset.mem_filter, Finset.mem_univ, true_and] at hsU hsD
    omega
  have hcover : (Finset.univ : Finset (Fin 10)) = insert r (U ∪ D) := by
    ext s
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_union, U, D, Finset.mem_filter,
      true_and, true_iff]
    by_cases hsr : s = r
    · exact Or.inl hsr
    · right
      rcases le_abs.mp (h s hsr) with h1 | h1 <;> omega
  have hrUD : r ∉ U ∪ D := by simp [hrU, hrD]
  have hsplit : ∑ s ∈ (Finset.univ : Finset (Fin 10)), sgn (b s) * (2 : ℤ) ^ (j s) =
      sgn (b r) * (2 : ℤ) ^ (j r) +
      (∑ s ∈ U, sgn (b s) * (2 : ℤ) ^ (j s)) +
      (∑ s ∈ D, sgn (b s) * (2 : ℤ) ^ (j s)) := by
    rw [hcover, Finset.sum_insert hrUD, Finset.sum_union hUD]
    ring
  set A : ℤ := ∑ s ∈ U, sgn (b s) * (2 : ℤ) ^ (j s)
  set Bsum : ℤ := sgn (b r) * (2 : ℤ) ^ (j r) + ∑ s ∈ D, sgn (b s) * (2 : ℤ) ^ (j s)
  have hAB : Bsum = -A := by linarith
  have hdvdA : ((2 : ℤ) ^ (j r + 4)) ∣ A := by
    apply Finset.dvd_sum
    intro s hs
    have hs' : j r + 4 ≤ j s := (Finset.mem_filter.mp hs).2
    have hpow : ((2 : ℤ) ^ (j r + 4)) ∣ (2 : ℤ) ^ (j s) := pow_dvd_pow (2 : ℤ) hs'
    exact dvd_mul_of_dvd_right hpow (sgn (b s))
  have hdvdB : ((2 : ℤ) ^ (j r + 4)) ∣ Bsum := by
    rw [hAB]
    exact dvd_neg.mpr hdvdA
  have hDcard : D.card ≤ 9 := by
    have hsub : D ⊆ (Finset.univ : Finset (Fin 10)).erase r := by
      intro s hs
      exact Finset.mem_erase.mpr ⟨fun hsr => hrD (hsr ▸ hs), Finset.mem_univ s⟩
    calc D.card ≤ ((Finset.univ : Finset (Fin 10)).erase r).card := Finset.card_le_card hsub
      _ = 9 := by
          rw [Finset.card_erase_of_mem (Finset.mem_univ r), Finset.card_univ, Fintype.card_fin]
  have hDsum_mul : |∑ s ∈ D, sgn (b s) * (2 : ℤ) ^ (j s)| * 16 ≤ 9 * (2 : ℤ) ^ (j r) := by
    have h1 : |∑ s ∈ D, sgn (b s) * (2 : ℤ) ^ (j s)| ≤ ∑ s ∈ D, (2 : ℤ) ^ (j s) := by
      calc |∑ s ∈ D, sgn (b s) * (2 : ℤ) ^ (j s)|
          ≤ ∑ s ∈ D, |sgn (b s) * (2 : ℤ) ^ (j s)| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ s ∈ D, (2 : ℤ) ^ (j s) := by
            apply Finset.sum_congr rfl
            intro s _
            rw [abs_mul, abs_sgn, one_mul, abs_of_nonneg (by positivity)]
    have h2 : (∑ s ∈ D, (2 : ℤ) ^ (j s)) * 16 ≤ ∑ _s ∈ D, (2 : ℤ) ^ (j r) := by
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro s hs
      have hs' : j s + 4 ≤ j r := (Finset.mem_filter.mp hs).2
      calc (2 : ℤ) ^ (j s) * 16 = (2 : ℤ) ^ (j s) * (2 : ℤ) ^ 4 := by norm_num
        _ = (2 : ℤ) ^ (j s + 4) := (pow_add (2 : ℤ) (j s) 4).symm
        _ ≤ (2 : ℤ) ^ (j r) := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) hs'
    have h3 : (∑ _s ∈ D, (2 : ℤ) ^ (j r)) = (D.card : ℤ) * (2 : ℤ) ^ (j r) := by
      simp [Finset.sum_const]
    have h4 : (D.card : ℤ) * (2 : ℤ) ^ (j r) ≤ 9 * (2 : ℤ) ^ (j r) := by
      gcongr
      exact_mod_cast hDcard
    linarith
  have hpow_pos : (0 : ℤ) < (2 : ℤ) ^ (j r) := by positivity
  have hDlt : |∑ s ∈ D, sgn (b s) * (2 : ℤ) ^ (j s)| < (2 : ℤ) ^ (j r) := by linarith
  have hBne : Bsum ≠ 0 := by
    intro hB0
    have hEq : sgn (b r) * (2 : ℤ) ^ (j r) = -(∑ s ∈ D, sgn (b s) * (2 : ℤ) ^ (j s)) := by
      linarith [hB0]
    have hAbs : |sgn (b r) * (2 : ℤ) ^ (j r)| = |∑ s ∈ D, sgn (b s) * (2 : ℤ) ^ (j s)| := by
      rw [hEq, abs_neg]
    rw [abs_mul, abs_sgn, one_mul, abs_of_nonneg (le_of_lt hpow_pos)] at hAbs
    linarith
  have hBlt : |Bsum| < (2 : ℤ) ^ (j r + 4) := by
    have htri : |Bsum| ≤ |sgn (b r) * (2 : ℤ) ^ (j r)| + |∑ s ∈ D, sgn (b s) * (2 : ℤ) ^ (j s)| :=
      abs_add_le _ _
    rw [abs_mul, abs_sgn, one_mul, abs_of_nonneg (le_of_lt hpow_pos)] at htri
    have hpow4 : (2 : ℤ) ^ (j r + 4) = 16 * (2 : ℤ) ^ (j r) := by
      rw [pow_add]; ring
    linarith
  have hdvdAbs : ((2 : ℤ) ^ (j r + 4)) ∣ |Bsum| := by
    rcases le_or_gt 0 Bsum with h | h
    · rwa [abs_of_nonneg h]
    · rw [abs_of_neg h]
      exact dvd_neg.mpr hdvdB
  have hBle : (2 : ℤ) ^ (j r + 4) ≤ |Bsum| :=
    Int.le_of_dvd (abs_pos.mpr hBne) hdvdAbs
  linarith

private lemma exists_dominating_set_card_le_five
    (j : Fin 10 → ℕ)
    (hj : ∀ r : Fin 10, ∃ s : Fin 10, s ≠ r ∧ |(j r : ℤ) - (j s : ℤ)| < 4) :
    ∃ D : Finset (Fin 10), D.card ≤ 5 ∧
      ∀ r : Fin 10, ∃ s ∈ D, |(j r : ℤ) - (j s : ℤ)| < 4 := by
  classical
  let adj : Fin 10 → Fin 10 → Prop := fun a b => a ≠ b ∧ |(j a : ℤ) - (j b : ℤ)| < 4
  let Indep : Finset (Finset (Fin 10)) :=
    Finset.univ.filter (fun I => ∀ a ∈ I, ∀ b ∈ I, ¬ adj a b)
  have hEmpty : (∅ : Finset (Fin 10)) ∈ Indep := by
    simp [Indep]
  obtain ⟨I, hI_mem, hI_max⟩ := Finset.exists_max_image Indep Finset.card ⟨∅, hEmpty⟩
  have hI_indep : ∀ a ∈ I, ∀ b ∈ I, ¬ adj a b := (Finset.mem_filter.mp hI_mem).2
  have hI_dom : ∀ r : Fin 10, ∃ s ∈ I, |(j r : ℤ) - (j s : ℤ)| < 4 := by
    intro r
    by_cases hr : r ∈ I
    · exact ⟨r, hr, by rw [sub_self, abs_zero]; norm_num⟩
    · by_contra hno
      push_neg at hno
      have hins : insert r I ∈ Indep := by
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        intro a ha b hb hadj
        rcases Finset.mem_insert.mp ha with ha_eq | haI <;>
        rcases Finset.mem_insert.mp hb with hb_eq | hbI
        · rw [ha_eq, hb_eq] at hadj
          exact hadj.1 rfl
        · rw [ha_eq] at hadj
          exact absurd hadj.2 (not_lt.mpr (hno b hbI))
        · rw [hb_eq] at hadj
          have hsym : |(j r : ℤ) - (j a : ℤ)| = |(j a : ℤ) - (j r : ℤ)| := abs_sub_comm _ _
          exact absurd (hsym ▸ hadj.2) (not_lt.mpr (hno a haI))
        · exact hI_indep a haI b hbI hadj
      have hle := hI_max (insert r I) hins
      rw [Finset.card_insert_of_notMem hr] at hle
      omega
  have hIc_dom : ∀ r : Fin 10, ∃ s ∈ Iᶜ, |(j r : ℤ) - (j s : ℤ)| < 4 := by
    intro r
    by_cases hr : r ∈ Iᶜ
    · exact ⟨r, hr, by rw [sub_self, abs_zero]; norm_num⟩
    · have hrI : r ∈ I := by simpa using hr
      obtain ⟨s, hsr, hdist⟩ := hj r
      have hsIc : s ∈ Iᶜ := by
        rw [Finset.mem_compl]
        intro hsI
        exact hI_indep r hrI s hsI ⟨hsr.symm, hdist⟩
      exact ⟨s, hsIc, hdist⟩
  have hsum_card : I.card + Iᶜ.card = 10 := by
    simpa using Finset.card_add_card_compl I
  by_cases hcard : I.card ≤ 5
  · exact ⟨I, hcard, hI_dom⟩
  · exact ⟨Iᶜ, by omega, hIc_dom⟩

private lemma card_goodFor_le (L : ℕ) (hL : 1 ≤ L) (D : Finset (Fin 10)) (hD : D.card ≤ 5) :
    (Finset.univ.filter (fun j : Fin 10 → Fin L =>
      ∀ r : Fin 10, ∃ s ∈ D, |((j r).val : ℤ) - ((j s).val : ℤ)| < 4)).card
      ≤ L ^ 5 * 70 ^ 10 := by
  classical
  let S : Finset (Fin 10 → Fin L) :=
    Finset.univ.filter (fun j : Fin 10 → Fin L =>
      ∀ r : Fin 10, ∃ s ∈ D, |((j r).val : ℤ) - ((j s).val : ℤ)| < 4)
  let T := ({x : Fin 10 // x ∈ D} → Fin L) × (Fin 10 → Fin 10 × Fin 7)
  let φ : (Fin 10 → Fin L) → T := fun j =>
    (fun x => j x.1,
     fun r =>
       if h : ∃ s ∈ D, |((j r).val : ℤ) - ((j s).val : ℤ)| < 4 then
         let s := h.choose
         let hs := h.choose_spec
         (s, ⟨(((j r).val : ℤ) - ((j s).val : ℤ) + 3).toNat, by
           have hlt : |((j r).val : ℤ) - ((j s).val : ℤ)| < 4 := hs.2
           rw [abs_lt] at hlt
           have hge : 0 ≤ ((j r).val : ℤ) - ((j s).val : ℤ) + 3 := by omega
           have hlt7 : ((((j r).val : ℤ) - ((j s).val : ℤ) + 3).toNat : ℤ) < 7 := by
             rw [Int.toNat_of_nonneg hge]
             omega
           exact_mod_cast hlt7⟩)
       else (0, 0))
  have hinj : Set.InjOn φ (S : Set (Fin 10 → Fin L)) := by
    intro j₁ hj₁ j₂ hj₂ heq
    have h₁ : ∀ r : Fin 10, ∃ s ∈ D, |((j₁ r).val : ℤ) - ((j₁ s).val : ℤ)| < 4 :=
      (Finset.mem_filter.mp (Finset.mem_coe.mp hj₁)).2
    have h₂ : ∀ r : Fin 10, ∃ s ∈ D, |((j₂ r).val : ℤ) - ((j₂ s).val : ℤ)| < 4 :=
      (Finset.mem_filter.mp (Finset.mem_coe.mp hj₂)).2
    have hfst : ∀ x : {x : Fin 10 // x ∈ D}, j₁ x.1 = j₂ x.1 :=
      congrFun (congrArg Prod.fst heq)
    have hsnd : ∀ r : Fin 10, (φ j₁).2 r = (φ j₂).2 r :=
      congrFun (congrArg Prod.snd heq)
    funext r
    have hr := hsnd r
    dsimp only [φ] at hr
    rw [dif_pos (h₁ r), dif_pos (h₂ r)] at hr
    have hs_eq : (h₁ r).choose = (h₂ r).choose := congrArg Prod.fst hr
    have hd_eq : (((j₁ r).val : ℤ) - ((j₁ (h₁ r).choose).val : ℤ) + 3).toNat =
        (((j₂ r).val : ℤ) - ((j₂ (h₂ r).choose).val : ℤ) + 3).toNat :=
      congrArg (fun p => p.2.val) hr
    have hsD : (h₁ r).choose ∈ D := (h₁ r).choose_spec.1
    have hjs : j₁ (h₁ r).choose = j₂ (h₂ r).choose := by
      rw [← hs_eq]
      exact hfst ⟨(h₁ r).choose, hsD⟩
    have hlt₁ := (h₁ r).choose_spec.2
    have hlt₂ := (h₂ r).choose_spec.2
    rw [abs_lt] at hlt₁ hlt₂
    have hge₁ : 0 ≤ ((j₁ r).val : ℤ) - ((j₁ (h₁ r).choose).val : ℤ) + 3 := by omega
    have hge₂ : 0 ≤ ((j₂ r).val : ℤ) - ((j₂ (h₂ r).choose).val : ℤ) + 3 := by omega
    have hsub_eq : ((j₁ r).val : ℤ) - ((j₁ (h₁ r).choose).val : ℤ) + 3 =
        ((j₂ r).val : ℤ) - ((j₂ (h₂ r).choose).val : ℤ) + 3 := by
      rw [← Int.toNat_of_nonneg hge₁, ← Int.toNat_of_nonneg hge₂, hd_eq]
    have hjs_val : (j₁ (h₁ r).choose).val = (j₂ (h₂ r).choose).val := congrArg Fin.val hjs
    have hval : (j₁ r).val = (j₂ r).val := by omega
    exact Fin.ext hval
  have hcard_le : S.card ≤ Fintype.card T := by
    calc S.card ≤ (Finset.univ : Finset T).card :=
          Finset.card_le_card_of_injOn φ (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _)) hinj
      _ = Fintype.card T := Finset.card_univ
  have hcard_T : Fintype.card T = L ^ D.card * 70 ^ 10 := by
    simp only [T, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Fintype.card_coe]
  have hpow : L ^ D.card ≤ L ^ 5 := Nat.pow_le_pow_right (by omega : 0 < L) hD
  calc S.card ≤ Fintype.card T := hcard_le
    _ = L ^ D.card * 70 ^ 10 := hcard_T
    _ ≤ L ^ 5 * 70 ^ 10 := Nat.mul_le_mul_right _ hpow

private lemma card_zeroSum_le (L : ℕ) (hL : 1 ≤ L) :
    (Finset.univ.filter (fun f : Fin 10 → Fin L × Bool =>
      ∑ r : Fin 10, sgn (f r).2 * (2 : ℤ) ^ ((f r).1.val + 1) = 0)).card
      ≤ (2 ^ 10 * 2 ^ 10 * 70 ^ 10) * L ^ 5 := by
  let Z : Finset (Fin 10 → Fin L × Bool) :=
    Finset.univ.filter (fun f : Fin 10 → Fin L × Bool =>
      ∑ r : Fin 10, sgn (f r).2 * (2 : ℤ) ^ ((f r).1.val + 1) = 0)
  classical
  let Good : Finset (Fin 10 → Fin L) :=
    Finset.univ.filter (fun j : Fin 10 → Fin L =>
      ∀ r : Fin 10, ∃ s : Fin 10, s ≠ r ∧ |((j r).val : ℤ) - ((j s).val : ℤ)| < 4)
  let DomSets : Finset (Finset (Fin 10)) :=
    Finset.univ.filter (fun D : Finset (Fin 10) => D.card ≤ 5)
  let GoodFor : Finset (Fin 10) → Finset (Fin 10 → Fin L) := fun D =>
    Finset.univ.filter (fun j : Fin 10 → Fin L =>
      ∀ r : Fin 10, ∃ s ∈ D, |((j r).val : ℤ) - ((j s).val : ℤ)| < 4)
  have hsub_Good : Good ⊆ DomSets.biUnion GoodFor := by
    intro j hj
    have hj' : ∀ r : Fin 10, ∃ s : Fin 10, s ≠ r ∧ |((j r).val : ℤ) - ((j s).val : ℤ)| < 4 :=
      (Finset.mem_filter.mp hj).2
    obtain ⟨D, hDcard, hDdom⟩ := exists_dominating_set_card_le_five (fun r => (j r).val) hj'
    rw [Finset.mem_biUnion]
    exact ⟨D, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hDcard⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hDdom⟩⟩
  have hGood_card : Good.card ≤ 2 ^ 10 * (L ^ 5 * 70 ^ 10) := by
    calc Good.card
        ≤ (DomSets.biUnion GoodFor).card := Finset.card_le_card hsub_Good
      _ ≤ ∑ D ∈ DomSets, (GoodFor D).card := Finset.card_biUnion_le
      _ ≤ ∑ _D ∈ DomSets, (L ^ 5 * 70 ^ 10) := by
          apply Finset.sum_le_sum
          intro D hD
          exact card_goodFor_le L hL D (Finset.mem_filter.mp hD).2
      _ = DomSets.card * (L ^ 5 * 70 ^ 10) := by simp [Finset.sum_const]
      _ ≤ (Finset.univ : Finset (Finset (Fin 10))).card * (L ^ 5 * 70 ^ 10) :=
          Nat.mul_le_mul_right _ (Finset.card_le_card (Finset.subset_univ _))
      _ = 2 ^ 10 * (L ^ 5 * 70 ^ 10) := by
          simp [Finset.card_univ, Fintype.card_finset, Fintype.card_fin]
  let P : Finset ((Fin 10 → Fin L) × (Fin 10 → Bool)) :=
    Good ×ˢ (Finset.univ : Finset (Fin 10 → Bool))
  let ψ : (Fin 10 → Fin L × Bool) → (Fin 10 → Fin L) × (Fin 10 → Bool) :=
    fun f => (fun r => (f r).1, fun r => (f r).2)
  have hmaps : Set.MapsTo ψ (Z : Set (Fin 10 → Fin L × Bool))
      (P : Set ((Fin 10 → Fin L) × (Fin 10 → Bool))) := by
    intro f hf
    have hf0 : ∑ r : Fin 10, sgn (f r).2 * (2 : ℤ) ^ ((f r).1.val + 1) = 0 :=
      (Finset.mem_filter.mp (Finset.mem_coe.mp hf)).2
    have hmul2 : (∑ r : Fin 10, sgn (f r).2 * (2 : ℤ) ^ ((f r).1.val)) * 2 = 0 := by
      rw [Finset.sum_mul]
      have hterm : ∑ r : Fin 10, sgn (f r).2 * (2 : ℤ) ^ ((f r).1.val) * 2 =
          ∑ r : Fin 10, sgn (f r).2 * (2 : ℤ) ^ ((f r).1.val + 1) := by
        apply Finset.sum_congr rfl
        intro r _
        rw [pow_succ]
        ring
      rw [hterm, hf0]
    have hsum0 : ∑ r : Fin 10, sgn (f r).2 * (2 : ℤ) ^ ((f r).1.val) = 0 := by omega
    have hgood : (fun r => (f r).1) ∈ Good := by
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, exists_close_of_sum_pow_two_eq_zero hsum0⟩
    exact Finset.mem_coe.mpr (Finset.mem_product.mpr ⟨hgood, Finset.mem_univ _⟩)
  have hinj : Set.InjOn ψ (Z : Set (Fin 10 → Fin L × Bool)) := by
    intro f₁ _ f₂ _ heq
    funext r
    have h1 := congrFun (congrArg Prod.fst heq) r
    have h2 := congrFun (congrArg Prod.snd heq) r
    exact Prod.ext h1 h2
  have hZ_card : Z.card ≤ Good.card * 2 ^ 10 := by
    calc Z.card
        ≤ P.card := Finset.card_le_card_of_injOn ψ hmaps hinj
      _ = Good.card * 2 ^ 10 := by
          simp [P, Finset.card_product, Finset.card_univ, Fintype.card_fun,
            Fintype.card_bool, Fintype.card_fin]
  calc Z.card ≤ Good.card * 2 ^ 10 := hZ_card
    _ ≤ (2 ^ 10 * (L ^ 5 * 70 ^ 10)) * 2 ^ 10 := Nat.mul_le_mul_right _ hGood_card
    _ = (2 ^ 10 * 2 ^ 10 * 70 ^ 10) * L ^ 5 := by ring

private lemma integral_cos_two_pi_int_mul (m : ℤ) :
    intervalIntegral (fun t : ℝ => Real.cos (2 * Real.pi * (m : ℝ) * t)) (0 : ℝ) 1
      MeasureTheory.volume = if m = 0 then 1 else 0 := by
  by_cases hm : m = 0
  · subst hm
    simp [intervalIntegral.integral_const]
  · rw [if_neg hm]
    set c : ℝ := 2 * Real.pi * (m : ℝ)
    have hc : c ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) (Int.cast_ne_zero.mpr hm)
    have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
        HasDerivAt (fun x : ℝ => Real.sin (c * x) / c) (Real.cos (c * t)) t := by
      intro t _
      have h1 : HasDerivAt (fun x : ℝ => c * x) c t := by
        simpa using (hasDerivAt_id t).const_mul c
      have h2 : HasDerivAt (fun x : ℝ => Real.sin (c * x)) (Real.cos (c * t) * c) t :=
        (Real.hasDerivAt_sin (c * t)).comp t h1
      have h3 : HasDerivAt (fun x : ℝ => Real.sin (c * x) / c) (Real.cos (c * t) * c / c) t :=
        h2.div_const c
      rwa [mul_div_cancel_right₀ _ hc] at h3
    have hint : IntervalIntegrable (fun t : ℝ => Real.cos (c * t)) MeasureTheory.volume 0 1 :=
      (Real.continuous_cos.comp (continuous_const.mul continuous_id)).intervalIntegrable 0 1
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
    have hsin1 : Real.sin (c * 1) = 0 := by
      have hEq : c * 1 = ((2 * m : ℤ) : ℝ) * Real.pi := by
        simp only [c]; push_cast; ring
      rw [hEq, Real.sin_int_mul_pi]
    rw [hsin1]
    simp

private lemma complex_re_sum {ι : Type*} (s : Finset ι) (g : ι → ℂ) :
    (∑ i ∈ s, g i).re = ∑ i ∈ s, (g i).re := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, Complex.add_re, ih]

private lemma sum_cos_pow_ten (L : ℕ) (t : ℝ) :
    (∑ j ∈ Finset.range L, Real.cos (2 * Real.pi * (2 : ℝ) ^ (j + 1) * t)) ^ 10 =
      (1 / 2 : ℝ) ^ 10 *
        ∑ f : Fin 10 → Fin L × Bool,
          Real.cos (2 * Real.pi *
            ((∑ r : Fin 10, sgn (f r).2 * (2 : ℤ) ^ ((f r).1.val + 1) : ℤ) : ℝ) * t) := by
  let ce : ℤ → ℂ := fun m => Complex.exp (((2 * Real.pi * (m : ℝ) * t : ℝ) : ℂ) * Complex.I)
  have hce_re : ∀ m : ℤ, (ce m).re = Real.cos (2 * Real.pi * (m : ℝ) * t) := by
    intro m
    dsimp only [ce]
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  have hce_prod : ∀ (s : Finset (Fin 10)) (g : Fin 10 → ℤ),
      ∏ r ∈ s, ce (g r) = ce (∑ r ∈ s, g r) := by
    intro s g
    induction s using Finset.induction_on with
    | empty => simp [ce]
    | insert a s ha ih =>
        rw [Finset.prod_insert ha, Finset.sum_insert ha, ih]
        simp only [ce, ← Complex.exp_add]
        congr 1
        push_cast
        ring
  have hcos_eq : ∀ j : Fin L,
      (Real.cos (2 * Real.pi * (2 : ℝ) ^ (j.val + 1) * t) : ℂ) =
        (1 / 2 : ℂ) * ∑ b : Bool, ce (sgn b * (2 : ℤ) ^ (j.val + 1)) := by
    intro j
    rw [Complex.ofReal_cos, Complex.cos, Fintype.sum_bool]
    simp only [ce, sgn, ↓reduceIte, Bool.false_eq_true]
    have h1 : (((2 * Real.pi * (2 : ℝ) ^ (j.val + 1) * t : ℝ) : ℂ) * Complex.I) =
        (((2 * Real.pi * ((1 * (2 : ℤ) ^ (j.val + 1) : ℤ) : ℝ) * t : ℝ) : ℂ) * Complex.I) := by
      push_cast; ring
    have h2 : -((2 * Real.pi * (2 : ℝ) ^ (j.val + 1) * t : ℝ) : ℂ) * Complex.I =
        (((2 * Real.pi * ((-1 * (2 : ℤ) ^ (j.val + 1) : ℤ) : ℝ) * t : ℝ) : ℂ) * Complex.I) := by
      push_cast; ring
    rw [h1, h2]
    ring
  have hsumC : ((∑ j ∈ Finset.range L, Real.cos (2 * Real.pi * (2 : ℝ) ^ (j + 1) * t) : ℝ) : ℂ) =
      (1 / 2 : ℂ) * ∑ p : Fin L × Bool, ce (sgn p.2 * (2 : ℤ) ^ (p.1.val + 1)) := by
    rw [← Fin.sum_univ_eq_sum_range, Complex.ofReal_sum]
    simp_rw [hcos_eq]
    rw [← Finset.mul_sum, Fintype.sum_prod_type]
  have hpowC : ((∑ j ∈ Finset.range L, Real.cos (2 * Real.pi * (2 : ℝ) ^ (j + 1) * t) : ℝ) : ℂ) ^ 10 =
      (1 / 2 : ℂ) ^ 10 * ∑ f : Fin 10 → Fin L × Bool,
        ce (∑ r : Fin 10, sgn (f r).2 * (2 : ℤ) ^ ((f r).1.val + 1)) := by
    rw [hsumC, mul_pow]
    congr 1
    calc (∑ p : Fin L × Bool, ce (sgn p.2 * (2 : ℤ) ^ (p.1.val + 1))) ^ 10
        = ∏ _r : Fin 10, ∑ p : Fin L × Bool, ce (sgn p.2 * (2 : ℤ) ^ (p.1.val + 1)) := by
            simp [Finset.prod_const]
      _ = ∑ f : Fin 10 → Fin L × Bool,
            ∏ r : Fin 10, ce (sgn (f r).2 * (2 : ℤ) ^ ((f r).1.val + 1)) :=
            Fintype.prod_sum (fun (_ : Fin 10) (p : Fin L × Bool) =>
              ce (sgn p.2 * (2 : ℤ) ^ (p.1.val + 1)))
      _ = ∑ f : Fin 10 → Fin L × Bool,
            ce (∑ r : Fin 10, sgn (f r).2 * (2 : ℤ) ^ ((f r).1.val + 1)) := by
            apply Finset.sum_congr rfl
            intro f _
            exact hce_prod Finset.univ (fun r => sgn (f r).2 * (2 : ℤ) ^ ((f r).1.val + 1))
  have hre := congrArg Complex.re hpowC
  rw [← Complex.ofReal_pow, Complex.ofReal_re] at hre
  have hhalf : ((1 / 2 : ℂ) ^ 10) = (((1 / 2 : ℝ) ^ 10 : ℝ) : ℂ) := by push_cast; rfl
  rw [hhalf] at hre
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hre
  rw [complex_re_sum] at hre
  simp_rw [hce_re] at hre
  exact hre

private lemma integral_sum_cos_pow_ten_le (L : ℕ) (hL : 1 ≤ L) :
    intervalIntegral
      (fun t : ℝ => (∑ j ∈ Finset.range L, Real.cos (2 * Real.pi * (2 : ℝ) ^ (j + 1) * t)) ^ 10)
      (0 : ℝ) 1 MeasureTheory.volume ≤ (2 ^ 10 * 70 ^ 10 : ℝ) * (L : ℝ) ^ 5 := by
  have hfun : (fun t : ℝ =>
        (∑ j ∈ Finset.range L, Real.cos (2 * Real.pi * (2 : ℝ) ^ (j + 1) * t)) ^ 10) =
      fun t : ℝ => (1 / 2 : ℝ) ^ 10 *
        ∑ f : Fin 10 → Fin L × Bool,
          Real.cos (2 * Real.pi *
            ((∑ r : Fin 10, sgn (f r).2 * (2 : ℤ) ^ ((f r).1.val + 1) : ℤ) : ℝ) * t) := by
    funext t
    exact sum_cos_pow_ten L t
  rw [hfun, intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_finsetSum
    (s := (Finset.univ : Finset (Fin 10 → Fin L × Bool)))
    (f := fun f t => Real.cos (2 * Real.pi *
      ((∑ r : Fin 10, sgn (f r).2 * (2 : ℤ) ^ ((f r).1.val + 1) : ℤ) : ℝ) * t))]
  · simp_rw [integral_cos_two_pi_int_mul]
    rw [Finset.sum_boole]
    have hcard : ((Finset.univ.filter (fun f : Fin 10 → Fin L × Bool =>
        ∑ r : Fin 10, sgn (f r).2 * (2 : ℤ) ^ ((f r).1.val + 1) = 0)).card : ℝ) ≤
        (((2 ^ 10 * 2 ^ 10 * 70 ^ 10) * L ^ 5 : ℕ) : ℝ) := by
      exact_mod_cast card_zeroSum_le L hL
    have hcard' : ((Finset.univ.filter (fun f : Fin 10 → Fin L × Bool =>
        ∑ r : Fin 10, sgn (f r).2 * (2 : ℤ) ^ ((f r).1.val + 1) = 0)).card : ℝ) ≤
        (2 ^ 10 : ℝ) * (2 ^ 10 * 70 ^ 10 : ℝ) * (L : ℝ) ^ 5 := by
      refine le_trans hcard (le_of_eq ?_)
      push_cast
      ring
    calc (1 / 2 : ℝ) ^ 10 * ((Finset.univ.filter (fun f : Fin 10 → Fin L × Bool =>
            ∑ r : Fin 10, sgn (f r).2 * (2 : ℤ) ^ ((f r).1.val + 1) = 0)).card : ℝ)
        ≤ (1 / 2 : ℝ) ^ 10 * ((2 ^ 10 : ℝ) * (2 ^ 10 * 70 ^ 10 : ℝ) * (L : ℝ) ^ 5) :=
          mul_le_mul_of_nonneg_left hcard' (by positivity)
      _ = (2 ^ 10 * 70 ^ 10 : ℝ) * (L : ℝ) ^ 5 := by ring
  · intro f _
    exact (Real.continuous_cos.comp (continuous_const.mul continuous_id)).intervalIntegrable 0 1

private lemma measurableSet_rational_window
    (P : ℕ → ℕ → Prop) (c r : ℕ → ℕ → ℝ) :
    MeasurableSet {t : ℝ | ∃ q a : ℕ, P q a ∧ |t - c q a| ≤ r q a} := by
  have heq : {t : ℝ | ∃ q a : ℕ, P q a ∧ |t - c q a| ≤ r q a} =
      ⋃ q : ℕ, ⋃ a : ℕ, {t : ℝ | P q a ∧ |t - c q a| ≤ r q a} := by
    ext t
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
  rw [heq]
  refine MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun a => ?_
  by_cases h : P q a
  · have hset : {t : ℝ | P q a ∧ |t - c q a| ≤ r q a} = {t : ℝ | |t - c q a| ≤ r q a} := by
      ext t; simp [h]
    rw [hset]
    exact (isClosed_le (continuous_abs.comp (continuous_id.sub continuous_const))
      continuous_const).measurableSet
  · have hset : {t : ℝ | P q a ∧ |t - c q a| ≤ r q a} = ∅ := by
      ext t; simp [h]
    rw [hset]
    exact MeasurableSet.empty

private lemma intervalIntegral_indicator_split
    {f : ℝ → ℝ} {s u : Set ℝ}
    (hf : IntervalIntegrable f MeasureTheory.volume (0 : ℝ) 1)
    (hs : MeasurableSet s) (hu : MeasurableSet u) :
    intervalIntegral (s.indicator f) (0 : ℝ) 1 MeasureTheory.volume =
      intervalIntegral ((s ∩ u).indicator f) (0 : ℝ) 1 MeasureTheory.volume +
      intervalIntegral ((s \ u).indicator f) (0 : ℝ) 1 MeasureTheory.volume := by
  have hpoint : s.indicator f = fun t => (s ∩ u).indicator f t + (s \ u).indicator f t := by
    funext t
    by_cases hts : t ∈ s <;> by_cases htu : t ∈ u <;> simp [Set.indicator, hts, htu]
  have hf_on : MeasureTheory.IntegrableOn f (Set.Ioc (0 : ℝ) 1) MeasureTheory.volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp hf
  have h1 : IntervalIntegrable ((s ∩ u).indicator f) MeasureTheory.volume (0 : ℝ) 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mpr
      (hf_on.indicator (hs.inter hu))
  have h2 : IntervalIntegrable ((s \ u).indicator f) MeasureTheory.volume (0 : ℝ) 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mpr
      (hf_on.indicator (hs.diff hu))
  rw [hpoint, intervalIntegral.integral_add h1 h2]

theorem Conjectures.Goldbach.PacketEnergyFromRationalRegions :
  (let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let low := fun (n k : ℕ) => if k^3≤n then w k else 0; let high := fun (n k : ℕ) => w k-low n k; let L := fun n : ℕ => max 1 (Nat.log 2 n / 2); let K := fun (n : ℕ) (t : ℝ) => (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ); let B := fun n : ℕ => {t : ℝ | t ∉ arcs n ∧ (1:ℝ)/2 < K n t}; let W := fun (n : ℕ) (p : ℕ → Prop) => {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ (Q n)^2 ∧ a ≤ q ∧ Nat.Coprime a q ∧ p q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ ((Q n:ℝ)^2)/((q:ℝ)*(n:ℝ))}; let o := fun n q : ℕ => Odd q ∧ ∃ j : ℕ, 1 ≤ j ∧ j ≤ (Nat.log 2 (Q n)+1)^2 ∧ q ∣ 2^j-1; let F := fun (n : ℕ) (t : ℝ) => ‖S n (high n) t‖^2; let m := fun (s : Set ℝ) (f : ℝ → ℝ) => intervalIntegral (s.indicator f) (0:ℝ) 1 MeasureTheory.volume; ∃ N : ℕ, ∀ n ≥ N, Even n → m ((B n ∩ (W n (fun _ => True))) ∩ W n (o n)) (F n) ≤ (n:ℝ)/2304) → (let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let low := fun (n k : ℕ) => if k^3≤n then w k else 0; let high := fun (n k : ℕ) => w k-low n k; let L := fun n : ℕ => max 1 (Nat.log 2 n / 2); let K := fun (n : ℕ) (t : ℝ) => (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ); let B := fun n : ℕ => {t : ℝ | t ∉ arcs n ∧ (1:ℝ)/2 < K n t}; let W := fun (n : ℕ) (p : ℕ → Prop) => {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ (Q n)^2 ∧ a ≤ q ∧ Nat.Coprime a q ∧ p q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ ((Q n:ℝ)^2)/((q:ℝ)*(n:ℝ))}; let o := fun n q : ℕ => Odd q ∧ ∃ j : ℕ, 1 ≤ j ∧ j ≤ (Nat.log 2 (Q n)+1)^2 ∧ q ∣ 2^j-1; let F := fun (n : ℕ) (t : ℝ) => ‖S n (high n) t‖^2; let m := fun (s : Set ℝ) (f : ℝ → ℝ) => intervalIntegral (s.indicator f) (0:ℝ) 1 MeasureTheory.volume; ∃ N : ℕ, ∀ n ≥ N, Even n → m ((B n ∩ (W n (fun _ => True))) \ W n (o n)) (F n) ≤ (n:ℝ)/2304) → (let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let low := fun (n k : ℕ) => if k^3≤n then w k else 0; let high := fun (n k : ℕ) => w k-low n k; let L := fun n : ℕ => max 1 (Nat.log 2 n / 2); let K := fun (n : ℕ) (t : ℝ) => (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ); let B := fun n : ℕ => {t : ℝ | t ∉ arcs n ∧ (1:ℝ)/2 < K n t}; let W := fun (n : ℕ) (p : ℕ → Prop) => {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ (Q n)^2 ∧ a ≤ q ∧ Nat.Coprime a q ∧ p q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ ((Q n:ℝ)^2)/((q:ℝ)*(n:ℝ))}; let F := fun (n : ℕ) (t : ℝ) => ‖S n (high n) t‖^2; let T := fun n : ℕ => (n:ℝ)*(1+Real.log (n:ℝ))^4; let m := fun (s : Set ℝ) (f : ℝ → ℝ) => intervalIntegral (s.indicator f) (0:ℝ) 1 MeasureTheory.volume; ∃ N : ℕ, ∀ n ≥ N, Even n → m ((B n \ (W n (fun _ => True))) ∩ {t : ℝ | T n < F n t}) (F n) ≤ (n:ℝ)/2304) → (let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let low := fun (n k : ℕ) => if k^3≤n then w k else 0; let high := fun (n k : ℕ) => w k-low n k; let I := fun (n:ℕ) (a b:ℕ→ℝ) => intervalIntegral (fun t => (arcs n)ᶜ.indicator (fun u => S n a u*S n b u*E (-(n:ℝ)*u)) t) (0:ℝ) 1 MeasureTheory.volume; let L := fun n : ℕ => max 1 (Nat.log 2 n / 2); let K := fun (n : ℕ) (t : ℝ) => (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ); let B := fun n : ℕ => {t : ℝ | t ∉ arcs n ∧ (1:ℝ)/2 < K n t}; let U := fun (n : ℕ) (a : ℕ → ℝ) => intervalIntegral ((B n).indicator (fun t => ‖S n a t‖^2)) (0:ℝ) 1 MeasureTheory.volume; ∃ N : ℕ, ∀ n ≥ N, Even n → U n (high n) ≤ (n:ℝ)/576) := by
  intro h1 h2 h3
  let w := fun k : ℕ => if Nat.Prime k then Real.log (k : ℝ) else 0
  let E := fun x : ℝ => Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)
  let S := fun (n : ℕ) (a : ℕ → ℝ) (t : ℝ) =>
    Finset.sum (Finset.range (n + 1)) (fun k => (a k : ℂ) * E ((k : ℝ) * t))
  let Q := fun n : ℕ => (Nat.log 2 (n + 2)) ^ 2
  let arcs := fun n : ℕ =>
    {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Q n ∧ a ≤ q ∧ Nat.Coprime a q ∧
      |t - (a : ℝ) / (q : ℝ)| ≤ (Q n : ℝ) / ((q : ℝ) * (n : ℝ))}
  let low := fun (n k : ℕ) => if k ^ 3 ≤ n then w k else 0
  let high := fun (n k : ℕ) => w k - low n k
  let L := fun n : ℕ => max 1 (Nat.log 2 n / 2)
  let K := fun (n : ℕ) (t : ℝ) =>
    (∑ j ∈ Finset.range (L n), Real.cos (2 * Real.pi * (2 : ℝ) ^ (j + 1) * t)) / (L n : ℝ)
  let B := fun n : ℕ => {t : ℝ | t ∉ arcs n ∧ (1 : ℝ) / 2 < K n t}
  let W := fun (n : ℕ) (p : ℕ → Prop) =>
    {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ (Q n) ^ 2 ∧ a ≤ q ∧ Nat.Coprime a q ∧ p q ∧
      |t - (a : ℝ) / (q : ℝ)| ≤ ((Q n : ℝ) ^ 2) / ((q : ℝ) * (n : ℝ))}
  let o := fun n q : ℕ =>
    Odd q ∧ ∃ j : ℕ, 1 ≤ j ∧ j ≤ (Nat.log 2 (Q n) + 1) ^ 2 ∧ q ∣ 2 ^ j - 1
  let F := fun (n : ℕ) (t : ℝ) => ‖S n (high n) t‖ ^ 2
  let T := fun n : ℕ => (n : ℝ) * (1 + Real.log (n : ℝ)) ^ 4
  let m := fun (s : Set ℝ) (f : ℝ → ℝ) =>
    intervalIntegral (s.indicator f) (0 : ℝ) 1 MeasureTheory.volume
  rcases h1 with ⟨N1, hN1⟩
  rcases h2 with ⟨N2, hN2⟩
  rcases h3 with ⟨N3, hN3⟩
  let C_const : ℕ := 256 * 2 ^ 20 * 70 ^ 10
  let C : ℕ := 2304 * C_const
  let N4 : ℕ := max 16 (2 ^ (2 * C))
  refine ⟨max (max N1 N2) (max N3 N4), fun n hn heven => ?_⟩
  have hn1 : N1 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hn2 : N2 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn3 : N3 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hn4 : N4 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  have hm1 : m ((B n ∩ W n (fun _ => True)) ∩ W n (o n)) (F n) ≤ (n : ℝ) / 2304 :=
    hN1 n hn1 heven
  have hm2 : m ((B n ∩ W n (fun _ => True)) \ W n (o n)) (F n) ≤ (n : ℝ) / 2304 :=
    hN2 n hn2 heven
  have hm3 : m ((B n \ W n (fun _ => True)) ∩ {t : ℝ | T n < F n t}) (F n) ≤ (n : ℝ) / 2304 :=
    hN3 n hn3 heven
  have hE_cont : Continuous E := by
    dsimp only [E]
    exact Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.comp (continuous_const.mul continuous_id)).mul continuous_const)
  have hS_cont : Continuous (S n (high n)) := by
    dsimp only [S]
    refine continuous_finsetSum _ fun k _ => ?_
    exact continuous_const.mul (hE_cont.comp (continuous_const.mul continuous_id))
  have hF_cont : Continuous (F n) := by
    dsimp only [F]
    exact hS_cont.norm.pow 2
  have hF_int : IntervalIntegrable (F n) MeasureTheory.volume (0 : ℝ) 1 :=
    hF_cont.intervalIntegrable 0 1
  have hK_cont : Continuous (K n) := by
    dsimp only [K]
    refine (continuous_finsetSum _ fun j _ => ?_).div_const _
    exact Real.continuous_cos.comp (continuous_const.mul continuous_id)
  have harcs_meas : MeasurableSet (arcs n) := by
    have heq : arcs n = {t : ℝ | ∃ q a : ℕ,
        (1 ≤ q ∧ q ≤ Q n ∧ a ≤ q ∧ Nat.Coprime a q) ∧
        |t - (a : ℝ) / (q : ℝ)| ≤ (Q n : ℝ) / ((q : ℝ) * (n : ℝ))} := by
      ext t
      simp [arcs, and_assoc]
    rw [heq]
    exact measurableSet_rational_window _ _ _
  have hW_meas : ∀ p : ℕ → Prop, MeasurableSet (W n p) := by
    intro p
    have heq : W n p = {t : ℝ | ∃ q a : ℕ,
        (1 ≤ q ∧ q ≤ (Q n) ^ 2 ∧ a ≤ q ∧ Nat.Coprime a q ∧ p q) ∧
        |t - (a : ℝ) / (q : ℝ)| ≤ ((Q n : ℝ) ^ 2) / ((q : ℝ) * (n : ℝ))} := by
      ext t
      simp [W, and_assoc]
    rw [heq]
    exact measurableSet_rational_window _ _ _
  have hB_meas : MeasurableSet (B n) := by
    have heq : B n = (arcs n)ᶜ ∩ {t : ℝ | (1 : ℝ) / 2 < K n t} := by
      ext t
      simp [B]
    rw [heq]
    exact harcs_meas.compl.inter (isOpen_lt continuous_const hK_cont).measurableSet
  have hH_meas : MeasurableSet {t : ℝ | T n < F n t} :=
    (isOpen_lt continuous_const hF_cont).measurableSet
  let W_all : Set ℝ := W n (fun _ => True)
  let W_o : Set ℝ := W n (o n)
  let H : Set ℝ := {t : ℝ | T n < F n t}
  let A4 : Set ℝ := (B n \ W_all) \ H
  have hW_all_meas : MeasurableSet W_all := hW_meas (fun _ => True)
  have hW_o_meas : MeasurableSet W_o := hW_meas (o n)
  have hA4_meas : MeasurableSet A4 := (hB_meas.diff hW_all_meas).diff hH_meas
  have hsplit_B : m (B n) (F n) =
      m ((B n ∩ W_all) ∩ W_o) (F n) +
      m ((B n ∩ W_all) \ W_o) (F n) +
      m ((B n \ W_all) ∩ H) (F n) +
      m A4 (F n) := by
    have s1 := intervalIntegral_indicator_split hF_int hB_meas hW_all_meas
    have s2 := intervalIntegral_indicator_split hF_int (hB_meas.inter hW_all_meas) hW_o_meas
    have s3 := intervalIntegral_indicator_split hF_int (hB_meas.diff hW_all_meas) hH_meas
    dsimp only [m, A4]
    linarith
  have hn16 : 16 ≤ n := le_trans (le_max_left _ _) hn4
  have hn_pow : 2 ^ (2 * C) ≤ n := le_trans (le_max_right _ _) hn4
  have hlog_ge4 : 4 ≤ Nat.log 2 n :=
    Nat.le_log_of_pow_le (by norm_num : 1 < 2) (by omega : 2 ^ 4 ≤ n)
  have hlog_ge2C : 2 * C ≤ Nat.log 2 n :=
    Nat.le_log_of_pow_le (by norm_num : 1 < 2) hn_pow
  have hL_ge_half : Nat.log 2 n / 2 ≤ L n := le_max_right _ _
  have hL_ge2 : 2 ≤ L n := by omega
  have hL_geC : C ≤ L n := by omega
  have hL_pos : (0 : ℝ) < (L n : ℝ) := by
    have : 0 < L n := by omega
    exact_mod_cast this
  have h1log_nonneg : 0 ≤ 1 + Real.log (n : ℝ) := by
    have hlog_nonneg : 0 ≤ Real.log (n : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
    linarith
  have hT_nonneg : 0 ≤ T n := by
    dsimp only [T]
    positivity
  have hT_le : T n ≤ 256 * (n : ℝ) * (L n : ℝ) ^ 4 := by
    have hn_lt : n < 2 ^ (Nat.log 2 n + 1) :=
      Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) n
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hcast : (n : ℝ) ≤ (2 : ℝ) ^ (Nat.log 2 n + 1) := by
      exact_mod_cast le_of_lt hn_lt
    have hlog1 : Real.log (n : ℝ) ≤ Real.log ((2 : ℝ) ^ (Nat.log 2 n + 1)) :=
      Real.log_le_log hn_pos hcast
    rw [Real.log_pow] at hlog1
    push_cast at hlog1
    have hlog2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    have hmul : ((Nat.log 2 n : ℝ) + 1) * Real.log 2 ≤ ((Nat.log 2 n : ℝ) + 1) * 1 :=
      mul_le_mul_of_nonneg_left hlog2 (by positivity)
    have hnat_le : Nat.log 2 n + 2 ≤ 4 * L n := by omega
    have hnat_le' : (Nat.log 2 n : ℝ) + 2 ≤ 4 * (L n : ℝ) := by exact_mod_cast hnat_le
    have h1log_le : 1 + Real.log (n : ℝ) ≤ 4 * (L n : ℝ) := by linarith
    calc T n = (n : ℝ) * (1 + Real.log (n : ℝ)) ^ 4 := rfl
      _ ≤ (n : ℝ) * (4 * (L n : ℝ)) ^ 4 := by gcongr
      _ = 256 * (n : ℝ) * (L n : ℝ) ^ 4 := by ring
  have hpt : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      A4.indicator (F n) t ≤ (T n * (2 : ℝ) ^ 10) * (K n t) ^ 10 := by
    intro t _
    have hK10_nonneg : 0 ≤ (K n t) ^ 10 := by
      have : (K n t) ^ 10 = ((K n t) ^ 5) ^ 2 := by ring
      rw [this]
      exact sq_nonneg _
    by_cases ht : t ∈ A4
    · rw [Set.indicator_of_mem ht]
      have hB : t ∈ B n := ht.1.1
      have hKgt : (1 : ℝ) / 2 < K n t := hB.2
      have hFle : F n t ≤ T n := not_lt.mp ht.2
      have h2K : (1 : ℝ) ≤ 2 * K n t := by linarith
      have h1le : (1 : ℝ) ≤ (2 * K n t) ^ 10 := by
        calc (1 : ℝ) = 1 ^ 10 := by norm_num
          _ ≤ (2 * K n t) ^ 10 := by gcongr
      have h1le' : (1 : ℝ) ≤ (2 : ℝ) ^ 10 * (K n t) ^ 10 := by
        simpa [mul_pow] using h1le
      calc F n t ≤ T n := hFle
        _ = T n * 1 := (mul_one _).symm
        _ ≤ T n * ((2 : ℝ) ^ 10 * (K n t) ^ 10) :=
            mul_le_mul_of_nonneg_left h1le' hT_nonneg
        _ = (T n * (2 : ℝ) ^ 10) * (K n t) ^ 10 := by ring
    · rw [Set.indicator_of_notMem ht]
      positivity
  have hK10_int : IntervalIntegrable (fun t : ℝ => (T n * (2 : ℝ) ^ 10) * (K n t) ^ 10)
      MeasureTheory.volume (0 : ℝ) 1 :=
    (continuous_const.mul (hK_cont.pow 10)).intervalIntegrable 0 1
  have hA4_int : IntervalIntegrable (A4.indicator (F n)) MeasureTheory.volume (0 : ℝ) 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mpr
      (((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp
        hF_int).indicator hA4_meas)
  have hmA4_le1 : m A4 (F n) ≤
      (T n * (2 : ℝ) ^ 10) *
        intervalIntegral (fun t : ℝ => (K n t) ^ 10) (0 : ℝ) 1 MeasureTheory.volume := by
    have hmono := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1) hA4_int hK10_int hpt
    rwa [intervalIntegral.integral_const_mul] at hmono
  have hK10_eq : (fun t : ℝ => (K n t) ^ 10) =
      fun t : ℝ => ((L n : ℝ) ^ 10)⁻¹ *
        (∑ j ∈ Finset.range (L n), Real.cos (2 * Real.pi * (2 : ℝ) ^ (j + 1) * t)) ^ 10 := by
    funext t
    dsimp only [K]
    rw [div_pow, div_eq_inv_mul]
  have hK10_bound : intervalIntegral (fun t : ℝ => (K n t) ^ 10) (0 : ℝ) 1 MeasureTheory.volume ≤
      (2 ^ 10 * 70 ^ 10 : ℝ) / (L n : ℝ) ^ 5 := by
    rw [hK10_eq, intervalIntegral.integral_const_mul]
    have hsum_le := integral_sum_cos_pow_ten_le (L n) (by omega)
    have hinv_nonneg : (0 : ℝ) ≤ ((L n : ℝ) ^ 10)⁻¹ := by positivity
    calc ((L n : ℝ) ^ 10)⁻¹ *
          intervalIntegral
            (fun t : ℝ =>
              (∑ j ∈ Finset.range (L n), Real.cos (2 * Real.pi * (2 : ℝ) ^ (j + 1) * t)) ^ 10)
            (0 : ℝ) 1 MeasureTheory.volume
        ≤ ((L n : ℝ) ^ 10)⁻¹ * ((2 ^ 10 * 70 ^ 10 : ℝ) * (L n : ℝ) ^ 5) :=
          mul_le_mul_of_nonneg_left hsum_le hinv_nonneg
      _ = (2 ^ 10 * 70 ^ 10 : ℝ) / (L n : ℝ) ^ 5 := by
          have hLne : (L n : ℝ) ≠ 0 := ne_of_gt hL_pos
          field_simp [hLne]
  have hCconst_real : (C_const : ℝ) = 256 * (2 : ℝ) ^ 20 * (70 : ℝ) ^ 10 := by
    dsimp only [C_const]
    push_cast
    ring
  have hCconst_pos : (0 : ℝ) < (C_const : ℝ) := by
    rw [hCconst_real]
    positivity
  have hC_cast : (C : ℝ) = 2304 * (C_const : ℝ) := by
    dsimp only [C]
    push_cast
    ring
  have hL_geC_real : 2304 * (C_const : ℝ) ≤ (L n : ℝ) := by
    rw [← hC_cast]
    exact_mod_cast hL_geC
  have hm4 : m A4 (F n) ≤ (n : ℝ) / 2304 := by
    calc m A4 (F n)
        ≤ (T n * (2 : ℝ) ^ 10) *
            intervalIntegral (fun t : ℝ => (K n t) ^ 10) (0 : ℝ) 1 MeasureTheory.volume := hmA4_le1
      _ ≤ (T n * (2 : ℝ) ^ 10) * ((2 ^ 10 * 70 ^ 10 : ℝ) / (L n : ℝ) ^ 5) :=
          mul_le_mul_of_nonneg_left hK10_bound (by positivity)
      _ ≤ ((256 * (n : ℝ) * (L n : ℝ) ^ 4) * (2 : ℝ) ^ 10) *
            ((2 ^ 10 * 70 ^ 10 : ℝ) / (L n : ℝ) ^ 5) := by
          have hfac_nonneg : (0 : ℝ) ≤ (2 ^ 10 * 70 ^ 10 : ℝ) / (L n : ℝ) ^ 5 := by positivity
          have hT2 : T n * (2 : ℝ) ^ 10 ≤ (256 * (n : ℝ) * (L n : ℝ) ^ 4) * (2 : ℝ) ^ 10 :=
            mul_le_mul_of_nonneg_right hT_le (by positivity)
          exact mul_le_mul_of_nonneg_right hT2 hfac_nonneg
      _ = (C_const : ℝ) * (n : ℝ) / (L n : ℝ) := by
          have hLne : (L n : ℝ) ≠ 0 := ne_of_gt hL_pos
          rw [hCconst_real]
          field_simp [hLne]
      _ ≤ (C_const : ℝ) * (n : ℝ) / (2304 * (C_const : ℝ)) :=
          div_le_div_of_nonneg_left (mul_nonneg (le_of_lt hCconst_pos) (Nat.cast_nonneg n))
            (by positivity) hL_geC_real
      _ = (n : ℝ) / 2304 := by
          have hCne : (C_const : ℝ) ≠ 0 := ne_of_gt hCconst_pos
          field_simp [hCne]
  change m (B n) (F n) ≤ (n : ℝ) / 576
  linarith