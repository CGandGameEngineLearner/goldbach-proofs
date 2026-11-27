import Mathlib

private def revMod (H L b : ℕ) : ℕ := (2 * H + L - b) % L

private def classSet (H L b : ℕ) : Finset (Fin (2 * H + 1)) :=
  Finset.univ.filter (fun i => i.val % L = b)

private def rankFin {n : ℕ} (S : Finset (Fin n)) (i : Fin n) : ℕ :=
  (S.filter (· < i)).card

private lemma rev_mod_lt (H L b : ℕ) (hL : 0 < L) : revMod H L b < L :=
  Nat.mod_lt _ hL

private lemma mod_eq_iff_zmod (L x y : ℕ) (hL : 0 < L) :
    x % L = y % L ↔ (x : ZMod L) = (y : ZMod L) := by
  have : NeZero L := ⟨hL.ne'⟩
  rw [← ZMod.val_natCast (n := L) x, ← ZMod.val_natCast (n := L) y]
  exact ⟨fun h => ZMod.val_injective L h, fun h => by rw [h]⟩

private lemma rev_mod_invol (H L b : ℕ) (hL : 0 < L) (hb : b < L) :
    revMod H L (revMod H L b) = b := by
  have : NeZero L := ⟨hL.ne'⟩
  have h1 : revMod H L b < L := rev_mod_lt H L b hL
  have h2 : revMod H L (revMod H L b) < L := rev_mod_lt H L _ hL
  have hmod : revMod H L (revMod H L b) % L = b % L := by
    rw [mod_eq_iff_zmod L _ _ hL]
    dsimp [revMod]
    rw [ZMod.natCast_mod,
      Nat.cast_sub (by have : (2 * H + L - b) % L < L := Nat.mod_lt _ hL; omega),
      ZMod.natCast_mod, Nat.cast_sub (by omega : b ≤ 2 * H + L)]
    rw [Nat.cast_add, ZMod.natCast_self, add_zero]
    ring
  rwa [Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt hb] at hmod

private lemma rev_mem_classSet (H L b : ℕ) (hL : 0 < L) (hb : b < L) (i : Fin (2 * H + 1)) :
    i.rev ∈ classSet H L b ↔ i ∈ classSet H L (revMod H L b) := by
  have : NeZero L := ⟨hL.ne'⟩
  simp only [classSet, Finset.mem_filter, Finset.mem_univ, true_and]
  have hrm : revMod H L b < L := rev_mod_lt H L b hL
  nth_rw 1 [← Nat.mod_eq_of_lt hb]
  rw [mod_eq_iff_zmod L i.rev.val b hL]
  nth_rw 1 [← Nat.mod_eq_of_lt hrm]
  rw [mod_eq_iff_zmod L i.val (revMod H L b) hL]
  have hrev_val : i.rev.val = 2 * H - i.val := by rw [Fin.val_rev]; omega
  have hi_le : i.val ≤ 2 * H := by omega
  rw [hrev_val, Nat.cast_sub hi_le]
  dsimp [revMod]
  rw [ZMod.natCast_mod, Nat.cast_sub (by omega : b ≤ 2 * H + L), Nat.cast_add,
    ZMod.natCast_self, add_zero]
  constructor <;> intro h
  · linear_combination -h
  · linear_combination -h

private lemma mem_classSet_rev_iff (H L b : ℕ) (hL : 0 < L) (hb : b < L) (i : Fin (2 * H + 1)) :
    i ∈ classSet H L b ↔ i.rev ∈ classSet H L (revMod H L b) := by
  rw [← Fin.rev_rev i, rev_mem_classSet H L b hL hb i.rev, Fin.rev_rev]

private lemma classSet_card_rev (H L b : ℕ) (hL : 0 < L) (hb : b < L) :
    (classSet H L (revMod H L b)).card = (classSet H L b).card := by
  refine Finset.card_bij (fun i _ => i.rev) ?_ ?_ ?_
  · intro i hi
    exact (rev_mem_classSet H L b hL hb i).mpr hi
  · intro x _ y _ h
    exact Fin.rev_injective h
  · intro j hj
    refine ⟨j.rev, ?_, Fin.rev_rev j⟩
    exact (rev_mem_classSet H L b hL hb j.rev).mp (by simpa [Fin.rev_rev] using hj)

private lemma rankFin_lt_rankFin {n : ℕ} {S : Finset (Fin n)} {x y : Fin n}
    (hx : x ∈ S) (hxy : x < y) : rankFin S x < rankFin S y := by
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨x, Finset.mem_filter.mpr ⟨hx, hxy⟩, ?_⟩
    simp
  · intro z hz
    rw [Finset.mem_filter] at hz ⊢
    exact ⟨hz.1, lt_trans hz.2 hxy⟩

private lemma rankFin_lt_card {n : ℕ} {S : Finset (Fin n)} {x : Fin n} (hx : x ∈ S) :
    rankFin S x < S.card := by
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)]
  refine ⟨x, hx, ?_⟩
  simp

private lemma rankFin_injOn {n : ℕ} (S : Finset (Fin n)) : Set.InjOn (rankFin S) S := by
  intro x hx y hy hxy
  rcases lt_trichotomy x y with hlt | heq | hgt
  · exact absurd hxy (Nat.ne_of_lt (rankFin_lt_rankFin hx hlt))
  · exact heq
  · exact absurd hxy.symm (Nat.ne_of_lt (rankFin_lt_rankFin hy hgt))

private lemma image_rankFin_eq_range {n : ℕ} (S : Finset (Fin n)) :
    S.image (rankFin S) = Finset.range S.card := by
  apply Finset.eq_of_subset_of_card_le
  · exact Finset.image_subset_iff.mpr fun x hx => Finset.mem_range.mpr (rankFin_lt_card hx)
  · rw [Finset.card_range, Finset.card_image_of_injOn (rankFin_injOn S)]

private lemma card_filter_rankFin {n : ℕ} (S : Finset (Fin n)) (P : ℕ → Prop)
    [DecidablePred P] :
    (S.filter (fun x => P (rankFin S x))).card = ((Finset.range S.card).filter P).card := by
  have himg : (S.filter (fun x => P (rankFin S x))).image (rankFin S) =
      (Finset.range S.card).filter P := by
    rw [← image_rankFin_eq_range S]
    ext k
    simp only [Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨x, ⟨hx, hPx⟩, rfl⟩
      exact ⟨⟨x, hx, rfl⟩, hPx⟩
    · rintro ⟨⟨x, hx, rfl⟩, hPx⟩
      exact ⟨x, ⟨hx, hPx⟩, rfl⟩
  rw [← himg, Finset.card_image_of_injOn ((rankFin_injOn S).mono (Finset.filter_subset _ _))]

private lemma rankFin_rev_add (H L b : ℕ) (hL : 0 < L) (hb : b < L)
    (i : Fin (2 * H + 1)) (hi : i ∈ classSet H L b) :
    rankFin (classSet H L b) i + 1 + rankFin (classSet H L (revMod H L b)) i.rev =
      (classSet H L b).card := by
  let S := classSet H L b
  let T := classSet H L (revMod H L b)
  have hgt_img : (T.filter (· < i.rev)).image Fin.rev = S.filter (i < ·) := by
    ext x
    simp only [Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨y, ⟨hyT, hy_lt⟩, rfl⟩
      have hxS : y.rev ∈ S := (rev_mem_classSet H L b hL hb y).mpr hyT
      have hix : i < y.rev := by
        rw [Fin.lt_def] at hy_lt ⊢
        have hiy : i.rev.val = 2 * H - i.val := by rw [Fin.val_rev]; omega
        have hyr : y.rev.val = 2 * H - y.val := by rw [Fin.val_rev]; omega
        omega
      exact ⟨hxS, hix⟩
    · rintro ⟨hxS, hix⟩
      refine ⟨x.rev, ⟨(mem_classSet_rev_iff H L b hL hb x).mp hxS, ?_⟩, Fin.rev_rev x⟩
      rw [Fin.lt_def] at hix ⊢
      have hir : i.rev.val = 2 * H - i.val := by rw [Fin.val_rev]; omega
      have hxr : x.rev.val = 2 * H - x.val := by rw [Fin.val_rev]; omega
      omega
  have hgt_card : rankFin T i.rev = (S.filter (i < ·)).card := by
    dsimp [rankFin]
    rw [← hgt_img, Finset.card_image_of_injOn (fun x _ y _ h => Fin.rev_injective h)]
  have hpart : S = S.filter (· < i) ∪ ({i} ∪ S.filter (i < ·)) := by
    ext x
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_singleton]
    constructor
    · intro hx
      rcases lt_trichotomy x i with hlt | rfl | hgt
      · exact Or.inl ⟨hx, hlt⟩
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr ⟨hx, hgt⟩)
    · rintro (⟨hx, _⟩ | rfl | ⟨hx, _⟩)
      · exact hx
      · exact hi
      · exact hx
  have hdisj2 : Disjoint ({i} : Finset (Fin (2 * H + 1))) (S.filter (i < ·)) := by
    rw [Finset.disjoint_singleton_left, Finset.mem_filter]
    intro h
    exact lt_irrefl i h.2
  have hdisj1 : Disjoint (S.filter (· < i)) ({i} ∪ S.filter (i < ·)) := by
    rw [Finset.disjoint_left]
    intro x hx hux
    rw [Finset.mem_filter] at hx
    rw [Finset.mem_union, Finset.mem_singleton, Finset.mem_filter] at hux
    rcases hux with rfl | ⟨_, hix⟩
    · exact lt_irrefl x hx.2
    · exact lt_asymm hx.2 hix
  have hcard : S.card = (S.filter (· < i)).card + (1 + (S.filter (i < ·)).card) := by
    conv_lhs => rw [hpart]
    rw [Finset.card_union_of_disjoint hdisj1, Finset.card_union_of_disjoint hdisj2,
      Finset.card_singleton]
  dsimp [S, rankFin] at hgt_card hcard ⊢
  rw [hgt_card]
  omega

private lemma hit_eq_sum (H L : ℕ) (hL : 0 < L) (U : Finset (Fin (2 * H + 1))) :
    (U.filter (fun i => i.rev ∈ U)).card =
      ∑ b : Fin L, ((U ∩ classSet H L b.val).filter (fun i => i.rev ∈ U)).card := by
  have hunion : U.filter (fun i => i.rev ∈ U) =
      Finset.univ.biUnion (fun b : Fin L => (U ∩ classSet H L b.val).filter (fun i => i.rev ∈ U)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_univ, Finset.mem_inter, true_and]
    constructor
    · rintro ⟨hiU, hirev⟩
      refine ⟨⟨i.val % L, Nat.mod_lt _ hL⟩, ⟨hiU, ?_⟩, hirev⟩
      simp [classSet]
    · rintro ⟨b, ⟨hiU, _⟩, hirev⟩
      exact ⟨hiU, hirev⟩
  rw [hunion, Finset.card_biUnion]
  intro b _ c _ hbc
  dsimp [Function.onFun]
  rw [Finset.disjoint_left]
  intro x hxb hxc
  rw [Finset.mem_filter, Finset.mem_inter] at hxb hxc
  have h1 : x.val % L = b.val := (Finset.mem_filter.mp hxb.1.2).2
  have h2 : x.val % L = c.val := (Finset.mem_filter.mp hxc.1.2).2
  exact hbc (Fin.ext (h1.symm.trans h2))

private lemma class_hit_eq_inter (H L : ℕ) (hL : 0 < L)
    (U : Finset (Fin (2 * H + 1))) (b : Fin L) :
    ((U ∩ classSet H L b.val).filter (fun i => i.rev ∈ U)) =
      (U ∩ classSet H L b.val) ∩ ((U ∩ classSet H L (revMod H L b.val)).image Fin.rev) := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_inter, Finset.mem_image]
  constructor
  · rintro ⟨⟨hiU, hiS⟩, hirev⟩
    refine ⟨⟨hiU, hiS⟩, i.rev, ⟨hirev, ?_⟩, Fin.rev_rev i⟩
    exact (mem_classSet_rev_iff H L b.val hL b.isLt i).mp hiS
  · rintro ⟨⟨hiU, hiS⟩, j, ⟨hjU, _⟩, rfl⟩
    rw [Fin.rev_rev]
    exact ⟨⟨hiU, hiS⟩, hjU⟩

theorem Conjectures.Goldbach.ThetaResidueOverlapMinimum :
    ∀ (H L : ℕ), 0 < L → ∀ A : Finset (Fin (2*H+1)), let cnt := fun (U : Finset (Fin (2*H+1))) (b : ℕ) => (U.filter (fun i => i.val % L = b)).card; let hit := fun (U : Finset (Fin (2*H+1))) => (U.filter (fun i => i.rev ∈ U)).card; let same := fun (U : Finset (Fin (2*H+1))) => ∀ b : Fin L, cnt U b.val = cnt A b.val; let lower := ∑ b : Fin L, (cnt A b.val + cnt A ((2*H+L-b.val) % L) - cnt Finset.univ b.val); (∀ U, same U → lower ≤ hit U) ∧ ∃ U, same U ∧ hit U = lower := by
  intro H L hL A cnt hit same lower
  have hcnt_inter : ∀ U b, cnt U b = (U ∩ classSet H L b).card := by
    intro U b
    dsimp [cnt, classSet]
    congr 1
    ext i
    simp
  have hcnt_univ : ∀ b, cnt Finset.univ b = (classSet H L b).card := by
    intro b
    rw [hcnt_inter, Finset.univ_inter]
  have hcnt_le : ∀ b : Fin L, cnt A b.val ≤ (classSet H L b.val).card := by
    intro b
    rw [hcnt_inter, ← Finset.univ_inter (classSet H L b.val), ← hcnt_inter]
    rw [hcnt_inter, Finset.univ_inter]
    exact Finset.card_le_card Finset.inter_subset_right
  constructor
  · intro U hsame
    have hterm : ∀ b : Fin L,
        cnt A b.val + cnt A (revMod H L b.val) - cnt Finset.univ b.val ≤
          ((U ∩ classSet H L b.val).filter (fun i => i.rev ∈ U)).card := by
      intro b
      let S := classSet H L b.val
      let Ub := U ∩ S
      let Vb := (U ∩ classSet H L (revMod H L b.val)).image Fin.rev
      have hUb_sub : Ub ⊆ S := Finset.inter_subset_right
      have hVb_sub : Vb ⊆ S := by
        intro x hx
        rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
        exact (rev_mem_classSet H L b.val hL b.isLt y).mpr (Finset.mem_inter.mp hy).2
      have hVb_card : Vb.card = cnt A (revMod H L b.val) := by
        dsimp [Vb]
        rw [Finset.card_image_of_injOn (fun x _ y _ h => Fin.rev_injective h), ← hcnt_inter]
        let b' : Fin L := ⟨revMod H L b.val, rev_mod_lt H L b.val hL⟩
        have hb'_val : revMod H L b.val = b'.val := rfl
        rw [hb'_val, hsame b']
      have hUb_card : Ub.card = cnt A b.val := by
        rw [← hcnt_inter, hsame b]
      have hunion_le : (Ub ∪ Vb).card ≤ S.card :=
        Finset.card_le_card (Finset.union_subset hUb_sub hVb_sub)
      have hie := Finset.card_union_add_card_inter Ub Vb
      rw [hUb_card, hVb_card] at hie
      have hinter_eq : Ub ∩ Vb = (U ∩ classSet H L b.val).filter (fun i => i.rev ∈ U) :=
        (class_hit_eq_inter H L hL U b).symm
      rw [hinter_eq] at hie
      rw [hcnt_univ b.val]
      change cnt A b.val + cnt A (revMod H L b.val) - S.card ≤ _
      omega
    dsimp [lower, hit]
    rw [hit_eq_sum H L hL U]
    exact Finset.sum_le_sum fun b _ => hterm b
  · let U : Finset (Fin (2 * H + 1)) :=
      Finset.univ.biUnion fun b : Fin L =>
        (classSet H L b.val).filter (fun i => rankFin (classSet H L b.val) i < cnt A b.val)
    have hU_inter : ∀ b : Fin L,
        U ∩ classSet H L b.val =
          (classSet H L b.val).filter (fun i => rankFin (classSet H L b.val) i < cnt A b.val) := by
      intro b
      ext i
      simp only [U, Finset.mem_inter, Finset.mem_biUnion, Finset.mem_univ, Finset.mem_filter,
        true_and]
      constructor
      · rintro ⟨⟨c, hcS, hcr⟩, hiS⟩
        have hc1 : i.val % L = c.val := (Finset.mem_filter.mp hcS).2
        have hb1 : i.val % L = b.val := (Finset.mem_filter.mp hiS).2
        have hcb : c = b := Fin.ext (hc1.symm.trans hb1)
        subst hcb
        exact ⟨hiS, hcr⟩
      · rintro ⟨hiS, hrank⟩
        exact ⟨⟨b, hiS, hrank⟩, hiS⟩
    have hUsame : same U := by
      intro b
      rw [hcnt_inter, hU_inter b]
      rw [card_filter_rankFin (classSet H L b.val) (fun k => k < cnt A b.val)]
      have hfilt : (Finset.range (classSet H L b.val).card).filter (· < cnt A b.val) =
          Finset.range (cnt A b.val) := by
        have hle := hcnt_le b
        ext k
        simp only [Finset.mem_filter, Finset.mem_range]
        omega
      rw [hfilt, Finset.card_range]
    refine ⟨U, hUsame, ?_⟩
    dsimp [hit, lower]
    rw [hit_eq_sum H L hL U]
    apply Finset.sum_congr rfl
    intro b _
    rw [hU_inter b]
    let b' : Fin L := ⟨revMod H L b.val, rev_mod_lt H L b.val hL⟩
    have hb'_val : revMod H L b.val = b'.val := rfl
    let S := classSet H L b.val
    let T := classSet H L (revMod H L b.val)
    have hT_card : T.card = S.card := classSet_card_rev H L b.val hL b.isLt
    have hu' : cnt A (revMod H L b.val) ≤ S.card := by
      rw [← hT_card, hb'_val]
      exact hcnt_le b'
    have hu : cnt A b.val ≤ S.card := hcnt_le b
    have hfilt_eq :
        ((S.filter (fun i => rankFin S i < cnt A b.val)).filter (fun i => i.rev ∈ U)) =
          S.filter (fun i => S.card - cnt A (revMod H L b.val) ≤ rankFin S i ∧
            rankFin S i < cnt A b.val) := by
      ext i
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨⟨hiS, hri⟩, hirev⟩
        have hirevT : i.rev ∈ classSet H L b'.val :=
          (mem_classSet_rev_iff H L b.val hL b.isLt i).mp hiS
        have hirev_inter : i.rev ∈ U ∩ classSet H L b'.val := Finset.mem_inter.mpr ⟨hirev, hirevT⟩
        rw [hU_inter b'] at hirev_inter
        have hr_rev : rankFin T i.rev < cnt A (revMod H L b.val) := by
          simpa [T, hb'_val] using (Finset.mem_filter.mp hirev_inter).2
        have hsum_r := rankFin_rev_add H L b.val hL b.isLt i hiS
        have hri_lt : rankFin S i < S.card := rankFin_lt_card hiS
        refine ⟨hiS, ?_, hri⟩
        dsimp [S, T] at hsum_r hri_lt hr_rev ⊢
        omega
      · rintro ⟨hiS, hlo, hri⟩
        refine ⟨⟨hiS, hri⟩, ?_⟩
        have hirevT : i.rev ∈ classSet H L b'.val :=
          (mem_classSet_rev_iff H L b.val hL b.isLt i).mp hiS
        have hsum_r := rankFin_rev_add H L b.val hL b.isLt i hiS
        have hri_lt : rankFin S i < S.card := rankFin_lt_card hiS
        have hr_rev : rankFin (classSet H L b'.val) i.rev < cnt A b'.val := by
          dsimp [S] at hlo
          rw [← hb'_val]
          omega
        have hirev_in : i.rev ∈ U ∩ classSet H L b'.val := by
          rw [hU_inter b', Finset.mem_filter]
          exact ⟨hirevT, hr_rev⟩
        exact (Finset.mem_inter.mp hirev_in).1
    rw [hfilt_eq]
    rw [card_filter_rankFin S
      (fun k => S.card - cnt A (revMod H L b.val) ≤ k ∧ k < cnt A b.val)]
    have hico : (Finset.range S.card).filter
        (fun k => S.card - cnt A (revMod H L b.val) ≤ k ∧ k < cnt A b.val) =
        Finset.Ico (S.card - cnt A (revMod H L b.val)) (cnt A b.val) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
      omega
    rw [hico, Nat.card_Ico, hcnt_univ b.val]
    change cnt A b.val - (S.card - cnt A (revMod H L b.val)) =
      cnt A b.val + cnt A (revMod H L b.val) - S.card
    omega
