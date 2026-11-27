import Mathlib

/-!
# Cyclic small rows at one-third density

For `n = 3k + 1` and the seed `S = [0, k-2] ∪ {2k-3}` of size `k`, every
subset `A` of size 2 or 3 (or with complement of size 2 or 3) has a cyclic
translate `S + t` whose intersection size with `A` avoids any prescribed
pair `{a, a+1}` of consecutive integers.
-/

open scoped Fin.NatCast

namespace Conjectures.LogRank

private lemma mem_seed {k n : ℕ} (i : Fin n) :
    i ∈ ((Finset.univ : Finset (Fin n)).filter (fun j => j.val ≤ k - 2 ∨ j.val = 2 * k - 3)) ↔
      i.val ≤ k - 2 ∨ i.val = 2 * k - 3 := by
  simp

private lemma seed_card {k n : ℕ} (hk : 6 ≤ k) (hn : n = 3 * k + 1) :
    ((Finset.univ : Finset (Fin n)).filter (fun j => j.val ≤ k - 2 ∨ j.val = 2 * k - 3)).card = k := by
  let L := (Finset.univ : Finset (Fin n)).filter (fun j : Fin n => j.val ≤ k - 2)
  let P := (Finset.univ : Finset (Fin n)).filter (fun j : Fin n => j.val = 2 * k - 3)
  have hlt : 2 * k - 3 < n := by omega
  have hdisj : Disjoint L P := by
    rw [Finset.disjoint_left]
    intro j hjL hjP
    have h1 : j.val ≤ k - 2 := by simpa [L] using hjL
    have h2 : j.val = 2 * k - 3 := by simpa [P] using hjP
    omega
  have hLP : ((Finset.univ : Finset (Fin n)).filter (fun j => j.val ≤ k - 2 ∨ j.val = 2 * k - 3)) = L ∪ P := by
    ext j
    simp [L, P]
  rw [hLP, Finset.card_union_of_disjoint hdisj]
  have hcardL : L.card = k - 1 := by
    let e : {j : Fin n // j.val ≤ k - 2} ≃ Fin (k - 1) where
      toFun x := ⟨x.1.val, by have := x.2; omega⟩
      invFun y := ⟨⟨y.val, by omega⟩, by omega⟩
      left_inv x := by ext; rfl
      right_inv y := by ext; rfl
    change (Finset.univ.filter (fun j : Fin n => j.val ≤ k - 2)).card = k - 1
    simpa [L] using Fintype.card_congr e
  have hcardP : P.card = 1 := by
    have hsingle : P = {⟨2 * k - 3, hlt⟩} := by
      ext j
      simp [P, Fin.ext_iff]
    rw [hsingle, Finset.card_singleton]
  rw [hcardL, hcardP]
  omega

/-- The seed differences cover every nonzero residue mod n. -/
private lemma seed_diff_covers {k n : ℕ} (hk : 6 ≤ k) (hn : n = 3 * k + 1)
    {d : ℕ} (hdpos : 0 < d) (hdlt : d < n) :
    ∃ s s' : Fin n,
      (s.val ≤ k - 2 ∨ s.val = 2 * k - 3) ∧
      (s'.val ≤ k - 2 ∨ s'.val = 2 * k - 3) ∧
      (s.val + n - s'.val) % n = d := by
  by_cases h1 : d ≤ k - 2
  · refine ⟨⟨d, hdlt⟩, ⟨0, by omega⟩, ?_, ?_, ?_⟩
    · left; simp
    · left; simp; omega
    · simp [Nat.mod_eq_of_lt hdlt]
  · have hdge : k - 1 ≤ d := by omega
    by_cases h2 : d ≤ 2 * k - 3
    · refine ⟨⟨2 * k - 3, by omega⟩, ⟨2 * k - 3 - d, by omega⟩, ?_, ?_, ?_⟩
      · right; simp
      · left; simp; omega
      · have hs : 2 * k - 3 + n - (2 * k - 3 - d) = n + d := by omega
        rw [hs]
        simp [Nat.add_mod, Nat.mod_eq_of_lt hdlt]
    · have hdge2 : 2 * k - 2 ≤ d := by omega
      let e := n - d
      have hepos : 0 < e := by dsimp [e]; omega
      have hele : e ≤ k + 3 := by dsimp [e]; omega
      by_cases h3 : e ≤ k - 2
      · refine ⟨⟨0, by omega⟩, ⟨e, by omega⟩, ?_, ?_, ?_⟩
        · left; simp; omega
        · left; simp; omega
        · have hs : 0 + n - e = d := by dsimp [e]; omega
          rw [hs, Nat.mod_eq_of_lt hdlt]
      · have hege : k - 1 ≤ e := by omega
        refine ⟨⟨2 * k - 3 - e, by omega⟩, ⟨2 * k - 3, by omega⟩, ?_, ?_, ?_⟩
        · left; simp; omega
        · right; simp
        · have hs : 2 * k - 3 - e + n - (2 * k - 3) = d := by dsimp [e]; omega
          rw [hs, Nat.mod_eq_of_lt hdlt]

/-- Any two distinct points lie in a common translate of the seed. -/
private lemma pair_in_common_shift {k n : ℕ} (hk : 6 ≤ k) (hn : n = 3 * k + 1)
    (p q : Fin n) (hpq : p ≠ q) :
    ∃ t : Fin n,
      p ∈ ((Finset.univ : Finset (Fin n)).filter (fun j => j.val ≤ k - 2 ∨ j.val = 2 * k - 3)).image (fun i => i + t) ∧
      q ∈ ((Finset.univ : Finset (Fin n)).filter (fun j => j.val ≤ k - 2 ∨ j.val = 2 * k - 3)).image (fun i => i + t) := by
  classical
  let S : Finset (Fin n) := (Finset.univ : Finset (Fin n)).filter (fun j => j.val ≤ k - 2 ∨ j.val = 2 * k - 3)
  let d := (q.val + n - p.val) % n
  have hdlt : d < n := Nat.mod_lt _ (by omega)
  have hdpos : 0 < d := by
    have hne : q.val ≠ p.val := by
      intro h
      apply hpq
      apply Fin.ext
      exact h.symm
    have hltq : q.val < n := q.isLt
    have hltp : p.val < n := p.isLt
    have hsum : q.val + n - p.val = n + (q.val - p.val) := by omega
    rw [hsum, Nat.add_mod]
    simp only [Nat.mod_self, zero_add, Nat.mod_mod]
    have : (q.val - p.val) % n = q.val - p.val := Nat.mod_eq_of_lt (by omega)
    rw [this]
    omega
  rcases seed_diff_covers hk hn hdpos hdlt with ⟨s, s', hsS, hs'S, hdiff⟩
  refine ⟨p - s', ?_, ?_⟩
  · refine Finset.mem_image.mpr ⟨s', ?_, ?_⟩
    · simpa [S] using hs'S
    · simp [S]
    abel
  · refine Finset.mem_image.mpr ⟨s, ?_, ?_⟩
    · simpa [S] using hsS
    · have hsd : (s - s' : Fin n) = q - p := by
        apply Fin.ext
        dsimp [d] at hdiff
        -- Fin subtraction val is (a.val + n - b.val) % n
        change (s.val + n - s'.val) % n = (q.val + n - p.val) % n
        exact hdiff
      calc
        s + (p - s') = p + (s - s') := by abel
        _ = p + (q - p) := by rw [hsd]
        _ = q := by abel

/-- Total intersection count over all translates. -/
private lemma sum_inter_shift {n : ℕ} [NeZero n] (A S : Finset (Fin n)) :
    (∑ t : Fin n, (A ∩ S.image (fun i => i + t)).card) = A.card * S.card := by
  classical
  calc
    (∑ t : Fin n, (A ∩ S.image (fun i => i + t)).card)
        = ∑ t : Fin n, ∑ x ∈ A, if x ∈ S.image (fun i => i + t) then 1 else 0 := by
            refine Finset.sum_congr rfl fun t _ => ?_
            rw [Finset.card_eq_sum_ones]
            simp [Finset.sum_filter]
    _ = ∑ x ∈ A, ∑ t : Fin n, if x ∈ S.image (fun i => i + t) then 1 else 0 := by
            rw [Finset.sum_comm]
    _ = ∑ x ∈ A, S.card := by
            refine Finset.sum_congr rfl fun x hx => ?_
            have hbij : (Finset.univ.filter (fun t : Fin n => x ∈ S.image (fun i => i + t))).card = S.card := by
              let f : Fin n → Fin n := fun t => x - t
              have hinj : Function.Injective f := by
                intro a b h
                dsimp [f] at h
                exact sub_right_injective h
              have himage : (Finset.univ.image f) = (Finset.univ.filter (fun t : Fin n => x ∈ S.image (fun i => i + t))) := by
                ext t
                simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
                constructor
                · rintro ⟨u, -, rfl⟩
                  refine ⟨x - u, ?_⟩
                  refine Finset.mem_image.mpr ⟨u, Finset.mem_univ u, ?_⟩
                  simp [f]
                · intro ht
                  rcases ht with ⟨i, hi, hit⟩
                  refine ⟨x - i, Finset.mem_univ _, ?_⟩
                  dsimp [f]
                  rw [hit]
                  abel
              rw [← himage, Finset.card_image_of_injective _ hinj]
              simp
            simpa [Finset.sum_ite, Finset.sum_const, hbij]
    _ = A.card * S.card := by simp

theorem Conjectures.LogRank.CyclicSmallRows :
    ∀ k : ℕ, 6 ≤ k → let n := 3 * k + 1;
      let S := (Finset.univ : Finset (Fin n)).filter (fun i => i.val ≤ k - 2 ∨ i.val = 2 * k - 3);
      let shift := fun (t : Fin n) => S.image (fun i => i + t);
      S.card = k ∧ ∀ A : Finset (Fin n),
        (A.card = 2 ∨ A.card = 3 ∨ Aᶜ.card = 2 ∨ Aᶜ.card = 3) → ∀ a : ℤ,
        ∃ t : Fin n, ¬ (((A ∩ shift t).card : ℤ) = a ∨ ((A ∩ shift t).card : ℤ) = a + 1) := by
  classical
  intro k hk
  let n := 3 * k + 1
  have hnpos : 0 < n := by dsimp [n]; omega
  letI : NeZero n := ⟨hnpos.ne'⟩
  let S : Finset (Fin n) := (Finset.univ : Finset (Fin n)).filter (fun i => i.val ≤ k - 2 ∨ i.val = 2 * k - 3)
  let shift := fun (t : Fin n) => S.image (fun i => i + t)
  change S.card = k ∧ ∀ A : Finset (Fin n),
    (A.card = 2 ∨ A.card = 3 ∨ Aᶜ.card = 2 ∨ Aᶜ.card = 3) → ∀ a : ℤ,
    ∃ t : Fin n, ¬ (((A ∩ shift t).card : ℤ) = a ∨ ((A ∩ shift t).card : ℤ) = a + 1)
  refine ⟨?_, ?_⟩
  · dsimp [S]
    exact seed_card hk rfl
  · intro A hA a
    by_contra hno
    push_neg at hno
    -- Pick B = A or B = Aᶜ (whichever is small) and c so that
    -- |B ∩ shift t| ∈ {c, c+1} for all t, with some t having |B ∩ shift t| ≥ 2.
    have hmain : ∃ (B : Finset (Fin n)) (c : ℤ),
        (B.card = 2 ∨ B.card = 3) ∧
        (∀ t : Fin n, ((B ∩ shift t).card : ℤ) = c ∨ ((B ∩ shift t).card : ℤ) = c + 1) ∧
        (∃ t : Fin n, 2 ≤ (B ∩ shift t).card) := by
      rcases hA with hA2 | hA3 | hAc2 | hAc3
      · refine ⟨A, a, hA2, hno, ?_⟩
        exact two_in_shift hA2
      · refine ⟨A, a, hA3, hno, ?_⟩
        exact two_in_shift hA3
      · refine ⟨Aᶜ, (k : ℤ) - a - 1, hAc2, ?_, ?_⟩
        · intro t
          have hv := hno t
          have hcomp : (Aᶜ ∩ shift t).card + (A ∩ shift t).card = k := by
            have hdisj : Disjoint (Aᶜ ∩ shift t) (A ∩ shift t) := by
              rw [Finset.disjoint_left]
              intro x hx1 hx2
              exact (Finset.mem_compl.mp (Finset.mem_inter.mp hx1).1) (Finset.mem_inter.mp hx2).1
            have hunion : (Aᶜ ∩ shift t) ∪ (A ∩ shift t) = shift t := by
              ext x
              by_cases hxA : x ∈ A <;> simp [hxA]
            rw [← Finset.card_union_of_disjoint hdisj, hunion]
            dsimp [shift, S]
            rw [Finset.card_image_of_injective]
            · dsimp [S]; exact seed_card hk rfl
            · intro x y hxy; exact add_right_cancel hxy
          rcases hv with hv | hv
          · have hv' : (A ∩ shift t).card = a := by exact_mod_cast hv
            simp only [hv'] at hcomp
            omega
          · have hv' : (A ∩ shift t).card = a + 1 := by exact_mod_cast hv
            simp only [hv'] at hcomp
            omega
        · exact two_in_shift hAc2
      · refine ⟨Aᶜ, (k : ℤ) - a - 1, hAc3, ?_, ?_⟩
        · intro t
          have hv := hno t
          have hcomp : (Aᶜ ∩ shift t).card + (A ∩ shift t).card = k := by
            have hdisj : Disjoint (Aᶜ ∩ shift t) (A ∩ shift t) := by
              rw [Finset.disjoint_left]
              intro x hx1 hx2
              exact (Finset.mem_compl.mp (Finset.mem_inter.mp hx1).1) (Finset.mem_inter.mp hx2).1
            have hunion : (Aᶜ ∩ shift t) ∪ (A ∩ shift t) = shift t := by
              ext x
              by_cases hxA : x ∈ A <;> simp [hxA]
            rw [← Finset.card_union_of_disjoint hdisj, hunion]
            dsimp [shift, S]
            rw [Finset.card_image_of_injective]
            · dsimp [S]; exact seed_card hk rfl
            · intro x y hxy; exact add_right_cancel hxy
          rcases hv with hv | hv
          · have hv' : (A ∩ shift t).card = a := by exact_mod_cast hv
            simp only [hv'] at hcomp
            omega
          · have hv' : (A ∩ shift t).card = a + 1 := by exact_mod_cast hv
            simp only [hv'] at hcomp
            omega
        · exact two_in_shift hAc3
    rcases hmain with ⟨B, c, hBcard, hvals, htwo⟩
    have hsumB : (∑ t : Fin n, (B ∩ shift t).card) = B.card * k := by
      rw [sum_inter_shift B S, seed_card hk rfl]
    have hBsmall : B.card ≤ 3 := by omega
    have hBpos : 0 < B.card := by omega
    -- Case split on c
    rcases lt_trichotomy c (-1 : ℤ) with hcneg | hc_eq_neg | hcgtneg
    · have hzero : ∀ t : Fin n, (B ∩ shift t).card = 0 := by
        intro t
        rcases hvals t with hv | hv <;> omega
      have : (∑ t : Fin n, (B ∩ shift t).card) = 0 := by simp [hzero]
      omega
    · subst c
      have hzero : ∀ t : Fin n, (B ∩ shift t).card = 0 := by
        intro t
        rcases hvals t with hv | hv <;> omega
      have : (∑ t : Fin n, (B ∩ shift t).card) = 0 := by simp [hzero]
      omega
    · rcases lt_trichotomy c (0 : ℤ) with hcneg0 | hc_eq_zero | hcgtzero
      · omega
      · subst c
        rcases htwo with ⟨t0, ht0⟩
        have hc0 := hvals t0
        rcases hc0 with hv | hv <;> omega
      · rcases lt_trichotomy c (1 : ℤ) with hc01 | hc_eq_one | hcgtone
        · omega
        · subst c
          have hge1 : ∀ t : Fin n, 1 ≤ (B ∩ shift t).card := by
            intro t
            rcases hvals t with hv | hv <;> omega
          have hsumge : n ≤ ∑ t : Fin n, (B ∩ shift t).card := by
            calc
              n = ∑ t : Fin n, 1 := by simp
              _ ≤ ∑ t : Fin n, (B ∩ shift t).card := Finset.sum_le_sum (fun t _ => hge1 t)
          omega
        · have hge2 : ∀ t : Fin n, 2 ≤ (B ∩ shift t).card := by
            intro t
            rcases hvals t with hv | hv <;> omega
          have hsumge : 2 * n ≤ ∑ t : Fin n, (B ∩ shift t).card := by
            calc
              2 * n = ∑ t : Fin n, 2 := by simp
              _ ≤ ∑ t : Fin n, (B ∩ shift t).card := Finset.sum_le_sum (fun t _ => hge2 t)
          omega
 where
  two_in_shift {B : Finset (Fin n)} (hB : B.card = 2 ∨ B.card = 3) :
      ∃ t : Fin n, 2 ≤ (B ∩ shift t).card := by
    have hBpos : 0 < B.card := by omega
    obtain ⟨p, hp⟩ := Finset.card_pos.mp hBpos
    obtain ⟨q, hq, hpq⟩ : ∃ q ∈ B, q ≠ p := by
      by_contra hnq
      push_neg at hnq
      have hsub : B ⊆ {p} := by
        intro x hx
        by_cases hx' : x = p
        · simp [hx']
        · exfalso; exact hnq x hx hx'
      have : B.card ≤ 1 := by simpa using Finset.card_le_card hsub
      omega
    rcases pair_in_common_shift hk rfl p q hpq with ⟨t, ht1, ht2⟩
    refine ⟨t, ?_⟩
    exact Finset.two_le_card.mpr ⟨p, q, hpq, by simpa [ht1, hp], by simpa [ht2, hq]⟩

end Conjectures.LogRank
