import Mathlib

namespace GoldbachChildDegenSupport

open Finset Polynomial
open scoped BigOperators

private theorem finset_cover_by_fin :
    ∀ (r : ℕ) (S : Finset ℕ) (d : ℕ), S.card ≤ r →
      ∃ g : Fin r → ℕ, (∀ i, g i ∈ insert d S) ∧ ∀ x ∈ S, ∃ i, g i = x := by
  classical
  intro r
  induction r with
  | zero =>
    intro S d hcard
    have hx_not : ∀ x, x ∉ S := fun x hx => by
      have h1 : ({x} : Finset ℕ).card ≤ S.card :=
        Finset.card_le_card (Finset.singleton_subset_iff.mpr hx)
      simp at h1
      omega
    have h0 : S = ∅ := by
      ext x
      exact ⟨fun hx => absurd hx (hx_not x), fun hx => by simp at hx⟩
    subst h0
    exact ⟨Fin.elim0, fun i => Fin.elim0 i, fun x hx => absurd hx (hx_not x)⟩
  | succ r ih =>
    intro S d hcard
    by_cases hne : S.Nonempty
    · obtain ⟨a, haS⟩ := hne
      let S' := S.filter (· ≠ a)
      have haS' : a ∉ S' := by simp [S']
      have hins : insert a S' = S := by
        ext x
        simp only [S', Finset.mem_insert, Finset.mem_filter]
        constructor
        · rintro (rfl | ⟨hx, _⟩)
          · exact haS
          · exact hx
        · intro hx
          by_cases hxa : x = a
          · exact Or.inl hxa
          · exact Or.inr ⟨hx, hxa⟩
      have hle : S'.card ≤ r := by
        have hc : (insert a S').card = S'.card + 1 := by simp [haS']
        rw [hins] at hc
        omega
      obtain ⟨g', hg'mem, hg'cov⟩ := ih S' a hle
      let g : Fin (r + 1) → ℕ := fun i =>
        if h : i.val = 0 then a else g' ⟨i.val - 1, by omega⟩
      refine ⟨g, ?_, ?_⟩
      · intro i
        dsimp only [g]
        split_ifs with hz
        · exact Finset.mem_insert_of_mem haS
        · have hj := hg'mem ⟨i.val - 1, by omega⟩
          rw [← hins]
          rcases Finset.mem_insert.mp hj with rfl | hj'
          · exact Finset.mem_insert_of_mem (Finset.mem_insert.mpr (Or.inl rfl))
          · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hj')
      · intro x hx
        rw [← hins] at hx
        rcases Finset.mem_insert.mp hx with rfl | hx'
        · exact ⟨0, by simp [g]⟩
        · obtain ⟨j, hj⟩ := hg'cov x hx'
          refine ⟨⟨j.val + 1, by omega⟩, ?_⟩
          dsimp only [g]
          have hne0 : (⟨j.val + 1, by omega⟩ : Fin (r + 1)).val ≠ 0 := by simp
          rw [dif_neg hne0]
          have hidx : (⟨(⟨j.val + 1, by omega⟩ : Fin (r + 1)).val - 1, by omega⟩ : Fin r) = j := by
            ext
            simp
          rw [hidx, hj]
    · have h0 : S = ∅ := by
        ext x
        exact ⟨fun hx => absurd ⟨x, hx⟩ hne, fun hx => by simp at hx⟩
      subst h0
      exact ⟨fun _ => d, fun _ => Finset.mem_insert.mpr (Or.inl rfl), fun _ hx => by simp at hx⟩

private def pickVal {r : ℕ} (m : ℕ) (g : Fin r → ℕ) (o : Option (Fin r)) : ℕ :=
  match o with
  | none => m
  | some i => g i

private def repeatPoly : ℕ → Polynomial ℤ → Polynomial ℤ
  | 0, _ => 0
  | n + 1, P => P + repeatPoly n P

private theorem repeatPoly_eval (n : ℕ) (P : Polynomial ℤ) (x : ℤ) :
    (repeatPoly n P).eval x = (n : ℤ) * P.eval x := by
  induction n with
  | zero => simp [repeatPoly]
  | succ n ih =>
    simp only [repeatPoly, Polynomial.eval_add, ih, Nat.cast_succ]
    ring

private theorem repeatPoly_natDegree_le (n : ℕ) (P : Polynomial ℤ) :
    (repeatPoly n P).natDegree ≤ P.natDegree := by
  induction n with
  | zero => simp [repeatPoly]
  | succ n ih =>
    exact (Polynomial.natDegree_add_le _ _).trans (max_le le_rfl ih)

private theorem repeatPoly_coeff (n : ℕ) (P : Polynomial ℤ) (k : ℕ) :
    (repeatPoly n P).coeff k = (n : ℤ) * P.coeff k := by
  induction n with
  | zero => simp [repeatPoly]
  | succ n ih =>
    simp only [repeatPoly, Polynomial.coeff_add, ih, Nat.cast_succ]
    ring

private theorem exists_degen_encoding (r : ℕ) (A : Finset ℕ) (u v : Fin 4 → ℕ)
    (huA : ∀ j : Fin 4, u j ∈ A) (hvA : ∀ j : Fin 4, v j ∈ A)
    (hdisj : ∀ q : Fin 4 × Fin 4, u q.1 ≠ v q.2)
    (hcard : (Finset.image u Finset.univ ∪ Finset.image v Finset.univ).card ≤ r + 1) :
    ∃ b : ((Fin 4 → Option (Fin r)) × (Fin 4 → Option (Fin r))) × (Fin r → ℕ),
      b.1.1 0 = none ∧ (∀ j : Fin 4, b.1.2 j ≠ none) ∧ (∀ i : Fin r, b.2 i ∈ A) ∧
      (∀ j : Fin 4, pickVal (u 0) b.2 (b.1.1 j) = u j) ∧
      (∀ j : Fin 4, pickVal (u 0) b.2 (b.1.2 j) = v j) := by
  classical
  let V := Finset.image u Finset.univ ∪ Finset.image v Finset.univ
  let m := u 0
  let V' := V.filter (· ≠ m)
  have hmV : m ∈ V :=
    Finset.mem_union_left _ (Finset.mem_image.mpr ⟨0, Finset.mem_univ 0, rfl⟩)
  have hins : insert m V' = V := by
    ext x
    simp only [V', Finset.mem_insert, Finset.mem_filter]
    constructor
    · rintro (rfl | ⟨hx, _⟩)
      · exact hmV
      · exact hx
    · intro hx
      by_cases hx0 : x = m
      · exact Or.inl hx0
      · exact Or.inr ⟨hx, hx0⟩
  have hm_not : m ∉ V' := by simp [V']
  have hV'card : V'.card ≤ r := by
    have h1 : (insert m V').card = V'.card + 1 := by simp [hm_not]
    rw [hins] at h1
    omega
  obtain ⟨g, hg_mem, hg_cov⟩ := finset_cover_by_fin r V' m hV'card
  have hVA : ∀ x ∈ V, x ∈ A := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx1 | hx2
    · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx1
      exact huA j
    · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx2
      exact hvA j
  let α : Fin 4 → Option (Fin r) := fun j =>
    if hjm : u j = m then none
    else
      some (Classical.choose (hg_cov (u j) (Finset.mem_filter.mpr
        ⟨Finset.mem_union_left _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩), hjm⟩)))
  let β : Fin 4 → Option (Fin r) := fun j =>
    some (Classical.choose (hg_cov (v j) (Finset.mem_filter.mpr
      ⟨Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩),
        (hdisj (0, j)).symm⟩)))
  refine ⟨((α, β), g), ?_, ?_, ?_, ?_, ?_⟩
  · simp [α, m]
  · intro j
    simp [β]
  · intro i
    have hi := hg_mem i
    rw [hins] at hi
    exact hVA (g i) hi
  · intro j
    by_cases hjm : u j = m
    · simp [α, pickVal, hjm]
    · simp only [α, dif_neg hjm, pickVal]
      exact Classical.choose_spec (hg_cov (u j) (Finset.mem_filter.mpr
        ⟨Finset.mem_union_left _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩), hjm⟩))
  · intro j
    simp only [β, pickVal]
    exact Classical.choose_spec (hg_cov (v j) (Finset.mem_filter.mpr
      ⟨Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩),
        (hdisj (0, j)).symm⟩))

theorem prove_degen_support :
    ∀ (x1 : Polynomial ℤ), (3 : ℕ) ≤ x1.natDegree →
      ∀ (x3 : ℝ), (0 : ℝ) < x3 →
        ∃ (x5 : ℝ), (0 : ℝ) < x5 ∧
          ∀ (x6 : ℕ), (2 : ℕ) ≤ x6 →
            ∀ x8 ⊆ Finset.Icc (1 : ℕ) x6,
              have x10 : Finset (Fin (4 : ℕ) → ℕ) := Fintype.piFinset fun (x10 : Fin (4 : ℕ)) => x8;
              let x11 : (Fin (4 : ℕ) → ℕ) → ℤ := fun (x11 : Fin (4 : ℕ) → ℕ) => ∑ x12 : Fin (4 : ℕ), Polynomial.eval (↑(x11 x12) : ℤ) x1;
              have x12 : Finset ((Fin (4 : ℕ) → ℕ) × (Fin (4 : ℕ) → ℕ)) := {x12 ∈ x10.product x10 | x11 x12.1 = x11 x12.2 ∧ ∀ (x13 : Fin (4 : ℕ) × Fin (4 : ℕ)), x12.1 x13.1 ≠ x12.2 x13.2};
              have x13 : Finset ((Fin (4 : ℕ) → ℕ) × (Fin (4 : ℕ) → ℕ)) := {x13 ∈ x12 | ∀ (x14 x15 : Fin (4 : ℕ) × Fin (4 : ℕ)), x14.1 ≠ x14.2 → x15.1 ≠ x15.2 → x13.1 x14.1 + x13.1 x14.2 ≠ x13.2 x15.1 + x13.2 x15.2 ∧ x13.1 x14.1 ^ (2 : ℕ) + x13.1 x14.2 ^ (2 : ℕ) ≠ x13.2 x15.1 ^ (2 : ℕ) + x13.2 x15.2 ^ (2 : ℕ)};
              have x14 : (Fin (4 : ℕ) → ℕ) × (Fin (4 : ℕ) → ℕ) → Finset ℕ := fun (x14 : (Fin (4 : ℕ) → ℕ) × (Fin (4 : ℕ) → ℕ)) => Finset.image x14.1 Finset.univ ∪ Finset.image x14.2 Finset.univ;
              (↑{x15 ∈ x13 | (x14 x15).card ≤ if x1.natDegree = (3 : ℕ) then (6 : ℕ) else (5 : ℕ)}.card : ℝ) ≤ x5 * (↑x6 : ℝ) ^ x3 * (↑x8.card : ℝ) ^ if x1.natDegree = (3 : ℕ) then (5 : ℕ) else (4 : ℕ) := by
  classical
  intro P hdeg ε hε
  let K : ℕ := if P.natDegree = 3 then 6 else 5
  let r : ℕ := K - 1
  have hr_eq : r = if P.natDegree = 3 then 5 else 4 := by
    by_cases h3 : P.natDegree = 3 <;> simp [r, K, h3]
  have hKr : K = r + 1 := by
    by_cases h3 : P.natDegree = 3 <;> simp [K, r, h3]
  let Pat := (Fin 4 → Option (Fin r)) × (Fin 4 → Option (Fin r))
  let BaseLeft : Finset Pat :=
    Finset.univ.filter fun π : Pat => π.1 0 = none ∧ ∀ j : Fin 4, π.2 j ≠ none
  let C : ℝ := (BaseLeft.card : ℝ) * (P.natDegree : ℝ) + 1
  refine ⟨C, by positivity, ?_⟩
  intro M hM A hA
  dsimp only
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by omega)
  have hpowM : 1 ≤ (M : ℝ) ^ ε := Real.one_le_rpow hM1 hε.le
  let T : Finset (Fin 4 → ℕ) := Fintype.piFinset (fun _ : Fin 4 => A)
  let w : (Fin 4 → ℕ) → ℤ := fun u => ∑ j : Fin 4, P.eval (u j : ℤ)
  let valAt (g : Fin r → ℕ) (o : Option (Fin r)) : ℤ :=
    match o with
    | none => 0
    | some i => P.eval (g i : ℤ)
  let polyOf (π : Pat) (g : Fin r → ℕ) : Polynomial ℤ :=
    let c : ℕ := (Finset.univ.filter fun j : Fin 4 => π.1 j = none).card
    let rhs : ℤ := (∑ j : Fin 4, valAt g (π.2 j)) - (∑ j : Fin 4, valAt g (π.1 j))
    repeatPoly c P - Polynomial.C rhs
  let Base := BaseLeft.product (Fintype.piFinset (fun _ : Fin r => A))
  let Fib (b : Pat × (Fin r → ℕ)) : Finset ℤ := (polyOf b.1 b.2).roots.toFinset
  have hpoly_deg (π : Pat) (g : Fin r → ℕ) : (polyOf π g).natDegree ≤ P.natDegree := by
    dsimp only [polyOf]
    exact (Polynomial.natDegree_sub_le _ _).trans
      (max_le (repeatPoly_natDegree_le _ P) (by simp))
  have hpoly_ne (b : Pat × (Fin r → ℕ)) (hb : b ∈ Base) : polyOf b.1 b.2 ≠ 0 := by
    have hbL := (Finset.mem_filter.mp (Finset.mem_product.mp hb).1).2
    have h0mem : (0 : Fin 4) ∈ Finset.univ.filter (fun j : Fin 4 => b.1.1 j = none) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ 0, hbL.1⟩
    have hc_pos : 1 ≤ (Finset.univ.filter (fun j : Fin 4 => b.1.1 j = none)).card := by
      have h1 := Finset.card_le_card (Finset.singleton_subset_iff.mpr h0mem)
      simpa using h1
    have hc_ne : ((Finset.univ.filter (fun j : Fin 4 => b.1.1 j = none)).card : ℤ) ≠ 0 := by
      omega
    have hP0 : P ≠ 0 := by
      intro he
      simp [he] at hdeg
    have hlead : P.coeff P.natDegree ≠ 0 := by
      rw [Polynomial.coeff_natDegree]
      exact Polynomial.leadingCoeff_ne_zero.mpr hP0
    intro hzero
    have hcoeff := congrArg (fun q : Polynomial ℤ => q.coeff P.natDegree) hzero
    dsimp only [polyOf] at hcoeff
    rw [Polynomial.coeff_sub, repeatPoly_coeff,
      Polynomial.coeff_C_of_ne_zero (by omega), sub_zero, Polynomial.coeff_zero] at hcoeff
    exact (mul_ne_zero hc_ne hlead) hcoeff
  have hbound (G : Finset ((Fin 4 → ℕ) × (Fin 4 → ℕ)))
      (hG : ∀ z ∈ G, z ∈ T.product T ∧ w z.1 = w z.2 ∧
        (∀ q : Fin 4 × Fin 4, z.1 q.1 ≠ z.2 q.2) ∧
        (Finset.image z.1 Finset.univ ∪ Finset.image z.2 Finset.univ).card ≤ K) :
      G.card ≤ BaseLeft.card * P.natDegree * A.card ^ r := by
    have hex : ∀ z ∈ G, ∃ b : Pat × (Fin r → ℕ),
        b.1.1 0 = none ∧ (∀ j : Fin 4, b.1.2 j ≠ none) ∧ (∀ i : Fin r, b.2 i ∈ A) ∧
        (∀ j : Fin 4, pickVal (z.1 0) b.2 (b.1.1 j) = z.1 j) ∧
        (∀ j : Fin 4, pickVal (z.1 0) b.2 (b.1.2 j) = z.2 j) := by
      intro z hz
      obtain ⟨hzT, _, hdisj, hcard⟩ := hG z hz
      obtain ⟨hz1, hz2⟩ := Finset.mem_product.mp hzT
      exact exists_degen_encoding r A z.1 z.2
        (Fintype.mem_piFinset.mp hz1) (Fintype.mem_piFinset.mp hz2) hdisj (hKr ▸ hcard)
    let encode (z : (Fin 4 → ℕ) × (Fin 4 → ℕ)) : Σ _ : Pat × (Fin r → ℕ), ℤ :=
      if hz : z ∈ G then ⟨Classical.choose (hex z hz), (z.1 0 : ℤ)⟩
      else ⟨((fun _ => none, fun _ => none), fun _ => 0), 0⟩
    have hspec_cov {z : (Fin 4 → ℕ) × (Fin 4 → ℕ)} (hz : z ∈ G) :
        (∀ j : Fin 4, pickVal (z.1 0) (encode z).1.2 ((encode z).1.1.1 j) = z.1 j) ∧
        (∀ j : Fin 4, pickVal (z.1 0) (encode z).1.2 ((encode z).1.1.2 j) = z.2 j) ∧
        (encode z).1 ∈ Base ∧ (encode z).2 = (z.1 0 : ℤ) := by
      dsimp only [encode]
      rw [dif_pos hz]
      have hspec := Classical.choose_spec (hex z hz)
      refine ⟨hspec.2.2.2.1, hspec.2.2.2.2, ?_, rfl⟩
      exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hspec.1, hspec.2.1⟩,
        Fintype.mem_piFinset.mpr hspec.2.2.1⟩
    have hmaps : Set.MapsTo encode (↑G : Set ((Fin 4 → ℕ) × (Fin 4 → ℕ)))
        (↑(Base.sigma Fib) : Set (Σ _ : Pat × (Fin r → ℕ), ℤ)) := by
      intro z hz
      obtain ⟨hu_eq, hv_eq, hb_mem, hm_eq⟩ := hspec_cov hz
      apply Finset.mem_sigma.mpr
      refine ⟨hb_mem, Multiset.mem_toFinset.mpr ((Polynomial.mem_roots (hpoly_ne _ hb_mem)).mpr ?_)⟩
      rw [hm_eq]
      dsimp only [polyOf]
      rw [Polynomial.eval_sub, repeatPoly_eval, Polynomial.eval_C]
      let π := (encode z).1.1
      let g := (encode z).1.2
      let m := z.1 0
      have hterm1 (j : Fin 4) :
          P.eval (z.1 j : ℤ) = (if π.1 j = none then P.eval (m : ℤ) else 0) + valAt g (π.1 j) := by
        have hpick := hu_eq j
        rw [← hpick]
        cases hopt : π.1 j <;> simp [hopt, pickVal, valAt]
      have hterm2 (j : Fin 4) : P.eval (z.2 j : ℤ) = valAt g (π.2 j) := by
        have hpick := hv_eq j
        have hne : π.2 j ≠ none := (Finset.mem_filter.mp (Finset.mem_product.mp hb_mem).1).2.2 j
        rw [← hpick]
        cases hopt : π.2 j <;> simp_all [pickVal, valAt]
      have hsum1 : w z.1 =
          ((Finset.univ.filter fun j : Fin 4 => π.1 j = none).card : ℤ) * P.eval (m : ℤ) +
            ∑ j : Fin 4, valAt g (π.1 j) := by
        dsimp only [w]
        simp_rw [hterm1]
        rw [Finset.sum_add_distrib, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      have hsum2 : w z.2 = ∑ j : Fin 4, valAt g (π.2 j) := by
        dsimp only [w]
        simp_rw [hterm2]
      have hweq := (hG z hz).2.1
      linarith only [hweq, hsum1, hsum2]
    have hinj : Set.InjOn encode (↑G : Set ((Fin 4 → ℕ) × (Fin 4 → ℕ))) := by
      intro z₁ hz₁ z₂ hz₂ heq
      obtain ⟨hu₁, hv₁, _, hm₁⟩ := hspec_cov hz₁
      obtain ⟨hu₂, hv₂, _, hm₂⟩ := hspec_cov hz₂
      have hbase : (encode z₁).1 = (encode z₂).1 :=
        congrArg (fun p : Σ _ : Pat × (Fin r → ℕ), ℤ => p.1) heq
      have hfval : (encode z₁).2 = (encode z₂).2 :=
        congrArg (fun p : Σ _ : Pat × (Fin r → ℕ), ℤ => p.2) heq
      have hm_nat : z₁.1 0 = z₂.1 0 := Int.ofNat.inj (hm₁.symm.trans (hfval.trans hm₂))
      have hπ : (encode z₁).1.1 = (encode z₂).1.1 := congrArg Prod.fst hbase
      have hg : (encode z₁).1.2 = (encode z₂).1.2 := congrArg Prod.snd hbase
      apply Prod.ext
      · funext j
        rw [← hu₁ j, ← hu₂ j, hm_nat, hπ, hg]
      · funext j
        rw [← hv₁ j, ← hv₂ j, hm_nat, hπ, hg]
    calc
      G.card ≤ (Base.sigma Fib).card := Finset.card_le_card_of_injOn encode hmaps hinj
      _ = ∑ b ∈ Base, (Fib b).card := Finset.card_sigma _ _
      _ ≤ ∑ _b ∈ Base, P.natDegree := by
        apply Finset.sum_le_sum
        intro b _
        exact (Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' _).trans (hpoly_deg b.1 b.2))
      _ = Base.card * P.natDegree := by simp [nsmul_eq_mul]
      _ = BaseLeft.card * A.card ^ r * P.natDegree := by
        simp only [Base, Finset.card_product, Fintype.card_piFinset_const, Fintype.card_fin]
      _ = BaseLeft.card * P.natDegree * A.card ^ r := by ring
  refine le_trans (Nat.cast_le.mpr (hbound _ ?_)) ?_
  · intro z hz
    rw [Finset.mem_filter] at hz
    obtain ⟨hz13, hcard⟩ := hz
    rw [Finset.mem_filter] at hz13
    obtain ⟨hz12, _⟩ := hz13
    rw [Finset.mem_filter] at hz12
    obtain ⟨hzT, hweq, hdisj⟩ := hz12
    exact ⟨hzT, hweq, fun q => hdisj q, hcard⟩
  · push_cast
    rw [← hr_eq]
    have hC_ge : (BaseLeft.card : ℝ) * (P.natDegree : ℝ) ≤ C := by
      dsimp only [C]
      linarith
    calc
      (BaseLeft.card : ℝ) * (P.natDegree : ℝ) * (A.card : ℝ) ^ r
        = ((BaseLeft.card : ℝ) * (P.natDegree : ℝ) * (A.card : ℝ) ^ r) * 1 := by ring
      _ ≤ ((BaseLeft.card : ℝ) * (P.natDegree : ℝ) * (A.card : ℝ) ^ r) * (M : ℝ) ^ ε :=
        mul_le_mul_of_nonneg_left hpowM (by positivity)
      _ = (BaseLeft.card : ℝ) * (P.natDegree : ℝ) * (M : ℝ) ^ ε * (A.card : ℝ) ^ r := by ring
      _ ≤ C * (M : ℝ) ^ ε * (A.card : ℝ) ^ r := by gcongr

end GoldbachChildDegenSupport

theorem Conjectures.Cuts.Task4bdabed8fa607625bcad4247 : (∀ (x1 : Polynomial ℤ),   (3 : ℕ) ≤ x1.natDegree →     ∀ (x3 : ℝ),       (0 : ℝ) < x3 →         ∃ (x5 : ℝ),           (0 : ℝ) < x5 ∧             ∀ (x6 : ℕ),               (2 : ℕ) ≤ x6 →                 ∀ x8 ⊆ Finset.Icc (1 : ℕ) x6,                   have x10 : Finset (Fin (4 : ℕ) → ℕ) := Fintype.piFinset fun (x10 : Fin (4 : ℕ)) => x8;                   let x11 : (Fin (4 : ℕ) → ℕ) → ℤ := fun (x11 : Fin (4 : ℕ) → ℕ) => ∑ x12 : Fin (4 : ℕ), Polynomial.eval (↑(x11 x12) : ℤ) x1;                   have x12 : Finset ((Fin (4 : ℕ) → ℕ) × (Fin (4 : ℕ) → ℕ)) := {x12 ∈ x10.product x10 | x11 x12.1 = x11 x12.2 ∧ ∀ (x13 : Fin (4 : ℕ) × Fin (4 : ℕ)), x12.1 x13.1 ≠ x12.2 x13.2};                   have x13 : Finset ((Fin (4 : ℕ) → ℕ) × (Fin (4 : ℕ) → ℕ)) := {x13 ∈ x12 | ∀ (x14 x15 : Fin (4 : ℕ) × Fin (4 : ℕ)), x14.1 ≠ x14.2 → x15.1 ≠ x15.2 → x13.1 x14.1 + x13.1 x14.2 ≠ x13.2 x15.1 + x13.2 x15.2 ∧ x13.1 x14.1 ^ (2 : ℕ) + x13.1 x14.2 ^ (2 : ℕ) ≠ x13.2 x15.1 ^ (2 : ℕ) + x13.2 x15.2 ^ (2 : ℕ)};                   have x14 : (Fin (4 : ℕ) → ℕ) × (Fin (4 : ℕ) → ℕ) → Finset ℕ := fun (x14 : (Fin (4 : ℕ) → ℕ) × (Fin (4 : ℕ) → ℕ)) => Finset.image x14.1 Finset.univ ∪ Finset.image x14.2 Finset.univ;                   (↑{x15 ∈ x13 | (x14 x15).card ≤ if x1.natDegree = (3 : ℕ) then (6 : ℕ) else (5 : ℕ)}.card : ℝ) ≤ x5 * (↑x6 : ℝ) ^ x3 * (↑x8.card : ℝ) ^ if x1.natDegree = (3 : ℕ) then (5 : ℕ) else (4 : ℕ)) :=
  GoldbachChildDegenSupport.prove_degen_support
