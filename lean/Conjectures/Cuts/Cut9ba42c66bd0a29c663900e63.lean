import Mathlib

-- child 1 zh: 控制无共享指标且左右各存在一对下标普通和相等的四元组多项式等和碰撞数。
-- child 1 en: Bound disjoint-index quadruple polynomial collisions that contain a pair on each side with equal ordinary sum.
-- child 2 zh: 控制无共享指标且左右各存在一对下标平方和相等的四元组多项式等和碰撞数。
-- child 2 en: Bound disjoint-index quadruple polynomial collisions that contain a pair on each side with equal sum of squares.
-- child 3 zh: 控制既无共享指标、又无匹配两项普通和及两项平方和的四元组多项式等和碰撞数。
-- child 3 en: Bound disjoint-index quadruple polynomial collisions with neither equal pair sums nor equal pair sums of squares.

theorem Conjectures.Cuts.Cut9ba42c66bd0a29c663900e63
  (hPairSum : ∀ P : Polynomial ℤ, 3 ≤ P.natDegree → ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ, 2 ≤ M → ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 M →
      let T := Fintype.piFinset (fun _ : Fin 4 => A)
      let w := fun u : Fin 4 → ℕ => ∑ j : Fin 4, P.eval (u j : ℤ)
      (((T.product T).filter (fun z => w z.1 = w z.2 ∧
        (∀ i j : Fin 4, z.1 i ≠ z.2 j) ∧
        (∃ i₁ i₂ j₁ j₂ : Fin 4, i₁ ≠ i₂ ∧ j₁ ≠ j₂ ∧
          z.1 i₁ + z.1 i₂ = z.2 j₁ + z.2 j₂))).card : ℝ) ≤
        C * (M : ℝ) ^ ε * (A.card : ℝ) ^ 4)
  (hPairSq : ∀ P : Polynomial ℤ, 3 ≤ P.natDegree → ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ, 2 ≤ M → ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 M →
      let T := Fintype.piFinset (fun _ : Fin 4 => A)
      let w := fun u : Fin 4 → ℕ => ∑ j : Fin 4, P.eval (u j : ℤ)
      (((T.product T).filter (fun z => w z.1 = w z.2 ∧
        (∀ i j : Fin 4, z.1 i ≠ z.2 j) ∧
        (∃ i₁ i₂ j₁ j₂ : Fin 4, i₁ ≠ i₂ ∧ j₁ ≠ j₂ ∧
          (z.1 i₁)^2 + (z.1 i₂)^2 = (z.2 j₁)^2 + (z.2 j₂)^2))).card : ℝ) ≤
        C * (M : ℝ) ^ ε * (A.card : ℝ) ^ 4)
  (hResidual : ∀ P : Polynomial ℤ, 3 ≤ P.natDegree → ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ, 2 ≤ M → ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 M →
      let T := Fintype.piFinset (fun _ : Fin 4 => A)
      let w := fun u : Fin 4 → ℕ => ∑ j : Fin 4, P.eval (u j : ℤ)
      (((T.product T).filter (fun z => w z.1 = w z.2 ∧
        (∀ i j : Fin 4, z.1 i ≠ z.2 j) ∧
        (∀ i₁ i₂ j₁ j₂ : Fin 4, i₁ ≠ i₂ → j₁ ≠ j₂ →
          z.1 i₁ + z.1 i₂ ≠ z.2 j₁ + z.2 j₂ ∧
          (z.1 i₁)^2 + (z.1 i₂)^2 ≠ (z.2 j₁)^2 + (z.2 j₂)^2))).card : ℝ) ≤
        C * (M : ℝ) ^ ε * (A.card : ℝ) ^ (if P.natDegree = 3 then (5 : ℕ) else 4)) : (∀ (x1 : Polynomial ℤ),   (3 : ℕ) ≤ x1.natDegree →     ∀ (x3 : ℝ),       (0 : ℝ) < x3 →         ∃ (x5 : ℝ),           (0 : ℝ) < x5 ∧             ∀ (x6 : ℕ),               (2 : ℕ) ≤ x6 →                 ∀ x8 ⊆ Finset.Icc (1 : ℕ) x6,                   have x10 : Finset (Fin (4 : ℕ) → ℕ) := Fintype.piFinset fun (x10 : Fin (4 : ℕ)) => x8;                   let x11 : (Fin (4 : ℕ) → ℕ) → ℤ := fun (x11 : Fin (4 : ℕ) → ℕ) => ∑ x12 : Fin (4 : ℕ), Polynomial.eval (↑(x11 x12) : ℤ) x1;                   have x12 : Finset ((Fin (4 : ℕ) → ℕ) × (Fin (4 : ℕ) → ℕ)) := {x12 ∈ x10.product x10 | x11 x12.1 = x11 x12.2 ∧ ∀ (x13 : Equiv.Perm (Fin (4 : ℕ))), x12.2 ≠ x12.1 ∘ (⇑x13 : Fin (4 : ℕ) → Fin (4 : ℕ))};                   (↑{x13 ∈ x12 | ∀ (x14 x15 : Fin (4 : ℕ)), x13.1 x14 ≠ x13.2 x15}.card : ℝ) ≤ x5 * (↑x6 : ℝ) ^ x3 * (↑x8.card : ℝ) ^ if x1.natDegree = (3 : ℕ) then (5 : ℕ) else (4 : ℕ)) := by
  intro P hP ε hε
  obtain ⟨Csum, hCsum, bSum⟩ := hPairSum P hP ε hε
  obtain ⟨Csq, hCsq, bSq⟩ := hPairSq P hP ε hε
  obtain ⟨Cres, hCres, bRes⟩ := hResidual P hP ε hε
  refine ⟨Csum + Csq + Cres, by positivity, ?_⟩
  intro M hM A hA
  dsimp only
  have h1 := bSum M hM A hA
  have h2 := bSq M hM A hA
  have h3 := bRes M hM A hA
  dsimp only at h1 h2 h3
  let T : Finset (Fin 4 → ℕ) := Fintype.piFinset (fun _ : Fin 4 => A)
  let w : (Fin 4 → ℕ) → ℤ := fun u => ∑ j : Fin 4, P.eval (u j : ℤ)
  let S1 := (T.product T).filter (fun z => w z.1 = w z.2 ∧
    (∀ i j : Fin 4, z.1 i ≠ z.2 j) ∧
    (∃ i₁ i₂ j₁ j₂ : Fin 4, i₁ ≠ i₂ ∧ j₁ ≠ j₂ ∧ z.1 i₁ + z.1 i₂ = z.2 j₁ + z.2 j₂))
  let S2 := (T.product T).filter (fun z => w z.1 = w z.2 ∧
    (∀ i j : Fin 4, z.1 i ≠ z.2 j) ∧
    (∃ i₁ i₂ j₁ j₂ : Fin 4, i₁ ≠ i₂ ∧ j₁ ≠ j₂ ∧
      (z.1 i₁)^2 + (z.1 i₂)^2 = (z.2 j₁)^2 + (z.2 j₂)^2))
  let S3 := (T.product T).filter (fun z => w z.1 = w z.2 ∧
    (∀ i j : Fin 4, z.1 i ≠ z.2 j) ∧
    (∀ i₁ i₂ j₁ j₂ : Fin 4, i₁ ≠ i₂ → j₁ ≠ j₂ →
      z.1 i₁ + z.1 i₂ ≠ z.2 j₁ + z.2 j₂ ∧
      (z.1 i₁)^2 + (z.1 i₂)^2 ≠ (z.2 j₁)^2 + (z.2 j₂)^2))
  have hle_of_eq {s₁ s₂ : Finset ((Fin 4 → ℕ) × (Fin 4 → ℕ))} {R : ℝ}
      (hs : ∀ z, z ∈ s₁ ↔ z ∈ s₂) (hR : (s₂.card : ℝ) ≤ R) :
      (s₁.card : ℝ) ≤ R := by
    have heq : s₁ = s₂ := Finset.ext hs
    rw [heq]
    exact hR
  have hS1 : (S1.card : ℝ) ≤ Csum * (M : ℝ) ^ ε * (A.card : ℝ) ^ 4 := by
    refine hle_of_eq (fun z => ?_) h1
    dsimp only [S1, T, w]
    rw [Finset.mem_filter, Finset.mem_filter]
  have hS2 : (S2.card : ℝ) ≤ Csq * (M : ℝ) ^ ε * (A.card : ℝ) ^ 4 := by
    refine hle_of_eq (fun z => ?_) h2
    dsimp only [S2, T, w]
    rw [Finset.mem_filter, Finset.mem_filter]
  let k : ℕ := if P.natDegree = 3 then (5 : ℕ) else 4
  have hS3 : (S3.card : ℝ) ≤ Cres * (M : ℝ) ^ ε * (A.card : ℝ) ^ k := by
    refine hle_of_eq (fun z => ?_) h3
    dsimp only [S3, T, w]
    rw [Finset.mem_filter, Finset.mem_filter]
  have hcover_sum (G : Finset ((Fin 4 → ℕ) × (Fin 4 → ℕ)))
      (hG : ∀ z ∈ G, z ∈ T.product T ∧ w z.1 = w z.2 ∧ ∀ i j : Fin 4, z.1 i ≠ z.2 j) :
      (G.card : ℝ) ≤ (S1.card : ℝ) + (S2.card : ℝ) + (S3.card : ℝ) := by
    have hsub : G ⊆ S1 ∪ S2 ∪ S3 := by
      intro z hz
      obtain ⟨hprod, heq, hdisj⟩ := hG z hz
      by_cases hs : ∃ i₁ i₂ j₁ j₂ : Fin 4, i₁ ≠ i₂ ∧ j₁ ≠ j₂ ∧
          z.1 i₁ + z.1 i₂ = z.2 j₁ + z.2 j₂
      · exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_filter.mpr ⟨hprod, heq, hdisj, hs⟩))
      · by_cases hq : ∃ i₁ i₂ j₁ j₂ : Fin 4, i₁ ≠ i₂ ∧ j₁ ≠ j₂ ∧
            (z.1 i₁)^2 + (z.1 i₂)^2 = (z.2 j₁)^2 + (z.2 j₂)^2
        · exact Finset.mem_union_left _ (Finset.mem_union_right _
            (Finset.mem_filter.mpr ⟨hprod, heq, hdisj, hq⟩))
        · refine Finset.mem_union_right _
            (Finset.mem_filter.mpr ⟨hprod, heq, hdisj, fun i₁ i₂ j₁ j₂ hi hj => ⟨?_, ?_⟩⟩)
          · intro heq1
            exact hs ⟨i₁, i₂, j₁, j₂, hi, hj, heq1⟩
          · intro heq2
            exact hq ⟨i₁, i₂, j₁, j₂, hi, hj, heq2⟩
    have hnat : G.card ≤ S1.card + S2.card + S3.card :=
      (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
        (Nat.add_le_add_right (Finset.card_union_le _ _) _))
    have hcast : (G.card : ℝ) ≤ ((S1.card + S2.card + S3.card : ℕ) : ℝ) :=
      Nat.cast_le.mpr hnat
    push_cast at hcast
    exact hcast
  refine le_trans (hcover_sum _ ?_) ?_
  · intro z hz
    rw [Finset.mem_filter] at hz
    obtain ⟨hz12, hdisj⟩ := hz
    rw [Finset.mem_filter] at hz12
    obtain ⟨hprod, heq, _⟩ := hz12
    exact ⟨hprod, heq, hdisj⟩
  · have hpow4 : (A.card : ℝ) ^ 4 ≤ (A.card : ℝ) ^ k := by
      by_cases hz : A.card = 0
      · by_cases hdeg : P.natDegree = 3 <;> simp [k, hz, hdeg]
      · have hone : (1 : ℝ) ≤ A.card := by exact_mod_cast (show 1 ≤ A.card by omega)
        apply pow_le_pow_right₀ hone
        by_cases hdeg : P.natDegree = 3 <;> simp [k, hdeg]
    have hm_nonneg : 0 ≤ (M : ℝ) ^ ε := by positivity
    have h1k : Csum * (M : ℝ) ^ ε * (A.card : ℝ) ^ 4 ≤ Csum * (M : ℝ) ^ ε * (A.card : ℝ) ^ k := by
      rw [mul_assoc Csum, mul_assoc Csum]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow4 hm_nonneg) hCsum.le
    have h2k : Csq * (M : ℝ) ^ ε * (A.card : ℝ) ^ 4 ≤ Csq * (M : ℝ) ^ ε * (A.card : ℝ) ^ k := by
      rw [mul_assoc Csq, mul_assoc Csq]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow4 hm_nonneg) hCsq.le
    have hfactor : Csum * (M : ℝ) ^ ε * (A.card : ℝ) ^ k +
        Csq * (M : ℝ) ^ ε * (A.card : ℝ) ^ k +
        Cres * (M : ℝ) ^ ε * (A.card : ℝ) ^ k =
        (Csum + Csq + Cres) * (M : ℝ) ^ ε * (A.card : ℝ) ^ k := by ring
    change (S1.card : ℝ) + (S2.card : ℝ) + (S3.card : ℝ) ≤
      (Csum + Csq + Cres) * (M : ℝ) ^ ε * (A.card : ℝ) ^ k
    linarith only [hS1, hS2, hS3, h1k, h2k, hfactor]
