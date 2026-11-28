import Mathlib

-- child 1 zh: 控制既无共享指标、无匹配两项普通和及平方和，且左右去重坐标总数不超过 6（三次）或 5（高次）的四元组多项式等和碰撞数。
-- child 1 en: Bound disjoint-index residual quadruple polynomial collisions whose combined distinct coordinate support has cardinality at most 6 in degree 3 or 5 in degree at least 4.
-- child 2 zh: 对三次多项式，控制既无共享指标、无匹配两项普通和及平方和，且左右去重坐标总数至少为 7 的四元组等和碰撞数。
-- child 2 en: For cubic polynomials, bound disjoint-index residual quadruple collisions whose combined distinct coordinate support has cardinality at least 7.
-- child 3 zh: 对四次及以上多项式，控制既无共享指标、无匹配两项普通和及平方和，且左右去重坐标总数至少为 6 的四元组等和碰撞数。
-- child 3 en: For polynomials of degree at least 4, bound disjoint-index residual quadruple collisions whose combined distinct coordinate support has cardinality at least 6.

theorem Conjectures.Cuts.Cut52c3d38b630a2bc1734688f4
  (hDegen : ∀ P : Polynomial ℤ, 3 ≤ P.natDegree → ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ, 2 ≤ M → ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 M →
      let T := Fintype.piFinset (fun _ : Fin 4 => A)
      let w := fun u : Fin 4 → ℕ => ∑ j : Fin 4, P.eval (u j : ℤ)
      let D := (T.product T).filter (fun z => w z.1 = w z.2 ∧ ∀ q : Fin 4 × Fin 4, z.1 q.1 ≠ z.2 q.2)
      let R := D.filter (fun z => ∀ p₁ p₂ : Fin 4 × Fin 4, p₁.1 ≠ p₁.2 → p₂.1 ≠ p₂.2 →
        z.1 p₁.1 + z.1 p₁.2 ≠ z.2 p₂.1 + z.2 p₂.2 ∧
        (z.1 p₁.1)^2 + (z.1 p₁.2)^2 ≠ (z.2 p₂.1)^2 + (z.2 p₂.2)^2)
      let vals := fun z : (Fin 4 → ℕ) × (Fin 4 → ℕ) =>
        Finset.image z.1 Finset.univ ∪ Finset.image z.2 Finset.univ
      ((R.filter (fun z => (vals z).card ≤ if P.natDegree = 3 then 6 else 5)).card : ℝ) ≤
        C * (M : ℝ) ^ ε * (A.card : ℝ) ^ (if P.natDegree = 3 then (5 : ℕ) else 4))
  (hCubic : ∀ P : Polynomial ℤ, P.natDegree = 3 → ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ, 2 ≤ M → ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 M →
      let T := Fintype.piFinset (fun _ : Fin 4 => A)
      let w := fun u : Fin 4 → ℕ => ∑ j : Fin 4, P.eval (u j : ℤ)
      let D := (T.product T).filter (fun z => w z.1 = w z.2 ∧ ∀ q : Fin 4 × Fin 4, z.1 q.1 ≠ z.2 q.2)
      let R := D.filter (fun z => ∀ p₁ p₂ : Fin 4 × Fin 4, p₁.1 ≠ p₁.2 → p₂.1 ≠ p₂.2 →
        z.1 p₁.1 + z.1 p₁.2 ≠ z.2 p₂.1 + z.2 p₂.2 ∧
        (z.1 p₁.1)^2 + (z.1 p₁.2)^2 ≠ (z.2 p₂.1)^2 + (z.2 p₂.2)^2)
      let vals := fun z : (Fin 4 → ℕ) × (Fin 4 → ℕ) =>
        Finset.image z.1 Finset.univ ∪ Finset.image z.2 Finset.univ
      ((R.filter (fun z => 7 ≤ (vals z).card)).card : ℝ) ≤
        C * (M : ℝ) ^ ε * (A.card : ℝ) ^ 5)
  (hHigh : ∀ P : Polynomial ℤ, 4 ≤ P.natDegree → ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ, 2 ≤ M → ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 M →
      let T := Fintype.piFinset (fun _ : Fin 4 => A)
      let w := fun u : Fin 4 → ℕ => ∑ j : Fin 4, P.eval (u j : ℤ)
      let D := (T.product T).filter (fun z => w z.1 = w z.2 ∧ ∀ q : Fin 4 × Fin 4, z.1 q.1 ≠ z.2 q.2)
      let R := D.filter (fun z => ∀ p₁ p₂ : Fin 4 × Fin 4, p₁.1 ≠ p₁.2 → p₂.1 ≠ p₂.2 →
        z.1 p₁.1 + z.1 p₁.2 ≠ z.2 p₂.1 + z.2 p₂.2 ∧
        (z.1 p₁.1)^2 + (z.1 p₁.2)^2 ≠ (z.2 p₂.1)^2 + (z.2 p₂.2)^2)
      let vals := fun z : (Fin 4 → ℕ) × (Fin 4 → ℕ) =>
        Finset.image z.1 Finset.univ ∪ Finset.image z.2 Finset.univ
      ((R.filter (fun z => 6 ≤ (vals z).card)).card : ℝ) ≤
        C * (M : ℝ) ^ ε * (A.card : ℝ) ^ 4) : (∀ (x1 : Polynomial ℤ),   (3 : ℕ) ≤ x1.natDegree →     ∀ (x3 : ℝ),       (0 : ℝ) < x3 →         ∃ (x5 : ℝ),           (0 : ℝ) < x5 ∧             ∀ (x6 : ℕ),               (2 : ℕ) ≤ x6 →                 ∀ x8 ⊆ Finset.Icc (1 : ℕ) x6,                   have x10 : Finset (Fin (4 : ℕ) → ℕ) := Fintype.piFinset fun (x10 : Fin (4 : ℕ)) => x8;                   let x11 : (Fin (4 : ℕ) → ℕ) → ℤ := fun (x11 : Fin (4 : ℕ) → ℕ) => ∑ x12 : Fin (4 : ℕ), Polynomial.eval (↑(x11 x12) : ℤ) x1;                   have x12 : Finset ((Fin (4 : ℕ) → ℕ) × (Fin (4 : ℕ) → ℕ)) := {x12 ∈ x10.product x10 | x11 x12.1 = x11 x12.2 ∧ ∀ (x13 : Fin (4 : ℕ) × Fin (4 : ℕ)), x12.1 x13.1 ≠ x12.2 x13.2};                   (↑{x13 ∈ x12 | ∀ (x14 x15 : Fin (4 : ℕ) × Fin (4 : ℕ)), x14.1 ≠ x14.2 → x15.1 ≠ x15.2 → x13.1 x14.1 + x13.1 x14.2 ≠ x13.2 x15.1 + x13.2 x15.2 ∧ x13.1 x14.1 ^ (2 : ℕ) + x13.1 x14.2 ^ (2 : ℕ) ≠ x13.2 x15.1 ^ (2 : ℕ) + x13.2 x15.2 ^ (2 : ℕ)}.card : ℝ) ≤ x5 * (↑x6 : ℝ) ^ x3 * (↑x8.card : ℝ) ^ if x1.natDegree = (3 : ℕ) then (5 : ℕ) else (4 : ℕ)) := by
  intro P hdeg ε hε
  have hle_of_eq {s₁ s₂ : Finset ((Fin 4 → ℕ) × (Fin 4 → ℕ))} {R : ℝ}
      (hs : ∀ z, z ∈ s₁ ↔ z ∈ s₂) (hR : (s₂.card : ℝ) ≤ R) :
      (s₁.card : ℝ) ≤ R := by
    have heq : s₁ = s₂ := Finset.ext hs
    rw [heq]
    exact hR
  by_cases hdeg3 : P.natDegree = 3
  · obtain ⟨C1, hC1, b1⟩ := hDegen P hdeg ε hε
    obtain ⟨C2, hC2, b2⟩ := hCubic P hdeg3 ε hε
    refine ⟨C1 + C2, by positivity, ?_⟩
    intro M hM A hA
    dsimp only
    simp only [hdeg3, if_true]
    have h1 := b1 M hM A hA
    have h2 := b2 M hM A hA
    dsimp only at h1 h2
    simp only [hdeg3, if_true] at h1
    let T : Finset (Fin 4 → ℕ) := Fintype.piFinset (fun _ : Fin 4 => A)
    let w : (Fin 4 → ℕ) → ℤ := fun u => ∑ j : Fin 4, P.eval (u j : ℤ)
    let D := (T.product T).filter (fun z => w z.1 = w z.2 ∧ ∀ q : Fin 4 × Fin 4, z.1 q.1 ≠ z.2 q.2)
    let R := D.filter (fun z => ∀ p₁ p₂ : Fin 4 × Fin 4, p₁.1 ≠ p₁.2 → p₂.1 ≠ p₂.2 →
      z.1 p₁.1 + z.1 p₁.2 ≠ z.2 p₂.1 + z.2 p₂.2 ∧
      (z.1 p₁.1)^2 + (z.1 p₁.2)^2 ≠ (z.2 p₂.1)^2 + (z.2 p₂.2)^2)
    let vals : (Fin 4 → ℕ) × (Fin 4 → ℕ) → Finset ℕ := fun z =>
      Finset.image z.1 Finset.univ ∪ Finset.image z.2 Finset.univ
    let S1 := R.filter (fun z => (vals z).card ≤ 6)
    let S2 := R.filter (fun z => 7 ≤ (vals z).card)
    have hS1 : (S1.card : ℝ) ≤ C1 * (M : ℝ) ^ ε * (A.card : ℝ) ^ 5 := by
      refine hle_of_eq (fun z => ?_) h1
      simp only [S1, R, D, T, w, vals, Finset.mem_filter, hdeg3, if_true]
    have hS2 : (S2.card : ℝ) ≤ C2 * (M : ℝ) ^ ε * (A.card : ℝ) ^ 5 := by
      refine hle_of_eq (fun z => ?_) h2
      simp only [S2, R, D, T, w, vals, Finset.mem_filter]
    have hcover (G : Finset ((Fin 4 → ℕ) × (Fin 4 → ℕ))) (hG : ∀ z ∈ G, z ∈ R) :
        (G.card : ℝ) ≤ (S1.card : ℝ) + (S2.card : ℝ) := by
      have hsub : G ⊆ S1 ∪ S2 := by
        intro z hz
        have hzR := hG z hz
        by_cases hle : (vals z).card ≤ 6
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hzR, hle⟩)
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hzR, by omega⟩)
      have hnat : G.card ≤ S1.card + S2.card :=
        (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
      have hcast : (G.card : ℝ) ≤ ((S1.card + S2.card : ℕ) : ℝ) := Nat.cast_le.mpr hnat
      push_cast at hcast
      exact hcast
    refine le_trans (hcover _ ?_) ?_
    · intro z hz
      rw [Finset.mem_filter] at hz
      obtain ⟨hz12, hres⟩ := hz
      rw [Finset.mem_filter] at hz12
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr hz12, hres⟩
    · linarith only [hS1, hS2, show C1 * (M : ℝ) ^ ε * (A.card : ℝ) ^ 5 +
        C2 * (M : ℝ) ^ ε * (A.card : ℝ) ^ 5 = (C1 + C2) * (M : ℝ) ^ ε * (A.card : ℝ) ^ 5 by ring]
  · have hdeg4 : 4 ≤ P.natDegree := by omega
    obtain ⟨C1, hC1, b1⟩ := hDegen P hdeg ε hε
    obtain ⟨C3, hC3, b3⟩ := hHigh P hdeg4 ε hε
    refine ⟨C1 + C3, by positivity, ?_⟩
    intro M hM A hA
    dsimp only
    simp only [hdeg3, if_false]
    have h1 := b1 M hM A hA
    have h3 := b3 M hM A hA
    dsimp only at h1 h3
    simp only [hdeg3, if_false] at h1
    let T : Finset (Fin 4 → ℕ) := Fintype.piFinset (fun _ : Fin 4 => A)
    let w : (Fin 4 → ℕ) → ℤ := fun u => ∑ j : Fin 4, P.eval (u j : ℤ)
    let D := (T.product T).filter (fun z => w z.1 = w z.2 ∧ ∀ q : Fin 4 × Fin 4, z.1 q.1 ≠ z.2 q.2)
    let R := D.filter (fun z => ∀ p₁ p₂ : Fin 4 × Fin 4, p₁.1 ≠ p₁.2 → p₂.1 ≠ p₂.2 →
      z.1 p₁.1 + z.1 p₁.2 ≠ z.2 p₂.1 + z.2 p₂.2 ∧
      (z.1 p₁.1)^2 + (z.1 p₁.2)^2 ≠ (z.2 p₂.1)^2 + (z.2 p₂.2)^2)
    let vals : (Fin 4 → ℕ) × (Fin 4 → ℕ) → Finset ℕ := fun z =>
      Finset.image z.1 Finset.univ ∪ Finset.image z.2 Finset.univ
    let S1 := R.filter (fun z => (vals z).card ≤ 5)
    let S3 := R.filter (fun z => 6 ≤ (vals z).card)
    have hS1 : (S1.card : ℝ) ≤ C1 * (M : ℝ) ^ ε * (A.card : ℝ) ^ 4 := by
      refine hle_of_eq (fun z => ?_) h1
      simp only [S1, R, D, T, w, vals, Finset.mem_filter, hdeg3, if_false]
    have hS3 : (S3.card : ℝ) ≤ C3 * (M : ℝ) ^ ε * (A.card : ℝ) ^ 4 := by
      refine hle_of_eq (fun z => ?_) h3
      simp only [S3, R, D, T, w, vals, Finset.mem_filter]
    have hcover (G : Finset ((Fin 4 → ℕ) × (Fin 4 → ℕ))) (hG : ∀ z ∈ G, z ∈ R) :
        (G.card : ℝ) ≤ (S1.card : ℝ) + (S3.card : ℝ) := by
      have hsub : G ⊆ S1 ∪ S3 := by
        intro z hz
        have hzR := hG z hz
        by_cases hle : (vals z).card ≤ 5
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hzR, hle⟩)
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hzR, by omega⟩)
      have hnat : G.card ≤ S1.card + S3.card :=
        (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
      have hcast : (G.card : ℝ) ≤ ((S1.card + S3.card : ℕ) : ℝ) := Nat.cast_le.mpr hnat
      push_cast at hcast
      exact hcast
    refine le_trans (hcover _ ?_) ?_
    · intro z hz
      rw [Finset.mem_filter] at hz
      obtain ⟨hz12, hres⟩ := hz
      rw [Finset.mem_filter] at hz12
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr hz12, hres⟩
    · linarith only [hS1, hS3, show C1 * (M : ℝ) ^ ε * (A.card : ℝ) ^ 4 +
        C3 * (M : ℝ) ^ ε * (A.card : ℝ) ^ 4 = (C1 + C3) * (M : ℝ) ^ ε * (A.card : ℝ) ^ 4 by ring]
