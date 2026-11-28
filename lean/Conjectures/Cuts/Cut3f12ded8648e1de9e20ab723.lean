import Mathlib

-- child 1 zh: 对四次及以上多项式，控制存在一对两项多项式等和局部匹配的去重坐标至少 6 的残差四元组等和碰撞数。
-- child 1 en: For polynomials of degree at least 4, bound residual collisions with support at least 6 having a 2-to-2 local polynomial sum match.
-- child 2 zh: 对四次及以上多项式，控制不存在任何两项多项式等和局部匹配的去重坐标至少 6 的不可约残差四元组等和碰撞数。
-- child 2 en: For polynomials of degree at least 4, bound irreducible residual collisions with support at least 6 and no 2-to-2 local polynomial sum match.

theorem Conjectures.Cuts.Cut3f12ded8648e1de9e20ab723
  (hLocalPoly2 : ∀ P : Polynomial ℤ, 4 ≤ P.natDegree → ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ, 2 ≤ M → ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 M →
      let T := Fintype.piFinset (fun _ : Fin 4 => A)
      let w := fun u : Fin 4 → ℕ => ∑ j : Fin 4, P.eval (u j : ℤ)
      let S := (T.product T).filter (fun z => w z.1 = w z.2 ∧
        (∀ q : Fin 4 × Fin 4, z.1 q.1 ≠ z.2 q.2) ∧
        6 ≤ (Finset.image z.1 Finset.univ ∪ Finset.image z.2 Finset.univ).card)
      let R := S.filter (fun z => ∀ p₁ p₂ : Fin 4 × Fin 4, p₁.1 ≠ p₁.2 → p₂.1 ≠ p₂.2 →
        z.1 p₁.1 + z.1 p₁.2 ≠ z.2 p₂.1 + z.2 p₂.2 ∧
        (z.1 p₁.1)^2 + (z.1 p₁.2)^2 ≠ (z.2 p₂.1)^2 + (z.2 p₂.2)^2)
      ((R.filter (fun z => ∃ p₁ p₂ : Fin 4 × Fin 4, p₁.1 ≠ p₁.2 ∧ p₂.1 ≠ p₂.2 ∧
        P.eval (z.1 p₁.1 : ℤ) + P.eval (z.1 p₁.2 : ℤ) =
          P.eval (z.2 p₂.1 : ℤ) + P.eval (z.2 p₂.2 : ℤ))).card : ℝ) ≤
        C * (M : ℝ) ^ ε * (A.card : ℝ) ^ 4)
  (hIrred : ∀ P : Polynomial ℤ, 4 ≤ P.natDegree → ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ, 2 ≤ M → ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 M →
      let T := Fintype.piFinset (fun _ : Fin 4 => A)
      let w := fun u : Fin 4 → ℕ => ∑ j : Fin 4, P.eval (u j : ℤ)
      let S := (T.product T).filter (fun z => w z.1 = w z.2 ∧
        (∀ q : Fin 4 × Fin 4, z.1 q.1 ≠ z.2 q.2) ∧
        6 ≤ (Finset.image z.1 Finset.univ ∪ Finset.image z.2 Finset.univ).card)
      let R := S.filter (fun z => ∀ p₁ p₂ : Fin 4 × Fin 4, p₁.1 ≠ p₁.2 → p₂.1 ≠ p₂.2 →
        z.1 p₁.1 + z.1 p₁.2 ≠ z.2 p₂.1 + z.2 p₂.2 ∧
        (z.1 p₁.1)^2 + (z.1 p₁.2)^2 ≠ (z.2 p₂.1)^2 + (z.2 p₂.2)^2)
      ((R.filter (fun z => ∀ p₁ p₂ : Fin 4 × Fin 4, p₁.1 ≠ p₁.2 → p₂.1 ≠ p₂.2 →
        P.eval (z.1 p₁.1 : ℤ) + P.eval (z.1 p₁.2 : ℤ) ≠
          P.eval (z.2 p₂.1 : ℤ) + P.eval (z.2 p₂.2 : ℤ))).card : ℝ) ≤
        C * (M : ℝ) ^ ε * (A.card : ℝ) ^ 4) : (∀ (x1 : Polynomial ℤ),   (4 : ℕ) ≤ x1.natDegree →     ∀ (x3 : ℝ),       (0 : ℝ) < x3 →         ∃ (x5 : ℝ),           (0 : ℝ) < x5 ∧             ∀ (x6 : ℕ),               (2 : ℕ) ≤ x6 →                 ∀ x8 ⊆ Finset.Icc (1 : ℕ) x6,                   have x10 : Finset (Fin (4 : ℕ) → ℕ) := Fintype.piFinset fun (x10 : Fin (4 : ℕ)) => x8;                   let x11 : (Fin (4 : ℕ) → ℕ) → ℤ := fun (x11 : Fin (4 : ℕ) → ℕ) => ∑ x12 : Fin (4 : ℕ), Polynomial.eval (↑(x11 x12) : ℤ) x1;                   have x12 : Finset ((Fin (4 : ℕ) → ℕ) × (Fin (4 : ℕ) → ℕ)) := {x12 ∈ x10.product x10 | x11 x12.1 = x11 x12.2 ∧ ∀ (x13 : Fin (4 : ℕ) × Fin (4 : ℕ)), x12.1 x13.1 ≠ x12.2 x13.2};                   have x13 : Finset ((Fin (4 : ℕ) → ℕ) × (Fin (4 : ℕ) → ℕ)) := {x13 ∈ x12 | ∀ (x14 x15 : Fin (4 : ℕ) × Fin (4 : ℕ)), x14.1 ≠ x14.2 → x15.1 ≠ x15.2 → x13.1 x14.1 + x13.1 x14.2 ≠ x13.2 x15.1 + x13.2 x15.2 ∧ x13.1 x14.1 ^ (2 : ℕ) + x13.1 x14.2 ^ (2 : ℕ) ≠ x13.2 x15.1 ^ (2 : ℕ) + x13.2 x15.2 ^ (2 : ℕ)};                   have x14 : (Fin (4 : ℕ) → ℕ) × (Fin (4 : ℕ) → ℕ) → Finset ℕ := fun (x14 : (Fin (4 : ℕ) → ℕ) × (Fin (4 : ℕ) → ℕ)) => Finset.image x14.1 Finset.univ ∪ Finset.image x14.2 Finset.univ;                   (↑{x15 ∈ x13 | (6 : ℕ) ≤ (x14 x15).card}.card : ℝ) ≤ x5 * (↑x6 : ℝ) ^ x3 * (↑x8.card : ℝ) ^ (4 : ℕ)) := by
  intro P hdeg ε hε
  obtain ⟨C1, hC1, b1⟩ := hLocalPoly2 P hdeg ε hε
  obtain ⟨C2, hC2, b2⟩ := hIrred P hdeg ε hε
  refine ⟨C1 + C2, by positivity, ?_⟩
  intro M hM A hA
  dsimp only
  have h1 := b1 M hM A hA
  have h2 := b2 M hM A hA
  dsimp only at h1 h2
  let T : Finset (Fin 4 → ℕ) := Fintype.piFinset (fun _ : Fin 4 => A)
  let w : (Fin 4 → ℕ) → ℤ := fun u => ∑ j : Fin 4, P.eval (u j : ℤ)
  let S := (T.product T).filter (fun z => w z.1 = w z.2 ∧
    (∀ q : Fin 4 × Fin 4, z.1 q.1 ≠ z.2 q.2) ∧
    6 ≤ (Finset.image z.1 Finset.univ ∪ Finset.image z.2 Finset.univ).card)
  let R := S.filter (fun z => ∀ p₁ p₂ : Fin 4 × Fin 4, p₁.1 ≠ p₁.2 → p₂.1 ≠ p₂.2 →
    z.1 p₁.1 + z.1 p₁.2 ≠ z.2 p₂.1 + z.2 p₂.2 ∧
    (z.1 p₁.1)^2 + (z.1 p₁.2)^2 ≠ (z.2 p₂.1)^2 + (z.2 p₂.2)^2)
  let S1 := R.filter (fun z => ∃ p₁ p₂ : Fin 4 × Fin 4, p₁.1 ≠ p₁.2 ∧ p₂.1 ≠ p₂.2 ∧
    P.eval (z.1 p₁.1 : ℤ) + P.eval (z.1 p₁.2 : ℤ) =
      P.eval (z.2 p₂.1 : ℤ) + P.eval (z.2 p₂.2 : ℤ))
  let S2 := R.filter (fun z => ∀ p₁ p₂ : Fin 4 × Fin 4, p₁.1 ≠ p₁.2 → p₂.1 ≠ p₂.2 →
    P.eval (z.1 p₁.1 : ℤ) + P.eval (z.1 p₁.2 : ℤ) ≠
      P.eval (z.2 p₂.1 : ℤ) + P.eval (z.2 p₂.2 : ℤ))
  have hle_of_eq {s₁ s₂ : Finset ((Fin 4 → ℕ) × (Fin 4 → ℕ))} {B : ℝ}
      (hs : ∀ z, z ∈ s₁ ↔ z ∈ s₂) (hB : (s₂.card : ℝ) ≤ B) :
      (s₁.card : ℝ) ≤ B := by
    have heq : s₁ = s₂ := Finset.ext hs
    rw [heq]
    exact hB
  have hS1 : (S1.card : ℝ) ≤ C1 * (M : ℝ) ^ ε * (A.card : ℝ) ^ 4 := by
    refine hle_of_eq (fun z => ?_) h1
    simp only [S1, R, S, T, w, Finset.mem_filter]
    tauto
  have hS2 : (S2.card : ℝ) ≤ C2 * (M : ℝ) ^ ε * (A.card : ℝ) ^ 4 := by
    refine hle_of_eq (fun z => ?_) h2
    simp only [S2, R, S, T, w, Finset.mem_filter]
    tauto
  have hcover (G : Finset ((Fin 4 → ℕ) × (Fin 4 → ℕ))) (hG : ∀ z ∈ G, z ∈ R) :
      (G.card : ℝ) ≤ (S1.card : ℝ) + (S2.card : ℝ) := by
    have hsub : G ⊆ S1 ∪ S2 := by
      intro z hz
      have hzR := hG z hz
      by_cases hp : ∃ p₁ p₂ : Fin 4 × Fin 4, p₁.1 ≠ p₁.2 ∧ p₂.1 ≠ p₂.2 ∧
          P.eval (z.1 p₁.1 : ℤ) + P.eval (z.1 p₁.2 : ℤ) =
            P.eval (z.2 p₂.1 : ℤ) + P.eval (z.2 p₂.2 : ℤ)
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hzR, hp⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr
          ⟨hzR, fun p₁ p₂ h12 h34 he => hp ⟨p₁, p₂, h12, h34, he⟩⟩)
    have hnat : G.card ≤ S1.card + S2.card :=
      (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have hcast : (G.card : ℝ) ≤ ((S1.card + S2.card : ℕ) : ℝ) := Nat.cast_le.mpr hnat
    push_cast at hcast
    exact hcast
  refine le_trans (hcover _ ?_) ?_
  · intro z hz
    rw [Finset.mem_filter] at hz
    obtain ⟨hz13, hcard⟩ := hz
    rw [Finset.mem_filter] at hz13
    obtain ⟨hz12, hres⟩ := hz13
    rw [Finset.mem_filter] at hz12
    obtain ⟨hzT, hweq, hdisj⟩ := hz12
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hzT, hweq, hdisj, hcard⟩, hres⟩
  · linarith only [hS1, hS2, show C1 * (M : ℝ) ^ ε * (A.card : ℝ) ^ 4 +
      C2 * (M : ℝ) ^ ε * (A.card : ℝ) ^ 4 = (C1 + C2) * (M : ℝ) ^ ε * (A.card : ℝ) ^ 4 by ring]
