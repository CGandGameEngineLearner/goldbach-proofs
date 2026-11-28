import Mathlib

/-!
# 拆题：按支撑大小两分（次数 ≥ 4 的三元组等和碰撞）

父题：次数不等于 3 时，碰撞数 ≤ C·M^ε·|A|³。

两支：小支撑 |A| ≤ M^(ε/4)（除子差分给出的 K^4 直接够用），
大支撑 |A| > M^(ε/4)（需要均值定理/逐次差分的真正节省）。常数取 max。
-/

-- child 1 zh: 小支撑时碰撞数 ≤ C·M^ε·|A|³。
-- child 2 zh: 大支撑时同一界成立。

theorem Conjectures.Cuts.Cuta9a93950f244aadd9085317c
    (h₁ : ∀ (x1 : Polynomial ℤ),   (3 : ℕ) ≤ x1.natDegree →     x1.natDegree ≠ (3 : ℕ) →       ∀ (x4 : ℝ),         (0 : ℝ) < x4 →           ∃ (x6 : ℝ),             (0 : ℝ) < x6 ∧               ∀ (x7 : ℕ),                 (2 : ℕ) ≤ x7 →                   ∀ x9 ⊆ Finset.Icc (1 : ℕ) x7, (↑x9.card : ℝ) ≤ (↑x7 : ℝ) ^ (x4 / 4) →                     have x11 : Finset (Fin (3 : ℕ) → ℕ) := Fintype.piFinset fun (x11 : Fin (3 : ℕ)) => x9;                     have x12 : (Fin (3 : ℕ) → ℕ) → ℤ := fun (x12 : Fin (3 : ℕ) → ℕ) => ∑ x13 : Fin (3 : ℕ), Polynomial.eval (↑(x12 x13)) x1;                     ↑{x13 ∈ x11.product x11 | x12 x13.1 = x12 x13.2 ∧ ∀ (x14 : Equiv.Perm (Fin (3 : ℕ))), x13.2 ≠ x13.1 ∘ ⇑x14}.card ≤ x6 * ↑x7 ^ x4 * ↑x9.card ^ (3 : ℕ))
    (h₂ : ∀ (x1 : Polynomial ℤ),   (3 : ℕ) ≤ x1.natDegree →     x1.natDegree ≠ (3 : ℕ) →       ∀ (x4 : ℝ),         (0 : ℝ) < x4 →           ∃ (x6 : ℝ),             (0 : ℝ) < x6 ∧               ∀ (x7 : ℕ),                 (2 : ℕ) ≤ x7 →                   ∀ x9 ⊆ Finset.Icc (1 : ℕ) x7, (↑x7 : ℝ) ^ (x4 / 4) < (↑x9.card : ℝ) →                     have x11 : Finset (Fin (3 : ℕ) → ℕ) := Fintype.piFinset fun (x11 : Fin (3 : ℕ)) => x9;                     have x12 : (Fin (3 : ℕ) → ℕ) → ℤ := fun (x12 : Fin (3 : ℕ) → ℕ) => ∑ x13 : Fin (3 : ℕ), Polynomial.eval (↑(x12 x13)) x1;                     ↑{x13 ∈ x11.product x11 | x12 x13.1 = x12 x13.2 ∧ ∀ (x14 : Equiv.Perm (Fin (3 : ℕ))), x13.2 ≠ x13.1 ∘ ⇑x14}.card ≤ x6 * ↑x7 ^ x4 * ↑x9.card ^ (3 : ℕ))
    : ∀ (x1 : Polynomial ℤ),   (3 : ℕ) ≤ x1.natDegree →     x1.natDegree ≠ (3 : ℕ) →       ∀ (x4 : ℝ),         (0 : ℝ) < x4 →           ∃ (x6 : ℝ),             (0 : ℝ) < x6 ∧               ∀ (x7 : ℕ),                 (2 : ℕ) ≤ x7 →                   ∀ x9 ⊆ Finset.Icc (1 : ℕ) x7,                     have x11 : Finset (Fin (3 : ℕ) → ℕ) := Fintype.piFinset fun (x11 : Fin (3 : ℕ)) => x9;                     have x12 : (Fin (3 : ℕ) → ℕ) → ℤ := fun (x12 : Fin (3 : ℕ) → ℕ) => ∑ x13 : Fin (3 : ℕ), Polynomial.eval (↑(x12 x13)) x1;                     ↑{x13 ∈ x11.product x11 | x12 x13.1 = x12 x13.2 ∧ ∀ (x14 : Equiv.Perm (Fin (3 : ℕ))), x13.2 ≠ x13.1 ∘ ⇑x14}.card ≤ x6 * ↑x7 ^ x4 * ↑x9.card ^ (3 : ℕ) := by
  intro P h3 hne eps heps
  obtain ⟨C₁, hC₁, H₁⟩ := h₁ P h3 hne eps heps
  obtain ⟨C₂, hC₂, H₂⟩ := h₂ P h3 hne eps heps
  refine ⟨max C₁ C₂, lt_max_of_lt_left hC₁, ?_⟩
  intro M hM A hA
  by_cases h : (A.card : ℝ) ≤ (M : ℝ) ^ (eps / 4)
  · have hmain := H₁ M hM A hA h
    have hle : C₁ * (M : ℝ) ^ eps * (A.card : ℝ) ^ (3 : ℕ)
        ≤ max C₁ C₂ * (M : ℝ) ^ eps * (A.card : ℝ) ^ (3 : ℕ) := by
      gcongr
      exact le_max_left _ _
    exact le_trans hmain hle
  · have hlt : (M : ℝ) ^ (eps / 4) < (A.card : ℝ) := lt_of_not_ge h
    have hmain := H₂ M hM A hA hlt
    have hle : C₂ * (M : ℝ) ^ eps * (A.card : ℝ) ^ (3 : ℕ)
        ≤ max C₁ C₂ * (M : ℝ) ^ eps * (A.card : ℝ) ^ (3 : ℕ) := by
      gcongr
      exact le_max_right _ _
    exact le_trans hmain hle