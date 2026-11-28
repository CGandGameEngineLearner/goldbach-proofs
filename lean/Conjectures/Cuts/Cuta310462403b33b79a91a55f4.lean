import Mathlib

-- child 1 zh: 存在固定正实数 d，使对任意下界 B，存在边长 n > B 与网格点集 T ⊆ [0, n)²，满足每行每列至多 2 个点，且点数减去严格斜向共线三元组（x₁ < x₂ < x₃ 且 y₁ ≠ y₂）的数量至少为 (3/2 + d)n。
-- child 1 en: There exists d > 0 such that for every B there are n > B and a grid set T ⊆ [0, n)² with at most two points per row and column whose size minus its strictly oblique collinear triples (x₁ < x₂ < x₃ and y₁ ≠ y₂) is at least (3/2 + d)n.
-- child 2 zh: 若有限网格点集 T 的每行与每列至多包含 2 个点，则 T 中任一严格字典序共线三元组必满足 x₁ < x₂ < x₃ 且 y₁ ≠ y₂，不存在竖直或水平共线三元组。
-- child 2 en: If a finite grid set T has at most two points in every row and column, then every strictly lexicographically ordered collinear triple in T satisfies x₁ < x₂ < x₃ and y₁ ≠ y₂.
theorem Conjectures.Cuts.Cuta310462403b33b79a91a55f4
    (hOblique : ∃ d : ℝ, (0 : ℝ) < d ∧ ∀ B : ℕ, ∃ n : ℕ, B < n ∧ ∃ T : Finset (ℕ × ℕ),
      (∀ p ∈ T, p.1 < n ∧ p.2 < n) ∧
      (∀ x : ℕ, {p ∈ T | p.1 = x}.card ≤ 2) ∧
      (∀ y : ℕ, {p ∈ T | p.2 = y}.card ≤ 2) ∧
      ((3 / 2 : ℝ) + d) * (n : ℝ) +
        ({t ∈ (T ×ˢ T) ×ˢ T |
          t.1.1.1 < t.1.2.1 ∧ t.1.2.1 < t.2.1 ∧ t.1.1.2 ≠ t.1.2.2 ∧
          ((t.1.2.1 : ℤ) - (t.1.1.1 : ℤ)) * ((t.2.2 : ℤ) - (t.1.1.2 : ℤ)) =
          ((t.1.2.2 : ℤ) - (t.1.1.2 : ℤ)) * ((t.2.1 : ℤ) - (t.1.1.1 : ℤ))}.card : ℝ)
        ≤ (T.card : ℝ))
    (hNoAxis : ∀ (T : Finset (ℕ × ℕ)),
      (∀ x : ℕ, {p ∈ T | p.1 = x}.card ≤ 2) →
      (∀ y : ℕ, {p ∈ T | p.2 = y}.card ≤ 2) →
      ∀ a ∈ T, ∀ b ∈ T, ∀ c ∈ T,
        (a.1 < b.1 ∨ a.1 = b.1 ∧ a.2 < b.2) →
        (b.1 < c.1 ∨ b.1 = c.1 ∧ b.2 < c.2) →
        ((b.1 : ℤ) - (a.1 : ℤ)) * ((c.2 : ℤ) - (a.2 : ℤ)) =
          ((b.2 : ℤ) - (a.2 : ℤ)) * ((c.1 : ℤ) - (a.1 : ℤ)) →
        a.1 < b.1 ∧ b.1 < c.1 ∧ a.2 ≠ b.2) : (∃ (x1 : ℝ), (0 : ℝ) < x1 ∧ ∀ (x2 : ℕ), ∃ (x3 : ℕ), x2 < x3 ∧ ∃ (x4 : Finset (ℕ × ℕ)), (∀ x5 ∈ x4, x5.1 < x3 ∧ x5.2 < x3) ∧ ((3 / 2 : ℝ) + x1) * (↑x3 : ℝ) + (↑{x5 ∈ (x4 ×ˢ x4) ×ˢ x4 | (x5.1.1.1 < x5.1.2.1 ∨ x5.1.1.1 = x5.1.2.1 ∧ x5.1.1.2 < x5.1.2.2) ∧ (x5.1.2.1 < x5.2.1 ∨ x5.1.2.1 = x5.2.1 ∧ x5.1.2.2 < x5.2.2) ∧ ((↑x5.1.2.1 : ℤ) - (↑x5.1.1.1 : ℤ)) * ((↑x5.2.2 : ℤ) - (↑x5.1.1.2 : ℤ)) = ((↑x5.1.2.2 : ℤ) - (↑x5.1.1.2 : ℤ)) * ((↑x5.2.1 : ℤ) - (↑x5.1.1.1 : ℤ))}.card : ℝ) ≤ (↑x4.card : ℝ)) := by
  obtain ⟨d, hd, hBuild⟩ := hOblique
  refine ⟨d, hd, ?_⟩
  intro B
  obtain ⟨n, hn, T, hBounds, hCol, hRow, hBound⟩ := hBuild B
  refine ⟨n, hn, T, hBounds, ?_⟩
  have hSub :
      {x5 ∈ (T ×ˢ T) ×ˢ T |
        (x5.1.1.1 < x5.1.2.1 ∨ x5.1.1.1 = x5.1.2.1 ∧ x5.1.1.2 < x5.1.2.2) ∧
        (x5.1.2.1 < x5.2.1 ∨ x5.1.2.1 = x5.2.1 ∧ x5.1.2.2 < x5.2.2) ∧
        ((↑x5.1.2.1 : ℤ) - (↑x5.1.1.1 : ℤ)) * ((↑x5.2.2 : ℤ) - (↑x5.1.1.2 : ℤ)) =
        ((↑x5.1.2.2 : ℤ) - (↑x5.1.1.2 : ℤ)) * ((↑x5.2.1 : ℤ) - (↑x5.1.1.1 : ℤ))} ⊆
      {t ∈ (T ×ˢ T) ×ˢ T |
        t.1.1.1 < t.1.2.1 ∧ t.1.2.1 < t.2.1 ∧ t.1.1.2 ≠ t.1.2.2 ∧
        ((t.1.2.1 : ℤ) - (t.1.1.1 : ℤ)) * ((t.2.2 : ℤ) - (t.1.1.2 : ℤ)) =
        ((t.1.2.2 : ℤ) - (t.1.1.2 : ℤ)) * ((t.2.1 : ℤ) - (t.1.1.1 : ℤ))} := by
    intro t ht
    rw [Finset.mem_filter] at ht ⊢
    rcases ht with ⟨htMem, h12, h23, hDet⟩
    rcases Finset.mem_product.mp htMem with ⟨hab, hc⟩
    rcases Finset.mem_product.mp hab with ⟨ha, hb⟩
    rcases hNoAxis T hCol hRow t.1.1 ha t.1.2 hb t.2 hc h12 h23 hDet with ⟨hx12, hx23, hy12⟩
    exact ⟨htMem, hx12, hx23, hy12, hDet⟩
  have hCard :
      ({x5 ∈ (T ×ˢ T) ×ˢ T |
        (x5.1.1.1 < x5.1.2.1 ∨ x5.1.1.1 = x5.1.2.1 ∧ x5.1.1.2 < x5.1.2.2) ∧
        (x5.1.2.1 < x5.2.1 ∨ x5.1.2.1 = x5.2.1 ∧ x5.1.2.2 < x5.2.2) ∧
        ((↑x5.1.2.1 : ℤ) - (↑x5.1.1.1 : ℤ)) * ((↑x5.2.2 : ℤ) - (↑x5.1.1.2 : ℤ)) =
        ((↑x5.1.2.2 : ℤ) - (↑x5.1.1.2 : ℤ)) * ((↑x5.2.1 : ℤ) - (↑x5.1.1.1 : ℤ))}.card : ℝ) ≤
      ({t ∈ (T ×ˢ T) ×ˢ T |
        t.1.1.1 < t.1.2.1 ∧ t.1.2.1 < t.2.1 ∧ t.1.1.2 ≠ t.1.2.2 ∧
        ((t.1.2.1 : ℤ) - (t.1.1.1 : ℤ)) * ((t.2.2 : ℤ) - (t.1.1.2 : ℤ)) =
        ((t.1.2.2 : ℤ) - (t.1.1.2 : ℤ)) * ((t.2.1 : ℤ) - (t.1.1.1 : ℤ))}.card : ℝ) := by
    exact_mod_cast Finset.card_le_card hSub
  linarith only [hBound, hCard]
