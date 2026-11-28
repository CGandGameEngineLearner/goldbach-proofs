import Mathlib

/-!
# 拆题：L-goldbach-cut-623eb52cdf1bd37a88d7d4b7 按次数两分

父题：三次及以上多项式 E:\3-Coding\goldbach-work\lean\Conjectures\Cuts\Cutb341ad22506acd46cccc8b33.lean$，三元组等和碰撞（除去重排），三次时界为 $|A|^4$，高次时为 $|A|^3$。

拆法按次数分成两支——这不是形式上的分类：三次的情形要用 Weyl 差分与三次均值定理，
四次及以上的情形可以用差分逐次降维（
atDegree ≥ 4 时 E:\3-Coding\goldbach-work\lean\Conjectures\Cuts\Cutb341ad22506acd46cccc8b33.lean$ 的四阶差分仍是多项式且次数降一），
两支的分析工具完全不同，因此值得各自成题。两支互不依赖，合并即父题。

-/

-- child 1 zh: 三次多项式的三元组等和碰撞数不超过 C·M^ε·|A|^4。
-- child 2 zh: 四次及以上多项式的三元组等和碰撞数不超过 C·M^ε·|A|^3。

theorem Conjectures.Cuts.Cutb341ad22506acd46cccc8b33
    (h₁ : (∀ (x1 : Polynomial ℤ),   (3 : ℕ) ≤ x1.natDegree → x1.natDegree = (3 : ℕ) →     ∀ (x3 : ℝ),       (0 : ℝ) < x3 →         ∃ (x5 : ℝ),           (0 : ℝ) < x5 ∧             ∀ (x6 : ℕ),               (2 : ℕ) ≤ x6 →                 ∀ x8 ⊆ Finset.Icc (1 : ℕ) x6,                   have x10 : Finset (Fin (3 : ℕ) → ℕ) := Fintype.piFinset fun (x10 : Fin (3 : ℕ)) => x8;                   have x11 : (Fin (3 : ℕ) → ℕ) → ℤ := fun (x11 : Fin (3 : ℕ) → ℕ) => ∑ x12 : Fin (3 : ℕ), Polynomial.eval (↑(x11 x12)) x1;                   ↑{x12 ∈ x10.product x10 | x11 x12.1 = x11 x12.2 ∧ ∀ (x13 : Equiv.Perm (Fin (3 : ℕ))), x12.2 ≠ x12.1 ∘ ⇑x13}.card ≤ x5 * ↑x6 ^ x3 * ↑x8.card ^ (4 : ℕ)))
    (h₂ : (∀ (x1 : Polynomial ℤ),   (3 : ℕ) ≤ x1.natDegree → x1.natDegree ≠ (3 : ℕ) →     ∀ (x3 : ℝ),       (0 : ℝ) < x3 →         ∃ (x5 : ℝ),           (0 : ℝ) < x5 ∧             ∀ (x6 : ℕ),               (2 : ℕ) ≤ x6 →                 ∀ x8 ⊆ Finset.Icc (1 : ℕ) x6,                   have x10 : Finset (Fin (3 : ℕ) → ℕ) := Fintype.piFinset fun (x10 : Fin (3 : ℕ)) => x8;                   have x11 : (Fin (3 : ℕ) → ℕ) → ℤ := fun (x11 : Fin (3 : ℕ) → ℕ) => ∑ x12 : Fin (3 : ℕ), Polynomial.eval (↑(x11 x12)) x1;                   ↑{x12 ∈ x10.product x10 | x11 x12.1 = x11 x12.2 ∧ ∀ (x13 : Equiv.Perm (Fin (3 : ℕ))), x12.2 ≠ x12.1 ∘ ⇑x13}.card ≤ x5 * ↑x6 ^ x3 * ↑x8.card ^ (3 : ℕ)))
    : (∀ (x1 : Polynomial ℤ),   (3 : ℕ) ≤ x1.natDegree →     ∀ (x3 : ℝ),       (0 : ℝ) < x3 →         ∃ (x5 : ℝ),           (0 : ℝ) < x5 ∧             ∀ (x6 : ℕ),               (2 : ℕ) ≤ x6 →                 ∀ x8 ⊆ Finset.Icc (1 : ℕ) x6,                   have x10 : Finset (Fin (3 : ℕ) → ℕ) := Fintype.piFinset fun (x10 : Fin (3 : ℕ)) => x8;                   have x11 : (Fin (3 : ℕ) → ℕ) → ℤ := fun (x11 : Fin (3 : ℕ) → ℕ) => ∑ x12 : Fin (3 : ℕ), Polynomial.eval (↑(x11 x12)) x1;                   ↑{x12 ∈ x10.product x10 | x11 x12.1 = x11 x12.2 ∧ ∀ (x13 : Equiv.Perm (Fin (3 : ℕ))), x12.2 ≠ x12.1 ∘ ⇑x13}.card ≤ x5 * ↑x6 ^ x3 * ↑x8.card ^ if x1.natDegree = (3 : ℕ) then (4 : ℕ) else (3 : ℕ)) := by
  intro P hdeg eps heps
  by_cases h3 : P.natDegree = 3
  · simpa only [h3, if_true] using h₁ P hdeg h3 eps heps
  · simpa only [h3, if_false] using h₂ P hdeg h3 eps heps