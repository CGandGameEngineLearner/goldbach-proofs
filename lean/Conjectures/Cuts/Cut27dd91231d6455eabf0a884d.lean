import Mathlib
open scoped BigOperators

/-! Cut of `L-goldbach-cut-623eb52cdf1bd37a88d7d4b7` by the size of the ambient interval: child 1 is the
bounded case `M ≤ 2` (elementary, only a cardinality bound is needed),
child 2 is the tail `2+1 ≤ M`. -/

theorem Conjectures.Cuts.Cut27dd91231d6455eabf0a884d
    (h₁ : ∀ (x1 : Polynomial ℤ),   (3 : ℕ) ≤ x1.natDegree →     ∀ (x3 : ℝ),       (0 : ℝ) < x3 →         ∃ (x5 : ℝ),           (0 : ℝ) < x5 ∧             ∀ (x6 : ℕ),               (2 : ℕ) ≤ x6 → x6 ≤ 2 →                 ∀ x8 ⊆ Finset.Icc (1 : ℕ) x6,                   have x10 : Finset (Fin (3 : ℕ) → ℕ) := Fintype.piFinset fun (x10 : Fin (3 : ℕ)) => x8;                   have x11 : (Fin (3 : ℕ) → ℕ) → ℤ := fun (x11 : Fin (3 : ℕ) → ℕ) => ∑ x12 : Fin (3 : ℕ), Polynomial.eval (↑(x11 x12)) x1;                   ↑{x12 ∈ x10.product x10 | x11 x12.1 = x11 x12.2 ∧ ∀ (x13 : Equiv.Perm (Fin (3 : ℕ))), x12.2 ≠ x12.1 ∘ ⇑x13}.card ≤ x5 * ↑x6 ^ x3 * ↑x8.card ^ if x1.natDegree = (3 : ℕ) then (4 : ℕ) else (3 : ℕ))
    (h₂ : ∀ (x1 : Polynomial ℤ),   (3 : ℕ) ≤ x1.natDegree →     ∀ (x3 : ℝ),       (0 : ℝ) < x3 →         ∃ (x5 : ℝ),           (0 : ℝ) < x5 ∧             ∀ (x6 : ℕ),               (2 : ℕ) ≤ x6 → 2+1 ≤ x6 →                 ∀ x8 ⊆ Finset.Icc (1 : ℕ) x6,                   have x10 : Finset (Fin (3 : ℕ) → ℕ) := Fintype.piFinset fun (x10 : Fin (3 : ℕ)) => x8;                   have x11 : (Fin (3 : ℕ) → ℕ) → ℤ := fun (x11 : Fin (3 : ℕ) → ℕ) => ∑ x12 : Fin (3 : ℕ), Polynomial.eval (↑(x11 x12)) x1;                   ↑{x12 ∈ x10.product x10 | x11 x12.1 = x11 x12.2 ∧ ∀ (x13 : Equiv.Perm (Fin (3 : ℕ))), x12.2 ≠ x12.1 ∘ ⇑x13}.card ≤ x5 * ↑x6 ^ x3 * ↑x8.card ^ if x1.natDegree = (3 : ℕ) then (4 : ℕ) else (3 : ℕ)) :
    ∀ (x1 : Polynomial ℤ),   (3 : ℕ) ≤ x1.natDegree →     ∀ (x3 : ℝ),       (0 : ℝ) < x3 →         ∃ (x5 : ℝ),           (0 : ℝ) < x5 ∧             ∀ (x6 : ℕ),               (2 : ℕ) ≤ x6 →                 ∀ x8 ⊆ Finset.Icc (1 : ℕ) x6,                   have x10 : Finset (Fin (3 : ℕ) → ℕ) := Fintype.piFinset fun (x10 : Fin (3 : ℕ)) => x8;                   have x11 : (Fin (3 : ℕ) → ℕ) → ℤ := fun (x11 : Fin (3 : ℕ) → ℕ) => ∑ x12 : Fin (3 : ℕ), Polynomial.eval (↑(x11 x12)) x1;                   ↑{x12 ∈ x10.product x10 | x11 x12.1 = x11 x12.2 ∧ ∀ (x13 : Equiv.Perm (Fin (3 : ℕ))), x12.2 ≠ x12.1 ∘ ⇑x13}.card ≤ x5 * ↑x6 ^ x3 * ↑x8.card ^ if x1.natDegree = (3 : ℕ) then (4 : ℕ) else (3 : ℕ) := by
  intro P hdeg ε hε
  obtain ⟨c₁, hc₁, hb₁⟩ := h₁ P hdeg ε hε
  obtain ⟨c₂, hc₂, hb₂⟩ := h₂ P hdeg ε hε
  refine ⟨max c₁ c₂, lt_max_of_lt_left hc₁, ?_⟩
  intro M hM A hA
  by_cases hs : M ≤ 2
  · have h := hb₁ M hM hs A hA
    refine le_trans h ?_
    gcongr
    exact le_max_left _ _
  · have h3 : 2+1 ≤ M := by omega
    have h := hb₂ M hM h3 A hA
    refine le_trans h ?_
    gcongr
    exact le_max_right _ _
