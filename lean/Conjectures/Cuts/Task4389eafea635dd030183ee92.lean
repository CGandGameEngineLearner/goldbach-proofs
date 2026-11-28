import Mathlib

theorem Conjectures.Cuts.Task4389eafea635dd030183ee92 : (∀ (x1 : Polynomial ℤ),   (3 : ℕ) ≤ x1.natDegree →     x1.natDegree ≠ (3 : ℕ) →       ∀ (x4 : ℝ),         (0 : ℝ) < x4 →           ∃ (x6 : ℝ),             (0 : ℝ) < x6 ∧               ∀ (x7 : ℕ),                 (2 : ℕ) ≤ x7 →                   ∀ x9 ⊆ Finset.Icc (1 : ℕ) x7,                     (↑x9.card : ℝ) ≤ (↑x7 : ℝ) ^ (x4 / (4 : ℝ)) →                       have x12 : Finset (Fin (3 : ℕ) → ℕ) := Fintype.piFinset fun (x12 : Fin (3 : ℕ)) => x9;                       have x13 : (Fin (3 : ℕ) → ℕ) → ℤ := fun (x13 : Fin (3 : ℕ) → ℕ) => ∑ x14 : Fin (3 : ℕ), Polynomial.eval (↑(x13 x14) : ℤ) x1;                       (↑{x14 ∈ x12.product x12 | x13 x14.1 = x13 x14.2 ∧ ∀ (x15 : Equiv.Perm (Fin (3 : ℕ))), x14.2 ≠ x14.1 ∘ (⇑x15 : Fin (3 : ℕ) → Fin (3 : ℕ))}.card : ℝ) ≤ x6 * (↑x7 : ℝ) ^ x4 * (↑x9.card : ℝ) ^ (3 : ℕ)) := by
  classical
  intro P _ _ ε hε
  refine ⟨1, by norm_num, ?_⟩
  intro M hM A _ hA T w
  have hMone : (1 : ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by omega)
  have habsorb : (A.card : ℝ)^3 ≤ (M : ℝ)^ε := by
    calc
      _ ≤ ((M : ℝ)^(ε/4))^3 := pow_le_pow_left₀ (Nat.cast_nonneg _) hA 3
      _ = (M : ℝ)^((ε/4)*(3:ℝ)) := by
        rw [← Real.rpow_mul_natCast (Nat.cast_nonneg M)]
        norm_num
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hMone (by linarith)
  calc
    _ ≤ ((T.product T).card : ℝ) := by exact_mod_cast Finset.card_filter_le _ _
    _ = (A.card : ℝ)^3 * (A.card : ℝ)^3 := by simp [T]
    _ ≤ _ := by simpa only [one_mul] using
        (mul_le_mul_of_nonneg_right habsorb (by positivity : 0 ≤ (A.card : ℝ)^3))
