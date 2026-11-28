import Mathlib
theorem Conjectures.Cuts.Task4389eafea635dd030183ee92 : (∀ (x1 : Polynomial ℤ),   (3 : ℕ) ≤ x1.natDegree →     x1.natDegree ≠ (3 : ℕ) →       ∀ (x4 : ℝ),         (0 : ℝ) < x4 →           ∃ (x6 : ℝ),             (0 : ℝ) < x6 ∧               ∀ (x7 : ℕ),                 (2 : ℕ) ≤ x7 →                   ∀ x9 ⊆ Finset.Icc (1 : ℕ) x7,                     (↑x9.card : ℝ) ≤ (↑x7 : ℝ) ^ (x4 / (4 : ℝ)) →                       have x12 : Finset (Fin (3 : ℕ) → ℕ) := Fintype.piFinset fun (x12 : Fin (3 : ℕ)) => x9;                       have x13 : (Fin (3 : ℕ) → ℕ) → ℤ := fun (x13 : Fin (3 : ℕ) → ℕ) => ∑ x14 : Fin (3 : ℕ), Polynomial.eval (↑(x13 x14) : ℤ) x1;                       (↑{x14 ∈ x12.product x12 | x13 x14.1 = x13 x14.2 ∧ ∀ (x15 : Equiv.Perm (Fin (3 : ℕ))), x14.2 ≠ x14.1 ∘ (⇑x15 : Fin (3 : ℕ) → Fin (3 : ℕ))}.card : ℝ) ≤ x6 * (↑x7 : ℝ) ^ x4 * (↑x9.card : ℝ) ^ (3 : ℕ)) := 
by
  intro P hd hnc ε hε
  refine ⟨1,by norm_num,?_⟩
  intro M hM A hA hcard
  classical
  dsimp only
  calc
    _ ≤ (A.card:ℝ)^6 := by
      let S := Fintype.piFinset (fun _ : Fin 3 => A)
      have hc : S.card = A.card^3 := by simp [S,Fintype.card_piFinset]
      calc
        _ ≤ ((S.product S).card:ℝ) := by exact_mod_cast Finset.card_filter_le _ _
        _ = _ := by
          have hp : (S.product S).card = S.card*S.card := Finset.card_product _ _
          rw [hp,hc]; push_cast; ring
    _ = (A.card:ℝ)^3 * (A.card:ℝ)^3 := by ring
    _ ≤ (1*(M:ℝ)^ε) * (A.card:ℝ)^3 := by
      gcongr
      have hm : 1 ≤ (M:ℝ) := by exact_mod_cast (show 1≤M by omega)
      have ha := pow_le_pow_left₀ (Nat.cast_nonneg (α:=ℝ) A.card) hcard 3
      rw [←Real.rpow_natCast ((M:ℝ)^(ε/4)),←Real.rpow_mul (by positivity)] at ha
      simp only [one_mul]
      exact ha.trans (Real.rpow_le_rpow_of_exponent_le hm (by norm_num; linarith))

