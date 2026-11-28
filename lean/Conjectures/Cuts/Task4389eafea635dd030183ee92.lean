import Mathlib

/-! 小支撑段：|A| ≤ M^(ε/4) 时碰撞数 ≤ C·M^ε·|A|³（取 C = 1，平凡计数）。 -/

theorem Conjectures.Cuts.Task4389eafea635dd030183ee92 : ∀ (x1 : Polynomial ℤ),   (3 : ℕ) ≤ x1.natDegree →     x1.natDegree ≠ (3 : ℕ) →       ∀ (x4 : ℝ),         (0 : ℝ) < x4 →           ∃ (x6 : ℝ),             (0 : ℝ) < x6 ∧               ∀ (x7 : ℕ),                 (2 : ℕ) ≤ x7 →                   ∀ x9 ⊆ Finset.Icc (1 : ℕ) x7,                     (↑x9.card : ℝ) ≤ (↑x7 : ℝ) ^ (x4 / (4 : ℝ)) →                       have x12 : Finset (Fin (3 : ℕ) → ℕ) := Fintype.piFinset fun (x12 : Fin (3 : ℕ)) => x9;                       have x13 : (Fin (3 : ℕ) → ℕ) → ℤ := fun (x13 : Fin (3 : ℕ) → ℕ) => ∑ x14 : Fin (3 : ℕ), Polynomial.eval (↑(x13 x14) : ℤ) x1;                       (↑{x14 ∈ x12.product x12 | x13 x14.1 = x13 x14.2 ∧ ∀ (x15 : Equiv.Perm (Fin (3 : ℕ))), x14.2 ≠ x14.1 ∘ (⇑x15 : Fin (3 : ℕ) → Fin (3 : ℕ))}.card : ℝ) ≤ x6 * (↑x7 : ℝ) ^ x4 * (↑x9.card : ℝ) ^ (3 : ℕ) := by
  intro P h3 hne eps heps
  refine ⟨1, one_pos, ?_⟩
  intro M hM A hA hK
  dsimp only
  set T : Finset (Fin (3 : ℕ) → ℕ) := Fintype.piFinset (fun _ : Fin (3 : ℕ) => A) with hT
  set Cc : Finset ((Fin (3 : ℕ) → ℕ) × (Fin (3 : ℕ) → ℕ)) :=
    (T.product T).filter (fun f => (∑ i : Fin (3 : ℕ), Polynomial.eval (↑(f.1 i) : ℤ) P) = (∑ i : Fin (3 : ℕ), Polynomial.eval (↑(f.2 i) : ℤ) P) ∧ ∀ (σ : Equiv.Perm (Fin (3 : ℕ))), f.2 ≠ f.1 ∘ ⇑σ) with hC
  have hTcard : T.card = A.card ^ (3 : ℕ) := by
    rw [hT]
    simp [Fintype.card_piFinset]
  have hCle : Cc.card ≤ A.card ^ (6 : ℕ) := by
    have hsub : Cc ⊆ T.product T := by rw [hC]; exact Finset.filter_subset _ _
    have h1 : Cc.card ≤ (T.product T).card := Finset.card_le_card hsub
    have h2 : (T.product T).card = T.card * T.card := Finset.card_product ..
    have h3 : T.card * T.card = A.card ^ (6 : ℕ) := by rw [hTcard]; ring
    exact le_trans h1 (le_of_eq (h2.trans h3))
  have hKnn : (0 : ℝ) ≤ (A.card : ℝ) := by positivity
  have hM1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast (by omega : 1 ≤ M)
  have hK3 : (A.card : ℝ) ^ (3 : ℕ) ≤ (M : ℝ) ^ eps := by
    have ha : (A.card : ℝ) ^ (3 : ℕ) ≤ ((M : ℝ) ^ (eps / 4)) ^ (3 : ℕ) :=
      pow_le_pow_left₀ hKnn hK 3
    have hb : ((M : ℝ) ^ (eps / 4)) ^ (3 : ℕ) = (M : ℝ) ^ (eps / 4 * 3) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0:ℝ) ≤ (M:ℝ))]
      norm_num
    have hc : (M : ℝ) ^ (eps / 4 * 3) ≤ (M : ℝ) ^ eps :=
      Real.rpow_le_rpow_of_exponent_le hM1 (by linarith)
    linarith
  have hcast : ((Cc.card : ℕ) : ℝ) ≤ (A.card : ℝ) ^ (6 : ℕ) := by exact_mod_cast hCle
  calc ((Cc.card : ℕ) : ℝ) ≤ (A.card : ℝ) ^ (6 : ℕ) := hcast
    _ = (A.card : ℝ) ^ (3 : ℕ) * (A.card : ℝ) ^ (3 : ℕ) := by ring
    _ ≤ (M : ℝ) ^ eps * (A.card : ℝ) ^ (3 : ℕ) := by gcongr
    _ = 1 * (M : ℝ) ^ eps * (A.card : ℝ) ^ (3 : ℕ) := by ring