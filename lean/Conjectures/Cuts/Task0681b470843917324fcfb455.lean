import Mathlib
open scoped BigOperators

/-! Bounded case `M ≤ 2` of the triple-collision bound: the only input is the
trivial cardinality estimate `card ≤ |A|^2·|A|^2·|A|^2` together with `|A| ≤ 2`. -/

theorem Conjectures.Cuts.Task0681b470843917324fcfb455 :
    ∀ (x1 : Polynomial ℤ),   (3 : ℕ) ≤ x1.natDegree →     ∀ (x3 : ℝ),       (0 : ℝ) < x3 →         ∃ (x5 : ℝ),           (0 : ℝ) < x5 ∧             ∀ (x6 : ℕ),               (2 : ℕ) ≤ x6 →                 x6 ≤ (2 : ℕ) →                   ∀ x9 ⊆ Finset.Icc (1 : ℕ) x6,                     have x11 : Finset (Fin (3 : ℕ) → ℕ) := Fintype.piFinset fun (x11 : Fin (3 : ℕ)) => x9;                     have x12 : (Fin (3 : ℕ) → ℕ) → ℤ := fun (x12 : Fin (3 : ℕ) → ℕ) => ∑ x13 : Fin (3 : ℕ), Polynomial.eval (↑(x12 x13)) x1;                     ↑{x13 ∈ x11.product x11 | x12 x13.1 = x12 x13.2 ∧ ∀ (x14 : Equiv.Perm (Fin (3 : ℕ))), x13.2 ≠ x13.1 ∘ ⇑x14}.card ≤ x5 * ↑x6 ^ x3 * ↑x9.card ^ if x1.natDegree = (3 : ℕ) then (4 : ℕ) else (3 : ℕ) := by
  intro P hdeg ε hε
  refine ⟨8, by norm_num, ?_⟩
  intro M hM hM2 A hA
  have hMeq : M = 2 := by omega
  subst hMeq
  have hAc : A.card ≤ 2 := by
    have h := Finset.card_le_card hA
    have h2 : (Finset.Icc 1 2).card = 2 := by decide
    omega
  have hX : (Fintype.piFinset fun _ : Fin 3 => A).card = A.card ^ 3 := by
    rw [Fintype.card_piFinset]
    simp
  have hle : ({z ∈ (Fintype.piFinset fun _ : Fin 3 => A).product (Fintype.piFinset fun _ : Fin 3 => A) |
      (fun v : Fin 3 → ℕ => ∑ j : Fin 3, Polynomial.eval ((v j : ℕ) : ℤ) P) z.1 =
      (fun v : Fin 3 → ℕ => ∑ j : Fin 3, Polynomial.eval ((v j : ℕ) : ℤ) P) z.2 ∧
      ∀ (e : Equiv.Perm (Fin 3)), z.2 ≠ z.1 ∘ ⇑e}).card ≤ A.card ^ 6 := by
    have hsub : ({z ∈ (Fintype.piFinset fun _ : Fin 3 => A).product (Fintype.piFinset fun _ : Fin 3 => A) |
        (fun v : Fin 3 → ℕ => ∑ j : Fin 3, Polynomial.eval ((v j : ℕ) : ℤ) P) z.1 =
        (fun v : Fin 3 → ℕ => ∑ j : Fin 3, Polynomial.eval ((v j : ℕ) : ℤ) P) z.2 ∧
        ∀ (e : Equiv.Perm (Fin 3)), z.2 ≠ z.1 ∘ ⇑e}) ⊆
        (Fintype.piFinset fun _ : Fin 3 => A).product (Fintype.piFinset fun _ : Fin 3 => A) :=
      Finset.filter_subset _ _
    calc ({z ∈ (Fintype.piFinset fun _ : Fin 3 => A).product (Fintype.piFinset fun _ : Fin 3 => A) |
        (fun v : Fin 3 → ℕ => ∑ j : Fin 3, Polynomial.eval ((v j : ℕ) : ℤ) P) z.1 =
        (fun v : Fin 3 → ℕ => ∑ j : Fin 3, Polynomial.eval ((v j : ℕ) : ℤ) P) z.2 ∧
        ∀ (e : Equiv.Perm (Fin 3)), z.2 ≠ z.1 ∘ ⇑e}).card
        ≤ ((Fintype.piFinset fun _ : Fin 3 => A).product (Fintype.piFinset fun _ : Fin 3 => A)).card :=
          Finset.card_le_card hsub
      _ = A.card ^ 3 * A.card ^ 3 := by simp [Finset.card_product, hX]
      _ = A.card ^ 6 := by ring
  have hcast : (({z ∈ (Fintype.piFinset fun _ : Fin 3 => A).product (Fintype.piFinset fun _ : Fin 3 => A) |
      (fun v : Fin 3 → ℕ => ∑ j : Fin 3, Polynomial.eval ((v j : ℕ) : ℤ) P) z.1 =
      (fun v : Fin 3 → ℕ => ∑ j : Fin 3, Polynomial.eval ((v j : ℕ) : ℤ) P) z.2 ∧
      ∀ (e : Equiv.Perm (Fin 3)), z.2 ≠ z.1 ∘ ⇑e}).card : ℝ) ≤ (A.card : ℝ) ^ 6 := by
    exact_mod_cast hle
  have hn : (A.card : ℝ) ≤ 2 := by exact_mod_cast hAc
  have hn0 : (0 : ℝ) ≤ (A.card : ℝ) := by positivity
  have hr : (1 : ℝ) ≤ (2 : ℝ) ^ ε := Real.one_le_rpow (by norm_num) (le_of_lt hε)
  split_ifs with h3
  ·
    have step1 : (A.card : ℝ) ^ 6 ≤ 8 * (A.card : ℝ) ^ 4 := by
      have h1 : (A.card : ℝ) ^ 2 ≤ 8 := by nlinarith
      calc (A.card : ℝ) ^ 6 = (A.card : ℝ) ^ 4 * (A.card : ℝ) ^ 2 := by ring
        _ ≤ (A.card : ℝ) ^ 4 * 8 :=
            mul_le_mul_of_nonneg_left h1 (pow_nonneg hn0 4)
        _ = 8 * (A.card : ℝ) ^ 4 := by ring
    have step2 : 8 * (A.card : ℝ) ^ 4 ≤ 8 * (2 : ℝ) ^ ε * (A.card : ℝ) ^ 4 := by
      have h4 : (0 : ℝ) ≤ (A.card : ℝ) ^ 4 := pow_nonneg hn0 4
      calc 8 * (A.card : ℝ) ^ 4 = 8 * 1 * (A.card : ℝ) ^ 4 := by ring
        _ ≤ 8 * (2 : ℝ) ^ ε * (A.card : ℝ) ^ 4 := by
            apply mul_le_mul_of_nonneg_right _ h4
            exact mul_le_mul_of_nonneg_left hr (by norm_num)
    exact le_trans (le_trans hcast step1) step2
  ·
    have step1 : (A.card : ℝ) ^ 6 ≤ 8 * (A.card : ℝ) ^ 3 := by
      have h1 : (A.card : ℝ) ^ 3 ≤ 8 := by
        have h : (A.card : ℝ) ^ 3 ≤ (2 : ℝ) ^ 3 := by gcongr
        nlinarith [h]
      calc (A.card : ℝ) ^ 6 = (A.card : ℝ) ^ 3 * (A.card : ℝ) ^ 3 := by ring
        _ ≤ (A.card : ℝ) ^ 3 * 8 :=
            mul_le_mul_of_nonneg_left h1 (pow_nonneg hn0 3)
        _ = 8 * (A.card : ℝ) ^ 3 := by ring
    have step2 : 8 * (A.card : ℝ) ^ 3 ≤ 8 * (2 : ℝ) ^ ε * (A.card : ℝ) ^ 3 := by
      have h4 : (0 : ℝ) ≤ (A.card : ℝ) ^ 3 := pow_nonneg hn0 3
      calc 8 * (A.card : ℝ) ^ 3 = 8 * 1 * (A.card : ℝ) ^ 3 := by ring
        _ ≤ 8 * (2 : ℝ) ^ ε * (A.card : ℝ) ^ 3 := by
            apply mul_le_mul_of_nonneg_right _ h4
            exact mul_le_mul_of_nonneg_left hr (by norm_num)
    exact le_trans (le_trans hcast step1) step2
