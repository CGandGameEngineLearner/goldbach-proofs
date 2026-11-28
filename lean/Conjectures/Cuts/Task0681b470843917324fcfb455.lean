import Mathlib

theorem Conjectures.Cuts.Task0681b470843917324fcfb455 :
∀ (x1 : Polynomial ℤ),   (3 : ℕ) ≤ x1.natDegree →     ∀ (x3 : ℝ),       (0 : ℝ) < x3 →         ∃ (x5 : ℝ),           (0 : ℝ) < x5 ∧             ∀ (x6 : ℕ),               (2 : ℕ) ≤ x6 →                 x6 ≤ (2 : ℕ) →                   ∀ x9 ⊆ Finset.Icc (1 : ℕ) x6,                     have x11 : Finset (Fin (3 : ℕ) → ℕ) := Fintype.piFinset fun (x11 : Fin (3 : ℕ)) => x9;                     have x12 : (Fin (3 : ℕ) → ℕ) → ℤ := fun (x12 : Fin (3 : ℕ) → ℕ) => ∑ x13 : Fin (3 : ℕ), Polynomial.eval (↑(x12 x13)) x1;                     ↑{x13 ∈ x11.product x11 | x12 x13.1 = x12 x13.2 ∧ ∀ (x14 : Equiv.Perm (Fin (3 : ℕ))), x13.2 ≠ x13.1 ∘ ⇑x14}.card ≤ x5 * ↑x6 ^ x3 * ↑x9.card ^ if x1.natDegree = (3 : ℕ) then (4 : ℕ) else (3 : ℕ) := by
  classical
  intro P _ ε hε
  refine ⟨64,by norm_num,?_⟩
  intro M hM hM' A hA
  have hM2 : M=2 := by omega
  subst M
  intro T value
  have ht : T.card = A.card^3 := by simp [T]
  have hc := Finset.card_le_card hA
  have hA2 : A.card ≤ 2 := by simpa using hc
  have hf := Finset.card_filter_le (T.product T)
    (fun z => value z.1 = value z.2 ∧ ∀ σ : Equiv.Perm (Fin 3), z.2 ≠ z.1 ∘ σ)
  have htprod : (T.product T).card = A.card^3*A.card^3 :=
    (Finset.card_product T T).trans (by rw [ht])
  have hg := hf.trans_eq htprod
  have hReal : (1:ℝ) ≤ (2:ℝ)^ε := Real.one_le_rpow (by norm_num) hε.le
  apply (Nat.cast_le.mpr hg).trans
  push_cast
  rcases (show A.card=0 ∨ A.card=1 ∨ A.card=2 by omega) with h|h|h
  all_goals rw [h]; split_ifs <;> norm_num <;> linarith
