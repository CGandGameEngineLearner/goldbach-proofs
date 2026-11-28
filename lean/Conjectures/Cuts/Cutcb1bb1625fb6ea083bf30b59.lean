import Mathlib

-- child 1 zh: 长窗口（H ≥ √X）：用有界判据 0 < #{p ≤ n : p 与 n-p 都是素数} 的否定表述例外集，计数满足对数幂节省。
-- child 1 en: Long windows (H >= sqrt X): the exceptional set written with the bounded test that no p <= n has p and n - p both prime obeys the logarithmic power saving.
-- child 2 zh: 短窗口（X^(1/18+ε) ≤ H < √X）：同一对数幂节省。
-- child 2 en: Short windows (X^(1/18+eps) <= H < sqrt X): the same logarithmic power saving.

theorem Conjectures.Cuts.Cutcb1bb1625fb6ea083bf30b59
    (h₁ : ∀ ε : ℝ, 0 < ε → ∀ A : ℕ, ∃ C : ℝ, 0 < C ∧ ∃ T : ℕ,
      ∀ X H : ℕ, T ≤ X → H ≤ X → (X : ℝ) ^ ((1 : ℝ) / 18 + ε) ≤ (H : ℝ) →
        (X : ℝ) ^ (1 / 2 : ℝ) ≤ (H : ℝ) →
        ((((Finset.Icc (X - H) X).filter (fun n : ℕ => Even n ∧
          ¬ (0 < ((Finset.range (n + 1)).filter (fun p => Nat.Prime p ∧ Nat.Prime (n - p))).card))).card : ℝ) ≤
          C * (H : ℝ) / (1 + Real.log (X : ℝ)) ^ A))
    (h₂ : ∀ ε : ℝ, 0 < ε → ∀ A : ℕ, ∃ C : ℝ, 0 < C ∧ ∃ T : ℕ,
      ∀ X H : ℕ, T ≤ X → H ≤ X → (X : ℝ) ^ ((1 : ℝ) / 18 + ε) ≤ (H : ℝ) →
        (H : ℝ) < (X : ℝ) ^ (1 / 2 : ℝ) →
        ((((Finset.Icc (X - H) X).filter (fun n : ℕ => Even n ∧
          ¬ (0 < ((Finset.range (n + 1)).filter (fun p => Nat.Prime p ∧ Nat.Prime (n - p))).card))).card : ℝ) ≤
          C * (H : ℝ) / (1 + Real.log (X : ℝ)) ^ A)) :
    (by classical exact ∀ ε : ℝ, 0<ε → ∀ A : ℕ, ∃ C : ℝ, 0<C ∧ ∃ T : ℕ, ∀ X H : ℕ, T≤X → H≤X → (X:ℝ)^((1:ℝ)/18+ε) ≤ (H:ℝ) → (((Finset.Icc (X-H) X).filter (fun n : ℕ => Even n ∧ ¬ (∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p+q=n))).card:ℝ) ≤ C*(H:ℝ)/(1+Real.log (X:ℝ))^A) := by
  classical
  intro ε hε A
  obtain ⟨C₁, hC₁, T₁, hP₁⟩ := h₁ ε hε A
  obtain ⟨C₂, hC₂, T₂, hP₂⟩ := h₂ ε hε A
  refine ⟨max C₁ C₂, lt_max_of_lt_left hC₁, max (max T₁ T₂) 4, ?_⟩
  intro X H hX hH hbig
  have hX4 : 4 ≤ X := le_trans (le_max_right (max T₁ T₂) 4) hX
  have hX₁ : T₁ ≤ X := le_trans (le_trans (le_max_left T₁ T₂) (le_max_left (max T₁ T₂) 4)) hX
  have hX₂ : T₂ ≤ X := le_trans (le_trans (le_max_right T₁ T₂) (le_max_left (max T₁ T₂) 4)) hX
  have hnonneg : (0 : ℝ) ≤ (H : ℝ) / (1 + Real.log (X : ℝ)) ^ A := by positivity
  have hCmax : (0 : ℝ) < max C₁ C₂ := lt_max_of_lt_left hC₁
  have hsub : (Finset.Icc (X - H) X).filter (fun n : ℕ => Even n ∧
      ¬ (∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n)) ⊆
      (Finset.Icc (X - H) X).filter (fun n : ℕ => Even n ∧
      ¬ (0 < ((Finset.range (n + 1)).filter (fun p => Nat.Prime p ∧ Nat.Prime (n - p))).card)) := by
    intro n hn
    rw [Finset.mem_filter] at hn ⊢
    refine ⟨hn.1, hn.2.1, ?_⟩
    rintro hpos
    obtain ⟨p, hp⟩ := Finset.card_pos.mp hpos
    rw [Finset.mem_filter, Finset.mem_range] at hp
    exact hn.2.2 ⟨p, n - p, hp.2.1, hp.2.2, by omega⟩
  have hcardle : (((Finset.Icc (X - H) X).filter (fun n : ℕ => Even n ∧
      ¬ (∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n))).card : ℝ) ≤
      ((((Finset.Icc (X - H) X).filter (fun n : ℕ => Even n ∧
      ¬ (0 < ((Finset.range (n + 1)).filter (fun p => Nat.Prime p ∧ Nat.Prime (n - p))).card))).card : ℝ)) := by
    exact_mod_cast Finset.card_le_card hsub
  by_cases hcase : (X : ℝ) ^ (1 / 2 : ℝ) ≤ (H : ℝ)
  · have hb := hP₁ X H hX₁ hH hbig hcase
    calc (((Finset.Icc (X - H) X).filter (fun n : ℕ => Even n ∧
        ¬ (∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n))).card : ℝ)
        ≤ ((((Finset.Icc (X - H) X).filter (fun n : ℕ => Even n ∧
        ¬ (0 < ((Finset.range (n + 1)).filter (fun p => Nat.Prime p ∧ Nat.Prime (n - p))).card))).card : ℝ)) := hcardle
      _ ≤ C₁ * (H : ℝ) / (1 + Real.log (X : ℝ)) ^ A := hb
      _ ≤ max C₁ C₂ * (H : ℝ) / (1 + Real.log (X : ℝ)) ^ A := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_right (le_max_left C₁ C₂) (by positivity)
  · have hlt : (H : ℝ) < (X : ℝ) ^ (1 / 2 : ℝ) := not_le.mp hcase
    have hb := hP₂ X H hX₂ hH hbig hlt
    calc (((Finset.Icc (X - H) X).filter (fun n : ℕ => Even n ∧
        ¬ (∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n))).card : ℝ)
        ≤ ((((Finset.Icc (X - H) X).filter (fun n : ℕ => Even n ∧
        ¬ (0 < ((Finset.range (n + 1)).filter (fun p => Nat.Prime p ∧ Nat.Prime (n - p))).card))).card : ℝ)) := hcardle
      _ ≤ C₂ * (H : ℝ) / (1 + Real.log (X : ℝ)) ^ A := hb
      _ ≤ max C₁ C₂ * (H : ℝ) / (1 + Real.log (X : ℝ)) ^ A := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_right (le_max_right C₁ C₂) (by positivity)
