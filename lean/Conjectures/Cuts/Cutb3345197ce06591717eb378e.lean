import Mathlib

-- child 1 zh: 长窗口（H ≥ √X）：把例外集换成有界判据 0 < #{p ≤ n : p, n-p 素数且 HMod.hMod p d = a, HMod.hMod (n - p) d = b} 的否定，计数满足对数幂节省。
-- child 1 en: Long windows (H >= sqrt X): the exceptional set with the bounded test that no p <= n has p and n - p prime in the prescribed classes obeys the logarithmic power saving.
-- child 2 zh: 短窗口（X^(7/120+ε) ≤ H < √X）：同一对数幂节省。
-- child 2 en: Short windows (X^(7/120+eps) <= H < sqrt X): the same logarithmic power saving.

theorem Conjectures.Cuts.Cutb3345197ce06591717eb378e
    (h₁ : ∀ k : ℕ, ∀ ε : ℝ, 0 < ε → ∀ A : ℕ, ∃ C : ℝ, 0 < C ∧ ∃ T : ℕ,
      ∀ X H : ℕ, T ≤ X → H ≤ X → (X : ℝ) ^ ((7 : ℝ) / 120 + ε) ≤ (H : ℝ) →
        ∀ a b d : ℕ, 1 ≤ d → (d : ℝ) ≤ (1 + Real.log (X : ℝ)) ^ k → a < d → b < d →
          Nat.Coprime a d → Nat.Coprime b d → (X : ℝ) ^ (1 / 2 : ℝ) ≤ (H : ℝ) →
          ((((Finset.Icc (X - H) X).filter (fun n : ℕ => Even n ∧ HMod.hMod n d = HMod.hMod (a + b) d ∧
            ¬ (0 < ((Finset.range (n + 1)).filter (fun p => Nat.Prime p ∧ Nat.Prime (n - p) ∧
              HMod.hMod p d = a ∧ HMod.hMod (n - p) d = b)).card))).card : ℝ) ≤
            C * (H : ℝ) / (1 + Real.log (X : ℝ)) ^ A))
    (h₂ : ∀ k : ℕ, ∀ ε : ℝ, 0 < ε → ∀ A : ℕ, ∃ C : ℝ, 0 < C ∧ ∃ T : ℕ,
      ∀ X H : ℕ, T ≤ X → H ≤ X → (X : ℝ) ^ ((7 : ℝ) / 120 + ε) ≤ (H : ℝ) →
        ∀ a b d : ℕ, 1 ≤ d → (d : ℝ) ≤ (1 + Real.log (X : ℝ)) ^ k → a < d → b < d →
          Nat.Coprime a d → Nat.Coprime b d → (H : ℝ) < (X : ℝ) ^ (1 / 2 : ℝ) →
          ((((Finset.Icc (X - H) X).filter (fun n : ℕ => Even n ∧ HMod.hMod n d = HMod.hMod (a + b) d ∧
            ¬ (0 < ((Finset.range (n + 1)).filter (fun p => Nat.Prime p ∧ Nat.Prime (n - p) ∧
              HMod.hMod p d = a ∧ HMod.hMod (n - p) d = b)).card))).card : ℝ) ≤
            C * (H : ℝ) / (1 + Real.log (X : ℝ)) ^ A)) :
    (by classical exact ∀ k : ℕ, ∀ ε : ℝ, 0<ε → ∀ A : ℕ, ∃ C : ℝ, 0<C ∧ ∃ T : ℕ, ∀ X H : ℕ, T≤X → H≤X → (X:ℝ)^((7:ℝ)/120+ε) ≤ (H:ℝ) → ∀ a b d : ℕ, 1≤d → (d:ℝ)≤(1+Real.log (X:ℝ))^k → a<d → b<d → a.Coprime d → b.Coprime d → (((Finset.Icc (X-H) X).filter (fun n : ℕ => Even n ∧ HMod.hMod n d = HMod.hMod (a + b) d ∧ ¬ ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p+q=n ∧ HMod.hMod p d = a ∧ HMod.hMod q d = b)).card:ℝ) ≤ C*(H:ℝ)/(1+Real.log (X:ℝ))^A) := by
  classical
  intro k ε hε A
  obtain ⟨C₁, hC₁, T₁, hP₁⟩ := h₁ k ε hε A
  obtain ⟨C₂, hC₂, T₂, hP₂⟩ := h₂ k ε hε A
  refine ⟨max C₁ C₂, lt_max_of_lt_left hC₁, max (max T₁ T₂) 4, ?_⟩
  intro X H hX hH hbig a b d hd1 hdlog ha hb hca hcb
  have hX4 : 4 ≤ X := le_trans (le_max_right (max T₁ T₂) 4) hX
  have hX₁ : T₁ ≤ X := le_trans (le_trans (le_max_left T₁ T₂) (le_max_left (max T₁ T₂) 4)) hX
  have hX₂ : T₂ ≤ X := le_trans (le_trans (le_max_right T₁ T₂) (le_max_left (max T₁ T₂) 4)) hX
  have hnonneg : (0 : ℝ) ≤ (H : ℝ) / (1 + Real.log (X : ℝ)) ^ A := by positivity
  have hsub : (Finset.Icc (X - H) X).filter (fun n : ℕ => Even n ∧ HMod.hMod n d = HMod.hMod (a + b) d ∧
      ¬ (∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n ∧ HMod.hMod p d = a ∧ HMod.hMod q d = b)) ⊆
      (Finset.Icc (X - H) X).filter (fun n : ℕ => Even n ∧ HMod.hMod n d = HMod.hMod (a + b) d ∧
      ¬ (0 < ((Finset.range (n + 1)).filter (fun p => Nat.Prime p ∧ Nat.Prime (n - p) ∧
        HMod.hMod p d = a ∧ HMod.hMod (n - p) d = b)).card)) := by
    intro n hn
    rw [Finset.mem_filter] at hn ⊢
    refine ⟨hn.1, hn.2.1, hn.2.2.1, ?_⟩
    rintro hpos
    obtain ⟨p, hp⟩ := Finset.card_pos.mp hpos
    rw [Finset.mem_filter, Finset.mem_range] at hp
    exact hn.2.2.2 ⟨p, n - p, hp.2.1, hp.2.2.1, by omega, hp.2.2.2.1, hp.2.2.2.2⟩
  have hcardle : (((Finset.Icc (X - H) X).filter (fun n : ℕ => Even n ∧ HMod.hMod n d = HMod.hMod (a + b) d ∧
      ¬ (∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n ∧ HMod.hMod p d = a ∧ HMod.hMod q d = b))).card : ℝ) ≤
      ((((Finset.Icc (X - H) X).filter (fun n : ℕ => Even n ∧ HMod.hMod n d = HMod.hMod (a + b) d ∧
      ¬ (0 < ((Finset.range (n + 1)).filter (fun p => Nat.Prime p ∧ Nat.Prime (n - p) ∧
        HMod.hMod p d = a ∧ HMod.hMod (n - p) d = b)).card))).card : ℝ)) := by
    exact_mod_cast Finset.card_le_card hsub
  by_cases hcase : (X : ℝ) ^ (1 / 2 : ℝ) ≤ (H : ℝ)
  · have hb1 := hP₁ X H hX₁ hH hbig a b d hd1 hdlog ha hb hca hcb hcase
    calc (((Finset.Icc (X - H) X).filter (fun n : ℕ => Even n ∧ HMod.hMod n d = HMod.hMod (a + b) d ∧
        ¬ (∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n ∧ HMod.hMod p d = a ∧ HMod.hMod q d = b))).card : ℝ)
        ≤ ((((Finset.Icc (X - H) X).filter (fun n : ℕ => Even n ∧ HMod.hMod n d = HMod.hMod (a + b) d ∧
        ¬ (0 < ((Finset.range (n + 1)).filter (fun p => Nat.Prime p ∧ Nat.Prime (n - p) ∧
          HMod.hMod p d = a ∧ HMod.hMod (n - p) d = b)).card))).card : ℝ)) := hcardle
      _ ≤ C₁ * (H : ℝ) / (1 + Real.log (X : ℝ)) ^ A := hb1
      _ ≤ max C₁ C₂ * (H : ℝ) / (1 + Real.log (X : ℝ)) ^ A := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_right (le_max_left C₁ C₂) (by positivity)
  · have hlt : (H : ℝ) < (X : ℝ) ^ (1 / 2 : ℝ) := not_le.mp hcase
    have hb2 := hP₂ X H hX₂ hH hbig a b d hd1 hdlog ha hb hca hcb hlt
    calc (((Finset.Icc (X - H) X).filter (fun n : ℕ => Even n ∧ HMod.hMod n d = HMod.hMod (a + b) d ∧
        ¬ (∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n ∧ HMod.hMod p d = a ∧ HMod.hMod q d = b))).card : ℝ)
        ≤ ((((Finset.Icc (X - H) X).filter (fun n : ℕ => Even n ∧ HMod.hMod n d = HMod.hMod (a + b) d ∧
        ¬ (0 < ((Finset.range (n + 1)).filter (fun p => Nat.Prime p ∧ Nat.Prime (n - p) ∧
          HMod.hMod p d = a ∧ HMod.hMod (n - p) d = b)).card))).card : ℝ)) := hcardle
      _ ≤ C₂ * (H : ℝ) / (1 + Real.log (X : ℝ)) ^ A := hb2
      _ ≤ max C₁ C₂ * (H : ℝ) / (1 + Real.log (X : ℝ)) ^ A := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_right (le_max_right C₁ C₂) (by positivity)
