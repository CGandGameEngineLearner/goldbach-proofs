import Mathlib

-- child 1 zh: 长窗口（H ≥ √X）：用有界判据 0 < #{p ≤ n : p 与 n-p 都是素数} 的否定表述例外集，其计数满足幂节省。
-- child 1 en: Long windows (H >= sqrt X): the exceptional set, written with the bounded test that no p <= n has p and n - p both prime, obeys the power saving.
-- child 2 zh: 短窗口（X^(7/120+ε) ≤ H < √X）：同一幂节省。
-- child 2 en: Short windows (X^(7/120+eps) <= H < sqrt X): the same power saving.

theorem Conjectures.Cuts.Cutf7a23f4aa03713291dda44ae
    (h₁ : ∀ ε : ℝ, 0 < ε → ∃ δ C : ℝ, 0 < δ ∧ δ < 1 ∧ 0 < C ∧ ∃ T : ℕ,
      ∀ X H : ℕ, T ≤ X → H ≤ X → (X : ℝ) ^ ((7 : ℝ) / 120 + ε) ≤ (H : ℝ) →
        (X : ℝ) ^ (1 / 2 : ℝ) ≤ (H : ℝ) →
        ((((Finset.Icc (X - H) X).filter (fun n : ℕ => Even n ∧
          ¬ (0 < ((Finset.range (n + 1)).filter (fun p => Nat.Prime p ∧ Nat.Prime (n - p))).card))).card : ℝ) ≤
          C * (H : ℝ) ^ (1 - δ)))
    (h₂ : ∀ ε : ℝ, 0 < ε → ∃ δ C : ℝ, 0 < δ ∧ δ < 1 ∧ 0 < C ∧ ∃ T : ℕ,
      ∀ X H : ℕ, T ≤ X → H ≤ X → (X : ℝ) ^ ((7 : ℝ) / 120 + ε) ≤ (H : ℝ) →
        (H : ℝ) < (X : ℝ) ^ (1 / 2 : ℝ) →
        ((((Finset.Icc (X - H) X).filter (fun n : ℕ => Even n ∧
          ¬ (0 < ((Finset.range (n + 1)).filter (fun p => Nat.Prime p ∧ Nat.Prime (n - p))).card))).card : ℝ) ≤
          C * (H : ℝ) ^ (1 - δ))) :
    (by classical exact ∀ ε : ℝ, 0<ε → ∃ δ C : ℝ, 0<δ ∧ δ<1 ∧ 0<C ∧ ∃ T : ℕ, ∀ X H : ℕ, T≤X → H≤X → (X:ℝ)^((7:ℝ)/120+ε) ≤ (H:ℝ) → (((Finset.Icc (X-H) X).filter (fun n : ℕ => Even n ∧ ¬ (∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p+q=n))).card:ℝ) ≤ C*(H:ℝ)^(1-δ)) := by
  classical
  intro ε hε
  obtain ⟨δ₁, C₁, hδ₁, hδ₁lt, hC₁, T₁, hP₁⟩ := h₁ ε hε
  obtain ⟨δ₂, C₂, hδ₂, hδ₂lt, hC₂, T₂, hP₂⟩ := h₂ ε hε
  refine ⟨min δ₁ δ₂, max C₁ C₂, lt_min hδ₁ hδ₂, min_lt_iff.mpr (Or.inl hδ₁lt),
    lt_max_of_lt_left hC₁, max (max T₁ T₂) 4, ?_⟩
  intro X H hX hH hbig
  have hX4 : 4 ≤ X := le_trans (le_max_right (max T₁ T₂) 4) hX
  have hX₁ : T₁ ≤ X := le_trans (le_trans (le_max_left T₁ T₂) (le_max_left (max T₁ T₂) 4)) hX
  have hX₂ : T₂ ≤ X := le_trans (le_trans (le_max_right T₁ T₂) (le_max_left (max T₁ T₂) 4)) hX
  have hXpos : (1 : ℝ) < (X : ℝ) := by exact_mod_cast (by omega : 1 < X)
  have hone : (1 : ℝ) < (X : ℝ) ^ ((7 : ℝ) / 120 + ε) := Real.one_lt_rpow hXpos (by positivity)
  have hH1 : (1 : ℝ) ≤ (H : ℝ) := le_trans (le_of_lt hone) hbig
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
    have hle : 1 - δ₁ ≤ 1 - min δ₁ δ₂ := by linarith [min_le_left δ₁ δ₂]
    have hstep : (H : ℝ) ^ (1 - δ₁) ≤ (H : ℝ) ^ (1 - min δ₁ δ₂) :=
      Real.rpow_le_rpow_of_exponent_le hH1 hle
    have hnonneg : (0 : ℝ) ≤ (H : ℝ) ^ (1 - δ₁) := Real.rpow_nonneg (by positivity) _
    calc (((Finset.Icc (X - H) X).filter (fun n : ℕ => Even n ∧
        ¬ (∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n))).card : ℝ)
        ≤ ((((Finset.Icc (X - H) X).filter (fun n : ℕ => Even n ∧
        ¬ (0 < ((Finset.range (n + 1)).filter (fun p => Nat.Prime p ∧ Nat.Prime (n - p))).card))).card : ℝ)) := hcardle
      _ ≤ C₁ * (H : ℝ) ^ (1 - δ₁) := hb
      _ ≤ max C₁ C₂ * (H : ℝ) ^ (1 - δ₁) :=
          mul_le_mul_of_nonneg_right (le_max_left C₁ C₂) hnonneg
      _ ≤ max C₁ C₂ * (H : ℝ) ^ (1 - min δ₁ δ₂) :=
          mul_le_mul_of_nonneg_left hstep (le_of_lt hCmax)
  · have hlt : (H : ℝ) < (X : ℝ) ^ (1 / 2 : ℝ) := not_le.mp hcase
    have hb := hP₂ X H hX₂ hH hbig hlt
    have hle : 1 - δ₂ ≤ 1 - min δ₁ δ₂ := by linarith [min_le_right δ₁ δ₂]
    have hstep : (H : ℝ) ^ (1 - δ₂) ≤ (H : ℝ) ^ (1 - min δ₁ δ₂) :=
      Real.rpow_le_rpow_of_exponent_le hH1 hle
    have hnonneg : (0 : ℝ) ≤ (H : ℝ) ^ (1 - δ₂) := Real.rpow_nonneg (by positivity) _
    calc (((Finset.Icc (X - H) X).filter (fun n : ℕ => Even n ∧
        ¬ (∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n))).card : ℝ)
        ≤ ((((Finset.Icc (X - H) X).filter (fun n : ℕ => Even n ∧
        ¬ (0 < ((Finset.range (n + 1)).filter (fun p => Nat.Prime p ∧ Nat.Prime (n - p))).card))).card : ℝ)) := hcardle
      _ ≤ C₂ * (H : ℝ) ^ (1 - δ₂) := hb
      _ ≤ max C₁ C₂ * (H : ℝ) ^ (1 - δ₂) :=
          mul_le_mul_of_nonneg_right (le_max_right C₁ C₂) hnonneg
      _ ≤ max C₁ C₂ * (H : ℝ) ^ (1 - min δ₁ δ₂) :=
          mul_le_mul_of_nonneg_left hstep (le_of_lt hCmax)
