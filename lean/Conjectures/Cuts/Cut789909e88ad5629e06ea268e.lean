import Mathlib

-- child 1 zh: 经典 Bombieri–Vinogradov 层：A 固定时，模数只到 X^(1/2)，最坏互素余类误差 B(q) 的 q 和在 X/(log X)^A 量级。这是 1965 年已证的分布水平 1/2，不含新内容。
-- child 1 en: Classical Bombieri–Vinogradov level: for fixed A, over moduli q ≤ X^(1/2) the sum of the worst coprime-class errors B(q) is O(X/(log X)^A). This is the known level 1/2 distribution, with no new content.
-- child 2 zh: 新前沿层：同一误差和在圆环 X^(1/2) < q ≤ X^(3/5) 上仍为 O(X/(log X)^A)。这才是越过 1/2 障壁的全部内容。
-- child 2 en: The new frontier: the same error sum over the annulus X^(1/2) < q ≤ X^(3/5) is still O(X/(log X)^A). This is where breaking the 1/2 barrier actually lives.

theorem Conjectures.Cuts.Cut789909e88ad5629e06ea268e
    (h₁ : ∀ A : ℝ, 0 < A → ∃ (C₁ : ℝ) (X₁ : ℕ), 0 < C₁ ∧ ∀ X : ℕ, X₁ ≤ X → ∃ B : ℕ → ℝ,
      (∀ q ∈ Finset.Icc 1 ⌊(X : ℝ) ^ (1 / 2 : ℝ)⌋₊, ∀ a : ℕ, Nat.Coprime a q →
        |(∑ k ∈ (Finset.Icc 1 X).filter (fun k => k % q = a % q), ArithmeticFunction.vonMangoldt k) - (X : ℝ) / (Nat.totient q : ℝ)| ≤ B q) ∧
      (∑ q ∈ Finset.Icc 1 ⌊(X : ℝ) ^ (1 / 2 : ℝ)⌋₊, B q) ≤ C₁ * (X : ℝ) / (Real.log (X : ℝ)) ^ A)
    (h₂ : ∀ A : ℝ, 0 < A → ∃ (C₂ : ℝ) (X₂ : ℕ), 0 < C₂ ∧ ∀ X : ℕ, X₂ ≤ X → ∃ B : ℕ → ℝ,
      (∀ q ∈ Finset.Icc (⌊(X : ℝ) ^ (1 / 2 : ℝ)⌋₊ + 1) ⌊(X : ℝ) ^ (3 / 5 : ℝ)⌋₊, ∀ a : ℕ, Nat.Coprime a q →
        |(∑ k ∈ (Finset.Icc 1 X).filter (fun k => k % q = a % q), ArithmeticFunction.vonMangoldt k) - (X : ℝ) / (Nat.totient q : ℝ)| ≤ B q) ∧
      (∑ q ∈ Finset.Icc (⌊(X : ℝ) ^ (1 / 2 : ℝ)⌋₊ + 1) ⌊(X : ℝ) ^ (3 / 5 : ℝ)⌋₊, B q) ≤ C₂ * (X : ℝ) / (Real.log (X : ℝ)) ^ A) :
    (∀ A : ℝ, 0 < A → ∃ (C : ℝ) (X₀ : ℕ), 0 < C ∧ ∀ X : ℕ, X₀ ≤ X → ∃ B : ℕ → ℝ,
      (∀ q ∈ Finset.Icc 1 ⌊(X : ℝ) ^ (3 / 5 : ℝ)⌋₊, ∀ a : ℕ, Nat.Coprime a q →
        |(∑ k ∈ (Finset.Icc 1 X).filter (fun k => k % q = a % q), ArithmeticFunction.vonMangoldt k) - (X : ℝ) / (Nat.totient q : ℝ)| ≤ B q) ∧
      (∑ q ∈ Finset.Icc 1 ⌊(X : ℝ) ^ (3 / 5 : ℝ)⌋₊, B q) ≤ C * (X : ℝ) / (Real.log (X : ℝ)) ^ A) := by
  classical
  intro A hA
  obtain ⟨C₁, X₁, hC₁, hP₁⟩ := h₁ A hA
  obtain ⟨C₂, X₂, hC₂, hP₂⟩ := h₂ A hA
  refine ⟨C₁ + C₂, max (max X₁ X₂) 1, by positivity, ?_⟩
  intro X hX
  have hX₁ : X₁ ≤ X := le_trans (le_trans (le_max_left X₁ X₂) (le_max_left (max X₁ X₂) 1)) hX
  have hX₂ : X₂ ≤ X := le_trans (le_trans (le_max_right X₁ X₂) (le_max_left (max X₁ X₂) 1)) hX
  have hX1 : 1 ≤ X := le_trans (le_max_right (max X₁ X₂) 1) hX
  obtain ⟨B₁, hB₁, hsum₁⟩ := hP₁ X hX₁
  obtain ⟨B₂, hB₂, hsum₂⟩ := hP₂ X hX₂
  set m : ℕ := ⌊(X : ℝ) ^ (1 / 2 : ℝ)⌋₊ with hm
  set M : ℕ := ⌊(X : ℝ) ^ (3 / 5 : ℝ)⌋₊ with hM
  have hmM : m ≤ M := by
    have hle : (X : ℝ) ^ (1 / 2 : ℝ) ≤ (X : ℝ) ^ (3 / 5 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hX1) (by norm_num)
    rw [hm, hM]
    exact Nat.floor_mono hle
  refine ⟨fun q => if q ≤ m then B₁ q else B₂ q, ?_, ?_⟩
  · intro q hq a ha
    obtain ⟨hq1, hqM⟩ := Finset.mem_Icc.mp hq
    by_cases hqm : q ≤ m
    · dsimp only
      rw [if_pos hqm]
      exact hB₁ q (Finset.mem_Icc.mpr ⟨hq1, hqm⟩) a ha
    · dsimp only
      rw [if_neg hqm]
      exact hB₂ q (Finset.mem_Icc.mpr ⟨by omega, hqM⟩) a ha
  · have hsplit : (∑ q ∈ Finset.Icc 1 M, (if q ≤ m then B₁ q else B₂ q))
        = (∑ q ∈ Finset.Icc 1 m, B₁ q) + (∑ q ∈ Finset.Icc (m + 1) M, B₂ q) := by
      rw [Finset.sum_ite]
      have hfil₁ : (Finset.Icc 1 M).filter (fun q => q ≤ m) = Finset.Icc 1 m := by
        ext q
        simp only [Finset.mem_filter, Finset.mem_Icc]
        constructor
        · rintro ⟨⟨h1, h2⟩, h3⟩
          exact ⟨h1, h3⟩
        · rintro ⟨h1, h2⟩
          exact ⟨⟨h1, le_trans h2 hmM⟩, h2⟩
      have hfil₂ : (Finset.Icc 1 M).filter (fun q => ¬ q ≤ m) = Finset.Icc (m + 1) M := by
        ext q
        simp only [Finset.mem_filter, Finset.mem_Icc]
        constructor
        · rintro ⟨⟨h1, h2⟩, h3⟩
          exact ⟨by omega, h2⟩
        · rintro ⟨h1, h2⟩
          exact ⟨⟨by omega, h2⟩, by omega⟩
      rw [hfil₁, hfil₂]
    rw [hsplit]
    calc (∑ q ∈ Finset.Icc 1 m, B₁ q) + (∑ q ∈ Finset.Icc (m + 1) M, B₂ q)
        ≤ C₁ * (X : ℝ) / (Real.log (X : ℝ)) ^ A + C₂ * (X : ℝ) / (Real.log (X : ℝ)) ^ A := by
          linarith
      _ = (C₁ + C₂) * (X : ℝ) / (Real.log (X : ℝ)) ^ A := by ring
