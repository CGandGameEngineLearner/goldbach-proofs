import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Factors
import Mathlib.Data.Nat.Log
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.NormNum

-- child 1 zh: 对 n ≡ 4 mod 6，证明以四个禁用剩余类定义的截断奇异级数一致不小于 81/64。
-- child 1 en: For n ≡ 4 mod 6, uniformly lower-bound the truncated singular series defined by the four forbidden residue classes by 81/64.
-- child 2 zh: 在每个二进整体区间固定短端窗口，证明相对于截断奇异级数的归一化表示数单侧亏损的平方和具有幂次节省。
-- child 2 en: Fix the short summand window within each dyadic target interval and obtain a power saving in the squared one-sided normalized representation deficit relative to the truncated singular series.

theorem Conjectures.Cuts.Cut9f58be7bbc77bbb576522564
    (hFloor :
      let series := fun P n : ℕ =>
        (27 / 2 : ℝ) * ∏ ℓ ∈ (Finset.Ico 5 P).filter Nat.Prime,
          (1 - (({0, ℓ - 2, n % ℓ, (n + 2) % ℓ} : Finset ℕ).card : ℝ) / (ℓ : ℝ)) /
            (1 - 1 / (ℓ : ℝ)) ^ 4
      ∀ P n : ℕ, n % 6 = 4 → (81 / 64 : ℝ) ≤ series P n)
    (hMoment :
      let series := fun P n : ℕ =>
        (27 / 2 : ℝ) * ∏ ℓ ∈ (Finset.Ico 5 P).filter Nat.Prime,
          (1 - (({0, ℓ - 2, n % ℓ, (n + 2) % ℓ} : Finset ℕ).card : ℝ) / (ℓ : ℝ)) /
            (1 - 1 / (ℓ : ℝ)) ^ 4
      let ch := fun p : ℕ => Nat.Prime p ∧ (p + 2).primeFactorsList.length ≤ 2
      let band := fun X : ℕ => (Finset.Icc 1 X).filter (fun p => 2 * X ≤ p ^ 2 ∧ p ^ 3 ≤ X ^ 2)
      let count := fun X n : ℕ => ((band X).filter (fun p => p ≤ n ∧ ch p ∧ ch (n - p))).card
      let targets := fun X : ℕ => (Finset.Icc X (2 * X)).filter (fun n => n % 6 = 4)
      let scale := fun X : ℕ => (1 + ((band X).card : ℝ)) / ((X : ℝ) + 1) ^ (1 / 32 : ℝ)
      let deficit := fun X n : ℕ =>
        max (0 : ℝ) (series (Nat.log 2 (X + 2)) n - (count X n : ℝ) / scale X)
      ∃ δ C : ℝ, 0 < δ ∧ δ < 1 ∧ 0 < C ∧ ∃ T : ℕ, ∀ X : ℕ, T ≤ X →
        (∑ n ∈ targets X, deficit X n ^ 2) ≤ C * (X : ℝ) ^ (1 - δ)) : (by
  classical
  exact let ch := fun p : ℕ => Nat.Prime p ∧ (p+2).primeFactorsList.length≤2; ∃ δ C : ℝ, 0<δ ∧ δ<1 ∧ 0<C ∧ ∃ T : ℕ, ∀ X : ℕ, T≤X → (((Finset.Icc X (2*X)).filter (fun n : ℕ => n % 6=4 ∧ ¬ (∃ p q : ℕ, ch p ∧ ch q ∧ p+q=n ∧ p^3≤n^2 ∧ n≤p^2))).card:ℝ)≤C*(X:ℝ)^(1-δ)) := by
  classical
  let series := fun P n : ℕ =>
    (27 / 2 : ℝ) * ∏ ℓ ∈ (Finset.Ico 5 P).filter Nat.Prime,
      (1 - (({0, ℓ - 2, n % ℓ, (n + 2) % ℓ} : Finset ℕ).card : ℝ) / (ℓ : ℝ)) /
        (1 - 1 / (ℓ : ℝ)) ^ 4
  let ch := fun p : ℕ => Nat.Prime p ∧ (p + 2).primeFactorsList.length ≤ 2
  let band := fun X : ℕ => (Finset.Icc 1 X).filter (fun p => 2 * X ≤ p ^ 2 ∧ p ^ 3 ≤ X ^ 2)
  let count := fun X n : ℕ => ((band X).filter (fun p => p ≤ n ∧ ch p ∧ ch (n - p))).card
  let targets := fun X : ℕ => (Finset.Icc X (2 * X)).filter (fun n => n % 6 = 4)
  let scale := fun X : ℕ => (1 + ((band X).card : ℝ)) / ((X : ℝ) + 1) ^ (1 / 32 : ℝ)
  let deficit := fun X n : ℕ =>
    max (0 : ℝ) (series (Nat.log 2 (X + 2)) n - (count X n : ℝ) / scale X)
  change ∃ δ C : ℝ, 0 < δ ∧ δ < 1 ∧ 0 < C ∧ ∃ T : ℕ, ∀ X : ℕ, T ≤ X →
    (∑ n ∈ targets X, deficit X n ^ 2) ≤ C * (X : ℝ) ^ (1 - δ) at hMoment
  rcases hMoment with ⟨δ, C, hδ, hδlt, hC, T, hMoment⟩
  refine ⟨δ, C, hδ, hδlt, hC, T, ?_⟩
  intro X hX
  let missing := (Finset.Icc X (2 * X)).filter (fun n =>
    n % 6 = 4 ∧ ¬ ∃ p q : ℕ, ch p ∧ ch q ∧ p + q = n ∧ p ^ 3 ≤ n ^ 2 ∧ n ≤ p ^ 2)
  change (missing.card : ℝ) ≤ C * (X : ℝ) ^ (1 - δ)
  have missing_subset : missing ⊆ targets X := by
    intro n hn
    have hn' := Finset.mem_filter.mp hn
    exact Finset.mem_filter.mpr ⟨hn'.1, hn'.2.1⟩
  have count_zero (n : ℕ) (hn : n ∈ missing) : count X n = 0 := by
    change ((band X).filter (fun p => p ≤ n ∧ ch p ∧ ch (n - p))).card = 0
    by_contra h
    obtain ⟨p, hp⟩ := Finset.card_ne_zero.mp h
    have hp' := Finset.mem_filter.mp hp
    have hp_band := (Finset.mem_filter.mp hp'.1).2
    have hn' := Finset.mem_filter.mp hn
    have hn_interval := Finset.mem_Icc.mp hn'.1
    exact hn'.2.2 ⟨p, n - p, hp'.2.2.1, hp'.2.2.2, Nat.add_sub_of_le hp'.2.1,
      hp_band.2.trans (Nat.pow_le_pow_left hn_interval.1 2), hn_interval.2.trans hp_band.1⟩
  calc
    (missing.card : ℝ) = ∑ _n ∈ missing, (1 : ℝ) := by simp
    _ ≤ ∑ n ∈ missing, deficit X n ^ 2 := by
      apply Finset.sum_le_sum
      intro n hn
      have hn' := Finset.mem_filter.mp hn
      have floor_le : (1 : ℝ) ≤ series (Nat.log 2 (X + 2)) n :=
        le_trans (by norm_num : (1 : ℝ) ≤ 81 / 64) (hFloor _ _ hn'.2.1)
      have one_le_deficit : (1 : ℝ) ≤ deficit X n := by
        simp only [deficit, count_zero n hn, Nat.cast_zero, zero_div, sub_zero]
        exact floor_le.trans (le_max_right _ _)
      simpa only [one_pow] using
        (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) one_le_deficit 2)
    _ ≤ ∑ n ∈ targets X, deficit X n ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg missing_subset (fun n _ _ => sq_nonneg (deficit X n))
    _ ≤ C * (X : ℝ) ^ (1 - δ) := hMoment X hX
