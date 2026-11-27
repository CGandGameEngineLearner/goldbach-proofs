import Mathlib

open scoped BigOperators

private lemma tail_sum_le (k : ℕ) :
    (∑ j ∈ Finset.range k, (1 : ℝ) / (4 * (((4 + j : ℕ) : ℝ) + 1) ^ 2))
      ≤ 1 / 16 - 1 / (4 * ((k : ℝ) + 4)) := by
  have heq : ∀ j : ℕ,
      (1 : ℝ) / (4 * (((4 + j : ℕ) : ℝ) + 1) ^ 2)
        = 1 / (4 * ((j : ℝ) + 5) ^ 2) := by
    intro j
    push_cast
    have h : (4 : ℝ) * ((4 + (j : ℝ)) + 1) ^ 2 = 4 * ((j : ℝ) + 5) ^ 2 := by ring
    rw [h]
  simp only [heq]
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [Finset.sum_range_succ]
    push_cast
    have harg : ((k : ℝ) + 1 + 4) = (k : ℝ) + 5 := by ring
    rw [harg]
    have hterm : (1 : ℝ) / (4 * ((k : ℝ) + 5) ^ 2)
        ≤ 1 / (4 * ((k : ℝ) + 4)) - 1 / (4 * ((k : ℝ) + 5)) := by
      have hA : (0 : ℝ) < 4 * ((k : ℝ) + 4) * ((k : ℝ) + 5) := by positivity
      have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      have hB : 4 * ((k : ℝ) + 4) * ((k : ℝ) + 5) ≤ 4 * ((k : ℝ) + 5) ^ 2 := by
        nlinarith [hk]
      have h := one_div_le_one_div_of_le (α := ℝ) hA hB
      have hdiff : (1 : ℝ) / (4 * ((k : ℝ) + 4)) - 1 / (4 * ((k : ℝ) + 5))
          = 1 / (4 * ((k : ℝ) + 4) * ((k : ℝ) + 5)) := by
        field_simp
        ring
      rw [hdiff]
      exact h
    linarith

private lemma tail_prod_le (k : ℕ) :
    (∏ j ∈ Finset.range k, (1 + 1 / (4 * (((4 + j : ℕ) : ℝ) + 1) ^ 2))) ≤ 33 / 31 := by
  have hsum : (∑ j ∈ Finset.range k, (1 : ℝ) / (4 * (((4 + j : ℕ) : ℝ) + 1) ^ 2))
      ≤ 1 / 16 := by
    have h := tail_sum_le k
    have hpos : (0 : ℝ) ≤ 1 / (4 * ((k : ℝ) + 4)) := by positivity
    linarith
  calc (∏ j ∈ Finset.range k, (1 + 1 / (4 * (((4 + j : ℕ) : ℝ) + 1) ^ 2)))
      ≤ Real.exp (∑ j ∈ Finset.range k, (1 : ℝ) / (4 * (((4 + j : ℕ) : ℝ) + 1) ^ 2)) :=
        Real.prod_one_add_le_exp_sum (Finset.range k) (fun j => by positivity)
    _ ≤ Real.exp (1 / 16) := Real.exp_le_exp.mpr hsum
    _ ≤ (2 + 1 / 16) / (2 - 1 / 16) :=
        Real.exp_le_two_add_div_two_sub (by norm_num) (by norm_num)
    _ = 33 / 31 := by norm_num

private lemma prod_bound (m : ℕ) :
    (∏ j ∈ Finset.range m, (1 + 1 / (4 * ((j : ℝ) + 1) ^ 2))) < 3 / 2 := by
  have hF4 : (∏ j ∈ Finset.range 4, (1 + 1 / (4 * ((j : ℝ) + 1) ^ 2)))
      = 204425 / 147456 := by
    norm_num [Finset.prod_range_succ]
  by_cases hm : m ≤ 4
  · have hsub : Finset.range m ⊆ Finset.range 4 := Finset.range_subset_range.mpr hm
    have hle : (∏ j ∈ Finset.range m, (1 + 1 / (4 * ((j : ℝ) + 1) ^ 2)))
        ≤ ∏ j ∈ Finset.range 4, (1 + 1 / (4 * ((j : ℝ) + 1) ^ 2)) := by
      apply Finset.prod_le_prod_of_subset_of_one_le₀ hsub
      · intro i hi
        positivity
      · intro i hi hni
        have h : (0 : ℝ) ≤ 1 / (4 * ((i : ℝ) + 1) ^ 2) := by positivity
        linarith
    rw [hF4] at hle
    have hlt : (204425 : ℝ) / 147456 < 3 / 2 := by norm_num
    linarith
  · have hm4 : 4 < m := by omega
    obtain ⟨k, rfl⟩ : ∃ k, m = 4 + k := ⟨m - 4, by omega⟩
    rw [Finset.prod_range_add (fun j : ℕ => 1 + 1 / (4 * ((j : ℝ) + 1) ^ 2)) 4 k]
    rw [hF4]
    have htail := tail_prod_le k
    have h1 : (204425 : ℝ) / 147456
        * (∏ j ∈ Finset.range k, (1 + 1 / (4 * (((4 + j : ℕ) : ℝ) + 1) ^ 2)))
        ≤ 204425 / 147456 * (33 / 31) :=
      mul_le_mul_of_nonneg_left htail (by norm_num)
    have h2 : (204425 : ℝ) / 147456 * (33 / 31) < 3 / 2 := by norm_num
    linarith

theorem Conjectures.Goldbach.OddSignedSubsetFloor :
    ∀ (m : ℕ) (c : Finset ℕ → ℝ), c ∅ = 1 → (∀ T ∈ (Finset.range m).powerset, -1 ≤ c T) → (1 / 2 : ℝ) < Finset.sum (Finset.range m).powerset (fun T => c T * Finset.prod T (fun j => 1 / (4 * ((j : ℝ) + 1)^2))) := by
  intro m c hc hbd
  have hP : (∏ j ∈ Finset.range m, (1 + 1 / (4 * ((j : ℝ) + 1) ^ 2))) < 3 / 2 :=
    prod_bound m
  have hpow : (∑ T ∈ (Finset.range m).powerset,
        ∏ j ∈ T, (1 / (4 * ((j : ℝ) + 1) ^ 2)))
      = ∏ j ∈ Finset.range m, (1 + 1 / (4 * ((j : ℝ) + 1) ^ 2)) :=
    (Finset.prod_one_add (f := fun j : ℕ => 1 / (4 * ((j : ℝ) + 1) ^ 2))
      (Finset.range m)).symm
  have hsplit : (∑ T ∈ (Finset.range m).powerset,
        c T * ∏ j ∈ T, (1 / (4 * ((j : ℝ) + 1) ^ 2)))
      = (∑ T ∈ (Finset.range m).powerset,
            (c T + 1) * ∏ j ∈ T, (1 / (4 * ((j : ℝ) + 1) ^ 2)))
        - (∑ T ∈ (Finset.range m).powerset,
            ∏ j ∈ T, (1 / (4 * ((j : ℝ) + 1) ^ 2))) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro T hT
    ring
  have hlow : (2 : ℝ) ≤ ∑ T ∈ (Finset.range m).powerset,
      (c T + 1) * ∏ j ∈ T, (1 / (4 * ((j : ℝ) + 1) ^ 2)) := by
    have hnonneg : ∀ T ∈ (Finset.range m).powerset,
        0 ≤ (c T + 1) * ∏ j ∈ T, (1 / (4 * ((j : ℝ) + 1) ^ 2)) := by
      intro T hT
      apply mul_nonneg
      · have := hbd T hT
        linarith
      · apply Finset.prod_nonneg
        intro j hj
        positivity
    have hmem : (∅ : Finset ℕ) ∈ (Finset.range m).powerset := by simp
    have hsingle := Finset.single_le_sum hnonneg hmem
    have h2 : ((c ∅ + 1) * ∏ j ∈ (∅ : Finset ℕ), (1 / (4 * ((j : ℝ) + 1) ^ 2))) = 2 := by
      norm_num [hc]
    rw [h2] at hsingle
    exact hsingle
  have hmain : 2 - (∏ j ∈ Finset.range m, (1 + 1 / (4 * ((j : ℝ) + 1) ^ 2)))
      ≤ ∑ T ∈ (Finset.range m).powerset,
          c T * ∏ j ∈ T, (1 / (4 * ((j : ℝ) + 1) ^ 2)) := by
    rw [hsplit, hpow]
    linarith
  linarith
