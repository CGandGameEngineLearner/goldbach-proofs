import Mathlib

-- child 1 zh: 二进区块上的例外集界：对每个 e 大于 0，存在常数 C 大于 0 与 N，使得每个不小于 N 的 X，其区间 (X/2, X] 内的哥德巴赫例外偶数个数（即 [4, X] 与 [4, X/2] 累计计数之差）不超过 C 倍 X 的 4/7+e 次方。
-- child 1 en: Bound on dyadic blocks: for every e above 0 there are a constant C above 0 and N such that, for every X at least N, the number of exceptional even targets in (X/2, X], the difference of the cumulative counts on [4, X] and [4, X/2], is at most C times X to the power 4/7 + e.
-- child 2 zh: 二进递归的吸收不等式：若 D 至少为 C 除以 1 减 (1/2) 的 4/7+e 次方，则对 X 至少为 1，D 倍 X/2 的 4/7+e 次方与 C 倍 X 的 4/7+e 次方之和不超过 D 倍 X 的 4/7+e 次方。
-- child 2 en: Absorption inequality for the dyadic recursion: if D is at least C divided by 1 minus (1/2) to the power 4/7 + e, then for X at least 1 the sum of D times (X/2) to the power 4/7 + e and C times X to the power 4/7 + e is at most D times X to the power 4/7 + e.
-- Refinement: the exceptional-set bound on all of [4, X] follows from the dyadic-block bound by strong induction on X, using the absorption inequality at each halving step.

theorem Conjectures.Cuts.Cutc3ab3f28af83999e0f95f96f
    (h₁ : ∀ e : ℝ, 0 < e → ∃ (C : ℝ) (N : ℕ), 0 < C ∧ ∀ X : ℕ, N ≤ X →
      ((@Finset.filter ℕ (fun n : ℕ => 4 ≤ n ∧ Even n ∧ ¬ ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p+q=n) (Classical.decPred (fun n : ℕ => 4 ≤ n ∧ Even n ∧ ¬ ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p+q=n)) (Finset.Icc 4 X)).card : ℝ) -
      ((@Finset.filter ℕ (fun n : ℕ => 4 ≤ n ∧ Even n ∧ ¬ ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p+q=n) (Classical.decPred (fun n : ℕ => 4 ≤ n ∧ Even n ∧ ¬ ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p+q=n)) (Finset.Icc 4 (X/2))).card : ℝ) ≤
      C * (X:ℝ) ^ (4/7 + e))
    (h₂ : ∀ e : ℝ, 0 < e → ∀ (C D : ℝ), 0 < C → C / (1 - ((1:ℝ)/2)^(4/7 + e)) ≤ D → ∀ X : ℕ, 1 ≤ X →
      D * ((X / 2 : ℕ) : ℝ) ^ (4/7 + e) + C * (X:ℝ) ^ (4/7 + e) ≤ D * (X:ℝ) ^ (4/7 + e)) :
    (let bad := fun n : ℕ => 4 ≤ n ∧ Even n ∧ ¬ ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p+q=n; ∀ e : ℝ, 0 < e → ∃ (C : ℝ) (N : ℕ), 0 < C ∧ ∀ X : ℕ, N ≤ X → ((@Finset.filter ℕ bad (Classical.decPred bad) (Finset.Icc 4 X)).card : ℝ) ≤ C * (X:ℝ) ^ (4/7 + e)) := by
  intro bad e he
  obtain ⟨C, N, hC, hP1⟩ := h₁ e he
  have ha : (0 : ℝ) < 4 / 7 + e := by positivity
  have hr1 : ((1 : ℝ) / 2) ^ (4 / 7 + e) < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) ha
  have hr0 : (0 : ℝ) < ((1 : ℝ) / 2) ^ (4 / 7 + e) := Real.rpow_pos_of_pos (by norm_num) _
  have h1r : (0 : ℝ) < 1 - ((1 : ℝ) / 2) ^ (4 / 7 + e) := by linarith
  have hDpos : (0 : ℝ) < C / (1 - ((1 : ℝ) / 2) ^ (4 / 7 + e)) + ((2 * N + 1 : ℕ) : ℝ) :=
    by have h1 := div_pos hC h1r
       have h2 := (Nat.cast_pos.mpr (show 0 < 2 * N + 1 by omega) : (0 : ℝ) < ((2 * N + 1 : ℕ) : ℝ))
       linarith
  refine ⟨C / (1 - ((1 : ℝ) / 2) ^ (4 / 7 + e)) + ((2 * N + 1 : ℕ) : ℝ), N, hDpos, ?_⟩
  set D : ℝ := C / (1 - ((1 : ℝ) / 2) ^ (4 / 7 + e)) + ((2 * N + 1 : ℕ) : ℝ) with hD
  have hCD : C / (1 - ((1 : ℝ) / 2) ^ (4 / 7 + e)) ≤ D := by
    rw [hD]
    exact le_add_of_nonneg_right (by positivity)
  -- the count of exceptional targets in [4, X] never exceeds X
  have hcnt : ∀ X : ℕ, ((@Finset.filter ℕ bad (Classical.decPred bad) (Finset.Icc 4 X)).card : ℝ) ≤ (X : ℝ) := by
    intro X
    calc ((@Finset.filter ℕ bad (Classical.decPred bad) (Finset.Icc 4 X)).card : ℝ)
        ≤ ((Finset.Icc 4 X).card : ℝ) :=
          Nat.cast_le.mpr (@Finset.card_filter_le ℕ (Finset.Icc 4 X) bad (Classical.decPred bad))
      _ ≤ (X : ℝ) := by rw [Nat.card_Icc]; exact Nat.cast_le.mpr (by omega)
  intro X
  induction X using Nat.strong_induction_on with
  | ind X ih =>
    intro hXN
    rcases Nat.eq_zero_or_pos X with hX0 | hXpos
    · subst hX0
      have hz : ((@Finset.filter ℕ bad (Classical.decPred bad) (Finset.Icc 4 0)).card : ℝ) = 0 := by simp
      have hpow : ((0 : ℕ) : ℝ) ^ (4 / 7 + e) = 0 := Real.zero_rpow ha.ne'
      rw [hz, hpow]
      simp
    · have hX1 : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hXpos
      have hXpow : (1 : ℝ) ≤ ((X : ℕ) : ℝ) ^ (4 / 7 + e) := Real.one_le_rpow hX1 ha.le
      by_cases hsmall : X < 2 * N
      · calc ((@Finset.filter ℕ bad (Classical.decPred bad) (Finset.Icc 4 X)).card : ℝ)
          ≤ (X : ℝ) := hcnt X
        _ ≤ ((2 * N + 1 : ℕ) : ℝ) := by exact_mod_cast (show X ≤ 2 * N + 1 by omega)
        _ ≤ D := by rw [hD]; exact le_add_of_nonneg_left (div_pos hC h1r).le
        _ ≤ D * ((X : ℕ) : ℝ) ^ (4 / 7 + e) := le_mul_of_one_le_right hDpos.le hXpow
      · -- below X the induction hypothesis applies at X / 2, and the dyadic step is absorbed
        have ih' := ih (X / 2) (by omega) (by omega)
        have hp : ((@Finset.filter ℕ bad (Classical.decPred bad) (Finset.Icc 4 X)).card : ℝ) -
            ((@Finset.filter ℕ bad (Classical.decPred bad) (Finset.Icc 4 (X / 2))).card : ℝ) ≤
            C * ((X : ℕ) : ℝ) ^ (4 / 7 + e) := hP1 X hXN
        have habs := h₂ e he C D hC hCD X hXpos
        linarith
