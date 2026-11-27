import Mathlib

namespace Conjectures.Goldbach.DyadicExceptionDensityTransfer_aux

theorem sum_pow_two_Ico_le (K J : ℕ) :
    (∑ j ∈ Finset.Ico K J, ((2 ^ j : ℕ) : ℝ)) ≤ ((2 ^ J : ℕ) : ℝ) := by
  have hsub : (∑ j ∈ Finset.Ico K J, (2 ^ j : ℕ)) ≤ ∑ j ∈ Finset.range J, (2 ^ j : ℕ) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro j hj
      exact Finset.mem_range.mpr (Finset.mem_Ico.mp hj).2
    · intro j _ _
      exact Nat.zero_le _
  have hrange : ∀ n : ℕ, (∑ j ∈ Finset.range n, (2 ^ j : ℕ)) ≤ 2 ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ]
      calc (∑ j ∈ Finset.range m, (2 ^ j : ℕ)) + 2 ^ m ≤ 2 ^ m + 2 ^ m :=
            Nat.add_le_add_right ih _
        _ = 2 ^ (m + 1) := by rw [pow_succ]; ring
  have hnat : (∑ j ∈ Finset.Ico K J, (2 ^ j : ℕ)) ≤ 2 ^ J := hsub.trans (hrange J)
  calc (∑ j ∈ Finset.Ico K J, ((2 ^ j : ℕ) : ℝ))
      = ((∑ j ∈ Finset.Ico K J, (2 ^ j : ℕ) : ℕ) : ℝ) := by simp
    _ ≤ ((2 ^ J : ℕ) : ℝ) := by exact_mod_cast hnat

end Conjectures.Goldbach.DyadicExceptionDensityTransfer_aux

theorem Conjectures.Goldbach.DyadicExceptionDensityTransfer :
    let reps (n : ℕ) := (Finset.range (n + 1)).filter (fun p => Nat.Prime p ∧ Nat.Prime (n - p)); let D (X : ℕ) := (Finset.Ico X (2 * X)).filter (fun n => 4 ≤ n ∧ Even n); let bad (X : ℕ) := (D X).filter (fun n => (reps n).card = 0); let exc (N : ℕ) := (Finset.range (N + 1)).filter (fun n => 4 ≤ n ∧ Even n ∧ (reps n).card = 0); ∀ (K N : ℕ) (ε : ℝ), 0 ≤ ε → (∀ n : ℕ, 4 ≤ n → n < 2 ^ K → Even n → (reps n).Nonempty) → (∀ j : ℕ, K ≤ j → ((bad (2 ^ j)).card : ℝ) ≤ ε * ((2 ^ j : ℕ) : ℝ)) → ((exc N).card : ℝ) ≤ 2 * ε * (N : ℝ) := by
  classical
  intro reps D bad exc K N ε hε hsmall hblocks
  have hmem_exc : ∀ (M n : ℕ), n ∈ exc M ↔ (n ≤ M ∧ 4 ≤ n ∧ Even n ∧ (reps n).card = 0) := by
    intro M n
    simp only [exc, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨by omega, h2, h3, h4⟩
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨by omega, h2, h3, h4⟩
  have hmem_bad : ∀ (X n : ℕ),
      n ∈ bad X ↔ (X ≤ n ∧ n < 2 * X ∧ 4 ≤ n ∧ Even n ∧ (reps n).card = 0) := by
    intro X n
    simp only [bad, D, Finset.mem_filter, Finset.mem_Ico, and_assoc]
  by_cases hN0 : N = 0
  · have hempty : exc 0 = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro n hn
      have := (hmem_exc 0 n).mp hn
      omega
    rw [hN0, hempty]
    simp
  have hJexists : ∃ J : ℕ, N < 2 ^ J ∧ 2 ^ J ≤ 2 * N := by
    refine ⟨Nat.log 2 N + 1, ?_, ?_⟩
    · have h := Nat.lt_pow_succ_log_self Nat.one_lt_two N
      simpa only [Nat.succ_eq_add_one] using h
    · have h := Nat.pow_log_le_self 2 hN0
      calc (2 : ℕ) ^ (Nat.log 2 N + 1) = 2 * 2 ^ (Nat.log 2 N) := by rw [pow_succ]; ring
        _ ≤ 2 * N := Nat.mul_le_mul_left 2 h
  obtain ⟨J, hJlt, hJle⟩ := hJexists
  have hcover : exc N ⊆ (Finset.Ico K J).biUnion (fun j => bad (2 ^ j)) := by
    intro n hn
    obtain ⟨hnN, hn4, hnEven, hncard⟩ := (hmem_exc N n).mp hn
    have hn0 : n ≠ 0 := by omega
    have h2K : 2 ^ K ≤ n := by
      by_contra hlt
      have hne : reps n ≠ ∅ := Finset.nonempty_iff_ne_empty.mp
        (hsmall n hn4 (Nat.lt_of_not_le hlt) hnEven)
      exact hne (Finset.card_eq_zero.mp hncard)
    have hjK : K ≤ Nat.log 2 n := Nat.le_log_of_pow_le Nat.one_lt_two h2K
    have hlo : 2 ^ (Nat.log 2 n) ≤ n := Nat.pow_log_le_self 2 hn0
    have hhi : n < 2 * 2 ^ (Nat.log 2 n) := by
      simpa only [Nat.succ_eq_add_one, pow_succ'] using
        Nat.lt_pow_succ_log_self Nat.one_lt_two n
    have hjJ : Nat.log 2 n < J := by
      have hlt : (2 : ℕ) ^ (Nat.log 2 n) < 2 ^ J := lt_of_le_of_lt hlo (lt_of_le_of_lt hnN hJlt)
      exact (Nat.pow_lt_pow_iff_right Nat.one_lt_two).mp hlt
    refine Finset.mem_biUnion.mpr ⟨Nat.log 2 n, Finset.mem_Ico.mpr ⟨hjK, hjJ⟩, ?_⟩
    exact (hmem_bad (2 ^ (Nat.log 2 n)) n).mpr ⟨hlo, hhi, hn4, hnEven, hncard⟩
  calc ((exc N).card : ℝ)
      ≤ (((Finset.Ico K J).biUnion (fun j => bad (2 ^ j))).card : ℝ) :=
        Nat.cast_le.mpr (Finset.card_le_card hcover)
    _ ≤ ((∑ j ∈ Finset.Ico K J, (bad (2 ^ j)).card : ℕ) : ℝ) :=
        Nat.cast_le.mpr Finset.card_biUnion_le
    _ = ∑ j ∈ Finset.Ico K J, ((bad (2 ^ j)).card : ℝ) := by simp
    _ ≤ ∑ j ∈ Finset.Ico K J, ε * ((2 ^ j : ℕ) : ℝ) := by
        apply Finset.sum_le_sum
        intro j hj
        exact hblocks j (Finset.mem_Ico.mp hj).1
    _ = ε * ∑ j ∈ Finset.Ico K J, ((2 ^ j : ℕ) : ℝ) :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ ε * ((2 ^ J : ℕ) : ℝ) := by
        exact mul_le_mul_of_nonneg_left
          (Conjectures.Goldbach.DyadicExceptionDensityTransfer_aux.sum_pow_two_Ico_le K J) hε
    _ ≤ ε * (2 * (N : ℝ)) := by
        exact mul_le_mul_of_nonneg_left (by exact_mod_cast hJle) hε
    _ = 2 * ε * (N : ℝ) := by ring
