import Mathlib

theorem Conjectures.Cuts.Taskc7fea2c4c3799c095daf5d5a : (∀ (x1 : Finset ℕ) (x2 x3 : ℕ → ℕ), (∑ x4 ∈ x1, x2 x4 * x3 x4) ^ (2 : ℕ) ≤ {x4 ∈ x1 | (0 : ℕ) < x2 x4 ∧ (0 : ℕ) < x3 x4}.card * ∑ x4 ∈ x1, (x2 x4 * x3 x4) ^ (2 : ℕ)) := by
  intro S a b
  let T := S.filter (fun n => 0 < a n ∧ 0 < b n)
  have hsub : T ⊆ S := Finset.filter_subset _ _
  have heq : (∑ n ∈ T, a n * b n) = ∑ n ∈ S, a n * b n := by
    apply Finset.sum_subset hsub
    intro n hn h
    by_cases ha : a n = 0
    · simp [ha]
    by_cases hb : b n = 0
    · simp [hb]
    exact False.elim (h (Finset.mem_filter.mpr ⟨hn, Nat.pos_of_ne_zero ha, Nat.pos_of_ne_zero hb⟩))
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq T (fun _ => (1 : ℕ)) (fun n => a n * b n)
  simp only [one_mul, one_pow, Finset.sum_const, smul_eq_mul, mul_one] at hcs
  rw [← heq]
  exact hcs.trans (Nat.mul_le_mul_left _ (Finset.sum_le_sum_of_subset_of_nonneg hsub (by intros; exact Nat.zero_le _)))
