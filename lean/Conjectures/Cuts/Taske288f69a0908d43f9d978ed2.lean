import Mathlib

theorem Conjectures.Cuts.Taske288f69a0908d43f9d978ed2 : (∀ (x1 : Finset ℕ) (x2 x3 : ℕ → ℕ),   have x4 : ℕ → ℕ → ℕ := fun (x4 x5 : ℕ) => ∑ x6 ∈ x1, (x2 x6).choose x4 * (x3 x6).choose x5;   ∑ x5 ∈ x1, (x2 x5 * x3 x5) ^ (2 : ℕ) = x4 (1 : ℕ) (1 : ℕ) + (2 : ℕ) * x4 (2 : ℕ) (1 : ℕ) + (2 : ℕ) * x4 (1 : ℕ) (2 : ℕ) + (4 : ℕ) * x4 (2 : ℕ) (2 : ℕ)) := by
  have square_split (n : ℕ) : n ^ 2 = n + 2 * n.choose 2 := by
    cases n with
    | zero => rfl
    | succ m =>
      have h : (m + 1) * m = (m + 1).choose 2 * 2 := by
        simpa only [Nat.choose_one_right] using Nat.add_one_mul_choose_eq m 1
      change (m + 1) ^ 2 = (m + 1) + 2 * (m + 1).choose 2
      rw [Nat.mul_comm 2 ((m + 1).choose 2), ← h]
      ring
  intro s a b
  dsimp only
  simp only [Nat.choose_one_right, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_pow, square_split (a i), square_split (b i)]
  ring
