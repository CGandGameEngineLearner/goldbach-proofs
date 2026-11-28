import Mathlib

theorem Conjectures.Cuts.Taske288f69a0908d43f9d978ed2 : (∀ (x1 : Finset ℕ) (x2 x3 : ℕ → ℕ),   have x4 : ℕ → ℕ → ℕ := fun (x4 x5 : ℕ) => ∑ x6 ∈ x1, (x2 x6).choose x4 * (x3 x6).choose x5;   ∑ x5 ∈ x1, (x2 x5 * x3 x5) ^ (2 : ℕ) = x4 (1 : ℕ) (1 : ℕ) + (2 : ℕ) * x4 (2 : ℕ) (1 : ℕ) + (2 : ℕ) * x4 (1 : ℕ) (2 : ℕ) + (4 : ℕ) * x4 (2 : ℕ) (2 : ℕ)) := by
  intro S a b
  have sq (n : ℕ) : n ^ 2 = n + 2 * n.choose 2 := by
    induction n with
    | zero => decide
    | succ n ih =>
      rw [Nat.choose_succ_succ, Nat.choose_one_right]
      nlinarith
  dsimp only
  simp only [Nat.choose_one_right, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  rw [mul_pow, sq (a n), sq (b n)]
  ring
