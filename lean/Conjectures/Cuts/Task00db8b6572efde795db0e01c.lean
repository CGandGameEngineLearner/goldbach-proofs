import Mathlib.Algebra.BigOperators.Fin

theorem Conjectures.Cuts.Task00db8b6572efde795db0e01c :
∀ (x1 x2 x3 : ℕ), (2 : ℕ) ≤ x1 → ∑ x5 : Fin x2, x3 / x1 ^ (↑x5 : ℕ) % x1 * x1 ^ (↑x5 : ℕ) = x3 % x1 ^ x2 := by
  intro b k n _
  induction k with
  | zero => simp [Nat.mod_one]
  | succ k ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, ih, pow_succ, Nat.mod_mul]
    rw [Nat.mul_comm (n / b^k % b) (b^k)]
