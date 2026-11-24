import Mathlib

/-- Summing an additive convolution up to N groups the same terms by their first index. -/
theorem PEqualNP.Outside.L_goldbach_conv_mass_prefix :
    let conv := fun (u v : ℕ → ℝ) (n : ℕ) =>
      Finset.sum (Finset.range (n + 1)) (fun k => u k * v (n - k))
    ∀ (u v : ℕ → ℝ) (N : ℕ), Finset.sum (Finset.range (N + 1)) (conv u v) =
      Finset.sum (Finset.range (N + 1))
        (fun p => u p * Finset.sum (Finset.range (N - p + 1)) v) := by
  intro conv u v N
  dsimp only [conv]
  rw [Finset.sum_range_diag_flip (N + 1) (fun p q => u p * v q)]
  apply Finset.sum_congr rfl
  intro p hp
  have hpN : p ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hp)
  rw [show N + 1 - p = N - p + 1 by omega, Finset.mul_sum]
