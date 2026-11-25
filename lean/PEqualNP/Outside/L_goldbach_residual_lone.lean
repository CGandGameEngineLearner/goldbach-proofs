import Mathlib

theorem PEqualNP.Outside.L_goldbach_residual_lone :
    let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let h := fun k : ℕ => ArithmeticFunction.vonMangoldt k-w k; ∀ X : ℕ, 2≤X → Finset.sum (Finset.range (X+1)) h ≤ ((Nat.sqrt X+1:ℕ):ℝ)*((Nat.log 2 X+1:ℕ):ℝ)*Real.log (X:ℝ) := by
  dsimp only
  intro X hX
  have hXone : 1 ≤ (X : ℝ) := by
    exact_mod_cast (show 1 ≤ X by omega)
  have hlogNat : 2 ≤ Nat.log 2 X + 1 := by
    have := Nat.log_pos (by decide : 1 < 2) hX
    omega
  have hlog : (2 : ℝ) ≤ ((Nat.log 2 X + 1 : ℕ) : ℝ) := by
    exact_mod_cast hlogNat
  have hsqrt : Real.sqrt (X : ℝ) ≤ ((Nat.sqrt X + 1 : ℕ) : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using (Real.real_sqrt_le_nat_sqrt_succ (a := X))
  calc
    _ = Chebyshev.psi X - Chebyshev.theta X := by
      simp only [Finset.sum_sub_distrib, Chebyshev.psi_eq_sum_Icc, Chebyshev.theta_eq_sum_Icc,
        Nat.floor_natCast, Nat.range_succ_eq_Icc_zero, Finset.sum_filter]
    _ ≤ |Chebyshev.psi X - Chebyshev.theta X| := le_abs_self _
    _ ≤ 2 * Real.sqrt (X : ℝ) * Real.log (X : ℝ) :=
      Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log hXone
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (Real.log_nonneg hXone)
      rw [mul_comm (2 : ℝ) (Real.sqrt (X : ℝ))]
      exact mul_le_mul hsqrt hlog (by norm_num) (by positivity)
