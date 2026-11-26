import Mathlib

open Finset

/-- Deleting primes from the Mangoldt sum leaves exactly ψ(n) − θ(n). -/
private theorem nonprimeMass (n : ℕ) :
    (∑ k ∈ range (n+1), if k.Prime then 0 else ArithmeticFunction.vonMangoldt k) =
      Chebyshev.psi n - Chebyshev.theta n := by
  rw [Chebyshev.psi_eq_sum_Icc, Chebyshev.theta_eq_sum_Icc, Nat.floor_natCast,
    sum_filter, ← sum_sub_distrib, Nat.range_succ_eq_Icc_zero]
  apply sum_congr rfl
  intro k _
  by_cases hk : k.Prime
  · simp [hk, ArithmeticFunction.vonMangoldt_apply_prime hk]
  · simp [hk]

theorem PEqualNP.Outside.L_goldbach_fixed_ap_higher_powers_budget : ∀ n : ℕ, 10^16 ≤ n → (∑ k ∈ Finset.range (n+1), (if k.Prime then 0 else ArithmeticFunction.vonMangoldt k)) ≤ (n:ℝ)/200 := by
  intro n hn
  rw [nonprimeMass]
  have hx : (10^16 : ℝ) ≤ n := by exact_mod_cast hn
  apply (Chebyshev.psi_sub_theta_le (show (1:ℝ) ≤ n by linarith)).trans
  let y := Real.sqrt (Real.sqrt (n:ℝ))
  have hy : 0 ≤ y := Real.sqrt_nonneg _
  have hy2 : y^2 = Real.sqrt (n:ℝ) := Real.sq_sqrt (Real.sqrt_nonneg _)
  have hy4 : y^4 = (n:ℝ) := by
    rw [show (4:ℕ) = 2*2 by decide, pow_mul, hy2, Real.sq_sqrt (Nat.cast_nonneg n)]
  have hlo : 1600 ≤ y := by
    by_contra! h
    have := pow_lt_pow_left₀ h hy (by decide : 4 ≠ 0)
    linarith only [this, hx, hy4]
  have hlog : Real.log n ≤ 4*y := by
    rw [← hy4, Real.log_pow]
    have := Real.log_le_sub_one_of_pos (show 0 < y by linarith)
    norm_num only [Nat.cast_ofNat] at *
    linarith
  calc
    _ ≤ 2*y^2*(4*y) := by rw [hy2]; gcongr
    _ ≤ y^4/200 := by nlinarith only [mul_nonneg (sub_nonneg.mpr hlo) (pow_nonneg hy 3)]
    _ = _ := by rw [hy4]