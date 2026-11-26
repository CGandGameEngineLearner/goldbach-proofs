import Mathlib

namespace FixedAPPrimePowerError

/-- An explicit form of the higher-prime-power bound, uniform above the FR-7022 cutoff. -/
theorem psi_sub_theta_le {x : ℝ} (hx : 10 ^ 16 ≤ x) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (7 / 5) * Real.sqrt x := by
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 ≤ x := by linarith
  let t := x ^ (12 : ℝ)⁻¹
  have ht0 : 0 < t := by dsimp [t]; positivity
  have ht : 21 ≤ t := by
    apply le_of_not_gt
    intro h
    have hp := pow_lt_pow_left₀ h ht0.le (by decide : (12 : ℕ) ≠ 0)
    have ht12 : t ^ 12 = x := Real.rpow_inv_natCast_pow hx0 (by decide)
    rw [ht12] at hp
    linarith
  have root (k : ℕ) : x ^ ((12 : ℝ)⁻¹ * k) = t ^ k :=
    Real.rpow_mul_natCast hx0 _ _
  have htwo : x ^ (2 : ℝ)⁻¹ = t ^ 6 := by convert root 6 using 2; norm_num
  have hthree : x ^ (3 : ℝ)⁻¹ = t ^ 4 := by convert root 4 using 2; norm_num
  have hfive : x ^ (5 : ℝ)⁻¹ ≤ t ^ 3 := by
    rw [← root 3]
    apply Real.rpow_le_rpow_of_exponent_le hx1
    norm_num
  have hsqrt : Real.sqrt x = t ^ 6 := by simpa [Real.sqrt_eq_rpow, one_div] using htwo
  have hlog4 : Real.log 4 ≤ 1.387 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    linarith [Real.log_two_lt_d9]
  have hlog : Real.log t ≤ t / 4 := by
    have h := Real.log_le_sub_one_of_pos (div_pos ht0 (by norm_num) : 0 < t / 8)
    rw [Real.log_div ht0.ne' (by norm_num), show (8 : ℝ) = 2^3 by norm_num, Real.log_pow] at h
    linarith [Real.log_two_lt_d9]
  have psi6 : Chebyshev.psi (t ^ 6) ≤ 1.387 * t ^ 6 + 3 * t ^ 4 := by
    have h := Chebyshev.psi_le (one_le_pow₀ (by linarith : 1 ≤ t) (n := 6))
    rw [show t ^ 6 = (t ^ 3) ^ 2 by ring, Real.sqrt_sq (by positivity),
      ← pow_mul, Real.log_pow] at h
    norm_num at h
    nlinarith only [h, mul_le_mul_of_nonneg_right hlog4 (by positivity : 0 ≤ t ^ 6),
      mul_le_mul_of_nonneg_right hlog (by positivity : 0 ≤ t ^ 3)]
  have psi4 : Chebyshev.psi (t ^ 4) ≤ 1.4 * t ^ 4 + 2 * t ^ 3 := by
    have h := Chebyshev.psi_le (one_le_pow₀ (by linarith : 1 ≤ t) (n := 4))
    rw [show t ^ 4 = (t ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity),
      ← pow_mul, Real.log_pow] at h
    norm_num at h
    nlinarith only [h, mul_le_mul_of_nonneg_right (show Real.log 4 ≤ 1.4 by linarith)
      (by positivity : 0 ≤ t ^ 4), mul_le_mul_of_nonneg_right hlog (by positivity : 0 ≤ t ^ 2)]
  have psi5 : Chebyshev.psi (x ^ (5 : ℝ)⁻¹) ≤ 6 * t ^ 3 := calc
    _ ≤ Chebyshev.psi (t ^ 3) := Chebyshev.psi_mono hfive
    _ ≤ _ := (Chebyshev.psi_le_const_mul_self (by positivity)).trans
      (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
  have h4 : 21 * t ^ 3 ≤ t ^ 4 := by
    nlinarith only [mul_le_mul_of_nonneg_right ht (by positivity : 0 ≤ t ^ 3)]
  have ht2 : 441 ≤ t ^ 2 := by nlinarith [sq_nonneg (t - 21)]
  have h6 : 441 * t ^ 4 ≤ t ^ 6 := by
    nlinarith only [mul_le_mul_of_nonneg_right ht2 (by positivity : 0 ≤ t ^ 4)]
  have hc := Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi x
  rw [htwo, hthree] at hc
  rw [hsqrt]
  linarith [show 0 ≤ t ^ 4 by positivity]

/-- The same estimate in the finite-sum notation of the Goldbach task. -/
theorem higher_powers_le (n : ℕ) (hn : 10 ^ 16 ≤ n) :
    (∑ k ∈ Finset.range (n+1), if k.Prime then 0 else ArithmeticFunction.vonMangoldt k)
      ≤ (7 / 5 : ℝ) * Real.sqrt n := by
  have h := psi_sub_theta_le (x := n) (by exact_mod_cast hn)
  rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, Nat.floor_natCast, Finset.sum_filter] at h
  rw [Nat.range_succ_eq_Icc_zero, ← Finset.add_sum_Ioc_eq_sum_Icc (Nat.zero_le n)]
  simpa [ite_not] using h

/-- Restricting to one residue class preserves the bound for every modulus. -/
theorem higher_powers_in_class_le (q a n : ℕ) (hn : 10 ^ 16 ≤ n) :
    (∑ k ∈ (Finset.range (n+1)).filter (fun k => k % q = a % q),
      if k.Prime then 0 else ArithmeticFunction.vonMangoldt k) ≤ (7 / 5 : ℝ) * Real.sqrt n := by
  apply le_trans _ (higher_powers_le n hn)
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset ..)
    (by intro k _ _; split_ifs <;> positivity)

/-- At the lower endpoint, the square-root bound gives a relative error of 1.4 × 10⁻⁸. -/
theorem higher_powers_in_class_linear (q a n : ℕ) (hn : 10 ^ 16 ≤ n) :
    (∑ k ∈ (Finset.range (n+1)).filter (fun k => k % q = a % q),
      if k.Prime then 0 else ArithmeticFunction.vonMangoldt k) ≤ 7 * (n : ℝ) / 500000000 := by
  apply (higher_powers_in_class_le q a n hn).trans
  have hn' : (10 : ℝ)^16 ≤ n := by exact_mod_cast hn
  have hs : (10 : ℝ)^8 ≤ Real.sqrt n := Real.le_sqrt_of_sq_le (by linarith)
  nlinarith [mul_le_mul_of_nonneg_right hs (Real.sqrt_nonneg (n : ℝ)),
    Real.sq_sqrt (show 0 ≤ (n : ℝ) by positivity)]

/-- An asymmetric prime-error interval suffices for the full one-percent bound,
since the higher-prime-power weights only increase the sum. -/
theorem progression_bound_of_prime_interval (q a n : ℕ) (hn : 10 ^ 16 ≤ n) :
    let S := (Finset.range (n + 1)).filter (fun k => k % q = a % q)
    let P := ∑ k ∈ S, if k.Prime then ArithmeticFunction.vonMangoldt k else 0
    (-(n : ℝ) / 100 ≤ P - (n : ℝ) / q.totient) →
    P - (n : ℝ) / q.totient ≤ (n : ℝ) / 100 - 7 * n / 500000000 →
    |(∑ k ∈ S, ArithmeticFunction.vonMangoldt k) - (n : ℝ) / q.totient| ≤ n / 100 := by
  intro S P hlo hhi
  let R := ∑ k ∈ S, if k.Prime then 0 else ArithmeticFunction.vonMangoldt k
  have hR : 0 ≤ R := Finset.sum_nonneg fun k _ => by split_ifs <;> positivity
  have hsmall : R ≤ 7 * (n : ℝ) / 500000000 := higher_powers_in_class_linear q a n hn
  have hsum : (∑ k ∈ S, ArithmeticFunction.vonMangoldt k) = P + R := by
    dsimp only [P, R]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hk : k.Prime <;> simp [hk]
  rw [hsum, abs_le]
  constructor <;> linarith

end FixedAPPrimePowerError
