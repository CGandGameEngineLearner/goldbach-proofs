import Mathlib

open scoped Classical

theorem Conjectures.Goldbach.MobiusComplementaryCutoffs :
  ∀ (n : ℕ) (t : ℝ), 1 < n → Squarefree n → let T := fun x : ℝ => n.divisors.sum (fun d => (ArithmeticFunction.moebius d : ℝ) * max (x - Real.log (d : ℝ)) 0); ArithmeticFunction.vonMangoldt n = T t - (ArithmeticFunction.moebius n : ℝ) * T (Real.log (n : ℝ) - t) := by
  intro n t hn hsq T
  let μ := fun d : ℕ => (ArithmeticFunction.moebius d : ℝ)
  have hzero : ∑ d ∈ n.divisors, μ d = 0 := by
    dsimp [μ]
    rw [← Int.cast_sum, ← ArithmeticFunction.coe_mul_zeta_apply,
      ArithmeticFunction.moebius_mul_coe_zeta, ArithmeticFunction.one_apply_ne (by omega)]
    simp
  have hlog : ∑ d ∈ n.divisors, μ d * Real.log d = -ArithmeticFunction.vonMangoldt n :=
    ArithmeticFunction.sum_moebius_mul_log_eq
  let f := fun d : ℕ => μ d * max (Real.log n - t - Real.log d) 0
  have hflip : μ n * T (Real.log n-t) =
      ∑ d ∈ n.divisors, μ d * max (Real.log d-t) 0 := by
    change μ n * n.divisors.sum f = _
    rw [← Nat.sum_div_divisors n f, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    have hdiv := Nat.dvd_of_mem_divisors hd
    have hprod := Nat.div_mul_cancel hdiv
    have hs := Nat.squarefree_mul_iff.mp (hprod.symm ▸ hsq)
    have hm : μ n = μ (n/d) * μ d := by
      dsimp [μ]
      exact_mod_cast (hprod ▸ ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hs.1)
    have hunit : μ (n/d)^2 = 1 := by
      dsimp [μ]
      exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hs.2.1
    have hpr : ((n/d : ℕ) : ℝ) * d = n := by exact_mod_cast hprod
    have ha : (n/d:ℕ) ≠ 0 := by intro e; simp [e] at hprod; omega
    have hb : d ≠ 0 := by intro e; simp [e] at hprod; omega
    have hl := Real.log_mul (Nat.cast_ne_zero.mpr ha : ((n/d:ℕ):ℝ) ≠ 0)
      (Nat.cast_ne_zero.mpr hb : (d:ℝ) ≠ 0)
    rw [hpr] at hl
    dsimp only [f]
    rw [show Real.log n - t - Real.log (n/d:ℕ) = Real.log d-t by linarith, hm]
    linear_combination (μ d * max (Real.log d - t) 0) * hunit
  change ArithmeticFunction.vonMangoldt n = T t - μ n * T (Real.log n - t)
  rw [hflip]
  change _ = (∑ d ∈ n.divisors, μ d * max (t-Real.log d) 0) - _
  rw [← Finset.sum_sub_distrib]
  have term (d : ℕ) : μ d * max (t-Real.log d) 0 - μ d * max (Real.log d-t) 0 =
      μ d*t - μ d*Real.log d := by
    by_cases h : Real.log d ≤ t
    · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring
    · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
  simp_rw [term]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hzero, hlog]
  ring
