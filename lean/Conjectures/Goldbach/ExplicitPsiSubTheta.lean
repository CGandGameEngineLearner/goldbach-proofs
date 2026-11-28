import Mathlib.NumberTheory.Chebyshev
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

open Finset Real

private theorem psi_theta_bound (x : ℝ) (hx : 2 ≤ x) :
    0 ≤ Chebyshev.psi x - Chebyshev.theta x ∧
    Chebyshev.psi x - Chebyshev.theta x ≤
      Real.log 4 * Real.sqrt x + 2 * x ^ (1 / 3 : ℝ) * Real.log x := by
  refine ⟨sub_nonneg.mpr (Chebyshev.theta_le_psi x), ?_⟩
  let M := ⌊Real.log x / Real.log 2⌋₊
  have hx0 : 0 ≤ x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    calc
      Real.log 4 = Real.log ((2 : ℝ) * 2) := by norm_num
      _ = _ := by rw [Real.log_mul (by norm_num) (by norm_num)]; ring
  have hM : (M : ℝ) ≤ Real.log x / Real.log 2 :=
    Nat.floor_le (div_nonneg hlog hlog2.le)
  have hcard : ((Icc 3 M).card : ℝ) ≤ (M : ℝ) := by
    exact_mod_cast (show (Icc 3 M).card ≤ M by simp only [Nat.card_Icc]; omega)
  have hterm (n : ℕ) (hn : n ∈ Icc 3 M) :
      Chebyshev.theta (x ^ (1 / (n : ℝ))) ≤ Real.log 4 * x ^ (1 / 3 : ℝ) := by
    have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast (mem_Icc.mp hn).1
    have hexp : (1 : ℝ) / n ≤ 1 / 3 := by
      apply one_div_le_one_div_of_le (by norm_num) hn3
    exact (Chebyshev.theta_le_log4_mul_x (Real.rpow_nonneg hx0 _)).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx1 hexp)
        (Real.log_nonneg (by norm_num)))
  have htail : (∑ n ∈ Icc 3 M, Chebyshev.theta (x ^ (1 / (n : ℝ)))) ≤
      2 * x ^ (1 / 3 : ℝ) * Real.log x := by
    calc
      _ ≤ ∑ _n ∈ Icc 3 M, Real.log 4 * x ^ (1 / 3 : ℝ) :=
        Finset.sum_le_sum hterm
      _ = ((Icc 3 M).card : ℝ) * (Real.log 4 * x ^ (1 / 3 : ℝ)) := by simp
      _ ≤ (M : ℝ) * (Real.log 4 * x ^ (1 / 3 : ℝ)) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
      _ ≤ (Real.log x / Real.log 2) * (Real.log 4 * x ^ (1 / 3 : ℝ)) :=
        mul_le_mul_of_nonneg_right hM (by positivity)
      _ = _ := by rw [hlog4]; field_simp
  have hsub : Icc 2 M ⊆ insert 2 (Icc 3 M) := by
    intro n hn
    simp only [mem_Icc, mem_insert] at *
    omega
  have hsum : (∑ n ∈ Icc 2 M, Chebyshev.theta (x ^ (1 / (n : ℝ)))) ≤
      Chebyshev.theta (Real.sqrt x) +
        ∑ n ∈ Icc 3 M, Chebyshev.theta (x ^ (1 / (n : ℝ))) := by
    calc
      _ ≤ ∑ n ∈ insert 2 (Icc 3 M), Chebyshev.theta (x ^ (1 / (n : ℝ))) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun n _ _ => Chebyshev.theta_nonneg _)
      _ = _ := by rw [sum_insert (by simp)]; simp [Real.sqrt_eq_rpow]
  rw [Chebyshev.psi_eq_theta_add_sum_theta hx, add_sub_cancel_left]
  exact hsum.trans (add_le_add (Chebyshev.theta_le_log4_mul_x (Real.sqrt_nonneg x)) htail)

theorem Conjectures.Goldbach.ExplicitPsiSubTheta : (let ψ := fun x : ℝ => ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n; let θ := fun x : ℝ => ∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, Real.log (p : ℝ); ∀ x : ℝ, 2 ≤ x → 0 ≤ ψ x - θ x ∧ ψ x - θ x ≤ Real.log 4 * Real.sqrt x + 2 * x ^ (1 / 3 : ℝ) * Real.log x) := by
  dsimp only
  intro x hx
  have hinterval : Finset.Ioc 0 ⌊x⌋₊ = Finset.Icc 1 ⌊x⌋₊ := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  simpa only [Chebyshev.psi, Chebyshev.theta, hinterval] using psi_theta_bound x hx
