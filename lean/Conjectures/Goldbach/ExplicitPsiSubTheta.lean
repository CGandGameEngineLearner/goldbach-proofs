import Mathlib.NumberTheory.Chebyshev

namespace Conjectures.Goldbach.ExplicitPsiSubTheta_aux

open Finset

theorem psi_sum_eq_chebyshev (x : ℝ) :
    (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n) = Chebyshev.psi x := by
  have hIcc : Finset.Icc (1 : ℕ) ⌊x⌋₊ = Finset.Ioc 0 ⌊x⌋₊ := by
    simpa using Finset.Icc_succ_left_eq_Ioc (0 : ℕ) ⌊x⌋₊
  rw [Chebyshev.psi, hIcc]

theorem theta_sum_eq_chebyshev (x : ℝ) :
    (∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, Real.log (p : ℝ)) = Chebyshev.theta x := by
  have hIcc : Finset.Icc (1 : ℕ) ⌊x⌋₊ = Finset.Ioc 0 ⌊x⌋₊ := by
    simpa using Finset.Icc_succ_left_eq_Ioc (0 : ℕ) ⌊x⌋₊
  rw [Chebyshev.theta]
  simp only [Finset.sum_filter]
  rw [hIcc]

theorem bound {x : ℝ} (hx : 2 ≤ x) :
    0 ≤ Chebyshev.psi x - Chebyshev.theta x ∧
      Chebyshev.psi x - Chebyshev.theta x ≤
        Real.log 4 * Real.sqrt x + 2 * x ^ (1 / 3 : ℝ) * Real.log x := by
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2ne : Real.log 2 ≠ 0 := hlog2.ne'
  have hdiv : 0 ≤ Real.log x / Real.log 2 := div_nonneg hlog hlog2.le
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    ring
  set N : ℕ := ⌊Real.log x / Real.log 2⌋₊
  have hNle : (N : ℝ) ≤ Real.log x / Real.log 2 := Nat.floor_le hdiv
  have hdiff : Chebyshev.psi x - Chebyshev.theta x =
      ∑ n ∈ Finset.Icc 2 N, Chebyshev.theta (x ^ ((1 : ℝ) / n)) := by
    rw [Chebyshev.psi_eq_theta_add_sum_theta hx]
    ring
  have hsplit : (∑ n ∈ Finset.Icc 2 N, Chebyshev.theta (x ^ ((1 : ℝ) / n))) ≤
      Chebyshev.theta (x ^ ((1 : ℝ) / 2)) +
        ∑ n ∈ Finset.Icc 3 N, Chebyshev.theta (x ^ ((1 : ℝ) / n)) := by
    let f : ℕ → ℝ := fun n => Chebyshev.theta (x ^ ((1 : ℝ) / n))
    by_cases hN : 2 ≤ N
    · have h2 : Finset.Icc 3 N = Finset.Ioc 2 N := Finset.Icc_succ_left_eq_Ioc 2 N
      calc (∑ n ∈ Finset.Icc 2 N, Chebyshev.theta (x ^ ((1 : ℝ) / n)))
          = f 2 + ∑ n ∈ Finset.Ioc 2 N, f n :=
            (Finset.add_sum_Ioc_eq_sum_Icc (f := f) hN).symm
        _ = Chebyshev.theta (x ^ ((1 : ℝ) / 2)) +
              ∑ n ∈ Finset.Icc 3 N, Chebyshev.theta (x ^ ((1 : ℝ) / n)) := by
            rw [h2]
            norm_num [f]
        _ ≤ _ := le_rfl
    · have hempty : Finset.Icc 2 N = ∅ := Finset.Icc_eq_empty (by omega)
      rw [hempty, Finset.sum_empty]
      exact add_nonneg (Chebyshev.theta_nonneg _)
        (Finset.sum_nonneg fun _ _ => Chebyshev.theta_nonneg _)
  have hsq : Chebyshev.theta (x ^ ((1 : ℝ) / 2)) ≤ Real.log 4 * Real.sqrt x := by
    calc Chebyshev.theta (x ^ ((1 : ℝ) / 2))
        ≤ Real.log 4 * x ^ ((1 : ℝ) / 2) :=
          Chebyshev.theta_le_log4_mul_x (Real.rpow_nonneg hx0.le ((1 : ℝ) / 2))
      _ = Real.log 4 * Real.sqrt x := by rw [Real.sqrt_eq_rpow]
  have hhigh : (∑ n ∈ Finset.Icc 3 N, Chebyshev.theta (x ^ ((1 : ℝ) / n))) ≤
      (Real.log x / Real.log 2) * (Real.log 4 * x ^ (1 / 3 : ℝ)) := by
    have hterm : ∀ n ∈ Finset.Icc 3 N,
        Chebyshev.theta (x ^ ((1 : ℝ) / n)) ≤ Real.log 4 * x ^ (1 / 3 : ℝ) := by
      intro n hn
      have hn3 : (3 : ℕ) ≤ n := (Finset.mem_Icc.mp hn).1
      have hn3r : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn3
      have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
      have hexp : (1 : ℝ) / (n : ℝ) ≤ 1 / 3 := by
        rw [div_le_div_iff₀ hnpos (by norm_num)]
        linarith
      calc Chebyshev.theta (x ^ ((1 : ℝ) / n))
          ≤ Real.log 4 * x ^ ((1 : ℝ) / n) :=
            Chebyshev.theta_le_log4_mul_x (Real.rpow_nonneg hx0.le ((1 : ℝ) / (n : ℝ)))
        _ ≤ Real.log 4 * x ^ (1 / 3 : ℝ) := by
            gcongr
    have hcard : ((Finset.Icc 3 N).card : ℝ) ≤ Real.log x / Real.log 2 := by
      rw [Nat.card_Icc]
      have hc : ((N + 1 - 3 : ℕ) : ℝ) ≤ (N : ℝ) := by
        exact_mod_cast (by omega : N + 1 - 3 ≤ N)
      linarith
    calc (∑ n ∈ Finset.Icc 3 N, Chebyshev.theta (x ^ ((1 : ℝ) / n)))
        ≤ ∑ _n ∈ Finset.Icc 3 N, Real.log 4 * x ^ (1 / 3 : ℝ) :=
          Finset.sum_le_sum hterm
      _ = ((Finset.Icc 3 N).card : ℝ) * (Real.log 4 * x ^ (1 / 3 : ℝ)) := by
          simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (Real.log x / Real.log 2) * (Real.log 4 * x ^ (1 / 3 : ℝ)) := by
          gcongr
  have hmain : Chebyshev.psi x - Chebyshev.theta x ≤
      Real.log 4 * Real.sqrt x + 2 * x ^ (1 / 3 : ℝ) * Real.log x := by
    calc Chebyshev.psi x - Chebyshev.theta x
        = ∑ n ∈ Finset.Icc 2 N, Chebyshev.theta (x ^ ((1 : ℝ) / n)) := hdiff
      _ ≤ Chebyshev.theta (x ^ ((1 : ℝ) / 2)) +
            ∑ n ∈ Finset.Icc 3 N, Chebyshev.theta (x ^ ((1 : ℝ) / n)) := hsplit
      _ ≤ Real.log 4 * Real.sqrt x +
            (Real.log x / Real.log 2) * (Real.log 4 * x ^ (1 / 3 : ℝ)) := by
          gcongr
      _ = Real.log 4 * Real.sqrt x + 2 * x ^ (1 / 3 : ℝ) * Real.log x := by
          rw [hlog4]
          field_simp
  exact ⟨sub_nonneg.mpr (Chebyshev.theta_le_psi x), hmain⟩

end Conjectures.Goldbach.ExplicitPsiSubTheta_aux

theorem Conjectures.Goldbach.ExplicitPsiSubTheta :
    let ψ := fun x : ℝ => ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n; let θ := fun x : ℝ => ∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, Real.log (p : ℝ); ∀ x : ℝ, 2 ≤ x → 0 ≤ ψ x - θ x ∧ ψ x - θ x ≤ Real.log 4 * Real.sqrt x + 2 * x ^ (1 / 3 : ℝ) * Real.log x := by
  dsimp only
  intro x hx
  rw [Conjectures.Goldbach.ExplicitPsiSubTheta_aux.psi_sum_eq_chebyshev,
    Conjectures.Goldbach.ExplicitPsiSubTheta_aux.theta_sum_eq_chebyshev]
  exact Conjectures.Goldbach.ExplicitPsiSubTheta_aux.bound hx
