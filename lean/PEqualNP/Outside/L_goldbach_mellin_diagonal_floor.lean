import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

theorem L_goldbach_mellin_diagonal_floor : let Adm := fun φ : ℝ → ℝ => (∀ j : ℕ, ContDiff ℝ j φ) ∧ (∀ u, 0≤φ u ∧ φ u≤1) ∧ (∀ u, φ (1-u)=φ u) ∧ (∀ u, u < 1/3 ∨ 2/3 < u → φ u=0) ∧ (∀ u, 5/12≤u → u≤7/12 → φ u=1); ∀ φ : ℝ → ℝ, Adm φ → 1/6 ≤ intervalIntegral (fun u : ℝ => (φ u)^2) 0 1 MeasureTheory.volume := by
  dsimp only
  intro φ hφ
  have hc : Continuous (fun u : ℝ => (φ u)^2) := (hφ.1 0).continuous.pow 2
  have hl : (0 : ℝ) ≤ 5/12 := by norm_num
  have hm : (5/12 : ℝ) ≤ 7/12 := by norm_num
  have hr : (7/12 : ℝ) ≤ 1 := by norm_num
  have hmid :
      intervalIntegral (fun u : ℝ => (φ u)^2) (5/12) (7/12) MeasureTheory.volume =
        (1/6 : ℝ) := by
    calc
      _ = intervalIntegral (fun _ : ℝ => (1 : ℝ)) (5/12) (7/12) MeasureTheory.volume := by
        apply intervalIntegral.integral_congr
        intro u hu
        rw [Set.uIcc_of_le hm] at hu
        change (φ u)^2 = 1
        rw [hφ.2.2.2.2 u hu.1 hu.2]
        norm_num
      _ = _ := by norm_num [intervalIntegral.integral_const]
  have hleft := intervalIntegral.integral_nonneg_of_forall
    (μ := MeasureTheory.volume) hl (fun u => sq_nonneg (φ u))
  have hright := intervalIntegral.integral_nonneg_of_forall
    (μ := MeasureTheory.volume) hr (fun u => sq_nonneg (φ u))
  have h₁ := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0 (5/12)) (hc.intervalIntegrable (5/12) (7/12))
  have h₂ := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0 (7/12)) (hc.intervalIntegrable (7/12) 1)
  linarith
