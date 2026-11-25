import Mathlib

open MeasureTheory Set

theorem PEqualNP.Outside.L_goldbach_mellin_autocorr_diagonal :
    let F := fun (φ : ℝ → ℝ) x => Real.exp (x/2)*φ (Real.exp x); let R := fun (f : ℝ → ℝ) h => ∫ x : ℝ, f x*f (x+h); ∀ φ : ℝ → ℝ, Continuous φ → (∀ u : ℝ, u < 1/3 ∨ 2/3 < u → φ u=0) → R (F φ) 0 = intervalIntegral (fun u : ℝ => (φ u)^2) 0 1 MeasureTheory.volume := by
  intro F R φ _ hsupport
  change (∫ x : ℝ, F φ x * F φ (x + 0)) = _
  calc
    _ = ∫ x : ℝ, Real.exp x • (φ (Real.exp x)) ^ 2 := by
      apply integral_congr_ae
      filter_upwards with x
      have hexp : Real.exp (x / 2) ^ 2 = Real.exp x := by
        rw [Real.exp_half, Real.sq_sqrt (Real.exp_pos x).le]
      simp only [add_zero, F, smul_eq_mul, ← hexp]
      ring
    _ = ∫ u in Ioi (0 : ℝ), (φ u) ^ 2 := integral_comp_exp (fun u => (φ u) ^ 2)
    _ = ∫ u in Ioc (0 : ℝ) 1, (φ u) ^ 2 := by
      apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      · exact fun _ hu => hu.1
      · intro u hu
        have hu₁ : 1 < u := lt_of_not_ge fun h => hu.2 ⟨hu.1, h⟩
        have hφ := hsupport u (Or.inr ((by norm_num : (2 : ℝ) / 3 < 1).trans hu₁))
        simp [hφ]
    _ = _ := (intervalIntegral.integral_of_le zero_le_one).symm
