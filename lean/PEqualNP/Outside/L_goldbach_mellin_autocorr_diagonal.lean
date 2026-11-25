import Mathlib

open MeasureTheory Set

theorem PEqualNP.Outside.L_goldbach_mellin_autocorr_diagonal :
    let F := fun (φ : ℝ → ℝ) x => Real.exp (x/2)*φ (Real.exp x); let R := fun (f : ℝ → ℝ) h => ∫ x : ℝ, f x*f (x+h); ∀ φ : ℝ → ℝ, Continuous φ → (∀ u : ℝ, u < 1/3 ∨ 2/3 < u → φ u=0) → R (F φ) 0 = intervalIntegral (fun u : ℝ => (φ u)^2) 0 1 MeasureTheory.volume := by
  dsimp only
  intro φ _ hsupport
  rw [intervalIntegral.integral_of_le zero_le_one]
  have htrim (s : Set ℝ) (hs : Ioc (0 : ℝ) 1 ⊆ s) :
      (∫ u in s, (φ u) ^ 2) = ∫ u : ℝ, (φ u) ^ 2 := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro u hu
    have hout : ¬ (0 < u ∧ u ≤ 1) := fun h => hu (hs h)
    have hφ : φ u = 0 := by
      apply hsupport
      by_cases hpos : 0 < u
      · right
        have hgt : 1 < u := lt_of_not_ge (fun hle => hout ⟨hpos, hle⟩)
        linarith
      · left
        have hle := le_of_not_gt hpos
        linarith
    rw [hφ, zero_pow (by decide)]
  calc
    _ = ∫ x : ℝ, Real.exp x • (φ (Real.exp x)) ^ 2 := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [add_zero, smul_eq_mul, sq,
        show Real.exp x = Real.exp (x / 2) * Real.exp (x / 2) by
          rw [← Real.exp_add, add_halves]]
      ring
    _ = ∫ u in Ioi (0 : ℝ), (φ u) ^ 2 := integral_comp_exp (fun u => (φ u) ^ 2)
    _ = ∫ u in Ioc (0 : ℝ) 1, (φ u) ^ 2 := by
      rw [htrim _ (fun _ hu => hu.1), htrim _ (fun _ hu => hu)]
