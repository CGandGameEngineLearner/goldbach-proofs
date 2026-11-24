import Mathlib

theorem PEqualNP.Outside.L_goldbach_integrated_loss :
    ∀ (f g : ℝ → ℝ) (a b D : ℝ), a≤b → Continuous f → Continuous g → (∀ t∈Set.Icc a b, g t-D≤f t) → intervalIntegral g a b MeasureTheory.volume-(b-a)*D ≤ intervalIntegral f a b MeasureTheory.volume := by
  intro f g a b D hab hf hg hle
  have hgi : IntervalIntegrable g MeasureTheory.volume a b := hg.intervalIntegrable a b
  have hfi : IntervalIntegrable f MeasureTheory.volume a b := hf.intervalIntegrable a b
  have hsub : IntervalIntegrable (fun t : ℝ => g t - D) MeasureTheory.volume a b :=
    IntervalIntegrable.sub hgi intervalIntegrable_const
  have hmono : (∫ t in a..b, (g t - D)) ≤ ∫ t in a..b, f t :=
    intervalIntegral.integral_mono_on hab hsub hfi hle
  have hsplit : (∫ t in a..b, (g t - D)) = (∫ t in a..b, g t) - (b-a)*D := by
    rw [intervalIntegral.integral_sub hgi intervalIntegrable_const, intervalIntegral.integral_const]
    simp [smul_eq_mul]
  rw [hsplit] at hmono
  linarith
