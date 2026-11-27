import Mathlib

open MeasureTheory

namespace Conjectures.Goldbach.PacketDoublingTilt_aux

lemma cos_pi_mul_add_one (x : ℝ) :
    Real.cos (Real.pi * (x + 1)) = -Real.cos (Real.pi * x) := by
  have h1 : Real.pi * (x + 1) = Real.pi * x + Real.pi := by ring
  rw [h1, Real.cos_add_pi]

lemma abs_mul_cos_le (s x : ℝ) : |s * Real.cos (Real.pi * x)| ≤ |s| := by
  rw [abs_mul]
  calc |s| * |Real.cos (Real.pi * x)| ≤ |s| * 1 :=
        mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg s)
    _ = |s| := mul_one _

end Conjectures.Goldbach.PacketDoublingTilt_aux

open Conjectures.Goldbach.PacketDoublingTilt_aux

theorem Conjectures.Goldbach.PacketDoublingTilt : ∀ (s : ℝ) (g : ℝ → ℝ), Continuous g → Function.Periodic g 1 → (∀ t, 0 ≤ g t) → intervalIntegral (fun t => Real.exp (s*Real.cos (2*Real.pi*t))*g (2*t)) (0:ℝ) 1 MeasureTheory.volume ≤ Real.cosh s * intervalIntegral (g) (0:ℝ) 1 MeasureTheory.volume := by
  intro s g hg hper hnonneg
  have hpi : Continuous (fun x : ℝ => Real.pi * x) := continuous_const.mul continuous_id
  have hcos : Continuous (fun x : ℝ => Real.cos (Real.pi * x)) := Real.continuous_cos.comp hpi
  have hFcont : Continuous (fun x : ℝ => Real.exp (s * Real.cos (Real.pi * x)) * g x) :=
    (Real.continuous_exp.comp (continuous_const.mul hcos)).mul hg
  have hF2cont : Continuous (fun x : ℝ => Real.exp (-(s * Real.cos (Real.pi * x))) * g x) :=
    (Real.continuous_exp.comp (continuous_neg.comp (continuous_const.mul hcos))).mul hg
  have hCcont : Continuous (fun x : ℝ => Real.cosh (s * Real.cos (Real.pi * x)) * g x) :=
    (Real.continuous_cosh.comp (continuous_const.mul hcos)).mul hg
  have hDcont : Continuous (fun x : ℝ => Real.cosh s * g x) := continuous_const.mul hg
  -- pointwise: the shifted branch flips the sign of the cosine and uses periodicity of g
  have hpt : ∀ x : ℝ, Real.exp (s * Real.cos (Real.pi * (x + 1))) * g (x + 1)
      = Real.exp (-(s * Real.cos (Real.pi * x))) * g x := by
    intro x
    rw [cos_pi_mul_add_one x, hper x, mul_neg]
  -- the second half of the doubled interval
  have hshift : intervalIntegral (fun x : ℝ => Real.exp (s * Real.cos (Real.pi * x)) * g x) 1 2
      MeasureTheory.volume
      = intervalIntegral (fun x : ℝ => Real.exp (-(s * Real.cos (Real.pi * x))) * g x) 0 1
        MeasureTheory.volume := by
    have hcomp := intervalIntegral.integral_comp_add_right
      (f := fun x : ℝ => Real.exp (s * Real.cos (Real.pi * x)) * g x) (a := (0 : ℝ)) (b := 1)
      (d := (1 : ℝ))
    rw [show (0 : ℝ) + 1 = 1 by norm_num, show (1 : ℝ) + 1 = 2 by norm_num] at hcomp
    calc intervalIntegral (fun x : ℝ => Real.exp (s * Real.cos (Real.pi * x)) * g x) 1 2
          MeasureTheory.volume
        = intervalIntegral (fun x : ℝ => Real.exp (s * Real.cos (Real.pi * (x + 1))) * g (x + 1)) 0 1
          MeasureTheory.volume := hcomp.symm
      _ = intervalIntegral (fun x : ℝ => Real.exp (-(s * Real.cos (Real.pi * x))) * g x) 0 1
          MeasureTheory.volume := by
          apply intervalIntegral.integral_congr
          intro x _
          exact hpt x
  -- doubling substitution and splitting
  have hA : intervalIntegral (fun t => Real.exp (s * Real.cos (2 * Real.pi * t)) * g (2 * t)) 0 1
      MeasureTheory.volume
      = (1 / 2 : ℝ) *
        (intervalIntegral (fun x : ℝ => Real.exp (s * Real.cos (Real.pi * x)) * g x) 0 1
            MeasureTheory.volume
          + intervalIntegral (fun x : ℝ => Real.exp (-(s * Real.cos (Real.pi * x))) * g x) 0 1
            MeasureTheory.volume) := by
    have hconv : (fun t : ℝ => Real.exp (s * Real.cos (2 * Real.pi * t)) * g (2 * t))
        = (fun t : ℝ => Real.exp (s * Real.cos (Real.pi * (2 * t))) * g (2 * t)) := by
      funext t
      have h2 : Real.pi * (2 * t) = 2 * Real.pi * t := by ring
      rw [← h2]
    rw [hconv]
    have key : intervalIntegral (fun t : ℝ => Real.exp (s * Real.cos (Real.pi * (2 * t))) * g (2 * t))
        0 1 MeasureTheory.volume
        = ((2 : ℝ)⁻¹) * intervalIntegral (fun x : ℝ => Real.exp (s * Real.cos (Real.pi * x)) * g x)
            ((2 : ℝ) * 0) ((2 : ℝ) * 1) MeasureTheory.volume := by
      have h := intervalIntegral.integral_comp_mul_left
        (f := fun x : ℝ => Real.exp (s * Real.cos (Real.pi * x)) * g x) (a := (0 : ℝ)) (b := 1)
        (c := (2 : ℝ)) (by norm_num : (2 : ℝ) ≠ 0)
      simpa only [smul_eq_mul] using h
    rw [key]
    rw [show (2 : ℝ) * 0 = 0 by norm_num, show (2 : ℝ) * 1 = 2 by norm_num,
      show ((2 : ℝ)⁻¹) = (1 / 2 : ℝ) by norm_num]
    have hsplit : intervalIntegral (fun x : ℝ => Real.exp (s * Real.cos (Real.pi * x)) * g x) 0 2
        MeasureTheory.volume
        = intervalIntegral (fun x : ℝ => Real.exp (s * Real.cos (Real.pi * x)) * g x) 0 1
            MeasureTheory.volume
          + intervalIntegral (fun x : ℝ => Real.exp (s * Real.cos (Real.pi * x)) * g x) 1 2
            MeasureTheory.volume :=
      (intervalIntegral.integral_add_adjacent_intervals
        (f := fun x : ℝ => Real.exp (s * Real.cos (Real.pi * x)) * g x) (a := (0 : ℝ)) (b := 1)
        (c := 2) (μ := MeasureTheory.volume) (hFcont.intervalIntegrable 0 1)
        (hFcont.intervalIntegrable 1 2)).symm
    rw [hsplit, hshift]
  -- merging the two branches into a cosh
  have hadd : intervalIntegral (fun x : ℝ => Real.exp (s * Real.cos (Real.pi * x)) * g x) 0 1
      MeasureTheory.volume
      + intervalIntegral (fun x : ℝ => Real.exp (-(s * Real.cos (Real.pi * x))) * g x) 0 1
        MeasureTheory.volume
      = intervalIntegral (fun x : ℝ => Real.exp (s * Real.cos (Real.pi * x)) * g x
          + Real.exp (-(s * Real.cos (Real.pi * x))) * g x) 0 1 MeasureTheory.volume :=
    (intervalIntegral.integral_add
      (f := fun x : ℝ => Real.exp (s * Real.cos (Real.pi * x)) * g x)
      (g := fun x : ℝ => Real.exp (-(s * Real.cos (Real.pi * x))) * g x) (a := (0 : ℝ)) (b := 1)
      (μ := MeasureTheory.volume) (hFcont.intervalIntegrable 0 1)
      (hF2cont.intervalIntegrable 0 1)).symm
  have hmul : (1 / 2 : ℝ) * intervalIntegral (fun x : ℝ =>
        Real.exp (s * Real.cos (Real.pi * x)) * g x
          + Real.exp (-(s * Real.cos (Real.pi * x))) * g x) 0 1 MeasureTheory.volume
      = intervalIntegral (fun x : ℝ => (1 / 2 : ℝ) *
          (Real.exp (s * Real.cos (Real.pi * x)) * g x
            + Real.exp (-(s * Real.cos (Real.pi * x))) * g x)) 0 1 MeasureTheory.volume :=
    (intervalIntegral.integral_const_mul (1 / 2 : ℝ) (fun x : ℝ =>
      Real.exp (s * Real.cos (Real.pi * x)) * g x
        + Real.exp (-(s * Real.cos (Real.pi * x))) * g x)).symm
  have hcosh : intervalIntegral (fun x : ℝ => (1 / 2 : ℝ) *
        (Real.exp (s * Real.cos (Real.pi * x)) * g x
          + Real.exp (-(s * Real.cos (Real.pi * x))) * g x)) 0 1 MeasureTheory.volume
      = intervalIntegral (fun x : ℝ => Real.cosh (s * Real.cos (Real.pi * x)) * g x) 0 1
        MeasureTheory.volume := by
    apply intervalIntegral.integral_congr
    intro x _
    show (1 / 2 : ℝ) * (Real.exp (s * Real.cos (Real.pi * x)) * g x
        + Real.exp (-(s * Real.cos (Real.pi * x))) * g x)
      = Real.cosh (s * Real.cos (Real.pi * x)) * g x
    rw [Real.cosh_eq]
    ring
  have hmain : intervalIntegral (fun t => Real.exp (s * Real.cos (2 * Real.pi * t)) * g (2 * t)) 0 1
      MeasureTheory.volume
      = intervalIntegral (fun x : ℝ => Real.cosh (s * Real.cos (Real.pi * x)) * g x) 0 1
        MeasureTheory.volume := by
    rw [hA, hadd, hmul, hcosh]
  have hstep2 : intervalIntegral (fun x : ℝ => Real.cosh (s * Real.cos (Real.pi * x)) * g x) 0 1
      MeasureTheory.volume
      ≤ intervalIntegral (fun x : ℝ => Real.cosh s * g x) 0 1 MeasureTheory.volume := by
    refine intervalIntegral.integral_mono
      (f := fun x : ℝ => Real.cosh (s * Real.cos (Real.pi * x)) * g x)
      (g := fun x : ℝ => Real.cosh s * g x) (a := (0 : ℝ)) (b := 1)
      (μ := MeasureTheory.volume) (by norm_num : (0 : ℝ) ≤ 1) (hCcont.intervalIntegrable 0 1)
      (hDcont.intervalIntegrable 0 1) ?_
    exact fun x => mul_le_mul_of_nonneg_right
      (Real.cosh_le_cosh.mpr (abs_mul_cos_le s x)) (hnonneg x)
  have hstep3 : intervalIntegral (fun x : ℝ => Real.cosh s * g x) 0 1 MeasureTheory.volume
      = Real.cosh s * intervalIntegral (g) (0 : ℝ) 1 MeasureTheory.volume :=
    intervalIntegral.integral_const_mul (Real.cosh s) g
  exact hmain.le.trans (hstep2.trans_eq hstep3)
