import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SimpRw

open scoped BigOperators

theorem PEqualNP.Outside.L_goldbach_even_shift_phase_filter :
    let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); ∀ (H : ℕ) (t : ℝ), 0<H → Real.sin (2*Real.pi*t) ≠ 0 → ‖(∑ j ∈ Finset.range H, E (-2*(j:ℝ)*t))/(H:ℂ)‖ ≤ min 1 (1/((H:ℝ)*|Real.sin (2*Real.pi*t)|)) := by
  intro w E H t hH hsin
  let θ : ℝ := 2 * Real.pi * t
  let z : ℂ := Complex.exp (((-2 * θ : ℝ) : ℂ) * Complex.I)
  have hterm (j : ℕ) : E (-2 * (j : ℝ) * t) = z ^ j := by
    dsimp only [E, z, θ]
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hz : ‖z‖ = 1 := Complex.norm_exp_ofReal_mul_I (-2 * θ)
  have hchord : ‖z - 1‖ = 2 * |Real.sin θ| := by
    dsimp only [z]
    rw [mul_comm _ Complex.I, Complex.norm_exp_I_mul_ofReal_sub_one]
    have hhalf : (-2 * θ : ℝ) / 2 = -θ := by ring
    rw [hhalf, Real.sin_neg]
    simp [norm_mul, Real.norm_eq_abs]
  have htrivial : ‖∑ j ∈ Finset.range H, z ^ j‖ ≤ (H : ℝ) := by
    calc
      _ ≤ ∑ j ∈ Finset.range H, ‖z ^ j‖ := norm_sum_le _ _
      _ = (H : ℝ) := by simp [Complex.norm_pow, hz]
  have hproduct : ‖∑ j ∈ Finset.range H, z ^ j‖ * (2 * |Real.sin θ|) ≤ 2 := by
    calc
      _ = ‖(∑ j ∈ Finset.range H, z ^ j) * (z - 1)‖ := by
        rw [Complex.norm_mul, hchord]
      _ = ‖z ^ H - 1‖ := by rw [geom_sum_mul]
      _ ≤ ‖z ^ H‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by norm_num [Complex.norm_pow, hz]
  have hs : (0 : ℝ) < |Real.sin θ| := abs_pos.mpr hsin
  have hdecay : ‖∑ j ∈ Finset.range H, z ^ j‖ ≤ 1 / |Real.sin θ| := by
    apply (le_div_iff₀ hs).2
    nlinarith only [hproduct]
  have hHreal : (0 : ℝ) < (H : ℝ) := Nat.cast_pos.mpr hH
  simp_rw [hterm]
  rw [Complex.norm_div, Complex.norm_natCast]
  apply le_min
  · apply (div_le_iff₀ hHreal).2
    simpa only [one_mul] using htrivial
  · calc
      _ ≤ (1 / |Real.sin θ|) / (H : ℝ) :=
        div_le_div_of_nonneg_right hdecay hHreal.le
      _ = 1 / ((H : ℝ) * |Real.sin (2 * Real.pi * t)|) := by
        rw [div_div, mul_comm |Real.sin θ| (H : ℝ)]
