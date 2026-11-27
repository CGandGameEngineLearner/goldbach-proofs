import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic

/-!
# Constants in Pintz's weighted zero-density inequalities

For the simultaneous binary-shift exception problem, Pintz's Corollary 1
uses the factor from (4.3) with the parameters of §5. The functions below
specialize (4.5) to φ = 1/3, κ = 1/6, r = 2/3. They give uniform strict
budgets with room for a relative error of one part per million.

Source: J. Pintz, https://arxiv.org/abs/1804.09084, §4, Corollary 1.
-/
namespace PintzWeightedDensity

noncomputable def kernel (a y : ℝ) : ℝ := (1 - Real.exp (-a * y)) / y

noncomputable def B (w y : ℝ) : ℝ := kernel (2*w) y / 6 + (kernel w y)^2

noncomputable def factor (y : ℝ) : ℝ := 156 * Real.sqrt (B (1/6) y * B (2/3) y)

theorem kernel_nonneg {a y : ℝ} (ha : 0 ≤ a) (hy : 0 < y) : 0 ≤ kernel a y := by
  apply div_nonneg _ hy.le
  exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by nlinarith))

theorem kernel_antitone {a x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    kernel a y ≤ kernel a x := by
  have hy : 0 < y := hx.trans_le hxy
  have h := convexOn_exp.2 (Set.mem_univ (-a*y)) (Set.mem_univ 0)
    (div_nonneg hx.le hy.le) (sub_nonneg.mpr ((div_le_one hy).2 hxy))
    (show x/y + (1-x/y) = 1 by ring)
  simp only [smul_eq_mul, mul_zero, add_zero, Real.exp_zero, mul_one] at h
  rw [show x/y * (-a*y) = -a*x by field_simp] at h
  dsimp [kernel]
  apply (div_le_div_iff₀ hy hx).2
  field_simp [hy.ne'] at h
  simp only [neg_mul] at *
  linarith

theorem B_nonneg {w y : ℝ} (hw : 0 ≤ w) (hy : 0 < y) : 0 ≤ B w y := by
  unfold B
  have := kernel_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hw) hy
  positivity

theorem B_antitone {w x y : ℝ} (hw : 0 ≤ w) (hx : 0 < x) (hxy : x ≤ y) :
    B w y ≤ B w x := by
  unfold B
  have hy := hx.trans_le hxy
  exact add_le_add (by gcongr; exact kernel_antitone hx hxy)
    (pow_le_pow_left₀ (kernel_nonneg hw hy) (kernel_antitone hx hxy) _)

theorem factor_antitone {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) : factor y ≤ factor x := by
  unfold factor
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.sqrt_le_sqrt
  exact mul_le_mul (B_antitone (by norm_num) hx hxy) (B_antitone (by norm_num) hx hxy)
    (B_nonneg (by norm_num) (hx.trans_le hxy)) (B_nonneg (by norm_num) hx)

private theorem certificate {y E : ℝ} (hE : 0 < E)
    (h : (156 * (1 + 1/1000000 : ℝ))^2 * (B (1/6) y * B (2/3) y) < E^2) :
    (1 + 1/1000000 : ℝ) * factor y < E := by
  have hroot := Real.sq_sqrt (x := B (1/6) y * B (2/3) y)
  by_cases h0 : 0 ≤ B (1/6) y * B (2/3) y
  · specialize hroot h0
    unfold factor
    by_contra! hle
    have hh := mul_self_le_mul_self hE.le hle
    nlinarith only [h, hroot, hh]
  · unfold factor
    rw [Real.sqrt_eq_zero_of_nonpos (le_of_not_ge h0), mul_zero, mul_zero]
    exact hE

set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

private noncomputable def numerator (y u v : ℝ) : ℝ := y * (1-u) + 6 * (1-v)^2

private theorem cleared {y E : ℝ} (hy : 0 < y) (hE : 0 < E)
    (h : (156.000156 : ℝ)^2 *
      numerator y (Real.exp (-(2*(1/6))*y)) (Real.exp (-(1/6)*y)) *
      numerator y (Real.exp (-(2*(2/3))*y)) (Real.exp (-(2/3)*y)) <
      E^2 * (6*y^2)^2) : (1 + 1/1000000 : ℝ) * factor y < E := by
  apply certificate hE
  apply (mul_lt_mul_iff_left₀ (show 0 < (6*y^2)^2 by positivity)).mp
  convert h using 1
  unfold B kernel numerator
  norm_num1
  field_simp

theorem at_first : (1 + 1/1000000 : ℝ) * factor 1.311 < 22.281 := by
  apply cleared (by norm_num) (by norm_num)
  unfold numerator
  rw [show -(2*(1/6))*(1.311 : ℝ) = -0.437 by norm_num]
  rw [show -(1/6)*(1.311 : ℝ) = -0.2185 by norm_num]
  rw [show -(2*(2/3))*(1.311 : ℝ) = -1.748 by norm_num]
  rw [show -(2/3)*(1.311 : ℝ) = -0.874 by norm_num]
  dyadic_interval [prec := 36]

theorem at_second : (1 + 1/1000000 : ℝ) * factor 2.421 < 15.6 := by
  apply cleared (by norm_num) (by norm_num)
  unfold numerator
  rw [show -(2*(1/6))*(2.421 : ℝ) = -0.807 by norm_num]
  rw [show -(1/6)*(2.421 : ℝ) = -0.4035 by norm_num]
  rw [show -(2*(2/3))*(2.421 : ℝ) = -3.228 by norm_num]
  rw [show -(2/3)*(2.421 : ℝ) = -1.614 by norm_num]
  dyadic_interval [prec := 36]

theorem at_third : (1 + 1/1000000 : ℝ) * factor 3.96 < 10.4 := by
  apply cleared (by norm_num) (by norm_num)
  unfold numerator
  rw [show -(2*(1/6))*(3.96 : ℝ) = -1.32 by norm_num]
  rw [show -(1/6)*(3.96 : ℝ) = -0.66 by norm_num]
  rw [show -(2*(2/3))*(3.96 : ℝ) = -5.28 by norm_num]
  rw [show -(2/3)*(3.96 : ℝ) = -2.64 by norm_num]
  dyadic_interval [prec := 36]

/-- All three cutoff bounds persist on their respective half-lines. -/
theorem budgets (y : ℝ) :
    (1.311 ≤ y → (1 + 1/1000000 : ℝ) * factor y < 22.281) ∧
    (2.421 ≤ y → (1 + 1/1000000 : ℝ) * factor y < 15.6) ∧
    (3.96 ≤ y → (1 + 1/1000000 : ℝ) * factor y < 10.4) := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  all_goals
    apply lt_of_le_of_lt (mul_le_mul_of_nonneg_left (factor_antitone (by norm_num) h)
      (by norm_num))
  exacts [at_first, at_second, at_third]

/-- The truncated exponential moment controls the number of zeros up to the
cutoff, with multiplicity represented by distinct indices of the finite family.
This is the passage from (4.8)–(4.9) to (4.10)–(4.11). -/
theorem count_of_moment {ι : Type*} (Z : Finset ι) (l : ι → ℝ)
    {a b y E : ℝ} (hba : b ≤ a)
    (h : ∑ j ∈ Z, Real.exp (-a*l j - b*max 0 (y-l j)) < E) :
    (((Z.filter (fun j => l j ≤ y)).card : ℝ)) < E * Real.exp (a*y) := by
  classical
  let T := Z.filter (fun j => l j ≤ y)
  have hsum : (T.card : ℝ) * Real.exp (-(a*y)) < E := calc
    _ = ∑ _j ∈ T, Real.exp (-(a*y)) := by simp
    _ ≤ ∑ j ∈ T, Real.exp (-a*l j - b*max 0 (y-l j)) := by
      apply Finset.sum_le_sum
      intro j hj
      have hjy := (Finset.mem_filter.mp hj).2
      rw [max_eq_right (sub_nonneg.mpr hjy)]
      exact Real.exp_le_exp.mpr (by nlinarith [mul_nonneg (sub_nonneg.mpr hba) (sub_nonneg.mpr hjy)])
    _ ≤ ∑ j ∈ Z, Real.exp (-a*l j - b*max 0 (y-l j)) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => (Real.exp_pos _).le)
    _ < E := h
  rw [Real.exp_neg, ← div_eq_mul_inv] at hsum
  exact (div_lt_iff₀ (Real.exp_pos _)).mp hsum

/-- At the third cutoff, the damping disappears on the upper tail. Applied to
the whole family with a = 8/3 and to a conductor class with a = 2, this is
the pair of moment estimates in (9.32). -/
theorem upper_tail {ι : Type*} (Z : Finset ι) (l : ι → ℝ) {a y δ : ℝ}
    (hy : 3.96 ≤ y) (hδ : δ ≤ 1/1000000)
    (h : ∑ j ∈ Z, Real.exp (-a*l j - (5/12)*max 0 (y-l j)) ≤ (1+δ)*factor y) :
    ∑ j ∈ Z.filter (fun j => y ≤ l j), Real.exp (-a*l j) < 10.4 := by
  classical
  let T := Z.filter (fun j => y ≤ l j)
  calc
    _ = ∑ j ∈ T, Real.exp (-a*l j - (5/12)*max 0 (y-l j)) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjy := (Finset.mem_filter.mp hj).2
      rw [max_eq_left (sub_nonpos.mpr hjy), mul_zero, sub_zero]
    _ ≤ ∑ j ∈ Z, Real.exp (-a*l j - (5/12)*max 0 (y-l j)) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => (Real.exp_pos _).le)
    _ ≤ (1+δ)*factor y := h
    _ ≤ (1+1/1000000)*factor y :=
      mul_le_mul_of_nonneg_right (add_le_add_right hδ 1) (by unfold factor; positivity)
    _ < 10.4 := (budgets y).2.2 hy

end PintzWeightedDensity
