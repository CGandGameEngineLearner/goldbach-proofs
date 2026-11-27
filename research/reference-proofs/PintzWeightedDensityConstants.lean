import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
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

private theorem sinh_ratio_mono {w x y : ℝ} (hw : 0 ≤ w) (hx : 0 < x) (hxy : x ≤ y) :
    Real.sinh (w*x) / x ≤ Real.sinh (w*y) / y := by
  have hy := hx.trans_le hxy
  have hc : ConvexOn ℝ (Set.Ici 0) Real.sinh := by
    apply convexOn_of_deriv2_nonneg' (convex_Ici _) Real.differentiable_sinh.differentiableOn
    · rw [Real.deriv_sinh]
      exact Real.differentiable_cosh.differentiableOn
    · intro t ht
      simpa [Function.iterate_succ_apply', Real.deriv_sinh, Real.deriv_cosh] using
        (Real.sinh_nonneg_iff.mpr ht)
  have h := hc.2 (show w*y ∈ Set.Ici 0 from mul_nonneg hw hy.le)
    (show (0:ℝ) ∈ Set.Ici 0 from Set.self_mem_Ici) (div_nonneg hx.le hy.le)
    (sub_nonneg.mpr ((div_le_one hy).2 hxy)) (show x/y+(1-x/y)=1 by ring)
  simp only [smul_eq_mul, mul_zero, add_zero, Real.sinh_zero] at h
  rw [show x/y*(w*y) = w*x by field_simp] at h
  apply (div_le_div_iff₀ hx hy).2
  field_simp [hy.ne'] at h
  linarith

private theorem tilted_B (w x : ℝ) (hx : 0 < x) :
    Real.exp (w*x) * B w x =
      (2 * (Real.sinh (w*x) / x)) / 6 + (2 * (Real.sinh ((w/2)*x) / x))^2 := by
  have h1 : Real.exp (w*x) = Real.exp ((w/2)*x)^2 := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  have h2 : Real.exp ((2*w)*x) = Real.exp (w*x)^2 := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  simp only [B, kernel, neg_mul, Real.exp_neg, Real.sinh_eq, h2, h1]
  field_simp [hx.ne', Real.exp_ne_zero]

/-- Damping the row estimate at a zero below the cutoff moves the bound
to the common cutoff. This also covers zeros above it, as in (5.32)–(5.34). -/
theorem damped_B_le_at_cutoff {w x y : ℝ} (hw : 0 ≤ w) (hx : 0 < x) (hy : 0 < y) :
    Real.exp (-w * max 0 (y-x)) * B w x ≤ B w y := by
  by_cases hxy : x ≤ y
  · have hm : Real.exp (w*x) * B w x ≤ Real.exp (w*y) * B w y := by
      rw [tilted_B w x hx, tilted_B w y hy]
      have h₁ := sinh_ratio_mono hw hx hxy
      have h₂ := sinh_ratio_mono (show 0 ≤ w/2 by positivity) hx hxy
      have hs : 0 ≤ Real.sinh (w/2*x) := Real.sinh_nonneg_iff.mpr (by positivity)
      gcongr
    apply (mul_le_mul_iff_right₀ (Real.exp_pos (w*y))).mp
    rw [max_eq_right (sub_nonneg.mpr hxy), ← mul_assoc, ← Real.exp_add,
      show w*y + -w*(y-x) = w*x by ring]
    exact hm
  · simpa only [max_eq_left (sub_nonpos.mpr (le_of_not_ge hxy)), mul_zero, Real.exp_zero,
      one_mul] using (show B w x ≤ B w y from B_antitone hw hy (le_of_not_ge hxy))

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


/-- Symmetry allows the two factors at different zeros to be replaced by a
square at one zero, even if several indices represent the same zero. -/
private theorem symmetric_pair_sum {ι : Type*} (Z : Finset ι) (u : ι → ℝ)
    (K : ι → ι → ℝ) (hK : ∀ i j, 0 ≤ K i j) (hsym : ∀ i j, K i j = K j i) :
    ∑ i ∈ Z, ∑ j ∈ Z, u i * u j * K i j ≤
      ∑ i ∈ Z, u i ^ 2 * ∑ j ∈ Z, K i j := by
  have cross : (∑ i ∈ Z, ∑ j ∈ Z, u j^2 * K i j) =
      ∑ i ∈ Z, ∑ j ∈ Z, u i^2 * K i j := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl
      (fun j _ => by rw [hsym j i]))
  have am : (∑ i ∈ Z, ∑ j ∈ Z, 2 * (u i * u j * K i j)) ≤
      ∑ i ∈ Z, ∑ j ∈ Z, (u i^2 * K i j + u j^2 * K i j) := by
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    nlinarith [mul_nonneg (sq_nonneg (u i - u j)) (hK i j)]
  simp only [← Finset.mul_sum, Finset.sum_add_distrib] at am
  simp only [← Finset.mul_sum] at cross
  rw [cross] at am
  linarith

private theorem damped_row {w x y err row : ℝ} (hw : 0 ≤ w) (hx : 0 < x)
    (hy : 0 < y) (herr : 0 ≤ err) (hrow : row ≤ B w x + err) :
    Real.exp (-w * max 0 (y-x)) * row ≤ B w y + err := by
  have hD := Real.exp_le_one_iff.mpr
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hw) (le_max_left 0 (y-x)))
  calc
    _ ≤ Real.exp (-w * max 0 (y-x)) * (B w x + err) :=
      mul_le_mul_of_nonneg_left hrow (Real.exp_pos _).le
    _ ≤ _ := by
      rw [mul_add]
      exact add_le_add (damped_B_le_at_cutoff hw hx hy)
        (by simpa using mul_le_mul_of_nonneg_right hD herr)

noncomputable def deficit (y x : ℝ) : ℝ := max 0 (y-x)

noncomputable def pairWeight (t y x : ℝ) : ℝ :=
  Real.exp (-t*x - (5/12)*deficit y x)

noncomputable def zeroWeight (t y x : ℝ) : ℝ :=
  Real.exp (-2*t*x - (5/12)*deficit y x)

/-- Equations (5.29)–(5.36) for the parameters of Corollary 1. The kernels
may vanish outside any symmetric set of nearby pairs of zeros. The row error
and the constant in the quadratic density estimate are explicit. -/
theorem density_of_row_bounds {ι : Type*} (Z : Finset ι) (l : ι → ℝ)
    (K R : ι → ι → ℝ) {t y err c : ℝ} (hy : 0 < y) (herr : 0 ≤ err) (hc : 0 ≤ c)
    (hl : ∀ i ∈ Z, 0 < l i) (hK : ∀ i j, 0 ≤ K i j) (hR : ∀ i j, 0 ≤ R i j)
    (symK : ∀ i j, K i j = K j i) (symR : ∀ i j, R i j = R j i)
    (rowsK : ∀ i ∈ Z, ∑ j ∈ Z, K i j ≤ B (1/6) (l i) + err)
    (rowsR : ∀ i ∈ Z, ∑ j ∈ Z, R i j ≤ B (2/3) (l i) + err)
    (quad : (∑ i ∈ Z, zeroWeight t y (l i))^2 ≤ c *
      ∑ i ∈ Z, ∑ j ∈ Z, pairWeight t y (l i) * pairWeight t y (l j) *
        (Real.sqrt (K i j) * Real.sqrt (R i j))) :
    ∑ i ∈ Z, zeroWeight t y (l i) ≤
      c * Real.sqrt ((B (1/6) y + err) * (B (2/3) y + err)) := by
  let d := fun i => deficit y (l i)
  let u := fun i => pairWeight t y (l i)
  let w := fun i => zeroWeight t y (l i)
  let M := fun i j => Real.sqrt (K i j) * Real.sqrt (R i j)
  let T := Real.sqrt ((B (1/6) y + err) * (B (2/3) y + err))
  have hrow (i) (hi : i ∈ Z) : u i ^ 2 * ∑ j ∈ Z, M i j ≤ w i * T := by
    let A := ∑ j ∈ Z, K i j
    let D := ∑ j ∈ Z, R i j
    have hA : 0 ≤ A := Finset.sum_nonneg (fun j _ => hK i j)
    have hD : 0 ≤ D := Finset.sum_nonneg (fun j _ => hR i j)
    have hcs : ∑ j ∈ Z, M i j ≤ Real.sqrt (A * D) := by
      rw [Real.sqrt_mul hA]
      exact Real.sum_sqrt_mul_sqrt_le Z (hK i) (hR i)
    have hweight : u i ^ 2 = w i * Real.exp (-(5/12)*d i) := by
      dsimp [u, w, pairWeight, zeroWeight, d]
      rw [sq, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    have hscale : Real.exp (-(5/12)*d i) * Real.sqrt (A*D) =
        Real.sqrt ((Real.exp (-(1/6)*d i)*A) * (Real.exp (-(2/3)*d i)*D)) := by
      have hexp : Real.exp (-(1/6)*d i) * Real.exp (-(2/3)*d i) =
          Real.exp (-(5/12)*d i)^2 := by
        rw [sq, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      rw [mul_mul_mul_comm, hexp, Real.sqrt_mul (sq_nonneg _),
        Real.sqrt_sq (Real.exp_pos _).le]
    calc
      _ ≤ u i ^ 2 * Real.sqrt (A*D) := mul_le_mul_of_nonneg_left hcs (sq_nonneg _)
      _ = w i * Real.sqrt ((Real.exp (-(1/6)*d i)*A) * (Real.exp (-(2/3)*d i)*D)) := by
        rw [hweight, mul_assoc, hscale]
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        apply Real.sqrt_le_sqrt
        exact mul_le_mul
          (damped_row (by norm_num) (hl i hi) hy herr (rowsK i hi))
          (damped_row (by norm_num) (hl i hi) hy herr (rowsR i hi))
          (mul_nonneg (Real.exp_pos _).le hD)
          (add_nonneg (B_nonneg (by norm_num) hy) herr)
  have hs := symmetric_pair_sum Z u M (fun i j => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    (fun i j => by simp only [M, symK i j, symR i j])
  have hp : (∑ i ∈ Z, w i)^2 ≤ c * ((∑ i ∈ Z, w i)*T) :=
    quad.trans (mul_le_mul_of_nonneg_left (hs.trans (by
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum hrow)) hc)
  have hpos : 0 ≤ ∑ i ∈ Z, w i := Finset.sum_nonneg (fun i _ => (Real.exp_pos _).le)
  change ∑ i ∈ Z, w i ≤ c*T
  by_cases hz : ∑ i ∈ Z, w i = 0
  · rw [hz]
    exact mul_nonneg hc (Real.sqrt_nonneg _)
  · apply (mul_le_mul_iff_right₀ (lt_of_le_of_ne hpos (Ne.symm hz))).mp
    nlinarith only [hp]

end PintzWeightedDensity
