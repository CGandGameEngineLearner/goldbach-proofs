import Mathlib

namespace GoldbachMertensSum

open Finset MeasureTheory
open scoped Interval

noncomputable section

def theta (t : ℝ) : ℝ :=
  ∑ p ∈ (Icc 1 ⌊t⌋₊).filter Nat.Prime, Real.log (p:ℝ)

def w (t : ℝ) : ℝ := 1/(t*Real.log t)

def g (t : ℝ) : ℝ := (Real.log t+1)/(t^2*(Real.log t)^2)

private def coefficient (p : ℕ) : ℝ :=
  if Nat.Prime p then Real.log (p:ℝ) else 0

private theorem theta_eq_prefix (t : ℝ) :
    theta t = ∑ p ∈ Icc 0 ⌊t⌋₊, coefficient p := by
  have h : Icc 0 ⌊t⌋₊ = insert 0 (Icc 1 ⌊t⌋₊) := by
    ext p
    simp only [mem_Icc, mem_insert]
    omega
  rw [theta, sum_filter, h, sum_insert (by simp)]
  simp [coefficient, Nat.not_prime_zero]

theorem w_hasDerivAt {t : ℝ} (ht : 2 ≤ t) : HasDerivAt w (-g t) t := by
  have ht0 : t ≠ 0 := by linarith
  have hlog : Real.log t ≠ 0 := (Real.log_pos (by linarith : 1 < t)).ne'
  have hden : HasDerivAt (fun y : ℝ => y * Real.log y) (Real.log t+1) t := by
    simpa only [id_eq, one_mul, mul_inv_cancel₀ ht0] using
      (hasDerivAt_id t).fun_mul (Real.hasDerivAt_log ht0)
  change HasDerivAt (fun y : ℝ => 1/(y * Real.log y)) (-g t) t
  simpa only [g, mul_pow, zero_mul, zero_sub, one_mul, neg_div] using
    (hasDerivAt_const t (1:ℝ)).fun_div hden (mul_ne_zero ht0 hlog)

theorem g_continuousOn {a b : ℝ} (ha : 2 ≤ a) : ContinuousOn g (Set.Icc a b) := by
  intro t ht
  have ht1 : 1 < t := by linarith [ht.1]
  have ht0 : t ≠ 0 := by linarith
  have hlog : Real.log t ≠ 0 := (Real.log_pos ht1).ne'
  have hden : t ^ 2 * Real.log t ^ 2 ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ ht0) (pow_ne_zero _ hlog)
  unfold g
  exact ContinuousAt.continuousWithinAt (by fun_prop)

theorem theta_mul_g_integrable {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun t => theta t*g t) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
  have hg : IntegrableOn g (Set.Icc a b) := (g_continuousOn ha).integrableOn_Icc
  have h := integrableOn_mul_sum_Icc (m := 0) coefficient (show 0 ≤ a by linarith) hg
  simpa only [← theta_eq_prefix, mul_comm] using h

/-- Abel summation for the reciprocal-prime sum with real endpoints. -/
theorem abel_reciprocal_sum {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    (∑ p ∈ (Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime, 1/(p:ℝ)) =
      theta b*w b-theta a*w a + ∫ t in a..b, theta t*g t := by
  have hsum :
      (∑ p ∈ (Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime, 1/(p:ℝ)) =
        ∑ p ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, w p*coefficient p := by
    rw [sum_filter]
    apply sum_congr rfl
    intro p _
    by_cases hp : Nat.Prime p
    · have hp0 : (p:ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
      have hlog : Real.log (p:ℝ) ≠ 0 :=
        (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
      simp only [hp, ite_true, w, coefficient]
      field_simp
    · simp [hp, coefficient]
  have hdiff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ w t :=
    fun t ht => (w_hasDerivAt (ha.trans ht.1)).differentiableAt
  have hderiv : IntegrableOn (deriv w) (Set.Icc a b) := by
    apply ((g_continuousOn ha).neg.congr ?_).integrableOn_Icc
    intro t ht
    exact (w_hasDerivAt (ha.trans ht.1)).deriv
  have hform := sum_mul_eq_sub_sub_integral_mul coefficient (show 0 ≤ a by linarith)
    hab hdiff hderiv
  rw [← intervalIntegral.integral_of_le hab] at hform
  simp_rw [← theta_eq_prefix] at hform
  have hint : (∫ t in a..b, deriv w t * theta t) = -(∫ t in a..b, theta t*g t) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro t ht
    have hta : a ≤ t := by
      rw [Set.uIcc_of_le hab] at ht
      exact ht.1
    change deriv w t * theta t = -(theta t * g t)
    rw [(w_hasDerivAt (ha.trans hta)).deriv]
    ring
  rw [hsum, hform, hint]
  ring

end
end GoldbachMertensSum

namespace GoldbachMertensSmooth

open MeasureTheory

/-- Integrability of the smooth term in the Abel formula. -/
theorem baseline_integrable {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable
      (fun t : ℝ => t * ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2)))
      volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le hab]
  intro t ht
  have ht2 : 2 ≤ t := ha.trans ht.1
  have htn : t ≠ 0 := by linarith
  have hln : Real.log t ≠ 0 := (Real.log_pos (by linarith)).ne'
  have hlog : ContinuousAt Real.log t := Real.continuousAt_log htn
  have hid : ContinuousAt (fun t : ℝ => t) t := continuousAt_id
  have hden : t ^ 2 * Real.log t ^ 2 ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ htn) (pow_ne_zero _ hln)
  exact (hid.mul ((hlog.add continuousAt_const).div
    ((hid.pow 2).mul (hlog.pow 2)) hden)).continuousWithinAt

private theorem primitive_derivative (t : ℝ) (ht : 2 ≤ t) :
    HasDerivAt (fun x : ℝ => Real.log (Real.log x) - 1 / Real.log x)
      (t * ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2))) t := by
  have htn : t ≠ 0 := by linarith
  have hln : Real.log t ≠ 0 := (Real.log_pos (by linarith)).ne'
  have hLogLog := Real.hasDerivAt_log_log htn (by linarith : t ≠ 1) (by linarith : t ≠ -1)
  have hInv := (hasDerivAt_const t (1 : ℝ)).div (Real.hasDerivAt_log htn) hln
  convert hLogLog.sub hInv using 1
  field_simp [htn, hln]
  ring

/-- The smooth endpoint and integral contributions give the difference of the iterated logarithms. -/
theorem baseline {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    b * (1 / (b * Real.log b)) - a * (1 / (a * Real.log a)) +
      (∫ t in a..b, t * ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2))) =
        Real.log (Real.log b) - Real.log (Real.log a) := by
  have hPrim (t : ℝ) (ht : t ∈ Set.uIcc a b) :
      HasDerivAt (fun x : ℝ => Real.log (Real.log x) - 1 / Real.log x)
        (t * ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2))) t := by
    rw [Set.uIcc_of_le hab] at ht
    exact primitive_derivative t (ha.trans ht.1)
  have hEndpoint (t : ℝ) (ht : 2 ≤ t) :
      t * (1 / (t * Real.log t)) = 1 / Real.log t := by
    have htn : t ≠ 0 := by linarith
    have hln : Real.log t ≠ 0 := (Real.log_pos (by linarith)).ne'
    field_simp [htn, hln]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hPrim (baseline_integrable ha hab),
    hEndpoint b (ha.trans hab), hEndpoint a ha]
  ring

end GoldbachMertensSmooth

theorem Conjectures.Goldbach.MertensAbelBridge :
    let θ := fun x : ℝ =>
      ∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, Real.log (p : ℝ)
    ∀ (x₀ x : ℝ) (E : ℝ → ℝ), 2 ≤ x₀ → x₀ ≤ x →
      ContinuousOn E (Set.Icc x₀ x) → (∀ t ∈ Set.Icc x₀ x, |θ t - t| ≤ E t) →
      |(∑ p ∈ (Finset.Ioc ⌊x₀⌋₊ ⌊x⌋₊).filter Nat.Prime, (1 : ℝ) / (p : ℝ)) -
        (Real.log (Real.log x) - Real.log (Real.log x₀))| ≤
        E x / (x * Real.log x) + E x₀ / (x₀ * Real.log x₀) +
          ∫ t in x₀..x, E t * (Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2) := by
  dsimp only
  intro x₀ x E hx₀ hxx hE hBound
  let θ := GoldbachMertensSum.theta
  let w := GoldbachMertensSum.w
  let g := GoldbachMertensSum.g
  change ∀ t ∈ Set.Icc x₀ x, |θ t - t| ≤ E t at hBound
  have hPos (t : ℝ) (ht : t ∈ Set.Icc x₀ x) : 0 < t ∧ 0 < Real.log t := by
    have ht₂ : 2 ≤ t := hx₀.trans ht.1
    exact ⟨by linarith, Real.log_pos (by linarith)⟩
  have hg (t : ℝ) (ht : t ∈ Set.Icc x₀ x) : 0 ≤ g t := by
    obtain ⟨htPos, hLog⟩ := hPos t ht
    change 0 ≤ (Real.log t + 1) / (t ^ 2 * Real.log t ^ 2)
    positivity
  have hContG : ContinuousOn g (Set.Icc x₀ x) :=
    GoldbachMertensSum.g_continuousOn hx₀
  have hEInt : IntervalIntegrable (fun t => E t * g t) MeasureTheory.volume x₀ x :=
    ContinuousOn.intervalIntegrable_of_Icc hxx (hE.mul hContG)
  have hInt :
      |∫ t in x₀..x, (θ t - t) * g t| ≤ ∫ t in x₀..x, E t * g t := by
    rw [← Real.norm_eq_abs]
    apply intervalIntegral.norm_integral_le_of_norm_le hxx ?_ hEInt
    refine Filter.Eventually.of_forall ?_
    intro t ht
    have ht' : t ∈ Set.Icc x₀ x := ⟨ht.1.le, ht.2⟩
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hg t ht')]
    exact mul_le_mul_of_nonneg_right (hBound t ht') (hg t ht')
  have hEnd (t : ℝ) (ht : t ∈ Set.Icc x₀ x) : |(θ t - t) * w t| ≤ E t / (t * Real.log t) := by
    obtain ⟨htPos, hLog⟩ := hPos t ht
    have hw : 0 ≤ w t := div_nonneg zero_le_one (mul_nonneg htPos.le hLog.le)
    rw [abs_mul, abs_of_nonneg hw]
    calc
      _ ≤ E t * w t := mul_le_mul_of_nonneg_right (hBound t ht) hw
      _ = _ := by simp only [w, GoldbachMertensSum.w, mul_one_div]
  have hThetaInt : IntervalIntegrable (fun t => θ t * g t) MeasureTheory.volume x₀ x :=
    GoldbachMertensSum.theta_mul_g_integrable hx₀ hxx
  have hIdInt : IntervalIntegrable (fun t => t * g t) MeasureTheory.volume x₀ x :=
    GoldbachMertensSmooth.baseline_integrable hx₀ hxx
  have hAbel :
      (∑ p ∈ (Finset.Ioc ⌊x₀⌋₊ ⌊x⌋₊).filter Nat.Prime, (1 : ℝ) / (p : ℝ)) =
        θ x * w x - θ x₀ * w x₀ + ∫ t in x₀..x, θ t * g t :=
    GoldbachMertensSum.abel_reciprocal_sum hx₀ hxx
  have hSmooth :
      x * w x - x₀ * w x₀ + (∫ t in x₀..x, t * g t) =
        Real.log (Real.log x) - Real.log (Real.log x₀) :=
    GoldbachMertensSmooth.baseline hx₀ hxx
  have hSubInt :
      (∫ t in x₀..x, (θ t - t) * g t) =
        (∫ t in x₀..x, θ t * g t) - (∫ t in x₀..x, t * g t) := by
    simp only [sub_mul]
    exact intervalIntegral.integral_sub hThetaInt hIdInt
  have hEnvInt : (∫ t in x₀..x, E t * g t) =
      ∫ t in x₀..x, E t * (Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2) := by
    apply intervalIntegral.integral_congr
    intro t _
    simp only [g, GoldbachMertensSum.g, mul_div_assoc]
  rw [hAbel, ← hSmooth]
  have hError :
      θ x * w x - θ x₀ * w x₀ + (∫ t in x₀..x, θ t * g t) -
        (x * w x - x₀ * w x₀ + ∫ t in x₀..x, t * g t) =
      (θ x - x) * w x - (θ x₀ - x₀) * w x₀ + ∫ t in x₀..x, (θ t - t) * g t := by
    rw [hSubInt]
    ring
  rw [hError]
  calc
    _ ≤ |(θ x - x) * w x - (θ x₀ - x₀) * w x₀| + |∫ t in x₀..x, (θ t - t) * g t| :=
      abs_add_le _ _
    _ ≤ |(θ x - x) * w x| + |(θ x₀ - x₀) * w x₀| + (∫ t in x₀..x, E t * g t) := by
      apply add_le_add _ hInt
      simpa only [sub_zero, zero_sub, abs_neg] using
        abs_sub_le ((θ x - x) * w x) (0 : ℝ) ((θ x₀ - x₀) * w x₀)
    _ ≤ _ := by
      rw [hEnvInt]
      exact add_le_add
        (add_le_add (hEnd x ⟨hxx, le_rfl⟩) (hEnd x₀ ⟨le_rfl, hxx⟩)) le_rfl
