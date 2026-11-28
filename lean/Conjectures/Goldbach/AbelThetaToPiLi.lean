import Mathlib.NumberTheory.Chebyshev
import Mathlib.Tactic

open MeasureTheory Finset

theorem Conjectures.Goldbach.AbelThetaToPiLi : (let π := fun x : ℝ => (((Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime).card : ℝ); let θ := fun x : ℝ => ∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, Real.log (p : ℝ); ∀ (x₀ x : ℝ) (E : ℝ → ℝ), 2 ≤ x₀ → x₀ ≤ x → ContinuousOn E (Set.Icc x₀ x) → (∀ t ∈ Set.Icc x₀ x, |θ t - t| ≤ E t) → |(π x - π x₀) - ∫ t in x₀..x, 1 / Real.log t| ≤ E x / Real.log x + E x₀ / Real.log x₀ + ∫ t in x₀..x, E t / (t * (Real.log t) ^ 2)) := by
  intro P T a b E ha hab hE herr
  have hb := ha.trans hab
  have pc (t : ℝ) : P t = (Nat.primeCounting ⌊t⌋₊ : ℝ) := by
    simp only [P, ← Nat.primesLE_eq_filter_Icc_one,Nat.primesLE_card_eq_primeCounting]
  have theta (t : ℝ) : T t = Chebyshev.theta t := by
    simp only [T, ← Nat.primesLE_eq_filter_Icc_one,Chebyshev.theta_eq_sum_primesLE]
  let F (t : ℝ) := Chebyshev.theta t/(t*Real.log t^2)
  let U (t : ℝ) := 1/Real.log t
  let V (t : ℝ) := 1/Real.log t^2
  have hF (x : ℝ) (hx : 2 ≤ x) : IntervalIntegrable F volume 2 x :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hx).mpr
      (Chebyshev.integrableOn_theta_div_id_mul_log_sq x)
  have hFab : IntervalIntegrable F volume a b := (hF a ha).symm.trans (hF b hb)
  have hlog (t : ℝ) (ht : t ∈ Set.uIcc a b) : 0 < Real.log t := by
    rw [Set.uIcc_of_le hab] at ht
    exact Real.log_pos (by linarith [ht.1])
  have hU : IntervalIntegrable U volume a b := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    have ht' := ht
    rw [Set.uIcc_of_le hab] at ht'
    have ht0 : t ≠ 0 := by linarith [ht'.1]
    exact (continuousAt_const.div (Real.continuousAt_log ht0) (hlog t ht).ne').continuousWithinAt
  have hV : IntervalIntegrable V volume a b :=
    Chebyshev.intervalIntegrable_one_div_log_sq (by linarith) (by linarith)
  have main := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun t : ℝ => t / Real.log t) (f' := fun t => U t - V t)
    (a:=a) (b:=b) (fun t ht => by
      have ht' := ht
      rw [Set.uIcc_of_le hab] at ht'
      have hpos : t ≠ 0 := by linarith [ht'.1]
      have hl := (hlog t ht).ne'
      have H := (hasDerivAt_id t).div (Real.hasDerivAt_log hpos) hl
      have eq : U t-V t = (1*Real.log t - id t * t⁻¹)/Real.log t^2 := by
        dsimp [U,V]; field_simp
      rw [eq]
      exact H) (hU.sub hV)
  rw [intervalIntegral.integral_sub hU hV] at main
  have hf := intervalIntegral.integral_interval_sub_left (hF b hb) (hF a ha)
  have hcb := Chebyshev.primeCounting_eq_theta_div_log_add_integral hb
  have hca := Chebyshev.primeCounting_eq_theta_div_log_add_integral ha
  change (Nat.primeCounting ⌊b⌋₊:ℝ) = _ + ∫ t in 2..b, F t at hcb
  change (Nat.primeCounting ⌊a⌋₊:ℝ) = _ + ∫ t in 2..a, F t at hca
  have center : (P b - P a) - (∫ t in a..b, U t) =
      (T b-b)/Real.log b - (T a-a)/Real.log a + ∫ t in a..b, F t - V t := by
    rw [pc,pc,theta,theta,sub_div,sub_div,intervalIntegral.integral_sub hFab hV]
    linarith
  have endpoint (t : ℝ) (ht : t ∈ Set.Icc a b) : |(T t-t)/Real.log t| ≤ E t/Real.log t := by
    rw [abs_div,abs_of_pos (Real.log_pos (by linarith [ht.1]))]
    exact div_le_div_of_nonneg_right (herr t ht) (Real.log_nonneg (by linarith [ht.1]))
  have hmajor : IntervalIntegrable (fun t => E t/(t*Real.log t^2)) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    refine hE.div (continuousOn_id.mul ((Real.continuousOn_log.mono ?_).pow 2)) ?_
    · intro t ht
      exact ne_of_gt (by linarith [ht.1] : 0 < t)
    · intro t ht
      have ht1 : 1 < t := by linarith [ht.1]
      exact mul_ne_zero (by linarith) (pow_ne_zero _ (Real.log_pos ht1).ne')
  have integ : |∫ t in a..b, F t - V t| ≤ ∫ t in a..b, E t/(t*Real.log t^2) := by
    rw [← Real.norm_eq_abs]
    apply intervalIntegral.norm_integral_le_of_norm_le hab _ hmajor
    apply Filter.Eventually.of_forall
    intro t ht
    have ht1 : 1 < t := by linarith [ht.1]
    have ht0 : t ≠ 0 := by linarith
    have hlt := (Real.log_pos ht1).ne'
    have eq : F t-V t = (T t-t)/(t*Real.log t^2) := by
      rw [theta]; dsimp [F,V]; field_simp
    rw [Real.norm_eq_abs,eq,abs_div,abs_of_pos (mul_pos (by linarith) (sq_pos_of_pos (Real.log_pos ht1)))]
    exact div_le_div_of_nonneg_right (herr t ⟨ht.1.le,ht.2⟩) (by positivity)
  change |(P b-P a) - (∫ t in a..b,U t)| ≤ _
  rw [center]
  exact (abs_add_le ..).trans (add_le_add ((abs_sub ..).trans (add_le_add
    (endpoint b ⟨hab,le_rfl⟩) (endpoint a ⟨le_rfl,hab⟩))) integ)
