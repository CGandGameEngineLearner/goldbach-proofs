import Mathlib

open Finset MeasureTheory

private noncomputable def ordinatePhase (θ t : ℝ) : ℂ :=
  Complex.exp (Complex.I * (θ * Real.log t : ℝ))

private theorem norm_phase_chord (x y : ℝ) :
    ‖Complex.exp (Complex.I * (x : ℂ)) - Complex.exp (Complex.I * (y : ℂ))‖ ≤ |x-y| := by
  have h : Complex.exp (Complex.I * (x : ℂ)) - Complex.exp (Complex.I * (y : ℂ)) =
      Complex.exp (Complex.I * (y : ℂ)) *
        (Complex.exp (Complex.I * (x-y : ℝ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [h, norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]
  simpa only [Real.norm_eq_abs] using (Real.norm_exp_I_mul_ofReal_sub_one_le (x:=x-y))

private theorem phase_intervalIntegrable (θ : ℝ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (ordinatePhase θ) volume a b := by
  apply ContinuousOn.intervalIntegrable_of_Icc hab
  have hlog : ContinuousOn Real.log (Set.Icc a b) := Real.continuousOn_log.mono (by
    intro t ht
    exact Set.mem_compl_singleton_iff.mpr ((lt_of_lt_of_le ha ht.1).ne'))
  unfold ordinatePhase
  exact Complex.continuous_exp.comp_continuousOn
    (continuous_const.continuousOn.mul (Complex.continuous_ofReal.comp_continuousOn
      (continuous_const.continuousOn.mul hlog)))

private theorem phase_cell_bound (θ : ℝ) {Y x t : ℝ} (hY : 0 < Y)
    (hYx : Y ≤ x) (hxt : x ≤ t) (ht : t ≤ x+1) :
    ‖ordinatePhase θ x - ordinatePhase θ t‖ ≤ |θ|/Y := by
  have hx : 0 < x := hY.trans_le hYx
  have htp : 0 < t := hx.trans_le hxt
  have hLogNN : 0 ≤ Real.log t-Real.log x := sub_nonneg.mpr (Real.log_le_log hx hxt)
  have hLog : Real.log t-Real.log x ≤ 1/Y := calc
    _ = Real.log (t/x) := (Real.log_div htp.ne' hx.ne').symm
    _ ≤ t/x-1 := Real.log_le_sub_one_of_pos (div_pos htp hx)
    _ = (t-x)/x := by rw [sub_div,div_self hx.ne']
    _ ≤ 1/x := div_le_div_of_nonneg_right (by linarith) hx.le
    _ ≤ _ := one_div_le_one_div_of_le hY hYx
  calc
    _ ≤ |θ*Real.log x - θ*Real.log t| := norm_phase_chord _ _
    _ = |θ| * (Real.log t-Real.log x) := by
      rw [← mul_sub,abs_mul,abs_of_nonpos (by linarith : Real.log x-Real.log t ≤ 0)]
      ring
    _ ≤ |θ| * (1/Y) := mul_le_mul_of_nonneg_left hLog (abs_nonneg θ)
    _ = _ := by ring

private theorem interval_cell_error (θ : ℝ) {Y x : ℝ} (hY : 0 < Y) (hYx : Y ≤ x) :
    ‖ordinatePhase θ x - ∫ t in x..(x+1), ordinatePhase θ t‖ ≤ |θ|/Y := by
  have hle : x ≤ x+1 := by linarith
  have hi := phase_intervalIntegrable θ (hY.trans_le hYx) hle
  have hIntegral : ordinatePhase θ x - (∫ t in x..(x+1), ordinatePhase θ t) =
      ∫ t in x..(x+1), ordinatePhase θ x - ordinatePhase θ t := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const hi,intervalIntegral.integral_const]
    simp
  rw [hIntegral]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a:=x) (b:=x+1) (C:=|θ|/Y) (f:=fun t => ordinatePhase θ x - ordinatePhase θ t) (by
      intro t ht
      rw [Set.uIoc_of_le hle] at ht
      exact phase_cell_bound θ hY hYx ht.1.le ht.2)
  simpa using hb

theorem Conjectures.TwinPrimes.IntegerScaleOrdinatePairKernel :
    (∀ (Y u v : ℕ) (θ : ℝ), 1≤Y → Y≤u → u≤v → v≤2*Y → ‖(∑ X ∈ Finset.Ico u v, Complex.exp (Complex.I * (θ * Real.log X : ℝ))) - ∫ t in (u:ℝ)..(v:ℝ), Complex.exp (Complex.I * (θ * Real.log t : ℝ))‖ ≤ 1+|θ|) := by
  intro Y u v θ hY hu huv hv
  have hYr : (0:ℝ) < Y := by exact_mod_cast (show 0 < Y by omega)
  have hLower (x : ℕ) (hx : x ∈ Ico u v) : (Y:ℝ) ≤ x :=
    by exact_mod_cast hu.trans (mem_Ico.mp hx).1
  have hI (x : ℕ) (hx : x ∈ Ico u v) :
      IntervalIntegrable (ordinatePhase θ) volume (x:ℝ) ((x+1:ℕ):ℝ) := by
    exact phase_intervalIntegrable θ (hYr.trans_le (hLower x hx))
      (by exact_mod_cast (show x≤x+1 by omega))
  have hSum := intervalIntegral.sum_integral_adjacent_intervals_Ico
    (a := fun x : ℕ => (x:ℝ)) huv
    (fun x hx => hI x (Finset.mem_Ico.mpr hx))
  change ‖(∑ x ∈ Ico u v, ordinatePhase θ (x:ℝ)) -
      ∫ t in (u:ℝ)..(v:ℝ), ordinatePhase θ t‖ ≤ 1+|θ|
  rw [← hSum, ← sum_sub_distrib]
  calc
    _ ≤ ∑ x ∈ Ico u v, ‖ordinatePhase θ (x:ℝ) -
        ∫ t in (x:ℝ)..((x+1:ℕ):ℝ), ordinatePhase θ t‖ := norm_sum_le _ _
    _ ≤ ∑ _x ∈ Ico u v, |θ|/(Y:ℝ) := by
      apply sum_le_sum
      intro x hx
      simpa only [Nat.cast_add, Nat.cast_one] using interval_cell_error θ hYr (hLower x hx)
    _ = ((Ico u v).card : ℝ) * (|θ|/(Y:ℝ)) := by rw [sum_const,nsmul_eq_mul]
    _ ≤ (Y:ℝ) * (|θ|/(Y:ℝ)) := by
      apply mul_le_mul_of_nonneg_right _ (div_nonneg (abs_nonneg _) hYr.le)
      rw [Nat.card_Ico]
      exact_mod_cast (show v-u≤Y by omega)
    _ = |θ| := by field_simp
    _ ≤ _ := by linarith
