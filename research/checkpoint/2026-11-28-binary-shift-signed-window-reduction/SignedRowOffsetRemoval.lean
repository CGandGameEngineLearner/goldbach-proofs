import SignedResidualTerminal

open Filter Finset MeasureTheory
namespace Goldbach.SignedRowOffsetRemoval
open MiddleCanonicalModel ShiftWideArc PrincipalZeroOffset
noncomputable section
open scoped Classical

/-- The reduced numerator's principal mean on the middle-denominator windows. -/
def meanField (Y : ℕ) (t : ℝ) : ℂ :=
  ∑ i ∈ GB6Geometry.indices (Q Y), {u : ℝ | bandCenter Y u i.1 i.2}.indicator
    (fun _ => ThreeQArith.mean i.1 i.2) t

/-- Summing all terms involving the constant offset before estimating them cancels
the full geometric kernel. -/
def offsets (Y : ℕ) (t : ℝ) : ℂ := -2 * meanField Y t * field Y t - (meanField Y t)^2

def strippedRows (Y : ℕ) (t : ℝ) : ℂ := signedRows Y t - offsets Y t

private theorem geometry {Y q a : ℕ} {t : ℝ} (hw : bandCenter Y t q a) :
    (⟨q,a⟩:GB6Geometry.Idx) ∈ GB6Geometry.indices (Q Y) ∧
    t ∈ GB6Geometry.window (H Y) Y q a := by
  obtain ⟨hq,_,hu,ha,hc,ht⟩ := hw
  have hqQ := (hu.trans (min_le_left ..)).trans_eq (GB6Growth.grid_eq_floor Y)
  exact ⟨mem_sigma.mpr ⟨mem_Icc.mpr ⟨hq,hqQ⟩,mem_filter.mpr ⟨mem_range.mpr (by change a < q+1; omega),hc⟩⟩,
    (GB6Geometry.mem_window Y q a t).mpr ht⟩

private theorem at_center {Y q a : ℕ} {t : ℝ} (hs : 2*(H Y)^2 < Y) (hQ : Q Y ≤ H Y)
    (hw : bandCenter Y t q a) (f : ℕ → ℕ → ℝ → ℂ) :
    (∑ i ∈ GB6Geometry.indices (Q Y), {u : ℝ | bandCenter Y u i.1 i.2}.indicator
      (f i.1 i.2) t) = f q a t := by
  let i : GB6Geometry.Idx := ⟨q,a⟩
  obtain ⟨hi,hwin⟩ := geometry hw
  rw [sum_eq_single_of_mem i hi]
  · exact Set.indicator_of_mem hw _
  · intro j hj hn
    apply Set.indicator_of_notMem
    intro h
    exact hn (GB6Geometry.unique_window hs hQ t ⟨hj,(geometry h).2⟩ ⟨hi,hwin⟩)

theorem strippedRows_center {Y q a : ℕ} [NeZero q] {t : ℝ}
    (hs : 2*(H Y)^2 < Y) (hQ : Q Y ≤ H Y) (hw : bandCenter Y t q a) :
    let β := t-(a:ℝ)/q
    let Z := GoldbachTwistedMellin.canonicalCorrection Y (a : ZMod q) β
    strippedRows Y t = Z^2 - 2*(ThreeQArith.mean q a * GB6Kernel.kernel Y β)*Z := by
  dsimp only
  unfold strippedRows signedRows offsets meanField
  rw [at_center hs hQ hw (fun q a u => rowTerm Y q a (u-(a:ℝ)/q)),
    at_center hs hQ hw (fun q a _ => ThreeQArith.mean q a),field_eq_center hs hQ hw,
    center_eq hw.2.2.2.2.1]
  simp only [rowTerm,dite_eq_right (NeZero.ne q)]
  ring

theorem strippedRows_zero_outside {Y : ℕ} {t : ℝ} (ht : t ∉ bandSet Y) :
    strippedRows Y t = 0 := by
  have h (f : ℕ → ℕ → ℝ → ℂ) :
      (∑ i ∈ GB6Geometry.indices (Q Y), {u : ℝ | bandCenter Y u i.1 i.2}.indicator
        (f i.1 i.2) t) = 0 := sum_eq_zero fun i _ =>
          Set.indicator_of_notMem (fun h => ht ⟨i.1,i.2,h⟩) _
  simp only [strippedRows,signedRows,offsets,meanField,h (fun q a u => rowTerm Y q a (u-(a:ℝ)/q)),
    h (fun q a _ => ThreeQArith.mean q a)]
  ring

/-- Chebyshev's theta upper bound gives a uniform linear bound for the
actual prime polynomial on the entire circle. -/
theorem prime_norm (Y : ℕ) (t : ℝ) : ‖S Y t‖ ≤ 3*(Y:ℝ) := by
  have hw (k : ℕ) : 0 ≤ weight k := by
    unfold weight
    split_ifs <;> simp [Real.log_natCast_nonneg]
  have hθ : (∑ k ∈ range (Y+1), weight k) = Chebyshev.theta Y := by
    rw [Chebyshev.theta_eq_sum_primesLE_log,Nat.primesLE_eq_filter_range,sum_filter]
    rfl
  have hb := Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg (α:=ℝ) Y)
  have hl := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4)
  calc
    _ ≤ ∑ k ∈ range (Y+1), ‖(weight k : ℂ)*phase ((k:ℝ)*t)‖ := norm_sum_le _ _
    _ = Chebyshev.theta Y := by
      simpa only [norm_mul,phase,Complex.norm_exp_ofReal_mul_I,mul_one,Complex.norm_real,
        Real.norm_of_nonneg (hw _)] using hθ
    _ ≤ _ := hb.trans (mul_le_mul_of_nonneg_right (by linarith only [hl]) (Nat.cast_nonneg _))

private theorem eventual_band_field : ∀ᶠ Y : ℕ in atTop, ∀ t ∈ bandSet Y,
    ‖field Y t‖ ≤ 4*(Y:ℝ) := by
  obtain ⟨C,hC,h⟩ := eventual_field_bound
  filter_upwards [h,GB6Growth.polylog_le_power C hC.le 4 (15/64) (by norm_num),
    eventually_ge_atTop (1:ℕ)] with Y he hlog hY
  have hy : 0 < (Y:ℝ) := by exact_mod_cast hY
  have hscale : 0 ≤ GoldbachTwistedMellin.logScale Y := by
    unfold GoldbachTwistedMellin.logScale
    have hy1 : (1:ℝ) ≤ Y := by exact_mod_cast hY
    have : 1 ≤ 2*(Y:ℝ) := by linarith
    linarith [Real.log_nonneg this]
  have hpow := (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ hscale (logScale_le_logFactor hY) 4) hC.le).trans hlog
  intro t ht
  have hdiff : ‖S Y t-field Y t‖ ≤ (Y:ℝ) := calc
    _ ≤ _ := he t ht
    _ = (C*(GoldbachTwistedMellin.logScale Y)^4)*(Y:ℝ)^(49/64:ℝ) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hpow (by positivity : 0 ≤ (Y:ℝ)^(49/64:ℝ))
    _ = _ := by rw [← Real.rpow_add hy]; norm_num
  have ht' := norm_sub_le (S Y t) (S Y t-field Y t)
  rw [sub_sub_cancel] at ht'
  linarith only [prime_norm Y t,hdiff,ht']

private theorem envelope {Y : ℕ} (hs : 2*(H Y)^2 < Y) (hQ : Q Y ≤ H Y)
    (hf : ∀ t ∈ bandSet Y, ‖field Y t‖ ≤ 4*(Y:ℝ)) (t : ℝ) :
    ‖offsets Y t‖ ≤ (bandSet Y).indicator (fun _ => 8*(Y:ℝ)+1) t := by
  by_cases ht : t ∈ bandSet Y
  · rw [Set.indicator_of_mem ht]
    obtain ⟨q,a,hw⟩ := ht
    have htq : (1:ℝ) ≤ q.totient := by exact_mod_cast Nat.totient_pos.mpr hw.1
    have hc := (ThreeQArith.norm_mean_le hw.2.2.2.2.1).trans (one_div_le_one_div_of_le zero_lt_one htq)
    rw [div_one] at hc
    have hm : meanField Y t = ThreeQArith.mean q a :=
      at_center hs hQ hw (fun q a _ => ThreeQArith.mean q a)
    have h2 := (pow_le_pow_left₀ (norm_nonneg _) hc 2).trans_eq (one_pow 2)
    unfold offsets
    rw [hm]
    apply (norm_sub_le _ _).trans
    simp only [norm_mul,norm_neg,Complex.norm_ofNat,norm_pow]
    have hp := mul_le_mul (mul_le_mul_of_nonneg_left hc (by norm_num : 0 ≤ (2:ℝ)))
      (hf t ⟨q,a,hw⟩) (norm_nonneg _) (by norm_num)
    linarith only [hp,h2]
  · have hz : meanField Y t = 0 := sum_eq_zero fun i _ =>
        Set.indicator_of_notMem (fun h => ht ⟨i.1,i.2,h⟩) _
    simp [offsets,hz,ht]

private theorem offsets_measurable (Y : ℕ) : StronglyMeasurable (offsets Y) := by
  have h : StronglyMeasurable (meanField Y) := Finset.stronglyMeasurable_fun_sum _ fun i _ =>
    stronglyMeasurable_const.indicator (measurable_center_set Y i.1 i.2)
  exact ((stronglyMeasurable_const.mul h).mul (field_stronglyMeasurable Y)).sub (h.pow 2)

private theorem integrable_mode_square {F : ℝ → ℂ} (hm : MemLp F 2 GB5Variance.unitMeasure) (m : ℕ) :
    Integrable (fun t => (F t)^2*GB5Variance.phase (-(m:ℝ)*t)) GB5Variance.unitMeasure := by
  have ha : AEStronglyMeasurable (fun t => (F t)^2*GB5Variance.phase (-(m:ℝ)*t)) GB5Variance.unitMeasure :=
    (hm.aestronglyMeasurable.pow 2).mul (by unfold GB5Variance.phase; fun_prop)
  apply (integrable_norm_iff ha).mp
  simp only [norm_mul,norm_pow,GB5Variance.phase,Complex.norm_exp_ofReal_mul_I,mul_one]
  exact (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm

theorem uniform_power : ∀ᶠ Y : ℕ in atTop, ∀ m : ℕ,
    ‖GB5Variance.modeCoeff (signedRows Y) m - GB5Variance.modeCoeff (strippedRows Y) m‖ ≤
      (Y:ℝ)^(2/3:ℝ) := by
  filter_upwards [eventual_band_field,GB6Growth.eventual_geometry,eventually_field_mem,
    GB6Growth.polylog_le_power 9216 (by norm_num) 2 (1/12) (by norm_num),eventually_ge_atTop (1:ℕ)]
    with Y hf hg hmem hlog hy
  have hgrid := GB6Growth.grid_eq_floor Y
  have hheight : GB6Growth.height Y = H Y := by simp only [GB6Growth.height,H,hgrid]; rfl
  change GB6Growth.grid Y = Q Y at hgrid
  rw [hheight,hgrid] at hg
  have hP : 0 < (Y:ℝ) := by exact_mod_cast hy
  have h1 : (1:ℝ) ≤ Y := by exact_mod_cast hy
  have hdom := envelope hg.2.2.2.2 hg.2.1 hf
  have hI : Integrable ((bandSet Y).indicator (fun _ : ℝ => 8*(Y:ℝ)+1)) GB5Variance.unitMeasure :=
    (integrable_const _).indicator (measurable_bandSet Y)
  have hvol := CanonicalBandCount.unit_measure_middle_power hy
  have hh : 9216*(Nat.log 2 (Y+2):ℝ)^2 ≤ (Y:ℝ)^(1/12:ℝ) :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) (GB6Growth.L_le_logFactor Y) 2)
      (by norm_num : 0 ≤ (9216:ℝ))).trans hlog
  intro m
  let P (t : ℝ) := GB5Variance.phase (-(m:ℝ)*t)
  have hphase (t : ℝ) : ‖P t‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have hO (t : ℝ) : ‖offsets Y t*P t‖ ≤ (bandSet Y).indicator (fun _ => 8*(Y:ℝ)+1) t := by
    simpa only [norm_mul,hphase,mul_one] using hdom t
  have hOi : Integrable (fun t => offsets Y t*P t) GB5Variance.unitMeasure := hI.mono'
    ((offsets_measurable Y).aestronglyMeasurable.mul (by unfold P GB5Variance.phase; fun_prop))
    (ae_of_all _ hO)
  have hp := (GB6Var.G_memLp (Q Y) (H Y) Y).indicator (measurable_bandSet Y).nullMeasurableSet
  have hsigned : Integrable (fun t => signedRows Y t*P t) GB5Variance.unitMeasure := by
    have he (t : ℝ) := field_square_difference hg.2.2.2.2 hg.2.1 t
    simp_rw [← he,sub_mul]
    exact (integrable_mode_square hmem m).sub (integrable_mode_square (F:=pureField Y) hp m)
  simp only [GB5Variance.modeCoeff,intervalIntegral.integral_of_le zero_le_one]
  change ‖(∫ t, signedRows Y t*P t ∂GB5Variance.unitMeasure) -
    (∫ t, strippedRows Y t*P t ∂GB5Variance.unitMeasure)‖ ≤ _
  simp only [strippedRows,sub_mul]
  rw [integral_sub hsigned hOi,sub_sub_cancel]
  apply (MeasureTheory.norm_integral_le_of_norm_le hI (ae_of_all _ hO)).trans
  rw [integral_indicator_const _ (measurable_bandSet Y)]
  calc
    _ ≤ (1024*(Nat.log 2 (Y+2):ℝ)^2*(Y:ℝ)^(-(5/12):ℝ)) * (9*Y) :=
      mul_le_mul hvol (by linarith only [h1]) (by positivity) (by positivity)
    _ = (9216*(Nat.log 2 (Y+2):ℝ)^2)*((Y:ℝ)^(-(5/12):ℝ)*Y) := by ring
    _ ≤ (Y:ℝ)^(1/12:ℝ)*((Y:ℝ)^(-(5/12):ℝ)*Y) :=
      mul_le_mul_of_nonneg_right hh (by positivity)
    _ = (Y:ℝ)^(2/3:ℝ) := by rw [← Real.rpow_add_one hP.ne',← Real.rpow_add hP]; norm_num

/-- The full joint removal has size o(Y) uniformly at all Fourier frequencies. -/
theorem eventual_mode_bound (ε : ℝ) (hε : 0 < ε) : ∀ᶠ Y : ℕ in atTop, ∀ m : ℕ,
    ‖GB5Variance.modeCoeff (signedRows Y) m - GB5Variance.modeCoeff (strippedRows Y) m‖ ≤ ε*(Y:ℝ) := by
  have hlarge := ((tendsto_rpow_atTop (by norm_num : 0 < (1/3:ℝ))).comp
    (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop (1/ε)
  filter_upwards [uniform_power,hlarge,eventually_ge_atTop (1:ℕ)] with Y hpow hY hy
  have hp : 0 < (Y:ℝ) := by exact_mod_cast hy
  change 1/ε ≤ (Y:ℝ)^(1/3:ℝ) at hY
  have ha := (div_le_iff₀ hε).mp hY
  intro m
  refine (hpow m).trans ?_
  calc
    _ = (1:ℝ)*(Y:ℝ)^(2/3:ℝ) := by ring
    _ ≤ ((Y:ℝ)^(1/3:ℝ)*ε)*(Y:ℝ)^(2/3:ℝ) := mul_le_mul_of_nonneg_right ha (by positivity)
    _ = _ := by rw [mul_right_comm,mul_comm _ ε,←Real.rpow_add hp]; norm_num

end
end Goldbach.SignedRowOffsetRemoval
#print axioms Goldbach.SignedRowOffsetRemoval.strippedRows_center
#print axioms Goldbach.SignedRowOffsetRemoval.eventual_mode_bound
