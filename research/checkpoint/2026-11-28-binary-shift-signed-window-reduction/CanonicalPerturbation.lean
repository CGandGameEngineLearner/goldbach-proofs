import Conjectures.Goldbach.ThreeQuartersModelSqrtExceptions

open Finset MeasureTheory
namespace Goldbach.CanonicalPerturbation
noncomputable section
open scoped Classical
open GB5Variance (unitMeasure modeCoeff)

/-- The perturbation is measured against the true prime sum alone. -/
theorem pointwise (s t : ℂ) {D : ℝ} (hD : 0 ≤ D) (h : ‖s-t‖ ≤ D) :
    ‖s^2-t^2‖^2 ≤ 8*D^2*‖s‖^2 + 2*D^4 := by
  have hsum : ‖s+t‖ ≤ 2*‖s‖+D := by
    have h₁ := norm_add_le s (s-(s-t))
    have h₂ := norm_sub_le s (s-t)
    rw [sub_sub_cancel] at h₁ h₂
    linarith
  have hsq : ‖s^2-t^2‖ ≤ (2*‖s‖+D)*D := by
    rw [sq_sub_sq,norm_mul]
    exact mul_le_mul hsum h (norm_nonneg _) (by positivity)
  have hpow := pow_le_pow_left₀ (norm_nonneg _) hsq 2
  nlinarith only [hpow,sq_nonneg (2*D*‖s‖ - D^2)]

def masked (B : Set ℝ) (S T : ℝ → ℂ) := B.indicator (fun t => S t^2-T t^2)

def budget (B : Set ℝ) (S : ℝ → ℂ) (D : ℝ) : ℝ :=
  8*D^2*(∫ t in B, ‖S t‖^2 ∂unitMeasure) + 2*D^4*unitMeasure.real B

theorem band_energy (B : Set ℝ) (hB : MeasurableSet B) (S T : ℝ → ℂ)
    (hS : MemLp S 2 unitMeasure) (hT : AEStronglyMeasurable T unitMeasure)
    {D : ℝ} (hD : 0 ≤ D) (h : ∀ t ∈ Set.Icc (0:ℝ) 1 ∩ B, ‖S t - T t‖ ≤ D) :
    MemLp (masked B S T) 2 unitMeasure ∧
    (∫ t in (0:ℝ)..1, ‖masked B S T t‖^2) ≤ budget B S D := by
  let F := masked B S T
  let U := B.indicator (fun t => 8*D^2*‖S t‖^2)
  let V := B.indicator (fun _ => 2*D^4)
  have hF : AEStronglyMeasurable F unitMeasure :=
    ((hS.aestronglyMeasurable.pow 2).sub (hT.pow 2)).indicator hB
  have hSi := (memLp_two_iff_integrable_sq_norm hS.aestronglyMeasurable).mp hS
  have hU : Integrable U unitMeasure := (hSi.const_mul _).indicator hB
  have hV : Integrable V unitMeasure := (integrable_const _).indicator hB
  have hb : ∀ᵐ t ∂unitMeasure, ‖F t‖^2 ≤ U t + V t := by
    apply (ae_restrict_iff' measurableSet_Ioc).2
    apply ae_of_all
    intro t ht
    by_cases htB : t ∈ B
    · simpa only [U,V,F,masked,Set.indicator_of_mem htB] using
        pointwise (S t) (T t) hD (h t ⟨⟨ht.1.le,ht.2⟩,htB⟩)
    · simp only [U,V,F,masked,Set.indicator_of_notMem htB,norm_zero,zero_pow (by decide : 2 ≠ 0),zero_add,le_refl]
  have hi : Integrable (fun t => ‖F t‖^2) unitMeasure := by
    apply (hU.add hV).mono' (hF.norm.pow 2)
    filter_upwards [hb] with t ht
    change ‖(‖F t‖^2:ℝ)‖ ≤ U t + V t
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact ht
  refine ⟨(memLp_two_iff_integrable_sq_norm hF).mpr hi,?_⟩
  rw [intervalIntegral.integral_of_le zero_le_one]
  change (∫ t, ‖F t‖^2 ∂unitMeasure) ≤ budget B S D
  have hUV := integral_mono_ae hi (hU.add hV) hb
  calc
    _ ≤ ∫ t, U t + V t ∂unitMeasure := hUV
    _ = _ := by
      rw [integral_add hU hV]
      dsimp only [U,V,budget]
      rw [integral_indicator hB,integral_const_mul,integral_indicator_const _ hB,smul_eq_mul]
      ring

theorem prime_budget (B : Set ℝ) (Y : ℕ) (D : ℝ) :
    budget B (GB6Var.S Y) D ≤
      8*D^2*(((Y:ℝ)+1)*(1+Real.log ((Y:ℝ)+2))^2) + 2*D^4*unitMeasure.real B := by
  have hS := GB6Var.S_memLp Y
  have hi := (memLp_two_iff_integrable_sq_norm hS.aestronglyMeasurable).mp hS
  have hB : (∫ t in B, ‖GB6Var.S Y t‖^2 ∂unitMeasure) ≤
      ∫ t, ‖GB6Var.S Y t‖^2 ∂unitMeasure :=
    setIntegral_le_integral hi (ae_of_all _ fun _ => sq_nonneg _)
  have hglobal := GB6Var.S_energy Y
  rw [intervalIntegral.integral_of_le zero_le_one] at hglobal
  unfold budget
  exact add_le_add (mul_le_mul_of_nonneg_left (hB.trans hglobal)
    (mul_nonneg (by norm_num : 0 ≤ (8:ℝ)) (sq_nonneg D))) (le_refl _)

/-- Finite Bessel bounds all natural frequencies simultaneously for each band. -/
theorem exceptional_frequencies (B : Set ℝ) (hB : MeasurableSet B) (S T : ℝ → ℂ)
    (hS : MemLp S 2 unitMeasure) (hT : AEStronglyMeasurable T unitMeasure)
    {D : ℝ} (hD : 0 ≤ D) (h : ∀ t ∈ Set.Icc (0:ℝ) 1 ∩ B, ‖S t - T t‖ ≤ D)
    (I : Finset ℕ) {r : ℝ} (hr : 0 ≤ r) :
    (((I.filter (fun m => r ≤ ‖modeCoeff (masked B S T) m‖)).card:ℝ)*r^2) ≤ budget B S D := by
  let A := I.filter (fun m => r ≤ ‖modeCoeff (masked B S T) m‖)
  obtain ⟨hF,hh⟩ := band_energy B hB S T hS hT hD h
  change (A.card:ℝ)*r^2 ≤ _
  calc
    _ = ∑ _m ∈ A, r^2 := by simp
    _ ≤ ∑ m ∈ A, ‖modeCoeff (masked B S T) m‖^2 :=
      sum_le_sum fun m hm => pow_le_pow_left₀ hr (mem_filter.mp hm).2 2
    _ ≤ _ := (GB5Variance.finite_bessel A _ hF).trans hh

/-- At smoothing exponent 1/128 the discrepancy exponent is 49/64.
The two powers before logarithm absorption are 81/32 and 127/48. -/
theorem budget_at_49_64 {B : ℕ → Set ℝ} (hm : ∀ Y, MeasurableSet (B Y))
    {D : ℕ → ℝ} {C : ℝ} (hC : 0 ≤ C) (k : ℕ)
    (hD : ∀ᶠ Y : ℕ in Filter.atTop, 0 ≤ D Y ∧
      D Y ≤ (C*(GB6Growth.logFactor Y)^k)*(Y:ℝ)^(49/64:ℝ))
    (hVol : ∀ᶠ Y : ℕ in Filter.atTop, volume.real (B Y ∩ Set.Icc 0 1) ≤
      1024*(Nat.log 2 (Y+2):ℝ)^2*(Y:ℝ)^(-(5/12):ℝ)) :
    ∀ᶠ Y : ℕ in Filter.atTop, budget (B Y) (GB6Var.S Y) (D Y) ≤
      18*(Y:ℝ)^(8/3:ℝ) := by
  have cut (a : ℝ) (ha : 0 ≤ a) (j : ℕ) :=
    GB6Growth.polylog_le_power a ha j (1/512:ℝ) (by norm_num)
  filter_upwards [hD,hVol,cut C hC k,cut 1 (by norm_num) 2,
    cut 1024 (by norm_num) 2,Filter.eventually_ge_atTop (1:ℕ)] with Y hd hv hcd hlog hmeasure hY
  have hY1 : (1:ℝ) ≤ Y := by exact_mod_cast hY
  have hy : 0 < (Y:ℝ) := by linarith
  have hlin : (Y:ℝ)+1 ≤ 2*Y := by linarith
  have hsmall : D Y ≤ (Y:ℝ)^(393/512:ℝ) := by
    refine hd.2.trans ((mul_le_mul_of_nonneg_right hcd (by positivity)).trans_eq ?_)
    rw [← Real.rpow_add hy]; norm_num
  have hvol' : unitMeasure.real (B Y) ≤ (Y:ℝ)^(1/512-5/12:ℝ) := by
    rw [measureReal_restrict_apply (hm Y)]
    have hs : B Y ∩ Set.Ioc (0:ℝ) 1 ⊆ B Y ∩ Set.Icc 0 1 :=
      Set.inter_subset_inter_right _ Set.Ioc_subset_Icc_self
    have hfin : volume (B Y ∩ Set.Icc (0:ℝ) 1) ≠ ⊤ :=
      ne_top_of_le_ne_top (measure_Icc_lt_top.ne) (measure_mono Set.inter_subset_right)
    apply (measureReal_mono hs hfin).trans
    apply hv.trans
    have hlc : (Nat.log 2 (Y+2):ℝ)^2 ≤ (GB6Growth.logFactor Y)^2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) (GB6Growth.L_le_logFactor Y) 2
    have hav := (mul_le_mul_of_nonneg_left hlc (by norm_num : (0:ℝ) ≤ 1024)).trans hmeasure
    refine (mul_le_mul_of_nonneg_right hav (by positivity)).trans_eq ?_
    rw [← Real.rpow_add hy]; congr 1
  have hlog0 : 0 ≤ 1+Real.log ((Y:ℝ)+2) := by
    linarith [Real.log_nonneg (show 1 ≤ (Y:ℝ)+2 by linarith)]
  have hlog' : (1+Real.log ((Y:ℝ)+2))^2 ≤ (Y:ℝ)^(1/512:ℝ) :=
    (pow_le_pow_left₀ hlog0 (GB6Growth.log_le_logFactor Y) 2).trans (by simpa using hlog)
  have h2 := pow_le_pow_left₀ hd.1 hsmall 2
  have h4 := pow_le_pow_left₀ hd.1 hsmall 4
  rw [← Real.rpow_mul_natCast hy.le] at h2 h4
  have h1 : (D Y)^2*(((Y:ℝ)+1)*(1+Real.log ((Y:ℝ)+2))^2) ≤ 2*(Y:ℝ)^(8/3:ℝ) := by
    refine (mul_le_mul h2 (mul_le_mul hlin hlog' (sq_nonneg _) (by positivity))
      (by positivity) (by positivity)).trans ?_
    calc
      _ = 2*((Y:ℝ)^((393/512:ℝ)*(2:ℕ))*(Y:ℝ)^(1/512:ℝ)*(Y:ℝ)) := by ring
      _ = 2*(Y:ℝ)^(((393/512:ℝ)*(2:ℕ)+1/512)+1) := by
        rw [Real.rpow_add_one hy.ne',Real.rpow_add hy]
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hY1 (by norm_num)) (by norm_num)
  have htail : (D Y)^4*unitMeasure.real (B Y) ≤ (Y:ℝ)^(8/3:ℝ) := by
    refine (mul_le_mul h4 hvol' (by positivity) (by positivity)).trans ?_
    rw [← Real.rpow_add hy]
    apply Real.rpow_le_rpow_of_exponent_le hY1; norm_num
  apply (prime_budget (B Y) Y (D Y)).trans
  linarith only [h1,htail]

end
end Goldbach.CanonicalPerturbation
