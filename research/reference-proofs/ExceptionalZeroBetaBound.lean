import Mathlib

/-! The beta factor in Pintz's explicit formula for Goldbach numbers,
arXiv:1804.09084, equations (2.19)–(2.21). Interpolation between the
constant density and the arcsine density makes the error explicit and
uniform in both imaginary parts. -/

namespace Conjectures.Goldbach.ExceptionalZeroBetaBound

open Complex MeasureTheory Filter
open scoped Topology

noncomputable section

private def kernel (z w : ℂ) (x : ℝ) : ℂ := (x : ℂ)^(z-1)*(1-(x : ℂ))^(w-1)
private def half : ℂ := 1/2
private def arcsine (x : ℝ) := x^(-(1/2 : ℝ))*(1-x)^(-(1/2 : ℝ))

private theorem kernel_half {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    kernel half half x = (arcsine x : ℂ) := by
  have h : half-1 = ((-(1/2 : ℝ) : ℝ) : ℂ) := by norm_num [half]
  dsimp only [kernel,arcsine]
  rw [Complex.ofReal_mul,Complex.ofReal_cpow h0,Complex.ofReal_cpow (sub_nonneg.mpr h1),
    Complex.ofReal_sub,Complex.ofReal_one,h]

private theorem norm_half {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    ‖kernel half half x‖ = arcsine x := by
  rw [kernel_half h0 h1,Complex.norm_real, Real.norm_eq_abs,abs_of_nonneg]
  exact mul_nonneg (Real.rpow_nonneg h0 _) (Real.rpow_nonneg (sub_nonneg.mpr h1) _)

private theorem half_integral : (∫ x in (0 : ℝ)..1, ‖kernel half half x‖) = Real.pi := by
  have hh : 0 < half.re := by norm_num [half,Complex.div_re]
  have hvalue : Complex.betaIntegral half half = (Real.pi : ℂ) := by
    rw [Complex.betaIntegral_eq_Gamma_mul_div _ _ hh hh,show half+half=1 by norm_num [half],
      Complex.Gamma_one,div_one]
    have hg : Complex.Gamma half = ((Real.sqrt Real.pi : ℝ) : ℂ) := by
      have he : half = ((1/2:ℝ) : ℂ) := by norm_num [half]
      rw [he,Complex.Gamma_ofReal,Real.Gamma_one_half_eq]
    rw [hg,← Complex.ofReal_mul,Real.mul_self_sqrt Real.pi_pos.le]
  apply Complex.ofReal_injective
  calc
    _ = ∫ x in (0:ℝ)..1, (‖kernel half half x‖ : ℂ) := intervalIntegral.integral_ofReal.symm
    _ = Complex.betaIntegral half half := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ)≤1)] at hx
      change (‖kernel half half x‖ : ℂ) = kernel half half x
      rw [norm_half hx.1 hx.2,kernel_half hx.1 hx.2]
    _ = _ := hvalue

private theorem pointwise {δ x : ℝ} {z w : ℂ} (hδ : 0 ≤ δ) (hδ' : δ ≤ 1/2)
    (hz : 1-δ ≤ z.re) (hw : 1-δ ≤ w.re) (h0 : 0 < x) (h1 : x < 1) :
    ‖kernel z w x‖ ≤ 1-2*δ+2*δ*‖kernel half half x‖ := by
  have h0' : 0 < 1-x := sub_pos.mpr h1
  have h1' : 1-x ≤ 1 := by linarith
  have hk : 0 ≤ arcsine x := mul_nonneg (Real.rpow_nonneg h0.le _)
    (Real.rpow_nonneg h0'.le _)
  have hg := Real.geom_mean_le_arith_mean2_weighted (show 0 ≤ 1-2*δ by linarith)
    (show 0 ≤ 2*δ by linarith) (by norm_num : (0:ℝ) ≤ 1) hk (by ring)
  rw [Real.one_rpow,one_mul,mul_one] at hg
  rw [norm_half h0.le h1.le]
  refine le_trans ?_ hg
  rw [kernel,norm_mul,← Complex.ofReal_one,← Complex.ofReal_sub,
    Complex.norm_cpow_eq_rpow_re_of_pos h0,Complex.norm_cpow_eq_rpow_re_of_pos h0']
  simp only [Complex.sub_re]
  have hs : x^(z.re-1)*(1-x)^(w.re-1) ≤ x^(-δ)*(1-x)^(-δ) :=
    mul_le_mul (Real.rpow_le_rpow_of_exponent_ge h0 h1.le (by linarith only [hz]))
      (Real.rpow_le_rpow_of_exponent_ge h0' h1' (by linarith only [hw]))
      (Real.rpow_nonneg h0'.le _) (Real.rpow_nonneg h0.le _)
  refine hs.trans_eq ?_
  dsimp only [arcsine]
  rw [Real.mul_rpow (Real.rpow_nonneg h0.le _) (Real.rpow_nonneg h0'.le _),
    ← Real.rpow_mul h0.le, ← Real.rpow_mul h0'.le]
  ring_nf

/-- Explicit uniform replacement for the asymptotic beta-factor estimate. -/
theorem gamma_ratio {δ : ℝ} {z w : ℂ} (hδ : 0 ≤ δ) (hδ' : δ ≤ 1/2)
    (hz : 1-δ ≤ z.re) (hw : 1-δ ≤ w.re) :
    ‖Complex.Gamma z*Complex.Gamma w/Complex.Gamma (z+w)‖ ≤ 1+2*(Real.pi-1)*δ := by
  have hz' : 0 < z.re := by linarith
  have hw' : 0 < w.re := by linarith
  have hh : 0 < half.re := by norm_num [half,Complex.div_re]
  have hk : IntervalIntegrable (kernel half half) volume 0 1 := Complex.betaIntegral_convergent hh hh
  have hk' : IntervalIntegrable (kernel z w) volume 0 1 := Complex.betaIntegral_convergent hz' hw'
  rw [← Complex.betaIntegral_eq_Gamma_mul_div _ _ hz' hw']
  calc
    _ ≤ ∫ x in (0:ℝ)..1, ‖kernel z w x‖ := intervalIntegral.norm_integral_le_integral_norm zero_le_one
    _ ≤ ∫ x in (0:ℝ)..1, (1-2*δ+2*δ*‖kernel half half x‖) :=
      intervalIntegral.integral_mono_on_of_le_Ioo zero_le_one hk'.norm
        (intervalIntegrable_const.add (hk.norm.const_mul _)) (fun _ h =>
          pointwise hδ hδ' hz hw h.1 h.2)
    _ = _ := by
      rw [intervalIntegral.integral_add intervalIntegrable_const (hk.norm.const_mul _),
        intervalIntegral.integral_const,intervalIntegral.integral_const_mul,half_integral]
      simp only [sub_zero,one_smul]
      ring

/-- Apply the uniform gamma bound to the full complex secondary sum,
preserving each zero's individual horizontal distance from 1. -/
theorem secondary_floor (δ s m : ℝ) (P : Finset (ℕ×ℕ)) (z : ℕ → ℂ)
    (a : ℕ×ℕ → ℂ) (err : ℂ) (hδ : 0 ≤ δ) (hδ' : δ ≤ 1/2)
    (hs : 0 ≤ s) (hm : 0 < m)
    (hab : ∀ p ∈ P, ‖a p‖ ≤ s ∧ 1-δ ≤ (z p.1).re ∧ 1-δ ≤ (z p.2).re) :
    s*m*(1-(1+2*(Real.pi-1)*δ)*
      ∑ p ∈ P, m^((z p.1).re-1)*m^((z p.2).re-1))-‖err‖ ≤
    ((s*m : ℝ)+ (∑ p ∈ P, a p*(Complex.Gamma (z p.1)*Complex.Gamma (z p.2)/
      Complex.Gamma (z p.1+z p.2))*(m : ℂ)^(z p.1+z p.2-1))+err : ℂ).re := by
  let A := 1+2*(Real.pi-1)*δ
  have hA : 0 ≤ A := by
    dsimp [A]
    exact add_nonneg zero_le_one (mul_nonneg (mul_nonneg (by norm_num)
      (by linarith only [Real.pi_gt_three])) hδ)
  let d := fun i : ℕ => m^((z i).re-1)
  let c := fun p : ℕ×ℕ => a p*(Complex.Gamma (z p.1)*Complex.Gamma (z p.2)/
    Complex.Gamma (z p.1+z p.2))*(m : ℂ)^(z p.1+z p.2-1)
  have hz (p : ℕ×ℕ) : ‖(m:ℂ)^(z p.1+z p.2-1)‖ = m*(d p.1*d p.2) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hm,Complex.sub_re,Complex.add_re,Complex.one_re]
    dsimp [d]
    rw [← Real.rpow_add hm,show (z p.1).re+(z p.2).re-1 =
      1+(((z p.1).re-1)+((z p.2).re-1)) by ring,Real.rpow_add hm,Real.rpow_one]
  have hu : ‖∑ p ∈ P, c p‖ ≤ (s*m*A)*(∑ p ∈ P, d p.1*d p.2) := calc
    _ ≤ ∑ p ∈ P, ‖c p‖ := norm_sum_le _ _
    _ ≤ ∑ p ∈ P, (s*m*A)*(d p.1*d p.2) := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨ha,hz₁,hz₂⟩ := hab p hp
      dsimp only [c]
      rw [norm_mul,norm_mul,hz]
      have h := mul_le_mul ha (gamma_ratio hδ hδ' hz₁ hz₂) (norm_nonneg _) hs
      have hpos : 0 ≤ m*(d p.1*d p.2) := by dsimp [d]; positivity
      exact (mul_le_mul_of_nonneg_right h hpos).trans_eq (by dsimp [A];ring)
    _ = _ := (Finset.mul_sum _ _ _).symm
  have hr := (abs_le.mp (Complex.abs_re_le_norm (∑ p ∈ P,c p))).1
  have he := (abs_le.mp (Complex.abs_re_le_norm err)).1
  change s*m*(1-A*(∑ p ∈ P,d p.1*d p.2))-‖err‖ ≤
    (((s*m : ℝ) : ℂ)+(∑ p ∈ P,c p)+err).re
  simp only [Complex.add_re,Complex.ofReal_re]
  linarith only [hu,hr,he]

end
end Conjectures.Goldbach.ExceptionalZeroBetaBound

open Conjectures.Goldbach.ExceptionalZeroBetaBound in
theorem Conjectures.Goldbach.ExceptionalZeroBetaBound :
    (∀ (δ : ℝ) (z w : ℂ), 0 ≤ δ → δ ≤ 1/2 → 1-δ ≤ z.re → 1-δ ≤ w.re →
      ‖Complex.Gamma z*Complex.Gamma w/Complex.Gamma (z+w)‖ ≤ 1+2*(Real.pi-1)*δ) ∧
    (∀ (δ s m : ℝ) (P : Finset (ℕ×ℕ)) (z : ℕ → ℂ) (a : ℕ×ℕ → ℂ) (err : ℂ),
      0 ≤ δ → δ ≤ 1/2 → 0 ≤ s → 0 < m →
      (∀ p ∈ P, ‖a p‖ ≤ s ∧ 1-δ ≤ (z p.1).re ∧ 1-δ ≤ (z p.2).re) →
      s*m*(1-(1+2*(Real.pi-1)*δ)*(∑ p ∈ P,m^((z p.1).re-1)*m^((z p.2).re-1)))-‖err‖ ≤
        (((s*m : ℝ) : ℂ)+(∑ p ∈ P,a p*(Complex.Gamma (z p.1)*Complex.Gamma (z p.2)/
          Complex.Gamma (z p.1+z p.2))*(m : ℂ)^(z p.1+z p.2-1))+err).re) :=
  ⟨fun _ _ _ => gamma_ratio, secondary_floor⟩
