import Mathlib
import PEqualNP.Outside.L_goldbach_arc_major_floor
import Conjectures.Goldbach.ExceptionFourSeventhsCountingBridge
import Conjectures.Goldbach.FiniteMajorRescaledIntervalKernel
import Conjectures.Goldbach.FiniteMajorSincMass
import Conjectures.Goldbach.ReflectedMeanSquareEulerTail

namespace GoldbachRawKernel

open Finset MeasureTheory
open GoldbachMajorArc
open Conjectures.Goldbach.FiniteMajorSincMass_aux (sinc_sq_nonneg sinc_sq_le_one
  sinc_sq_even sinc_sq_integrable)
open scoped Interval

noncomputable section

/-- The rescaled symmetric sinc mass. -/
def profile (h : ℝ) : ℝ :=
  ∫ t in -h..h, Real.sinc (Real.pi*t)^2

theorem profile_bounds (h : ℝ) (hh : 0 ≤ h) : 0 ≤ profile h ∧ profile h ≤ 1 := by
  rcases hh.eq_or_lt with hzero | hpos
  · simp [profile, ← hzero]
  · have hmain := Conjectures.Goldbach.FiniteMajorSincMass h hpos
    exact ⟨hmain.1, hmain.2.1⟩

private theorem profile_eq_twice (h : ℝ) :
    profile h = 2*(∫ t in (0:ℝ)..h, Real.sinc (Real.pi*t)^2) := by
  let f (t : ℝ) := Real.sinc (Real.pi*t)^2
  have hf : Integrable f := sinc_sq_integrable
  have hneg : (∫ t in -h..(0:ℝ), f t) = ∫ t in (0:ℝ)..h, f t := by
    calc
      (∫ t in -h..(0:ℝ), f t) = ∫ t in -h..(0:ℝ), f (-t) := by
        simp only [f, sinc_sq_even]
      _ = _ := by rw [intervalIntegral.integral_comp_neg, neg_zero, neg_neg]
  change (∫ t in -h..h, f t) = _
  rw [← intervalIntegral.integral_add_adjacent_intervals
      (hf.intervalIntegrable : IntervalIntegrable f volume (-h) 0)
      (hf.intervalIntegrable : IntervalIntegrable f volume 0 h), hneg, two_mul]

/-- The annular change is twice the mass of the positive interval. -/
theorem profile_sub_eq (h k : ℝ) :
    profile k - profile h = 2*(∫ t in h..k, Real.sinc (Real.pi*t)^2) := by
  let f (t : ℝ) := Real.sinc (Real.pi*t)^2
  have hf : Integrable f := sinc_sq_integrable
  rw [profile_eq_twice k, profile_eq_twice h]
  change 2*(∫ t in (0:ℝ)..k, f t) - 2*(∫ t in (0:ℝ)..h, f t) = _
  rw [← intervalIntegral.integral_add_adjacent_intervals
      (hf.intervalIntegrable : IntervalIntegrable f volume 0 h)
      (hf.intervalIntegrable : IntervalIntegrable f volume h k)]
  ring

theorem profile_sub_bounds {h k : ℝ} (hk : h ≤ k) :
    0 ≤ profile k - profile h ∧ profile k - profile h ≤ 2*(k-h) := by
  let f (t : ℝ) := Real.sinc (Real.pi*t)^2
  have hf : Integrable f := sinc_sq_integrable
  rw [profile_sub_eq]
  constructor
  · exact mul_nonneg (by norm_num)
      (intervalIntegral.integral_nonneg hk fun t _ => sinc_sq_nonneg t)
  · have hmono := intervalIntegral.integral_mono_on hk (hf.intervalIntegrable : IntervalIntegrable f volume h k)
      (intervalIntegrable_const (c := (1:ℝ))) (fun t _ => sinc_sq_le_one t)
    have h' : (∫ t in h..k, f t) ≤ k-h := by simpa using hmono
    exact mul_le_mul_of_nonneg_left h' (by norm_num)

private theorem phase_add (u v : ℝ) : phase (u+v) = phase u * phase v := by
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem shifted_kernel_norm (n : ℕ) (t : ℝ) :
    ‖∑ k ∈ Icc 1 (n+1), phase ((k:ℝ)*t)‖ = ‖kernel n t‖ := by
  have h :
      (∑ k ∈ Icc 1 (n+1), phase ((k:ℝ)*t)) =
        phase t * kernel n t := by
    calc
      _ = ∑ k ∈ range (n+1), phase (((k+1:ℕ):ℝ)*t) := by
        symm
        refine sum_bij' (fun k _ => k+1) (fun k _ => k-1) ?_ ?_ ?_ ?_ ?_
        · intro k hk
          exact mem_Icc.mpr ⟨by omega, by have := mem_range.mp hk; omega⟩
        · intro k hk
          have := mem_Icc.mp hk
          exact mem_range.mpr (by omega)
        · intro k hk
          omega
        · intro k hk
          have := (mem_Icc.mp hk).1
          omega
        · intro k _
          rfl
      _ = _ := by
        rw [kernel, mul_sum]
        apply sum_congr rfl
        intro k _
        rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_comm, phase_add]
  rw [h, norm_mul, show ‖phase t‖ = 1 from Complex.norm_exp_ofReal_mul_I _, one_mul]

/-- Compare the published geometric kernel to the same sinc profile at fixed width. -/
theorem kernel_mass_error (n q Q : ℕ) (hn : 0 < n) (hq : 0 < q) :
    |kernelMass n ((Q:ℝ)/((q:ℝ)*(n:ℝ))) - ((n:ℝ)+1)*profile ((Q:ℝ)/(q:ℝ))| ≤
      (16*Real.pi+2)*((Q:ℝ)+1)^2 := by
  let N := n+1
  let K : ℝ := (Q:ℝ)/(q:ℝ)
  let H : ℝ := K*(N:ℝ)/(n:ℝ)
  let b : ℝ := (Q:ℝ)/((q:ℝ)*(n:ℝ))
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  have hnR₁ : 1 ≤ (n:ℝ) := by exact_mod_cast hn
  have hqR : 0 < (q:ℝ) := by exact_mod_cast hq
  have hqR₁ : 1 ≤ (q:ℝ) := by exact_mod_cast hq
  have hN0 : 0 < N := by dsimp [N]; omega
  have hNpos : 0 < (N:ℝ) := by exact_mod_cast hN0
  have hNcast : (N:ℝ) = (n:ℝ)+1 := by simp [N]
  have hNle : (N:ℝ) ≤ 2*(n:ℝ) := by rw [hNcast]; linarith only [hnR₁]
  have hK0 : 0 ≤ K := by dsimp [K]; positivity
  have hKQ : K ≤ (Q:ℝ) := div_le_self (by positivity) hqR₁
  have hH0 : 0 ≤ H := by dsimp [H]; positivity
  have hHb : H/(N:ℝ) = b := by
    dsimp [H,b,K]
    field_simp [hnR.ne', hqR.ne', hNpos.ne']
  have hHsub : H-K = K/(n:ℝ) := by
    dsimp only [H]
    rw [hNcast]
    field_simp [hnR.ne']
    ring
  have hHK : K ≤ H := sub_nonneg.mp (by rw [hHsub]; positivity)
  have hHle : H ≤ 2*K := by
    apply (div_le_iff₀ hnR).mpr
    calc
      K*(N:ℝ) ≤ K*(2*(n:ℝ)) := mul_le_mul_of_nonneg_left hNle hK0
      _ = _ := by ring
  have hHRQ : H ≤ 2*(Q:ℝ) :=
    hHle.trans (mul_le_mul_of_nonneg_left hKQ (by norm_num))
  have hres := (Conjectures.Goldbach.FiniteMajorRescaledIntervalKernel N H hN0 hH0).2.2
  change |(∫ t in -(H/(N:ℝ))..H/(N:ℝ),
      ‖∑ k ∈ Icc 1 N, phase ((k:ℝ)*t)‖^2)/(N:ℝ) - profile H| ≤ _ at hres
  simp_rw [show ∀ t : ℝ, ‖∑ k ∈ Icc 1 N, phase ((k:ℝ)*t)‖ = ‖kernel n t‖
    from shifted_kernel_norm n] at hres
  rw [hHb] at hres
  change |kernelMass n b/(N:ℝ) - profile H| ≤ 4*Real.pi*H^2/(N:ℝ) at hres
  have he : kernelMass n b/(N:ℝ) - profile H =
      (kernelMass n b - (N:ℝ)*profile H)/(N:ℝ) := by
    field_simp [hNpos.ne']
  rw [he, abs_div, abs_of_pos hNpos] at hres
  have hscaled : |kernelMass n b - (N:ℝ)*profile H| ≤ 4*Real.pi*H^2 :=
    (div_le_div_iff_of_pos_right hNpos).mp hres
  have hscaled' : |kernelMass n b - (N:ℝ)*profile H| ≤ 16*Real.pi*(Q:ℝ)^2 := by
    apply hscaled.trans
    calc
      _ ≤ 4*Real.pi*(2*(Q:ℝ))^2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hH0 hHRQ 2) (by positivity)
      _ = _ := by ring
  have hProfile : (N:ℝ)*|profile H-profile K| ≤ 4*(Q:ℝ) := by
    have hp := profile_sub_bounds hHK
    have hNdiv : (N:ℝ)/(n:ℝ) ≤ 2 := (div_le_iff₀ hnR).mpr hNle
    rw [abs_of_nonneg hp.1]
    calc
      _ ≤ (N:ℝ)*(2*(H-K)) := mul_le_mul_of_nonneg_left hp.2 hNpos.le
      _ = (2*K)*((N:ℝ)/(n:ℝ)) := by rw [hHsub]; ring
      _ ≤ (2*K)*2 := mul_le_mul_of_nonneg_left hNdiv (by positivity)
      _ = 4*K := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hKQ (by norm_num)
  have htri := abs_sub_le (kernelMass n b) ((N:ℝ)*profile H) ((N:ℝ)*profile K)
  rw [← mul_sub, abs_mul, abs_of_pos hNpos] at htri
  change |kernelMass n b - ((n:ℝ)+1)*profile K| ≤ _
  rw [← hNcast]
  have hsum := htri.trans (add_le_add hscaled' hProfile)
  apply hsum.trans
  have hQ0 : 0 ≤ (Q:ℝ) := by positivity
  have hdiff : (Q:ℝ)^2 ≤ ((Q:ℝ)+1)^2 := by nlinarith only [hQ0]
  have hpi := mul_le_mul_of_nonneg_left hdiff (show 0 ≤ 16*Real.pi by positivity)
  nlinarith only [hpi, sq_nonneg (Q:ℝ)]

private theorem integral_sine_sq_nat (a b : ℕ) :
    (∫ t in (a:ℝ)..(b:ℝ), Real.sin (Real.pi*t)^2) = ((b:ℝ)-a)/2 := by
  rw [intervalIntegral.integral_comp_mul_left (fun x : ℝ => Real.sin x ^ 2)
    Real.pi_ne_zero, integral_sin_sq]
  rw [mul_comm Real.pi (a:ℝ), mul_comm Real.pi (b:ℝ),
    Real.sin_nat_mul_pi, Real.sin_nat_mul_pi]
  simp only [zero_mul, sub_self, zero_add, smul_eq_mul]
  field_simp [Real.pi_ne_zero]

/-- The missing sinc mass between the denominator-one and denominator-two widths. -/
theorem profile_gap (Q : ℕ) (hQ : 2 ≤ Q) (he : Even Q) :
    (1/(4*Real.pi^2))/(Q:ℝ) ≤ profile (Q:ℝ) - profile ((Q:ℝ)/2) := by
  obtain ⟨k,hk⟩ := he
  have hhalf : (Q:ℝ)/2 = (k:ℝ) := by rw [hk, Nat.cast_add]; ring
  have hQpos : 0 < (Q:ℝ) := by exact_mod_cast (show 0 < Q by omega)
  have hhalfpos : 0 < (Q:ℝ)/2 := by positivity
  have hle : (Q:ℝ)/2 ≤ (Q:ℝ) := by linarith only [hQpos]
  let G (t : ℝ) := Real.sin (Real.pi*t)^2/(Real.pi*(Q:ℝ))^2
  let F (t : ℝ) := Real.sinc (Real.pi*t)^2
  have hG : Continuous G := by dsimp [G]; fun_prop
  have hF : Integrable F := sinc_sq_integrable
  have hgf : (∫ t in (Q:ℝ)/2..(Q:ℝ), G t) ≤ ∫ t in (Q:ℝ)/2..(Q:ℝ), F t := by
    apply intervalIntegral.integral_mono_on hle (hG.intervalIntegrable ..) (hF.intervalIntegrable)
    intro t ht
    have htpos := hhalfpos.trans_le ht.1
    have htp : 0 < Real.pi*t := mul_pos Real.pi_pos htpos
    have hh : Real.pi*t ≤ Real.pi*(Q:ℝ) := mul_le_mul_of_nonneg_left ht.2 Real.pi_pos.le
    unfold G F
    rw [Real.sinc_of_ne_zero htp.ne', div_pow]
    exact div_le_div_of_nonneg_left (sq_nonneg _) (sq_pos_of_pos htp)
      (pow_le_pow_left₀ htp.le hh 2)
  have hsin :
      (∫ t in (Q:ℝ)/2..(Q:ℝ), Real.sin (Real.pi*t)^2) = (Q:ℝ)/4 := by
    rw [hhalf, integral_sine_sq_nat, ← hhalf]
    ring
  have hval : (∫ t in (Q:ℝ)/2..(Q:ℝ), G t) = (1/(4*Real.pi^2))/(Q:ℝ) := by
    rw [show (∫ t in (Q:ℝ)/2..(Q:ℝ), G t) =
        (∫ t in (Q:ℝ)/2..(Q:ℝ), Real.sin (Real.pi*t)^2)/(Real.pi*(Q:ℝ))^2 by
          unfold G; exact intervalIntegral.integral_div _ _]
    rw [hsin]
    field_simp [Real.pi_ne_zero, hQpos.ne']
  rw [hval] at hgf
  rw [profile_sub_eq]
  change _ ≤ 2*(∫ t in (Q:ℝ)/2..(Q:ℝ), F t)
  have hn : 0 ≤ ∫ t in (Q:ℝ)/2..(Q:ℝ), F t :=
    intervalIntegral.integral_nonneg hle (fun t _ => sinc_sq_nonneg t)
  linarith only [hgf,hn]

end
end GoldbachRawKernel

/-! The coefficient periodicity, zero sums along a progression, and coefficient
norm bound are from the checked reflected mean-square proof, PR 4435. -/

namespace GoldbachRawCancellation

open Finset

private theorem prefix_bound (g : ℕ → ℂ) (q L : ℕ) (hq : 0 < q)
    (hperiod : ∀ j, g (j+q) = g j)
    (hzero : ∑ j ∈ range q, g j = 0) (hnorm : ∀ j, ‖g j‖ ≤ 1) :
    ‖∑ j ∈ range L, g j‖ ≤ (q : ℝ) := by
  have hshift (k j : ℕ) : g (k*q+j) = g j := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.succ_mul, show k*q+q+j = (k*q+j)+q by omega, hperiod, ih]
  have hblocks (k : ℕ) : (∑ j ∈ range (k*q), g j) = 0 := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.succ_mul, sum_range_add, ih, zero_add]
      simpa only [hshift k] using hzero
  have hL : (L/q)*q + L % q = L := by simpa only [Nat.mul_comm] using Nat.div_add_mod L q
  have hsmall : ((L % q : ℕ) : ℝ) ≤ q := by exact_mod_cast (Nat.mod_lt L hq).le
  have hrem : (∑ j ∈ range L, g j) = ∑ j ∈ range (L % q), g j := by
    conv_lhs => rw [← hL, sum_range_add, hblocks, zero_add]
    simp only [hshift]
  rw [hrem]
  calc
    _ ≤ ∑ j ∈ range (L % q), ‖g j‖ := norm_sum_le _ _
    _ ≤ ∑ _j ∈ range (L % q), (1 : ℝ) := sum_le_sum (fun j _ => hnorm j)
    _ = ((L % q : ℕ) : ℝ) := by simp
    _ ≤ _ := hsmall

theorem coefficient_norm (q n : ℕ) (hq : 0 < q) :
    ‖GoldbachMajorArc.coefficient q n‖ ≤ 1 :=
  ProgressionSums.coefficient_norm q n hq

/-- Without the constant or order-two mode, the affine weighted sum of a
progression has only a boundary-sized contribution. -/
theorem affine_bound (q b L : ℕ) (hq : 2 < q) :
    ‖∑ j ∈ range L, (((b+2*j : ℕ) : ℂ)+1)*GoldbachMajorArc.coefficient q (b+2*j)‖ ≤
      ((b : ℝ)+4*(L : ℝ)+1)*(q : ℝ) := by
  let g (j : ℕ) := GoldbachMajorArc.coefficient q (b+2*j)
  let f (j : ℕ) : ℝ := (b : ℝ)+2*(j : ℝ)+1
  let G (j : ℕ) : ℂ := ∑ i ∈ range j, g i
  have hq₀ : 0 < q := by omega
  have hperiod (j : ℕ) : g (j+q) = g j := by
    change GoldbachMajorArc.coefficient q (b+2*(j+q)) = GoldbachMajorArc.coefficient q (b+2*j)
    rw [show b+2*(j+q) = (b+2*j)+q*2 by ring]
    exact ProgressionZero.coefficient_period_mul q (b+2*j) 2 hq₀
  have hzero : (∑ j ∈ range q, g j) = 0 :=
    ProgressionZero.coefficient_sum_zero q b 2 hq₀ (Nat.not_dvd_of_pos_of_lt (by decide) hq)
  have hG (j : ℕ) : ‖G j‖ ≤ (q : ℝ) :=
    prefix_bound g q j hq₀ hperiod hzero (fun i => coefficient_norm q (b+2*i) hq₀)
  have hslope (j : ℕ) : f (j+1)-f j = 2 := by
    unfold f
    push_cast
    ring
  have hweight : (∑ j ∈ range L, (((b+2*j : ℕ) : ℂ)+1) * GoldbachMajorArc.coefficient q (b+2*j)) =
      ∑ j ∈ range L, f j • g j := by
    apply sum_congr rfl
    intro j _
    rw [Complex.real_smul]
    unfold f g
    push_cast
    rfl
  have hende : ‖f (L-1) • G L‖ ≤ ((b : ℝ)+2*(L : ℝ)+1)*(q : ℝ) := by
    have hf : 0 ≤ f (L-1) := by unfold f; positivity
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hf]
    refine mul_le_mul ?_ (hG L) (norm_nonneg _) (by positivity)
    have hL : ((L-1 : ℕ) : ℝ) ≤ L := by exact_mod_cast Nat.sub_le L 1
    unfold f
    linarith only [hL]
  have hrem : ‖∑ j ∈ range (L-1), (2 : ℝ) • G (j+1)‖ ≤ 2*(L : ℝ)*(q : ℝ) := by
    calc
      _ ≤ ∑ j ∈ range (L-1), ‖(2 : ℝ) • G (j+1)‖ := norm_sum_le _ _
      _ ≤ ∑ _j ∈ range (L-1), 2*(q : ℝ) := by
        apply sum_le_sum
        intro j _
        rw [norm_smul, show ‖(2 : ℝ)‖ = 2 by norm_num]
        exact mul_le_mul_of_nonneg_left (hG (j+1)) (by norm_num)
      _ = ((L-1 : ℕ) : ℝ) * (2*(q : ℝ)) := by simp [sum_const, nsmul_eq_mul]
      _ ≤ (L : ℝ) * (2*(q : ℝ)) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le L 1) (by positivity)
      _ = _ := by ring
  rw [hweight, sum_range_by_parts]
  change ‖f (L-1) • G L - ∑ j ∈ range (L-1), (f (j+1)-f j) • G (j+1)‖ ≤ _
  simp_rw [hslope]
  calc
    _ ≤ ‖f (L-1) • G L‖ + ‖∑ j ∈ range (L-1), (2 : ℝ) • G (j+1)‖ := norm_sub_le _ _
    _ ≤ ((b : ℝ)+2*(L : ℝ)+1)*(q : ℝ) + 2*(L : ℝ)*(q : ℝ) := add_le_add hende hrem
    _ = _ := by ring

theorem odd_bound (X q : ℕ) (hX : 2 ≤ X) (hq : 2 < q) :
    ‖∑ j ∈ range (X/2-1), (((X+1+2*j : ℕ) : ℂ)+1) *
      GoldbachMajorArc.coefficient q (X+1+2*j)‖ ≤ 3*(X : ℝ)*(q : ℝ) := by
  refine (affine_bound q (X+1) (X/2-1) hq).trans ?_
  apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg q)
  have hL : X+1+4*(X/2-1)+1 ≤ 3*X := by omega
  exact_mod_cast hL


theorem odd_higher_bound (X Q : ℕ) (hX : 2 ≤ X) (K : ℕ → ℂ)
    (hK : ∀ q ∈ Icc 3 Q, ‖K q‖ ≤ 1) :
    ‖∑ q ∈ Icc 3 Q, K q * (∑ j ∈ range (X/2-1), (((X+1+2*j : ℕ) : ℂ)+1) *
      GoldbachMajorArc.coefficient q (X+1+2*j))‖ ≤ 3*(X : ℝ)*(Q : ℝ)^2 := by
  let A (q : ℕ) := ∑ j ∈ range (X/2-1), (((X+1+2*j : ℕ) : ℂ)+1) *
    GoldbachMajorArc.coefficient q (X+1+2*j)
  have hcard : ((Icc 3 Q).card : ℝ) ≤ Q := by
    exact_mod_cast (show (Icc 3 Q).card ≤ Q by rw [Nat.card_Icc]; omega)
  change ‖∑ q ∈ Icc 3 Q, K q * A q‖ ≤ _
  calc
    _ ≤ ∑ q ∈ Icc 3 Q, ‖K q * A q‖ := norm_sum_le _ _
    _ ≤ ∑ _q ∈ Icc 3 Q, 3*(X : ℝ)*(Q : ℝ) := by
      apply sum_le_sum
      intro q hq
      have hqQ : (q : ℝ) ≤ Q := by exact_mod_cast (mem_Icc.mp hq).2
      rw [norm_mul]
      calc
        _ ≤ 1*(3*(X : ℝ)*(q : ℝ)) :=
          mul_le_mul (hK q hq) (odd_bound X q hX (mem_Icc.mp hq).1) (norm_nonneg _) zero_le_one
        _ ≤ _ := by
          rw [one_mul]
          exact mul_le_mul_of_nonneg_left hqQ (by positivity)
    _ = ((Icc 3 Q).card : ℝ)*(3*(X : ℝ)*(Q : ℝ)) := by simp [sum_const, nsmul_eq_mul]
    _ ≤ (Q : ℝ)*(3*(X : ℝ)*(Q : ℝ)) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by ring

end GoldbachRawCancellation

-- The single-arc estimates and the finite summation below adapt the verified
-- Goldbach major-arc proof in PR 316, released under Apache 2.0.
namespace GoldbachRawError

open GoldbachMajorArc Finset Filter MeasureTheory
open scoped Topology

noncomputable section

private theorem unitMean_norm (q a : ℕ) (hq : 0 < q) : ‖unitMean q a‖ ≤ 1 := by
  let U := (range q).filter (fun r => r.Coprime q)
  have hcard : U.card = q.totient := by
    rw [Nat.totient_eq_card_coprime]
    have h : U = (range q).filter (fun r => q.Coprime r) := by ext k; simp [U, Nat.coprime_comm]
    rw [h]
  have hφ : 0 < (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
  unfold unitMean
  rw [norm_div, Complex.norm_natCast, div_le_one hφ]
  refine (norm_sum_le _ _).trans ?_
  change ∑ r ∈ U, ‖phase ((r : ℝ) * ((a : ℝ) / q))‖ ≤ _
  simp only [phase, Complex.norm_exp_ofReal_mul_I, sum_const, nsmul_eq_mul, mul_one, hcard, le_refl]

private theorem integral_error_bound {n q : ℕ} (hn : 1 ≤ n) (hq : 0 < q) (hQ : q ≤ cutoff n)
    (a : ℕ) {E : ℝ} (hE : 0 ≤ E)
    (hp : prefixError n ((a : ℝ) / q) (unitMean q a) ≤ q * E) :
    (∫ β in -(width n q)..(width n q), modelError n q a β) ≤
      2 * (cutoff n : ℝ) ^ 2 * E * ((1 + 2 * Real.pi) * (Real.log 4 + 2)) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hQ' : (q : ℝ) ≤ cutoff n := by exact_mod_cast hQ
  have npos : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn'
  have qpos : (0 : ℝ) < q := lt_of_lt_of_le zero_lt_one hq'
  let B := E * ((1 + 2 * Real.pi) * (cutoff n : ℝ)) * ((Real.log 4 + 2) * (n : ℝ))
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have wpos : 0 ≤ width n q := by unfold width; positivity
  have hlength : width n q ≤ (cutoff n : ℝ) / n := by
    unfold width
    apply div_le_div_of_nonneg_left (by positivity) npos
    simpa only [one_mul] using (mul_le_mul_of_nonneg_right hq' npos.le)
  have hpoint {β : ℝ} (hβ : β ∈ Set.Icc (-(width n q)) (width n q)) :
      modelError n q a β ≤ B := by
    have hp' := squared_arc_error (a := a) hn hq (abs_le.mpr hβ)
    have hscale :
        prefixError n ((a : ℝ) / q) (unitMean q a) * (1 + 2 * Real.pi * ((cutoff n : ℝ) / q)) ≤
        E * ((1 + 2 * Real.pi) * (cutoff n : ℝ)) := by
      calc
        _ ≤ ((q : ℝ) * E) * (1 + 2 * Real.pi * ((cutoff n : ℝ) / q)) :=
          mul_le_mul_of_nonneg_right hp (by positivity)
        _ = E * ((q : ℝ) + 2 * Real.pi * cutoff n) := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left (by nlinarith only [hQ']) hE
    have hU := unitMean_norm q a hq
    have hcap : Chebyshev.theta n + ‖unitMean q a‖ * (n + 1 : ℕ) ≤ (Real.log 4 + 2) * (n : ℝ) := by
      have hcard := mul_le_mul_of_nonneg_right hU (show 0 ≤ (n : ℝ) + 1 by positivity)
      push_cast
      nlinarith only [Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg n), hcard, hn']
    exact hp'.trans (mul_le_mul hscale hcap (by positivity) (by positivity))
  have hc : Continuous (modelError n q a) := by
    unfold modelError integrand primeSum kernel phase
    fun_prop
  calc
    _ ≤ ∫ _β in -(width n q)..(width n q), B :=
      intervalIntegral.integral_mono_on (by linarith) (hc.intervalIntegrable _ _)
        (by simp) (fun β hβ => hpoint hβ)
    _ = (2 * width n q) * B := by rw [intervalIntegral.integral_const, smul_eq_mul]; ring
    _ ≤ (2 * ((cutoff n : ℝ) / n)) * B :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlength (by norm_num)) hB
    _ = _ := by dsimp [B]; field_simp

/-- The old arc approximation error saves an additional factor of its cutoff. -/
theorem eventually_totalArcError_le {η : ℝ} (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop, totalArcError n ≤ η * (n : ℝ) / (cutoff n : ℝ) := by
  obtain ⟨M, hM, hpre⟩ := uniform_prefix_error
  let C : ℝ := 4 * ((1 + 2 * Real.pi) * (Real.log 4 + 2))
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hlimit := (envelope_saving M).const_mul (C * 16 ^ 5)
  simp only [mul_zero] at hlimit
  filter_upwards [hpre, eventually_ge_atTop (2 : ℕ), hlimit.eventually_lt_const hη]
    with n hp hn hsmall
  have hn1 : 1 ≤ n := by omega
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hQ1 : 1 ≤ cutoff n := GoldbachMajorArc.cutoff_positive n
  have hQ' : (1 : ℝ) ≤ cutoff n := by exact_mod_cast hQ1
  have hQpos : 0 < (cutoff n : ℝ) := zero_lt_one.trans_le hQ'
  have hE : 0 ≤ errorEnvelope M n := by unfold errorEnvelope; positivity
  let B : ℝ := 2 * (cutoff n : ℝ) ^ 2 * errorEnvelope M n * ((1 + 2 * Real.pi) * (Real.log 4 + 2))
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have htot : totalArcError n ≤ C * (cutoff n : ℝ) ^ 4 * errorEnvelope M n := by
    unfold totalArcError
    calc
      _ ≤ ∑ _q ∈ Icc 1 (cutoff n), (((cutoff n : ℝ) + 1) * B) := by
        refine sum_le_sum fun q hq => ?_
        have hq' := mem_Icc.mp hq
        calc
          _ ≤ ∑ _a ∈ range (q + 1), B := sum_le_sum fun a _ =>
            integral_error_bound hn1 hq'.1 hq'.2 a hE (hp q a hq'.1 hq'.2)
          _ = ((q : ℝ) + 1) * B := by simp
          _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.add_le_add_right hq'.2 1) hB
      _ = (cutoff n : ℝ) * (((cutoff n : ℝ) + 1) * B) := by simp [Nat.card_Icc]
      _ ≤ (cutoff n : ℝ) * ((2 * (cutoff n : ℝ)) * B) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by linarith) hB) hQpos.le
      _ = _ := by dsimp [B, C]; ring
  have hpow : (cutoff n : ℝ) ^ 5 ≤ 16 ^ 5 * (Real.log n) ^ 10 := by
    calc
      _ ≤ (16 * (Real.log n) ^ 2) ^ 5 := pow_le_pow_left₀ hQpos.le (cutoff_le_log_sq hn) 5
      _ = _ := by ring
  have hscaled : totalArcError n * (cutoff n : ℝ) / n ≤ η := by
    calc
      _ ≤ (C * (cutoff n : ℝ) ^ 4 * errorEnvelope M n) * (cutoff n : ℝ) / n :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right htot hQpos.le) hnpos.le
      _ = C * (cutoff n : ℝ) ^ 5 * errorEnvelope M n / n := by ring
      _ ≤ C * (16 ^ 5 * (Real.log n) ^ 10) * errorEnvelope M n / n :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hC) hE) hnpos.le
      _ = (C * 16 ^ 5) * ((Real.log n) ^ 10 * errorEnvelope M n / n) := by ring
      _ ≤ η := hsmall.le
  exact (le_div_iff₀ hQpos).mpr ((div_le_iff₀ hnpos).mp hscaled)

theorem totalArcError_cutoff_saving (η : ℝ) (hη : 0 < η) :
    ∃ N : ℕ, ∀ n ≥ N, totalArcError n ≤ η * (n : ℝ) / (cutoff n : ℝ) :=
  eventually_atTop.mp (eventually_totalArcError_le hη)

end

end GoldbachRawError

namespace GoldbachRawGrowth

open Finset Filter
open scoped BigOperators Topology

private theorem primeWeight_le_log (n k : ℕ) (hn : 0 < n) (hk : k ≤ n) :
    GoldbachMajorArc.primeWeight k ≤ Real.log (n:ℝ) := by
  unfold GoldbachMajorArc.primeWeight
  split_ifs with h
  · exact Real.log_le_log (by exact_mod_cast h.pos) (by exact_mod_cast hk)
  · exact Real.log_nonneg (by exact_mod_cast hn)

/-- An odd target has no ordered prime pairs away from the two possible
positions of the only even prime. -/
theorem odd_convolution_le (n : ℕ) (hn : Odd n) :
    (∑ k ∈ range (n+1),
      GoldbachMajorArc.primeWeight k * GoldbachMajorArc.primeWeight (n-k))
      ≤ 2 * Real.log 2 * Real.log (n:ℝ) := by
  let A := range (n+1)
  let B := A.filter (fun k => k=2 ∨ n-k=2)
  let w := GoldbachMajorArc.primeWeight
  have hpos : 0 < n := by obtain ⟨j, hj⟩ := hn; omega
  have hlogn : 0 ≤ Real.log (n:ℝ) := Real.log_nonneg (by exact_mod_cast hpos)
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have h2 : w 2 = Real.log 2 := by simp [w, GoldbachMajorArc.primeWeight, Nat.prime_two]
  have hzero (k : ℕ) (hk : k ∈ A) (hnB : k ∉ B) : w k * w (n-k) = 0 := by
    have hkn : k ≤ n := Nat.le_of_lt_succ (mem_range.mp hk)
    by_cases hkp : k.Prime
    · by_cases hnp : (n-k).Prime
      · exfalso
        apply hnB
        refine mem_filter.mpr ⟨hk, ?_⟩
        rcases hkp.eq_two_or_odd' with h | hko
        · exact Or.inl h
        rcases hnp.eq_two_or_odd' with h | hno
        · exact Or.inr h
        have he : Even (k+(n-k)) := hko.add_odd hno
        rw [Nat.add_sub_of_le hkn] at he
        exact ((Nat.not_even_iff_odd.mpr hn) he).elim
      · simp [w, GoldbachMajorArc.primeWeight, hnp]
    · simp [w, GoldbachMajorArc.primeWeight, hkp]
  have hconvolution : (∑ k ∈ A, w k * w (n-k)) = ∑ k ∈ B, w k * w (n-k) :=
    (sum_subset (filter_subset _ _) hzero).symm
  have hbound (k : ℕ) (hk : k ∈ B) : w k*w (n-k) ≤ Real.log 2*Real.log (n:ℝ) := by
    obtain ⟨hkA, hkB⟩ := mem_filter.mp hk
    have hkn : k ≤ n := Nat.le_of_lt_succ (mem_range.mp hkA)
    rcases hkB with he | he
    · rw [he, h2]
      exact mul_le_mul_of_nonneg_left (primeWeight_le_log n _ hpos (Nat.sub_le _ _)) hlog2
    · rw [he, h2, mul_comm (w k)]
      exact mul_le_mul_of_nonneg_left (primeWeight_le_log n k hpos hkn) hlog2
  have hcard : B.card ≤ 2 := by
    have hsub : B ⊆ {2,n-2} := by
      intro k hk
      obtain ⟨hkA, hkB⟩ := mem_filter.mp hk
      have hkn : k ≤ n := Nat.le_of_lt_succ (mem_range.mp hkA)
      simp only [mem_insert, mem_singleton]
      exact hkB.imp_right (fun he => by omega)
    exact (card_le_card hsub).trans (by
      simpa only [card_singleton] using (card_insert_le 2 ({n-2} : Finset ℕ)))
  change (∑ k ∈ A, w k*w (n-k)) ≤ _
  rw [hconvolution]
  calc
    _ ≤ ∑ _k ∈ B, Real.log 2*Real.log (n:ℝ) := sum_le_sum hbound
    _ = (B.card:ℝ)*(Real.log 2*Real.log (n:ℝ)) := by simp
    _ ≤ 2*(Real.log 2*Real.log (n:ℝ)) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (mul_nonneg hlog2 hlogn)
    _ = _ := by ring

/-- A negative total on a subset forces a square-energy lower bound on
the containing set. -/
theorem energy_ge_of_sum_le_neg {ι : Type*} {s t : Finset ι} (hst : s ⊆ t)
    (f : ι → ℝ) {A K : ℝ} (hA : 0 ≤ A) (hcard : (s.card:ℝ) ≤ K)
    (hsum : (∑ n ∈ s, f n) ≤ -A) :
    A^2 ≤ K * ∑ n ∈ t, (f n)^2 := by
  have hK : 0 ≤ K := (Nat.cast_nonneg s.card).trans hcard
  have hs : A ≤ -(∑ n ∈ s, f n) := by linarith only [hsum]
  calc
    A^2 ≤ (∑ n ∈ s, f n)^2 := by
      simpa only [neg_sq] using pow_le_pow_left₀ hA hs 2
    _ ≤ (s.card:ℝ) * ∑ n ∈ s, (f n)^2 := by
      simpa using sum_mul_sq_le_sq_mul_sq s (fun _ => (1:ℝ)) f
    _ ≤ K * ∑ n ∈ t, (f n)^2 := mul_le_mul hcard
      (sum_le_sum_of_subset_of_nonneg hst (fun _ _ _ => sq_nonneg _))
      (sum_nonneg (fun _ _ => sq_nonneg _)) hK

/-- Every fixed power of the dyadic level is negligible compared to every
positive power of the dyadic scale. -/
theorem eventually_dyadic_log_power_le_pow (d : ℕ) {α η : ℝ}
    (hα : 0 < α) (hη : 0 < η) :
    ∀ᶠ k : ℕ in atTop, (k:ℝ)^d ≤ η * (((2^k:ℕ):ℝ)^α) := by
  have ht : Tendsto (fun k : ℕ => (2:ℝ)^k) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hlim := (tendsto_rpow_atTop hα).comp ht
  let D : ℝ := (α*Real.log 2)^d
  have hD : 0 < D := by exact pow_pos (mul_pos hα (Real.log_pos (by norm_num))) _
  have hb := ((Real.isLittleO_pow_log_id_atTop (n:=d)).comp_tendsto hlim).bound
    (mul_pos hη hD)
  filter_upwards [hb] with k hk
  have h₂ : 0 < (2:ℝ)^k := by positivity
  have hx : 0 ≤ (k:ℝ) := Nat.cast_nonneg _
  have heq : Real.log (((2:ℝ)^k)^α) ^ d = D*((k:ℝ)^d) := by
    rw [Real.log_rpow h₂, Real.log_pow]
    rw [show α*((k:ℝ)*Real.log 2) = (α*Real.log 2)*(k:ℝ) by ring, mul_pow]
  change ‖Real.log (((2:ℝ)^k)^α) ^ d‖ ≤ η*D*‖((2:ℝ)^k)^α‖ at hk
  rw [heq, Real.norm_of_nonneg (mul_nonneg hD.le (pow_nonneg hx _)),
    Real.norm_of_nonneg (Real.rpow_nonneg h₂.le α)] at hk
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  apply le_of_mul_le_mul_left _ hD
  calc
    _ ≤ η*D*((2:ℝ)^k)^α := hk
    _ = _ := by ring

/-- A dyadic sequence of negative subset sums of size `X^2/(log₂ X)^2`
contradicts the raw energy bound with exponent `18/7 + ε`. -/
theorem not_raw_energy_of_negative_subset_sums (f : ℕ → ℝ) {b : ℝ} (hb : 0 < b)
    (hneg : ∀ᶠ k : ℕ in atTop, Even k → ∃ s : Finset ℕ, s ⊆ Icc (2^k) (2*2^k) ∧
      (∑ n ∈ s, f n) ≤ -b*(((2^k:ℕ):ℝ)^2)/(k:ℝ)^2) :
    ¬ (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∃ T : ℕ, 0 < C ∧ ∀ X : ℕ, T ≤ X →
      (∑ n ∈ Icc X (2*X), (f n)^2) ≤ C*(X:ℝ)^(18/7+ε)) := by
  intro h
  obtain ⟨C,T,hC,hupper⟩ := h (1/7) (by norm_num)
  have hη : 0 < b^2/(4*C) := by positivity
  have hgrowth := eventually_dyadic_log_power_le_pow 4
    (α := 2/7) (η := b^2/(4*C)) (by norm_num) hη
  have ht : Tendsto (fun k : ℕ => (2:ℕ)^k) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by decide)
  obtain ⟨K,hK⟩ := eventually_atTop.mp
    ((eventually_ge_atTop (1:ℕ)).and ((ht.eventually_ge_atTop T).and (hgrowth.and hneg)))
  let k := 2*K
  obtain ⟨hk,hT,hsmall,hneg'⟩ := hK k (by unfold k; omega)
  have hkE : Even k := even_iff_two_dvd.mpr (dvd_mul_right 2 K)
  obtain ⟨s,hs,hsNeg⟩ := hneg' hkE
  let X : ℕ := 2^k
  have hXpos : 0 < X := pow_pos (by decide : 0 < (2:ℕ)) k
  have hX : 0 < (X:ℝ) := by exact_mod_cast hXpos
  have hkR : 0 < (k:ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hcard : (s.card:ℝ) ≤ 2*(X:ℝ) := by
    have hnat : s.card ≤ 2*X := calc
      _ ≤ (Icc X (2*X)).card := card_le_card hs
      _ = 2*X+1-X := Nat.card_Icc X (2*X)
      _ ≤ 2*X := by omega
    exact_mod_cast hnat
  have hlower := energy_ge_of_sum_le_neg hs f
    (A := b*(X:ℝ)^2/(k:ℝ)^2) (by positivity) hcard
    (by simpa only [neg_mul, neg_div] using hsNeg)
  have hup : (∑ n ∈ Icc X (2*X), (f n)^2) ≤ C*(X:ℝ)^(19/7:ℝ) := by
    simpa only [show (18/7+(1/7):ℝ) = 19/7 by norm_num] using hupper X hT
  have hbnd : (b^2*(X:ℝ)^4)/(k:ℝ)^4 ≤ 2*(X:ℝ)*(C*(X:ℝ)^(19/7:ℝ)) := by
    simpa only [div_pow,mul_pow,← pow_mul,show 2*2 = (4:ℕ) by decide] using
      hlower.trans (mul_le_mul_of_nonneg_left hup (by positivity : 0 ≤ 2*(X:ℝ)))
  have hbad : b^2*(X:ℝ)^4 ≤ (b^2/2)*(X:ℝ)^4 := calc
    _ ≤ 2*(X:ℝ)*(C*(X:ℝ)^(19/7:ℝ))*(k:ℝ)^4 :=
      (div_le_iff₀ (pow_pos hkR 4)).mp hbnd
    _ ≤ 2*(X:ℝ)*(C*(X:ℝ)^(19/7:ℝ))*(b^2/(4*C)*(X:ℝ)^(2/7:ℝ)) :=
      mul_le_mul_of_nonneg_left hsmall (by positivity)
    _ = (b^2/2)*((X:ℝ)^(1:ℝ)*(X:ℝ)^(19/7:ℝ)*(X:ℝ)^(2/7:ℝ)) := by
      rw [Real.rpow_one]
      field_simp [hC.ne']
      ring
    _ = _ := by
      rw [← Real.rpow_add hX, ← Real.rpow_add hX]
      norm_num
  have hpos : 0 < b^2*(X:ℝ)^4 := by positivity
  linarith only [hbad,hpos]

end GoldbachRawGrowth

namespace GoldbachRawOddWindow

open Finset Filter MeasureTheory GoldbachMajorArc
open scoped Topology

noncomputable section

def minor (n : ℕ) : ℝ :=
  (∫ t in (0:ℝ)..1, (arcs n)ᶜ.indicator (integrand n) t).re

def convolution (n : ℕ) : ℝ :=
  ∑ p ∈ Finset.range (n+1), primeWeight p * primeWeight (n-p)

theorem minor_add_major (n : ℕ) :
    minor n + (majorContribution n).re = convolution n := by
  have h : majorContribution n +
      (∫ t in (0:ℝ)..1, (arcs n)ᶜ.indicator (integrand n) t) = (convolution n : ℂ) :=
    Conjectures.Goldbach.FourSevenths.Coefficient n
  simpa only [minor, Complex.add_re, Complex.ofReal_re, add_comm] using congrArg Complex.re h

def length (X : ℕ) : ℕ := X/2-1

def node (X j : ℕ) : ℕ := X+1+2*j

def odds (X : ℕ) : Finset ℕ := (range (length X)).image (node X)

theorem node_injective (X : ℕ) : Function.Injective (node X) := by
  intro a b h
  dsimp [node] at h
  omega

theorem odds_card (X : ℕ) : (odds X).card = length X := by
  simpa only [odds,card_range] using card_image_of_injective (range (length X)) (node_injective X)

theorem sum_odds {R : Type*} [AddCommMonoid R] (X : ℕ) (f : ℕ → R) :
    ∑ n ∈ odds X, f n = ∑ j ∈ range (length X), f (node X j) :=
  sum_image (node_injective X).injOn

theorem length_ge_quarter {X : ℕ} (hX : 4 ≤ X) (hEven : Even X) :
    (X:ℝ)/4 ≤ (length X:ℝ) := by
  obtain ⟨v,hv⟩ := hEven
  have hNat : X ≤ 4*length X := by dsimp [length]; omega
  have hReal : (X:ℝ) ≤ 4*(length X:ℝ) := by exact_mod_cast hNat
  linarith only [hReal]

theorem length_le_half (X : ℕ) : (length X : ℝ) ≤ (X:ℝ)/2 := by
  have hh : 2*length X ≤ X := by dsimp [length]; omega
  have hReal : 2*(length X:ℝ) ≤ (X:ℝ) := by exact_mod_cast hh
  linarith only [hReal]

theorem node_bounds {X j : ℕ} (hEven : Even X) (hj : j < length X) :
    X ≤ node X j ∧ node X j ≤ 2*X-3 ∧ Odd (node X j) := by
  obtain ⟨v,hv⟩ := hEven
  constructor
  · dsimp [node]; omega
  constructor
  · dsimp [node, length] at *; omega
  · exact ⟨v+j, by dsimp [node]; omega⟩

theorem odds_subset {X : ℕ} (hEven : Even X) : odds X ⊆ Icc X (2*X) := by
  intro n hn
  obtain ⟨j,hj,rfl⟩ := mem_image.mp hn
  have hB := node_bounds hEven (mem_range.mp hj)
  exact mem_Icc.mpr ⟨hB.1, hB.2.1.trans (Nat.sub_le _ _)⟩

theorem pow_two_even {k : ℕ} (hk : 0 < k) : Even (2^k : ℕ) := by
  cases k with
  | zero => omega
  | succ k => exact ⟨2^k, by rw [pow_succ]; omega⟩

theorem pow_two_ge_four {k : ℕ} (hk : 2 ≤ k) : 4 ≤ (2^k : ℕ) :=
  Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hk

theorem cutoff_dyadic {k n : ℕ} (hl : 2^k ≤ n) (hu : n ≤ 2*(2^k)-3)
    (hk : 2 ≤ k) : cutoff n = k^2 := by
  have hlog₁ : k ≤ Nat.log 2 (n+2) := Nat.le_log_of_pow_le (by decide) (by omega)
  have h4 := pow_two_ge_four hk
  have hlog₂ : Nat.log 2 (n+2) < k+1 := by
    apply Nat.log_lt_of_lt_pow (by omega)
    rw [pow_succ]
    omega
  rw [cutoff, show Nat.log 2 (n+2)=k by omega]

end
end GoldbachRawOddWindow

namespace GoldbachRawModel

open Finset GoldbachMajorArc GoldbachRawKernel GoldbachRawOddWindow

noncomputable section

def kernelScale : ℝ := 16*Real.pi+2

def shellScale : ℝ := 1/(4*Real.pi^2)

theorem kernelScale_pos : 0 < kernelScale := by
  unfold kernelScale
  positivity

theorem shellScale_pos : 0 < shellScale := by
  unfold shellScale
  positivity

def mass (n Q q : ℕ) : ℝ :=
  ((n:ℝ)+1)*profile ((Q:ℝ)/(q:ℝ))

def profiled (n Q : ℕ) : ℂ :=
  ∑ q ∈ Icc 1 Q, coefficient q n * (mass n Q q : ℂ)

def higher (n Q : ℕ) : ℂ :=
  ∑ q ∈ Icc 3 Q, coefficient q n * (mass n Q q : ℂ)

theorem model_profile_error (n Q : ℕ) (hn : 0 < n) (hQ : cutoff n = Q) :
    ‖modeledContribution n-profiled n Q‖ ≤ kernelScale*((Q:ℝ)+1)^3 := by
  rw [modeledContribution, hQ, profiled, ← sum_sub_distrib]
  calc
    _ ≤ ∑ q ∈ Icc 1 Q, ‖coefficient q n * (kernelMass n (width n q):ℂ) -
        coefficient q n * (mass n Q q:ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ q ∈ Icc 1 Q, kernelScale*((Q:ℝ)+1)^2 := by
      apply sum_le_sum
      intro q hq
      have hq' : 0 < q := (mem_Icc.mp hq).1
      rw [← mul_sub, norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
        width, hQ]
      have hk : |kernelMass n ((Q:ℝ)/((q:ℝ)*(n:ℝ)))-mass n Q q| ≤
          kernelScale*((Q:ℝ)+1)^2 := kernel_mass_error n q Q hn hq'
      calc
        _ ≤ 1*(kernelScale*((Q:ℝ)+1)^2) :=
          mul_le_mul (GoldbachRawCancellation.coefficient_norm q n hq') hk (abs_nonneg _) zero_le_one
        _ = _ := one_mul _
    _ = (Q:ℝ)*(kernelScale*((Q:ℝ)+1)^2) := by simp [Nat.card_Icc, nsmul_eq_mul]
    _ ≤ ((Q:ℝ)+1)*(kernelScale*((Q:ℝ)+1)^2) := by
      exact mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg kernelScale_pos.le (sq_nonneg _))
    _ = _ := by ring

theorem higher_sum_norm (X Q : ℕ) (hX : 2 ≤ X) :
    ‖∑ j ∈ range (length X), higher (node X j) Q‖ ≤ 3*(X:ℝ)*(Q:ℝ)^2 := by
  unfold higher
  rw [sum_comm]
  let K (q : ℕ) : ℂ := (profile ((Q:ℝ)/(q:ℝ)) : ℂ)
  have hK (q : ℕ) (_ : q ∈ Icc 3 Q) : ‖K q‖ ≤ 1 := by
    obtain ⟨hp,hle⟩ := profile_bounds ((Q:ℝ)/(q:ℝ)) (by positivity)
    simpa only [K, Complex.norm_real, Real.norm_of_nonneg hp] using hle
  have hsum (q : ℕ) :
      (∑ j ∈ range (length X), coefficient q (node X j) * (mass (node X j) Q q : ℂ)) =
        K q * (∑ j ∈ range (length X), (((node X j : ℕ):ℂ)+1) * coefficient q (node X j)) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro j _
    simp only [K, mass, Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_natCast]
    ring
  simp_rw [hsum]
  exact GoldbachRawCancellation.odd_higher_bound X Q hX K hK

private theorem coefficient_two_odd (n : ℕ) (hn : Odd n) : coefficient 2 n = -1 := by
  rw [coefficient_prime Nat.prime_two]
  norm_num [localCoefficient, hn.not_two_dvd_nat]

theorem profiled_split (n Q : ℕ) (hn : Odd n) (hQ : 2 ≤ Q) :
    profiled n Q =
      (((n:ℂ)+1) * ((profile (Q:ℝ)-profile ((Q:ℝ)/2):ℝ):ℂ)) + higher n Q := by
  have hset : Icc 1 Q = insert 1 (insert 2 (Icc 3 Q)) := by
    ext q
    simp only [mem_Icc,mem_insert]
    omega
  have hn1 : 1 ∉ insert 2 (Icc 3 Q) := by simp
  have hn2 : 2 ∉ Icc 3 Q := by simp
  rw [profiled, hset, sum_insert hn1, sum_insert hn2, coefficient_one, coefficient_two_odd n hn]
  simp only [mass, Nat.cast_one, Nat.cast_ofNat, div_one, Complex.ofReal_mul,
    Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_natCast, Complex.ofReal_sub, higher]
  ring

theorem main_shell (n Q X : ℕ) (hX : X ≤ n) (hQ : 2 ≤ Q) (heQ : Even Q) :
    shellScale*(X:ℝ)/(Q:ℝ) ≤ ((n:ℝ)+1)*(profile (Q:ℝ)-profile ((Q:ℝ)/2)) := by
  have hGap : shellScale/(Q:ℝ) ≤ profile (Q:ℝ)-profile ((Q:ℝ)/2) := profile_gap Q hQ heQ
  have hXr : (X:ℝ) ≤ n := by exact_mod_cast hX
  calc
    _ = (X:ℝ)*(shellScale/(Q:ℝ)) := by ring
    _ ≤ ((n:ℝ)+1)*(profile (Q:ℝ)-profile ((Q:ℝ)/2)) :=
      mul_le_mul (by linarith only [hXr]) hGap (div_nonneg shellScale_pos.le (Nat.cast_nonneg _)) (by positivity)

end
end GoldbachRawModel

namespace GoldbachRawNegative

open Filter Finset GoldbachMajorArc GoldbachRawOddWindow GoldbachRawModel
open scoped Topology

noncomputable section

def scale (X Q : ℕ) : ℝ := shellScale*(X:ℝ)/(Q:ℝ)

theorem scale_nonneg (X Q : ℕ) : 0 ≤ scale X Q := by
  unfold scale
  exact div_nonneg (mul_nonneg shellScale_pos.le (Nat.cast_nonneg _)) (Nat.cast_nonneg _)

theorem pointwise_upper (n X Q : ℕ) (hX : X ≤ n) (hn : n ≤ 2*X) (ho : Odd n)
    (hQ : 2 ≤ Q) (he : Even Q) (hc : cutoff n = Q) (hsmall : 2*Q^2 < X)
    (hArc : totalArcError n ≤ (shellScale/16)*(n:ℝ)/(Q:ℝ))
    (hKernel : kernelScale*((Q:ℝ)+1)^3 ≤ scale X Q/16)
    (hConv : convolution n ≤ scale X Q/16) :
    minor n ≤ -(scale X Q/2)-(higher n Q).re := by
  have hsep : 2*(cutoff n)^2 < n := by rw [hc]; exact hsmall.trans_le hX
  have hnpos : 0 < n := (Nat.zero_le _).trans_lt hsep
  have hnR : (n:ℝ) ≤ 2*(X:ℝ) := by exact_mod_cast hn
  have hArc' : totalArcError n ≤ scale X Q/8 := by
    calc
      _ ≤ (shellScale/16)*(n:ℝ)/(Q:ℝ) := hArc
      _ ≤ (shellScale/16)*(2*(X:ℝ))/(Q:ℝ) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hnR
          (div_nonneg shellScale_pos.le (by norm_num))) (Nat.cast_nonneg Q)
      _ = _ := by unfold scale; ring
  have hProfile : ‖profiled n Q-modeledContribution n‖ ≤ scale X Q/16 := by
    rw [norm_sub_rev]
    exact (model_profile_error n Q hnpos hc).trans hKernel
  have hOriginal : ‖modeledContribution n-majorContribution n‖ ≤ scale X Q/8 := by
    rw [norm_sub_rev]
    exact (major_error hsep).trans hArc'
  have hModel : ‖profiled n Q-majorContribution n‖ ≤ scale X Q/16+scale X Q/8 := by
    calc
      _ = ‖(profiled n Q-modeledContribution n) +
          (modeledContribution n-majorContribution n)‖ := by congr 1; ring
      _ ≤ ‖profiled n Q-modeledContribution n‖ +
          ‖modeledContribution n-majorContribution n‖ := norm_add_le _ _
      _ ≤ _ := add_le_add hProfile hOriginal
  have hRe := (Complex.re_le_norm (profiled n Q-majorContribution n)).trans hModel
  rw [Complex.sub_re] at hRe
  have hShape :
      (profiled n Q).re =
        ((n:ℝ)+1)*(GoldbachRawKernel.profile (Q:ℝ)-GoldbachRawKernel.profile ((Q:ℝ)/2)) +
          (higher n Q).re := by
    rw [profiled_split n Q ho hQ]
    simp [Complex.mul_re, Complex.add_re]
  have hMain : scale X Q ≤
      ((n:ℝ)+1)*(GoldbachRawKernel.profile (Q:ℝ)-GoldbachRawKernel.profile ((Q:ℝ)/2)) :=
    main_shell n Q X hX hQ he
  linarith only [minor_add_major n, hRe, hShape, hMain, hConv, scale_nonneg X Q]

theorem window_upper (X Q : ℕ) (hX : 4 ≤ X) (heX : Even X)
    (hQ : 2 ≤ Q) (heQ : Even Q) (hsmall : 2*Q^2 < X)
    (hc : ∀ j < length X, cutoff (node X j) = Q)
    (hArc : ∀ j < length X,
      totalArcError (node X j) ≤ (shellScale/16)*(node X j:ℝ)/(Q:ℝ))
    (hKernel : kernelScale*((Q:ℝ)+1)^3 ≤ scale X Q/16)
    (hConv : ∀ n, X ≤ n → n ≤ 2*X → Odd n → convolution n ≤ scale X Q/16)
    (hTail : 3*(X:ℝ)*(Q:ℝ)^2 ≤ (X:ℝ)*scale X Q/16) :
    (∑ n ∈ odds X, minor n) ≤ -((X:ℝ)*scale X Q/16) := by
  rw [sum_odds]
  let J := range (length X)
  let M := ∑ j ∈ J, higher (node X j) Q
  have hRe : -M.re ≤ 3*(X:ℝ)*(Q:ℝ)^2 :=
    (neg_le_abs _).trans ((Complex.abs_re_le_norm M).trans (higher_sum_norm X Q (by omega)))
  have hL := mul_le_mul_of_nonneg_right (length_ge_quarter hX heX)
    (div_nonneg (scale_nonneg X Q) (by norm_num : (0:ℝ) ≤ 2))
  calc
    _ ≤ ∑ j ∈ J, (-(scale X Q/2)-(higher (node X j) Q).re) := by
      apply sum_le_sum
      intro j hj
      have hj' : j < length X := mem_range.mp hj
      obtain ⟨hlo,hhi,ho⟩ := node_bounds heX hj'
      have hhi' := hhi.trans (Nat.sub_le (2*X) 3)
      exact pointwise_upper _ _ _ hlo hhi' ho hQ heQ (hc j hj') hsmall
        (hArc j hj') hKernel (hConv _ hlo hhi' ho)
    _ = (length X:ℝ)*(-(scale X Q/2))-M.re := by
      rw [sum_sub_distrib]
      simp [J, M, nsmul_eq_mul, Complex.re_sum]
    _ ≤ -( (X:ℝ)*scale X Q/16) := by
      calc
        _ ≤ -( (X:ℝ)/4*(scale X Q/2)) + 3*(X:ℝ)*(Q:ℝ)^2 := by
          rw [mul_neg]
          linarith only [hL,hRe]
        _ ≤ _ := by
          calc
            _ ≤ -((X:ℝ)/4*(scale X Q/2)) + (X:ℝ)*scale X Q/16 := by
              linarith only [hTail]
            _ = _ := by ring

theorem eventual_controls :
    ∀ᶠ k : ℕ in atTop,
      let X := 2^k
      let Q := k^2
      2 ≤ k ∧ 2*Q^2 < X ∧
      kernelScale*((Q:ℝ)+1)^3 ≤ scale X Q/16 ∧
      3*(X:ℝ)*(Q:ℝ)^2 ≤ (X:ℝ)*scale X Q/16 ∧
      ∀ n : ℕ, X ≤ n → n ≤ 2*X → Odd n → convolution n ≤ scale X Q/16 := by
  let D := 8*kernelScale+8
  have hD : 0 < D := by dsimp [D]; linarith only [kernelScale_pos]
  have hD8 : 8*kernelScale ≤ D := by dsimp [D]; linarith
  have hD4 : 4 ≤ D := by dsimp [D]; linarith only [kernelScale_pos]
  let τ := min (1/8) (shellScale/16/D)
  have hτ : 0 < τ := lt_min (by norm_num) (div_pos (div_pos shellScale_pos (by norm_num)) hD)
  have hτ8 : τ ≤ 1/8 := min_le_left _ _
  have hτD : D*τ ≤ shellScale/16 := by
    rw [mul_comm]
    exact (le_div_iff₀ hD).mp (min_le_right _ _)
  have hg := GoldbachRawGrowth.eventually_dyadic_log_power_le_pow 8 (α := 1)
    (by norm_num) hτ
  filter_upwards [eventually_ge_atTop (2:ℕ), hg] with k hk hg'
  dsimp only
  simp only [Real.rpow_one] at hg'
  let X : ℕ := 2^k
  let Q : ℕ := k^2
  have hOne : (1:ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
  have hK2 : (2:ℝ) ≤ k := by exact_mod_cast hk
  have hXpos : 0 < (X:ℝ) := by dsimp [X]; positivity
  have hX4 : 4 ≤ X := pow_two_ge_four hk
  have hQ : (Q:ℝ) = (k:ℝ)^2 := by simp [Q]
  have hQpos : 0 < (Q:ℝ) := by rw [hQ]; positivity
  have hQplus : (Q:ℝ)+1 ≤ 2*(k:ℝ)^2 := by
    rw [hQ]
    nlinarith only [hK2, sq_nonneg ((k:ℝ)-2)]
  have rise (j : ℕ) (hj : j ≤ 8) : (k:ℝ)^j ≤ (k:ℝ)^8 :=
    pow_le_pow_right₀ hOne hj
  have hSmall : 2*Q^2 < X := by
    have hP := (rise 4 (by decide)).trans hg'
    have hh : τ*(X:ℝ) ≤ (1/8)*(X:ℝ) :=
      mul_le_mul_of_nonneg_right hτ8 hXpos.le
    have hz : (2:ℝ)*(Q:ℝ)^2 < X := by
      rw [hQ]
      nlinarith only [hP,hh,hXpos]
    exact_mod_cast hz
  have hPoly : D*(k:ℝ)^8 ≤ (shellScale/16)*(X:ℝ) := by
    calc
      _ ≤ D*(τ*(X:ℝ)) := mul_le_mul_of_nonneg_left hg' hD.le
      _ = (D*τ)*(X:ℝ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hτD hXpos.le
  have hDiv : scale X Q/16 = (shellScale/16)*(X:ℝ)/(Q:ℝ) := by unfold scale; ring
  refine ⟨hk,hSmall,?_,?_,?_⟩
  · rw [hDiv]
    apply (le_div_iff₀ hQpos).mpr
    calc
      _ ≤ kernelScale*(2*(k:ℝ)^2)^3*(Q:ℝ) := by
        apply mul_le_mul_of_nonneg_right _ hQpos.le
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by positivity) hQplus 3) kernelScale_pos.le
      _ = (8*kernelScale)*(k:ℝ)^8 := by rw [hQ]; ring
      _ ≤ D*(k:ℝ)^8 := mul_le_mul_of_nonneg_right hD8 (by positivity)
      _ ≤ _ := hPoly
  · have hTail : 3*(Q:ℝ)^2 ≤ scale X Q/16 := by
      rw [hDiv]
      apply (le_div_iff₀ hQpos).mpr
      calc
        _ = 3*(k:ℝ)^6 := by rw [hQ]; ring
        _ ≤ 3*(k:ℝ)^8 := mul_le_mul_of_nonneg_left (rise 6 (by decide)) (by norm_num)
        _ ≤ D*(k:ℝ)^8 := mul_le_mul_of_nonneg_right (by linarith only [hD4]) (by positivity)
        _ ≤ _ := hPoly
    calc
      _ = (X:ℝ)*(3*(Q:ℝ)^2) := by ring
      _ ≤ (X:ℝ)*(scale X Q/16) := mul_le_mul_of_nonneg_left hTail hXpos.le
      _ = _ := by ring
  · intro n hn hhi ho
    have hNpos : 0 < (n:ℝ) := hXpos.trans_le (by exact_mod_cast hn)
    have hN1 : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    have hNr : (n:ℝ) ≤ 2*(X:ℝ) := by exact_mod_cast hhi
    have hLogX : Real.log (X:ℝ) = (k:ℝ)*Real.log 2 := by
      dsimp [X]
      rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
    have hLog2 : Real.log 2 ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
      norm_num at h
      exact h
    have hlog := Real.log_le_log hNpos hNr
    rw [Real.log_mul (by norm_num) hXpos.ne', hLogX] at hlog
    have hm : (k:ℝ)*Real.log 2 ≤ (k:ℝ) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hLog2 (Nat.cast_nonneg k : (0:ℝ) ≤ k)
    have hlog2k : Real.log (n:ℝ) ≤ 2*(k:ℝ) := by linarith only [hlog,hLog2,hm,hOne]
    have hConv4 : convolution n ≤ 4*(k:ℝ) := by
      calc
        _ ≤ 2*Real.log 2*Real.log (n:ℝ) := GoldbachRawGrowth.odd_convolution_le n ho
        _ ≤ (2*1)*(2*(k:ℝ)) := mul_le_mul
          (mul_le_mul_of_nonneg_left hLog2 (by norm_num)) hlog2k (Real.log_nonneg hN1) (by norm_num)
        _ = _ := by ring
    rw [hDiv]
    apply (le_div_iff₀ hQpos).mpr
    calc
      _ ≤ 4*(k:ℝ)*(Q:ℝ) := mul_le_mul_of_nonneg_right hConv4 hQpos.le
      _ = 4*(k:ℝ)^3 := by rw [hQ]; ring
      _ ≤ 4*(k:ℝ)^8 := mul_le_mul_of_nonneg_left (rise 3 (by decide)) (by norm_num)
      _ ≤ D*(k:ℝ)^8 := mul_le_mul_of_nonneg_right hD4 (by positivity)
      _ ≤ _ := hPoly

theorem eventual_negative_windows : ∀ᶠ k : ℕ in atTop, Even k →
    ∃ s : Finset ℕ, s ⊆ Icc (2^k) (2*2^k) ∧
      (∑ n ∈ s, minor n) ≤ -(shellScale/16)*(((2^k:ℕ):ℝ)^2)/(k:ℝ)^2 := by
  obtain ⟨N,hN⟩ := GoldbachRawError.totalArcError_cutoff_saving (shellScale/16)
    (div_pos shellScale_pos (by norm_num))
  have ht : Tendsto (fun k : ℕ => (2:ℕ)^k) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by decide)
  filter_upwards [eventual_controls, ht.eventually (eventually_ge_atTop N)] with k hk hBound he
  obtain ⟨hK,hSmall,hKernel,hTail,hConv⟩ := hk
  let X : ℕ := 2^k
  let Q : ℕ := k^2
  have hXe : Even X := pow_two_even (by omega)
  have hX4 : 4 ≤ X := pow_two_ge_four hK
  have hQ : 2 ≤ Q := by dsimp [Q]; nlinarith
  have hQe : Even Q := by
    obtain ⟨a,ha⟩ := he
    refine ⟨2*a^2, ?_⟩
    dsimp [Q]
    rw [ha]
    ring
  have hc (j) (hj : j < length X) : cutoff (node X j) = Q :=
    cutoff_dyadic (node_bounds hXe hj).1 (node_bounds hXe hj).2.1 hK
  have hArc (j) (hj : j < length X) :
      totalArcError (node X j) ≤ (shellScale/16)*(node X j:ℝ)/(Q:ℝ) := by
    have h := hN _ (hBound.trans (node_bounds hXe hj).1)
    simpa only [hc j hj] using h
  refine ⟨odds X, odds_subset hXe, ?_⟩
  calc
    _ ≤ -((X:ℝ)*scale X Q/16) :=
      window_upper X Q hX4 hXe hQ hQe hSmall hc hArc hKernel hConv hTail
    _ = _ := by simp only [scale, X, Q, Nat.cast_pow]; ring

end
end GoldbachRawNegative

open scoped Topology in
set_option maxHeartbeats 900000 in
theorem Conjectures.Cuts.Refuteb8b4ba21e36f3ce1448331bf : ¬ (have x1 : ℕ → ℝ := fun (x1 : ℕ) => if Nat.Prime x1 then Real.log ↑x1 else (0 : ℝ); have x2 : ℝ → ℂ := fun (x2 : ℝ) => Complex.exp (↑((2 : ℝ) * Real.pi * x2) * Complex.I); have x3 : ℕ → (ℕ → ℝ) → ℝ → ℂ := fun (x3 : ℕ) (x4 : ℕ → ℝ) (x5 : ℝ) => ∑ x6 ∈ Finset.range (x3 + (1 : ℕ)), ↑(x4 x6) * x2 (↑x6 * x5); have x4 : ℕ → ℕ := fun (x4 : ℕ) => Nat.log (2 : ℕ) (x4 + (2 : ℕ)) ^ (2 : ℕ); have x5 : ℕ → Set ℝ := fun (x5 : ℕ) => {x6 : ℝ | ∃ (x7 : ℕ) (x8 : ℕ), (1 : ℕ) ≤ x7 ∧ x7 ≤ x4 x5 ∧ x8 ≤ x7 ∧ x8.Coprime x7 ∧ |x6 - ↑x8 / ↑x7| ≤ ↑(x4 x5) / (↑x7 * ↑x5)}; have x6 : ℕ → ℝ → ℂ := fun (x6 : ℕ) (x7 : ℝ) => x3 x6 x1 x7 ^ (2 : ℕ) * x2 (-↑x6 * x7); have x7 : ℕ → ℂ := fun (x7 : ℕ) => ∫ (x8 : ℝ) in (0 : ℝ)..(1 : ℝ), (x5 x7).indicator (x6 x7) x8; have x8 : ℕ → ℝ := fun (x8 : ℕ) => (∫ (x9 : ℝ) in (0 : ℝ)..(1 : ℝ), (x5 x8)ᶜ.indicator (x6 x8) x9).re; ∀ (x9 : ℝ), (0 : ℝ) < x9 → ∃ (x11 : ℝ) (x12 : ℕ), (0 : ℝ) < x11 ∧ ∀ (x13 : ℕ), x12 ≤ x13 → ∑ x15 ∈ Finset.Icc x13 ((2 : ℕ) * x13), x8 x15 ^ (2 : ℕ) ≤ x11 * ↑x13 ^ ((18 / 7 : ℝ) + x9)) := by
  exact GoldbachRawGrowth.not_raw_energy_of_negative_subset_sums GoldbachRawOddWindow.minor
    (div_pos GoldbachRawModel.shellScale_pos (by norm_num))
    GoldbachRawNegative.eventual_negative_windows
