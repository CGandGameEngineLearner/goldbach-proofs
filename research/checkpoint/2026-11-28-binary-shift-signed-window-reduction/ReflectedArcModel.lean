import Conjectures.Goldbach.ThreeQuartersModelSqrtExceptions

/- The arithmetic summation in reflected_model_floor adapts the accepted
   proof of GB6Geometry.model_floor (Goldbach PR #3709). The reflection
   acts on the analytic kernel only; the Ramanujan coefficients retain m. -/
open Finset MeasureTheory GB6Kernel GB6Geometry
namespace Goldbach.ReflectedArcModel
noncomputable section

private theorem phase_add' (x y : ℝ) : phase (x+y) = phase x * phase y := by
  unfold phase; rw [← Complex.exp_add]; congr 1; push_cast; ring

theorem kernel_reflect (Y : ℕ) (t : ℝ) :
    kernel Y (-t) = kernel Y t * phase (-(Y:ℝ)*t) := by
  unfold kernel
  rw [sum_mul]
  calc
    _ = ∑ k ∈ range (Y+1), phase (((Y-k:ℕ):ℝ)*(-t)) := by
      simpa only [Nat.add_sub_cancel] using
        (sum_range_reflect (fun k => phase ((k:ℝ)*(-t))) (Y+1)).symm
    _ = _ := by
      refine sum_congr rfl fun k hk => ?_
      rw [← phase_add', Nat.cast_sub (show k≤Y by simpa using hk)]
      congr 1
      ring

theorem twisted_reflect (Y m : ℕ) (hm : m ≤ 2*Y) (t : ℝ) :
    twisted Y (2*Y-m) (-t) = twisted Y m t := by
  unfold twisted
  rw [kernel_reflect, mul_pow, mul_assoc, sq (phase _), ← phase_add', ← phase_add',
    Nat.cast_sub hm]
  push_cast
  congr 2
  ring

theorem trunc_error_upper (Y m : ℕ) (hlo : Y ≤ m) (hhi : m ≤ 2*Y)
    {b : ℝ} (hb : 0 < b) (hh : b ≤ 1/2) :
    ‖(∫ t in -b..b, twisted Y m t) - (((2*Y-m:ℕ):ℂ)+1)‖ ≤ 1/(2*b) := by
  have h : (∫ t in -b..b, twisted Y m t) = ∫ t in -b..b, twisted Y (2*Y-m) t := by
    calc
      _ = ∫ t in -b..b, twisted Y (2*Y-m) (-t) :=
        intervalIntegral.integral_congr (fun t _ => (twisted_reflect Y m hhi t).symm)
      _ = _ := by rw [intervalIntegral.integral_comp_neg]; simp
  rw [h]
  exact integral_trunc_error Y (2*Y-m) (by omega) hb hh

theorem reflected_model_floor {Q H n m : ℕ} (hs : 2*H^2<n) (hQH : Q≤H) (hQ : 1≤Q)
    (hnm : n ≤ m) (hm : 2*m ≤ 3*n) (he : Even m)
    (hbudget : (Q:ℝ)*(1+(Nat.log 2 Q:ℝ))/(2*(H:ℝ)) ≤ 1/32) :
    (n:ℝ)/8 ≤ (∫ t in (0:ℝ)..1, (model Q H n ThreeQArith.mean t)^2 * phase (-(m:ℝ)*t)).re := by
  classical
  let S (q : ℕ) := (range q).filter (fun a => a.Coprime q)
  let A (q a : ℕ) := (ThreeQArith.mean q a)^2 * phase (-(m:ℝ)*center q a)
  let B (q : ℕ) := ∑ a ∈ S q, A q a
  let J (q : ℕ) := ∫ t in -(width H n q)..width H n q, twisted n m t
  have hHr : (0:ℝ)<H := by exact_mod_cast (show 0<H by omega)
  have hnr : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hfloor : (1:ℝ)/3 ≤ (∑ q ∈ Icc 1 Q, B q).re := ThreeQArith.main_floor Q m hQ he
  have hcoef : (∫ t in (0:ℝ)..1, (model Q H n ThreeQArith.mean t)^2 * phase (-(m:ℝ)*t)) =
      ∑ q ∈ Icc 1 Q, B q * J q := by
    apply exact_model_coeff ThreeQArith.mean _ hs hQH
    simp [ThreeQArith.mean, ThreeQArith.phase]
  have heq : (∑ q ∈ Icc 1 Q, B q * J q) - (∑ q ∈ Icc 1 Q, B q) * (((2*n-m:ℕ):ℂ)+1) =
      ∑ q ∈ Icc 1 Q, B q * (J q - (((2*n-m:ℕ):ℂ)+1)) := by
    rw [sum_mul, ← sum_sub_distrib]
    exact sum_congr rfl fun _ _ => (mul_sub ..).symm
  have heach (q : ℕ) (hq : q ∈ Icc 1 Q) : ‖B q * (J q - (((2*n-m:ℕ):ℂ)+1))‖ ≤
      (∑ a ∈ S q, (q:ℝ)*‖ThreeQArith.mean q a‖^2)*((n:ℝ)/(2*H)) := by
    have hqr : (0:ℝ)<q := by exact_mod_cast (mem_Icc.mp hq).1
    have hw : 0<width H n q := div_pos hHr (mul_pos hqr hnr)
    have hhalf : width H n q≤1/2 := by
      have hnH : 2*H≤n := by nlinarith only [hs,Nat.le_self_pow (by decide : 2≠0) H]
      have hqr1 : (1:ℝ)≤q := by exact_mod_cast (mem_Icc.mp hq).1
      apply (div_le_iff₀ (mul_pos hqr hnr)).mpr
      have hr : 2*(H:ℝ)≤n := by exact_mod_cast hnH
      nlinarith only [hr,mul_le_mul_of_nonneg_right hqr1 hnr.le]
    have htail : ‖J q - (((2*n-m:ℕ):ℂ)+1)‖ ≤ (q:ℝ) * ((n:ℝ)/(2*H)) := by
      refine (trunc_error_upper n m hnm (by omega) hw hhalf).trans_eq ?_
      unfold width; field_simp
    have hB : ‖B q‖ ≤ ∑ a ∈ S q, ‖ThreeQArith.mean q a‖^2 := by
      refine (norm_sum_le ..).trans_eq ?_
      apply sum_congr rfl
      intro a _
      have hp (u : ℝ) : ‖phase u‖ = 1 := Complex.norm_exp_ofReal_mul_I _
      simp only [A, norm_mul,norm_pow,hp,mul_one]
    rw [norm_mul, ← mul_sum]
    exact (mul_le_mul hB htail (norm_nonneg _) (sum_nonneg fun _ _ => sq_nonneg _)).trans_eq (by ring)
  have hd : ‖(∑ q ∈ Icc 1 Q, B q * J q) - (∑ q ∈ Icc 1 Q, B q) * (((2*n-m:ℕ):ℂ)+1)‖ ≤ (n:ℝ)/32 := by
    rw [heq]
    refine (norm_sum_le ..).trans ((sum_le_sum heach).trans ?_)
    rw [←sum_mul]
    refine (mul_le_mul_of_nonneg_right (ThreeQArith.error_sum Q) (by positivity)).trans ?_
    calc
      (Q:ℝ)*(1+(Nat.log 2 Q:ℝ))*((n:ℝ)/(2*H)) = ((Q:ℝ)*(1+(Nat.log 2 Q:ℝ))/(2*H))*n := by ring
      _ ≤ (1/32:ℝ)*n := mul_le_mul_of_nonneg_right hbudget hnr.le
      _ = _ := by ring
  have diff := (Complex.abs_re_le_norm _).trans hd
  rw [Complex.sub_re, Complex.mul_re] at diff
  simp only [Complex.add_re,Complex.natCast_re,Complex.one_re,Complex.add_im,Complex.natCast_im,Complex.one_im,zero_add,mul_zero,sub_zero] at diff
  rw [hcoef]
  have hhalf : (n:ℝ) ≤ 2*((2*n-m:ℕ):ℝ) := by exact_mod_cast (show n ≤ 2*(2*n-m) by omega)
  have hmf : 0≤ ((2*n-m:ℕ):ℝ)+1 := by positivity
  linarith [mul_le_mul_of_nonneg_right hfloor hmf,(abs_le.mp diff).1]

open GB6Growth

theorem eventual_interior_model_floor :
    ∃ N : ℕ, ∀ Y ≥ N, ∀ m : ℕ, Y ≤ m → 2*m ≤ 3*Y → Even m →
    (Y:ℝ)/8 ≤ (∫ t in (0:ℝ)..1,
      (model (GB6Growth.grid Y) (GB6Growth.height Y) Y ThreeQArith.mean t)^2 *
        phase (-(m:ℝ)*t)).re := by
  obtain ⟨N,hN⟩ := Filter.eventually_atTop.mp eventual_geometry
  refine ⟨N,?_⟩
  intro Y hy m hlo hhi he
  obtain ⟨hQ,hQH,hQM,hL,hsep⟩ := hN Y hy
  have hH : (0:ℝ)<height Y := by exact_mod_cast (hQ.trans hQH)
  have hlog : (Nat.log 2 (grid Y):ℝ) ≤ L Y := by
    unfold L
    exact_mod_cast Nat.log_mono_right (b:=2) (hQM.trans (show Y ≤ Y+2 by omega))
  have hw : (height Y:ℝ) = 256*(grid Y:ℝ)*(L Y)^2 := by simp [height,L]
  have hbudget : (grid Y:ℝ)*(1+(Nat.log 2 (grid Y):ℝ))/(2*height Y) ≤ 1/32 := by
    apply (div_le_iff₀ (mul_pos (by norm_num) hH)).mpr
    rw [hw]
    have hcoef : 1+(Nat.log 2 (grid Y):ℝ) ≤ 16*(L Y)^2 := by nlinarith [sq_nonneg (L Y-1)]
    convert mul_le_mul_of_nonneg_left hcoef (Nat.cast_nonneg (grid Y)) using 1; ring
  exact reflected_model_floor hsep hQH hQ hlo hhi he hbudget

/-- Every interior cutoff where the true wide coefficient is small forces
a linear error in the disjoint rational-arc model coefficient. -/
def modelCoefficient (Y m : ℕ) : ℂ := ∫ t in (0:ℝ)..1,
      (model (grid Y) (height Y) Y ThreeQArith.mean t)^2 * phase (-(m:ℝ)*t)

theorem eventual_discrepancy :
    ∃ N : ℕ, ∀ Y ≥ N, ∀ m : ℕ, Y ≤ m → 2*m ≤ 3*Y → Even m →
    ∀ z : ℂ, ‖z‖ ≤ (Y:ℝ)^(23/24:ℝ) → (Y:ℝ)/16 ≤ ‖modelCoefficient Y m - z‖ := by
  obtain ⟨N,hN⟩ := eventual_interior_model_floor
  have hlarge := ((tendsto_rpow_atTop (by norm_num : 0 < (1/24:ℝ))).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop 16
  apply Filter.eventually_atTop.mp
  filter_upwards [hlarge,Filter.eventually_ge_atTop N,Filter.eventually_ge_atTop (1:ℕ)]
    with Y hY hy hy1
  intro m hlo hhi he z hz
  have hYpos : (0:ℝ) < Y := by exact_mod_cast hy1
  have hsplit : (Y:ℝ)^(23/24:ℝ)*(Y:ℝ)^(1/24:ℝ) = Y := by
    rw [← Real.rpow_add hYpos]; norm_num
  have hz' : 16*‖z‖ ≤ Y := by
    rw [← hsplit, mul_comm (16:ℝ)]
    exact mul_le_mul hz hY (by norm_num) (by positivity)
  have hfloor : (Y:ℝ)/8 ≤ (modelCoefficient Y m).re := hN Y hy m hlo hhi he
  have hnorm := Complex.re_le_norm (modelCoefficient Y m - z)
  rw [Complex.sub_re] at hnorm
  linarith [Complex.re_le_norm z]

end
end Goldbach.ReflectedArcModel
