import Mathlib
import Conjectures.Goldbach.PrimitivePartnerCubicMass
import Conjectures.Goldbach.DyadicCellShortPrimeFloor

/-!
Pair the cubic row and column estimates by finite Hölder to obtain a
bilinear estimate with two ℓ^(6/5) norms. On a common dyadic height
block, the Gamma quotient also gains a factor 1/√T. Grouping indices
by their character preserves multiplicities and gives the asserted
bound for the weighted zero sum.

The cubic estimate is from PR #4245. The Gamma strip comparison uses
the verified logarithmic ratio estimate in PR #3746.
-/

namespace DyadicZero
open Finset DirichletCharacter
open Conjectures.Goldbach.SharpSingularSeriesRatiosProof
open TwistedGoldbachLocalProduct TwistedGoldbachSingularSeries
open scoped Classical

private theorem geometric_holder {ι : Type*} (s : Finset ι) (f g : ι → ℝ)
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x) (p q : ℝ)
    (hpq : p.HolderConjugate q) (hp : p ≠ 0) (hq : q ≠ 0) :
    ∑ x ∈ s, f x^(1/p) * g x^(1/q) ≤
      (∑ x ∈ s, f x)^(1/p) * (∑ x ∈ s, g x)^(1/q) := by
  have h := Real.inner_le_Lp_mul_Lq_of_nonneg s hpq
    (f := fun x => f x^(1/p)) (g := fun x => g x^(1/q))
    (fun x _ => Real.rpow_nonneg (hf x) _) (fun x _ => Real.rpow_nonneg (hg x) _)
  simpa only [← Real.rpow_mul (hf _), ← Real.rpow_mul (hg _),
    one_div_mul_cancel hp, one_div_mul_cancel hq, Real.rpow_one] using h

private theorem holder_three {ι : Type*} (s : Finset ι) (f g h : ι → ℝ)
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x) (hh : ∀ x, 0 ≤ h x) :
    (∑ x ∈ s, f x^(1/6:ℝ) * g x^(1/6:ℝ) * h x^(2/3:ℝ)) ≤
      (∑ x ∈ s, f x)^(1/6:ℝ) * (∑ x ∈ s, g x)^(1/6:ℝ) * (∑ x ∈ s, h x)^(2/3:ℝ) := by
  have split (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
      (a^(1/2:ℝ)*b^(1/2:ℝ))^(1/3:ℝ) = a^(1/6:ℝ)*b^(1/6:ℝ) := by
    rw [Real.mul_rpow (Real.rpow_nonneg ha _) (Real.rpow_nonneg hb _),
      ← Real.rpow_mul ha, ← Real.rpow_mul hb]
    norm_num
  let H x := (f x)^(1/2:ℝ) * (g x)^(1/2:ℝ)
  have hH x : 0 ≤ H x := mul_nonneg (Real.rpow_nonneg (hf x) _) (Real.rpow_nonneg (hg x) _)
  have half := geometric_holder s f g hf hg 2 2
    (by rw [Real.holderConjugate_iff]; norm_num) (by norm_num) (by norm_num)
  have third := geometric_holder s H h hH hh 3 (3/2)
    (by rw [Real.holderConjugate_iff]; norm_num) (by norm_num) (by norm_num)
  rw [show (1/(3/2):ℝ)=2/3 by norm_num] at third
  calc
    _ = ∑ x ∈ s, (H x)^(1/3:ℝ)*h x^(2/3:ℝ) := by
      simp only [H, split _ _ (hf _) (hg _)]
    _ ≤ _ := third
    _ ≤ ((∑ x ∈ s, f x)^(1/2:ℝ) * (∑ x ∈ s, g x)^(1/2:ℝ))^(1/3:ℝ) *
        (∑ x ∈ s, h x)^(2/3:ℝ) := by
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow (sum_nonneg fun x _ => hH x) half (by norm_num))
        (Real.rpow_nonneg (sum_nonneg fun x _ => hh x) _)
    _ = _ := by rw [split _ _ (sum_nonneg fun x _ => hf x) (sum_nonneg fun x _ => hg x)]

private theorem geom_factors (u v c : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (hc : 0 ≤ c) :
    (u*c)^(1/6:ℝ)*(v*c)^(1/6:ℝ)*(u*v)^(2/3:ℝ) =
      c^(1/3:ℝ)*u^(5/6:ℝ)*v^(5/6:ℝ) := by
  have add (x : ℝ) (hx : 0 ≤ x) : x^(1/6:ℝ)*x^(2/3:ℝ) = x^(5/6:ℝ) := by
    rw [← Real.rpow_add_of_nonneg hx (by norm_num) (by norm_num)]; norm_num
  have pair : c^(1/6:ℝ)*c^(1/6:ℝ)=c^(1/3:ℝ) := by
    rw [← Real.rpow_add_of_nonneg hc (by norm_num) (by norm_num)]; norm_num
  rw [Real.mul_rpow hu hc,Real.mul_rpow hv hc,Real.mul_rpow hu hv,← add _ hu,← add _ hv,← pair]
  ring

private theorem root_cube (x : ℝ) (hx : 0 ≤ x) : (x^3)^(1/3:ℝ)=x := by
  rw [← Real.rpow_natCast x 3,← Real.rpow_mul hx]
  norm_num

private theorem symmetric_series {r s : ℕ} (a : DirichletCharacter ℂ r)
    (b : DirichletCharacter ℂ s) (m : ℕ) : series a b m = series b a m := by
  apply tsum_congr
  intro d
  by_cases hd : d ≠ 0
  · by_cases h : r ∣ d ∧ s ∣ d
    · let _ : NeZero d := ⟨hd⟩
      simp only [coefficient,dite_eq_left hd,dite_eq_left h,dite_eq_left h.symm,gaussCoefficient]
      rw [mul_comm (changeLevel h.1 a) (changeLevel h.2 b),
        mul_comm (gaussSum (changeLevel h.1 a) ZMod.stdAddChar) (gaussSum (changeLevel h.2 b) ZMod.stdAddChar)]
    · have h' : ¬(s ∣ d ∧ r ∣ d) := fun H => h H.symm
      simp [coefficient,hd,h,h']
  · simp [coefficient,hd]

theorem bilinear (m : ℕ) (hm : 0 < m) (he : Even m)
    (F : Finset (Σ s : ℕ, DirichletCharacter ℂ s))
    (hf : ∀ b ∈ F, b.1 ≠ 0 ∧ b.2.IsPrimitive)
    (u v : (Σ s : ℕ, DirichletCharacter ℂ s) → ℝ) :
    (∑ a ∈ F, ∑ b ∈ F, |u a| * ‖series a.2 b.2 m‖ * |v b|) ≤
      (3:ℝ)^(1/3:ℝ) * ‖series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m‖ *
      (∑ a ∈ F, |u a|^(6/5:ℝ))^(5/6:ℝ) * (∑ b ∈ F, |v b|^(6/5:ℝ))^(5/6:ℝ) := by
  let K (a b : Σ s : ℕ, DirichletCharacter ℂ s) := ‖series a.2 b.2 m‖
  let O := ‖series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m‖
  let U a := |u a|^(6/5:ℝ)
  let V a := |v a|^(6/5:ℝ)
  have ku a b : 0 ≤ K a b := norm_nonneg _
  have un a : 0 ≤ U a := Real.rpow_nonneg (abs_nonneg _) _
  have vn b : 0 ≤ V b := Real.rpow_nonneg (abs_nonneg _) _
  have on : 0 ≤ O := norm_nonneg _
  have row (a) (ha : a ∈ F) : ∑ b ∈ F, (K a b)^3 ≤ 3*O^3 := by
    let _ : NeZero a.1 := ⟨(hf a ha).1⟩
    exact Conjectures.Goldbach.PrimitivePartnerCubicMass a.1 a.2 (hf a ha).2 m hm he F hf
  have scol (b) (hb : b ∈ F) : ∑ a ∈ F, (K a b)^3 ≤ 3*O^3 := by
    simpa only [K, symmetric_series b.2 _ m] using row b hb
  let P := F ×ˢ F
  let X (t : (Σ s : ℕ, DirichletCharacter ℂ s) × (Σ s : ℕ, DirichletCharacter ℂ s)) := U t.1*(K t.1 t.2)^3
  let Y (t : (Σ s : ℕ, DirichletCharacter ℂ s) × (Σ s : ℕ, DirichletCharacter ℂ s)) := V t.2*(K t.1 t.2)^3
  let Z (t : (Σ s : ℕ, DirichletCharacter ℂ s) × (Σ s : ℕ, DirichletCharacter ℂ s)) := U t.1*V t.2
  have x0 t : 0 ≤ X t := mul_nonneg (un _) (pow_nonneg (ku _ _) _)
  have y0 t : 0 ≤ Y t := mul_nonneg (vn _) (pow_nonneg (ku _ _) _)
  have z0 t : 0 ≤ Z t := mul_nonneg (un _) (vn _)
  have xsum : ∑ t ∈ P, X t ≤ (∑ a ∈ F,U a)*(3*O^3) := by
    simp only [P,X,sum_product,← mul_sum,sum_mul]
    exact sum_le_sum fun a ha => mul_le_mul_of_nonneg_left (row a ha) (un a)
  have ysum : ∑ t ∈ P, Y t ≤ (∑ b ∈ F,V b)*(3*O^3) := by
    simp only [P,Y,sum_product_right,← mul_sum,sum_mul]
    exact sum_le_sum fun b hb => mul_le_mul_of_nonneg_left (scol b hb) (vn b)
  have zsum : ∑ t ∈ P, Z t = (∑ a ∈ F,U a)*(∑ b ∈ F,V b) := by
    simp only [P,Z,sum_product,←mul_sum,sum_mul]
  have power (x : ℝ) : (|x|^(6/5:ℝ))^(5/6:ℝ) = |x| := by
    rw [← Real.rpow_mul (abs_nonneg _)]; norm_num
  calc
    _ = ∑ t ∈ P, X t^(1/6:ℝ)*Y t^(1/6:ℝ)*Z t^(2/3:ℝ) := by
      simp only [P,X,Y,Z,sum_product,geom_factors _ _ _ (un _) (vn _) (pow_nonneg (ku _ _) _),
        root_cube _ (ku _ _),U,V,power,K,mul_comm (|u _|) (‖_‖)]
    _ ≤ _ := holder_three P X Y Z x0 y0 z0
    _ ≤ ((∑ a ∈ F,U a)*(3*O^3))^(1/6:ℝ) * ((∑ b ∈ F,V b)*(3*O^3))^(1/6:ℝ) *
        ((∑ a ∈ F,U a)*(∑ b ∈ F,V b))^(2/3:ℝ) := by
      rw [zsum]
      gcongr
    _ = _ := by
      rw [geom_factors _ _ _ (sum_nonneg fun a _ => un a) (sum_nonneg fun b _ => vn b)
        (by positivity), Real.mul_rpow (by norm_num : (0:ℝ) ≤ 3) (pow_nonneg on _),root_cube _ on]

end DyadicZero

namespace PartnerBeta

open Complex
open scoped ComplexConjugate

/-- The reflection formula on the central line, where the reflected point is
the complex conjugate, converts the Gamma norm square into a hyperbolic cosine. -/
private theorem gamma_midline (t : ℝ) :
    Real.exp (-(Real.pi*|t|)/2) ≤ ‖Gamma ((1/2:ℂ) + (t:ℂ)*I)‖ ∧
    ‖Gamma ((1/2:ℂ) + (t:ℂ)*I)‖ ≤ 3*Real.exp (-(Real.pi*|t|)/2) := by
  let z : ℂ := 1/2 + (t:ℂ)*I
  have hc : 1-z = conj z := by
    have zz : z = ((1/2:ℝ):ℂ) + (t:ℂ)*I := by push_cast; rfl
    rw [zz, map_add, map_mul, conj_ofReal, conj_ofReal, conj_I]
    push_cast
    ring
  have hs : sin ((Real.pi:ℂ)*z) = (Real.cosh (Real.pi*t) : ℂ) := by
    have hh : (Real.pi:ℂ)*z = (Real.pi:ℂ)/2 + ((Real.pi*t:ℝ):ℂ)*I := by
      dsimp [z]; push_cast; ring
    rw [hh, sin_add, sin_pi_div_two, cos_pi_div_two, cos_mul_I]
    simp
  have ref := congrArg norm (Gamma_mul_Gamma_one_sub z)
  rw [hc, Gamma_conj, hs, norm_mul, Complex.norm_conj, norm_div,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.cosh_pos _)] at ref
  have ht : |Real.pi*t| = Real.pi*|t| := by rw [abs_mul, abs_of_pos Real.pi_pos]
  rw [← Real.cosh_abs (Real.pi*t), ht] at ref
  let u := Real.pi * |t|
  let v := ‖Gamma z‖ * Real.exp (u/2)
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hcosh := (eq_div_iff (Real.cosh_pos u).ne').mp ref
  have exp_bounds : Real.cosh u ≤ Real.exp u ∧ Real.exp u ≤ 2*Real.cosh u := by
    rw [Real.cosh_eq]
    have hd := Real.exp_le_exp.mpr (show -u ≤ u by linarith)
    constructor <;> linarith [Real.exp_pos (-u)]
  have he : Real.exp (u/2) * Real.exp (u/2) = Real.exp u := by
    rw [← Real.exp_add]; congr 1; ring
  have hv : v^2 = ‖Gamma z‖^2 * Real.exp u := by
    dsimp [v]
    rw [mul_pow, pow_two (Real.exp _), he]
  have ht₁ := mul_le_mul_of_nonneg_left exp_bounds.1 (sq_nonneg ‖Gamma z‖)
  have ht₂ := mul_le_mul_of_nonneg_left exp_bounds.2 (sq_nonneg ‖Gamma z‖)
  have hsq : 1 ≤ v^2 ∧ v^2 ≤ 9 := by
    constructor <;> rw [hv] <;> nlinarith [Real.pi_gt_three, Real.pi_lt_four]
  have hv0 : 0 ≤ v := by dsimp [v]; positivity
  have hvbound : 1 ≤ v ∧ v ≤ 3 := by
    constructor <;> nlinarith [hsq.1, hsq.2]
  have inverse : Real.exp (-u/2) * Real.exp (u/2) = 1 := by
    rw [←Real.exp_add, show -u/2 + u/2 = 0 by ring, Real.exp_zero]
  change Real.exp (-u/2) ≤ ‖Gamma z‖ ∧ ‖Gamma z‖ ≤ 3*Real.exp (-u/2)
  constructor
  · apply le_of_mul_le_mul_right _ (Real.exp_pos (u/2))
    rw [inverse]
    exact hvbound.1
  · apply le_of_mul_le_mul_right _ (Real.exp_pos (u/2))
    rw [mul_assoc, inverse, mul_one]
    exact hvbound.2

/-- A uniform vertical strip estimate obtained by moving horizontally from
the critical line. -/
theorem gamma_strip_of_log
    (ratio : ∀ a b t : ℝ, 1/8 ≤ a → a ≤ b → b ≤ 3 →
      |Real.log ‖Gamma ((b:ℂ)+t*I)‖ - Real.log ‖Gamma ((a:ℂ)+t*I)‖ -
        (b-a)*Real.log (|t|+2)| ≤ (59+|Real.eulerMascheroniConstant|)*(b-a)) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ a t : ℝ, 1/2 ≤ a → a ≤ 2 →
      (|t|+2)^(a-1/2)*Real.exp (-(Real.pi*|t|)/2) ≤ C*‖Gamma ((a:ℂ)+(t:ℂ)*I)‖ ∧
      ‖Gamma ((a:ℂ)+(t:ℂ)*I)‖ ≤ C*((|t|+2)^(a-1/2)*Real.exp (-(Real.pi*|t|)/2)) := by
  let B := 2*(59+|Real.eulerMascheroniConstant|)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hE : 1 ≤ Real.exp B := Real.one_le_exp hB
  refine ⟨3*Real.exp B, by linarith, ?_⟩
  intro a t ha ha'
  let base := ‖Gamma ((1/2:ℂ)+(t:ℂ)*I)‖
  let target := ‖Gamma ((a:ℂ)+(t:ℂ)*I)‖
  let rad := (|t|+2)^(a-1/2)
  let decay := Real.exp (-(Real.pi*|t|)/2)
  have hb : 0 < base := by
    apply norm_pos_iff.mpr
    apply Gamma_ne_zero_of_re_pos
    simp
  have ht : 0 < target := by
    apply norm_pos_iff.mpr
    apply Gamma_ne_zero_of_re_pos
    simp; linarith
  have hrad : 0 < |t| + 2 := by positivity
  have hrad' : 0 ≤ rad := (Real.rpow_pos_of_pos hrad _).le
  have hlog := ratio (1/2) a t (by norm_num) ha (by linarith)
  push_cast at hlog
  change |Real.log target - Real.log base - (a-1/2)*Real.log (|t|+2)| ≤ _ at hlog
  have hbb : (59+|Real.eulerMascheroniConstant|)*(a-1/2) ≤ B := by
    change _ ≤ 2*(59+|Real.eulerMascheroniConstant|)
    nlinarith [mul_nonneg (by positivity : 0 ≤ 59+|Real.eulerMascheroniConstant|) (show 0 ≤ 2-(a-1/2) by linarith)]
  have bounds := abs_le.mp (hlog.trans hbb)
  have hr : Real.exp ((a-1/2)*Real.log (|t|+2)) = rad := by
    dsimp [rad]
    rw [Real.rpow_def_of_pos hrad, mul_comm]
  have hlo : rad*base ≤ Real.exp B * target := by
    have h := Real.exp_le_exp.mpr (show (a-1/2)*Real.log (|t|+2)+Real.log base ≤ B+Real.log target by
      linarith [bounds.1])
    rwa [Real.exp_add, Real.exp_add, Real.exp_log hb, Real.exp_log ht, hr] at h
  have hhi : target ≤ Real.exp B*(rad*base) := by
    have h := Real.exp_le_exp.mpr (show Real.log target ≤ B+((a-1/2)*Real.log (|t|+2)+Real.log base) by
      linarith [bounds.2])
    rwa [Real.exp_log ht, Real.exp_add, Real.exp_add, Real.exp_log hb, hr] at h
  have hmid : decay ≤ base ∧ base ≤ 3*decay := gamma_midline t
  change rad*decay ≤ 3*Real.exp B*target ∧ target ≤ (3*Real.exp B)*(rad*decay)
  constructor
  · exact ((mul_le_mul_of_nonneg_left hmid.1 hrad').trans hlo).trans (by
      nlinarith [mul_nonneg (Real.exp_pos B).le ht.le])
  · calc
      target ≤ Real.exp B*(rad*base) := hhi
      _ ≤ Real.exp B*(rad*(3*decay)) := by gcongr; exact hmid.2
      _ = _ := by ring

theorem gamma_strip :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ a t : ℝ, 1/2 ≤ a → a ≤ 2 →
      (|t|+2)^(a-1/2)*Real.exp (-(Real.pi*|t|)/2) ≤ C*‖Gamma ((a:ℂ)+(t:ℂ)*I)‖ ∧
      ‖Gamma ((a:ℂ)+(t:ℂ)*I)‖ ≤ C*((|t|+2)^(a-1/2)*Real.exp (-(Real.pi*|t|)/2)) :=
  gamma_strip_of_log OAI.Ostmann.Vwq

end PartnerBeta

namespace DyadicZero

private noncomputable def betaWeight (a t : ℝ) :=
  (|t|+2)^(a-1/2) * Real.exp (-(Real.pi*|t|)/2)

private theorem weight_pos (a t : ℝ) : 0 < betaWeight a t := by
  unfold betaWeight
  positivity

/-- If the output height is large the powers give a square-root saving.
Otherwise the numerator has at least one full block of extra exponential decay. -/
private theorem weight_block (a b t u T : ℝ) (hT : 1 ≤ T)
    (ha : 1/2 ≤ a) (ha' : a ≤ 1) (hb : 1/2 ≤ b) (hb' : b ≤ 1)
    (ht : T ≤ |t|) (ht' : |t| ≤ 2*T) (hu : T ≤ |u|) (hu' : |u| ≤ 2*T) :
    Real.sqrt T * betaWeight a t * betaWeight b u ≤ 4 * betaWeight (a+b) (t+u) := by
  have Tp : 0 < T := by linarith
  let p := a+b-1
  have p1 : p ≤ 1 := by dsimp [p]; linarith
  have powers : (|t|+2)^(a-1/2) * (|u|+2)^(b-1/2) ≤ 4 * T^p := by
    calc
      _ ≤ (4*T)^(a-1/2) * (4*T)^(b-1/2) := by
        apply mul_le_mul
        · exact Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)
        · exact Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)
        · positivity
        · positivity
      _ = (4:ℝ)^p * T^p := by
        rw [← Real.rpow_add (by positivity)]
        rw [show a-1/2+(b-1/2)=p by dsimp [p]; ring, Real.mul_rpow (by norm_num) Tp.le]
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤4) p1
  let q := a+b-1/2
  have q0 : 0 ≤ q := by dsimp [q]; linarith
  have sqpow : Real.sqrt T * T^p = T^q := by
    rw [Real.sqrt_eq_rpow, ←Real.rpow_add Tp]
    congr 1
    dsimp [p,q]; ring
  have core : T^q * Real.exp (-(Real.pi*|t|)/2 + -(Real.pi*|u|)/2) ≤
      (|t+u|+2)^q * Real.exp (-(Real.pi*|t+u|)/2) := by
    by_cases large : T ≤ |t+u|
    · apply mul_le_mul
      · exact Real.rpow_le_rpow Tp.le (by linarith) q0
      · apply Real.exp_le_exp.mpr
        linarith [mul_le_mul_of_nonneg_left (abs_add_le t u) Real.pi_pos.le]
      · positivity
      · positivity
    · have slack : T ≤ |t| + |u| - |t+u| := by linarith
      have decay := mul_le_mul Real.pi_gt_three.le slack Tp.le Real.pi_pos.le
      have lg := Real.log_le_sub_one_of_pos Tp
      have hq : q ≤ 3/2 := by dsimp [q]; linarith
      calc
        _ ≤ T^(3/2:ℝ) * Real.exp (-(Real.pi*|t|)/2 + -(Real.pi*|u|)/2) :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hT hq) (by positivity)
        _ ≤ Real.exp (-(Real.pi*|t+u|)/2) := by
          rw [Real.rpow_def_of_pos Tp, ← Real.exp_add]
          apply Real.exp_le_exp.mpr
          linarith
        _ ≤ _ := le_mul_of_one_le_left (by positivity)
          (Real.one_le_rpow (by linarith [abs_nonneg (t+u)]) q0)
  calc
    _ = ((|t|+2)^(a-1/2)*(|u|+2)^(b-1/2)) *
        (Real.sqrt T * Real.exp (-(Real.pi*|t|)/2 + -(Real.pi*|u|)/2)) := by
      unfold betaWeight; rw [Real.exp_add]; ring
    _ ≤ (4*T^p) * (Real.sqrt T * Real.exp (-(Real.pi*|t|)/2 + -(Real.pi*|u|)/2)) :=
      mul_le_mul_of_nonneg_right powers (by positivity)
    _ = 4 * ((Real.sqrt T * T^p) * Real.exp (-(Real.pi*|t|)/2 + -(Real.pi*|u|)/2)) := by ring
    _ ≤ _ := by rw [sqpow]; exact mul_le_mul_of_nonneg_left core (by norm_num)

private theorem beta_bound_of_strip
    (strip : ∃ C : ℝ, 1 ≤ C ∧ ∀ a t : ℝ, 1/2 ≤ a → a ≤ 2 →
      betaWeight a t ≤ C*‖Complex.Gamma ((a:ℂ)+(t:ℂ)*Complex.I)‖ ∧
      ‖Complex.Gamma ((a:ℂ)+(t:ℂ)*Complex.I)‖ ≤ C*betaWeight a t) :
    ∃ C : ℝ, 0 < C ∧ ∀ {T : ℝ} {z w : ℂ}, 1 ≤ T →
      1/2 ≤ z.re → z.re ≤ 1 → 1/2 ≤ w.re → w.re ≤ 1 →
      T ≤ |z.im| → |z.im| ≤ 2*T → T ≤ |w.im| → |w.im| ≤ 2*T →
      ‖Complex.Gamma z * Complex.Gamma w / Complex.Gamma (z+w)‖ ≤ C / Real.sqrt T := by
  obtain ⟨C,hC,H⟩ := strip
  have Cp : 0 < C := by linarith
  refine ⟨4*C^3, by positivity, ?_⟩
  intro T z w hT za za' wa wa' zt zt' wt wt'
  have each (x : ℂ) (ha : 1/2 ≤ x.re) (hb : x.re ≤ 2) :
      betaWeight x.re x.im ≤ C*‖Complex.Gamma x‖ ∧ ‖Complex.Gamma x‖ ≤ C*betaWeight x.re x.im := by
    simpa only [Complex.re_add_im] using H x.re x.im ha hb
  have upz := (each z za (by linarith)).2
  have upw := (each w wa (by linarith)).2
  have low := (each (z+w) (by rw [Complex.add_re]; linarith) (by rw [Complex.add_re]; linarith)).1
  have wp := weight_pos (z+w).re (z+w).im
  have gp : 0 < ‖Complex.Gamma (z+w)‖ := by
    by_contra! hg
    have := mul_nonpos_of_nonneg_of_nonpos Cp.le hg
    linarith
  rw [norm_div,norm_mul,div_le_div_iff₀ gp (Real.sqrt_pos.mpr (by linarith))]
  have block := weight_block z.re w.re z.im w.im T hT za za' wa wa' zt zt' wt wt'
  simp only [Complex.add_re,Complex.add_im] at low
  calc
    _ ≤ (C*betaWeight z.re z.im)*(C*betaWeight w.re w.im)*Real.sqrt T :=
      mul_le_mul_of_nonneg_right (mul_le_mul upz upw (norm_nonneg _) (mul_nonneg Cp.le (weight_pos _ _).le)) (Real.sqrt_nonneg _)
    _ = C^2 * (Real.sqrt T * betaWeight z.re z.im * betaWeight w.re w.im) := by ring
    _ ≤ C^2 * (4*betaWeight (z.re+w.re) (z.im+w.im)) :=
      mul_le_mul_of_nonneg_left block (sq_nonneg _)
    _ ≤ C^2 * (4*(C*‖Complex.Gamma (z+w)‖)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left low (by norm_num)) (sq_nonneg _)
    _ = _ := by ring

theorem beta_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ {T : ℝ} {z w : ℂ}, 1 ≤ T →
      1/2 ≤ z.re → z.re ≤ 1 → 1/2 ≤ w.re → w.re ≤ 1 →
      T ≤ |z.im| → |z.im| ≤ 2*T → T ≤ |w.im| → |w.im| ≤ 2*T →
      ‖Complex.Gamma z * Complex.Gamma w / Complex.Gamma (z+w)‖ ≤ C / Real.sqrt T :=
  beta_bound_of_strip PartnerBeta.gamma_strip

end DyadicZero

namespace DyadicZero
open Finset
open Conjectures.Goldbach.SharpSingularSeriesRatiosProof.TwistedGoldbachLocalProduct

private theorem group_one {ι B : Type*} [Fintype ι] [DecidableEq B]
    (χ : ι → B) (v : ι → ℝ) (f : B → ℝ) :
    (∑ i, f (χ i)*v i) = ∑ b ∈ univ.image χ, f b * (∑ i ∈ univ.filter (fun i => χ i = b), v i) := by
  classical
  symm
  calc
    _ = ∑ b ∈ univ.image χ, ∑ i ∈ univ.filter (fun i => χ i = b), f (χ i)*v i := by
      apply sum_congr rfl
      intro b _
      rw [mul_sum]
      apply sum_congr rfl
      intro i hi
      rw [(mem_filter.mp hi).2]
    _ = _ := sum_fiberwise_of_maps_to (fun i hi => mem_image_of_mem χ hi) _

private theorem group_both {ι B : Type*} [Fintype ι] [DecidableEq B]
    (χ : ι → B) (u v : ι → ℝ) (D : B → B → ℝ) :
    (∑ i, ∑ j, u i * D (χ i) (χ j) * v j) =
        ∑ a ∈ univ.image χ, ∑ b ∈ univ.image χ,
          (∑ i ∈ univ.filter (fun i => χ i = a), u i) * D a b *
            (∑ j ∈ univ.filter (fun j => χ j = b), v j) := by
  classical
  let W (w : ι → ℝ) (b : B) := ∑ j ∈ univ.filter (fun j => χ j = b), w j
  have inner (a : B) : (∑ j, D a (χ j)*v j) =
      ∑ b ∈ univ.image χ, D a b*W v b := group_one χ v (D a)
  calc
    _ = ∑ i, (∑ b ∈ univ.image χ, D (χ i) b * W v b) * u i := by
      apply sum_congr rfl
      intro i _
      rw [← inner, sum_mul]
      apply sum_congr rfl
      intro j _
      ring
    _ = ∑ a ∈ univ.image χ, (∑ b ∈ univ.image χ, D a b * W v b) * W u a :=
      group_one χ u (fun a => ∑ b ∈ univ.image χ, D a b * W v b)
    _ = _ := by
      apply sum_congr rfl
      intro a _
      rw [sum_mul]
      apply sum_congr rfl
      intro b _
      change D a b * W v b * W u a = W u a * D a b * W v b
      ring

private theorem power_split {m : ℕ} (hm : 0 < m) (z w : ℂ) :
    ‖(m : ℂ)^(z+w-1)‖ = (m:ℝ)*(m:ℝ)^(z.re-1)*(m:ℝ)^(w.re-1) := by
  have hp : 0 < (m:ℝ) := by exact_mod_cast hm
  change ‖(((m:ℝ):ℂ)) ^ (z+w-1)‖ = _
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hp]
  rw [show (z+w-1).re = (1 + (z.re-1)) + (w.re-1) by simp; ring,
    Real.rpow_add hp, Real.rpow_add hp, Real.rpow_one]

private theorem collect_kernel {B : Type*} [DecidableEq B] (S : B → B → ℂ)
    (m n : ℕ) (hm : 0 < m) (T C : ℝ)
    (χ : Fin n → B) (z u v : Fin n → ℂ)
    (hk : ∀ i j, ‖Complex.Gamma (z i) * Complex.Gamma (z j) / Complex.Gamma (z i + z j)‖ ≤
      C / Real.sqrt T) :
    let F := univ.image χ
    let W (w : Fin n → ℂ) (b : B) :=
      ∑ i ∈ univ.filter (fun i => χ i = b), ‖w i‖ * (m : ℝ)^((z i).re-1)
    let K (i j : Fin n) := Complex.Gamma (z i) * Complex.Gamma (z j) /
      Complex.Gamma (z i + z j) * (m : ℂ)^(z i + z j - 1)
    ‖∑ i, ∑ j, u i * v j * S (χ i) (χ j) * K i j‖ ≤
      (C*(m:ℝ)/Real.sqrt T) * ∑ a ∈ F, ∑ b ∈ F, |W u a| * ‖S a b‖ * |W v b| := by
  classical
  intro F W K
  let w (f : Fin n → ℂ) (i : Fin n) := ‖f i‖*(m:ℝ)^((z i).re-1)
  let D (a b : B) := ‖S a b‖
  let t := C*(m:ℝ)/Real.sqrt T
  have wpos (f : Fin n → ℂ) (b : B) : 0 ≤ W f b := sum_nonneg fun i _ => by positivity
  have term (i j : Fin n) : ‖u i * v j * S (χ i) (χ j) * K i j‖ ≤ t*(w u i * D (χ i) (χ j) * w v j) := by
    simp only [K,norm_mul,power_split hm]
    calc
      _ ≤ ‖u i‖ * ‖v j‖ * ‖S (χ i) (χ j)‖ *
        ((C/Real.sqrt T) * ((m:ℝ)*(m:ℝ)^((z i).re-1)*(m:ℝ)^((z j).re-1))) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          simpa only [norm_div, norm_mul] using hk i j
      _ = _ := by dsimp only [t,w,D]; ring
  calc
    _ ≤ ∑ i, ∑ j, ‖u i * v j * S (χ i) (χ j) * K i j‖ := by
      apply (norm_sum_le _ _).trans
      exact sum_le_sum fun i _ => norm_sum_le _ _
    _ ≤ ∑ i, ∑ j, t*(w u i*D (χ i) (χ j)*w v j) :=
      sum_le_sum fun i _ => sum_le_sum fun j _ => term i j
    _ = t * ∑ i, ∑ j, w u i*D (χ i) (χ j)*w v j := by simp_rw [mul_sum]
    _ = _ := by
      rw [group_both χ (w u) (w v) D]
      simp only [abs_of_nonneg (wpos _ _)]
      rfl

end DyadicZero

open Finset
open Conjectures.Goldbach.SharpSingularSeriesRatiosProof.TwistedGoldbachLocalProduct

theorem Conjectures.Goldbach.PartnerDyadicZeroBlock : (
by
  classical
  let S := fun {r s : ℕ} (α : DirichletCharacter ℂ r) (β : DirichletCharacter ℂ s) (m : ℕ) =>
    ∑' q : ℕ, if hq : q ≠ 0 then
      let _ : NeZero q := ⟨hq⟩
      if h : r ∣ q ∧ s ∣ q then
        let A := DirichletCharacter.changeLevel h.1 α
        let B := DirichletCharacter.changeLevel h.2 β
        gaussSum A ZMod.stdAddChar * gaussSum B ZMod.stdAddChar *
          gaussSum (A*B)⁻¹ (ZMod.stdAddChar.mulShift (-(m:ZMod q))) / (q.totient:ℂ)^2
      else 0
    else 0
  let O := S (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1)
  let B := Σ s : ℕ, DirichletCharacter ℂ s
  let primitive := fun b : B => b.1 ≠ 0 ∧ b.2.IsPrimitive
  let zeroAt := fun (b : B) (z : ℂ) => if h : b.1 ≠ 0 then
    letI : NeZero b.1 := ⟨h⟩
    DirichletCharacter.LFunction b.2 z = 0
    else False
  let N := fun (F : Finset B) (w : B → ℝ) => (∑ b ∈ F, |w b| ^ (6/5 : ℝ)) ^ (5/6 : ℝ)
  exact
    (∀ m : ℕ, 0 < m → Even m → ∀ F : Finset B, (∀ b ∈ F, primitive b) →
      ∀ u v : B → ℝ, (∑ a ∈ F, ∑ b ∈ F, |u a| * ‖S a.2 b.2 m‖ * |v b|)
        ≤ (3 : ℝ)^(1/3 : ℝ) * ‖O m‖ * N F u * N F v) ∧
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (T : ℝ), 0 < m → Even m → 1 ≤ T →
      ∀ (n : ℕ) (χ : Fin n → B) (z u v : Fin n → ℂ),
      (∀ i, primitive (χ i) ∧ zeroAt (χ i) (z i) ∧
        1/2 ≤ (z i).re ∧ (z i).re ≤ 1 ∧ T ≤ |(z i).im| ∧ |(z i).im| ≤ 2*T) →
      let F := Finset.univ.image χ
      let W := fun (w : Fin n → ℂ) (b : B) =>
        ∑ i ∈ Finset.univ.filter (fun i => χ i = b), ‖w i‖ * (m : ℝ)^((z i).re-1)
      let K := fun i j : Fin n => Complex.Gamma (z i) * Complex.Gamma (z j) /
        Complex.Gamma (z i + z j) * (m : ℂ)^(z i + z j - 1)
      ‖∑ i : Fin n, ∑ j : Fin n, u i * v j * S (χ i).2 (χ j).2 m * K i j‖
        ≤ C * (m : ℝ) * ‖O m‖ / Real.sqrt T * N F (W u) * N F (W v)
) := by
  classical
  dsimp only
  refine ⟨DyadicZero.bilinear, ?_⟩
  obtain ⟨C,hC,est⟩ := DyadicZero.beta_bound
  let A := (3:ℝ)^(1/3:ℝ)
  refine ⟨C*A, by dsimp only [A]; positivity, ?_⟩
  intro m T hm he hT n χ z u v hz
  let B := Σ s : ℕ, DirichletCharacter ℂ s
  let F := Finset.univ.image χ
  let S (a b : B) := series a.2 b.2 m
  let O := ‖series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m‖
  let W (w : Fin n → ℂ) (b : B) :=
    ∑ i ∈ Finset.univ.filter (fun i => χ i = b), ‖w i‖ * (m : ℝ)^((z i).re-1)
  let L (w : B → ℝ) := (∑ a ∈ F, |w a|^(6/5:ℝ))^(5/6:ℝ)
  have primitive (b : B) (hb : b ∈ F) : b.1 ≠ 0 ∧ b.2.IsPrimitive := by
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hb
    exact (hz i).1
  have kernel (i j : Fin n) :
      ‖Complex.Gamma (z i) * Complex.Gamma (z j) / Complex.Gamma (z i+z j)‖ ≤
      C / Real.sqrt T := by
    obtain ⟨_, _, hi₁, hi₂, hi₃, hi₄⟩ := hz i
    obtain ⟨_, _, hj₁, hj₂, hj₃, hj₄⟩ := hz j
    exact est hT hi₁ hi₂ hj₁ hj₂ hi₃ hi₄ hj₃ hj₄
  calc
    _ ≤ (C*(m:ℝ)/Real.sqrt T) * ∑ a ∈ F, ∑ b ∈ F, |W u a| * ‖S a b‖ * |W v b| :=
      DyadicZero.collect_kernel S m n hm T C χ z u v kernel
    _ ≤ (C*(m:ℝ)/Real.sqrt T) * (A * O * L (W u) * L (W v)) :=
      mul_le_mul_of_nonneg_left (DyadicZero.bilinear m hm he F primitive (W u) (W v))
        (by positivity)
    _ = _ := by
      change _ = (C*A)*(m:ℝ)*O/Real.sqrt T*L (W u)*L (W v)
      ring
