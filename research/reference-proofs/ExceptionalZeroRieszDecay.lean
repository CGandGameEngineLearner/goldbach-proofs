import Conjectures.Goldbach.ExceptionalZeroRieszEstimate

/-! Uniform exponential decay for the first Riesz mean in the rectangle
of conductors up to exp u and lengths satisfying u² ≤ log x ≤ 2u².
All lengths in the interval share the same possible exceptional residue. -/

namespace Conjectures.Goldbach.ExceptionalZeroRieszDecay

open Real DirichletCharacter
open _root_.Goldbach GoldbachSmoothing ExceptionalZeroRieszEstimate
open Conjectures.Goldbach.EstermannAlmostAllPolylog_aux.OAI.LargePrimeGaps (rieszSum)
open scoped Classical

private theorem height_le {u : ℝ} (hu : 8≤u) (Q : ℕ) [NeZero Q] (hQ : (Q:ℝ)≤exp u) :
    logHeight Q (exp u+1) ≤ 3*u := by
  have tp := exp_pos u
  have t1 : 1≤exp u := one_le_exp (by linarith)
  have qp : 0<(Q:ℝ) := by exact_mod_cast NeZero.pos Q
  have first : 2*(Q:ℝ)*(2+|exp u+1|) ≤ 8*(exp u*exp u) := by
    rw [abs_of_pos (by positivity)]
    calc
      _ ≤ 2*exp u*(2+(exp u+1)) := by gcongr
      _ ≤ 2*exp u*(4*exp u) := by gcongr; linarith
      _ = _ := by ring
  apply (Real.log_le_log (by positivity) first).trans
  rw [Real.log_mul (by norm_num) (mul_ne_zero tp.ne' tp.ne'),Real.log_mul tp.ne' tp.ne',Real.log_exp]
  linarith only [hu,Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<8)]

private theorem saved_power {x u a σ : ℝ} (hx : 1≤x) (hu : 0<u) (ha : 0≤a)
    (low : u^2≤log x) (hs : σ≤1-2*a/u) : x^σ ≤ x*exp (-(2*a*u)) := by
  have xp := zero_lt_one.trans_le hx
  rw [rpow_def_of_pos xp,←Real.exp_log xp,Real.log_exp,←exp_add,exp_le_exp]
  have mul1 := mul_le_mul_of_nonneg_left hs (log_nonneg hx)
  have mul2 := mul_le_mul_of_nonneg_right low (by positivity : 0≤2*a/u)
  have cancel : u^2*(2*a/u)=2*a*u := by field_simp
  rw [cancel] at mul2
  linarith only [mul1,mul2]

private theorem right_power {x u : ℝ} (hx : 1≤x) (hu : 0<u) (hi : log x≤2*u^2) :
    x^(1+1/u^2) ≤ x*exp 2 := by
  have xp := zero_lt_one.trans_le hx
  rw [rpow_def_of_pos xp,←Real.exp_log xp,Real.log_exp,←exp_add,exp_le_exp]
  have := (div_le_iff₀ (sq_pos_of_pos hu)).mpr hi
  linarith only [show log x*(1+1/u^2) = log x + log x/u^2 by ring,this]

theorem square_exp_bound {a u : ℝ} (ha : 0<a) (hu : 0≤u) :
    u^2*exp (-(2*a*u)) ≤ (2/a^2)*exp (-(a*u)) := by
  have ser := Real.pow_div_factorial_le_exp (a*u) (mul_nonneg ha.le hu) 2
  norm_num at ser
  have bound : u^2 ≤ (2/a^2)*exp (a*u) := by
    have := (le_div_iff₀ (sq_pos_of_pos ha)).mpr (show u^2*a^2 ≤ 2*exp (a*u) by nlinarith only [ser])
    calc
      _ ≤ 2*exp (a*u)/a^2 := this
      _ = _ := by ring
  apply (mul_le_mul_of_nonneg_right bound (exp_pos _).le).trans_eq
  rw [mul_assoc,←exp_add]
  congr 2; ring

theorem uniform_estimate :
    ∃ a C : ℝ, 0<a ∧ a≤1/4 ∧ 0<C ∧ ∀ (u : ℝ), 8≤u →
      ∀ (Q : ℕ) [NeZero Q], (Q:ℝ)≤exp u → ∃ σ b : ℝ, 1/2≤σ ∧ σ≤1-2*a/u ∧
      ∀ (q : ℕ) [NeZero q], q≤Q → ∀ (χ : DirichletCharacter ℂ q) (x : ℝ),
        1≤x → u^2≤log x → log x≤2*u^2 →
        ‖rieszSum (twistedCoefficient χ) x - model χ x σ b‖ ≤ C*x*exp (-(a*u)) := by
  obtain ⟨c,A,D,hc,c1,hA,hD,finite⟩ := finite_estimate
  let a := c/24
  let C₀ := 72*A*Real.pi + 288*A*exp 2 + 16*(1+D)*exp 2
  have ap : 0<a := by dsimp [a];positivity
  have a1 : a≤1/4 := by dsimp [a];linarith
  have C₀p : 0<C₀ := by dsimp [C₀];positivity
  refine ⟨a,C₀*(2/a^2),ap,a1,by positivity,?_⟩
  intro u hu Q _ hQ
  have up : 0<u := by linarith
  have unit : 1≤u^2 := by nlinarith only [hu,sq_nonneg (u-8)]
  let T := exp u
  let L := logHeight Q (T+1)
  have t1 : 1≤T := one_le_exp up.le
  have tp : 0<T := exp_pos _
  have L1 : 1≤L := logHeight_ge_one Q _
  have lp : 0<L := zero_lt_one.trans_le L1
  have Lu : L≤3*u := height_le hu Q hQ
  obtain ⟨σ,b,left,upper,raw⟩ := finite Q T t1
  change 1-(c/L)/2≤σ at left
  change σ≤1-(c/L)/4 at upper
  have σ0 : 1/2≤σ := by linarith only [left,div_le_self hc.le L1,c1]
  have gain : 2*a/u≤(c/L)/4 := by
    have m := div_le_div_of_nonneg_left hc.le lp Lu
    dsimp [a]
    linarith only [show c/(3*u)/4=2*(c/24)/u by ring,m]
  have σ1 : σ≤1-2*a/u := by linarith
  refine ⟨σ,b,σ0,σ1,?_⟩
  intro q _ leQ χ x hx lo hi
  let U := u^2
  let H := exp (-(2*a*u))
  have gap : T⁻¹≤H := by
    change (exp u)⁻¹≤exp _
    rw [←exp_neg,exp_le_exp]
    nlinarith only [mul_le_mul_of_nonneg_right a1 up.le,up]
  have d2 : (T^2)⁻¹≤H := (inv_anti₀ tp (by nlinarith only [t1,sq_nonneg (T-1)] : T≤T^2)).trans gap
  have l2 : L^2≤9*U := by
    calc
      _ ≤ (3*u)^2 := pow_le_pow_left₀ lp.le Lu 2
      _ = _ := by dsimp [U];ring
  have y0 : 0≤x := zero_le_one.trans hx
  have bnd0 : x^σ≤x*H := saved_power hx up ap.le lo σ1
  have bnd1 : x^(1+1/U)≤x*exp 2 := right_power hx up hi
  have den : 1/(1/U)+D≤(1+D)*U := by
    simp only [one_div,inv_inv]
    nlinarith only [mul_le_mul_of_nonneg_left unit hD]
  have hU : 0<U := sq_pos_of_pos up
  have eta : 1/U≤1 := (div_le_one hU).mpr unit
  have raw' := raw q leQ χ x (1/U) hx (by positivity) eta
  have s1 : 8*(A*L^2)*x^σ*Real.pi ≤ 8*(A*(9*U))*(x*H)*Real.pi := by gcongr
  have s2 : 32*(A*L^2)*x^(1+1/U)/T^2 ≤ 32*(A*(9*U))*(x*exp 2)*H := by
    rw [div_eq_mul_inv];gcongr
  have s3 : 16*(1/(1/U)+D)*x^(1+1/U)/T ≤ 16*((1+D)*U)*(x*exp 2)*H := by
    rw [div_eq_mul_inv];gcongr
  apply raw'.trans
  calc
    _ ≤ (8*(A*(9*U))*(x*H)*Real.pi + 32*(A*(9*U))*(x*exp 2)*H + 16*((1+D)*U)*(x*exp 2)*H) :=
      add_le_add (add_le_add s1 s2) s3
    _ = (C₀*x)*(U*H) := by dsimp [C₀];ring
    _ ≤ (C₀*x)*((2/a^2)*exp (-(a*u))) :=
      mul_le_mul_of_nonneg_left (square_exp_bound ap up.le) (mul_nonneg C₀p.le y0)
    _ = _ := by ring

end Conjectures.Goldbach.ExceptionalZeroRieszDecay

set_option maxHeartbeats 1800000 in
theorem Conjectures.Goldbach.ExceptionalZeroRieszDecay :
by
  classical
  let wt := fun (x : ℝ) (s : ℂ) => (x:ℂ)^s/(s*(s+1))
  exact ∃ a C : ℝ, 0<a ∧ a≤1/4 ∧ 0<C ∧ ∀ (u : ℝ), 8≤u →
    ∀ (Q : ℕ) [NeZero Q], (Q:ℝ)≤Real.exp u → ∃ σ b : ℝ, 1/2≤σ ∧ σ≤1-2*a/u ∧
    ∀ (q : ℕ) [NeZero q], q≤Q → ∀ (χ : DirichletCharacter ℂ q) (x : ℝ),
      1≤x → u^2≤Real.log x → Real.log x≤2*u^2 →
      let P := ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
        χ (n:ZMod q)*(ArithmeticFunction.vonMangoldt n:ℂ)*(1-(n:ℂ)/(x:ℂ))
      let R := (@ite ℂ (χ=1) (Classical.propDecidable _) 1 0)*wt x 1 -
        (@ite ℂ (σ<b ∧ b<1 ∧ (χ ≠ 1 ∨ (b:ℂ) ≠ 1) ∧ DirichletCharacter.LFunction χ (b:ℂ)=0)
          (Classical.propDecidable _) (wt x (b:ℂ)) 0)
      ‖P-R‖ ≤ C*x*Real.exp (-(a*u)) :=
by
  with_unfolding_all exact ExceptionalZeroRieszDecay.uniform_estimate
