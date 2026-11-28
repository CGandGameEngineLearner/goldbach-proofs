import Mathlib

/- Fourier orthogonality for integer modes. The interval integral calculation
uses the same elementary exponential antiderivative as SaladDay, Goldbach
PR 3079, revision 0e1a3dd13643a90c925d13c4e660c445e03820e8 (Apache-2.0).
The eighth moment is obtained by expanding two independent ordered four-tuples. -/
namespace GoldbachIntegerModeMoment
open Finset MeasureTheory
open scoped ComplexConjugate
noncomputable section

def mode (k : ℤ) (t : ℝ) : ℂ := Complex.exp ((2*(Real.pi:ℂ)*Complex.I)*(k:ℂ)*(t:ℂ))

theorem continuous_mode (k : ℤ) : Continuous (mode k) := by unfold mode; fun_prop

theorem integral_mode (k : ℤ) : (∫ t in (0:ℝ)..1, mode k t) = if k=0 then 1 else 0 := by
  by_cases hk : k=0
  · subst k; simp [mode]
  let c : ℂ := (k:ℂ)*(2*(Real.pi:ℂ)*Complex.I)
  have hc : c≠0 := mul_ne_zero (by exact_mod_cast hk)
    (mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero)
  have he (t : ℝ) : mode k t=Complex.exp (c*(t:ℂ)) := by unfold mode c; congr 1; ring
  simp_rw [he]
  rw [integral_exp_mul_complex hc]
  simp [hk,c,Complex.exp_int_mul_two_pi_mul_I]

theorem product_conjugate (a b : ℤ) (t : ℝ) : mode a t * conj (mode b t) = mode (a-b) t := by
  unfold mode
  rw [←Complex.exp_conj,←Complex.exp_add]
  congr 1
  simp only [map_mul,map_ofNat,map_intCast,Complex.conj_ofReal,Complex.conj_I,Int.cast_sub]
  ring

theorem fourth (ν : ℕ → ℤ) (A : Finset ℕ) (t : ℝ) :
    (∑ j ∈ A, mode (ν j) t)^4 = ∑ f ∈ Fintype.piFinset (fun _ : Fin 4 => A), mode (∑ i, ν (f i)) t := by
  classical
  rw [Finset.sum_pow']
  apply sum_congr rfl
  intro f _
  unfold mode
  rw [←Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.mul_sum,Finset.sum_mul]

end
end GoldbachIntegerModeMoment

open Finset MeasureTheory GoldbachIntegerModeMoment
open scoped ComplexConjugate

theorem Conjectures.Cuts.Task4258c8db4b0e59f69cc4fa33 :
  (∀ (x1 : ℕ → ℤ) (x2 : Finset ℕ),   have x3 : ℝ → ℂ := fun (x3 : ℝ) => ∑ x4 ∈ x2, Complex.exp ((2 : ℂ) * ↑Real.pi * Complex.I * ↑(x1 x4) * ↑x3);   have x4 : Finset (Fin (4 : ℕ) → ℕ) := Fintype.piFinset fun (x4 : Fin (4 : ℕ)) => x2;   have x5 : (Fin (4 : ℕ) → ℕ) → ℤ := fun (x5 : Fin (4 : ℕ) → ℕ) => ∑ x6 : Fin (4 : ℕ), x1 (x5 x6);   ∫ (x6 : ℝ) in (0 : ℝ)..(1 : ℝ), ‖x3 x6‖ ^ (8 : ℕ) = ↑{x6 ∈ x4.product x4 | x5 x6.1 = x5 x6.2}.card) := by
  classical
  intro ν A
  let S := fun t : ℝ => ∑ j ∈ A, mode (ν j) t
  let T := Fintype.piFinset (fun _ : Fin 4 => A)
  let freq := fun f : Fin 4 → ℕ => ∑ i, ν (f i)
  let P := T ×ˢ T
  change (∫ t in (0:ℝ)..1, ‖S t‖^8) = ((P.filter (fun z => freq z.1=freq z.2)).card:ℝ)
  have hpoint (t : ℝ) : ((‖S t‖^8:ℝ):ℂ) = ∑ z ∈ P, mode (freq z.1-freq z.2) t := by
    have h4 : (S t)^4 = ∑ f ∈ T, mode (freq f) t := fourth ν A t
    calc
      _ = (S t)^4 * conj ((S t)^4) := by
        rw [Complex.mul_conj,Complex.normSq_eq_norm_sq,norm_pow,←pow_mul]
      _ = _ := by
        rw [h4,map_sum,Finset.sum_mul]
        change _ = ∑ z ∈ T ×ˢ T, mode (freq z.1-freq z.2) t
        rw [Finset.sum_product]
        refine sum_congr rfl fun u _ => ?_
        rw [Finset.mul_sum]
        exact sum_congr rfl fun v _ => product_conjugate _ _ _
  have hreal (k : ℤ) : (∫ t in (0:ℝ)..1, (mode k t).re) = if k=0 then 1 else 0 := by
    calc
      _ = (∫ t in (0:ℝ)..1, mode k t).re :=
        intervalIntegral.intervalIntegral_re (𝕜:=ℂ) ((continuous_mode k).intervalIntegrable (μ:=volume) (0:ℝ) 1)
      _ = _ := by rw [integral_mode]; split <;> rfl
  calc
    _ = ∫ t in (0:ℝ)..1, ∑ z ∈ P, (mode (freq z.1-freq z.2) t).re := by
      apply intervalIntegral.integral_congr
      intro t _
      simpa only [Complex.ofReal_re,Complex.re_sum] using congrArg Complex.re (hpoint t)
    _ = ∑ z ∈ P, ∫ t in (0:ℝ)..1, (mode (freq z.1-freq z.2) t).re :=
      intervalIntegral.integral_finsetSum (fun z _ => (Complex.continuous_re.comp (continuous_mode (freq z.1-freq z.2))).intervalIntegrable ..)
    _ = ∑ z ∈ P, if freq z.1=freq z.2 then (1:ℝ) else 0 :=
      sum_congr rfl fun z _ => by simpa only [sub_eq_zero] using hreal (freq z.1-freq z.2)
    _ = _ := by rw [←Finset.sum_filter]; simp
