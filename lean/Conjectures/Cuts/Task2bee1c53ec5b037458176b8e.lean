import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

open Finset MeasureTheory
open scoped ComplexConjugate

namespace DigitPairing

-- Orthogonality calculation adapted from the repository's triple moment proof (#4325).
private noncomputable def mode (m : ℤ) (t : ℝ) : ℂ :=
  Complex.exp ((m:ℂ) * (2*(Real.pi:ℂ)*Complex.I) * (t:ℂ))

private lemma orthogonal (m : ℤ) :
    (∫ t in (0:ℝ)..1, mode m t) = if m = 0 then 1 else 0 := by
  by_cases hm : m = 0
  · simp [hm,mode]
  · have hc : (m:ℂ)*(2*(Real.pi:ℂ)*Complex.I) ≠ 0 :=
      mul_ne_zero (by exact_mod_cast hm) (mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero)
    simp only [mode, integral_exp_mul_complex hc]
    simp [hm, Complex.exp_int_mul_two_pi_mul_I]

end DigitPairing

open DigitPairing in
theorem Conjectures.Cuts.Task2bee1c53ec5b037458176b8e :
have x1 : ℕ → ℝ → ℂ := fun (x1 : ℕ) (x2 : ℝ) => Complex.exp ((2 : ℂ) * (↑Real.pi : ℂ) * Complex.I * (↑x1 : ℂ) * (↑x2 : ℂ)); ∀ (x2 x3 : ℕ) (x4 : ℕ → Finset ℕ) (x5 : Finset ℕ),   have x6 : Finset (Fin x3 → ℕ) := Fintype.piFinset fun (x6 : Fin x3) => x4 (↑x6 : ℕ);   have x7 : (Fin x3 → ℕ) → ℕ := fun (x7 : Fin x3 → ℕ) => ∑ x8 : Fin x3, x7 x8 * x2 ^ (↑x8 : ℕ);   (↑{x8 ∈ x6 | x7 x8 ∈ x5}.card : ℝ) = (∫ (x8 : ℝ) in (0 : ℝ)..(1 : ℝ), (∏ x9 : Fin x3, ∑ x10 ∈ x4 (↑x9 : ℕ), x1 (x10 * x2 ^ (↑x9 : ℕ)) x8) * Star.star (∑ x9 ∈ x5, x1 x9 x8)).re := by
  classical
  intro e b k D R W v
  have expand (t : ℝ) : (∏ i : Fin k, ∑ d ∈ D i.val, e (d*b^i.val) t) =
      ∑ w ∈ W, e (v w) t := by
    rw [prod_univ_sum]
    apply sum_congr rfl
    intro w _
    dsimp [e,v]
    rw [← Complex.exp_sum]
    congr 1
    push_cast
    simp only [Finset.sum_mul,Finset.mul_sum]
  let pairs := W.product R
  let M (z : (Fin k → ℕ) × ℕ) := mode ((v z.1:ℤ)-z.2)
  have point (t : ℝ) : (∏ i : Fin k, ∑ d ∈ D i.val, e (d*b^i.val) t) *
      star (∑ n ∈ R, e n t) = ∑ z ∈ pairs, M z t := by
    change _ * conj (∑ n ∈ R, e n t) = _
    rw [expand,map_sum,sum_mul,show pairs = W ×ˢ R by rfl, sum_product]
    apply sum_congr rfl
    intro w _
    rw [mul_sum]
    apply sum_congr rfl
    intro n _
    dsimp only [e,M,mode]
    rw [← Complex.exp_conj, ← Complex.exp_add]
    congr 1
    simp only [map_mul,map_ofNat,Complex.conj_ofReal,Complex.conj_I,map_natCast,
      Int.cast_sub,Int.cast_natCast]
    ring
  have integral (z : (Fin k → ℕ) × ℕ) : (∫ t in (0:ℝ)..1, M z t) =
      if v z.1 = z.2 then 1 else 0 := by
    simp [M,orthogonal,sub_eq_zero]
  simp_rw [point]
  rw [intervalIntegral.integral_finsetSum (fun z _ =>
    (show Continuous (M z) by change Continuous (fun t : ℝ => Complex.exp (_ * (t:ℂ))); fun_prop).intervalIntegrable ..)]
  simp_rw [integral]
  rw [show pairs = W ×ˢ R by rfl,sum_product]
  have count (w : Fin k → ℕ) : (∑ n ∈ R, (if v w = n then (1:ℂ) else 0)) =
      if v w ∈ R then 1 else 0 := by simp
  simp_rw [count]
  rw [← sum_filter]
  simp
