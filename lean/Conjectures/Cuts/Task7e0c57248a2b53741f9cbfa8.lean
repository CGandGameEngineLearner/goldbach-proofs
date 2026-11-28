import Mathlib

/-!
Weighted digit-tuple target-hit count as the real part of a factored trigonometric inner product.

Adapted from `Conjectures.Cuts.Task2bee1c53ec5b037458176b8e` (same character machinery, with the
digit weights `b ^ i` replaced by an arbitrary weight tuple `w : Fin k → ℕ` and a fixed digit set).

The additive character `e n t = exp (2 π i n t)` satisfies `e (u + v) = e u * e v`, `conj (e n t) =
e (-n) t` and `∫ t in 0..1, e (m t) = [m = 0]`.  Expanding the product over the coordinates turns
the integrand into `∑ w ∈ W, ∑ n ∈ R, e (v w) t * conj (e n t)`, whose integral is the number of
tuples with `v w ∈ R`.  Self-contained: Mathlib only.
-/

open Finset MeasureTheory
open scoped ComplexConjugate

namespace Conjectures.Cuts.Task7e0c57248a2b53741f9cbfa8_aux

noncomputable def E (x : ℝ) : ℂ := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

lemma phase_add (u v : ℝ) : E (u + v) = E u * E v := by
  unfold E
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma fourier_mode (m : ℤ) :
    (∫ t in (0 : ℝ)..1, E ((m : ℝ) * t)) = if m = 0 then 1 else 0 := by
  by_cases hm : m = 0
  · subst m
    simp [E]
  let c : ℂ := (m : ℂ) * (2 * Real.pi * Complex.I)
  have he (t : ℝ) : E ((m : ℝ) * t) = Complex.exp (c * (t : ℂ)) := by
    unfold E c
    congr 1
    push_cast
    ring
  have hc : c ≠ 0 := by
    dsimp [c]
    exact mul_ne_zero (by exact_mod_cast hm)
      (mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero)
  simp_rw [he]
  rw [integral_exp_mul_complex hc]
  simp [hm, c, Complex.exp_int_mul_two_pi_mul_I]

lemma eneg (x : ℝ) : conj (E x) = E (-x) := by
  unfold E
  rw [← Complex.exp_conj]
  congr 1
  push_cast
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  ring

end Conjectures.Cuts.Task7e0c57248a2b53741f9cbfa8_aux

open Conjectures.Cuts.Task7e0c57248a2b53741f9cbfa8_aux in
theorem Conjectures.Cuts.Task7e0c57248a2b53741f9cbfa8 :
    have x1 : ℕ → ℝ → ℂ := fun (x1 : ℕ) (x2 : ℝ) => Complex.exp ((2 : ℂ) * ↑Real.pi * Complex.I * ↑x1 * ↑x2); ∀ (x2 : ℕ) (x3 : Finset ℕ) (x4 : Fin x2 → ℕ) (x5 : Finset ℕ),   have x6 : Finset (Fin x2 → ℕ) := Fintype.piFinset fun (x6 : Fin x2) => x3;   have x7 : (Fin x2 → ℕ) → ℕ := fun (x7 : Fin x2 → ℕ) => ∑ x8 : Fin x2, x7 x8 * x4 x8;   ↑{x8 ∈ x6 | x7 x8 ∈ x5}.card = (∫ (x8 : ℝ) in (0 : ℝ)..(1 : ℝ), (∏ x9 : Fin x2, ∑ x10 ∈ x3, x1 (x10 * x4 x9) x8) * Star.star (∑ x9 ∈ x5, x1 x9 x8)).re := by
  classical
  intro e k D w R W v
  have charEq (n : ℕ) (t : ℝ) : e n t = E ((n : ℝ) * t) := by
    dsimp [e, E]
    congr 1
    push_cast
    ring
  have orth (u n : ℕ) :
      (∫ t in (0 : ℝ)..1, e u t * conj (e n t)) = if u = n then 1 else 0 := by
    have phase (t : ℝ) : e u t * conj (e n t) = E ((((u : ℤ) - (n : ℤ) : ℤ) : ℝ) * t) := by
      rw [charEq, charEq, eneg, ← phase_add]
      congr 1
      push_cast
      ring
    simp_rw [phase]
    rw [fourier_mode]
    by_cases h : u = n
    · subst n
      simp
    · have hh : (u : ℤ) - (n : ℤ) ≠ 0 := by omega
      simp [h, hh]
  have expand (t : ℝ) : (∏ i : Fin k, ∑ d ∈ D, e (d * w i) t) = ∑ u ∈ W, e (v u) t := by
    rw [Finset.prod_univ_sum]
    apply Finset.sum_congr rfl
    intro u _
    dsimp only [e, v]
    rw [← Complex.exp_sum]
    congr 1
    push_cast
    simp only [Finset.mul_sum, Finset.sum_mul]
  have iden : (∫ t in (0 : ℝ)..1, (∏ i : Fin k, ∑ d ∈ D, e (d * w i) t) *
      star (∑ n ∈ R, e n t)) = ((W.filter (fun u => v u ∈ R)).card : ℂ) := by
    have ep (t : ℝ) : (∏ i : Fin k, ∑ d ∈ D, e (d * w i) t) * star (∑ n ∈ R, e n t) =
        ∑ u ∈ W, ∑ n ∈ R, e (v u) t * conj (e n t) := by
      rw [expand]
      change (∑ u ∈ W, e (v u) t) * conj (∑ n ∈ R, e n t) = _
      rw [map_sum, Finset.sum_mul]
      simp only [Finset.mul_sum]
    simp_rw [ep]
    rw [intervalIntegral.integral_finsetSum (fun u _ =>
      (show Continuous (fun t => ∑ n ∈ R, e (v u) t * conj (e n t)) by
        dsimp [e]; fun_prop).intervalIntegrable ..)]
    have row (u : Fin k → ℕ) :
        (∫ t in (0 : ℝ)..1, ∑ n ∈ R, e (v u) t * conj (e n t)) = if v u ∈ R then (1 : ℂ) else 0 := by
      rw [intervalIntegral.integral_finsetSum (fun n (_ : n ∈ R) =>
        (show Continuous (fun t => e (v u) t * conj (e n t)) by dsimp [e]; fun_prop).intervalIntegrable ..)]
      simp_rw [orth]
      simp
    simp_rw [row]
    exact Finset.sum_boole _ _
  rw [iden]
  simp
