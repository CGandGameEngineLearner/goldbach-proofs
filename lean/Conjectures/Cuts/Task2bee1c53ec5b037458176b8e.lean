import Mathlib

-- The character integral and conjugation laws are adapted from the Apache-2.0
-- BinaryShiftFourierFourth proof in this repository.
open Finset MeasureTheory
open scoped ComplexConjugate

namespace DigitBoxCharacter

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


theorem eneg (x : ℝ) : conj (E x) = E (-x) := by
  unfold E
  rw [← Complex.exp_conj]
  congr 1
  push_cast
  simp only [map_mul,Complex.conj_ofReal,Complex.conj_I,map_ofNat]
  ring

end DigitBoxCharacter

open DigitBoxCharacter in
theorem Conjectures.Cuts.Task2bee1c53ec5b037458176b8e : (by
  classical
  let e := fun (n : ℕ) (t : ℝ) => Complex.exp (2*(Real.pi:ℂ)*Complex.I*(n:ℂ)*(t:ℂ))
  exact ∀ (b k : ℕ) (D : ℕ → Finset ℕ) (R : Finset ℕ),
    let W := Fintype.piFinset (fun i : Fin k => D i)
    let v := fun w : Fin k → ℕ => ∑ i : Fin k, w i*b^(i:ℕ)
    (((W.filter (fun w => v w ∈ R)).card):ℝ) = (∫ t in (0:ℝ)..1, (∏ i : Fin k, ∑ d ∈ D i, e (d*b^(i:ℕ)) t) * star (∑ n ∈ R, e n t)).re) := by
  classical
  intro e b k D R W v
  have charEq (n : ℕ) (t : ℝ) : e n t = E ((n:ℝ)*t) := by
    dsimp [e,E]; congr 1; push_cast; ring
  have orth (u n : ℕ) :
      (∫ t in (0:ℝ)..1, e u t * conj (e n t)) = if u = n then 1 else 0 := by
    have phase (t : ℝ) : e u t * conj (e n t) = E ((((u:ℤ)-(n:ℤ):ℤ):ℝ)*t) := by
      rw [charEq, charEq, eneg, ← phase_add]
      congr 1
      push_cast
      ring
    simp_rw [phase]
    rw [fourier_mode]
    by_cases h : u = n
    · subst n; simp
    · have hh : (u:ℤ) - (n:ℤ) ≠ 0 := by omega
      simp [h,hh]
  have expand (t : ℝ) : (∏ i : Fin k, ∑ d ∈ D i, e (d*b^(i:ℕ)) t) = ∑ w ∈ W, e (v w) t := by
    rw [Finset.prod_univ_sum]
    apply Finset.sum_congr rfl
    intro w _
    dsimp only [e,v]
    rw [← Complex.exp_sum]
    congr 1
    push_cast
    simp only [Finset.mul_sum, Finset.sum_mul]
  have iden : (∫ t in (0:ℝ)..1, (∏ i : Fin k, ∑ d ∈ D i, e (d*b^(i:ℕ)) t) *
      star (∑ n ∈ R, e n t)) = ((W.filter (fun w => v w ∈ R)).card:ℂ) := by
    have ep (t : ℝ) : (∏ i : Fin k, ∑ d ∈ D i, e (d*b^(i:ℕ)) t) * star (∑ n ∈ R, e n t) =
        ∑ w ∈ W, ∑ n ∈ R, e (v w) t * conj (e n t) := by
      rw [expand]
      change (∑ w ∈ W, e (v w) t) * conj (∑ n ∈ R, e n t) = _
      rw [map_sum,Finset.sum_mul]
      simp only [Finset.mul_sum]
    simp_rw [ep]
    rw [intervalIntegral.integral_finsetSum (fun w _ => (show Continuous (fun t => ∑ n ∈ R, e (v w) t * conj (e n t)) by dsimp [e]; fun_prop).intervalIntegrable ..)]
    have row (w : Fin k → ℕ) : (∫ t in (0:ℝ)..1, ∑ n ∈ R, e (v w) t * conj (e n t)) = if v w ∈ R then (1:ℂ) else 0 := by
      rw [intervalIntegral.integral_finsetSum (fun n (_ : n ∈ R) => (show Continuous (fun t => e (v w) t * conj (e n t)) by dsimp [e]; fun_prop).intervalIntegrable ..)]
      simp_rw [orth]
      simp
    simp_rw [row]
    exact Finset.sum_boole _ _
  rw [iden]
  simp
