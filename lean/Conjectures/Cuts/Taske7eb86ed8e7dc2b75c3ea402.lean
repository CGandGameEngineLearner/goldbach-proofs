import Mathlib

-- The character integral and conjugation laws are adapted from the Apache-2.0
-- BinaryShiftFourierFourth proof in this repository.
open Finset MeasureTheory
open scoped ComplexConjugate

namespace SubsetSumTargetIntegralCharacters

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

end SubsetSumTargetIntegralCharacters


open SubsetSumTargetIntegralCharacters
private noncomputable def ch (n : ℕ) (t : ℝ) : ℂ :=
  Complex.exp (2*(Real.pi:ℂ)*Complex.I*(n:ℂ)*(t:ℂ))

private theorem ortho (m n : ℕ) :
    (∫ t in (0:ℝ)..1, ch m t * star (ch n t)) = if m = n then 1 else 0 := by
  have asE (a : ℕ) (t : ℝ) : ch a t = E ((a:ℝ)*t) := by
    dsimp [ch,E]; congr 1; push_cast; ring
  have he (t : ℝ) : ch m t * star (ch n t) = E ((((m:ℤ)-(n:ℤ):ℤ):ℝ)*t) := by
    change ch m t * conj (ch n t) = _
    rw [asE,asE,eneg,← phase_add]
    congr 1; push_cast; ring
  simp_rw [he]
  rw [fourier_mode]
  by_cases h : m=n
  · subst n; simp
  · have hh : (m:ℤ)-(n:ℤ) ≠ 0 := by omega
    simp [hh,h]

theorem Conjectures.Cuts.Taske7eb86ed8e7dc2b75c3ea402 : (by
  classical
  let e := fun (n : ℕ) (t : ℝ) => Complex.exp (2*(Real.pi:ℂ)*Complex.I*(n:ℂ)*(t:ℂ))
  exact ∀ (A : Finset ℕ) (b j : ℕ) (R : Finset ℕ),
    let B := A.powersetCard j
    let v := fun s : Finset ℕ => ∑ i ∈ s, b^i
    (((B.filter (fun s => v s ∈ R)).card):ℝ) = (∫ t in (0:ℝ)..1, (∑ s ∈ B, ∏ i ∈ s, e (b^i) t) * star (∑ n ∈ R, e n t)).re) := by
  classical
  intro e A b j R B v
  have collapse (s : Finset ℕ) (t : ℝ) : (∏ i ∈ s, ch (b^i) t) = ch (v s) t := by
    dsimp [ch,v]
    rw [← Complex.exp_sum]
    congr 1
    push_cast
    simp only [Finset.sum_mul,Finset.mul_sum]
  have expand (t : ℝ) : (∑ s ∈ B, ∏ i ∈ s, ch (b^i) t) * star (∑ n ∈ R, ch n t) =
      ∑ s ∈ B, ∑ n ∈ R, ch (v s) t * star (ch n t) := by
    simp_rw [collapse]
    change _ * conj (∑ n ∈ R, ch n t) = _
    rw [map_sum,Finset.sum_mul]; simp only [Finset.mul_sum]; rfl
  have row (s : Finset ℕ) : (∫ t in (0:ℝ)..1, ∑ n ∈ R, ch (v s) t * star (ch n t)) = if v s ∈ R then (1:ℂ) else 0 := by
    rw [intervalIntegral.integral_finsetSum (fun n _ => (show Continuous (fun t => ch (v s) t * star (ch n t)) by dsimp [ch]; fun_prop).intervalIntegrable ..)]
    simp_rw [ortho]; simp
  change _ = (∫ t in (0:ℝ)..1, (∑ s ∈ B, ∏ i ∈ s, ch (b^i) t) * star (∑ n ∈ R, ch n t)).re
  simp_rw [expand]
  rw [intervalIntegral.integral_finsetSum (fun s _ => (show Continuous (fun t => ∑ n ∈ R, ch (v s) t * star (ch n t)) by dsimp [ch]; fun_prop).intervalIntegrable ..)]
  simp_rw [row]
  rw [Finset.sum_boole]
  simp
