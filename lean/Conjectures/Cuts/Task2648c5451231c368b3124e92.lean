import Mathlib

-- The character integral and conjugation laws are adapted from the Apache-2.0
-- BinaryShiftFourierFourth proof in this repository.
open Finset MeasureTheory
open scoped ComplexConjugate

namespace FixedWeightFourierCoefficientCharacters

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

end FixedWeightFourierCoefficientCharacters


open FixedWeightFourierCoefficientCharacters
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

theorem Conjectures.Cuts.Task2648c5451231c368b3124e92 : (by
  classical
  let e := fun (n : ℕ) (t : ℝ) => Complex.exp (2*(Real.pi:ℂ)*Complex.I*(n:ℂ)*(t:ℂ))
  exact ∀ (A : Finset ℕ) (c : ℕ → ℂ) (j : ℕ),
    (∫ u in (0:ℝ)..1, (∏ i ∈ A, (1+c i * e 1 u)) * star (e j u)) = ∑ s ∈ A.powersetCard j, ∏ i ∈ s, c i) := by
  classical
  intro e A c j
  change (∫ u in (0:ℝ)..1, (∏ i ∈ A, (1+c i * ch 1 u)) * star (ch j u)) = _
  have power (n : ℕ) (u : ℝ) : ch 1 u ^ n = ch n u := by
    dsimp [ch]
    rw [← Complex.exp_nat_mul]
    congr 1; push_cast; ring
  have expand (u : ℝ) : (∏ i ∈ A, (1+c i * ch 1 u)) * star (ch j u) =
      ∑ s ∈ A.powerset, (∏ i ∈ s, c i) * (ch s.card u * star (ch j u)) := by
    rw [Finset.prod_one_add,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro s _
    rw [Finset.prod_mul_distrib,Finset.prod_const,power,mul_assoc]
  have row (s : Finset ℕ) : (∫ u in (0:ℝ)..1, (∏ i ∈ s, c i) * (ch s.card u * star (ch j u))) =
      if s.card=j then (∏ i ∈ s, c i) else 0 := by
    rw [intervalIntegral.integral_const_mul,ortho]
    split <;> simp
  simp_rw [expand]
  rw [intervalIntegral.integral_finsetSum (fun s _ => (show Continuous (fun u => (∏ i ∈ s, c i) * (ch s.card u * star (ch j u))) by dsimp [ch]; fun_prop).intervalIntegrable ..)]
  simp_rw [row]
  rw [Finset.powersetCard_eq_filter,Finset.sum_filter]
