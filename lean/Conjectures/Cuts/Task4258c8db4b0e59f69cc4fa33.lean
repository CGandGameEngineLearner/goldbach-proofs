import Mathlib

-- The character integral and conjugation laws are adapted from the Apache-2.0
-- BinaryShiftFourierFourth proof in this repository.
open Finset MeasureTheory
open scoped ComplexConjugate

namespace EighthMomentOrthogonality

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

end EighthMomentOrthogonality

open EighthMomentOrthogonality in
theorem Conjectures.Cuts.Task4258c8db4b0e59f69cc4fa33 : (∀ (x1 : ℕ → ℤ) (x2 : Finset ℕ),   have x3 : ℝ → ℂ := fun (x3 : ℝ) => ∑ x4 ∈ x2, Complex.exp ((2 : ℂ) * ↑Real.pi * Complex.I * ↑(x1 x4) * ↑x3);   have x4 : Finset (Fin (4 : ℕ) → ℕ) := Fintype.piFinset fun (x4 : Fin (4 : ℕ)) => x2;   have x5 : (Fin (4 : ℕ) → ℕ) → ℤ := fun (x5 : Fin (4 : ℕ) → ℕ) => ∑ x6 : Fin (4 : ℕ), x1 (x5 x6);   ∫ (x6 : ℝ) in (0 : ℝ)..(1 : ℝ), ‖x3 x6‖ ^ (8 : ℕ) = ↑{x6 ∈ x4.product x4 | x5 x6.1 = x5 x6.2}.card) := by
  classical
  intro f s S T F
  have term (j : ℕ) (t : ℝ) :
      Complex.exp (2*(Real.pi:ℂ)*Complex.I*(f j:ℂ)*(t:ℂ)) = E ((f j:ℝ)*t) := by
    unfold E
    congr 1
    push_cast
    ring
  have fourth (t : ℝ) : (S t)^4 = ∑ u ∈ T, E ((F u:ℝ)*t) := by
    change (∑ j ∈ s, Complex.exp (2*(Real.pi:ℂ)*Complex.I*(f j:ℂ)*(t:ℂ)))^4 = _
    simp_rw [term]
    calc
      _ = ∏ _i : Fin 4, (∑ j ∈ s, E ((f j:ℝ)*t)) := by simp
      _ = ∑ u ∈ T, ∏ i : Fin 4, E ((f (u i):ℝ)*t) :=
        Finset.prod_univ_sum (fun _ : Fin 4 => s) (fun _ j => E ((f j:ℝ)*t))
      _ = _ := by
        apply sum_congr rfl
        intro u _
        unfold E
        rw [← Complex.exp_sum]
        congr 1
        dsimp [F]
        push_cast
        simp only [Finset.sum_mul, Finset.mul_sum]
  let W := T.product T
  let M := fun (w : (Fin 4 → ℕ) × (Fin 4 → ℕ)) (t : ℝ) => E (((F w.1 - F w.2 : ℤ):ℝ)*t)
  have ortho (w) : (∫ t in (0:ℝ)..1, M w t) = if F w.1 = F w.2 then 1 else 0 := by
    simp only [M,fourier_mode,sub_eq_zero]
  have point (t : ℝ) : ((‖S t‖^8:ℝ):ℂ) = ∑ w ∈ W, M w t := by
    have sqnorm : ((‖S t‖^8:ℝ):ℂ) = (S t)^4 * conj ((S t)^4) := by
      rw [Complex.mul_conj', norm_pow]; push_cast; ring
    rw [sqnorm, fourth, map_sum, sum_mul, show W = T ×ˢ T by rfl, sum_product]
    apply sum_congr rfl
    intro u _
    rw [mul_sum]
    apply sum_congr rfl
    intro v _
    rw [eneg, ← phase_add]
    dsimp [M]
    push_cast
    ring_nf
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  simp_rw [point]
  rw [intervalIntegral.integral_finsetSum (fun w _ =>
    (show Continuous (M w) by dsimp [M,E]; fun_prop).intervalIntegrable ..)]
  simp_rw [ortho]
  push_cast
  rw [← Finset.sum_filter]
  simp [W]
