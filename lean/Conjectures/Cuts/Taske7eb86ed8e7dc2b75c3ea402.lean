import Mathlib

open Finset MeasureTheory
open scoped ComplexConjugate

namespace GoldbachSubsetTargetFourier

noncomputable section

-- Fourier mode lemmas adapted from DyadicMixedB4Fourier in
-- Conjectures.Goldbach.Type2MovingDiagonalMoment (Apache-2.0).
def frequency (k : ℤ) : ℂ := (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)

def mode (k : ℤ) (t : ℝ) : ℂ := Complex.exp (frequency k * (t : ℂ))

theorem continuous_mode (k : ℤ) : Continuous (mode k) := by
  unfold mode
  fun_prop

theorem mode_integral (k : ℤ) :
    (∫ t in (0 : ℝ)..1, mode k t) = if k = 0 then 1 else 0 := by
  by_cases zero : k = 0
  · simp [zero, mode, frequency]
  · have kNonzero : (k : ℂ) ≠ 0 := Int.cast_ne_zero.mpr zero
    have piNonzero : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have frequencyNonzero : frequency k ≠ 0 := by
      exact mul_ne_zero kNonzero (mul_ne_zero (mul_ne_zero (by norm_num) piNonzero) Complex.I_ne_zero)
    change (∫ t in (0 : ℝ)..1, Complex.exp (frequency k * (t : ℂ))) = _
    rw [ite_eq_right zero, integral_exp_mul_complex frequencyNonzero]
    simp [frequency, Complex.exp_int_mul_two_pi_mul_I]

theorem mode_mul_conj (j k : ℤ) (t : ℝ) :
    mode j t * star (mode k t) = mode (j - k) t := by
  change Complex.exp (frequency j * (t : ℂ)) *
    conj (Complex.exp (frequency k * (t : ℂ))) = _
  rw [← Complex.exp_conj, ← Complex.exp_add]
  unfold mode frequency
  congr 1
  have conjTwo : (starRingEnd ℂ) 2 = 2 := by
    simpa only [Nat.cast_ofNat] using (map_natCast (starRingEnd ℂ) 2)
  simp [map_mul, Complex.conj_I, Int.cast_sub, conjTwo]
  ring

end
end GoldbachSubsetTargetFourier

open GoldbachSubsetTargetFourier in
theorem Conjectures.Cuts.Taske7eb86ed8e7dc2b75c3ea402 : (have x1 : ℕ → ℝ → ℂ := fun (x1 : ℕ) (x2 : ℝ) => Complex.exp ((2 : ℂ) * ↑Real.pi * Complex.I * ↑x1 * ↑x2); ∀ (x2 : Finset ℕ) (x3 x4 : ℕ) (x5 : Finset ℕ),   have x6 : Finset (Finset ℕ) := Finset.powersetCard x4 x2;   have x7 : Finset ℕ → ℕ := fun (x7 : Finset ℕ) => ∑ x8 ∈ x7, x3 ^ x8;   ↑{x8 ∈ x6 | x7 x8 ∈ x5}.card = (∫ (x8 : ℝ) in (0 : ℝ)..(1 : ℝ), (∑ x9 ∈ x6, ∏ x10 ∈ x9, x1 (x3 ^ x10) x8) * Star.star (∑ x9 ∈ x5, x1 x9 x8)).re) := by
  classical
  intro e A b j R S v
  have character (n : ℕ) (t : ℝ) : e n t = mode (n : ℤ) t := by
    unfold e mode frequency
    congr 1
    push_cast
    ring
  have product (s : Finset ℕ) (t : ℝ) :
      (∏ i ∈ s, e (b ^ i) t) = mode (v s : ℤ) t := by
    simp_rw [character]
    unfold mode frequency
    rw [← Complex.exp_sum]
    congr 1
    dsimp only [v]
    push_cast <;> simp only [Finset.sum_mul]
  let P := S ×ˢ R
  let d (p : Finset ℕ × ℕ) : ℤ := (v p.1 : ℤ) - p.2
  have point (t : ℝ) :
      (∑ s ∈ S, ∏ i ∈ s, e (b ^ i) t) * star (∑ n ∈ R, e n t) =
      ∑ p ∈ P, mode (d p) t := by
    simp_rw [product, character]
    rw [star_sum, sum_mul_sum, show P = S ×ˢ R by rfl, sum_product]
    exact sum_congr rfl fun s _ => sum_congr rfl fun n _ => mode_mul_conj _ _ _
  have pairing : (∫ t in (0 : ℝ)..1, ∑ p ∈ P, mode (d p) t) =
      ((S.filter fun s => v s ∈ R).card : ℂ) := by
    rw [intervalIntegral.integral_finsetSum (fun p _ => (continuous_mode (d p)).intervalIntegrable _ _)]
    calc
      _ = ∑ s ∈ S, (if v s ∈ R then (1 : ℂ) else 0) := by
        rw [show P = S ×ˢ R by rfl, sum_product]
        apply sum_congr rfl
        intro s _
        simp [mode_integral, d, sub_eq_zero, Finset.sum_ite_eq]
      _ = _ := by rw [← Finset.sum_filter]; simp
  simp_rw [point]
  rw [pairing] <;> simp
