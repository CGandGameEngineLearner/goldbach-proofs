import Mathlib

/-! Finite summation by parts controls a frequency perturbation by the variation of its unit-modulus phase. -/

namespace FourierAbel

open Finset

theorem estimate (f g : ℕ → ℂ) (N : ℕ) (B d : ℝ) (hB : 0 ≤ B) (hd : 0 ≤ d)
    (hpart : ∀ X ≤ N, ‖∑ j ∈ range X, f j‖ ≤ B)
    (hunit : ∀ j, ‖g j‖ = 1) (hstep : ∀ j, ‖g (j+1)-g j‖ ≤ d) :
    ‖∑ j ∈ range N, f j*g j‖ ≤ (1+(N:ℝ)*d)*B := by
  let P (X : ℕ) := ∑ j ∈ range X, f j
  have decomp : (∑ j ∈ range N, f j*g j) =
      P N * g (N-1) - ∑ i ∈ range (N-1), P (i+1)*(g (i+1)-g i) :=
    Finset.sum_range_by_parts' f g N
  have hend : ‖P N * g (N-1)‖ ≤ B := by simpa [norm_mul, hunit] using hpart N le_rfl
  have htail : ‖∑ i ∈ range (N-1), P (i+1)*(g (i+1)-g i)‖ ≤ (N:ℝ)*(B*d) := by
    calc
      _ ≤ ∑ i ∈ range (N-1), ‖P (i+1)*(g (i+1)-g i)‖ := norm_sum_le _ _
      _ ≤ ∑ _i ∈ range (N-1), B*d := by
        apply sum_le_sum
        intro i hi
        have hi' := mem_range.mp hi
        rw [norm_mul]
        exact mul_le_mul (hpart (i+1) (by omega)) (hstep i) (norm_nonneg _) hB
      _ = ((N-1:ℕ):ℝ)*(B*d) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (by exact_mod_cast (Nat.sub_le N 1)) (mul_nonneg hB hd)
  rw [decomp]
  exact (norm_sub_le _ _).trans ((add_le_add hend htail).trans_eq (by ring))

end FourierAbel

namespace FrequencyPerturbation

noncomputable def E (x : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

theorem E_norm (x : ℝ) : ‖E x‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

theorem E_add (x y : ℝ) : E (x+y) = E x * E y := by
  unfold E
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The chord between consecutive phase factors has length at most the
absolute change in the angle. -/
theorem E_step (n : ℕ) (e : ℝ) :
    ‖E (((n+1 : ℕ):ℝ)*e) - E ((n:ℝ)*e)‖ ≤ 2*Real.pi*|e| := by
  rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, E_add]
  rw [show E ((n:ℝ)*e)*E e - E ((n:ℝ)*e) = E ((n:ℝ)*e)*(E e-1) by ring,
    norm_mul, E_norm, one_mul]
  simpa only [E, mul_comm Complex.I, Real.norm_eq_abs, abs_mul,
    abs_of_pos Real.pi_pos, abs_of_pos (by norm_num : (0:ℝ)<2)] using
    (Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2*Real.pi*e))

end FrequencyPerturbation

theorem Conjectures.Cuts.Taskedf57c34465900af937f8755 : (have x1 : (ℕ → ℝ) → ℕ → ℝ → ℂ := fun (x1 : ℕ → ℝ) (x2 : ℕ) (x3 : ℝ) => ∑ x4 ∈ Finset.range x2, ↑(x1 x4) * Complex.exp (↑((2 : ℝ) * Real.pi * ↑x4 * x3) * Complex.I); ∀ (x2 : ℕ → ℝ) (x3 : ℕ) (x4 x5 x6 : ℝ), (0 : ℝ) ≤ x6 → (∀ x8 ≤ x3, ‖x1 x2 x8 x4‖ ≤ x6) → ‖x1 x2 x3 (x4 + x5)‖ ≤ ((1 : ℝ) + (2 : ℝ) * Real.pi * ↑x3 * |x5|) * x6) := by
  classical
  intro S w N x e B hB hx
  let f (j : ℕ) : ℂ := (w j : ℂ) * FrequencyPerturbation.E ((j:ℝ)*x)
  let g (j : ℕ) : ℂ := FrequencyPerturbation.E ((j:ℝ)*e)
  have form (L : ℕ) (y : ℝ) : S w L y =
      ∑ j ∈ Finset.range L, (w j:ℂ) * FrequencyPerturbation.E ((j:ℝ)*y) := by
    dsimp only [S, FrequencyPerturbation.E]
    simp only [mul_assoc]
  have sums (L : ℕ) (hL : L ≤ N) : ‖∑ j ∈ Finset.range L, f j‖ ≤ B := by
    simpa only [form, f] using hx L hL
  have shift : S w N (x+e) = ∑ j ∈ Finset.range N, f j * g j := by
    rw [form]
    apply Finset.sum_congr rfl
    intro j _
    dsimp only [f, g]
    rw [mul_add, FrequencyPerturbation.E_add, mul_assoc]
  rw [shift]
  calc
    _ ≤ (1 + (N:ℝ)*(2*Real.pi*|e|))*B :=
      FourierAbel.estimate f g N B (2*Real.pi*|e|) hB (by positivity) sums
        (fun j => FrequencyPerturbation.E_norm _) (fun j => FrequencyPerturbation.E_step j e)
    _ = _ := by ring
