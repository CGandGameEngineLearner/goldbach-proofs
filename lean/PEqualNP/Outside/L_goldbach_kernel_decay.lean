import Mathlib

namespace PEqualNP.Outside

theorem L_goldbach_kernel_decay :
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let K := fun (N : ℕ) (b : ℝ) => Finset.sum (Finset.range (N+1)) (fun k => E ((k:ℝ)*b)); ∀ N b, E b ≠ 1 → ‖K N b‖ ≤ 2/‖1-E b‖ := by
  let E := fun x : ℝ => Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)
  change ∀ (N : ℕ) (b : ℝ), E b ≠ 1 →
    ‖∑ k ∈ Finset.range (N + 1), E ((k : ℝ) * b)‖ ≤ 2 / ‖1 - E b‖
  intro N b hb
  have harmonic (k : ℕ) : E ((k : ℝ) * b) = (E b) ^ k := by
    unfold E
    rw [← Complex.exp_nat_mul]
    apply congrArg Complex.exp
    push_cast <;> ring
  have unit : ‖E b‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have chord : 0 < ‖1 - E b‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hb.symm)
  simp_rw [harmonic]
  apply (le_div_iff₀ chord).mpr
  calc
    ‖∑ k ∈ Finset.range (N + 1), (E b) ^ k‖ * ‖1 - E b‖ =
        ‖1 - (E b) ^ (N + 1)‖ := by rw [← norm_mul, geom_sum_mul_neg]
    _ ≤ ‖(1 : ℂ)‖ + ‖(E b) ^ (N + 1)‖ := norm_sub_le _ _
    _ = 2 := by rw [norm_one, norm_pow, unit, one_pow]; norm_num

end PEqualNP.Outside
