import Mathlib

open scoped BigOperators

/-- The finite geometric kernel is bounded by twice the inverse distance from resonance. -/
theorem PEqualNP.Outside.L_goldbach_kernel_decay :
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I)
    let K := fun (N : ℕ) (b : ℝ) =>
      Finset.sum (Finset.range (N+1)) (fun k => E ((k:ℝ)*b))
    ∀ N b, E b ≠ 1 → ‖K N b‖ ≤ 2/‖1-E b‖ := by
  dsimp only
  intro N b hb
  let z := Complex.exp (((2*Real.pi*b:ℝ):ℂ)*Complex.I)
  have hz : ‖z‖ = 1 := Complex.norm_exp_ofReal_mul_I (2*Real.pi*b)
  have hpos : 0 < ‖1-z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hb))
  have hp (k : ℕ) :
      Complex.exp (((2*Real.pi*((k:ℝ)*b):ℝ):ℂ)*Complex.I) = z^k := by
    dsimp only [z]
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  change ‖∑ k ∈ Finset.range (N+1),
    Complex.exp (((2*Real.pi*((k:ℝ)*b):ℝ):ℂ)*Complex.I)‖ ≤ 2/‖1-z‖
  simp_rw [hp]
  apply (le_div_iff₀ hpos).2
  rw [← norm_mul, geom_sum_mul_neg]
  calc
    ‖1-z^(N+1)‖ ≤ ‖(1:ℂ)‖ + ‖z^(N+1)‖ := norm_sub_le _ _
    _ = 2 := by rw [norm_pow, hz, norm_one, one_pow]; norm_num
