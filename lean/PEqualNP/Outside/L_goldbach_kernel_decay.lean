import Mathlib

theorem PEqualNP.Outside.L_goldbach_kernel_decay :
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I);
    let K := fun (N : ℕ) (b : ℝ) => Finset.sum (Finset.range (N+1)) (fun k => E ((k:ℝ)*b));
    ∀ N b, E b ≠ 1 → ‖K N b‖ ≤ 2/‖1-E b‖ := by
  intro E K N b hb
  have hE (t : ℝ) : ‖E t‖ = 1 := by
    change ‖Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I)‖ = 1
    rw [Complex.norm_exp]
    simp [Complex.mul_re]
  have he (k : ℕ) : E ((k : ℝ) * b) = (E b) ^ k := by
    dsimp only [E]
    rw [← Complex.exp_nat_mul]
    congr 1 <;> push_cast <;> ring
  have hK : K N b = Finset.sum (Finset.range (N+1)) (fun k => (E b) ^ k) := by
    dsimp only [K]
    apply Finset.sum_congr rfl
    intro k hk
    exact he k
  have hgeom : K N b * (1 - E b) = 1 - (E b) ^ (N+1) := by
    rw [hK]
    exact geom_sum_mul_neg (E b) (N+1)
  have hprod : ‖K N b‖ * ‖1 - E b‖ ≤ 2 := by
    rw [← norm_mul, hgeom]
    calc
      ‖1 - (E b) ^ (N+1)‖ ≤ ‖(1 : ℂ)‖ + ‖(E b) ^ (N+1)‖ := norm_sub_le _ _
      _ = 2 := by rw [Complex.norm_pow, hE b]; norm_num
  have hpos : 0 < ‖1 - E b‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hb))
  exact (le_div_iff₀ hpos).mpr hprod
