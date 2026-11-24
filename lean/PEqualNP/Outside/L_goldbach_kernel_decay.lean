import Mathlib

theorem PEqualNP.Outside.L_goldbach_kernel_decay :
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let K := fun (N : ℕ) (b : ℝ) => Finset.sum (Finset.range (N+1)) (fun k => E ((k:ℝ)*b)); ∀ N b, E b ≠ 1 → ‖K N b‖ ≤ 2/‖1-E b‖ := by
  intro E K N b hb
  have hEadd : ∀ x y : ℝ, E (x + y) = E x * E y := by
    intro x y
    simp only [E]
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hEzero : E 0 = 1 := by
    simp only [E]
    norm_num
  have hpow : ∀ k : ℕ, E ((k:ℝ)*b) = (E b)^k := by
    intro k
    induction k with
    | zero => simp only [Nat.cast_zero, zero_mul, hEzero, pow_zero]
    | succ k ih =>
      rw [Nat.cast_succ, add_mul, one_mul, hEadd, ih, pow_succ]
  have hnorm : ‖E b‖ = 1 := by
    simp only [E]
    exact Complex.norm_exp_ofReal_mul_I _
  have hK : K N b = Finset.sum (Finset.range (N+1)) (fun k => (E b)^k) := by
    simp only [K]
    apply Finset.sum_congr rfl
    intro k hk
    exact hpow k
  have hgeom : (1 - E b) * Finset.sum (Finset.range (N+1)) (fun k => (E b)^k) = 1 - (E b)^(N+1) := by
    rw [mul_comm, geom_sum_mul_neg]
  have hne : 1 - E b ≠ 0 := by
    intro h
    apply hb
    have := sub_eq_zero.mp h
    exact this.symm
  have hden : (0:ℝ) < ‖1 - E b‖ := by
    rw [norm_pos_iff]
    exact hne
  rw [hK, le_div_iff₀ hden, mul_comm]
  have hstep : ‖1 - E b‖ * ‖Finset.sum (Finset.range (N+1)) (fun k => (E b)^k)‖ = ‖1 - (E b)^(N+1)‖ := by
    rw [← norm_mul, ← hgeom]
  rw [hstep]
  calc ‖1 - (E b)^(N+1)‖ ≤ ‖(1:ℂ)‖ + ‖(E b)^(N+1)‖ := norm_sub_le _ _
    _ = 1 + 1 := by rw [norm_pow, hnorm, one_pow, norm_one]
    _ = 2 := by norm_num
