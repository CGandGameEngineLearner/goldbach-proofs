import Mathlib

open Finset

/-- Finite summation by parts with the sum evaluated at its right endpoint. -/
private theorem prefixAbel (d : ℕ → ℝ) (z : ℕ → ℂ) (h0 : d 0 = 0) (n : ℕ) :
    (∑ k ∈ Icc 1 n, ((d k - d (k-1) : ℝ) : ℂ) * z k) =
      (d n : ℂ) * z n + ∑ k ∈ range n, (d k : ℂ) * (z k - z (k+1)) := by
  induction n with
  | zero => simp [h0]
  | succ n ih =>
    rw [sum_Icc_succ_top (by omega), ih, sum_range_succ]
    simp only [Nat.add_sub_cancel, Complex.ofReal_sub]
    ring

private noncomputable def osc (x : ℝ) := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

private theorem oscStep (k : ℕ) (β : ℝ) :
    ‖osc ((k:ℝ)*β) - osc ((k+1:ℕ)*β)‖ ≤ 2*Real.pi*|β| := by
  have hs : osc ((k+1:ℕ)*β) = osc ((k:ℝ)*β) * osc β := by
    unfold osc
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hs, ← mul_one_sub, norm_mul, show ‖osc ((k:ℝ)*β)‖ = 1 from Complex.norm_exp_ofReal_mul_I _,
    one_mul, norm_sub_rev]
  have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2*Real.pi*β)
  simpa [osc, mul_comm Complex.I, Real.norm_eq_abs, abs_mul, abs_of_pos Real.pi_pos] using h

theorem PEqualNP.Outside.L_goldbach_finite_phase_abel_two_ranges : let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let D := fun (q a n : ℕ) => (∑ k ∈ (Finset.range (n+1)).filter (fun k => k % q = a % q), ArithmeticFunction.vonMangoldt k) - (n:ℝ)/(Nat.totient q:ℝ); let F := fun (q a n : ℕ) (β : ℝ) => ∑ k ∈ Finset.Icc 1 n, (((if k % q = a % q then ArithmeticFunction.vonMangoldt k else 0) - 1/(Nat.totient q:ℝ):ℝ):ℂ)*E ((k:ℝ)*β); let J := fun (q a l u : ℕ) (β : ℝ) => 2 * Real.pi * |β| * (∑ m ∈ Finset.Ico l u, |D q a m|); ∀ (q a n t : ℕ) (β : ℝ), 0 < q → t ≤ n → ‖F q a n β‖ ≤ |D q a n| + J q a 0 t β + J q a t n β := by
  intro E D F J q a n t β _hq ht
  let d := D q a
  let z := fun k : ℕ => osc ((k:ℝ)*β)
  have h0 : d 0 = 0 := by simp [d, D, sum_filter]
  have hd (k : ℕ) : d (k+1) - d k =
      (if (k+1) % q = a % q then ArithmeticFunction.vonMangoldt (k+1) else 0) -
        1/(Nat.totient q:ℝ) := by
    simp only [d, D, sum_filter, sum_range_succ (n := k+1), Nat.cast_add, Nat.cast_one]
    ring
  have formula : F q a n β = (d n:ℂ)*z n + ∑ k ∈ range n, (d k:ℂ)*(z k-z (k+1)) := by
    rw [← prefixAbel d z h0 n]
    refine sum_congr rfl fun k hk => ?_
    obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (n := k) (by have := (mem_Icc.mp hk).1; omega)
    simp only [Nat.succ_sub_one, hd]
    rfl
  rw [formula]
  calc
    _ ≤ ‖(d n:ℂ)*z n‖ + ∑ k ∈ range n, ‖(d k:ℂ)*(z k-z (k+1))‖ :=
      (norm_add_le ..).trans (add_le_add_right (norm_sum_le ..) _)
    _ ≤ |d n| + ∑ k ∈ range n, 2*Real.pi*|β| * |d k| := by
      have hz : ‖z n‖ = 1 := Complex.norm_exp_ofReal_mul_I _
      rw [norm_mul, hz, mul_one, Complex.norm_real, Real.norm_eq_abs]
      gcongr with k
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_comm]
      exact mul_le_mul_of_nonneg_right (oscStep k β) (abs_nonneg _)
    _ = _ := by
      rw [← mul_sum, range_eq_Ico, ← sum_Ico_consecutive (fun k => |d k|) (Nat.zero_le t) ht]
      dsimp [J, d]
      ring