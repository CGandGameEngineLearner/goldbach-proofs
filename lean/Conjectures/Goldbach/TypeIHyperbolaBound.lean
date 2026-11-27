import Mathlib

open scoped BigOperators

private lemma geom_partial_bound (z : ℂ) (hz : ‖z‖ = 1) (K : ℕ) :
    ‖∑ k ∈ Finset.Icc 1 K, z ^ k‖ ≤
      if z = 1 then (K : ℝ) else min (K : ℝ) (2 / ‖1 - z‖) := by
  have hid : ∀ K : ℕ, (1 - z) * ∑ k ∈ Finset.Icc 1 K, z ^ k = z - z ^ (K + 1) := by
    intro n
    induction n with
    | zero =>
      have h0 : Finset.Icc 1 (0 : ℕ) = ∅ := Finset.Icc_eq_empty (by omega)
      rw [h0, Finset.sum_empty]
      simp
    | succ m ih =>
      rw [Finset.sum_Icc_succ_top (f := fun k => z ^ k) (by omega), mul_add, ih]
      ring
  by_cases hc : z = 1
  · rw [ite_eq_left hc]
    subst hc
    have hcard : (Finset.Icc 1 K).card = K := by
      rw [Nat.card_Icc]; omega
    have hsum : (∑ k ∈ Finset.Icc 1 K, (1 : ℂ) ^ k) = ((K : ℕ) : ℂ) := by
      rw [Finset.sum_congr rfl (fun k _ => one_pow k), Finset.sum_const, hcard, nsmul_eq_mul, mul_one]
    rw [hsum, Complex.norm_natCast]
  · rw [ite_eq_right hc]
    refine le_min ?_ ?_
    · calc ‖∑ k ∈ Finset.Icc 1 K, z ^ k‖ ≤ ∑ k ∈ Finset.Icc 1 K, ‖z ^ k‖ := norm_sum_le _ _
        _ = ∑ k ∈ Finset.Icc 1 K, (1 : ℝ) := by
            apply Finset.sum_congr rfl
            intro k _
            rw [norm_pow, hz, one_pow]
        _ = (K : ℝ) := by
            rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one]
            push_cast
            ring
    · have hpos : (0 : ℝ) < ‖1 - z‖ := by
        rw [norm_pos_iff]
        exact sub_ne_zero.mpr (Ne.symm hc)
      rw [le_div_iff₀ hpos]
      calc ‖∑ k ∈ Finset.Icc 1 K, z ^ k‖ * ‖1 - z‖
          = ‖(1 - z) * ∑ k ∈ Finset.Icc 1 K, z ^ k‖ := by rw [norm_mul, mul_comm]
        _ = ‖z - z ^ (K + 1)‖ := by rw [hid K]
        _ ≤ ‖z‖ + ‖z ^ (K + 1)‖ := norm_sub_le _ _
        _ = 2 := by rw [norm_pow, hz, one_pow]; norm_num

private lemma geom_term_eq (d k : ℕ) (t : ℝ) :
    Complex.exp (((2 * Real.pi * ((d : ℝ) * (k : ℝ) * t) : ℝ) : ℂ) * Complex.I)
      = (Complex.exp (((2 * Real.pi * ((d : ℝ) * t) : ℝ) : ℂ) * Complex.I)) ^ k := by
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

private lemma unit_norm (y : ℝ) :
    ‖Complex.exp (((2 * Real.pi * y : ℝ) : ℂ) * Complex.I)‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I (2 * Real.pi * y)

theorem Conjectures.Goldbach.TypeIHyperbolaBound :
    let E (x : ℝ) := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)
    let cap (H : ℕ) (x : ℝ) := if E x = 1 then (H : ℝ) else min (H : ℝ) (2 / ‖1 - E x‖)
    ∀ (N D : ℕ) (a : ℕ → ℂ) (t : ℝ),
      ‖∑ d ∈ Finset.Icc 1 D, a d * ∑ k ∈ Finset.Icc 1 (N / d), E ((d : ℝ) * (k : ℝ) * t)‖
        ≤ ∑ d ∈ Finset.Icc 1 D, ‖a d‖ * cap (N / d) ((d : ℝ) * t) := by
  dsimp only
  intro N D a t
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum ?_)
  intro d _
  rw [norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  calc ‖∑ k ∈ Finset.Icc 1 (N / d), Complex.exp (((2 * Real.pi * ((d : ℝ) * (k : ℝ) * t) : ℝ) : ℂ) * Complex.I)‖
      = ‖∑ k ∈ Finset.Icc 1 (N / d), (Complex.exp (((2 * Real.pi * ((d : ℝ) * t) : ℝ) : ℂ) * Complex.I)) ^ k‖ := by
        congr 1
        exact Finset.sum_congr rfl (fun k _ => geom_term_eq d k t)
    _ ≤ (if Complex.exp (((2 * Real.pi * ((d : ℝ) * t) : ℝ) : ℂ) * Complex.I) = 1
          then ((N / d : ℕ) : ℝ)
          else min ((N / d : ℕ) : ℝ) (2 / ‖1 - Complex.exp (((2 * Real.pi * ((d : ℝ) * t) : ℝ) : ℂ) * Complex.I)‖)) :=
        geom_partial_bound _ (unit_norm _) (N / d)
