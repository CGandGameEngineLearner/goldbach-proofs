import Mathlib

theorem PEqualNP.Outside.L_goldbach_cross_repeated_height :
    ∀ (m : ℕ) (v : ℂ), (∑ i : Fin m, ∑ _j ∈ Finset.univ.erase i, (v * star v).re) = (m : ℝ)*((m : ℝ)-1)*‖v‖^2 := by
  intro m v
  have hv : (v * star v).re = ‖v‖ ^ 2 := by
    rw [Complex.star_def, Complex.mul_conj, Complex.ofReal_re,
      Complex.normSq_eq_norm_sq]
  simp_rw [hv]
  cases m with
  | zero => simp
  | succ m =>
      have hcard (i : Fin (m + 1)) : (Finset.univ.erase i).card = m := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ i)]
        simp
      simp [hcard, nsmul_eq_mul, Nat.cast_add, mul_assoc]
