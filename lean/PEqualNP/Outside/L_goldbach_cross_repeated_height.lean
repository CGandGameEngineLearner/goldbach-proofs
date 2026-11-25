import Mathlib

theorem PEqualNP.Outside.L_goldbach_cross_repeated_height :
    ∀ (m : ℕ) (v : ℂ), (∑ i : Fin m, ∑ _j ∈ Finset.univ.erase i, (v * star v).re) = (m : ℝ)*((m : ℝ)-1)*‖v‖^2 := by
  intro m v
  have hval : (v * star v).re = ‖v‖^2 := by
    have h : v * star v = (Complex.normSq v : ℂ) := by
      rw [Complex.star_def]
      exact Complex.mul_conj v
    rw [h, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  have hinner : ∀ i : Fin m, (∑ _j ∈ Finset.univ.erase i, (v * star v).re) = ((m : ℝ)-1)*‖v‖^2 := by
    intro i
    have hm : 1 ≤ m := i.pos
    rw [Finset.sum_congr rfl (fun j _ => hval)]
    rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
    rw [nsmul_eq_mul, Nat.cast_sub hm]
    ring
  rw [Finset.sum_congr rfl (fun i _ => hinner i)]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring
